-- AsteroidModel.elm
----
-- Simon Swanson
-- part of final project
----

{-
    Module to draw and move the objects in the game Asteroids 
-}


module AsteroidModel ( Ship, newShip, formFromShip, updateShip, hitShip, isInvincible, isDestroyed, isGone, shipPosition
                     , Asteroid, Blink, newAsteroid, moveAsteroid, formFromAsteroid, asteroidDestruction, isEliminated, layers
                     , Shot, fireShot, formFromShot, updateShots, addShot, isFaded
                     ) where


import Color
import Graphics.Collage     as GC
import Graphics.Element     (empty)
import List                 ((::))
import Random
import Time                 (Time,millisecond,second)


type alias Acceleration = Float
type alias Layers       = Int
type alias Velocity     = (Float,Float)


-- keeps form thetas in the range [0,2pi) for better comparison
-- not be necessary in latest configuration, leaving in for legacy support
smartRotate : Float -> GC.Form -> GC.Form
smartRotate x f = { f | theta <- floatRem (f.theta + x) (2 * pi) }


floatRem : Float -> Float -> Float
floatRem x y = if
    | x < 0     -> floatRem (x + y) y
    | x >= y    -> floatRem (x - y) y
    | otherwise -> x


-- moves forms to other side of board if they go too far
overflowMove : (Float,Float) -> GC.Form -> GC.Form
overflowMove (a,b) f = { f | x <- overflow <| f.x + a, y <- overflow <| f.y + b}


overflow : Float -> Float
overflow x = if
    | x <= -108 -> 108
    | x >= 108  -> -108
    | otherwise -> x


-- only use this in one place, so very specific to certain right triangles
-- takes in the sin of an angle and a hypotenuse
triangleSidesAAS : Float -> Float -> (Float,Float)
triangleSidesAAS sinAngle hypo = if
    | sinAngle == 0 -> (hypo,0)
    | otherwise     ->
        let height = hypo / sinAngle
            width  = sqrt <| hypo^2 - height^2
        in
            (width,height)


---- functions which create and control the ship ----
----


type Ship = Destroyed GC.Form Time Time
          | Gone (Float,Float)
          | Ship GC.Form Velocity Acceleration
          | Invincible Ship Blink
          | Shooting Ship Time Time


shipLineStyle : GC.LineStyle
shipLineStyle = 
    let ls = GC.defaultLine
    in
        { ls | width <- 2 / 3, color <- Color.white }


newShip : (Float,Float) -> Ship
newShip (x,y) = 
    let form       = overflowMove (x,y) shipForm
        ship       = Ship form (0,form.theta) 0
        blink      = Normal 0 0.3 3
    in
        Invincible ship blink


formFromShip : Ship -> GC.Form
formFromShip ship = case ship of
    Destroyed form _ _   -> form
    Gone _               -> GC.toForm empty
    Ship form _ _        -> form
    Invincible s _       -> formFromShip s
    Shooting s _ _       -> formFromShip s


explodingShip : Ship -> Time -> Ship
explodingShip ship delta = case ship of
    Destroyed form elapsed end -> 
        let newT = delta + elapsed 
        in 
            if  | newT > end -> Gone (form.x,form.y)
                | otherwise  -> 
                    let ratio   = (end - newT) / end
                        rotForm = GC.rotate (delta * 2 * pi) form
                        seeThru = GC.alpha ratio rotForm
                        shrink  = GC.scale ratio seeThru
                    in
                        Destroyed shrink newT end
    _                          -> ship


hitShip : Ship -> Ship
hitShip ship = case ship of
    Invincible inShip blink -> ship
    Shooting inShip p e     -> hitShip inShip
    Ship form vel angV      -> Destroyed form 0 6
    _                       -> ship


shipAlpha : Float -> Ship -> Ship
shipAlpha opacity s = case s of
    Destroyed form el end   -> Destroyed (GC.alpha opacity form) el end
    Gone pos                -> Gone pos
    Invincible ship b       -> Invincible (shipAlpha opacity ship) b
    Ship form v a           -> Ship (GC.alpha opacity form) v a
    Shooting ship el end    -> Shooting (shipAlpha opacity ship) el end


-- invincible ships need to blink!! Duh!
flickerShip : Ship -> Time -> Ship
flickerShip s delta = case s of
    Invincible ship blink -> 
        let (time,freq,end) = case blink of { Normal p f e    -> (p,f,e) 
                                            ; Alternate p f e -> (p,f,e) }
            newT            = delta + time
            newElapsed      = newT - freq
            newEnd          = end - freq
        in
            if  | newT > end     -> shipAlpha 1 ship
                | newT > freq -> case blink of
                    Normal _ _ _    -> Invincible (shipAlpha 0.2 ship) (Alternate newElapsed freq newEnd)
                    Alternate _ _ _ -> Invincible (shipAlpha  1  ship) (Normal    newElapsed freq newEnd)
                | otherwise      -> case blink of
                    Normal _ _ _    -> Invincible ship (Normal    newT freq end)
                    Alternate _ _ _ -> Invincible ship (Alternate newT freq end)
    _                     -> s


-- creates the form that makes the ship we know and love
shipForm : GC.Form
shipForm = 
    let line       = shipLineStyle
        base       = toFloat 20 / 27
        side       = base * 7.5
        top        = base * 5
        xIntersect = base * -5
        yIntersect = base * 4 
    in
        GC.outlined line <| GC.polygon
            [ (side,0)
            , (-side,top)
            , (xIntersect,yIntersect)
            , (xIntersect,-yIntersect)
            , (-side,-top)
            ]


-- rotates ship, accelerating and decelerating based on fancy measurements
rotateShip : Ship -> Int -> Time -> Ship
rotateShip ship b delta = case ship of
    Invincible inShip blink     -> Invincible (rotateShip inShip b delta) blink
    Shooting inShip elapsed end -> Shooting (rotateShip inShip b delta) elapsed end
    Ship form vel angV          -> if
        | b == 0    ->
            let slowFast = if abs angV > pi / 4 then 2 else 1
                thetaAdj = clamp 0 (pi * 8 / 7) <| abs angV - delta * slowFast
                newTheta = if angV < 0 then -thetaAdj else thetaAdj
                newForm  = GC.rotate newTheta form
            in
                Ship newForm vel newTheta
        | otherwise ->
            let newTheta = clamp (-pi * 8 / 7) (pi * 8 / 7) <| angV - delta * 4 * pi / 20 * toFloat b
                newForm  = GC.rotate newTheta form
            in
                Ship newForm vel newTheta
    _                           -> ship


-- propels the ship forward and slows it down appropriately using the magic of polar coordinate conversions
-- max speed is 2 full travels across the screen per second
-- accelerates and decelerates more slowly at slower speeds for better control
moveShip : Ship -> Int -> Time -> Ship
moveShip ship up delta = case ship of
    Invincible inShip blink     -> Invincible (moveShip inShip up delta) blink
    Shooting inShip elapsed end -> Shooting   (moveShip inShip up delta) elapsed end
    Ship form (vel,vTheta) angV -> if
        | abs angV > pi -> Ship form (0,form.theta) angV
        | up < 1        ->
            let decel   = if vel > 220 then 60 else if vel > 150 then 50 else 40
                newVel  = max 0 (vel - decel)
                newAng  = if newVel == 0 then form.theta else vTheta
                pos     = fromPolar (delta * newVel, newAng)
                newForm = overflowMove pos form
            in
                Ship newForm (newVel,newAng) angV
        | otherwise     ->
            let accel   = if vel > 220 then 40 else 20
                (aX,aY) = fromPolar (accel, form.theta)
                (vX,vY) = fromPolar (vel, vTheta)
                (pV,pT) = toPolar (vX + aX, vY + aY)
                newVel  = (min 330 pV, pT)
                (mX,mY) = fromPolar newVel
                newForm = overflowMove (delta * mX, delta * mY) form
            in
                Ship newForm newVel angV
    _                           -> ship



-- given a ship, makes sure it runs
updateShip : Ship -> Int -> Int -> Time -> Ship
updateShip ship turn up delta = case ship of
    Destroyed _ _ _             -> explodingShip ship delta
    Gone _                      -> ship
    Invincible inShip blink     -> flip flickerShip delta 
        <| flip Invincible blink
        <| updateShip inShip turn up delta
    Ship _ _ _                  -> moveShip (rotateShip ship turn delta) up delta
    Shooting inShip elapsed end -> 
        let newT = delta + elapsed
            newS = moveShip (rotateShip inShip turn delta) up delta
        in
            if  | newT > end -> newS
                | otherwise  -> Shooting newS newT end


isInvincible : Ship -> Bool
isInvincible ship = case ship of { Invincible _ _ -> True ; _ -> False }


isGone : Ship -> Bool
isGone ship = case ship of { Gone _ -> True ; _ -> False }


isDestroyed : Ship -> Bool
isDestroyed ship = case ship of { Destroyed _ _ _ -> True ; _ -> False }


shipPosition : Ship -> (Float,Float)
shipPosition ship = case ship of
    Destroyed form _ _   -> (form.x,form.y)
    Gone pos             -> pos
    Invincible inShip _  -> shipPosition inShip
    Ship form _ _        -> (form.x,form.y)
    Shooting inShip _ _  -> shipPosition inShip


---- functions which control and draw asteroids ----
----


type Asteroid = Eliminated
              | Asteroid GC.Form Layers Velocity
type Blink    = Normal Time Time Time
              | Alternate Time Time Time

asteroidLineStyle : GC.LineStyle
asteroidLineStyle = 
    let ls = GC.defaultLine
    in
        { ls | width <- 1 / 3, color <- Color.white }


-- time is used to generate the points randomly
newAsteroid : Time -> (Float,Float) -> Layers -> Asteroid
newAsteroid time pos layer =
    let vertices = 2 * layer + 10
        points   = asteroidVertices time layer vertices (2 * pi / toFloat vertices)
        form     = overflowMove (fromPolar pos) <| GC.outlined asteroidLineStyle <| GC.polygon points
        vel      = thetaVelo (128 * time) layer
    in
        Asteroid form layer vel


thetaVelo : Time -> Layers -> Velocity
thetaVelo time layer = 
    let seed  = Random.initialSeed <| truncate time + layer
        angle = fst <| Random.generate (Random.float 0 (2 * pi)) seed
        (n,x) = (6 * (4 - toFloat layer), 8 * (4 - toFloat layer))
        speed = fst <| Random.generate (Random.float n x) seed 
    in
        (speed,angle)


formFromAsteroid : Asteroid -> GC.Form
formFromAsteroid ast = case ast of
    Eliminated        -> GC.toForm empty
    Asteroid form _ _ -> form


asteroidVertices : Time -> Layers -> Int -> Float -> List (Float,Float)
asteroidVertices time layer pointsLeft shift = 
    case pointsLeft of
        0 -> []
        _ ->
            let seed   = Random.initialSeed (truncate time + pointsLeft)
                innerR = 200 / 71 * toFloat layer
                outerR = 200 / 41 * toFloat layer
                radius = fst <| Random.generate (Random.float innerR outerR) seed
                angle  = shift * toFloat pointsLeft + (fst <| Random.generate (Random.float 0 shift) seed) 
            in
                fromPolar (radius,angle) :: asteroidVertices (time ^ 2) layer (pointsLeft - 1) shift


moveAsteroid : Asteroid -> Time -> Asteroid
moveAsteroid ast delta = case ast of
    Asteroid form layer (pV,pT) ->
        let newPos  = fromPolar (delta * pV, pT)
            newForm = overflowMove newPos form
        in
            Asteroid newForm layer (pV,pT)
    _                             -> ast


asteroidDestruction : Asteroid -> List Asteroid
asteroidDestruction ast = case ast of
    Eliminated            -> []
    Asteroid form layer _ -> if
        | layer > 1 ->
            let delta = form.x * form.theta - form.y
                lays  = layer - 1
            in
                [ newAsteroid delta          (toPolar (form.x - 3, form.y + 3)) lays
                , newAsteroid (delta - 1000) (toPolar (form.x + 1, form.y))     lays
                ]
        | otherwise -> []


isEliminated : Asteroid -> Bool
isEliminated ast = case ast of { Eliminated -> True ; _ -> False }


layers : Asteroid -> Layers
layers ast = case ast of { Eliminated -> 0 ; Asteroid _ l _ -> l }


---- functions for creating and controlling the shots ----
----

type Shot = Faded
          | Shot GC.Form Velocity Time Time


fireShot : Ship -> Bool -> Time -> (Ship,Shot)
fireShot s shoot delta = if
    | shoot     -> case s of
        Ship form (vel,theta) angV   -> 
            let shotform = makeShotForm form 200
                shotVel  = vel + 120
                newShot  = Shot shotform (shotVel,form.theta) 0 0.5
                inShip   = Ship form (vel,theta) angV
                outShip  = Shooting inShip 0 0.1
            in
                (outShip,newShot)
        Invincible ship blink     ->
            let (newShip,shot) = fireShot ship shoot delta
                flickeringShip = flickerShip (Invincible newShip blink) delta 
            in
                (flickeringShip,shot)
        Shooting ship elapsed end -> if
            | delta + elapsed > end -> fireShot ship shoot delta
            | otherwise             -> (s,Faded)
        _                         -> (s,Faded)
    | otherwise -> (s,Faded)


makeShotForm : GC.Form -> Int -> GC.Form
makeShotForm ship size = 
    let (offX,offY) = fromPolar (toFloat size / 40, ship.theta)
        pos         = (ship.x + offX, ship.y + offY)
    in
        overflowMove pos
            <| GC.filled Color.white
            <| GC.square
            <| toFloat size / 200


moveShot : Shot -> Time -> Shot
moveShot shot delta = case shot of
    Faded                               -> Faded
    Shot form (vRad,vTheta) elapsed end -> 
        let newT = elapsed + delta
        in
        if  | newT > end  -> Faded
            | otherwise   -> 
                let newForm = flip overflowMove form <| fromPolar (vRad * delta,vTheta)
                in
                    Shot newForm (vRad,vTheta) newT end


formFromShot : Shot -> GC.Form
formFromShot shot = case shot of
    Faded           -> GC.toForm empty
    Shot form _ _ _ -> form


updateShots : List Shot -> Time -> List Shot
updateShots hs now = case hs of
    []    -> []
    x::xs -> case x of
        Faded -> updateShots xs now
        _     -> 
            let newShot = moveShot x now 
            in 
                case newShot of
                    Faded -> updateShots xs now
                    _     -> newShot :: updateShots xs now


addShot : Shot -> List Shot -> List Shot
addShot shot xs = case shot of
    Faded -> xs
    _     -> shot :: xs


isFaded : Shot -> Bool
isFaded shot = case shot of { Faded -> True ; _ -> False }

