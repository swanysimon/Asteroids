-- AsteroidDrawing.elm
----
-- Simon Swanson
-- part of final project
----

{-
    Module to run the actual gameplay of the game Asteroids
-}


module Asteroids where

import AsteroidModel    as A
import Collisions       as C
import Color
import Graphics.Collage as GC
import Graphics.Element (Element)
import Graphics.Element as GE
import Keyboard
import List             ((::))
import List             as L
import Random
import Signal           (Signal,(<~),(~))
import Signal
import Text             as T
import Time             (Time,every,fps,inSeconds,millisecond,second)
import Window


type alias State     = (GameState,CurrentLevel,LivesLeft,PointTotal)
type GameState       = GameOver
                     | Instructions Time Time
                     | Playing A.Ship (List A.Shot) (List A.Asteroid)
                     | Scoreboard
                     | StartScreen
type CurrentLevel    = Level Int
type LivesLeft       = Lives Int
type PointTotal      = Points Int

type alias Input     = { space:Space, up:Forward, turn:Turning, delta:Time }
type alias Forward   = Int
type alias Space     = Bool
type alias Turning   = Int

-- could've just used records for this but it's 4am so why not
type ShotsStroids    = ShotsStroids (List A.Shot) (List A.Asteroid) PointTotal


fromJust : Maybe a -> a
fromJust x = case x of { Just y -> y }


---- space object manipulation functions
----


scoreAsteroid : A.Asteroid -> Int
scoreAsteroid ast =
    let layers = A.layers ast
    in
        if  | layers == 1 -> 100
            | layers == 2 -> 50
            | layers == 3 -> 20
            | otherwise   -> 0


makeAsteroid : Int -> Time -> A.Asteroid
makeAsteroid layer time = 
    let seed   = Random.initialSeed <| truncate time
        xCoord = fst <| Random.generate (Random.float -90 90) seed
        yCoord = 90 - (fst <| Random.generate (Random.float 0 180) seed)
    in 
        if  | (fst <| toPolar (xCoord,yCoord)) < 70 -> 
                makeAsteroid layer (time + 1000)
            | otherwise                             ->
                A.newAsteroid (time + 500) (xCoord,yCoord) layer


makeAsteroids : List Int -> Time -> List A.Asteroid
makeAsteroids layers time = case layers of
    []    -> []
    x::xs -> makeAsteroid x time :: makeAsteroids xs (time + 500)


shipCollision : A.Ship -> List A.Asteroid -> PointTotal -> Maybe (A.Ship, A.Asteroid, PointTotal)
shipCollision ship asts (Points pt) = if
    | A.isInvincible ship -> Nothing
    | A.isDestroyed ship  -> Nothing
    | otherwise           -> case asts of
        []       -> Nothing
        ast::axs -> if
            | A.isEliminated ast -> shipCollision ship axs (Points pt)
            | otherwise          ->
                let form1 = A.formFromShip ship
                    form2 = A.formFromAsteroid ast
                    sbox  = C.formToBox form1
                    abox  = C.formToBox form2
                    point = scoreAsteroid ast
                in 
                    if  | C.collision form1 sbox form2 abox -> Just (ship, ast, Points (point + pt))
                        | otherwise                         -> shipCollision ship axs (Points pt)


shotCollision : A.Shot -> List A.Asteroid -> PointTotal -> Maybe (A.Shot, A.Asteroid, PointTotal)
shotCollision shot asts (Points pt) = if
    | A.isFaded shot -> Nothing
    | otherwise      -> case asts of
        []       -> Nothing
        ast::axs -> if
            | A.isEliminated ast -> shotCollision shot axs (Points pt)
            | otherwise          ->
                let form1 = A.formFromShot shot
                    form2 = A.formFromAsteroid ast
                    sbox  = C.formToBox form1
                    abox  = C.formToBox form2
                    point = scoreAsteroid ast
                in 
                    if  | C.collision form1 sbox form2 abox -> Just (shot,ast,Points (point + pt))
                        | otherwise                         -> shotCollision shot axs (Points pt)


shotCollisions : ShotsStroids -> ShotsStroids
shotCollisions (ShotsStroids shots asts (Points pt)) = case (shots,asts) of
    ([],_)    -> ShotsStroids shots asts (Points pt)
    (_,[])    -> ShotsStroids shots asts (Points pt)
    (x::xs,_) -> case shotCollision x asts (Points pt) of
        Nothing      -> ssCons x <| shotCollisions <| ShotsStroids xs asts (Points pt)
        Just (_,a,x) -> shotCollisions <| ShotsStroids xs (blowAsteroid a asts) x


ssCons : A.Shot -> ShotsStroids -> ShotsStroids
ssCons shot (ShotsStroids shots asts pt) = ShotsStroids (shot::shots) asts pt


blowAsteroid : A.Asteroid -> List A.Asteroid -> List A.Asteroid
blowAsteroid ast asts = L.foldl (\a ax -> 
    if (A.formFromAsteroid ast).form == (A.formFromAsteroid a).form 
        then L.append (A.asteroidDestruction a) ax 
        else a::ax) [] asts


runCollisions : A.Ship -> List A.Shot -> List A.Asteroid -> PointTotal -> (A.Ship, List A.Shot, List A.Asteroid, PointTotal)
runCollisions ship shots asts pt = 
    let (ShotsStroids xs ys np) = shotCollisions (ShotsStroids shots asts pt)
        collide                 = shipCollision ship ys np
    in
        case collide of
            Nothing      -> (ship,xs,ys,np)
            Just (_,a,x) -> (A.hitShip ship,xs,blowAsteroid a ys,x)


---- stateful functions
----


initState : State
initState = (StartScreen, Level 0, Lives 0, Points 0)


startLevel : CurrentLevel -> LivesLeft -> PointTotal -> Time -> State
startLevel (Level level) lives points delta = 
    let lev  = level + 1
        ship = A.newShip (0,0)
        asts = makeAsteroids (L.repeat (lev + 2) 3) (delta * toFloat level)
    in
        (Playing ship [] asts, Level lev, lives, points)


playState : Input -> State -> State
playState {space,up,turn,delta} (gs,lv,li,pt) = case gs of
    Playing ship shots asts ->
        let upShip                  = A.updateShip ship turn up delta
            (newShip,shot)          = A.fireShot upShip space delta
            allShot                 = flip A.updateShots delta <| A.addShot shot shots
            allAsts                 = L.map (flip A.moveAsteroid delta) asts
            (cShip,cShots,cAsts,np) = runCollisions newShip allShot allAsts pt
            upGame                  = Playing cShip cShots cAsts
        in
            (upGame,lv,li,np)
    _                       -> (gs,lv,li,pt)


upstate : Input -> State -> State
upstate ({space,up,turn,delta} as inputs) (gs,lv,Lives li,pt) = case gs of
    GameOver                 -> if
        | up == 1   -> (Scoreboard,lv,Lives li,pt)
        | otherwise -> (GameOver,lv,Lives li,pt)
    Instructions elapsed end -> 
        let newT = elapsed + delta
        in
            if  | space && up == -1 -> startLevel (Level 0) (Lives 3) (Points 0) delta
                | newT > end        -> startLevel (Level 0) (Lives 3) (Points 0) delta
                | otherwise         -> (Instructions newT end,lv,Lives li,pt)
    Scoreboard               -> if
        | up == -1  -> initState
        | otherwise -> (Scoreboard,lv,Lives li,pt)
    StartScreen              -> if
        | space     -> (Instructions 0 4,lv,Lives li,pt)
        | otherwise -> (gs,lv,Lives li,pt)
    Playing ship shots asts  -> case asts of
        [] -> startLevel lv (Lives li) pt delta
        _  -> if
            | A.isGone ship && li < 1 -> (GameOver,lv,Lives 0,pt)
            | A.isGone ship           -> 
                let newShip = A.newShip <| A.shipPosition ship
                    newLife = li - 1
                    howPlay = Playing newShip shots asts
                in
                    playState inputs (howPlay,lv,Lives newLife,pt)
            | otherwise               -> playState inputs (gs,lv,Lives li,pt) 


---- functions that draw the elements 'n' such
----


background : (Int,Int) -> Element
background (x,y) = GE.color Color.black <| GE.spacer (x - 1) (y - 1)


text : Float -> String -> Element
text size str = T.centered 
    <| T.color Color.white
    <| T.monospace
    <| T.height size
    <| T.fromString str


startScreen : (Int,Int) -> Element
startScreen (x,y) = 
    let size = min (x - 2) (y - 2)
        main = text (toFloat size / 10) "ASTEROIDS"
        word = text (toFloat size / 30) "SPACE TO PLAY"
    in
        GE.container (x - 1) (y - 1) GE.middle <| GE.flow GE.down [main,word]


instructionScreen : (Int,Int) -> Element
instructionScreen (x,y) = 
    let size  = min (x - 2) (y - 2)
        space = text (toFloat size / 25) "SPACE TO SHOOT"
        move  = text (toFloat size / 25) "UP TO MOVE FORWARD"
        turn  = text (toFloat size / 25) "LEFT AND RIGHT TO ROTATE"
    in
        GE.container (x - 1) (y - 1) GE.middle <| GE.flow GE.down [space,move,turn]


gameOverScreen : (Int,Int) -> State -> Element
gameOverScreen (x,y) (gs,lv,li,Points pt) = 
    let size   = min (x - 2) (y - 2)
        main   = text (toFloat size / 10) "GAME OVER" 
        snark  = text (toFloat size / 30) "SUCKS TO SUCK"
        points = text (toFloat size / 30) ("YOU SCORED " ++ toString pt ++ " POINTS") 
        tip    = text (toFloat size / 30) "PRESS UP"
    in
        GE.container (x - 1) (y - 1) GE.middle <| GE.flow GE.down [main,snark,points,tip]


-- this is where I would have a sweet scoreboard with top scores
-- and the option to enter in your 3 letter name for everyone to see
-- but alas...
scoreEntry : (Int,Int) -> State -> Element
scoreEntry (x,y) (gs,lv,li,pt) = 
    let size = min (x - 2) (y - 2)
        main = text (toFloat size / 20) "ENTER YOUR NAME"
        lame = text (toFloat size / 20) "DON'T KNOW HOW?"
        boom = text (toFloat size / 30) "NEITHER DO I!"
        tip  = text (toFloat size / 30) "PRESS DOWN"
    in
        GE.container (x - 1) (y - 1) GE.middle <| GE.flow GE.down [main,lame,boom,tip]


playingView : (Int,Int) -> GameState -> LivesLeft -> PointTotal -> Element
playingView (x,y) (Playing ship shots asts) (Lives lives) (Points pt) = 
    let size    = min x y
        adjSize = toFloat size / 8 * 7
        colSize = truncate adjSize

        life    = L.repeat lives 
            <| GC.collage (colSize // 30) (colSize // 15)
            [GC.rotate (pi / 2)
                <| GC.scale (toFloat size / 400)
                <| A.formFromShip 
                <| A.newShip (0,0)]
        points  = text (toFloat size / 20) (toString pt)
        status  = GE.flow GE.down [points, GE.flow GE.right life]
        contain = GE.container colSize (y - 1) GE.topLeft status
        bigCont = GE.container (x - 1) (y - 1) GE.middle contain

        group   = GC.scale (adjSize / 200)
            <| GC.group 
            <| A.formFromShip ship
                :: L.append 
                (L.map A.formFromShot shots)
                (L.map A.formFromAsteroid asts)
        collage = GC.collage colSize colSize [group]
        colCont = GE.container (x - 1) (y - 1) GE.middle collage
    in
        GE.layers [bigCont,colCont]


view : (Int,Int) -> State -> Element
view (x,y) (gs,lv,li,pt) = 
    let back = background (x,y)
    in
        case gs of
            GameOver      -> GE.layers [back, gameOverScreen (x,y) (gs,lv,li,pt)]
            Scoreboard    -> GE.layers [back, scoreEntry (x,y) (gs,lv,li,pt)]
            StartScreen   -> GE.layers [back, startScreen (x,y)]
            Playing _ _ _ -> GE.layers [back, playingView (x,y) gs li pt]
            _             -> GE.layers [back, instructionScreen (x,y)]


---- Signal-based functions
----


ticker : Signal Float
ticker = inSeconds <~ fps 30


inputs : Signal Input
inputs = Signal.sampleOn ticker 
    <| Input 
        <~ Keyboard.space 
        ~ (.y <~ Keyboard.arrows)
        ~ (.x <~ Keyboard.arrows)
        ~ ticker


manageGameState : Signal State
manageGameState = Signal.foldp upstate initState inputs


main : Signal Element
main = Signal.map2 view Window.dimensions manageGameState
