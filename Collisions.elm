-- Collisions.elm
----
-- Simon Swanson
-- part of final project
----

{-
    Module to determine whether two forms are overlapping
    In the case of a game, this would be called a 
    "collision"
-}
module Collisions (Box, formToBox, collision) where


import Graphics.Collage as GC
import List             ((::))
import List             as L


type alias Box   = (Point,Point)
type alias Line  = Box
type alias Point = (Float,Float)



collision : GC.Form -> Box -> GC.Form -> Box -> Bool
collision form1 box1 form2 box2 = if
    | boundingBoxIntersect box1 box2 -> formsOverlap form1 form2 box2
    | otherwise                      -> False


formsOverlap : GC.Form -> GC.Form -> Box -> Bool
formsOverlap form1 form2 bx = 
    let ps1 = pointsOfForm form1
        ps2 = pointsOfForm form2
    in 
        case ps2 of
            []    -> False
            p::ps -> 
                let bxs = makeBoxes p ps2
                in
                    if  | checkPoints ps1 bx bxs -> True
                        | otherwise              -> case ps1 of
                            []    -> False
                            p::ps -> 
                                let bxs1 = makeBoxes p ps1 
                                in
                                    checkLines bxs1 bxs



checkPoints : List Point -> Box -> List Box -> Bool
checkPoints ps b bs = L.foldl (\p q -> q || pointLiesInShape p b bs) False ps


checkLines : List Line -> List Line -> Bool
checkLines xs ys = L.foldl ((||)) False <| L.concatMap (\x -> L.map (linesIntersect x) ys) xs


formToBox : GC.Form -> Box
formToBox form = case boxFromPoints <| pointsOfForm form of
    Nothing                -> ((form.x,form.y),(form.x,form.y))
    Just ((x1,y1),(x2,y2)) -> ((x1 + form.x, y1 + form.y),(x2 + form.x, y2 + form.y))


-- not entirely sure how to handle the FElement case...
pointsOfForm : GC.Form -> List Point
pointsOfForm f = case f.form of
    GC.FElement e         -> []
    GC.FImage w h (x,y) _ -> 
        let xDiff = w // 2
            yDiff = h // 2
            adjX  = rem w 2
            adjY  = rem h 2
            xMin  = toFloat <| x - xDiff - adjX
            yMin  = toFloat <| y - yDiff - adjY
            xMax  = toFloat <| x + xDiff
            yMax  = toFloat <| y + yDiff 
        in
            [(xMin,yMin),(xMin,yMax),(xMax,yMax),(xMax,yMin)]
    GC.FGroup _ fs        -> L.concat <| L.map pointsOfForm fs
    GC.FPath _ ps         -> ps
    GC.FShape _ ps        -> ps


---- functions for building boxes
----

makeBoundingBox : Box -> List Point -> Box
makeBoundingBox ((x1,y1),(x2,y2)) fs = case fs of
    []         -> ((x1,y1),(x2,y2))
    (x,y)::fs' -> 
        let newX1 = min x x1
            newX2 = max x x2
            newY1 = min y y1
            newY2 = max y y2 
        in
            makeBoundingBox ((newX1,newY1),(newX2,newY2)) fs'


boxFromPoints : List Point -> Maybe Box
boxFromPoints ps = case ps of
    []    -> Nothing
    x::xs -> Just <| makeBoundingBox (x,x) xs


boundingBoxIntersect : Box -> Box -> Bool
boundingBoxIntersect ((p1x,p1y),(p2x,p2y)) ((t1x,t1y),(t2x,t2y)) = 
    p1x <= t2x 
        && t1x <= p2x
        && p1y <= t2y
        && t1y <= p2y


---- functions for line intersections
----


crossProduct : Point -> Point -> Float
crossProduct (x1,y1) (x2,y2) = x1 * y2 - y1 * x2


modPointOnLine : Point -> Point -> Bool
modPointOnLine p1 p2 = (crossProduct p1 p2) == 0


modPointRightOfLine : Point -> Point -> Bool
modPointRightOfLine p1 p2 = (crossProduct p1 p2) < 0


lineSegmentsIntersect : Line -> Line -> Bool
lineSegmentsIntersect ((x1,y1),(x2,y2)) ((p1,t1),(p2,t2)) =
    let pt = (x2 - x1, y2 - y1)
        b1 = (p1 - x1, t1 - y1)
        b2 = (p2 - x1, t2 - y1) 
    in
        (modPointOnLine pt b1) 
            || (modPointOnLine pt b2) 
            || ((modPointRightOfLine pt b1) `xor` (modPointRightOfLine pt b2))


linesIntersect : Line -> Line -> Bool
linesIntersect b1 b2 = if
    | boundingBoxIntersect b1 b2 -> lineSegmentsIntersect b1 b2 && lineSegmentsIntersect b2 b1
    | otherwise                  -> False


---- functions involving points in shapes
----


pointLiesInShape : Point -> Box -> List Box -> Bool
pointLiesInShape (x,y) ((x1,_),(x2,_)) xs = 
    let newPt   = (x + x2 - x1, y)
        crosses = pointIntersectionCount ((x,y),newPt) xs 
    in
        crosses % 2 == 1


pointIntersectionCount : Line -> List Line -> Int
pointIntersectionCount line xs = case xs of
    []    -> 0
    x::_  -> L.length
        <| L.filter ((==) False)
        <| L.map (linesIntersect line) xs


makeBoxes : Point -> List Point -> List Line
makeBoxes (x,y) ps = case ps of
    []                -> []
    [(a,b)]           -> 
        let (minX,maxX) = if x < a then (x,a) else (a,x)
            (minY,maxY) = if y < b then (y,b) else (b,y) 
        in
            [((minX,minY),(maxX,maxY))]
    (a,b)::(p,t)::ps' ->
        let (minX,maxX) = if p < a then (p,a) else (a,p)
            (minY,maxY) = if t < b then (t,b) else (b,t) 
        in
            ((minX,minY),(maxX,maxY)) :: makeBoxes (x,y) ((p,t)::ps')
