module Dominoes3 where

 {- play a 5's & 3's singles match between 2 given players
    play n games, each game up to 61
 -}
 
 import System.Random
 import Data.List
 import Debug.Trace
 import Data.List ((\\))
 
 type Dom = (Int,Int)
 -- with highest pip first i.e. (6,1) not (1,6)

 data DomBoard = InitBoard|Board Dom Dom History
                    deriving (Eq,Show)
 
 type History = [(Dom,Player,MoveNum)]
  
 -- History allows course of game to be reconstructed                                            
                                               
 data Player = P1|P2 -- player 1 or player 2
                  deriving (Eq,Show)
 
 data End = L|R -- left end or right end
                  deriving (Eq,Show)
 
 type MoveNum = Int

 type Hand = [Dom]
  
 -- the full set of Doms
 domSet :: [Dom]
 
 --28 doms in a set
 domSet = [(6,6),(6,5),(6,4),(6,3),(6,2),(6,1),(6,0),
                 (5,5),(5,4),(5,3),(5,2),(5,1),(5,0),
                       (4,4),(4,3),(4,2),(4,1),(4,0),
                             (3,3),(3,2),(3,1),(3,0),
                                   (2,2),(2,1),(2,0),
                                         (1,1),(1,0),
                                               (0,0)]
                                                                                         
 
 type Move = (Dom,End)
 --p1's score then p2's score
 type Scores = (Int,Int)
                                                                                              
 -- state in a game - p1's hand, p2's hand, player to drop, current board, scores 
 type GameState =(Hand,Hand,Player, DomBoard, Scores)
 
  {- DomsPlayer
    given a Hand, the Board, which Player this is and the current Scores
    returns a Dom and an End
    only called when player is not knocking
    made this a type, so different players can be created
 -}
 
 {- variables
     hand h
     board b
     player p
     scores s (for both players)
 -}
 type DomsPlayer = Hand->DomBoard->Player->Scores->(Dom,End)
 
 ------------------------------------------------------
 {-tactic framework-}
 
 runTactics :: DomsPlayer

 runTactics h b p s
  |winningMove/=((7,7),L)= winningMove
  |score59MoveStopWin/=((7,7),L)= score59MoveStopWin
  |domsThatStopWin/=[]= hsdPlayer domsThatStopWin b p s
  |score59Move/=((7,7),L)= score59Move
  |hsdUnlessOppScoresMore /=((7,7),L) = hsdUnlessOppScoresMore
  |drop /= ((7,7),L) = drop 
  |majority /= ((7,7),L) = majority 
--  |(highestKnockOff h b p s)/=((7,7),L)=highestKnockOff h b p s
  |otherwise = hsdPlayer h b p s
  where 
  drop = (firstDrop h b)
  majority =(playMajority h b)
  winningMove=moveThatWillWin h b p s
  domsThatStopWin=checkOpponentWin [] h h b p s
  score59MoveStopWin=moveScoring59 domsThatStopWin b p s
  score59Move=moveScoring59 h b p s
  hsdUnlessOppScoresMore=opponentDoesNotScoreMore h h b p s
  
 ------------------------------------------------------
  {-Play highest scoring unless can't knock it off
  if it is a dangerous dom (a double)-}
 
 --gets my highest scoring dom, checks if it is double, if its a double 
 --and i have atleast one more dom with the same pip value then play it 
 --otherwise return sentinel value
 highestKnockOff :: DomsPlayer
 highestKnockOff h b p s
  |(knocking handWithoutHighest b) =((7,7),L)
  |((length domswithval)>1) && double = ((d1,d2),e)
  |otherwise=hsdPlayer handWithoutHighest b p s
  where
  ((d1,d2),e)=hsdPlayer h b p s
  double = isDouble (d1,d2)
  domswithval=domsWithValue h d1
  handWithoutHighest=h \\ [(d1,d2)]
  
 ------------------------------------------------------
  {-Play highest scoring unless opponent can score more afterwards
  than player just scored-}
  
  --Simulates move of my highest scoring dom, then simulates move of
  --oppoennts highest scoring dom from his possible hand, if mine is not 
  --higher than return sentinel value else return move of my highest scoring
 opponentDoesNotScoreMore :: Hand->DomsPlayer
 opponentDoesNotScoreMore _ [] _ _ _ = ((7,7),L)
 opponentDoesNotScoreMore origHand (h:t) b p s
  |knocking (h:t) b= ((7,7),L)
  |(myScore>opponentScore) = ((d1,d2),e)
  |otherwise= opponentDoesNotScoreMore origHand t b p s
  where
  ((d1,d2),e)=hsdPlayer (h:t) b p s 
  boardAfterMyPlay= updateBoard (d1,d2) e p b
  myScore=scoreboard boardAfterMyPlay
  opponent=getOpponentPlayer p
  opponenthand=opponentsPossHand origHand b
  ((d3,d4),e1)= hsdPlayer opponenthand boardAfterMyPlay opponent s
  boardAfterOpponentPlay= updateBoard (d3,d4) e1 opponent b
  opponentScore=scoreboard boardAfterOpponentPlay

 ------------------------------------------------------
 {-Prevent opponent winning on their next move-}
  
  --Rerurn a list of doms that i can play that wont result in opponent win
 checkOpponentWin :: Hand->Hand->Hand->DomBoard->Player->Scores->Hand
 checkOpponentWin newHand _ [] _ _ _ = newHand
 checkOpponentWin newHand origHand (h:t) b p s
  |(canOpponentWin h origHand b p s) =checkOpponentWin newHand origHand t b p s
  |otherwise=checkOpponentWin (newHand++[h]) origHand t b p s
  
 --Can opponent win if i place a particular piece
 canOpponentWin::Dom->Hand->DomBoard->Player->Scores->Bool
 canOpponentWin d h b p s
  --checks each possible opponnent piece left and right based on my play to see if opponent
  --can win
  |(goesLeft) && (opponentswindomsright==[]) && (opponentswindomsleft==[]) =False
  |(goesRight) && (goesLeft==False) && (opponentswindomsright==[]) =False
  |(goesLeft) && (goesRight) && (opponentswindomsright==[]) && (opponentswindomsleft==[])=False
  |otherwise=True
  where
  goesLeft= goesLP d b
  goesRight=goesRP d b
  opponenthand=opponentsPossHand h b
  opponent=getOpponentPlayer p
  --simulating opponent playing his doms on the domboard after my play, and get lists of
  --any of his winning doms
  opponentswindomsleft= getwindom [] opponenthand (playleft p d b) opponent s
  opponentswindomsright= getwindom [] opponenthand (playright p d b) opponent s
  
 --Gets a list of doms that will win from a hand based on a domboard
 getwindom ::Hand->Hand->DomBoard->Player->Scores->Hand
 getwindom newHnd [] _ _ _ =newHnd
 getwindom newHnd (h:t) brd plyr scores
  |scoringmove/=((7,7),L) = getwindom (newHnd++[h]) t brd plyr scores
  |otherwise=getwindom newHnd t brd plyr scores
  where
  playersScore=getPlayerScore plyr scores
  scoreRequired=scoreToWin playersScore
  scoringmove=moveThatWillScore scoreRequired [h] brd plyr scores
 
 --Gets the opponent player
 getOpponentPlayer:: Player->Player
 getOpponentPlayer P1 =P2
 getOpponentPlayer P2 =P1

 --returns the score of the opponent
 getOpponentScore :: Player->Scores->Int
 getOpponentScore plyr (s1,s2)
  |plyr==P1=s2
  |plyr==P2=s1
 ------------------------------------------------------
 {-Can I win? -}
 
 --get move of a winning dom
 moveThatWillWin :: DomsPlayer
 moveThatWillWin hnd brd plyr scores = 
  let 
   playersScore=getPlayerScore plyr scores
   scoreRequired=scoreToWin playersScore
  in 
   moveThatWillScore scoreRequired hnd brd plyr scores
  
 --Gets move of first dom from a hand that will score a specific score
 moveThatWillScore :: Int->DomsPlayer
 moveThatWillScore _ [] _ _ _ = ((7,7),L)
 --recurses through all doms in a hand to check for win left and right
 moveThatWillScore scoreReq (h:t) brd plyr scores
  |(goesLeft)&&((scoreboard (playleft plyr h brd))==scoreReq) =(h,L)
  |(goesRight)&&((scoreboard (playright plyr h brd))==scoreReq) =(h,R)
  |otherwise=moveThatWillScore scoreReq t brd plyr scores
  where
  goesLeft=goesLP h brd
  goesRight=goesRP h brd
 
 --Gets the score required to win
 scoreToWin :: Int->Int
 scoreToWin scr = 61 - scr
 
 --Returns the score of the player
 getPlayerScore :: Player->Scores->Int
 getPlayerScore plyr (s1,s2)
  |plyr==P1=s1
  |plyr==P2=s2
  
 ------------------------------------------------------
 {-Can I reach a score of 59? 
 good score to reach since there are many more ways of scoring a 2
 than 1, 3 or 4 -}
 
 --get move of dom that will score 59
 moveScoring59 :: DomsPlayer
 moveScoring59 hnd brd plyr scores = 
  let 
   playersScore=getPlayerScore plyr scores
   scoreRequired=scoreTo59 playersScore
  in 
   moveThatWillScore scoreRequired hnd brd plyr scores
 
 --Gets the score required to reach 59
 scoreTo59 :: Int->Int
 scoreTo59 scr = 59 - scr
 
 ------------------------------------------------------
 {-Plays optimal scoring (5,4) dominoe if player has first go,
 when playing this doms the score gained when placing is greater than any 
 possible response the opponent can play-}
 
 firstDrop :: Hand->DomBoard-> Move
 firstDrop [] _ = ((7,7),L)
 firstDrop (h:t) b
  |(h==(5,4)) && (b==InitBoard) = (h,L)
  |otherwise = firstDrop t b
  
 ------------------------------------------------------
 {-Calculate Possible Opponents hand
 Takes into account what a player was knocking on in the past
 what has been played and what is in players hand-} 
 
 --Builds the opponents possible hand based on what is in my hand, what has been played
 --and when the opponent was knocking in the past
 opponentsPossHand :: Hand->DomBoard->Hand
 opponentsPossHand hnd brd= domSet \\ (((hnd++domsOnBoard)++boardReversed)++domsknockingon)
  where
  history=getHistory brd
  domsOnBoard=domsInHistory history []
  boardReversed=reverseHand domsOnBoard []
  --uses the values that the opponent is knocking on to remove all related dominoes from
  --possible opponents hand by getting those doms from the domset
  (d1,d2)=endvalsKnockingOn history
  domsWithd1=domsWithValue domSet d1
  domsWithd2=domsWithValue domSet d2
  --list of all doms player cant have because they were knocking on those values
  domsknockingon=domsWithd1++domsWithd2
  
 --flips the spot values of all the doms in hand/board
 reverseHand ::Hand->Hand->Hand
 reverseHand [] h =h
 reverseHand (h:t) reversedhnd =reverseHand t handreversed
  where
  flipped=reverseDom h
  handreversed=reversedhnd++[flipped]
  
 --flips a dom 
 reverseDom:: Dom->Dom
 reverseDom (d1,d2) = (d2,d1)
 
 ------------------------------------------------------
 {-Calculating what numbers opponent is knocking on 
 when opposite player knocks for first time in history-} 
 
 --Sort algorithm to sort the history by movenumber
 sortGT :: Ord c => (a,b,c) -> (a,b,c) -> Ordering
 sortGT (a1,b1,c1) (a2,b2,c2) = 
  case compare c1 c2 of
    EQ -> compare c1 c2
    LT -> GT
    GT -> LT

 --sorts History by MoveNumber
 sortHistory :: History ->History
 sortHistory his =sLis
  where
  --sorts using algorithm above
  sLis= reverse (sortBy sortGT his)
  
 --gets history of when player was knocking 
 knockingOn :: History -> History
 knockingOn []=[]
 knockingOn [_]=[]
 --calcualtes when played was knocking if in sorted history by movenumber, two consecutive moves
 --were made by the same player, therefore the player was knocking at that point
 knockingOn (h:t)
   |plyr==plyr1 =[h]
   |otherwise=knockingOn t
  where
  ((_,_),plyr,_)=h
  ((_,_),plyr1,_)=head t
  
 --gets the movenumber of when opponent was knocking 
 moveKnockingOn :: History->Int
 moveKnockingOn [((_,_),_,move)] =move
 
 --given the movenumber of when player is knocking reconstruct history of when they
 --were knocking exactly
 reconstructHistory :: History->Int->History
 reconstructHistory his n =list
  where
  list=filter (\((_,_),_,move) -> (move<n+1)) his 
 
 --reconstruct the board using the reconstructed history which is the history
 --before the player was knocking 
 constructBoard :: History->Hand->Hand
 constructBoard [] brd =brd
 constructBoard (((d1,d2),_,_):t) brd
  |(brd==[])=constructBoard t [(d1,d2)]++brd
  |(d1==rightendbrd)= constructBoard t (brd++[(d1,d2)])
  |(d2==leftendbrd)= constructBoard t ((d1,d2):brd)
  |otherwise= constructBoard t brd
  where
  leftendbrd=fst (head brd)
  rightendbrd=snd (last brd)
 
 --produces the end values of what the opposite player is knocking on
 --sentinel value returned if they were not knocking in history
 endvalsKnockingOn ::History ->(Int,Int)
 endvalsKnockingOn [] = (7,7)
 endvalsKnockingOn [_] = (7,7)
 --gets end values player was knocking on by taking the end values of the 
 --reconstructed board of the reconstructed history of when opponent was
 --knocking
 endvalsKnockingOn his 
  |hisKnockingOn==[]=(7,7)
  |otherwise =(leftendbrd,rightendbrd)
  where
  sortedHis=sortHistory his
  hisKnockingOn=knockingOn sortedHis
  moveKnocking=moveKnockingOn hisKnockingOn
  reconstructed=reconstructHistory sortedHis moveKnocking
  reconstructedBrd=constructBoard reconstructed []
  leftendbrd=fst (head reconstructedBrd)
  rightendbrd=snd (last reconstructedBrd)
  
 ------------------------------------------------------
 {-Do i have a mojority of one spot value?
  If so play one of them doms, if double is there play that first-}
 
 --Returns move of highest scoring dom if player has a majority of 
 --one spot value from list of majority
 playMajority :: Hand ->DomBoard->Move
 playMajority h b
  |knocking (majorityList) b = ((7,7),L)
  --if no double play highest scoring from majority list
  |(knocking double b) =(d,e)
  --if dom in majority list scores higher than the double in the majority list
  --then play that, depends if there is a double in the majority list
  |(s>s1)=(d1,e1)
  |otherwise = (d,e)-- otherwise plays double from majority list
  where 
  (d,e,s) = hsd (majorityList) b
  majorityList=getmajoritylistfromhand h b
  double= getDouble majorityList
  (d1,e1,s1) = hsd double b --if there is double and it scores
 
 --Returns list of doms that are a majority of one spot value from a hand
 getmajoritylistfromhand :: Hand->DomBoard->Hand
 getmajoritylistfromhand h b
 --checks if i have a majority for each possible spot value, if i do have
 --majority for a spot value simply returns a list containig the doms with that value
 --that are in my hand
  |(isMajority h b 0) = domsWithValue h 0
  |(isMajority h b 1) = domsWithValue h 1
  |(isMajority h b 2) = domsWithValue h 2
  |(isMajority h b 3) = domsWithValue h 3
  |(isMajority h b 4) = domsWithValue h 4
  |(isMajority h b 5) = domsWithValue h 5
  |(isMajority h b 6) = domsWithValue h 6
  |otherwise =[]
  
 --Checks if a list of doms has a majority of one spot value
 --takes into account doms of a spot value played on the board 
 --when calculating if majority
 isMajority :: Hand->DomBoard->Int-> Bool
 isMajority h b n
  |(handDomsWithVal > 4) && (playedDomsWithVal==0) = True 
  |(handDomsWithVal > 3) && (playedDomsWithVal==1) = True 
  |(handDomsWithVal > 3) && (playedDomsWithVal==2) = True 
  |(handDomsWithVal > 2) && (playedDomsWithVal==3) = True 
  |(handDomsWithVal > 1) && (playedDomsWithVal==4) = True 
  |(handDomsWithVal > 1) && (playedDomsWithVal==5) = True 
  |(handDomsWithVal > 0) && (playedDomsWithVal==6) = True
  |otherwise = False
  where
   handDomsWithVal= length (domsWithValue h n)
   playedDomsWithVal=(domsInHistoryOfValue b n)
 
 --gets a list of doms from a hand that have a certain spot value
 domsWithValue :: Hand ->Int->Hand
 domsWithValue h n =list
  where
   list= filter (\d -> domContainval d n) h 
 
 --does a dom contain a spot value
 domContainval :: Dom->Int->Bool
 domContainval (d1,d2) n
  |(d1==n) || (d2==n) =True
  |otherwise = False
  
 --gets the number of doms with a spot value played on the board 
 domsInHistoryOfValue :: DomBoard->Int->Int
 domsInHistoryOfValue b n
  |history/=[]= numOfDomsWithVal
  |otherwise=0
  where
  history=getHistory b
  board= domsInHistory history []
  numOfDomsWithVal=length (domsWithValue board n)
  
 ------------------------------------------------------
 {-Miscellaneous functions-}
 
 --returns history from a domboard if there is one
 getHistory:: DomBoard ->History
 getHistory InitBoard = []
 getHistory (Board _ _ h)=h
  
 --gets a list of all the doms in the history by recursing through it
 domsInHistory:: History->Hand->Hand
 domsInHistory [] hnd = hnd
 domsInHistory (h:t) hnd = domsInHistory t hand
  where
  dom=getnextdomfromhistory [h]
  hand=hnd++[dom]
 
 --Returns first dom in history
 getnextdomfromhistory ::History->Dom
 getnextdomfromhistory [(d,_,_)] =dom
  where
  dom=d
 
 --checks if a dom is a double
 isDouble :: Dom -> Bool
 isDouble h
  |(d1==d2) = True
  |otherwise = False 
  where
  (d1,d2)=h
  
 --gets a double domino from a hand 
 getDouble :: Hand -> Hand
 getDouble h = filter (\d -> isDouble d) h
 ------------------------------------------------------
 
 {-PROVIDED FUNCTIONS BELOW HERE-}
 
 ------------------------------------------------------

 -- example players
 -- randomPlayer plays the first legal dom it can, even if it goes bust
 randomPlayer :: DomsPlayer
 
 randomPlayer h b p s 
  |not(null ldrops) = ((head ldrops),L)
  |otherwise = ((head rdrops),R)
  where
   ldrops = traceShow(b) leftdrops h b
   rdrops = traceShow(b) rightdrops h b
   
 -- hsdplayer plays highest scoring dom
 -- we have  hsd :: Hand->DomBoard->(Dom,End,Int)
 
 hsdPlayer h b p s = (d,e) 
                     where (d,e,_)=hsd h b
                     
  -- highest scoring dom

 hsd :: Hand->DomBoard->(Dom,End,Int)
 
 hsd h InitBoard = (md,L,ms)
  where
   dscores = zip h (map (\ (d1,d2)->score53 (d1+d2)) h)
   (md,ms) = maximumBy (comparing snd) dscores
   
 
 hsd h b = 
   let
    ld=  leftdrops h b
    rd = rightdrops h b
    lscores = zip ld (map (\d->(scoreDom d L b)) ld) -- [(Dom, score)]
    rscores = zip rd (map (\d->(scoreDom d R b)) rd)
    (lb,ls) = if (not(null lscores)) then (maximumBy (comparing snd) lscores) else ((0,0),-1) -- can't be chosen
    (rb,rs) = if (not(null rscores)) then (maximumBy (comparing snd) rscores) else ((0,0),-1)
   in
    if (ls>rs) then (lb,L,ls) else (rb,R,rs)
                                               
 -----------------------------------------------------------------------------------------
 {- top level fn
    args: 2 players (p1, p2), number of games (n), random number seed (seed)
    returns: number of games won by player 1 & player 2
    calls playDomsGames giving it n, initial score in games and random no gen
 -} 
 
 domsMatch :: DomsPlayer->DomsPlayer->Int->Int->(Int,Int)
 
 domsMatch p1 p2 n seed = playDomsGames p1 p2 n (0,0) (mkStdGen seed)
 
 -----------------------------------------------------------------------------------------
 
{- playDomsGames plays n games

  p1,p2 players
  (s1,s2) their scores
  gen random generator
-}
 
 playDomsGames :: DomsPlayer->DomsPlayer->Int->(Int,Int)->StdGen->(Int,Int)
 
 playDomsGames _ _ 0 score_in_games _ = score_in_games -- stop when n games played
 
 playDomsGames p1 p2 n (s1,s2) gen 
   |gameres==P1 = playDomsGames p1 p2 (n-1) (s1+1,s2) gen2 -- p1 won
   |otherwise = playDomsGames p1 p2 (n-1) (s1,s2+1) gen2 -- p2 won
  where
   (gen1,gen2)=split gen -- get 2 generators, so doms can be reshuffled for next hand
   gameres = playDomsGame p1 p2 (if (odd n) then P1 else P2) (0,0) gen1 -- play next game p1 drops if n odd else p2
 
 -----------------------------------------------------------------------------------------
 -- playDomsGame plays a single game - 61 up
 -- returns winner - P1 or P2
 -- the Bool pdrop is true if it's p1 to drop
 -- pdrop alternates between games
 
 playDomsGame :: DomsPlayer->DomsPlayer->Player->(Int,Int)->StdGen->Player
 
 playDomsGame p1 p2 pdrop scores gen 
  |s1==61 = P1
  |s2==61 = P2
  |otherwise = playDomsGame p1 p2 (if (pdrop==P1) then P2 else P1) (s1,s2) gen2
  where
   (gen1,gen2)=split gen
   (s1,s2)=playDomsHand p1 p2 pdrop scores gen1  
  
 -----------------------------------------------------------------------------------------
 -- play a single hand
  
 playDomsHand :: DomsPlayer->DomsPlayer->Player->(Int,Int)->StdGen->(Int,Int)
 
 playDomsHand p1 p2 nextplayer scores gen = 
   playDoms p1 p2 init_gamestate
  where
   spack = shuffleDoms gen
   p1_hand = take 9 spack
   p2_hand = take 9 (drop 9 spack)
   init_gamestate = (p1_hand,p2_hand,nextplayer,InitBoard,scores) 
   
 ------------------------------------------------------------------------------------------   
 -- shuffle 
 
 shuffleDoms :: StdGen -> [Dom]

 shuffleDoms gen =  
  let
    weights = take 28 (randoms gen :: [Int])
    dset = (map fst (sortBy  
               (\ (_,w1)(_,w2)  -> (compare w1 w2)) 
               (zip domSet weights)))
  in
   dset
   
 ------------------------------------------------------------------------------------------
 -- playDoms runs the hand
 -- returns scores at the end

 
 playDoms :: DomsPlayer->DomsPlayer->GameState->(Int,Int)
 
 playDoms _ _ (_,_,_,_, (61,s2)) = (61,s2) --p1 has won the game
 playDoms _ _ (_,_,_,_, (s1,61)) = (s1,61) --p2 has won the game
 
 
 playDoms p1 p2 gs@(h1,h2,nextplayer,b,scores)
  |(kp1 &&  kp2) = scores -- both players knocking, end of the hand
  |((nextplayer==P1) && (not kp1)) =  playDoms p1 p2 (p1play p1 gs) -- p1 plays, returning new gameState. p2 to go next
  |(nextplayer==P1) = playDoms p1 p2 (p2play p2 gs) -- p1 knocking so p2 plays
  |(not kp2) = playDoms p1 p2 (p2play p2 gs) -- p2 plays
  |otherwise = playDoms p1 p2 (p1play p1 gs) -- p2 knocking so p1 plays
  where
   kp1 = knocking h1 b -- true if p1 knocking
   kp2 = knocking h2 b -- true if p2 knocking
   
 ------------------------------------------------------------------------------------------
 -- is a player knocking?

 knocking :: Hand->DomBoard->Bool
 
 knocking h b = 
  ((null (leftdrops h b)) && (null (rightdrops h b))) -- leftdrops & rightdrops in doms.hs
 
 ------------------------------------------------------------------------------------------
   
 -- player p1 to drop
 
 p1play :: DomsPlayer->GameState->GameState
 
 p1play p1 (h1,h2,_,b, (s1,s2)) = 
  ((delete dom h1), h2, P2,(updateBoard dom end P1 b), (ns1, s2))
   where
    (dom,end) = p1 h1 b P1 (s1,s2)-- call the player, returning dom dropped and end it's dropped at.
    score = s1+ (scoreDom dom end b) -- what it scored
    ns1 = if (score >61) then s1 else score -- check for going bust
    
 
 -- p2 to drop
   
 p2play :: DomsPlayer->GameState->GameState
 
 p2play p2 (h1,h2,_,b,(s1,s2)) = 
  (h1, (delete dom h2),P1, (updateBoard dom end P2 b), (s1, ns2))
  where
   (dom,end) = p2 h2 b P2 (s1,s2)-- call the player, returning dom dropped and end it's dropped at.
   score = s2+ (scoreDom dom end b) -- what it scored
   ns2 = if (score >61) then s2 else score -- check for going bust
 
   -------------------------------------------------------------------------------------------
 -- updateBoard 
 -- update the board after a play
 
 updateBoard :: Dom->End->Player->DomBoard->DomBoard
 
 updateBoard d e p b
  |e==L = playleft p d b
  |otherwise = playright p d b

  ------------------------------------------------------------------------------------------
 -- doms which will go left
 leftdrops :: Hand->DomBoard->Hand
 
 leftdrops h b = filter (\d -> goesLP d b) h
 
 -- doms which go right
 rightdrops :: Hand->DomBoard->Hand
 
 rightdrops h b = filter (\d -> goesRP d b) h 
 
 -------------------------------------------------
 -- 5s and 3s score for a number
  
 score53 :: Int->Int
 score53 n = 
  let 
   s3 = if (rem n 3)==0 then (quot n 3) else 0
   s5 = if (rem n 5)==0 then (quot n 5) else 0 
  in
   s3+s5
   
 ------------------------------------------------ 
 -- need comparing
 -- useful fn specifying what we want to compare by
 comparing :: Ord b=>(a->b)->a->a->Ordering
 comparing f l r = compare (f l) (f r)
 
 ------------------------------------------------
 -- scoreDom
 -- what will a given Dom score at a given end?
 -- assuming it goes
 
 scoreDom :: Dom->End->DomBoard->Int
 
 scoreDom d e b = scoreboard nb
                  where
                  (Just nb) = (playDom P1 d e b) -- player doesn't matter
 
 ----------------------------------------------------                 
 -- play to left - it will go
 playleft :: Player->Dom->DomBoard->DomBoard
 
 playleft p (d1,d2) InitBoard = Board (d1,d2) (d1,d2) [((d1,d2),p,1)]
 
 playleft p (d1,d2) (Board (l1,l2) r h)
  |d1==l1 = Board (d2,d1) r (((d2,d1),p,n+1):h)
  |otherwise =Board (d1,d2) r (((d1,d2),p,n+1):h)
  where
    n = maximum [m |(_,_,m)<-h] -- next drop number
    
 -- play to right
 playright :: Player->Dom->DomBoard->DomBoard
 
 playright p (d1,d2) InitBoard = Board (d1,d2) (d1,d2) [((d1,d2),p,1)]
 
 playright p (d1,d2)(Board l (r1,r2) h)
  |d1==r2 = Board l (d1,d2) (h++[((d1,d2),p,n+1)])
  |otherwise = Board l (d2,d1) (h++[((d2,d1),p,n+1)])
  where 
    n = maximum [m |(_,_,m)<-h] -- next drop number
 
 ------------------------------------------------------
 -- predicate - will given domino go at left?
 -- assumes a dom has been played
 
 goesLP :: Dom->DomBoard->Bool
 
 goesLP _ InitBoard = True
 
 goesLP (d1,d2) (Board (l,_) _ _) = (l==d1)||(l==d2)


 -- will dom go to the right?
 -- assumes a dom has been played
 
 goesRP :: Dom->DomBoard->Bool
 
 goesRP _ InitBoard = True
 
 goesRP (d1,d2) (Board _ (_,r) _) = (r==d1)||(r==d2)
 
 ------------------------------------------------

 -- playDom
 -- given player plays
 -- play a dom at left or right, if it will go

 
 playDom :: Player->Dom->End->DomBoard->Maybe DomBoard
 
 playDom p d L b
   |goesLP d b = Just (playleft p d b)
   |otherwise = Nothing
 
 playDom p d R b
   |goesRP d b = Just (playright p d b)
   |otherwise = Nothing
   
 ---------------------------------------------------    
 -- 5s & threes score for a board
 
 scoreboard :: DomBoard -> Int
 
 scoreboard InitBoard = 0

 scoreboard (Board (l1,l2) (r1,r2) hist)
  |length hist == 1 = score53 (l1+l2) -- 1 dom played, it's both left and right end
  |otherwise = score53 ((if l1==l2 then 2*l1 else l1)+ (if r1==r2 then 2*r2 else r2))   