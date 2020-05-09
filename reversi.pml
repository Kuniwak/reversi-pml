mtype:GameModelState = { GMReady, GMCompleted }
mtype:AnimatedGameModelState = { AGMReady, AGMPlacing, AGMFlipping, AGMResetting, AGMCompleted }
mtype:AutomatorProgress = { APWorking, APSleeping }

chan gameStateDidChange = [0] of { mtype:GameModelState }
chan animatedGameDidChange = [0] of { mtype:AnimatedGameModelState }
chan automatorDidProgress = [0] of { mtype:AutomatorProgress }


active proctype GameModel() {
	mtype:GameModelState gameState = GMReady;
	gameStateDidChange!gameState;

	end: do
	:: gameState == GMCompleted -> skip;
	:: gameState != GMCompleted ->
		if
		:: gameState = GMReady;
		:: gameState = GMCompleted;
		fi
		gameStateDidChange!gameState;
	od
}


active proctype AnyGameModelObserver() {
	mtype:GameModelState gameState;
	end: do
	:: gameStateDidChange?gameState;
	od
}


never {
	do
	:: len(gameStateDidChange) > 0 -> gameStateDidChange?[GMReady];
	od
}
