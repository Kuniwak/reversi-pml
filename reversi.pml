mtype:GameState = { GMReady, GMCompleted }
mtype:GameCommand = { GMPass, GMPlace, GMReset }
mtype:BoardAnimationState = { BAMNotAnimating, BAMPlacing, BAMFlipping, BAMForceSyncing }
mtype:BoardAnimationCommand = { BAMPlace, BAMForceSync, BAMMarkAnimationAsCompleted, BAMMarkSyncAsCompleted }
mtype:AnimatedGameState = { AGMReady, AGMCompleted, AGMAnimating }
mtype:AnimatedGameCommand = { AGMPass, AGMPlace, AGMReset, AGMMarkAnimationAsCompleted, AGMMarkSyncAsCompleted }
// mtype:AutomatorProgress = { APWorking, APSleeping }

chan gameStateDidChange = [1] of { mtype:GameState }
chan gameCommandDidAccept = [1] of { mtype:GameCommand }
chan gameCommandQueue = [1] of { mtype:GameCommand }
chan boardAnimationStateDidChange = [1] of { mtype:BoardAnimationState }
chan boardAnimationCommandQueue = [1] of { mtype:BoardAnimationCommand }
chan animatedGameStateDidChange = [1] of { mtype:AnimatedGameState }
chan animatedGameCommandQueue = [1] of { mtype:AnimatedGameCommand }
// chan automatorDidProgress = [0] of { mtype:AutomatorProgress }



active proctype GameModel() {
	mtype:GameState gameState
	mtype:GameCommand gameCommand
	gameState = GMReady
	gameStateDidChange!GMReady

	end: do
	:: nempty(gameCommandQueue) && empty(gameStateDidChange) && empty(gameCommandDidAccept) && gameState == GMCompleted ->
		gameCommandQueue?gameCommand

		if
		:: gameCommand == GMPass -> skip
		:: gameCommand == GMPlace -> skip
		:: gameCommand == GMReset ->
			gameState = GMReady
			gameStateDidChange!gameState
			gameCommandDidAccept!GMReset
		fi

	:: nempty(gameCommandQueue) && empty(gameStateDidChange) && empty(gameCommandDidAccept) && gameState == GMReady ->
		gameCommandQueue?gameCommand

		if
		:: gameCommand == GMPass ->
			if
			:: gameState = GMReady
				gameStateDidChange!gameState
				gameCommandDidAccept!GMPass
			:: else -> skip
			fi

		:: gameCommand == GMPlace ->
			if
			:: gameState = GMReady
				gameStateDidChange!gameState
				gameCommandDidAccept!GMPlace
			:: gameState = GMCompleted
				gameStateDidChange!gameState
				gameCommandDidAccept!GMPlace
			:: else -> skip
			fi

		:: gameCommand == GMReset ->
			gameState = GMReady
			gameStateDidChange!gameState
			gameCommandDidAccept!GMReset
		fi
	od
}


active proctype BoardAnimationModel() {
	mtype:BoardAnimationState boardAnimationState
	mtype:BoardAnimationCommand boardAnimationCommand
	boardAnimationState = BAMNotAnimating
	boardAnimationStateDidChange!boardAnimationState

	end: do
	:: nempty(boardAnimationCommandQueue) && empty(boardAnimationStateDidChange) && boardAnimationState == BAMNotAnimating ->
		boardAnimationCommandQueue?boardAnimationCommand
		if
		:: boardAnimationCommand == BAMPlace ->
			boardAnimationState = BAMPlacing
			boardAnimationStateDidChange!boardAnimationState
		:: boardAnimationCommand == BAMForceSync ->
			boardAnimationState = BAMForceSyncing
			boardAnimationStateDidChange!boardAnimationState
		:: boardAnimationCommand == BAMMarkAnimationAsCompleted -> skip
		:: boardAnimationCommand == BAMMarkSyncAsCompleted -> skip
		fi

	:: nempty(boardAnimationCommandQueue) && empty(boardAnimationStateDidChange) && boardAnimationState == BAMPlacing ->
		boardAnimationCommandQueue?boardAnimationCommand
		if
		:: boardAnimationCommand == BAMPlace -> skip
		:: boardAnimationCommand == BAMForceSync ->
			boardAnimationState = BAMForceSyncing
			boardAnimationStateDidChange!boardAnimationState
		:: boardAnimationCommand == BAMMarkAnimationAsCompleted ->
			boardAnimationState = BAMFlipping
			boardAnimationStateDidChange!boardAnimationState
		:: boardAnimationCommand == BAMMarkSyncAsCompleted -> skip
		fi

	:: nempty(boardAnimationCommandQueue) && empty(boardAnimationStateDidChange) && boardAnimationState == BAMFlipping ->
		boardAnimationCommandQueue?boardAnimationCommand
		if
		:: boardAnimationCommand == BAMPlace -> skip
		:: boardAnimationCommand == BAMForceSync ->
			boardAnimationState = BAMForceSyncing
			boardAnimationStateDidChange!boardAnimationState
		:: boardAnimationCommand == BAMMarkAnimationAsCompleted ->
			if
			:: boardAnimationState = BAMFlipping
				boardAnimationStateDidChange!boardAnimationState
			:: boardAnimationState = BAMNotAnimating
				boardAnimationStateDidChange!boardAnimationState
			fi
		:: boardAnimationCommand == BAMMarkSyncAsCompleted -> skip
		fi

	:: nempty(boardAnimationCommandQueue) && empty(boardAnimationStateDidChange) && boardAnimationState == BAMForceSyncing ->
		boardAnimationCommandQueue?boardAnimationCommand
		if
		:: boardAnimationCommand == BAMPlace -> skip
		:: boardAnimationCommand == BAMForceSync ->
			boardAnimationState = BAMForceSyncing
			boardAnimationStateDidChange!boardAnimationState
		:: boardAnimationCommand == BAMMarkAnimationAsCompleted -> skip
		:: boardAnimationCommand == BAMMarkSyncAsCompleted ->
			boardAnimationState = BAMNotAnimating
			boardAnimationStateDidChange!boardAnimationState
		fi
	od
}


inline animatedGameStateFrom(gameState, boardAnimationState, animatedGameState) {
	d_step {
		if
		:: boardAnimationState == BAMNotAnimating ->
			if
			:: gameState == GMReady ->
				animatedGameState = AGMReady
			:: gameState == GMCompleted ->
				animatedGameState = AGMCompleted
			fi
		:: boardAnimationState == BAMPlacing ->
			animatedGameState = AGMAnimating
		:: boardAnimationState == BAMFlipping ->
			animatedGameState = AGMAnimating
		:: boardAnimationState == BAMForceSyncing ->
			animatedGameState = AGMAnimating
		fi
	}
}


active proctype AnimatedGameModel() {
	mtype:AnimatedGameState animatedGameState
	mtype:AnimatedGameCommand animatedGameCommand
	mtype:GameState gameState
	mtype:GameCommand acceptedGameCommand
	mtype:BoardAnimationState boardAnimationState

	gameStateDidChange?gameState
	boardAnimationStateDidChange?boardAnimationState
	animatedGameStateFrom(gameState, boardAnimationState, animatedGameState)
	animatedGameStateDidChange!animatedGameState
	
	end: do
	:: nempty(gameStateDidChange) && empty(animatedGameStateDidChange) ->
		gameStateDidChange?gameState
		animatedGameStateFrom(gameState, boardAnimationState, animatedGameState)
		animatedGameStateDidChange!animatedGameState

	:: nempty(boardAnimationStateDidChange) && empty(animatedGameStateDidChange) ->
		boardAnimationStateDidChange?boardAnimationState
		animatedGameStateFrom(gameState, boardAnimationState, animatedGameState)
		animatedGameStateDidChange!animatedGameState

	:: nempty(gameCommandDidAccept) && empty(boardAnimationCommandQueue) ->
		gameCommandDidAccept?acceptedGameCommand 
		if
		:: acceptedGameCommand == GMPass -> skip
		:: acceptedGameCommand == GMPlace ->
			boardAnimationCommandQueue!BAMPlace
		:: acceptedGameCommand == GMReset ->
			boardAnimationCommandQueue!BAMForceSync
		fi

	:: nempty(animatedGameCommandQueue) && empty(gameCommandQueue) && empty(boardAnimationCommandQueue) ->
			animatedGameCommandQueue?animatedGameCommand
			if
			:: animatedGameState == AGMReady ->
				if
				:: animatedGameCommand == AGMPass ->
					gameCommandQueue!GMPass
				:: animatedGameCommand == AGMPlace ->
					gameCommandQueue!GMPlace
				:: animatedGameCommand == AGMReset ->
					gameCommandQueue!GMReset
				:: animatedGameCommand == AGMMarkAnimationAsCompleted -> skip
				:: animatedGameCommand == AGMMarkSyncAsCompleted -> skip
				fi
			:: animatedGameState == AGMAnimating -> skip
			:: animatedGameState == AGMCompleted ->
				if
				:: animatedGameCommand == AGMPass ->
					gameCommandQueue!GMPass
				:: animatedGameCommand == AGMPlace ->
					gameCommandQueue!GMPlace
				:: animatedGameCommand == AGMReset ->
					gameCommandQueue!GMReset
				:: animatedGameCommand == AGMMarkAnimationAsCompleted -> skip
				:: animatedGameCommand == AGMMarkSyncAsCompleted -> skip
				fi
			fi

			if
			:: animatedGameCommand == AGMPass -> skip
			:: animatedGameCommand == AGMPlace -> skip
			:: animatedGameCommand == AGMReset -> skip
			:: animatedGameCommand == AGMMarkAnimationAsCompleted ->
				boardAnimationCommandQueue!BAMMarkAnimationAsCompleted
			:: animatedGameCommand == AGMMarkSyncAsCompleted ->
				boardAnimationCommandQueue!BAMMarkSyncAsCompleted
			fi
	od
}


active proctype AnyView() {
	mtype:AnimatedGameState animatedGameState
	end: do
	:: animatedGameStateDidChange?animatedGameState
	:: animatedGameCommandQueue!AGMPass
	:: animatedGameCommandQueue!AGMPlace
	:: animatedGameCommandQueue!AGMReset
	:: animatedGameCommandQueue!AGMMarkAnimationAsCompleted
	:: animatedGameCommandQueue!AGMMarkSyncAsCompleted
	od
}
