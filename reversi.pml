mtype:AutomatableGameState = { GMReady, GMCompleted }
mtype:AutomatableGameCommand = { GMPass, GMPlace, GMReset }
// mtype:AutomatorProgress = { APWorking, APSleeping }

// 60 = 8x8-4
#define MAX_GAME_LIFE 3
chan gameStateDidChange = [1] of { mtype:GameState }
chan gameCommandDidAccept = [1] of { mtype:GameCommand }
chan gameCommandQueue = [1] of { mtype:GameCommand }
// chan automatorDidProgress = [0] of { mtype:AutomatorProgress }


inline runDispatchWorkItem(remainedGameLife, gameState, gameCommand, acceptedGameCommand, boardAnimationState, boardAnimationCommand, animatedGameState, animatedGameCommand) {
	if
	:: nempty(gameCommandQueue) && empty(gameStateDidChange) && empty(gameCommandDidAccept) && gameState == GMCompleted ->
		gameCommandQueue?gameCommand

		if
		:: gameCommand == GMPass -> skip
		:: gameCommand == GMPlace -> skip
		:: gameCommand == GMReset ->
			remainedGameLife = MAX_GAME_LIFE
			gameState = GMReady
			gameStateDidChange!gameState
			gameCommandDidAccept!GMReset
		:: else -> assert(false)
		fi

	:: nempty(gameCommandQueue) && empty(gameStateDidChange) && empty(gameCommandDidAccept) && gameState == GMReady ->
		gameCommandQueue?gameCommand

		if
		:: gameCommand == GMPass ->
			if
			:: remainedGameLife > 1 ->
				gameState = GMReady
				gameStateDidChange!gameState
				gameCommandDidAccept!GMPass
			:: remainedGameLife <= 1 -> skip
			fi

		:: gameCommand == GMPlace ->
			if
			:: remainedGameLife > 0 ->
				remainedGameLife--
			  gameState = GMReady
				gameStateDidChange!gameState
				gameCommandDidAccept!GMPlace
			:: remainedGameLife == 0 ->
				remainedGameLife--
				gameState = GMCompleted
				gameStateDidChange!gameState
				gameCommandDidAccept!GMPlace
			// :: else -> skip
			fi

		:: gameCommand == GMReset ->
			remainedGameLife = MAX_GAME_LIFE
			gameState = GMReady
			gameStateDidChange!gameState
			gameCommandDidAccept!GMReset
		:: else -> assert(false)
		fi


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
		:: else -> assert(false)
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
		:: else -> assert(false)
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
			:: boardAnimationState = BAMNotAnimating
			fi
			boardAnimationStateDidChange!boardAnimationState
		:: boardAnimationCommand == BAMMarkSyncAsCompleted -> skip
		:: else -> assert(false)
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
		:: else -> assert(false)
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
			:: else -> assert(false)
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
			:: else -> assert(false)
			fi
		:: else -> assert(false)
		fi

		if
		:: animatedGameCommand == AGMPass -> skip
		:: animatedGameCommand == AGMPlace -> skip
		:: animatedGameCommand == AGMReset -> skip
		:: animatedGameCommand == AGMMarkAnimationAsCompleted ->
			boardAnimationCommandQueue!BAMMarkAnimationAsCompleted
		:: animatedGameCommand == AGMMarkSyncAsCompleted ->
			boardAnimationCommandQueue!BAMMarkSyncAsCompleted
		:: else -> assert(false)
		fi

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
		:: else -> assert(false)
		fi
	fi
}


active proctype ModelsOnSameSerialDispatchQueue() {
	mtype:GameState gameState
	mtype:GameCommand gameCommand
	mtype:GameCommand acceptedGameCommand
	mtype:BoardAnimationState boardAnimationState
	mtype:BoardAnimationCommand boardAnimationCommand
	mtype:AnimatedGameState animatedGameState
	mtype:AnimatedGameCommand animatedGameCommand
	int remainedGameLife = 60

	gameState = GMReady
	gameStateDidChange!GMReady

	boardAnimationState = BAMNotAnimating
	boardAnimationStateDidChange!boardAnimationState

	animatedGameStateFrom(gameState, boardAnimationState, animatedGameState)
	animatedGameStateDidChange!animatedGameState

	end: do
	:: runDispatchWorkItem(
			remainedGameLife,
			gameState,
			gameCommand,
			acceptedGameCommand,
			boardAnimationState,
			boardAnimationCommand,
			animatedGameState,
			animatedGameCommand
		)
	od
}


active proctype AnyView() {
	mtype:AnimatedGameState animatedGameState
	end: do
	:: animatedGameStateDidChange?animatedGameState
	//:: animatedGameCommandQueue!AGMPass
	:: animatedGameCommandQueue!AGMPlace
	//:: animatedGameCommandQueue!AGMReset
	:: animatedGameCommandQueue!AGMMarkAnimationAsCompleted
	:: animatedGameCommandQueue!AGMMarkSyncAsCompleted
	od
}


// never  {    /* [](empty(animatedGameStateDidChange) || !animatedGameStateDidChange?[AGMCompleted]) */
// accept_init:
// T0_init:
// 	do
// 	:: ((empty(animatedGameStateDidChange) || !animatedGameStateDidChange?[AGMCompleted])) -> goto T0_init
// 	od;
// }
