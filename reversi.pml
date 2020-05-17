mtype:Dest = { GameModelPlaceObserver, GameModelPassObserver, GameModelResetObserver, GameModelStateObserver }
mtype:GameModelState = { GameModelMustPass, GameModelMustPlace, GameModelCompleted }
chan dispatchQueue = [1] of { mtype:Dest }
chan dispatchQueueMain = [1] of { mtype:Dest }

#define INIT_GAME_LIFE 10
#define INIT_GameModel_STATE GameModelMustPass



active proctype DispatchQueueLoop() {
	int remainedGameLife = INIT_GAME_LIFE
	mtype:GameModelState gameModelState = INIT_GameModel_STATE

	end: do
	:: dispatchQueue?GameModelPlaceObserver ->
		if
		:: gameModelState == GameModelCompleted -> skip
		:: gameModelState == GameModelMustPass -> skip
		:: gameModelState == GameModelMustPlace ->
			if
			:: remainedGameLife > 1 ->
				gameModelState = GameModelMustPass
				remainedGameLife--
				dispatchQueueMain!GameModelStateObserver
			:: remainedGameLife > 0 ->
				gameModelState = GameModelMustPlace
				remainedGameLife--
				dispatchQueueMain!GameModelStateObserver
			:: remainedGameLife > 0 ->
				gameModelState = GameModelCompleted
				remainedGameLife--
				dispatchQueueMain!GameModelStateObserver
			:: remainedGameLife == 0 ->
				gameModelState = GameModelCompleted
				dispatchQueueMain!GameModelStateObserver
			:: else -> skip
			fi
		fi

	:: dispatchQueue?GameModelPassObserver ->
		if
		:: gameModelState == GameModelCompleted -> skip
		:: gameModelState == GameModelMustPass ->
			if
			:: remainedGameLife > 0 ->
				gameModelState = GameModelMustPlace
				remainedGameLife--
				dispatchQueueMain!GameModelStateObserver
			:: remainedGameLife > 0 ->
				gameModelState = GameModelCompleted
				remainedGameLife--
				dispatchQueueMain!GameModelStateObserver
			:: remainedGameLife == 0 ->
				gameModelState = GameModelCompleted
				dispatchQueueMain!GameModelStateObserver
			:: else -> skip
			fi
		:: gameModelState == GameModelMustPlace -> skip
		fi

	:: dispatchQueue?GameModelResetObserver ->
		gameModelState = INIT_GameModel_STATE
		remainedGameLife = INIT_GAME_LIFE
		dispatchQueueMain!GameModelStateObserver
	od
}



active proctype DispatchQueueMainLoop() {
	mtype:Dest dest
	
	end: do
	:: dispatchQueue!GameModelPlaceObserver -> skip
	:: dispatchQueue!GameModelPassObserver -> skip
	:: dispatchQueueMain?dest -> skip
	od
}
