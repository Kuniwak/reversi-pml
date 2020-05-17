mtype:Dest = {
	GameModelPlaceObserver,
	GameModelPassObserver,
	GameModelResetObserver,
	GameModelStateObserver,
	AutoBkupGameModelPlaceObserver,
	AutoBkupGameModelPassObserver,
	AutoBkupGameModelResetObserver,
	AutoBkupGameModelStateObserver,
}
mtype:GameModelState = {
	GameModelMustPass,
	GameModelMustPlace,
	GameModelCompleted
}
mtype:AutoBkupGameModelState = {
	AutoBkupGameModelMustPass,
	AutoBkupGameModelMustPlace,
	AutoBkupGameModelCompleted
}
chan dispatchQueue = [2] of { mtype:Dest }
chan dispatchQueueMain = [2] of { mtype:Dest }

#define INIT_GameLife 10
#define INIT_GameModelState GameModelMustPlace


inline map_GameModelState_to_AutoBkupGameModelState(gameModelState, autoBkupGameModelState) {
	if
	:: gameModelState == GameModelMustPass ->
		autoBkupGameModelState = AutoBkupGameModelMustPass
	:: gameModelState == GameModelMustPlace ->
		autoBkupGameModelState = AutoBkupGameModelMustPlace
	:: gameModelState == GameModelCompleted ->
		autoBkupGameModelState = AutoBkupGameModelCompleted
	fi
}



active proctype DispatchQueueLoop() {
	int remainedGameLife = INIT_GameLife
	mtype:GameModelState gameModelState = INIT_GameModelState
	mtype:AutoBkupGameModelState autoBkupGameModelState
	map_GameModelState_to_AutoBkupGameModelState(gameModelState, autoBkupGameModelState)

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
				dispatchQueue!GameModelStateObserver
			:: remainedGameLife > 0 ->
				gameModelState = GameModelMustPlace
				remainedGameLife--
				dispatchQueue!GameModelStateObserver
			:: remainedGameLife > 0 ->
				gameModelState = GameModelCompleted
				remainedGameLife--
				dispatchQueue!GameModelStateObserver
			:: remainedGameLife == 0 ->
				gameModelState = GameModelCompleted
				dispatchQueue!GameModelStateObserver
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
				dispatchQueue!GameModelStateObserver
			:: remainedGameLife > 0 ->
				gameModelState = GameModelCompleted
				remainedGameLife--
				dispatchQueue!GameModelStateObserver
			:: remainedGameLife == 0 ->
				gameModelState = GameModelCompleted
				dispatchQueue!GameModelStateObserver
			:: else -> skip
			fi
		:: gameModelState == GameModelMustPlace -> skip
		fi

	:: dispatchQueue?GameModelResetObserver ->
		gameModelState = INIT_GameModelState
		remainedGameLife = INIT_GameLife
		dispatchQueue!GameModelStateObserver

	:: dispatchQueue?AutoBkupGameModelPlaceObserver ->
		dispatchQueue!GameModelPlaceObserver

	:: dispatchQueue?AutoBkupGameModelPassObserver ->
		dispatchQueue!GameModelPassObserver

	:: dispatchQueue?AutoBkupGameModelResetObserver ->
		dispatchQueue!GameModelResetObserver
	
	:: dispatchQueue?GameModelStateObserver ->
		map_GameModelState_to_AutoBkupGameModelState(gameModelState, autoBkupGameModelState)
		dispatchQueueMain!AutoBkupGameModelStateObserver
	od
}



active proctype DispatchQueueMainLoop() {
	mtype:Dest dest
	
	end: do
	// NOTE: Ensure capacity of dispatchQueue to be remained.
	:: d_step { empty(dispatchQueue) -> dispatchQueue!AutoBkupGameModelPlaceObserver }
	:: d_step { empty(dispatchQueue) -> dispatchQueue!AutoBkupGameModelPassObserver }
	:: dispatchQueueMain?dest -> skip
	od
}
