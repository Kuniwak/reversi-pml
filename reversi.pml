mtype:Dest = {
	GameModelPlaceObserver,
	GameModelPassObserver,
	GameModelResetObserver,
	GameModelStateObserver1,
	GameModelStateObserver2,
	AutoBkupGameModelPlaceObserver,
	AutoBkupGameModelPassObserver,
	AutoBkupGameModelResetObserver,
	AutoBkupGameModelStateObserver,
	UserDefaultsModelStoreObserver,
	UserDefaultsModelStateObserver
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

// NOTE: 3 = a + b
//       a = 1: Reserved capacity for tasks from outside of the dispatchQueue. It must be one.
//       b = 2: Reserved capacity for tasks from the dispatchQueue itself. It must be equal to the
//              max number how much a task can enqueue to dispatchQueue.
#define CAP_dispatchQueue 3
chan dispatchQueue = [CAP_dispatchQueue] of { mtype:Dest }
chan dispatchQueueMain = [1] of { mtype:Dest }

#define INIT_GameLife 10
#define INIT_GameModelState GameModelMustPlace


inline notifyObservers1(queue, a) {
	queue!a
}


inline notifyObservers2(queue, a, b) {
	if
	:: queue!a
		queue!b
	:: queue!b
		queue!a
	fi
}



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


int remainedGameLife = INIT_GameLife
mtype:GameModelState gameModelState = INIT_GameModelState
mtype:AutoBkupGameModelState autoBkupGameModelState


active proctype DispatchQueueLoop() {
	map_GameModelState_to_AutoBkupGameModelState(gameModelState, autoBkupGameModelState)

	end: do
	:: d_step { (dispatchQueue?[GameModelPlaceObserver] && len(dispatchQueue) == 1) -> dispatchQueue?GameModelPlaceObserver }
		if
		:: gameModelState == GameModelCompleted -> skip
		:: gameModelState == GameModelMustPass -> skip
		:: gameModelState == GameModelMustPlace ->
			if
			:: remainedGameLife > 1 ->
				gameModelState = GameModelMustPass
				remainedGameLife--
				notifyObservers2(dispatchQueue, GameModelStateObserver1, GameModelStateObserver2)
			:: remainedGameLife > 0 ->
				gameModelState = GameModelMustPlace
				remainedGameLife--
				notifyObservers2(dispatchQueue, GameModelStateObserver1, GameModelStateObserver2)
			:: remainedGameLife > 0 ->
				gameModelState = GameModelCompleted
				remainedGameLife--
				notifyObservers2(dispatchQueue, GameModelStateObserver1, GameModelStateObserver2)
			:: remainedGameLife == 0 ->
				gameModelState = GameModelCompleted
				notifyObservers2(dispatchQueue, GameModelStateObserver1, GameModelStateObserver2)
			:: else -> skip
			fi
		fi

	:: d_step { (dispatchQueue?[GameModelPassObserver] && len(dispatchQueue) == 1) -> dispatchQueue?GameModelPassObserver } ->
		if
		:: gameModelState == GameModelCompleted -> skip
		:: gameModelState == GameModelMustPass ->
			if
			:: remainedGameLife > 0 ->
				gameModelState = GameModelMustPlace
				remainedGameLife--
				notifyObservers2(dispatchQueue, GameModelStateObserver1, GameModelStateObserver2)
			:: remainedGameLife > 0 ->
				gameModelState = GameModelCompleted
				remainedGameLife--
				notifyObservers2(dispatchQueue, GameModelStateObserver1, GameModelStateObserver2)
			:: remainedGameLife == 0 ->
				gameModelState = GameModelCompleted
				notifyObservers2(dispatchQueue, GameModelStateObserver1, GameModelStateObserver2)
			:: else -> skip
			fi
		:: gameModelState == GameModelMustPlace -> skip
		fi

	:: dispatchQueue?GameModelResetObserver ->
		gameModelState = INIT_GameModelState
		remainedGameLife = INIT_GameLife
		notifyObservers2(dispatchQueue, GameModelStateObserver1, GameModelStateObserver2)

	:: dispatchQueue?AutoBkupGameModelPlaceObserver ->
		notifyObservers1(dispatchQueue, GameModelPlaceObserver)

	:: dispatchQueue?AutoBkupGameModelPassObserver ->
		notifyObservers1(dispatchQueue, GameModelPassObserver)

	:: dispatchQueue?AutoBkupGameModelResetObserver ->
		notifyObservers1(dispatchQueue, GameModelResetObserver)
	
	:: dispatchQueue?GameModelStateObserver1 ->
		map_GameModelState_to_AutoBkupGameModelState(gameModelState, autoBkupGameModelState)
		notifyObservers1(dispatchQueueMain, AutoBkupGameModelStateObserver)

	:: dispatchQueue?UserDefaultsModelStoreObserver ->
		notifyObservers1(dispatchQueue, UserDefaultsModelStateObserver)
	od
}



active proctype DispatchQueueMainLoop() {
	mtype:Dest dest
	
	end: do
	// NOTE: Ensure capacity of dispatchQueue to be remained.
	:: d_step { empty(dispatchQueue) -> notifyObservers1(dispatchQueue, AutoBkupGameModelPlaceObserver) }
	:: d_step { empty(dispatchQueue) -> notifyObservers1(dispatchQueue, AutoBkupGameModelPassObserver) }
	:: dispatchQueueMain?dest -> skip
	od
}
