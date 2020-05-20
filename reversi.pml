// NOTE: This model is based on the following 2 hypotheses:
//
//       NO DIVERGE HYPOTHESIS:
//       A process implemented on a serial DispatchQueue has two work-item sources; the process itself and other processes.
//       This hypothesis claims all sound models have an upper bound for a number of the work-items in the DispatchQueue if
//       the number of work-items from other processes is finite.
//
//       SMALL SCOPE HYPOTHESIS:
//       A high proportion of bugs can be found by testing a program for all test inputs within some small scope[^1].
//
// [^1]: https://pdfs.semanticscholar.org/0c6d/97fbc3c753f59e7fb723725639f1b18706bb.pdf

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
	UserDefaultsModelStoreObserver
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

// NOTE: It must be larger than the upper bound of the number of work-items will be enqueued.
#define CAP_dispatchQueue 10
chan dispatchQueue = [CAP_dispatchQueue] of { mtype:Dest }
chan dispatchQueueMain = [CAP_dispatchQueue] of { mtype:Dest }

// NOTE: It must be finite.
#define MAX_USER_INTERACTION 5

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
	:: dispatchQueue?GameModelPlaceObserver ->
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

	:: dispatchQueue?GameModelPassObserver ->
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
		notifyObservers1(dispatchQueue, GameModelStateObserver1)

	:: dispatchQueue?AutoBkupGameModelPlaceObserver ->
		notifyObservers1(dispatchQueue, GameModelPlaceObserver)

	:: dispatchQueue?AutoBkupGameModelPassObserver ->
		notifyObservers1(dispatchQueue, GameModelPassObserver)

	:: dispatchQueue?AutoBkupGameModelResetObserver ->
		notifyObservers1(dispatchQueue, GameModelResetObserver)
	
	:: dispatchQueue?GameModelStateObserver1 ->
		map_GameModelState_to_AutoBkupGameModelState(gameModelState, autoBkupGameModelState)
		notifyObservers1(dispatchQueueMain, AutoBkupGameModelStateObserver)

	:: dispatchQueue?GameModelStateObserver2 ->
		notifyObservers1(dispatchQueue, UserDefaultsModelStoreObserver)

	:: dispatchQueue?UserDefaultsModelStoreObserver ->
		// NOTE: No one observe the state change of UserDefaultsModel.
		skip
	od
}



active proctype DispatchQueueMainLoop() {
	mtype:Dest dest
	int remainedUserInteraction = MAX_USER_INTERACTION
	
	end: do
	:: remainedUserInteraction > 0 ->
		notifyObservers1(dispatchQueue, AutoBkupGameModelPlaceObserver)
		remainedUserInteraction--
	:: remainedUserInteraction > 0 ->
		notifyObservers1(dispatchQueue, AutoBkupGameModelPassObserver)
		remainedUserInteraction--
	:: dispatchQueueMain?dest ->
		skip
	od
}
