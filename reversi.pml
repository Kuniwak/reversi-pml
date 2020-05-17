mtype:GameModelState = { GMMustPass, GMMustPlace, GMCompleted }
mtype:AutoBackupGameModelState = { ABGMMustPass, ABGMMustPlace, ABGMCompleted }
mtype:BordAnimationModelState = { BAMNotAnimating, BAMPlacing, BAMFlipping }
mtype:AnimatedGameModelState = { AGMMustPassNotAnimating, AGMMustPlaceNotAnimating, AGMCompletedNotAnimating, AGMMustPassAnimating, AGMMustPlaceAnimating, AGMCompletedAnimating }
mtype:AutomatableGameModelState = { AGMMustPass, AGMPustPlace, AGMCompleted, AGMNotReady }
mtype:AutomatorProgressModelState = { APWorking, APSleeping }

mtype:DispatchQueueUserInitiatedEvent = {
	GMMustPassEvent, GMMustPlaceEvent, GMCompletedEvent,
	ABGMMustPassEvent, ABGMMustPlaceEvent, ABGMCompletedEvent,
	BAMNotAnimatingEvent, BAMPlacingEvent, BAMFlippingEvent,
	AGMMustPassNotAnimatingEvent, AGMMustPlaceNotAnimatingEvent, AGMCompletedNotAnimatingEvent,
	AGMMustPassAnimatingEvent, AGMMustPlaceAnimatingEvent, AGMCompletedAnimatingEvent,
	AGMMustPassEvent, AGMPustPlaceEvent, AGMCompletedEvent, AGMNotReadyEvent,
	APWorkingEvent, APSleepingEvent,
}


// 60 = 8x8-4
#define MAX_GAME_LIFE 3

chan dispatchQueueUserInitiated = [0] of { DispatchQueueMainEvent }
chan dispatchQueueMain = [0] of { mtype: }


active proctype ModelsOnSameSerialDispatchQueue() {
	int remainedGameLife = MAX_GAME_LIFE

	mtype:DispatchQueueMainEvent mainEvent
	mtype:DispatchQueueUserInitiatedEvent userInitiatedEvent
	mtype:GameModelState gameModelState = GMMustPlace

	end: do
	:: dispatchQueueUserInitiated?userInitiatedEvent
		if
		:: remainedGameLife > 1 && mainEvent == GMPassEvent ->
			gameModelState = GMMustPlace
			dispatchQueueUserInitiated!GMMustPassEvent

		:: mainEvent == GMPlaceEvent ->
			if
			:: remainedGameLife > 0 -> gameModelState = GMMustPass
			:: remainedGameLife > 0 -> gameModelState = GMMustPlace
			:: remainedGameLife == 0 -> gameModelState = GMCompleted
			fi
			dispatchQueueUserInitiated!GMMustPassEvent
		:: else -> skip
		fi



	/* :: dispatchQueueUserInitiated?userInitiatedEvent -> */
	/* 	if */
	/* 	:: userInitiatedEvent == GMMustPassEvent -> */
	/* 	:: userInitiatedEvent == GMPustPlaceEvent -> */
	/* 	:: userInitiatedEvent == GMCompletedEvent -> */
	/* 	:: userInitiatedEvent == ABGMMustPassEvent -> */
	/* 	:: userInitiatedEvent == ABGMMustPlaceEvent -> */
	/* 	:: userInitiatedEvent == ABGMCompletedEvent -> */
	/* 	:: userInitiatedEvent == BAMNotAnimatingEvent -> */
	/* 	:: userInitiatedEvent == BAMPlacingEvent -> */
	/* 	:: userInitiatedEvent == BAMFlippingEvent -> */
	/* 	:: userInitiatedEvent == AGMMustPassNotAnimatingEvent -> */
	/* 	:: userInitiatedEvent == AGMMustPlaceNotAnimatingEvent -> */
	/* 	:: userInitiatedEvent == AGMCompletedNotAnimatingEvent -> */
	/* 	:: userInitiatedEvent == AGMMustPassAnimatingEvent -> */
	/* 	:: userInitiatedEvent == AGMMustPlaceAnimatingEvent -> */
	/* 	:: userInitiatedEvent == AGMCompletedAnimatingEvent -> */
	/* 	:: userInitiatedEvent == AGMMustPassEvent -> */
	/* 	:: userInitiatedEvent == AGMPustPlaceEvent -> */
	/* 	:: userInitiatedEvent == AGMCompletedEvent -> */
	/* 	:: userInitiatedEvent == AGMNotReadyEvent -> */
	/* 	:: userInitiatedEvent == APWorkingEvent -> */
	/* 	:: userInitiatedEvent == APSleepingEvent -> */
	/* 	:: userInitiatedEvent == APDidChoiceEvent -> */
	/* 	:: else -> assert(false) */
	/* 	fi */
	od
}
