s/(gameState(==| = |DidChange[!?]))2/\1GMReady/g
s/(gameState(==| = |DidChange[!?]))1/\1GMCompleted/g
s/((gameCommand|acceptedGameCommand)(==| = |Queue[!?]|DidAccept[!?]))3/\1GMPass/g
s/((gameCommand|acceptedGameCommand)(==| = |Queue[!?]|DidAccept[!?]))2/\1GMPlace/g
s/((gameCommand|acceptedGameCommand)(==| = |Queue[!?]|DidAccept[!?]))1/\1GMReset/g
s/(boardAnimationState(==| = |DidChange[!?]))4/\1BAMNotAnimating/g
s/(boardAnimationState(==| = |DidChange[!?]))3/\1BAMPlacing/g
s/(boardAnimationState(==| = |DidChange[!?]))2/\1BAMFlipping/g
s/(boardAnimationState(==| = |DidChange[!?]))1/\1BAMForceSyncing/g
s/(boardAnimationCommand(==| = |Queue[!?]))4/\1BAMPlace/g
s/(boardAnimationCommand(==| = |Queue[!?]))3/\1BAMForceSync/g
s/(boardAnimationCommand(==| = |Queue[!?]))2/\1BAMMarkAnimationAsCompleted/g
s/(boardAnimationCommand(==| = |Queue[!?]))1/\1BAMMarkSyncAsCompleted/g
s/(animatedGameState(==| = |DidChange[!?]))3/\1AGMReady/g
s/(animatedGameState(==| = |DidChange[!?]))2/\1AGMCompleted/g
s/(animatedGameState(==| = |DidChange[!?]))1/\1AGMAnimating/g
s/(animatedGameCommand(==| = |Queue[!?]))5/\1AGMPass/g
s/(animatedGameCommand(==| = |Queue[!?]))4/\1AGMPlace/g
s/(animatedGameCommand(==| = |Queue[!?]))3/\1AGMReset/g
s/(animatedGameCommand(==| = |Queue[!?]))2/\1AGMMarkAnimationAsCompleted/g
s/(animatedGameCommand(==| = |Queue[!?]))1/\1AGMMarkSyncAsCompleted/g