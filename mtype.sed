s/(dispatchQueue(Main)?[?!])4/\1GameModelPlaceObserver/g
s/(dispatchQueue(Main)?[?!])3/\1GameModelPassObserver/g
s/(dispatchQueue(Main)?[?!])2/\1GameModelResetObserver/g
s/(dispatchQueue(Main)?[?!])1/\1GameModelStateObserver/g
s/(gameModelState = )3/\1GameModelMustPass/g
s/(gameModelState = )2/\1GameModelMustPlace/g
s/(gameModelState = )1/\1GameModelCompleted/g
