s/(dispatchQueue(Main)?[?!])8/\1GameModelPlaceObserver/g
s/(dispatchQueue(Main)?[?!])7/\1GameModelPassObserver/g
s/(dispatchQueue(Main)?[?!])6/\1GameModelResetObserver/g
s/(dispatchQueue(Main)?[?!])5/\1GameModelStateObserver/g
s/(dispatchQueue(Main)?[?!])4/\1AutoBkupGameModelPlaceObserver/g
s/(dispatchQueue(Main)?[?!])3/\1AutoBkupGameModelPassObserver/g
s/(dispatchQueue(Main)?[?!])2/\1AutoBkupGameModelResetObserver/g
s/(dispatchQueue(Main)?[?!])1/\1AutoBkupGameModelStateObserver/g
s/(gameModelState( = |==))3/\1GameModelMustPass/g
s/(gameModelState( = |==))2/\1GameModelMustPlace/g
s/(gameModelState( = |==))1/\1GameModelCompleted/g
s/(autoBkupGameModelState = )3/\1AutoBkupGameModelMustPass/g
s/(autoBkupGameModelState = )2/\1AutoBkupGameModelMustPlace/g
s/(autoBkupGameModelState = )1/\1AutoBkupGameModelCompleted/g
