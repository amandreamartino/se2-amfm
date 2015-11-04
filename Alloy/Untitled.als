sig Customer {
	email: one String,
	password: one String,
	name: one String,
	surname: one String,
	ssn:  one String,
	
}

sig Reservation {

	to: one GPSPosition,
	from: one GPSPosition

}

sig GPSPosition {

}

sig TaxiDriver {

	currentPosition: lone GPSPosition,

}

sig Request {

	ofReservation: one Reservation,
	isTakenCareBy: lone TaxiDriver

}

sig Area {

	queueOfDrivers: set TaxiDriver,
	listOfReservation: set Reservation

}

//Every taxi driver is at most one list

fact everyTaxiDriverInOneQueue {
	
	all drv: TaxiDriver | lone area: Area | drv in area.queueOfDrivers
	
}

//Every reservation is in one and only one list

fact everyReservationInOneList {
	
	all res: Reservation | one area: Area | res in area.listOfReservation
	
}

//Every reservation is associated to one and only one request,

fact everyReservationIsAssociatedToOneRequest {

	all res: Reservation | one request: Request | request.ofReservation = res	

}

//Every GPSPosition in the system is used by some entity

fact noGPSPositionForNothing {
	
	all gps: GPSPosition | some tD: TaxiDriver | tD.currentPosition = gps
	or some res: Reservation | res.from = gps
	or some res1: Reservation | res1.to = gps

}

//Is not possible to have a reservation from point a to a point a. No movement!

fact noZeroMovement {

	all res:Reservation | not (res.from = res.to)

}

fact ifADSD {
	
	all drv: TaxiDriver | some req: Request | some area:Area| drv = req.isTakenCareBy implies drv in area.queueOfDrivers

}


pred show() {}

run show for 6
