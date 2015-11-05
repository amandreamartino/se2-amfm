sig Email {}
sig SSN {}
sig ID {}
sig GPSPosition {}

abstract sig User {}


abstract sig RegisteredUser extends User {
	id: one ID
}

sig Visitor extends User {}

sig Customer extends RegisteredUser{

	email: one Email,
	ssn:  one SSN,
	reservations: set Reservation,
	currentPosition: lone GPSPosition
	
}

sig TaxiDriver extends RegisteredUser{

	currentPosition: lone GPSPosition,
	isCurrentlyBusyOn: lone Reservation

}

sig SysAdmin extends RegisteredUser {}

sig Reservation {

	to: one GPSPosition,
	from: one GPSPosition,
	takenCareBy: lone TaxiDriver

}

sig LiveReservation extends Reservation {}

sig Area {

	queueOfDrivers: set TaxiDriver,
	listOfReservation: set Reservation,
	xPosition: Int,
	yPosition: Int

}


fact customerProperties {
	
	//Cannot exist two different users with the same ssn or the same email address
	all s:SSN | one cus:Customer | cus.ssn = s
	all e:Email | one cus:Customer | cus.email = e
	//a customer can have at most one livereservation in his/her reservations
	all cus:Customer | lone reg:LiveReservation | reg in cus.reservations
	//system uses customer positions iff a livereservation is saved in customer reservations
	no cus:Customer | one reg:LiveReservation | one gps:GPSPosition | cus.currentPosition = gps && not reg in cus.reservations

}

fact registeredUserProperties {
	
	//id value is used by the system to identify every different registered user. two different users with the same id are not allowed
	all i:ID | one user:RegisteredUser | user.id = i

}

fact areaProperties {

	//every area must have more than one driver and less than 6 drivers
	all area:Area | #area.queueOfDrivers>=2 && #area.queueOfDrivers<=5	
	//area coordinates must be positive numbers
	&& area.xPosition>0 && area.yPosition>0
	//every area has different set of coordinates
	all disj area1, area2 : Area | area1.xPosition!=area2.xPosition or area1.yPosition!=area2.yPosition

}

fact reservationProperties {

	//Every reservation is associated to one and only one Customer
	all res:Reservation | one cust:Customer | res in cust.reservations
	//Is not possible to have a reservation with starting point equal to destination point. 
	//It's meaningless to have a reservation with no movement at all
	all res:Reservation | not (res.from = res.to)
	//Every reservation is in one and only one list
	all res: Reservation | one area: Area | res in area.listOfReservation

}

fact taxiDriverProperties {
	
	//if a taxi driver is busy on a reservation then this reservation is taken care by this driver
	all drv:TaxiDriver | all res:Reservation | (drv.isCurrentlyBusyOn=res implies res.takenCareBy=drv)	
	//a taxi driver is in a list when he/she is working. gps position must be saved only when the driver is working.
	all area:Area | all drv: TaxiDriver | (drv in area.queueOfDrivers iff (one gps:GPSPosition | drv.currentPosition=gps))
	//every taxi driver is in at most one area at time
	all drv: TaxiDriver | lone area: Area | drv in area.queueOfDrivers
	
}

fact gpsPositionProperties {
	
	//No gps position in the system not associated to any entity that requires a gps position
	all gps:GPSPosition | some drv:TaxiDriver | some res:Reservation | drv.currentPosition = gps or res.from = gps or res.to = gps	

}

fact liveReservationProperties {
	
	//if a customer has a live reservation, from field of live reservation is equal to customer's current location
	//it means that customer's current gps position is used to make a new live reservation
	all res:LiveReservation | all cus:Customer | res in cus.reservations implies cus.currentPosition = res.from

}

pred show [drv:TaxiDriver, drv2:TaxiDriver, res1:LiveReservation, res2:LiveReservation, cus:Customer, cus2:Customer] {

	some res:Reservation | res.takenCareBy=drv
	no res:Reservation | drv.isCurrentlyBusyOn=res
	no res:LiveReservation | res in cus.reservations
/*
	no area:Area | drv in area.queueOfDrivers
 	no res3: LiveReservation | res3 in cus2.reservations
	res1 in cus.reservations
	res2 in cus.reservations
	res1.takenCareBy=drv2
	res2.takenCareBy=drv2
	drv2.isCurrentlyBusyOn!=res2
	drv2.isCurrentlyBusyOn!=res1
*/
}

run show for 5 but 4 Area, 20 TaxiDriver, 7 Customer , 3 Reservation , 1 LiveReservation
