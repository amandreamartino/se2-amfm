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
	all cus:Customer | no gps:GPSPosition | cus.currentPosition = gps && no res:LiveReservation | res in cus.reservations

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
	all drv:TaxiDriver | (one gps:GPSPosition | drv.currentPosition=gps) iff (one area:Area | drv in area.queueOfDrivers) 
	//every taxi driver is in at most one area at time
	all drv: TaxiDriver | lone area1: Area | drv in area1.queueOfDrivers
	
}

fact gpsPositionProperties {
	
	//No gps position in the system not associated to any entity that requires a gps position	
	no gps:GPSPosition | (no drv:TaxiDriver | drv.currentPosition=gps) and (no res:Reservation | res.from=gps) and (no res:Reservation | res.to = gps)

}

fact liveReservationProperties {

	//if a user has a live reservation in his/her list then is current position is equal to from field of live reservation
	all res:LiveReservation | all cus:Customer | res in cus.reservations implies res.from=cus.currentPosition
	
}


assert noCustomersWithSameSSN {
	
	all ssn1, ssn2: SSN | all disj cus1, cus2: Customer | cus1.ssn=ssn1 && cus2.ssn=ssn2 implies ssn1!=ssn2

}

check noCustomersWithSameSSN for 10

assert noCustomersWithSameEmail {
		
	all email1, email2: Email | all disj cus1, cus2: Customer | cus1.email=email1 && cus2.email=email2 implies email1!=email2	

}

check noCustomersWithSameEmail for 10

assert noRegisteredUserWithSameID {

	all id1, id2: ID | all disj reg1, reg2: RegisteredUser | reg1.id = id1 && reg2.id = id2 implies id1!=id2

}

check noRegisteredUserWithSameID for 10

assert disjointedAreas {
	
	all area1, area2 : Area| all disj x1, x2: Int | all disj y1,y2: Int | area1.xPosition=x1 && area1.yPosition=y1 && area2.xPosition=x2 && area2.yPosition=y2 implies (x1!=x2 or y1=y2)	

}

check disjointedAreas for 10

assert driverInQueueAndGPS {
	
	all drv:TaxiDriver | ( one area:Area | drv in area.queueOfDrivers ) implies one gps:GPSPosition | drv.currentPosition=gps	

}
check driverInQueueAndGPS for 10


pred showComplex (drv:TaxiDriver, drv2:TaxiDriver) {

	no area:Area | drv in area.queueOfDrivers
	one res:Reservation | drv.isCurrentlyBusyOn=res
	one res:Reservation | drv.isCurrentlyBusyOn!=res && res.takenCareBy=drv
	#Area=2
	#Reservation=5
	#LiveReservation=2
	#Customer=2
	#TaxiDriver=5
	#GPSPosition>0
	#Visitor=2
	#SysAdmin=1

}

pred showSimple() {

	#Area=1
	#Reservation=2
	#LiveReservation=1
	#Customer=2
	#TaxiDriver=2
	#GPSPosition>0
	#Visitor=0
	#SysAdmin=0

}


run showSimple for 10

run showComplex for 10
