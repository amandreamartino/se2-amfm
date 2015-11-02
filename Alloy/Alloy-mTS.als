module mTS

sig Customer {
}

sig TaxiDriver {
}

sig Reservation {
}

sig Area {

	reservations: set Reservation,
	drivers: set TaxiDriver

}

fact taxiDriverBelongsToOneQueue {
	
	all disj area1, area2: Area | no taxiDriver: TaxiDriver | taxiDriver in area1.drivers && taxiDriver in area2.drivers
	
}

fact reservationBelongsToOneQueue {

	all disj area1, area2: Area | no reservation: Reservation | reservation in area1.reservations && reservation in area2.reservations

}

assert driverRules {
	
 	

}

pred show{}

run show for 10
