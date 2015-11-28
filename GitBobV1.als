sig USERS {
	type: UTYPE	
}

abstract sig UTYPE {}

one sig BASIC extends UTYPE {}

one sig PREMIUM extends UTYPE {}

sig UEMAILS {}

sig FILES{
	mode: MODES
}

abstract sig MODES {}

one sig REGULAR extends MODES {}

one sig SECURE extends MODES {}

one sig READONLY extends MODES {}
