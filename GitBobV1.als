sig USERS {}

abstract sig UTYPE {}

one sig BASIC extends UTYPE {}

one sig PREMIUM extends UTYPE {}

sig UEMAILS {}

sig FILES{}

abstract sig MODES {}

one sig REGULAR extends MODES {}

one sig SECURE extends MODES {}

one sig READONLY extends MODES {}

//Set de utilizadores registados no gitBob. Users<->Mail<->Tipo
one sig gitBob{
	registeredUsers:  USERS lone -> lone UEMAILS 

}
//  -> some UTYPE
//  , t: UTYPE
fun newUser [u: USERS , m: UEMAILS] : set gitBob.registeredUsers{
	gitBob.registeredUsers + u->m
} 

run{} for 10
 
