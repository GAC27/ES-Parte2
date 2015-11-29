sig USERS {}

abstract sig UTYPES {}

one sig BASIC extends UTYPES {}

one sig PREMIUM extends UTYPES {}

sig UEMAILS {}

sig FILES{}

abstract sig MODE {}

one sig REGULAR extends MODE {}

one sig SECURE extends MODE {}

one sig READONLY extends MODE {}

//Set de utilizadores registados no gitBob. Users<->Mail<->Tipo
one sig gitBob{
	registeredUsers:  USERS lone -> lone (UEMAILS ->  UTYPES)

}
//2 users diferentes nao podem ter o mesmo mail independentemente do tipo associado a sua conta (t1 e t2 iguais ou diferentes)
fact{
	all u1,u2: USERS | all m1,m2: UEMAILS | all t1,t2: UTYPES | 
		u1->m1->t1 in gitBob.registeredUsers && u2->m2->t2 in gitBob.registeredUsers && u1!=u2 => m1!=m2
}

//Nao existem users iguais
assert noUsersIguais{
	all u1,u2:USERS | all m1,m2: UEMAILS | all t1,t2: UTYPES | 
		u1->m1->t1 in gitBob.registeredUsers && u2->m2->t2 in gitBob.registeredUsers && m1!=m2 && u1!=u2 
}
//Nao existem mails iguais
assert noMailsIguais{
	all u1,u2:USERS | no m1,m2: UEMAILS | all t1,t2: UTYPES | 
		u1->m1->t1 in gitBob.registeredUsers && u2->m2->t2 in gitBob.registeredUsers && u1!=u2 && m1=m2
}

check noUsersIguais

//check noMailsIguais


fun newUser [u: USERS , m: UEMAILS , t: UTYPES] : set gitBob.registeredUsers{
	gitBob.registeredUsers + u->m->t
} 

run{} for 2
 
