//Os Naturals nao estavam a funcionar
open util/integer as i

sig USERS {}

abstract sig UTYPES {}

one sig BASIC extends UTYPES {}

one sig PREMIUM extends UTYPES {}

sig UEMAILS {}

sig FILES{
	version: Int,
	size: Int,
	owner: one USERS
}

abstract sig MODE {}

one sig REGULAR extends MODE {}

one sig SECURE extends MODE {}

one sig READONLY extends MODE {}

//Set de utilizadores registados no gitBob. Users<->Mail<->Tipo

one sig gitBob{
	registeredUsers:  USERS lone -> lone (UEMAILS ->  UTYPES),
	filesInGit:	FILES lone -> lone MODE

}
//2 users diferentes nao podem ter o mesmo mail independentemente do tipo associado a sua conta (t1 e t2 iguais ou diferentes): R3
fact{
	all u1,u2: USERS | all m1,m2: UEMAILS | all t1,t2: UTYPES | 
		u1->m1->t1 in gitBob.registeredUsers && u2->m2->t2 in gitBob.registeredUsers && u1!=u2 => m1!=m2
}

//2 nao podem existir dois ficheiros iguais
fact{
	all f1,f2: FILES | all m1,m2: MODE |
		f1->m1 in gitBob.filesInGit && f2->m2 in gitBob.filesInGit && m1!=m2 => f1!=f2
}

//Um ficheiro tem de ter uma versao >0 e tamanho tem de ser um numero natural
fact{
	all f: FILES|
		f.version>0 && f.size>=0
}

pred newUser (g, g': gitBob, u: USERS, m: MODE, t: UTYPES){
	g'.registeredUsers = 	g.registeredUsers + u->m->t
}

pred removeUser(g, g': gitBob, u: USERS){
	g'.registeredUsers = g.registeredUsers - u->g.registeredUsers[u]

}
pred upgradeUser(g,g': gitBob, u: USERS){
//	 g'.registeredUsers[u].UEMAILS=g.registeredUsers[u].UEMAILS ++ PREMIUM
	 g'.registeredUsers[u]=g.registeredUsers[u].UTYPES->PREMIUM

}
pred downgradeBasic(g,g': gitBob, u: USERS){
	 g'.registeredUsers[u]=g.registeredUsers[u].UTYPES->BASIC
}

//Nao existem 2+ users iguais
assert noUsersIguais{
	all  u1: USERS |
		#gitBob.registeredUsers[u1]<=1
}

//check noUsersIguais


//Nao existem 2+ mails iguais
assert noMailsIguais{
	all  m1: UEMAILS |
		#~(gitBob.registeredUsers.UTYPES)[m1]<=1
}

//check noMailsIguais


//Nao existem 2+ ficheiros iguais
assert noFilesIguais{
	all  f1: FILES |
		#gitBob.filesInGit[f1]<=1
}

check noFilesIguais

assert fileSizeBiggerThan0{
	no  f: FILES |
		f.size<0
}

//check fileSizeBiggerThan0

assert fileVersionBiggerThan0{
	no  f: FILES |
		f.version<1
}

//check fileVersionBiggerThan0


run add for 3
run{} for 2
 
