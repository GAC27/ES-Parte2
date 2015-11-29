//Os Naturals nao estavam a funcionar
open util/integer as i

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
	registeredUserEmail:  USERS lone -> lone UEMAILS,
	registeredUserType:  USERS lone -> lone UTYPES,
	fileMode:	FILES lone -> lone MODE,
	fileSize:	FILES lone -> lone Int,
	fileVersion:	FILES lone -> lone Int,
	fileOwner:	FILES lone -> lone USERS
}

//2 users diferentes nao podem ter o mesmo mail independentemente do tipo associado a sua conta (t1 e t2 iguais ou diferentes): R3
fact{
	all u1,u2: USERS | all m1,m2: UEMAILS |
		u1->m1 in gitBob.registeredUserEmail && u2->m2 in gitBob.registeredUserEmail && u1!=u2 => m1!=m2
}

//1 user so pode ter um mail e um tipo
fact{
	all  u1: USERS |
		#gitBob.registeredUserEmail[u1]<=1 && #gitBob.registeredUserType[u1]<=1
}

//nao podem existir dois ficheiros iguais
fact{
	all f: FILES|
		#gitBob.fileMode[f]<=1  && #gitBob.fileSize[f]<=1 && #gitBob.fileVersion[f]<=1  && #gitBob.fileOwner[f]<=1  
}

//Um ficheiro tem de ter uma versao >0 e tamanho tem de ser um numero natural
fact{
	all f: FILES|
	gitBob.fileVersion[f]>0 && gitBob.fileSize[f]>=0
}


assert fileSizeBiggerThan0{
	no  f: FILES |
		gitBob.fileSize[f]<0
}

//check fileSizeBiggerThan0

assert fileVersionBiggerThan0{
	no  f: FILES |
		gitBob.fileVersion[f]<1
}

//check fileVersionBiggerThan0

pred newUser (g, g': gitBob, u: USERS, m: MODE, t: UTYPES){
	g'.registeredUserEmail = 	g.registeredUserEmail + u->m
	g'.registeredUserType = 	g.registeredUserType + u->t
}

pred removeUser(g, g': gitBob, u: USERS){
	g'.registeredUserEmail = g.registeredUserEmail - u->g.registeredUserEmail[u]
	g'.registeredUserType = g.registeredUserType - u->g.registeredUserType[u]
}

pred upgradeUser(g,g': gitBob, u: USERS){
	 g'.registeredUserType[u]= PREMIUM
}

pred downgradeBasic(g,g': gitBob, u: USERS){
	  g'.registeredUserType[u]= BASIC
}

run{} for 2
