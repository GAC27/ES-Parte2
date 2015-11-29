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
	fileMode:	FILES  -> lone MODE,
	fileSize:	FILES  -> lone Int,
	fileVersion:	FILES  -> lone Int,
	fileOwner:	FILES  -> lone USERS,
	localFiles:  FILES -> USERS-> lone Int
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

//Um ficheiro local tem de ter uma versao >0 
fact{
	all f: FILES | all u: USERS |
		gitBob.localFiles[f][u]>0 
}



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

pred addFile(g,g': gitBob, file:FILES, size:Int, owner: USERS){
	g'.fileMode = g.fileMode + file->REGULAR
	g'.fileSize = g.fileSize + file-> size
	g'.fileVersion = g.fileVersion + file ->1
	g'.fileOwner = g.fileOwner + file-> owner
	g'.localFiles = g.localFiles + file-> owner -> 1
}

//falta ver os acessos e partilhas
pred removeFile (g,g': gitBob, file:FILES, usr: USERS){
	g'.fileMode = g.fileMode - file->g.fileMode[file]
	g'.fileSize = g.fileSize + file-> g.fileSize[file]
	g'.fileVersion = g.fileVersion + file ->g.fileVersion[file]
	g'.fileOwner = g.fileOwner + file-> g.fileOwner[file]
	g'.localFiles = file <: g.localFiles
}

//falta actualizar o repo local do user que adiciona
pred uploadFile(g,g': gitBob, file:FILES, usr: USERS){
	g'.fileVersion[file] = integer/add[g.fileVersion[file], 1]
	g'.localFiles[file][usr] = integer/add[g.fileVersion[file], 1] 	//estou a igualar a versao no gitBob +1 por questoes de simplificaçao 
}

pred downloadFile(g,g': gitBob, file:FILES, usr: USERS){
	//temos de meter o file no repositorio local e com a versao actual do gitBob
	g'.localFiles[file][usr] = g.fileVersion[file]
}


run{} for 2
