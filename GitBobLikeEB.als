//Os Naturals nao estavam a funcionar
open util/integer as i
open util/ordering[gitBob] as gb


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

sig gitBob{
	registeredUserEmail:  USERS lone -> lone UEMAILS,  //requisite 2
	registeredUserType:  USERS set -> lone UTYPES,  //requisite 2
	fileMode:	FILES  -> lone MODE,
	fileSize:	FILES  -> lone Int,
	fileVersion:	FILES  -> lone Int,
	fileOwner:	FILES  -> lone USERS,
	localFiles:  FILES -> USERS-> lone Int,

}
pred init [g: gitBob] {
	no g.registeredUserEmail 
	no g.registeredUserType
	no g.fileMode
	no g.fileSize
	no g.fileVersion
	no g.fileOwner 
	no g.localFiles

 // all g: gitBob | g.state= t
}


//2 users diferentes nao podem ter o mesmo mail independentemente do tipo associado a sua conta (t1 e t2 iguais ou diferentes): R3
fact{
	all g:gitBob| all u1,u2: USERS | all m1: UEMAILS |
		u1->m1 in g.registeredUserEmail && u2->m1 in g.registeredUserEmail => u1=u2
}

//1 user so pode ter um mail e um tipo
//
fact{
	all g:gitBob| all  u1: USERS |
		#g.registeredUserEmail[u1]<=1 && #g.registeredUserType[u1]<=1
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




fact traces {
  init [gb/first]
  all g: gitBob - gb/last | let g' = g.next |
    some u:USERS, m: UEMAILS, t: UTYPES|
      newUser[g, g', u, m, t] or removeUser[g,g',u] or upgradeUser[g,g',u]
}

//requisite1
pred newUser (g,g': gitBob, u: USERS, m: UEMAILS, t: UTYPES, ){
	//preconditions
	#g.registeredUserEmail[u]=0
	#g.registeredUserType[u]=0
	no g.registeredUserEmail.m
     //operations
	g'.registeredUserEmail = 	g.registeredUserEmail + u->m
	g'.registeredUserType = 	g.registeredUserType + u->t
}

pred removeUser(g,g': gitBob, u: USERS){
    //preconditions
	#g.registeredUserEmail[u]=1
	#g.registeredUserType[u]=1
	//operations
	g'.registeredUserEmail = g.registeredUserEmail - u->g.registeredUserEmail[u]
	g'.registeredUserType = g.registeredUserType - u->g.registeredUserType[u]
}

pred upgradeUser(g,g': gitBob, u: USERS){
	//preconditions
	#g.registeredUserEmail[u]=1
	#g.registeredUserType[u]=1
	g.registeredUserType[u]=BASIC
	//operation
	 g'.registeredUserType[u]= PREMIUM
}

pred downgradeBasic(g,g': gitBob, u: USERS){
	//preconditions
	#g.registeredUserEmail[u]=1
	#g.registeredUserType[u]=1
	g.registeredUserType[u]=PREMIUM
	//operation
	g'.registeredUserType[u]= BASIC
}
/*
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
*/

run upgradeUser for 5 but 3 gitBob

	
