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
	localFiles:  FILES -> USERS

}


pred init [g: gitBob] {
	no g.registeredUserEmail //requisite 4
	no g.registeredUserType //requisite 4
	no g.fileMode		//requisite 13
	no g.fileSize 		//requisite 13
	no g.fileVersion		//requisite 13
	no g.fileOwner 		//requisite 13
	no g.localFiles		//requisite 13

 // all g: gitBob | g.state= t
}


// 2 users diferentes nao podem ter o mesmo mail independentemente do tipo associado a sua conta (t1 e t2 iguais ou diferentes)
// requisite 3
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

fact traces {
  init [gb/first]
  all g: gitBob - gb/last | let g' = g.next |
    some u:USERS, m: UEMAILS, t: UTYPES,file: FILES, size: Int,owner: USERS|
	//g'.registeredUserEmail=g.registeredUserEmail para todas as relaçoes do gitBob de forma a forçarmos 
	//o git seguinte a ter tudo igual ao anterior e so depois executamos um predicado
      newUser[g, g', u, m, t] or removeUser[g,g',u] or upgradeUser[g,g',u] or addFile[g,g', file, size, owner]
}

//requisite1
pred newUser (g,g': gitBob, u: USERS, m: UEMAILS, t: UTYPES, ){
	//preconditions
	#g.registeredUserEmail[u]=0 //requisite 5
	#g.registeredUserType[u]=0 //requisite 5
	no g.registeredUserEmail.m
    	//operations
	g'.registeredUserEmail = 	g.registeredUserEmail + u->m
	g'.registeredUserType = 	g.registeredUserType + u->t
}

pred removeUser(g,g': gitBob, u: USERS){
    //preconditions
	#g.registeredUserEmail[u]=1 //requisite 6
	#g.registeredUserType[u]=1 //requisite 6
	//operations
	g'.registeredUserEmail = g.registeredUserEmail - u->g.registeredUserEmail[u]
	g'.registeredUserType = g.registeredUserType - u->g.registeredUserType[u]
}

pred upgradeUser(g,g': gitBob, u: USERS){
	//preconditions
	#g.registeredUserEmail[u]=1 //requisite 7
	#g.registeredUserType[u]=1 //requisite 7
	g.registeredUserType[u]=BASIC //requisite 9
	//operation
	 g'.registeredUserType[u]= PREMIUM
}

pred downgradeBasic(g,g': gitBob, u: USERS){
	//preconditions
	#g.registeredUserEmail[u]=1 //requisite 8
	#g.registeredUserType[u]=1 //requisite 8
	g.registeredUserType[u]=PREMIUM //requisite 9
	//operation
	g'.registeredUserType[u]= BASIC
}

pred addFile(g,g': gitBob, file:FILES, size:Int, owner: USERS){
	//preconditions
	#g.fileMode[file]=0 //requisite 15
	#g.fileSize[file]=0 //requisite 15
	#g.fileVersion[file]=0 //requisite 15
	#g.fileOwner[file]=0 //requisite 15
	#g.localFiles[file]=0 //requisite 15
	//operation
	g'.fileMode = g.fileMode + file->REGULAR
	g'.fileSize = g.fileSize + file-> size
	g'.fileVersion = g.fileVersion + file ->1
	g'.fileOwner = g.fileOwner + file-> owner
	g'.localFiles = g.localFiles + file-> owner
}



//falta ver os acessos e partilhas
pred removeFile (g,g': gitBob, file:FILES, usr: USERS){
	//preconditions
	#g.fileMode[file]=1 //requisite 15
	#g.fileSize[file]=1 //requisite 15
	#g.fileVersion[file]=1 //requisite 15
	#g.fileOwner[file]=1 //requisite 15
	#g.localFiles[file]>=1 //requisite 15
	//operations
	g'.fileMode = g.fileMode - file->g.fileMode[file]
	g'.fileSize = g.fileSize - file-> g.fileSize[file]
	g'.fileVersion = g.fileVersion - file ->g.fileVersion[file]
	g'.fileOwner = g.fileOwner - file-> g.fileOwner[file]
	g'.localFiles = g.localFiles - file-> USERS
}


/*
pred uploadFile(g,g': gitBob, file:FILES, usr: USERS){
	g'.fileVersion[file] = integer/add[g.fileVersion[file], 1]
}


pred downloadFile(g,g': gitBob, file:FILES, usr: USERS){
	//temos de meter o file no repositorio local e com a versao actual do gitBob
	g'.localFiles[file][usr] = g.fileVersion[file]
}
*/

run removeFile for 3 but 2 gitBob , 1 FILES

	
