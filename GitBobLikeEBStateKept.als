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
	registeredUserEmail:  USERS lone -> lone UEMAILS,  //requisite 1 and 2
	registeredUserType:  USERS set -> lone UTYPES,  //requisite 1 and 2
	fileMode:	FILES  -> lone MODE, 			//requisite 10 and 29
	fileSize:	FILES  -> lone Int, 				//requisite 10
	fileVersion:	FILES  -> lone Int, 				//requisite 10 and 37
	fileOwner:	FILES  -> lone USERS, 			//requisite 10
	//usado para guardarmos os acessos dos users aos files
	sharingOfFiles:  FILES -> USERS 					//requisite 10 and 20

}


pred init [g: gitBob] {
	no g.registeredUserEmail //requisite 4
	no g.registeredUserType //requisite 4
	no g.fileMode		//requisite 13
	no g.fileSize 		//requisite 13
	no g.fileVersion		//requisite 13
	no g.fileOwner 		//requisite 13
	no g.sharingOfFiles		//requisite 13 and 23

	// all g: gitBob | g.state= t
}


//requisite 22: A GitBob ﬁle is always shared with its owner;
fact{
	all f:FILES | all u:USERS | all g:gitBob |
		f->u in g.fileOwner => f->u in g.sharingOfFiles
}

//requisite 29
fact{
	all f:FILES | 
		gitBob.fileMode[f] in MODE
}

fact traces {
	init [gb/first]
	all g: gitBob - gb/last | let g' = g.next |
		some u, u2:USERS, m: UEMAILS, t: UTYPES, file: FILES, size: Int, mode:MODE|
     		newUser[g, g', u, m, t] or removeUser[g,g',u] or upgradeUser[g,g',u] or downgradeBasic[g,g',u] or 
			addFile[g,g', file, size, u] or removeFile [g,g', file,u ] or uploadFile[g,g', file, u] or downloadFile[g,g', file, u] or shareFile[g,g', file, u, u2]
		 	or  removeShare[g,g', file, u, u2] or changeSharingMode[g,g', file, u, mode]
}


//1 user so pode ter um mail e um tipo
//requisite 2
assert userHasOneTypeOneMail{
	all g:gitBob, u:USERS|
				(#g.registeredUserEmail[u]=1 and #g.registeredUserType[u]=1) or (#g.registeredUserEmail[u]=0 and #g.registeredUserType[u]=0) 
			
}


// 2 users diferentes nao podem ter o mesmo mail independentemente do tipo associado a sua conta (t1 e t2 iguais ou diferentes)
// requisite 3
assert onlyOneMail{
	all g:gitBob, u1,u2:USERS, m: UEMAILS |
		(u1->m in g.registeredUserEmail and u2->m in g.registeredUserEmail => u1=u2)
			
}

check userHasOneTypeOneMail for 10
check onlyOneMail for 10


//nao podem existir dois ficheiros iguais
//requisite 10
assert noFilesIguais{
	all g: gitBob, f: FILES|
		(#g.fileMode[f]=1  and #g.fileSize[f]=1 and #g.fileVersion[f]=1  and #g.fileOwner[f]=1  ) or (#g.fileMode[f]=0  and #g.fileSize[f]=0 and #g.fileVersion[f]=0  and #g.fileOwner[f]=0  )
			
}

check noFilesIguais for 10

//Um ficheiro tem de ter uma versao >0 e tamanho tem de ser um numero natural
// requisite 17
assert versionAndSizeBiggerThan0{
	all g: gitBob, f : g.fileVersion.Int & g.fileSize.Int |
		(g.fileVersion[f] >0 && g.fileSize[f]>=0)
			
}

check versionAndSizeBiggerThan0 for 10

//requisite 11
assert sizeIsAllwaysTheSame{
	all g: gitBob  - gb/last ,  f : g.fileVersion.Int & g.fileSize.Int  | let g'=g.next | 
		(f in g'.fileVersion.Int & g'.fileSize.Int) implies (g.fileSize[f] = g'.fileSize[f])
			
}

check sizeIsAllwaysTheSame for 10


assert versionNat1SizeNat{
	all g: gitBob, f: FILES| (f in (g.fileVersion.Int & g.fileSize.Int &  g.fileMode.MODE & g.fileOwner.USERS & g.sharingOfFiles.USERS)) implies ( 
		 f.(g.fileVersion)>0 and f.(g.fileSize)>=0 )
			
}

check versionNat1SizeNat for 10

//requisite 21
assert shareOnlyRegUsers{
	all g:gitBob, u:USERS| 
		(u in FILES.(g.sharingOfFiles)) implies ( #g.registeredUserEmail[u]=1 and #g.registeredUserType[u]=1)
}

check shareOnlyRegUsers


//requisite1
pred newUser (g,g': gitBob, u: USERS, m: UEMAILS, t: UTYPES, ){
	//preconditions
	#g.registeredUserEmail[u]=0 //requisite 5
	#g.registeredUserType[u]=0 //requisite 5
	no g.registeredUserEmail.m
    	//operations
	g'.registeredUserEmail = 	g.registeredUserEmail + u->m
	g'.registeredUserType = 	g.registeredUserType + u->t
	//coisas que nao se podem alterar
	g'.fileMode=g.fileMode
	g'.fileSize=g.fileSize
	g'.fileVersion=g.fileVersion
	g'.fileOwner=g.fileOwner
	g'.sharingOfFiles=g.sharingOfFiles
	
}


pred removeUser(g,g': gitBob, u: USERS){
    //preconditions
	#g.registeredUserEmail[u]=1 	//requisite 6
	#g.registeredUserType[u]=1 	//requisite 6
	#~(g.fileOwner)[u]=0			//requisite 14	
	#~(g.sharingOfFiles)[u]=0			//requisite 24
	//operations
	g'.registeredUserEmail = g.registeredUserEmail - u->g.registeredUserEmail[u]
	g'.registeredUserType = g.registeredUserType - u->g.registeredUserType[u]
	//coisas que nao se podem alterar
	g'.fileMode=g.fileMode
	g'.fileSize=g.fileSize
	g'.fileVersion=g.fileVersion
	g'.fileOwner=g.fileOwner
	g'.sharingOfFiles=g.sharingOfFiles
}

pred upgradeUser(g,g': gitBob, u: USERS){
	//preconditions
	#g.registeredUserEmail[u]=1 //requisite 7
	#g.registeredUserType[u]=1 //requisite 7
	g.registeredUserType[u]=BASIC //requisite 9
	//operation
	g'.registeredUserType=g.registeredUserType - u->BASIC + u->PREMIUM
	//coisas que nao se podem alterar
	g'.registeredUserEmail=g.registeredUserEmail
	g'.fileMode=g.fileMode
	g'.fileSize=g.fileSize
	g'.fileVersion=g.fileVersion
	g'.fileOwner=g.fileOwner
	g'.sharingOfFiles=g.sharingOfFiles
}



pred downgradeBasic(g,g': gitBob, u: USERS){
	//preconditions
	#g.registeredUserEmail[u]=1 				//requisite 8
	#g.registeredUserType[u]=1				//requisite 8
	g.registeredUserType[u]=PREMIUM			//requisite 9
	(all f: g.sharingOfFiles.u| g.fileMode[f]!= SECURE) 	//requisite 31
	//operation
	g'.registeredUserType=g.registeredUserType + u->BASIC - u->PREMIUM
	//coisas que nao se podem alterar
	g'.registeredUserEmail=g.registeredUserEmail
	g'.fileMode=g.fileMode
	g'.fileSize=g.fileSize
	g'.fileVersion=g.fileVersion
	g'.fileOwner=g.fileOwner
	g'.sharingOfFiles=g.sharingOfFiles
}




pred addFile(g,g': gitBob, file:FILES, size:Int, owner: USERS){
	//preconditions
	#g.registeredUserEmail[owner]=1 	//requisite 16
	#g.registeredUserType[owner]=1		//requisite 16
	#g.fileMode[file]=0 				//requisite 15
	#g.fileSize[file]=0				//requisite 15
	#g.fileVersion[file]=0				//requisite 15
	#g.fileOwner[file]=0				//requisite 15
	#g.sharingOfFiles[file]=0				//requisite 15
	size>=0												//Um ficheiro tem de ter uma versao >0 e tamanho tem de ser um numero natural
	//operation
	g'.fileMode = g.fileMode + file->REGULAR 	//requisite 29 and 32  & Um ficheiro tem de ter uma versao >0 e tamanho tem de ser um numero natural
	g'.fileSize = g.fileSize + file-> size
	g'.fileVersion = g.fileVersion + file ->1 		//requisite 17
	g'.fileOwner = g.fileOwner + file-> owner
	g'.sharingOfFiles = g.sharingOfFiles + file-> owner 	//requisite 22
	//coisas que nao se podem alterar
	g'.registeredUserEmail=g.registeredUserEmail
	g'.registeredUserType=g.registeredUserType
}


//falta ver os acessos e partilhas
pred removeFile (g,g': gitBob, file:FILES, usr: USERS){
	//preconditions
	#g.registeredUserEmail[usr]=1 	
	#g.registeredUserType[usr]=1	
	#g.fileMode[file]=1		//requisite 18
	#g.fileSize[file]=1 		//requisite 18
	#g.fileVersion[file]=1 		//requisite 18
	#g.fileOwner[file]=1 		//requisite 18
	#g.sharingOfFiles[file]>=1 		//requisite 18
	file->usr in g.sharingOfFiles 	//requisite 25
	(g.fileMode[file]=READONLY => g.fileOwner[file]=usr)	//requisite 33
	//operations
	g'.fileMode = g.fileMode - file->g.fileMode[file]		//requisite 12 ficheiros removidos ja nao constam no gitBob
	g'.fileSize = g.fileSize - file-> g.fileSize[file]			//requisite 12
	g'.fileVersion = g.fileVersion - file ->g.fileVersion[file]	//requisite 12
	g'.fileOwner = g.fileOwner - file-> g.fileOwner[file]		//requisite 12
	g'.sharingOfFiles = g.sharingOfFiles - file-> USERS			//requisite 12
	//coisas que nao se podem alterar
	g'.registeredUserEmail=g.registeredUserEmail
	g'.registeredUserType=g.registeredUserType
}


pred uploadFile(g,g': gitBob, file:FILES, usr: USERS){
	//preconditions
	#g.registeredUserEmail[usr]=1 	
	#g.registeredUserType[usr]=1
	#g.fileMode[file]=1 	//requisite 18
	#g.fileSize[file]=1 	//requisite 18
	#g.fileVersion[file]=1 	//requisite 18
	#g.fileOwner[file]=1 	//requisite 18
	file->usr in g.sharingOfFiles //requisite 18 and 25
	(g.fileMode[file]=READONLY => g.fileOwner[file]=usr)	//requisite 34
	//operations
	g'.fileVersion =    g.fileVersion - file-> g.fileVersion[file]	//requisite 19
	g'.fileVersion = 	g'.fileVersion + file->g.fileVersion[file].next
	//coisas que nao se podem alterar
	g'.registeredUserEmail=g.registeredUserEmail
	g'.registeredUserType=g.registeredUserType
	g'.fileMode=g.fileMode
	g'.fileSize=g.fileSize
	g'.fileOwner=g.fileOwner
	g'.sharingOfFiles=g.sharingOfFiles

}


pred downloadFile(g,g': gitBob, file:FILES, usr: USERS){
	//preconditions
	#g.fileMode[file]=1 		//requisite 18
	#g.fileSize[file]=1 		//requisite 18
	#g.fileVersion[file]=1 		//requisite 18
	#g.fileOwner[file]=1 		//requisite 18
	file->usr in g.sharingOfFiles	//requisite 18  and 25
	//coisas que nao se podem alterar
	g'.registeredUserEmail=g.registeredUserEmail
	g'.registeredUserType=g.registeredUserType
	g'.fileMode=g.fileMode
	g'.fileSize=g.fileSize
	g'.fileVersion=g.fileVersion
	g'.fileOwner=g.fileOwner
	g'.sharingOfFiles=g.sharingOfFiles
}



pred shareFile(g,g': gitBob, file: FILES, usr1, usr2: USERS){
	//preconditions
	#g.registeredUserEmail[usr1]=1	//requisite 21
	#g.registeredUserType[usr1]=1 	//requisite 21
	#g.registeredUserEmail[usr2]=1	//requisite 21
	#g.registeredUserType[usr2]=1	//requisite 21
	#g.fileMode[file]=1 			//requisite 18
	#g.fileSize[file]=1 			//requisite 18
	#g.fileVersion[file]=1 			//requisite 18
	#g.fileOwner[file]=1 			//requisite 18
	file->usr1 in g.sharingOfFiles		//requisite 18 and 26
	file->usr2 not in g.sharingOfFiles	//requisite 18 and 27
	//operations
	g'.sharingOfFiles = g.sharingOfFiles + file-> usr2
	//coisas que nao se podem alterar
	g'.registeredUserEmail=g.registeredUserEmail
	g'.registeredUserType=g.registeredUserType
	g'.fileMode=g.fileMode
	g'.fileSize=g.fileSize
	g'.fileVersion=g.fileVersion
	g'.fileOwner=g.fileOwner
}



pred removeShare(g,g': gitBob, file: FILES, usr1, usr2: USERS){
	//preconditions
	#g.registeredUserEmail[usr1]=1 	//requisite 21
	#g.registeredUserType[usr1]=1 	//requisite 21
	#g.registeredUserEmail[usr2]=1 	//requisite 21
	#g.registeredUserType[usr2]=1 	//requisite 21
	#g.fileMode[file]=1 			//requisite 18
	#g.fileSize[file]=1 			//requisite 18
	#g.fileVersion[file]=1 			//requisite 18
	#g.fileOwner[file]=1 			//requisite 18
	file->usr1 in g.sharingOfFiles 		//requisite 18 and 28
	file->usr2 in g.sharingOfFiles 		//requisite 18 and 28
	file->usr2 not in g.fileOwner	//requisite 28
	//operations
	g'.sharingOfFiles = g.sharingOfFiles - file-> usr2
	//coisas que nao se podem alterar
	g'.registeredUserEmail=g.registeredUserEmail
	g'.registeredUserType=g.registeredUserType
	g'.fileMode=g.fileMode
	g'.fileSize=g.fileSize
	g'.fileVersion=g.fileVersion
	g'.fileOwner=g.fileOwner
}



pred changeSharingMode(g,g': gitBob, file: FILES, usr: USERS, mode: MODE){
	//preconditions
	#g.registeredUserEmail[usr]=1	//requisite 21
	#g.registeredUserType[usr]=1 	//requisite 21
	#g.fileMode[file]=1 			//requisite 18
	#g.fileSize[file]=1 			//requisite 18
	#g.fileVersion[file]=1 			//requisite 18
	file->usr in g.fileOwner 		//requisite 18 and 35
	(mode=SECURE => all u:USERS| g.registeredUserType[u]=PREMIUM)	//requisite 30 and 36
	//operations
	g'.fileMode = g.fileMode -  file->g.fileMode[file] + file->mode		//requisite 29
	//coisas que nao se podem alterar
	g'.registeredUserEmail=g.registeredUserEmail
	g'.registeredUserType=g.registeredUserType
	g'.fileSize=g.fileSize
	g'.fileVersion=g.fileVersion
	g'.fileOwner=g.fileOwner
	g'.sharingOfFiles=g.sharingOfFiles
}	


run newUser for 3 but 3 gitBob , 2 USERS , 2 UEMAILS

	
