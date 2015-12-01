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
		some u:USERS, m: UEMAILS, t: UTYPES,file: FILES, size: Int,owner: USERS|
		//g'.registeredUserEmail=g.registeredUserEmail para todas as relaçoes do gitBob de forma a forçarmos 
		//o git seguinte a ter tudo igual ao anterior e so depois executamos um predicado
     		newUser[g, g', u, m, t] or removeUser[g,g',u] or upgradeUser[g,g',u] or 
		addFile[g,g', file, size, owner] or uploadFile[g,g', file, u] or downloadFile[g,g', file, u]
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
	//coisas que nao se podem alterar
	g'.fileMode=g.fileMode
	g'.fileSize=g.fileSize
	g'.fileVersion=g.fileVersion
	g'.fileOwner=g.fileOwner
	g'.sharingOfFiles=g.sharingOfFiles
	
}

assert newUserAdded{
	all g,g':gitBob, u:USERS, m: UEMAILS, t: UTYPES|
		(no u.(g.registeredUserEmail) and no u.(g.registeredUserType) and newUser[g,g',u,m,t])
			implies (u->m in g'.registeredUserEmail and u->t in g'.registeredUserType
			and g'.fileMode=g.fileMode and g'.fileSize=g.fileSize and g'.fileVersion=g.fileVersion
			and g'.fileOwner=g.fileOwner and g'.sharingOfFiles=g.sharingOfFiles)
			
}

check newUserAdded

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

assert removedUser{
	all g,g',g'':gitBob, u:USERS, m: UEMAILS, t: UTYPES|
		(no u.(g.registeredUserEmail) and no u.(g.registeredUserType) and newUser[g,g',u,m,t] and removeUser[g',g'',u])
			implies (u->m not in g''.registeredUserEmail and u->t not in g''.registeredUserType 
			and g'.fileMode=g.fileMode and g'.fileSize=g.fileSize and g'.fileVersion=g.fileVersion
			and g'.fileOwner=g.fileOwner and g'.sharingOfFiles=g.sharingOfFiles)
}

//requisite 24
assert noRemoveUserInSharingOfFiles{
	all g,g': gitBob, u:USERS,f: FILES|
		( !(no u.(g.registeredUserEmail)) and !(no u.(g.registeredUserType)) and f->u in g.sharingOfFiles  and f->u not in g.fileOwner 
			and removeUser[g,g',u]) implies (g'.registeredUserType=g.registeredUserType 
			and g'.registeredUserEmail=g.registeredUserEmail and g'.fileMode=g.fileMode 
			and g'.fileSize=g.fileSize and g'.fileVersion=g.fileVersion
			and g'.fileOwner=g.fileOwner and g'.sharingOfFiles=g.sharingOfFiles)
}



////requisite 14
assert noRemoveUserInFileOwner{
		all g,g': gitBob, u:USERS,f: FILES|
		( !(no u.(g.registeredUserEmail)) and !(no u.(g.registeredUserType)) and f->u  in g.fileOwner 
			and removeUser[g,g',u]) implies (g'.registeredUserType=g.registeredUserType 
			and g'.registeredUserEmail=g.registeredUserEmail and g'.fileMode=g.fileMode 
			and g'.fileSize=g.fileSize and g'.fileVersion=g.fileVersion
			and g'.fileOwner=g.fileOwner and g'.sharingOfFiles=g.sharingOfFiles)
}

assert noRemoveUserInexistent{
		all g,g': gitBob, u:USERS|
		( no u.(g.registeredUserEmail) and no u.(g.registeredUserType) and removeUser[g,g',u]) 
			implies (g'.registeredUserType=g.registeredUserType 
			and g'.registeredUserEmail=g.registeredUserEmail and g'.fileMode=g.fileMode 
			and g'.fileSize=g.fileSize and g'.fileVersion=g.fileVersion
			and g'.fileOwner=g.fileOwner and g'.sharingOfFiles=g.sharingOfFiles)
}

check noRemoveUserInFileOwner
check noRemoveUserInexistent

pred upgradeUser(g,g': gitBob, u: USERS){
	//preconditions
	#g.registeredUserEmail[u]=1 //requisite 7
	#g.registeredUserType[u]=1 //requisite 7
	g.registeredUserType[u]=BASIC //requisite 9
	//operation
	g'.registeredUserType[u]= PREMIUM
	//coisas que nao se podem alterar
	g'.registeredUserEmail=g.registeredUserEmail
	g'.fileMode=g.fileMode
	g'.fileSize=g.fileSize
	g'.fileVersion=g.fileVersion
	g'.fileOwner=g.fileOwner
	g'.sharingOfFiles=g.sharingOfFiles
}

assert upgradedUser{
	all g,g':gitBob, u:USERS|
		(!(no u.(g.registeredUserEmail)) and !(no u.(g.registeredUserType)) 
		and u->BASIC in g.registeredUserType and upgradeUser[g, g', u])
			implies (g'.registeredUserEmail=g.registeredUserEmail and g'.registeredUserType[u]=PREMIUM 
			and g'.fileMode=g.fileMode and g'.fileSize=g.fileSize and g'.fileVersion=g.fileVersion
			and g'.fileOwner=g.fileOwner and g'.sharingOfFiles=g.sharingOfFiles)
}

assert noUpgradeUserInexistent{
	all g,g':gitBob, u:USERS|
		(no u.(g.registeredUserEmail) and no u.(g.registeredUserType) 
		and upgradeUser[g, g', u])
			implies (g'.registeredUserEmail=g.registeredUserEmail and g'.registeredUserType=g.registeredUserType 
			and g'.fileMode=g.fileMode and g'.fileSize=g.fileSize and g'.fileVersion=g.fileVersion
			and g'.fileOwner=g.fileOwner and g'.sharingOfFiles=g.sharingOfFiles)
}

assert noUpgradeUserPremium{
	all g,g':gitBob, u:USERS|
		(!(no u.(g.registeredUserEmail)) and !(no u.(g.registeredUserType)) 
		and u->PREMIUM in g.registeredUserType and upgradeUser[g, g', u])
			implies (g'.registeredUserEmail=g.registeredUserEmail and g'.registeredUserType=g.registeredUserType 
			and g'.fileMode=g.fileMode and g'.fileSize=g.fileSize and g'.fileVersion=g.fileVersion
			and g'.fileOwner=g.fileOwner and g'.sharingOfFiles=g.sharingOfFiles)
}

check upgradedUser
check noUpgradeUserInexistent
check noUpgradeUserPremium


pred downgradeBasic(g,g': gitBob, u: USERS){
	//preconditions
	#g.registeredUserEmail[u]=1 				//requisite 8
	#g.registeredUserType[u]=1				//requisite 8
	g.registeredUserType[u]=PREMIUM			//requisite 9
	(all f: g.sharingOfFiles.u| g.fileMode[f]!= SECURE) 	//requisite 31
	//operation
	g'.registeredUserType[u]= BASIC
	//coisas que nao se podem alterar
	g'.registeredUserEmail=g.registeredUserEmail
	g'.fileMode=g.fileMode
	g'.fileSize=g.fileSize
	g'.fileVersion=g.fileVersion
	g'.fileOwner=g.fileOwner
	g'.sharingOfFiles=g.sharingOfFiles
}

//requsite 8
assert downgradeBasicUser{
		all g,g':gitBob, u:USERS|
		(!(no u.(g.registeredUserEmail)) and !(no u.(g.registeredUserType)) 
		and u->PREMIUM in g.registeredUserType and (all f: g.sharingOfFiles.u| g.fileMode[f]!= SECURE)
		 and downgradeBasic[g, g', u])
			implies (g'.registeredUserEmail=g.registeredUserEmail and g'.registeredUserType[u]=BASIC 
			and g'.fileMode=g.fileMode and g'.fileSize=g.fileSize and g'.fileVersion=g.fileVersion
			and g'.fileOwner=g.fileOwner and g'.sharingOfFiles=g.sharingOfFiles)
}

//requsite 6
assert noDowngradeBasicInexistent{
	all g,g':gitBob, u:USERS|
		(no u.(g.registeredUserEmail) and no u.(g.registeredUserType) 
		and downgradeBasic[g, g', u])
			implies (g'.registeredUserEmail=g.registeredUserEmail and g'.registeredUserType=g.registeredUserType 
			and g'.fileMode=g.fileMode and g'.fileSize=g.fileSize and g'.fileVersion=g.fileVersion
			and g'.fileOwner=g.fileOwner and g'.sharingOfFiles=g.sharingOfFiles)
}

//requsite 9
assert noDowngradeBasic{
	all g,g':gitBob, u:USERS|
		(!(no u.(g.registeredUserEmail)) and !(no u.(g.registeredUserType)) 
		and u->BASIC in g.registeredUserType and downgradeBasic[g, g', u])
			implies (g'.registeredUserEmail=g.registeredUserEmail and g'.registeredUserType=g.registeredUserType 
			and g'.fileMode=g.fileMode and g'.fileSize=g.fileSize and g'.fileVersion=g.fileVersion
			and g'.fileOwner=g.fileOwner and g'.sharingOfFiles=g.sharingOfFiles)
}

//requisite 31
assert noDowngradeBasicInSecureShare{
	all g,g':gitBob, u:USERS, f: FILES|
		(!(no u.(g.registeredUserEmail)) and !(no u.(g.registeredUserType)) 
		and u->PREMIUM in g.registeredUserType and  f->u in  g.sharingOfFiles and g.fileMode[f]=SECURE
		 and downgradeBasic[g, g', u])
			implies (g'.registeredUserEmail=g.registeredUserEmail and g'.registeredUserType[u]=BASIC 
			and g'.fileMode=g.fileMode and g'.fileSize=g.fileSize and g'.fileVersion=g.fileVersion
			and g'.fileOwner=g.fileOwner and g'.sharingOfFiles=g.sharingOfFiles)

}
check downgradeBasicUser
check noDowngradeBasicInexistent
check noDowngradeBasic
check noDowngradeBasicInSecureShare

pred addFile(g,g': gitBob, file:FILES, size:Int, owner: USERS){
	//preconditions
	#g.registeredUserEmail[owner]=1 	//requisite 16
	#g.registeredUserType[owner]=1		//requisite 16
	#g.fileMode[file]=0 				//requisite 15
	#g.fileSize[file]=0				//requisite 15
	#g.fileVersion[file]=0				//requisite 15
	#g.fileOwner[file]=0				//requisite 15
	#g.sharingOfFiles[file]=0				//requisite 15
	//operation
	g'.fileMode = g.fileMode + file->REGULAR 	//requisite 29 and 32
	g'.fileSize = g.fileSize + file-> size
	g'.fileVersion = g.fileVersion + file ->1 		//requisite 17
	g'.fileOwner = g.fileOwner + file-> owner
	g'.sharingOfFiles = g.sharingOfFiles + file-> owner 	//requisite 22
	//coisas que nao se podem alterar
	g'.registeredUserEmail=g.registeredUserEmail
	g'.registeredUserType=g.registeredUserType
}

assert addedFile{
	all g,g':gitBob, owner:USERS, file: FILES, size: Int|
		(!(no owner.(g.registeredUserEmail)) and !(no owner.(g.registeredUserType)) 
		and no g.fileMode[file] and no g.fileSize[file] and no g.fileVersion[file] 
		and no g.fileOwner[file] and no g.sharingOfFiles[file] and addFile[g,g', file, size, owner])
			implies (g'.registeredUserEmail=g.registeredUserEmail and g'.registeredUserType=g.registeredUserType
			and g'.fileMode[file]=REGULAR and g'.fileSize[file]=size and g'.fileVersion[file]=1
			and g'.fileOwner[file]=owner and file->owner in g'.sharingOfFiles)
}

assert noAddedFileExists{
	all g,g':gitBob, owner:USERS, file: FILES, size: Int|
		(!(no owner.(g.registeredUserEmail)) and !(no owner.(g.registeredUserType)) 
		and !(no g.fileMode[file]) and !(no g.fileSize[file]) and !(no g.fileVersion[file]) 
		and !(no g.fileOwner[file]) and !(no g.sharingOfFiles[file]) and addFile[g,g', file, size, owner])
			implies (g'.registeredUserEmail=g.registeredUserEmail and g'.registeredUserType=g.registeredUserType
			and g'.fileMode=g.fileMode and g'.fileSize=g.fileSize and g'.fileVersion=g.fileVersion
			and g'.fileOwner=g.fileOwner and g'.sharingOfFiles=g.sharingOfFiles)
}

assert noAddedFileUserNotRegistered{
	all g,g':gitBob, owner:USERS, file: FILES, size: Int|
		(no owner.(g.registeredUserEmail) and no owner.(g.registeredUserType) 
		and !(no g.fileMode[file]) and !(no g.fileSize[file]) and !(no g.fileVersion[file]) 
		and !(no g.fileOwner[file]) and !(no g.sharingOfFiles[file]) and addFile[g,g', file, size, owner])
			implies (g'.registeredUserEmail=g.registeredUserEmail and g'.registeredUserType=g.registeredUserType
			and g'.fileMode=g.fileMode and g'.fileSize=g.fileSize and g'.fileVersion=g.fileVersion
			and g'.fileOwner=g.fileOwner and g'.sharingOfFiles=g.sharingOfFiles)
}

check addedFile
check noAddedFileExists
check noAddedFileUserNotRegistered

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


assert removedFile{
	all g,g':gitBob, user:USERS, file: FILES|
		(!(no user.(g.registeredUserEmail)) and !(no user.(g.registeredUserType)) 
		and  !(no g.fileMode[file]) and !(no g.fileSize[file]) and !(no g.fileVersion[file]) 
		and !(no g.fileOwner[file]) and !(no g.sharingOfFiles[file]) and removeFile[g,g',file,user])
			implies (g'.registeredUserEmail=g.registeredUserEmail and g'.registeredUserType=g.registeredUserType
			and no g'.fileMode[file] and no  g'.fileSize[file] and no g'.fileVersion[file]
			and no g'.fileOwner[file] and no g'.sharingOfFiles[file])
}

//requisite 18
assert noRemoveFileDontExists{
	all g,g':gitBob, user:USERS, file: FILES|
		(!(no user.(g.registeredUserEmail)) and !(no user.(g.registeredUserType)) 
		and  no g.fileMode[file] and no g.fileSize[file] and no g.fileVersion[file]
		and no g.fileOwner[file] and no g.sharingOfFiles[file] and removeFile[g,g',file,user])
			implies (g'.registeredUserEmail=g.registeredUserEmail and g'.registeredUserType=g.registeredUserType
			and g'.fileMode=g.fileMode and g'.fileSize=g.fileSize and g'.fileVersion=g.fileVersion
			and g'.fileOwner=g.fileOwner and g'.sharingOfFiles=g.sharingOfFiles)
}

//requisite 25
assert noRemoveFileUserDontAcess{
	all g,g':gitBob, user:USERS, file: FILES|
		(!(no user.(g.registeredUserEmail)) and !(no user.(g.registeredUserType)) 
		and  !(no g.fileMode[file]) and !(no g.fileSize[file]) and !(no g.fileVersion[file]) 
		and !(no g.fileOwner[file]) and file->user not in g.sharingOfFiles and removeFile[g,g',file,user])
			implies (g'.registeredUserEmail=g.registeredUserEmail and g'.registeredUserType=g.registeredUserType
			and g'.fileMode=g.fileMode and g'.fileSize=g.fileSize and g'.fileVersion=g.fileVersion
			and g'.fileOwner=g.fileOwner and g'.sharingOfFiles=g.sharingOfFiles)
}

//requisite 33
assert noRemoveFileNotOwner{
	all g,g':gitBob, user:USERS, file: FILES|
		(!(no user.(g.registeredUserEmail)) and !(no user.(g.registeredUserType)) 
		and g.fileMode[file]=READONLY and !(no g.fileSize[file]) and !(no g.fileVersion[file]) 
		and g.fileOwner[file]!= user and file->user in g.sharingOfFiles and removeFile[g,g',file,user])
			implies (g'.registeredUserEmail=g.registeredUserEmail and g'.registeredUserType=g.registeredUserType
			and g'.fileMode=g.fileMode and g'.fileSize=g.fileSize and g'.fileVersion=g.fileVersion
			and g'.fileOwner=g.fileOwner and g'.sharingOfFiles=g.sharingOfFiles)
}

check removedFile
check noRemoveFileDontExists
check noRemoveFileUserDontAcess
check noRemoveFileNotOwner


pred uploadFile(g,g': gitBob, file:FILES, usr: USERS){
	//preconditions
	#g.fileMode[file]=1 	//requisite 18
	#g.fileSize[file]=1 	//requisite 18
	#g.fileVersion[file]=1 	//requisite 18
	#g.fileOwner[file]=1 	//requisite 18
	file->usr in g.sharingOfFiles //requisite 18 and 25
	(g.fileMode[file]=READONLY => g.fileOwner[file]=usr)	//requisite 34
	//operations
	g'.fileVersion[file] = g.fileVersion[file].next	//requisite 19
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
	g'.fileMode[file] = mode		//requisite 29
	//coisas que nao se podem alterar
	g'.registeredUserEmail=g.registeredUserEmail
	g'.registeredUserType=g.registeredUserType
	g'.fileSize=g.fileSize
	g'.fileVersion=g.fileVersion
	g'.fileOwner=g.fileOwner
	g'.sharingOfFiles=g.sharingOfFiles
}	


run newUser for 3 but 3 gitBob , 2 USERS , 2 UEMAILS

	
