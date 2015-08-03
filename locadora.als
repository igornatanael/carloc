module locadora
open util/ordering[Time] as to

/*--------------------------------------------Assinaturas------------------------------------------------------*/

sig Time{}


one sig Locadora { //Locadora onde todos os carros estão "guardados"
	carros:  Carro,
	clientesComuns: Cliente -> Time,
	clientesVip: Cliente -> Time
}

abstract sig Carro{}
sig CarroImp extends Carro{}
sig CarroNac extends Carro{}


sig Cliente {
	alugadosComun: set Carro,
	alugadosVip: set Carro
}

sig ClienteVIP in Cliente {}

/*--------------------------------------------Fatos------------------------------------------------------*/
fact{ //FATOS SOBRE LOCADORA
	one Locadora
	some l: Locadora | #(l.carros) >= 1 	//Uma locadora possui carros nacionais e importados
	

}

fact { //FATOS SOBRE CARROS
	all c:Carro | one c.~carros	
	// CarroImp só pode ser alugado por ClienteVIP
}

fact  { //FATOS  SOBRE CLIENTES
}

/*--------------------------------------------Funções-----------------------------------------------------*/

/*--------------------------------------------Predicados-----------------------------------------------------*/

/*--------------------------------------------Asserts-----------------------------------------------------*/


pred show[]{
}

run show for 4
