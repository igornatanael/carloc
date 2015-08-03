module locadora
open util/ordering[Time] as to

/*--------------------------------------------Assinaturas------------------------------------------------------*/

sig Time{}


one sig Locadora { //Locadora onde todos os carros estão "guardados"
	carrosDisponiveis:  set Carro -> Time,
	carrosAlugados:  set Carro -> Time,
	clientesComuns: set Cliente -> Time,
	clientesVip: set Cliente -> Time
}

abstract sig Carro{
	cliente: set Cliente,
	locadora: one Locadora
}

sig CarroImp, CarroNac extends Carro{}

sig Cliente {
	locadora: one Locadora,
	alugadosNac: set CarroNac,
	alugadosImp: set CarroImp
}

/*--------------------------------------------Fatos------------------------------------------------------*/
fact{ //FATOS SOBRE LOCADORA
	one Locadora
}

fact { //FATOS SOBRE CARROS
	all car: Carro | carroTemUmaLocadora[car]
	all car: Carro | carroTemUmCliente[car]
}

fact  { //FATOS  SOBRE CLIENTES
	all c:Cliente | clienteTemUmaLocadora[c]
}

/*--------------------------------------------Funções-----------------------------------------------------*/

/*--------------------------------------------Predicados-----------------------------------------------------*/

pred carroTemUmaLocadora[car:Carro] {
	one car.locadora
}

pred carroTemUmCliente[car:Carro] {
	#(car.cliente) = 0 or #(car.cliente) = 1
	one car.locadora
}

pred clienteTemUmaLocadora[cli:Cliente] {
	one cli.locadora
}

/*--------------------------------------------Asserts-----------------------------------------------------*/


pred show[]{
}

run show for 7
