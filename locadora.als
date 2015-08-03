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

pred init[t: Time] { --Inicializador
	no (Carro.cliente).t  -- No tempo inicial carros não podem ter cliente
	no (Locadora.carrosAlugados).t 	-- No tempo inicial a locadora não tem nenhum carro alugado
	no (Locadora.clientesVip).t 	--No tempo inicial nenhum cliente é VIP, pois ainda não possui nenhum carro alugado
 	no (Cliente.alugadosNac).t 	-- No tempo inicial nenhum cliente tem carro alugado
	no (Cliente.alugadosImp).t 	-- No tempo inicial nenhum cliente tem carro alugado
}

pred carroTemUmaLocadora[car:Carro] {
	one car.locadora
}

pred carroTemUmCliente[car:Carro] {
	#(car.cliente) = 0 or #(car.cliente) = 1
}

pred clienteTemUmaLocadora[cli:Cliente] {
	one cli.locadora
}

/*--------------------------------------------Asserts-----------------------------------------------------*/


pred show[]{
}

run show for 7
