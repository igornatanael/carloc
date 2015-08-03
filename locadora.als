module locadora
open util/ordering[Time] as to

/*--------------------------------------------Assinaturas------------------------------------------------------*/

sig Time{}

one sig Locadora { -- Locadora onde todos os carros estão "guardados"
	carrosDisponiveis:  set Carro -> Time,
	carrosAlugados:  set Carro -> Time,
	carrosDesejados: set Carro -> Time,
	clientes: set Cliente -> Time
}

abstract sig Carro{}

sig CarroImp, CarroNac extends Carro{}

sig Cliente {
	alugadosNac: set CarroNac -> Time,
	alugadosImp: set CarroImp -> Time
}

/*--------------------------------------------Fatos------------------------------------------------------*/

fact traces {
	init [first]	
 	all pre: Time-last | let pos = pre.next |
		some cli : Cliente, car: Carro, loc: Locadora |
			(cli.alugadosNac).pos = (cli.alugadosNac).pre + car and (loc.carrosAlugados).pos = (loc.carrosAlugados).pre + car
}

fact{ -- FATOS SOBRE LOCADORA
	one Locadora
}

fact { -- FATOS SOBRE CARROS
	all car: Carro | carroTemUmaLocadora[car]
	all car: Carro | carroTemUmCliente[car]
 	all car: Carro | all t: Time, l: Locadora | carroAlugadoOuNao[car,l,t]
}

fact  { -- FATOS  SOBRE CLIENTES
	all c:Cliente | clienteTemUmaLocadora[c]
}

/*--------------------------------------------Funções-----------------------------------------------------*/



/*--------------------------------------------Predicados-----------------------------------------------------*/

pred init[t: Time] { --Inicializador
	no (Locadora.carrosDesejados).t
	no (Locadora.carrosAlugados).t 	-- No tempo inicial a locadora não tem nenhum carro alugado
 	no (Cliente.alugadosNac).t 	-- No tempo inicial nenhum cliente tem carro alugado
	no (Cliente.alugadosImp).t 	-- No tempo inicial nenhum cliente tem carro alugado
}

pred carroTemUmaLocadora[car:Carro] {
	
}

pred carroTemUmCliente[car:Carro] {

}

pred carroAlugadoOuNao[car: Carro, loc:Locadora, t:Time]{
	car in (loc.carrosAlugados).t or car in (loc.carrosDisponiveis).t
}

pred clienteTemUmaLocadora[cli:Cliente] {

}

/*
pred alugaUmCarroNac[cli: Cliente, car: Carro, loc: Locadora, t, t': Time] { 	-- Aluga um carro
	 cli in (car.clientesComuns).t or cli 	in (car.clientesVip).t
	 car in (loc.carrosDisponiveis).t
	 (cli.alugadosNac).t' = (cli.alugadosNac).t + car
}

/*--------------------------------------------Asserts-----------------------------------------------------*/


pred show[]{
}

run show for 7
