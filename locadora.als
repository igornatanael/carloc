module locadora
open util/ordering[Time]

/*--------------------------------------------Assinaturas------------------------------------------------------*/

sig Time{}

one sig Locadora { -- Locadora onde todos os carros estão "guardados"
	clientesVip: set ClienteVip -> Time,
 	carrosDisponiveis:  Carro -> Time,
	carrosAlugados:  Carro -> Time,
	carrosDesejados: Carro -> Time,
	clientes: Cliente -> Time
}

sig Cliente {
	alugadosNac: CarroNac -> Time,
	alugadosImp:  CarroImp -> Time,
   desejados:  Carro -> Time
}
sig ClienteVip in Cliente{}

abstract sig Carro{}
sig CarroImp extends Carro{}
sig CarroNac extends Carro{}


/*--------------------------------------------Fatos------------------------------------------------------*/

fact traces {
	init [first]	
 	all pre: Time-last | let pos = pre.next |
		some cli : Cliente, loc: Locadora |
			clienteVipNaLista[cli,loc,pre, pos]	
}

fact{ -- FATOS SOBRE LOCADORA
	one Locadora
}

fact { -- FATOS SOBRE CARROS
	all car: Carro | all t: Time | carroTemUmCliente[car, t]
 	all car: Carro | all t: Time, l: Locadora | carroAlugadoOuNao[car,l,t]
}

fact  { -- FATOS SOBRE CLIENTES
	all c:Cliente | clienteTemUmaLocadora[c]
	all c:Cliente | one l: Locadora | all t: Time | clienteTemUmaLocadora[c,l,t]
}

/*--------------------------------------------Funções--------------------------------------------------------*/



/*--------------------------------------------Predicados-----------------------------------------------------*/

pred init[t: Time] { --Inicializador
	no (Locadora.clientesVip).t
	no (Locadora.carrosDesejados).t
	no (Locadora.carrosAlugados).t 	-- No tempo inicial a locadora não tem nenhum carro alugado
 	no (Cliente.alugadosNac).t 	-- No tempo inicial nenhum cliente tem carro alugado
	no (Cliente.alugadosImp).t 	-- No tempo inicial nenhum cliente tem carro alugado
}

pred carroTemUmCliente[car:Carro, t: Time] {

}

pred alugarCarroImportado[cli: Cliente, car: Carro, t,t': Time]{
	car !in (cli.alugadosImp).t and #(cli.alugadosNac).t + #(cli.alugadosNac).t <= 3
}

pred carroAlugadoOuNao[car: Carro, loc:Locadora, t:Time]{
	car in (loc.carrosAlugados).t or car in (loc.carrosDisponiveis).t
}

pred clienteTemUmaLocadora[cli:Cliente, loc: Locadora, t: Time] {
	cli in (loc.clientes).t
}

pred clienteVipNaLista[cli:ClienteVip, loc: Locadora, t: Time, t': Time]{
	cli !in (loc.clientesVip).t => (loc.clientesVip).t' = (loc.clientesVip).t' + cli
 }


/*
pred alugaUmCarroNac[cli: Cliente, car: Carro, loc: Locadora, t, t': Time] { 	-- Aluga um carro
	 cli in (car.clientesComuns).t or cli 	in (car.clientesVip).t
	 car in (loc.carrosDisponiveis).t
	 (cli.alugadosNac).t' = (cli.alugadosNac).t + car
}


/*--------------------------------------------Operações----------------------------------------------------*/

-- OPERAÇÃO CADASTRAR CLIENTE
pred cadastrarCliente[cli: Cliente, loc: Locadora, t, t': Time] {
	cli !in (loc.clientes).t
	(loc.clientes).t' = (loc.clientes).t + cli
}


/*--------------------------------------------Asserts-----------------------------------------------------*/


pred show[]{
}

run show for 10
