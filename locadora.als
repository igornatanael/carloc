module locadora
open util/ordering[Time]

/*--------------------------------------------Assinaturas------------------------------------------------------*/

sig Time{}

one sig Locadora { -- Locadora onde todos os carros estão "guardados"
	clientesVip: set Cliente -> Time,
 	carrosDisponiveis: set Carro -> Time,
	carrosAlugados: set Carro -> Time,
	carrosDesejados: set Carro -> Time,
	clientes: Cliente -> Time
}

sig Cliente {
	alugadosNac: CarroNac -> Time,
	alugadosImp:  CarroImp -> Time,
   desejados:  Carro -> Time
}

abstract sig Carro{}
sig CarroImp extends Carro{}
sig CarroNac extends Carro{}


/*--------------------------------------------Fatos------------------------------------------------------*/

fact traces {
	init [first]	
 	all pre: Time-last | let pos = pre.next |
		some cli : Cliente, loc: Locadora, carN:CarroNac, carImp: CarroImp|
			clienteVipNaLista[cli,loc,pre, pos] or viraClienteVip[cli, loc, pre, pos] or
			alugarCarroNac[cli,carN,loc,pre,pos] or alugarCarroImp[cli,carImp,loc,pre,pos] 
}

fact Locadora{
	one Locadora
}

fact Carros{
	all car: Carro | all t: Time | carroTemUmCliente[car, t]
 	all car: Carro | all t: Time, l: Locadora | carroAlugadoOuNao[car,l,t]
	all car: Carro, t:Time, l: Locadora | carroDesejado[car,l,t]
	all car: Carro, t:Time, l: Locadora | carroDisponivel[car,l,t]
}

fact  Clientes {
	all c:Cliente | one l: Locadora | all t: Time | clienteTemUmaLocadora[c,l,t]
	some c:Cliente, t:Time,l: Locadora | ehClienteVip[c,l,t]
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

pred carroDesejado[car:Carro,l:Locadora,t:Time]{
	car in (l.carrosDesejados).t => car in (l.carrosAlugados).t
}

pred carroDisponivel[car:Carro,l:Locadora,t:Time]{
	car in (l.carrosDisponiveis).t => car !in (l.carrosAlugados).t and car !in (l.carrosDesejados).t
}

pred carroTemUmCliente[car:Carro, t: Time] {

}

pred ehClienteVip[c:Cliente,l: Locadora, t:Time]{
	c in (l.clientesVip).t
}

pred viraClienteVip[c:Cliente,l:Locadora,t, t':Time]{
	#(c.alugadosNac).t >= 2
	(l.clientesVip).t' = (l.clientesVip).t + c
}

pred alugarCarroImp[cli: Cliente, car: CarroImp, l:Locadora, t,t': Time]{
	car in (l.carrosDisponiveis).t and cli in (l.clientesVip).t
	car !in (cli.alugadosImp).t and #(cli.alugadosNac).t + #(cli.alugadosNac).t <= 3
	(cli.alugadosImp).t' = (cli.alugadosImp).t + car
}

pred alugarCarroNac[cli: Cliente, car: CarroNac, l:Locadora, t,t': Time]{
	car in (l.carrosDisponiveis).t and cli in (l.clientes).t
	car !in (cli.alugadosNac).t and #(cli.alugadosNac).t + #(cli.alugadosNac).t <= 3
	(cli.alugadosNac).t' = (cli.alugadosNac).t + car
}

pred carroAlugadoOuNao[car: Carro, loc:Locadora, t:Time]{
	car in (loc.carrosAlugados).t or car in (loc.carrosDisponiveis).t
}

pred clienteTemUmaLocadora[cli:Cliente, loc: Locadora, t: Time] {
	cli in (loc.clientes).t
}

pred clienteVipNaLista[cli:Cliente, loc: Locadora, t: Time, t': Time]{
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

run show for 10  but exactly 5 Carro, exactly 5 Cliente
