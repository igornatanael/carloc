module locadora
open util/ordering[Time]

/*--------------------------------------------Assinaturas------------------------------------------------------*/

sig Time{}

one sig Locadora { -- Locadora onde todos os carros estão "guardados"
	carros: set Carro,
	clientes: Cliente -> Time,
	clientesVip: Cliente -> Time,
 	carrosDisponiveis: Carro -> Time,
	carrosAlugados: Carro -> Time
}

sig Nome{}
sig Telefone{}
sig Cliente {
	alugadosNac: CarroNac -> Time,
	alugadosImp: CarroImp -> Time
}

abstract sig Carro{
	locador: Cliente -> Time
}
sig CarroImp extends Carro{}
sig CarroNac extends Carro{}

/*--------------------------------------------Inicializador e Traces---------------------------------------------------------*/

pred init[t: Time] { --Inicializador
	no (Locadora.clientes).t
	no (Locadora.clientesVip).t -- Não possui clientes Vips no início
	no (Locadora.carrosAlugados).t 	-- No tempo inicial a locadora não tem nenhum carro alugado
 	no (Cliente.alugadosNac).t 	-- No tempo inicial nenhum cliente tem carro alugado
	no (Cliente.alugadosImp).t 	-- No tempo inicial nenhum cliente tem carro alugado
	no (Locadora.clientes).t -- Não possui clientes cadastrados no início
	no (Carro.locador).t
	all c: Carro | c in (Locadora.carrosDisponiveis).t -- todos os carros estão disponíveis no início
}

fact traces {
	init [first]	
 	all pre: Time-last | let pos = pre.next |
		some cli : Cliente | one loc: Locadora | --some carN:CarroNac |
			cadastraCliente[cli, loc, pre, pos]
}
/*--------------------------------------------Predicados-------------------------------------------------------*/

pred carroTemUmLocador[c:Carro, cli:Cliente, t:Time]{
	(cli in (c.locador).t) => (c in (cli.alugadosNac).t)
}

/*--------------------------------------------Fatos------------------------------------------------------------*/

fact Locadora{
	all c: Carro | c in Locadora.carros
}

fact Carros{
	all c:Carro | #(c.locador) <= 1
	all c:Carro, cli: Cliente, t:Time | carroTemUmLocador[c,cli,t]
}

fact Clientes{

}

/*--------------------------------------------Operações-------------------------------------------------------*/

pred cadastraCliente[cli:Cliente, loc: Locadora, t, t': Time]{
	cli !in (loc.clientes).t
	cli !in (loc.clientesVip).t
	(loc.clientes).t' = (loc.clientes).t + cli
}

pred alugarCarroNac[cli: Cliente, car: CarroNac, l:Locadora, t,t': Time]{
	cli in (l.clientes).t and
	car !in (cli.alugadosNac).t and
	#(car.locador) = 0 and
	#(cli.alugadosNac).t + #(cli.alugadosImp).t < 3 and
	(l.carrosDisponiveis).t' = (l.carrosDisponiveis).t - car and
	(l.carrosAlugados).t' = (l.carrosAlugados).t + car and
	(cli.alugadosNac).t' = (cli.alugadosNac).t + car and
	(car.locador).t' = 	(car.locador).t + cli 
}

pred show[]{}
run show for 10 but exactly 5 Carro
