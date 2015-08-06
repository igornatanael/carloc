module locadora
open util/ordering[Time]

/*--------------------------------------------Assinaturas------------------------------------------------------*/

sig Time{}

one sig Locadora { -- Locadora onde todos os carros estão "guardados"
	clientes: Cliente -> Time,
	clientesVip: Cliente -> Time,
 	carrosDisponiveis: Carro -> Time,
	carrosAlugados: Carro -> Time
}

sig Cliente {
	alugadosNac: CarroNac -> Time,
	alugadosImp: CarroImp -> Time
}

abstract sig Carro{}
sig CarroImp extends Carro{}
sig CarroNac extends Carro{}

/*--------------------------------------------Fatos------------------------------------------------------------*/

fact Locadora{
}

fact Carros{
	all car: Carro, t: Time, l: Locadora| carroTemUmCliente[car, l, t]
 	all car: Carro, t: Time, l: Locadora | carroAlugadoOuNao[car, l, t]
	all car: Carro, t:Time, l: Locadora | carroDisponivel[car, l, t]
}

fact  Clientes {
	--some c:Cliente, t:Time,l: Locadora | some t':Time | ehClienteVip[c,l,t,t']
	all c:Cliente, t: Time, l:Locadora | clienteTemImp[c,l,t]
--	all c:Cliente, loc:Locadora, t: Time | clienteSoAlugaCadastrado[c,loc,t]
	!one c:Cliente, loc:Locadora, t:Time | clienteSoAlugaCadastrado[c,loc,t]
	all c:Cliente, loc:Locadora, t:Time | c in (loc.clientesVip).t => c in (loc.clientes).t

}

/*--------------------------------------------Funções----------------------------------------------------------*/

/*--------------------------------------------Predicados-------------------------------------------------------*/

pred init[t: Time] { --Inicializador
	no (Locadora.clientesVip).t -- Não possui clientes Vips no início
	no (Locadora.carrosAlugados).t 	-- No tempo inicial a locadora não tem nenhum carro alugado
 	no (Cliente.alugadosNac).t 	-- No tempo inicial nenhum cliente tem carro alugado
	no (Cliente.alugadosImp).t 	-- No tempo inicial nenhum cliente tem carro alugado
	no (Locadora.clientes).t -- Não possui clientes cadastrados no início
	all c: Carro | c in (Locadora.carrosDisponiveis).t -- todos os carros estão disponíveis no início
}

pred clienteSoAlugaCadastrado[cli:Cliente, loc:Locadora, t:Time]{
	((#((cli.alugadosNac).t) + #((cli.alugadosImp).t)) > 0) => cli in (loc.clientes).t
}

pred carroDisponivel[car:Carro,l:Locadora,t:Time]{
	car in (l.carrosDisponiveis).t => car !in (l.carrosAlugados).t
}

pred carroTemUmCliente[car:Carro,l:Locadora, t: Time] {
	car in (l.carrosAlugados).t => one c:Cliente | car in (c.alugadosNac).t or car in (c.alugadosImp).t 
}

pred ehClienteVip[c:Cliente,l: Locadora, t:Time,t':Time]{
	c in (l.clientesVip).t and c in (l.clientes).t
	#(c.alugadosNac).t' >= 2
}

pred carroAlugadoOuNao[car: Carro, loc:Locadora, t:Time]{
	car in (loc.carrosAlugados).t or car in (loc.carrosDisponiveis).t
}

pred clienteTemImp[cli:Cliente, loc: Locadora, t: Time]{ -- Cliente só tem carro importado se for vip
	#(cli.alugadosImp).t > 0 => cli in (loc.clientesVip).t
 }

/*--------------------------------------------Traces-----------------------------------------------------------*/

fact traces {
	init [first]	
 	all pre: Time-last | let pos = pre.next |
		all cli : Cliente | one loc: Locadora | all carN:CarroNac | all carImp: CarroImp |
			alugarCarroNac[cli,carN,loc,pre,pos] or alugarCarroImp[cli,carImp,loc,pre,pos] or
			viraClienteVip[cli,loc,pre,pos] or cadastrarCliente[cli, loc,pre,pos]
}

/*--------------------------------------------Operações--------------------------------------------------------*/

-- OPERAÇÃO CADASTRAR CLIENTE
pred cadastrarCliente[cli: Cliente, loc: Locadora, t, t': Time] {
	cli !in (loc.clientes).t and cli !in (loc.clientesVip).t
	#(cli.alugadosNac).t = 0 and #(cli.alugadosImp).t = 0
	(loc.clientes).t' = (loc.clientes).t + cli
}

-- OPERAÇÃO ALUGAR CARRO IMPORTADO
pred alugarCarroImp[cli: Cliente, car: CarroImp, l:Locadora, t,t': Time]{
	cli in (l.clientes).t and	car in (l.carrosDisponiveis).t and cli in (l.clientesVip).t
	car !in (cli.alugadosImp).t and #(cli.alugadosNac).t + #(cli.alugadosNac).t <= 3
	(cli.alugadosImp).t' = (cli.alugadosImp).t + car
	(l.carrosDisponiveis).t' = (l.carrosDisponiveis).t - car
	(l.carrosAlugados).t' = (l.carrosAlugados).t + car
}

-- OPERAÇÃO ALUGAR CARRO NACIONAL
pred alugarCarroNac[cli: Cliente, car: CarroNac, l:Locadora, t,t': Time]{
	cli in (l.clientes).t and	car in (l.carrosDisponiveis).t and cli in (l.clientes).t
	car !in (cli.alugadosNac).t and #(cli.alugadosNac).t + #(cli.alugadosNac).t <= 3
	(cli.alugadosNac).t' = (cli.alugadosNac).t + car
	(l.carrosDisponiveis).t' = (l.carrosDisponiveis).t - car
	(l.carrosAlugados).t' = (l.carrosAlugados).t + car
}

-- OPERAÇÃO TORNAR UM CLIENTE VIP
pred viraClienteVip[cli: Cliente, loc: Locadora,t, t':Time]{
	(#(cli.alugadosNac).t) >= 2
	cli in (loc.clientes).t
	cli !in (loc.clientesVip).t
	(loc.clientes).t' = (loc.clientes).t - cli
	(loc.clientesVip).t' = (loc.clientesVip).t + cli
}

/*--------------------------------------------Asserts----------------------------------------------------------*/

pred show[]{
}

run show for 10  but exactly 5 Carro, exactly 5 Cliente
