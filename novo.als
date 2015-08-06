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

sig Nome{}
sig Telefone{}
sig Cliente {
--	nome: one Nome,
--	tel: one Telefone,
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
	all car: Carro, loc: Locadora, t: Time | carroNaLocadora[car,loc,t]

}

fact  Clientes {
	all cli:Cliente, loc:Locadora, t:Time | clienteNaoEhVip[cli,loc,t]
	all cli:Cliente,t:Time | #(cli.alugadosNac).t + #(cli.alugadosImp).t <= 3
	all t: Time | carroNacEhAlugadoAUmUnicoCliente[t] 
	all t: Time | carroImpEhAlugadoAUmUnicoCliente[t] 
	all t:Time, cli:Cliente, loc:Locadora | cli !in (loc.clientes).t => #cli.alugadosNac = 0
	all t:Time, cli:Cliente, loc:Locadora | cli !in (loc.clientes).t => #cli.alugadosImp = 0
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

pred carroNaLocadora[c:Carro, l: Locadora, t:Time]{
	c in (l.carrosDisponiveis).t and c !in (l.carrosAlugados).t or
	c !in (l.carrosDisponiveis).t and c in (l.carrosAlugados).t 
}

pred clienteNaoEhVip[c:Cliente, l:Locadora, t:Time]{
	c in (l.clientesVip).t => c in (l.clientes).t
}

pred carroNacEhAlugadoAUmUnicoCliente[t: Time] { -- Um animal pertence a um único abrigo
	all car:Carro,cli:Cliente | (car in cli.alugadosNac.t) => 
	(all cli2:Cliente-cli| car !in cli2.alugadosNac.t)
}


pred carroImpEhAlugadoAUmUnicoCliente[t: Time] { -- Um animal pertence a um único abrigo
	all car:Carro,cli:Cliente | (car in cli.alugadosImp.t)=> 
	(all cli2:Cliente-cli| car !in cli2.alugadosImp.t)
}

/*
pred clienteSoAlugaCadastrado[cli:Cliente, loc:Locadora, t:Time]{
	#(cli.alugadosNac).t > 0 or #(cli.alugadosImp).t > 0 => cli in (loc.clientes).t
}

pred carroTemUmCliente[car:Carro,l:Locadora, t: Time] {
	car in (l.carrosAlugados).t => one c:Cliente | car in (c.alugadosNac).t or car in (c.alugadosImp).t 
}

pred carroAlugadoOuNao[car: Carro, loc:Locadora, t:Time]{
	car in (loc.carrosAlugados).t and car !in (loc.carrosDisponiveis).t or
	car !in (loc.carrosAlugados).t and car in (loc.carrosDisponiveis).t 
}

pred clienteTemImp[cli:Cliente, loc: Locadora, t: Time]{ -- Cliente só tem carro importado se for vip
	#(cli.alugadosImp).t > 0 => cli in (loc.clientesVip).t
 }

pred carroDisponivel[car:Carro, loc:Locadora, cli:Cliente, t: Time]{
	car in (loc.carrosDisponiveis).t => car !in (cli.alugadosNac).t and car !in (cli.alugadosImp).t
}


/*--------------------------------------------Traces-----------------------------------------------------------*/

fact traces {
	init [first]	
 	all pre: Time-last | let pos = pre.next |
	one cli:Cliente, loc:Locadora | some car:CarroNac | cadastrarCliente[cli,loc,pre,pos] or alugarCarroNac[cli,car,loc,pre,pos]
	--some cli : Cliente | one loc: Locadora | some carN:CarroNac | some carImp: CarroImp |
		--	alugarCarroNac[cli,carN,loc,pre,pos] or alugarCarroImp[cli,carImp,loc,pre,pos] or
		--	viraClienteVip[cli,loc,pre,pos] or cadastrarCliente[cli, loc,pre,pos]
}

/*--------------------------------------------Operações--------------------------------------------------------*/

-- OPERAÇÃO CADASTRAR CLIENTE
pred cadastrarCliente[cli: Cliente, loc: Locadora, t, t': Time] {
	cli !in (loc.clientes).t
	(loc.clientes).t' = (loc.clientes).t + cli
}

-- OPERAÇÃO TORNAR UM CLIENTE VIP
pred viraClienteVip[cli: Cliente, loc: Locadora,t, t':Time]{
	--(#(cli.alugadosNac).t) + (#(cli.alugadosImp).t) >= 2 and
	cli in (loc.clientes).t =>
	(loc.clientes).t' = (loc.clientes).t - cli
	(loc.clientesVip).t' = (loc.clientesVip).t + cli
}

-- OPERAÇÃO ALUGAR CARRO NACIONAL
pred alugarCarroNac[cli: Cliente, car: CarroNac, l:Locadora, t,t': Time]{
	(cli in (l.clientes).t and car in (l.carrosDisponiveis).t and
	#(cli.alugadosNac).t + #(cli.alugadosNac).t < 3) =>
	(l.carrosDisponiveis).t' = (l.carrosDisponiveis).t - car
	(cli.alugadosNac).t' = (cli.alugadosNac).t + car
	(l.carrosAlugados).t' = (l.carrosAlugados).t + car
	viraClienteVip[cli,l,t,t']
}

/*
-- OPERAÇÃO ALUGAR CARRO IMPORTADO
pred alugarCarroImp[cli: Cliente, car: CarroImp, l:Locadora, t,t': Time]{
	(cli in (l.clientes).t and	car in (l.carrosDisponiveis).t and cli in (l.clientesVip).t and
	car !in (cli.alugadosImp).t and #(cli.alugadosNac).t + #(cli.alugadosNac).t <= 3) => 
	((cli.alugadosImp).t' = (cli.alugadosImp).t + car and
	(l.carrosDisponiveis).t' = (l.carrosDisponiveis).t - car and
	(l.carrosAlugados).t' = (l.carrosAlugados).t + car)
}

-- OPERAÇÃO DEVOLVER CARRO IMPORTADO
pred devolverCarroImp[cli: Cliente, car: CarroImp, l:Locadora, t,t': Time]{
	cli in (l.clientes).t and	car in (l.carrosAlugados).t and
	car in (cli.alugadosImp).t =>
	(cli.alugadosImp).t' = (cli.alugadosImp).t - car
	(l.carrosDisponiveis).t' = (l.carrosDisponiveis).t + car
	(l.carrosAlugados).t' = (l.carrosAlugados).t - car
}

-- OPERAÇÃO DEVOLVER CARRO NACIONAL
pred devolverCarroNac[cli: Cliente, car: CarroNac, l:Locadora, t,t': Time]{
	cli in (l.clientes).t and	car in (l.carrosAlugados).t and
	car in (cli.alugadosNac).t =>
	(l.carrosDisponiveis).t' = (l.carrosDisponiveis).t + car	
	(cli.alugadosNac).t' = (cli.alugadosNac).t - car
	(l.carrosAlugados).t' = (l.carrosAlugados).t - car
}




/*--------------------------------------------Asserts----------------------------------------------------------*/

pred show[]{
}

run show for 10
