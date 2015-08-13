module locadora
open util/ordering[Time]

/*--------------------------------------------Assinaturas------------------------------------------------------*/

sig Time{}

one sig Locadora { -- Locadora onde todos os carros estão "guardados"
	clientes: Cliente -> Time,
	clientesVip: Cliente -> Time,
 	carrosDisponiveis: Carro -> Time,
	carrosAlugados: Carro -> Time,
	sujos: Cliente -> Time
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
	#Cliente = 3
	#CarroImp = 3
	#CarroNac = 5
}

fact Carros{
	all c: Carro, t:Time, l:Locadora | c in (l.carrosDisponiveis).t <=> c !in (l.carrosAlugados).t
	--all car: Carro, loc: Locadora, t: Time | carroNaLocadora[car,loc,t]
	all loc: Locadora, t: Time| some car:Carro, cli: Cliente | carroAlugado[car, cli,loc,t]
	all car: CarroImp, loc: Locadora, t: Time, cli: Cliente | importadoSohVip[car, cli, loc, t]
}

fact  Clientes {
	--all cli:Cliente, loc:Locadora, t:Time | clienteNaoEhVip[cli,loc,t]
	all t: Time | carroNacEhAlugadoAUmUnicoCliente[t] 
	all t: Time | carroImpEhAlugadoAUmUnicoCliente[t] 
	all t:Time, cli:Cliente, loc:Locadora | cli !in (loc.clientes).t => #cli.alugadosNac.t = 0
	all t:Time, cli:Cliente, loc:Locadora | cli !in (loc.clientes).t => #cli.alugadosImp.t = 0
	
}

/*--------------------------------------------Funções----------------------------------------------------------*/

/*--------------------------------------------Predicados-------------------------------------------------------*/

pred init[t: Time] { --Inicializador
	no (Locadora.clientesVip).t -- Não possui clientes Vips no início
	no (Locadora.carrosAlugados).t 	-- No tempo inicial a locadora não tem nenhum carro alugado
 	no (Cliente.alugadosNac).t 	-- No tempo inicial nenhum cliente tem carro alugado
	no (Cliente.alugadosImp).t 	-- No tempo inicial nenhum cliente tem carro alugado
	no (Locadora.clientes).t -- Não possui clientes cadastrados no início
	no (Locadora.sujos).t -- Locadora começa com a lista negra vazia
	all c: Carro | c in (Locadora.carrosDisponiveis).t -- todos os carros estão disponíveis no início
}

pred carroNaLocadora[c:Carro, l: Locadora, t:Time]{
	c in (l.carrosDisponiveis).t and c !in (l.carrosAlugados).t or
	c !in (l.carrosDisponiveis).t and c in (l.carrosAlugados).t 
}

pred clienteNaoEhVip[c:Cliente, l:Locadora, t:Time]{
	c in (l.clientesVip).t => c in (l.clientes).t
}

pred importadoSohVip[car:CarroImp, cli:Cliente, loc:Locadora, t:Time]{
	car in (cli.alugadosImp).t => (cli in (loc.clientesVip).t)
}

pred carroNacEhAlugadoAUmUnicoCliente[t: Time] { -- Um carro só é alugado a um só dono
	all car:Carro,cli:Cliente | (car in cli.alugadosNac.t) => 
	(all cli2:Cliente-cli| car !in cli2.alugadosNac.t)
}


pred carroImpEhAlugadoAUmUnicoCliente[t: Time] { -- Um carro só é alugado a um só dono
	all car:Carro,cli:Cliente | (car in cli.alugadosImp.t) => 
	(all cli2:Cliente-cli| car !in cli2.alugadosImp.t)
}

pred carroAlugado[car:Carro, cli:Cliente, loc: Locadora, t:Time]{
	(car in cli.alugadosNac.t or car in cli.alugadosImp.t) <=> car in (loc.carrosAlugados).t
  	!(car in cli.alugadosNac.t or car in cli.alugadosImp.t) <=> car in (loc.carrosDisponiveis).t
}

pred carrosDeClientesNaoMudam[c:Cliente,t,t': Time]{
	(c.alugadosNac.t = c.alugadosNac.t') and
	(c.alugadosImp.t = c.alugadosImp.t')
}

pred locadoraNaoMuda[l:Locadora,cli:Cliente,t,t':Time]{
	(l.clientes).t = (l.clientes).t' - cli
}

pred clientesVipNaoMudam[l:Locadora, cli:Cliente, t,t':Time]{
	(l.clientesVip).t = (l.clientesVip).t' - cli
}

/*--------------------------------------------Traces-----------------------------------------------------------*/

fact traces {
	init [first]	
 	all pre: Time-last | let pos = pre.next |
	one cli:Cliente, loc:Locadora | --some car:CarroNac, car2:CarroImp | 
	cadastrarCliente[cli,loc,pre,pos] --or alugarCarroNac[cli,car,loc,pre,pos] or 
	--alugarCarroImp[cli,car2,loc,pre,pos]
	--some cli : Cliente | one loc: Locadora | some carN:CarroNac | some carImp: CarroImp |
		--	alugarCarroNac[cli,carN,loc,pre,pos] or alugarCarroImp[cli,carImp,loc,pre,pos] or
		--	viraClienteVip[cli,loc,pre,pos] or cadastrarCliente[cli, loc,pre,pos]
}

/*--------------------------------------------Operações--------------------------------------------------------*/

-- OPERAÇÃO CADASTRAR CLIENTE
pred cadastrarCliente[cli: Cliente, loc: Locadora, t, t': Time] {
	cli !in (loc.clientes).t =>
	(loc.clientes).t' = (loc.clientes).t + cli
--	locadoraNaoMuda[loc,cli,t,t']
}

-- OPERAÇÃO TORNAR UM CLIENTE VIP
pred viraClienteVip[cli: Cliente, loc: Locadora,t, t':Time]{
	#((cli.alugadosNac)).t >= 2 and cli !in (loc.sujos).t and
	cli in (loc.clientes).t  and cli !in (loc.clientesVip).t =>
	((loc.clientes).t' = (loc.clientes).t - cli and
	(loc.clientesVip).t' = (loc.clientesVip).t + cli)
	--clientesVipNaoMudam[loc,cli,t,t']
}

-- OPERAÇÃO ALUGAR CARRO NACIONAL
pred alugarCarroNac[cli: Cliente, car: CarroNac, l:Locadora, t,t': Time]{
	((cli in (l.clientes).t) and (car in (l.carrosDisponiveis).t)) =>
	(l.carrosDisponiveis).t' = (l.carrosDisponiveis).t - car
	(l.carrosAlugados).t' = (l.carrosAlugados).t + car
	(cli.alugadosNac).t' = (cli.alugadosNac).t + car
	--viraClienteVip[cli,l,t,t']
	all cli2:Cliente - cli | carrosDeClientesNaoMudam[cli2,t,t']
}


-- OPERAÇÃO ALUGAR CARRO IMPORTADO
pred alugarCarroImp[cli: Cliente, car: CarroImp, l:Locadora, t,t': Time]{
	((cli in (l.clientes).t) and car in ((l.carrosDisponiveis).t) and (cli in (l.clientesVip).t) and
	car !in (cli.alugadosImp).t and #(cli.alugadosNac).t + #(cli.alugadosNac).t <= 3) => 
	(l.carrosDisponiveis).t' = (l.carrosDisponiveis).t - car 
	(l.carrosAlugados).t' = (l.carrosAlugados).t + car
	(cli.alugadosImp).t' = (cli.alugadosImp).t + car 
	--viraClienteVip[cli,l,t,t']
	all cli2:Cliente - cli | carrosDeClientesNaoMudam[cli2,t,t']
}


/*
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
