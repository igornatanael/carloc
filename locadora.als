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

fact Locadora{
	one Locadora
}

fact Carros{
	all car: Carro, t: Time, l: Locadora| carroTemUmCliente[car,l, t]
 	all car: Carro, t: Time, l: Locadora | carroAlugadoOuNao[car,l,t]
	all car: Carro, t:Time, l: Locadora | carroDesejado[car,l,t]
	all car: Carro, t:Time, l: Locadora | carroDisponivel[car,l,t]
}

fact  Clientes {
	--some c:Cliente, t:Time,l: Locadora | some t':Time | ehClienteVip[c,l,t,t']
	all c:Cliente, t: Time, l:Locadora | clienteTemImp[c,l,t]
--	all c:Cliente, loc:Locadora, t: Time | clienteSoAlugaCadastrado[c,loc,t]
	!one c:Cliente, loc:Locadora, t:Time | clienteSoAlugaCadastrado[c,loc,t]
	all c:Cliente, loc:Locadora, t:Time | c in (loc.clientesVip).t => c in (loc.clientes).t
}

/*--------------------------------------------Funções--------------------------------------------------------*/



/*--------------------------------------------Predicados-----------------------------------------------------*/

pred init[t: Time] { --Inicializador
	no (Locadora.clientesVip).t -- Não possui clientes Vips no início
	no (Locadora.carrosDesejados).t -- Não há carros desejados, pois não há carros alugados
	no (Locadora.carrosAlugados).t 	-- No tempo inicial a locadora não tem nenhum carro alugado
 	no (Cliente.alugadosNac).t 	-- No tempo inicial nenhum cliente tem carro alugado
	no (Cliente.alugadosImp).t 	-- No tempo inicial nenhum cliente tem carro alugado
	no (Locadora.clientes).t -- Não possui clientes cadastrados no início
	all c: Carro | c in (Locadora.carrosDisponiveis).t -- todos os carros estão disponíveis no início
}

pred carroDesejado[car:Carro,l:Locadora,t:Time]{
	car in (l.carrosDesejados).t => car in (l.carrosAlugados).t
}

pred clienteSoAlugaCadastrado[cli:Cliente, l:Locadora, t:Time]{
	(#(cli.alugadosNac).t + #(cli.alugadosImp).t) > 0 and cli !in (l.clientes).t
}

pred carroDisponivel[car:Carro,l:Locadora,t:Time]{
	car in (l.carrosDisponiveis).t => car !in (l.carrosAlugados).t and car !in (l.carrosDesejados).t
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

/*--------------------------------traces---------------------------------*/

fact traces {
	init [first]	
 	all pre: Time-last | let pos = pre.next |
		some cli : Cliente, loc: Locadora, carN:CarroNac, carImp: CarroImp |
			viraClienteVip[cli, loc, pre, pos] or
			alugarCarroNac[cli,carN,loc,pre,pos] or alugarCarroImp[cli,carImp,loc,pre,pos] or
			viraClienteVip[cli,loc,pre,pos] or cadastrarCliente[cli, loc,pre,pos]
}

/*--------------------------------------------Operações----------------------------------------------------*/

-- OPERAÇÃO CADASTRAR CLIENTE
pred cadastrarCliente[cli: Cliente, loc: Locadora, t, t': Time] {
	cli !in (loc.clientes).t
	(loc.clientes).t' = (loc.clientes).t + cli
}

pred alugarCarroImp[cli: Cliente, car: CarroImp, l:Locadora, t,t': Time]{
	cli in (l.clientes).t and	car in (l.carrosDisponiveis).t and cli in (l.clientesVip).t
	car !in (cli.alugadosImp).t and #(cli.alugadosNac).t + #(cli.alugadosNac).t <= 3
	(cli.alugadosImp).t' = (cli.alugadosImp).t + car
	(l.carrosDisponiveis).t' = (l.carrosDisponiveis).t - car
	(l.carrosAlugados).t' = (l.carrosAlugados).t + car
}

pred alugarCarroNac[cli: Cliente, car: CarroNac, l:Locadora, t,t': Time]{
	cli in (l.clientes).t and	car in (l.carrosDisponiveis).t and cli in (l.clientes).t
	car !in (cli.alugadosNac).t and #(cli.alugadosNac).t + #(cli.alugadosNac).t <= 3
	(cli.alugadosNac).t' = (cli.alugadosNac).t + car
	(l.carrosDisponiveis).t' = (l.carrosDisponiveis).t - car
	(l.carrosAlugados).t' = (l.carrosAlugados).t + car
}

pred viraClienteVip[c:Cliente,l:Locadora,t, t':Time]{
	#(c.alugadosNac).t >= 2
	c in (l.clientes).t and c !in (l.clientesVip).t
	(l.clientesVip).t' = (l.clientesVip).t + c
}


/*--------------------------------------------Asserts-----------------------------------------------------*/


pred show[]{
}

run show for 15  but exactly 5 Carro, exactly 5 Cliente
