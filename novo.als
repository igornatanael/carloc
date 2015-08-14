module locadora
open util/ordering[Time]

/*--------------------------------------------Assinaturas------------------------------------------------------*/

sig Time{}

one sig Locadora {
	clientes: Cliente -> Time,
	clientesVip: Cliente -> Time,
 	carrosDisponiveis: Carro -> Time,
	carrosAlugados: Carro -> Time,
--	clientesSujos: Cliente -> Time
}

sig Cliente {
	nome: one Nome,
	telefone: one Telefone,
	alugadosNac: CarroNac -> Time,
	alugadosImp: CarroImp -> Time
}

abstract sig Carro, Nome, Telefone{}
sig CarroImp extends Carro{}
sig CarroNac extends Carro{}

/*--------------------------------------------Fatos------------------------------------------------------------*/

fact Locadora{
	all c: Carro, cli: Cliente, t: Time |  !((c in cli.alugadosNac.t) and (c in Locadora.carrosDisponiveis.t))
	all c: Carro, cli: Cliente, t: Time |  !((c in cli.alugadosImp.t) and (c in Locadora.carrosDisponiveis.t))
	all c: Carro, t: Time | some cli: Cliente | c in Locadora.carrosAlugados.t <=> (c in cli.alugadosNac.t or c in cli.alugadosImp.t)
	all t: Time | all c: CarroImp | c in Locadora.carrosAlugados.t <=> one cli: Cliente | c in cli.alugadosImp.t and cli in Locadora.clientesVip.(t.prev)
}

fact Carros{
	all car: Carro, loc: Locadora, t: Time | carroNaLocadora[car,loc,t]
	all loc: Locadora, t: Time | some cli: Cliente, car: Carro | carroAlugado[car,cli,loc,t]
	all car:CarroImp,cli:Cliente, t:Time | car in (cli.alugadosImp).t => cli in (Locadora.clientesVip).t
}

fact  Clientes {
	all n: Nome | one n.~nome -- Todo nome está associado a um único cliente
	all tel: Telefone | one tel.~telefone --Todo endereço está associado a algum cliente
	all cli:Cliente, t:Time | #(cli.alugadosNac + cli.alugadosImp).t < 2 => cli !in (Locadora.clientesVip).t
	all cli:Cliente, loc:Locadora, t:Time | clienteEhVip[cli,loc,t]
	all cli:Cliente,t:Time | #(cli.alugadosNac).t + #(cli.alugadosImp).t <= 3
	all t: Time | carroEhAlugadoAUmUnicoCliente[t] 
	all t: Time | carroImpEhAlugadoAUmUnicoCliente[t] 
	all t:Time, cli:Cliente, loc:Locadora | cli !in (loc.clientes).t => #cli.alugadosNac.t = 0
	all t:Time, cli:Cliente, loc:Locadora | cli !in (loc.clientes).t => #cli.alugadosImp.t = 0
	all c: Cliente, t: Time | #((c.alugadosNac) +(c.alugadosImp)).t <= 3
	all c: Cliente, t: Time | #(c.alugadosNac).t >= 2 => c in (Locadora.clientesVip).(t.next)
}

/*--------------------------------------------Funções----------------------------------------------------------*/

/*--------------------------------------------Predicados-------------------------------------------------------*/

pred init[t: Time] { --Inicializador
	no (Locadora.clientesVip).t -- Não possui clientes Vips no início
	no (Locadora.carrosAlugados).t 	-- No tempo inicial a locadora não tem nenhum carro alugado
 	no (Cliente.alugadosNac).t 	-- No tempo inicial nenhum cliente tem carro alugado
	no (Cliente.alugadosImp).t 	-- No tempo inicial nenhum cliente tem carro alugado
	no (Locadora.clientes).t -- Não possui clientes cadastrados no início
--	no (Locadora.clientesSujos).t
	all c: Carro | c in (Locadora.carrosDisponiveis).t -- todos os carros estão disponíveis no início
}

pred carroNaLocadora[c:Carro, l: Locadora, t:Time]{
	c in (l.carrosDisponiveis).t and c !in (l.carrosAlugados).t or
	c !in (l.carrosDisponiveis).t and c in (l.carrosAlugados).t 
}

pred clientePermanece[cli:Cliente,t,t':Time]{
	cli in Locadora.clientes.t => cli in Locadora.clientes.t'
}

pred clienteEhVip[c:Cliente, l:Locadora, t:Time]{
	c in (l.clientesVip).t => c in (l.clientes).t
}

pred carroEhAlugadoAUmUnicoCliente[t: Time] {
	all car:Carro,cli:Cliente | (car in cli.alugadosNac.t) => 
	(all cli2:Cliente-cli| car !in cli2.alugadosNac.t)
}


pred carroImpEhAlugadoAUmUnicoCliente[t: Time] {
	all car:Carro,cli:Cliente | (car in cli.alugadosImp.t)=> 
	(all cli2:Cliente-cli| car !in cli2.alugadosImp.t)
}

pred carroAlugado[car:Carro, cli:Cliente, loc: Locadora, t:Time]{
	((car in cli.alugadosNac.t or car in cli.alugadosImp.t) => car in loc.carrosAlugados.t) and 
   (!(car in cli.alugadosNac.t or car in cli.alugadosImp.t) => car in loc.carrosDisponiveis.t)
}

pred carrosDeClientesNaoMudam[c:Cliente,t,t': Time]{
	c.alugadosNac.t = c.alugadosNac.t' and
	c.alugadosImp.t = c.alugadosImp.t'
}

pred locadoraNaoMuda[l:Locadora,cli:Cliente,t,t':Time]{
	l.clientes.t = l.clientes.t' - cli
	l.clientesVip.t = l.clientesVip.t'
}


/*--------------------------------------------Traces-----------------------------------------------------------*/

fact traces {
	init [first]	
 	all pre: Time-last | let pos = pre.next |
	one cli:Cliente, loc:Locadora | some car:CarroNac, carImp: CarroImp | all cli2:Cliente | clientePermanece[cli2,pre,pos] 
	and (cadastrarCliente[cli,loc,pre,pos] or alugarCarroNac[cli,car,loc,pre,pos] or alugarCarroImp[cli,carImp,loc,pre,pos] )
}

/*--------------------------------------------Operações--------------------------------------------------------*/

-- OPERAÇÃO CADASTRAR CLIENTE
pred cadastrarCliente[cli: Cliente, loc: Locadora, t, t': Time] {
	cli !in (loc.clientes).t
	(loc.clientes).t' = (loc.clientes).t + cli
	locadoraNaoMuda[loc,cli,t,t']
}

-- OPERAÇÃO TORNAR UM CLIENTE VIP
pred viraClienteVip[cli: Cliente, loc: Locadora,t, t':Time]{
	cli not in loc.clientesVip.t and 
	cli in loc.clientes.t and
	#(cli.alugadosNac).t >= 2
	loc.clientesVip.t' = loc.clientesVip.t + cli
}

-- OPERAÇÃO ALUGAR CARRO NACIONAL
pred alugarCarroNac[cli: Cliente, car: CarroNac, l: Locadora, t, t': Time]{
	cli in (l.clientes).t and car in (l.carrosDisponiveis).t
	(#(cli.alugadosNac).t + #(cli.alugadosImp).t) < 3
	(l.carrosDisponiveis).t' = (l.carrosDisponiveis).t - car
	(cli.alugadosNac).t' = (cli.alugadosNac).t + car
	(l.carrosAlugados).t' = (l.carrosAlugados).t + car
	viraClienteVip[cli,l,t,t']
	all cli2: Cliente - cli | carrosDeClientesNaoMudam[cli2, t, t']
}

-- OPERAÇÃO ALUGAR CARRO IMPORTADO
pred alugarCarroImp[cli: Cliente, car: CarroImp, l: Locadora, t, t': Time]{
	cli in (l.clientes).t and car in (l.carrosDisponiveis).t and cli in (l.clientesVip).t
	(#(cli.alugadosNac).t + #(cli.alugadosImp).t) < 3
	(l.carrosDisponiveis).t' = (l.carrosDisponiveis).t - car
	(cli.alugadosImp).t' = (cli.alugadosImp).t + car
	(l.carrosAlugados).t' = (l.carrosAlugados).t + car
	all cli2: Cliente - cli | carrosDeClientesNaoMudam[cli2, t, t']
}
/*
-- OPERAÇÃO DEVOLVER CARRO IMPORTADO
pred devolverCarroAtrasado[cli:Cliente, l:Locadora, t,t': Time]{
	one car:Carro | car in (cli.alugadosNac).t =>
	(cli.alugadosNac.t' = cli.alugadosNac.t - car and
	l.carrosDisponiveis.t' = l.carrosDisponiveis.t +car and
	l.carrosAlugados.t' = ((l.carrosAlugados).t - car) and
	l.clientesVip.t' = l.clientesVip.t - cli and
	l.clientesSujos.t' = l.clientesSujos.t + cli)
}


/*--------------------------------------------Asserts----------------------------------------------------------*/

assert todaLocadoraTemMaisDeUmCarro {
 all l: Locadora ,t:Time| #(l.carrosDisponiveis.t + l.carrosAlugados.t) > 1
}

assert todoCarroEstaNaLocadora{
  all car:Carro,t:Time | ((car in Locadora.carrosDisponiveis.t) or (car in Locadora.carrosAlugados.t))
} 

assert todoCarroEalugadoApenasAumCliente {
 all car:Carro,cli:Cliente, t: Time| ((car in cli.alugadosNac.t) or (car in cli.alugadosImp.t) => (all c:Cliente-cli| (car !in c.alugadosNac.t) and (car !in c.alugadosImp.t) ))
}

assert todoClienteTemUmNome {
 	all cli: Cliente | one cli.nome 
}
  
assert todoClienteTemUmTelefone {
 	all cli: Cliente | one cli.telefone 
}

check todaLocadoraTemMaisDeUmCarro
check todoClienteTemUmTelefone
check todoClienteTemUmNome 
check todoCarroEalugadoApenasAumCliente 
check todoCarroEstaNaLocadora

pred show[]{
}

run show for 8
