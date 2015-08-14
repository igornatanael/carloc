-- Tema 9: Locadora de Carros
-- Alunos: Arthur Lustosa, Clenimar Filemon, Igor Natanael, Nicolas Gabriel, Roberto Soares

module locadora
open util/ordering[Time]

/*--------------------------------------------Assinaturas------------------------------------------------------*/

sig Time {}

one sig Locadora {
	clientes: Cliente -> Time,
	clientesVip: Cliente -> Time,
 	carrosDisponiveis: Carro -> Time,
	carrosAlugados: Carro -> Time,
	carrosDesejados: Carro ->Time
}

sig Cliente {
	nome: one Nome,
	telefone: one Telefone,
	alugadosNac: CarroNac -> Time,
	alugadosImp: CarroImp -> Time,
	desejados: Carro -> Time
}

abstract sig Carro, Nome, Telefone {}
sig CarroImp extends Carro {}
sig CarroNac extends Carro {}

/*--------------------------------------------Fatos------------------------------------------------------------*/

fact Locadora{
	#Cliente = 5
	#Carro = 7
	#Locadora = 1
	all c: Carro, cli: Cliente, t: Time |  !((c in cli.alugadosNac.t) and (c in Locadora.carrosDisponiveis.t)) -- Carro nacional não pode estar alugado e disponível ao mesmo tempo.
	all c: Carro, cli: Cliente, t: Time |  !((c in cli.alugadosImp.t) and (c in Locadora.carrosDisponiveis.t)) -- Carro importado não pode estar alugado e disponível ao mesmo tempo.
	all c: Carro, t: Time | some cli: Cliente | c in Locadora.carrosAlugados.t <=> (c in cli.alugadosNac.t or c in cli.alugadosImp.t) -- Carro nacional está como alugado na locadora se, e somente se, ele estiver na lista de alugados nacionais ou importados de um cliente.
	all t: Time | all c: CarroImp | c in Locadora.carrosAlugados.t <=> one cli: Cliente | c in cli.alugadosImp.t and cli in Locadora.clientesVip.(t.prev) -- Carro nacional está como alugado na locadora se, e somente se, ele estiver na lista de alugados nacionais ou importados de um cliente.
}

fact Carros{
	all car: Carro, loc: Locadora, t: Time | carroNaLocadora[car,loc,t]
	all loc: Locadora, t: Time | some cli: Cliente, car: Carro | carroAlugado[car,cli,loc,t]
	all car:CarroImp,cli:Cliente, t:Time | car in (cli.alugadosImp).t => cli in (Locadora.clientesVip).t
	all car:Carro, t:Time | car in todosOsCarros[t]
	all cli:Cliente,car:Carro, t:Time | car in (cli.desejados).t => car in carrosAlug[t]
	all cli:Cliente,car:Carro,t:Time | car in (cli.desejados).t => car !in (cli.alugadosNac).t
	all t:Time | carroEhDesejadoPorUmUnicoCliente[t]
	all  loc: Locadora, t: Time |no (loc.carrosDisponiveis).t & (loc.carrosDesejados).t --Carros desejados nao podem ser disponiveis	
    all c: Carro, t: Time | c in (Locadora.carrosDesejados).t <=> one cli : Cliente | c in (cli.desejados).t and  cli in (Locadora.clientes).t
}

fact  Clientes {
	all n: Nome | one n.~nome -- Todo nome está associado a um único cliente
	all tel: Telefone | one tel.~telefone --Todo endereço está associado a algum cliente
	all cli:Cliente, t:Time | #carrosDoCliente[cli,t] < 2 => cli !in (Locadora.clientesVip).t -- Cliente que tem menos de 2 carros alugados não pode ser vip.
	all cli:Cliente, loc:Locadora, t:Time | clienteEhVip[cli,loc,t]  -- Cliente que é vip não perde vínculo com lista de clientes normais da locadora.
	all cli:Cliente,t:Time | #carrosDoCliente[cli,t] <= 3  -- Cliente não pode ter mais de 3 carros alugados.
	all t: Time | carroEhAlugadoAUmUnicoCliente[t]  -- Carro nacional só pode ser alugado à um único cliente.
	all t: Time | carroImpEhAlugadoAUmUnicoCliente[t] -- Carro importado só pode ser alugado à um único cliente.
	all t:Time, cli:Cliente, loc:Locadora | cli !in clientesLocadora[loc,t] => #cli.alugadosNac.t = 0 -- Cliente que não está cadastrado não pode ter carros nacionais.
	all t:Time, cli:Cliente, loc:Locadora | cli !in clientesLocadora[loc,t] => #cli.alugadosImp.t = 0  -- Cliente que não está cadastrado não pode ter carros importados.
	all t:Time, cli:Cliente, loc:Locadora | cli !in clientesLocadora[loc,t] => #cli.desejados.t = 0  -- Cliente que não está cadastrado não pode ter carros desejados.
	all c: Cliente, t: Time | #(c.alugadosNac).t >= 2 => c in (Locadora.clientesVip).(t.next) -- Cliente que tem mais de 2 carros nacionais alugados é vip.
}

/*--------------------------------------------Funções----------------------------------------------------------*/


fun carrosDoCliente[cli: Cliente, t: Time]: set Carro{
	cli.(alugadosNac + alugadosImp).t
}

fun carrosDisp[t: Time]: set Carro {
	Locadora.carrosDisponiveis.t
}

fun carrosAlug[t: Time]: set Carro {
	Locadora.carrosAlugados.t
}

fun clientesLocadora[loc: Locadora, t: Time]: set Cliente{
	loc.clientes.t
}

fun todosOsCarros[t:Time]: set Carro{
	Locadora.(carrosAlugados + carrosDisponiveis).t
}

/*--------------------------------------------Predicados-------------------------------------------------------*/

pred init[t: Time] { --Inicializador
	no (Locadora.carrosDesejados).t
	no (Locadora.clientesVip).t -- Não possui clientes Vips no início
	no carrosAlug[t] 	-- No tempo inicial a locadora não tem nenhum carro alugado
 	no (Cliente.alugadosNac).t 	-- No tempo inicial nenhum cliente tem carro alugado
	no (Cliente.alugadosImp).t 	-- No tempo inicial nenhum cliente tem carro alugado
	no (Locadora.clientes).t -- Não possui clientes cadastrados no início
	no (Cliente.desejados).t
--	no (Locadora.clientesSujos).t
	all c: Carro | c in carrosDisp[t] -- todos os carros estão disponíveis no início
}

pred carroNaLocadora[c:Carro, l: Locadora, t:Time]{-- Carro não pode está alugado e disponível ao mesmo tempo.
	c in (l.carrosDisponiveis).t and c !in (l.carrosAlugados).t or
	c !in (l.carrosDisponiveis).t and c in (l.carrosAlugados).t 
}

pred clientePermanece[cli:Cliente,t,t':Time]{-- Cliente passado como parâmetro não muda.
	cli in Locadora.clientes.t => cli in Locadora.clientes.t'
}

pred clienteEhVip[c:Cliente, l:Locadora, t:Time]{ -- Cliente que é vip também é cliente normal.
	c in (l.clientesVip).t => c in (l.clientes).t
}

pred carroEhAlugadoAUmUnicoCliente[t: Time] { -- Carro nacional só pode ser alugado à um único cliente.
	all car:Carro,cli:Cliente | (car in cli.alugadosNac.t) => 
	(all cli2:Cliente-cli| car !in cli2.alugadosNac.t)
}


pred carroImpEhAlugadoAUmUnicoCliente[t: Time] { -- Carro importado só pode ser alugado à um único cliente.
	all car:Carro,cli:Cliente | (car in cli.alugadosImp.t)=> 
	(all cli2:Cliente-cli| car !in cli2.alugadosImp.t)
}

pred carroAlugado[car:Carro, cli:Cliente, loc: Locadora, t:Time]{ -- Se carro está alugado, ele não está disponível, e vice-versa.
	((car in cli.alugadosNac.t or car in cli.alugadosImp.t) => car in loc.carrosAlugados.t) and 
   (!(car in cli.alugadosNac.t or car in cli.alugadosImp.t) => car in loc.carrosDisponiveis.t)
}

pred carrosDeClientesNaoMudam[c:Cliente,t,t': Time]{ -- Carros de cliente passado como parâmetro não mudam.
	c.alugadosNac.t = c.alugadosNac.t' and
	c.alugadosImp.t = c.alugadosImp.t'
	c.desejados.t = c.desejados.t'
}

pred locadoraNaoMuda[l:Locadora,cli:Cliente,t,t':Time]{ -- Locadora passada como parâmetro não muda.
	l.clientes.t = l.clientes.t' - cli
	l.clientesVip.t = l.clientesVip.t'
}

pred carroEhDesejadoPorUmUnicoCliente[t: Time] { -- Carro só pode ser desejado por um único cliente.
	all car:Carro,cli:Cliente | (car in cli.desejados.t)=> 
	(all cli2:Cliente-cli| car !in cli2.desejados.t)
}


/*--------------------------------------------Traces-----------------------------------------------------------*/

fact traces {
	init [first]	
 	all pre: Time-last | let pos = pre.next |
	one cli: Cliente, loc: Locadora | some car: CarroNac, carImp: CarroImp | all cli2: Cliente | clientePermanece[cli2, pre, pos]-- and alugaReservado[loc,car,pre,pos]
	and (cadastrarCliente[cli, loc, pre, pos] or alugarCarroNac[cli, car, loc, pre, pos] or alugarCarroImp[cli, carImp, loc, pre, pos] or reservarCarro[loc,cli,car, pre,pos])
}

/*--------------------------------------------Operações--------------------------------------------------------*/

-- OPERAÇÃO CADASTRAR CLIENTE
pred cadastrarCliente[cli: Cliente, loc: Locadora, t, t': Time] {
	cli !in (loc.clientes).t -- Verifica se cliente já não está cadastrado.
	(loc.clientes).t' = (loc.clientes).t + cli -- Cadastra cliente na lista de clientes da locadora.
	locadoraNaoMuda[loc, cli, t, t']
}

-- OPERAÇÃO TORNAR UM CLIENTE VIP
pred viraClienteVip[cli: Cliente, loc: Locadora, t, t':Time]{
	cli not in loc.clientesVip.t and -- Verifica se cliente já não é vip e
	cli in loc.clientes.t and -- se está cadastrado.
	#(cli.alugadosNac).t >= 2 -- Para virar vip, cliente precisa ter pelo menos 2 carros nacionais alugados.
	loc.clientesVip.t' = loc.clientesVip.t + cli -- Cadastra cliente vip.
}

-- OPERAÇÃO ALUGAR CARRO NACIONAL
pred alugarCarroNac[cli: Cliente, car: CarroNac, l: Locadora, t, t': Time] {
	cli in (l.clientes).t and car in (l.carrosDisponiveis).t -- Verifica se cliente está cadastrado e se carro está disponível.
	(#(cli.alugadosNac).t + #(cli.alugadosImp).t) <= 3 -- Verifica se o número de carros alugados do cliente é menor que 3.
	(l.carrosDisponiveis).t' = (l.carrosDisponiveis).t - car -- Carro passa a não estar mais disponível.
	(cli.alugadosNac).t' = (cli.alugadosNac).t + car -- Cliente passa a ter o carro alugado.
	(l.carrosAlugados).t' = (l.carrosAlugados).t + car -- Locadora cadastra o carro como alugado.
	viraClienteVip[cli, l, t, t'] -- Checa se o cliente pode virar vip.
	all cli2: Cliente - cli | carrosDeClientesNaoMudam[cli2, t, t']
}

-- OPERAÇÃO ALUGAR CARRO IMPORTADO
pred alugarCarroImp[cli: Cliente, car: CarroImp, l: Locadora, t, t': Time] {
	cli in (l.clientes).t and car in (l.carrosDisponiveis).t and cli in (l.clientesVip).t -- Verifica se cliente está cadastrado, se carro está disponível e se cliente é vip.
	(#(cli.alugadosNac).t + #(cli.alugadosImp).t) <= 3 -- Verifica se o número de carros alugados do cliente é menor que 3.
	(l.carrosDisponiveis).t' = (l.carrosDisponiveis).t - car  -- Carro passa a não estar mais disponível.
	(cli.alugadosImp).t' = (cli.alugadosImp).t + car -- Cliente passa a ter o carro alugado.
	(l.carrosAlugados).t' = (l.carrosAlugados).t + car -- Locadora cadastra o carro como alugado.
	all cli2: Cliente - cli | carrosDeClientesNaoMudam[cli2, t, t']
}

pred reservarCarro[loc: Locadora , cli:Cliente,car:Carro, t,t':Time]{
	(cli in (loc.clientes).t and car !in cli.(alugadosNac).t and car !in cli.(alugadosImp).t and car in (loc.carrosAlugados).t and car !in (loc.carrosDesejados).t )=>
	(loc.carrosDesejados).t' = (loc.carrosDesejados).t + car
	cli.desejados.t' = cli.desejados.t + car
	all cli2: Cliente - cli | carrosDeClientesNaoMudam[cli2, t, t']
}

pred alugaReservado[loc: Locadora , car:CarroNac, t,t':Time]{
	some cli:Cliente | car in (loc.carrosDesejados).t and car in (cli.desejados).t and car in (loc.carrosDisponiveis).(t.next) =>
	((loc.carrosDesejados).t' = (loc.carrosDesejados).t - car and
	cli.desejados.t' = cli.desejados.t - car and
	alugarCarroNac[cli,car,loc,t,t'] and
	all cli2: Cliente - cli | carrosDeClientesNaoMudam[cli2, t, t'])
}

/*--------------------------------------------Asserts----------------------------------------------------------*/

assert todaLocadoraTemMaisDeUmCarro {
 all loc: Locadora, t :Time| #(loc.carrosDisponiveis.t + loc.carrosAlugados.t) > 1
}

assert todoCarroEstaNaLocadora {
  all car: Carro, t: Time | ((car in Locadora.carrosDisponiveis.t) or (car in Locadora.carrosAlugados.t))
} 

assert todoCarroEhAlugadoApenasAUmCliente {
 all car: Carro, cli :Cliente, t: Time| ((car in cli.alugadosNac.t) or (car in cli.alugadosImp.t) => (all c:Cliente-cli | (car !in c.alugadosNac.t) and (car !in c.alugadosImp.t)))
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
check todoCarroEhAlugadoApenasAUmCliente 
check todoCarroEstaNaLocadora

/*--------------------------------------------Show---------------------------------------------------------*/

pred show[]{
}

run show for 8
