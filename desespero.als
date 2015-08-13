module locadora
open util/ordering[Time]

/*--------------------------------------------Assinaturas------------------------------------------------------*/

sig Time{}

one sig Locadora { -- Locadora onde todos os carros estão "guardados"
	clientes: Cliente -> Time,
	clientesVip: Cliente -> Time,
	
 	carrosDisponiveis: Carro -> Time,
	carrosAlugados: Carro -> Time,
	clientesSujos: Cliente -> Time
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

/*--------------------------------------------Predicados----------------------------------------------------------*/

pred carrosDeClientesNaoMudam[cli:Cliente, car:Carro, loc:Locadora, t, t': Time]{
	cli.alugadosNac.t' = cli.alugadosNac.t
	cli.alugadosImp.t' = cli.alugadosImp.t
}

/*--------------------------------------------Fatos------------------------------------------------------------*/

fact Locadora{
	#CarroImp = 2
	#CarroNac = 3
	#Cliente = 3
	// carros alugados e disponíveis são conjuntos disjuntos
	all t: Time, l: Locadora | no l.carrosAlugados.t & l.carrosDisponiveis.t
	// clientes sujos não podem ser vips e vice-versa
	all t: Time, l: Locadora | no l.clientesVip.t & l.clientesSujos.t
	// todos os carros têm relação com a locadora
--	all t: Time, l: Locadora, c: Carro | c in (l.carrosAlugados).t or c in (l.carrosDisponiveis).t
}

fact Clientes{
	// se cliente é vip ou sujo ele está na lista de clientes
	all c:Cliente,l:Locadora, t:Time | (c in ((l.clientesVip).t) => c in (l.clientes).t) and (c in (l.clientesSujos).t => c in (l.clientes).t)
	all c:Cliente, pre: Time-last | let pos = pre.next | some loc: Locadora | clientesNaoMudam[c,loc,pre,pos]
	all c: Cliente, t: Time | #((c.alugadosNac) +(c.alugadosImp)).t <= 3
	all c: Cliente, l:Locadora, t:Time | #(c.alugadosNac + c.alugadosImp).t > 0 => c in (l.clientes).t
	all c: Cliente, l:Locadora, t:Time, car:CarroImp | car in (c.alugadosNac + c.alugadosImp).t => c in (l.clientes).t
}

fact Carros{
    all car:Carro,l:Locadora,t:Time| car in (l.carrosAlugados).t or car in (l.carrosDisponiveis).t
	all car: Carro, cli: Cliente, l:Locadora, t:Time | car in (cli.alugadosNac + cli.alugadosImp).t => car in (l.carrosAlugados).t
	all car: Carro, l:Locadora, t:Time, cli:Cliente | car !in (cli.alugadosNac + cli.alugadosImp).t => car in (l.carrosDisponiveis).t
	all car:Carro,l:Locadora,t:Time | some cli:Cliente| car in (l.carrosAlugados).t => car in cli.alugadosNac.t and cli in l.clientes.t
}

/*--------------------------------------------Operações------------------------------------------------------------*/

pred init[t: Time] { --Inicializador
	no (Locadora.clientesVip).t -- Não possui clientes Vips no início
	no (Locadora.carrosAlugados).t 	-- No tempo inicial a locadora não tem nenhum carro alugado
 	no (Cliente.alugadosNac).t 	-- No tempo inicial nenhum cliente tem carro alugado
	no (Cliente.alugadosImp).t 	-- No tempo inicial nenhum cliente tem carro alugado
	no (Locadora.clientes).t -- Não possui clientes cadastrados no início
	no (Locadora.clientesSujos).t -- Locadora começa com a lista negra vazia
	all c: Carro | c in (Locadora.carrosDisponiveis).t -- todos os carros estão disponíveis no início
}

fact traces {
	init [first]	
 	all pre: Time-last | let pos = pre.next | some cli:Cliente | one loc: Locadora | all car : CarroNac | 
	cadastraCliente[cli,loc,pre,pos] or  alugaNac[cli, car, loc, pre, pos]
}

// Método para cadastrar os clientes
pred cadastraCliente[c:Cliente, l:Locadora, t,t':Time]{
	(c !in (l.clientes).t) =>
	(l.clientes).t' = (l.clientes).t + c
}

// Aluga um carro nacional 
pred alugaNac[c:Cliente, ca:Carro, l:Locadora, t,t':Time]{
	(c in (l.clientes).t) and (ca in (l.carrosDisponiveis).t) => 
	( (l.carrosAlugados.t' = l.carrosAlugados.t + ca) and
	(l.carrosDisponiveis.t' = l.carrosDisponiveis.t - ca) and
	(c.alugadosNac.t' = c.alugadosNac.t +ca))
	carrosDeClientesNaoMudam[Cliente - c, ca, l, t,t']
	carrosAlugadosNaoMudam[Carro - ca,l, t, t']
	carrosDisponiveisNaoMudam[Carro - ca, Cliente - c, l, t, t']
}

// Um cliente nunca deixa de ser cliente
pred clientesNaoMudam[c:Cliente,l:Locadora, t,t':Time]{
	(c in (l.clientes).t) => (c in (l.clientes).t')
}

pred carrosAlugadosNaoMudam[car:Carro,l:Locadora,t,t':Time]{
    car in (l.carrosAlugados).t => car in (l.carrosAlugados).t'
}

pred carrosDisponiveisNaoMudam[car:Carro,cli:Cliente,l:Locadora,t,t':Time]{
    car in (l.carrosDisponiveis).t => car in (l.carrosDisponiveis).t'
}

pred show[]{
}

run show for 15
