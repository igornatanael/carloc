module rentalstore
open util/ordering[Time]

/* =============
       ASSINATURAS
    ============= */

sig Time {}

one sig Loja {
	clientes : Cliente -> Time,
	clientesVip : Cliente -> Time,
	carrosDisponiveis : Carro -> Time,
	carrosAlugados : Carro -> Time
}

sig Cliente {
	alugadosNac : CarroNac -> Time,
	alugadosImp : CarroImp -> Time,
	desejados : Carro -> Time,
	nome : Nome,
	fone : Fone
}

abstract sig Info {}
sig Nome, Fone extends Info {}

abstract sig Carro {
	clienteAtual : Cliente -> Time
}
sig CarroNac, CarroImp extends Carro {}

/* =============
       FATOS
    ============= */

fact Loja {
	// a loja tem carros
	all c : Carro, l : Loja, t : Time | c in (l.carrosDisponiveis).t or c in (l.carrosAlugados).t
}

fact Cliente {
	// número máximo de carros alugados ao mesmo tempo = 3
	all c : Cliente, t : Time | #((c.alugadosNac).t) + #((c.alugadosImp).t) <= 3
	// um cliente ou é normal (aqui descrito como cliente apenas) ou é vip
	all c : Cliente, t : Time, l : Loja | c in (l.clientes).t <=> c not in (l.clientesVip).t
}

fact Carro {
	// para todo carro, a todo tempo, um carro só está disponível se, e somente se, não estiver alugado
	all c : Carro, t : Time, l : Loja | c in (l.carrosDisponiveis).t <=> c not in (l.carrosAlugados).t
}

/* =============
       PREDICADOS
    ============= */

pred init[t: Time] { --Inicializador
	no (Loja.clientesVip).t -- Não possui clientes Vips no início
	no (Loja.carrosAlugados).t 	-- No tempo inicial a locadora não tem nenhum carro alugado
 	no (Cliente.alugadosNac).t 	-- No tempo inicial nenhum cliente tem carro alugado
	no (Cliente.alugadosImp).t 	-- No tempo inicial nenhum cliente tem carro alugado
	no (Loja.clientes).t -- Não possui clientes cadastrados no início
	all c: Carro | no (c.clienteAtual).t and c in (Loja.carrosDisponiveis).t
}

/* =============
       TRACES
    ============= */

pred traces {
	init[first]
	all pre : Time | let pos = pre.next |
	all cli : Cliente | one l : Loja | all nac : CarroNac | all imp : CarroImp |
	alugarUmCarroNac[cli, nac, l, pre, pos] or
	alugarUmCarroImp[cli, imp, l, pre, pos] or
	devolverUmCarroNac[cli, nac, l, pre, pos] or
	devolverUmCarroImp[cli, imp, l, pre, pos]
}


/* =============
       OPERAÇÕES
    ============= */

/* checa se o cidadão pode ser vip
	para isso, ele não pode ser vip
	e precisa ter dois carros alugados ao mesmo tempo
	(nota: essa checagem é realizada a cada operação de aluguel
	de carro nacional, logo não é necessário checar se é maior que 2)
*/
pred checaElegibilidadeVip [c: Cliente, l : Loja, t : Time] {
	c not in (l.clientesVip).t
	#(c.alugadosNac).t = 2
}

/* checa se um carro está disponível na loja */
pred checaDisponibilidade [car : Carro, l : Loja, t : Time] {
	car in (l.carrosDisponiveis).t and car not in (l.carrosAlugados).t
}

/* checa se um usuário está cadastrado */
pred checaCadastro [cli : Cliente, l : Loja, t : Time] {
	cli in (l.clientes).t || cli in (l.clientesVip).t
}

/* checa se um usuário é vip */
pred ehVip[cli : Cliente, l : Loja, t : Time] {
	cli in (l.clientesVip).t and cli not in (l.clientes).t
}

/* torna um cliente vip */
pred tornarVip [c : Cliente, l : Loja, t, t' = Time] {
	not ehVip[c, l,  t]
	(l.clientes).t' = (l.clientes).t - c
	(l.clientesVip).t' = (l.clientesVip).t + c
}

/* aluga um carro nacional */
pred alugarUmCarroNac [cli : Cliente, car : CarroNac, l : Loja, t, t' : Time] {
	// carro tem que estar disponível
	checaDisponibilidade[car, l, t]
	// o cliente precisa estar cadastrado: estar ou em clientes, ou em clientesVip
	checaCadastro[cli, l, t]
	// aluga o carro
	(cli.alugadosNac).t' = (cli.alugadosNac).t + car
	(car.clienteAtual).t' = cli
	// se o cara for elegível à viptude, ele vira vip
	checaElegibilidadeVip[cli, l, t'] and tornarVip[cli, l, t, t']
	// registra o aluguel na loja
	(l.carrosDisponiveis).t' = (l.carrosDisponiveis).t - car
	(l.carrosAlugados).t' = (l.carrosAlugados).t + car
	// se for desejado, ele desdeseja
	car in (cli.desejados).t => realizarSonho[cli, car, l, t, t']
	devolverUmCarroNac[cli, car, l, t, t']
}

/* aluga um carro importado */
pred alugarUmCarroImp [cli : Cliente, car : CarroImp, l : Loja, t, t' : Time] {
	// o carro precisa estar disponível
	// o cliente precisa ser vip
	checaDisponibilidade[car, l, t]
		and ehVip[cli, l, t]
	// aluga o carro:
	(cli.alugadosImp).t' = (cli.alugadosImp).t + car
	(car.clienteAtual).t' = cli
	// registra na loja
	(l.carrosDisponiveis).t' = (l.carrosDisponiveis).t - car
	(l.carrosAlugados).t' = (l.carrosAlugados).t + car
	// se for desejado, desdeseja
	car in (cli.desejados).t => realizarSonho[cli, car, l, t, t']
}

pred devolverUmCarroNac [cli : Cliente, car : CarroNac, l : Loja, t, t' : Time] {
	car in (l.carrosAlugados).t 
		and car in (cli.alugadosNac).t
		and checaCadastro[cli, l, t]
	// desaluga
	(cli.alugadosNac).t' = (cli.alugadosNac).t - car
	no (car.clienteAtual).t'
	// registra na loja
	(l.carrosDisponiveis).t' = (l.carrosDisponiveis).t + car
	(l.carrosAlugados).t' = (l.carrosAlugados).t - car
}

pred devolverUmCarroImp [cli : Cliente, car : CarroImp, l : Loja, t, t' : Time] {
	car in (l.carrosAlugados).t 
		and car in (cli.alugadosImp).t
		and checaCadastro[cli, l, t]
	// desaluga
	(cli.alugadosImp).t' = (cli.alugadosImp).t - car
	no car.clienteAtual
	// registra na loja
	(l.carrosDisponiveis).t' = (l.carrosDisponiveis).t + car
	(l.carrosAlugados).t' = (l.carrosAlugados).t - car
}

pred realizarSonho[cli: Cliente, car : Carro, l : Loja, t, t' : Time] {
	(cli.desejados).t' = (cli.desejados).t - car
}

pred show[] {}

run show for 10
	
	
	
	
