module locadora
open util/ordering[Time] as to
sig Time{}

abstract sig Carro{}

sig CarroImp extends Carro{}
sig CarroNac extends Carro{}

sig Cliente {
	alugados: some Carro
}

sig ClienteVIP in Cliente {}

one sig Locadora {
	carros: some Carro,
	clientes: some Cliente
}

fact {
	all c:Carro | one c.~carros
}

pred show[]{
}

run show for 4
