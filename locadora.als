module locadora
open util/ordering[Time]

sig Time{}

sig Locadora {
	carros: some Carro ->,
	clientes: some Cliente -> 
}


sig Cliente {
	alugados: some Carro
}

fact {
	all c:Carro | one c.~carros
}

sig ClienteVIP in Cliente {}

abstract sig Carro{}

sig CarroImp extends Carro{}
sig CarroNac extends Carro{}

pred show[]{
}
run show for 4




