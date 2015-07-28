module locadora

sig Locadora {
	carros: some Carro,
	clientes: some Cliente
}


sig Cliente {
	alugados: some Carro
}

sig ClienteVIP in Cliente {}

abstract sig Carro{}

sig CarroImp extends Carro{}
sig CarroNac extends Carro{}

pred show[]{
}
run show for 4




