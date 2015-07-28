module locadora

sig Locadora {
	carros: set Carro
}


sig Cliente {}

sig ClienteVIP extends Cliente {}

abstract sig Carro{}

sig CarroImp extends Carro{}
sig CarroNac extends Carro{}

pred show[]{
}
run show for 3
