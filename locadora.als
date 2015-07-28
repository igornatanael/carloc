module locadora

sig Locadora {
	carros: set Carro
}


sig Cliente {}

sig ClienteVIP in Cliente {}

abstract sig Carro{}

sig CarroImp extends Carro{}
sig CarroNac extends Carro{}



pred show[]{
}
run show for 4
