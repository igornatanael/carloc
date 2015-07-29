module locadora
open util/ordering[Time] as to
sig Time{}

sig Locadora {
	carros: set Carro
}

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


fact { //FATOS SOBRE CARROS
	all c:Carro | one c.~carros

	// CarroImp só pode ser alugado por ClienteVIP
	
	
}

fact  { //FATOS  SOBRE CLIENTES
	//Cliente alocações <= 3
	all c: Cliente | #c.alugados<= 3
	
	//Cliente é VIP se alocações >= 2
	all c: ClienteVIP | #c.alugados >= 2
	

}


pred show[]{
}

run show for 4
