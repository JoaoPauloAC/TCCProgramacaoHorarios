//Parâmetros                                     
range Disciplinas = 1..18;                                           //Disciplinas ofertadas na instiruição
{string} Professores = ...;                                          //Professores na instituição
range Turnos = 1..10;                                                //Dias da semana que haverá aula
int nHorarios = 5;               
range Horarios = 1..nHorarios;                                       //Horários de aula
{string} Turmas = ...;                                               //Turmas ofertadas
int ProfDisponibilidade[Professores][Turnos][Horarios] = ...;        //Horários que o professor está disponível para dar aula
int ProfDisciplinas[Professores][Turmas][Disciplinas] = ...;         //Disciplinas que o professor é apto a dar aulas em cada turma
int TurmaMoT[Turmas] = ...;                                          //Se a turma possui aula de manhã(0), tarde(1) ou misto(2)
int TurmaPeriodo[Turmas][Turnos][Horarios] = ...;                    //Horários que a turma pode ter aula
int TurmaCargaHoraria[Disciplinas][Turmas] = ...;                    //Carga horaria(em horas-aula) que cada turma deve ter de cada disciplina
int TurmaCargaHorariaDias[Disciplinas][Turmas];                      //Carga horaria(em dias por semana) que cada turma deve ter de cada disciplina

//Converter TurmaCargaHoraria em TurmaCargaHorariaDias
execute HorasParaDias {
  for(var d in Disciplinas)
  for(var t in Turmas)
    if(TurmaCargaHoraria[d][t] == 5)
      {TurmaCargaHorariaDias[d][t] = 3}
        else
          {
            if(TurmaCargaHoraria[d][t] <= 4 && TurmaCargaHoraria[d][t] >= 3)
             {TurmaCargaHorariaDias[d][t] = 2}
               else 
                 {TurmaCargaHorariaDias[d][t] = 1}
             }
};


//Variáveis de decisão
dvar boolean V[Turmas];                                                           //Se naquela turma, disciplinas 5 de 5h/semana serão dadas em 2(Z=1) ou 3(Z=0) dias
dvar boolean W[Disciplinas][Turmas][Turnos];                                      //Alocar disciplina [d] na turma [t] no turno [l], 1 = SIM, 0 = NÃO
dvar boolean X[Professores][Disciplinas][Turmas][Turnos][Horarios];               //Alocar o professor [p] com a disciplina [d] na turma [t] no turno [l] no horario [h], 1 = SIM, 0 = NÃO
dvar boolean Y[Professores][Turnos];                                              //Alocar Professor [p] no turno [l], 1 = SIM, 0 = NÃO


//Função Objetiva
//Diminuir o total de turnos que cada professor (a) deve se apresentar
minimize
  sum(p in Professores, l in Turnos)Y[p][l];


//Restrições
subject to{

//a) Se determinado (a) professor (a) vier ministrar alguma aula em uma turma em qualquer horário naquele turno, selecionar aquele turno
forall(p in Professores, d in Disciplinas, t in Turmas, l in Turnos, h in Horarios)
  X[p][d][t][l][h] <= Y[p][l];
 
//b) Se determinada disciplina for lecionada naquele turno, selecionar aquele turno em wdtl
forall(p in Professores, d in Disciplinas, t in Turmas, l in Turnos, h in Horarios)
  X[p][d][t][l][h] <= W[d][t][l];
 
//c) Cada professor (a) não pode estar, no mesmo horário, em duas turmas diferentes
forall(p in Professores, l in Turnos, h in Horarios)
  sum(t in Turmas, d in Disciplinas)
    X[p][d][t][l][h] <= 1;

//d) Cada turma só pode ter uma aula por horário
forall(t in Turmas, l in Turnos, h in Horarios)
  sum(p in Professores, d in Disciplinas)
    X[p][d][t][l][h] <= 1;

//e) Cada professor (a) só pode lecionar na instituição em seus horários disponíveis
forall(p in Professores,l in Turnos, h in Horarios, d in Disciplinas, t in Turmas)
    X[p][d][t][l][h] <= ProfDisponibilidade[p][l][h];

//f) Disciplinas só podem ser ministradas por professores responsáveis para lecionar determinada disciplina na respectiva turma
forall(p in Professores, d in Disciplinas, t in Turmas, l in Turnos, h in Horarios)
    X[p][d][t][l][h] <= ProfDisciplinas[p][t][d];

//g) As aulas de cada turma só podem ocorrer nos turnos em que a respectiva turma possui aulas
forall(p in Professores, d in Disciplinas, t in Turmas, l in Turnos, h in Horarios)
  X[p][d][t][l][h] <= TurmaPeriodo[t][l][h];

//h) Não pode haver mais de duas ou três aulas de uma mesma disciplina no mesmo dia em uma determinada turma, de acordo com sua carga horária semanal
forall(t in Turmas, l in Turnos, d in Disciplinas)
  if(TurmaCargaHoraria[d][t] <= 4)
   sum(p in Professores, h in Horarios)
     X[p][d][t][l][h] <= 2;
forall(d in Disciplinas, t in Turmas, l in Turnos)
	if(TurmaCargaHoraria[d][t]==5)
		sum(p in Professores, h in Horarios)X[p][d][t][l][h] <= 2 + V[t];

//i) Uma mesma disciplina não pode ser lecionada no segundo e no terceiro horários consecutivamente em uma turma
forall(d in Disciplinas, t in Turmas, l in Turnos, h2 in Horarios: h2==2, h3 in Horarios: h3==3)
  sum(p in Professores) X[p][d][t][l][h2] + sum(p in Professores) X[p][d][t][l][h3] <= 1;

//j) Aulas de uma mesma disciplina devem ser lecionadas em duplas ou trios de aulas consecutivas em cada dia, de acordo com sua carga horária semanal
forall(p in Professores, d in Disciplinas, t in Turmas, l in Turnos, h1 in Horarios: h1 == 1 || h1 == 2, h2 in Horarios: h2 == 3 || h2 == 4 || h2 == 5)
  X[p][d][t][l][h1] + X[p][d][t][l][h2] <= 1;
forall(p in Professores, d in Disciplinas, t in Turmas, l in Turnos, h3 in Horarios: h3 == 3, h4 in Horarios: h4 == 4, h5 in Horarios: h5 == 5)
  X[p][d][t][l][h3] + X[p][d][t][l][h5] <= 1 + X[p][d][t][l][h4];  

//k) Aulas de disciplinas devem ser distribuídas em um, dois ou três dias, de acordo com sua carga horária semanal
forall(d in Disciplinas, t in Turmas)
  sum(l in Turnos)
    W[d][t][l] <= TurmaCargaHorariaDias[d][t];
forall(d in Disciplinas, t in Turmas)
	if(TurmaCargaHoraria[d][t]==5)
		sum(l in Turnos)W[d][t][l] == 3 - V[t];
		
//l) Não deve haver horários vagos entre os horários das turmas
forall(t in Turmas, l in Turnos, h in Horarios: h >= 2)
  sum(p in Professores, d in Disciplinas)X[p][d][t][l][h] <= sum(p in Professores, d in Disciplinas)X[p][d][t][l][h-1];

//m) Cada turma deve cumprir a carga horária de cada disciplina
forall(d in Disciplinas, t in Turmas)
  sum(p in Professores, l in Turnos, h in Horarios)
    X[p][d][t][l][h] == TurmaCargaHoraria[d][t];

//n) Deve haver no mínimo três aulas em cada dia da semana para cada turma do turno da tarde
forall(t in Turmas, l in Turnos: l >= 6)
  if(TurmaMoT[t] == 1)
    sum(p in Professores, d in Disciplinas, h in Horarios)
      X[p][d][t][l][h] >= 3;

//o) Cada professor(a) não pode ministrar mais do que três aulas em uma mesma turma em cada dia
forall(p in Professores, t in Turmas, l in Turnos)
  sum(d in Disciplinas, h in Horarios)
    X[p][d][t][l][h] <= 3;

//p) As aulas de Inglês e Espanhol devem ser lecionadas em aulas seguidas em cada turma
forall(d1 in Disciplinas: d1 == 4 || d1 == 5, d2 in Disciplinas: d2 == 4 && d1 != d2 || d2 == 5 && d1 != d2, t in Turmas, l in Turnos, h1 in Horarios: h1 == 1 || h1 == 2, h2 in Horarios: h2 == 3 || h2 == 4 || h2 == 5)
		sum(p in Professores)X[p][d1][t][l][h1] + sum(p in Professores)X[p][d2][t][l][h2] <= 1;
forall(d1 in Disciplinas: d1 == 4 || d1 == 5, d2 in Disciplinas: d2 == 4 && d1 != d2 || d2 == 5 && d1 != d2, t in Turmas, l in Turnos, h1 in Horarios: h1 == 3, h2 in Horarios: h2 == 5)
		sum(p in Professores)X[p][d1][t][l][h1] + sum(p in Professores)X[p][d2][t][l][h2] <= 1;

}

