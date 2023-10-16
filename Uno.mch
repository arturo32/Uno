MACHINE Uno

SETS
    ESTADO_JOGO = {INICIO, MEIO, COMPRAR, FIM};
    DIZER_UNO = {UNO}

CONSTANTS
    NUMERO,
    COMPRAR_DUAS,
    PULAR,
    INVERTER,
    MUDAR_COR,
    COMPRAR_QUATRO,
    NUMERO_JOGADORES,
    NM

PROPERTIES
    NUMERO = 0..9 &
    COMPRAR_DUAS = {10} &
    PULAR = {11} &
    INVERTER = {12} &
    MUDAR_COR = 13..16 &
    COMPRAR_QUATRO = 17..20 &
    NUMERO_JOGADORES = 3 &
    NM = 21 // número mágico: para ser usado em relações de congruência &
    
    
    
VARIABLES
	MESA, // cartas já puxadas
	MONTE, // cartas para serem puxadas
	CARTAS_AMARELAS, 
	CARTAS_AZUIS, CARTAS_VERMELHAS, CARTAS_VERDES, // cartas numéricas, comprar duas, pular e inverter
	CARTAS_MUDAR_COR, // cartas coringas que mudam a cor
	CARTAS_COMPRAR_QUATRO, // cartas coringas comprar 4
	jogador_atual, carta_atual, estado_atual,
	JOGADORES,
	acumulo_comprar // número de cartas que devem ser compradas pelo jogador atual
   
	

INVARIANT
    CARTAS_AZUIS <: NAT &
    CARTAS_VERMELHAS <: NAT &
    CARTAS_VERDES<: NAT &
    CARTAS_AMARELAS <: NAT &
    CARTAS_MUDAR_COR <: NAT &
    CARTAS_COMPRAR_QUATRO <: NAT &
    MESA <: NAT &
    MONTE <: NAT &
    JOGADORES : iseq(POW(NAT)) &
    card(JOGADORES) = NUMERO_JOGADORES &
    jogador_atual : JOGADORES &
    carta_atual : NAT &
    estado_atual : ESTADO_JOGO &
    size(JOGADORES) >= 2 &
    size(JOGADORES) <= 10 &
    acumulo_comprar : NAT

    
    
INITIALISATION
	CARTAS_AZUIS := 0..9 \/ 10..12 \/ 22..30 \/ 31..33 || // mod 21. União dos conjuntos na ordem: números, especiais, números (sem zero), especiais. Os coringas podem ser adicionados entre 13..20.
	CARTAS_VERMELHAS := 42..51 \/ 52..54 \/ 64..72 \/ 73..75 ||
	CARTAS_VERDES := 84..93 \/ 94..96 \/ 106..114 \/ 115..117 ||
	CARTAS_AMARELAS := 126..135 \/ 136..138 \/ 148..156 \/ 157..159 ||
	CARTAS_MUDAR_COR := 13..16 ||
	CARTAS_COMPRAR_QUATRO := 17..20 ||
	MESA := {} ||
	MONTE := CARTAS_AZUIS \/ CARTAS_VERMELHAS \/ CARTAS_VERDES \/ CARTAS_AMARELAS \/ CARTAS_MUDAR_COR  \/ CARTAS_COMPRAR_QUATRO ||
   JOGADORES::{} ||
   jogador_atual::JOGADORES ||
   estado_atual := INICIO ||
   carta_atual::{} ||
   acumulo_comprar := 0
	

	
OPERATIONS 
    distribuirCartas(jogador, indice_jogador, cartas) =
        PRE estado_atual = INICIO & 
            indice_jogador : dom(JOGADORES) &
            jogador : JOGADORES & {indice_jogador} <| JOGADORES = {jogador} &
            JOGADORES(indice_jogador) = {} &
            cartas <: MONTE & card(cartas) = 7
        THEN 
            JOGADORES := JOGADORES <+ {indice_jogador |-> cartas} ||
            MONTE := MONTE - cartas
        END;
        
    comecarJogo =
        PRE estado_atual = INICIO & {} /: ran(JOGADORES)
        THEN 
            estado_atual := MEIO
        END;

    jogarNumero(jogador, indice_jogador, carta) = 
        PRE estado_atual = MEIO & 
            jogador = jogador_atual & 
            carta : NAT & {carta} : ran({jogador}) & // jogador possui carta
            carta_atual mod NM : NUMERO & carta mod NM : NUMERO & // cartas são números
            (carta mod NM = carta_atual mod NM or 
               {carta, carta_atual} <: CARTAS_AZUIS or {carta, carta_atual} <: CARTAS_VERMELHAS or 
               {carta, carta_atual} <: CARTAS_VERDES or {carta, carta_atual} <: CARTAS_AMARELAS) & // cartas são iguais ou possuem mesma cor
            indice_jogador : dom(JOGADORES) & 
            {indice_jogador} <| JOGADORES = {jogador} // índice correponde a jogador
        THEN 
            carta_atual := carta ||
            JOGADORES := JOGADORES <+ {indice_jogador |-> JOGADORES(indice_jogador) - {carta}} || // remove carta da mão do jogador
            MESA := MESA \/ {carta} ||
            jogador_atual:(jogador_atual : JOGADORES & {(indice_jogador+1) mod NUMERO_JOGADORES} <| JOGADORES = {jogador})
        END;
        
    jogarInverter(jogador, indice_jogador, carta) = 
        PRE estado_atual = MEIO & 
            jogador = jogador_atual & 
            carta : NAT & {carta} : ran({jogador}) & // jogador possui carta
            carta mod NM : INVERTER & // carta é de inverter
            (carta mod NM = carta_atual mod NM or 
               {carta, carta_atual} <: CARTAS_AZUIS or {carta, carta_atual} <: CARTAS_VERMELHAS or 
               {carta, carta_atual} <: CARTAS_VERDES or {carta, carta_atual} <: CARTAS_AMARELAS) & // cartas são iguais ou possuem mesma cor
            indice_jogador : dom(JOGADORES) & 
            {indice_jogador} <| JOGADORES = {jogador} // índice correponde a jogador
        THEN 
            carta_atual := carta ||
            MONTE := MONTE - {carta} ||
            MESA := MESA \/ {carta} ||
            JOGADORES := rev(JOGADORES <+ {indice_jogador |-> JOGADORES(indice_jogador) - {carta}}) || // remove carta da mão do jogador e inverte sequência de jogadores
            jogador_atual:(jogador_atual : JOGADORES & {(indice_jogador+1) mod NUMERO_JOGADORES} <| JOGADORES = {jogador})
        END;    
        
     jogarPular(jogador, indice_jogador, carta) = 
        PRE estado_atual = MEIO & 
            jogador = jogador_atual & 
            carta : NAT & {carta} : ran({jogador}) & // jogador possui carta
            carta mod NM : PULAR & // carta é de pular
            (carta mod NM = carta_atual mod NM or 
               {carta, carta_atual} <: CARTAS_AZUIS or {carta, carta_atual} <: CARTAS_VERMELHAS or 
               {carta, carta_atual} <: CARTAS_VERDES or {carta, carta_atual} <: CARTAS_AMARELAS) & // cartas são iguais ou possuem mesma cor
            indice_jogador : dom(JOGADORES) &
            {indice_jogador} <| JOGADORES = {jogador} // índice correponde a jogador
        THEN 
            carta_atual := carta ||
            JOGADORES := JOGADORES <+ {indice_jogador |-> JOGADORES(indice_jogador) - {carta}} || // remove carta da mão do jogador
            MESA := MESA \/ {carta} ||
            jogador_atual:(jogador_atual : JOGADORES & {(indice_jogador+2) mod NUMERO_JOGADORES} <| JOGADORES = {jogador}) // aumenta índice em duas unidades
        END;    
        
    jogarComprarDuas(jogador, indice_jogador, carta) = 
        PRE (estado_atual = MEIO or estado_atual = COMPRAR) & // pode executar se alguma carta de comprar foi jogada
            jogador = jogador_atual & 
            carta : NAT & {carta} : ran({jogador}) & // jogador possui carta
            carta mod NM : COMPRAR_DUAS & // carta é de comprar duas
            (carta mod NM = carta_atual mod NM or 
               {carta, carta_atual} <: CARTAS_AZUIS or {carta, carta_atual} <: CARTAS_VERMELHAS or 
               {carta, carta_atual} <: CARTAS_VERDES or {carta, carta_atual} <: CARTAS_AMARELAS) & // cartas são iguais ou possuem mesma cor
            indice_jogador : dom(JOGADORES) & 
            {indice_jogador} <| JOGADORES = {jogador} // índice correponde a jogador
        THEN 
            carta_atual := carta ||
            JOGADORES := JOGADORES <+ {indice_jogador |-> JOGADORES(indice_jogador) - {carta}} || // remove carta da mão do jogador
            MESA := MESA \/ {carta} ||
            jogador_atual:(jogador_atual : JOGADORES & {(indice_jogador+1) mod NUMERO_JOGADORES} <| JOGADORES = {jogador}) ||
            estado_atual := COMPRAR || // muda ou mantém o estado em COMPRAR
            acumulo_comprar := acumulo_comprar + 2 // aumenta o acumulo de compra em 2
        END;            
        
	
    jogarMudarCor(jogador, indice_jogador, carta) = 
        PRE (estado_atual = MEIO) &
            jogador = jogador_atual & 
            carta : NAT & {carta} : ran({jogador}) & // jogador possui carta
            carta mod NM : MUDAR_COR & // carta é coringa que muda cor
            indice_jogador : dom(JOGADORES) &
            {indice_jogador} <| JOGADORES = {jogador} // índice correponde a jogador
        THEN 
            carta_atual := carta ||
            JOGADORES := JOGADORES <+ {indice_jogador |-> JOGADORES(indice_jogador) - {carta}} || // remove carta da mão do jogador
            MESA := MESA \/ {carta} ||
            CHOICE CARTAS_AZUIS := CARTAS_AZUIS \/ {carta_atual} OR CARTAS_VERMELHAS := CARTAS_VERMELHAS \/ {carta_atual} OR 
                CARTAS_VERDES := CARTAS_VERDES \/ {carta_atual} OR CARTAS_AMARELAS := CARTAS_AMARELAS \/ {carta_atual}
            END || // Define uma cor para carta atual
            jogador_atual:(jogador_atual : JOGADORES & {(indice_jogador+1) mod NUMERO_JOGADORES} <| JOGADORES = {jogador})
        END;	
        
        
    jogarComprarQuatro(jogador, indice_jogador, carta) = 
        PRE (estado_atual = MEIO or estado_atual = COMPRAR) & // pode executar se alguma carta de comprar foi jogada
            jogador = jogador_atual & 
            carta : NAT & {carta} : ran({jogador}) & // jogador possui carta
            carta mod NM : COMPRAR_QUATRO & // carta é coringa comprar 4
            indice_jogador : dom(JOGADORES) &
            {indice_jogador} <| JOGADORES = {jogador} // índice correponde a jogador
        THEN 
            carta_atual := carta ||
            JOGADORES := JOGADORES <+ {indice_jogador |-> JOGADORES(indice_jogador) - {carta}} || // remove carta da mão do jogador
            MESA := MESA \/ {carta} ||
            CHOICE CARTAS_AZUIS := CARTAS_AZUIS \/ {carta} OR CARTAS_VERMELHAS := CARTAS_VERMELHAS \/ {carta} OR 
                CARTAS_VERDES := CARTAS_VERDES \/ {carta} OR CARTAS_AMARELAS := CARTAS_AMARELAS \/ {carta}
            END || // Define uma cor para carta atual
            jogador_atual:(jogador_atual : JOGADORES & {(indice_jogador+1) mod NUMERO_JOGADORES} <| JOGADORES = {jogador}) ||
            estado_atual := COMPRAR || // muda ou mantém o estado em COMPRAR
            acumulo_comprar := acumulo_comprar + 4 // aumenta o acumulo de compra em 4
        END;  
        
    comprarCartas(jogador, indice_jogador, cartas) = 
        PRE (estado_atual = COMPRAR) & // só pode executar caso o estado seja COMPRAR
            jogador = jogador_atual & 
            indice_jogador : dom(JOGADORES) & 
            {indice_jogador} <| JOGADORES = {jogador} & // índice correponde a jogador
            cartas <: MONTE & card(cartas) = acumulo_comprar // a quantidade de cartas a serem compradas é igual ao acúmulo
        THEN 
            MONTE := MONTE - cartas ||
            JOGADORES := JOGADORES <+ {indice_jogador |-> (JOGADORES(indice_jogador) \/ cartas)} || // adiciona cartas a mão do jogador
            jogador_atual:(jogador_atual : JOGADORES & {(indice_jogador+1) mod NUMERO_JOGADORES} <| JOGADORES = {jogador}) ||
            estado_atual := MEIO || // muda o estado atual para MEIO
            acumulo_comprar := 0
        END;    
        
        
    puxarCarta(jogador, indice_jogador, carta) = 
        PRE (estado_atual = MEIO) & 
            jogador = jogador_atual & 
            indice_jogador : dom(JOGADORES) &
            {indice_jogador} <| JOGADORES = {jogador} & // índice correponde a jogador
            carta : MONTE &
            !ca.(ca : JOGADORES(indice_jogador) => {ca, carta_atual} /<: CARTAS_AZUIS & 
                {ca, carta_atual} /<: CARTAS_VERMELHAS & {ca, carta_atual} /<: CARTAS_VERDES & 
                {ca, carta_atual} /<: CARTAS_AMARELAS & ca /: (MUDAR_COR \/ COMPRAR_QUATRO)) // jogador não possui nenhuma carta que combine com a atual nem possui nenhum coringa
        THEN 
            MONTE := MONTE - {carta} ||
            JOGADORES := JOGADORES <+ {indice_jogador |-> (JOGADORES(indice_jogador) \/ {carta})} || // adiciona carta a mão do jogador
            jogador_atual:(jogador_atual : JOGADORES & {(indice_jogador+1) mod NUMERO_JOGADORES} <| JOGADORES = {jogador})
        END;   
        
        
    un <-- dizerUno(jogador, indice_jogador) = 
        PRE (estado_atual = MEIO) & 
            jogador : JOGADORES &
            indice_jogador : dom(JOGADORES) & 
            {indice_jogador} <| JOGADORES = {jogador} & // índice correponde a jogador
            card(JOGADORES(indice_jogador)) = 1 & // o jogador possui apenas uma carta
            un : DIZER_UNO
        THEN
            un := UNO
        END            
END
