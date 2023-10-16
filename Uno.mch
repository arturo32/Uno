MACHINE Uno

SETS
    ESTADO_JOGO = {INICIO, MEIO, FIM}

CONSTANTS
    NUMERO,
    COMPRAR_DUAS,
    PULAR,
    INVERTER,
    MUDAR_COR,
    COMPRAR_QUATRO,
    NUMERO_JOGADORES

PROPERTIES
    NUMERO = 0..9 &
    COMPRAR_DUAS = {10} &
    PULAR = {11} &
    INVERTER = {12} &
    MUDAR_COR = 13..16 &
    COMPRAR_QUATRO = 17..20 &
    NUMERO_JOGADORES = 3
    
    
    
VARIABLES
	MESA, // cartas já puxadas
	MONTE, // cartas para serem puxadas
	CARTAS_AMARELAS, 
	CARTAS_AZUIS, CARTAS_VERMELHAS, CARTAS_VERDES, // cartas numéricas, comprar duas, pular e inverter
	CARTAS_MUDAR_COR, // cartas coringas que mudam a cor
	CARTAS_COMPRAR_QUATRO, // cartas coringas comprar 4
	jogador_atual, carta_atual, estado_atual,
	JOGADORES
   
	

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
    size(JOGADORES) <= 10

    
    
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
   carta_atual::{}
	

	
OPERATIONS 
    distribuirCartas(jogador, indice_jogador, cartas) =
        PRE estado_atual = INICIO & 
            indice_jogador : NAT  & indice_jogador <= NUMERO_JOGADORES & 
            jogador : JOGADORES & {indice_jogador} <| JOGADORES = {jogador} &
            JOGADORES(indice_jogador) = {} &
            cartas <: MONTE & card(cartas) = 7
        THEN 
            jogador := indice_jogador |-> cartas ||
            MONTE := MONTE - cartas
        END;
        
    comecarJogo =
        PRE estado_atual = INICIO & {} /: ran(JOGADORES)
        THEN 
            estado_atual := MEIO
        END;

    jogarNumero(jogador, indice_jogador, carta) = 
        PRE estado_atual = MEIO & 
            jogador = jogador_atual & carta : NAT & {carta} : ran({jogador}) &
            indice_jogador : NAT & indice_jogador <= NUMERO_JOGADORES
        THEN 
            carta_atual := carta ||
            MONTE := MONTE - {carta} ||
            MESA := MESA \/ {carta} ||
            jogador_atual:(jogador_atual : JOGADORES & {(indice_jogador+1) mod NUMERO_JOGADORES} <| JOGADORES = {jogador})
        END
        
        
        
	
END