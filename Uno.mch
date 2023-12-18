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
    NM

PROPERTIES
    NUMERO = 0..9 &
    COMPRAR_DUAS = {10} &
    PULAR = {11} &
    INVERTER = {12} &
    MUDAR_COR = 13..16 &
    COMPRAR_QUATRO = 17..20 &
    NM = 21 // número mágico: para ser usado em relações de congruência
    
    
    
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
    MESA : FIN(NAT) &
    MONTE : FIN(NAT)  &
    CARTAS_AMARELAS : FIN(NAT) &
    CARTAS_AZUIS : FIN(NAT)&
    CARTAS_VERMELHAS : FIN(NAT) &
    CARTAS_VERDES : FIN(NAT) &
    CARTAS_MUDAR_COR : FIN(NAT) &
    CARTAS_COMPRAR_QUATRO : FIN(NAT) &
    JOGADORES : iseq(FIN(NAT)) &
    carta_atual : NAT &
    estado_atual : ESTADO_JOGO &
    jogador_atual : FIN(NAT) &
    (estado_atual /= INICIO => (jogador_atual : ran(JOGADORES))) &
    (estado_atual /= INICIO => (card(JOGADORES) >= 2 or card(JOGADORES) <= 10)) &
    (estado_atual /= INICIO => jogador_atual : ran(JOGADORES)) &
    acumulo_comprar : NAT 
    

    
    
INITIALISATION
    CARTAS_AZUIS := 0..9 \/ 10..12 \/ 22..30 \/ 31..33 || // mod 21. União dos conjuntos na ordem: números, especiais, números (sem zero), especiais. Os coringas podem ser adicionados entre 13..20.
    CARTAS_VERMELHAS := 42..51 \/ 52..54 \/ 64..72 \/ 73..75 ||
    CARTAS_VERDES := 84..93 \/ 94..96 \/ 106..114 \/ 115..117 ||
    CARTAS_AMARELAS := 126..135 \/ 136..138 \/ 148..156 \/ 157..159 ||
    CARTAS_MUDAR_COR := 13..16 ||
    CARTAS_COMPRAR_QUATRO := 17..20 ||
    MESA := {} ||
    MONTE := 0..9 \/ 10..12 \/ 22..30 \/ 31..33 \/ 42..51 \/ 52..54 \/ 64..72 \/ 73..75 \/ 84..93 \/ 94..96 \/ 106..114 \/ 115..117 \/ 126..135 \/ 136..138 \/ 148..156 \/ 157..159 ||
   JOGADORES := {} ||
   jogador_atual := {} ||
   estado_atual := INICIO ||
   carta_atual := 0 ||
   acumulo_comprar := 0
    

    
OPERATIONS 
        
    adicionarJogador =
        PRE estado_atual = INICIO & 
            size(JOGADORES) < 10
        THEN 
            ANY cartas WHERE cartas : FIN(NAT) & cartas <: MONTE & card(cartas) = 7 THEN
                JOGADORES := JOGADORES <- cartas ||
                MONTE := MONTE - cartas ||
                jogador_atual := cartas //define o jogador passado como o jogador atual
            END                        
        END;    
    
    comecarJogo(primeiraCarta) =
        PRE estado_atual = INICIO & {} /: ran(JOGADORES) &
        !jg.(jg : ran(JOGADORES) => card(jg) = 7) &
        size(JOGADORES) >= 2 &
        size(JOGADORES) <= 10 &
        primeiraCarta : MONTE
        THEN 
            estado_atual := MEIO ||
            carta_atual := primeiraCarta ||
            MONTE := MONTE - {primeiraCarta} ||
            MESA := MESA \/ {primeiraCarta}
        END;

    jogarNumero(carta) = 
        PRE estado_atual = MEIO &
            carta : NAT & 
            carta mod NM : NUMERO &
            carta : jogador_atual & // jogador possui carta
            ((carta mod NM = carta_atual mod NM) or 
                ({carta, carta_atual} <: CARTAS_AZUIS) or 
                ({carta, carta_atual} <: CARTAS_VERMELHAS) or 
                ({carta, carta_atual} <: CARTAS_VERDES) or 
                ({carta, carta_atual} <: CARTAS_AMARELAS)) & // cartas são iguais ou possuem mesma cor
            (JOGADORES~(jogador_atual) mod size(JOGADORES) + 1) : dom(JOGADORES)
        THEN 
            IF card(jogador_atual) = 1 THEN
                estado_atual := FIM
            ELSE
                carta_atual := carta ||
                JOGADORES := JOGADORES <+ {JOGADORES~(jogador_atual) |-> jogador_atual - {carta}} ||
                jogador_atual := JOGADORES((JOGADORES~(jogador_atual) mod size(JOGADORES)) + 1) ||
                MESA := MESA \/ {carta}
                END
                
        END;
        
    jogarInverter(carta) = 
        PRE estado_atual = MEIO & 
            carta : NAT & carta : jogador_atual & // jogador possui carta
            carta mod NM : INVERTER & // carta é de inverter
            ((carta mod NM = carta_atual mod NM) or 
               ({carta, carta_atual} <: CARTAS_AZUIS) or ({carta, carta_atual} <: CARTAS_VERMELHAS) or 
               ({carta, carta_atual} <: CARTAS_VERDES) or ({carta, carta_atual} <: CARTAS_AMARELAS)) // cartas são iguais ou possuem mesma cor
        THEN 
            IF card(jogador_atual) = 1 THEN
                estado_atual := FIM
            ELSE             
                carta_atual := carta ||
                MONTE := MONTE - {carta} ||
                MESA := MESA \/ {carta} ||
                LET NOVO_JOGADORES BE  NOVO_JOGADORES = rev(JOGADORES <+ {JOGADORES~(jogador_atual) |-> jogador_atual - {carta}}) IN 
                    JOGADORES := NOVO_JOGADORES || // remove carta da mão do jogador e inverte ordem
                    jogador_atual := NOVO_JOGADORES((JOGADORES~(jogador_atual) mod size(JOGADORES)) + 1)
                END 
            END            
        END;    
        
     jogarPular(carta) = 
        PRE estado_atual = MEIO & 
            carta : NAT & carta : jogador_atual & // jogador possui carta
            carta mod NM : PULAR & // carta é de pular
            (carta mod NM = carta_atual mod NM or 
               {carta, carta_atual} <: CARTAS_AZUIS or {carta, carta_atual} <: CARTAS_VERMELHAS or 
               {carta, carta_atual} <: CARTAS_VERDES or {carta, carta_atual} <: CARTAS_AMARELAS) // cartas são iguais ou possuem mesma cor
        THEN 
            IF card(jogador_atual) = 1 THEN
                estado_atual := FIM
            ELSE
                carta_atual := carta ||
                LET NOVO_JOGADORES BE  NOVO_JOGADORES = JOGADORES <+ {JOGADORES~(jogador_atual) |-> jogador_atual - {carta}} IN 
                    JOGADORES := NOVO_JOGADORES || // remove carta da mão do jogador
                    jogador_atual := NOVO_JOGADORES(((JOGADORES~(jogador_atual)+1) mod size(JOGADORES)) + 1) // aumenta índice em duas unidades
                END ||
                MESA := MESA \/ {carta} 
            END            
        END;    
        
    jogarComprarDuas(carta) = 
        PRE (estado_atual = MEIO or estado_atual = COMPRAR) & // pode executar se alguma carta de comprar foi jogada
            carta : NAT & carta : jogador_atual & // jogador possui carta
            carta mod NM : COMPRAR_DUAS & // carta é de comprar duas
            (carta mod NM = carta_atual mod NM or 
               {carta, carta_atual} <: CARTAS_AZUIS or {carta, carta_atual} <: CARTAS_VERMELHAS or 
               {carta, carta_atual} <: CARTAS_VERDES or {carta, carta_atual} <: CARTAS_AMARELAS) & // cartas são iguais ou possuem mesma cor
            acumulo_comprar + 2 : NAT
        THEN 
            IF card(jogador_atual) = 1 THEN
                estado_atual := FIM
            ELSE
                carta_atual := carta ||
                LET NOVO_JOGADORES BE  NOVO_JOGADORES = JOGADORES <+ {JOGADORES~(jogador_atual) |-> jogador_atual - {carta}} IN 
                    JOGADORES := NOVO_JOGADORES || // remove carta da mão do jogador
                    jogador_atual := NOVO_JOGADORES((JOGADORES~(jogador_atual) mod size(JOGADORES)) + 1)
                END ||            
                MESA := MESA \/ {carta} ||
                estado_atual := COMPRAR || // muda ou mantém o estado em COMPRAR
                acumulo_comprar := acumulo_comprar + 2 // aumenta o acumulo de compra em 2
            END            
        END;            
        
    
    jogarMudarCor(carta) = 
        PRE (estado_atual = MEIO) &
            card(jogador_atual) > 1 & // a ultima carta do jogador nao pode ser um coringa
            carta : NAT & carta : jogador_atual & // jogador possui carta
            carta mod NM : MUDAR_COR // carta é coringa que muda cor
        THEN 
            carta_atual := carta ||
            LET NOVO_JOGADORES BE  NOVO_JOGADORES = JOGADORES <+ {JOGADORES~(jogador_atual) |-> jogador_atual - {carta}} IN 
                JOGADORES := NOVO_JOGADORES || // remove carta da mão do jogador
                jogador_atual := NOVO_JOGADORES((JOGADORES~(jogador_atual) mod size(JOGADORES)) + 1)
            END ||
            MESA := MESA \/ {carta} ||
            CHOICE CARTAS_AZUIS := CARTAS_AZUIS \/ {carta_atual} OR CARTAS_VERMELHAS := CARTAS_VERMELHAS \/ {carta_atual} OR 
                CARTAS_VERDES := CARTAS_VERDES \/ {carta_atual} OR CARTAS_AMARELAS := CARTAS_AMARELAS \/ {carta_atual}
            END // Define uma cor para carta atual
            
        END;    
        
        
    jogarComprarQuatro(carta) = 
        PRE (estado_atual = MEIO or estado_atual = COMPRAR) & // pode executar se alguma carta de comprar foi jogada
            card(jogador_atual) > 1 & // a ultima carta do jogador nao pode ser um coringa
            carta : NAT & carta : jogador_atual & // jogador possui carta
            carta mod NM : COMPRAR_QUATRO & // carta é coringa comprar 4
            acumulo_comprar + 4 : NAT
        THEN 
            carta_atual := carta ||
            LET NOVO_JOGADORES BE  NOVO_JOGADORES = JOGADORES <+ {JOGADORES~(jogador_atual) |-> jogador_atual - {carta}} IN 
                JOGADORES := NOVO_JOGADORES || // remove carta da mão do jogador
                jogador_atual := NOVO_JOGADORES((JOGADORES~(jogador_atual) mod size(JOGADORES)) + 1)
            END ||
            MESA := MESA \/ {carta} ||
            CHOICE CARTAS_AZUIS := CARTAS_AZUIS \/ {carta} OR CARTAS_VERMELHAS := CARTAS_VERMELHAS \/ {carta} OR 
                CARTAS_VERDES := CARTAS_VERDES \/ {carta} OR CARTAS_AMARELAS := CARTAS_AMARELAS \/ {carta}
            END || // Define uma cor para carta atual            
            estado_atual := COMPRAR || // muda ou mantém o estado em COMPRAR
            acumulo_comprar := acumulo_comprar + 4 // aumenta o acumulo de compra em 4
        END;  
        
    comprarCartas(cartas) = 
        PRE (estado_atual = COMPRAR) & // só pode executar caso o estado seja COMPRAR
            cartas <: MONTE & card(cartas) = acumulo_comprar // a quantidade de cartas a serem compradas é igual ao acúmulo
        THEN 
            MONTE := MONTE - cartas ||
            LET NOVO_JOGADORES BE  NOVO_JOGADORES = JOGADORES <+ {JOGADORES~(jogador_atual) |-> (jogador_atual \/ cartas)} IN 
                JOGADORES := NOVO_JOGADORES ||  // adiciona cartas a mão do jogador
                jogador_atual := NOVO_JOGADORES((JOGADORES~(jogador_atual) mod size(JOGADORES)) + 1)
            END ||
            estado_atual := MEIO || // muda o estado atual para MEIO
            acumulo_comprar := 0
        END;    
        
        
    puxarCarta(carta) = 
        PRE (estado_atual = MEIO) & 
            carta : MONTE &
            !ca.(ca : jogador_atual => {ca, carta_atual} /<: CARTAS_AZUIS & 
                {ca, carta_atual} /<: CARTAS_VERMELHAS & {ca, carta_atual} /<: CARTAS_VERDES & 
                {ca, carta_atual} /<: CARTAS_AMARELAS & ca /: (MUDAR_COR \/ COMPRAR_QUATRO)) & // jogador não possui nenhuma carta que combine com a atual nem possui nenhum coringa
            ((JOGADORES~(jogador_atual) mod size(JOGADORES)) + 1) : dom(JOGADORES)
        THEN 
            MONTE := MONTE - {carta} ||
             LET NOVO_JOGADORES BE  NOVO_JOGADORES = JOGADORES <+ {JOGADORES~(jogador_atual) |-> (jogador_atual \/ {carta})} IN 
                JOGADORES := NOVO_JOGADORES ||  // adiciona carta a mão do jogador
                jogador_atual := NOVO_JOGADORES((JOGADORES~(jogador_atual) mod size(JOGADORES)) + 1)
            END
        END;   
        
        
    un <-- dizerUno(jogador, indice_jogador) = 
        PRE (estado_atual = MEIO) & 
            indice_jogador : dom(JOGADORES) &
            jogador : ran(JOGADORES) & 
            JOGADORES(indice_jogador) = jogador & // índice correponde a jogador
            card(JOGADORES(indice_jogador)) = 1 & // o jogador possui apenas uma carta
            un : DIZER_UNO
        THEN
            un := UNO
        END;    
        
    reiniciarJogo =
        PRE estado_atual = FIM 
        THEN    
            estado_atual := INICIO ||
            jogador_atual := {}  ||
            JOGADORES := {} ||
            MESA := {} ||
            MONTE := 0..9 \/ 10..12 \/ 22..30 \/ 31..33 \/ 42..51 \/ 52..54 \/ 64..72 \/ 73..75 \/ 84..93 \/ 94..96 \/ 106..114 \/ 115..117 \/ 126..135 \/ 136..138 \/ 148..156 \/ 157..159 ||
            carta_atual := 0 ||
            acumulo_comprar := 0
        END        
END


