#include <stdio.h>
#include <stdlib.h>
#include <pcap.h>
#include <ctype.h>
#include <string.h>
#include <time.h>
#include <getopt.h>
#include <pcap/pcap.h>
#include <errno.h>
#include <sys/socket.h>
#include <netinet/ip6.h>
#include <math.h>
#define __FAVOR_BSD
#include <netinet/in.h>
#include <netinet/ip.h>
#include <netinet/tcp.h>
#include <arpa/inet.h>
#include <netinet/if_ether.h>
#include <err.h>

/*
ISA PROJEKT - Monitoring SSL spojení
Autor: Pavel Sklenář(xsklen12)
*/

/*------------Promenne a Struktury-----------------*/

/*Definice struktury pro IPv4 spojeni*/
typedef struct spojeni{
    struct sockaddr_in zdroj; //zdrojova IPv4 adresa(socket)
    struct sockaddr_in cil; //cilova IPv4 adresa(socket)
    long mikroSekundy; //mikrosekundy konkretniho spojeni
    char casVypis[40]; //cas startu spojeni
    int port; // port spojeni (zdrojovy SYN zpravy(flagu))
    char serverSNI[255]; //promenna pro drzeni nazvu SNI
    int pocetPaketu; // pocet paketu konkretniho spojeni
    long durationSekundy; // sekundy konkretniho spojeni
    int bytes; // pocet bajtu konkretniho spojeni
    int jeClientHello; //indikacni promenna rikajici, zdali v ramci spojeni prisel clienthello paket
    int jeServerHello; //indikacni promenna rikajici, zdali v ramci spojeni prisel serverhello paket
    int finCountCorrect; //indikacni promenna rikajici kolik prislo paketu s FIN flagem
    int serverFin; //indikacni promenna vyjadrujici, ze prisel TCP FIN od serveru
    int clientFin; //indikacni promenna vyjadrujici, ze prisel TCP FIN od klienta
}spojeni;

/*Definice struktury pro IPv6 spojeni - parametry az na zdrojv6 a cilv6 stejne jako pro IPv4 spojeni*/
typedef struct spojeniv6{
    char zdrojv6[INET6_ADDRSTRLEN];//zdrojova IPv6 adresa
    char cilv6[INET6_ADDRSTRLEN];//cilova IPv6 adresa
    long mikroSekundy;
    char casVypis[40];
    int port;
    char serverSNI[255];
    int pocetPaketu;
    long durationSekundy;
    int bytes;
    int jeClientHello;
    int jeServerHello;
    int finCountCorrect;
    int serverFin;
    int clientFin;
}spojeniv6;

spojeni * poleSpojeni; //deklarace pole(dynamicka alokace pomoci malloc a realloc) pro ipv4
spojeniv6 * poleSpojeniv6; //deklarace pole(dynamicka alokace pomoci malloc a realloc) pro ipv6
pcap_t* session; // aktualni session

int ind = 0; //promenna urcena pro indexaci vsech spojeni tykajicich se ipv4
int ind6 = 0; //promenna urcena pro indexaci vsech spojeni tykajicich se ipv6
int paketDebug = 0; //pomocna promenna, hlavne pro debugging.

/*-----------------Sekce Funkce--------------------*/

/*Nazev funkce: getSNI
  Argumenty: 1. const u_char* packet - paket typu Hello Client pro extrahovani server indication name
             2. spojeni *paketv4 - aktualni paket ip verze 4, pro ktery ziskavam SNI
             3. spojeni *paketv6 - aktualni paket ip verze 6, pro ktery ziskavam SNI
             4. int verze - tato promenna slouzi jako prepinac, podle kontextu volani funkce(bud zavolana na ipv4, nebo ipv6)
  Ucel: Ziskani Server Indication Name sifrovaneho spojeni */
void * getSNI(const u_char* packet,spojeni * paketv4,spojeniv6 * paketv6, int verze) {
    int nepokracovat = 0; //indikacni promenna, pokud narazim na znak, ktery neni ascii, opoustim cyklus pro sber znaku SNI
    uint8_t length = *(uint8_t *) (packet + 43); //posunuti po offsetu tak, abych zjistil session length a mohl se posunout dale
    uint16_t lengthCipher = htons(*(uint16_t *) (packet + 43 + length + 1)); //zjisteni sifrovaci delky a nasledny posun dale
    uint8_t compMethodsLength = *(uint8_t *) (packet + 43 + length + lengthCipher + 3); //zjisteni compmethods delky a nasledny posun dale
    uint16_t lengthExtensions = htons(*(uint16_t *) (packet + 43 + length + lengthCipher + compMethodsLength +4)); //zjisteni delky extensions, jen pro kontrolu, asi nejake extensions vubec existuji
    int i = 43 + length + lengthCipher + compMethodsLength + 6;

    if (lengthExtensions == 0) { //pokud nejsou extensions vratim prazdny retezec
        if (verze == 4) {paketv4->serverSNI[0] = 'U';paketv4->serverSNI[1] = 'N';paketv4->serverSNI[2] = 'K';paketv4->serverSNI[3] = 'N';paketv4->serverSNI[4] = 'O';paketv4->serverSNI[5] = 'W';paketv4->serverSNI[6] = 'N';}
        if (verze == 6) {paketv6->serverSNI[0] = 'U';paketv6->serverSNI[1] = 'N';paketv6->serverSNI[2] = 'K';paketv6->serverSNI[3] = 'N';paketv6->serverSNI[4] = 'O';paketv6->serverSNI[5] = 'W';paketv6->serverSNI[6] = 'N';}
    } else {
        for (i; i < i+lengthExtensions; i++) { //pruchod extensiony
            char tmp[7] = "";
            sprintf(tmp, "%02x", packet[i]); //ziskani typu extension, SNI ma 0x0000
            char tmpDruhaCast[7] = "";
            sprintf(tmpDruhaCast, "%02x", packet[i + 1]); //ziskani prefix TLS/SSL hlavicky
            if ((strcmp(tmp, "00") == 0) && (strcmp(tmpDruhaCast, "00") == 0)) { //kontrola na typ zpravy
                uint16_t lengthSNI= htons(*(uint16_t*)(packet+i+7)); //ziskani delky SNI
                if((lengthSNI > 255) || (lengthSNI > lengthExtensions)){ continue; } //kontrola pro delku SNI
                char prvniZnak = packet[i+9]; //offset prvniho znaku
                if ((isalpha(prvniZnak)) || (isdigit(prvniZnak))) { //overovaci podminka
                    char SNI[255] = ""; //inicializace docasne SNI
                    for (int j = 0; j < lengthSNI; j++) {
                        char tmpSNI[2] = "";
                        sprintf(tmpSNI, "%c", packet[i+9+j]);
                        if(isprint(tmpSNI[0])){ //overeni, ze je znak tisknutelny
                            strcat(SNI, tmpSNI); //sber znaku
                        }
                    }
                    strcpy(paketv4->serverSNI, SNI);
                    strcpy(paketv6->serverSNI, SNI);
                    nepokracovat = 1;
                }else { continue; } //pokud to ascii znak neni, vypisu unknown, jinak pokracuji ve sberu znaku
                if(nepokracovat == 1){break;}
            }else{
                uint16_t velikostExtension = htons(*(uint16_t *) (packet + i + 2)); //zjisteni delky Extensionu
                i+=velikostExtension; //posun o velikost extensionu, kdyz extension nebyl typu 0x0000(SNI)
                if(i > lengthExtensions){ break; } //kontrola pro delku extensionu SNI
            }
        }
    }
}

/*Nazev funkce: extractSSLversionData
  Argumenty: 1. const u_char* packet - samotny paket(TCP)
             2. int velikostPayload - velikost dat
             3. int hlavicka - velikost hlavicky paketu
             4. char aktualniPaketZdrojString[] - zdrojova ip adresa aktualniho paketu(ipv4, nebo ipv6)
             5. char aktualniPaketCilString[] - cilova ip adresa aktualniho paketu(ipv4, nebo ipv6)
             6. int zdrojPort, int cilPort - zdrojovy a cilovy port aktualniho paketu
             7. int verze - tato promenna slouzi jako prepinac, podle kontextu volani funkce(bud zavolana na ipv4, nebo ipv6)
             8. char sslVerze[] - tato promenna slouzi k ulozeni konkretni SSL/TLS verze paketu
  Ucel: Ziskani verze SSL/TLS, a pocet bajtu reprezentujici konkretni paket(aktualni)*/
void * extractSSLversionData(const u_char* packet,int velikostPayload,int hlavicka,char aktualniPaketZdrojString[],char aktualniPaketCilString[],int zdrojPort,int cilPort,int verze,char sslVerze[]){
    char spojeniZdrojString[16]; //promenna pro ulozeni string reprezentace teckove notace sitove adresy pri ip verzi 4
    char spojeniCilString[16];
    int jeClientHello = 0; //indikacni promenna pro sledovani helloclient paketu
    const u_char *payloadSegment = (u_char * )(packet+hlavicka); //samotny paket
    int moreSSL = 0; //pokud je vic hlavicek SSL/TLS v paketu, tak tato promenna slouzi k jejich indikaci
    for (int i = 0; i < velikostPayload; i++) { //hledam od ethernet+ip+tcp do konce payloadu daneho paketu
        if((velikostPayload-i) < 5){ //musi zbyvat vic nez 5 bajtu na hlavicku
            break;
        }
        /*Tato sekce slouzi k parsovani jednotlivych bajtu*/
        char tmp[7]="";
        sprintf(tmp, "%02x", payloadSegment[i]); //ziskani typu zpravy
        char tmpDruhaCast[7]="";
        sprintf(tmpDruhaCast, "%02x", payloadSegment[i+1]); //ziskani prefix TLS/SSL hlavicky
        char tmpTretiCast[7] = "";
        sprintf(tmpTretiCast, "%02x", payloadSegment[i+2]); //ziskani verze TLS/SSL hlavicky

        if((strcmp(tmp,"14") == 0) || (strcmp(tmp,"15") == 0) || (strcmp(tmp,"16") == 0) || (strcmp(tmp,"17") == 0)){ //kontrola na typ zpravy
            if(strcmp(tmpDruhaCast,"03") == 0){ //kontrola na prefix SSL/TLS hlavicky
                if((strcmp(tmpTretiCast,"01")) == 0 || (strcmp(tmpTretiCast,"02")) == 0 || (strcmp(tmpTretiCast,"03")) == 0 || (strcmp(tmpTretiCast,"04")) == 0){ //kontrola na verzi SSL(TLS)
                    moreSSL++; //zvyseni o 1
                    if(moreSSL == 1){ //pokud je moressl 1, zapisu data do promenne sslVerze
                        strcat(sslVerze,"0x");
                        strcat(sslVerze,tmpDruhaCast);
                        strcat(sslVerze,tmpTretiCast);
                    }
                    uint16_t delkaBajty =htons(*(uint16_t*)(payloadSegment+i+3)); //ziskani record length z ssl/tls hlavicky
                    if(strcmp(tmp,"16") == 0){ //pokud je client hello, najdu prvni vyskyt hlavicky a koncim, zbytecne iterovat cely paket
                        uint8_t handshakeTyp= *(uint8_t*)(payloadSegment+i+5);
                        if(handshakeTyp == 1){ jeClientHello = 1; }
                    }
                    if(verze == 4){ //pokud je vstup IPv4, tak proiteruji vsechna spojeni a ke konkretnimu spojeni pripoctu delku bajtu konkretniho paketu, ktery ke spojeni patri
                        for (int j = 0; j < ind; j++) {
                            strcpy(spojeniZdrojString,inet_ntoa(poleSpojeni[j].zdroj.sin_addr));
                            strcpy(spojeniCilString,inet_ntoa(poleSpojeni[j].cil.sin_addr));
                            if (((strcmp(spojeniZdrojString, aktualniPaketZdrojString) == 0)) && (strcmp(spojeniCilString,aktualniPaketCilString) == 0) || (strcmp(spojeniZdrojString, aktualniPaketCilString) == 0) && (strcmp(spojeniCilString, aktualniPaketZdrojString) == 0)) {
                                if((zdrojPort == poleSpojeni[j].port) || (cilPort == poleSpojeni[j].port )){
                                    poleSpojeni[j].bytes += delkaBajty; //pripocitani bajtu ke konkretnimu spojeni
                                    i += delkaBajty;
                                }
                            }
                        }
                    }else if(verze == 6){ //pokud je vstup IPv6, tak proiteruji vsechna spojeni a ke konkretnimu spojeni pripoctu delku bajtu konkretniho paketu, ktery ke spojeni patri
                        for (int k = 0; k < ind6; k++) {
                            if (((strcmp(poleSpojeniv6[k].zdrojv6, aktualniPaketZdrojString) == 0)) && (strcmp(poleSpojeniv6[k].cilv6,aktualniPaketCilString) == 0) || (strcmp(poleSpojeniv6[k].zdrojv6, aktualniPaketCilString) == 0) && (strcmp(poleSpojeniv6[k].cilv6, aktualniPaketZdrojString) == 0)) {
                                if((zdrojPort == poleSpojeniv6[k].port) || (cilPort == poleSpojeniv6[k].port )){
                                    poleSpojeniv6[k].bytes += delkaBajty; //pripocitani bajtu ke konkretnimu spojeni
                                    i += delkaBajty;
                                }
                            }
                        }
                    }
                    if(jeClientHello == 1){ break; } //pokud je paket hello client, tak opoustim cyklus
                }
            }
        }
    }
}

/*Nazev funkce: writeConnectionOut
 *   Argumenty: 1. char casVypis[] - timestamp spojeni(tcp paket s flagem SYN konkretniho spojeni),long mikroSekundy - mikrosekundy konkretniho spojeni,char spojeniZdrojString[] - zdrojova adresa konkretniho spojeni(ipv4 nebo ipv6)
 *              2. int port - zdrojovy port(klientsky) konkretniho spojeni,char spojeniCilString[] - cilova adresa konkretniho spojeni (ipv4 nebo ipv6),char serverSNI[] - SNI konkretniho spojeni(z ClientHello paketu)
 *              3. int bytes - pocet bajtu konkretniho spojeni,int pocetPaketu - pocet paketu konkretniho spojeni ,long sekundyFin - pocet sekund paketu s druhym FIN flagem konkretniho spojeni
 *              4. long mikroSekundyFin - pocet mikrosekund paketu s druhym FIN flagem konkretniho spojeni,long durationSekundy - sekundy konkretniho spojeni, const struct pcap_pkthdr* header - pcap_pkthdr* header - hlavicka, ktera obsahuje informace jako kdy byl packet sniffovan, jak je velky, ...
  Ucel: Vypsani informaci o konkretnim spojeni pri prijeti druhe FIN zpravy
 */
void * writeConnectionOut(char casVypis[],long mikroSekundy,char spojeniZdrojString[],int port,char spojeniCilString[],char serverSNI[],int bytes,int pocetPaketu,long sekundyFin, long mikroSekundyFin,long durationSekundy,const struct pcap_pkthdr* header){
    printf("%s.%06ld,%s,%d,%s,%s,%d,%d,",casVypis,mikroSekundy, spojeniZdrojString, port,spojeniCilString,serverSNI,bytes, pocetPaketu);
    char casFin[40];
    strftime(casFin, 40, "%Y-%m-%d %H:%M:%S",localtime(&header->ts.tv_sec)); //inspirace z https://www.geeksforgeeks.org/strftime-function-in-c/
    mikroSekundyFin = header->ts.tv_usec; //ziskani mikrosekund z headeru
    sekundyFin = header->ts.tv_sec; //ziskani sekund z headeru
    long durationMikroSekundy = mikroSekundyFin - mikroSekundy; //vypocitani duration pro mikrosekundy
    durationSekundy = sekundyFin - durationSekundy; //vypocitani duration pro sekundy
    if(durationSekundy >= 1){ //pokud je pocet sekund vetsi nebo rovno 1, nelze jen od sebe odecist mikrosekundy
        durationMikroSekundy *= -1; //inverze
        double mikroSekundyDouble = (double)durationMikroSekundy; //pretypovani na double kvuli desetinnym mistum
        double SekundyDouble = (double)durationSekundy;
        mikroSekundyDouble /= 1000000; //vydeleni mikrosekund milionem abych dostal 0.xxxxxx
        double casFloat =SekundyDouble - mikroSekundyDouble; //vypocitani sekund
        printf("%f\n",casFloat);
    }else{
        printf("%ld.%06ld\n", durationSekundy,durationMikroSekundy);
    }
}

/*Nazev funkce: packet_operation
  Argumenty: 1. u_char* args - aktualni session
             2. pcap_pkthdr* header - hlavicka, ktera obsahuje informace jako kdy byl packet sniffovan, jak je velky, ...
             3. const u_char* packet - samotny paket
  ucel: Operace nad paketem, kontrola delky hlavicek, vypsani payload, ... */
void packet_operation(u_char* args, const struct pcap_pkthdr* header, const u_char* packet) {
    paketDebug++;
    spojeni paket; //paket ipv4
    spojeniv6 paketv6; //paket ipv6
    int finFlag = 0; //inicializace fin flagu
    int rstFlag = 0; //inicializace reset flagu
    int velikostIP; //promenna pro validaci velikosti IP
    int velikostTCP; //promenna pro validaci velikosti TCP
    int hlavicka; // promenna pro velikost cele hlavicky
    int linuxCookedVerze = 0; //indikacni promenna, zda-li linux cooked header je ipv4, nebo ipv6

    struct sockaddr_in aktualniPaketCil,aktualniPaketZdroj; //struktury pro drzeni hodnot saddr, daddr
    struct sockaddr_in6 zdrojv6, cilv6; //struktury pro drzeni hodnot saddr, daddr v ramci ipv6

    /*sekce pro deklaraci jednotlivych typu headeru*/
    const struct iphdr *ip; //ipv4 header
    const struct ip6_hdr *ip6; //ipv6 header
    const struct tcphdr *tcp; //tcp header
    const struct ether_header *ethernet; // ethernet header

    const u_char *payload; //payload paketu
    int velikostPayload; //velikost payloadu

    /*sekce pro deklaraci promennych slouzici k vypoctu casu*/
    long sekundy;
    long mikroSekundy;
    long sekundyFin;
    long mikroSekundyFin;
    char sslVerze[7]=""; //promenna urcena pro ulozeni SSL/TLS verze aktualniho paketu nezavisle na ip verzi

    ethernet = (struct ether_header *) packet;
    const u_short verze = ethernet->ether_type; //ulozeni verze IP sitove vrstvy

    if (pcap_datalink(session) == DLT_LINUX_SLL){ //pokud prijde linux cooked header, musim zjistit verzi ip rucne
        uint16_t hodnotaVerzeLinuxCooked = htons(*(uint16_t *) (packet + 14)); //zjisteni hodnoty verze ip, pokud prijde linux cooked header
        if(hodnotaVerzeLinuxCooked == 2048){ //vetev pro ipv4, hodnoty jsou zjisteny podle standartů
            linuxCookedVerze = 4;
        }else if(hodnotaVerzeLinuxCooked == 34525){ //vetev pro ipv6
            linuxCookedVerze = 6;
        }
    }

    /*==============VĚTEV PRO IPv4==========================*/
    if (ntohs(verze) == ETHERTYPE_IP || linuxCookedVerze == 4) { //pokud je verze IPv4, nebo prijde linux cooked header s ipv4(pri pouziti rozhrani any)
        /*vypocet velikosti IP headeru, minimalne to musi byt 20 bytu*/
        if(pcap_datalink(session) == DLT_LINUX_SLL){ //pokud prijde linux cooked header
            ip = (struct iphdr*)(packet + 16); //eth header ma v tomto pripade 16 bajtu
        }else{
            ip = (struct iphdr *) (packet + sizeof(struct ethhdr)); //viz dokumentace pcap, cituji: "X + SIZE_ETHERNET"
        }
        velikostIP = ip->ihl * 4; //viz dokumentace pcap
        if (velikostIP < 20) {  return; }

        if (ip->protocol == 6) { //pokud je protokol TCP
            /*vypocet velikosti TCP headeru, minimalne to musi byt 20 bytu*/
            if(pcap_datalink(session) == DLT_LINUX_SLL){ //pokud prijde linux cooked header
                tcp = (struct tcphdr*)(packet + 16 + velikostIP); //viz dokumentace pcap:X + SIZE_ETHERNET + {IP header length}
            }else{
                tcp = (struct tcphdr *) (packet + sizeof(struct ethhdr) + velikostIP);
            }

            velikostTCP = (tcp->th_off * 4); //vypocet velikosti TCP hlavicky
            if(pcap_datalink(session) == DLT_LINUX_SLL){ //pokud prijde linux cooked header
                hlavicka = 16 + velikostIP + velikostTCP;
            }else{
                hlavicka = sizeof(struct ethhdr) + velikostIP + velikostTCP;
            }
            if (velikostTCP < 20) { return; } //musi byt minimalne 20 bajtu

            /*ziskani odkazu kam ukazuje zacatek dat(payloadu) paketu v pameti*/
            payload = (u_char * )(packet+hlavicka);

            velikostPayload = header->caplen; //ziskani velikosti payloadu
            int hlavickaExtractSSL = header->len - header->caplen; //len zahrnuje hlavičku, caplen nikoliv(obsahuje payload), proto odectenim ziskam velikost hlavicky, tato promenna se pouziva pouze pro extractSSLversionData()

            /*tato sekce slouzi k ziskani adres pomoci socket struktury(deklarace) a jejich naslednou extrakci do promenne typu pole*/
            memset(&aktualniPaketZdroj, 0, sizeof(aktualniPaketZdroj));
            aktualniPaketZdroj.sin_addr.s_addr = ip->saddr; //ziskani zdrojove adresy
            char aktualniPaketZdrojString[INET_ADDRSTRLEN] = ""; //deklarace promenne pro udrzeni teckove notace ipv4 adresy
            strcpy(aktualniPaketZdrojString,inet_ntoa(aktualniPaketZdroj.sin_addr)); //nutno kopirovat, protoze inet_ntoa pouziva jeden staticky buffer, coz znamena, ze pri pristim zavolani by byl buffer prepsat a adresa ztracena

            memset(&aktualniPaketCil, 0, sizeof(aktualniPaketCil));
            aktualniPaketCil.sin_addr.s_addr = ip->daddr; //ziskani cilove adresy
            char aktualniPaketCilString[INET_ADDRSTRLEN] = ""; //deklarace promenne pro udrzeni teckove notace ipv4 adresy
            strcpy(aktualniPaketCilString,inet_ntoa(aktualniPaketCil.sin_addr));

            int aktualniPaketPortZdroj = ntohs(tcp->th_sport); //ziskani zdrojoveho portu
            int aktualniPaketPortCil =  ntohs(tcp->th_dport); //ziskani ciloveho portu

            char spojeniZdrojString[INET_ADDRSTRLEN] = ""; //promenna slouzici k porovnavani v ramci iterovani pres spojeni(zdrojova adresa)
            char spojeniCilString[INET_ADDRSTRLEN] = ""; //promenna slouzici k porovnavani v ramci iterovani pres spojeni(cilova adresa)
            const u_char * tcpFlag;

            if(pcap_datalink(session) == DLT_LINUX_SLL){ //pokud prijde linux cooked header
                tcpFlag = (u_char * )(packet + 16 + velikostIP); //posunuti na offsetu tak, aby byl zacatek TCP
            }else{
                tcpFlag = (u_char * )(packet + sizeof(struct ethhdr) + velikostIP); //posunuti na offsetu tak, aby byl zacatek TCP
            }

            if ((tcpFlag[13] & 1) != 0) { //pokud prisel paket s FIN flagem
                finFlag = 1; //indikace na 1
                for (int i = 0; i < ind; i++) { //iterovani pres vsechna spojeni a zjisteni, k jakemu spojeni fin paket patri
                    strcpy(spojeniZdrojString,inet_ntoa(poleSpojeni[i].zdroj.sin_addr)); //ziskani adresy v teckove notaci do pole
                    strcpy(spojeniCilString,inet_ntoa(poleSpojeni[i].cil.sin_addr));
                    if((strcmp(spojeniZdrojString, aktualniPaketCilString) == 0) && (strcmp(spojeniCilString, aktualniPaketZdrojString) == 0)
                    &&(strcmp(spojeniZdrojString, aktualniPaketZdrojString) == 0) && (strcmp(spojeniCilString,aktualniPaketCilString) == 0)){ //porovnani asi paket nema stejnou cilovou a zdrojovou adresu(napriklad localhost)
                        poleSpojeni[i].finCountCorrect += 1;
                    }else if ((strcmp(spojeniZdrojString, aktualniPaketZdrojString) == 0) && (strcmp(spojeniCilString,aktualniPaketCilString) == 0)) { //zdrojova adresa paketu(aktualniho) je zdrojova adresa spojeni a cilova adresa paketu je cilova adresa spojeni
                        if(aktualniPaketPortZdroj == poleSpojeni[i].port){
                            poleSpojeni[i].clientFin += 1; //evidovani klientskeho TCP FINu
                            if(poleSpojeni[i].clientFin <= 1){ //pokud uz TCP FIN od klienta prisel, tak aktualni nepocitam
                                poleSpojeni[i].finCountCorrect += 1;
                            }
                        }
                    }else if((strcmp(spojeniZdrojString, aktualniPaketCilString) == 0) && (strcmp(spojeniCilString, aktualniPaketZdrojString) == 0)){ //cilova adresa paketu(aktualniho) je zdrojova adresa spojeni a zdrojova adresa paketu je cilova adresa spojeni
                        if(aktualniPaketPortCil == poleSpojeni[i].port){
                            poleSpojeni[i].serverFin += 1; //evidovani server TCP FINu
                            if(poleSpojeni[i].serverFin <= 1){ //pokud uz TCP FIN od serveru prisel, tak aktualni nepocitam
                                poleSpojeni[i].finCountCorrect += 1;
                            }
                        }
                    }
                }
            }
            if((tcpFlag[13] & 4) != 0){ //pokud prijde reset flag, tak si zeviduji, ze prisel
                rstFlag = 1;
            }
            if (((tcpFlag[13] & 2) != 0) && ((tcpFlag[13] & 16) == 0)) { //pokud prisel paket SYN
                if(ind == 0){ //pokud jeste nebylo vytvorene zadne spojeni, vytvori se dynamicky misto pro 1 spojeni
                    poleSpojeni = malloc(1 * sizeof(*poleSpojeni));
                }else{ // pokud uz spojeni vytvoreno bylo realokuji ind+1 spojeni
                    poleSpojeni = realloc(poleSpojeni,(ind+1) * sizeof(*poleSpojeni));
                }
                sekundy = header->ts.tv_sec; //ziskani sekund
                mikroSekundy = header->ts.tv_usec; //ziskani mikrosekund

                strftime(paket.casVypis, 40, "%Y-%m-%d %H:%M:%S",localtime(&header->ts.tv_sec)); //inspirace z https://www.geeksforgeeks.org/strftime-function-in-c/
                paket.mikroSekundy = mikroSekundy;
                paket.durationSekundy = sekundy;
                paket.serverSNI[0]=',';
                memset(&paket.zdroj, 0, sizeof(paket.zdroj));
                paket.zdroj.sin_addr.s_addr = ip->saddr;

                memset(&paket.cil, 0, sizeof(paket.cil));
                paket.cil.sin_addr.s_addr = ip->daddr;
                int duplikat = 0; // promenna slouzici k tomu, asi se uz nove potencialni spojeni nenachazi ve strukture vsech spojeni

                paket.port = ntohs(tcp->th_sport); //klientsky port(source port)
                char synPaketZdroj[16];
                strcpy(synPaketZdroj,inet_ntoa(paket.zdroj.sin_addr));
                char synPaketCil[16];
                strcpy(synPaketCil,inet_ntoa(paket.cil.sin_addr));

                if(ind > 0){ //pokud je vic nez jedno spojeni kontroluji, asi uz neexistuje
                    for (int i = 0; i < ind; i++) {
                        strcpy(spojeniZdrojString,inet_ntoa(poleSpojeni[i].zdroj.sin_addr));
                        strcpy(spojeniCilString,inet_ntoa(poleSpojeni[i].cil.sin_addr));
                        if ((strcmp(spojeniZdrojString, synPaketZdroj) == 0) && (strcmp(spojeniCilString,synPaketCil) == 0) && (paket.port == poleSpojeni[i].port)) {
                            duplikat = 1; //pokud existuje, oznacim si, ze duplikat je hodnotou 1 a nevytvarim nove spojeni

                        }
                    }
                }
                if((duplikat != 1) || (ind == 0)){ //vytvoreni noveho spojeni pokud nebyl duplikat, nebo je prvni spojeni
                    /*sekce pocatecni inicializace*/
                    poleSpojeni[ind]=paket;
                    poleSpojeni[ind].bytes = 0;
                    poleSpojeni[ind].pocetPaketu = 0;
                    poleSpojeni[ind].clientFin = 0;
                    poleSpojeni[ind].serverFin = 0;
                    poleSpojeni[ind].finCountCorrect = 0;
                    ind++;
                }
            }
            /*tento cyklus slouzi k pocitani paketu konkretniho spojeni, ci overeni ze prisel paket SYN i SYN ACK*/
            for (int i = 0; i < ind; i++) {
                strcpy(spojeniZdrojString,inet_ntoa(poleSpojeni[i].zdroj.sin_addr));
                strcpy(spojeniCilString,inet_ntoa(poleSpojeni[i].cil.sin_addr));
                if (((strcmp(spojeniZdrojString, aktualniPaketZdrojString) == 0)) && (strcmp(spojeniCilString,aktualniPaketCilString) == 0) || (strcmp(spojeniZdrojString, aktualniPaketCilString) == 0) && (strcmp(spojeniCilString, aktualniPaketZdrojString) == 0)) {
                    if((aktualniPaketPortZdroj == poleSpojeni[i].port) || (aktualniPaketPortCil == poleSpojeni[i].port )){
                        poleSpojeni[i].pocetPaketu+= 1;
                    }
                }
            }
            /*zavolani funkce pro extrakci ssl/tls verze a ziskani poctu bajtu do konkretniho spojeni*/
            extractSSLversionData(packet,velikostPayload,hlavickaExtractSSL,aktualniPaketZdrojString,aktualniPaketCilString,aktualniPaketPortZdroj,aktualniPaketPortCil,4,sslVerze);
            if ((strcmp(sslVerze, "0x0301") == 0) || (strcmp(sslVerze, "0x0302") == 0) || (strcmp(sslVerze, "0x0303") == 0) || (strcmp(sslVerze,"0x0304") == 0)) { //pokud je hlavicka TLS 1.0,TLS1.1,TLS1.2,TLS1.3
                uint8_t typZpravy= *(uint8_t*)(payload); //zjisteni typu zpravy
                if(typZpravy == 22){ //pokud je typ zpravy HANDSHAKE
                    uint8_t typHandshake= *(uint8_t*)(payload+5); //pak zjistim typ handshake
                    if((typHandshake == 1) || (typHandshake == 2)){ //pokud je typHandshake 1 jedna se o CLIENT_HELLO, pokud 2 tak se jedna o SERVER_HELLO
                        for (int i = 0; i < ind; i++) { //zjisteni konkretniho spojeni kam zapsat hello client, na zaklade rovnosti source adres a source portu
                            strcpy(spojeniZdrojString,inet_ntoa(poleSpojeni[i].zdroj.sin_addr));
                            strcpy(spojeniCilString,inet_ntoa(poleSpojeni[i].cil.sin_addr));
                            if ((strcmp(aktualniPaketZdrojString, spojeniZdrojString) == 0) && (strcmp(aktualniPaketCilString, spojeniCilString) == 0)) {
                                if(aktualniPaketPortZdroj == poleSpojeni[i].port){
                                    getSNI(payload,&paket,&paketv6,4); //zavolani funkce pro extrakci SNI
                                    if(paket.serverSNI[0] == ','){
                                        poleSpojeni[i].serverSNI[0] = 'U';poleSpojeni[i].serverSNI[1] = 'N';poleSpojeni[i].serverSNI[2] = 'K';poleSpojeni[i].serverSNI[3] = 'N';poleSpojeni[i].serverSNI[4] = 'O';poleSpojeni[i].serverSNI[5] = 'W';poleSpojeni[i].serverSNI[6] = 'N';poleSpojeni[i].serverSNI[7] = '\0';poleSpojeni[i].serverSNI[8] = '\0';
                                    }else{
                                        strcpy(poleSpojeni[i].serverSNI,paket.serverSNI); //nakopirovani do spojeni
                                    }
                                    poleSpojeni[i].jeClientHello = 1; //evidovani clienthello paketu

                                }
                            }

                            if ((strcmp(aktualniPaketZdrojString,spojeniCilString) == 0) && (strcmp(aktualniPaketCilString, spojeniZdrojString) == 0)) {
                                if(aktualniPaketPortCil == poleSpojeni[i].port){ //zjisteni konkretniho spojeni kam zapsat server hello, na zaklade rovnosti source adresy serveru a dest adresy spojeni a dest portu server hello s portem spojeni
                                    poleSpojeni[i].jeServerHello = 1; //evidovani serverhello paket
                                }
                            }

                        }
                    }
                }
            }
            if((finFlag == 1) || (rstFlag == 1)){ //pokud je fin, nebo reset flag jedna zkontroluji, zda-li nejake spojeni nesplnilo podminky pro vypsani, pokud splnilo podminky, tak vypisu
                for (int i = 0; i < ind; i++) {
                    strcpy(spojeniZdrojString,inet_ntoa(poleSpojeni[i].zdroj.sin_addr));
                    strcpy(spojeniCilString,inet_ntoa(poleSpojeni[i].cil.sin_addr));
                    if (((strcmp(spojeniZdrojString, aktualniPaketZdrojString) == 0)) && (strcmp(spojeniCilString,aktualniPaketCilString) == 0) || (strcmp(spojeniZdrojString, aktualniPaketCilString) == 0) && (strcmp(spojeniCilString, aktualniPaketZdrojString) == 0)) {
                        if(poleSpojeni[i].port == aktualniPaketPortZdroj || poleSpojeni[i].port == aktualniPaketPortCil){
                            if((poleSpojeni[i].jeClientHello == 1) && (poleSpojeni[i].jeServerHello == 1)){
                                if((poleSpojeni[i].finCountCorrect == 2) || (rstFlag == 1)){
                                    writeConnectionOut(poleSpojeni[i].casVypis,poleSpojeni[i].mikroSekundy,spojeniZdrojString,poleSpojeni[i].port,spojeniCilString,poleSpojeni[i].serverSNI,poleSpojeni[i].bytes,poleSpojeni[i].pocetPaketu,sekundyFin,mikroSekundyFin,poleSpojeni[i].durationSekundy,header);
                                    poleSpojeni[i].port=-1; //deaktivace portu
                                }
                            }else if((rstFlag == 1) || (poleSpojeni[i].finCountCorrect == 2)){ //odchytavani nevalidnich spojeni(napriklad, kdyz se neuskutecnil TLS handshake)
                                poleSpojeni[i].port=-1; //deaktivace portu
                            }
                        }
                    }
                }

            }
        }
        /*==============VĚTEV PRO IPv6==========================*/
    }else if (ntohs(verze) == ETHERTYPE_IPV6 || linuxCookedVerze == 6) { //pokud je verze paketu ipv6, nebo prijde linux cooked header s ipv6
        /*tato sekce slouzi k ziskani adres pomoci socket struktury(deklarace) a jejich naslednou extrakci do promenne typu pole*/
        struct sockaddr_in6 AktualniPaketZdroj;
        char aktualniPaketZdrojString[INET6_ADDRSTRLEN];
        memset(&AktualniPaketZdroj, 0, sizeof(struct sockaddr_in6));
        struct sockaddr_in6 AktualniPaketCil;
        char aktualniPaketCilString[INET6_ADDRSTRLEN];
        memset(&AktualniPaketCil, 0, sizeof(struct sockaddr_in6));

        if(pcap_datalink(session) == DLT_LINUX_SLL){ //pokud prijde linux cooked header
            ip6 = (struct ip6_hdr*)(packet + 16); //viz dokumentace pcap, cituji: "X + SIZE_ETHERNET"
        }else{
            ip6 = (struct ip6_hdr*)(packet + sizeof(struct ethhdr));
        }

        if (ip6->ip6_ctlun.ip6_un1.ip6_un1_nxt == 6) { //pokud je protokol TCP
            /*alokace pameti pro ulozeni source adresy*/
            memset(&zdrojv6, 0, sizeof(zdrojv6));
            memcpy(zdrojv6.sin6_addr.s6_addr, ip6->ip6_src.s6_addr, sizeof ip6->ip6_src.s6_addr);
            /*alokace pameti pro ulozeni cilove adresy*/
            memset(&cilv6, 0, sizeof(cilv6));
            memcpy(cilv6.sin6_addr.s6_addr, ip6->ip6_dst.s6_addr, sizeof ip6->ip6_dst.s6_addr);

            /*nastaveni pro IPv6 a nasledna extrakce do string podoby*/
            AktualniPaketZdroj.sin6_family = AF_INET6;
            inet_ntop(AF_INET6, &zdrojv6.sin6_addr, aktualniPaketZdrojString, INET6_ADDRSTRLEN);

            /*nastaveni pro IPv6 a nasledna extrakce do string podoby*/
            AktualniPaketCil.sin6_family = AF_INET6;
            inet_ntop(AF_INET6, &cilv6.sin6_addr,aktualniPaketCilString, INET6_ADDRSTRLEN);

            if(pcap_datalink(session) == DLT_LINUX_SLL){ //pokud prijde linux cooked header
                tcp = (struct tcphdr*)(packet + 16 + 40); //viz dokumentace pcap:X + SIZE_ETHERNET + {IP header length}
            }else{
                tcp = (struct tcphdr*)(packet + sizeof(struct ethhdr) + 40);
            }

            velikostTCP = (tcp->th_off * 4); //vypocet velikosti TCP hlavicky

            if(pcap_datalink(session) == DLT_LINUX_SLL){ //pokud prijde linux cooked header
                hlavicka = 16 + 40 + velikostTCP; //40 je konstanta velikosti IPv6
            }else{
                hlavicka = sizeof(struct ethhdr) + 40 + velikostTCP;
            }

            int hlavickaExtractSSL = header->len - header->caplen; //len zahrnuje hlavičku, caplen nikoliv, proto odectenim ziskam velikost hlavicky, tato promenna se pouziva pouze pro extractSSLversionData()
            velikostPayload = header->caplen; //ziskani velikosti payloadu

            /*ziskani odkazu kam ukazuje zacatek hlavicky paketu v pameti*/
            payload = (u_char * )(packet+hlavicka);

            /*extrakce zdrojoveho a ciloveho portu*/
            int aktualniPaketPortZdroj = ntohs(tcp->th_sport);
            int aktualniPaketPortCil =  ntohs(tcp->th_dport);

            const u_char * tcpFlag = (u_char * )(packet + sizeof(struct ethhdr) + 40); //posunuti na offsetu tak, aby byl zacatek TCP
            if((tcpFlag[13] & 4) != 0){ //pokud prijde reset flag, tak si zeviduji, ze prisel
                rstFlag = 1;
            }
            if ((tcpFlag[13] & 1) != 0) { //pokud prisel paket s FIN flagem
                finFlag = 1;
                for (int i = 0; i < ind6; i++) { //iterovani pres vsechna spojeni a zjisteni, k jakemu spojeni fin paket patri
                    if((strcmp(poleSpojeniv6[i].zdrojv6, aktualniPaketZdrojString) == 0) && (strcmp(poleSpojeniv6[i].cilv6,aktualniPaketCilString) == 0)
                    && (strcmp(poleSpojeniv6[i].zdrojv6, aktualniPaketCilString) == 0) && (strcmp(poleSpojeniv6[i].cilv6, aktualniPaketZdrojString) == 0)){ //porovnani asi paket nema stejnou cilovou a zdrojovou adresu(napriklad localhost)
                        poleSpojeniv6[i].finCountCorrect += 1;
                    }else if ((strcmp(poleSpojeniv6[i].zdrojv6, aktualniPaketZdrojString) == 0) && (strcmp(poleSpojeniv6[i].cilv6,aktualniPaketCilString) == 0)) { //zdrojova adresa paketu(aktualniho) je zdrojova adresa spojeni a cilova adresa paketu je cilova adresa spojeni
                        if(aktualniPaketPortZdroj == poleSpojeniv6[i].port){
                            poleSpojeniv6[i].clientFin += 1; //evidovani klientskeho TCP FINu
                            if(poleSpojeniv6[i].clientFin <= 1){  //pokud uz TCP FIN od klienta prisel, tak aktualni nepocitam
                                poleSpojeniv6[i].finCountCorrect += 1;
                            }
                        }
                    }else if((strcmp(poleSpojeniv6[i].zdrojv6, aktualniPaketCilString) == 0) && (strcmp(poleSpojeniv6[i].cilv6, aktualniPaketZdrojString) == 0)){  //cilova adresa paketu(aktualniho) je zdrojova adresa spojeni a zdrojova adresa paketu je cilova adresa spojeni
                        if(aktualniPaketPortCil == poleSpojeniv6[i].port){
                            poleSpojeniv6[i].serverFin += 1; //evidovani server TCP FINu
                            if(poleSpojeniv6[i].serverFin <= 1){ //pokud uz TCP FIN od serveru prisel, tak aktualni nepocitam
                                poleSpojeniv6[i].finCountCorrect += 1;
                            }
                        }
                    }
                }
            }
            if (((tcpFlag[13] & 2) != 0) && ((tcpFlag[13] & 16) == 0)) { //pokud prisel paket SYN
                if(ind6 == 0){ //pokud jeste nebylo vytvorene zadne spojeni, vytvori se dynamicky misto pro 1 spojeni
                    poleSpojeniv6 = malloc(1 * sizeof(*poleSpojeniv6));
                }else{ //pokud uz spojeni vytvoreno bylo realokuji ind+1 spojeni
                    poleSpojeniv6 = realloc(poleSpojeniv6,(ind6+1) * sizeof(*poleSpojeniv6));
                }
                sekundy = header->ts.tv_sec;
                mikroSekundy = header->ts.tv_usec;

                strftime(paketv6.casVypis, 40, "%Y-%m-%d %H:%M:%S",localtime(&header->ts.tv_sec)); //inspirace z https://www.geeksforgeeks.org/strftime-function-in-c/
                paketv6.mikroSekundy = mikroSekundy;
                paketv6.durationSekundy = sekundy;
                paketv6.serverSNI[0] = ',';
                int duplikat = 0; // promenna slouzici k tomu, asi se uz nove potencialni spojeni nenachazi ve strukture vsech spojeni
                paketv6.port = ntohs(tcp->th_sport);

                if(ind6 > 0){  //pokud je vic nez jedno spojeni kontroluji, asi uz neexistuje
                    for (int i = 0; i < ind6; i++) {
                        if (((strcmp(poleSpojeniv6[i].zdrojv6, aktualniPaketZdrojString) == 0)) && (strcmp(poleSpojeniv6[i].cilv6,aktualniPaketCilString) == 0) && (paketv6.port == poleSpojeniv6[i].port)) {
                            duplikat = 1; //pokud existuje, oznacim si, ze duplikat je hodnotou 1 a nevytvarim nove spojeni
                        }
                    }
                }
                if((duplikat != 1) || (ind6 == 0)){ //vytvoreni noveho spojeni pro ipv6 pokud nebyl duplikat, nebo je prvni spojeni
                    /*sekce pocatecni inicializace*/
                    poleSpojeniv6[ind6]=paketv6;
                    strcpy(poleSpojeniv6[ind6].zdrojv6,aktualniPaketZdrojString);
                    strcpy(poleSpojeniv6[ind6].cilv6,aktualniPaketCilString);
                    poleSpojeniv6[ind6].bytes = 0;
                    poleSpojeniv6[ind6].clientFin = 0;
                    poleSpojeniv6[ind6].serverFin = 0;
                    poleSpojeniv6[ind6].pocetPaketu = 0;
                    poleSpojeniv6[ind6].finCountCorrect = 0;
                    ind6++;
                }
            }
            /*tento cyklus slouzi k pocitani paketu konkretniho spojeni, ci overeni ze prisel paket SYN i SYN ACK*/
            for (int i = 0; i < ind6; i++) {
                if (((strcmp(poleSpojeniv6[i].zdrojv6, aktualniPaketZdrojString) == 0)) && (strcmp(poleSpojeniv6[i].cilv6,aktualniPaketCilString) == 0)
                    || (strcmp(poleSpojeniv6[i].zdrojv6, aktualniPaketCilString) == 0) && (strcmp(poleSpojeniv6[i].cilv6, aktualniPaketZdrojString) == 0)) {
                    if((aktualniPaketPortZdroj == poleSpojeniv6[i].port) || (aktualniPaketPortCil == poleSpojeniv6[i].port )){
                        poleSpojeniv6[i].pocetPaketu+= 1;
                    }
                }
            }
            /*zavolani funkce pro extrakci ssl verze a ziskani poctu bajtu do konkretniho spojeni*/
            extractSSLversionData(packet,velikostPayload,hlavickaExtractSSL,aktualniPaketZdrojString,aktualniPaketCilString,aktualniPaketPortZdroj,aktualniPaketPortCil,6,sslVerze);
            if ((strcmp(sslVerze, "0x0301") == 0) || (strcmp(sslVerze, "0x0302") == 0) || (strcmp(sslVerze, "0x0303") == 0) || (strcmp(sslVerze,"0x0304") == 0)) {
                uint8_t typZpravy= *(uint8_t*)(payload); //zjisteni typu zpravy
                if(typZpravy == 22){
                    uint8_t typHandshake= *(uint8_t*)(payload+5); //zjistim typ handshake
                    if((typHandshake == 1) || (typHandshake == 2)){ //pokud je typHandshake 1 jedna se o CLIENT_HELLO, pokud 2 tak se jedna o SERVER_HELLO
                        for (int i = 0; i < ind6; i++) { //zjisteni konkretniho spojeni kam zapsat hello client, na zaklade rovnosti source adres a source portu
                            if ((strcmp(poleSpojeniv6[i].zdrojv6,aktualniPaketZdrojString) == 0) && (strcmp(poleSpojeniv6[i].cilv6,aktualniPaketCilString) == 0)) {
                                if(aktualniPaketPortZdroj == poleSpojeniv6[i].port){
                                    getSNI(payload,&paket,&paketv6,6);
                                    if(paketv6.serverSNI[0] == ','){
                                        poleSpojeniv6[i].serverSNI[0] = 'U';poleSpojeniv6[i].serverSNI[1] = 'N';poleSpojeniv6[i].serverSNI[2] = 'K';poleSpojeniv6[i].serverSNI[3] = 'N';poleSpojeniv6[i].serverSNI[4] = 'O';poleSpojeniv6[i].serverSNI[5] = 'W';poleSpojeniv6[i].serverSNI[6] = 'N';poleSpojeniv6[i].serverSNI[7] = '\0';poleSpojeniv6[i].serverSNI[8] = '\0';
                                    }else{
                                        strcpy(poleSpojeniv6[i].serverSNI,paketv6.serverSNI); //nakopirovani do spojeni
                                    }
                                    poleSpojeniv6[i].jeClientHello = 1; //evidovani clienthello paketu
                                }
                            }
                            if ((strcmp(poleSpojeniv6[i].zdrojv6, aktualniPaketCilString) == 0) && (strcmp(poleSpojeniv6[i].cilv6,aktualniPaketZdrojString) == 0)) {
                                if(aktualniPaketPortCil == poleSpojeniv6[i].port){ //zjisteni konkretniho spojeni kam zapsat server hello, na zaklade rovnosti source adresy serveru a dest adresy spojeni a dest portu server hello s portem spojeni
                                    poleSpojeniv6[i].jeServerHello = 1; //evidovani serverhello paketu
                                }
                            }
                        }
                    }
                }
            }
            if((finFlag == 1) || (rstFlag == 1)){ //pokud je fin, nebo reset flag jedna zkontroluji, zda-li nejake spojeni nesplnilo podminky pro vypsani, pokud splnilo podminky, tak vypisu
                for (int i = 0; i < ind6; i++) {
                    if (((strcmp(poleSpojeniv6[i].zdrojv6, aktualniPaketZdrojString) == 0)) && (strcmp(poleSpojeniv6[i].cilv6,aktualniPaketCilString) == 0)
                        || (strcmp(poleSpojeniv6[i].zdrojv6, aktualniPaketCilString) == 0) && (strcmp(poleSpojeniv6[i].cilv6, aktualniPaketZdrojString) == 0)) {
                        if((aktualniPaketPortZdroj == poleSpojeniv6[i].port) || (aktualniPaketPortCil == poleSpojeniv6[i].port )){
                            if((poleSpojeniv6[i].jeClientHello == 1) && (poleSpojeniv6[i].jeServerHello == 1)){
                                if((poleSpojeniv6[i].finCountCorrect == 2) || (rstFlag == 1)){
                                    writeConnectionOut(poleSpojeniv6[i].casVypis,poleSpojeniv6[i].mikroSekundy,poleSpojeniv6[i].zdrojv6,poleSpojeniv6[i].port,poleSpojeniv6[i].cilv6,poleSpojeniv6[i].serverSNI,poleSpojeniv6[i].bytes,poleSpojeniv6[i].pocetPaketu,sekundyFin,mikroSekundyFin,poleSpojeniv6[i].durationSekundy,header);
                                    poleSpojeniv6[i].port=-1; //deaktivace portu
                                }
                            }else if((rstFlag == 1) || (poleSpojeniv6[i].finCountCorrect == 2)){ //odchytavani nevalidnich spojeni(napriklad, kdyz se neuskutecnil TLS handshake)
                                poleSpojeniv6[i].port=-1; //deaktivace portu
                            }
                        }
                    }
                }
            }
        }
    }
}

/*Nazev funkce: zpracovaniArgumentu
  ucel: funkce se stará o validaci vstupnich hodnot uzivatele, taktez se stara o samotne "zapnuti" snifferu, ci cteni ze souboru
*/
void * zpracovaniArgumentu(int jeRozhrani, int jeSoubor, int jeNapoveda, int jeRozhraniValid, int pocetRozhrani, int pocetSoubor, char * hodnotaRozhrani, char * hodnotaSoubor){
    if (jeSoubor == 1 && hodnotaSoubor == NULL) { //pokud uzivatel nezada hodnotu ve forme souboru ==> chyba, kvuli prioritam chyb si promennou oznacim a osetrim pozdeji
        jeSoubor = 2;
    }

    /*Zjisteni, asi uzivatel nezadal vice rozhrani*/
    if (pocetRozhrani > 1) {
        fprintf(stderr, "\nZadáno více než jedno rozhraní![Nepodporováno]\n\n");
        exit(-1);
    }

    /*Zjisteni, asi uzivatel nezadal vice souboru*/
    if (pocetSoubor > 1) {
        fprintf(stderr, "\nZadáno více souborů než jeden![Nepodporováno]\n\n");
        exit(-1);
    }

    /*pokud uzivatel nezadal rozhrani ani soubor, vypisu napovedu*/
    if (jeRozhrani == 0 && jeSoubor == 0) {
        fprintf(stderr, "\n===============================  Nápověda  ==========================================\n\n");
        fprintf(stderr,"-i [rozhrani] = výběr rozhraní na monitoring SSL, pokud je -i bez hodnoty vypíší se aktivní rozhraní.\n");
        fprintf(stderr,"------------------------------------------------------------------------------------------------------\n");
        fprintf(stderr, "-r [file] = SSL monitoring ze souboru ve formátu .pcapng, pokud soubor neexistuje, nebo na něj nejsou dostatečná oprávnění ==> chybová hláška\n");
        fprintf(stderr,"------------------------------------------------------------------------------------------------------\n\n");
        exit(-1);
    }

    if(jeSoubor == 2){ //vypsani chyby, pokud uzivatel zvolil volbu -r bez hodnoty
        fprintf(stderr,"\nNezadal jste žádný soubor...\n\n");
        exit(0);
    }

    char chyba_pcap[PCAP_ERRBUF_SIZE];//ulozeni error zpravy
    pcap_if_t *rozhrani; //samotna rozhrani
    pcap_if_t *iter; //promenna pro iteraci skrze rozhrani
    int i = 1; //promenna pouzivana jako counter
    if (pcap_findalldevs(&rozhrani, chyba_pcap) == -1) { //zjisteni, asi nastala chyba v ramci konani funkce pcap_findalldevs(), https://www.tcpdump.org/manpages/pcap_findalldevs.3pcap.html
        fprintf(stderr, "\nCHYBA pcap_findalldevs()!");
        exit(-1);
    }

    /*Pokud uzivatel nezadal rozhrani, vypisu vsechny aktivni rozhrani*/
    if (jeRozhrani == 2) {
        fprintf(stderr,"Nezadal jste žádné rozhraní, aktivní rozhraní k výběru jsou:\n");
        for (iter = rozhrani; iter; iter = iter->next) { //iterace skrze rozhrani
            char chyba_lookup[PCAP_ERRBUF_SIZE];//ulozeni error zpravy
            bpf_u_int32 sit; //promenna pro uchovani site
            bpf_u_int32 maska; //promenna pro uchovani masky

            if (!(pcap_lookupnet(iter->name, &sit, &maska, chyba_lookup) == -1)) { //pokud ma rozhrani adresu a masku ==> je aktivni, jinak aktivni neni,  https://www.tcpdump.org/manpages/pcap_lookupnet.3pcap.html
                fprintf(stderr,"%d: %s\n", i, iter->name);
                i++; //zvyseni counteru o 1
            }
        }
        exit(0); //konec programu
    }

    //pokud uzivatel dal k argumentu rozhrani hodnotu
    if (jeRozhrani == 1 && jeSoubor == 0) {
        /*Tento usek kodu slouzi k overeni existence zadaneho rozhrani*/
        char chyba[PCAP_ERRBUF_SIZE]; //ulozeni error zpravy
        pcap_if_t *rozhrani;
        pcap_if_t *iter;
        if (pcap_findalldevs(&rozhrani, chyba) == -1) { //zjisteni, asi pri konani funkce nenastala chyba, https://www.tcpdump.org/manpages/pcap_findalldevs.3pcap.html
            fprintf(stderr, "\nCHYBA pcap_findalldevs()!");
            exit(-1);
        }

        for (iter = rozhrani; iter; iter = iter->next) { //iterovani pres vsechny rozhrani
            if (strcmp(iter->name, hodnotaRozhrani) == 0) { //pokud je zadane rozhrani validni, hodnota indikatoru zmenena na 1
                jeRozhraniValid = 1;
            }
        }

        if (jeRozhraniValid == 0) { //pokud zadane rozhrani neexistuje v seznamu rozhrani, chyba
            fprintf(stderr, "Rozhraní %s neexistuje, aktivní rozhraní jsou následující:\n", hodnotaRozhrani);
            for (iter = rozhrani; iter; iter = iter->next) { //iterace skrze rozhrani
                char chyba_lookup[PCAP_ERRBUF_SIZE];//ulozeni error zpravy
                bpf_u_int32 sit; //promenna pro uchovani site
                bpf_u_int32 maska; //promenna pro uchovani masky
                if (!(pcap_lookupnet(iter->name, &sit, &maska, chyba_lookup) == -1)) { //pokud ma rozhrani adresu a masku ==> je aktivni, jinak aktivni neni,  https://www.tcpdump.org/manpages/pcap_lookupnet.3pcap.html
                    fprintf(stderr,"%d: %s\n", i, iter->name);
                    i++; //zvyseni counteru o 1
                }
            }
            exit(-1);
        }
    }
    if(jeSoubor == 1 && jeRozhrani == 1){ fprintf(stderr,"Zadal jste dvě možnosti naráz, soubor ignoruji, naslouchám na %s ...\n",hodnotaRozhrani);} //pokud uzivatel zada naraz obe moznosti, preferuji naslouchani na rozhrani
    u_char *argumenty = NULL;
    int kolik = 8192; //hodnota, ktera udava, kolik bajtu zachytit z paketu
    char chyba_dev[PCAP_ERRBUF_SIZE]; //ulozeni error zpravy

    if(jeRozhrani == 1){ //pokud uzivatel chce odposlouchavat, pouziji funkci pcap_open_live
        session = pcap_open_live(hodnotaRozhrani, kolik, 1, 1000,chyba_dev); //otevreni session, https://www.tcpdump.org/manpages/pcap_open_live.3pcap.html
        if (session == NULL) { //zachyceni chybneho stavu
            fprintf(stderr, "\nNedostatečné oprávnění k rozhraní, nebo rozhraní neexistuje.\n\n");
            exit(-1);
        }
    }else if(jeSoubor == 1){ //pokud uzivatel chce cist ze souboru, pouziji funkci pcap_open_offline
        session = pcap_open_offline(hodnotaSoubor,chyba_dev); //otevreni session, offline (ze souboru)
        if (session == NULL) { //zachyceni chybneho stavu
            fprintf(stderr, "\nNelze otevřít soubor, soubor buďto neexistuje, nebo nejsou dostatečná práva.\n\n");
            exit(-1);
        }
    }
    pcap_freealldevs(rozhrani); //uvolneni pameti
    pcap_loop(session, INFINITY, packet_operation,argumenty); //ziskavani paketu v cyklu, https://www.tcpdump.org/manpages/pcap_loop.3pcap.html
    free(poleSpojeni); //uvolneni pameti pro ipv4 spojeni
    free(poleSpojeniv6); //uvolneni pameti pro ipv6 spojeni
}

/*-----------Main funkce-----------------*/
int main(int argc, char *argv[]) {
    /* Popsani jednotlivych argumentu */
    static struct option moznosti[] = {{"", optional_argument, 0, 'i'},{"", optional_argument, 0, 'r'}};
    /* Pocatecni inicializace voleb a jejich osetreni */
    int jeRozhrani = 0;
    int jeSoubor = 0;
    int jeNapoveda = 0;
    int jeRozhraniValid = 0;
    int pocetSoubor = 0;
    int pocetRozhrani = 0;
    /* Pocatecni inicializace hodnot voleb a jejich osetreni */
    char * hodnotaRozhrani = "";
    char * hodnotaSoubor = "";

    int choice; //promenna pro iterovani skrze getopt_long

    /*Použit getopt_long viz https://www.gnu.org/software/libc/manual/html_node/Getopt-Long-Option-Example.html*/
    /*Pokud vsechny argumenty byly proiterovany getopt vraci -1, pokud je zadan nejaky neexistujici argument, vraci: ?*/
    while ((choice = getopt_long(argc, argv, ":i:r:", moznosti, NULL)) != -1) { //Iterovani pres vsechny argumenty
        switch (choice) { //Rozhodovaci logika
            case 'i': //pri zadani -i
                jeRozhrani = 1;
                hodnotaRozhrani = optarg;
                pocetRozhrani++;
                break;

            case 'r': //pri zadani -r
                jeSoubor = 1;
                hodnotaSoubor = optarg;
                pocetSoubor++;
                break;

            case ':':
                switch (optopt) { //vetve pokud jsou volby zadane bez hodnoty
                    case 'i': //pro -i ==> aktivni rozhrani
                        pocetRozhrani++;
                        jeRozhrani = 2;
                        break;
                    case 'r': //pro -r ==> soubor
                        jeSoubor = 2;
                        pocetSoubor++;
                        break;
                    default:
                        break;
                }
                break;
            case '?':
                fprintf(stderr, "\nZadán invalidní argument!\n\n");
                exit(-1);
        }
    }
    zpracovaniArgumentu(jeRozhrani, jeSoubor, jeNapoveda, jeRozhraniValid, pocetRozhrani, pocetSoubor, hodnotaRozhrani, hodnotaSoubor);
    return EXIT_SUCCESS;
}
