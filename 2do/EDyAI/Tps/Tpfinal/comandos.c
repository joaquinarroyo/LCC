#include "comandos.h"

int opcion(char comando[]) {
  int j = 0;
  if (!memcmp(comando, "imprimir", sizeof(char) * 8)) {    
    return IMPRIMIR; 
  } 
  if (!(strcmp(comando, "salir"))) {      
    return SALIR;
  }
  while (comando[j] != '=' && comando[j] != '\0') {
    j++;
  }
  if (comando[j] != '\0') {
    j+=2;
  } else {
      return INVALIDO;
  }
  for (int i = j; comando[i] != '\0'; i++) {
    if (comando[i] == '|') {        
      return UNION;     
    }   
    if (comando[i] == '&') {      
      return INTERSECCION;    
    }    
    if (comando[i] == '-' && (isdigit(comando[i + 1]) == 0)) {          
      return RESTA;      
    }
    if (comando[i] == '~') {       
      return COMPLEMENTO;   
    }
  }
  j = 0;
  while (comando[j] != '{' && comando[j] != '\0') {
    j++;
  }
  for (int i = j; comando[i] != '\0'; i++) {
    if(comando[i] == '{' && comando[i + 1] == '}'){
      return CREAR_VACIO;
    }
    if (comando[i] == '{' 
               && ((isdigit(comando[i + 1]) != 0) || comando[i + 1] == '-')) {
      return CREAR_EXT;
    }
    if (comando[i] == '{') {
      return CREAR_COMP;   
    }
  }
  return INVALIDO;
}

int cantidad_elementos(char comando[]) {
  int i = 0, contador = 0;
  while (comando[i] != '\0') {
    if (comando[i] == ',') {         
      contador++;    
    }   
    i++;  
  }
  return contador + 1;
}

char *comando_alias(char comando[]) {
  int i = 0, j = 0, contador = 0;
  if (!memcmp(comando, "imprimir", sizeof(char) * 8)) {     
    i = 9;      
    while (comando[i] != '\0' && comando[i] != ' ') {        
      contador++;         
      i++;      
    }      
    char *alias = malloc(sizeof(char) * (contador + 1));   
    i = 9;     
    while (j < contador) {         
      alias[j] = comando[i];   
      j++;        
      i++;      
    }    
    alias[j] = '\0';     
    return alias; 
  } else {     
      while (comando[i] != ' ') {          
        i++;      
      }
      char *alias = malloc(sizeof(char) * (i + 1)); 
      while (j < i) {        
        alias[j] = comando[j];         
        j++;     
      }
      alias[j] = '\0';     
      return alias;  
  }
}
 
void comando_conjunto(char comando[], int conjunto[], int tipo, int cantidad) {
  int i = 0, j = 0, contador = 0, cantCarac = 0;
  if (tipo == CREAR_EXT) {     
    while (comando[i] != '{') {       
      i++;    
    }     
    i++;      
    while (contador < cantidad) {          
      int tmp = i;          
      while (comando[tmp] != ',' && comando[tmp] != '}') {           
        cantCarac++;             
        tmp++;         
      }         
      cantCarac++;         
      char temp[cantCarac];          
      while (comando[i] != ',' && comando[i] != '}') {            
        temp[j] = comando[i];             
        j++;              
        i++;          
      }          
      temp[j] = '\0';         
      i++;         
      conjunto[contador] = atoi(temp);          
      j = 0;          
      cantCarac = 0;          
      contador++;      
      }  
  } else {      
    while (comando[i] != ':') {          
      i++;      
    }     
    i += 2;     
    int tmp = i;      
    while (comando[tmp] != ' ') {          
      cantCarac++;          
      tmp++;     
    }     
    cantCarac++;       
    char temp[cantCarac];       
    while (comando[i] != ' ') {          
      temp[j] = comando[i];        
      j++;        
      i++;    
    }      
    temp[j] = '\0';
    conjunto[0] = atoi(temp);      
    j = 0;    
    cantCarac = 0;      
    while ((isdigit(comando[i]) == 0) && comando[i] != '-') {        
      i++;    
    }  
    tmp = i;      
    while (comando[tmp] != '}') {          
      cantCarac++;     
      tmp++;    
    }      
    cantCarac++;   
    char temp2[cantCarac]; 
    while (comando[i] != '}') {       
      temp2[j] = comando[i];       
      j++;      
      i++;    
    } 
    temp2[j] = '\0';    
    conjunto[1] = atoi(temp2);
  }
}

int extension_assert(char comando[]) {
  int i = 0, bandera = 0; 
  while (comando[i] != '{' && comando[i] != '\0') {      
    if (comando[i + 1] == '=' && comando[i] == ' ') {          
      bandera = 1;      
    }    
    i++; 
  }
  i++;
  if (!bandera) {     
    return bandera;
  } 
  bandera = 1;
  while ((comando[i] != '}' && comando[i] != '\0' && bandera)) {
    if (comando[i] == ',' 
               && (comando[i + 1] == ',' || comando[i + 1] == '}' 
                      || comando[i+1] == '\0')) {
      bandera = 0;     
    }    
    if ((isdigit(comando[i]) == 0) && comando[i] != ',' 
               &&comando[i] != '}' && comando[i] != '-') {       
      bandera = 0;   
    }      
    i++;  
  }  
  return bandera;
}

int compresion_assert(char comando[]) { 
  int i = 0, bandera = 0;
  while (comando[i] != '{' && comando[i] != '\0') {     
    if (comando[i] == '=') {         
      bandera = 1;    
    }     
    i++; 
  } 
  i++;
  if (!bandera) {     
    return bandera;
  }
  bandera = 0; 
  while (comando[i] != ':' && comando[i] != '\0') {       
    i++;
  }
  if (comando[i] == '\0') {
    return bandera;
  }
  i += 2;
  while ((isdigit(comando[i]) != 0) || comando[i] == '-') {
    i++;
  }
  if (comando[i] != ' ') {    
    return 0;  
  }
  i++;
  if (comando[i] != '<' || comando[i + 1] != '=') {
    return 0;
  } 
  i += 2;
  if (comando[i] != ' ') {    
    return 0;
  } 
  i++;
  while (comando[i] != ' ') {     
    i++;
  } 
  i++;  
  if (comando[i] != '<' || comando[i + 1] != '=') {     
    return 0;
  }
  i += 2;
  if (comando[i] != ' ') {
    return 0;  
  }  
  i++; 
  while (((isdigit(comando[i]) != 0) || comando[i] == '-') && !bandera) {     
    if (comando[i + 1] == '}') {        
      bandera = 1;     
    }    
    i++;
  }  
  return bandera;
}

int operaciones_dos_conj_assert(char comando[]) {
  int i = 0;  
  while (comando[i] != '=') {      
    i++;  
  }  
  if (comando[i - 1] != ' ' || comando[i + 1] != ' ') {      
    return 0;  
  }
  while (comando[i] != '|' && comando[i] != '&' && comando[i] != '-') {     
    i++;
  }
  if (comando[i - 1] != ' ' || comando[i + 1] != ' ') {    
    return 0;
  } 
  return 1;
}
 
int compl_assert(char comando[]) {   
  int i = 0;  
  while (comando[i] != '=') {    
    i++;
  }
  if (comando[i - 1] != ' ' || comando[i + 1] != ' ') {     
    return 0; 
  }
  while (comando[i] != '~') {
    i++;
  } 
  if (comando[i - 1] != ' ' || comando[i + 1] == ' ') {      
    return 0;  
  }  
  return 1;
}
 
void comando_aliasbyc(char comando[], char *aliasAyB[]) {   
  int i = 0, longA = 0, longB = 0, j = 0;  
  while (comando[i] != '=') {      
    i++;  
  }
  i += 2; 
  for (int j = i; comando[j] != ' '; j++) {     
    longA++;
  } 
  aliasAyB[0] = malloc(sizeof(char) * (longA + 1));
  while (comando[i + 1] != '|' && comando[i+1] != '-' 
              && comando[i + 1] != '&') {     
    aliasAyB[0][j] = comando[i];     
    i++;      
    j++;  
  }  
  aliasAyB[0][j] = '\0'; 
  i += 3;
  j = 0;
  for (int j = i; comando[j] != ' ' && comando[j] != '\0'; j++) {    
    longB++; 
  }  
  aliasAyB[1] = malloc(sizeof(char) * (longB + 1)); 
  while (comando[i] != ' ' && comando[i] != '\0') {      
    aliasAyB[1][j] = comando[i];    
    i++;    
    j++; 
  }   
  aliasAyB[1][j] = '\0';
}
 
char *comando_alias_compl(char comando[]) {
  int i = 0, longA = 0, j = 0;
  char *aliasA;
  while (comando[i] != '~') {   
    i++;
  }
  i++;
  for (int j = i; comando[j] != '\0' && comando[j] != ' '; j++) {     
    longA++; 
  }  
  aliasA = malloc(sizeof(char) * (longA + 1));
  while (comando[i] != '\0' && comando[i] != ' ') {     
    aliasA[j] = comando[i];     
    i++;      
    j++;
  }
  aliasA[j] = '\0';
  return aliasA;
}


 
 
