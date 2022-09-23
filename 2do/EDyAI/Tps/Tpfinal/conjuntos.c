#include "conjuntos.h"

//Auxiliares
    
/**
 * Inserta el dato recibido en la lista enlazada que representa 
 * a un conjunto.
 */ 
SList clist_agregar(SList lista, void *dato, int tipo) {
  CNodo *nuevoNodo = malloc(sizeof(CNodo));
  nuevoNodo->dato = dato;
  nuevoNodo->tipo = tipo;
  nuevoNodo->sig = NULL;
  if (lista->conjunto == NULL) {
    lista->conjunto = nuevoNodo;
    lista->ultimo = nuevoNodo;
    return lista;
  }
  CList nodo = lista->ultimo;
  lista->ultimo = nuevoNodo;
  nodo->sig = nuevoNodo;
  return lista;
}

/**
 * Destruye la lista enlazada recibida.
 */ 
void clist_destruir(CList lista) {
  CNodo * nodoAEliminar;
  while (lista != NULL) {
    nodoAEliminar = lista;
    lista = lista->sig;
    free(nodoAEliminar->dato);
    free(nodoAEliminar);
  }
}

int conjuntos_assert(SList conjuntoB, SList conjuntoC, 
                          char *aliasB, char *aliasC) {
  int bandera = 1;
  if (conjuntoB == NULL && conjuntoC == NULL) {
    printf("    ");
    printf("No hay ningun conjunto relacionado con ambos alias\n");
    bandera = 0;
  } else {
      if (conjuntoB == NULL) {
        printf("    ");
        printf("No hay ningun conjunto relacionado con el alias %s\n", 
                aliasB);
        bandera = 0;
      }
      if (conjuntoC == NULL) {
        printf("    ");
        printf("No hay ningun conjunto relacionado con el alias %s\n", 
                aliasC);
        bandera = 0;
      }
  }
  free(aliasB);
  free(aliasC);
  return bandera;
}
 
SList conj_lista(SList lista, int datos[], int tipo, int cantidad) {
  lista = malloc(sizeof(SNodo));
  lista->conjunto = NULL;
  if (tipo == INTERVALO) {
    Intervalo intervalo = malloc(sizeof(Interval));
    if (datos[0] > datos[1]) {
      Intervalo intervaloB = malloc(sizeof(Interval));
      intervalo->extIzq = INT_MIN;
      intervalo->extDer = datos[1];
      intervaloB->extIzq = datos[0];
      intervaloB->extDer = INT_MAX;
      lista = clist_agregar(lista, intervalo, tipo);
      lista = clist_agregar(lista, intervaloB, tipo);
    } else {
        intervalo->extIzq = datos[0];
        intervalo->extDer = datos[1];
        lista = clist_agregar(lista, intervalo, tipo);
      }
  } else { 
      if(tipo == NUMERO){
        if (cantidad != 0) {
          int extDer, extIzq, bandera = 0;
          Intervalo intervalo;
          for (int i = 0; i < cantidad; i++) {
            if (i + 1 != cantidad && datos[i] + 1 == datos[i + 1]) {
              if (!bandera) {
                intervalo = malloc(sizeof(Interval)); 
                extIzq = datos[i]; 
                bandera = 1; 
              } 
              extDer = datos[i + 1]; 
            } else {  
                if (bandera) {    
                  intervalo->extIzq = extIzq;  
                  intervalo->extDer = extDer; 
                  lista = clist_agregar(lista, intervalo, INTERVALO);   
                  bandera = 0;   
                } else {
                    int *dato = malloc(sizeof(int));
                    dato[0] = datos[i];  
                    lista = clist_agregar(lista, dato, tipo);
                }      
            }  
          } 
        }
      } else {
          lista = clist_agregar(lista, NULL, tipo);
      }
  } 
  return lista;
}

void insertion_sort(int conjunto[], int cantidad) {
  int pivot, j;
  for (int i = 1; i < cantidad; i++) {
    pivot = conjunto[i];
    j = i - 1;
    while (j >= 0 && conjunto[j] > pivot) {
      conjunto[j + 1] = conjunto[j];
      j = j - 1;
    }
    conjunto[j + 1] = pivot;
  }
}

int eliminar_dupl(int conjunto[], int cantidad) {
  int k;
  for (int i = 0; i < cantidad; i++) {
    for (int j = i + 1; j < cantidad; j++) {
      if (conjunto[i] == conjunto[j]) {
        k = j;
        while (k < cantidad) {
          conjunto[k] = conjunto[k + 1];
          k++;
        }
        cantidad--;
        j--;
      }
    } 
  }
  return cantidad;
}

//Principales

TablaConjuntos *tablaconj_crear(unsigned capacidad, FuncionHash hash) {
  TablaConjuntos *tabla = malloc(sizeof(TablaConjuntos));
  tabla->hash = hash;
  tabla->capacidad = capacidad;
  tabla->tabla = malloc(sizeof(CasillaConjunto) * capacidad);
  for (unsigned idx = 0; idx < capacidad; ++idx) {
    tabla->tabla[idx].conjuntos = NULL;
  }
  return tabla;
}

void tablaconj_insertar(TablaConjuntos *tabla, void *clave, SList lista) {
  unsigned idx = tabla->hash(clave);
  idx = idx % tabla->capacidad;
  if (tabla->tabla[idx].conjuntos == NULL) {
    tabla->tabla[idx].conjuntos = lista;
    tabla->tabla[idx].conjuntos->sig = NULL;
  } else {
      if (!strcmp(tabla->tabla[idx].conjuntos->alias, lista->alias)) {
        clist_destruir(tabla->tabla[idx].conjuntos->conjunto);
        tabla->tabla[idx].conjuntos->conjunto = lista->conjunto;
        free(lista->alias);
        free(lista);
      } else {
          SList nodo = tabla->tabla[idx].conjuntos;
          while (nodo->sig != NULL && 
                    (strcmp(nodo->alias, lista->alias) != 0)) {
            nodo = nodo->sig;
          }
          if (!strcmp(nodo->alias, lista->alias)) {
            clist_destruir(nodo->conjunto);
            nodo->conjunto = lista->conjunto;
            free(lista->alias);
            free(lista);
          } else {
              nodo->sig = lista;
              nodo->sig->sig = NULL;
          }
      }
  }
}

SList tablaconj_buscar(TablaConjuntos *tabla, void *clave, char *alias) {
  unsigned idx = tabla->hash(clave);
  idx = idx % tabla->capacidad;
  SList nodo = tabla->tabla[idx].conjuntos;
  if (tabla->tabla[idx].conjuntos != NULL) {
    while ((strcmp(nodo->alias, alias) != 0) && nodo->sig != NULL) {
      nodo = nodo->sig;
    }
    if (strcmp(nodo->alias, alias) != 0) {
      return NULL;
    } else {
        return nodo;
    }
  } else {
      return NULL;
  }
}
 
SList tablaconj_union(SList conjB, SList conjC) {
  SList Union = malloc(sizeof(SNodo));
  Union->conjunto = NULL;
  CList nodoB = conjB->conjunto;
  CList nodoC = conjC->conjunto;
  if (nodoB->tipo == VACIO) {
    while (nodoC != NULL) {
      if (nodoC->tipo == INTERVALO) {
        Interval intervaloC = *((Interval *) nodoC->dato);
        Intervalo intervalo = malloc(sizeof(Interval));
        intervalo->extIzq = intervaloC.extIzq; 
        intervalo->extDer = intervaloC.extDer; 
        Union = clist_agregar(Union, intervalo, INTERVALO);
      } else { 
          int datoC = *((int *) nodoC->dato); 
          int *dato = malloc(sizeof(int));  
          dato[0] = datoC; 
          Union = clist_agregar(Union, dato, NUMERO);
      } 
      nodoC = nodoC->sig;
    }  
    return Union;
  }
  if (nodoC->tipo == VACIO) {
    while (nodoB != NULL) {
      if (nodoB->tipo == INTERVALO) {  
        Interval intervaloB = *((Interval *) nodoB->dato);
        Intervalo intervalo = malloc(sizeof(Interval));
        intervalo->extIzq = intervaloB.extIzq;
        intervalo->extDer = intervaloB.extDer;
        Union = clist_agregar(Union, intervalo, INTERVALO);
      } else {  
          int datoB = *((int *) nodoB->dato);  
          int *dato = malloc(sizeof(int));
          dato[0] = datoB; 
          Union = clist_agregar(Union, dato, NUMERO); 
      } 
      nodoB = nodoB->sig;
    } 
    return Union;
  }
  Interval intervaloUnion;
  int bandera = 0, entra = 1;
  while (nodoB != NULL && nodoC != NULL) {
    if (nodoB->tipo == INTERVALO) {
      Interval intervaloB = *((Interval *) nodoB->dato);
      if (nodoC->tipo == INTERVALO) {
        Interval intervaloC = *((Interval *) nodoC->dato); 
        if (bandera == 1) {   
          if (intervaloUnion.extDer + 1 == intervaloB.extIzq 
            || intervaloUnion.extDer + 1 == intervaloC.extIzq) {    
            entra = 0;   
          }   
        }  
        if (intervaloC.extDer + 1 == intervaloB.extIzq 
           || intervaloB.extDer + 1 == intervaloC.extIzq) {  
          entra = 0; 
        } 
        if ((intervaloB.extDer < intervaloC.extIzq 
            ||intervaloC.extDer < intervaloB.extIzq) && entra) { 
          if (intervaloB.extDer < intervaloC.extIzq) {   
            if (bandera == 1) {     
              Intervalo intervalo = malloc(sizeof(Interval));     
              intervalo->extIzq = intervaloUnion.extIzq;     
              intervalo->extDer = intervaloUnion.extDer;     
              Union = clist_agregar(Union, intervalo, INTERVALO);    
              bandera = 0;
            } else { 
                Intervalo intervalo = malloc(sizeof(Interval));   
                intervalo->extIzq = intervaloB.extIzq;   
                  intervalo->extDer = intervaloB.extDer;    
              Union = clist_agregar(Union, intervalo, INTERVALO);
            }
            nodoB = nodoB->sig;
          } else {
              if (bandera == 1) { 
                Intervalo intervalo = malloc(sizeof(Interval));  
                intervalo->extIzq = intervaloUnion.extIzq;    
                intervalo->extDer = intervaloUnion.extDer;     
                Union = clist_agregar(Union, intervalo, INTERVALO);
                bandera = 0;
              } else {     
                  Intervalo intervalo = malloc(sizeof(Interval));    
                  intervalo->extIzq = intervaloC.extIzq;    
                  intervalo->extDer = intervaloC.extDer;   
                  Union = clist_agregar(Union, intervalo, INTERVALO);   
              }    
              nodoC = nodoC->sig;  
          }  
        } else {    
            if ((intervaloB.extIzq < intervaloC.extIzq) && bandera == 0) {     
              intervaloUnion.extIzq = intervaloB.extIzq;    
            } else {   
                if (bandera == 0) {    
                intervaloUnion.extIzq = intervaloC.extIzq;   
                }   
            } 
            if (intervaloB.extDer > intervaloC.extDer) {   
              intervaloUnion.extDer = intervaloB.extDer;    
              nodoC = nodoC->sig;   
            } else {    
                intervaloUnion.extDer = intervaloC.extDer;    
                nodoB = nodoB->sig;    
            }  
            bandera = 1;   
        }  
        entra = 1; 
      } else { 
          int datoC = *((int *) nodoC->dato); 
          if (bandera == 1) {   
            if (intervaloUnion.extDer + 1 == intervaloB.extIzq 
                ||intervaloUnion.extDer + 1 == datoC) {   
              entra = 0;  
            }  
          }  
          if (datoC + 1 == intervaloB.extIzq
                || intervaloB.extDer + 1 == datoC) {  
            entra = 0; 
          }  
          if ((datoC < intervaloB.extIzq || datoC > intervaloB.extDer) 
                &&entra) {   
            if (datoC < intervaloB.extIzq) {    
              if (bandera == 1) {    
                Intervalo intervalo = malloc(sizeof(Interval));    
                intervalo->extIzq = intervaloUnion.extIzq;     
                intervalo->extDer = intervaloUnion.extDer;    
                Union = clist_agregar(Union, intervalo, INTERVALO);    
                bandera = 0;   
              } else {   
                  int *dato = malloc(sizeof(int));   
                  dato[0] = datoC;
                  Union = clist_agregar(Union, dato, NUMERO);  
              } 
              nodoC = nodoC->sig;   
            } else {    
                if (bandera == 1) {     
                  Intervalo intervalo = malloc(sizeof(Interval));    
                  intervalo->extIzq = intervaloUnion.extIzq;      
                  intervalo->extDer = intervaloUnion.extDer;      
                  Union = clist_agregar(Union, intervalo, INTERVALO);      
                  bandera = 0;     
                } else {      
                    Intervalo intervalo = malloc(sizeof(Interval));     
                    intervalo->extIzq = intervaloB.extIzq;     
                    intervalo->extDer = intervaloB.extDer;     
                    Union = clist_agregar(Union, intervalo, INTERVALO);    
                }    
              nodoB = nodoB->sig;   
            }  
          } else {   
              if ((intervaloB.extIzq < datoC) && bandera == 0) {     
              intervaloUnion.extIzq = intervaloB.extIzq;    
              } else {    
                  if (bandera == 0) {      
                    intervaloUnion.extIzq = datoC;  
                  }    
              }    
              if (intervaloB.extDer > datoC) {   
                intervaloUnion.extDer = intervaloB.extDer;     
                nodoC = nodoC->sig;    
              } else {    
                  intervaloUnion.extDer = datoC;     
                  nodoB = nodoB->sig;   
              }         
              bandera = 1;   
          }   
          entra = 1;  
        } 
    } else {  
        int datoB = *((int *) nodoB->dato);  
          if (nodoC->tipo == INTERVALO) {   
            Interval intervaloC = *((Interval *) nodoC->dato);   
            if (bandera == 1) {    
              if (intervaloUnion.extDer + 1 == datoB 
                  ||intervaloUnion.extDer + 1 == intervaloC.extIzq) {     
                entra = 0;    
              }   
            }  
            if (intervaloC.extDer + 1 == datoB
                || datoB + 1 == intervaloC.extIzq) {   
              entra = 0;   
            }   
            if ((datoB < intervaloC.extIzq || datoB > intervaloC.extDer) 
                &&entra) {   
              if (datoB < intervaloC.extIzq) {     
                if (bandera == 1) {     
                  Intervalo intervalo = malloc(sizeof(Interval));   
                  intervalo->extIzq = intervaloUnion.extIzq;      
                  intervalo->extDer = intervaloUnion.extDer;      
                  Union = clist_agregar(Union, intervalo, INTERVALO);      
                  bandera = 0;     
                } else {      
                    int *dato = malloc(sizeof(int));      
                    dato[0] = datoB;      
                    Union = clist_agregar(Union, dato, NUMERO);      
                } 
                nodoB = nodoB->sig;  
              } else {    
                  if (bandera == 1) {      
                    Intervalo intervalo = malloc(sizeof(Interval));     
                    intervalo->extIzq = intervaloUnion.extIzq;     
                    intervalo->extDer = intervaloUnion.extDer;     
                    Union = clist_agregar(Union, intervalo, INTERVALO);     
                    bandera = 0;     
                  } else {      
                      Intervalo intervalo = malloc(sizeof(Interval));     
                      intervalo->extIzq = intervaloC.extIzq;      
                      intervalo->extDer = intervaloC.extDer;      
                      Union = clist_agregar(Union, intervalo, INTERVALO);     
                  }     
                  nodoC = nodoC->sig;    
              }  
            } else {    
                if ((datoB < intervaloC.extIzq) && bandera == 0) {     
                intervaloUnion.extIzq = datoB;   
                } else {     
                    if (bandera == 0) {      
                      intervaloUnion.extIzq = intervaloC.extIzq;     
                    }    
                }    
                if (datoB > intervaloC.extDer) {    
                  intervaloUnion.extDer = datoB;     
                  nodoC = nodoC->sig;   
                } else {    
                    intervaloUnion.extDer = intervaloC.extDer;     
                    nodoB = nodoB->sig;   
                }    
                bandera = 1; 
            }  
            entra = 1; 
          } else { 
              int datoC = *((int *) nodoC->dato);  
              if (bandera == 1) {    
                if (intervaloUnion.extDer + 1 == datoC 
                    ||intervaloUnion.extDer + 1 == datoB) {    
                  entra = 0;   
                }   
              }
              if (datoC + 1 == datoB || datoB + 1 == datoC) {  
                entra = 0;   
              } 
              if ((datoC < datoB || datoB < datoC) && entra) {
                if (datoC < datoB) {   
                  if (bandera == 1) {     
                    Intervalo intervalo = malloc(sizeof(Interval));
                    intervalo->extIzq = intervaloUnion.extIzq; 
                    intervalo->extDer = intervaloUnion.extDer;    
                    Union = clist_agregar(Union, intervalo, INTERVALO);    
                    bandera = 0;   
                  } else {     
                      int *dato = malloc(sizeof(int));    
                      dato[0] = datoC;    
                      Union = clist_agregar(Union, dato, NUMERO);    
                  } 
                  nodoC = nodoC->sig;
                } else {
                    if (bandera == 1) {  
                      Intervalo intervalo = malloc(sizeof(Interval));  
                      intervalo->extIzq = intervaloUnion.extIzq;    
                      intervalo->extDer = intervaloUnion.extDer;    
                      Union = clist_agregar(Union, intervalo, INTERVALO);   
                      bandera = 0;  
                    } else {    
                        int *dato = malloc(sizeof(int));
                        dato[0] = datoB;   
                        Union = clist_agregar(Union, dato, NUMERO);  
                    } 
                    nodoB = nodoB->sig;
                  } 
              } else {
                  if (datoC == datoB && bandera == 0) {     
                    int *dato = malloc(sizeof(int));    
                    dato[0] = datoB;    
                    Union = clist_agregar(Union, dato, NUMERO);    
                    nodoB = nodoB->sig;    
                    nodoC = nodoC->sig;   
                  } else {    
                      if ((datoB < datoC) && bandera == 0) {
                        intervaloUnion.extIzq = datoB;    
                      } else {     
                          if (bandera == 0) {      
                            intervaloUnion.extIzq = datoC;     
                          }   
                      }
                      if (datoB > datoC) {
                        intervaloUnion.extDer = datoB;
                        nodoC = nodoC->sig;
                      } else {
                          intervaloUnion.extDer = datoC;
                          nodoB = nodoB->sig;
                      }
                      bandera = 1;
                    }
                }
              entra = 1;
          }
    }
  }
  if (bandera == 1) {
    Intervalo intervalo = malloc(sizeof(Interval));
    intervalo->extIzq = intervaloUnion.extIzq;
    intervalo->extDer = intervaloUnion.extDer;
    Union = clist_agregar(Union, intervalo, INTERVALO);
    if (intervaloUnion.extDer != INT_MAX) {
      bandera = 0;
      if (nodoB != NULL) {
        nodoB = nodoB->sig;
      } else {
          if (nodoC != NULL) {
          nodoC = nodoC->sig;
        }
      }
    }
  }
  if (nodoB == NULL && bandera == 0) {
    while (nodoC != NULL) {
      if (nodoC->tipo == INTERVALO) {
        Interval intervaloC = *((Interval *) nodoC->dato);
        Intervalo intervalo = malloc(sizeof(Interval));
        intervalo->extIzq = intervaloC.extIzq;
        intervalo->extDer = intervaloC.extDer;
        Union = clist_agregar(Union, intervalo, INTERVALO);
      } else {
          int datoC = *((int *) nodoC->dato);
          int *dato = malloc(sizeof(int));
          dato[0] = datoC;
          Union = clist_agregar(Union, dato, NUMERO);
      }
      nodoC = nodoC->sig;
    } 
  } else {
      if (bandera == 0) {
        if (nodoB != NULL) {
          while (nodoB != NULL) {
            if (nodoB->tipo == INTERVALO) {
              Interval intervaloB = *((Interval *) nodoB->dato);
              Intervalo intervalo = malloc(sizeof(Interval));
              intervalo->extIzq = intervaloB.extIzq;
              intervalo->extDer = intervaloB.extDer;
              Union = clist_agregar(Union, intervalo, INTERVALO);
            } else {
                int datoB = *((int *) nodoB->dato);
                int *dato = malloc(sizeof(int));
                dato[0] = datoB;
                Union = clist_agregar(Union, dato, NUMERO);
            } 
            nodoB = nodoB->sig;
          } 
        }
      }
  } 
  return Union;
}

SList tablaconj_interseccion(SList conjB, SList conjC) {
  SList interseccion = malloc(sizeof(SNodo));
  interseccion->conjunto = NULL;
  CList nodoB = conjB->conjunto;
  CList nodoC = conjC->conjunto;
  if (nodoB->tipo == VACIO || nodoC->tipo == VACIO) {
    interseccion = clist_agregar(interseccion, NULL, VACIO);
    return interseccion;
  }
  while (nodoB != NULL && nodoC != NULL) {
    if (nodoB->tipo == INTERVALO) {
      Interval intervaloB = *((Interval *) nodoB->dato);
      if (nodoC->tipo == INTERVALO) {
        Interval intervaloC = *((Interval *) nodoC->dato); 
        if (intervaloB.extDer < intervaloC.extIzq 
                ||intervaloC.extDer < intervaloB.extIzq) { 
          if (intervaloB.extDer < intervaloC.extIzq) {
            nodoB = nodoB->sig;
          } else {
              nodoC = nodoC->sig;
          }
        } else {
            if (intervaloC.extIzq <= intervaloB.extDer) {
              Intervalo intervaloInt = malloc(sizeof(Interval));
              if (intervaloC.extIzq < intervaloB.extIzq) {
                intervaloInt->extIzq = intervaloB.extIzq;
              } else {
                  intervaloInt->extIzq = intervaloC.extIzq;
              }
              if (intervaloB.extDer < intervaloC.extDer) {
                intervaloInt->extDer = intervaloB.extDer;
                nodoB = nodoB->sig; 
              } else {  
                  intervaloInt->extDer = intervaloC.extDer;  
                  nodoC = nodoC->sig; 
              }
              if (intervaloInt->extIzq == intervaloInt->extDer) {
                int *dato = malloc(sizeof(int));
                dato[0] = intervaloInt->extDer;
                interseccion = clist_agregar(interseccion, dato, NUMERO);
                free(intervaloInt);
              } else {
                  interseccion =
                  clist_agregar(interseccion, intervaloInt, INTERVALO);
              }
          } else {
              Intervalo intervaloInt = malloc(sizeof(Interval));
              if (intervaloC.extIzq < intervaloB.extIzq) {
                intervaloInt->extIzq = intervaloB.extIzq;
              } else {
                  intervaloInt->extIzq = intervaloC.extIzq;
              }
              if (intervaloC.extDer < intervaloB.extDer) {
                intervaloInt->extDer = intervaloC.extDer;
                nodoC = nodoC->sig;
              } else {
                  intervaloInt->extDer = intervaloB.extDer;
                  nodoB = nodoB->sig;
              }
              if (intervaloInt->extIzq == intervaloInt->extDer) {
                int *dato = malloc(sizeof(int));
                dato[0] = intervaloInt->extDer;
                interseccion = clist_agregar(interseccion, dato, NUMERO);
                free(intervaloInt);
              } else {
                  interseccion =
                  clist_agregar(interseccion, intervaloInt, INTERVALO);
              }
          }
        }
      } else {
          int datoC = *((int *) nodoC->dato);
          if (datoC < intervaloB.extIzq || datoC > intervaloB.extDer) {
            if (datoC < intervaloB.extIzq) {
              nodoC = nodoC->sig;
            } else {
                nodoB = nodoB->sig;
            }
          } else {
              int *dato = malloc(sizeof(int));
              dato[0] = datoC;
              interseccion = clist_agregar(interseccion, dato, NUMERO);
              if (datoC != intervaloB.extDer) {
                nodoC = nodoC->sig;
              } else {
                  nodoB = nodoB->sig;
                  nodoC = nodoC->sig;
              }
          }
      }
    } else {
        int datoB = *((int *) nodoB->dato);
        if (nodoC->tipo == INTERVALO) {
          Interval intervaloC = *((Interval *) nodoC->dato);
          if (datoB < intervaloC.extIzq || datoB > intervaloC.extDer) {
            if (datoB < intervaloC.extIzq) {
              nodoB = nodoB->sig;
            } else {
                nodoC = nodoC->sig;
            }
          } else {
              int *dato = malloc(sizeof(int));
              dato[0] = datoB;
              interseccion = clist_agregar(interseccion, dato, NUMERO);
              if (datoB != intervaloC.extDer) {
                nodoB = nodoB->sig;
              } else {
                  nodoB = nodoB->sig;
                  nodoC = nodoC->sig;
              }   
          }
        } else {
            int datoC = *((int *) nodoC->dato);
            if (datoB < datoC || datoB > datoC) {
              if (datoB < datoC) {
                nodoB = nodoB->sig;
              } else {
                  nodoC = nodoC->sig;
              }
            } else {
                int *dato = malloc(sizeof(int));
                dato[0] = datoB;
                interseccion = clist_agregar(interseccion, dato, NUMERO);
                nodoB = nodoB->sig;
                nodoC = nodoC->sig;
            } 
        } 
    } 
  } 
  if (interseccion->conjunto == NULL) {
    interseccion = clist_agregar(interseccion, NULL, VACIO);
  }
  return interseccion;
}

SList tablaconj_resta(SList conjB, SList conjC) {
  SList complementoConjC = tablaconj_compl(conjC);
  SList resta = tablaconj_interseccion(conjB, complementoConjC);
  clist_destruir(complementoConjC->conjunto);
  free(complementoConjC);
  if (resta->conjunto == NULL) {
    resta = clist_agregar(resta, NULL, VACIO);
  }
  return resta;
}

SList tablaconj_compl(SList conjuntoB) {
  SList complemento = malloc(sizeof(SNodo));
  complemento->conjunto = NULL;
  CList nodo = conjuntoB->conjunto;
  int extDer;
  int *dato;
  if (nodo->tipo == VACIO) {
    Intervalo intervaloCompl = malloc(sizeof(Interval));
    intervaloCompl->extIzq = INT_MIN;
    intervaloCompl->extDer = INT_MAX;
    complemento = clist_agregar(complemento, intervaloCompl, INTERVALO);
    return complemento;
  }
  if (nodo->tipo == INTERVALO) {
    Interval intervalo = *((Interval *) (nodo->dato));
    if (intervalo.extIzq != INT_MIN) {
      Intervalo intervaloCompl = malloc(sizeof(Interval));
      intervaloCompl->extIzq = INT_MIN;
      intervaloCompl->extDer = intervalo.extIzq - 1;
      extDer = intervalo.extDer;
      if (intervaloCompl->extIzq == intervaloCompl->extDer) {
        dato = malloc(sizeof(int));
        dato[0] = intervaloCompl->extDer;
        complemento = clist_agregar(complemento, dato, NUMERO);
        free(intervaloCompl);
      } else {
          if (intervaloCompl->extIzq != intervaloCompl->extDer + 1) {
            complemento =
            clist_agregar(complemento, intervaloCompl, INTERVALO);
          }
      }
    } else {
        extDer = intervalo.extDer;
    }
  } else {
      int numero = *((int *) nodo->dato);
      if (numero != INT_MIN) { 
        Intervalo intervaloCompl = malloc(sizeof(Interval));
        intervaloCompl->extIzq = INT_MIN;
        intervaloCompl->extDer = numero - 1;
        extDer = numero;
        if (intervaloCompl->extIzq == intervaloCompl->extDer) {
          dato = malloc(sizeof(int));
          dato[0] = intervaloCompl->extDer;
          complemento = clist_agregar(complemento, dato, NUMERO);
          free(intervaloCompl);
        } else {
            if (intervaloCompl->extIzq != intervaloCompl->extDer + 1) {
              complemento =
              clist_agregar(complemento, intervaloCompl, INTERVALO);
            }
        } 
      } else {
          extDer = numero;
      }
  }
  nodo = nodo->sig;
  while (nodo != NULL) {
    if (nodo->tipo == INTERVALO) {
      Interval intervalo = *((Interval *) nodo->dato);
      Intervalo intervaloCompl = malloc(sizeof(Interval));
      intervaloCompl->extIzq = extDer + 1;
      intervaloCompl->extDer = intervalo.extIzq - 1;
      extDer = intervalo.extDer;
      if (intervaloCompl->extIzq == intervaloCompl->extDer) {
        dato = malloc(sizeof(int));
        dato[0] = intervaloCompl->extDer;
        complemento = clist_agregar(complemento, dato, NUMERO);
        free(intervaloCompl);
      } else {
          if (intervaloCompl->extIzq != intervaloCompl->extDer + 1) {
            complemento =
            clist_agregar(complemento, intervaloCompl, INTERVALO);
          }
      }
    } else {
        int numero = *((int *) nodo->dato);
        Intervalo intervaloCompl = malloc(sizeof(Interval));
        intervaloCompl->extIzq = extDer + 1;
        intervaloCompl->extDer = numero - 1;
        extDer = numero;
        if (intervaloCompl->extIzq == intervaloCompl->extDer) {
          dato = malloc(sizeof(int));
          dato[0] = intervaloCompl->extDer;
          complemento = clist_agregar(complemento, dato, NUMERO);
          free(intervaloCompl);
        } else {
            if (intervaloCompl->extIzq != intervaloCompl->extDer + 1) {
              complemento =
              clist_agregar(complemento, intervaloCompl, INTERVALO);
            }
        } 
    }
    nodo = nodo->sig;
  }
  if (extDer != INT_MAX) {
    Intervalo intervaloCompl = malloc(sizeof(Interval));
    intervaloCompl->extIzq = extDer + 1;
    intervaloCompl->extDer = INT_MAX;
    if (intervaloCompl->extIzq == intervaloCompl->extDer) {
      dato = malloc(sizeof(int));
      dato[0] = intervaloCompl->extDer;
      complemento = clist_agregar(complemento, dato, NUMERO);
      free(intervaloCompl);
    } else {
        if (intervaloCompl->extIzq != intervaloCompl->extDer + 1) {
          complemento = clist_agregar(complemento, intervaloCompl, INTERVALO);
        }
    }
  }
  if (complemento->conjunto == NULL) {
    complemento = clist_agregar(complemento, NULL, VACIO);
  }
  return complemento;
}

void tablaconj_imprimir(TablaConjuntos *tabla, void *clave, char *alias,             
                            FuncionVisitante visit) {
  SList lista = tablaconj_buscar(tabla, clave, alias);
  if (lista != NULL) {
    if (lista->conjunto->tipo != VACIO) {
      visit(lista->conjunto);
    } else {
        printf("Conjunto vacio\n");
    }
  } else {
      printf("No hay ningun conjunto relacionado con el alias %s\n", alias);
  }
}

void tablaconj_destruir(TablaConjuntos * tabla) {
  for (unsigned idx = 0; idx < tabla->capacidad; idx++) {
    SNodo * nodoAEliminar;
    while (tabla->tabla[idx].conjuntos != NULL) {
      nodoAEliminar = tabla->tabla[idx].conjuntos;
      tabla->tabla[idx].conjuntos = tabla->tabla[idx].conjuntos->sig;
      clist_destruir(nodoAEliminar->conjunto);
      free(nodoAEliminar->alias);
      free(nodoAEliminar);
    }
  }
  free(tabla->tabla);
  free(tabla);
}
