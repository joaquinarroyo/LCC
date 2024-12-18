# Usar make macc para compilar macc
# Usar make macc8 para compilar macc8
TARGET1 = macc
TARGET2 = macc8

# Compila y enlaza el archivo fuente seleccionado
$(TARGET1): $(TARGET1).c
	gcc $(CFLAGS) -o $(TARGET1) $(TARGET1).c $(LDLIBS)

# Compila y enlaza el archivo fuente seleccionado
$(TARGET2): $(TARGET2).c
	gcc $(CFLAGS) -o $(TARGET2) $(TARGET2).c $(LDLIBS)

# Define opciones de compilación y bibliotecas
CFLAGS += -Wall -pedantic
LDLIBS += -lgc

# Limpia los archivos generados
clean:
	rm -f macc macc8

.PHONY: clean all