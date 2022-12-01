-- Integrantes
-- Arroyo Joaquin A-4294/3
-- Bolzan Francisco B-6159/1
-- Montoro Emiliano M-6653/2

CREATE DATABASE IF NOT EXISTS Biblioteca;

USE Biblioteca;

DROP TABLE IF EXISTS Es_escrito;
DROP TABLE IF EXISTS Libro;
DROP TABLE IF EXISTS Autor;

/* Ejercicio 1 */
CREATE TABLE Autor(
  id int (11) AUTO_INCREMENT,				  
  nombre VARCHAR(20) NOT NULL,
  apellido VARCHAR(20) NOT NULL,
  nacionalidad VARCHAR(20),
  residencia VARCHAR(20),
  PRIMARY KEY (id)
);

CREATE TABLE Libro(
  isbn VARCHAR(13) NOT NULL, -- ISBN-10		  
  titulo VARCHAR(20) NOT NULL,
  editorial VARCHAR(20) NOT NULL,
  precio DOUBLE NOT NULL,
  PRIMARY KEY (isbn)
);

CREATE TABLE Es_escrito(
  libro VARCHAR(13),				  
  autor int(11),
  anio YEAR,
  PRIMARY KEY (libro, autor),
  FOREIGN KEY (libro) REFERENCES Libro (isbn) ON DELETE CASCADE ON UPDATE CASCADE, 
  -- Suponemos que el comportamiento es cascade ya que el ej 3d pide borrar todos los 
  -- libros publicados en 1998
  FOREIGN KEY (autor) REFERENCES Autor (id) ON DELETE CASCADE ON UPDATE CASCADE
  -- Suponemos el mismo comportamiento para los autores
);

/* Ejercicio 2 */
CREATE INDEX apellido_index on Autor(apellido);
CREATE INDEX titulo_index on Libro(titulo);

/* Ejercicio 3 */
-- a)
INSERT INTO Autor VALUES (DEFAULT, 'Emiliano', 'Montoro', 'Estadounidense', 'Detroit');
INSERT INTO Autor VALUES (DEFAULT, 'Francisco', 'Bolzan', 'Argentino', 'Buenos Aires');
INSERT INTO Autor VALUES (DEFAULT, 'Joaquin', 'Arroyo', 'Argentino', 'San Lorenzo');
INSERT INTO Autor VALUES (DEFAULT, 'Abelardo', 'Castillo', 'Argentino', 'Miami');

INSERT INTO Libro VALUES ('0-684-84328-5', 'El Principito', 'Listocalisto', 3999.99);
INSERT INTO Libro VALUES ('2-732-91204-2', 'El Tunel', 'CGEDITORIAL', 4399.99);
INSERT INTO Libro VALUES ('9-966-84562-1', 'Farenheit 451', 'La Ley', 2799.50);

INSERT INTO Es_escrito VALUES ('0-684-84328-5', (SELECT id FROM Autor WHERE apellido = 'Montoro'), '2012');
INSERT INTO Es_escrito VALUES ('2-732-91204-2', (SELECT id FROM Autor WHERE apellido = 'Bolzan'), '1998');
INSERT INTO Es_escrito VALUES ('9-966-84562-1', (SELECT id FROM Autor WHERE apellido = 'Arroyo'), '2013');
INSERT INTO Es_escrito VALUES ('9-966-84562-1', (SELECT id FROM Autor WHERE apellido = 'Bolzan'), '2013');

-- b)
UPDATE Autor SET residencia = 'Buenos Aires' WHERE nombre = 'Abelardo' AND apellido = 'Castillo';

-- c)
UPDATE Libro l, Autor a, Es_escrito e SET l.precio = l.precio * 1.20 
									  WHERE (l.isbn = e.isbn AND a.id = e.id)
                                      AND a.nacionalidad not like 'argentin%'
                                      AND l.precio <= 200;

UPDATE Libro l, Autor a, Es_escrito e SET l.precio = l.precio * 1.10 
									  WHERE (l.isbn = e.isbn AND a.id = e.id)
                                      AND a.nacionalidad not like 'argentin%'
                                      AND l.precio > 200;

-- d)
DELETE FROM Libro WHERE anio = YEAR('1998');

-- e)
SELECT * FROM Libro l WHERE l.isbn IN 
			(SELECT e.isbn FROM Es_escrito e GROUP BY e.isbn HAVING COUNT(e.id) = 2);









