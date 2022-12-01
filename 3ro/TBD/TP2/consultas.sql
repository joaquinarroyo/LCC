-- Integrantes
-- Arroyo Joaquin A-4294/3
-- Bolzan Francisco B-6159/1
-- Montoro Emiliano M-6653/2

USE `Inmobiliaria`;

/* Ejercicio 4 */
-- a)
SELECT DISTINCT p.nombre, p.apellido FROM Persona p, Propietario pr WHERE p.codigo = pr.codigo;

-- b)
SELECT codigo FROM Inmueble WHERE precio BETWEEN 600000 AND 700000;

-- c)
SELECT p.nombre, p.apellido FROM Persona p, Cliente c, PrefiereZona pz 
WHERE c.codigo = pz.codigo_cliente
AND p.codigo = c.codigo
AND pz.nombre_poblacion = 'Santa Fe'
AND pz.nombre_zona = 'Norte'
AND NOT EXISTS (SELECT * FROM PrefiereZona pz2 WHERE pz2.codigo_cliente = c.codigo
				AND pz2.nombre_poblacion <> 'Santa Fe'
				AND pz2.nombre_zona <> 'Norte');

-- d)
SELECT DISTINCT p.nombre, p.apellido FROM Persona p, Cliente c, Vendedor v 
WHERE v.codigo = c.vendedor 
	AND v.codigo = p.codigo
	AND c.codigo IN (SELECT c.codigo FROM PrefiereZona pz 
					 WHERE c.codigo = pz.codigo_cliente
						AND pz.nombre_poblacion = 'Rosario'
						AND pz.nombre_zona = 'Centro');
                                                              
-- e)
SELECT nombre_zona, COUNT(*), AVG(precio) FROM Inmueble 
GROUP BY nombre_zona, nombre_poblacion 
HAVING nombre_poblacion = 'Rosario';

-- f)
SELECT DISTINCT p.nombre, p.apellido FROM Persona p, Cliente c, PrefiereZona pz 
WHERE c.codigo = pz.codigo_cliente
	AND p.codigo = c.codigo
	AND pz.nombre_poblacion = 'Santa Fe'
GROUP BY p.codigo
HAVING COUNT(DISTINCT nombre_zona) = (SELECT COUNT(*) FROM Zona WHERE nombre_poblacion = 'Santa Fe');
                                                           
-- g)
SELECT COUNT(*), MONTH(aux.fecha_hora) 
FROM (SELECT * FROM Visitas 
WHERE YEAR(CAST(fecha_hora as DATE))=YEAR(now())) aux
GROUP BY MONTH(aux.fecha_hora) 
ORDER BY MONTH(aux.fecha_hora);
