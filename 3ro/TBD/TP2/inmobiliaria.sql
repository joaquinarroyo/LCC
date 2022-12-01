CREATE DATABASE IF NOT EXISTS `jarroyo_Inmobiliaria`;

USE `jarroyo_Inmobiliaria`;

DROP TABLE IF EXISTS `Poblacion`;
DROP TABLE IF EXISTS `Zona`;
DROP TABLE IF EXISTS `Inmueble`;
DROP TABLE IF EXISTS `Limita`;
DROP TABLE IF EXISTS `Persona`;
DROP TABLE IF EXISTS `Vendedor`;
DROP TABLE IF EXISTS `Cliente`;
DROP TABLE IF EXISTS `Propietario`;
DROP TABLE IF EXISTS `PoseeInmueble`;
DROP TABLE IF EXISTS `PrefiereZona`;
DROP TABLE IF EXISTS `Visitas`;

CREATE TABLE `Poblacion`(
  `nombre_poblacion`  VARCHAR(20)   NOT NULL,
  `n_habitantes`      INT UNSIGNED  NULL,
  PRIMARY KEY (`nombre_poblacion`)
) ENGINE=InnoDB DEFAULT CHARSET=latin1;

CREATE TABLE `Zona`(
  `nombre_poblacion`  VARCHAR(20) NOT NULL REFERENCES `Poblacion`(`nombre_poblacion`) ON DELETE CASCADE ON UPDATE CASCADE,
  `nombre_zona`       VARCHAR(20) NOT NULL,
  PRIMARY KEY (`nombre_zona`, `nombre_poblacion`)
) ENGINE=InnoDB DEFAULT CHARSET=latin1;

CREATE TABLE `Inmueble` (
  `codigo`            VARCHAR(10)   NOT NULL,
  `precio`            INT UNSIGNED  NULL,
  `direccion`         VARCHAR(45)   NOT NULL,
  `superficie`        INT UNSIGNED  NULL,
  `nombre_poblacion`  VARCHAR(20)   NOT NULL REFERENCES `Zona`(`nombre_poblacion` ) ON DELETE CASCADE ON UPDATE CASCADE,
  `nombre_zona`       VARCHAR(20)   NOT NULL REFERENCES `Zona`(`nombre_zona`)       ON DELETE CASCADE ON UPDATE CASCADE,
  PRIMARY KEY (`codigo`)
) ENGINE=InnoDB DEFAULT CHARSET=latin1;

CREATE TABLE `Limita` (
  `nombre_poblacion`    VARCHAR(20) NOT NULL REFERENCES `Poblacion`(`nombre_poblacion` )  ON DELETE CASCADE ON UPDATE CASCADE,
  `nombre_zona`         VARCHAR(20) NOT NULL REFERENCES `Zona`(`nombre_zona`)             ON DELETE CASCADE ON UPDATE CASCADE,
  `nombre_poblacion_2`  VARCHAR(20) NOT NULL REFERENCES `Poblacion`(`nombre_poblacion` )  ON DELETE CASCADE ON UPDATE CASCADE,
  `nombre_zona_2`       VARCHAR(20) NOT NULL REFERENCES `Zona`(`nombre_zona`)             ON DELETE CASCADE ON UPDATE CASCADE,
  PRIMARY KEY (`nombre_poblacion`, `nombre_zona`, `nombre_poblacion_2`, `nombre_zona_2`)
) ENGINE=InnoDB DEFAULT CHARSET=latin1;

CREATE TABLE `Persona` (
  `codigo`    INT UNSIGNED  NOT NULL,
  `nombre`    VARCHAR(20)   NOT NULL,
  `apellido`  VARCHAR(20)   NOT NULL,
  `domicilio` VARCHAR(45)   NULL,
  `telefono`  INT UNSIGNED  NULL,
  PRIMARY KEY (`codigo`)
) ENGINE=InnoDB DEFAULT CHARSET=latin1;

CREATE TABLE `Vendedor` (
  `codigo`  INT UNSIGNED  NOT NULL REFERENCES `Persona`(`codigo` ) ON DELETE CASCADE ON UPDATE CASCADE,
  `cuil`    VARCHAR(20)   NULL,
  `sueldo`  INT UNSIGNED  NULL,
  PRIMARY KEY (`codigo`)
) ENGINE=InnoDB DEFAULT CHARSET=latin1;

CREATE TABLE `Cliente` (
  `codigo`    INT UNSIGNED NOT NULL REFERENCES `Persona`(`codigo` )   ON DELETE CASCADE ON UPDATE CASCADE,
  `vendedor`  INT UNSIGNED NOT NULL REFERENCES `Vendedor`(`codigo` )  ON DELETE CASCADE ON UPDATE CASCADE,
  PRIMARY KEY (`codigo`)
) ENGINE=InnoDB DEFAULT CHARSET=latin1;

CREATE TABLE `Propietario` (
  `codigo`  INT UNSIGNED NOT NULL REFERENCES `Persona`(`codigo` ) ON DELETE CASCADE ON UPDATE CASCADE,
  `dni`     INT UNSIGNED NULL,
  PRIMARY KEY (`codigo` )
) ENGINE=InnoDB DEFAULT CHARSET=latin1;

CREATE TABLE `PoseeInmueble` (
  `codigo_propietario`  INT UNSIGNED  NOT NULL REFERENCES `Propietario`(`codigo` )  ON DELETE CASCADE ON UPDATE CASCADE,
  `codigo_inmueble`     VARCHAR(10)   NOT NULL REFERENCES `Inmueble`(`codigo` )     ON DELETE CASCADE ON UPDATE CASCADE,
  PRIMARY KEY (`codigo_propietario`, `codigo_inmueble`)
) ENGINE=InnoDB DEFAULT CHARSET=latin1;

CREATE TABLE `PrefiereZona` (
  `codigo_cliente`    INT UNSIGNED  NOT NULL REFERENCES `Cliente`(`codigo` )        ON DELETE CASCADE ON UPDATE CASCADE,
  `nombre_poblacion`  VARCHAR(20)   NOT NULL REFERENCES `Zona`(`nombre_poblacion`)  ON DELETE CASCADE ON UPDATE CASCADE,
  `nombre_zona`       VARCHAR(20)   NOT NULL REFERENCES `Zona`(`nombre_zona`)       ON DELETE CASCADE ON UPDATE CASCADE,
  PRIMARY KEY (`codigo_cliente`, `nombre_poblacion`, `nombre_zona`)
) ENGINE=InnoDB DEFAULT CHARSET=latin1;

CREATE TABLE `Visitas` (
  `codigo_cliente`    INT UNSIGNED  NOT NULL REFERENCES `Cliente`(`codigo` )  ON DELETE CASCADE ON UPDATE CASCADE,
  `codigo_inmueble`   VARCHAR(10)   NOT NULL REFERENCES `Inmueble`(`codigo` ) ON DELETE CASCADE ON UPDATE CASCADE,
  `fecha_hora`        DATETIME      NOT NULL,
  PRIMARY KEY (`codigo_inmueble`, `fecha_hora`)
) ENGINE=InnoDB DEFAULT CHARSET=latin1;

INSERT INTO `Poblacion` VALUES('Rosario', 1500000);
INSERT INTO `Poblacion` VALUES('Casilda', 14000);
INSERT INTO `Poblacion` VALUES('Santa Fe', 500000);
INSERT INTO `Poblacion` VALUES('San Lorenzo', 400000);

INSERT INTO `Zona` VALUES('Rosario', 'Norte');
INSERT INTO `Zona` VALUES('Rosario', 'Sur');
INSERT INTO `Zona` VALUES('Rosario', 'Centro');
INSERT INTO `Zona` VALUES('Rosario', 'Oeste');
INSERT INTO `Zona` VALUES('Rosario', 'Este');
INSERT INTO `Zona` VALUES('Santa Fe', 'Norte');
INSERT INTO `Zona` VALUES('Santa Fe', 'Sur');
INSERT INTO `Zona` VALUES('Santa Fe', 'Centro');
INSERT INTO `Zona` VALUES('Casilda', 'Este');
INSERT INTO `Zona` VALUES('Casilda', 'Oeste');
INSERT INTO `Zona` VALUES('San Lorenzo', 'Norte');
INSERT INTO `Zona` VALUES('San Lorenzo', 'Sur');
INSERT INTO `Zona` VALUES('San Lorenzo', 'Centro');

INSERT INTO `Inmueble` VALUES('Ros0001', 200000, 'Sarmiento 234', 80, 'Rosario','Centro');
INSERT INTO `Inmueble` VALUES('Ros0002', 3000000, 'Mitre 134', 90, 'Rosario','Centro');
INSERT INTO `Inmueble` VALUES('Ros0003', 600000, 'Rioja 344', 60, 'Rosario','Centro');
INSERT INTO `Inmueble` VALUES('Ros0004', 900000, 'Cordoba 344', 92, 'Rosario','Sur');
INSERT INTO `Inmueble` VALUES('Ros0005', 110000, 'Santa Fe 344', 102, 'Rosario','Sur');
INSERT INTO `Inmueble` VALUES('Ros0006', 700000, 'San Lorenzo 344', 52, 'Rosario','Sur');
INSERT INTO `Inmueble` VALUES('Ros0007', 820000, 'Alberdi 3344', 93, 'Rosario','Norte');
INSERT INTO `Inmueble` VALUES('Ros0008', 830000, 'Rondeau 4044', 44, 'Rosario','Norte');
INSERT INTO `Inmueble` VALUES('Ros0009', 640000, 'Mendoza 5344', 92, 'Rosario','Oeste');
INSERT INTO `Inmueble` VALUES('Ros0010', 650000, 'Rioja 2344', 110, 'Rosario','Oeste');
INSERT INTO `Inmueble` VALUES('Ros0011', 660000, 'Mendoza 2344', 64, 'Rosario','Oeste');
INSERT INTO `Inmueble` VALUES('Cas0001', 670000, 'Mitre 111', 250, 'Casilda','Este');
INSERT INTO `Inmueble` VALUES('Cas0002', 680000, 'San Martin 222', 90, 'Casilda','Oeste');
INSERT INTO `Inmueble` VALUES('Stf0001', 690000, 'San Martin 1234', 89, 'Santa Fe','Centro');
INSERT INTO `Inmueble` VALUES('Stf0002', 710000, 'San Martin 1345', 91, 'Santa Fe','Centro');
INSERT INTO `Inmueble` VALUES('Stf0003', 810000, 'San Martin 1456', 99, 'Santa Fe','Centro');
INSERT INTO `Inmueble` VALUES('Stf0004', 611000, 'Mitre 46', 99, 'Santa Fe','Norte');
INSERT INTO `Inmueble` VALUES('Stf0005', 1000000, 'Mitre 4446', 99, 'Santa Fe','Sur');
INSERT INTO `Inmueble` VALUES('Slr0001', 1000000, 'Maipu 46', 109, 'San Lorenzo','Sur');

INSERT INTO `Limita` VALUES('Rosario', 'Oeste', 'Rosario', 'Centro');
INSERT INTO `Limita` VALUES('Rosario', 'Sur', 'Rosario', 'Centro');
INSERT INTO `Limita` VALUES('Rosario', 'Norte', 'Rosario', 'Centro');
INSERT INTO `Limita` VALUES('Santa Fe', 'Norte', 'Santa Fe', 'Centro');
INSERT INTO `Limita` VALUES('Santa Fe', 'Sur', 'Santa Fe', 'Centro');
INSERT INTO `Limita` VALUES('San Lorenzo', 'Norte', 'San Lorenzo', 'Centro');
INSERT INTO `Limita` VALUES('San Lorenzo', 'Sur', 'San Lorenzo', 'Centro');
INSERT INTO `Limita` VALUES('Casilda', 'Este', 'Casilda', 'Oeste');

INSERT INTO `Persona` VALUES(1001, 'Roberto', 'Planta', 'Sarmiento 236, Rosario', 4304931);
INSERT INTO `Persona` VALUES(1002, 'Rogelio', 'Aguas', 'Avellaneda 2436, Rosario', 4304932);
INSERT INTO `Persona` VALUES(1003, 'Juan', 'Rodriguez', 'Mitre 45, Rosario', 4304933);
INSERT INTO `Persona` VALUES(1004, 'Juana', 'Lopez', 'San Martin 246, Rosario', 4304934);
INSERT INTO `Persona` VALUES(1005, 'Mirta', 'Gonzalez', 'Sarmiento 4236, Rosario', 4304935);
INSERT INTO `Persona` VALUES(1006, 'Laura', 'Perez', 'Corrientes 4236, Santa Fe', 445935);
INSERT INTO `Persona` VALUES(1007, 'Luis', 'Salazar', 'Moreno 236, Casilda', 455935);
INSERT INTO `Persona` VALUES(1008, 'Maria', 'Salazar', 'Moreno 236, Casilda', 455935);

INSERT INTO `Persona` VALUES(1011, 'Ana', 'Zarantonelli', 'Sarmiento 123, Rosario', 4555001);
INSERT INTO `Persona` VALUES(1012, 'Belen', 'Yani', 'Avellaneda 234, Rosario', 4555002);
INSERT INTO `Persona` VALUES(1013, 'Carlos', 'Xuan', 'Roca 345, San Lorenzo', 4555003);
INSERT INTO `Persona` VALUES(1014, 'Dario', 'Watson', 'Mitre 456, Casilda', 4555004);
INSERT INTO `Persona` VALUES(1015, 'Emilio', 'Visconti', 'Urquiza 567, Rosario', 4555005);
INSERT INTO `Persona` VALUES(1016, 'Facundo', 'Uriarte', 'Alvear 678, Rosario', 4555006);
INSERT INTO `Persona` VALUES(1017, 'Gabriela', 'Troncoso', 'Belgrano 789, Santa Fe', 4555007);
INSERT INTO `Persona` VALUES(1018, 'Hugo', 'Sosa', 'Saavedra 890, Rosario', 4555008);

INSERT INTO `Vendedor` VALUES(1004, '21-12777999-2', 10000);
INSERT INTO `Vendedor` VALUES(1005, '21-13777999-2', 10000);
INSERT INTO `Vendedor` VALUES(1006, '21-14777999-2', 10000);

INSERT INTO `Cliente` VALUES(1011, 1004);
INSERT INTO `Cliente` VALUES(1012, 1004);
INSERT INTO `Cliente` VALUES(1013, 1004);
INSERT INTO `Cliente` VALUES(1014, 1004);
INSERT INTO `Cliente` VALUES(1015, 1005);
INSERT INTO `Cliente` VALUES(1016, 1005);
INSERT INTO `Cliente` VALUES(1017, 1006);
INSERT INTO `Cliente` VALUES(1018, 1006);
INSERT INTO `Cliente` VALUES(1005, 1006);
INSERT INTO `Cliente` VALUES(1001, 1005);

INSERT INTO `PrefiereZona` VALUES(1012, 'Rosario', 'Centro');
INSERT INTO `PrefiereZona` VALUES(1013, 'Rosario', 'Centro');
INSERT INTO `PrefiereZona` VALUES(1014, 'Casilda', 'Oeste');
INSERT INTO `PrefiereZona` VALUES(1014, 'Casilda', 'Este');
INSERT INTO `PrefiereZona` VALUES(1015, 'Santa Fe', 'Sur');
INSERT INTO `PrefiereZona` VALUES(1015, 'Santa Fe', 'Norte');
INSERT INTO `PrefiereZona` VALUES(1015, 'Santa Fe', 'Centro');
INSERT INTO `PrefiereZona` VALUES(1016, 'Santa Fe','Norte');
INSERT INTO `PrefiereZona` VALUES(1017, 'Rosario', 'Centro');
INSERT INTO `PrefiereZona` VALUES(1017, 'Rosario', 'Sur');
INSERT INTO `PrefiereZona` VALUES(1017, 'Rosario', 'Norte');
INSERT INTO `PrefiereZona` VALUES(1017, 'Rosario', 'Oeste');
INSERT INTO `PrefiereZona` VALUES(1018, 'Rosario', 'Centro');
INSERT INTO `PrefiereZona` VALUES(1005, 'San Lorenzo','Sur');
INSERT INTO `PrefiereZona` VALUES(1001, 'Casilda', 'Oeste');

INSERT INTO `Propietario` VALUES(1002, 8777999);
INSERT INTO `Propietario` VALUES(1003, 9777999);
INSERT INTO `Propietario` VALUES(1004, 10777999);
INSERT INTO `Propietario` VALUES(1007, 20777999);
INSERT INTO `Propietario` VALUES(1008, 20778000);

INSERT INTO `PoseeInmueble` VALUES(1003, 'Ros0001');
INSERT INTO `PoseeInmueble` VALUES(1003, 'Ros0002');
INSERT INTO `PoseeInmueble` VALUES(1002, 'Ros0003');
INSERT INTO `PoseeInmueble` VALUES(1002, 'Ros0004');
INSERT INTO `PoseeInmueble` VALUES(1002, 'Ros0005');
INSERT INTO `PoseeInmueble` VALUES(1002, 'Ros0006');
INSERT INTO `PoseeInmueble` VALUES(1002, 'Ros0007');
INSERT INTO `PoseeInmueble` VALUES(1002, 'Ros0008');
INSERT INTO `PoseeInmueble` VALUES(1002, 'Ros0009');
INSERT INTO `PoseeInmueble` VALUES(1002, 'Ros0010');
INSERT INTO `PoseeInmueble` VALUES(1002, 'Ros0011');
INSERT INTO `PoseeInmueble` VALUES(1007, 'Cas0001');
INSERT INTO `PoseeInmueble` VALUES(1007, 'Cas0002');
INSERT INTO `PoseeInmueble` VALUES(1007, 'Stf0001');
INSERT INTO `PoseeInmueble` VALUES(1007, 'Stf0002');
INSERT INTO `PoseeInmueble` VALUES(1007, 'Stf0003');
INSERT INTO `PoseeInmueble` VALUES(1007, 'Stf0004');
INSERT INTO `PoseeInmueble` VALUES(1008, 'Stf0004');
INSERT INTO `PoseeInmueble` VALUES(1007, 'Stf0005');
INSERT INTO `PoseeInmueble` VALUES(1008, 'Stf0005');
INSERT INTO `PoseeInmueble` VALUES(1008, 'Slr0001');

INSERT INTO `Visitas` VALUES(1011, 'Slr0001', '2022-10-29 10:00:00');
INSERT INTO `Visitas` VALUES(1012, 'Ros0001', '2022-10-29 10:00:00');
INSERT INTO `Visitas` VALUES(1011, 'Slr0001', '2022-10-28 10:00:00');
INSERT INTO `Visitas` VALUES(1012, 'Ros0001', '2022-10-28 10:00:00');
INSERT INTO `Visitas` VALUES(1015, 'Ros0001', '2022-10-15 10:00:00');
INSERT INTO `Visitas` VALUES(1016, 'Ros0002', '2022-10-15 10:00:00');
INSERT INTO `Visitas` VALUES(1013, 'Ros0001', '2022-09-01 10:00:00');
INSERT INTO `Visitas` VALUES(1013, 'Ros0002', '2022-09-02 10:00:00');
INSERT INTO `Visitas` VALUES(1013, 'Ros0003', '2022-09-03 10:00:00');
INSERT INTO `Visitas` VALUES(1001, 'Cas0002', '2022-09-01 10:00:00');
INSERT INTO `Visitas` VALUES(1018, 'Stf0001', '2022-11-06 10:00:00');
INSERT INTO `Visitas` VALUES(1018, 'Stf0001', '2022-11-08 10:00:00');
