PROBLEMA 6 IES:

########Alta_Animal########

context : Sistema::existeixPersona(nomP : String, poblaci� : String) : persona

pre :

post: if (Persona.allInstances()->exists(p | p.nom = nomP) Persona.allInstances()->exists(p | p.nom = nomP and p.poblaci� = poblaci� and result = p);
else Persona.allInstances()->exists(p | p.oclIsNew() and p.nom = nomP and p.poblaci� = poblaci� and result = p);


context: Sistema::altaAnimal(nom : String, sexe : TSexe, nomEsp�cie : String, persona : Persona) : animal

pre : Esp�cie.allInstances()->exists(e | e.nom = nomEsp�cie);

post: Animal.allInstances()->exists(a | a.oclIsNew() and a.nom = nom and a.sexe = sexe and a.Esp�cie.nom = nomEsp�cie and a.Persona = persona and result = a);


########Alta_Operaci�_Urgent########


########Consulta_Gossos_Perillosos_no_Esterilitzats########

context: Sistema::consultaGossosP(poblaci� : String) : Set(TupleType(nomG : String, nomProp : String, esVet : boolean));

pre: Persona.allInstances()->exists(p | p.poblaci� = poblaci� and p.animal->notEmpty())

body : let gossos : Set(Gos) =
		Gos.allInstances()->select(g | g.operaci�.motiu->select(m | m = "Esterilitzaci�")->size() = 0 and 
		g.agressiu = true and g.Persona.poblaci� = poblaci� and g.Tsexe = "mascle") 
	   in 
		gossos->collect(g | Tuple{nomG = g.nom, nomProp = g.Persona.nom, esVet = g.Persona.oclIsTypeOf(Veterinari)})




PROBLEMA 7 IES:

########Alta_inscripci�########

context : Sistema::altaInscripci�(dniP : String, nomT : String, avui : Date, avaPreu : TPreu)

pre : Persona.allInstances()->exists(p | p.dni = dniP) and
Taller.allInstances()->exists(t | t.nom = nomT and t.dataIni > avui)

post : Inscripci�.allInstances()->exists(i | i.oclIsNew() and i.taller.nom = nomT and i.participant.dni = dniP and
	if (i.taller.oclIsTypeOf(TallerDePagament))
		then i.oclIsTypeOf(Inscripci�DePagament) and i.oclAsType(Inscripci�DePagament).pagada = false and
		i.oclAsType(Inscripci�DePagament).avaluaci�Preu = avaPreu
		endif
		)


########Alta_reserva########

context: Sistema::altaReserva(dniO : String, nomT : String, data : Date, hora : Hora, codiS : String, duradaR : integer) : Reserva

pre : Organitzador.allInstances()->exists(o | o.dni = dniO) and
	  Taller.allInstances()->exists(t | t.nom = nomT) and
      Sala.allInstances()->exists(s | s.codi = codiS)

post : Reserva.allInstances()->exists(r | r.oclIsNew() and r.organitzador.dni = dniO and r.taller.nom = nomT and r.sala.codi = codiS and r.dataHora.data = data and r.dataHora.hora = hora and result = r)


context : Sistema::recursosUtilitzats(r : Reserva, codiR : String, tipusR : String)

pre :

post : if (Recurs.allInstances()->exists(r1 | r1.codi = codiR))
	   then Recurs.allInstances()->exists(rec | rec.reserva = r and rec.codi = codiR)
	   else (Recurs.allInstances()->exists(rec | rec.oclIsNew() and rec.codi = codiR and rec.tipusRec = tipusR and rec.reserva = r)
	   endif


########Consulta_Reserves_Exitoses########

context: Sistema::consultaResEx(nomT : String) : Set(TupleType(codiS: String, data: Date, hora: Hora, Bag(correus: String))

pre: TallerDePagament.allInstances()->exists(t | t.nom = nomT and t.inscripci�->count(i | i.oclIsTypeOf(Inscripci�DePagament) and i.oclAsType(Inscripci�DePagament).pagada = true and i.oclAsType(Inscripci�DePagament).avaluaci�Preu = TPreu::barat) > 2)

body: let res : Set(Reserva) =
		Reserva.allInstances()->select(r | r.valoraci�->count(v | v.puntuaci� = TPuntuaci�::5) > 5)
	  in
		res->collect(re | Tuple{codiS = re.sala.codi, data = re.dataHora.data, hora = re.dataHora.hora,  
			let cor : Bag(Partipant) =
			  Partipant.allInstances()->select(p | p.taller.nom = nomT)
			in
			  cor->collect(c | c.correuE = correus)
				
	  })




C2:


#########AltaPlatIndividual##########1

context: Sistema::AltaPlatIndividual (codiP : String, nomP : String, receptaPI : String): PlatIndividual

pre: 

post: PlatIndividual.allInstances()->exists(pi | pi.oclIsNew() and pi.codi = codiP and pi.nom = nomP and pi.recepta = receptaPI and pi.nombreMen�s = 0 and result = pi)


context: Sistema::AssigIngredients (pi : PlatIndividual, nomI : String, quantitatI : Decimal, unitatI : String)

pre: Ingredient.allInstances()->exists(i | i.nom = nomI)

post: Mesura.allInstances()->exists(m | m.oclIsNew() and m.quantitat = quantitatI and m.unitatDeMesura = unitatI and m.ingredient.nom = nomI and m.platIndividual = pi) and pi.ingredient.nom->includes(nomI)



#########Confecci�Men�Diari##########1

context: Sistema::Confecci�Men�Diari (preuM : Decimal, nomM : String, nomR : String, dat : Date, codiM : String, nomPlats : Set(String))

pre: Restaurant.allInstances()->exists(r | r.nom = nomR and r.platIndividual->size() <= 100)

post: if (not (Men�.allInstances() @pre ->exists( m | m.nom = nomM)))
	  then Men�.allInstances()->exists(m | m.oclIsNew() and m.nom = nomM and m.codi = codiM and m.platIndividual.nom->includes(nomPlats))
	  endif
	  and Men�DiariOfert.allInstances()->exists(mdo | mdo.oclIsNew() and mdo.preu = preuM and mdo.men�.nom = nomM and mdo.restaurant.nom = nomR and mdo.data = dat)
	       

#########ConsultaPlatsOferts##########1

context: Sistema::ConsultaPlatsOferts (dataIni : Date, dataFi : Date, nomR : String):Set(TupleType(codiPI : String, nomI : Set(String)))

pre: Men�DiariOfert.allInstances()->select(mdo | mdo.restaurant.nom = nomR and mdo.preu < 10)->size() > 9

body: let platsI : Set(PlatIndividual) =
		Men�DiariOfert.allInstances()->select(mdo | mdo.restaurant.nom = nomR and mdo.data >= dataIni and mdo.data <= dataFi)
	  in
		result = platsI->collect(pi | Tuple{codiPI = pi.codi and nomI = pi.ingredient.nom})
	


#########AltaPersonaPoders##########2

context: Sistema::AltaPersona (nomP : String, paisP : String, esHeroi : Boolean, esMalvat : Boolean):Persona

pre: Malvat.allInstances()->select(m | m.poderDePersona.oclIsTypeOf(Adquirit))->size() > 9

post:Persona.allInstances()->exists(p | p.oclIsNew() and p.nom = nomP and p.pais = paisP and
	 if (esHeroi) 
	 then p.oclIsTypeOf(Heroi)
	 endif
	 if (esMalvat)
	 then p.oclIsTypeOf(Malvat)
	 endif
	 and result = p)


context: Sistema::AssigPoders (p : Persona, nomPoder : String, desc : String, esAdquirit : Boolean, esEnsenyant : Boolean, nomPers : String, nomL : String)

pre: 

post: if (not (Poder.allInstances()@pre->exists(po | po.nom = nomPoder)))
	  then Poder.allInstances()->exists(po | po.oclIsNew() and po.nom = nomPoder and po.descripci� = desc)
	  endif
	  and p.poder.nom->includes(nomPoder) and 
	  PoderDePersona.allInstances()->exists(pdp | pdp.oclIsNew() and 
	  if (esAdquirit)
	  then pdp.oclIsTypeOf(Adquirit) and pdp.lloc.nom->includes(nomL) and 
		if(esEnsenyant)
		then pdp.ensenyant.nom->includes(nomPers)
		endif
	  else pdp.oclIsTypeOf(Innat)
	  endif)


#########AltaCrisisMalvat##########2

context: Sistema::AltaCrisisMalvat (nomM : String, nomL : String, dataIni : Date, dataFi : Date):Crisi

pre: Malvat.allInstances()->exists(m | m.nom = nomM) and
	 Lloc.allInstances()->exists(l | l.nom = nomL)

post: Crisi.allInstances()->exists(c | c.oclIsNew() and c.malvat.nom = nomM and c.lloc.nom = nomL and c.inici.data = dataIni and c.data_fi = dataFi and result = c)


context: Sistema::HeroiParticpant (c : Crisi, nomH : String)

pre: Heroi.allInstances()->exists(h | h.nom = nomH)

post: c.heroi.nom->includes(nomH)

##########LlocsPerillosos#########2

context : Sistema::ConsultaLlocsPerillosos(dataIni : Date, dataFi : Date):Set(TupleType(nomL : String, nomM : Set(String)))

pre : Persona.allInstances()->exists(p | p.oclIsTypeOf(Malvat) and p.oclIsTypeOf(Heroi) and
	  p.poderDePersona.oclIsTypeOf(Adquirit) and p.poderDePersona.oclAsType(Adquirit).lloc.nom = "Barcelona")

body : let llocP : Set(Lloc) =
		Lloc.allInstances()->select(l | l.crisi.inici.data <= dataIni and l.crisi.data_fi >= dataFiand l.crisi.heroi->size() < 3)->size() > 5
	   in
		result = llocP->collect(l | Tuple{ nomL = l.nom and nomM = l.adquirit.ensenyant.oclAsTypeOf(Malvat).nom })


##########AltaSuscriptor#########3

context: Sistema::AltaSubscriptor (usuariS : String, ibanS : String, volPremium : Boolean):Subscriptor

pre: 

post: Subscriptor.allInstances()->exists(s | s.oclIsNew() and s.usuari = usuariS and s.iban = ibanS and s.dataAlta = today() and 
	  if (volPremium)
	  then s.oclIsTypeOf(SubscriptorPremium)
	  endif 
	  and result = s)


context: Sistema::AltaPerfil (s : Subscriptor, nomP : String, esAdult : Boolean)

pre: 

post: Perfil.allInstances()->exists(p | p.oclIsNew() and p.nom = nomP and p.adult = esAdult and p.subscriptor = s)

##########VisionatContingut########3

context: Sistema::VisionatContingut (usuariS : String, nomP : String, t�tolC: String, dataUV : Date, punt : TPuntuaci�, coment : String)

pre: Subscriptor.allInstances()->exists(s | s.usuari = usuariS and s.perfil.nom = nomP and s.dataAlta < dataUV) and
	 Contingut.allInstances()->exists(c | c.t�tol = t�tolC)

post: if (not (ContingutVisionat.allInstances()@pre->exists(cv | cv.contingut.t�tol = t�tolC and cv.perfil.nom = nomP and cv.perfil.subscriptor.usuari = usuariS)))
	  then ContingutVisionat.allInstances()->exists(cv | cv.oclIsNew() and cv.data�ltimVisionat = dataUV, cv.puntuaci� = punt and cv.comentaris = coment and cv.perfil.nom = nomP and cv.perfil.subscriptor.usuari = usuariS and cv.contingut.t�tol = t�tolC)
	  else  ContingutVisionat.allInstances()->exists(cv | cv.data�ltimVisionat = dataUV, cv.puntuaci� = punt and cv.comentaris = coment and cv.perfil.nom = nomP and cv.perfil.subscriptor.usuari = usuariS and cv.contingut.t�tol = t�tolC)



########CategoriesExitoses#######3

context: Sistema::CategoriesExitoses (dataIni : Date, dataFi : Date):Set(TupleType(t�tolC : String, nomCat : Set(String), preuD : Float))

pre: ContingutDescarregat.allInstances()->select(cd | cd.data.date >= dataIni and cd.data.date <= dataFi)->size() > 2

body: let cont : Set(ContingutPremium) =
		ContingutPremium.allInstances()->select(cp | cp.contingutDescarregat->select (cd | cd.data.date >= dataIni and cd.data.date <= dataFi)->size() > 5)
	  in
		result = cont->collect(cp | Tuple {t�tolC = cp.t�tol, nomCat = cp.categoria.nom, preuD = cp.preu*cp.contingutDescarregat->size()})


########EstablirCalendari########4

context: Sistema::AltaPartit (nomL : String, nomV : String):Partit

pre: Equip.allInstances()->exists(e | e.nom = nomL) and
	 Equip.allInstances()->exists(e | e.nom = nomV)

post: Partit.allInstances()->exists(p | p.oclIsNew() and p.local.nom = nomL and p.visitant.nom = nomV and result = p)


context: Sistema::AssigJornada (p : Partit, numJ : Integer)

pre: Jornada.allInstances()->exists(j | j.numero = numJ)

post: p.jornada.numero->includes(numJ)


########ConvocarJugadors#######4

context: Sistema::ConvJugadors (nomL : String, nomV : String, nomJ : String)

pre: Equip.allInstances()->exists(e | e.nom = nomL) and
	 Equip.allInstances()->exists(e | e.nom = nomV) and 
	 Jugador.allInstances()->exists(j | j.nom = nomJ)

post: Partit.allInstances()->exists(p | p.local.nom = nomL and p.visitant.nom = nomV and p.convocat.nom->includes(nomJ))


#######EnregEsdeveniment#######4

context: Sistema::EnregEsdeveniment (nomL : String, nomV : String, min : Integer, tipusE: TipusEsdev, nomJ : String, nomJS : String)

pre: Equip.allInstances()->exists(e | e.nom = nomL) and
	 Equip.allInstances()->exists(e | e.nom = nomV) and 
	 Jugador.allInstances()->exists(j | j.nom = nomJ)
	 if(tipusE = TipusEsdev::canvi) 
	 then Jugador.allInstances()->exists(j | j.nom = nomJS)
	 endif

post: Esdeveniment.allInstances()->exists(e | e.oclIsNew() and e.partit.local.nom = nomL and e.partit.visitant.nom = nomV and e.minut.minut = min and e.tipus = tipusE and e.jugador.nom = nomJ and
	  if (tipusE = TipusEsdev::canvi)
	  then e.oclIsTypeOf(Canvi) and e.oclAsType(Canvi).substitut.nom = nomJS
	  endif)

#######ConsultaGolejado######4

context: Sistema::ConsultaGolejador():Set(TupleTyple(nomJ : string, numP : Integer))

pre: 

body: let jug : Set(Jugador) =
		Jugador.allInstances()->select(j | j.esdeveniment.tipus = TipusEsdev::gol->size() > 10 and j.esdeveniment.tipus = TipusEsdev::tarjeta_vermella->size() = 0)
	  in
		result = jug->collect(j | Tuple{nomJ = j.nom, numP = (j.partitJugat.esdeveniment.tipus = TipusEsdev::gol -> size())})





