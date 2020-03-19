sig Object{
	NE: set Object,
	SE: set Object,
	NW: set Object,
	SW: set Object,
}

fact SEoppNW{all nw: Object, se: Object |	se in nw.SE  <=> nw in se.NW }

fact SWoppNE{all sw: Object, ne: Object |    sw in ne.SW <=> ne in sw.NE }

//fact NWexludes{
//	all o:Object, nw:Object |
//		nw in o.NW <=> nw not in o.SE
//}


//fact conectedness{
//	all o: Object |
//		#o.NE + #o.SE + #o.NW + #o.SW > 0
//}

fact acyclic{
 	all o : Object | 
		o not in o.^NE and
		o not in o.^SE and
		o not in o.^NW and 
		o not in o.^SW
}

pred derivedNS [ n: Object, s: Object] {
	(n+s) in Object
	(s in n.SE and n in s.NW) and not (s in n.SW and n in s.NE) or 
	(s in n.SW and n in s.NE) and not (s in n.SE and n in s.NW)
}

pred derivedEW( e: Object, w: Object){
	(w + e) in Object
	(w in e.NW and e in w.SE) and not (w in e.SW and e in w.NE)  or
	 (w in e.SW and e in w.NE) and not (w in e.NW and e in w.SE)
}

run {} for exactly 2 Object

