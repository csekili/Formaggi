sig Object{
	NE: set Object,
	SE: set Object,
	NW: set Object,
	SW: set Object,
}

fact SEoppNW{all nw: Object, se: Object |	se in nw.SE  <=> nw in se.NW }

fact SWoppNE{all sw: Object, ne: Object |    sw in ne.SW <=> ne in sw.NE }

fact NWexludes{
	all o:Object, nw:Object |
		nw in o.NW <=> nw not in o.SE
}


//fact conectedness{
//	all o: Object |
//		#o.NE + #o.SE + #o.NW + #o.SW > 0
//}

fact acyclic{
 	no o : Object | 
		o in o.^NE or 
		o in o.^SE or 
		o in o.^NW or 
		o in o.^SW
}

run {} for exactly 3 Object

