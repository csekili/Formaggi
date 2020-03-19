sig Object{
	dirNE: set Object,
	dirSE: set Object,
	dirNW: set Object,
	dirSW: set Object,

	indirN: set Object,
	indirS: set Object,
	indirW: set Object,
	indirE: set Object,
}

fact SEoppNW{all nw: Object, se: Object |	se in nw.dirSE  <=> nw in se.dirNW }

fact SWoppNE{all sw: Object, ne: Object |    sw in ne.dirSW <=> ne in sw.dirNE }

fact north{
	indirN = ^(dirNE + dirNW)
}

fact east{
	indirE = ^(dirNE + dirSE)
}

fact south{
	indirS = ^(dirSE + dirSW)
}

fact west{
	indirW = ^(dirNW + dirSW)
}

fact acyclic{
	all o: Object |
		o not in o.^indirN and
		o not in o.^indirS and
		o not in o.^indirW and
		o not in o.^indirE
}



//fact NWexludes{
//	all o:Object, nw:Object |
//		nw in o.NW <=> nw not in o.SE
//}


fact conectedness{
	all disjoint o , o1: Object |	
		(o in o1.indirE or o in o1.indirW ) and
		(o in o1.indirS or o in o1.indirN )
}

run {} for exactly 5 Object
run {} for exactly 10 Object
run {} for exactly 15 Object
run {} for exactly 20 Object
run {} for exactly 25 Object
run {} for exactly 30 Object
run {} for exactly 40 Object
run {} for exactly 50 Object
