str = Import["data/graph_data.txt"];
edges = ToExpression["{"<>StringTake[str, StringLength[str]-1]<>"}"];
g = Graph[edges,
		  GraphLayout->{"LayeredDigraphEmbedding", "Orientation"->Top},
		  ImageSize->{1920, 1920/3},
		  AspectRatio->1/3,
		  VertexShapeFunction->({Black, AbsolutePointSize[4], Point[#]}&),
		  EdgeShapeFunction->({Gray, AbsoluteThickness[1], Line[#1]}&),
		  DirectedEdges->False
	]
Export["graph.png", g];
