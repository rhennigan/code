#!/bin/sh
math -noprompt -run '<<JavaGraphics`;Export["data.png",ListPointPlot3D[ToExpression[Import["data.dat","TEXT"]],ImageSize->800]];Quit[];';
cygstart data.png