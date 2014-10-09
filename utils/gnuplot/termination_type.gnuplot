# Run in GNUPlot with
# call "termination_type.gnuplot" /path/to/termination_counters.txt
set xlabel "Termination type"
set ylabel "Number of occurances"
set key off
set boxwidth 0.5
set grid ytics

# Prevent long labels from colliding by rotating lines
set xtics rotate by -45

plot "$0" using 2:xticlabels(1) with boxes fillstyle solid border -1
