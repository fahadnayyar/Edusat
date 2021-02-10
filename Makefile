default: edusat

edusat: edusat.cpp edusat.h
	g++ -g edusat.cpp -o edusat

run:
	sh ./test.sh

clean:
		rm edusat