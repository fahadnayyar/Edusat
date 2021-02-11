default: edusat

edusat: edusat.cpp edusat.h options.cpp options.h
	g++ -g edusat.cpp options.cpp -o edusat

run:
	sh ./run_test.sh

clean:
		rm edusat