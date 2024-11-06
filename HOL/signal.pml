#define QSZ 1

int free_buffers = 0 // tokens for how many OS buffers have yet to be filled
int got, packet
bool sysexit = false
bool device_off = false
chan ring = [QSZ] of {int}
chan sysq = [QSZ] of {int}

active proctype system(){
int data
provide:
    do
    :: d_step { (free_buffers < QSZ) -> free_buffers++ }
    :: else -> goto wait
    od
wait:
    do
    :: d_step {
       sysq?data -> printf("system recv: packet %d\n", data);
                    packet = data }
    :: atomic {
       (len(sysq) == 0) ->
       if
       :: !sysexit -> goto provide
       :: else -> goto exit
       fi }
    :: d_step {
       !sysexit && device_off && len(sysq) == 0 ->
       printf("system: received device exit, cleaning up...\n")
       sysexit = true }
    od
exit:
    if
    :: (len(sysq) != 0) -> goto wait
    fi
    printf("system: stop driver\n")
}

active proctype driver(){
    int data
    do
    :: atomic { ring?data -> printf("driver data %d\n", data)
       if
       :: (free_buffers > 0) -> sysq!data; free_buffers--
       fi
       }
    :: atomic { sysexit && !ring?[_] -> goto exit }
    od
exit:
    printf("driver: system stopped, exiting...\n")
}

active proctype device(){
    int iter = QSZ
    do
    :: d_step { (iter > 0) -> got = iter + 100; ring!got; iter-- }
    :: else -> goto off
    od
off: skip
    d_step { device_off = 1; printf("device: off\n") }
}

ltl s1 { always (packet != 100) }
ltl l1 { always (got ==101 -> eventually (packet == 101)) } // +weak fairness
ltl s2 { always (_nr_pr ==0 -> (len(sysq) == 0)) }
