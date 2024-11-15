#define QSZ 1 // a bigger queue is not necessary to demonstrate signal issues

//int free_buffers = 0 // tokens for how many OS buffers have yet to be filled
int got              // got is set by the device when generating a packet
int processed        // processed is set by the system after receiving it
chan ring = [QSZ] of {int} // device -> driver
chan sysq = [QSZ] of {int} // driver -> OS

// modelling signals using async queues to avoid ABA problems with flags
chan device_io = [1] of {bool}
chan driver_signal = [1] of {bool}
bool need_signal = true // whether the system should signal the driver on i/o

// various states of stuff exiting
bool sysexit = false
bool device_off = false

active proctype system() {
    bool sig
    int data
provide:
    do
//    :: atomic { (free_buffers < QSZ) -> free_buffers++ }
    :: else -> goto wait
    od
wait:
    do
    :: atomic { device_io?sig
       if
       :: need_signal -> driver_signal!true
       fi }
    :: atomic { sysq?data
    -> printf("system recv: packet %d\n", data);
       processed = data }
    :: atomic { len(sysq) == 0 && !device_io?[_]
    -> if
       :: !sysexit -> goto provide
       :: else -> goto exit
       fi }
    :: d_step { !sysexit && device_off && len(sysq) == 0 && !device_io?[_]
    -> printf("system: received device exit, cleaning up...\n")
       sysexit = true }
    od
exit:
    // without this additional check, packets can be dropped between
    // 1) OS signalling the driver to exit
    // 2) driver receiving the signal and exiting
    atomic {
    if
    :: (len(sysq) != 0) -> goto wait
    fi
    printf("system: stop driver\n") }
}

active proctype driver() {
    bool sig
    int data
sleep:
    do
    :: atomic { driver_signal?sig -> goto loop }
    :: atomic { sysexit -> goto loop }
    od
loop:
    do
    :: atomic { ring?data
processing:
    -> printf("driver data %d\n", data)
       sysq!data;
       //if
       //:: (free_buffers > 0) -> sysq!data; free_buffers--
       //fi
       }
    :: atomic { sysexit && !ring?[_] -> goto exit }
    :: atomic { else
    -> need_signal = true;
       goto sleep }
    od
    // need to recheck
    if
    :: atomic { ring?[_] -> goto loop }
    fi
exit:
    printf("driver: system stopped, exiting...\n")
}

active proctype device() {
    int iter = 2 // limit number of iterations for tractability
    do
    :: atomic { iter > 0
    -> got = iter + 100; ring!got;
       device_io!true;
       iter-- }
    :: d_step { skip -> skip }
    :: atomic { skip -> goto off }
    od
off: skip
    d_step { device_off = 1;
    printf("device: off\n") }
}

// sanity check for packets being processed
ltl s1 { always (_nr_pr == 0 -> len(sysq) ==0) }
// signal off during processing
ltl s2 { always (driver@processing -> !driver_signal?[_]) }

// needs weak fairness, check that packets are delivered
ltl l1 { always (got == 102 -> eventually (processed == 102)) }
ltl l2 { always (got == 101 -> eventually (processed == 101)) }
