#define QSZ 2 // a bigger queue is not necessary to demonstrate signal issues

//int free_buffers = 0 // tokens for how many OS buffers have yet to be filled
int got              // got is set by the device when generating a packet
int processed        // processed is set by the system after receiving it
chan ring = [QSZ] of {int} // device -> driver
chan sysq = [QSZ] of {int} // driver -> OS

// modelling signals using async queues to avoid ABA problems with flags
chan device_io = [1] of {bool}
chan driver_signal = [1] of {bool}
bool need_signal = true // whether the system should signal the driver on i/o
chan device_off = [1] of {bool}
bool sysexit = false
bool driver_exit = false

active proctype system() {
    bool sig
    int data
loop:
    do
    :: atomic { device_io?sig
       if
       :: need_signal && len(driver_signal) == 0 -> driver_signal!true
       :: else -> skip
       fi }
    :: atomic { sysq?data
    -> printf("system recv: packet %d\n", data);
       processed = data }
    :: atomic { len(sysq) == 0 && !device_io?[_]
    -> if
       :: !sysexit -> goto loop
       :: else -> goto exit
       fi }
    :: atomic { device_off?sig
    -> if
       :: len(sysq) == 0 && !device_io?[_]
       -> printf("system: received device exit, cleaning up...\n")
          sysexit = true
       :: else -> skip
       fi }
    od
exit:
    // without this additional check, packets can be dropped between
    // 1) OS signalling the driver to exit
    // 2) driver receiving the signal and exiting
    atomic {
    driver_exit -> if
                   :: sysq?[_] -> goto loop
                   :: else -> skip
                   fi
    printf("system: supervisor stop\n") }
}

active proctype driver() {
    bool sig
    int data
sleep:
    do
    :: atomic { driver_signal?sig -> need_signal = false; goto loop }
    :: atomic { else
    -> if
       :: sysexit -> goto loop
       :: else -> skip
       fi }
    od
loop:
    do
    :: atomic { ring?data
    -> printf("driver data %d\n", data)
       sysq!data
       }
    :: atomic { sysexit && !ring?[_] -> goto exit }
    :: else // not atomic
    -> atomic {
       need_signal = true;
       /* need to recheck */
       if
       :: atomic { ring?[_] -> need_signal = false; goto loop }
       :: else -> skip
       fi
       goto sleep }
    od
exit:
    printf("driver: system stopped, exiting...\n")
    driver_exit = true
}

active proctype device() {
    int iter = QSZ+2 // limit number of iterations for tractability
    do
    :: atomic { iter > 0
    -> got = iter + 100; ring!got;
       device_io!true;
       iter-- }
    :: d_step { 0 == 0 -> skip }
    :: atomic { 1 == 1 -> goto off }
    od
off: skip
    d_step { device_off!true;
    printf("device: off\n") }
}

// sanity check for packets being processed
ltl s1 { always (_nr_pr == 0 -> len(sysq) ==0) }
// signal off during processing
ltl s2 { always (driver@loop -> !driver_signal?[_]) }

// needs weak fairness, check that packets are delivered
ltl l1 { always (got == 102 -> eventually (processed == 102)) }
ltl l2 { always (got == 101 -> eventually (processed == 101)) }
