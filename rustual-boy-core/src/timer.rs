/*
    TODO hw tests
    1. If you disable the timer and clear zero in the same write, while 
       counter == 0, does zero status get cleared?  The docs say you 
       shouldnt do this, but what actually happens when you do.
    2. Additional testing with disable/enable timer when the counter is 0
       In some hw tests the counter seems to get instantly set to the 
       reload value on timer disable, other times it almost seems like 
       a random number between 0 and the reload value.
    3. Its been shown that doing disable int, clear zero, enable int vs
       disable timer, enable timer doesnt result in the same fire time 
       for the next interrupt.  The later seems to fire early by about
       10us.  Need to do additional testing on this, its probably  
       related to #2
    4. Not really timer specific but try to measure how long it takes to
       enter an exception
*/

// 20mhz / (1s / 100us) = 2000
const LARGE_INTERVAL_PERIOD: usize = 2000;

// 20mhz / (1s / 20us) = 400
const SMALL_INTERVAL_PERIOD: usize = 400;

enum Interval {
    Large,
    Small,
}

pub struct Timer {
    interval: Interval,
    zero_interrupt_enable: bool,
    zero_status: bool,
    enable: bool,
    reload: u16,
    counter: u16,

    tick_counter: usize,
    zero_interrupt: bool,
}

impl Timer {
    pub fn new() -> Timer {
        Timer {
            interval: Interval::Large,
            zero_interrupt_enable: false,
            zero_status: false,
            enable: false,
            reload: 0,
            counter: 0xffff,

            tick_counter: 0,
            zero_interrupt: false,
        }
    }

    pub fn read_control_reg(&self) -> u8 {
        0xe4 |
        (match self.interval {
            Interval::Large => 0,
            Interval::Small => 1,
        } << 4) |
        (if self.zero_interrupt_enable { 1 } else { 0 } << 3) |
        (if self.zero_status { 1 } else { 0 } << 1) |
        if self.enable { 1 } else { 0 }
    }

    pub fn write_control_reg(&mut self, value: u8) {
        self.interval = if ((value >> 4) & 0x01) == 0 {
            Interval::Large
        } else {
            Interval::Small
        };
        self.zero_interrupt_enable = ((value >> 3) & 0x01) != 0;
        if ((value >> 2) & 0x01) != 0 {
            if !self.enable || self.counter != 0 {
                self.zero_status = false;
            }
        }
        if !self.zero_interrupt_enable || !self.zero_status {
            self.zero_interrupt = false;
        }
        self.enable = (value & 0x01) != 0;
    }

    pub fn read_counter_reload_low_reg(&self) -> u8 {
        self.counter as _
    }

    pub fn write_counter_reload_low_reg(&mut self, value: u8) {
        self.reload = (self.reload & 0xff00) | (value as u16);
        let new_counter = self.reload;
        self.update_counter(new_counter);
    }

    pub fn read_counter_reload_high_reg(&self) -> u8 {
        (self.counter >> 8) as _
    }

    pub fn write_counter_reload_high_reg(&mut self, value: u8) {
        self.reload = ((value as u16) << 8) | (self.reload & 0xff);
        let new_counter = self.reload;
        self.update_counter(new_counter);
    }

    fn update_counter(&mut self, value: u16) {
        if self.counter != 0 && value == 0 {
            self.zero_status = true;
            if self.zero_interrupt_enable {
                self.zero_interrupt = true;
            }
        }
        self.counter = value;
    }

    pub fn cycles(&mut self, cycles: usize) -> bool {
        if self.enable {
            for _ in 0..cycles {
                let tick_period = match self.interval {
                    Interval::Large => LARGE_INTERVAL_PERIOD,
                    Interval::Small => SMALL_INTERVAL_PERIOD,
                };
                self.tick_counter += 1;
                if self.tick_counter >= tick_period {
                    self.tick_counter = 0;

                    let new_counter = match self.counter {
                        0 => self.reload,
                        _ => self.counter - 1,
                    };
                    self.update_counter(new_counter);
                }
            }
        }

        self.zero_interrupt
    }
}
