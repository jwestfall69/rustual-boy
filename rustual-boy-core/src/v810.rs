use instruction::*;
use interconnect::*;

use std::collections::HashSet;
use std::fmt;

#[derive(Clone,Copy)]
pub enum TraceEntry {
    CpuCycles(usize),
    GprRead(usize, u32),
    GprWrite(usize, u32, u32),
    MemReadByte(u32, u8),
    MemReadHalfword(u32, u16),
    MemReadWord(u32, u32),
    MemWriteByte(u32, u8, u8, u8),
    MemWriteHalfword(u32, u16, u16, u16),
    MemWriteWord(u32, u32, u32, u32),
    Pc(u32, u32),
    Psw(u32, u32),
    SignedDisp16(i16),
    SignedImm5(i8),
    SignedImm16(i16),
    SysRegRead(usize, u32),
    SysRegWrite(usize, u32, u32, u32),
    UnsignedDisp32(u32),
    UnsignedImm5(u8),
    UnsignedImm16(u16),
}

#[cfg(not(feature = "cpu-trace"))]
macro_rules! trace_add {
    ($($arg:expr),*) => {};
}

#[cfg(feature = "cpu-trace")]
macro_rules! trace_add {
    ($self_:ident, $te:expr) => {
        if $self_.trace_enabled {
            let trace_entry = $te;
            $self_.trace_entries.push(trace_entry);
        }
    };
}

#[derive(Copy, Clone, Default)]
pub struct CacheEntry {
    pub tag: u32,
    pub base_addr: u32,
    pub subblock_valid: [bool; 2],
}

impl fmt::Display for CacheEntry {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "base_addr: 0x{:08x}, tag: 0x{:08x}, sb1 valid: {:5}, sb2 valid: {:5}", self.base_addr, self.tag, self.subblock_valid[0], self.subblock_valid[1])
    }
}

pub enum CacheResult {
    Hit,
    Miss,
    Disabled,
}

pub struct Cache {
    hits: usize,
    misses: usize,
    is_enabled: bool,
    entries: Box<[CacheEntry; 128]>,
}

impl Cache {
    fn new() -> Cache {
        Cache {
            hits: 0,
            misses: 0,
            is_enabled: false,
            entries: Box::new([CacheEntry::default(); 128]),
        }
    }

    pub fn clear_entries(&mut self, start: usize, mut count: usize) {
        if start >= 128 {
            return;
        }

        if count > 128 {
            count = 128;
        }

        if start + count > 128 {
            count = 128 - start;
        }

        for offset in 0..count {
            self.entries[start + offset].tag = 0;
            self.entries[start + offset].subblock_valid = [false; 2];
         }
    }

    pub fn set_is_enabled(&mut self, is_enabled: bool) {
        self.is_enabled = is_enabled;
    }

    pub fn is_enabled(&self) -> bool {
        return self.is_enabled;
    }

    pub fn read_halfword(&mut self, interconnect: &mut Interconnect, addr: u32) -> (u16, CacheResult) {
        let halfword = interconnect.read_halfword(addr);

        if !self.is_enabled {
            return (halfword, CacheResult::Disabled);
        }

        let byte_offset = (addr & 0x07) as usize;
        let entry = ((addr >> 3) & 0x7f) as usize;
        let tag = addr >> 10;
        let subblock = if byte_offset >= 4 { 1 } else { 0 };

        if self.entries[entry].tag == tag {
            if self.entries[entry].subblock_valid[subblock] {
                self.hits += 1;
                return (halfword, CacheResult::Hit);
            }
            self.entries[entry].subblock_valid[subblock] = true;
            self.misses += 1;
            return (halfword, CacheResult::Miss);
        } else {
            self.entries[entry].tag = tag;
            self.entries[entry].subblock_valid = [false; 2];
            self.entries[entry].subblock_valid[subblock] = true;
            self.entries[entry].base_addr = addr & 0xfffffff8;
            self.misses += 1;
            return (halfword, CacheResult::Miss);
        }
    }

    pub fn entry(&self, entry: usize) -> CacheEntry {
        return self.entries[entry];
    }

    pub fn stats(&self) -> (usize, usize) {
        return (self.hits, self.misses);
    }
}

pub struct V810 {
    reg_pc: u32,

    _reg_gpr: Box<[u32; 32]>,
    reg_gpr_ptr: *mut u32,

    reg_eipc: u32,
    reg_eipsw: u32,
    reg_ecr: u16,

    psw_zero: bool,
    psw_sign: bool,
    psw_overflow: bool,
    psw_carry: bool,
    psw_fp_precision_degredation: bool,
    psw_fp_underflow: bool,
    psw_fp_overflow: bool,
    psw_fp_zero_division: bool,
    psw_fp_invalid_operation: bool,
    psw_fp_reserved_operand: bool,
    psw_interrupt_disable: bool,
    psw_address_trap_enable: bool,
    psw_exception_pending: bool,
    psw_nmi_pending: bool,
    psw_interrupt_mask_level: usize,

    pub cache: Cache,

    trace_enabled: bool,
    pub trace_entries: Vec<TraceEntry>,

    pub watchpoints: HashSet<u32>,
}

impl V810 {
    pub fn new() -> V810 {
        let mut reg_gpr = Box::new([0xdeadbeef; 32]);
        reg_gpr[0] = 0;
        let reg_gpr_ptr = reg_gpr.as_mut_ptr();

        V810 {
            reg_pc: 0xfffffff0,

            _reg_gpr: reg_gpr,
            reg_gpr_ptr: reg_gpr_ptr,

            reg_eipc: 0xdeadbeef,
            reg_eipsw: 0xdeadbeef,
            reg_ecr: 0xfff0,

            psw_zero: false,
            psw_sign: false,
            psw_overflow: false,
            psw_carry: false,
            psw_fp_precision_degredation: false,
            psw_fp_underflow: false,
            psw_fp_overflow: false,
            psw_fp_zero_division: false,
            psw_fp_invalid_operation: false,
            psw_fp_reserved_operand: false,
            psw_interrupt_disable: false,
            psw_address_trap_enable: false,
            psw_exception_pending: false,
            psw_nmi_pending: true,
            psw_interrupt_mask_level: 0,

            cache: Cache::new(),

            trace_enabled: false,
            trace_entries: Vec::new(),

            watchpoints: HashSet::new(),
        }
    }

    pub fn set_trace_enabled(&mut self, enable: bool) {
        self.trace_enabled = enable;
    }

    pub fn is_trace_enabled(&self) -> bool {
        self.trace_enabled
    }

    pub fn reg_pc(&self) -> u32 {
        self.reg_pc
    }

    pub fn reg_gpr(&mut self, index: usize) -> u32 {
        unsafe {
            let reg_ptr = self.reg_gpr_ptr.offset(index as _);
            trace_add!(self, TraceEntry::GprRead(index, *reg_ptr));
            *reg_ptr
        }
    }

    fn set_reg_gpr(&mut self, index: usize, value: u32) {
        if index != 0 {
            unsafe {
                let reg_ptr = self.reg_gpr_ptr.offset(index as _);
                trace_add!(self, TraceEntry::GprWrite(index, *reg_ptr, value));
                *reg_ptr = value;
            }
        }
    }

    // TODO: Come up with a more portable way to do this conversion
    fn reg_gpr_float(&mut self, index: usize) -> f32 {
        unsafe {
            let reg_ptr = self.reg_gpr_ptr.offset(index as _);
            trace_add!(self, TraceEntry::GprRead(index, *reg_ptr));
            let reg_float_ptr = reg_ptr as *const f32;
            *reg_float_ptr
        }
    }

    fn set_reg_gpr_float(&mut self, index: usize, value: f32) {
        if index != 0 {
            unsafe {
                let reg_ptr = self.reg_gpr_ptr.offset(index as _);
                trace_add!(self, TraceEntry::GprWrite(index, *reg_ptr, value as u32));
                let reg_float_ptr = reg_ptr as *mut f32;
                *reg_float_ptr = value;
            }
        }
    }

    pub fn reg_chcw(&self) -> u32 {
        match self.cache.is_enabled() {
            true => 2,
            false => 0,
        }
    }

    fn set_reg_chcw(&mut self, value: u32) {
        let enable = (value >> 1) & 0x01 == 1;
        if enable != self.cache.is_enabled() {
            logln!(Log::Cpu, "chcw cache enable changed to {}", enable);
            self.cache.set_is_enabled(enable);
        }

        if value & 0x01 == 1 {
            let entry_count = ((value >> 8) & 0x7ffff) as usize;
            let entry_start = (value >> 20) as usize;
            logln!(Log::Cpu, "chcw request to clear cache for start entry: {}, entry count: {}", entry_start, entry_count);
            self.cache.clear_entries(entry_start, entry_count);
        } else if (value >> 4) & 0x01 == 1 {
            let addr = value & 0xffffff00;
            logln!(Log::Cpu, "WARNING: chcw request to dump instruction cache to 0x{:08x} not implemented yet", addr);
        } else if (value >> 5) & 0x01 == 1 {
            let addr = value & 0xffffff00;
            logln!(Log::Cpu, "WARNING: chcw request to restore instruction cache from 0x{:08x} not implemented yet", addr);
        }
    }

    pub fn reg_eipc(&self) -> u32 {
        self.reg_eipc
    }

    pub fn reg_eipsw(&self) -> u32 {
        self.reg_eipsw
    }

    pub fn reg_ecr(&self) -> u16 {
        self.reg_ecr
    }

    pub fn reg_psw(&self) -> u32 {
        (if self.psw_zero { 1 << 0 } else { 0 }) |
        (if self.psw_sign { 1 << 1 } else { 0 }) |
        (if self.psw_overflow { 1 << 2 } else { 0 }) |
        (if self.psw_carry { 1 << 3 } else { 0 }) |
        (if self.psw_fp_precision_degredation { 1 << 4 } else { 0 }) |
        (if self.psw_fp_underflow { 1 << 5 } else { 0 }) |
        (if self.psw_fp_overflow { 1 << 6 } else { 0 }) |
        (if self.psw_fp_zero_division { 1 << 7 } else { 0 }) |
        (if self.psw_fp_invalid_operation { 1 << 8 } else { 0 }) |
        (if self.psw_fp_reserved_operand { 1 << 9 } else { 0 }) |
        (if self.psw_interrupt_disable { 1 << 12 } else { 0 }) |
        (if self.psw_address_trap_enable { 1 << 13 } else { 0 }) |
        (if self.psw_exception_pending { 1 << 14 } else { 0 }) |
        (if self.psw_nmi_pending { 1 << 15 } else { 0 }) |
        (self.psw_interrupt_mask_level as u32) << 16
    }

    pub fn set_reg_psw(&mut self, value: u32) {
        self.psw_zero = ((value >> 0) & 0x01) != 0;
        self.psw_sign = ((value >> 1) & 0x01) != 0;
        self.psw_overflow = ((value >> 2) & 0x01) != 0;
        self.psw_carry = ((value >> 3) & 0x01) != 0;
        self.psw_fp_precision_degredation = ((value >> 4) & 0x01) != 0;
        self.psw_fp_underflow = ((value >> 5) & 0x01) != 0;
        self.psw_fp_overflow = ((value >> 6) & 0x01) != 0;
        self.psw_fp_zero_division = ((value >> 7) & 0x01) != 0;
        self.psw_fp_invalid_operation = ((value >> 8) & 0x01) != 0;
        self.psw_fp_reserved_operand = ((value >> 9) & 0x01) != 0;
        self.psw_interrupt_disable = ((value >> 12) & 0x01) != 0;
        self.psw_address_trap_enable = ((value >> 13) & 0x01) != 0;
        self.psw_exception_pending = ((value >> 14) & 0x01) != 0;
        self.psw_nmi_pending = ((value >> 15) & 0x01) != 0;
        self.psw_interrupt_mask_level = ((value as usize) >> 16) & 0x0f;
    }

    pub fn step(&mut self, interconnect: &mut Interconnect) -> (usize, bool) {
        let original_pc = self.reg_pc;

        #[cfg(feature = "cpu-trace")]
        self.trace_entries.clear();
        trace_add!(self, TraceEntry::Psw(self.reg_psw(), 0));

        let (first_halfword, _) = self.cache.read_halfword(interconnect, original_pc);
        let mut next_pc = original_pc.wrapping_add(2);

        let mut num_cycles = 1;
        let mut trigger_watchpoint = false;

        if first_halfword >> 13 == OPCODE_BITS_BCOND_PREFIX {
            let cond_bits = (first_halfword >> 9) & 0x0f;
            let take_branch = match cond_bits {
                OPCODE_BITS_BCOND_BV => self.psw_overflow,
                OPCODE_BITS_BCOND_BC => self.psw_carry,
                OPCODE_BITS_BCOND_BZ => self.psw_zero,
                OPCODE_BITS_BCOND_BNH => self.psw_carry || self.psw_zero,
                OPCODE_BITS_BCOND_BN => self.psw_sign,
                OPCODE_BITS_BCOND_BR => true,
                OPCODE_BITS_BCOND_BLT => self.psw_sign != self.psw_overflow,
                OPCODE_BITS_BCOND_BLE => (self.psw_sign != self.psw_overflow) || self.psw_zero,
                OPCODE_BITS_BCOND_BNV => !self.psw_overflow,
                OPCODE_BITS_BCOND_BNC => !self.psw_carry,
                OPCODE_BITS_BCOND_BNZ => !self.psw_zero,
                OPCODE_BITS_BCOND_BH => !(self.psw_carry || self.psw_zero),
                OPCODE_BITS_BCOND_BP => !self.psw_sign,
                OPCODE_BITS_BCOND_NOP => false,
                OPCODE_BITS_BCOND_BGE => !(self.psw_sign != self.psw_overflow),
                OPCODE_BITS_BCOND_BGT => !((self.psw_sign != self.psw_overflow) || self.psw_zero),
                _ => panic!("Unrecognized cond bits: {:04b} (halfword: 0b{:016b})", cond_bits, first_halfword)
            };

            trace_add!(self, TraceEntry::SignedDisp16((((first_halfword as i16) << 7) >> 7)));
            if take_branch {
                let disp = ((((first_halfword as i16) << 7) >> 7) as u32) & 0xfffffffe;
                next_pc = self.reg_pc.wrapping_add(disp);
                num_cycles = 3;
            }
        } else {
            macro_rules! format_i {
                ($f:expr) => ({
                    let reg1 = (first_halfword & 0x1f) as usize;
                    let reg2 = ((first_halfword >> 5) & 0x1f) as usize;

                    $f(reg1, reg2);
                });
            }

            macro_rules! format_ii {
                ($f:expr) => ({
                    let imm5 = (first_halfword & 0x1f) as usize;
                    let reg2 = ((first_halfword >> 5) & 0x1f) as usize;
                    $f(imm5, reg2);
                })
            }

            macro_rules! format_iv {
                ($f:expr) => ({
                    let (second_halfword, _) = self.cache.read_halfword(interconnect, next_pc);
                    next_pc = next_pc.wrapping_add(2);

                    let disp = ((((((first_halfword as i16) << 6) >> 6) as u32) << 16) | (second_halfword as u32)) & 0xfffffffe;
                    let target = self.reg_pc.wrapping_add(disp);
                    trace_add!(self, TraceEntry::UnsignedDisp32(disp));
                    $f(target);
                })
            }

            macro_rules! format_v {
                ($f:expr) => ({
                    let (second_halfword, _) = self.cache.read_halfword(interconnect, next_pc);
                    next_pc = next_pc.wrapping_add(2);

                    let reg1 = (first_halfword & 0x1f) as usize;
                    let reg2 = ((first_halfword >> 5) & 0x1f) as usize;
                    let imm16 = second_halfword;
                    $f(reg1, reg2, imm16);
                })
            }

            macro_rules! format_vi {
                ($f:expr) => ({
                    let (second_halfword, _) = self.cache.read_halfword(interconnect, next_pc);
                    next_pc = next_pc.wrapping_add(2);

                    let reg1 = (first_halfword & 0x1f) as usize;
                    let reg2 = ((first_halfword >> 5) & 0x1f) as usize;
                    let disp16 = second_halfword as i16;
                    trace_add!(self, TraceEntry::SignedDisp16(disp16));
                    $f(reg1, reg2, disp16);
                })
            }

            let opcode_bits = first_halfword >> 10;
            match opcode_bits {
                OPCODE_BITS_MOV_REG => format_i!(|reg1, reg2| {
                    let value = self.reg_gpr(reg1);
                    self.set_reg_gpr(reg2, value);
                }),
                OPCODE_BITS_ADD_REG => format_i!(|reg1, reg2| {
                    let lhs = self.reg_gpr(reg2);
                    let rhs = self.reg_gpr(reg1);
                    self.add(lhs, rhs, reg2);
                }),
                OPCODE_BITS_SUB => format_i!(|reg1, reg2| {
                    let lhs = self.reg_gpr(reg2);
                    let rhs = self.reg_gpr(reg1);
                    let res = self.sub_and_set_flags(lhs, rhs);
                    self.set_reg_gpr(reg2, res);
                }),
                OPCODE_BITS_CMP_REG => format_i!(|reg1, reg2| {
                    let lhs = self.reg_gpr(reg2);
                    let rhs = self.reg_gpr(reg1);
                    self.sub_and_set_flags(lhs, rhs);
                }),
                OPCODE_BITS_SHL_REG => format_i!(|reg1, reg2| {
                    let lhs = self.reg_gpr(reg2);
                    let rhs = self.reg_gpr(reg1);
                    let res = self.shl_and_set_flags(lhs, rhs);
                    self.set_reg_gpr(reg2, res);
                }),
                OPCODE_BITS_SHR_REG => format_i!(|reg1, reg2| {
                    let lhs = self.reg_gpr(reg2);
                    let rhs = self.reg_gpr(reg1);
                    let res = self.shr_and_set_flags(lhs, rhs);
                    self.set_reg_gpr(reg2, res);
                }),
                OPCODE_BITS_JMP => format_i!(|reg1, _| {
                    next_pc = self.reg_gpr(reg1) & 0xfffffffe;
                    num_cycles = 3;
                }),
                OPCODE_BITS_SAR_REG => format_i!(|reg1, reg2| {
                    let lhs = self.reg_gpr(reg2);
                    let rhs = self.reg_gpr(reg1);
                    let res = self.sar_and_set_flags(lhs, rhs);
                    self.set_reg_gpr(reg2, res);
                }),
                OPCODE_BITS_MUL => format_i!(|reg1, reg2| {
                    let lhs = (self.reg_gpr(reg2) as i32) as i64;
                    let rhs = (self.reg_gpr(reg1) as i32) as i64;
                    let res = (lhs * rhs) as u64;
                    let res_low = res as u32;
                    let res_high = (res >> 32) as u32;
                    let overflow = res != ((res_low as i32) as u64);
                    self.set_reg_gpr(30, res_high);
                    self.set_reg_gpr(reg2, res_low);
                    self.set_zero_sign_flags(res_low);
                    self.psw_overflow = overflow;
                    num_cycles = 13;
                }),
                OPCODE_BITS_DIV => format_i!(|reg1, reg2| {
                    let lhs = self.reg_gpr(reg2);
                    let rhs = self.reg_gpr(reg1);
                    let (res, rem, overflow) = if lhs == 0x80000000 && rhs == 0xffffffff {
                        (lhs, 0, true)
                    } else {
                        let lhs = lhs as i32;
                        let rhs = rhs as i32;
                        let res = (lhs / rhs) as u32;
                        let rem = (lhs % rhs) as u32;
                        (res, rem, false)
                    };
                    self.set_reg_gpr(30, rem);
                    self.set_reg_gpr(reg2, res);
                    self.set_zero_sign_flags(res);
                    self.psw_overflow = overflow;
                    num_cycles = 38;
                }),
                OPCODE_BITS_MUL_U => format_i!(|reg1, reg2| {
                    let lhs = self.reg_gpr(reg2) as u64;
                    let rhs = self.reg_gpr(reg1) as u64;
                    let res = lhs * rhs;
                    let res_low = res as u32;
                    let res_high = (res >> 32) as u32;
                    let overflow = res != (res_low as u64);
                    self.set_reg_gpr(30, res_high);
                    self.set_reg_gpr(reg2, res_low);
                    self.set_zero_sign_flags(res_low);
                    self.psw_overflow = overflow;
                    num_cycles = 13;
                }),
                OPCODE_BITS_DIV_U => format_i!(|reg1, reg2| {
                    let lhs = self.reg_gpr(reg2);
                    let rhs = self.reg_gpr(reg1);
                    let res = lhs / rhs;
                    let rem = lhs % rhs;
                    self.set_reg_gpr(30, rem);
                    self.set_reg_gpr(reg2, res);
                    self.set_zero_sign_flags(res);
                    self.psw_overflow = false;
                    num_cycles = 36;
                }),
                OPCODE_BITS_OR => format_i!(|reg1, reg2| {
                    let lhs = self.reg_gpr(reg2);
                    let rhs = self.reg_gpr(reg1);
                    let res = lhs | rhs;
                    self.set_reg_gpr(reg2, res);
                    self.set_zero_sign_flags(res);
                    self.psw_overflow = false;
                }),
                OPCODE_BITS_AND => format_i!(|reg1, reg2| {
                    let lhs = self.reg_gpr(reg2);
                    let rhs = self.reg_gpr(reg1);
                    let res = lhs & rhs;
                    self.set_reg_gpr(reg2, res);
                    self.set_zero_sign_flags(res);
                    self.psw_overflow = false;
                }),
                OPCODE_BITS_XOR => format_i!(|reg1, reg2| {
                    let lhs = self.reg_gpr(reg2);
                    let rhs = self.reg_gpr(reg1);
                    let res = lhs ^ rhs;
                    self.set_reg_gpr(reg2, res);
                    self.set_zero_sign_flags(res);
                    self.psw_overflow = false;
                }),
                OPCODE_BITS_NOT => format_i!(|reg1, reg2| {
                    let res = !self.reg_gpr(reg1);
                    self.set_reg_gpr(reg2, res);
                    self.set_zero_sign_flags(res);
                    self.psw_overflow = false;
                }),
                OPCODE_BITS_MOV_IMM => format_ii!(|imm5, reg2| {
                    let value = sign_extend_imm5(imm5);
                    trace_add!(self, TraceEntry::SignedImm5(value as i8));
                    self.set_reg_gpr(reg2, value);
                }),
                OPCODE_BITS_ADD_IMM_5 => format_ii!(|imm5, reg2| {
                    let lhs = self.reg_gpr(reg2);
                    let rhs = sign_extend_imm5(imm5);
                    trace_add!(self, TraceEntry::SignedImm5(rhs as i8));
                    self.add(lhs, rhs, reg2);
                }),
                OPCODE_BITS_SETF => format_ii!(|imm5, reg2| {
                    trace_add!(self, TraceEntry::UnsignedImm5(imm5 as u8));
                    let set = match imm5 & 0x0f {
                        OPCODE_CONDITION_BITS_V => self.psw_overflow,
                        OPCODE_CONDITION_BITS_C => self.psw_carry,
                        OPCODE_CONDITION_BITS_Z => self.psw_zero,
                        OPCODE_CONDITION_BITS_NH => self.psw_carry || self.psw_zero,
                        OPCODE_CONDITION_BITS_N => self.psw_sign,
                        OPCODE_CONDITION_BITS_T => true,
                        OPCODE_CONDITION_BITS_LT => self.psw_sign != self.psw_overflow,
                        OPCODE_CONDITION_BITS_LE => (self.psw_sign != self.psw_overflow) || self.psw_zero,
                        OPCODE_CONDITION_BITS_NV => !self.psw_overflow,
                        OPCODE_CONDITION_BITS_NC => !self.psw_carry,
                        OPCODE_CONDITION_BITS_NZ => !self.psw_zero,
                        OPCODE_CONDITION_BITS_H => !(self.psw_carry || self.psw_zero),
                        OPCODE_CONDITION_BITS_P => !self.psw_sign,
                        OPCODE_CONDITION_BITS_F => false,
                        OPCODE_CONDITION_BITS_GE => !(self.psw_sign != self.psw_overflow),
                        OPCODE_CONDITION_BITS_GT => !((self.psw_sign != self.psw_overflow) || self.psw_zero),
                        _ => panic!("Unrecognized condition: {}", imm5),
                    };
                    self.set_reg_gpr(reg2, if set { 1 } else { 0 });
                }),
                OPCODE_BITS_CMP_IMM => format_ii!(|imm5, reg2| {
                    let lhs = self.reg_gpr(reg2);
                    let rhs = sign_extend_imm5(imm5);
                    trace_add!(self, TraceEntry::SignedImm5(rhs as i8));
                    self.sub_and_set_flags(lhs, rhs);
                }),
                OPCODE_BITS_SHL_IMM => format_ii!(|imm5, reg2| {
                    trace_add!(self, TraceEntry::UnsignedImm5(imm5 as u8));
                    let lhs = self.reg_gpr(reg2);
                    let rhs = imm5 as u32;
                    let res = self.shl_and_set_flags(lhs, rhs);
                    self.set_reg_gpr(reg2, res);
                }),
                OPCODE_BITS_SHR_IMM => format_ii!(|imm5, reg2| {
                    trace_add!(self, TraceEntry::UnsignedImm5(imm5 as u8));
                    let lhs = self.reg_gpr(reg2);
                    let rhs = imm5 as u32;
                    let res = self.shr_and_set_flags(lhs, rhs);
                    self.set_reg_gpr(reg2, res);
                }),
                OPCODE_BITS_CLI => format_ii!(|_, _| {
                    self.psw_interrupt_disable = false;

                    num_cycles = 12;
                }),
                OPCODE_BITS_SAR_IMM => format_ii!(|imm5, reg2| {
                    trace_add!(self, TraceEntry::UnsignedImm5(imm5 as u8));
                    let lhs = self.reg_gpr(reg2);
                    let rhs = imm5 as u32;
                    let res = self.sar_and_set_flags(lhs, rhs);
                    self.set_reg_gpr(reg2, res);
                }),
                OPCODE_BITS_RETI => format_ii!(|_, _| {
                    next_pc = self.return_from_exception();
                    num_cycles = 10;
                }),
                OPCODE_BITS_HALT => format_ii!(|_, _| {
                    next_pc = original_pc;
                }),
                OPCODE_BITS_LDSR => format_ii!(|imm5, reg2| {
                    trace_add!(self, TraceEntry::UnsignedImm5(imm5 as u8));
                    let value = self.reg_gpr(reg2);
                    match imm5 {
                        OPCODE_SYSTEM_REGISTER_ID_EIPC => {
                            trace_add!(self, TraceEntry::SysRegWrite(imm5, self.reg_eipc, value, 0));
                            self.reg_eipc = value;
                        }
                        OPCODE_SYSTEM_REGISTER_ID_EIPSW => {
                            trace_add!(self, TraceEntry::SysRegWrite(imm5, self.reg_eipsw, value, 0));
                            self.reg_eipsw = value;
                        }
                        OPCODE_SYSTEM_REGISTER_ID_FEPC => {
                            trace_add!(self, TraceEntry::SysRegWrite(imm5, 0, 0, 0));
                            logln!(Log::Cpu, "WARNING: ldsr fepc not yet implemented (value: 0x{:08x})", value);
                        }
                        OPCODE_SYSTEM_REGISTER_ID_FEPSW => {
                            trace_add!(self, TraceEntry::SysRegWrite(imm5, 0, 0, 0));
                            logln!(Log::Cpu, "WARNING: ldsr fepsw not yet implemented (value: 0x{:08x})", value);
                        }
                        OPCODE_SYSTEM_REGISTER_ID_ECR => {
                            trace_add!(self, TraceEntry::SysRegWrite(imm5, self.reg_ecr as u32, value as u32, 0));
                            self.reg_ecr = value as _;
                        }
                        OPCODE_SYSTEM_REGISTER_ID_PSW => {
                            trace_add!(self, TraceEntry::SysRegWrite(imm5, self.reg_psw(), value, 0));
                            self.set_reg_psw(value);
                        }
                        OPCODE_SYSTEM_REGISTER_ID_CHCW => {
                            trace_add!(self, TraceEntry::SysRegWrite(imm5, self.reg_chcw(), value, 0));
                            self.set_reg_chcw(value);
                            logln!(Log::Cpu, "WARNING: ldsr chcw not fully implemented (value: 0x{:08x})", value);
                        }
                        _ => logln!(Log::Cpu, "WARNING: Unrecognized system register: {}", imm5),
                    }
                }),
                OPCODE_BITS_STSR => format_ii!(|imm5, reg2| {
                    trace_add!(self, TraceEntry::UnsignedImm5(imm5 as u8));
                    let value = match imm5 {
                        OPCODE_SYSTEM_REGISTER_ID_EIPC => self.reg_eipc,
                        OPCODE_SYSTEM_REGISTER_ID_EIPSW => self.reg_eipsw,
                        OPCODE_SYSTEM_REGISTER_ID_FEPC => {
                            logln!(Log::Cpu, "WARNING: stsr fepc not yet implemented");
                            0
                        }
                        OPCODE_SYSTEM_REGISTER_ID_FEPSW => {
                            logln!(Log::Cpu, "WARNING: stsr fepsw not yet implemented");
                            0
                        }
                        OPCODE_SYSTEM_REGISTER_ID_ECR => self.reg_ecr as _,
                        OPCODE_SYSTEM_REGISTER_ID_PSW => self.reg_psw(),
                        OPCODE_SYSTEM_REGISTER_ID_CHCW => {
                            logln!(Log::Cpu, "WARNING: stsr chcw not fully implemented");
                            self.reg_chcw()
                        }
                        _ => {
                            logln!(Log::Cpu, "WARNING: Unrecognized system register: {}", imm5);
                            0
                        }
                    };
                    trace_add!(self, TraceEntry::SysRegRead(imm5, value));
                    self.set_reg_gpr(reg2, value);
                }),
                OPCODE_BITS_SEI => format_ii!(|_, _| {
                    self.psw_interrupt_disable = true;

                    num_cycles = 12;
                }),
                OPCODE_BITS_BIT_STRING => format_ii!(|imm5, _| {
                    macro_rules! bsu {
                        ($f:expr) => ({
                            let mut src_word_addr = self.reg_gpr(30) & 0xfffffffc;
                            let mut dst_word_addr = self.reg_gpr(29) & 0xfffffffc;
                            let mut src_bit_offset = self.reg_gpr(27) & 0x1f;
                            let mut dst_bit_offset = self.reg_gpr(26) & 0x1f;
                            let mut num_bits = self.reg_gpr(28);

                            while num_bits > 0 {
                                let src_word = self.read_word(interconnect, src_word_addr);
                                let dst_word = self.read_word(interconnect, dst_word_addr);
                                let src_bit = (src_word >> src_bit_offset) & 0x01;
                                let dst_bit = (dst_word >> dst_bit_offset) & 0x01;
                                let res_bit = $f(src_bit, dst_bit) & 0x01;
                                let dst_bit_mask = !(1 << dst_bit_offset);
                                let res_word = (dst_word & dst_bit_mask) | (res_bit << dst_bit_offset);
                                self.write_word(interconnect, dst_word_addr, res_word);

                                src_bit_offset += 1;
                                if src_bit_offset >= 32 {
                                    src_bit_offset = 0;
                                    src_word_addr += 4;
                                }
                                dst_bit_offset += 1;
                                if dst_bit_offset >= 32 {
                                    dst_bit_offset = 0;
                                    dst_word_addr += 4;
                                }

                                num_bits -= 1;
                            }

                            self.set_reg_gpr(30, src_word_addr);
                            self.set_reg_gpr(29, dst_word_addr);
                            self.set_reg_gpr(27, src_bit_offset);
                            self.set_reg_gpr(26, dst_bit_offset);
                            self.set_reg_gpr(28, num_bits);
                        });
                    }

                    match imm5 {
                        OPCODE_BITS_BIT_STRING_OP_ORBSU => bsu!(|src_bit: u32, dst_bit: u32| src_bit | dst_bit),
                        OPCODE_BITS_BIT_STRING_OP_ANDBSU => bsu!(|src_bit: u32, dst_bit: u32| src_bit & dst_bit),
                        OPCODE_BITS_BIT_STRING_OP_XORBSU => bsu!(|src_bit: u32, dst_bit: u32| src_bit ^ dst_bit),
                        OPCODE_BITS_BIT_STRING_OP_MOVBSU => bsu!(|src_bit: u32, _| src_bit),
                        OPCODE_BITS_BIT_STRING_OP_ORNBSU => bsu!(|src_bit: u32, dst_bit: u32| !src_bit | dst_bit),
                        OPCODE_BITS_BIT_STRING_OP_ANDNBSU => bsu!(|src_bit: u32, dst_bit: u32| !src_bit & dst_bit),
                        OPCODE_BITS_BIT_STRING_OP_XORNBSU => bsu!(|src_bit: u32, dst_bit: u32| !src_bit ^ dst_bit),
                        OPCODE_BITS_BIT_STRING_OP_NOTBSU => bsu!(|src_bit: u32, _| !src_bit),
                        _ => panic!("Unrecognized bit string op: {:05b}", imm5)
                    }
                }),
                OPCODE_BITS_MOVEA => format_v!(|reg1, reg2, imm16| {
                    trace_add!(self, TraceEntry::SignedImm16(imm16 as i16));
                    let lhs = self.reg_gpr(reg1);
                    let rhs = (imm16 as i16) as u32;
                    let res = lhs.wrapping_add(rhs);
                    self.set_reg_gpr(reg2, res);
                }),
                OPCODE_BITS_ADD_IMM_16 => format_v!(|reg1, reg2, imm16| {
                    trace_add!(self, TraceEntry::SignedImm16(imm16 as i16));
                    let lhs = self.reg_gpr(reg1);
                    let rhs = (imm16 as i16) as u32;
                    self.add(lhs, rhs, reg2);
                }),
                OPCODE_BITS_JR => format_iv!(|target| {
                    next_pc = target;
                    num_cycles = 3;
                }),
                OPCODE_BITS_JAL => format_iv!(|target| {
                    self.set_reg_gpr(31, next_pc);
                    next_pc = target;
                    num_cycles = 3;
                }),
                OPCODE_BITS_OR_I => format_v!(|reg1, reg2, imm16| {
                    trace_add!(self, TraceEntry::UnsignedImm16(imm16 as u16));
                    let lhs = self.reg_gpr(reg1);
                    let rhs = imm16 as u32;
                    let res = lhs | rhs;
                    self.set_reg_gpr(reg2, res);
                    self.set_zero_sign_flags(res);
                    self.psw_overflow = false;
                }),
                OPCODE_BITS_AND_I => format_v!(|reg1, reg2, imm16| {
                    trace_add!(self, TraceEntry::UnsignedImm16(imm16 as u16));
                    let lhs = self.reg_gpr(reg1);
                    let rhs = imm16 as u32;
                    let res = lhs & rhs;
                    self.set_reg_gpr(reg2, res);
                    self.set_zero_sign_flags(res);
                    self.psw_overflow = false;
                }),
                OPCODE_BITS_XOR_I => format_v!(|reg1, reg2, imm16| {
                    trace_add!(self, TraceEntry::UnsignedImm16(imm16 as u16));
                    let lhs = self.reg_gpr(reg1);
                    let rhs = imm16 as u32;
                    let res = lhs ^ rhs;
                    self.set_reg_gpr(reg2, res);
                    self.set_zero_sign_flags(res);
                    self.psw_overflow = false;
                }),
                OPCODE_BITS_MOVHI => format_v!(|reg1, reg2, imm16| {
                    trace_add!(self, TraceEntry::UnsignedImm16(imm16 as u16));
                    let lhs = self.reg_gpr(reg1);
                    let rhs = (imm16 as u32) << 16;
                    let res = lhs.wrapping_add(rhs);
                    self.set_reg_gpr(reg2, res);
                }),
                OPCODE_BITS_LDB => format_vi!(|reg1, reg2, disp16| {
                    let addr = self.reg_gpr(reg1).wrapping_add(disp16 as u32);
                    trigger_watchpoint |= self.check_watchpoints(addr);
                    let value = (self.read_byte(interconnect, addr) as i8) as u32;
                    self.set_reg_gpr(reg2, value);
                    num_cycles = 4;
                }),
                OPCODE_BITS_LDH => format_vi!(|reg1, reg2, disp16| {
                    let addr = self.reg_gpr(reg1).wrapping_add(disp16 as u32);
                    let addr = addr & 0xfffffffe;
                    trigger_watchpoint |= self.check_watchpoints(addr);
                    let value = (self.read_halfword(interconnect, addr) as i16) as u32;
                    self.set_reg_gpr(reg2, value);
                    num_cycles = 4;
                }),
                OPCODE_BITS_LDW | OPCODE_BITS_INW => format_vi!(|reg1, reg2, disp16| {
                    let addr = self.reg_gpr(reg1).wrapping_add(disp16 as u32);
                    let addr = addr & 0xfffffffc;
                    trigger_watchpoint |= self.check_watchpoints(addr);
                    let value = self.read_word(interconnect, addr);
                    self.set_reg_gpr(reg2, value);
                    num_cycles = 4;
                }),
                OPCODE_BITS_STB | OPCODE_BITS_OUTB => format_vi!(|reg1, reg2, disp16| {
                    let addr = self.reg_gpr(reg1).wrapping_add(disp16 as u32);
                    trigger_watchpoint |= self.check_watchpoints(addr);
                    let value = self.reg_gpr(reg2) as u8;
                    self.write_byte(interconnect, addr, value);
                    num_cycles = 4;
                }),
                OPCODE_BITS_STH | OPCODE_BITS_OUTH => format_vi!(|reg1, reg2, disp16| {
                    let addr = self.reg_gpr(reg1).wrapping_add(disp16 as u32);
                    let addr = addr & 0xfffffffe;
                    trigger_watchpoint |= self.check_watchpoints(addr);
                    let value = self.reg_gpr(reg2) as u16;
                    self.write_halfword(interconnect, addr, value);
                    num_cycles = 4;
                }),
                OPCODE_BITS_STW | OPCODE_BITS_OUTW => format_vi!(|reg1, reg2, disp16| {
                    let addr = self.reg_gpr(reg1).wrapping_add(disp16 as u32);
                    let addr = addr & 0xfffffffc;
                    trigger_watchpoint |= self.check_watchpoints(addr);
                    let value = self.reg_gpr(reg2);
                    self.write_word(interconnect, addr, value);
                    num_cycles = 4;
                }),
                OPCODE_BITS_INB => format_vi!(|reg1, reg2, disp16| {
                    let addr = self.reg_gpr(reg1).wrapping_add(disp16 as u32);
                    trigger_watchpoint |= self.check_watchpoints(addr);
                    let value = self.read_byte(interconnect, addr) as u32;
                    self.set_reg_gpr(reg2, value);
                    num_cycles = 4;
                }),
                OPCODE_BITS_INH => format_vi!(|reg1, reg2, disp16| {
                    let addr = self.reg_gpr(reg1).wrapping_add(disp16 as u32);
                    let addr = addr & 0xfffffffe;
                    trigger_watchpoint |= self.check_watchpoints(addr);
                    let value = self.read_halfword(interconnect, addr) as u32;
                    self.set_reg_gpr(reg2, value);
                    num_cycles = 4;
                }),
                OPCODE_BITS_EXTENDED => {
                    let (second_halfword, _) = self.cache.read_halfword(interconnect, next_pc);
                    next_pc = next_pc.wrapping_add(2);

                    let reg1 = (first_halfword & 0x1f) as usize;
                    let reg2 = ((first_halfword >> 5) & 0x1f) as usize;

                    let subop_bits = second_halfword >> 10;

                    match subop_bits {
                        OPCODE_BITS_SUB_OP_CMPF_S => {
                            let lhs = self.reg_gpr_float(reg2);
                            let rhs = self.reg_gpr_float(reg1);
                            let value = lhs - rhs;

                            self.set_fp_flags(value);

                            num_cycles = 10;
                        }
                        OPCODE_BITS_SUB_OP_CVT_WS => {
                            let value = (self.reg_gpr(reg1) as i32) as f32;
                            self.set_reg_gpr_float(reg2, value);

                            self.set_fp_flags(value);

                            num_cycles = 16;
                        }
                        OPCODE_BITS_SUB_OP_CVT_SW => {
                            let value = (self.reg_gpr_float(reg1).round() as i32) as u32;
                            self.set_reg_gpr(reg2, value);

                            self.psw_overflow = false;
                            self.set_zero_sign_flags(value);

                            num_cycles = 14;
                        }
                        OPCODE_BITS_SUB_OP_ADDF_S => {
                            let lhs = self.reg_gpr_float(reg2);
                            let rhs = self.reg_gpr_float(reg1);
                            let value = lhs + rhs;
                            self.set_reg_gpr_float(reg2, value);

                            self.set_fp_flags(value);

                            num_cycles = 28;
                        }
                        OPCODE_BITS_SUB_OP_SUBF_S => {
                            let lhs = self.reg_gpr_float(reg2);
                            let rhs = self.reg_gpr_float(reg1);
                            let value = lhs - rhs;
                            self.set_reg_gpr_float(reg2, value);

                            self.set_fp_flags(value);

                            num_cycles = 28;
                        }
                        OPCODE_BITS_SUB_OP_MULF_S => {
                            let lhs = self.reg_gpr_float(reg2);
                            let rhs = self.reg_gpr_float(reg1);
                            let value = lhs * rhs;
                            self.set_reg_gpr_float(reg2, value);

                            self.set_fp_flags(value);

                            num_cycles = 30;
                        }
                        OPCODE_BITS_SUB_OP_DIVF_S => {
                            let lhs = self.reg_gpr_float(reg2);
                            let rhs = self.reg_gpr_float(reg1);
                            let value = lhs / rhs;
                            self.set_reg_gpr_float(reg2, value);

                            self.set_fp_flags(value);

                            num_cycles = 44;
                        }
                        OPCODE_BITS_SUB_OP_XB => {
                            let original = self.reg_gpr(reg2);
                            let value = (original & 0xffff0000) | ((original & 0x0000ff00) >> 8) | ((original & 0x000000ff) << 8);
                            self.set_reg_gpr(reg2, value);

                            num_cycles = 6;
                        }
                        OPCODE_BITS_SUB_OP_XH => {
                            let original = self.reg_gpr(reg2);
                            let value = (original >> 16) | ((original & 0xffff) << 16);
                            self.set_reg_gpr(reg2, value);
                        }
                        OPCODE_BITS_SUB_OP_REV => {
                            let original = self.reg_gpr(reg1);
                            let mut value: u32 = 0;
                            for x in 0..32 {
                                value = (value << 1) | ((original >> x) & 0x01);
                            }
                            self.set_reg_gpr(reg2, value);

                            num_cycles = 22;
                        }
                        OPCODE_BITS_SUB_OP_TRNC_SW => {
                            let value = (self.reg_gpr_float(reg1).trunc() as i32) as u32;
                            self.set_reg_gpr(reg2, value);

                            self.psw_overflow = false;
                            self.set_zero_sign_flags(value);

                            num_cycles = 14;
                        }
                        OPCODE_BITS_SUB_OP_MPYHW => {
                            let lhs = self.reg_gpr(reg2) as i32;
                            let rhs = ((self.reg_gpr(reg1) as i32) << 15) >> 15;
                            let value = (lhs * rhs) as u32;
                            self.set_reg_gpr(reg2, value);

                            num_cycles = 9;
                        }
                        _ => panic!("Unrecognized subop bits: {:06b}", subop_bits)
                    }
                }
                _ => panic!("Unrecognized opcode bits: {:06b} (halfword: 0b{:016b})", opcode_bits, first_halfword),
            }
        }

        self.reg_pc = next_pc;

        trace_add!(self, TraceEntry::Pc(original_pc, self.reg_pc));
        trace_add!(self, TraceEntry::CpuCycles(num_cycles));
        #[cfg(feature = "cpu-trace")]
        self.trace_post_exec_data(interconnect);

        (num_cycles, trigger_watchpoint)
    }

    #[cfg(feature = "cpu-trace")]
    fn trace_post_exec_data(&mut self, interconnect: &mut Interconnect) {
        if self.trace_enabled {
            for i in 0..self.trace_entries.len() {
                let mut trace_entry = self.trace_entries[i];
                match trace_entry {
                    TraceEntry::MemWriteByte(addr, _, _, ref mut post_data) => *post_data = interconnect.read_byte(addr),
                    TraceEntry::MemWriteHalfword(addr, _, _, ref mut post_data) => *post_data = interconnect.read_halfword(addr),
                    TraceEntry::MemWriteWord(addr, _, _, ref mut post_data) => *post_data = (interconnect.read_halfword(addr) as u32) | ((interconnect.read_halfword(addr + 2) as u32) << 16),
                    TraceEntry::Psw(_, ref mut post_data) => *post_data = self.reg_psw(),
                    TraceEntry::SysRegWrite(reg, _, _, ref mut post_data) => {
                        match reg {
                            OPCODE_SYSTEM_REGISTER_ID_EIPC => *post_data = self.reg_eipc,
                            OPCODE_SYSTEM_REGISTER_ID_EIPSW => *post_data = self.reg_eipsw,
                            OPCODE_SYSTEM_REGISTER_ID_ECR => *post_data = self.reg_ecr as u32,
                            OPCODE_SYSTEM_REGISTER_ID_PSW => *post_data = self.reg_psw(),
                            OPCODE_SYSTEM_REGISTER_ID_CHCW => *post_data = self.reg_chcw(),
                            _ => {},
                        };
                    },
                    _ => {},
                }
                self.trace_entries[i] = trace_entry;
            }
        }
    }

    fn check_watchpoints(&self, addr: u32) -> bool {
        self.watchpoints.len() != 0 && self.watchpoints.contains(&addr)
    }

    fn add(&mut self, lhs: u32, rhs: u32, reg2: usize) {
        let (res, carry) = lhs.overflowing_add(rhs);
        self.set_reg_gpr(reg2, res);
        self.set_zero_sign_flags(res);
        self.psw_overflow = ((!(lhs ^ rhs) & (rhs ^ res)) & 0x80000000) != 0;
        self.psw_carry = carry;
    }

    fn sub_and_set_flags(&mut self, lhs: u32, rhs: u32) -> u32 {
        let (res, carry) = lhs.overflowing_sub(rhs);
        self.set_zero_sign_flags(res);
        self.psw_overflow = (((lhs ^ rhs) & !(rhs ^ res)) & 0x80000000) != 0;
        self.psw_carry = carry;
        res
    }

    fn shl_and_set_flags(&mut self, lhs: u32, rhs: u32) -> u32 {
        let mut res = lhs;
        let mut carry = false;
        let shift = (rhs as usize) & 0x1f;
        for _ in 0..shift {
            carry = (res & 0x80000000) != 0;
            res <<= 1;
        }
        self.set_zero_sign_flags(res);
        self.psw_overflow = false;
        self.psw_carry = carry;
        res
    }

    fn shr_and_set_flags(&mut self, lhs: u32, rhs: u32) -> u32 {
        let mut res = lhs;
        let mut carry = false;
        let shift = (rhs as usize) & 0x1f;
        for _ in 0..shift {
            carry = (res & 0x00000001) != 0;
            res >>= 1;
        }
        self.set_zero_sign_flags(res);
        self.psw_overflow = false;
        self.psw_carry = carry;
        res
    }

    fn sar_and_set_flags(&mut self, lhs: u32, rhs: u32) -> u32 {
        let mut res = lhs;
        let mut carry = false;
        let shift = (rhs as usize) & 0x1f;
        for _ in 0..shift {
            let sign = res & 0x80000000;
            carry = (res & 0x00000001) != 0;
            res = sign | (res >> 1);
        }
        self.set_zero_sign_flags(res);
        self.psw_overflow = false;
        self.psw_carry = carry;
        res
    }

    fn set_zero_sign_flags(&mut self, value: u32) {
        self.psw_zero = value == 0;
        self.psw_sign = (value & 0x80000000) != 0;
    }

    fn set_fp_flags(&mut self, value: f32) {
        self.psw_carry = value.is_sign_negative();
        self.psw_overflow = false;
        self.psw_sign = self.psw_carry;
        self.psw_zero = value == 0.0;
    }

    pub fn request_interrupt(&mut self, exception_code: u16) {
        if self.psw_nmi_pending || self.psw_exception_pending || self.psw_interrupt_disable {
            return;
        }

        self.enter_exception(exception_code);
    }

    fn enter_exception(&mut self, exception_code: u16) {
        logln!(Log::Cpu, "Entering exception (code: 0x{:04x})", exception_code);
        self.reg_eipc = self.reg_pc;
        self.reg_eipsw = self.reg_psw();
        self.reg_ecr = exception_code;
        self.psw_exception_pending = true;
        self.reg_pc = 0xffff0000 | (exception_code as u32);
    }

    fn return_from_exception(&mut self) -> u32 {
        logln!(Log::Cpu, "Returning from exception (code: 0x{:04x})", self.reg_ecr);
        let psw = self.reg_eipsw;
        self.set_reg_psw(psw);
        self.reg_eipc
    }


    fn read_byte(&mut self, interconnect: &mut Interconnect, addr: u32) -> u8 {
        let value = interconnect.read_byte(addr);
        trace_add!(self, TraceEntry::MemReadByte(addr, value));
        value
    }

    fn read_halfword(&mut self, interconnect: &mut Interconnect, addr: u32) -> u16 {
        let value = interconnect.read_halfword(addr);
        trace_add!(self, TraceEntry::MemReadHalfword(addr, value));
        value
    }

    fn read_word(&mut self, interconnect: &mut Interconnect, addr: u32) -> u32 {
        let value = (interconnect.read_halfword(addr) as u32) | ((interconnect.read_halfword(addr + 2) as u32) << 16);
        trace_add!(self, TraceEntry::MemReadWord(addr, value));
        value
    }

    fn write_byte(&mut self, interconnect: &mut Interconnect, addr: u32, value: u8) {
        trace_add!(self, TraceEntry::MemWriteByte(addr, interconnect.read_byte(addr), value, 0));
        interconnect.write_byte(addr, value);
    }

    fn write_halfword(&mut self, interconnect: &mut Interconnect, addr: u32, value: u16) {
        trace_add!(self, TraceEntry::MemWriteHalfword(addr, interconnect.read_halfword(addr), value, 0));
        interconnect.write_halfword(addr, value);
    }

    fn write_word(&mut self, interconnect: &mut Interconnect, addr: u32, value: u32) {
        trace_add!(self, TraceEntry::MemWriteWord(addr, (interconnect.read_halfword(addr) as u32) | ((interconnect.read_halfword(addr + 2) as u32) << 16), value, 0));
        interconnect.write_halfword(addr, value as _);
        interconnect.write_halfword(addr + 2, (value >> 16) as _);
    }
}

fn sign_extend_imm5(imm5: usize) -> u32 {
    (((imm5 as i32) << 27) >> 27) as _
}