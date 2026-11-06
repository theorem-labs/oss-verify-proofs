"""contracts.py -- the contracts the lui settlement cites (luiclass.py). Pinned sources: compiler-rt = llvm-project
87f0227cb60147a26a1eeb4fb06e3b505e9c7261 compiler-rt/lib/; musl = git.musl-libc.org musl f21a96538f78fa8e2040831b4209b35f2fb581da.
  CONTRACT          (callee linkage name, argument register) -> (class, the parameter, citation): class 'i' when the
                    pinned source's declaration / contract states that the parameter is a byte count, length, count,
                    size, flags, mode, prot or alignment; 'i-b' for CheckFailed's v1 / v2, which CheckFailed only prints.
  SYSCALL_CONTRACT  (syscall name, argument register) -> ('i', the parameter, citation)
  RETURNS           function -> citation: it returns an integer that is not an address by its meaning (class ii)
  STORES            (function, store pc offset) -> citation: the integer, non-address field it writes (class iv)
  ARGBEYOND         (callee, register) -> (class, citation): a register a callee reads beyond its declared parameters
                    (a variadic argument), settled by what the callee does with it"""

CRT = 'compiler-rt@87f0227cb601 '
MUSL = 'musl@f21a96538f78 '
CONTRACT = {
    ('_ZN11__sanitizer9MmapOrDieEmPKcb', 'a0'): ('i', 'uptr size (byte count)', CRT + 'sanitizer_common/sanitizer_common.h:90 '
        '`void *MmapOrDie(uptr size, const char *mem_type, bool raw_report = false);`'),
    ('_ZN11__sanitizer18MmapNoReserveOrDieEmPKc', 'a0'): ('i', 'uptr size (byte count)', CRT + 'sanitizer_common/'
        'sanitizer_common.h:103 `void *MmapNoReserveOrDie(uptr size, const char *mem_type);`'),
    ('_ZN11__sanitizer28MmapAlignedOrDieOnFatalErrorEmmPKc', 'a0'): ('i', 'uptr size (byte count)', CRT + 'sanitizer_common/'
        'sanitizer_common.h:113-114 `void *MmapAlignedOrDieOnFatalError(uptr size, uptr alignment, const char *mem_type);`'),
    ('_ZN11__sanitizer28MmapAlignedOrDieOnFatalErrorEmmPKc', 'a1'): ('i', 'uptr alignment', CRT + 'sanitizer_common/'
        'sanitizer_common.h:113-114 `void *MmapAlignedOrDieOnFatalError(uptr size, uptr alignment, const char *mem_type);`'),
    ('_ZN11__sanitizer20ReservedAddressRange8MapOrDieEmmPKc', 'a2'): ('i', 'uptr size (byte count; a0 this, a1 fixed_addr)',
        CRT + 'sanitizer_common/sanitizer_common.h:187 `uptr MapOrDie(uptr fixed_addr, uptr size, const char *name = nullptr);`'),
    ('_ZN11__sanitizer20ReservedAddressRange3MapEmmPKc', 'a2'): ('i', 'uptr size (byte count; a0 this, a1 fixed_addr)',
        CRT + 'sanitizer_common/sanitizer_common.h:186 `uptr Map(uptr fixed_addr, uptr size, const char *name = nullptr);`'),
    ('_ZN11__sanitizer16ReadFileToBufferEPKcPPcPmS4_mPi', 'a4'): ('i', 'uptr max_len (byte length)', CRT + 'sanitizer_common/'
        'sanitizer_common.h:781-783 `bool ReadFileToBuffer(const char *file_name, char **buff, uptr *buff_size, uptr *read_len, '
        'uptr max_len = kDefaultFileMaxSize, error_t *errno_p = nullptr);`'),
    ('_ZN11__sanitizer13internal_mmapEPvmiiiy', 'a1'): ('i', 'uptr length', CRT + 'sanitizer_common/sanitizer_posix.h:40-41 '
        '`uptr internal_mmap(void *addr, uptr length, int prot, int flags, int fd, u64 offset);`'),
    ('_ZN11__sanitizer13internal_mmapEPvmiiiy', 'a2'): ('i', 'int prot', CRT + 'sanitizer_common/sanitizer_posix.h:40-41 '
        '`uptr internal_mmap(void *addr, uptr length, int prot, int flags, int fd, u64 offset);`'),
    ('_ZN11__sanitizer13internal_mmapEPvmiiiy', 'a3'): ('i', 'int flags', CRT + 'sanitizer_common/sanitizer_posix.h:40-41 '
        '`uptr internal_mmap(void *addr, uptr length, int prot, int flags, int fd, u64 offset);`'),
    ('_ZN11__sanitizer13internal_openEPKcij', 'a1'): ('i', 'int flags', CRT + 'sanitizer_common/sanitizer_posix.h:30 '
        '`uptr internal_open(const char *filename, int flags, u32 mode);`'),
    ('_ZN11__sanitizer13internal_openEPKcij', 'a2'): ('i', 'u32 mode', CRT + 'sanitizer_common/sanitizer_posix.h:30 '
        '`uptr internal_open(const char *filename, int flags, u32 mode);`'),
    ('__sanitizer_internal_memset', 'a2'): ('i', 'uptr n (byte count)', CRT + 'sanitizer_common/sanitizer_libc.h:35-36 '
        '`void *__sanitizer_internal_memset(void *s, int c, uptr n);` (memset: n bytes)'),
    ('_ZN6__asan12PoisonShadowEmmh', 'a1'): ('i', 'uptr size (byte count)', CRT + 'asan/asan_poisoning.h:26-27 '
        '"Poisons the shadow memory for "size" bytes starting from "addr"." `void PoisonShadow(uptr addr, uptr size, u8 value);`'),
    ('_ZN11__sanitizer9Semaphore4PostEj', 'a1'): ('i', 'u32 count (a0 this)', CRT + 'sanitizer_common/sanitizer_mutex.h:73 '
        '`void Post(u32 count = 1);`'),
    ('_ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE20EnsureFreeArraySpaceEPNS5_10RegionInfoEmm',
     'a3'): ('i', 'uptr num_freed_chunks (count; a0 this, a1 region, a2 region_beg)', CRT + 'sanitizer_common/'
        'sanitizer_allocator_primary64.h:741-743 `bool EnsureFreeArraySpace(RegionInfo *region, uptr region_beg, uptr '
        'num_freed_chunks) { uptr needed_space = num_freed_chunks * sizeof(CompactPtrT);`'),
    ('_ZN11__sanitizer11CheckFailedEPKciS1_yy', 'a3'): ('i-b', 'u64 v1', CRT + 'sanitizer_common/sanitizer_termination.cpp:'
        '67-89 `void NORETURN CheckFailed(const char *file, int line, const char *cond, u64 v1, u64 v2)`: v1 and v2 '
        'appear only in the Printf of lines 70-72 `"%s: CHECK failed: %s:%d \\"%s\\" (0x%zx, 0x%zx) (tid=%u)\\n", ..., '
        '(uptr)v1, (uptr)v2, tid` (printed as numbers, never dereferenced)'),
    ('_ZN11__sanitizer11CheckFailedEPKciS1_yy', 'a4'): ('i-b', 'u64 v2', CRT + 'sanitizer_common/sanitizer_termination.cpp:'
        '67-89 `void NORETURN CheckFailed(const char *file, int line, const char *cond, u64 v1, u64 v2)`: v1 and v2 '
        'appear only in the Printf of lines 70-72 `"%s: CHECK failed: %s:%d \\"%s\\" (0x%zx, 0x%zx) (tid=%u)\\n", ..., '
        '(uptr)v1, (uptr)v2, tid` (printed as numbers, never dereferenced)'),
    ('open', 'a1'): ('i', 'int flags', MUSL + 'src/fcntl/open.c:5 `int open(const char *filename, int flags, ...)`'),
    ('socket', 'a1'): ('i', 'int type (socket type and its SOCK_* flags)', MUSL + 'src/network/socket.c:6 '
        '`int socket(int domain, int type, int protocol)`'),
}

RETURNS = {
    'sysconf': MUSL + 'src/conf/sysconf.c:28 `long sysconf(int name)` returns the value of a system variable, e.g. lines '
               '190-193 `case VER & 255: return _POSIX_VERSION; case JT_ARG_MAX & 255: return ARG_MAX;`: a number, not '
               'an address',
    '__tm_to_secs': MUSL + 'src/time/__tm_to_secs.c:3 `long long __tm_to_secs(const struct tm *tm)`, line 19 '
                    '`t += 86400LL * (tm->tm_mday-1);`: a count of seconds, not an address',
    '__year_to_secs': MUSL + 'src/time/__year_to_secs.c:1 `long long __year_to_secs(long long year, int *is_leap)`, '
                      'line 10 `return 31536000*(y-70) + 86400*leaps;` and line 46 `return (year-100) * 31536000LL + '
                      'leaps * 86400LL + 946684800 + 86400;`: a count of seconds, not an address',
}

# indirect calls: a callee entered through a function pointer reads only the argument registers of its type. RISC-V
# psABI (riscv-non-isa/riscv-elf-psabi-doc at master 9b2767e2a8851709608c4e1452998ad232d6278b, 2026-10-27; riscv-cc.adoc
# last changed at riscv-non-isa/riscv-elf-psabi-doc 1ac24703c0a6, blob 9d7a7b69f2f6): section "Integer Register Convention" lines 21-25 `x5 - x7 | t0 - t2 |
# Temporary registers`, `x10 - x17 | a0 - a7 | Argument registers`, `x28 - x31 | t3 - t6 | Temporary registers`; section
# "Integer Calling Convention" lines 178-179 "The base integer calling convention provides eight argument registers,
# a0-a7". So t0-t6 are never read by an indirect callee (and are clobbered by the call), and aN with N >= the pointer
# type's arity is not.
PSABI = ('RISC-V psABI riscv-elf-psabi-doc@9b2767e2a885 riscv-cc.adoc "Integer Register Convention" lines 21-25, '
         '"Integer Calling Convention" lines 178-179 (t0-t6 temporaries, a0-a7 the argument registers)')
# REAL(x): `typedef ret_type (*FUNC_TYPE(func))(__VA_ARGS__)` with the interceptor's own parameters
# (compiler-rt interception/interception.h:255-262 DECLARE_REAL / PTR_TO_REAL); the cell is __interception::real_<x>
SCI = CRT + 'sanitizer_common/sanitizer_common_interceptors.inc:'
AMI = CRT + 'asan/asan_interceptors_memintrinsics.cpp:'
REAL_ARITY = {
    'strlen': (1, SCI + '414 `INTERCEPTOR(SIZE_T, strlen, const char *s)`, 423 `REAL(strlen)(s)`'),
    'read': (3, SCI + '1004 `INTERCEPTOR(SSIZE_T, read, int fd, void *ptr, SIZE_T count)`, 1011'),
    'clock_gettime': (2, SCI + '2225 `INTERCEPTOR(int, clock_gettime, u32 clk_id, void *tp)`, 2231 / 2243'),
    'fflush': (1, SCI + '6408 `INTERCEPTOR(int, fflush, __sanitizer_FILE *fp)`, 6413 `REAL(fflush)(fp)`'),
    'fclose': (1, SCI + '6427 `INTERCEPTOR(int, fclose, __sanitizer_FILE *fp)`, 6434 `REAL(fclose)(fp)`'),
    'memcpy': (3, AMI + '28-39 ASAN_MEMCPY_IMPL `return REAL(memcpy)(to, from, size);`'),
    'memset': (3, AMI + '43-50 ASAN_MEMSET_IMPL `return REAL(memset)(block, c, size);`'),
}
# other function pointers, by call site (function, offset): (arity, citation)
CALLBACK_ARITY = {
    ('_ZN11__sanitizer3DieEv', 0x60): (0, CRT + 'sanitizer_common/sanitizer_common.h:354 `typedef void (*DieCallbackType)(void);`, '
                                         'sanitizer_termination.cpp:20 / 50-56 `UserDieCallback(); .. InternalDieCallbacks[i]();`'),
    ('_ZN11__sanitizer3DieEv', 0x78): (0, CRT + 'sanitizer_common/sanitizer_common.h:354 `typedef void (*DieCallbackType)(void);`, '
                                         'sanitizer_termination.cpp:20 / 50-56 `UserDieCallback(); .. InternalDieCallbacks[i]();`'),
    ('_ZN11__sanitizer14RunMallocHooksEPvm', 0x38): (2, CRT + 'sanitizer_common/sanitizer_common.cpp:334 `void '
                                                    '(*malloc_hook)(const void *, uptr);`, 343-346 `hook(ptr, size);`'),
    ('_ZN11__sanitizer14ThreadRegistry23FindThreadContextLockedEPFbPNS_17ThreadContextBaseEPvES3_', 0x74):
        (2, CRT + 'sanitizer_common/sanitizer_thread_registry.h:121 `typedef bool (*FindThreadCallback)(ThreadContextBase '
            '*tctx, void *arg);`'),
}

S64PFA = ('_ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE17PopulateFreeArrayEPNS_14'
          'AllocatorStatsEmPNS5_10RegionInfoEm')
S64EFS = ('_ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE20EnsureFreeArraySpaceEPNS5_'
          '10RegionInfoEmm')
S32PFL = ('_ZN11__sanitizer20SizeClassAllocator32INS_4AP32EE16PopulateFreeListEPNS_14AllocatorStatsEPNS_30SizeClassAllocator'
          '32LocalCacheIS2_EEPNS2_13SizeClassInfoEm')
S32AB = ('_ZN11__sanitizer20SizeClassAllocator32INS_4AP32EE13AllocateBatchEPNS_14AllocatorStatsEPNS_30SizeClassAllocator32'
         'LocalCacheIS2_EEm')
S32DB = '_ZN11__sanitizer20SizeClassAllocator32INS_4AP32EE15DeallocateBatchEPNS_14AllocatorStatsEmPNS2_13TransferBatchE'
P64 = CRT + 'sanitizer_common/sanitizer_allocator_primary64.h:'
MAPPED = (CRT + 'sanitizer_common/sanitizer_allocator_stats.h:18-19 / 47-49 `AllocatorStats *next_; AllocatorStats *prev_; '
          'atomic_uintptr_t stats_[AllocatorStatCount];`: stats_[AllocatorStatMapped] at +0x18, a byte count')
ASANMAPPED = (CRT + 'asan/asan_stats.h:24-37 `struct AsanStats { uptr mallocs; .. uptr mmaps; uptr mmaped;`: mmaped is the '
              '11th uptr, +0x50, a byte count; asan/asan_allocator.cpp:286-288 `AsanStats &thread_stats = '
              'GetCurrentThreadStats(); thread_stats.mmaps++; thread_stats.mmaped += size;`')
SPIN = (CRT + 'sanitizer_common/sanitizer_mutex.h:35-36 / 48 StaticSpinMutex `atomic_exchange(&state_, 1, '
        'memory_order_acquire)`, `atomic_uint8_t state_;`, emulated on the aligned word (andi -4, sllw / xor / and): the '
        'lock byte of SizeClassInfo::mutex (sanitizer_allocator_primary32.h:281-282 `StaticSpinMutex mutex;`), a lock state')
STORES = {
    (S64PFA, 0x154): ASANMAPPED,
    (S64PFA, 0x160): MAPPED + '; ' + P64 + '806 `stat->Add(AllocatorStatMapped, user_map_size);`',
    (S64PFA, 0x170): P64 + '671-677 RegionInfo { Mutex mutex (16 bytes); uptr num_freed_chunks; uptr mapped_free_array; uptr '
                     'allocated_user; uptr allocated_meta; uptr mapped_user; }: +0x30 mapped_user, "Bytes mapped for user '
                     'memory"; line 807 `region->mapped_user += user_map_size;`',
    (S64PFA, 0x1f0): P64 + '673 `uptr num_freed_chunks;  // Number of elements in the freearray.` (+0x10); line 845 '
                     '`region->num_freed_chunks += new_chunks_count;`',
    (S64PFA, 0x1f4): P64 + '675 `uptr allocated_user;  // Bytes allocated for user memory.` (+0x20); line 846 '
                     '`region->allocated_user += new_chunks_count * size;`',
    (S64EFS, 0xd4): ASANMAPPED,
    (S64EFS, 0xdc): P64 + '674 `uptr mapped_free_array;  // Bytes mapped for freearray.` (+0x18); line 753 '
                    '`region->mapped_free_array = new_mapped_free_array;`',
    (S32PFL, 0x70): MAPPED + ' (`addi s5, s5, 0x18 ; amoadd.d zero, s1, (s5)`); ' + CRT + 'sanitizer_common/sanitizer_allocator_'
                    'primary32.h:305 `stat->Add(AllocatorStatMapped, kRegionSize);`',
    (S32AB, 0x64): SPIN,
    (S32DB, 0x5c): SPIN,
    ('_ZN11__sanitizer10StackStore5AllocEmPmS1_', 0x9c): CRT + 'sanitizer_common/sanitizer_stack_store.h:88-91 BlockInfo '
        '`atomic_uint32_t stored_;` "Counter to track store progress"; sanitizer_stack_store.cpp:374-376 `n + '
        'atomic_fetch_add(&stored_, n, memory_order_release) == kBlockSizeFrames` (h:21 kBlockSizeFrames = 0x100000): a '
        'frame count',
    ('_ZN11__sanitizer10StackStore5AllocEmPmS1_', 0xd0): CRT + 'sanitizer_common/sanitizer_stack_store.h:88-91 BlockInfo '
        '`atomic_uint32_t stored_;` "Counter to track store progress"; sanitizer_stack_store.cpp:374-376 `n + '
        'atomic_fetch_add(&stored_, n, memory_order_release) == kBlockSizeFrames` (h:21 kBlockSizeFrames = 0x100000): a '
        'frame count',
    ('_ZN11__sanitizer11AddrHashMapI25CommonInterceptorMetadataLm31051EE7acquireEPNS2_6HandleE', 0x1b8):
        CRT + 'sanitizer_common/sanitizer_mutex.h:327 `atomic_uint64_t state_` of Mutex, 253-263 ReadLock `new_state = '
        '(state + kWaitingReaderInc) & reset_mask;` (357-358 kWaitingReaderInc = 1 << 20 = V): a lock state word',
    ('_ZN6__asan14AsanDeactivateEv', 0x90): CRT + 'asan/asan_allocator.h:34-38 AllocatorOptions { u32 quarantine_size_mb; '
        'u32 thread_local_quarantine_size_kb; u16 min_redzone; u16 max_redzone; }: the 32-bit store at +8 writes '
        'min_redzone = max_redzone = 16 (V = 0x00100010), redzone sizes in bytes; asan/asan_activation.cpp:115-116, 119 '
        '`disabled.min_redzone = Max(16, ..); disabled.max_redzone = disabled.min_redzone; .. ReInitializeAllocator(disabled);`',
    ('_ZN11__sanitizer15internal_usleepEy', 0x38): CRT + 'sanitizer_common/sanitizer_linux.cpp:582-586 `struct timespec ts; '
        'ts.tv_sec = useconds / 1000000; ts.tv_nsec = (useconds % 1000000) * 1000; internal_syscall(SYSCALL(nanosleep), '
        '&ts, &ts);`: tv_nsec, a count of nanoseconds (the struct is handed to the kernel)',
}

ARGBEYOND = {}

# syscalls: the argument register of a syscall (by the syscall's own contract)
SYSCALL_CONTRACT = {
    ('openat', 'a2'): ('i', 'int flags', 'Linux openat(2): `int openat(int dirfd, const char *pathname, int flags, mode_t mode)`; '
                       + MUSL + 'src/time/__map_file.c:10 `int fd = sys_open(pathname, O_RDONLY|O_CLOEXEC|O_NONBLOCK);`'),
}


def lookup(callee, reg):
    return CONTRACT.get((callee, reg))
