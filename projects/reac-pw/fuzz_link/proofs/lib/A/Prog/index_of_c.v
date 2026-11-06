(* index_of (fuzz_link.c:112-118) on image A (fuzz_link.asan 0x86784, 264 bytes; listing
   (internal path) (internal record, sha256 3b45a4408bf6)): the index of an interface name in
   the fake kernel's table, or 0. a0 = name. The plain contract is lib/Prog/index_of_c.v; this file states the SAME
   link_spec result (`index_of tab nm`) in link_amem.v's `aleaf` form.

   ONE STATEMENT, TWO ENTRIES: fuzz_if_nametoindex (0x826cc, 264 bytes) has the same instruction
   words as index_of at every offset but the pc-relative ones (+0x2c/+0x30 auipc/addi, +0x44/+0x48 auipc/ld, the
   three jal at +0x80, +0xfc, +0x104), and those resolve to the same targets (g_nl 0x5dcac0, .got 0xa19d0,
   wrapper_strcmp 0x4304c, errpath_load4 0x5a45c, errpath_load8 0x5a4fc): the two listings differ in no other line.
   So the statement is `index_of_acontract_at pc`, and `index_of_acontract` is it at index_of's entry.

   The image-A code, in order:
     +0x00..+0x24  push an 80-byte frame; save ra, s0..s7               (before the first test)
     +0x28..+0x38  s4 := LA_G_NL (auipc/addi); s3 := lw (g_nl + 0x42670) = nk_n_if; a constant offset into a
                   global, so the instrumentation leaves it unchecked
     +0x3c  blez s3 -> +0xa4                                            (no interface: answer 0)
     +0x44..+0x50  s5 := the shadow base, loaded through the .got cell 0xa19d0 (LA_GOT_SHADOW, which holds
                   LA_SHADOW_CELL = 0xaa438, which holds the base)
     +0x4c..+0x6c  s6 := g_nl + 0x422b0 (NK_IF_NAME = 271024), s7 := its shadow byte address;
                   s4 := g_nl + 0x42530 (NK_IF_INDEX = 271664); s2 := s6, s1 := s4
     loop, i = 0 .. n_if - 1:
     +0x70..+0x74, +0x100..+0x104  the instrumented check of the 8-byte load of if_name[i]: shadow byte (lbu) <> 0
                   goes to errpath_load8 (0x5a4fc) at once, so it passes only when the shadow byte is 0
     +0x78  ld a0, 0(s6) = if_name[i];  +0x7c..+0x80  wrapper_strcmp(if_name[i], name) (0x4304c)
     +0x84  beqz a0 -> +0xac                                            (hit)
     +0x88..+0xa0  next i; loop while the count s3 is not 0
     +0xa4  a0 := 0; j +0xc0
     +0xac..+0xb8, +0xec..+0xfc  the instrumented check of the 4-byte load of if_index[i]: shadow byte s = 0
                   passes; else (a & 7) + 3 < s passes; else errpath_load4 (0x5a45c)
     +0xbc  lw a0, 0(s4) = if_index[i] (sign-extended)
     +0xc0..+0xe8  restore, pop, ret.

   Which instruction needs which premise:
   - the journal, gp/tp, ret_ok (apre): the frame stores +0x04..+0x24 (inside [sp - K, sp)); each strcmp call
     takes the premises of the strcmp wrapper's contract at sp' = sp - 80, which the walk derives from the journal.
     That contract on link is lib/A/Rt/RtString.v `astrcmp_realizes` (the libc port of plugin-hostd/
     fuzz_command's, on the form branch since f961453c8093; pcap's Reusable/AStrcmpDef.v is the same statement
     without the tail clause); no journal lift of it exists yet (pcap's aj_strcmp_at, A/Prog/PcapFuzzFopen.v:109-125,
     is the model); +0xe8 ret.
   - K = 80 + 2 * ESTACK = 8272: the 80-byte frame, then the strcmp wrapper's window [sp' - 2 * ESTACK, sp') (astrcmp_realizes:
     `ecall_pre_stk (2 * ESTACK)`, each string's `aread_ok (2 * ESTACK)` outside it). No realignment. The plain K (48) does
     not carry over; link-a/form/FORM.md (internal record, sha256 13aeff774164) section 5's 4176 assumed ESTACK for strcmp.
   - `anlk_at m LA_G_NL bs`: +0x38 reads nk_n_if, +0x78 reads if_name[i], +0xbc reads if_index[i].
   - `aiftab_at m LA_G_NL bs tab`: the table the loop walks: n_if = length tab <= 80, each if_name[i] a non-NULL
     pointer to a C string, each if_index[i] in [0, 2^31) (so the sign-extending `lw` at +0xbc is the value).
   - `range_addressable (ard m) SHADOW_OFF (LA_G_NL + NK_IF_NAME) (8 * length tab)`: the check +0x70..+0x74 of
     if_name[i] for every i < n_if (the array starts on an 8-byte boundary, so each slot is a whole granule and
     range_addressable gives its shadow byte 0, YG0v.v check_passes_whole).
   - `range_addressable (ard m) SHADOW_OFF (LA_G_NL + NK_IF_INDEX) (4 * length tab)`: the check +0xac..+0xb8 of
     if_index[i] at the hit (YG0v.v check_passes_lb).
   - name: `aarg regs 0 <> 0`, `acstr_at m name nm` (strcmp's second string, its `astr_at`), and the facts
     astrcmp_realizes asks of each string (`astrcmp_arg`): `0 < name`; `aread_ok (2 * ESTACK) name (|nm| + 1)`,
     i.e. `|nm| + 1 < 2 ^ 32`, `amem_range name (|nm| + 1)` (which gives `name + |nm| + 1 <= 2 ^ 63`),
     `range_addressable (ard m) SHADOW_OFF name (|nm| + 1)` and its `shadow_hull_vis` (the interceptor's READ_RANGE
     checks), the bytes readable (acstr_at) and outside the window (`apart_frame regs K name (|nm| + 1)`: outside
     this frame and the wrapper's window; the plain lesson: a pointer argument is separated from everything the
     function writes); and `atail_vis (name + |nm|)`: the bytes after the NUL up to the end of its 8-byte granule
     are visible (musl's strcmp under the interceptor may read word-wise).
   - each table string p of entry i (strcmp's first string, read for every i < n_if): the same facts over [p, p + |n2| + 1).
     They are stated for the p that `au64_at` reads only when `0 <= p < 2^64`: `au64_at` fixes the value only modulo 2^64
     (link-a/plan/CONTRACTS.md (internal record, sha256 5cd783c633c3) 6a class 2), and the positive claims (amem_range,
     range_addressable, shadow_hull_vis) would be false of p + 2^64; aiftab_at's own `acstr_at m p n2` puts its p in that range.
   The write set is empty: the function writes only its frame. EV = 0 (no allocator event), SIDE = [] (no
   frame_alloc).
   The read set (`aleaf_rd`, the form change of 2026-10-30): the bytes read through the pointer argument,
   the name and its NUL [name, name + |nm|]. The interface-table strings are read through pointers loaded from g_nl,
   not through an argument, and index_of has no allocating callee that could hand their bytes out during the call,
   so they stay out of Rd (a caller with an allocating callee before its index_of call places them in its own Rd).
   The text of Rd is word for word fuzz_if_nametoindex's, so the two stay one statement.

   What does NOT carry over from the plain text:
   - `frame_apart_gnl regs 48` (link-a/form/FORM.md (internal record, sha256 13aeff774164) section 1a): on image A the
     window is on the real stack above alloc_ceiling (the journal's `astk_ok`, YCbq.v:330-332) and g_nl is an image byte.
   Nothing of the plain Post is false of image A: the plain Post is the register result only, and the returning
   path's memory change (the frame) is what `akept` allows.
   Released proofs (rule 24): none of index_of (link-a/index/SUMMARY.md (internal record, sha256 58ab2c29f038): the hits
   are generic identifiers of unrelated units).

   Satisfiability witness (op_read of "nl0" as the first op, the index_of call LLVMFuzzerTestOneInput 0x836d8, the
   refusal test after check_socket; run R of lib/A/Prog/help_witness.v): a0 = LA_G_NAMES ("nl0"); g_nl after
   interfaces() and one exchange: n_if = 64, if_name[j] = &g_names[k] and if_index[j] = k + 2 for the 60 k < 64 with
   k % 16 <> 15, then odd[1..4] = 0x20fe0 "enp131s0.33", 0x21000 "eth0", 0x21020 "wlan0", 0x21040 "veth-box" (the
   data words at LA_ODD + 8 .. + 32 of the unstripped twin's .data.rel.ro, pyelftools 0.33) with indices 101..104;
   g_names' 64 slots "nl<k>"; the shadow with the run's values (g_nl's and g_names' granules 0; each odd string's
   granules from its asan_globals descriptor, its redzone f9); sp = 0x7fffffffee60. The closed lemma
   `index_of_apre_sat` is in lib/A/Prog/help_witness.v (the 64 entries by one decidable check and one soundness
   lemma).
   Proves no function (kind: statement text). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YI16 YM05 YG0v YG0f YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem.
Import ListNotations.
Local Open Scope Z_scope.

Definition INDEX_OF_A : Z := 0x86784.
Lemma INDEX_OF_A_is_entry : INDEX_OF_A = LA_index_of. Proof. reflexivity. Qed.

(* the stack bound on image A: the 80-byte frame and the strcmp wrapper's window *)
Definition INDEX_OF_AFRAME : Z := 80.
Definition INDEX_OF_AK : Z := INDEX_OF_AFRAME + 2 * ESTACK.
Lemma INDEX_OF_AK_val : INDEX_OF_AK = 8272. Proof. reflexivity. Qed.

(* the write set: nothing outside the frame *)
Definition index_of_awr (regs : bvmap 5 word) (m : word -> option byte) : list (Z * Z) := [].

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Variable segs : list Segment.
Variables rlo rhi : Z.
Variable B : asyms.

(* the facts the strcmp wrapper's contract (lib/A/Rt/RtString.v astrcmp_realizes) asks of one of its strings s at
   p, beside `astr_at` (the caller's `acstr_at`), in a function whose stack bound K covers the wrapper's window
   [sp' - 2 * ESTACK, sp'): `0 < p`, `aread_ok (2 * ESTACK) p (|s| + 1)` and `atail_vis (p + |s|)` (RtDefs.v) *)
Definition astrcmp_arg (regs : bvmap 5 word) (K : Z) (m : word -> option byte) (p : Z) (s : list byte) : Prop :=
  0 < p /\ Z.of_nat (length s) + 1 < 2 ^ 32 /\ amem_range p (Z.of_nat (length s) + 1)
  /\ range_addressable (ard segs m) SHADOW_OFF p (Z.of_nat (length s) + 1)
  /\ shadow_hull_vis (ard segs m) p (Z.of_nat (length s) + 1)
  /\ apart_frame regs K p (Z.of_nat (length s) + 1)
  /\ (forall a, p + Z.of_nat (length s) < a < p + Z.of_nat (length s) - (p + Z.of_nat (length s)) mod 8 + 8 ->
        ard segs m a <> None).

Definition index_of_apre (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  exists bs tab nm,
    anlk_at segs m LA_G_NL bs /\ aiftab_at segs m LA_G_NL bs tab
    /\ range_addressable (ard segs m) SHADOW_OFF (LA_G_NL + NK_IF_NAME) (8 * Z.of_nat (length tab))
    /\ range_addressable (ard segs m) SHADOW_OFF (LA_G_NL + NK_IF_INDEX) (4 * Z.of_nat (length tab))
    /\ aarg regs 0 <> 0 /\ acstr_at segs m (aarg regs 0) nm
    /\ astrcmp_arg regs INDEX_OF_AK m (aarg regs 0) nm
    /\ (forall i n2 ix p, nth_error tab i = Some (n2, ix) ->
          au64_at segs m (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p -> 0 <= p < 2 ^ 64 ->
          astrcmp_arg regs INDEX_OF_AK m p n2).

(* the read set: the name and its NUL *)
Definition index_of_ard (regs : bvmap 5 word) (m : word -> option byte) (a : Z) : Prop :=
  exists s, acstr_at segs m (aarg regs 0) s /\ aarg regs 0 <= a <= aarg regs 0 + Z.of_nat (length s).

Definition index_of_apost (regs : bvmap 5 word) (m : word -> option byte)
    (regs' : bvmap 5 word) (m' : word -> option byte) : Prop :=
  forall bs tab nm, anlk_at segs m LA_G_NL bs -> aiftab_at segs m LA_G_NL bs tab ->
    acstr_at segs m (aarg regs 0) nm ->
    getr regs' 10 = w64 (index_of tab nm).

Definition index_of_acontract_at (pc : Z) : Prop :=
  aleaf_rd SK segs rlo rhi B pc INDEX_OF_AK 0 [] index_of_apre index_of_ard index_of_awr index_of_apost.

Definition index_of_acontract : Prop := index_of_acontract_at INDEX_OF_A.

End c.
