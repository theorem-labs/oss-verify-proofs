(* fuzz_if_nametoindex (netlink.h:148-154) on image A (fuzz_link.asan 0x826cc, 264 bytes; listing
   (internal path) (internal record, sha256 c3f31e966607)): the index of an interface
   name in the fake kernel's table, or 0. a0 = name (never NULL at a call site: both callers test `!name || !name[0]`
   first). The plain contract is lib/Prog/index_of_c.v (`fuzz_if_nametoindex_contract := index_of_contract
   FUZZ_IF_NAMETOINDEX`); this file states the SAME link_spec result (`index_of tab nm`) in link_amem.v's `aleaf`
   form.

   ONE STATEMENT, TWO ENTRIES. On image A fuzz_if_nametoindex and index_of (0x86784) have the same
   instruction words at every offset but the pc-relative ones (+0x2c/+0x30 auipc/addi, +0x44/+0x48 auipc/ld, the jal
   at +0x80, +0xfc, +0x104), which resolve to the same targets (g_nl 0x5dcac0, .got 0xa19d0, wrapper_strcmp 0x4304c,
   errpath_load4 0x5a45c, errpath_load8 0x5a4fc) (a diff of the two listings, 2026-10-30). This file
   states the premises and Post of `index_of_apre` / `index_of_apost` (lib/A/Prog/index_of_c.v) word for word,
   under this function's names; the two files were written apart, so this contract could also be stated as
   `index_of_acontract_at FUZZ_IF_NAMETOINDEX_A`.

   The image-A code, in order:
     +0x00..+0x24  push an 80-byte frame; save ra, s0..s7                (before the first test)
     +0x28..+0x38  s4 := LA_G_NL (auipc/addi); s3 := lw (g_nl + 0x42670) = n_if (a constant offset into a global,
                   left unchecked by the instrumentation)
     +0x3c  blez s3 -> +0xa4                                             (no interface: answer 0)
     +0x40  s0 := name;  +0x44..+0x50  s5 := the shadow base, loaded through LA_GOT_SHADOW
     +0x4c..+0x6c  s6 := g_nl + 0x422b0 (NK_IF_NAME), s7 := its shadow byte address; s4 := g_nl + 0x42530
                   (NK_IF_INDEX); s2 := s6, s1 := s4
     loop, i = 0 .. n_if - 1:
     +0x70..+0x74, +0x100..+0x104  the instrumented check of the 8-byte load of if_name[i]: shadow byte (lbu) <> 0
                   goes to errpath_load8 (0x5a4fc) at once
     +0x78  ld a0, 0(s6) = if_name[i];  +0x7c..+0x80  wrapper_strcmp(if_name[i], name) (0x4304c)
     +0x84  beqz a0 -> +0xac                                             (hit)
     +0x88..+0xa0  next i; loop while the count s3 is not 0
     +0xa4  a0 := 0; j +0xc0
     +0xac..+0xb8, +0xec..+0xfc  the instrumented check of the 4-byte load of if_index[i]: shadow byte s = 0 passes;
                   else (a & 7) + 3 < s passes; else errpath_load4 (0x5a45c)
     +0xbc  lw a0, 0(s4) = if_index[i] (sign-extended)
     +0xc0..+0xe8  restore, pop, ret.

   Which instruction needs which premise:
   - the journal, gp/tp, ret_ok (apre): the frame stores +0x04..+0x24; each strcmp call takes the strcmp contract's
     `PRE (2 * ESTACK)` at sp - 80, which the walk derives from the journal (link_ajkit.v aj_gx_ecall_pre; no journal
     lift of the strcmp wrapper itself is on link yet: pcap's aj_strcmp_at, A/Prog/PcapFuzzFopen.v:109-125, and
     link_ajkit.v's aj_gx_strncmp_at are the models); +0xe8 ret.
   - K = 80 + 2 * ESTACK = 8272: the 80-byte frame, then the strcmp wrapper's window [sp' - 2 ESTACK, sp') at
     sp' = sp - 80: link's strcmp contract (lib/A/Rt/RtString.v:102-113 astrcmp_realizes, on the form
     branch since f961453c8093) takes `PRE (2 * ESTACK)` and `aread_ok (2 * ESTACK)` of each string (each outside
     [sp' - 2 ESTACK, sp'), RtDefs.v:35-40). link-a/form/FORM.md (internal record, sha256 13aeff774164) section 5's 4176
     (one ESTACK) is too small. No realignment. The plain K (48) does not carry over.
   - `anlk_at m LA_G_NL bs`: +0x38 reads n_if, +0x78 reads if_name[i], +0xbc reads if_index[i].
   - `aiftab_at m LA_G_NL bs tab`: the table the loop walks: n_if = length tab <= 80, each if_name[i] a non-NULL
     pointer to a C string, each if_index[i] in [0, 2^31) (so the sign-extending `lw` at +0xbc is the value).
   - `range_addressable (ard m) SHADOW_OFF (LA_G_NL + NK_IF_NAME) (8 * length tab)`: the check +0x70..+0x74 of
     if_name[i] for every i < n_if (the array starts on an 8-byte boundary, so each slot is a whole granule and
     range_addressable gives its shadow byte 0).
   - `range_addressable (ard m) SHADOW_OFF (LA_G_NL + NK_IF_INDEX) (4 * length tab)`: the check +0xac..+0xb8 of
     if_index[i] at the hit.
   - name: `aarg regs 0 <> 0`, `acstr_at m name nm` (strcmp's second string, the contract's `STR`), and
     `astrcmp_arg_ni` of it: the contract's `0 < y`; `aread_ok (2 * ESTACK) y (|nm| + 1)` (RtDefs.v:35-40):
     `|nm| + 1 < 2 ^ 32`, `amem_range y (|nm| + 1)` (which gives `y + |nm| + 1 <= 2 ^ 63`), `range_addressable` and
     `shadow_hull_vis` over [y, y + |nm| + 1), and the string outside this frame and the wrapper's window
     (`apart_frame regs K`, the plain lesson: a pointer argument is separated from everything the function writes);
     and `atail_vis (y + |nm|)` (RtString.v:109, RtDefs.v:54-55): the bytes after the NUL up to the end of its 8-byte
     granule are visible (musl's strcmp under the interceptor may read word-wise). Their values do not enter the
     Post, so they are not in the read set.
   - each table string p of entry i (strcmp's first string, read for every i < n_if): the same facts over
     [p, p + |n2| + 1). They are stated for the p that `au64_at` reads only when `0 <= p < 2 ^ 64`: `au64_at`
     fixes the value only modulo 2 ^ 64 (link-a/plan/CONTRACTS.md (internal record, sha256 5cd783c633c3) 6a class 2),
     and the positive claims would be false of p + 2 ^ 64; aiftab_at's own `acstr_at m p n2` puts its p in that range.
   The write set is empty: the function writes only its frame. EV = 0 (no allocator event), SIDE = [] (no frame_alloc).
   The read set `fuzz_if_nametoindex_ard` = the name's bytes and its NUL, [name, name + |nm|], and aleaf_rd's
   premise that each is a byte `akept` keeps (`akb`, link-a/form/FORM.md (internal record, sha256 13aeff774164)
   section 11): the strcmp wrapper reads them, and the Post's `index_of tab nm` names the string the Pre
   read. The table strings are not pointer arguments and no callee here takes a frame or a block, so they
   stay out of Rd (the same read set as index_of's). In a run the name is a `g_names` or `odd`
   string (image) or a buffer of the caller's: `akb`'s image or frame clause.

   What does NOT carry over from the plain text:
   - `frame_apart_gnl regs 48` (link-a/form/FORM.md (internal record, sha256 13aeff774164) section 1a: the window is on
     the real stack above alloc_ceiling, g_nl is an image byte).
   Nothing of the plain Post is false of image A: it is the register result only, and the returning path's memory
   change (the frame) is what `akept` allows.

   Satisfiability witness (a run; lib/A/Prog/kernel_witness.v `fuzz_if_nametoindex_apre_sat` closes the
   function-specific part): reac_link_alias_read's call on op_read's name, in the run of kernel_c.v's witness:
   a0 = g_names[0] = "nl0" (LA_G_NAMES = 0x62fac0, a .bss string interfaces() wrote), the table of 64 entries
   interfaces() built (if_name[i] = g_names[i] or an `odd` entry, if_index[i] in 2..65 / 101..104), all in
   low memory (amem_range), shadow 0 (instrumented globals' object bytes), every string under 2 ^ 32 bytes; sp =
   reac_link_alias_read's sp on the real stack, above alloc_ceiling, so every string is outside [sp - K, sp).
   Proves no function (kind: statement text). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YI16 YM05 YG0v YG0f YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem.
Import ListNotations.
Local Open Scope Z_scope.

Definition FUZZ_IF_NAMETOINDEX_A : Z := 0x826cc.
Lemma FUZZ_IF_NAMETOINDEX_A_is_entry : FUZZ_IF_NAMETOINDEX_A = LA_fuzz_if_nametoindex. Proof. reflexivity. Qed.

(* the stack bound on image A: the 80-byte frame and the strcmp wrapper's window (2 * ESTACK) *)
Definition FUZZ_IF_NAMETOINDEX_AFRAME : Z := 80.
Definition FUZZ_IF_NAMETOINDEX_AK : Z := FUZZ_IF_NAMETOINDEX_AFRAME + 2 * ESTACK.
Lemma FUZZ_IF_NAMETOINDEX_AK_val : FUZZ_IF_NAMETOINDEX_AK = 8272. Proof. reflexivity. Qed.

(* the write set: nothing outside the frame *)
Definition fuzz_if_nametoindex_awr (regs : bvmap 5 word) (m : word -> option byte) : list (Z * Z) := [].

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Variable segs : list Segment.
Variables rlo rhi : Z.
Variable B : asyms.

(* the facts the strcmp wrapper needs of one of its strings s at p, beside `acstr_at`, inside a function whose stack
   bound K covers the wrapper's window: `0 < p`, `aread_ok (2 * ESTACK) p (|s| + 1)` and `atail_vis (p + |s|)` of
   lib/A/Rt/RtString.v astrcmp_realizes (index_of_c.v's `astrcmp_arg`, word for word) *)
Definition astrcmp_arg_ni (regs : bvmap 5 word) (K : Z) (m : word -> option byte) (p : Z) (s : list byte) : Prop :=
  0 < p /\ Z.of_nat (length s) + 1 < 2 ^ 32 /\ amem_range p (Z.of_nat (length s) + 1)
  /\ range_addressable (ard segs m) SHADOW_OFF p (Z.of_nat (length s) + 1)
  /\ shadow_hull_vis (ard segs m) p (Z.of_nat (length s) + 1)
  /\ apart_frame regs K p (Z.of_nat (length s) + 1)
  /\ (forall a, p + Z.of_nat (length s) < a < p + Z.of_nat (length s) - (p + Z.of_nat (length s)) mod 8 + 8 ->
        ard segs m a <> None).

(* the read set: the name's bytes and its NUL *)
Definition fuzz_if_nametoindex_ard (regs : bvmap 5 word) (m : word -> option byte) (a : Z) : Prop :=
  exists s, acstr_at segs m (aarg regs 0) s /\ aarg regs 0 <= a <= aarg regs 0 + Z.of_nat (length s).

Definition fuzz_if_nametoindex_apre (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  exists bs tab nm,
    anlk_at segs m LA_G_NL bs /\ aiftab_at segs m LA_G_NL bs tab
    /\ range_addressable (ard segs m) SHADOW_OFF (LA_G_NL + NK_IF_NAME) (8 * Z.of_nat (length tab))
    /\ range_addressable (ard segs m) SHADOW_OFF (LA_G_NL + NK_IF_INDEX) (4 * Z.of_nat (length tab))
    /\ aarg regs 0 <> 0 /\ acstr_at segs m (aarg regs 0) nm
    /\ astrcmp_arg_ni regs FUZZ_IF_NAMETOINDEX_AK m (aarg regs 0) nm
    /\ (forall i n2 ix p, nth_error tab i = Some (n2, ix) ->
          au64_at segs m (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p -> 0 <= p < 2 ^ 64 ->
          astrcmp_arg_ni regs FUZZ_IF_NAMETOINDEX_AK m p n2).

Definition fuzz_if_nametoindex_apost (regs : bvmap 5 word) (m : word -> option byte)
    (regs' : bvmap 5 word) (m' : word -> option byte) : Prop :=
  forall bs tab nm, anlk_at segs m LA_G_NL bs -> aiftab_at segs m LA_G_NL bs tab ->
    acstr_at segs m (aarg regs 0) nm ->
    getr regs' 10 = w64 (index_of tab nm).

Definition fuzz_if_nametoindex_acontract : Prop :=
  aleaf_rd SK segs rlo rhi B FUZZ_IF_NAMETOINDEX_A FUZZ_IF_NAMETOINDEX_AK 0 []
    fuzz_if_nametoindex_apre fuzz_if_nametoindex_ard fuzz_if_nametoindex_awr fuzz_if_nametoindex_apost.

End c.
