(* model_decide (fuzz_link.c:423-431, image A 0x8855c, 152 bytes) and reac_served_decide
   (reac_served_mark.c:26-36, image A 0x89510, 152 bytes) on image A (listings
   link-a/listings/{model_decide,reac_served_decide}.fuzz_link.asan.s (internal records, sha256 026ab41cb78f and
   110870bc0bb6)): the verdict on an interface, from its alias and then its link kind. a0 = kind, a1 = alias; either may
   be NULL. The plain contract is lib/Prog/model_decide_c.v (`decide_contract pc`, one statement at two entries); this
   file states the SAME link_spec result (`decide`) in link_amem.v's `aleaf_rd` form.

   ONE STATEMENT, TWO ENTRIES, BUT NOT ONE INSTANCE. The two listings hold the same 38 instruction words at every
   offset except the four pc-relative ones that form the two .rodata addresses (+0x30/+0x34 auipc/addi and
   +0x58/+0x5c auipc/addi) and the two jal. The jal resolve to the same two entries (wrapper_strncmp 0x43050,
   wrapper_strcmp 0x4304c) and to the same error path (errpath_load1 0x5a31c), but the .rodata addresses are
   DIFFERENT: the compiler made one copy of each literal per translation unit, and the memory-checking runtime
   registered each copy as its own global with its own redzone (twin .symtab, 32 bytes each):
     model_decide         "reac-pw:" .str.14 0x21160   "vlan" .str.17 0x211c0
     reac_served_decide   "reac-pw:" .str    0x212a0   "vlan" .str.1  0x212c0
   (bytes read from the pin's .rodata with pyelftools: 8 and 4 bytes, each followed by its NUL). So the statement
   `decide_acontract_at pc prefix vlan` takes the two literal addresses, and each entry gets its own instance.
   The plain file could use one pair of addresses for both entries; on image A that would be false of one of them.

   The image-A code, in order (offsets of model_decide; reac_served_decide is the same):
     +0x00..+0x04  push a 16-byte frame, save ra                   (before the NULL test, as in the plain code)
     +0x08  beqz a1 -> +0x54                                       (alias NULL: the kind arm)
     +0x0c..+0x14  a2 := the shadow base, loaded through the .got cell 0xa19d0 (LA_GOT_SHADOW, which holds
                   LA_SHADOW_CELL = 0xaa438, which holds the base)
     +0x18..+0x24, +0x88..+0x8c  the instrumented check of the 1-byte load of alias[0]: shadow byte s of a1;
                   s = 0 passes; else (a1 & 7) < s passes; else errpath_load1 (0x5a31c)
     +0x28  lbu a2, 0(a1) = alias[0];  +0x2c beqz a2 -> +0x54      (empty alias: the kind arm)
     +0x30..+0x44  a0 := alias, a1 := <prefix>, a2 := 8; jal wrapper_strncmp (0x43050)
     +0x48  beqz a0 -> +0x70 (a0 := 1 = V_OURS);  +0x4c a0 := 3 = V_LEAVE_HOST
     +0x54  beqz a0 -> +0x68 (kind NULL: a0 := 0 = V_MARK)
     +0x58..+0x60  a1 := <vlan>; jal wrapper_strcmp (0x4304c) with a0 = kind
     +0x64  beqz a0 -> +0x78 (a0 := 2 = V_LEAVE_VLAN);  +0x68 a0 := 0 = V_MARK
     +0x7c..+0x84  restore, pop, ret.
   That is `decide kind alias` of link_spec.v:388-402 (V_MARK 0, V_OURS 1, V_LEAVE_VLAN 2, V_LEAVE_HOST 3), with
   `has_prefix a` answered by strncmp(alias, "reac-pw:", 8) = 0 and `bl_eqb k S_VLAN` by strcmp(kind, "vlan") = 0.

   Which instruction needs which premise:
   - the journal, gp/tp, ret_ok (apre): the store +0x04 (inside [sp - K, sp)); the two wrapper calls take
     ecall_pre-style premises at sp - 16 that the walk derives from the journal (no journal lift of the strcmp /
     strncmp wrappers exists yet: pcap's aj_strcmp_at, A/Prog/PcapFuzzFopen.v:109-125, is the model); +0x84 ret.
   - K = 16 + 2 * ESTACK = 8208: the 16-byte frame (no realignment: there is no `andi sp, sp, -0x20`), then the
     deepest callee window. BOTH wrappers state a 2 * ESTACK window, not ESTACK: the strcmp contract that applies
     to a run-time string is pcap's Reusable/AStrcmpDef.v `astrcmp_realizes` (origin/ossv/recipes), which takes
     `ly_stk_lo ly + 2 * ESTACK <= spZ regs`, [sp - 8192, sp) present and both strings outside [sp - 2*ESTACK, sp);
     pcap's A/Rt/StrcmpDef.v (ESTACK) is only the literal instance "<fuzz-input>". The strncmp contract is
     plugin-hostd/fuzz_command's `astrncmp_realizes` (lib/A/Rt/RtString.v:121), window 2 * ESTACK
     (link-a/libc/strmem.md (internal record, sha256 b0efa271b731) section 2a). The plain K (16) does not carry over.
   - `astr_arg m (aarg regs 0) k` and `astr_arg m (aarg regs 1) al`: +0x08 and +0x54 test the pointers; +0x28 reads
     alias[0]; the wrappers read each string up to its NUL.
   - `astr_rt_ok regs K m (aarg regs 1) t` when alias is the string t: the shadow premise of the check +0x18 (its
     first byte) and everything wrapper_strncmp asks of its first string (whole string and NUL addressable, the
     shadow hull visible, the 8-byte band `amem_range p (|t| + 8)`, the bytes after the NUL up to its granule's
     end visible, the string outside [sp - 2*ESTACK, sp)). `range_addressable` over |t| + 1 bytes covers the
     1-byte check: the check at +0x18 passes exactly when the shadow byte makes alias[0] addressable.
   - `astr_rt_ok regs K m (aarg regs 0) t` when kind is t: the same, for wrapper_strcmp's first string.
   - `acstr_at m prefix S_PREFIX` / `acstr_at m vlan S_VLAN` and their `astr_rt_ok`: the second string of each
     wrapper. They are image bytes (.rodata), so the journal keeps them (`arodata_okP`), but the wrappers still
     ask for the shadow of the bytes they read, and each literal sits in a registered global whose 8-byte granules
     after the NUL are its redzone; `astr_rt_ok` states exactly the span the wrapper reads, |s| + 1 bytes, plus the
     visibility of the rest of the NUL's granule.
   - the read set Rd (`aleaf_rd`): the two argument strings. The function reads bytes through a pointer argument
     that are not in its write set (which is empty), so the caller must place them where `akb` keeps them. At
     every call site they are: reac_served_mark 0x89a48 passes two buffers of its own class-3 side frame (a frame
     of Sc); LLVMFuzzerTestOneInput 0x838fc passes model_read's two buffers in its class-4 frame
     (link-a/libc/strmem.md (internal record, sha256 b0efa271b731) section 2); LLVMFuzzerTestOneInput 0x82e44
     (reac_served_decide) and 0x82e54 (model_decide) pass the two answers of text_of, each a .rodata text (an image
     byte) or a fresh heap block (a block of Sc).
   The write set is empty: the function writes only its frame. EV = 0 (no allocator event), SIDE = [] (no
   frame_alloc on either path).

   What does NOT carry over from the plain text:
   - the plain `apart_frame regs 16 ...`: the window is now [sp - 8208, sp), and the premise is inside
     `astr_rt_ok`, which also carries what the wrappers ask beyond separation.
   - the plain `cstr_at m A_PREFIX S_PREFIX` for both entries: two literals per string on image A (above).
   Nothing of the plain Post is false of image A: it is the register result only, and the frame store on the
   returning path is what `akept` allows (the plain contract does not claim `m' = m` either).
   Released proofs (rule 24): none of model_decide or reac_served_decide
   (link-a/index/SUMMARY.md (internal record, sha256 58ab2c29f038)).
   Proves no function (kind: statement text). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YI16 YM05 YG0v YG0f YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem.
Import ListNotations.
Local Open Scope Z_scope.

Definition MODEL_DECIDE_A : Z := 0x8855c.
Lemma MODEL_DECIDE_A_is_entry : MODEL_DECIDE_A = LA_model_decide. Proof. reflexivity. Qed.
Definition REAC_SERVED_DECIDE_A : Z := 0x89510.
Lemma REAC_SERVED_DECIDE_A_is_entry : REAC_SERVED_DECIDE_A = LA_reac_served_decide. Proof. reflexivity. Qed.

(* The four .rodata literals of image A (twin .symtab; one registered global of 32 bytes each). These belong in
   lib/A/Prog/link_aaddr.v; they are here until the lane that owns that file adds them. *)
Definition LA_MD_PREFIX : Z := 0x21160.      (* model_decide's "reac-pw:" (.str.14) *)
Definition LA_MD_VLAN : Z := 0x211c0.        (* model_decide's "vlan" (.str.17) *)
Definition LA_RSD_PREFIX : Z := 0x212a0.     (* reac_served_decide's "reac-pw:" (.str) *)
Definition LA_RSD_VLAN : Z := 0x212c0.       (* reac_served_decide's "vlan" (.str.1) *)

(* The two runtime entries both functions call (listings +0x44 and +0x60). *)
Definition LA_wrapper_strncmp : Z := 0x43050.
Definition LA_wrapper_strcmp : Z := 0x4304c.

(* the stack bound on image A: the 16-byte frame and the wrappers' 2 * ESTACK window *)
Definition DECIDE_AFRAME : Z := 16.
Definition DECIDE_AK : Z := DECIDE_AFRAME + 2 * ESTACK.
Lemma DECIDE_AK_val : DECIDE_AK = 8208. Proof. reflexivity. Qed.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Variable segs : list Segment.
Variables rlo rhi : Z.
Variable B : asyms.

(* ==========================================================================
   The pieces this slice shares (remember_c.v, reac_code_emit_c.v, reac_served_mark_c.v, mark_quietly_c.v all
   Require this file for them).
   ========================================================================== *)

(* The bytes of the C string at p, as a predicate on one address: a read set `Rd` of `aleaf_rd` is
   `regs -> m -> Z -> Prop`, so a string argument's span is said with the Pre's own view and not computed. A NULL
   pointer covers no byte (the plain L7 rule, as `aivl` on the write side: no journal lets a callee read or write
   address 0). *)
Definition astr_rd (m : word -> option byte) (p : Z) (a : Z) : Prop :=
  p <> 0 /\ exists s, acstr_at segs m p s /\ p <= a <= p + Z.of_nat (length s).

(* What a string s at p must satisfy for one of the runtime's string wrappers (strcmp, strncmp, snprintf's %s
   argument) to read it inside a function whose stack bound is K: the span the wrapper reads is addressable and
   its shadow hull visible, the 8-byte band the interceptor's range check needs lies in memory
   (`amem_range p (|s| + 8)`, fuzz_command lib/A/Rt/RtString.v:132), the rest of the NUL's 8-byte word is visible
   (`atail_vis`, RtDefs.v:54), and the string lies outside the callee windows [sp - K, sp). *)
Definition astr_rt_ok (regs : bvmap 5 word) (K : Z) (m : word -> option byte) (p : Z) (s : list byte) : Prop :=
  0 < p /\ Z.of_nat (length s) + 8 < 2 ^ 31
  /\ amem_range p (Z.of_nat (length s) + 8)
  /\ range_addressable (ard segs m) SHADOW_OFF p (Z.of_nat (length s) + 1)
  /\ shadow_hull_vis (ard segs m) p (Z.of_nat (length s) + 1)
  /\ (forall b, p + Z.of_nat (length s) < b
                < p + Z.of_nat (length s) - (p + Z.of_nat (length s)) mod 8 + 8 -> ard segs m b <> None)
  /\ apart_frame regs K p (Z.of_nat (length s) + 1).

(* ==========================================================================
   The contract
   ========================================================================== *)

Definition decide_apre (prefix vlan : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  exists k al,
    astr_arg segs m (aarg regs 0) k /\ astr_arg segs m (aarg regs 1) al
    /\ acstr_at segs m prefix S_PREFIX /\ astr_rt_ok regs DECIDE_AK m prefix S_PREFIX
    /\ acstr_at segs m vlan S_VLAN /\ astr_rt_ok regs DECIDE_AK m vlan S_VLAN
    /\ (forall t, k = Some t -> astr_rt_ok regs DECIDE_AK m (aarg regs 0) t)
    /\ (forall t, al = Some t -> astr_rt_ok regs DECIDE_AK m (aarg regs 1) t).

(* the read set: the two argument strings (the two literals are image bytes, which `akb` keeps) *)
Definition decide_ard (regs : bvmap 5 word) (m : word -> option byte) (a : Z) : Prop :=
  astr_rd m (aarg regs 0) a \/ astr_rd m (aarg regs 1) a.

(* the write set: nothing outside the frame *)
Definition decide_awr (regs : bvmap 5 word) (m : word -> option byte) : list (Z * Z) := [].

Definition decide_apost (regs : bvmap 5 word) (m : word -> option byte)
    (regs' : bvmap 5 word) (m' : word -> option byte) : Prop :=
  forall k al, astr_arg segs m (aarg regs 0) k -> astr_arg segs m (aarg regs 1) al ->
    getr regs' 10 = w64 (decide k al).

Definition decide_acontract_at (pc prefix vlan : Z) : Prop :=
  aleaf_rd SK segs rlo rhi B pc DECIDE_AK 0 []
    (decide_apre prefix vlan) decide_ard decide_awr decide_apost.

Definition model_decide_acontract : Prop :=
  decide_acontract_at MODEL_DECIDE_A LA_MD_PREFIX LA_MD_VLAN.
Definition reac_served_decide_acontract : Prop :=
  decide_acontract_at REAC_SERVED_DECIDE_A LA_RSD_PREFIX LA_RSD_VLAN.

End c.
