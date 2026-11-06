From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import Mem Cells Frame Step.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0 Contract.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import LLVMFuzzerTestOneInput_c.
Import ListNotations.
Open Scope Z_scope.

Definition HDR : Z := 0x13410.
Definition EXIT : Z := 0x14454.
Definition RET0 : Z := 0x1445c.
Definition MAX_OPS : Z := 512.
Definition MAX_SIZE : Z := 2 ^ 26.
Definition WS_MASK : Z := 0x100002600.
Definition STALE_NS : Z := 5000000000.
Definition NOW0 : Z := 1000000000.
Definition MS_NS : Z := 1000000.
Definition W0X0 : Z := 0x307830.
Definition INV9 : Z := 0xffffffffffff8e39.
Definition HUNT_SIZE : Z := 480.

Definition rdb (R : list byte) (k : nat) : Z := bv_unsigned (nth k R (Z_to_bv 8 0)).
Definition op_take (n : Z) : Z := Z.min n 3.
Definition dt_of (R : list byte) : Z := rdb R 1 + 256 * rdb R 2.
Definition now_step (op dt now : Z) : Z :=
  if op <? 128 then (now + dt * MS_NS) mod 2 ^ 64
  else if now <? dt * MS_NS then 0 else now - dt * MS_NS.

Definition our_of (pl : list byte) : list byte := map (fun k => nth k pl (Z_to_bv 8 0)) (seq 0 6).
Definition rest_of (pl : list byte) (n : Z) : list byte := skipn (length pl - Z.to_nat n) pl.

Definition saved_cells (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra : word) : list cell :=
  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition saved_of (regs : bvmap 5 word) : list cell :=
  saved_cells (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
    (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 1).

Definition spill_cells (j0 j1 j2 j3 j4 : list byte) (h : Z) : list cell :=
  [CB 24 j0; C8 (Z_to_bv 64 0xffff); C8 (Z_to_bv 64 INV9); CB 104 j1; C8 (Z_to_bv 64 h); CB 16 j2;
   C8 (Z_to_bv 64 MS_NS); C8 (Z_to_bv 64 STALE_NS); CB 24 j3; C8 (Z_to_bv 64 W0X0); CB 20 j4].

Definition OFF_LOCK : Z := 236.
Definition OFF_GATE : Z := 248.
Definition OFF_TABLE : Z := 512.
Definition OFF_OUR : Z := 912.
Definition OFF_WORK : Z := 920.
Definition OFF_SAVE : Z := 2488.

Lemma spill_cells_size : forall j0 j1 j2 j3 j4 h, cells_size (spill_cells j0 j1 j2 j3 j4 h) = Z.to_nat OFF_LOCK.
Proof. reflexivity. Qed.

Lemma saved_cells_size : forall s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra,
  cells_size (saved_cells s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra) = Z.to_nat (SLOT_FRAME - OFF_SAVE).
Proof. reflexivity. Qed.

Section Inv.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Variables (TOK GOK LOK : list byte -> Prop) (HOK : list byte -> list byte -> Prop).
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition slot_sofar (K S : Z) (L0 : layout) (A0 : astate) (mem0 : word -> option byte) (md0 : Model)
    (L : layout) (A : astate) (mem : word -> option byte) (md : Model) : Prop :=
  MR L A mem md /\ WF A /\ bounded A /\ st_init_done A = true /\
  (exists vm, md = with_vmmaps vm md0) /\
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (S - K <= a < S) -> ~ (errno_addr B <= a < errno_addr B + 4) ->
     mbyte segs mem a = mbyte segs mem0 a /\ (writable_at segs mem0 a <-> writable_at segs mem a)) /\
  (forall a, in_img B a -> ~ static_owned B a -> ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) ->
     ~ (errno_addr B <= a < errno_addr B + 4) ->
     mbyte segs mem a = mbyte segs mem0 a /\ (writable_at segs mem0 a <-> writable_at segs mem a)) /\
  (forall q k i, In (q, k) (user_blocks A0) -> 0 <= i < k ->
     mbyte segs mem (ptr_addr L0 q + i) = mbyte segs mem0 (ptr_addr L0 q + i)) /\
  (forall a, (S - K <= a < S) \/ (errno_addr B <= a < errno_addr B + 4) -> writable_at segs mem a) /\
  sink_none B mem md /\ rodata_ok B mem.

Definition slot_hdr (K S data size : Z) (pl : list byte) (gp tp : word) (sv : list cell)
    (L0 : layout) (A0 : astate) (mem0 : word -> option byte) (md0 : Model) (b0 : sbound)
    (i : Z) (c : config) : Prop :=
  exists L A regs mem md (n now h : Z) (T Gt Lk H : list byte) (j0 j1 j2 j3 j4 j5 j6 : list byte),
    c = mkCfg (mkst regs (Z_to_bv 64 HDR) mem (seg_rom segs)) md /\
    0 <= i < MAX_OPS /\ 1 <= n <= size /\ size < MAX_SIZE /\ Z.of_nat (length pl) = size /\
    0 <= now < 2 ^ 64 /\
    getr regs 2 = Z_to_bv 64 (S - SLOT_FRAME) /\ getr regs 3 = gp /\ getr regs 4 = tp /\
    getr regs 8 = Z_to_bv 64 32 /\ getr regs 9 = Z_to_bv 64 i /\ getr regs 14 = Z_to_bv 64 STALE_NS /\
    getr regs 18 = Z_to_bv 64 WS_MASK /\ getr regs 19 = Z_to_bv 64 n /\ getr regs 20 = Z_to_bv 64 h /\
    getr regs 21 = Z_to_bv 64 (data + (size - n)) /\ getr regs 24 = Z_to_bv 64 (S - SLOT_FRAME + 2336) /\
    getr regs 27 = Z_to_bv 64 now /\
    rw_cells rsegs mem (S - SLOT_FRAME) (spill_cells j0 j1 j2 j3 j4 h) /\
    rw_cells rsegs mem (S - SLOT_FRAME + OFF_LOCK) [CB 12 Lk] /\
    rw_cells rsegs mem (S - SLOT_FRAME + OFF_GATE) [CB 264 Gt] /\
    rw_cells rsegs mem (S - SLOT_FRAME + OFF_TABLE) [CB 400 T] /\
    rw_cells rsegs mem (S - SLOT_FRAME + OFF_OUR) [CB 2 j5; CB 6 (our_of pl)] /\
    rw_cells rsegs mem (S - SLOT_FRAME + OFF_WORK) [CB 1568 j6] /\
    rw_cells rsegs mem (S - SLOT_FRAME + OFF_SAVE) sv /\
    mem_inv rsegs mem /\
    stk rsegs mem (S - K) (S - SLOT_FRAME) /\
    rw_cells rsegs mem h [CB (Z.to_nat HUNT_SIZE) H] /\
    bytes_at rsegs mem data pl /\
    disco_GI 0 mem /\
    TOK T /\ GOK Gt /\ LOK Lk /\ HOK H (our_of pl) /\
    slot_sofar K S L0 A0 mem0 md0 L A mem md /\
    Permutation (blocks L A) ((h, HUNT_SIZE) :: blocks L0 A0) /\
    res_ok_slots A (sb_malloc b0 HUNT_SIZE).

Definition slot_measure (i : Z) : nat := Z.to_nat (MAX_OPS - i).

End Inv.
