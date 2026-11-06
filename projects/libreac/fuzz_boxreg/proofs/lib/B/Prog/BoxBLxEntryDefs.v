(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ge_achain adapted from proofs/cgif/cgif_file_fuzzer/lib/A/ACf5.v (rt_chain) for the call chain of libreac/fuzz_grant's entry function; the rest of the file is written for fuzz_grant's entry walk. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntrySeat.v, with its module paths, module names and numbers changed; 892 of its 1130 lines of code are new or changed and 693 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: ported from fuzz_grant's lib/A/Prog/GrantEntrySeat.v (a working branch
   b47e973d564) for libreac/fuzz_boxreg B (fuzz_boxreg.asan-ubsan) over BoxBLxDefs.v: the context is BoxBLxDefs.v's
   lxcx / lx_base / lx_body; the environment is built here from the registers at the seat (the grant context's c_E0
   has no boxreg counterpart); the machine frame's saved words, its spill area, the class-3 side-stack frame
   (512 bytes, flag word at F + 504) and its 64 shadow bytes take boxreg B's numbers; the GOT / shadow-cell regions
   of the prologue are not part of a cut (no phase after the prologue reads them) and were dropped; the landing reads
   the memory facts from the phase's own lemmas (lx_saved_of_ss, lx_shadow_of_ss, lx_word_of_ss) instead of from a
   fixed region shape, and the shent / atom-fact lemmas a token walk needs were added.

   The seat and the landing of a phase of the B walk of fuzz_boxreg's LLVMFuzzerTestOneInput, stated once for all
   of its phases, at ANY pc of the body (a cut of BoxBLxDefs.v or a phase's own loop head).

   A phase carries its machine state as `lx_body` and its own facts; the walk engine wants a symbolic state
   (`st_ok_pi`). `lx_seat` turns the first into the second, and `lx_land` turns the symbolic state back into
   `lx_body`.

   The environment (`lx_env cx fp regs ex`): atoms 0 .. 31 are the registers at the seat (regs = ms_regs ms3);
   32 is SHADOW_OFF; 33 .. 45 the caller's saved words (33 ra, 34 s0, 35 s1, 36 .. 45 s2 .. s11); 46 the frame F
   on the side stack; 47 its flag word's address; 48 up the phase's own words `ex`; 240 .. 511 the image (Eimg).
   The registers (`lx_sr ov`): sr_atoms with the overrides ov; LX_OV makes s1 the atom of sp (2) and s2 the atom of
   SHADOW_OFF (32), LX_OVP also s5 = F + 64 (prev).
   The regions (`lx_regions`), by index: 0 the saved words (base s0 = sp0, read-only); 1 the spill slots
   sp1 + 0 .. sp1 + 0x97 (base sp, writable); 2 the frame (base 46, writable, flag word chunk at 504); 3 its shadow
   bytes (base s6, window [wlo, whi), which may be empty); then the phase's `extra`. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/B/Prog/BoxBLxSeat.v; 176 of its 244 lines of code are new or changed and 1062 lines of the source are left out. *)
(* Shared statements of the entry phase (BoxBLxEntry.v) of the B walk of fuzz_boxreg's LLVMFuzzerTestOneInput
   (fuzz_boxreg.asan-ubsan 0x7ffac): from the function's first slot under lx_base to the loop head 0x80258
   (BoxBLxDefs.v LP_J) of turn 0. The phase is cut at two more points, each a closed symbolic state:
   - D, the call of check (r, fabric) (0x80210, return to 0x80214): ss_D, le_D_stmt (BoxBLxEntryD.v proves it
     from le_K_stmt);
   - K, check's return (0x80214): ss_K, le_K_stmt (BoxBLxEntryK.v proves it: the loop's set-up, LI_J of turn 0).

   The walk: the prologue saves ra, s0, s1, s2 .. s11 below sp0 and realigns sp to sp1 (andi sp,sp,-0x20); the
   GOT-loaded use-after-return flag is 1 (AR's const law), so __asan_stack_malloc_3 (0x8001c) gives the frame F
   (its fallback on the machine stack is not taken: F <> 0); the frame header and the 52 shadow bytes LSH_entry are
   written; n >> 26 = 0 (lx_base: n < 2 ^ 26); the slots 0x10 / 0x18 / 0x80 hold F, 0x88 / 0x90 the input cursor;
   malloc (0x120) (0x8017c, amalloc04_rule) gives the registry r (NULL refuted by 4096 <= r); fuzz_u8 reads the
   first input byte when n > 0 (UBSan's pointer test refuted by p >= 4096, ASan's shadow check of p by the block's
   shadow); reac_boxreg_init (r, the sign-extended byte) (0x801e4); the byte - 1 clamp test gives the fabric;
   check (r, fabric) (0x80210); the loop's slots are set up, and the run stops at 0x80258, where LI_J of turn 0 holds.

   The symbolic state uses the seat layout of BoxBLxSeat.v from the first slot: atom 2 is sp1 and atom 8 is sp0
   (the entry registers 2 and 8 are named by the overrides of le_sr0), 33 .. 45 the caller's saved words, 32
   SHADOW_OFF; 46 / 47 (the frame and its flag address) and 22 (its shadow base) are bound after
   __asan_stack_malloc_3 returns; 48 is the use-after-return flag cell. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0s YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaRun PaShadow PaJournal BoxBase YC4b BoxRo PaStep.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBSyms BoxBList BoxBPa BoxBPaLib BoxBFrame.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import YC1g YC1h YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBReacBoxregInit BoxBCheck.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Rt Require Import SnprintfDefB.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBLxDefs BoxBLxSeat.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Boxreg BoxregInit reac_boxreg_init_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the cut at the call of reac_boxreg_init (0x801e4) ----
   Both arms of fuzz_u8 (n = 0, n > 0) meet in this state: atom 96 is the byte read (0 when n = 0), s3 holds it and
   s11 / a1 its sign extension; atoms 97 / 98 are the input cursor (p + pos, n - pos) the slots 0x88 / 0x90 hold;
   a2 is the scratch atom 513 (the token of the shadow check when n > 0). *)
Definition LE_SHC : list (Z * Z) :=
  [(51, 18446744073709551603); (50, 18446744073709551603); (49, 18446744073709551603); (48, 18446744073709551603);
   (47, 18446744073709551603); (46, 18446744073709551603); (45, 18446744073709551603); (44, 18446744073709551603);
   (43, 18446744073709551608); (42, 18446744073709551608); (41, 18446744073709551608); (40, 18446744073709551608);
   (35, 18446744073709551608); (34, 18446744073709551608); (33, 18446744073709551608); (32, 18446744073709551608);
   (39, 18446744073709551608); (38, 18446744073709551608); (37, 18446744073709551608); (36, 18446744073709551608);
   (27, 18446744073709551608); (26, 18446744073709551608); (25, 18446744073709551608); (24, 18446744073709551608);
   (31, 18446744073709551608); (30, 18446744073709551608); (29, 18446744073709551608); (28, 18446744073709551608);
   (19, 18446744073709551608); (18, 18446744073709551608); (17, 18446744073709551608); (16, 18446744073709551608);
   (23, 18446744073709551608); (22, 18446744073709551608); (21, 18446744073709551608); (20, 18446744073709551608);
   (11, 18446744073709551608); (10, 18446744073709551608); (9, 18446744073709551608); (8, 18446744073709551608);
   (15, 18446744073709551608); (14, 18446744073709551608); (13, 18446744073709551608); (12, 18446744073709551608);
   (3, 18446744073709551601); (2, 18446744073709551601); (1, 18446744073709551601); (0, 18446744073709551601);
   (7, 18446744073709551602); (6, 18446744073709551602); (5, 18446744073709551602); (4, 18446744073709551608);
   (52, 0); (53, 0); (54, 0); (55, 0); (56, 0); (57, 0); (58, 0); (59, 0); (60, 0); (61, 0); (62, 0); (63, 0)].
Definition le_sext8 (n : nat) : sv := SAlu ALU_SRA (SAlu ALU_SLL (SOff n 0) (SLit 56)) (SLit 56).
Definition le_regs_C : list sv := Eval vm_compute in
  [SLit 0; SOff 240 572; SOff 2 0; SOff 3 0; SOff 4 0; SOff 81 0; SOff 82 0; SOff 83 0; SOff 8 0; SOff 2 0;
   SOff 84 0; SAlu ALU_ADD (le_sext8 96) (SLit 0); SOff 513 0; SOff 46 0; SOff 88 0; SOff 89 0; SOff 90 0;
   SOff 91 0; SOff 32 0; SOff 96 0; SOff 84 0; SOff 46 64; SOff 22 0; SOff 41 0; SOff 42 0; SOff 43 0;
   SOff 44 0; le_sext8 96; SOff 92 0; SOff 93 0; SOff 94 0; SOff 95 0].
Definition le_spill_C : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0 152 0 152
    [YP09.mkChunk 136 (CVal 8 (SOff 97 0)); YP09.mkChunk 144 (CVal 8 (SOff 98 0));
     YP09.mkChunk 16 (CVal 8 (SOff 46 0)); YP09.mkChunk 24 (CVal 8 (SOff 46 0)); YP09.mkChunk 128 (CVal 8 (SOff 46 0))].
Definition le_frame_C : YP09.region :=
  YP09.mkRegion (Some 46%nat) 0 512 0 512
    [YP09.mkChunk 16 (CVal 8 (SOff 244 0)); YP09.mkChunk 8 (CVal 8 (SOff 243 0));
     YP09.mkChunk 0 (CVal 8 (SLit 1102416563)); YP09.mkChunk 504 (CVal 8 (SOff 47 0))].
Definition le_shadow_C : YP09.region :=
  YP09.mkRegion (Some 22%nat) 0 64 0 0 (map (fun q => YP09.mkChunk (fst q) (CVal 1 (SLit (snd q)))) LE_SHC).
Definition le_facts_C : facts :=
  mkFacts ((96%nat, mkAF 0 255 0) :: (84%nat, mkAF 4096 140737479966720 4) :: LX_AF) []
    [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 46 0) (SLit 3)) (SOff 32 0), SOff 22 0)].
Definition ss_C : sstate := Eval vm_compute in
  mkSS 572 le_regs_C [lx_saved_region; le_spill_C; le_frame_C; le_shadow_C] None le_facts_C.

(* ---- the cut at the call of check (r, fabric) (0x80210) ----
   s11 / a1 hold the fabric (atom 99, 1 .. 40, clamp40 of the sign-extended byte), s3 the byte - 1, s4 r, s5 F + 64,
   s6 the frame's shadow base; the slot 0x68 holds F + 32. Atoms 113 .. 127 are the registers reac_boxreg_init
   clobbered. *)
Definition le_regs_D : list sv :=
  [SLit 0; SOff 240 616; SOff 2 0; SOff 3 0; SOff 4 0; SOff 113 0; SOff 114 0; SOff 115 0; SOff 8 0; SOff 2 0;
   SOff 84 0; SOff 99 0; SOff 118 0; SOff 119 0; SOff 120 0; SOff 121 0; SOff 122 0; SOff 123 0; SOff 32 0;
   SOff 96 (-1); SOff 84 0; SOff 46 64; SOff 22 0; SOff 41 0; SOff 42 0; SOff 43 0; SOff 44 0; SOff 99 0;
   SOff 124 0; SOff 125 0; SOff 126 0; SOff 127 0].
Definition le_spill_D : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0 152 0 152
    [YP09.mkChunk 104 (CVal 8 (SOff 46 32)); YP09.mkChunk 136 (CVal 8 (SOff 97 0)); YP09.mkChunk 144 (CVal 8 (SOff 98 0));
     YP09.mkChunk 16 (CVal 8 (SOff 46 0)); YP09.mkChunk 24 (CVal 8 (SOff 46 0)); YP09.mkChunk 128 (CVal 8 (SOff 46 0))].
Definition le_facts_D : facts :=
  mkFacts ((99%nat, mkAF 1 40 0) :: (96%nat, mkAF 0 255 0) :: (84%nat, mkAF 4096 140737479966720 4) :: LX_AF) []
    [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 46 0) (SLit 3)) (SOff 32 0), SOff 22 0)].
Definition ss_D : sstate := Eval vm_compute in
  mkSS 616 le_regs_D [lx_saved_region; le_spill_D; le_frame_C; le_shadow_C] None le_facts_D.

(* ---- the cut at check's return (0x80214) ----
   ss_D after the call: the clobbered registers are atoms 128 .. 143, the four regions are kept. *)
Definition ss_K : sstate := Eval vm_compute in ss_after_call ss_D (ss_mem ss_D) 128 616.

Definition le_sx (b : Z) : Z := if b <? 128 then b else b - 256.
Lemma le_byte_chk : forall b, 0 <= b < 256 -> exists k : nat, b = Z.of_nat k /\ In k (seq 0 256).
Proof. intros b Hb. exists (Z.to_nat b). split; [lia | apply in_seq; lia]. Qed.

Lemma le_sext8_U : forall E n b, ew E n = w64 b -> 0 <= b < 256 -> U E (le_sext8 n) = le_sx b mod 2 ^ 64.
Proof.
  intros E n b H Hb. unfold le_sext8. rewrite !U_SAlu, U_SLit, (U_atom E n b H) by lia.
  destruct (le_byte_chk b Hb) as (k & -> & Hk). clear H Hb.
  assert (Hc : forallb (fun k => Z.eqb (zcanon (zalu_raw 63 64 ALU_SRA (zcanon (zalu_raw 63 64 ALU_SLL (Z.of_nat k)
      (zcanon 56))) (zcanon 56))) (le_sx (Z.of_nat k) mod 2 ^ 64)) (seq 0 256) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in Hc. apply Z.eqb_eq. exact (Hc k Hk).
Qed.

Lemma le_mask_U : forall E n b, ew E n = w64 b -> 0 <= b < 256 ->
  U E (SAlu ALU_AND (SOff n (-1)) (SLit 255)) = (b - 1) mod 256.
Proof.
  intros E n b H Hb. rewrite U_SAlu, U_SLit, U_SOff, H. unfold w64. rewrite unsigned_lit_small by lia.
  destruct (le_byte_chk b Hb) as (k & -> & Hk). clear H Hb.
  assert (Hc : forallb (fun k => Z.eqb (zcanon (zalu_raw 63 64 ALU_AND (zcanon (Z.of_nat k + -1)) (zcanon 255)))
      ((Z.of_nat k - 1) mod 256)) (seq 0 256) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in Hc. apply Z.eqb_eq. exact (Hc k Hk).
Qed.

Lemma le_byte_facts : forall b, 0 <= b < 256 ->
  bv_swrap 32 (le_sx b mod 2 ^ 64) = le_sx b /\
  reac_boxreg_init_c.clamp40 (le_sx b) = (if (b - 1) mod 256 <? 40 then b else 40) /\
  ((b - 1) mod 256 <? 40 = true -> le_sx b = b) /\ 1 <= reac_boxreg_init_c.clamp40 (le_sx b) <= 40.
Proof.
  intros b Hb. destruct (le_byte_chk b Hb) as (k & -> & Hk).
  assert (Hc : forallb (fun k => Z.eqb (bv_swrap 32 (le_sx (Z.of_nat k) mod 2 ^ 64)) (le_sx (Z.of_nat k)) &&
      Z.eqb (reac_boxreg_init_c.clamp40 (le_sx (Z.of_nat k)))
            (if (Z.of_nat k - 1) mod 256 <? 40 then Z.of_nat k else 40) &&
      (negb ((Z.of_nat k - 1) mod 256 <? 40) || Z.eqb (le_sx (Z.of_nat k)) (Z.of_nat k)) &&
      (1 <=? reac_boxreg_init_c.clamp40 (le_sx (Z.of_nat k))) && (reac_boxreg_init_c.clamp40 (le_sx (Z.of_nat k)) <=? 40))
      (seq 0 256) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in Hc. specialize (Hc k Hk).
  apply andb_prop in Hc as [Hc H5]. apply andb_prop in Hc as [Hc H4]. apply andb_prop in Hc as [Hc H3].
  apply andb_prop in Hc as [H1 H2].
  apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. apply Z.leb_le in H4. apply Z.leb_le in H5.
  split; [exact H1|]. split; [exact H2|]. split; [|lia].
  intros Ht. rewrite Ht in H3. cbn [negb orb] in H3. apply Z.eqb_eq. exact H3.
Qed.


Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg boxb_listing}.
#[local] Notation SEGS := (@pa_segs _ boxb_listing PI).
#[local] Notation VAL := (@pa_val _ boxb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ boxb_listing PI).
#[local] Notation BASE := (@pa_val _ boxb_listing PI A_TEXT).
Variable B : asyms.
Variable MT : ameter_ops.
(* sp0 and sp1 (BoxBLxSeat.v lx_sp_facts, from lx_base alone). *)
Lemma le_sp_facts : forall cx, lx_base B MT cx ->
  lsp0 cx mod 16 = 0 /\ alloc_ceiling + 32768 <= lsp0 cx /\ lsp0 cx <= 2 ^ 47 /\
  lsp0 cx - 287 <= lsp1 cx <= lsp0 cx - 256 /\ lsp1 cx mod 32 = 0.
Proof.
  intros cx HB. destruct HB as (HPRE & _). destruct HPRE as (_ & _ & _ & _ & _ & Hstk & _).
  destruct Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
  unfold lsp1, lsp0 in *. unfold LX_STK in *.
  pose proof (Z.div_mod (spZ (lc_regs cx) - 256) 32 ltac:(lia)) as Hdm.
  pose proof (Z.mod_pos_bound (spZ (lc_regs cx) - 256) 32 ltac:(lia)) as Hmp.
  split; [exact Hal16|]. split; [lia|]. split; [lia|]. split; [lia|].
  rewrite Z.mul_comm, Z_mod_mult. reflexivity.
Qed.

(* The write windows of the seat's four regions (BoxBLxSeat.v lx_awr_ok, for any chunks and any saved-words
   region without a window). *)
Lemma le_awr : forall cx fp E lo0 hi0 cs0 cs1 cs2 wlo whi cs3 extra lyc bl0 blc,
  lx_base B MT cx ->
  YP09.base_val E (Some LA_SP) = lsp1 cx -> YP09.base_val E (Some LA_F) = lF cx fp ->
  YP09.base_val E (Some LA_FSH) = lSH cx fp ->
  frame_addr lyc LX_CID fp = lF cx fp -> 0 <= wlo -> whi <= 64 ->
  awr_ok E extra LX_STK (lsp0 cx) [] bl0 blc lyc [(LX_CID, fp)] ->
  awr_ok E (YP09.mkRegion (Some LA_SP0) lo0 hi0 0 0 cs0 :: YP09.mkRegion (Some LA_SP) 0 LX_SPILL 0 LX_SPILL cs1 ::
            YP09.mkRegion (Some LA_F) 0 512 0 512 cs2 :: YP09.mkRegion (Some LA_FSH) 0 64 wlo whi cs3 :: extra)
    LX_STK (lsp0 cx) [] bl0 blc lyc [(LX_CID, fp)].
Proof.
  intros cx fp E lo0 hi0 cs0 cs1 cs2 wlo whi cs3 extra lyc bl0 blc HB U2 U46 U22 Hfa Hwlo Hwhi Hex.
  pose proof (le_sp_facts cx HB) as (Hal & Hlo & Hhi & Hsp1 & _).
  assert (Hfb : fs_frame_bytes LX_CID = 512) by (vm_compute; reflexivity).
  assert (Hfb8 : fs_frame_bytes LX_CID / 8 = 64) by (vm_compute; reflexivity).
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply (awr_ok_cons_stack_off E _ _ _ _ _ _ _ _ _ LA_SP (lsp1 cx - lsp0 cx));
    [reflexivity | cbn [YP09.base_val] in U2; rewrite U2; lia | cbn; unfold LX_STK; lia
    | cbn; unfold LX_SPILL; lia |].
  eapply (awr_ok_cons_gen E _ _ _ _ _ _ _ _ _ LA_F (lF cx fp));
    [reflexivity | cbn [YP09.base_val] in U46; exact U46 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
    right; right; right. exists LX_CID, fp. split; [left; reflexivity|].
    left. unfold in_zr. cbn [fst snd]. rewrite Hfa, Hfb. lia. }
  eapply (awr_ok_cons_gen E _ _ _ _ _ _ _ _ _ LA_FSH (lSH cx fp));
    [reflexivity | cbn [YP09.base_val] in U22; exact U22 | | exact Hex].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
  right; right; right. exists LX_CID, fp. split; [left; reflexivity|].
  right. unfold in_zr. cbn [fst snd]. rewrite Hfa, Hfb8. unfold lSH in Ha. lia.
Qed.

(* The seat's four regions across a call that keeps the stack above sp1, the frame and its shadow bytes. *)
Lemma le_kept4 : forall cx fp E (W W' : world SEGS) memc mem' cs0 cs1 cs2 wlo whi cs3,
  YP09.base_val E (Some LA_SP0) = lsp0 cx -> YP09.base_val E (Some LA_SP) = lsp1 cx ->
  YP09.base_val E (Some LA_F) = lF cx fp -> YP09.base_val E (Some LA_FSH) = lSH cx fp ->
  lsp1 cx <= lsp0 cx - 256 -> lsp0 cx <= 2 ^ 47 ->
  (forall a, (lsp1 cx <= a < 2 ^ 64 \/ lF cx fp <= a < lF cx fp + 512 \/ lSH cx fp <= a < lSH cx fp + 64) ->
     aview SEGS (w_H W') mem' a = aview SEGS (w_H W) memc a) ->
  (forall a, (lsp1 cx <= a < lsp1 cx + LX_SPILL \/ lF cx fp <= a < lF cx fp + 512 \/
              lSH cx fp + wlo <= a < lSH cx fp + whi) -> apresent (w_H W') mem' a) ->
  Forall (YI04.region_kept SEGS E (mrestrict (w_H W) memc) (mrestrict (w_H W') mem'))
    [YP09.mkRegion (Some LA_SP0) (-104) 0 0 0 cs0; YP09.mkRegion (Some LA_SP) 0 LX_SPILL 0 LX_SPILL cs1;
     YP09.mkRegion (Some LA_F) 0 512 0 512 cs2; YP09.mkRegion (Some LA_FSH) 0 64 wlo whi cs3].
Proof.
  intros cx fp E W W' memc mem' cs0 cs1 cs2 wlo whi cs3 U8 U2 U46 U22 Hs1 Hs0 Hk Hp.
  unfold LX_SPILL in *.
  repeat apply Forall_cons; try apply Forall_nil;
    (split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi];
     rewrite ?U8, ?U2, ?U46, ?U22; intros a Ha;
     [ apply (mbyte_of_aview SEGS); apply Hk; lia
     | intros _; apply (apresent_writable SEGS); apply Hp; lia ]).
Qed.


(* The saved words at a call's entry (the seat's region 0). *)
Lemma le_saved_at : forall cx fp E ss pc (W : world SEGS) ms,
  lx_base B MT cx -> lx_E cx fp E ->
  st_ok SEGS E (setpc ss pc) (restrict (w_H W) ms) -> nth_error (ss_mem ss) 0 = Some lx_saved_region ->
  lsaved cx W ms.
Proof.
  intros cx fp E ss pc W ms HB HE HS Hi.
  assert (HSpi : st_ok_pi SEGS VAL E (setpc ss (pc - BASE)) (restrict (w_H W) ms))
    by (unfold st_ok_pi, abs_ss; cbn [ss_pc setpc]; replace (BASE + (pc - BASE)) with pc by lia; exact HS).
  exact (lx_saved_of_ss B MT cx fp W ms HB E _ HE HSpi Hi).
Qed.

(* The call chain at a call made from sp1 with the saved words in place. *)
Lemma le_chain : forall cx fp ly' S' (W' : world SEGS) ms' md' k,
  lx_base B MT cx ->
  ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx) [(LX_CID, fp)]
    ly' S' W' (ms_mem ms') md' k ->
  lsaved cx W' ms' ->
  achain ly' (aview SEGS (w_H W') (ms_mem ms')) (lsp1 cx) (lsp0 cx) (lch cx).
Proof.
  intros cx fp ly' S' W' ms' md' k HB HJ (Hsv8 & Hsvj).
  pose proof (le_sp_facts cx HB) as (Hal16 & Hsp0lo & Hsp0hi & Hsp1 & Hal32).
  pose proof HB as (HPRE & _). pose proof HPRE as (_ & _ & Hra4 & _ & _ & Hstk & _ & Hch & _).
  pose proof Hstk as (_ & _ & _ & _ & _ & H47 & _ & Htop & Htop2).
  pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & HF1 & _).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
  assert (Hal8 : lsp0 cx mod 8 = 0).
  { pose proof (Z.div_mod (lsp0 cx) 16 ltac:(lia)) as D. rewrite Hal16, Z.add_0_r in D. rewrite D.
    replace (16 * (lsp0 cx / 16)) with ((2 * (lsp0 cx / 16)) * 8) by lia. apply Z_mod_mult. }
  apply (achain_ly_top (lc_ly cx)); [exact Etop|].
  pose proof asan_consts as (C1 & _).
  apply (lx_achain cx _ (lsp1 cx) Hch); [lia | lia | exact Hal8 | exact Hra4 | | exact Hsv8 | | lia].
  - intros a Ha. apply HF1; [lia | unfold LX_STK; lia].
  - pose proof (Hsvj 0 ltac:(lia)) as H16. replace (lsp0 cx - 16 - 8 * 0) with (lsp0 cx - 16) in H16 by lia.
    exact H16.
Qed.

(* The facts both cuts D and K carry beyond their symbolic state. r is the registry, b the input byte read (0
   when n = 0), fab = clamp40 (sign-extended b) the fabric, pos the input bytes read (0 or 1); the registry holds
   init_bytes fab (reac_boxreg_init's post; check keeps it). *)
Definition le_cut (POST : lxcx -> world SEGS -> config -> Prop) (cx : lxcx) (fp : Z) (E : env) (W : world SEGS)
  (ms : machine_state) (md : Model) (ly : alayout) (S : astate) (r b fab : Z) (pos : nat) : Prop :=
  lx_from B MT POST (LI_J B MT 0) /\ lx_base B MT cx /\
  img_env VAL A_LIM E /\ lx_E cx fp E /\
  ew E 84 = w64 r /\ ew E 96 = w64 b /\ 0 <= b < 256 /\ ew E 99 = w64 fab /\
  fab = reac_boxreg_init_c.clamp40 (le_sx b) /\
  ew E 97 = w64 (lc_p cx + Z.of_nat pos) /\ ew E 98 = w64 (lc_n cx - Z.of_nat pos) /\
  (pos <= length (lc_pl cx))%nat /\
  ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx) [(LX_CID, fp)]
    ly S W (ms_mem ms) md 1 /\
  frames S = [(LX_CID, fp)] /\ mo_le MT (lc_S cx) S (LX_A1 MT) /\
  ablocks B ly S = ablocks B (lc_ly cx) (lc_S cx) ++ [(r, LX_REG)] /\
  lreg W ms r (reac_boxreg_init_c.init_bytes fab).

(* D: the call of check (r, fabric) (0x80210). BoxBLxEntryD.v proves le_K_stmt -> le_D_stmt. *)
Definition le_D_stmt : Prop :=
  forall POST cx fp (E : env) (W : world SEGS) ms md ly S r b fab pos,
  le_cut POST cx fp E W ms md ly S r b fab pos ->
  st_ok SEGS E (setpc ss_D (SIGMA BB_check)) (restrict (w_H W) ms) ->
  SRr SEGS W (mkCfg ms md) (POST cx).

(* K: check's return (0x80214), up to the loop head of turn 0. BoxBLxEntryK.v proves it. *)
Definition le_K_stmt : Prop :=
  forall POST cx fp (E : env) (W : world SEGS) ms md ly S r b fab pos,
  le_cut POST cx fp E W ms md ly S r b fab pos ->
  st_ok_pi SEGS VAL E ss_K (restrict (w_H W) ms) ->
  SRr SEGS W (mkCfg ms md) (POST cx).
End a.
