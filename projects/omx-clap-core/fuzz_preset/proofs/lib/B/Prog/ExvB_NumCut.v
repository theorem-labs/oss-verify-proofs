(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Does not rest on tex_word_specX; memnorm only through EXB's exv_rm keep and EXV_PRE's entry memnorm (kit 4f18c75d4900). *)
(* Theorem Labs, 2026-10: fuzz_preset, image B (asan-ubsan, rebuilt pin f8f98a95bc52, unstripped twin 3b5e1a099b53),
   ex_value's NUMBER SEGMENT (the cut CN of lib/B/Prog/ExvB_Stmt.v, B 0x837a4 = exv_pc 0x278): the segment's own
   INTERNAL cuts and the statement of each sub-piece. Statements only; this file proves nothing about the program.

   The code walked (neutral listing, the internal file ex_value.fuzz_preset.asan-ubsan.s, a Theorem Labs lane's listing of the B' pin;
   every offset DERIVED = B address - B_entry_ex_value 0x8352c):
     CN  0x278  (0x837a4)  the two `sb zero, 4(s10) / 8(s10)` that open the frame's `end` and `num` slots, the '-',
                           the lead-digit and lead-'0' tests
     CL  0x324  (0x83850)  the scan loop's head, s6 = a0 = x0 + j
     CS  0x84c  (0x83d78)  the scan's end at j (the text's end, or the first byte that is not numch)
     CR  0x8d4  (0x83e00)  strtod's return site
     CC  0x910  (0x83e3c)  the number is whole and finite; the frame's num slot holds its bits
     CD  0x9a8  (0x83ed4)  in->differs decided
     CT  0xa70  (0x83f9c)  the segment's common tail: s5 = r, the two `sb a0, 4(s10) / 8(s10)` re-poison, then
     CX  0xa7c  (0x83fa8)  ExvB_Stmt's CUT_CX
   Sub-pieces (each proves `cut -> SRr .. (EXV_POST E)` from the cuts below it):
     T = CT -> CX;  A = CN -> CT | CL;  Bp = CL -> CS (the loop, by induction);
     C = CS -> CR (__asan_memcpy, the NUL store, strtod);  D = CR -> CT | CC (the fsd, *end, fclass.d);
     Ep = CC -> CD (v's type, __wrap_strcmp, __wrap_bcmp, the differs store);  F = CD -> CT.
   M = the two preservation statements of EXB across the segment's own writes (EXN_keepM / EXN_keepM_cur).

   Numerals, classified: DERIVED - the cut offsets above, and the write zone's bounds 160 (the last s1 spill + 8),
   STK_RT_STRTOD; LENGTH - 8, 4, 32, 40, 64, 72, 136, 144, 152 (widths and the frame / s1 slot offsets of B's code,
   read off the listing); WORD - the register numbers 2, 3, 4, 8, 9, 10, 11, 12, 13, 14, 15, 18, 19, 20, 21, 22, 23,
   24, 25, 26, 27 and the ASCII bytes 45 ('-') and 48 ('0') of ExvB_NumPure. No ADDRESS: every program counter is
   `exv_pc <offset>`. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import FCiface YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YStrtodRowX YGcallMx YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExvB_Stmt ExvB_NumPure.
Import ListNotations.
Local Open Scope Z_scope.

#[local] Existing Instance prh_img_B.

(* the segment's cut offsets *)
Definition EXN_CN : Z := 0x278.
Definition EXN_CL : Z := 0x324.
Definition EXN_CS : Z := 0x84c.
Definition EXN_CR : Z := 0x8d4.
Definition EXN_CC : Z := 0x910.
Definition EXN_CD : Z := 0x9a8.
Definition EXN_CT : Z := 0xa70.

Section c. Context {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Variable E : exv_e.
Variable pos : Z.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* the index of the dispatch byte inside the text, as a nat *)
Definition EXN_i1 : nat := Z.to_nat (exv_i1 E).

(* the base invariant of every cut of the segment, at the cut's float state *)
Definition EXN_base (fxc : YK11.FPState) (lyc : alayout) (Sc : astate) (Hpc : list Z) (Wc : world rsegs)
  (regs : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (k : Z) : Prop :=
  EXB (fx := fxc) B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos /\
  exv_spill E Wc memc 144 (shadow_addr (e_q E)) /\ exv_spill E Wc memc 152 (e_v E).

(* the cursor at text position p with in->differs = dl *)
Definition EXN_cur (Wc : world rsegs) (memc : word -> option byte) (p dl : Z) : Prop :=
  prhex_cur Wc memc (e_q E) (e_x0 E + p) (e_x0 E + exv_len E) (e_dep E) (e_scr E) dl.

(* the dispatch facts CUT_CN hands the segment *)
Definition EXN_disp (c : Z) : Prop :=
  exv_i1 E < exv_len E /\ nth EXN_i1 (e_x E) 0 = c /\ exv_disp c = false /\ PjGrammar.ws c = false.

(* the frame's `end` (f + 32) and `num` (f + 64) slots are open: their shadow bytes, written by CN's two
   `sb zero, 4(s10) / 8(s10)` (B 0x837a8, 0x837ac), read 0 *)
Definition EXN_fsh (lyc : alayout) (Wc : world rsegs) (memc : word -> option byte) : Prop :=
  aview rsegs (w_H Wc) memc (shadow_addr (frame_addr lyc 1 pos) + 4) = Some 0 /\
  aview rsegs (w_H Wc) memc (shadow_addr (frame_addr lyc 1 pos) + 8) = Some 0.

(* the span the scan reads: the lead byte at j0 = i1 + sg is a digit (and not a '0' before a digit), and every
   byte of [j0, j) is a number character *)
Definition EXN_span (c : Z) (j : nat) : Prop :=
  (EXN_i1 + exn_sg c < length (e_x E))%nat /\
  PjGrammar.digit (nth (EXN_i1 + exn_sg c) (e_x E) 0) = true /\
  ~ (nth (EXN_i1 + exn_sg c) (e_x E) 0 = 48 /\ (S (EXN_i1 + exn_sg c) < length (e_x E))%nat /\
     PjGrammar.digit (nth (S (EXN_i1 + exn_sg c)) (e_x E) 0) = true) /\
  Forall (fun z => PjGrammar.numch z = true) (exn_sub (e_x E) (EXN_i1 + exn_sg c) j).

(* ---- the model glue: at the dispatch byte the value the arm reads IS the grammar's number reading ---- *)
Lemma exn_i1_eq : 0 <= e_i0 E <= exv_len E -> skipn EXN_i1 (e_x E) = PjGrammar.skip (exv_X E).
Proof.
intros Hi0. unfold EXN_i1, exv_i1, exv_X, exv_len in *.
replace (Z.to_nat (Z.of_nat (length (e_x E)) -
           Z.of_nat (length (PjGrammar.skip (skipn (Z.to_nat (e_i0 E)) (e_x E))))))
  with (length (e_x E) - length (PjGrammar.skip (skipn (Z.to_nat (e_i0 E)) (e_x E))))%nat by lia.
apply exn_at_i1. lia.
Qed.

Lemma exn_V_eq : forall c, 0 <= e_i0 E <= exv_len E -> EXN_disp c ->
  exv_V E = exn_N (skipn EXN_i1 (e_x E)).
Proof.
intros c Hi0 (Hlt & Hnth & Hdisp & Hws).
assert (Hsk : skipn EXN_i1 (e_x E) = PjGrammar.skip (exv_X E)) by exact (exn_i1_eq Hi0).
destruct (skipn EXN_i1 (e_x E)) as [|b y] eqn:Esk.
{ exfalso. unfold exv_i1 in Hlt. rewrite <- Hsk in Hlt. cbn [length Z.of_nat] in Hlt. lia. }
assert (Hb : b = c) by (rewrite <- Hnth; symmetry; exact (exn_nth_skipn (e_x E) EXN_i1 b y Esk)).
assert (Ho : exn_other b).
{ rewrite Hb. unfold exn_other.
  repeat split; intros Hc; rewrite Hc in Hdisp; vm_compute in Hdisp; discriminate Hdisp. }
unfold exv_V, prhex_V.
exact (exn_value_is_number (Z.to_nat (e_dep E)) (exv_X E) b y
         (eq_sym Hsk) ltac:(rewrite Hb; exact Hws) Ho).
Qed.

(* ---- the internal cuts ---- *)

(* CT (0xa70): the common tail. s5 is the result and the functional post already holds. *)
Definition EXN_CT_pre (fxc : YK11.FPState) lyc Sc Hpc Wc regs memc mdc k (r : Z) : Prop :=
  EXN_base fxc lyc Sc Hpc Wc regs memc mdc k /\ getr regs 21 = w64 r /\ EXV_RES E Wc memc r.

(* CL (0x324): the scan loop's head, j bytes read *)
Definition EXN_CL_pre (fxc : YK11.FPState) lyc Sc Hpc Wc regs memc mdc k (c : Z) (j : nat) : Prop :=
  EXN_base fxc lyc Sc Hpc Wc regs memc mdc k /\ EXN_disp c /\
  EXN_cur Wc memc (exv_i1 E) (e_dl E) /\ EXN_fsh lyc Wc memc /\ EXN_span c j /\
  (EXN_i1 + exn_sg c <= j < length (e_x E))%nat /\
  getr regs 27 = w64 c /\ getr regs 22 = w64 (e_x0 E + Z.of_nat j) /\ getr regs 10 = w64 (e_x0 E + Z.of_nat j) /\
  getr regs 11 = w64 (e_x0 E + exv_i1 E) /\ getr regs 12 = w64 (e_x0 E + exv_len E) /\
  getr regs 21 = w64 (-1) /\ getr regs 23 = w64 (frame_addr lyc 1 pos + 32) /\
  getr regs 13 = w64 (-11) /\ getr regs 14 = w64 58 /\ getr regs 15 = w64 exn_MASK /\
  exv_spill E Wc memc 136 (frame_addr lyc 1 pos + 64).

(* CS (0x84c): the scan stopped at j - the text's end, or the first byte that is not numch *)
Definition EXN_CS_pre (fxc : YK11.FPState) lyc Sc Hpc Wc regs memc mdc k (c : Z) (j : nat) : Prop :=
  EXN_base fxc lyc Sc Hpc Wc regs memc mdc k /\ EXN_disp c /\
  EXN_cur Wc memc (exv_i1 E) (e_dl E) /\ EXN_fsh lyc Wc memc /\ EXN_span c j /\
  (EXN_i1 + exn_sg c < j <= length (e_x E))%nat /\
  (j = length (e_x E) \/ PjGrammar.numch (nth j (e_x E) 0) = false) /\
  getr regs 27 = w64 c /\ getr regs 22 = w64 (e_x0 E + Z.of_nat j) /\
  getr regs 11 = w64 (e_x0 E + exv_i1 E) /\ getr regs 21 = w64 (-1) /\
  getr regs 23 = w64 (frame_addr lyc 1 pos + 32) /\
  exv_spill E Wc memc 136 (frame_addr lyc 1 pos + 64).

(* CR (0x8d4): strtod returned. The scratch holds txt ++ [0], the frame's end slot holds scratch + cn, fa0 = bits. *)
Definition EXN_CR_pre (fxc : YK11.FPState) lyc Sc Hpc Wc regs memc mdc k (c : Z) (j : nat) (bits cn : Z) : Prop :=
  let txt := exn_sub (e_x E) EXN_i1 j in
  EXN_base fxc lyc Sc Hpc Wc regs memc mdc k /\ EXN_disp c /\
  EXN_cur Wc memc (exv_i1 E) (e_dl E) /\ EXN_fsh lyc Wc memc /\ EXN_span c j /\
  (EXN_i1 + exn_sg c < j <= length (e_x E))%nat /\
  (j = length (e_x E) \/ PjGrammar.numch (nth j (e_x E) 0) = false) /\
  garr8 rsegs (rdW Wc memc) (e_scr E) (txt ++ [0]) /\
  exv_strtod_model txt = Some (bits, cn) /\ 0 <= cn <= Z.of_nat (length txt) /\
  val_mem rsegs (rdW Wc memc) (frame_addr lyc 1 pos + 32) 8 (e_scr E + cn) /\
  LinuxProcessSemantics.Riscv.Sem.reg_get (@YK11.fp_regs fxc) (Z_to_bv 5 10) = Z_to_bv 64 bits /\
  getr regs 22 = w64 (e_x0 E + Z.of_nat j) /\ getr regs 21 = w64 (-1) /\
  getr regs 23 = w64 (frame_addr lyc 1 pos + 32) /\ getr regs 20 = w64 (e_q E + 24) /\
  getr regs 27 = w64 (shadow_addr (e_q E + 24)) /\
  exv_spill E Wc memc 136 (frame_addr lyc 1 pos + 64).

(* CC (0x910): the arm's value is read - JNum txt bits - and the frame's num slot holds its bits *)
Definition EXN_CC_pre (fxc : YK11.FPState) lyc Sc Hpc Wc regs memc mdc k (c : Z) (j : nat) (bits : Z) : Prop :=
  let txt := exn_sub (e_x E) EXN_i1 j in
  EXN_base fxc lyc Sc Hpc Wc regs memc mdc k /\ EXN_disp c /\
  EXN_cur Wc memc (exv_i1 E) (e_dl E) /\ EXN_fsh lyc Wc memc /\
  (EXN_i1 < j <= length (e_x E))%nat /\
  exn_N (skipn EXN_i1 (e_x E)) = Some (PjTree.JNum txt bits, skipn j (e_x E)) /\
  garr8 rsegs (rdW Wc memc) (e_scr E) (txt ++ [0]) /\
  val_mem rsegs (rdW Wc memc) (frame_addr lyc 1 pos + 64) 8 bits /\
  getr regs 22 = w64 (e_x0 E + Z.of_nat j) /\ getr regs 13 = w64 (shadow_addr (e_q E)) /\ getr regs 21 = w64 (-1) /\
  getr regs 20 = w64 (e_q E + 24) /\ getr regs 27 = w64 (shadow_addr (e_q E + 24)) /\
  exv_spill E Wc memc 136 (frame_addr lyc 1 pos + 64).

(* CD (0x9a8): in->differs decided; what is left is the store of in->p and s5 := 0 *)
Definition EXN_CD_pre (fxc : YK11.FPState) lyc Sc Hpc Wc regs memc mdc k (j : nat) (u : PjTree.jv) : Prop :=
  EXN_base fxc lyc Sc Hpc Wc regs memc mdc k /\
  (EXN_i1 < j <= length (e_x E))%nat /\
  exn_N (skipn EXN_i1 (e_x E)) = Some (u, skipn j (e_x E)) /\
  getr regs 22 = w64 (e_x0 E + Z.of_nat j) /\ getr regs 13 = w64 (shadow_addr (e_q E)) /\
  exists dl', EXN_cur Wc memc (exv_i1 E) dl' /\ (dl' = 0 \/ dl' = 1) /\
    (dl' = 1 <-> e_dl E = 1 \/ (e_v E <> 0 /\ e_t E <> u)).

(* ---- the sub-piece statements ---- *)
Local Notation SRX fxc regs off memc mdc Wc :=
  (SRr rsegs Wc (cfg_at (fx := fxc) rsegs (exv_pc off) regs memc mdc) (EXV_POST B ARx SK E)).

Definition EXN_T : Prop := forall fxc lyc Sc Hpc Wc regs memc mdc k r,
  EXV_PRE B ARx E -> EXN_CT_pre fxc lyc Sc Hpc Wc regs memc mdc k r -> SRX fxc regs EXN_CT memc mdc Wc.
Definition EXN_A : Prop := forall fxc lyc Sc Hpc Wc regs memc mdc k c,
  EXV_PRE B ARx E -> EXN_base fxc lyc Sc Hpc Wc regs memc mdc k -> EXN_disp c ->
  EXN_cur Wc memc (exv_i1 E) (e_dl E) ->
  getr regs 11 = w64 (e_x0 E + exv_i1 E) -> getr regs 12 = w64 (e_x0 E + exv_len E) ->
  getr regs 27 = w64 c -> getr regs 20 = w64 (shadow_addr (e_q E)) ->
  SRX fxc regs EXN_CN memc mdc Wc.
Definition EXN_Bl : Prop := forall fxc lyc Sc Hpc Wc regs memc mdc k c j,
  EXV_PRE B ARx E -> EXN_CL_pre fxc lyc Sc Hpc Wc regs memc mdc k c j -> SRX fxc regs EXN_CL memc mdc Wc.
Definition EXN_C : Prop := forall fxc lyc Sc Hpc Wc regs memc mdc k c j,
  EXV_PRE B ARx E -> EXN_CS_pre fxc lyc Sc Hpc Wc regs memc mdc k c j -> SRX fxc regs EXN_CS memc mdc Wc.
Definition EXN_D : Prop := forall fxc lyc Sc Hpc Wc regs memc mdc k c j bits cn,
  EXV_PRE B ARx E -> EXN_CR_pre fxc lyc Sc Hpc Wc regs memc mdc k c j bits cn -> SRX fxc regs EXN_CR memc mdc Wc.
Definition EXN_Ec : Prop := forall fxc lyc Sc Hpc Wc regs memc mdc k c j bits,
  EXV_PRE B ARx E -> EXN_CC_pre fxc lyc Sc Hpc Wc regs memc mdc k c j bits -> SRX fxc regs EXN_CC memc mdc Wc.
Definition EXN_F : Prop := forall fxc lyc Sc Hpc Wc regs memc mdc k j u,
  EXV_PRE B ARx E -> EXN_CD_pre fxc lyc Sc Hpc Wc regs memc mdc k j u -> SRX fxc regs EXN_CD memc mdc Wc.

(* ---- M: EXB across the segment's own writes ----
   the bytes the segment and its callees may change outside the cursor: the callee windows below s1 and the s1
   spills up to +160 (the frame's num pointer at +136, the shadow of q at +144, v at +152), the frame's `end` and
   `num` slots and their two shadow bytes, the scratch, errno *)
Definition EXN_wz (lyc : alayout) (z : Z) : Prop :=
  exv_s1 E - STK_RT_STRTOD <= z < exv_s1 E + 160 \/
  frame_addr lyc 1 pos + 32 <= z < frame_addr lyc 1 pos + 40 \/
  frame_addr lyc 1 pos + 64 <= z < frame_addr lyc 1 pos + 72 \/
  z = shadow_addr (frame_addr lyc 1 pos) + 4 \/ z = shadow_addr (frame_addr lyc 1 pos) + 8 \/
  e_scr E <= z < e_scr E + exv_len E + 1 \/
  as_errno B <= z < as_errno B + 4.

Definition EXN_regs_kept (regs regs' : bvmap 5 word) : Prop :=
  getr regs' 2 = getr regs 2 /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\
  getr regs' 18 = getr regs 18 /\ getr regs' 24 = getr regs 24 /\ getr regs' 25 = getr regs 25 /\
  getr regs' 26 = getr regs 26 /\ getr regs' 19 = getr regs 19 /\ getr regs' 3 = getr regs 3 /\
  getr regs' 4 = getr regs 4.

Local Notation AJ lyc Sc Hpc Wc memc mdc k :=
  (ajournal_x (SK := SK) rsegs B prh_pst ARx (exv_STK E + e_d E) (exv_sp E + e_d E) (exv_FP E)
     (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_mem E) (e_md E) [(1, pos)] lyc Sc Hpc Wc memc mdc k).

(* the cursor untouched *)
Definition EXN_keepM : Prop := forall fxc lyc Sc Hpc Wc regs memc mdc k regs' memc' mdc' k',
  EXV_PRE B ARx E -> EXB (fx := fxc) B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos ->
  AJ lyc Sc Hpc Wc memc' mdc' k' ->
  (forall z, 0 <= z < 2 ^ 64 -> ~ EXN_wz lyc z -> aview rsegs (w_H Wc) memc' z = aview rsegs (w_H Wc) memc z) ->
  (forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) memc' a) ->
  (* the step's own memnorm keep (an engine run's _inv twin, a callee's m-form keep): EXB's exv_rm carries
     `memnorm (e_mem E) -> memnorm memc`, which a view-level agreement cannot move (kit 4f18c75d4900, YSRrMemnorm.v) *)
  (YAkMemnorm.memnorm rsegs memc -> YAkMemnorm.memnorm rsegs memc') ->
  EXN_regs_kept regs regs' ->
  EXB (fx := fxc) B ARx SK E lyc Sc Hpc Wc regs' memc' mdc' k' pos.

(* in->p and in->differs rewritten as well (B 0x83ed0, 0x83ee0) *)
Definition EXN_keepM_cur : Prop := forall fxc lyc Sc Hpc Wc regs memc mdc k regs' memc' mdc' k',
  EXV_PRE B ARx E -> EXB (fx := fxc) B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos ->
  AJ lyc Sc Hpc Wc memc' mdc' k' ->
  (forall z, 0 <= z < 2 ^ 64 -> ~ EXN_wz lyc z -> ~ (e_q E <= z < e_q E + 8) -> ~ (e_q E + 32 <= z < e_q E + 36) ->
     aview rsegs (w_H Wc) memc' z = aview rsegs (w_H Wc) memc z) ->
  (forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) memc' a) ->
  (YAkMemnorm.memnorm rsegs memc -> YAkMemnorm.memnorm rsegs memc') ->
  EXN_regs_kept regs regs' ->
  EXB (fx := fxc) B ARx SK E lyc Sc Hpc Wc regs' memc' mdc' k' pos.

(* the two spills of EXN_base survive any write the segment makes outside them (they are at s1 + 144 / s1 + 152,
   inside the write zone, so M's lemma does not carry them: a piece re-derives them with this) *)
Definition EXN_keep_spill : Prop := forall Wc memc memc' o v,
  exv_spill E Wc memc o v ->
  (forall z, exv_s1 E + o <= z < exv_s1 E + o + 8 -> aview rsegs (w_H Wc) memc' z = aview rsegs (w_H Wc) memc z) ->
  exv_spill E Wc memc' o v.
End c.
