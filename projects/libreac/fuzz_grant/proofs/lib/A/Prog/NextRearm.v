(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a segment of reac_headamp_tx_next on fuzz_grant.asan (NextRearm), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v. *)
(* The re-arm block of reac_headamp_tx_next on the ASan build (fuzz_grant.asan 0x85404, the slot
   lib/A/Prog/NextRearmDefs.v names REARM) through the shared epilogue to the return: the walk of
   the cut nx_rearm_spec.

   The re-assert tail has ticked the silence counter at 456 and found the period reached. The
   block clears the counter, copies the remembered scene (the bytes at 449 and 450) into 436 and
   437, clears the replay cursor (440) and the wait counter (444), sets 448 to 1, and returns 0;
   the three bytes the caller holds are not written. The table it leaves is Pau Aliagas's
   HeadampI1.rearm.

   Seven instrumented accesses load the shadow byte at (a >> 3) + 0x7fff8000 and branch to the
   error path (a call of __asan_report_* ), which the proof shows is not reached. The engine
   decides each inside the run, with no obligation: for the counter at 456 (the slot 0x85404) the
   granule is only partly usable (the table is 460 bytes), so the branch goes to the slow block,
   which compares the shadow byte with (a1 & 7) + 3 for a1 = tx + 456 and returns to 0x8540c; for
   the six others (0x85414, 0x85428, 0x85440, 0x8544c, 0x85464, 0x85480) the shadow entry
   mkSHE 10 0 460 covers the whole granule, so the loaded shadow byte is 0 and the branch falls
   through. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import PaRun PaShadow GrantSyms GrantList GrantPa.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import PaJournal GrantPaLib GrantBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import Mem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import
HeadampModel NextModel NextLemmas SlotNeeds_c HeadampI1.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
NextArith HeadampTxEffective HeadampTxNext NextReplayDefs NextRearmDefs.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import YC1g.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require GrantFrame.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------------------------------------------------------------- *)
(* The bytes of HeadampI1.rearm, one at a time.                       *)

Lemma rr_tb_set4_0 : forall T k l, length T = 460%nat -> 0 <= k -> k + 4 <= 460 ->
  k <= l < k + 4 -> tb (set4 T k 0) l = 0.
Proof.
  intros T k l HL Hk Hk4 Hl.
  assert (Hj : l - k = 0 \/ l - k = 1 \/ l - k = 2 \/ l - k = 3) by lia.
  replace l with (k + (l - k)) by lia.
  destruct Hj as [-> | [-> | [-> | ->]]];
    rewrite (tb_set4_in T k 0) by (first [exact HL | lia]); reflexivity.
Qed.

Lemma rr_tb_setb_ne : forall T k v i, length T = 460%nat -> 0 <= k < 460 -> 0 <= i < 460 -> i <> k ->
  tb (setb T k v) i = tb T i.
Proof.
  intros T k v i HL Hk Hi Hne. rewrite (tb_setb_if T k v i HL Hk Hi).
  rewrite (proj2 (Z.eqb_neq i k) Hne). reflexivity.
Qed.

Lemma rr_tb_setb_eq : forall T k v, length T = 460%nat -> 0 <= k < 460 -> 0 <= v < 256 ->
  tb (setb T k v) k = v.
Proof.
  intros T k v HL Hk Hv. rewrite (tb_setb_if T k v k HL Hk Hk), Z.eqb_refl.
  apply Z.mod_small. exact Hv.
Qed.

(* The memory at REARM holds the table with the silence counter ticked: every byte below 456
   is the table's. *)
Lemma rr_tick_keep : forall X l, length X = 460%nat -> 0 <= l < 456 ->
  tb (set4 X 456 (u32 X 456 + 1)) l = tb X l.
Proof. intros X l HL Hl. apply tb_set4_out; first [exact HL | lia]. Qed.

Section rearm_bytes.
Variable X : list byte.
Hypothesis HL : length X = 460%nat.
Let X1 := set4 X 456 (u32 X 456 + 1).
Let X2 := setb X1 448 1.
Let X3 := set4 X2 456 0.
Let X4 := setb X3 436 (tb X 449).
Let X5 := setb X4 437 (tb X 450).
Let X6 := set4 X5 440 0.
Let L1 : length X1 = 460%nat := len_set4 X 456 _ HL ltac:(lia) ltac:(lia).
Let L2 : length X2 = 460%nat := len_setb X1 448 1 L1 ltac:(lia).
Let L3 : length X3 = 460%nat := len_set4 X2 456 0 L2 ltac:(lia) ltac:(lia).
Let L4 : length X4 = 460%nat := len_setb X3 436 _ L3 ltac:(lia).
Let L5 : length X5 = 460%nat := len_setb X4 437 _ L4 ltac:(lia).
Let L6 : length X6 = 460%nat := len_set4 X5 440 0 L5 ltac:(lia) ltac:(lia).

Lemma rr_rearm_eq : rearm X = set4 X6 444 0.
Proof. reflexivity. Qed.

Lemma rr_byte_keep : forall l, 0 <= l < 460 -> ~ (436 <= l < 438) -> ~ (440 <= l < 449) ->
  ~ (456 <= l < 460) -> tb (rearm X) l = tb X l.
Proof.
  intros l Hl H1 H2 H3. rewrite rr_rearm_eq.
  rewrite (tb_set4_out X6 444 0 l L6) by lia. unfold X6.
  rewrite (tb_set4_out X5 440 0 l L5) by lia. unfold X5.
  rewrite (rr_tb_setb_ne X4 437 _ l L4) by lia. unfold X4.
  rewrite (rr_tb_setb_ne X3 436 _ l L3) by lia. unfold X3.
  rewrite (tb_set4_out X2 456 0 l L2) by lia. unfold X2.
  rewrite (rr_tb_setb_ne X1 448 1 l L1) by lia. unfold X1.
  apply tb_set4_out; first [exact HL | lia].
Qed.

Lemma rr_byte_436 : tb (rearm X) 436 = tb X 449.
Proof.
  rewrite rr_rearm_eq.
  rewrite (tb_set4_out X6 444 0 436 L6) by lia. unfold X6.
  rewrite (tb_set4_out X5 440 0 436 L5) by lia. unfold X5.
  rewrite (rr_tb_setb_ne X4 437 _ 436 L4) by lia. unfold X4.
  apply rr_tb_setb_eq; [exact L3 | lia | apply HeadampTxEffective.tb_range].
Qed.

Lemma rr_byte_437 : tb (rearm X) 437 = tb X 450.
Proof.
  rewrite rr_rearm_eq.
  rewrite (tb_set4_out X6 444 0 437 L6) by lia. unfold X6.
  rewrite (tb_set4_out X5 440 0 437 L5) by lia. unfold X5.
  apply rr_tb_setb_eq; [exact L4 | lia | apply HeadampTxEffective.tb_range].
Qed.

Lemma rr_byte_448 : tb (rearm X) 448 = 1.
Proof.
  rewrite rr_rearm_eq.
  rewrite (tb_set4_out X6 444 0 448 L6) by lia. unfold X6.
  rewrite (tb_set4_out X5 440 0 448 L5) by lia. unfold X5.
  rewrite (rr_tb_setb_ne X4 437 _ 448 L4) by lia. unfold X4.
  rewrite (rr_tb_setb_ne X3 436 _ 448 L3) by lia. unfold X3.
  rewrite (tb_set4_out X2 456 0 448 L2) by lia. unfold X2.
  apply rr_tb_setb_eq; [exact L1 | lia | lia].
Qed.

Lemma rr_byte_zero : forall l, 440 <= l < 448 \/ 456 <= l < 460 -> tb (rearm X) l = 0.
Proof.
  intros l Hl. rewrite rr_rearm_eq.
  destruct (Z_lt_le_dec l 444) as [Ha | Ha].
  - rewrite (tb_set4_out X6 444 0 l L6) by lia. unfold X6.
    destruct (Z_lt_le_dec l 448) as [Hb | Hb].
    + apply rr_tb_set4_0; [exact L5 | lia | lia | lia].
    + rewrite (tb_set4_out X5 440 0 l L5) by lia. unfold X5.
      rewrite (rr_tb_setb_ne X4 437 _ l L4) by lia. unfold X4.
      rewrite (rr_tb_setb_ne X3 436 _ l L3) by lia. unfold X3.
      apply rr_tb_set4_0; [exact L2 | lia | lia | lia].
  - destruct (Z_lt_le_dec l 448) as [Hb | Hb].
    + apply rr_tb_set4_0; [exact L6 | lia | lia | lia].
    + rewrite (tb_set4_out X6 444 0 l L6) by lia. unfold X6.
      rewrite (tb_set4_out X5 440 0 l L5) by lia. unfold X5.
      rewrite (rr_tb_setb_ne X4 437 _ l L4) by lia. unfold X4.
      rewrite (rr_tb_setb_ne X3 436 _ l L3) by lia. unfold X3.
      apply rr_tb_set4_0; [exact L2 | lia | lia | lia].
Qed.
End rearm_bytes.

(* One byte of a stored word, read back. *)
Lemma rr_bow_lit : forall z j, 0 <= z < 2 ^ 64 ->
  YP09.byte_of_word (Z_to_bv 64 z) j = Z_to_bv 8 (Z.shiftr z (8 * j)).
Proof. intros z j Hz. unfold YP09.byte_of_word. rewrite unsigned_lit_small by exact Hz. reflexivity. Qed.

Lemma rr_bow_byte : forall z, 0 <= z < 256 -> YP09.byte_of_word (Z_to_bv 64 z) 0 = Z_to_bv 8 z.
Proof. intros z Hz. rewrite rr_bow_lit by lia. rewrite Z.mul_0_r, Z.shiftr_0_r. reflexivity. Qed.

Lemma rr_bow_zero : forall j, YP09.byte_of_word (Z_to_bv 64 0) j = Z_to_bv 8 0.
Proof. intros j. rewrite rr_bow_lit by lia. rewrite Z.shiftr_0_l. reflexivity. Qed.

(* ---------------------------------------------------------------- *)
(* The symbolic state at REARM.                                       *)

(* (a >> 3) + 0x7fff8000 for a = tx + o: the shadow byte's address as the engine builds it. *)
Definition SHX (o : Z) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 o) (SLit 3)) (SOff 32 0).

(* Atom 45 is the caller's stack pointer (the block runs on the frame the prologue took, so the
   machine's sp is that atom less 80), and 46..55 are the ten registers the prologue saved
   (ra, s0, s1, s2..s8), which the epilogue reads back. *)
Definition STKR : YP09.region := YP09.mkRegion (Some 45%nat) (-80) 0 (-80) (-80)
  [ YP09.mkChunk (-8) (CVal 8 (SOff 46 0)); YP09.mkChunk (-16) (CVal 8 (SOff 47 0));
    YP09.mkChunk (-24) (CVal 8 (SOff 48 0)); YP09.mkChunk (-32) (CVal 8 (SOff 49 0));
    YP09.mkChunk (-40) (CVal 8 (SOff 50 0)); YP09.mkChunk (-48) (CVal 8 (SOff 51 0));
    YP09.mkChunk (-56) (CVal 8 (SOff 52 0)); YP09.mkChunk (-64) (CVal 8 (SOff 53 0));
    YP09.mkChunk (-72) (CVal 8 (SOff 54 0)); YP09.mkChunk (-80) (CVal 8 (SOff 55 0)) ].
(* The table's bytes the block writes (436..448 and 456..459), and the scene byte at 449 it
   reads (atom 39). Every other byte of the table is outside the walk's write windows. *)
Definition RW1 : YP09.region := YP09.mkRegion (Some 10%nat) 436 449 436 449 [].
Definition RR9 : YP09.region :=
  YP09.mkRegion (Some 10%nat) 449 450 449 449 [YP09.mkChunk 449 (CVal 1 (SOff 39 0))].
Definition RW2 : YP09.region := YP09.mkRegion (Some 10%nat) 456 460 456 460 [].
Definition rr_regs : list YP09.region := [ STKR; RW1; RR9; RW2 ].
Definition rr_atoms : list (nat * afact) :=
  [ (45%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, PTRN 4); (32%nat, mkAF SB_NX SB_NX 0);
    (12%nat, mkAF 0 255 0); (39%nat, mkAF 0 255 0) ].
Definition sr_r : list sv :=
  sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms
    (2%bv : bv 5) (SOff 45 (-80)))
    (5%bv : bv 5) (SOff 32 0))
    (6%bv : bv 5) (SHX 437))
    (11%bv : bv 5) (SOff 10 456))
    (14%bv : bv 5) (SHX 456).
Definition ss_r : sstate := mkSS REARM sr_r rr_regs None (mkFacts rr_atoms [] []).
Definition SH_R : list shent := [ mkSHE 10 0 460 ].

Definition rr_extra (regs : bvmap 5 word) (Tj : list byte) : list word :=
  map (Z_to_bv 64) [ SB_NX; 0; 0; 0; 0; 0; 0; tb Tj 449; 0; 0; 0; 0; 0 ]
  ++ [ getr regs 2; getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19;
       getr regs 20; getr regs 21; getr regs 22; getr regs 23; getr regs 24 ].

Lemma shx_denot : forall E tx o, ew E 10 = Z_to_bv 64 tx -> ew E 32 = Z_to_bv 64 SB_NX ->
  0 <= tx -> 0 <= o -> tx + o < 2 ^ 47 ->
  sv_denot E (SHX o) = w64 (SHADOW_OFF + (tx + o) / 8).
Proof.
  intros E tx o H10 H32 Ht Ho Hto. rewrite denot_lit_U. unfold w64. f_equal. unfold SHX.
  rewrite (U_SAlu E ALU_ADD (SAlu ALU_SRL (SOff 10 o) (SLit 3)) (SOff 32 0)). cbn [zalu_raw].
  rewrite (U_SAlu E ALU_SRL (SOff 10 o) (SLit 3)). cbn [zalu_raw].
  rewrite (U_atom_off E 10 tx o H10) by lia. rewrite U_SLit.
  rewrite (U_atom E 32 SB_NX H32) by (unfold SB_NX; lia).
  change (Z.land (zcanon 3) 63) with 3.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  assert (Hd : 0 <= (tx + o) / 8 <= tx + o) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  rewrite (zcanon_id ((tx + o) / 8)) by (unfold M64; lia).
  rewrite zcanon_id by (unfold M64, SB_NX; lia). unfold SHADOW_OFF, SB_NX. lia.
Qed.

(* The bytes the walk may write. *)
Lemma rr_wr : forall E tx a, bv_unsigned (ew E 10) = tx -> in_wrange E rr_regs a ->
  (tx + 436 <= a < tx + 449) \/ (tx + 456 <= a < tx + 460).
Proof.
  intros E tx a E10 (r & Hin & Ha). unfold rr_regs in Hin. cbn [In] in Hin.
  destruct Hin as [<- | [<- | [<- | [<- | []]]]]; unfold STKR, RW1, RR9, RW2 in Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite ?E10 in Ha; lia.
Qed.

(* A register of the state the run leaves, as a value of the environment. *)
Ltac rr_reg HS r v pf H :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?vl ?Ex ?ss (restrict ?Hh ?ms) =>
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    assert (H : getr (ms_regs ms) r = v)
      by (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ss ms r HS) _);
          change (sv_denot Ex e = v); pf)
  end.
Ltac rr_pf EX :=
  cbn [sv_denot extK ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia;
  rewrite EX, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity.
Ltac rr_in := cbn [In]; repeat first [left; reflexivity | right].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).

Definition RE (regsj regs : bvmap 5 word) (Tj : list byte) : env :=
  Eimg (Ereg regsj (rr_extra regs Tj)).

(* A byte outside the walk's write windows is as it was. *)
Lemma rr_keep_byte : forall E (W : world SEGS) m1 m2 tx a,
  bv_unsigned (ew E 10) = tx ->
  frame_of E rr_regs (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) -> 0 <= a < 2 ^ 64 ->
  ~ (tx + 436 <= a < tx + 449) -> ~ (tx + 456 <= a < tx + 460) ->
  mbyte SEGS (mrestrict (w_H W) m2) a = mbyte SEGS (mrestrict (w_H W) m1) a.
Proof.
  intros E W m1 m2 tx a E10 HF Ha H1 H2. unfold mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
  intros Hw. destruct (rr_wr E tx _ E10 Hw) as [Hx | Hx]; rewrite unsigned_lit_small in Hx by lia; lia.
Qed.

Lemma rr_same : forall E (W : world SEGS) memc m1 m2 (sp tx chp parp valp d : Z),
  bv_unsigned (ew E 10) = tx ->
  frame_of E rr_regs (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) ->
  nx_same W memc m1 sp tx chp parp valp d -> nx_same W memc m2 sp tx chp parp valp d.
Proof.
  intros E W memc m1 m2 sp tx chp parp valp d E10 HF HS x H1 H2.
  rewrite (HF x); [exact (HS x H1 H2)|].
  intros Hw. destruct (rr_wr E tx _ E10 Hw) as [Hx | Hx]; apply H2; unfold nx_touch2; lia.
Qed.

Lemma rr_grows_pres : forall (W : world SEGS) m1 m2 a,
  mem_grows (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) ->
  apresent (w_H W) m1 a -> apresent (w_H W) m2 a.
Proof.
  intros W m1 m2 a HG (Hh & b & Hb). split; [exact Hh|].
  assert (HN : mrestrict (w_H W) m1 (Z_to_bv 64 a) <> None)
    by (unfold mrestrict; rewrite Hh, Hb; discriminate).
  pose proof (HG _ HN) as H2. unfold mrestrict in H2. rewrite Hh in H2.
  destruct (m2 (Z_to_bv 64 a)) as [b2|] eqn:Hb2; [exists b2; reflexivity | exfalso; exact (H2 eq_refl)].
Qed.

Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Let RUN := paj_run B LAWS.
Let RET := paj_ret_at (PL := PL_grant) (PI := PI).

Lemma rr_awr : forall (E : env) STK sp0 FP ly S lyc Sc own (tx : Z),
  bv_unsigned (ew E 10) = tx ->
  (forall a, tx <= a < tx + TX_SIZE ->
     awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
  awr_ok E rr_regs STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own.
Proof.
  intros E STK sp0 FP ly S lyc Sc own tx E10 Htab a Ha.
  destruct (rr_wr E tx a E10 Ha) as [Hx | Hx]; apply Htab; unfold TX_SIZE; lia.
Qed.

(* The symbolic state at REARM, seated on the machine the cut gives. *)
Lemma rr_seat : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS)
    memc mdc k (regs regsj : bvmap 5 word) memj mdj (tx chp parp valp : Z) (T Tj : list byte),
  nx_ctx B STK sp0 FP ly S lyc Sc own W memc mdc regs tx chp parp valp T ->
  nx_mid B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs memj mdj tx chp parp valp (tx + 432) ->
  nx_saved W memj regs (spZ regs) ->
  obj_at SEGS (mrestrict (w_H W) memj) tx LAY_TX (tx_vals (set4 Tj 456 (u32 Tj 456 + 1))) ->
  length Tj = 460%nat ->
  nx_at_rearm regs regsj tx (tb Tj 450) ->
  st_ok_pi SEGS VAL (RE regsj regs Tj) ss_r
    (restrict (w_H W) (mkst regsj (Z_to_bv 64 (BASE + REARM)) memj (seg_rom SEGS)))
  /\ sh_ok SEGS BxN SH_R (RE regsj regs Tj) (mrestrict (w_H W) memj).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regsj memj mdj
    tx chp parp valp T Tj HCTX HMID HSAV HOBJ HTL HAT.
  pose proof HCTX as (HAR & Hg & Hoc & Hop & Hov & Dcp & Dcv & Dpv & Pc & Pp & Pv & Rac & Rap & Rav &
    Hspr & Hceil & Hsp16 & Hslo & Hshi & Hwtab & Hwc & Hwp & Hwv & Hret & Hra4 & Hgp & Htp &
    Q10 & Q11 & Q12 & Q13 & HTL0 & HI & Hobjc & Hpresc).
  pose proof HMID as (HJ & HSAME & HpresS & HpresK).
  pose proof HAT as (HKG & R2 & R5 & R6 & R10 & R11 & R12 & R14).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (proj1 HJ) as HARj.
  destruct (al_blocks _ _ LAWS lyc Sc W memj mdj tx TX_SIZE HARj Hg)
    as (Hg16 & Hg4096 & Hgceil & Hgia & Hgpres & _).
  change (req_size TX_SIZE) with 460 in Hgceil, Hgia, Hgpres.
  pose proof (proj1 (tx_obj_bytes SEGS _ _ _) HOBJ) as HBY.
  pose proof (HeadampTxEffective.tb_range Tj 449) as R449.
  pose proof (HeadampTxEffective.tb_range Tj 450) as R450.
  set (E := RE regsj regs Tj).
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regsj (rr_extra regs Tj)) n)
    by (intros n Hn; unfold E, RE; apply Eimg_low; exact Hn).
  assert (E10 : ew E 10 = w64 tx)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsj _ 10 10%bv eq_refl); exact R10).
  assert (E12 : ew E 12 = w64 (tb Tj 450))
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsj _ 12 12%bv eq_refl); exact R12).
  assert (E32 : ew E 32 = w64 SB_NX)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsj _ 0)).
  assert (E39 : ew E 39 = w64 (tb Tj 449))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsj _ 7)).
  assert (E45 : ew E 45 = getr regs 2)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsj _ 13)).
  assert (E46 : ew E 46 = getr regs 1)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsj _ 14)).
  assert (E47 : ew E 47 = getr regs 8)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsj _ 15)).
  assert (E48 : ew E 48 = getr regs 9)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsj _ 16)).
  assert (E49 : ew E 49 = getr regs 18)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsj _ 17)).
  assert (E50 : ew E 50 = getr regs 19)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsj _ 18)).
  assert (E51 : ew E 51 = getr regs 20)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsj _ 19)).
  assert (E52 : ew E 52 = getr regs 21)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsj _ 20)).
  assert (E53 : ew E 53 = getr regs 22)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsj _ 21)).
  assert (E54 : ew E 54 = getr regs 23)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsj _ 22)).
  assert (E55 : ew E 55 = getr regs 24)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsj _ 23)).
  assert (U10 : bv_unsigned (ew E 10) = tx) by (rewrite E10; apply unsigned_lit_small; lia).
  assert (U12 : bv_unsigned (ew E 12) = tb Tj 450) by (rewrite E12; apply unsigned_lit_small; lia).
  assert (U32 : bv_unsigned (ew E 32) = SB_NX) by (rewrite E32; apply unsigned_lit_small; unfold SB_NX; lia).
  assert (U39 : bv_unsigned (ew E 39) = tb Tj 449) by (rewrite E39; apply unsigned_lit_small; lia).
  assert (U45 : bv_unsigned (ew E 45) = spZ regs) by (rewrite E45; reflexivity).
  assert (HUB : U E BxN = SHADOW_OFF)
    by (unfold U, BxN; cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned;
        rewrite unsigned_lit_small by (unfold SB_NX; lia); reflexivity).
  split.
  - rewrite restrict_mkst_fx. unfold ss_r. apply pa_entry_st_ok_full.
    + unfold sr_r.
      apply regs_ok_pin; [| intros X; discriminate X |].
      2:{ rewrite R14. symmetry. apply shx_denot; [exact E10 | exact E32 | lia | lia | lia]. }
      apply regs_ok_pin; [| intros X; discriminate X |].
      2:{ rewrite R11. cbn [sv_denot]. rewrite U10. reflexivity. }
      apply regs_ok_pin; [| intros X; discriminate X |].
      2:{ rewrite R6. symmetry. apply shx_denot; [exact E10 | exact E32 | lia | lia | lia]. }
      apply regs_ok_pin; [| intros X; discriminate X |].
      2:{ rewrite R5. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
      apply regs_ok_pin; [| intros X; discriminate X |].
      2:{ rewrite R2. cbn [sv_denot]. rewrite U45. unfold w64, NEXT_STK. f_equal; lia. }
      unfold E, RE. apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + unfold rr_regs, STKR, RW1, RR9, RW2.
      repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      * rewrite U45. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        pose proof HSAV as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10).
        repeat apply Forall_cons; try apply Forall_nil.
        -- apply (chunk_ok_val SEGS E _ (spZ regs) (-8) 8 (SOff 46 0) (bv_unsigned (getr regs 1)));
             [ cbn [sv_denot]; rewrite E46, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
             | pose proof (bv_unsigned_in_range 64 (getr regs 1)); unfold bv_modulus in *; cbn; lia
             | cbn; lia
             | replace (spZ regs + -8) with (spZ regs - 8) by lia; exact S1 ].
        -- apply (chunk_ok_val SEGS E _ (spZ regs) (-16) 8 (SOff 47 0) (bv_unsigned (getr regs 8)));
             [ cbn [sv_denot]; rewrite E47, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
             | pose proof (bv_unsigned_in_range 64 (getr regs 8)); unfold bv_modulus in *; cbn; lia
             | cbn; lia
             | replace (spZ regs + -16) with (spZ regs - 16) by lia; exact S2 ].
        -- apply (chunk_ok_val SEGS E _ (spZ regs) (-24) 8 (SOff 48 0) (bv_unsigned (getr regs 9)));
             [ cbn [sv_denot]; rewrite E48, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
             | pose proof (bv_unsigned_in_range 64 (getr regs 9)); unfold bv_modulus in *; cbn; lia
             | cbn; lia
             | replace (spZ regs + -24) with (spZ regs - 24) by lia; exact S3 ].
        -- apply (chunk_ok_val SEGS E _ (spZ regs) (-32) 8 (SOff 49 0) (bv_unsigned (getr regs 18)));
             [ cbn [sv_denot]; rewrite E49, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
             | pose proof (bv_unsigned_in_range 64 (getr regs 18)); unfold bv_modulus in *; cbn; lia
             | cbn; lia
             | replace (spZ regs + -32) with (spZ regs - 32) by lia; exact S4 ].
        -- apply (chunk_ok_val SEGS E _ (spZ regs) (-40) 8 (SOff 50 0) (bv_unsigned (getr regs 19)));
             [ cbn [sv_denot]; rewrite E50, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
             | pose proof (bv_unsigned_in_range 64 (getr regs 19)); unfold bv_modulus in *; cbn; lia
             | cbn; lia
             | replace (spZ regs + -40) with (spZ regs - 40) by lia; exact S5 ].
        -- apply (chunk_ok_val SEGS E _ (spZ regs) (-48) 8 (SOff 51 0) (bv_unsigned (getr regs 20)));
             [ cbn [sv_denot]; rewrite E51, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
             | pose proof (bv_unsigned_in_range 64 (getr regs 20)); unfold bv_modulus in *; cbn; lia
             | cbn; lia
             | replace (spZ regs + -48) with (spZ regs - 48) by lia; exact S6 ].
        -- apply (chunk_ok_val SEGS E _ (spZ regs) (-56) 8 (SOff 52 0) (bv_unsigned (getr regs 21)));
             [ cbn [sv_denot]; rewrite E52, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
             | pose proof (bv_unsigned_in_range 64 (getr regs 21)); unfold bv_modulus in *; cbn; lia
             | cbn; lia
             | replace (spZ regs + -56) with (spZ regs - 56) by lia; exact S7 ].
        -- apply (chunk_ok_val SEGS E _ (spZ regs) (-64) 8 (SOff 53 0) (bv_unsigned (getr regs 22)));
             [ cbn [sv_denot]; rewrite E53, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
             | pose proof (bv_unsigned_in_range 64 (getr regs 22)); unfold bv_modulus in *; cbn; lia
             | cbn; lia
             | replace (spZ regs + -64) with (spZ regs - 64) by lia; exact S8 ].
        -- apply (chunk_ok_val SEGS E _ (spZ regs) (-72) 8 (SOff 54 0) (bv_unsigned (getr regs 23)));
             [ cbn [sv_denot]; rewrite E54, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
             | pose proof (bv_unsigned_in_range 64 (getr regs 23)); unfold bv_modulus in *; cbn; lia
             | cbn; lia
             | replace (spZ regs + -72) with (spZ regs - 72) by lia; exact S9 ].
        -- apply (chunk_ok_val SEGS E _ (spZ regs) (-80) 8 (SOff 55 0) (bv_unsigned (getr regs 24)));
             [ cbn [sv_denot]; rewrite E55, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
             | pose proof (bv_unsigned_in_range 64 (getr regs 24)); unfold bv_modulus in *; cbn; lia
             | cbn; lia
             | replace (spZ regs + -80) with (spZ regs - 80) by lia; exact S10 ].
      * rewrite U10. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. apply (apresent_writable SEGS). exact (proj1 (Hgpres (tx + o) ltac:(lia))).
      * rewrite U10. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [| apply Forall_nil].
        apply (chunk_ok_val SEGS E _ tx 449 1 (SOff 39 0) (tb Tj 449));
          [ cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
          | cbn; lia | cbn; lia |].
        rewrite <- (rr_tick_keep Tj 449 HTL ltac:(lia)).
        apply (nx_val1 (mrestrict (w_H W) memj) tx _ 449 HBY). vm_compute. reflexivity.
      * rewrite U10. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. apply (apresent_writable SEGS). exact (proj1 (Hgpres (tx + o) ltac:(lia))).
    + apply pairwise_disjoint_of_extents.
      unfold rr_regs, STKR, RW1, RR9, RW2, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
      cbn [base_val]. rewrite U45, U10.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      unfold NEXT_STK in *. repeat split; lia.
    + split; [| split; [exact I | exact I]].
      cbn [rr_atoms f_atoms atoms_ok]. unfold afact_ok, PTRN.
      cbn [af_lo af_hi af_al2].
      rewrite U45, U10, U32, U12, U39.
      change (2 ^ 4) with 16. rewrite ?Z.pow_0_r, ?Z.mod_1_r.
      unfold SB_NX, NEXT_STK in *.
      repeat match goal with |- _ /\ _ => split end; lia.
  - unfold sh_ok, SH_R. constructor; [| constructor].
    apply (shent_ok_of_block SEGS B LAWS lyc Sc W memj mdj E BxN 10 tx TX_SIZE 0 460 HARj Hg HUB).
    + unfold U. cbn [sv_denot]. rewrite U10, Z.add_0_r. apply unsigned_lit_small. lia.
    + lia.
    + change (req_size TX_SIZE) with 460. lia.
Qed.

Theorem pb_nx_rearm : nx_rearm_spec B.
Proof.
  unfold nx_rearm_spec.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regsj memj mdj
    tx chp parp valp T Tj HCTX HMID HSAV HOBJ HTL HMOD HAT.
  destruct (rr_seat STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regsj memj mdj
    tx chp parp valp T Tj HCTX HMID HSAV HOBJ HTL HAT) as [HS SHOK].
  pose proof HCTX as (HAR & Hg & Hoc & Hop & Hov & Dcp & Dcv & Dpv & Pc & Pp & Pv & Rac & Rap & Rav &
    Hspr & Hceil & Hsp16 & Hslo & Hshi & Hwtab & Hwc & Hwp & Hwv & Hret & Hra4 & Hgp & Htp &
    Q10 & Q11 & Q12 & Q13 & HTL0 & HI & Hobjc & Hpresc).
  pose proof HMID as (HJ & HSAME & HpresS & HpresK).
  pose proof HAT as (HKG & R2 & R5 & R6 & R10 & R11 & R12 & R14).
  pose proof (HeadampTxEffective.tb_range Tj 449) as R449.
  pose proof (HeadampTxEffective.tb_range Tj 450) as R450.
  pose proof (proj1 HJ) as HARj.
  destruct (al_blocks _ _ LAWS lyc Sc W memj mdj tx TX_SIZE HARj Hg) as (Hg16 & Hg4096 & Hgceil & _).
  change (req_size TX_SIZE) with 460 in Hgceil.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (proj1 (tx_obj_bytes SEGS _ _ _) HOBJ) as HBY.
  remember (RE regsj regs Tj) as E eqn:HEdef.
  assert (HEI : img_env VAL A_LIM E) by (subst E; unfold RE; apply Eimg_env).
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regsj (rr_extra regs Tj)) n)
    by (intros n Hn; subst E; unfold RE; apply Eimg_low; exact Hn).
  assert (E3 : ew E 3 = getr regs 3)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsj _ 3 3%bv eq_refl);
        exact (HKG 3%bv ltac:(rr_in))).
  assert (E4 : ew E 4 = getr regs 4)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsj _ 4 4%bv eq_refl);
        exact (HKG 4%bv ltac:(rr_in))).
  assert (E25 : ew E 25 = getr regs 25)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsj _ 25 25%bv eq_refl);
        exact (HKG 25%bv ltac:(rr_in))).
  assert (E26 : ew E 26 = getr regs 26)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsj _ 26 26%bv eq_refl);
        exact (HKG 26%bv ltac:(rr_in))).
  assert (E27 : ew E 27 = getr regs 27)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsj _ 27 27%bv eq_refl);
        exact (HKG 27%bv ltac:(rr_in))).
  assert (E10 : ew E 10 = w64 tx)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsj _ 10 10%bv eq_refl); exact R10).
  assert (E12 : ew E 12 = w64 (tb Tj 450))
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsj _ 12 12%bv eq_refl); exact R12).
  assert (E39 : ew E 39 = w64 (tb Tj 449))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsj _ 7)).
  assert (E45 : ew E 45 = getr regs 2)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsj _ 13)).
  assert (E46 : ew E 46 = getr regs 1)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsj _ 14)).
  assert (E47 : ew E 47 = getr regs 8)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsj _ 15)).
  assert (E48 : ew E 48 = getr regs 9)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsj _ 16)).
  assert (E49 : ew E 49 = getr regs 18)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsj _ 17)).
  assert (E50 : ew E 50 = getr regs 19)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsj _ 18)).
  assert (E51 : ew E 51 = getr regs 20)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsj _ 19)).
  assert (E52 : ew E 52 = getr regs 21)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsj _ 20)).
  assert (E53 : ew E 53 = getr regs 22)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsj _ 21)).
  assert (E54 : ew E 54 = getr regs 23)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsj _ 22)).
  assert (E55 : ew E 55 = getr regs 24)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsj _ 23)).
  assert (U10 : bv_unsigned (ew E 10) = tx) by (rewrite E10; apply unsigned_lit_small; lia).
  clear HEdef EL.
  unfold cfg_at. change (w64 (BASE + REARM)) with (Z_to_bv 64 (BASE + REARM)).
  (* One run from REARM to the epilogue's ret: the seven shadow checks are decided inside it. *)
  paj_run_tok RUN HS HJ SHOK BspanN;
    [ exact (rr_awr E STK sp0 FP ly S lyc Sc own tx U10 Hwtab) | ].
  lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into msF end.
  rr_reg HS (1%bv : bv 5) (getr regs 1) ltac:(rr_pf E46) R1f.
  rr_reg HS (2%bv : bv 5) (getr regs 2) ltac:(rr_pf E45) R2f.
  rr_reg HS (3%bv : bv 5) (getr regs 3) ltac:(rr_pf E3) R3f.
  rr_reg HS (4%bv : bv 5) (getr regs 4) ltac:(rr_pf E4) R4f.
  rr_reg HS (8%bv : bv 5) (getr regs 8) ltac:(rr_pf E47) R8f.
  rr_reg HS (9%bv : bv 5) (getr regs 9) ltac:(rr_pf E48) R9f.
  rr_reg HS (18%bv : bv 5) (getr regs 18) ltac:(rr_pf E49) R18f.
  rr_reg HS (19%bv : bv 5) (getr regs 19) ltac:(rr_pf E50) R19f.
  rr_reg HS (20%bv : bv 5) (getr regs 20) ltac:(rr_pf E51) R20f.
  rr_reg HS (21%bv : bv 5) (getr regs 21) ltac:(rr_pf E52) R21f.
  rr_reg HS (22%bv : bv 5) (getr regs 22) ltac:(rr_pf E53) R22f.
  rr_reg HS (23%bv : bv 5) (getr regs 23) ltac:(rr_pf E54) R23f.
  rr_reg HS (24%bv : bv 5) (getr regs 24) ltac:(rr_pf E55) R24f.
  rr_reg HS (25%bv : bv 5) (getr regs 25) ltac:(rr_pf E25) R25f.
  rr_reg HS (26%bv : bv 5) (getr regs 26) ltac:(rr_pf E26) R26f.
  rr_reg HS (27%bv : bv 5) (getr regs 27) ltac:(rr_pf E27) R27f.
  rr_reg HS (10%bv : bv 5) (w64 0) ltac:(cbn [sv_denot]; reflexivity) R10f.
  pose proof (GrantFrame.aregs_preserved_eqs regs (ms_regs msF) R2f R3f R4f R8f R9f
    R18f R19f R20f R21f R22f R23f R24f R25f R26f R27f) as HPRES.
  (* The table's written fields, as the run leaves them. *)
  lazymatch type of HS with
  | st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) =>
    pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W) msx) 1%nat
      (YP09.mkRegion (Some 10%nat) 436 449 436 449
        [YP09.mkChunk 448 (CVal 1 (SLit 1)); YP09.mkChunk 444 (CVal 4 (SLit 0));
         YP09.mkChunk 440 (CVal 4 (SLit 0)); YP09.mkChunk 437 (CVal 1 (SOff 12 0));
         YP09.mkChunk 436 (CVal 1 (SOff 39 0))]) HS ltac:(vm_compute; reflexivity)) as HR1;
    pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W) msx) 3%nat
      (YP09.mkRegion (Some 10%nat) 456 460 456 460 [YP09.mkChunk 456 (CVal 4 (SLit 0))]) HS
      ltac:(vm_compute; reflexivity)) as HR2;
    assert (Ex10 : bv_unsigned (ew Ex 10) = tx)
      by (cbn [extK ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact U10);
    assert (Ex12 : ew Ex 12 = w64 (tb Tj 450))
      by (cbn [extK ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact E12);
    assert (Ex39 : ew Ex 39 = w64 (tb Tj 449))
      by (cbn [extK ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact E39)
  end.
  cbn [restrict ms_mem] in HR1, HR2.
  assert (HOBJ2 : obj_at SEGS (mrestrict (w_H W) (ms_mem msF)) tx LAY_TX (tx_vals (rearm Tj))).
  { apply (proj2 (tx_obj_bytes SEGS _ tx _)). intros i Hi. pose proof (tx_fbyte_range i Hi) as Hir.
    rewrite <- Z_to_bv8_tb.
    assert (Hc : (i < 436 \/ 449 <= i < 456) \/ i = 436 \/ i = 437 \/ (438 <= i < 440) \/
                 (440 <= i < 448) \/ i = 448 \/ (456 <= i < 460)) by lia.
    destruct Hc as [Hk | [-> | [-> | [Hp | [Hz | [-> | Hz2]]]]]].
    - (* a byte the walk does not write *)
      rewrite (rr_keep_byte E W memj (ms_mem msF) tx (tx + i) U10 HFr ltac:(lia) ltac:(lia) ltac:(lia)).
      rewrite (HBY i Hi). rewrite <- Z_to_bv8_tb.
      rewrite (rr_byte_keep Tj HTL i) by lia.
      rewrite (rr_tick_keep Tj i HTL) by lia. reflexivity.
    - (* 436 <- the scene byte at 449 *)
      rewrite (rr_byte_436 Tj HTL).
      replace (tx + 436) with (tx + 436 + 0) by lia.
      rewrite (byte_of_region SEGS _ _ 10%nat tx _ 436 449 436 449 436 1 (SOff 39 0) 0 HR1 Ex10
                 ltac:(rr_in) ltac:(cbn; lia)).
      f_equal. cbn [sv_denot]. rewrite Ex39, Z.add_0_r, Z_to_bv_bv_unsigned.
      apply rr_bow_byte. exact R449.
    - (* 437 <- a2, the scene width at 450 *)
      rewrite (rr_byte_437 Tj HTL).
      replace (tx + 437) with (tx + 437 + 0) by lia.
      rewrite (byte_of_region SEGS _ _ 10%nat tx _ 436 449 436 449 437 1 (SOff 12 0) 0 HR1 Ex10
                 ltac:(rr_in) ltac:(cbn; lia)).
      f_equal. cbn [sv_denot]. rewrite Ex12, Z.add_0_r, Z_to_bv_bv_unsigned.
      apply rr_bow_byte. exact R450.
    - (* 438 and 439 are padding *)
      exfalso. assert (i = 438 \/ i = 439) as [-> | ->] by lia; vm_compute in Hi; discriminate Hi.
    - (* 440..447 <- 0 *)
      rewrite (rr_byte_zero Tj HTL i) by lia.
      destruct (Z_lt_le_dec i 444) as [Hb | Hb].
      + replace (tx + i) with (tx + 440 + (i - 440)) by lia.
        rewrite (byte_of_region SEGS _ _ 10%nat tx _ 436 449 436 449 440 4 (SLit 0) (i - 440) HR1 Ex10
                   ltac:(rr_in) ltac:(cbn; lia)).
        cbn [sv_denot]. rewrite rr_bow_zero. reflexivity.
      + replace (tx + i) with (tx + 444 + (i - 444)) by lia.
        rewrite (byte_of_region SEGS _ _ 10%nat tx _ 436 449 436 449 444 4 (SLit 0) (i - 444) HR1 Ex10
                   ltac:(rr_in) ltac:(cbn; lia)).
        cbn [sv_denot]. rewrite rr_bow_zero. reflexivity.
    - (* 448 <- 1 *)
      rewrite (rr_byte_448 Tj HTL).
      replace (tx + 448) with (tx + 448 + 0) by lia.
      rewrite (byte_of_region SEGS _ _ 10%nat tx _ 436 449 436 449 448 1 (SLit 1) 0 HR1 Ex10
                 ltac:(rr_in) ltac:(cbn; lia)).
      cbn [sv_denot]. rewrite rr_bow_byte by lia. reflexivity.
    - (* 456..459 <- 0 *)
      rewrite (rr_byte_zero Tj HTL i) by lia.
      replace (tx + i) with (tx + 456 + (i - 456)) by lia.
      rewrite (byte_of_region SEGS _ _ 10%nat tx _ 456 460 456 460 456 4 (SLit 0) (i - 456) HR2 Ex10
                 ltac:(rr_in) ltac:(cbn; lia)).
      cbn [sv_denot]. rewrite rr_bow_zero. reflexivity. }
  pose proof (rr_same E W memc memj (ms_mem msF) (spZ regs) tx chp parp valp (tx + 432) U10 HFr HSAME)
    as HSAME2.
  assert (HpresS2 : forall a, spZ regs - NEXT_STK <= a < spZ regs -> apresent (w_H W) (ms_mem msF) a)
    by (intros a Ha; exact (rr_grows_pres W memj (ms_mem msF) a HG (HpresS a Ha))).
  assert (HpresK2 : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem msF) a)
    by (intros a Ha; exact (rr_grows_pres W memj (ms_mem msF) a HG (HpresK a Ha))).
  assert (Hd : tx <= tx + 432 < tx + TX_SIZE) by (unfold TX_SIZE; lia).
  assert (HMOD2 : next_model T tx = (0, (0, 0, 0), rearm Tj)) by exact HMOD.
  (* The return. *)
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat9. cbn [ms_regs ms_mem].
  unfold YK0s.ret_ok in Hret. rewrite R1f, Hret.
  eapply (nx_finish B LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
            (ms_regs msF) (ms_mem msF) _ tx chp parp valp (tx + 432) T (rearm Tj) 0 0 0 0
            Hd HAR Hg Hoc Hop Hov Hspr Hceil HMOD2
            ltac:(apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ)
            HPRES HSAME2 HpresS2 HpresK2 R10f HOBJ2
            ltac:(intros Hr; discriminate Hr)).
Qed.

End h.
End f.
End d.
