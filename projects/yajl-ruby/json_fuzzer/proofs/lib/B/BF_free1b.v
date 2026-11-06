(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import ZBridge.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BF_place BF_kit BF_free_kit BF_qkit.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import StrFun.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import LiaA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac lia ::= LiaA.liaA.
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import SecRanges.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= force_section_ranges.   (* [comment removed for export] *)
(* [comment removed for export] *)
Ltac aceil :=
  lazymatch goal with
  | H : _ <= alloc_ceiling <= _ |- _ => idtac
  | |- context [alloc_ceiling] => repeat match goal with H : True |- _ => clear H end; pose proof alloc_ceiling_range as CEILB
  | H : context [alloc_ceiling] |- _ => repeat match goal with H' : True |- _ => clear H' end; pose proof alloc_ceiling_range as CEILB
  | _ => first [ pose proof I as CEILB | idtac ]
  end.
Ltac pg := match goal with |- ?g => idtac "GOAL:"; idtac g end.
Ltac phyps := match goal with |- _ => repeat match goal with H : ?t |- _ => idtac H ":" t; fail end end.

Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.

(* [comment removed for export] *)
Lemma rw_CB_of_wr_at : forall m a n (k : nat), wr_at bsegs m a n -> n = Z.of_nat k -> exists bs, rw_cells bsegs m a [CB k bs].
Proof. aceil.
  intros m a n k WR E. destruct (wr_at_bytes m a n WR ltac:(lia)) as (bs & L & B).
  exists bs. split; [split|].
  - cbn. rewrite L, E, Nat2Z.id. split; [reflexivity| exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B.
  - cbn [cells_size csize]. rewrite Nat.add_0_r, <- E. exact WR.
Qed.

(* [comment removed for export] *)
Lemma u64arr_cons' : forall m A w ws, rw_cells bsegs m A [C8 w] -> u64arr bsegs m (A + 8) ws -> u64arr bsegs m A (w :: ws).
Proof. aceil.
  intros m A w ws [[_ B] W] [B2 W2]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. cbn [cells_size csize Nat.add] in W.
  split.
  - cbn [u64s]. apply bytes_at_app. split; [exact B|]. rewrite length_le8. exact B2.
  - destruct W as (W0 & W1 & Wi). destruct W2 as (V0 & V1 & Vi). split; [lia|]. split; [cbn [length]; lia|].
    intros i Hi. destruct (Z.lt_ge_cases i 8).
    + apply Wi. lia.
    + replace (A + i) with (A + 8 + (i - 8)) by lia. apply Vi. cbn [length] in Hi. lia.
Qed.

(* [comment removed for export] *)
Lemma rw_cells_app_split1b : forall segs m A cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) -> rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof. aceil.
  intros segs m A cs1 cs2 [[WF B] W]. apply cells_wf_app in WF. destruct WF as [W1 W2].
  rewrite cells_bytes_app in B. apply bytes_at_app in B. destruct B as [B1 B2]. rewrite (cells_bytes_length _ W1) in B2.
  rewrite cells_size_app in W. destruct W as (Wa & Wb & Wr).
  split; split; try (split; assumption).
  - split; [lia|]. split; [lia|]. intros i Hi. apply Wr. lia.
  - split; [lia|]. split; [lia|]. intros i Hi. replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia. apply Wr. lia.
Qed.

Section ENQ2.
Variable P : acc -> Prop.
Variables (ra sp gp tp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variable Q : machine_state -> Prop.
Variables (lo T B cb n cnt first last qb : Z) (bnext bsz : word) (SB RI cnt24 x alloc : Z) (maxc : word) (ws : list word).
Notation INST := 0xaaf58.
Notation CA := (T + 208).
(* [comment removed for export] *)
Variable nb : Z.
Hypothesis Enb : nb = SB + 24 * 2^32 + 16 * x.

Hypothesis LOC : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 64.
Hypothesis SPH : bv_unsigned sp <= 2^47.
Hypothesis HTp : placed_s T 4096.
Hypothesis HT16 : T mod 8 = 0.     (* [comment removed for export] *)
Hypothesis HSB : 0x603000 <= SB /\ SB mod 4096 = 0 /\ SB + kSpaceSize + 4096 <= alloc_ceiling.
Hypothesis HCNT : 0 <= cnt < 2^62.
Hypothesis HN : 0 <= n <= 2^27.
Hypothesis HQB : 0 <= qb /\ qb + n + 8192 < 2^64.
Hypothesis HX : 0 <= x < 2^32.
Hypothesis HAL : 0 <= alloc < 2^64.
(* [comment removed for export] *)
Hypothesis HNB : nb + 8192 <= SB + kSpaceSize /\ kHighMemBeg <= nb.
Hypothesis HNBT : nb + 8192 <= T \/ T + 4096 <= nb.
(* [comment removed for export] *)
Hypothesis HLo : cnt <> 0 -> kHighMemBeg <= last /\ last + 8192 <= alloc_ceiling /\ (last + 8192 <= T \/ T + 4096 <= last) /\ (last + 8192 <= nb \/ nb + 8192 <= last).
Hypothesis PSTK : forall a k, lo <= a -> a + Z.of_nat k <= bv_unsigned sp -> P (Z_to_bv 64 a, k).
Hypothesis PDAT : forall a k, 0xa5000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k).
Hypothesis PT : forall a k, T <= a -> a + Z.of_nat k <= T + 4096 -> P (Z_to_bv 64 a, k).
Hypothesis PNB : forall a k, nb <= a -> a + Z.of_nat k <= nb + 8192 -> P (Z_to_bv 64 a, k).
Hypothesis PLBo : cnt <> 0 -> forall a k, last <= a -> a + Z.of_nat k <= last + 8192 -> P (Z_to_bv 64 a, k).

(* [comment removed for export] *)
Definition enq_frame (m : mem) (j8 : list byte) : Prop :=
  rw_cells bsegs m (bv_unsigned sp - 64) [CB 8 j8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Definition lz8 : Z := if cnt =? 0 then 0 else 8.
Definition enq2W : list (Z * Z) :=
  [(bv_unsigned sp - 64, bv_unsigned sp); (T + 80, T + 112); (T + 2128, T + 2132); (T + 2784, T + 2792); (nb, nb + 32); (last, last + lz8)].

(* [comment removed for export] *)
Definition enq2_post (m m' : mem) (cnt24' : Z) : Prop :=
  exists junk,
     mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp) /\ wmono bsegs m m' /\ munch enq2W m m'
  /\ rw_cells bsegs m' (T + 80) [C8 (Z_to_bv 64 (cnt + 1)); C8 (Z_to_bv 64 (if cnt =? 0 then nb else first)); C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 (qb + (n + 8192)))]
  /\ rw_cells bsegs m' (T + 2128) [C4 (Z_to_bv 64 (cnt24' - 1)); C4 maxc; C8 (Z_to_bv 64 8192)]
  /\ u32arr bsegs m' (T + 2144) ws
  /\ rw_cells bsegs m' (T + 2784) [C8 (Z_to_bv 64 (alloc + 8192))]
  /\ rw_cells bsegs m' 0xaaf78 [C8 (Z_to_bv 64 SB); C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 RI)]
  /\ rw_cells bsegs m' nb [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (n + 8192)); C8 (Z_to_bv 64 1)]
  /\ u64arr bsegs m' (nb + 24) (Z_to_bv 64 cb :: junk) /\ length junk = 1020%nat
  /\ (cnt <> 0 -> rw_cells bsegs m' last [C8 (Z_to_bv 64 nb); C8 bsz; C8 (Z_to_bv 64 1021)]).

(* [comment removed for export] *)
Lemma enq2_tail : forall m (cnt24v : Z) (xra t0 t1 t2 a6 a7 xs0 xs1 xs2 xs3 xs4 xs5 t3 t4 t5 t6 : word) (j8 : list byte) (m0 : mem),
  1 <= cnt24v <= 16 -> length ws = 16%nat -> nth_error ws (Z.to_nat (cnt24v - 1)) = Some (Z_to_bv 64 x) ->
  mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp - 64) -> enq_frame m j8 -> munch enq2W m0 m -> wmono bsegs m0 m ->
  rw_cells bsegs m (T + 80) [C8 (Z_to_bv 64 cnt); C8 (Z_to_bv 64 first); C8 (Z_to_bv 64 last); C8 (Z_to_bv 64 qb)] ->
  rw_cells bsegs m (T + 2128) [C4 (Z_to_bv 64 cnt24v); C4 maxc; C8 (Z_to_bv 64 8192)] ->
  u32arr bsegs m (T + 2144) ws ->
  rw_cells bsegs m (T + 2784) [C8 (Z_to_bv 64 alloc)] ->
  rw_cells bsegs m 0xaaf78 [C8 (Z_to_bv 64 SB); C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 RI)] ->
  wr_at bsegs m nb 8192 ->
  (cnt <> 0 -> rw_cells bsegs m last [C8 bnext; C8 bsz; C8 (Z_to_bv 64 1021)]) ->
  (forall m' (t0' t1' t2' a1' a2' a5' a6' a7' : word), enq2_post m0 m' cnt24v ->
     evtA bsegs P Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (T + 80)) a1' a2' (Z_to_bv 64 cb) (Z_to_bv 64 (n + 8192)) a5' a6' a7'
                             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  evtA bsegs P Q (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp t0 t1 t2 xs0 xs1 (Z_to_bv 64 (T + 80)) (Z_to_bv 64 CA) (Z_to_bv 64 B) (Z_to_bv 64 cb) (Z_to_bv 64 n) (Z_to_bv 64 cnt24v) a6 a7
                          xs2 xs3 xs4 xs5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x36f08) fc None m (seg_rom bsegs)).
Proof. aceil.
  intros until m0. intros C24 LEN NTH MI SK FR MU WM QC PC ARR STA INS WRB LBo CONT.
  pose proof LOC as LOC0. aceil. pose proof HSB as HSB0. pose proof HNB as HNB0. unfold kSpaceSize in HSB0, HNB0. rewrite kHighMemBeg_val in HNB0.
  pose proof (placed_s_num _ _ HTp ltac:(clear; lia)) as (TQ1 & TQ2 & TQ3 & _).
  assert (HTb : T + 4096 <= alloc_ceiling) by (destruct HTp as (_ & X & _); exact X).
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (Hsp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 64)) = bv_unsigned sp - 64) by (apply unsigned_lit; clear -SPR LO LOC0 CEILB; lia).
  unfold enq_frame in FR. unfold enq2W in MU.
  pose proof (wr_at_sub bsegs m nb 8192 nb 32 WRB ltac:(clear; lia) ltac:(clear; lia)) as WR32.
  destruct (rw_CB_of_wr_at m nb 32 32%nat WR32 eq_refl) as [bj NBJ]. clear WR32.
  (* [comment removed for export] *)
  destruct (Z.eq_dec cnt 0) as [C0|C1];
    [ clear LBo | pose proof (HLo C1) as (L1 & L2 & L3 & L4); rewrite kHighMemBeg_val in L1; specialize (LBo C1); pose proof (PLBo C1) as PLB ].
  all: unfold lz8 in MU. 1: rewrite (proj2 (Z.eqb_eq cnt 0) C0) in MU. 2: rewrite (proj2 (Z.eqb_neq cnt 0) C1) in MU.
  (* [comment removed for export] *)
  all: zstepA. (* [comment removed for export] *)
  all: zstepA. (* [comment removed for export] *)
  all: zstepA. (* [comment removed for export] *)
  all: zstepA. (* [comment removed for export] *)
  all: replace (((cnt24v + -1) ≪ 32 mod 18446744073709551616) ≫ 30) with (4 * (cnt24v - 1))
    by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; rewrite Z.mod_small by (clear -CEILB C24; lia); clear -CEILB C24; Z.div_mod_to_equations; lia).
  all: zstepA. (* [comment removed for export] *)
  all: zstepA. (* [comment removed for export] *)
  all: zstepA; zstepA. (* [comment removed for export] *)
  all: try replace (T + 208 + 2047 + 529) with (T + 2784) by (clear; lia).
  all: lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mc _) =>
    pose proof (u32arr_read bsegs mc _ ws (cnt24v - 1) (Z_to_bv 64 x) (Z_to_bv 64 (T + 208 + 4 * (cnt24v - 1) + 1936)) ARR NTH ltac:(clear -CEILB C24; lia)
                ltac:(unfold wa; f_equal; clear; lia)) as RD end.
  all: zstepA; clear RD. (* [comment removed for export] *)
  all: rewrite fzx32_small' by (clear -CEILB HX; lia).
  all: assert (AL8 : (T + 2784) mod 8 = 0) by (clear -CEILB HT16; Z.div_mod_to_equations; lia).
  all: zstepA. (* [comment removed for export] *)
  all: zstepA; zstepA. (* [comment removed for export] *)
  all: zstepA; zstepA; zstepA. (* [comment removed for export] *)
  all: zstepA; zstepA. (* [comment removed for export] *)
  all: replace (Z.shiftl x 4 + (SB + 103079215104)) with nb by (rewrite Enb, !Z.shiftl_mul_pow2 by lia; clear; lia).
  all: zstepA; if_cases K0; zify_cond K0; [exfalso; revert K0; rewrite ?unsigned_lit by (clear -CEILB HNB0 HSB0; lia); clear -CEILB HNB0 HSB0; intros K0; lia|]; clear K0.
  all: zstepA; zstepA; zstepA. (* [comment removed for export] *)
  all: zstepA. (* [comment removed for export] *)
  (* [comment removed for export] *)
  all: zstepA. (* [comment removed for export] *)
  all: zstepA. (* [comment removed for export] *)
  all: zstepA. (* [comment removed for export] *)
  all: zstepA. (* [comment removed for export] *)
  (* [comment removed for export] *)
  all: lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m5 end.
  all: set (MID := fun ms1 => exists m6 (a2x : word),
        ms1 = MS (mkR xra (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp t0 t1 t2 xs0 xs1 (Z_to_bv 64 (T + 80)) (Z_to_bv 64 nb) a2x (Z_to_bv 64 cb) (Z_to_bv 64 (n + 8192)) (Z_to_bv 64 cnt) (Z_to_bv 64 103079215104) a7
                  xs2 xs3 xs4 xs5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x36fb8) fc None m6 (seg_rom bsegs)
        /\ mem_inv bsegs m6 /\ stk bsegs m6 lo (bv_unsigned sp - 64) /\ munch enq2W m0 m6 /\ wmono bsegs m0 m6
        /\ rw_cells bsegs m6 (bv_unsigned sp - 64) [CB 8 j8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
        /\ rw_cells bsegs m6 (T + 80) [C8 (Z_to_bv 64 (cnt + 1)); C8 (Z_to_bv 64 (if cnt =? 0 then nb else first)); C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 qb)]
        /\ rw_cells bsegs m6 (T + 2128) [C4 (Z_to_bv 64 (cnt24v - 1)); C4 maxc; C8 (Z_to_bv 64 8192)]
        /\ u32arr bsegs m6 (T + 2144) ws
        /\ rw_cells bsegs m6 (T + 2784) [C8 (Z_to_bv 64 (alloc + 8192))]
        /\ rw_cells bsegs m6 0xaaf78 [C8 (Z_to_bv 64 SB); C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 RI)]
        /\ rw_cells bsegs m6 nb [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (n + 8192)); C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 cb)] /\ wr_at bsegs m6 nb 8192
        /\ (cnt <> 0 -> rw_cells bsegs m6 last [C8 (Z_to_bv 64 nb); C8 bsz; C8 (Z_to_bv 64 1021)])).
  all: eapply (evtA_cut bsegs P MID).
  1:{ change 18446744073709551616 with (2^64) in *. rewrite ?Z_to_bv_mod64 in *.
      zstepA. if_cases K1; zify_cond K1. 2:{ exfalso. apply K1. rewrite C0. reflexivity. } clear K1.
      (* [comment removed for export] *)
      zstepA. (* [comment removed for export] *)
      zstepA. (* [comment removed for export] *)
      zstepA. (* [comment removed for export] *)
      apply evtA_done. do 2 eexists. split; [reflexivity|].
      unfold enq2W, lz8. rewrite C0. cbn [Z.eqb Z.add].
      repeat match goal with |- _ /\ _ => split end; try eassumption.
      all: first [ intros NE; exfalso; apply NE; first [reflexivity | exact C0] | idtac "TAIL-A1"; pg; fail ]. }
  2:{ change 18446744073709551616 with (2^64) in *. rewrite ?Z_to_bv_mod64 in *.
      zstepA. if_cases K1; zify_cond K1. { exfalso. revert K1. rewrite ?unsigned_lit by (clear -CEILB HCNT; lia). clear -CEILB HCNT C1. intros K1. lia. } clear K1.
      zstepA. (* [comment removed for export] *)
      zstepA. (* [comment removed for export] *)
      zstepA. (* [comment removed for export] *)
      zstepA. (* [comment removed for export] *)
      zstepA. (* [comment removed for export] *)
      zstepA. (* [comment removed for export] *)
      apply evtA_done. do 2 eexists. split; [reflexivity|].
      unfold enq2W, lz8. replace (cnt =? 0) with false by (symmetry; apply Z.eqb_neq; exact C1).
      repeat match goal with |- _ /\ _ => split end; try eassumption.
      all: first [ intros _; assumption | idtac "TAIL-B1"; pg; fail ]. }
  all: clear MI SK FR MU WM QC PC ARR STA INS NBJ WRB; try clear LBo.
  all: intros ms1 (m6 & a2x & -> & MI & SK & MU & WM & FR & QC & PC & ARR & STA & INS & NBJ & WRB & LB); unfold enq2W, lz8 in MU.
  1: rewrite (proj2 (Z.eqb_eq cnt 0) C0) in MU. 2: rewrite (proj2 (Z.eqb_neq cnt 0) C1) in MU.
  1: rewrite (proj2 (Z.eqb_eq cnt 0) C0) in QC. 2: rewrite (proj2 (Z.eqb_neq cnt 0) C1) in QC.
  all: try specialize (LB C1).
  (* [comment removed for export] *)
  all: zstepA. (* [comment removed for export] *)
  all: zstepA. (* [comment removed for export] *)
  all: zstepA. (* [comment removed for export] *)
  all: do 8 zstepA. (* [comment removed for export] *)
  all: rewrite ?Hsp; replace (bv_unsigned sp - 64 + 64) with (bv_unsigned sp) by (clear; lia); rewrite ?Z_to_bv_bv_unsigned.
  all: release_frame FR SK (bv_unsigned sp).
  all: zstepA. (* [comment removed for export] *)
  (* [comment removed for export] *)
  all: lazymatch goal with NB7 : rw_cells bsegs ?mq nb [_; _; _; _], WR7 : wr_at bsegs ?mq nb 8192 |- evtA _ _ _ (MS _ _ _ _ _ ?mq _) =>
    pose proof (rw_cells_app_split1b bsegs mq nb [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (n + 8192)); C8 (Z_to_bv 64 1)] _ NB7) as [NBH NBI0];
    pose proof (wr_at_sub bsegs mq nb 8192 (nb + 24 + 8) 8160 WR7 ltac:(clear; lia) ltac:(clear; lia)) as WRT; clear NB7 WR7 end.
  all: cbn [cells_size csize Nat.add Nat.mul] in NBI0.
  all: lazymatch type of NBI0 with rw_cells _ _ ?a _ => replace a with (nb + 24) in NBI0 by (clear; lia) end.
  all: destruct (rw_CB_of_wr_at _ _ _ (8 * 1020)%nat WRT ltac:(reflexivity)) as [bj2 NBJ2]; clear WRT.
  all: destruct (u64arr_of_cb bsegs _ _ _ 1020%nat NBJ2) as (junk & LJ & NBJA).
  all: pose proof (u64arr_cons' _ (nb + 24) (Z_to_bv 64 cb) junk NBI0 NBJA) as NBI.
  all: eapply CONT; unfold enq2_post, enq2W, lz8; exists junk.
  1: rewrite (proj2 (Z.eqb_eq cnt 0) C0). 2: rewrite (proj2 (Z.eqb_neq cnt 0) C1).
  all: repeat match goal with |- _ /\ _ => split end; try eassumption.
  all: first [ exact SK | rewrite Hsp in SK; replace (bv_unsigned sp - 64 + 64) with (bv_unsigned sp) in SK by (clear; lia); exact SK
             | intros NE; first [ exact LB | exfalso; exact (NE C0) ] | idtac "TAIL-C"; pg ].
Qed.

(* [comment removed for export] *)
Lemma enq2_pro : forall m (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word),
  (cnt = 0 \/ cnt <> 0) ->
  mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp) ->
  rw_cells bsegs m (T + 80) [C8 (Z_to_bv 64 cnt); C8 (Z_to_bv 64 first); C8 (Z_to_bv 64 last); C8 (Z_to_bv 64 qb)] ->
  (cnt <> 0 -> rw_cells bsegs m last [C8 bnext; C8 bsz; C8 (Z_to_bv 64 1021)]) ->
  (forall m' (a5' a6' a7' : word) j8, mem_inv bsegs m' -> stk bsegs m' lo (bv_unsigned sp - 64) -> enq_frame m' j8 -> munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m' -> wmono bsegs m m' ->
     rw_cells bsegs m' (T + 80) [C8 (Z_to_bv 64 cnt); C8 (Z_to_bv 64 first); C8 (Z_to_bv 64 last); C8 (Z_to_bv 64 qb)] ->
     (cnt <> 0 -> rw_cells bsegs m' last [C8 bnext; C8 bsz; C8 (Z_to_bv 64 1021)]) ->
     evtA bsegs P Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (T + 80)) (Z_to_bv 64 CA) (Z_to_bv 64 B) (Z_to_bv 64 cb) (Z_to_bv 64 n) a5' a6' a7'
                             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x36f00) fc None m' (seg_rom bsegs))) ->
  evtA bsegs P Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (T + 80)) (Z_to_bv 64 CA) (Z_to_bv 64 B) (Z_to_bv 64 cb) (Z_to_bv 64 n) a5 a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x36ec8) fc None m (seg_rom bsegs)).
Proof. aceil.
  intros until t6. intros CASE MI SK QC LBo CONT.
  pose proof LOC as LOC0. aceil. pose proof HNB as HNB0. unfold kSpaceSize in HNB0. rewrite kHighMemBeg_val in HNB0.
  pose proof (placed_s_num _ _ HTp ltac:(clear; lia)) as (TQ1 & TQ2 & TQ3 & _).
  assert (HTb : T + 4096 <= alloc_ceiling) by (destruct HTp as (_ & X & _); exact X).
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (MU : munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  destruct CASE as [C0|C1]; [| pose proof (HLo C1) as (L1 & L2 & L3 & L4); rewrite kHighMemBeg_val in L1; specialize (LBo C1); pose proof (PLBo C1) as PLB].
  all: carve_frame 64%nat SK.
  all: do 8 zstepA. (* [comment removed for export] *)
  all: zstepA. (* [comment removed for export] *)
  - zstepA. if_cases K0; zify_cond K0. 2:{ exfalso. apply K0. rewrite C0. reflexivity. } clear K0.
    eapply CONT; [exact MI| exact SK| exact FR| exact MU| exact WM| exact QC| intros NE; exfalso; exact (NE C0)].
  - zstepA. if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite ?unsigned_lit by (clear -CEILB HCNT; lia). clear -CEILB C1 HCNT. intros K0. lia. } clear K0.
    zstepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    zstepA. if_cases K1; zify_cond K1. { exfalso. apply K1. reflexivity. } clear K1.
    eapply CONT; [exact MI| exact SK| exact FR| exact MU| exact WM| exact QC| intros _; exact LBo].
Qed.

(* [comment removed for export] *)
Lemma enq2_hit : forall m (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word),
  (cnt = 0 \/ cnt <> 0) -> 1 <= cnt24 <= 16 -> length ws = 16%nat -> nth_error ws (Z.to_nat (cnt24 - 1)) = Some (Z_to_bv 64 x) ->
  mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp) ->
  rw_cells bsegs m (T + 80) [C8 (Z_to_bv 64 cnt); C8 (Z_to_bv 64 first); C8 (Z_to_bv 64 last); C8 (Z_to_bv 64 qb)] ->
  rw_cells bsegs m (T + 2128) [C4 (Z_to_bv 64 cnt24); C4 maxc; C8 (Z_to_bv 64 8192)] ->
  u32arr bsegs m (T + 2144) ws ->
  rw_cells bsegs m (T + 2784) [C8 (Z_to_bv 64 alloc)] ->
  rw_cells bsegs m 0xaaf78 [C8 (Z_to_bv 64 SB); C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 RI)] ->
  wr_at bsegs m nb 8192 ->
  (cnt <> 0 -> rw_cells bsegs m last [C8 bnext; C8 bsz; C8 (Z_to_bv 64 1021)]) ->
  (forall m' (t0' t1' t2' a1' a2' a5' a6' a7' : word), enq2_post m m' cnt24 ->
     evtA bsegs P Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (T + 80)) a1' a2' (Z_to_bv 64 cb) (Z_to_bv 64 (n + 8192)) a5' a6' a7'
                             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  evtA bsegs P Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (T + 80)) (Z_to_bv 64 CA) (Z_to_bv 64 B) (Z_to_bv 64 cb) (Z_to_bv 64 n) a5 a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x36ec8) fc None m (seg_rom bsegs)).
Proof. aceil.
  intros until t6. intros CASE C24 LEN NTH MI SK QC PC ARR STA INS WRB LBo CONT.
  pose proof LOC as LOC0. aceil. pose proof HNB as HNB0. unfold kSpaceSize in HNB0. rewrite kHighMemBeg_val in HNB0.
  pose proof (placed_s_num _ _ HTp ltac:(clear; lia)) as (TQ1 & TQ2 & TQ3 & _).
  assert (HTb : T + 4096 <= alloc_ceiling) by (destruct HTp as (_ & X & _); exact X).
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  eapply enq2_pro; [exact CASE| exact MI| exact SK| exact QC| exact LBo|].
  clear MI SK QC LBo. intros m1 a5' a6' a7' j8 MI SK FR MU WM QC LBo.
  assert (PC1 : rw_cells bsegs m1 (T + 2128) [C4 (Z_to_bv 64 cnt24); C4 maxc; C8 (Z_to_bv 64 8192)]).
  { eapply rw_cells_transport; [exact PC| exact MU| exact WM|]. cbn. clear -CEILB LOC LO TQ1 HTb; repeat split; try exact I; lia. }
  assert (STA1 : rw_cells bsegs m1 (T + 2784) [C8 (Z_to_bv 64 alloc)]).
  { eapply rw_cells_transport; [exact STA| exact MU| exact WM|]. cbn. clear -CEILB LOC LO TQ1 HTb; repeat split; try exact I; lia. }
  assert (INS1 : rw_cells bsegs m1 0xaaf78 [C8 (Z_to_bv 64 SB); C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 RI)]).
  { eapply rw_cells_transport; [exact INS| exact MU| exact WM|]. cbn. clear -CEILB LOC LO; repeat split; try exact I; lia. }
  assert (ARR1 : u32arr bsegs m1 (T + 2144) ws).
  { eapply u32arr_transport; [exact ARR| exact MU| exact WM|]. rewrite LEN. cbn. clear -CEILB LOC LO TQ1 HTb; repeat split; try exact I; lia. }
  assert (WRB1 : wr_at bsegs m1 nb 8192) by (eapply wr_at_transport; [exact WRB| exact WM]).
  clear PC STA INS ARR WRB.
  assert (MUW : munch enq2W m m1).
  { eapply munch_cover; [exact MU|]. intros lo' hi' Hin. destruct Hin as [Hin|[]]. injection Hin as <- <-.
    exists (bv_unsigned sp - 64), (bv_unsigned sp). split; [unfold enq2W; left; reflexivity| clear; lia]. }
  clear MU. rename MUW into MU.
  zstepA. (* [comment removed for export] *)
  rewrite fsx32_small' by (clear -CEILB C24; lia).
  zstepA. if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite ?unsigned_lit by (clear -CEILB C24; lia). clear -CEILB C24. intros K0. lia. } clear K0.
  eapply (enq2_tail m1 cnt24); [exact C24| exact LEN| exact NTH| exact MI| exact SK| exact FR| exact MU| exact WM| exact QC| exact PC1| exact ARR1| exact STA1| exact INS1| exact WRB1| exact LBo| exact CONT].
Qed.

(* [comment removed for export] *)
Definition enq2_refill_call (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) (m : mem) : machine_state :=
  MS (mkR (Z_to_bv 64 0x3701c) (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp t0 t1 t2 (Z_to_bv 64 (T + 2128)) (Z_to_bv 64 CA)
          (Z_to_bv 64 CA) (Z_to_bv 64 (T + 2128)) (Z_to_bv 64 INST) (Z_to_bv 64 24) (Z_to_bv 64 n) (Z_to_bv 64 INST) a6 a7
          (Z_to_bv 64 cb) (Z_to_bv 64 (T + 80)) (Z_to_bv 64 B) (Z_to_bv 64 n) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
     F (Z_to_bv 64 0x377fc) fc None m (seg_rom bsegs).

Lemma enq2_miss_front : forall m (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word) (cszw : word),
  (cnt = 0 \/ cnt <> 0) ->
  mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp) ->
  rw_cells bsegs m (T + 80) [C8 (Z_to_bv 64 cnt); C8 (Z_to_bv 64 first); C8 (Z_to_bv 64 last); C8 (Z_to_bv 64 qb)] ->
  rw_cells bsegs m (T + 2128) [C4 (Z_to_bv 64 0); C4 maxc; C8 cszw] ->
  (cnt <> 0 -> rw_cells bsegs m last [C8 bnext; C8 bsz; C8 (Z_to_bv 64 1021)]) ->
  (forall m' (a6' a7' : word) j8, mem_inv bsegs m' -> stk bsegs m' lo (bv_unsigned sp - 64) -> enq_frame m' j8 -> munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m' -> wmono bsegs m m' ->
     rw_cells bsegs m' (T + 80) [C8 (Z_to_bv 64 cnt); C8 (Z_to_bv 64 first); C8 (Z_to_bv 64 last); C8 (Z_to_bv 64 qb)] ->
     rw_cells bsegs m' (T + 2128) [C4 (Z_to_bv 64 0); C4 maxc; C8 cszw] ->
     (cnt <> 0 -> rw_cells bsegs m' last [C8 bnext; C8 bsz; C8 (Z_to_bv 64 1021)]) ->
     evtA bsegs P Q (enq2_refill_call t0 t1 t2 a6' a7' t3 t4 t5 t6 m')) ->
  evtA bsegs P Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (T + 80)) (Z_to_bv 64 CA) (Z_to_bv 64 B) (Z_to_bv 64 cb) (Z_to_bv 64 n) a5 a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x36ec8) fc None m (seg_rom bsegs)).
Proof. aceil.
  intros until cszw. intros CASE MI SK QC PC LBo CONT.
  pose proof LOC as LOC0. aceil. pose proof HNB as HNB0. unfold kSpaceSize in HNB0. rewrite kHighMemBeg_val in HNB0.
  pose proof (placed_s_num _ _ HTp ltac:(clear; lia)) as (TQ1 & TQ2 & TQ3 & _).
  assert (HTb : T + 4096 <= alloc_ceiling) by (destruct HTp as (_ & X & _); exact X).
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  eapply enq2_pro; [exact CASE| exact MI| exact SK| exact QC| exact LBo|].
  clear MI SK QC LBo. intros m1 a5' a6' a7' j8 MI SK FR MU WM QC LBo.
  assert (PC1 : rw_cells bsegs m1 (T + 2128) [C4 (Z_to_bv 64 0); C4 maxc; C8 cszw]).
  { eapply rw_cells_transport; [exact PC| exact MU| exact WM|]. cbn. clear -CEILB LOC LO TQ1 HTb; repeat split; try exact I; lia. }
  clear PC. rename MU into MU1.
  zstepA. (* [comment removed for export] *)
  change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0).
  zstepA. if_cases K0; zify_cond K0. 2:{ exfalso. apply K0. reflexivity. } clear K0.
  do 13 zstepA. (* [comment removed for export] *)
  eapply CONT; [exact MI| exact SK| exact FR| exact MU1| exact WM| exact QC| exact PC1| exact LBo].
Qed.

(* [comment removed for export] *)
Lemma enq2_back : forall m (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (j8 : list byte),
  1 <= cnt24 <= 16 -> length ws = 16%nat -> nth_error ws (Z.to_nat (cnt24 - 1)) = Some (Z_to_bv 64 x) ->
  mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp - 64) -> enq_frame m j8 ->
  rw_cells bsegs m (T + 80) [C8 (Z_to_bv 64 cnt); C8 (Z_to_bv 64 first); C8 (Z_to_bv 64 last); C8 (Z_to_bv 64 qb)] ->
  rw_cells bsegs m (T + 2128) [C4 (Z_to_bv 64 cnt24); C4 maxc; C8 (Z_to_bv 64 8192)] ->
  u32arr bsegs m (T + 2144) ws ->
  rw_cells bsegs m (T + 2784) [C8 (Z_to_bv 64 alloc)] ->
  rw_cells bsegs m 0xaaf78 [C8 (Z_to_bv 64 SB); C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 RI)] ->
  wr_at bsegs m nb 8192 ->
  (cnt <> 0 -> rw_cells bsegs m last [C8 bnext; C8 bsz; C8 (Z_to_bv 64 1021)]) ->
  (forall m' (t0' t1' t2' a1' a2' a5' a6' a7' : word), enq2_post m m' cnt24 ->
     evtA bsegs P Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (T + 80)) a1' a2' (Z_to_bv 64 cb) (Z_to_bv 64 (n + 8192)) a5' a6' a7'
                             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  evtA bsegs P Q (MS (mkR (Z_to_bv 64 0x3701c) (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp t0 t1 t2 (Z_to_bv 64 (T + 2128)) (Z_to_bv 64 CA)
                          (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 cb) (Z_to_bv 64 (T + 80)) (Z_to_bv 64 B) (Z_to_bv 64 n) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x3701c) fc None m (seg_rom bsegs)).
Proof. aceil.
  intros until j8. intros C24 LEN NTH MI SK FR QC PC ARR STA INS WRB LBo CONT.
  pose proof LOC as LOC0. aceil.
  pose proof (placed_s_num _ _ HTp ltac:(clear; lia)) as (TQ1 & TQ2 & TQ3 & _).
  assert (HTb : T + 4096 <= alloc_ceiling) by (destruct HTp as (_ & X & _); exact X).
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (MU : munch enq2W m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  zstepA. (* [comment removed for export] *)
  zstepA. if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite ?unsigned_lit by (clear; lia). clear. intros K0. lia. } clear K0.
  zstepA. zstepA. zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  rewrite fsx32_small' by (clear -CEILB C24; lia).
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  eapply (enq2_tail m cnt24); [exact C24| exact LEN| exact NTH| exact MI| exact SK| exact FR| exact MU| exact WM| exact QC| exact PC| exact ARR| exact STA| exact INS| exact WRB| exact LBo| exact CONT].
Qed.
End ENQ2.
End RC__1.
