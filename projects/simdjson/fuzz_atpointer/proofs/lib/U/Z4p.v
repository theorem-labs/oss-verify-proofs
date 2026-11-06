(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Image Z11w Z119 ITree Nodes Decode Arr FP MonadX Z10q.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Malloc Require Import Zei Zf6.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.MallocU Require Import Zhy Zhz Zi1.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec Require Import Prelim STree Malloc Monad Stdio StrFun Zpb Z3o Target Prog AtpImpl.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Import SjTape Zpk.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.U Require Import Layout Exit Zfr Zq5 Sj_kit Sj_new Zq6 Zpu.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.U Require Import Z9l Z9m Zb0 Z9n Z9o Z44 Z5l Z3u Z5z.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Definition ATP_GETSTR : Z := 0x27788.
Definition ATP_VDLOOP : Z := 0x29198.

Lemma elem_tf_facts : forall (tws : list Z) (S : Z -> Z) (sn : Z) (d : nat) (i j : Z),
  elem (Tf tws) S sn ck_any d i j -> 0 <= i -> sn < 2^56 -> Z.of_nat (length tws) < 2^32 ->
  i < Z.of_nat (length tws) /\ 0 <= Tf tws i < 2^64 /\ (ttype (Tf tws i) = t_str -> is_str (Tf tws) S sn i).
Proof.
  intros tws S sn d i j EL Hi Hsn Hn.
  assert (NZ : forall k, 0 < Tf tws k -> k < Z.of_nat (length tws)).
  { intros k Hk. destruct (Z.lt_ge_cases k (Z.of_nat (length tws))) as [L|G]; [exact L| exfalso].
    unfold Tf in Hk. rewrite nth_overflow in Hk by lia. lia. }
  assert (SC : scalar (Tf tws) S sn i j -> i < Z.of_nat (length tws) /\ 0 <= Tf tws i < 2^64 /\ (ttype (Tf tws i) = t_str -> is_str (Tf tws) S sn i)).
  { intros [[_ [X|[X|X]]]|[[_ [X|[X|X]]]|[_ STR]]].
    1-6: split; [apply NZ; rewrite X; unfold tword, t_true, t_false, t_null, t_i64, t_u64, t_dbl; lia|];
         split; [rewrite X; apply tword_range; [unfold t_true, t_false, t_null, t_i64, t_u64, t_dbl; lia| lia]|];
         rewrite X; rewrite ttype_tword by lia; unfold t_true, t_false, t_null, t_i64, t_u64, t_dbl, t_str; intros H; exfalso; lia.
    pose proof STR as (o & l & X & (O0 & L0 & OL & _)).
    split; [apply NZ; rewrite X; unfold tword, t_str; lia|].
    split; [rewrite X; apply tword_range; [unfold t_str; lia| lia]|].
    intros _; exact STR. }
  destruct d as [|d']; cbn [elem] in EL; fold (elem (Tf tws) S sn ck_any) in EL.
  - destruct EL as [EL|[]]. exact (SC EL).
  - destruct EL as [EL|(e & c & cv & Ej & CK & CS)]; [exact (SC EL)|].
    unfold ck_any in CK.
    assert (IE : i + 1 <= e /\ 0 < Tf tws e /\ exists t, (t = t_arr \/ t = t_obj) /\ Tf tws i = cword t (e + 1) cv).
    { destruct CS as [(X & Y & TL)|(X & Y & TL)].
      - pose proof (tiles_le _ (elem_lt _ _ _ _ d') _ _ _ TL) as TLE. split; [lia|]. split; [rewrite Y; unfold tword, t_arr_end; lia|]. exists t_arr. split; [left; reflexivity| exact X].
      - pose proof (tiles_le _ (field_lt _ _ _ _ (elem_lt _ _ _ _ d')) _ _ _ TL) as TLE. split; [lia|]. split; [rewrite Y; unfold tword, t_obj_end; lia|]. exists t_obj. split; [right; reflexivity| exact X]. }
    destruct IE as (IE & TE & t & Ht & X). pose proof (NZ e TE) as EN.
    assert (TR : 0 <= t < 256) by (unfold t_arr, t_obj in Ht; lia).
    split; [apply NZ; rewrite X; unfold cword, tword; lia|].
    split; [rewrite X; apply cword_range; [exact TR| lia| exact CK]|].
    rewrite X. rewrite ttype_cword by lia. unfold t_arr, t_obj, t_str in *. intros H; exfalso; lia.
Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma vdtor_loop : forall Q (x1 sp gp t0 t1 t2 s0 s1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (A : Z) (k : nat),
  16 <= A -> A + 16 * Z.of_nat k < 2^63 -> (1 <= k)%nat ->
  evt usegs Q (MS (mkR x1 sp gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 A) a2 (Z_to_bv 64 16) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x291a8) fc None m (seg_rom usegs)) ->
  evt usegs Q (MS (mkR x1 sp gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 (A + 16 * Z.of_nat k)) a2 (Z_to_bv 64 16) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 ATP_VDLOOP) fc None m (seg_rom usegs)).
Proof.
  intros until k. intros A16 AK K1 HK. unfold ATP_VDLOOP.
  revert AK K1. induction k as [|k IH]; intros AK K1; [lia|].
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.

  step. if_lia. step. if_lia. zstep.
  replace (A + 16 * Z.of_nat (S k) + -16) with (A + 16 * Z.of_nat k) by lia.
  step. if_cases K; zify_cond K.
  -
    apply IH; lia.
  -
    eapply evt_eq; [| exact HK]. atp_st_eq.
Qed.

Definition getstr_post (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) (g20 : list byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem) (w0 w8 : word) (code : Z),
    ms' = MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(q - 48, q); (q, q + 24)] m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo q
    /\ rw_cells usegs m' q [C8 w0; C8 w8; C4 (Z_to_bv 64 code); CB 4 g20] /\ (code = 0 \/ code = 17).

Section GStr.
  Variable E : aenv.
  Hypothesis OK : aenv_ok E.

  Lemma getstr_spec : forall (ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (q j jj : Z) (dd : nat) (g0 g8 g16 g20 : list byte),
    AINV E m -> RHEAP s (ae_LB E) m ->
    elem (ae_T E) (ae_S E) (ae_sn E) ck_any dd j jj -> 0 <= j ->
    rw_cells usegs m (q + 24) [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 j)] ->
    rw_cells usegs m q [CB 8 g0; CB 8 g8; CB 4 g16; CB 4 g20] ->
    q + 40 <= ae_DOC E -> q + 40 < 2^63 ->
    stk usegs m (ae_lo E) q -> ae_lo E <= q - 48 -> mem_inv usegs m ->
    evt usegs (getstr_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (ae_lo E) m g20)
      (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 q) (Z_to_bv 64 (q + 24)) a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ATP_GETSTR) fc None m (seg_rom usegs)).
  Proof.
    intros until g20. intros AI HEAP EL J0 LEAF OUT QD Q63 ST LO MI.
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L BT BS BP P0 [CEIL GLO] B63 [DL DB] [AL8D AL8T]].
    unfold GLOBALS_TOP, ATP_GETSTR in *.
    assert (LO0 : 0 <= ae_lo E) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    pose proof (tape_wf_root _ _ _ _ _ WF) as [_ NR].
    assert (HSN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia).
    pose proof (aenv_ranges E s m OK HEAP) as (TR & SR & PR).
    pose proof (elem_lt _ _ _ _ _ _ _ EL) as IJ.
    pose proof (elem_tf_facts (ae_tws E) (ae_S E) (ae_sn E) dd j jj EL J0 HSN ltac:(lia)) as (JN & TIR & STRF).
    assert (TTR : 0 <= ttype (ae_T E j) < 256) by (unfold ttype; lia).
    pose proof (munch_refl [(q - 48, q); (q, q + 24)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    hide AI.

    step. carve_frame 48%nat ST.
    apply (rw_cells_split_CB usegs _ _ [] 48 junk [] [8;8;8;8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.
    do 5 step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    unhide AI.
    assert (AI1 : AINV E m1).
    { eapply AINV_agree; [exact AI| eapply agree_on_of_munch; [exact MU| exact WM]| | | exact OK].
      - intros a Ha. pose proof (blocks_below _ _ _ _ HEAP Ha). cbn [outside]. lia.
      - intros a Ha. cbn [outside]. lia. }
    clear AI. destruct AI1 as (TAPEB & SBUFB & PTRB & DOCC).
    pose proof (tape_read _ (ae_TAPE E) (ae_tws E) j TAPEB ltac:(lia)) as RDT.
    pose proof (tape_read_type m1 (ae_TAPE E) (ae_tws E) j TAPEB ltac:(lia) TIR) as RDB.

    step. step. if_lia. step. astep. rewrite (land7_mod8 (ae_DOC E)) by lia. step. if_false.
    step. step. step. step.
    eapply tix_cps with (D := ae_DOC E) (TAPE := ae_TAPE E) (i := j) (RA := 0x277c4);
      [exact DOCC| lia| lia| lia| lia| exact AL8T| lia| lia| reflexivity| lia| reflexivity|].
    intros xa1 xa2 xa3 xa4.

    astep. step. step. if_cases KS; zify_cond KS.
    -

      step. if_lia. hstep. hstep. step. hstep.

      do 5 step. step. release_frame FR ST q. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
      lazymatch goal with H : rw_cells usegs m2 q _ |- _ => rename H into OUT2 end.
      apply evt_done. unfold getstr_post. do 15 eexists. exists m2. do 2 eexists. exists 17.
      split; [atp_st_eq_goal|].
      split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [exact ST|].
      split; [exact OUT2| right; reflexivity].
    -
      pose proof (STRF ltac:(unfold t_str; exact KS)) as STR.
      pose proof (key_word_range _ _ _ _ STR HSN) as (KR & KM & KT).
      destruct (is_str_read _ _ _ HSN _ STR) as [_ (l & SA)].
      pose proof (str_at_bounds _ _ HSN _ _ SA) as (O0 & L0 & OL & LE & O56).
      set (o := tval (ae_T E j)) in *.

      step. step. if_lia. astep. rewrite (land7_mod8 (ae_DOC E)) by lia. step. if_false. step. step.
      eapply tix_cps with (D := ae_DOC E) (TAPE := ae_TAPE E) (i := j) (RA := 0x277e8);
        [exact DOCC| lia| lia| lia| lia| exact AL8T| lia| lia| reflexivity| lia| reflexivity|].
      intros ya1 ya2 ya3 ya4.

      step. step. if_lia. astep. rewrite (land7_mod8 (ae_DOC E)) by lia. step. if_false. step. step. if_lia.

      step. step. zstep. astep. rewrite KM. astep. astep. step. if_lia. step. if_lia.

      step. step. step.
      eapply tix_cps with (D := ae_DOC E) (TAPE := ae_TAPE E) (i := j) (RA := 0x2782c);
        [exact DOCC| lia| lia| lia| lia| exact AL8T| lia| lia| reflexivity| lia| reflexivity|].
      intros za1 za2 za3 za4.

      step. step. if_lia. astep. rewrite (land7_mod8 (ae_DOC E)) by lia. step. if_false. step. step. astep. rewrite KM. astep. step. if_lia.

      astep. astep.
      replace (0 <? ae_SBUF E) with true by (symmetry; apply Z.ltb_lt; lia).
      first [ replace (ae_SBUF E + o <? 1) with false by (symmetry; apply Z.ltb_ge; lia)
            | replace (o + ae_SBUF E <? 1) with false by (symmetry; apply Z.ltb_ge; lia) ].
      cbn [Z.b2z Z.lxor Pos.lxor]. astep. step. if_false. step. if_lia. step. if_lia. step.

      pose proof (sbuf_read1 m1 (ae_SBUF E) (ae_sbs E) o SBUFB ltac:(lia)) as RB0.
      pose proof (sbuf_read1 m1 (ae_SBUF E) (ae_sbs E) (o + 1) SBUFB ltac:(lia)) as RB1.
      pose proof (sbuf_read1 m1 (ae_SBUF E) (ae_sbs E) (o + 2) SBUFB ltac:(lia)) as RB2.
      pose proof (sbuf_read1 m1 (ae_SBUF E) (ae_sbs E) (o + 3) SBUFB ltac:(lia)) as RB3.
      pose proof (sbs_byte E OK o ltac:(lia)) as B0. pose proof (sbs_byte E OK (o + 1) ltac:(lia)) as B1.
      pose proof (sbs_byte E OK (o + 2) ltac:(lia)) as B2. pose proof (sbs_byte E OK (o + 3) ltac:(lia)) as B3.
      astep. astep. astep. astep. astep. astep. astep. astep. astep. astep.

      hstep. hstep. step. hstep.

      do 5 step. step. release_frame FR ST q. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
      lazymatch goal with H : rw_cells usegs m2 q _ |- _ => rename H into OUT2 end.
      apply evt_done. unfold getstr_post. do 15 eexists. exists m2. do 2 eexists. exists 0.
      split; [atp_st_eq_goal|].
      split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [exact ST|].
      split; [exact OUT2| left; reflexivity].
  Qed.
End GStr.
End WithCeiling0.
