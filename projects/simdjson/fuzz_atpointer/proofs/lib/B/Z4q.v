(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import Zp7 Z1b.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS Z119 Z10q FP.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Import Zpf SjTape Zpk.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec Require Import Prelim Stdio Zpb Z3o.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Z10v Zvm Zvw.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.B Require Import Layout Zks Zkt D_defs D_kit D_clx Z87 Sj_rtf Zpm Zpl Zq2
  Z45 Z5k Z3v.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition ATP_GETSTR_A : Z := 0x97804.

Definition GSTR_STACK_A : Z := 96 + RT_STACK.

Definition gstr_W (q R : Z) : list ivl := [(q + -96, q); (R, R + 24)].

Definition gstr_frame (ra s0 s1 s2 s3 s4 s5 s6 s7 : word) (j0 : list byte) : list cell :=
  [CB 8 j0; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma mask56_val : Z.shiftr 18446744073709551615 8 = 72057594037927935.
Proof. reflexivity. Qed.
Lemma land56_tval : forall w, 0 <= w -> Z.land w 72057594037927935 = w mod 2^56.
Proof. intros w Hw. change 72057594037927935 with (Z.ones 56). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma tword_str_mod : forall o, 0 <= o < 2^56 -> (tword t_str o) mod 2^56 = o.
Proof. intros o Ho. unfold tword, t_str. replace (34 * 2^56 + o) with (o + 34 * 2^56) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia. Qed.

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

Lemma rec_words16 : forall (m : mem) A (w0 w1 : word) rest,
  rw_cells bsegs m A (C8 w0 :: C8 w1 :: rest) -> rw_cells bsegs m A (CB 16 (le8 w0 ++ le8 w1) :: rest).
Proof.
  intros m A w0 w1 rest H. eapply rw_cells_recastA; [exact H| | cbn [cells_bytes cbytes]; rewrite <- app_assoc; reflexivity].
  destruct H as [[W _] _]. cbn [cells_wf cell_wf] in W |- *. split; [rewrite length_app, !length_le8; reflexivity| tauto].
Qed.

Section GStr.
  Variable RT : rt_sig.
  Hypothesis AF : art_facts RT.
  Variable E : aenvA.
  Hypothesis OK : aenvA_ok E.

  Local Ltac ul := unfold GSTR_STACK_A, SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

  Local Ltac chkS H x := shz_pose H x; zstep; shz_norm.

  Local Ltac after_tix ma mb MUab WMab MW MUa WMa q EL R FR ELC RC G1 G2 :=
    let XP := fresh "XP" in
    assert (XP : forall A cs, q + -80 <= A -> rw_cells bsegs ma A cs -> rw_cells bsegs mb A cs)
      by (intros A cs HA H; apply (rw_cells_agree bsegs ma mb _ _ H); [| exact WMab]; apply (agree_of_munch _ _ _ _ MUab); intros x Hx; cbn [outside]; lia);
    let FR' := fresh "FR" in let ELC' := fresh "ELC" in let RC' := fresh "RC" in
    pose proof (XP (q + -80) _ ltac:(lia) FR) as FR'; pose proof (XP EL _ ltac:(lia) ELC) as ELC'; pose proof (XP R _ ltac:(lia) RC) as RC';
    clear FR ELC RC XP; rename FR' into FR; rename ELC' into ELC; rename RC' into RC;
    let G1' := fresh "G" in let G2' := fresh "G" in
    pose proof (ro_cells_transport bsegs _ ma mb _ _ G1 MUab) as G1'; cbn [cells_size csize Nat.add disjoint_from] in G1'; specialize (G1' ltac:(lia));
    pose proof (ro_cells_transport bsegs _ ma mb _ _ G2 MUab) as G2'; cbn [cells_size csize Nat.add disjoint_from] in G2'; specialize (G2' ltac:(lia));
    clear G1 G2; rename G1' into G1; rename G2' into G2;
    let MU := fresh "MU" in let WM := fresh "WM" in
    destruct (MW ma mb MUa WMa MUab WMab) as [MU WM]; clear MUa WMa MUab WMab; unfold gstr_W in MU.

  Definition gstr_x1 (q R EL : Z) (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (g : list byte)
      : machine_state -> Prop :=
    fun ms => exists (m1 : mem),
      munch (gstr_W q R) m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\
      (
        (exists (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (b16 g20 : list byte),
           ms = MS (mkR ra (wz q) gp (wz TPV) y5 y6 y7 s0 s1 y10 y11 y12 y13 y14 y15 y16 y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                   F (ret_pc ra) fc None m1 (seg_rom bsegs)
           /\ stk bsegs m1 (ae_lo E) q /\ rw_cells bsegs m1 R [CB 16 b16; C4 (wz 0); CB 4 g20])
     \/
        (exists (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' s4' s6' : word) (j0 : list byte),
           ms = entry_st (wz 0x97a30) (wz (q + -80)) gp (wz TPV) t0' t1' t2' (wz R) (wz EL) (wz R) (wz 0) (wz 16) a3' a4' a5' a6' a7'
                         (wz (EL + 8)) (wz 2147450880) s4' s5 s6' s7 s8 s9 s10 s11 t3' t4' t5' t6' F fc e_asan_memset m1
           /\ stk bsegs m1 (ae_lo E) (q + -80) /\ rw_cells bsegs m1 (q + -80) (gstr_frame ra s0 s1 s2 s3 s4 s5 s6 s7 j0)
           /\ rw_cells bsegs m1 R [CB 24 g]) ).

  Lemma gstr_walk1 : forall (q R EL : Z) (j jj : Z) (dd : nat)
      (ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (g : list byte),
    AINV_A E m -> elem (ae_T E) (ae_S E) (ae_sn E) ck_any dd j jj -> 0 <= j ->
    rw_cells bsegs m EL [C8 (wz (ae_DOC E)); C8 (wz j)] -> q <= EL -> EL + 16 <= ae_hi E -> EL mod 8 = 0 ->
    rw_cells bsegs m R [CB 24 g] -> q <= R -> R + 24 <= ae_hi E -> R mod 8 = 0 -> (EL + 16 <= R \/ R + 24 <= EL) ->
    mem_inv bsegs m -> stk bsegs m (ae_lo E) q -> ae_lo E + 96 <= q -> q mod 16 = 0 -> shb_cells m ->
    0 <= bv_unsigned ra < 2^64 ->
    (forall m', munch (gstr_W q R) m m' -> wmono bsegs m m' -> shz m' EL 16) ->
    (forall m', munch (gstr_W q R) m m' -> wmono bsegs m m' -> shz m' R 24) ->
    (forall m', munch (gstr_W q R) m m' -> wmono bsegs m m' -> shz m' (ae_DOC E) 16) ->
    (forall m', munch (gstr_W q R) m m' -> wmono bsegs m m' -> shz m' (ae_TAPE E) (8 * ae_n E)) ->
    (forall m', munch (gstr_W q R) m m' -> wmono bsegs m m' -> shz m' (ae_SBUF E) (ae_NS E)) ->
    (forall m', munch (gstr_W q R) m m' -> wmono bsegs m m' -> AINV_A E m') ->
    evt bsegs (gstr_x1 q R EL ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m g)
      (MS (mkR ra (wz q) gp (wz TPV) t0 t1 t2 s0 s1 (wz R) (wz EL) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz ATP_GETSTR_A) fc None m (seg_rom bsegs)).
  Proof using OK.
    intros until g. intros AI EL0 J0 ELC QE EH E8 RC QR RH R8 ER MI ST LO Q16 SHB RA0 SHZE SHZR SHZD SHZT SHZS AIM.
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L [T16 [NT8 [TN [TS TL]]]] [S16 [NS8 [SNS [SS SL]]]] PTRR P0' [D8 [DF [DL [DS DT]]]] LOW [HL HT]].
    clear P1 P1L PTRR P0'.

    hide T16. hide NT8. hide S16. hide NS8. hide D8. hide E8. hide R8.
    unfold ATP_GETSTR_A, TPV in *. unfold SEGTOP_A, USTACK_TOP in *.
    assert (FS : 0 <= fs_size (ae_kD E)) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
    pose proof (tape_wf_root _ _ _ _ _ WF) as [_ NR].
    assert (HSN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia).
    pose proof (elem_tf_facts (ae_tws E) (ae_S E) (ae_sn E) dd j jj EL0 J0 HSN ltac:(lia)) as (JN & TIR & STRF).
    assert (TTR : 0 <= ttype (ae_T E j) < 256) by (unfold ttype; lia).
    pose proof (munch_refl (gstr_W q R) m) as MU. pose proof (wmono_refl bsegs m) as WM. unfold gstr_W in MU.
    assert (EU : bv_unsigned (wz (q + -80)) = q + -80) by (apply unsigned_lit; lia).
    assert (Q16' : (q + -80) mod 16 = 0) by (replace (q + -80) with (q + (-5) * 16) by lia; rewrite Z.mod_add by lia; exact Q16).
    hide Q16. hide Q16'.
    destruct SHB as [G1 G2].
    hide AI.

    step. carve_frame 80%nat ST.
    apply (rw_cells_split_CB bsegs _ _ [] 80 junk [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    set (j0 := firstn 8 junk) in FR. clearbody j0.
    repeat match type of FR with context [CB 8 (firstn ?a ?b)] => let jk := fresh "jk" in set (jk := firstn a b) in FR; clearbody jk end.
    do 9 step.
    step. step. step.

    assert (MW : forall m1 m2, munch (gstr_W q R) m m1 -> wmono bsegs m m1 -> munch [(q + -80 + -16, q + -80)] m1 m2 -> wmono bsegs m1 m2 ->
                 munch (gstr_W q R) m m2 /\ wmono bsegs m m2).
    { intros m1 m2 MU1 WM1 MU2 WM2. split; [| exact (wmono_trans _ _ _ _ WM1 WM2)].
      apply (munch_trans _ m m1 m2 MU1). eapply munch_weaken; [| exact MU2]. intros x Hx. unfold gstr_W in Hx. cbn [outside] in *. lia. }

    step. chk0 SHZE EL. step. if_false.

    step. step. step. if_dead1 by DF DS. astep. step. unhide D8; if_dead1 by D8 DF DS; hide D8.

    astep. chk0 SHZE (EL + 8). step. if_false.

    step. step.
    name_mem m1.
    lazymatch goal with MU1 : munch _ m m1, WM1 : wmono _ m m1 |- _ => rename MU1 into MUa; rename WM1 into WMa end.
    eapply (tix_cps E OK); [exact (AIM m1 MUa WMa)| lia| exact (conj G1 G2)
      | intros m' MU' WM'; exact (SHZD m' (proj1 (MW m1 m' MUa WMa MU' WM')) (proj2 (MW m1 m' MUa WMa MU' WM')))
      | exact ST| lia| lia| exact Q16'| assumption| lia| reflexivity|].
    intros m2 xa1 xa3 xa4 MU2 WM2 MI2 ST2.
    after_tix m1 m2 MU2 WM2 MW MUa WMa q EL R FR ELC RC G1 G2.

    chk0 SHZT (ae_TAPE E + 8 * j). step. if_false.
    pose proof (tape_read_type m2 (ae_TAPE E) (ae_tws E) j (proj1 (AIM m2 MU WM)) ltac:(lia) TIR) as RDB.
    astep. step.
    step. if_cases KT; zify_cond KT.
    -
      step. if_dead1 by QR LO LOW. step. step. step. step.
      apply evt_done. exists m2. split; [exact MU|]. split; [exact WM|]. split; [exact MI2|]. right.
      do 15 eexists. split; [unfold entry_st, e_asan_memset; atp_st_eq_goal|]. split; [exact ST2|]. split; [exact FR| exact RC].
    -
      assert (TYS : ttype (ae_T E j) = t_str) by (unfold t_str; clear - KT TTR; lia).
      destruct (STRF TYS) as (o & l & TJ & O0 & L0 & OL & L32 & _).
      assert (OR : 0 <= o < 2^56) by lia.

      chkS SHZE EL. step. if_false.
      step. step. if_dead1 by DF DS. astep. step. unhide D8; if_dead1 by D8 DF DS; hide D8.
      chkS SHZE (EL + 8). step. if_false.
      step. step.
      lazymatch goal with MU1 : munch _ m m2, WM1 : wmono _ m m2 |- _ => rename MU1 into MUa; rename WM1 into WMa end.
      eapply (tix_cps E OK); [exact (AIM m2 MUa WMa)| lia| exact (conj G1 G2)
        | intros m' MU' WM'; exact (SHZD m' (proj1 (MW m2 m' MUa WMa MU' WM')) (proj2 (MW m2 m' MUa WMa MU' WM')))
        | exact ST2| lia| lia| exact Q16'| assumption| lia| reflexivity|].
      intros m3 xb1 xb3 xb4 MU3 WM3 MI3 ST3.
      after_tix m2 m3 MU3 WM3 MW MUa WMa q EL R FR ELC RC G1 G2. clear MI2 ST2 RDB.
      lazymatch goal with MU1 : munch _ m m3, WM1 : wmono _ m m3 |- _ => rename MU1 into MU; rename WM1 into WM end.
      pose proof (AIM m3 MU WM) as (TAPEB & _ & _ & DOCC & _).
      pose proof (tape_read _ (ae_TAPE E) (ae_tws E) j TAPEB ltac:(lia)) as RDT. clear TAPEB.

      chkS SHZE EL. step. if_false.
      step. step. step. if_dead1 by DF DS. astep. step. unhide D8; if_dead1 by D8 DF DS; hide D8.
      chk0 SHZT (ae_TAPE E + 8 * j). step. if_false.
      astep. chk0 SHZD (ae_DOC E + 8). step. if_false.
      step. step. if_dead1 by SS.

      step. step. astep. astep.
      replace (Z.land (ae_T E j) 72057594037927935) with o by (symmetry; rewrite land56_tval by lia; rewrite TJ; apply tword_str_mod; exact OR).
      astep. astep. step. if_dead1 by SS O0. step. if_dead1 by SS O0 SL SNS OL L0 HL HT.

      chkS SHZE (EL + 8). step. if_false.
      step. step. clear RDT DOCC.
      lazymatch goal with MU1 : munch _ m m3, WM1 : wmono _ m m3 |- _ => rename MU1 into MUa; rename WM1 into WMa end.
      eapply (tix_cps E OK); [exact (AIM m3 MUa WMa)| lia| exact (conj G1 G2)
        | intros m' MU' WM'; exact (SHZD m' (proj1 (MW m3 m' MUa WMa MU' WM')) (proj2 (MW m3 m' MUa WMa MU' WM')))
        | exact ST3| lia| lia| exact Q16'| assumption| lia| reflexivity|].
      intros m4 xc1 xc3 xc4 MU4 WM4 MI4 ST4.
      after_tix m3 m4 MU4 WM4 MW MUa WMa q EL R FR ELC RC G1 G2. clear MI3 ST3.
      lazymatch goal with MU1 : munch _ m m4, WM1 : wmono _ m m4 |- _ => rename MU1 into MU; rename WM1 into WM end.
      pose proof (AIM m4 MU WM) as (TAPEB & SBUFB & _ & DOCC & _).
      pose proof (tape_read _ (ae_TAPE E) (ae_tws E) j TAPEB ltac:(lia)) as RDT. clear TAPEB.

      chkS SHZE EL. step. if_false.
      step. step. if_dead1 by DF DS. astep. step. unhide D8; if_dead1 by D8 DF DS; hide D8.
      chk0 SHZT (ae_TAPE E + 8 * j). step. if_false.
      astep. chk0 SHZD (ae_DOC E + 8). step. if_false.
      step. step. clear RDT DOCC.

      astep. replace (Z.land (ae_T E j) 72057594037927935) with o by (symmetry; rewrite land56_tval by lia; rewrite TJ; apply tword_str_mod; exact OR).
      astep. step. if_dead1 by SS O0 SL SNS OL L0 HL HT.
      astep. astep.
      replace (0 <? ae_SBUF E) with true by (symmetry; apply Z.ltb_lt; lia).
      replace (ae_SBUF E + o <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
      astep. step. if_false. step. if_dead1 by SS. step. if_dead1 by QR LO LOW.

      chk0 SHZS (ae_SBUF E + o). step. if_false.
      astep. chk0 SHZS (ae_SBUF E + o + 3). step. if_false.
      chk0 SHZR R. step. if_false.

      assert (SNL : ae_sn E = Z.of_nat (length (ae_sbs E))) by reflexivity.
      pose proof (sbuf_read1 m4 (ae_SBUF E) (ae_sbs E) o SBUFB ltac:(lia)) as RS0.
      pose proof (sbuf_read1 m4 (ae_SBUF E) (ae_sbs E) (o + 1) SBUFB ltac:(lia)) as RS1. replace (ae_SBUF E + (o + 1)) with (ae_SBUF E + o + 1) in RS1 by lia.
      pose proof (sbuf_read1 m4 (ae_SBUF E) (ae_sbs E) (o + 2) SBUFB ltac:(lia)) as RS2. replace (ae_SBUF E + (o + 2)) with (ae_SBUF E + o + 2) in RS2 by lia.
      pose proof (sbuf_read1 m4 (ae_SBUF E) (ae_sbs E) (o + 3) SBUFB ltac:(lia)) as RS3. replace (ae_SBUF E + (o + 3)) with (ae_SBUF E + o + 3) in RS3 by lia.
      clear SBUFB.
      assert (CR : forall k, 0 <= k < ae_sn E -> 0 <= Tf (ae_sbs E) k < 256).
      { intros k Hk. unfold Tf. apply (Forall_nth_Z _ (ae_sbs E) (Z.to_nat k) SBS). lia. }
      pose proof (CR o ltac:(lia)) as C0R. pose proof (CR (o + 1) ltac:(lia)) as C1R. pose proof (CR (o + 2) ltac:(lia)) as C2R. pose proof (CR (o + 3) ltac:(lia)) as C3R.
      clear CR.

      set (c0 := Tf (ae_sbs E) o) in *. set (c1 := Tf (ae_sbs E) (o + 1)) in *. set (c2 := Tf (ae_sbs E) (o + 2)) in *. set (c3 := Tf (ae_sbs E) (o + 3)) in *.
      clearbody c0 c1 c2 c3.

      repeat match goal with H : ov_read_bytes _ _ _ 1 = Some [Z_to_bv 8 0] |- _ => clear H end.
      hide RS1. hide RS2. hide RS3.
      step. unhide RS1. step. unhide RS2. step. unhide RS3. step.

      apply (rw_cells_split_CB bsegs _ _ [] 24 g [] [8; 8; 4; 4]%nat) in RC; [| reflexivity]. cbn [mk_CB_cells app] in RC.
      step.

      astep. chk0 SHZR (R + 8). step. if_false.
      step. step. step. step. step. step.
      step. step.

      repeat match goal with |- evt _ _ (MS ?r _ _ _ _ _ _) =>
        match r with context [Some (Z_to_bv 64 (Z.lor ?x ?y))] => let w := fresh "lw" in set (w := Z.lor x y); clearbody w end end.
      repeat match goal with |- evt _ _ (MS ?r _ _ _ _ _ _) =>
        match r with context [Some (Z_to_bv 64 (Z.shiftl ?x ?y))] => let w := fresh "lw" in set (w := Z.shiftl x y); clearbody w end end.
      zstep. chk0 SHZR (R + 16). step. if_false.
      step.
      do 9 step. step.
      clear ST. lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => lazymatch goal with H : stk bsegs mx _ _ |- _ => release_frame FR H q end end. step.
      apply evt_done. unfold gstr_x1.
      lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists mx end.
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. left.
      do 17 eexists. split; [atp_st_eq_goal|]. split; [lazymatch goal with H : stk bsegs _ _ q |- _ => exact H end|].
      lazymatch goal with H : rw_cells bsegs _ R _ |- _ => exact (rec_words16 _ _ _ _ _ H) end.
  Qed.

  Lemma gstr_walk2 : forall (q R EL : Z) (ra gp y0 y1 y2 v z1 z2 z3 z4 z5 z6 z7 s0 s1 s2 s3 s4 s4' s5 s6 s6' s7 s8 s9 s10 s11 y3 y4 y5 y6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (b16 jb jc j0 : list byte),
    q <= R -> R + 24 <= ae_hi E -> R mod 8 = 0 -> ae_lo E + 96 <= q ->
    stk bsegs m (ae_lo E) (q + -80) -> rw_cells bsegs m (q + -80) (gstr_frame ra s0 s1 s2 s3 s4 s5 s6 s7 j0) ->
    rw_cells bsegs m R [CB 16 b16; CB 4 jb; CB 4 jc] -> shz m R 24 -> mem_inv bsegs m -> 0 <= bv_unsigned ra < 2^64 ->
    evt bsegs (fun ms => exists (m1 : mem) (y5' y6' y7' y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (g20 : list byte),
        ms = MS (mkR ra (wz q) gp (wz TPV) y5' y6' y7' s0 s1 y10 y11 y12 y13 y14 y15 y16 y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                F (ret_pc ra) fc None m1 (seg_rom bsegs)
        /\ munch [(R + 16, R + 20)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 (ae_lo E) q
        /\ rw_cells bsegs m1 R [CB 16 b16; C4 (wz 17); CB 4 g20])
      (MS (mkR (wz 0x97a30) (wz (q + -80)) gp (wz TPV) y0 y1 y2 (wz R) (wz EL) v z1 z2 z3 z4 z5 z6 z7 (wz (EL + 8)) (wz 2147450880) s4' s5 s6' s7 s8 s9 s10 s11 y3 y4 y5 y6)
          F (wz 0x97a30) fc None m (seg_rom bsegs)).
  Proof using OK.
    intros until j0. intros QR RH R8 LO ST FR RC SHZR MI RA0.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]]. unfold TPV, gstr_frame, SEGTOP_A, USTACK_TOP in *.
    hide R8.
    pose proof (munch_refl [(R + 16, R + 20)] m) as MU. pose proof (wmono_refl bsegs m) as WM.

    step. astep. chk0 SHZR (R + 16). step. if_false.
    step.

    do 9 step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => lazymatch goal with H : stk bsegs mx _ _ |- _ => release_frame FR H q end end. step.
    apply evt_done.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists mx end.
    do 16 eexists. split; [atp_st_eq_goal|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
    split; [lazymatch goal with H : stk bsegs _ _ q |- _ => exact H end|].
    lazymatch goal with H : rw_cells bsegs _ R _ |- _ => exact H end.
  Qed.
  Hypothesis RC0 : rt_contracts RT.

  Theorem gstr_cpsA : forall (Σ : rts RT) PMc (q R EL j jj : Z) (dd : nat)
      (ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (g : list byte),
    fdfs_only PMc -> mat_stable PMc -> a_live RT Σ E -> AINV_A E m ->
    elem (ae_T E) (ae_S E) (ae_sn E) ck_any dd j jj -> 0 <= j ->
    rw_cells bsegs m EL [C8 (wz (ae_DOC E)); C8 (wz j)] -> q <= EL -> EL + 16 <= ae_hi E -> EL mod 8 = 0 ->
    rw_cells bsegs m R [CB 24 g] -> q <= R -> R + 24 <= ae_hi E -> R mod 8 = 0 -> (EL + 16 <= R \/ R + 24 <= EL) ->
    ART RT Σ m -> mem_inv bsegs m -> stk bsegs m (ae_lo E) q -> ae_lo E + GSTR_STACK_A <= q -> q mod 16 = 0 -> frm0 fc ->
    cps_f (ASTA RT Σ PMc (eq (MS (mkR ra (wz q) gp (wz TPV) t0 t1 t2 s0 s1 (wz R) (wz EL) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                               F (wz ATP_GETSTR_A) fc None m (seg_rom bsegs))))
      (ASTA RT Σ PMc (fun ms => exists (v : word) (m' : mem) (b16 g20 : list byte) (code : Z),
           ret_st ra (wz q) gp (wz TPV) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
           /\ rt_after_f RT Σ q (ae_lo E) m m' /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) q [(R, R + 24)] m m'
           /\ rw_cells bsegs m' R [CB 16 b16; C4 (wz code); CB 4 g20] /\ (code = 0 \/ code = 17))).
  Proof using AF OK RC0.
    intros Σ PMc q R EL j jj dd ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m g
      FDO MST LV AI EL0 J0 ELC QE EH E8 RC QR RH R8 ER ART0 MI0 ST0 LOR Q16 FRM.
    intros T cc [Hc FC0] Hk. unfold GSTR_STACK_A, RT_STACK in LOR.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ [S16 [NS8 [SNS [SS SL]]]] _ _ _ LOW0 [HL HT]].
    pose proof LV as (LT & LS & LP & LF & LWIN).
    pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
    assert (RA0 : 0 <= bv_unsigned ra < 2^64) by (pose proof (bv_unsigned_in_range 64 ra) as X; unfold bv_modulus in X; cbn in X; lia).
    assert (FPW : forall Σx, fp_client RT Σx (ae_lo E) (gstr_W q R)) by (intros Σx; apply fp_client_stack2; ul).
    assert (ARTW : forall m', munch (gstr_W q R) m m' -> wmono bsegs m m' -> ART RT Σ m').
    { intros m' MU WM. exact (lvl_art_munch RT AF E Σ _ m m' ART0 LV (FPW Σ) MU WM). }
    assert (HWlo : Forall (fun r => ae_lo E <= fst r) (gstr_W q R)) by (unfold gstr_W; constructor; [cbn; ul|]; constructor; [cbn; ul| constructor]).
    assert (AIM : forall m', munch (gstr_W q R) m m' -> wmono bsegs m m' -> AINV_A E m').
    { intros m' MU WM. exact (AINV_A_munch E _ m m' OK AI MU HWlo). }
    assert (SHZE : forall m', munch (gstr_W q R) m m' -> wmono bsegs m m' -> shz m' EL 16).
    { intros m' MU WM. apply (lvl_shz_rec RT AF E OK Σ m' EL 16 (ARTW m' MU WM) LV); first [lia | reflexivity]. }
    assert (SHZR : forall m', munch (gstr_W q R) m m' -> wmono bsegs m m' -> shz m' R 24).
    { intros m' MU WM. apply (lvl_shz_rec RT AF E OK Σ m' R 24 (ARTW m' MU WM) LV); first [lia | reflexivity]. }
    assert (SHZD : forall m', munch (gstr_W q R) m m' -> wmono bsegs m m' -> shz m' (ae_DOC E) 16).
    { intros m' MU WM. apply (lvl_shz_doc E OK). exact (AIM m' MU WM). }
    assert (SHZT : forall m', munch (gstr_W q R) m m' -> wmono bsegs m m' -> shz m' (ae_TAPE E) (8 * ae_n E)).
    { intros m' MU WM. exact (lvl_shz_tape RT AF E OK Σ m' (ARTW m' MU WM) LV). }
    assert (SHZS : forall m', munch (gstr_W q R) m m' -> wmono bsegs m m' -> shz m' (ae_SBUF E) (ae_NS E)).
    { intros m' MU WM. assert (S8 : ae_SBUF E mod 8 = 0) by (clear - S16; Z.div_mod_to_equations; lia).
      pose proof (shz_live RT AF Σ m' (ae_SBUF E) (ae_NS E) (ARTW m' MU WM) LS S8) as X.
      replace (8 * (ae_NS E / 8)) with (ae_NS E) in X by (clear - NS8; Z.div_mod_to_equations; lia). exact X. }
    pose proof (shb_cells_of_art RT AF Σ m ART0) as SHB.
    assert (EU : bv_unsigned (wz (q + -80)) = q + -80) by (apply unsigned_lit; ul).
    assert (Q16' : (q + -80) mod 16 = 0) by (replace (q + -80) with (q + (-5) * 16) by lia; rewrite Z.mod_add by lia; exact Q16).

    pose proof (gstr_walk1 q R EL j jj dd ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m g
                  AI EL0 J0 ELC QE EH E8 RC QR RH R8 ER MI0 ST0 ltac:(ul) Q16 SHB RA0 SHZE SHZR SHZD SHZT SHZS AIM) as W1.
    lazymatch type of W1 with evt bsegs _ ?X =>
      assert (W1' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end.
    clear W1.
    apply (cps_realizes bsegs _ _ _ cc (asta_evt_c RT AF Σ PMc _ _ MST W1') Hc). clear W1'. intros c1 Hc1.
    destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & MU1 & WM1 & MI1 & X1) & Hc1'). clear Hc1.
    pose proof (ARTW m1 MU1 WM1) as ART1.
    pose proof (rt_pres_fp_of_munch RT AF E Σ m (q + -96) q [(R, R + 24)] m m1 ART0 LV ltac:(ul) MU1) as PFP1.
    destruct X1 as [XSTR|XERR].
    -
      destruct XSTR as (y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & b16 & g20 & -> & ST1 & RC1).
      apply Hk. split; [| apply (cfrm0_of_asta RT Σ PMc (eq _) c1 Hc1'); intros ms0 <-; exact FRM].
      eapply ASTA_conseq; [exact Hc1'|]. intros ms <-.
      exists y10, m1, b16, g20, 0. split; [unfold ret_st; do 16 eexists; reflexivity|].
      split; [split; [exact ART1| split; [exact MI1| exact ST1]]|]. split; [exact PFP1|]. split; [exact RC1| left; reflexivity].
    -
      destruct XERR as (t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & s4' & s6' & j0 & -> & ST1 & FR1 & RC1).
      pose proof (call_ok_lvl RT E OK Σ m1 (q + -80) LV ST1 ltac:(ul) ltac:(ul) Q16') as COK1.
      assert (CDST : checked_dst RT Σ m1 (wz (q + -80)) R 16).
      { apply (checked_dst_stack RT AF Σ m1 _ R 16 ART1); [ul| ul| rewrite EU; lia|].
        apply (wr_at_sub m1 R 24 R 16); [| lia| lia| lia]. exact (proj2 RC1). }
      apply (rc_asan_memset RT RC0 Σ PMc (wz 0x97a30) (wz (q + -80)) gp (wz TPV) t0' t1' t2' (wz R) (wz EL)
               (wz R) (wz 0) (wz 16) a3' a4' a5' a6' a7' (wz (EL + 8)) (wz 2147450880) s4' s5 s6' s7 s8 s9 s10 s11 t3' t4' t5' t6'
               F fc m1 R 16 (Z_to_bv 8 0) (ae_lo E) FDO MST eq_refl eq_refl eq_refl ltac:(ul) ltac:(lia) CDST ART1 MI1 COK1 T c1 Hc1').
      intros c2 Hc2. unfold icpt_postF in Hc2.
      destruct (ASTA_unpack RT Σ _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & BY2) & Hc2'). clear Hc2.
      destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & ->).
      rewrite EU in ST2, PRES2. change (Z.to_nat 16) with 16%nat in BY2.
      rewrite (ret_pc_even 0x97a30) in Hc2' by lia.
      assert (FR2 : rw_cells bsegs m2 (q + -80) (gstr_frame ra s0 s1 s2 s3 s4 s5 s6 s7 j0)).
      { apply (rw_cells_agree_nw bsegs m1 m2 _ _ FR1). apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PRES2).
        intros x Hx. unfold gstr_frame in Hx. cbn [cells_size csize Nat.add] in Hx. split; [left; ul| lia]. }
      apply (rw_cells_split_CB bsegs _ _ [] 24 g [] [16; 4; 4]%nat) in RC1; [| reflexivity]. cbn [mk_CB_cells app] in RC1.
      lazymatch type of RC1 with rw_cells _ _ _ [CB 16 ?xa; CB 4 ?xb; CB 4 ?xc] => set (jA := xa) in RC1; set (jB := xb) in RC1; set (jC := xc) in RC1 end.
      clearbody jA jB jC.
      pose proof (rec_copy16 m1 m2 R [CB 16 jA] (CB 4 jB) jC (repeat (Z_to_bv 8 0) 16) _ _ _ RC1 eq_refl eq_refl BY2 eq_refl WM2 PRES2 ltac:(lia) ltac:(ul)) as RC2.
      pose proof (lvl_shz_rec RT AF E OK Σ m2 R 24 ART2 LV ltac:(lia) ltac:(lia) R8 eq_refl ltac:(lia)) as SHZR2.
      pose proof (gstr_walk2 q R EL ra gp u0 u1 u2 (wz R) b1 b2 b3 b4 b5 b6 b7 s0 s1 s2 s3 s4 s4' s5 s6 s6' s7 s8 s9 s10 s11 u3 u4 u5 u6 F2 fc m2
                    (repeat (Z_to_bv 8 0) 16) jB jC j0 QR RH R8 ltac:(ul) ST2 FR2 RC2 SHZR2 MI2 RA0) as W2.
      lazymatch type of W2 with evt bsegs _ ?X =>
        assert (W2' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W2) end.
      clear W2.
      apply (cps_realizes bsegs _ _ _ c2 (asta_evt_c RT AF Σ PMc _ _ MST W2') Hc2'). clear W2'. intros c3 Hc3.
      destruct (ASTA_unpack RT Σ _ _ c3 Hc3) as (ms3 & (m3 & y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & g20
                                                & -> & MU3 & WM3 & MI3 & ST3 & RC3) & Hc3'). clear Hc3.
      assert (ART3 : ART RT Σ m3).
      { apply (lvl_art_munch RT AF E Σ [(R + 16, R + 20)] m2 m3 ART2 LV); [apply fp_client_stack1; ul| exact MU3| exact WM3]. }
      apply Hk. split; [| apply (cfrm0_of_asta RT Σ PMc (eq _) c3 Hc3'); intros ms0 <-; exact FRM].
      eapply ASTA_conseq; [exact Hc3'|]. intros ms <-.
      exists y10, m3, (repeat (Z_to_bv 8 0) 16), g20, 17. split; [unfold ret_st; do 16 eexists; reflexivity|].
      split; [split; [exact ART3| split; [exact MI3| exact ST3]]|].
      split.
      { apply (rt_pres_fp_trans _ _ _ _ m m1 m3 PFP1). apply (rt_pres_fp_trans _ _ _ _ m1 m2 m3).
        - apply (rt_pres_fp_of_ex _ _ _ _ _ _ _ _ _ PRES2); [lia|]. intros a Ha. cbn [outside] in Ha. lia.
        - apply (rt_pres_fp_of_munch RT AF E Σ m (q + -96) q [(R, R + 24)] m2 m3 ART0 LV ltac:(ul)).
          eapply munch_weaken; [| exact MU3]. intros x Hx. cbn [outside] in *. lia. }
      split; [exact RC3| right; reflexivity].
  Qed.
End GStr.

