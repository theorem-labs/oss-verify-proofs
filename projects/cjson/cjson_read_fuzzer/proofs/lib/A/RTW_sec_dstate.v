(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From Stdlib Require Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require MState.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Mem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Cells.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Step.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Frame.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_rep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_art.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_cost.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_fp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_artF.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_pop.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_bandtac4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Ceil.
Module RT_artR.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_pop.RT_artP OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_bandtac4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bytes_at_functional : forall m a bs bs',
  bytes_at asegs m a bs -> bytes_at asegs m a bs' -> length bs = length bs' -> bs = bs'.
Proof.
  intros m a bs bs' (_ & _ & H) (_ & _ & H') L. apply nth_error_ext. intros n.
  destruct (Nat.lt_ge_cases n (length bs)) as [LT|GE].
  - rewrite <- (H n LT). rewrite <- (H' n ltac:(lia)). reflexivity.
  - rewrite (proj2 (nth_error_None bs n) GE). rewrite (proj2 (nth_error_None bs' n) ltac:(lia)). reflexivity.
Qed.

Lemma cells_at_C8_inj : forall m a v v', cells_at asegs m a [C8 v] -> cells_at asegs m a [C8 v'] -> v = v'.
Proof.
  intros m a v v' [_ H] [_ H']. cbn [cells_bytes cbytes flat_map app] in H, H'. rewrite !app_nil_r in H, H'.
  pose proof (bytes_at_functional m a (le8 v) (le8 v') H H' ltac:(rewrite !length_le8; reflexivity)) as E.
  rewrite <- (le_bytes_to_word_le8 v), <- (le_bytes_to_word_le8 v'). rewrite E. reflexivity.
Qed.

Lemma wz_inj : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 -> wz x = wz y -> x = y.
Proof.
  intros x y Hx Hy E. unfold wz in E.
  apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned in E. unfold bv_wrap in E.
  change (bv_modulus 64) with (2^64) in E. rewrite !Z.mod_small in E by lia. exact E.
Qed.

(* [comment removed for export] *)
Lemma fflags_layout : forall k, 0 <= k < 11 -> fflags_off k = 36864 - 2^(15 - k) /\ fcap k = 2^(14 - k).
Proof.
  intros k Hk.
  assert (C : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10) by lia.
  destruct C as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]; split; reflexivity.
Qed.

Lemma fflag_addr_range : forall fs k pos, 0 <= k < 11 -> 0 <= pos < fcap k ->
  fs + 4096 <= fflag_addr fs k pos /\ fflag_addr fs k pos + 1 <= fs + 0x9000.
Proof.
  intros fs k pos Hk Hp. pose proof (flags_ok k Hk) as [O1 O2]. unfold fflag_addr. lia.
Qed.

Lemma fflag_addr_inj : forall fs k pos k' pos', 0 <= k < 11 -> 0 <= pos < fcap k -> 0 <= k' < 11 -> 0 <= pos' < fcap k' ->
  fflag_addr fs k pos = fflag_addr fs k' pos' -> k = k' /\ pos = pos'.
Proof.
  intros fs k pos k' pos' Hk Hp Hk' Hp' E. unfold fflag_addr in E.
  destruct (fflags_layout k Hk) as [O C]. destruct (fflags_layout k' Hk') as [O' C']. rewrite C in Hp. rewrite C' in Hp'.
  destruct (Z.lt_trichotomy k k') as [LT|[EQ|GT]].
  - exfalso. assert (2 ^ (15 - k') <= 2 ^ (14 - k)) by (apply Z.pow_le_mono_r; lia).
    assert (2 ^ (14 - k) + 2 ^ (14 - k) = 2 ^ (15 - k)) by (replace (15 - k) with (Z.succ (14 - k)) by lia; rewrite Z.pow_succ_r by lia; lia).
    lia.
  - subst k'. split; [reflexivity| lia].
  - exfalso. assert (2 ^ (15 - k) <= 2 ^ (14 - k')) by (apply Z.pow_le_mono_r; lia).
    assert (2 ^ (14 - k') + 2 ^ (14 - k') = 2 ^ (15 - k')) by (replace (15 - k') with (Z.succ (14 - k')) by lia; rewrite Z.pow_succ_r by lia; lia).
    lia.
Qed.

Lemma lf_remove_In : forall F LF x, In x (lf_remove F LF) -> In x LF.
Proof.
  induction LF as [|[G k] LF IH]; intros x H; [exact H|]. cbn in H. destruct (G =? F); [right; exact H|].
  destruct H as [H|H]; [left; exact H| right; apply IH; exact H].
Qed.

Lemma lf_remove_spec : forall F LF, List.NoDup (map fst LF) -> In F (map fst LF) ->
  forall x, In x (lf_remove F LF) <-> In x LF /\ fst x <> F.
Proof.
  induction LF as [|[G k] LF IH]; intros ND HF x; [destruct HF|]. cbn in ND. inversion ND as [|? ? NI ND']; subst.
  cbn [lf_remove]. destruct (Z.eqb_spec G F) as [->|NE].
  - split.
    + intros H. split; [right; exact H|]. intros E. apply NI. rewrite <- E. apply in_map_iff. exists x. auto.
    + intros [[<-|H] NEx]; [exfalso; apply NEx; reflexivity| exact H].
  - cbn in HF. destruct HF as [E|HF]; [exfalso; exact (NE E)|]. cbn [In]. rewrite (IH ND' HF x).
    split; [intros [<-|[H1 H2]]; [split; [left; reflexivity| cbn; exact NE]| split; [right; exact H1| exact H2]]|].
    intros [[<-|H] NEx]; [left; reflexivity| right; split; assumption].
Qed.

Lemma lf_remove_nodup : forall F LF, List.NoDup (map fst LF) -> List.NoDup (map fst (lf_remove F LF)).
Proof.
  induction LF as [|[G k] LF IH]; intros ND; [constructor|]. cbn in ND. inversion ND as [|? ? NI ND']; subst. cbn [lf_remove].
  destruct (G =? F); [exact ND'|]. cbn [map fst]. constructor; [| apply IH; exact ND'].
  intros H. apply NI. apply in_map_iff in H as [x [Ex Hx]]. apply in_map_iff. exists x. split; [exact Ex| eapply lf_remove_In; exact Hx].
Qed.

Lemma existsb_ext_In : forall {A} (f g : A -> bool) l, (forall x, In x l -> f x = g x) -> existsb f l = existsb g l.
Proof.
  induction l as [|y l IH]; intros H; [reflexivity|]. cbn. rewrite (H y ltac:(left; reflexivity)). rewrite IH; [reflexivity|].
  intros x Hx. apply H. right. exact Hx.
Qed.

Lemma existsb_false_iff : forall {A} (f : A -> bool) l, existsb f l = false <-> forall x, In x l -> f x = false.
Proof.
  induction l as [|y l IH]; cbn; [split; [intros _ x F; destruct F| reflexivity]|].
  rewrite Bool.orb_false_iff, IH. split.
  - intros [H1 H2] x [<-|Hx]; [exact H1| apply H2; exact Hx].
  - intros H. split; [apply H; left; reflexivity| intros x Hx; apply H; right; exact Hx].
Qed.

Lemma existsb_remove_nomatch : forall {A} (f : A -> bool) (l l' : list A),
  (forall x, In x l -> f x = true -> In x l') ->
  (forall x, In x l' -> In x l) ->
  existsb f l = existsb f l'.
Proof.
  intros A f l l' H1 H2. destruct (existsb f l) eqn:E1; destruct (existsb f l') eqn:E2; try reflexivity.
  - apply existsb_exists in E1 as [x [Hx Fx]]. rewrite (proj1 (existsb_false_iff f l') E2 x (H1 x Hx Fx)) in Fx. discriminate.
  - apply existsb_exists in E2 as [x [Hx Fx]]. rewrite (proj1 (existsb_false_iff f l) E1 x (H2 x Hx)) in Fx. discriminate.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section REL.
Variables (a1 a2 a3 : Z) (a4 : list region_st) (a5 : bool) (a6 : list (list Z)) (a7 a8 : Z) (a9 : list (Z * Z))
          (a10 a11 : list qbatch) (a12 : depot_st) (a13 a14 : list (list Z)) (a15 : Z) (a16 : list Z)
          (a18 a19 : Z) (a20 : tls_st) (a21 : list (Z * Z)) (a22 : bool)
          (b1 b2 b3 : list (Z * Z)) (b4 : list qbatch) (b5 : list (qbatch * Z)).
Variables (LB : list (Z * Z)) (LF : list fframe).
Variables (Fr k fl : Z) (m m' : word -> option byte).
Let st  := mkRT a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 LF a18 a19 a20 a21 a22 LB b1 b2 b3 b4 b5.
Let st' := mkRT a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 (lf_remove Fr LF) a18 a19 a20 a21 a22 LB b1 b2 b3 b4 b5.
Hypothesis WF : RTWF st.
Hypothesis HR : RTREP st m.
Hypothesis IN : In (Fr, k) LF.
Hypothesis CELL : cells_at asegs m (Fr + fsz k - 8) [C8 (wz fl)].
Hypothesis MU : munch [(fl, fl + 1)] m m'.
Hypothesis WM : wmono asegs m m'.
Hypothesis NEW : rw_cells asegs m' fl [C1 (zb 0)].

Local Abbreviation fs := a15.
Let pos := fpos st Fr k.

Lemma fsR : ablk fs (fs + FS_TOTAL) /\ fs + FS_TOTAL <= CEIL /\ fs mod 4096 = 0.
Proof. pose proof (RT_fp.fs_range st WF) as H. cbn [st_fs st] in H. unfold CEIL. exact H. Qed.

Lemma frame_ok : (k = 1 \/ k = 2) /\ 0 <= pos < fcap k /\ Fr = fframe_addr fs k pos.
Proof. exact (wff_frame st (wf_fs_ok st WF) Fr k IN). Qed.

Lemma k_lt11 : 0 <= k < 11.
Proof. destruct frame_ok as ([-> | ->] & _); lia. Qed.

Lemma fl_eq : fl = fflag_addr fs k pos.
Proof.
  destruct (rr_fs st m HR) as (_ & _ & _ & _ & _ & _ & SAV). pose proof (SAV Fr k IN) as C2. cbn [st_fs st] in C2.
  pose proof (cells_at_C8_inj m _ _ _ CELL C2) as E.
  destruct NEW as [_ (B0 & B1 & _)]. cbn in B1.
  pose proof fsR as (F1 & F2 & _). pose proof (fflag_addr_range fs k pos k_lt11 (proj1 (proj2 frame_ok))) as [R1 R2].
  apply wz_inj; [lia| unfold KHIGHMEM_BEG, CEIL, FS_TOTAL in *; blia| exact E].
Qed.

Lemma fl_range : fs + 4096 <= fl /\ fl + 1 <= fs + 0x9000.
Proof. rewrite fl_eq. apply fflag_addr_range; [exact k_lt11| exact (proj1 (proj2 frame_ok))]. Qed.

(* [comment removed for export] *)
Lemma rel_Zimg : forall a sz lo hi, In (lo, hi) ART_STATIC -> lo <= a -> a + sz <= hi -> 0 < sz -> disjoint_from [(fl, fl + 1)] a sz.
Proof.
  intros a sz lo hi HS Ha H1 _. pose proof (static_facts lo hi HS) as (_ & S2 & _). pose proof fsR as (F1 & _). pose proof fl_range as [R1 R2]. cbn. split; [| exact I].
  left. pose proof (ablk_img _ _ F1) as F1'. unfold AIMG_HI, KHIGHMEM_BEG in *. lia.
Qed.
Lemma rel_Zheap' : forall lo hi, oclr lo hi -> hi <= CEIL ->
  (forall A n, In (A, n) (st_lb st) -> hi <= A \/ A + n <= lo) -> framefree st lo hi -> disjoint_from [(fl, fl + 1)] lo (hi - lo).
Proof.
  intros lo hi H1 H2 _ HF. pose proof fl_range as [R1 R2]. unfold framefree in HF. cbn [st_fs st] in HF. cbn. split; [| exact I].
  unfold FS_TOTAL in HF. lia.
Qed.
Lemma rel_Zsh : forall lo hi, 0 <= lo -> lo <= hi -> hi <= CEIL -> lo mod 8 = 0 -> framefree st lo hi ->
  disjoint_from [(fl, fl + 1)] (SH lo) (SH hi - SH lo).
Proof.
  intros lo hi H0 H1 H2 _ _. pose proof fsR as (F1 & _). pose proof fl_range as [R1 R2]. cbn. split; [| exact I].
  pose proof (rt_SH_bounds lo ltac:(unfold CEIL in *; lia)) as B1. pose proof (rt_SH_bounds hi ltac:(unfold CEIL in *; lia)) as B2.
  clear - F1 R1 R2 B1 B2. unfold FS_TOTAL in *. blia.
Qed.

Local Ltac byzone L := eapply L; first [exact WF | exact rel_Zimg | exact rel_Zheap' | exact rel_Zsh].

(* [comment removed for export] *)
Lemma flag_val_rel : forall k' pos', 0 <= k' < 11 -> 0 <= pos' < fcap k' ->
  flag_val st' k' pos' = (if (k' =? k) && (pos' =? pos) then 0 else flag_val st k' pos').
Proof.
  intros k' pos' Hk' Hp'. pose proof frame_ok as (K12 & PR & EF). pose proof (wff_nodup st (wf_fs_ok st WF)) as ND. cbn [st_lf st] in ND.
  assert (INF : In Fr (map fst LF)) by (apply in_map_iff; exists (Fr, k); auto).
  unfold flag_val, flag_live. cbn [st_lf st_fs st st'].
  destruct (Z.eqb_spec k' k) as [->|NK]; cbn [andb].
  - destruct (Z.eqb_spec pos' pos) as [->|NP].
    + (* [comment removed for export] *)
      replace (existsb _ (lf_remove Fr LF)) with false; [reflexivity|]. symmetry. apply existsb_false_iff.
      intros [G j] HG. apply (lf_remove_spec Fr LF ND INF) in HG as [HG NE]. cbn [fst snd] in *.
      apply Bool.andb_false_iff. right. apply Z.eqb_neq. intros E. apply NE. rewrite E, EF. reflexivity.
    + match goal with |- (if ?a then _ else _) = (if ?b then _ else _) => replace a with b; [reflexivity|] end.
      apply existsb_remove_nomatch.
      * intros [G j] HG M. apply (lf_remove_spec Fr LF ND INF). split; [exact HG|]. cbn [fst snd] in *.
        apply andb_prop in M as [_ M]. apply Z.eqb_eq in M. intros ->. apply NP.
        assert (M' : fframe_addr fs k pos = fframe_addr fs k pos') by (rewrite <- EF; exact M).
        unfold fframe_addr in M'. destruct (fsz_12 k K12) as (FZ & _).
        assert (0 < fsz k) by (rewrite FZ; destruct K12 as [-> | ->]; cbn; lia). nia.
      * intros x Hx. eapply lf_remove_In. exact Hx.
  - match goal with |- (if ?a then _ else _) = (if ?b then _ else _) => replace a with b; [reflexivity|] end.
    apply existsb_remove_nomatch.
    + intros [G j] HG M. apply (lf_remove_spec Fr LF ND INF). split; [exact HG|]. cbn [fst snd] in *.
      apply andb_prop in M as [M1 M2]. apply Z.eqb_eq in M1. apply Z.eqb_eq in M2. subst j. intros ->.
      pose proof (nodup_map_inj fst _ (Fr, k) (Fr, k') ND IN HG eq_refl). apply NK. congruence.
    + intros x Hx. eapply lf_remove_In. exact Hx.
Qed.

Lemma R_fs_rel : R_fs st' m'.
Proof.
  destruct (rr_fs st m HR) as (V1 & V2 & HINTS & LOG & GC & FLG & SAV). cbn [st_fs st] in *.
  pose proof fsR as (F1 & F2 & F3). unfold KHIGHMEM_BEG in F1. pose proof fl_range as [R1 R2].
  pose proof (rt_SH_bounds (fs + FS_FRAMES_OFF) ltac:(unfold FS_FRAMES_OFF, FS_TOTAL, CEIL in *; blia)) as B1.
  assert (LOW : forall a sz, a + sz <= fs + 4096 -> disjoint_from [(fl, fl + 1)] a sz) by (intros a sz H; cbn; split; [lia| exact I]).
  unfold R_fs. cbn [st_fs st_lf st'].
  split; [eapply RT_fp.visT; [exact WM| exact V1| unfold AIMG_HI; blia]|].
  split; [eapply RT_fp.visT; [exact WM| exact V2| unfold AIMG_HI; lia]|].
  split; [intros j Hj; eapply RT_fp.rwT; [exact MU| exact WM| exact (HINTS j Hj)| apply LOW; cbn; lia]|].
  split; [eapply RT_fp.rwT; [exact MU| exact WM| exact LOG| apply LOW; cbn; lia]|].
  split; [eapply RT_fp.rwT; [exact MU| exact WM| exact GC| apply LOW; cbn; lia]|].
  split.
  - intros k' pos' Hk' Hp'. rewrite (flag_val_rel k' pos' Hk' Hp').
    destruct (Z.eqb_spec k' k) as [->|NK]; [destruct (Z.eqb_spec pos' pos) as [->|NP]|]; cbn [andb].
    + rewrite <- fl_eq. exact NEW.
    + eapply RT_fp.rwT; [exact MU| exact WM| exact (FLG k pos' Hk' Hp')|]. cbn. split; [| exact I].
      rewrite fl_eq. pose proof frame_ok as (_ & PR & _).
      destruct (Z.eq_dec (fflag_addr fs k pos') (fflag_addr fs k pos)) as [E|NEQ].
      { exfalso. destruct (fflag_addr_inj fs k pos' k pos Hk' Hp' Hk' PR E) as [_ E2]. exact (NP E2). }
      unfold fflag_addr in *. lia.
    + eapply RT_fp.rwT; [exact MU| exact WM| exact (FLG k' pos' Hk' Hp')|]. cbn. split; [| exact I].
      rewrite fl_eq. pose proof frame_ok as (_ & PR & _).
      destruct (Z.eq_dec (fflag_addr fs k' pos') (fflag_addr fs k pos)) as [E|NEQ].
      { exfalso. destruct (fflag_addr_inj fs k' pos' k pos Hk' Hp' k_lt11 PR E) as [E1 _]. exact (NK E1). }
      unfold fflag_addr in *. lia.
  - intros F' k' Hin'. pose proof (lf_remove_In _ _ _ Hin') as Hin.
    eapply RT_fp.roT; [exact MU| exact (SAV F' k' Hin)|]. cbn. split; [| exact I].
    pose proof (frame_range st WF F' k' Hin) as (Hk' & X & Y & AL). cbn [st_fs st] in X. right.
    destruct (fsz_12 k' Hk') as (FZ' & _). assert (128 <= fsz k') by (rewrite FZ'; destruct Hk' as [-> | ->]; cbn; lia).
    unfold FS_FRAMES_OFF in X. lia.
Qed.

Lemma RTREP_rel : RTREP st' m'.
Proof.
  pose proof rel_Zimg as ZI. pose proof rel_Zheap' as ZH. pose proof rel_Zsh as ZS.
  constructor.
  - eapply (RT_fp.T_link [(fl, fl+1)] m m' MU); [exact (rr_link st m HR)| eapply W_link; eauto].
  - eapply (RT_fp.T_consts st WF [(fl, fl+1)] m m' MU WM); [exact (rr_consts st m HR)| eapply W_consts; eauto].
  - eapply (RT_fp.T_alloc st [(fl, fl+1)] m m' MU WM); [exact (rr_alloc st m HR)| eapply W_alloc; eauto].
  - eapply (RT_fp.T_rinfo st WF [(fl, fl+1)] m m' MU WM); [exact (rr_rinfo st m HR)| eapply W_rinfo; eauto].
  - eapply (RT_fp.T_regions st WF [(fl, fl+1)] m m' MU WM); [exact (rr_regions st m HR)| eapply W_regions; eauto].
  - eapply (RT_fp.T_avail st WF [(fl, fl+1)] m m' MU WM); [exact (rr_avail st m HR)| eapply W_avail; eauto].
  - eapply (RT_fp.T_cache st [(fl, fl+1)] m m' MU WM); [exact (rr_cache st m HR)| eapply W_cache; eauto].
  - eapply (RT_fp.T_thread st WF [(fl, fl+1)] m m' MU WM); [exact (rr_thread st m HR)| eapply W_thread; eauto].
  - eapply (RT_fp.T_live st WF [(fl, fl+1)] m m' MU WM); [exact (rr_live st m HR)| eapply W_live; eauto].
  - eapply (RT_fp.T_quar st WF [(fl, fl+1)] m m' MU WM); [exact (rr_quar st m HR)| eapply W_quar; eauto].
  - eapply (RT_fp.T_batches st WF [(fl, fl+1)] m m' MU WM); [exact (rr_batches st m HR)| eapply W_batches; eauto].
  - eapply (RT_fp.T_ptrarr st WF [(fl, fl+1)] m m' MU WM); [exact (rr_ptrarr st m HR)| eapply W_ptrarr; eauto].
  - eapply (RT_fp.T_depot st WF [(fl, fl+1)] m m' MU WM); [exact (rr_depot st m HR)| eapply W_depot; eauto].
  - exact R_fs_rel.
  - eapply (RT_fp.T_ia [(fl, fl+1)] m m' MU WM); [exact (rr_ia st m HR)| eapply W_ia; eauto].
  - eapply (RT_fp.T_lowshadow [(fl, fl+1)] m m' MU WM); [exact (rr_lowshadow st m HR)| eapply W_lowshadow; eauto].
Qed.

Lemma RTWF_rel : RTWF st'.
Proof.
  constructor.
  - destruct (wf_base_ok st WF); constructor; assumption.
  - intros c Hc. destruct (wf_class_ok st WF c Hc); constructor; assumption.
  - destruct (wf_blocks_ok st WF); constructor; assumption.
  - destruct (wf_sec_ok st WF); constructor; assumption.
  - destruct (wf_quar_ok st WF); constructor; assumption.
  - destruct (wf_depot_ok st WF); constructor; assumption.
  - pose proof (wf_fs_ok st WF) as WFF. constructor.
    + cbn [st_lf st']. apply lf_remove_nodup. exact (wff_nodup st WFF).
    + intros F j Hin. exact (wff_frame st WFF F j (lf_remove_In _ _ _ Hin)).
Qed.

Lemma RTMODEL_rel : forall mo, RTMODEL st mo -> RTMODEL st' mo.
Proof. intros mo H. exact H. Qed.

(* [comment removed for export] *)
Lemma rt_prov_rel : rt_prov st' = rt_prov st.
Proof.
  assert (E1 : prov_classes st' = prov_classes st) by reflexivity.
  assert (E2 : prov_nb st' = prov_nb st) by reflexivity.
  assert (E3 : prov_q st' = prov_q st) by reflexivity.
  assert (E4 : prov_ptr st' = prov_ptr st) by reflexivity.
  assert (E5 : prov_live st' = prov_live st) by reflexivity.
  assert (E6 : prov_quar st' = prov_quar st) by reflexivity.
  assert (E7 : prov_depot st' = prov_depot st) by reflexivity.
  assert (E8 : prov_slots st' = prov_slots st) by reflexivity.
  assert (E9 : prov_l24 st' = prov_l24 st) by reflexivity.
  unfold rt_prov. rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9. reflexivity.
Qed.
End REL.

(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem artd_ff_release : forall sp0 SPB LB LF TRS B m m' mo g Fr k fl,
  ARTd sp0 SPB LB LF TRS B m mo g -> In (Fr, k) LF ->
  cells_at asegs m (Fr + fsz k - 8) [C8 (wz fl)] ->
  munch [(fl, fl + 1)] m m' -> wmono asegs m m' -> rw_cells asegs m' fl [C1 (zb 0)] ->
  ARTd sp0 SPB LB (lf_remove Fr LF) TRS B m' mo g.
Proof.
  intros sp0 SPB LB LF TRS B m m' mo g Fr k fl H IN CELL MU WM NEW.
  destruct H as (st & HR & WF & HM & HO & HB & HG & HFR & Hsp0 & HLB & HLF & HTRS & HQ & HB0 & HB1 & HSPB & HSW).
  exists (set_lb_lf st LB (lf_remove Fr LF)). destruct st. cbn in Hsp0, HLB, HLF, HTRS. subst. cbn [set_lb_lf].
  split; [eapply RTREP_rel; eauto|]. split; [eapply RTWF_rel; eauto|]. split; [exact HM|].
  split; [exact HO|]. split; [exact HB|]. split; [eapply GWIN_mem; [exact HG| exact HO| exact WM]|]. split; [exact HFR|]. repeat (split; [reflexivity|]). split; [exact HQ|]. split; [exact HB0|]. split; [| split; [exact HSPB| exact HSW]].
  erewrite rt_prov_rel. exact HB1.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem artd_flag_high : forall sp0 SPB LB LF TRS B m mo g Fr k fl,
  ARTd sp0 SPB LB LF TRS B m mo g -> In (Fr, k) LF ->
  cells_at asegs m (Fr + fsz k - 8) [C8 (wz fl)] -> 0 <= fl < 2^64 -> ablk fl (fl + 1).   (* [comment removed for export] *)
Proof.
  intros sp0 SPB LB LF TRS B m mo g Fr k fl H Hin HC Hfl.
  destruct H as (st & HR & WF & HM & HO & HB & HG & HFR & Hsp0 & HLB & HLF & HTRS & HQ & HB0 & HB1 & HSPB & HSW). subst LF.
  destruct (rr_fs st m HR) as (_ & _ & _ & _ & _ & _ & SAV). pose proof (SAV Fr k Hin) as HC'.
  destruct (wff_frame st (wf_fs_ok st WF) Fr k Hin) as (Hk & Hpos & _).
  pose proof (fs_range st WF) as (F1 & F2 & F3).
  pose proof (fflag_addr_range (st_fs st) k (fpos st Fr k) ltac:(lia) Hpos) as [A1 A2].
  assert (E : fl = fflag_addr (st_fs st) k (fpos st Fr k)).
  { apply wz_inj; [exact Hfl| unfold CEIL, KHIGHMEM_BEG, FS_TOTAL in *; blia|]. exact (cells_at_C8_inj m _ _ _ HC HC'). }
  rewrite E. apply (ablk_sub _ _ _ _ F1); unfold FS_TOTAL in *; lia.
Qed.

(* [comment removed for export] *)
Theorem artd_flag_low : forall sp0 SPB LB LF TRS B m mo g Fr k fl F' k',
  ARTd sp0 SPB LB LF TRS B m mo g -> In (Fr, k) LF ->
  cells_at asegs m (Fr + fsz k - 8) [C8 (wz fl)] -> 0 <= fl < 2^64 -> In (F', k') LF -> fl + 1 <= F'.
Proof.
  intros sp0 SPB LB LF TRS B m mo g Fr k fl F' k' H Hin HC Hfl Hin'.
  destruct H as (st & HR & WF & HM & HO & HB & HG & HFR & Hsp0 & HLB & HLF & HTRS & HQ & HB0 & HB1 & HSPB & HSW). subst LF.
  destruct (rr_fs st m HR) as (_ & _ & _ & _ & _ & _ & SAV). pose proof (SAV Fr k Hin) as HC'.
  destruct (wff_frame st (wf_fs_ok st WF) Fr k Hin) as (Hk & Hpos & _).
  pose proof (fs_range st WF) as (F1 & F2 & F3).
  pose proof (fflag_addr_range (st_fs st) k (fpos st Fr k) ltac:(lia) Hpos) as [A1 A2].
  assert (E : fl = fflag_addr (st_fs st) k (fpos st Fr k)).
  { apply wz_inj; [exact Hfl| unfold CEIL, KHIGHMEM_BEG, FS_TOTAL in *; blia|]. exact (cells_at_C8_inj m _ _ _ HC HC'). }
  pose proof (frame_range st WF F' k' Hin') as (_ & X & _). unfold FS_FRAMES_OFF in X. rewrite E. lia.
Qed.


End CeilWrap.
End RT_artR.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_front.
Module RT_fresh.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_front OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_artF RT_artR OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_bandtac4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fresh_upto (X : Z) (st : rtstate) : Prop :=
  forall c, 0 <= c < KNUMCLASSES -> X <= csize c -> fresh_cls st c.
Definition AFRESHd (X : Z) (m : word -> option byte) (mo : Model) (g : lghost) : Prop :=
  forall st, RTREP st m -> RTWF st -> fresh_upto X st.

Lemma afreshd_mono : forall X Y m mo g, AFRESHd X m mo g -> X <= Y -> AFRESHd Y m mo g.
Proof. intros X Y m mo g H HXY st HR WF c Hc HY. apply (H st HR WF c Hc). lia. Qed.
Lemma afreshd_model : forall X m mo mo' g, AFRESHd X m mo g ->
  m_vmmaps mo' = m_vmmaps mo -> m_vm_lazy mo' = m_vm_lazy mo -> m_halted mo' = None -> AFRESHd X m mo' g.
Proof. intros X m mo mo' g H _ _ _. exact H. Qed.
Lemma afreshd_g : forall X m mo g g', AFRESHd X m mo g -> AFRESHd X m mo g'.
Proof. intros X m mo g g' H. exact H. Qed.

(* [comment removed for export] *)
Lemma fresh_cls_facts : forall st c, fresh_cls st c ->
  r_allocated (rg st c) = 0 /\ r_mapped (rg st c) = 0 /\ r_mapped_fa (rg st c) = 0 /\ r_exhausted (rg st c) = false
  /\ r_fa (rg st c) = [] /\ num_freed st c = 0 /\ cch st c = [] /\ ncarved st c = 0 /\ navail st c = 0.
Proof.
  intros st c [E1 E2]. unfold num_freed, ncarved, navail, avail_cptrs. rewrite E1, E2. cbn. repeat split; reflexivity.
Qed.
Lemma fresh_cls_used : forall st c, RTWF st -> 0 <= c < KNUMCLASSES -> fresh_cls st c -> used_cptrs st c = [].
Proof.
  intros st c WF Hc HF. pose proof (wc_used_all st c (wf_class_ok st WF c Hc)) as E.
  destruct (fresh_cls_facts st c HF) as (_ & _ & _ & _ & _ & _ & _ & NC & _). rewrite NC in E.
  destruct (used_cptrs st c); [reflexivity| unfold zlen in E; cbn in E; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rw_W8_inj : forall m a u v, rw_cells asegs m a [W8 u] -> rw_cells asegs m a [W8 v] ->
  0 <= u < 2^64 -> 0 <= v < 2^64 -> u = v.
Proof.
  intros m a u v Hu Hv Ru Rv. apply wz_inj; [exact Ru| exact Rv|].
  exact (cells_at_C8_inj m a (wz u) (wz v) (rw_cells_cells m a _ Hu) (rw_cells_cells m a _ Hv)).
Qed.
Lemma cells_W8_inj : forall m a u v, cells_at asegs m a [W8 u] -> cells_at asegs m a [W8 v] ->
  0 <= u < 2^64 -> 0 <= v < 2^64 -> u = v.
Proof. intros m a u v Hu Hv Ru Rv. apply wz_inj; [exact Ru| exact Rv|]. exact (cells_at_C8_inj m a (wz u) (wz v) Hu Hv). Qed.

Lemma cells_at_C4_inj : forall m a (v v' : word), cells_at asegs m a [C4 v] -> cells_at asegs m a [C4 v'] ->
  bv_unsigned v mod 2^32 = bv_unsigned v' mod 2^32.
Proof.
  intros m a v v' [_ H] [_ H']. cbn [cells_bytes cbytes flat_map app] in H, H'. rewrite !app_nil_r in H, H'.
  pose proof (bytes_at_functional m a (le4 v) (le4 v') H H' ltac:(rewrite !length_le4; reflexivity)) as E.
  rewrite <- (bytes_le_to_Z_le4 v), <- (bytes_le_to_Z_le4 v'). rewrite E. reflexivity.
Qed.
Lemma rw_W4_inj : forall m a u v, rw_cells asegs m a [W4 u] -> rw_cells asegs m a [W4 v] ->
  0 <= u < 2^32 -> 0 <= v < 2^32 -> u = v.
Proof.
  intros m a u v Hu Hv Ru Rv.
  pose proof (cells_at_C4_inj m a (wz u) (wz v) (rw_cells_cells m a _ Hu) (rw_cells_cells m a _ Hv)) as E.
  unfold wz in E. rewrite !Z_to_bv_unsigned in E. unfold bv_wrap in E. change (bv_modulus 64) with (2^64) in E.
  rewrite !(Z.mod_small _ (2^64)) in E by lia. rewrite !Z.mod_small in E by lia. exact E.
Qed.
Lemma cells_at_C1_inj : forall m a (b b' : byte), cells_at asegs m a [C1 b] -> cells_at asegs m a [C1 b'] -> b = b'.
Proof.
  intros m a b b' [_ H] [_ H']. cbn [cells_bytes cbytes flat_map app] in H, H'.
  pose proof (bytes_at_functional m a [b] [b'] H H' eq_refl) as E. injection E. auto.
Qed.
Lemma rw_W1_inj : forall m a u v, rw_cells asegs m a [W1 u] -> rw_cells asegs m a [W1 v] ->
  0 <= u < 256 -> 0 <= v < 256 -> u = v.
Proof.
  intros m a u v Hu Hv Ru Rv.
  pose proof (cells_at_C1_inj m a (zb u) (zb v) (rw_cells_cells m a _ Hu) (rw_cells_cells m a _ Hv)) as E.
  apply (f_equal bv_unsigned) in E. unfold zb in E. rewrite !Z_to_bv_unsigned in E. unfold bv_wrap in E.
  change (bv_modulus 8) with 256 in E. rewrite !Z.mod_small in E by lia. exact E.
Qed.

(* [comment removed for export] *)
Lemma rw_cells_pick : forall m a pre c post, rw_cells asegs m a (pre ++ c :: post) ->
  rw_cells asegs m (a + Z.of_nat (cells_size pre)) [c].
Proof. intros m a pre c post H. apply (rw_cells_mid m a pre [c] post). exact H. Qed.

Section AGREE.
Variables (st1 st2 : rtstate) (m : word -> option byte).
Hypotheses (HR1 : RTREP st1 m) (WF1 : RTWF st1) (HR2 : RTREP st2 m) (WF2 : RTWF st2).

Lemma agree_spacebeg : st_spacebeg st2 = st_spacebeg st1.
Proof.
  destruct (rr_alloc st1 m HR1) as ((j1 & j2 & j3 & A1) & _). destruct (rr_alloc st2 m HR2) as ((k1 & k2 & k3 & A2) & _).
  pose proof (rw_cells_pick m A_ALLOC [W8 (st_pbase st1); W8 PRIM_RES_SIZE; CB 16 j1] (W8 (st_spacebeg st1)) _ A1) as C1.
  pose proof (rw_cells_pick m A_ALLOC [W8 (st_pbase st2); W8 PRIM_RES_SIZE; CB 16 k1] (W8 (st_spacebeg st2)) _ A2) as C2.
  cbn [cells_size Cells.csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in C1, C2.
  pose proof (S_range st1 WF1) as (X1 & X2 & _). pose proof (P_range st1 WF1) as (Y1 & Y2 & _).
  pose proof (S_range st2 WF2) as (X1' & X2' & _). pose proof (P_range st2 WF2) as (Y1' & Y2' & _).
  unfold KHIGHMEM_BEG, KSPACESIZE, PRIM_RES_SIZE in *.
  eapply (rw_W8_inj m _ _ _ C2 C1); lia.
Qed.

Lemma agree_ctx : st_ctx st2 = st_ctx st1.
Proof.
  destruct (rr_thread st1 m HR1) as (_ & _ & _ & _ & _ & _ & _ & T1 & _). destruct (rr_thread st2 m HR2) as (_ & _ & _ & _ & _ & _ & _ & T2 & _).
  destruct (wb_ctx_loose st1 (wf_base_ok st1 WF1)) as (b1 & k1 & L1 & L2 & L3). destruct (loose0_range st1 WF1 _ _ L1) as (R1 & R2 & R3 & R4).
  destruct (wb_ctx_loose st2 (wf_base_ok st2 WF2)) as (b2 & k2 & M1 & M2 & M3). destruct (loose0_range st2 WF2 _ _ M1) as (Q1 & Q2 & Q3 & Q4).
  unfold KHIGHMEM_BEG in *. eapply (cells_W8_inj m _ _ _ T2 T1); blia.
Qed.

Lemma agree_t : st_t st2 = st_t st1.
Proof.
  destruct (rr_thread st1 m HR1) as (_ & _ & _ & _ & _ & T1 & _). destruct (rr_thread st2 m HR2) as (_ & _ & _ & _ & _ & T2 & _).
  rewrite agree_ctx in T2. pose proof (t_range st1 WF1) as [A1 A2]. pose proof (t_range st2 WF2) as [B1 B2]. unfold KHIGHMEM_BEG in *.
  eapply (rw_W8_inj m _ _ _ T2 T1); blia.
Qed.

Lemma agree_fresh : forall c, 0 <= c < KNUMCLASSES -> fresh_cls st1 c -> fresh_cls st2 c.
Proof.
  intros c Hc HF. destruct (fresh_cls_facts st1 c HF) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & _).
  pose proof (wf_class_ok st2 WF2 c Hc) as WC2.
  pose proof (wc_alloc_nonneg st2 c WC2) as G1. pose proof (wc_alloc_mapped st2 c WC2) as G2. pose proof (wc_mapped_max st2 c WC2) as G3.
  pose proof (wc_fa_nonneg st2 c WC2) as G4. pose proof (wc_fa_max st2 c WC2) as G5. pose proof (wc_num_freed st2 c WC2) as G6.
  pose proof (wc_cache_max st2 c WC2) as G7. pose proof (cmaxcount_le16 c) as G8. pose proof (zlen_nonneg (r_fa (rg st2 c))) as G9.
  pose proof (zlen_nonneg (cch st2 c)) as G10.
  unfold KFREEARRAY_OFF, KFREEARRAY_SIZE, num_freed in *.
  (* [comment removed for export] *)
  destruct (rr_rinfo st1 m HR1) as [_ RI1]. destruct (RI1 c Hc) as (jr1 & je1 & js1 & C1).
  destruct (rr_rinfo st2 m HR2) as [_ RI2]. destruct (RI2 c Hc) as (jr2 & je2 & js2 & C2).
  assert (EA : rinfo st2 c = rinfo st1 c) by (unfold rinfo, ris; rewrite agree_spacebeg; reflexivity). rewrite EA in C2.
  unfold rinfo_cells in C1, C2. cbv zeta in C1, C2. rewrite F1, F2, F3, F4 in C1. unfold num_freed in C1. rewrite F5 in C1. change (zlen (@nil Z)) with 0 in C1.
  (* [comment removed for export] *)
  assert (NF : zlen (r_fa (rg st2 c)) = 0).
  { pose proof (rw_cells_pick m (rinfo st1 c) [W8 0; W8 0] (W8 (zlen (r_fa (rg st2 c)))) _ C2) as X2.
    pose proof (rw_cells_pick m (rinfo st1 c) [W8 0; W8 0] (W8 0) _ C1) as X1. cbn [cells_size Cells.csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in X1, X2.
    eapply (rw_W8_inj m _ _ _ X2 X1); lia. }
  assert (MFA : r_mapped_fa (rg st2 c) = 0).
  { pose proof (rw_cells_pick m (rinfo st1 c) [W8 0; W8 0; W8 (zlen (r_fa (rg st2 c)))] (W8 (r_mapped_fa (rg st2 c))) _ C2) as X2.
    pose proof (rw_cells_pick m (rinfo st1 c) [W8 0; W8 0; W8 0] (W8 0) _ C1) as X1. cbn [cells_size Cells.csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in X1, X2.
    eapply (rw_W8_inj m _ _ _ X2 X1); lia. }
  assert (AL : r_allocated (rg st2 c) = 0).
  { pose proof (rw_cells_pick m (rinfo st1 c) [W8 0; W8 0; W8 (zlen (r_fa (rg st2 c))); W8 (r_mapped_fa (rg st2 c))] (W8 (r_allocated (rg st2 c))) _ C2) as X2.
    pose proof (rw_cells_pick m (rinfo st1 c) [W8 0; W8 0; W8 0; W8 0] (W8 0) _ C1) as X1. cbn [cells_size Cells.csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in X1, X2.
    eapply (rw_W8_inj m _ _ _ X2 X1); lia. }
  assert (MP : r_mapped (rg st2 c) = 0).
  { pose proof (rw_cells_pick m (rinfo st1 c) [W8 0; W8 0; W8 (zlen (r_fa (rg st2 c))); W8 (r_mapped_fa (rg st2 c)); W8 (r_allocated (rg st2 c)); W8 0] (W8 (r_mapped (rg st2 c))) _ C2) as X2.
    pose proof (rw_cells_pick m (rinfo st1 c) [W8 0; W8 0; W8 0; W8 0; W8 0; W8 0] (W8 0) _ C1) as X1. cbn [cells_size Cells.csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in X1, X2.
    eapply (rw_W8_inj m _ _ _ X2 X1); lia. }
  assert (EX : r_exhausted (rg st2 c) = false).
  { pose proof (rw_cells_pick m (rinfo st1 c) [W8 0; W8 0; W8 (zlen (r_fa (rg st2 c))); W8 (r_mapped_fa (rg st2 c)); W8 (r_allocated (rg st2 c)); W8 0; W8 (r_mapped (rg st2 c)); W8 0; CB 4 jr2]
                  (W1 (if r_exhausted (rg st2 c) then 1 else 0)) _ C2) as X2.
    pose proof (rw_cells_pick m (rinfo st1 c) [W8 0; W8 0; W8 0; W8 0; W8 0; W8 0; W8 0; W8 0; CB 4 jr1] (W1 0) _ C1) as X1.
    cbn [cells_size Cells.csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ length] in X1, X2.
    destruct (r_exhausted (rg st2 c)); [exfalso| reflexivity].
    pose proof (rw_W1_inj m _ _ _ X2 X1 ltac:(lia) ltac:(lia)). lia. }
  (* [comment removed for export] *)
  assert (CC : zlen (cch st2 c) = 0).
  { destruct (rr_cache st1 m HR1 c Hc) as [K1 _]. destruct (rr_cache st2 m HR2 c Hc) as [K2 _].
    assert (EP : pcaddr st2 c = pcaddr st1 c) by (unfold pcaddr, acache; rewrite agree_t; reflexivity). rewrite EP in K2.
    rewrite F7 in K1. change (zlen (@nil Z)) with 0 in K1.
    pose proof (rw_cells_take m (pcaddr st1 c) [W4 (zlen (cch st2 c))] _ K2) as X2.
    pose proof (rw_cells_take m (pcaddr st1 c) [W4 0] _ K1) as X1.
    eapply (rw_W4_inj m _ _ _ X2 X1); lia. }
  split.
  - destruct (rg st2 c) as [al mp fa ex l]. cbn in *. subst. destruct l; [reflexivity| unfold zlen in NF; cbn in NF; lia].
  - destruct (cch st2 c); [reflexivity| unfold zlen in CC; cbn in CC; lia].
Qed.
End AGREE.

Theorem fresh_agree : forall st1 st2 m X, RTREP st1 m -> RTWF st1 -> RTREP st2 m -> RTWF st2 ->
  fresh_upto X st1 -> fresh_upto X st2.
Proof. intros st1 st2 m X HR1 WF1 HR2 WF2 H c Hc HX. exact (agree_fresh st1 st2 m HR1 WF1 HR2 WF2 c Hc (H c Hc HX)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma afreshd_use : forall X m mo g st, AFRESHd X m mo g -> RTREP st m -> RTWF st -> fresh_upto X st.
Proof. intros X m mo g st H HR WF. exact (H st HR WF). Qed.
(* [comment removed for export] *)
Lemma afreshd_keep : forall X m' mo' g' st', RTREP st' m' -> RTWF st' -> fresh_upto X st' -> AFRESHd X m' mo' g'.
Proof. intros X m' mo' g' st' HR' WF' HF st'' HR'' WF''. eapply fresh_agree; [exact HR'| exact WF'| exact HR''| exact WF''| exact HF]. Qed.
(* [comment removed for export] *)
Lemma afreshd_transfer : forall X m mo g m' mo' g' st st',
  AFRESHd X m mo g -> RTREP st m -> RTWF st -> RTREP st' m' -> RTWF st' ->
  (forall c, 0 <= c < KNUMCLASSES -> X <= csize c -> fresh_cls st c -> fresh_cls st' c) ->
  AFRESHd X m' mo' g'.
Proof.
  intros X m mo g m' mo' g' st st' H HR WF HR' WF' K. eapply afreshd_keep; [exact HR'| exact WF'|].
  intros c Hc HX. apply K; [exact Hc| exact HX| exact (H st HR WF c Hc HX)].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem afreshd_frame : forall sp0 SPB LB LF TRS B m m' mo g W X,
  ARTd sp0 SPB LB LF TRS B m mo g -> AFRESHd X m mo g -> munch W m m' -> wmono asegs m m' ->
  Forall (cj_write_ok sp0 SPB LB LF) W -> AFRESHd X m' mo g.
Proof.
  intros sp0 SPB LB LF TRS B m m' mo g W X HA HF MU WM FW.
  destruct HA as (st & HR & WF & HM & HO & HB & HG & HFR & Hsp0 & HLB & HLF & HTRS & HQ & HB0 & HB1 & HSPB & HSW).
  assert (HR' : RTREP st m').
  { set (W' := List.filter (fun iv : Z * Z => fst iv <? snd iv) W).
    eapply (RTREP_frame st WF sp0 SPB W' m m'); try assumption.
    - rewrite Hsp0. exact HSPB.
    - subst LB LF. unfold W'. apply Forall_forall. intros iv Hiv. apply filter_In in Hiv as [Hiv _]. rewrite Forall_forall in FW. apply FW. exact Hiv.
    - unfold W'. apply Forall_forall. intros [lo hi] Hiv. apply filter_In in Hiv as [_ Hb]. cbn in Hb |- *. apply Z.ltb_lt. exact Hb.
    - apply munch_nonempty. exact MU. }
  eapply afreshd_keep; [exact HR'| exact WF| exact (HF st HR WF)].
Qed.


End CeilWrap.
End RT_fresh.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes PropExec MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LMeasure LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg RT_defs RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_wf RT_rep RT_kit CJ_iface RT_art.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_cost.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.RT_artG.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_fp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_fp RT_artF.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_secz.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_secz.RT_artZ.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_front.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_kit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit.RT_shlem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_sec.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_sec.RTW_secondary_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_secz RT_sec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_pop.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_pop.RT_artP.
Import RT_artR.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sec_remove (l : list (Z * Z)) (idx : Z) : list (Z * Z) :=
  let l' := removelast l in if idx <? zlen l' then updz l' idx (last l (0,0)) else l'.

Lemma zlen_removelast : forall {A} (l : list A), l <> [] -> zlen (removelast l) = zlen l - 1.
Proof.
  intros A l H. destruct l as [|x l]; [congruence|].
  rewrite (app_removelast_last x H) at 2. rewrite zlen_app, zlen_cons, zlen_nil. lia.
Qed.

Lemma nthz_app_l : forall {A} (l1 l2 : list A) i d, 0 <= i < zlen l1 -> nthz (l1 ++ l2) i d = nthz l1 i d.
Proof. intros A l1 l2 i d Hi. unfold nthz, zlen in *. destruct (Z.ltb_spec0 i 0); [lia|]. apply app_nth1. lia. Qed.
Lemma nthz_app_r1 : forall {A} (l1 : list A) x d, nthz (l1 ++ [x]) (zlen l1) d = x.
Proof. intros A l1 x d. unfold nthz, zlen. destruct (Z.ltb_spec0 (Z.of_nat (length l1)) 0); [lia|]. rewrite Nat2Z.id, app_nth2 by lia. rewrite Nat.sub_diag. reflexivity. Qed.

Section REM.
  Variables (l : list (Z * Z)) (idx : Z) (e : Z * Z).
  Hypothesis ND : List.NoDup (map fst l).
  Hypothesis HI : 0 <= idx < zlen l.
  Hypothesis HE : nthz l idx (0,0) = e.
  Let n := zlen l.
  Let l' := removelast l.
  Let lst := last l (0,0).

  Lemma l_split : l = l' ++ [lst].
  Proof. unfold l', lst. apply app_removelast_last. intros E. subst l. unfold zlen in HI. cbn in HI. lia. Qed.
  Lemma zlen_l' : zlen l' = n - 1.
  Proof. unfold l', n. apply zlen_removelast. intros E. subst l. unfold zlen in HI. cbn in HI. lia. Qed.
  Lemma lst_nth : nthz l (n - 1) (0,0) = lst.
  Proof.
    transitivity (nthz (l' ++ [lst]) (n - 1) (0,0)); [rewrite <- l_split; reflexivity|].
    rewrite <- zlen_l'. apply nthz_app_r1.
  Qed.
  Lemma l'_nth : forall i, 0 <= i < n - 1 -> nthz l' i (0,0) = nthz l i (0,0).
  Proof.
    intros i Hi. transitivity (nthz (l' ++ [lst]) i (0,0)); [| rewrite <- l_split; reflexivity].
    symmetry. apply nthz_app_l. rewrite zlen_l'. exact Hi.
  Qed.

  Lemma sec_remove_zlen : zlen (sec_remove l idx) = n - 1.
  Proof using ND HI HE.
    unfold sec_remove. fold l'. fold lst. destruct (Z.ltb_spec0 idx (zlen l')) as [L|L]; [| apply zlen_l'].
    transitivity (zlen l'); [unfold zlen; rewrite updz_length; reflexivity| apply zlen_l'].
  Qed.
  Lemma sec_remove_nth : forall i, 0 <= i < n - 1 ->
    nthz (sec_remove l idx) i (0,0) = if i =? idx then lst else nthz l i (0,0).
  Proof using ND HI HE.
    intros i Hi. unfold sec_remove. fold l'. fold lst. pose proof zlen_l' as ZL.
    destruct (Z.ltb_spec0 idx (zlen l')) as [L|L].
    - destruct (Z.eqb_spec i idx) as [->|NE].
      + apply nthz_updz_same. rewrite zlen_l'. lia.
      + rewrite nthz_updz_other by lia. apply l'_nth. exact Hi.
    - destruct (Z.eqb_spec i idx) as [->|NE]; [lia|]. apply l'_nth. exact Hi.
  Qed.

  (* [comment removed for export] *)
  Let l1 := firstn (Z.to_nat idx) l.
  Let l2 := skipn (S (Z.to_nat idx)) l.
  Lemma l_split_idx : l = l1 ++ e :: l2 /\ zlen l1 = idx.
  Proof.
    unfold l1, l2. rewrite <- HE. unfold nthz, zlen in *. destruct (Z.ltb_spec0 idx 0); [lia|].
    split; [| rewrite length_firstn; lia].
    remember (Z.to_nat idx) as k eqn:Hk. assert (Hk' : (k < length l)%nat) by lia. clear - Hk'.
    revert k Hk'. induction l as [|x t IH]; intros [|k] Hk; cbn in *; try lia; [reflexivity|].
    f_equal. apply IH. lia.
  Qed.

  Lemma updz_app_mid : forall (a b : list (Z * Z)) x y, updz (a ++ x :: b) (zlen a) y = a ++ y :: b.
  Proof.
    intros a b x y. unfold updz, zlen. destruct (Z.ltb_spec0 (Z.of_nat (length a)) 0); [lia|]. rewrite Nat2Z.id. clear.
    induction a as [|z a IH]; cbn; [reflexivity|]. f_equal. exact IH.
  Qed.

  Lemma sec_remove_perm : Permutation l (e :: sec_remove l idx).
  Proof using ND HI HE.
    destruct l_split_idx as [EL ZL1].
    unfold sec_remove. fold l'. fold lst. pose proof zlen_l' as ZL.
    destruct (Z.ltb_spec0 idx (zlen l')) as [L|L].
    - (* [comment removed for export] *)
      assert (NE2 : l2 <> []).
      { intros E2. rewrite E2 in EL. assert (zlen l = idx + 1) by (rewrite EL, zlen_app, zlen_cons, zlen_nil; lia). unfold n in ZL. lia. }
      pose proof (app_removelast_last (0,0) NE2) as E2. set (l2' := removelast l2) in *. set (x := last l2 (0,0)) in *.
      assert (EL2 : l = (l1 ++ e :: l2') ++ [x]).
      { rewrite EL, E2. rewrite <- app_assoc. reflexivity. }
      assert (EL' : l' = l1 ++ e :: l2') by (unfold l'; rewrite EL2; apply removelast_last).
      assert (ELST : lst = x) by (unfold lst; rewrite EL2; apply last_last).
      rewrite EL', <- ZL1, updz_app_mid. rewrite EL2 at 1. rewrite ELST.
      (* [comment removed for export] *)
      eapply Permutation_trans; [apply Permutation_sym; apply Permutation_cons_append|].
      (* [comment removed for export] *)
      eapply Permutation_trans; [apply perm_skip; apply Permutation_sym; apply Permutation_middle|].
      (* [comment removed for export] *)
      eapply Permutation_trans; [apply perm_swap|]. apply perm_skip. apply Permutation_middle.
    - (* [comment removed for export] *)
      assert (E2 : l2 = []).
      { destruct l2 as [|y t] eqn:El2; [reflexivity|]. exfalso.
        assert (zlen l >= idx + 2) by (rewrite EL, zlen_app, !zlen_cons; pose proof (zlen_nonneg t); lia). unfold n in ZL. lia. }
      rewrite E2 in EL. assert (El' : l' = l1) by (unfold l'; rewrite EL; apply removelast_last). rewrite El'.
      rewrite EL at 1. apply Permutation_sym. apply Permutation_cons_append.
  Qed.

  Lemma sec_remove_In : forall x, In x (sec_remove l idx) -> In x l.
  Proof using ND HI HE. intros x Hx. apply (Permutation_in x (Permutation_sym sec_remove_perm)). right. exact Hx. Qed.
  Lemma sec_remove_nodup_fst : List.NoDup (map fst (sec_remove l idx)) /\ ~ In (fst e) (map fst (sec_remove l idx)).
  Proof using ND HI HE.
    pose proof (Permutation_NoDup (Permutation_map fst sec_remove_perm) ND) as ND'. cbn [map] in ND'.
    inversion ND'; subst. split; assumption.
  Qed.
  Lemma sec_remove_notin : ~ In e (sec_remove l idx).
  Proof using ND HI HE. intros C. apply (proj2 sec_remove_nodup_fst). apply in_map_iff. exists e. auto. Qed.
  Lemma sec_remove_In_iff : forall x, In x l <-> x = e \/ In x (sec_remove l idx).
  Proof using ND HI HE.
    intros x. split; intros H.
    - apply (Permutation_in x sec_remove_perm) in H. destruct H as [H|H]; [left; symmetry; exact H| right; exact H].
    - destruct H as [->|H]; [| exact (sec_remove_In x H)]. rewrite <- HE. unfold nthz. destruct (Z.ltb_spec0 idx 0); [lia|]. apply nth_In. unfold zlen in HI. lia.
  Qed.
End REM.

(* [comment removed for export] *)
Lemma index_of_nthz : forall l i d, List.NoDup (map fst l) -> 0 <= i < zlen l -> index_of l (fst (nthz l i d)) = i.
Proof.
  induction l as [|x l IH]; intros i d ND Hi; [unfold zlen in Hi; cbn in Hi; lia|].
  rewrite zlen_cons in Hi. inversion ND as [|y t Hn Hnd]; subst. cbn [index_of].
  destruct (Z.eq_dec i 0) as [->|NZ].
  - unfold nthz. cbn. rewrite Z.eqb_refl. reflexivity.
  - replace (nthz (x :: l) i d) with (nthz l (i - 1) d).
    2:{ unfold nthz. destruct (Z.ltb_spec0 i 0); [lia|]. destruct (Z.ltb_spec0 (i - 1) 0); [lia|].
        replace (Z.to_nat i) with (S (Z.to_nat (i - 1))) by lia. reflexivity. }
    destruct (Z.eqb_spec (fst x) (fst (nthz l (i - 1) d))) as [E|NE].
    + exfalso. apply Hn. rewrite E. apply in_map. unfold nthz. destruct (Z.ltb_spec0 (i - 1) 0); [lia|]. apply nth_In. unfold zlen in Hi. lia.
    + rewrite (IH (i - 1) d Hnd) by lia. lia.
Qed.
Lemma index_of_In_bound : forall l x, In x (map fst l) -> 0 <= index_of l x < zlen l /\ fst (nthz l (index_of l x) (0,0)) = x.
Proof.
  induction l as [|y l IH]; intros x Hx; [destruct Hx|]. cbn [index_of map] in *. rewrite zlen_cons.
  destruct (Z.eqb_spec (fst y) x) as [E|NE].
  - split; [pose proof (zlen_nonneg l); lia|]. unfold nthz. cbn. exact E.
  - destruct Hx as [Hx|Hx]; [congruence|]. destruct (IH x Hx) as [B E]. split; [lia|].
    unfold nthz in *. destruct (Z.ltb_spec0 (index_of l x) 0); [lia|]. destruct (Z.ltb_spec0 (1 + index_of l x) 0); [lia|].
    replace (Z.to_nat (1 + index_of l x)) with (S (Z.to_nat (index_of l x))) by lia. cbn [nth]. exact E.
Qed.

Lemma skipn_nthz_cons : forall {A} (l : list A) (d : Z) (x : A) dflt,
  0 <= d < Z.of_nat (length l) -> nthz l d dflt = x -> skipn (Z.to_nat d) l = x :: skipn (Z.to_nat (d + 1)) l.
Proof.
  intros A l d x dflt Hd Hn. unfold nthz in Hn. destruct (Z.ltb_spec0 d 0); [lia|].
  replace (Z.to_nat (d + 1)) with (S (Z.to_nat d)) by lia. remember (Z.to_nat d) as k eqn:Hk.
  assert (Hk' : (k < length l)%nat) by lia. clear Hk Hd. subst x. revert k Hk'.
  induction l as [|y l IH]; intros [|k] Hk; cbn in *; try lia; [reflexivity|]. apply IH. lia.
Qed.

Lemma NoDup_map_fst_unique : forall (l : list (Z * Z)) x a b, List.NoDup (map fst l) -> In (x, a) l -> In (x, b) l -> a = b.
Proof.
  induction l as [|[y c] l IH]; intros x a b ND Ha Hb; [destruct Ha|]. cbn [map fst] in ND. inversion ND as [|? ? Hn Hl]; subst.
  destruct Ha as [Ea|Ha]; destruct Hb as [Eb|Hb].
  - congruence.
  - injection Ea; intros; subst. exfalso. apply Hn. apply in_map_iff. exists (x, b). auto.
  - injection Eb; intros; subst. exfalso. apply Hn. apply in_map_iff. exists (x, a). auto.
  - exact (IH x a b Hl Ha Hb).
Qed.

Lemma pwdj_perm : forall L L', Permutation L L' -> pwdj L -> pwdj L'.
Proof.
  intros L L' HPm. induction HPm as [|x l l' HP IH|x y l|l l' l'' H1 IH1 H2 IH2]; intros H.
  - exact I.
  - cbn in H |- *. destruct H as [HF HP']. split; [| exact (IH HP')].
    eapply Permutation_Forall; [exact HP| exact HF].
  - cbn in H |- *. destruct H as [HF1 [HF2 HP]]. apply Forall_cons_iff in HF1 as [H12 HF1].
    split; [constructor; [lia| exact HF2]|]. split; [exact HF1| exact HP].
  - apply IH2, IH1, H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section TRD.
Variables (a1 a2 a3 : Z) (a4 : list region_st) (a5 : bool) (a6 : list (list Z)) (a7 a8 : Z) (a9 : list (Z * Z))
          (a10 a11 : list qbatch) (a12 : depot_st) (a13 a14 : list (list Z)) (a15 : Z) (a16 : list Z) (a17 : list fframe)
          (a18 a19 : Z) (a20 : tls_st) (a21 : list (Z * Z)) (a22 : bool) (LB : list (Z * Z))
          (AP SP QP : list (Z * Z)) (b4 : list qbatch) (b5 : list (qbatch * Z)).
Let st := mkRT a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 LB AP SP QP b4 b5.
Hypothesis WF : RTWF st.
Variables (mb n : Z) (b : qbatch) (d : Z).
Hypothesis HP : bprim n = false.
Hypothesis QC : b5 = [(b, d)].
Hypothesis Hd : 0 <= d < qb_count b.
Hypothesis EL : nthz (qb_elems b) d (0,0) = (sec_user mb, n).

Let A := sec_user mb.
Definition didx : Z := index_of a9 mb.
Let idx := didx.
Let secD := sec_remove a9 idx.
Let stD := mkRT a1 a2 a3 a4 a5 a6 a7 a8 secD a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 LB AP SP QP b4 [(b, d + 1)].
Let Q := flat_map qb_elems (a10 ++ a11 ++ b4).
Let rest := skipn (Z.to_nat (d + 1)) (qb_elems b).

(* [comment removed for export] *)
Lemma qelems_st : qelems st = Q ++ (A, n) :: rest.
Proof.
  unfold qelems. cbn [st_qthread st_qglobal st_qtmp st_qcur st]. rewrite QC. cbn [flat_map fst snd]. rewrite app_nil_r.
  fold Q. f_equal. unfold rest. apply (skipn_nthz_cons _ _ _ (0,0)); [unfold qb_count in Hd; lia| exact EL].
Qed.
Lemma qelems_stD : qelems stD = Q ++ rest.
Proof. unfold qelems. cbn [st_qthread st_qglobal st_qtmp st_qcur stD]. cbn [flat_map fst snd]. rewrite app_nil_r. reflexivity. Qed.
Lemma all_blocks_st : all_blocks st = LB ++ (Q ++ (A, n) :: rest) ++ QP.
Proof. unfold all_blocks. rewrite qelems_st. reflexivity. Qed.
Lemma all_blocks_stD : all_blocks stD = LB ++ (Q ++ rest) ++ QP.
Proof. unfold all_blocks. rewrite qelems_stD. reflexivity. Qed.
Lemma A_in_blocks : In (A, n) (all_blocks st).
Proof. rewrite all_blocks_st. apply in_or_app. right. apply in_or_app. left. apply in_or_app. right. left. reflexivity. Qed.
Lemma all_blocks_perm : Permutation (all_blocks st) ((A, n) :: all_blocks stD).
Proof.
  rewrite all_blocks_st, all_blocks_stD. rewrite <- !app_assoc. cbn [app].
  change (LB ++ Q ++ (A, n) :: rest ++ QP) with (LB ++ Q ++ (A, n) :: (rest ++ QP)).
  rewrite (app_assoc LB Q ((A, n) :: (rest ++ QP))), (app_assoc LB Q (rest ++ QP)). apply Permutation_sym. apply Permutation_middle.
Qed.
Lemma blocksD_sub : forall x, In x (all_blocks stD) -> In x (all_blocks st).
Proof. intros x Hx. apply (Permutation_in x (Permutation_sym all_blocks_perm)). right. exact Hx. Qed.
Lemma A_notin_blocksD : ~ In (A, n) (all_blocks stD) /\ forall n', ~ In (A, n') (all_blocks stD).
Proof.
  pose proof (Permutation_NoDup (Permutation_map fst all_blocks_perm) (wk_nodup st (wf_blocks_ok st WF))) as ND. cbn [map fst] in ND.
  inversion ND as [|x l Hn Hl]; subst.
  split; [intros C; apply Hn; apply in_map_iff; exists (A, n); auto|].
  intros n' C. apply Hn. apply in_map_iff. exists (A, n'). auto.
Qed.

Lemma mbn_in_sec : In (mb, n) a9.
Proof.
  pose proof (wk_block st (wf_blocks_ok st WF) _ A_in_blocks) as (_ & _ & _ & HS). cbn [fst snd] in HS.
  specialize (HS HP). replace (b_map_beg A) with mb in HS; [exact HS|]. unfold A, b_map_beg, sec_user. lia.
Qed.
Lemma mb_in_fst : In mb (map fst a9).
Proof. apply in_map_iff. exists (mb, n). split; [reflexivity| exact mbn_in_sec]. Qed.
Lemma idx_facts : 0 <= idx < nsec st /\ nthz a9 idx (0,0) = (mb, n).
Proof.
  pose proof (ws_nodup st (wf_sec_ok st WF)) as ND. cbn [st_sec st] in ND.
  destruct (index_of_In_bound a9 mb mb_in_fst) as [B E]. unfold idx, didx, nsec. cbn [st_sec st]. split; [exact B|].
  (* [comment removed for export] *)
  destruct (nthz a9 (index_of a9 mb) (0,0)) as [mb' n'] eqn:En. cbn [fst] in E. subst mb'.
  assert (Hin : In (mb, n') a9). { rewrite <- En. unfold nthz. destruct (Z.ltb_spec0 (index_of a9 mb) 0); [lia|]. apply nth_In. unfold zlen in B. lia. }
  f_equal. exact (NoDup_map_fst_unique a9 mb n' n ND Hin mbn_in_sec).
Qed.

(* [comment removed for export] *)
Lemma dereg_qall : qall stD = qall st.
Proof. unfold qall. cbn [st_qthread st_qglobal st_qtmp st_qcur stD st]. rewrite QC. reflexivity. Qed.
Lemma dereg_q_prim : forall c, q_prim stD c = q_prim st c.
Proof.
  intros c. unfold q_prim. rewrite qelems_st, qelems_stD. rewrite !filter_app. cbn [List.filter fst snd]. rewrite HP. cbn [andb]. reflexivity.
Qed.
Lemma dereg_used : forall c, used_cptrs stD c = used_cptrs st c.
Proof.
  intros c. unfold used_cptrs, avail_cptrs, live_cptrs, quar_cptrs, qpend_cptrs, batch_cptrs, apend_cptrs, qbatch_addrs, lb_prim, qp_prim.
  rewrite dereg_q_prim, dereg_qall. reflexivity.
Qed.
Lemma dereg_nsec : nsec stD = nsec st - 1.
Proof. unfold nsec. cbn [st_sec stD st]. unfold secD. apply (sec_remove_zlen a9 idx (mb, n) (ws_nodup st (wf_sec_ok st WF))); [exact (proj1 idx_facts)| exact (proj2 idx_facts)]. Qed.

(* [comment removed for export] *)
Let RSEC (l : list (Z * Z)) := map (fun e : Z * Z => (fst e, fst e + smapsize (snd e))) l.
Lemma rt_ranges_of : forall s9 qc, rt_ranges (mkRT a1 a2 a3 a4 a5 a6 a7 a8 s9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 LB AP SP QP b4 qc) =
  ((a2, a2 + PRIM_RES_SIZE) :: (a7, a7 + PTRARR_RES_SIZE) :: map (fun e => (fst e, fst e + snd e)) a21) ++ RSEC s9
  ++ (map (fun b => (b, b + NODEBLOCK_SIZE)) (d_nblocks a12) ++ map (fun b => (b, b + STOREBLOCK_SIZE)) (d_sblocks a12)).
Proof. intros. unfold rt_ranges. cbn [st_pbase st_pa st_loose0 st_sec st_depot]. cbn [app]. rewrite <- ?app_assoc. reflexivity. Qed.
Lemma rt_ranges_perm : Permutation (rt_ranges st) ((mb, mb + smapsize n) :: rt_ranges stD).
Proof.
  unfold st, stD. rewrite !rt_ranges_of.
  pose proof (Permutation_map (fun e : Z * Z => (fst e, fst e + smapsize (snd e))) (sec_remove_perm a9 idx (mb, n) (ws_nodup st (wf_sec_ok st WF)) (proj1 idx_facts) (proj2 idx_facts))) as PM.
  cbn [map fst snd] in PM. fold (RSEC a9) in PM. fold (RSEC secD) in PM. unfold secD in PM |- *. fold idx.
  eapply Permutation_trans; [apply Permutation_app_head; apply Permutation_app_tail; exact PM|].
  apply Permutation_sym. apply Permutation_middle with (l1 := (a2, a2 + PRIM_RES_SIZE) :: (a7, a7 + PTRARR_RES_SIZE) :: map (fun e => (fst e, fst e + snd e)) a21).
Qed.
Lemma dereg_In_ranges : forall r, In r (rt_ranges stD) -> In r (rt_ranges st).
Proof. intros r Hr. apply (Permutation_in r (Permutation_sym rt_ranges_perm)). right. exact Hr. Qed.
Lemma mb_fresh : forall r, In r (rt_ranges stD) -> mb + smapsize n <= fst r \/ snd r <= mb.
Proof.
  intros r Hr. pose proof (pwdj_perm _ _ rt_ranges_perm (wb_pwdj st (wf_base_ok st WF))) as PW. cbn in PW. destruct PW as [HF _].
  rewrite Forall_forall in HF. specialize (HF r Hr). cbn [fst snd] in HF. lia.
Qed.

(* [comment removed for export] *)
Lemma RTWF_dereg : RTWF stD.
Proof.
  pose proof idx_facts as [HI HN]. pose proof (wf_base_ok st WF) as WB. pose proof (wf_sec_ok st WF) as WS.
  pose proof A_notin_blocksD as [NA NA'].
  constructor.
  - (* [comment removed for export] *) destruct WB; constructor; try assumption.
    + intros r Hr. exact (wb_ranges r (dereg_In_ranges r Hr)).
    + pose proof (pwdj_perm _ _ rt_ranges_perm wb_pwdj) as PW. cbn in PW. exact (proj2 PW).
  - (* [comment removed for export] *) intros c Hc. destruct (wf_class_ok st WF c Hc); constructor; try assumption; rewrite ?dereg_used; assumption.
  - (* [comment removed for export] *) pose proof (wf_blocks_ok st WF) as WK. constructor.
    + intros bk Hb. pose proof (wk_block st WK bk (blocksD_sub bk Hb)) as (K1 & K2 & K3 & K4). unfold wf_block. split; [exact K1|]. split; [exact K2|]. split; [exact K3|].
      intros HF. cbn [st_sec stD]. specialize (K4 HF). cbn [st_sec st] in K4.
      apply (sec_remove_In_iff a9 idx (mb, n) (ws_nodup st WS) HI HN) in K4 as [E|K4]; [| exact K4].
      exfalso. injection E as E1 E2. apply (NA' (snd bk)). replace A with (fst bk); [rewrite <- surjective_pairing; exact Hb|].
      unfold A, sec_user. unfold b_map_beg in E1. lia.
    + pose proof (Permutation_NoDup (Permutation_map fst all_blocks_perm) (wk_nodup st WK)) as ND. cbn [map] in ND. inversion ND; assumption.
  - (* [comment removed for export] *) destruct WS; constructor.
    + cbn [st_sec stD]. exact (proj1 (sec_remove_nodup_fst a9 idx (mb, n) ws_nodup HI HN)).
    + rewrite dereg_nsec. cbn [st_nreserved stD]. cbn [st_nreserved st] in ws_nres. lia.
    + intros e He. cbn [st_sec st_spend stD] in He |- *. pose proof (sec_remove_In a9 idx (mb, n) ws_nodup HI HN e He) as He0.
      destruct (ws_entry e He0) as (E1 & E2 & E3 & E4). split; [exact E1|]. split; [exact E2|]. split; [exact E3|].
      destruct E4 as [E4|E4]; [| right; exact E4]. left.
      apply (Permutation_in _ all_blocks_perm) in E4. destruct E4 as [E4|E4]; [| exact E4].
      exfalso. injection E4 as E5 E6. assert (fst e = mb) by (unfold A, sec_user in E5; lia).
      assert (e = (mb, n)).
      { rewrite (surjective_pairing e). f_equal; [lia|]. apply (NoDup_map_fst_unique a9 mb); [exact ws_nodup| rewrite <- H, <- surjective_pairing; exact He0| exact mbn_in_sec]. }
      subst e. exact (sec_remove_notin a9 idx (mb, n) ws_nodup HI HN He).
    + intros e He. cbn [st_sec st_spend stD] in He |- *. destruct (ws_spend e He) as [T1 T2]. cbn [st_sec st] in T1. split.
      * apply (sec_remove_In_iff a9 idx (mb, n) ws_nodup HI HN) in T1 as [->|T1]; [| exact T1]. exfalso. apply T2. exact A_in_blocks.
      * intros C. apply T2. exact (blocksD_sub _ C).
    + exact ws_spend_nodup.
  - (* [comment removed for export] *) destruct (wf_quar_ok st WF); constructor; try assumption.
    + intros bb Hb. rewrite dereg_qall in Hb. exact (wq_batch bb Hb).
    + (* [comment removed for export] *) cbn [st_qglobal st_qtmp st_qcur stD map fst]. cbn [st_qglobal st_qtmp st_qcur st] in wq_rec_max. rewrite QC in wq_rec_max. cbn [map fst] in wq_rec_max. exact wq_rec_max.
    + intros bd [<-|[]]. cbn [fst snd]. lia.
  - destruct (wf_depot_ok st WF); constructor; assumption.
  - destruct (wf_fs_ok st WF); constructor; assumption.
Qed.

(* [comment removed for export] *)
Lemma dereg_same : same_but_secondary st stD.
Proof. unfold same_but_secondary. repeat split; reflexivity. Qed.
Lemma dereg_rel : sec_dealloc_rel st stD b d mb n.
Proof.
  split; [exact dereg_same|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  cbn [st_sec st stD]. exact (sec_remove_perm a9 idx (mb, n) (ws_nodup st (wf_sec_ok st WF)) (proj1 idx_facts) (proj2 idx_facts)).
Qed.

(* [comment removed for export] *)
Lemma rt_prov_dereg : rt_prov stD + SEC_SLOT_TAX + 2 * smapsize n <= rt_prov st.
Proof.
  assert (E1 : prov_classes stD = prov_classes st) by reflexivity.
  assert (E2 : prov_nb stD = prov_nb st) by reflexivity.
  assert (E3 : prov_q stD = prov_q st) by reflexivity.
  assert (E5 : prov_live stD = prov_live st) by reflexivity.
  assert (E7 : prov_depot stD = prov_depot st) by reflexivity.
  assert (E9 : prov_l24 stD = prov_l24 st) by reflexivity.
  assert (E10 : prov_emb stD = prov_emb st) by reflexivity.   (* [comment removed for export] *)
  assert (E8 : prov_slots stD = prov_slots st - SEC_SLOT_TAX) by (unfold prov_slots; rewrite dereg_nsec; lia).
  assert (E4 : prov_ptr stD <= prov_ptr st).
  { unfold prov_ptr. cbn [st_nreserved stD st]. rewrite dereg_nsec. lia. }
  assert (E6 : prov_quar stD + 2 * smapsize n = prov_quar st).
  { unfold prov_quar. rewrite qelems_st, qelems_stD. cbn [st_qpend st stD]. rewrite !map_app. cbn [map snd]. rewrite !zsum_app. cbn [zsum fold_right].
    replace (rp n) with (2 * smapsize n) by (unfold rp; rewrite HP; reflexivity). unfold zsum. lia. }
  unfold rt_prov. rewrite E1, E2, E3, E5, E7, E8, E9. lia.
Qed.

(* [comment removed for export] *)
Let lst := last a9 (0,0).
Lemma dereg_index : forall x, In x (map fst secD) ->
  sec_index stD x = (if x =? fst lst then (if idx <? nsec st - 1 then idx else sec_index st x) else sec_index st x)
  /\ 0 <= sec_index stD x < nsec st - 1 /\ nthz secD (sec_index stD x) (0,0) = nthz a9 (sec_index st x) (0,0).
Proof.
  intros x Hx. pose proof idx_facts as [HI HN]. pose proof (ws_nodup st (wf_sec_ok st WF)) as ND. cbn [st_sec st] in ND.
  pose proof (sec_remove_nodup_fst a9 idx (mb, n) ND HI HN) as [NDD NIN]. fold secD in NDD, NIN.
  pose proof (sec_remove_zlen a9 idx (mb, n) ND HI HN) as ZL. fold secD in ZL. unfold nsec. cbn [st_sec st].
  destruct (index_of_In_bound secD x Hx) as [B E]. unfold sec_index. cbn [st_sec stD st]. fold secD. rewrite ZL in B.
  (* [comment removed for export] *)
  assert (HxO : In x (map fst a9)).
  { apply in_map_iff in Hx as (ex & Ex & Hex). apply in_map_iff. exists ex. split; [exact Ex| exact (sec_remove_In a9 idx (mb, n) ND HI HN ex Hex)]. }
  destruct (index_of_In_bound a9 x HxO) as [BO EO].
  pose proof (sec_remove_nth a9 idx (mb, n) ND HI HN (index_of secD x) B) as NT. fold secD lst in NT.
  assert (KEY : forall i j, 0 <= i < zlen a9 -> 0 <= j < zlen a9 -> fst (nthz a9 i (0,0)) = fst (nthz a9 j (0,0)) -> i = j).
  { intros i j Hi Hj Hij. rewrite <- (index_of_nthz a9 i (0,0) ND Hi), <- (index_of_nthz a9 j (0,0) ND Hj). rewrite Hij. reflexivity. }
  pose proof (lst_nth a9 idx (mb, n) ND HI HN) as LN. fold lst in LN.
  destruct (Z.eqb_spec (index_of secD x) idx) as [EI|NI].
  - (* [comment removed for export] *)
    rewrite EI in NT, E |- *. rewrite NT in E.
    assert (IL : idx < zlen a9 - 1) by lia.
    split; [| split; [lia| rewrite NT, <- LN; f_equal; symmetry; apply KEY; [lia| lia| rewrite LN, EO; symmetry; exact E]]].
    rewrite <- E, Z.eqb_refl. destruct (Z.ltb_spec0 idx (zlen a9 - 1)); [reflexivity| lia].
  - rewrite NT in E.
    assert (EQ : index_of a9 x = index_of secD x) by (apply KEY; [lia| lia| rewrite EO, E; reflexivity]).
    split; [| split; [lia| rewrite NT, EQ; reflexivity]].
    destruct (Z.eqb_spec x (fst lst)) as [EX|NX]; [| symmetry; exact EQ].
    destruct (Z.ltb_spec0 idx (zlen a9 - 1)) as [IL|IL]; [| symmetry; exact EQ].
    exfalso. enough (index_of secD x = zlen a9 - 1) by lia. apply KEY; [lia| lia|]. rewrite E, LN. exact EX.
Qed.

(* [comment removed for export] *)
Lemma rt_loose_of : forall s9 qc, rt_loose (mkRT a1 a2 a3 a4 a5 a6 a7 a8 s9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 LB AP SP QP b4 qc) =
  a21 ++ map (fun e => (fst e, smapsize (snd e))) s9 ++ map (fun b => (b, NODEBLOCK_SIZE)) (d_nblocks a12) ++ map (fun b => (b, STOREBLOCK_SIZE)) (d_sblocks a12).
Proof. intros. reflexivity. Qed.
Lemma rt_loose_perm : Permutation (rt_loose st) ((mb, smapsize n) :: rt_loose stD).
Proof.
  unfold st, stD. rewrite !rt_loose_of.
  pose proof (Permutation_map (fun e : Z * Z => (fst e, smapsize (snd e))) (sec_remove_perm a9 idx (mb, n) (ws_nodup st (wf_sec_ok st WF)) (proj1 idx_facts) (proj2 idx_facts))) as PM.
  cbn [map fst snd] in PM. unfold secD. fold idx.
  eapply Permutation_trans; [apply Permutation_app_head; apply Permutation_app_tail; exact PM|].
  apply Permutation_sym. apply (Permutation_middle a21).
Qed.
Lemma rt_loose_ranges : forall s9 qc e, In e (rt_loose (mkRT a1 a2 a3 a4 a5 a6 a7 a8 s9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 LB AP SP QP b4 qc)) ->
  In (fst e, fst e + snd e) (rt_ranges (mkRT a1 a2 a3 a4 a5 a6 a7 a8 s9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 LB AP SP QP b4 qc)).
Proof.
  intros s9 qc e He. rewrite rt_loose_of in He. rewrite rt_ranges_of. rewrite !in_app_iff in He. rewrite !in_app_iff. cbn [In].
  destruct He as [He|[He|[He|He]]].
  - left. right. right. apply in_map_iff. exists e. split; [reflexivity| exact He].
  - right. left. apply in_map_iff in He as (x & <- & Hx). apply in_map_iff. exists x. split; [reflexivity| exact Hx].
  - right. right. left. apply in_map_iff in He as (x & <- & Hx). apply in_map_iff. exists x. split; [reflexivity| exact Hx].
  - right. right. right. apply in_map_iff in He as (x & <- & Hx). apply in_map_iff. exists x. split; [reflexivity| exact Hx].
Qed.

Lemma RTMODEL_dereg : forall moX, LOK asegs moX -> RTMODEL st moX -> RTMODEL stD (mm_unmap (wz mb) (wz (smapsize n)) moX).
Proof.
  intros moX HO (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9).
  pose proof (ws_entry st (wf_sec_ok st WF) (mb, n) mbn_in_sec) as (_ & Hn40 & MAL & _). cbn [fst snd] in Hn40, MAL.
  pose proof (wb_ranges st (wf_base_ok st WF) (mb, mb + smapsize n)) as RG. cbn [fst snd] in RG.
  specialize (RG ltac:(unfold st; rewrite rt_ranges_of; rewrite !in_app_iff; right; left; apply in_map_iff; exists (mb, n); split; [reflexivity| exact mbn_in_sec])).
  pose proof (smapsize_pos n ltac:(lia)) as [SP0 _]. unfold KHIGHMEM_BEG, AIMG_HI in RG.
  pose proof (P_range st WF) as (P1 & P2 & P3). pose proof (pa_range st WF) as (Q1 & Q2 & _). cbn [st_pbase st_pa st] in P1, P2, P3, Q1, Q2. unfold KHIGHMEM_BEG, AIMG_HI in P1, Q1.
  assert (U1 : bv_unsigned (wz mb) = mb) by (unfold wz; apply unsigned_lit; blia).
  assert (U2 : bv_unsigned (wz (smapsize n)) = smapsize n) by (unfold wz; apply unsigned_lit; blia).
  pose proof (nowrap_of_wf _ (lok_na_ceil _ _ HO)) as Hna. pose proof (nowrap_of_ceil _ (lok_lazy_ceil _ _ HO)) as Hlz.
  (* [comment removed for export] *)
  pose proof mb_fresh as MF.
  assert (NB : forall lo2 sz2, In (lo2, lo2 + sz2) (rt_ranges stD) -> wz lo2 <> wz mb).
  { intros lo2 sz2 Hin E. pose proof (MF _ Hin) as D. cbn [fst snd] in D.
    pose proof (wb_ranges st (wf_base_ok st WF) _ (dereg_In_ranges _ Hin)) as (R1 & R2 & R3 & _). cbn [fst snd] in R1, R2, R3. unfold KHIGHMEM_BEG, AIMG_HI in R1.
    apply wz_inj in E; blia. }
  unfold RTMODEL. rewrite mm_unmap_maps. cbn [vm_limit st_pbase st_pa stD st].
  assert (ZR : forall lo2 sz2, In (lo2, lo2 + sz2) (rt_ranges stD) -> zin lo2 sz2 (vm_maps (m_vmmaps moX)) -> zin lo2 sz2 (map_remove (vm_maps (m_vmmaps moX)) (wz mb))).
  { intros lo2 sz2 Hin HZ. unfold zin in *. apply In_map_remove. split; [exact HZ| cbn [fst]; exact (NB lo2 sz2 Hin)]. }
  split; [apply ZR; [unfold stD; rewrite rt_ranges_of; left; reflexivity| exact M1]|].
  split; [apply ZR; [unfold stD; rewrite rt_ranges_of; right; left; reflexivity| exact M2]|].
  split. { unfold zin in *. apply In_map_remove. split; [exact M3|]. cbn [fst]. intros E. apply wz_inj in E; [| unfold KHIGHSHADOW_BEG; lia| blia]. unfold KHIGHSHADOW_BEG in E. blia. }
  split. { unfold zin in *. apply In_map_remove. split; [exact M4|]. cbn [fst]. intros E. apply wz_inj in E; [| unfold KLOWSHADOW_BEG; lia| blia]. unfold KLOWSHADOW_BEG in E. blia. }
  split; [| split; [| split; [| split]]].
  - intros e He. apply (ZR (fst e) (snd e)); [exact (rt_loose_ranges _ _ e He)|]. apply M5.
    apply (Permutation_in e (Permutation_sym rt_loose_perm)). right. exact He.
  - (* [comment removed for export] *)
    unfold zin in *. apply In_map_remove. split; [exact M6|]. cbn [fst]. intros E. apply wz_inj in E; [| unfold KLOWSHADOW_END; lia| blia]. unfold KLOWSHADOW_END in E. blia.
  - intros x Hx. specialize (M7 x Hx). unfold lzf in *. rewrite mm_unmap_lazy, mm_unmap_na, U1, U2.
    rewrite !inzr_maps_subtract by (first [exact Hlz| exact Hna| lia]).
    apply andb_true_iff in M7 as [L1 L2]. rewrite L1. apply negb_true_iff in L2. rewrite L2.
    unfold KLOWSHADOW_BEG, KLOWSHADOW_END, KHIGHSHADOW_BEG, KHIGHMEM_BEG, AIMG_HI in Hx.
    destruct (Z.leb_spec0 mb (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (mb + smapsize n)); cbn; try reflexivity; exfalso; blia.
  - exact M8.
  - intros e He. apply (sec_plain_unmap moX _ _ _ _ HO). apply M9. cbn [st_sec st]. cbn [st_sec stD] in He.
    exact (sec_remove_In a9 idx (mb, n) (ws_nodup st (wf_sec_ok st WF)) (proj1 idx_facts) (proj2 idx_facts) e He).
Qed.

(* [comment removed for export] *)
Lemma SWIN_dereg : forall g, SWIN st g -> SWIN stD g.
Proof.
  intros g HS e He. apply HS. cbn [st_sec st]. cbn [st_sec stD] in He.
  exact (sec_remove_In a9 idx (mb, n) (ws_nodup st (wf_sec_ok st WF)) (proj1 idx_facts) (proj2 idx_facts) e He).
Qed.

Lemma GWIN_dereg : forall m mo g, GWIN st m mo g -> GWIN stD m mo g.
Proof. intros m mo g H. exact H. Qed.
Lemma qelems_sub : forall x, In x (qelems stD) -> In x (qelems st).
Proof. intros x Hx. rewrite qelems_stD in Hx. rewrite qelems_st. apply in_app_iff in Hx as [Hx|Hx]; apply in_or_app; [left; exact Hx| right; right; exact Hx]. Qed.
End TRD.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition st_secdereg (st : rtstate) (mb : Z) (b : qbatch) (d : Z) : rtstate :=
  match st with
  | mkRT a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 LB AP SP QP b4 b5 =>
    mkRT a1 a2 a3 a4 a5 a6 a7 a8 (sec_remove a9 (index_of a9 mb)) a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 LB AP SP QP b4 [(b, d + 1)]
  end.

Section W2.
  Variables (st : rtstate) (mb n : Z) (b : qbatch) (d : Z).
  Hypothesis WF : RTWF st.
  Hypothesis HP : bprim n = false.
  Hypothesis QC : st_qcur st = [(b, d)].
  Hypothesis Hd : 0 <= d < qb_count b.
  Hypothesis EL : nthz (qb_elems b) d (0,0) = (sec_user mb, n).
  Let stD := st_secdereg st mb b d.
  Let idx := sec_index st mb.

  Lemma st_secdereg_fields :
    st_sec stD = sec_remove (st_sec st) idx /\ st_qcur stD = [(b, d + 1)] /\ st_spend stD = st_spend st /\ st_nreserved stD = st_nreserved st
    /\ st_pa stD = st_pa st /\ st_t stD = st_t st /\ st_sp0 stD = st_sp0 st /\ st_lb stD = st_lb st /\ st_lf stD = st_lf st /\ st_trs stD = st_trs st
    /\ st_depot stD = st_depot st /\ st_ctx stD = st_ctx st /\ st_qpend stD = st_qpend st /\ st_pbase stD = st_pbase st.
  Proof. unfold stD, idx, sec_index. destruct st. cbn. repeat (split; [reflexivity|]). reflexivity. Qed.

  Lemma idx_facts' : 0 <= idx < nsec st /\ nthz (st_sec st) idx (0,0) = (mb, n).
  Proof. unfold idx, sec_index. destruct st. eapply idx_facts; eauto. Qed.
  Lemma mbn_in_sec' : In (mb, n) (st_sec st).
  Proof. destruct st. eapply mbn_in_sec; eauto. Qed.
  Lemma A_in_blocks' : In (sec_user mb, n) (all_blocks st).
  Proof. destruct st. eapply A_in_blocks; eauto. Qed.
  Lemma dereg_nsec' : nsec stD = nsec st - 1.
  Proof. unfold stD. destruct st. eapply dereg_nsec; eauto. Qed.
  Lemma RTWF_dereg' : RTWF stD.
  Proof. unfold stD. destruct st. eapply RTWF_dereg; eauto. Qed.
  Lemma dereg_rel' : sec_dealloc_rel st stD b d mb n.
  Proof. unfold stD. destruct st. eapply dereg_rel; eauto. Qed.
  Lemma rt_prov_dereg' : rt_prov stD + SEC_SLOT_TAX + 2 * smapsize n <= rt_prov st.
  Proof. unfold stD. destruct st. eapply rt_prov_dereg; eauto. Qed.
  Lemma RTMODEL_dereg' : forall moX, LOK asegs moX -> RTMODEL st moX -> RTMODEL stD (mm_unmap (wz mb) (wz (smapsize n)) moX).
  Proof. unfold stD. destruct st. intros. eapply RTMODEL_dereg; eauto. Qed.
  Lemma GWIN_dereg' : forall m mo g, GWIN st m mo g -> GWIN stD m mo g.
  Proof. unfold stD. destruct st. intros m mo g H. exact H. Qed.
  Lemma SWIN_dereg' : forall g, SWIN st g -> SWIN stD g.
  Proof. unfold stD. destruct st. eapply SWIN_dereg; eauto. Qed.
  Lemma RTSH_dereg' : forall x, RTSH stD x <-> RTSH st x.
  Proof. unfold stD. destruct st. intros x. unfold RTSH. cbn. tauto. Qed.
  Lemma mb_fresh' : forall r, In r (rt_ranges stD) -> mb + smapsize n <= fst r \/ snd r <= mb.
  Proof. unfold stD. destruct st. eapply mb_fresh; eauto. Qed.
  Lemma dereg_In_ranges' : forall r, In r (rt_ranges stD) -> In r (rt_ranges st).
  Proof. unfold stD. destruct st. eapply dereg_In_ranges; eauto. Qed.
  Lemma all_blocks_perm' : Permutation (all_blocks st) ((sec_user mb, n) :: all_blocks stD).
  Proof. unfold stD. destruct st. eapply all_blocks_perm; eauto. Qed.
  Lemma blocksD_sub' : forall x, In x (all_blocks stD) -> In x (all_blocks st).
  Proof. unfold stD. destruct st. eapply blocksD_sub; eauto. Qed.
  Lemma A_notin_blocksD' : forall n', ~ In (sec_user mb, n') (all_blocks stD).
  Proof. unfold stD. destruct st. eapply A_notin_blocksD; eauto. Qed.
  Lemma qelems_stD' : forall x, In x (qelems stD) -> In x (qelems st).
  Proof. unfold stD. destruct st. eapply qelems_sub; eauto. Qed.
  Lemma dereg_index' : forall x, In x (map fst (st_sec stD)) ->
    sec_index stD x = (if x =? fst (last (st_sec st) (0,0)) then (if idx <? nsec st - 1 then idx else sec_index st x) else sec_index st x)
    /\ 0 <= sec_index stD x < nsec st - 1 /\ nthz (st_sec stD) (sec_index stD x) (0,0) = nthz (st_sec st) (sec_index st x) (0,0).
  Proof. unfold stD, idx, sec_index. destruct st. cbn. intros x Hx. eapply dereg_index; eauto. Qed.
  Lemma secD_In' : forall e, In e (st_sec stD) -> In e (st_sec st) /\ e <> (mb, n).
  Proof.
    intros e He. pose proof st_secdereg_fields as (E1 & _). rewrite E1 in He. pose proof idx_facts' as [HI HN].
    split; [exact (sec_remove_In _ _ _ (ws_nodup st (wf_sec_ok st WF)) HI HN e He)|].
    intros ->. exact (sec_remove_notin _ _ _ (ws_nodup st (wf_sec_ok st WF)) HI HN He).
  Qed.
  Lemma secD_nth' : forall i, 0 <= i < nsec st - 1 ->
    nthz (st_sec stD) i (0,0) = if i =? idx then last (st_sec st) (0,0) else nthz (st_sec st) i (0,0).
  Proof.
    intros i Hi. pose proof st_secdereg_fields as (E1 & _). rewrite E1. pose proof idx_facts' as [HI HN].
    apply (sec_remove_nth _ _ _ (ws_nodup st (wf_sec_ok st WF)) HI HN). unfold nsec in Hi. lia.
  Qed.
End W2.


End CeilWrap.
