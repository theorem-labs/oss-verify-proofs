(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatExec CatSim SymExec3 SymExec3Sound.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil BMem BCells BArr BLFrame BStep BellsX BMState BExec.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BLPropExec.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Conv LbB_FKit LbB_Call LbB_DKit.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition tab : Type := (expr * Z * Z * Z * list fent * list (Z * nat))%type.
Definition tb (t : tab) : expr := match t with (b, _, _, _, _, _) => b end.
Definition tB (t : tab) : Z := match t with (_, B, _, _, _, _) => B end.
Definition tlo (t : tab) : Z := match t with (_, _, lo, _, _, _) => lo end.
Definition thi (t : tab) : Z := match t with (_, _, _, hi, _, _) => hi end.
Definition ttbl (t : tab) : list fent := match t with (_, _, _, _, tbl, _) => tbl end.
Definition tks (t : tab) : list (Z * nat) := match t with (_, _, _, _, _, ks) => ks end.

Definition swinsT (L : list tab) : list (expr * Z * Z) := map (fun t => (tb t, tlo t, thi t)) L.
Definition winsT (L : list tab) : list (Z * Z) := map (fun t => (tB t + tlo t, tB t + thi t)) L.
Definition fknT (L : list tab) : list kentry := flat_map (fun t => fkn (tb t) (ttbl t)) L.

Definition tupd (log : list sentry) (k0 : N) (L : list tab) : list (Z * list fent) :=
  map (fun t => (tB t, fupd log (tb t) k0 (ttbl t) ++ fadd log (tb t) k0 (tks t))) L.

Definition tabs_wf (W : list word) (L : list tab) : Prop :=
  Forall (fun t => wcl (wbound W) (tb t) = true /\ bv_unsigned (edenot (wenv W) (tb t)) = tB t
                   /\ 0 <= tB t + tlo t /\ tlo t <= thi t /\ tB t + thi t <= 2 ^ 64
                   /\ fwcl (wbound W) (ttbl t) = true /\ fin (tlo t) (thi t) (fkeys (ttbl t) ++ tks t) = true) L
  /\ (forall t1 t2, In t1 L -> In t2 L -> expr_eqb (tb t1) (tb t2) = false ->
        tB t1 + thi t1 <= tB t2 + tlo t2 \/ tB t2 + thi t2 <= tB t1 + tlo t1).

Definition tabs_ok (W : list word) (m : mem) (L : list tab) : Prop :=
  Forall (fun t => ftbl W (tB t) m (ttbl t) /\ forall k w, In (k, w) (tks t) -> wr_at asegs m (tB t + k) (Z.of_nat w)) L.

Definition ftbls (W : list word) (m : mem) (TS : list (Z * list fent)) : Prop :=
  Forall (fun p => ftbl W (fst p) m (snd p)) TS.

Lemma fin_app_l : forall lo hi a b, fin lo hi (a ++ b) = true -> fin lo hi a = true.
Proof. intros lo hi a b H. unfold fin in *. rewrite forallb_app in H. apply andb_true_iff in H. tauto. Qed.

Lemma omiss_of_tabs : forall E W L log t,
  tabs_wf W L -> (forall n, (32 <= n < wbound W)%N -> ev E n = ev (wenv W) n) -> In t L ->
  forallb (sym_inside (swinsT L)) log = true ->
  Forall (omiss E (tb t) (tB t + tlo t) (thi t - tlo t)) log.
Proof.
  intros E W L log t [HW HD] HE Ht Hs. apply Forall_forall. intros se Hse Hne.
  pose proof (proj1 (forallb_forall _ _) Hs se Hse) as K.
  assert (Ex : exists t', In t' L /\ sym_in1 (tb t') (tlo t') (thi t') se = true).
  { clear - K. unfold swinsT in K. induction L as [|t0 L IH]; cbn [map sym_inside] in K; [discriminate|].
    apply orb_true_iff in K as [K|K]; [exists t0; split; [left; reflexivity | exact K]|].
    destruct (IH K) as (t' & H1 & H2). exists t'. split; [right; exact H1 | exact H2]. }
  destruct Ex as (t' & Ht' & K1). unfold sym_in1 in K1.
  apply andb_true_iff in K1 as [K1 K3]. apply andb_true_iff in K1 as [K1 K2].
  apply expr_eqb_true in K1. apply Z.leb_le in K2. apply Z.leb_le in K3.
  assert (Hb' : expr_eqb (tb t) (tb t') = false).
  { destruct (expr_eqb (tb t) (tb t')) eqn:Eb; [|reflexivity]. apply expr_eqb_true in Eb. rewrite K1, <- Eb in Hne.
    rewrite expr_eqb_refl in Hne. discriminate. }
  pose proof (proj1 (Forall_forall _ _) HW t' Ht') as (C' & B' & _).
  assert (EB' : bv_unsigned (edenot E (tb t')) = tB t') by (rewrite (edenot_wcl E (wenv W) (wbound W) _ C' HE); exact B').
  pose proof (HD t t' Ht Ht' Hb') as DJ.
  unfold estart. rewrite K1, EB'. lia.
Qed.

Section DKRunN.
  Variable W : list word.
  Variable L : list tab.
  Hypothesis HWF : tabs_wf W L.
  Variable P : mem -> Prop.
  Hypothesis P_step : forall m m', P m -> munch (winsT L) m m' -> wmono asegs m m' -> mem_inv asegs m' -> P m'.

  Lemma dk_runN : forall (Q : machine_state -> Prop) R F pc fc m ro RT X kst fuel stops scr nx SSr scs scr' RT',
    rfull R -> rtbl W R RT -> rtbl_okb (wbound W) RT = true ->
    tabs_ok W m L -> P m -> mem_inv asegs m ->
    know_ok asegs (HLib.Eseed R (W ++ X)) m kst ->
    sym_exec asegs fuel true stops scr (SS pc (HLib.srs sr_id RT) [] (kst ++ fknT L) nx) [] = (SSr, scs, scr') ->
    scs_denot asegs m (HLib.Eseed R (W ++ X)) scs ->
    forallb (sym_inside (swinsT L)) (s_log SSr) = true ->
    rtbl_chk (wbound W) (s_regs SSr) RT' = true ->
    (forall R' m', rfull R' -> rtbl W R' RT' -> ftbls W m' (tupd (s_log SSr) (wbound W) L) ->
        P m' -> mem_inv asegs m' -> munch (winsT L) m m' -> wmono asegs m m' ->
        evt asegs Q (MS R' F (Z_to_bv 64 (s_pc SSr)) fc None m' ro)) ->
    evt asegs Q (MS R F (Z_to_bv 64 pc) fc None m ro).
  Proof.
    intros Q R F pc fc m ro RT X kst fuel stops scr nx SSr scs scr' RT' RF HT Hok HTB HP MI HK Hex Hsc Hin Hrt K.
    set (E := HLib.Eseed R (W ++ X)).
    assert (HE : forall n, (32 <= n < wbound W)%N -> ev E n = ev (wenv W) n) by (intros n Hn; apply Eseed_wenv; exact Hn).
    pose proof HWF as [HW HD].
    assert (EB : forall t, In t L -> bv_unsigned (edenot E (tb t)) = tB t).
    { intros t Ht. pose proof (proj1 (Forall_forall _ _) HW t Ht) as (C & B & _).
      rewrite (edenot_wcl E (wenv W) (wbound W) _ C HE). exact B. }
    pose proof (regs_ok_of_rtbl W X R RT HT Hok) as HR.
    assert (HKall : know_ok asegs E m (kst ++ fknT L)).
    { unfold know_ok. apply Forall_app. split; [exact HK|]. unfold fknT. apply Forall_forall. intros ke Hke.
      apply in_flat_map in Hke as (t & Ht & Hke).
      pose proof (proj1 (Forall_forall _ _) HW t Ht) as (C & B & B0 & Blh & Bhi & Cw & Fin).
      pose proof (proj1 (Forall_forall _ _) HTB t Ht) as [FT _].
      exact (proj1 (Forall_forall _ _) (ftbl_kn W (tB t) m (ttbl t) E (tb t) (tlo t) (thi t) FT (EB t Ht) HE Cw
                                          (fin_app_l _ _ _ _ Fin) ltac:(lia) ltac:(lia)) ke Hke). }
    destruct (@SymRun3.run_sound (PropExec.mkFP F fc) asegs fuel stops scr pc (HLib.srs sr_id RT) _ nx SSr scs scr' E m ro R
                Hex HR HKall Hsc) as (R' & HR' & Hlf & Hms).
    rewrite !mkst_MS in Hms.
    eapply blk_then; [exact Hms | exact RF |]. intros RF'.
    assert (NW : num_wins E (swinsT L) = winsT L).
    { unfold num_wins, swinsT, winsT. rewrite map_map. apply map_ext_in. intros t Ht. cbn beta. rewrite (EB t Ht). reflexivity. }
    assert (MU : munch (winsT L) m (mem_denot E m (s_log SSr))).
    { rewrite <- NW. apply munch_sym; [exact Hlf | exact Hin]. }
    pose proof (wmono_mem_denot E m (s_log SSr)) as WM.
    pose proof (msteps_mem_inv asegs _ _ Hms MI) as MI'. cbn [ms_mem] in MI'.
    apply K; [exact RF' | eapply rtbl_of_run; [exact HR' | exact Hrt] | | eapply P_step; eassumption | exact MI' | exact MU | exact WM].
    unfold ftbls, tupd. apply Forall_map. apply Forall_forall. intros t Ht. cbn [fst snd].
    pose proof (proj1 (Forall_forall _ _) HW t Ht) as (C & B & B0 & Blh & Bhi & Cw & Fin).
    pose proof (proj1 (Forall_forall _ _) HTB t Ht) as [FT WK].
    eapply (ftbl_run W (tB t) m (ttbl t) E (s_log SSr) (tb t) (tlo t) (thi t) (tks t));
      [exact FT | exact Hlf | exact (EB t Ht) | exact HE | | exact Fin | lia | lia | exact WK].
    exact (omiss_of_tabs E W L (s_log SSr) t HWF HE Ht Hin).
  Qed.
End DKRunN.

Lemma rw_zero_run : forall m a (j : nat),
  (forall i, (i < j)%nat -> rw_cells asegs m (a + Z.of_nat i) [CB 1 [Z_to_bv 8 0]]) -> 0 <= a ->
  a + Z.of_nat j <= 2 ^ 64 -> rw_cells asegs m a [CB j (repeat (Z_to_bv 8 0) j)].
Proof.
  intros m a j. induction j as [|j IH]; intros HB Ha Hj.
  - split; [split; [cbn; split; [reflexivity | exact I] | split; [lia|]; split; [cbn; lia|]; intros i Hi; cbn in Hi; lia]|].
    split; [lia|]. split; [cbn; lia|]. intros i Hi; cbn in Hi; lia.
  - replace (repeat (Z_to_bv 8 0) (S j)) with (repeat (Z_to_bv 8 0) j ++ [Z_to_bv 8 0])
      by (rewrite <- repeat_cons; reflexivity).
    replace (S j) with (j + 1)%nat by lia.
    apply rw_cells_CB_join; [apply IH; [intros i Hi; apply HB; lia | lia | lia] | apply HB; lia].
Qed.

Lemma addr_of_zents : forall W B m tbl k0 A n, ftbl W B m tbl ->
  forallb (fun j => fent_in (k0 + Z.of_nat j, 1%nat, ELit 0) tbl) (seq 0 (Z.to_nat (n / 8))) = true ->
  B + k0 = sh A -> 0 <= A -> A mod 8 = 0 -> 0 <= n -> n mod 8 = 0 -> sh A + n / 8 <= 2 ^ 64 ->
  addressable m A n.
Proof.
  intros W B m tbl k0 A n H Hb HA H0 H8 Hn Hn8 Hhi.
  assert (RW : rw_cells asegs m (sh A) [CB (Z.to_nat (n / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (n / 8)))]).
  { apply rw_zero_run; [| unfold sh, ASHADOW_BASE; apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia] | rewrite Z2Nat.id by (apply Z.div_pos; lia); lia].
    intros i Hi. assert (Hj : In i (seq 0 (Z.to_nat (n / 8)))) by (apply in_seq; lia).
    pose proof (proj1 (forallb_forall _ _) Hb i Hj) as K. cbv beta in K.
    pose proof (ftbl_In W B m tbl _ _ _ H (fent_in_In _ _ K)) as R.
    replace (word_to_le_bytes 1 (edenot (wenv W) (ELit 0))) with [Z_to_bv 8 0] in R by (vm_compute; reflexivity).
    rewrite <- HA. replace (B + k0 + Z.of_nat i) with (B + (k0 + Z.of_nat i)) by lia. exact R. }
  split; [exact Hn|]. split; [exact H0|]. split; [exact H8|].
  unfold shadow_of. rewrite (proj2 (Z.eqb_eq (n mod 8) 0) Hn8), app_nil_r.
  destruct RW as [[_ BA] WR]. cbn [cells_bytes cbytes] in BA. rewrite app_nil_r in BA.
  cbn [cells_size csize] in WR. rewrite Nat.add_0_r in WR.
  split; [exact BA|]. rewrite repeat_length. exact WR.
Qed.

Lemma u64arr_of_ents : forall W B m tbl k e0 e1 e2, ftbl W B m tbl ->
  fent_in (k, 8%nat, e0) tbl = true -> fent_in (k + 8, 8%nat, e1) tbl = true -> fent_in (k + 16, 8%nat, e2) tbl = true ->
  u64arr asegs m (B + k) [edenot (wenv W) e0; edenot (wenv W) e1; edenot (wenv W) e2].
Proof.
  intros W B m tbl k e0 e1 e2 H I0 I1 I2.
  pose proof (ftbl_In W B m tbl _ _ _ H (fent_in_In _ _ I0)) as R0.
  pose proof (ftbl_In W B m tbl _ _ _ H (fent_in_In _ _ I1)) as R1.
  pose proof (ftbl_In W B m tbl _ _ _ H (fent_in_In _ _ I2)) as R2.
  replace (B + (k + 8)) with (B + k + Z.of_nat 8) in R1 by lia.
  pose proof (rw_cells_CB_join asegs m (B + k) 8 8 _ _ R0 R1) as J1.
  replace (B + (k + 16)) with (B + k + Z.of_nat (8 + 8)) in R2 by lia.
  pose proof (rw_cells_CB_join asegs m (B + k) (8 + 8) 8 _ _ J1 R2) as J2.
  destruct J2 as [[_ BA] WR]. cbn [cells_bytes cbytes] in BA. rewrite app_nil_r in BA.
  split.
  - cbn [u64s]. unfold le8. rewrite app_nil_r, app_assoc. exact BA.
  - cbn [cells_size csize] in WR. cbn [length]. exact WR.
Qed.

Lemma rw_C2_CB : forall m a (w : word) j, rw_cells asegs m a [CB 2 (word_to_le_bytes 2 w)] ->
  rw_cells asegs m (a + 2) [CB 22 j] -> rw_cells asegs m a [C2 w; CB 22 j].
Proof.
  intros m a w j R1 R2.
  pose proof (rw_cells_CB_join asegs m a 2 22 _ _ R1 R2) as J.
  pose proof (rw_CB_len m (a + 2) 22 j R2) as L.
  destruct J as [[_ BA] WR]. split; [split|].
  - cbn. split; [exact I | split; [exact L | exact I]].
  - cbn [cells_bytes cbytes] in BA |- *. rewrite app_nil_r in BA. unfold le2. unfold word_to_le_bytes in BA.
    rewrite app_nil_r. exact BA.
  - cbn [cells_size csize] in WR |- *. exact WR.
Qed.

Lemma sub_fp_of : forall W W', Forall (fun iv => exists iv', In iv' W' /\ fst iv' <= fst iv /\ snd iv <= snd iv') W -> sub_fp W W'.
Proof.
  intros W W' H x Hx. induction W as [|[lo hi] W IH]; cbn [outside]; [exact I|].
  apply Forall_cons_iff in H as [(iv' & Hin & H1 & H2) HW]. split; [| exact (IH HW)].
  cbn [fst snd] in H1, H2. intros Hr.
  assert (K : forall W'' , In iv' W'' -> outside W'' x -> ~ (fst iv' <= x < snd iv')).
  { clear. intros W''. induction W'' as [|[l h] W'' IH]; intros Hi Ho; [destruct Hi|].
    cbn [outside] in Ho. destruct Ho as [Ho1 Ho2]. destruct Hi as [<-|Hi]; [exact Ho1 | exact (IH Hi Ho2)]. }
  apply (K W' Hin Hx). lia.
Qed.

Definition keptk (RT : list (reg * expr)) : list (reg * expr) :=
  List.filter (fun re => existsb (fun r => bv_eqb r (fst re)) KEPT) RT.
Lemma rtbl_keptk : forall W R RT, rtbl W R RT -> rtbl W R (keptk RT).
Proof. intros W R RT H. unfold rtbl, keptk in *. apply Forall_forall. intros x Hx. apply filter_In in Hx as [Hx _].
  exact (proj1 (Forall_forall _ _) H x Hx). Qed.
Lemma rsub_keptk : forall RT, rsub KEPT (keptk RT) = true.
Proof. intros RT. unfold rsub, keptk. apply forallb_forall. intros x Hx. apply filter_In in Hx as [_ Hx]. exact Hx. Qed.

Lemma wenv_ext : forall W X n, (32 <= n < wbound W)%N -> ev (wenv (W ++ X)) n = ev (wenv W) n.
Proof. intros W X n Hn. unfold wenv. apply Eseed_wenv. exact Hn. Qed.

Lemma ftbl_wext : forall W X B m tbl, fwcl (wbound W) tbl = true -> ftbl W B m tbl -> ftbl (W ++ X) B m tbl.
Proof.
  intros W X B m tbl C H. unfold ftbl in *. apply Forall_forall. intros [[k w] e] Hi.
  pose proof (proj1 (Forall_forall _ _) H (k, w, e) Hi) as R. cbn beta iota in R |- *.
  pose proof (proj1 (forallb_forall _ _) C (k, w, e) Hi) as Ce. cbn beta iota in Ce.
  rewrite (edenot_wcl (wenv (W ++ X)) (wenv W) (wbound W) e Ce (wenv_ext W X)). exact R.
Qed.

Lemma rtbl_wext : forall W X R RT, forallb (fun re => wcl (wbound W) (snd re)) RT = true -> rtbl W R RT -> rtbl (W ++ X) R RT.
Proof.
  intros W X R RT C H. unfold rtbl in *. apply Forall_forall. intros [r e] Hi.
  pose proof (proj1 (Forall_forall _ _) H (r, e) Hi) as K. cbn [fst snd] in K |- *.
  pose proof (proj1 (forallb_forall _ _) C (r, e) Hi) as Ce. cbn [snd] in Ce.
  rewrite (edenot_wcl (wenv (W ++ X)) (wenv W) (wbound W) e Ce (wenv_ext W X)). exact K.
Qed.

Definition re_eqb (x y : reg * expr) : bool := (bv_eqb (fst x) (fst y) && expr_eqb (snd x) (snd y))%bool.
Lemma rtbl_sub : forall W R RT RT', rtbl W R RT -> forallb (fun x => existsb (re_eqb x) RT) RT' = true -> rtbl W R RT'.
Proof.
  intros W R RT RT' H Hb. unfold rtbl in *. apply Forall_forall. intros [r e] Hi.
  pose proof (proj1 (forallb_forall _ _) Hb (r, e) Hi) as K. apply existsb_exists in K as ([r' e'] & Hi' & Eq).
  unfold re_eqb in Eq. cbn [fst snd] in Eq. apply andb_true_iff in Eq as [E1 E2].
  unfold bv_eqb in E1. apply Z.eqb_eq in E1. apply bv_eq in E1. apply expr_eqb_eq in E2. subst.
  exact (proj1 (Forall_forall _ _) H _ Hi').
Qed.

Lemma ftbl_of_C8 : forall W B m k e, rw_cells asegs m (B + k) [C8 (edenot (wenv W) e)] -> ftbl W B m [(k, 8%nat, e)].
Proof.
  intros W B m k e [[_ BA] WR]. constructor; [| constructor]. cbn beta iota.
  split; [split|].
  - cbn. split; [try reflexivity; unfold word_to_le_bytes; apply length_Z_to_le_bytes | exact I].
  - cbn [cells_bytes cbytes] in BA |- *. exact BA.
  - cbn [cells_size csize] in WR |- *. exact WR.
Qed.

Lemma getr_mkR_keptR : forall (R1 : bvmap 5 word) x1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
  x1 = PropExec.getr R1 1 -> forall r, In r KEPT ->
  PropExec.getr (mkR x1 (PropExec.getr R1 2) (PropExec.getr R1 3) (PropExec.getr R1 4) y5 y6 y7
                     (PropExec.getr R1 8) (PropExec.getr R1 9) y10 y11 y12 y13 y14 y15 y16 y17
                     (PropExec.getr R1 18) (PropExec.getr R1 19) (PropExec.getr R1 20) (PropExec.getr R1 21)
                     (PropExec.getr R1 22) (PropExec.getr R1 23) (PropExec.getr R1 24) (PropExec.getr R1 25)
                     (PropExec.getr R1 26) (PropExec.getr R1 27) y28 y29 y30 y31) r = PropExec.getr R1 r.
Proof.
  intros R1 x1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 E r Hr. cbn [In KEPT] in Hr.
  destruct Hr as [<-|Hr]; [exact E|].
  repeat (destruct Hr as [<-|Hr]; [reflexivity|]). destruct Hr.
Qed.

Lemma ftbl_sub : forall W B m t t', ftbl W B m t -> forallb (fun x => fent_in x t) t' = true -> ftbl W B m t'.
Proof.
  intros W B m t t' H Hb. unfold ftbl in *. apply Forall_forall. intros x Hx.
  pose proof (proj1 (forallb_forall _ _) Hb x Hx) as K. apply fent_in_In in K.
  exact (proj1 (Forall_forall _ _) H x K).
Qed.

Ltac inkept := cbn [In KEPT]; repeat (first [left; reflexivity | right]).
Ltac sfp_in iv := exists iv; split; [repeat (first [left; reflexivity | right]) | cbn [fst snd]; clear; lia].
