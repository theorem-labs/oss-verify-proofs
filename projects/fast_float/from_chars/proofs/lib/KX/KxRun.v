(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec FxLin FxCore FxSubst FxSound FxMem FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxDrv FxEnt FxRgs.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Mem Cells Exec Frame Arr Step Image RegsEquiv MState.
From OSSVerify.Proofs.fast_float.from_chars.lib.KX Require Import KxBridge.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section Run.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition kms (ms : machine_state) : machine_state :=
  MS (mkR_of (ms_regs ms)) (ms_fregs ms) (ms_pc_val ms) (ms_fcsr ms) (ms_resv ms) (ms_mem ms) (seg_rom segs).

#[using="Type"] Lemma kms_eqv : forall ms, ms_svc_pending ms = None -> ms_eqv (kms ms) (with_rom ms (seg_rom segs)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ms Hs. unfold kms, MS, with_rom. refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))); cbn.
  - apply regs_eqv_sym, regs_eqv_mkR.
  - apply fregs_eqv_refl.
  - reflexivity.
  - rewrite Hs. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma kit_run : forall (POST : machine_state -> Prop) ms,
  ms_svc_pending ms = None -> evt segs POST (kms ms) ->
  exists ms1 ms2, isteps segs ms ms1 /\ ms_eqv ms1 (with_rom ms2 (ms_rom ms)) /\ POST ms2.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros POST ms Hs H. apply (evt_at_rom segs POST ms (seg_rom segs)).
  eapply evt_eqv; [exact H | apply kms_eqv; exact Hs].
Qed.

#[using="Type"] Lemma ret_pc_even_w : forall ra : word, bv_unsigned ra mod 2 = 0 -> ret_pc ra = ra.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ra H. pose proof (bv_unsigned_in_range _ ra) as Hr. unfold bv_modulus in Hr.
  rewrite <- (Z_to_bv_bv_unsigned ra). apply MState.ret_pc_even; [|exact H].
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Hr. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma sden_of_kit : forall (Q : sst) E' ms1 R F pc fc m' ro rom,
  state_wf Q = true -> s_resv Q = RNone ->
  ms_eqv ms1 (with_rom (MS R F pc fc None m' ro) rom) ->
  pc = Z_to_bv 64 (s_pc Q) -> frm_zero fc ->
  regs_ok E' (s_regs Q) R ->
  Forall (rg_ok segs E' m') (s_rgs Q) -> rgs_disj E' (s_rgs Q) -> Forall (fact_ok E') (s_facts Q) ->
  sden segs E' Q ms1.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros Q E' ms1 R F pc fc m' ro rom Hw Hrv Heq Hpc Hfrm HR HG HD HF.
  apply sden0_sden; [exact Hw|].
  destruct Heq as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
  cbn [with_rom MS ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in E1, E2, E3, E4, E5, E6, E7, E8.
  unfold sden0. rewrite E3, E4, E5, E6, E7.
  refine (conj Hpc (conj eq_refl (conj _ (conj _ (conj HG (conj HD (conj HF Hfrm))))))).
  - rewrite Hrv. reflexivity.
  - intros r. rewrite E1. exact (HR r).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma regs_ok_of_cases : forall E T R,
  (forall n, (n < 32)%nat -> getr R (Z_to_bv 5 (Z.of_nat n)) = lden E (rget T (rkey (Z_to_bv 5 (Z.of_nat n))))) ->
  regs_ok E T R.
Proof. LiaFast.lf_pins LiaFast.u0. intros E T R H r. destruct (reg_of_nat r) as (n & -> & Hn). apply H. exact Hn. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma map_shiftr_seq : forall n z s,
  List.map (fun j => Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat j))) (seq s n) = Z_to_le_bytes n (Z.shiftr z (8 * Z.of_nat s)).
Proof. LiaFast.lf_pins LiaFast.u0.
  induction n as [|n IH]; intros z s; [reflexivity|].
  cbn [seq List.map Z_to_le_bytes]. f_equal. rewrite IH. f_equal. rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed.

#[using="Type"] Lemma map_bden_bvl : forall E l n,
  List.map (bden E) (List.map (fun j => BV l (Z.of_nat j)) (seq 0 n)) = Z_to_le_bytes n (bv_unsigned (lden E l)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E l n. rewrite List.map_map. cbn [bden].
  rewrite (map_shiftr_seq n (bv_unsigned (lden E l)) 0). rewrite Z.mul_0_r, Z.shiftr_0_r. reflexivity.
Qed.

#[using="Type"] Lemma map_bden_bv8 : forall E l, List.map (bden E) (List.map (fun j => BV l (Z.of_nat j)) (seq 0 8)) = le8 (lden E l).
Proof. LiaFast.lf_pins LiaFast.u0. intros E l. rewrite map_bden_bvl. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma track_bytes_at : forall E m R o bvs,
  rg_ok segs E m (track R o bvs) -> 0 <= o -> (0 < length bvs)%nat ->
  bytes_at segs m (bv_unsigned (lden E (rg_base R)) + o) (List.map (bden E) bvs).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m R o bvs HR Ho Hl. pose proof (u_lden_range E (rg_base R)) as U.
  destruct HR as (H1 & H2 & _ & H4). unfold track in H1, H2, H4. cbn [rg_base rg_size rg_kind rg_cont] in H1, H2, H4.
  rewrite rsz_RG_eq in H1, H2. 
  assert (Hc : forall j v, nth_error bvs j = Some v ->
             o + Z.of_nat j < rsz E R /\ rd1 segs m (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + (o + Z.of_nat j))) = Some (bden E v)).
  { intros j v Hj. pose proof (nth_error_Some bvs j) as X. rewrite Hj in X.
    assert (Hjl : (j < length bvs)%nat) by (apply X; discriminate).
    assert (Ht : tget (okey (o + Z.of_nat j)) (put_bytes (rg_cont R) o bvs) = Some v).
    { rewrite put_bytes_spec by exact Ho. rewrite okey_pos by lia.
      replace (Z.leb o (o + Z.of_nat j) && Z.ltb (o + Z.of_nat j) (o + Z.of_nat (length bvs)))%bool with true
        by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
      replace (Z.to_nat (o + Z.of_nat j - o)) with j by lia. exact Hj. }
    destruct (H4 _ _ Ht) as (Hlt & Hrd). rewrite okey_pos in Hlt, Hrd by lia. rewrite rsz_RG_eq in Hlt. split; [lia | exact Hrd]. }
  destruct (nth_error bvs (length bvs - 1)) as [vl|] eqn:Hlast; [|apply nth_error_None in Hlast; lia].
  destruct (Hc _ _ Hlast) as (Hlt & _).
  split; [lia|]. split; [rewrite List.length_map; unfold two64 in *; lia|].
  intros i Hi. rewrite List.length_map in Hi. destruct (nth_error bvs i) as [v|] eqn:Hv; [|apply nth_error_None in Hv; lia].
  rewrite nth_error_map, Hv. cbn [option_map]. destruct (Hc i v Hv) as (_ & Hr). rewrite <- rd1_mrd. unfold wa. rewrite Z.add_assoc in Hr. exact Hr.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma track_of_bytes_at : forall E m R o bvs,
  rg_ok segs E m R -> 0 <= o -> o + Z.of_nat (length bvs) <= rsz E R ->
  bytes_at segs m (bv_unsigned (lden E (rg_base R)) + o) (List.map (bden E) bvs) ->
  rg_ok segs E m (track R o bvs).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m R o bvs HR Ho Hl (B1 & B2 & B). apply rg_track; [exact HR | exact Ho | exact Hl|].
  intros j v Hj. pose proof (nth_error_Some bvs j) as X. rewrite Hj in X.
  assert (Hjl : (j < length bvs)%nat) by (apply X; discriminate).
  pose proof (B j ltac:(rewrite List.length_map; lia)) as Y. rewrite nth_error_map, Hj in Y. cbn [option_map] in Y.
  rewrite rd1_mrd. unfold wa in Y. rewrite Z.add_assoc. exact Y.
Qed.

(* [comment removed for export] *)
Definition tracked_b (c : tree bval) (o : Z) (bvs : list bval) : bool :=
  forallb (fun j => match tget (okey (o + Z.of_nat j)) c, nth_error bvs j with
                    | Some v, Some w => bval_eqb v w | _, _ => false end) (seq 0 (length bvs)).

#[using="Type"] Lemma tracked_b_spec : forall c o bvs, tracked_b c o bvs = true ->
  forall j v, nth_error bvs j = Some v -> tget (okey (o + Z.of_nat j)) c = Some v.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros c o bvs H j v Hj. unfold tracked_b in H. rewrite forallb_forall in H.
  pose proof (nth_error_Some bvs j) as X. rewrite Hj in X. assert (Hjl : (j < length bvs)%nat) by (apply X; discriminate).
  pose proof (H j ltac:(apply in_seq; lia)) as Y. rewrite Hj in Y.
  destruct (tget (okey (o + Z.of_nat j)) c) as [w|]; [|discriminate]. apply bval_eqb_eq in Y. subst. reflexivity.
Qed.

#[using="Type"] Lemma cont_bytes_at : forall E m R o bvs,
  rg_ok segs E m R -> 0 <= o -> (0 < length bvs)%nat -> tracked_b (rg_cont R) o bvs = true ->
  bytes_at segs m (bv_unsigned (lden E (rg_base R)) + o) (List.map (bden E) bvs).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m R o bvs HR Ho Hl Hb. pose proof (u_lden_range E (rg_base R)) as U.
  destruct HR as (H1 & H2 & _ & H4).
  assert (Hc : forall j v, nth_error bvs j = Some v ->
             o + Z.of_nat j < rsz E R /\ rd1 segs m (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + (o + Z.of_nat j))) = Some (bden E v)).
  { intros j v Hj. pose proof (tracked_b_spec _ _ _ Hb j v Hj) as Ht.
    destruct (H4 _ _ Ht) as (Hlt & Hrd). rewrite okey_pos in Hlt, Hrd by lia. split; [lia | exact Hrd]. }
  destruct (nth_error bvs (length bvs - 1)) as [vl|] eqn:Hlast; [|apply nth_error_None in Hlast; lia].
  destruct (Hc _ _ Hlast) as (Hlt & _).
  split; [lia|]. split; [rewrite List.length_map; unfold two64 in *; lia|].
  intros i Hi. rewrite List.length_map in Hi. destruct (nth_error bvs i) as [v|] eqn:Hv; [|apply nth_error_None in Hv; lia].
  rewrite nth_error_map, Hv. cbn [option_map]. destruct (Hc i v Hv) as (_ & Hr). rewrite <- rd1_mrd. unfold wa. rewrite Z.add_assoc in Hr. exact Hr.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma bytes_at_sub : forall m A bs k n,
  bytes_at segs m A bs -> (k + n <= length bs)%nat ->
  bytes_at segs m (A + Z.of_nat k) (firstn n (skipn k bs)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m A bs k n (B1 & B2 & B) Hkn. unfold bytes_at. rewrite length_firstn, length_skipn.
  split; [lia|]. split; [lia|]. intros i Hi.
  rewrite nth_error_firstn. destruct (Nat.ltb_spec i n); [|lia]. rewrite nth_error_skipn.
  rewrite <- Z.add_assoc, <- Nat2Z.inj_add. rewrite Nat.add_comm. apply B. lia.
Qed.

#[using="Type"] Lemma cont_le8 : forall E m R o l,
  rg_ok segs E m R -> 0 <= o -> tracked_b (rg_cont R) o (List.map (fun j => BV l (Z.of_nat j)) (seq 0 8)) = true ->
  bytes_at segs m (bv_unsigned (lden E (rg_base R)) + o) (le8 (lden E l)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m R o l HR Ho Hb. rewrite <- map_bden_bv8. apply (cont_bytes_at E m R o _ HR Ho); [cbn; lia | exact Hb].
Qed.

(* [comment removed for export] *)
Fixpoint bytes_eqb (a b : list byte) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => (Z.eqb (bv_unsigned x) (bv_unsigned y) && bytes_eqb a' b')%bool
  | _, _ => false
  end.
#[using="Type"] Lemma bytes_eqb_eq : forall a b, bytes_eqb a b = true -> a = b.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction a as [|x a IH]; intros [|y b] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. f_equal; [apply bv_eq; exact H1 | exact (IH b H2)].
Qed.

#[using="Type"] Lemma ro_cells_of_bytes : forall m A bs cs,
  bytes_at segs m A bs -> bytes_eqb bs (cells_bytes cs) = true -> cells_wf cs -> ro_cells segs m A cs.
Proof. LiaFast.lf_pins LiaFast.u0. intros m A bs cs H Hb Hw. apply bytes_eqb_eq in Hb. subst bs. split; assumption. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rz_bytes : forall E m R i, rg_ok segs E m R -> rg_kind R = RZ -> rg_cont R = TEmpty -> 0 <= i < rsz E R ->
  mrd segs m (wa (bv_unsigned (lden E (rg_base R)) + i)) = Some (Z_to_bv 8 0) /\
  wview segs m (wa (bv_unsigned (lden E (rg_base R)) + i)) <> None.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m R i HR Hk Hc Hi. split; [exact (zero_bytes_of_rz segs E m R i HR Hk Hc Hi)|].
  exact (proj2 (rdwr_of_rg segs E m R i HR ltac:(right; left; exact Hk) Hi)).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rg_ok_munch : forall E m m' R W,
  rg_ok segs E m R -> munch W m m' ->
  (forall i, 0 <= i < rsz E R -> outside W (bv_unsigned (lden E (rg_base R)) + i)) ->
  rg_ok segs E m' R.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m m' R W HR Hm Ho. apply (rg_ok_frame segs E m m' R HR). intros i Hi.
  pose proof (rg_flat segs E m R HR) as (F1 & F2). pose proof (u_lden_range E (rg_base R)) as U.
  apply Hm. rewrite u_Z_to_bv. rewrite Z.mod_small by (unfold two64 in *; lia). exact (Ho i Hi).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rg_ok_unwritten : forall E m m' rgs W (ws : list nat) i R,
  rgs_disj E rgs -> nth_error rgs i = Some R -> ~ In i ws -> munch W m m' ->
  (forall x, (forall j Rj, In j ws -> nth_error rgs j = Some Rj ->
                ~ (bv_unsigned (lden E (rg_base Rj)) <= x < bv_unsigned (lden E (rg_base Rj)) + rsz E Rj)) -> outside W x) ->
  rg_ok segs E m R -> rg_ok segs E m' R.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m m' rgs W ws i R HD Hi Hni Hm HW HR. apply (rg_ok_munch E m m' R W HR Hm). intros k Hk.
  apply HW. intros j Rj Hj HRj Hin. assert (Hij : i <> j) by (intros ->; exact (Hni Hj)).
  pose proof (rgs_disj_nth E rgs i j R Rj HD Hij Hi HRj) as Hd. unfold rg_disj in Hd. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rw_mix : forall E m m' R W lo hi,
  rg_ok segs E m R -> rg_kind R = RW -> rg_cont R = TEmpty -> munch W m m' -> stk segs m' lo hi ->
  (forall i, 0 <= i < rsz E R -> lo <= bv_unsigned (lden E (rg_base R)) + i < hi \/ outside W (bv_unsigned (lden E (rg_base R)) + i)) ->
  rg_ok segs E m' R.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m m' R W lo hi HR Hk Hc Hm (S1 & S2 & S) Hw. pose proof (rg_flat segs E m R HR) as (F1 & F2).
  pose proof (u_lden_range E (rg_base R)) as U.
  apply (rg_ok_of_rdwr segs E m' R (bv_unsigned (lden E (rg_base R))) (rsz E R)); try assumption; try reflexivity.
  intros i Hi. destruct (Hw i Hi) as [Hin|Hout].
  - destruct (S _ Hin) as (Sw & b & Sr). split; [rewrite Sr; discriminate | exact Sw].
  - pose proof (rdwr_of_rg segs E m R i HR ltac:(left; exact Hk) Hi) as (Hr & Hw').
    assert (Hx : m' (wa (bv_unsigned (lden E (rg_base R)) + i)) = m (wa (bv_unsigned (lden E (rg_base R)) + i))).
    { apply Hm. unfold wa. rewrite u_Z_to_bv, Z.mod_small by (unfold two64 in *; lia). exact Hout. }
    unfold mrd, wview in *. rewrite Hx. split; assumption.
Qed.

(* [comment removed for export] *)
Definition upds (E : valu) (l : list (positive * word)) : valu :=
  fun x => match List.find (fun p => Pos.eqb (fst p) x) l with Some p => snd p | None => E x end.
#[using="Type"] Lemma upds_agree : forall n E l, Forall (fun p => (n <= fst p)%positive) l -> agree n E (upds E l).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros n E l Hl x Hx. unfold upds. destruct (List.find (fun p => Pos.eqb (fst p) x) l) as [p|] eqn:Hf; [|reflexivity].
  apply find_some in Hf as (Hin & Heq). apply Pos.eqb_eq in Heq. rewrite Forall_forall in Hl. pose proof (Hl p Hin). lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rg_ok_track1 : forall E m R A v,
  rg_kind R = RZ -> rg_cont R = TEmpty -> rsz E R = 1 -> bv_unsigned (lden E (rg_base R)) = A -> A + 1 <= two64 ->
  mrd segs m (wa A) = Some (bden E v) -> wview segs m (wa A) <> None ->
  rg_ok segs E m (track R 0 [v]).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m R A v Hk Hc Hs Hb HA Hr Hw. pose proof (u_lden_range E (rg_base R)) as U.
  unfold rg_ok, track. cbn [rg_base rg_size rg_kind rg_cont]. rewrite rsz_RG_eq, Hs, Hb, Hk, Hc.
  split; [lia|]. split; [lia|]. split.
  - intros i Hi. assert (i = 0) as -> by lia. rewrite Z.add_0_r. rewrite rd1_mrd. unfold wa in Hr, Hw.
    split; [split; [rewrite Hr; discriminate | exact Hw]|]. intros Hn. cbn in Hn. discriminate.
  - intros p w Hp. rewrite put_bytes_spec in Hp by lia. cbn [length] in Hp.
    destruct (Z.leb 0 (Zpos p - 1) && Z.ltb (Zpos p - 1) (0 + Z.of_nat 1))%bool eqn:E1; [|rewrite tget_empty in Hp; discriminate].
    apply andb_prop in E1 as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. assert (Zpos p - 1 = 0) as Hp0 by lia.
    rewrite Hp0 in Hp |- *. cbn in Hp. injection Hp as <-. split; [lia|]. rewrite Z.add_0_r, rd1_mrd. exact Hr.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rgs_disj_shape : forall E rgs rgs', shape rgs' = shape rgs -> rgs_disj E rgs -> rgs_disj E rgs'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E rgs. induction rgs as [|R rs IH]; intros [|R' rs'] Hs H; cbn [shape List.map] in Hs; try discriminate; [exact I|].
  injection Hs as Hb Hz Hrs. destruct H as (HF & HD). split; [|exact (IH rs' Hrs HD)].
  assert (Hm : forall S, In S rs' -> exists S0, In S0 rs /\ rg_base S = rg_base S0 /\ rg_size S = rg_size S0).
  { clear -Hrs. revert rs Hrs. induction rs' as [|S rs2 IH2]; intros [|S0 rs0] Hrs; cbn [List.map] in Hrs; try discriminate; intros X Hx; [destruct Hx|].
    injection Hrs as Hb0 Hz0 Hr0. destruct Hx as [<-|Hx]; [exists S0; split; [left; reflexivity | split; assumption]|].
    destruct (IH2 rs0 Hr0 X Hx) as (S1 & HS1 & E1 & E2). exists S1. split; [right; exact HS1 | split; assumption]. }
  rewrite Forall_forall in HF |- *. intros S HS. destruct (Hm S HS) as (S0 & HS0 & E1 & E2).
  pose proof (HF S0 HS0) as X. unfold rg_disj, rsz in *. rewrite E1, E2, Hb, Hz. exact X.
Qed.

End Run.
