(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.FX Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound FxValSound FxStepSound FxStepMain FxRun FxRn
  FxLazy FxSys FxDrive FxCellFrame FxDrive3 FxDrive3N FxDrive3S FxDrive3C FxDrive3D FxDrive3H FxDrive3T FxDrive3O FxDrive3W.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition page_small (len : Z) (pn : int) (p : page) : Prop :=
  to_Z pn < 2 ^ 50
  /\ forall ci, iget ci (pg_cells p) <> None -> to_Z ci < 512 /\ to_Z pn * 4096 + to_Z ci * 8 + 8 <= len.

Definition region_small (rg : region) : Prop :=
  to_Z (rg_len rg) mod 8 = 0
  /\ forall pn p, iget pn (rg_pages rg) = Some p -> page_small (to_Z (rg_len rg)) pn p.

Definition cells_inv (M : itrie region) : Prop :=
  forall t rg, iget t M = Some rg -> region_small rg.

(* [comment removed for export] *)
Definition region_small_b (rg : region) : bool :=
  ((rg_len rg land 7) =? 0)%uint63 && pages_valid rg.
Definition cells_inv_b (M : itrie region) : bool := iall (fun _ rg => region_small_b rg) M.

Lemma region_small_b_sound rg : region_small_b rg = true -> region_small rg.
Proof.
  unfold region_small_b. intros H. apply andb_true_iff in H as [Hal Hpv]. split.
  - apply Uint63.eqb_spec in Hal. apply (f_equal to_Z) in Hal.
    rewrite (i63_land_ones (rg_len rg) 7%uint63 3 eq_refl ltac:(lia)) in Hal. exact Hal.
  - intros pn p Hp. unfold pages_valid in Hpv.
    pose proof (proj1 (iall_spec _ _) Hpv pn p Hp) as Hb. apply andb_true_iff in Hb as [Hb1 Hb2].
    apply ltb_spec in Hb1. change (to_Z 1125899906842624) with (2 ^ 50) in Hb1. split; [exact Hb1|].
    intros ci Hci. destruct (iget ci (pg_cells p)) as [c|] eqn:Ec; [|congruence].
    pose proof (proj1 (iall_spec _ _) Hb2 ci c Ec) as Hb3. apply andb_true_iff in Hb3 as [Hb3 Hb4].
    apply ltb_spec in Hb3. apply leb_spec in Hb4.
    change (to_Z 512) with 512 in Hb3. pose proof (i63_range ci) as Hci0. pose proof (i63_range pn) as Hpn0.
    split; [lia|].
    assert (E1 : to_Z (pn << 12) = to_Z pn * 4096).
    { rewrite lsl_spec. change (2 ^ to_Z 12) with 4096. apply Z.mod_small. change wB with (2 ^ 63). lia. }
    assert (E2 : to_Z (ci << 3) = to_Z ci * 8).
    { rewrite lsl_spec. change (2 ^ to_Z 3) with 8. apply Z.mod_small. change wB with (2 ^ 63). lia. }
    pose proof (i63_range (rg_len rg)) as Hlr0.
    rewrite !add_spec, E1, E2 in Hb4. change (to_Z 8) with 8 in Hb4. change wB with (2 ^ 63) in Hb4.
    rewrite (Z.mod_small (to_Z pn * 4096 + to_Z ci * 8)) in Hb4 by lia.
    rewrite Z.mod_small in Hb4 by lia. exact Hb4.
Qed.

Theorem cells_inv_b_sound M : cells_inv_b M = true -> cells_inv M.
Proof.
  unfold cells_inv_b. intros H t rg Hg.
  exact (region_small_b_sound rg (proj1 (iall_spec _ _) H t rg Hg)).
Qed.

(* [comment removed for export] *)
Theorem cells_inv_spec M t rg pn p ci :
  cells_inv M ->
  iget t M = Some rg -> iget pn (rg_pages rg) = Some p -> iget ci (pg_cells p) <> None ->
  to_Z pn < 2 ^ 50 /\ to_Z ci < 512 /\ to_Z pn * 4096 + to_Z ci * 8 + 8 <= to_Z (rg_len rg).
Proof.
  intros HM Hg Hp Hc. destruct (HM t rg Hg) as [_ Hpg]. destruct (Hpg pn p Hp) as [Hpn Hcs].
  destruct (Hcs ci Hc) as [H1 H2]. split; [exact Hpn|]. split; [exact H1 | exact H2].
Qed.

Theorem cells_inv_spec_lo segs IM rho M m t rg pn p ci :
  cells_inv M -> mem_ok segs IM rho M m ->
  iget t M = Some rg -> iget pn (rg_pages rg) = Some p -> iget ci (pg_cells p) <> None ->
  to_Z pn < 2 ^ 50 /\ to_Z ci < 512
  /\ to_Z (rg_lo rg) <= to_Z pn * 4096 /\ to_Z pn * 4096 + to_Z ci * 8 + 8 <= to_Z (rg_len rg).
Proof.
  intros HM Hmok Hg Hp Hc. destruct (cells_inv_spec M t rg pn p ci HM Hg Hp Hc) as (Hpn & Hci & Hend).
  split; [exact Hpn|]. split; [exact Hci|]. split; [|exact Hend].
  destruct (proj1 Hmok t rg Hg) as [_ Hpages].
  assert (Hpa : page_at IM rg t pn = Some p) by (unfold page_at; rewrite Hp; reflexivity).
  destruct (Hpages pn p Hpn Hpa) as (_ & Hlo & _). exact Hlo.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cells_inv_iset M t rg : cells_inv M -> region_small rg -> cells_inv (iset t rg M).
Proof.
  intros HM Hrg t' rg' Hg. rewrite iget_iset in Hg.
  destruct (t' =? t)%uint63; [injection Hg as <-; exact Hrg | exact (HM t' rg' Hg)].
Qed.

Lemma cells_inv_iremove M t : cells_inv M -> cells_inv (iremove t M).
Proof.
  intros HM t' rg' Hg. rewrite iget_iremove in Hg.
  destruct (t' =? t)%uint63; [discriminate | exact (HM t' rg' Hg)].
Qed.

(* [comment removed for export] *)
Lemma region_small_empty lo len al dflt clo chi k :
  to_Z len mod 8 = 0 -> region_small (RGK lo len al dflt iempty clo chi k).
Proof.
  intros Hl. split; [exact Hl|]. intros pn p Hp. cbn [rg_pages] in Hp. rewrite iget_iempty in Hp. discriminate.
Qed.

(* [comment removed for export] *)
Lemma region_small_rebound rg clo chi : region_small rg -> region_small (rebound rg clo chi).
Proof. intros H. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Exec.
Variable IM : fimage.
Variable code : itrie finstr.

Lemma fm_store_cells_inv M a sz v M' :
  cells_inv M -> fm_store IM M a sz v = Some M' -> cells_inv M'.
Proof.
  destruct a as [t [top off]]. intros HM Hst.
  destruct (fm_store_inv IM _ _ _ _ _ _ _ Hst) as (rg & p & Hrg & Hp & _ & C1 & C2 & C3 & ->).
  destruct (checks_inv top off sz rg C1 C2 C3) as (_ & Hcell & Hoff & Hlen & Hlo & Hin).
  destruct (HM t rg Hrg) as [Hal Hpages].
  apply cells_inv_iset; [exact HM|].
  pose proof (i63_range off) as Hoff0. pose proof (msz_nat_pos sz) as Hn.
  set (pn := (off >> 12)%uint63) in *. set (ci := ((off land 4095) >> 3)%uint63).
  assert (Epn : to_Z pn = to_Z off / 4096) by (unfold pn; rewrite lsr_spec; reflexivity).
  assert (Eci : to_Z ci = (to_Z off mod 4096) / 8).
  { unfold ci. rewrite lsr_spec, (i63_land_ones off 4095%uint63 12 eq_refl ltac:(lia)). reflexivity. }
  unfold region_small, store_region. cbn [rg_pages rg_len].
  split; [exact Hal|]. intros pn' p' Hp'.
  rewrite iget_iset in Hp'. destruct (pn' =? pn)%uint63 eqn:Epp; [|exact (Hpages pn' p' Hp')].
  apply Uint63.eqb_spec in Epp. subst pn'. injection Hp' as <-.
  split; [rewrite Epn; clear - Hoff Hoff0; Z.div_mod_to_equations; lia|].
  intros ci' Hci'. unfold store_page in Hci'. cbn [pg_cells] in Hci'. rewrite iget_iset in Hci'.
  destruct (ci' =? ci)%uint63 eqn:Ecc.
  - apply Uint63.eqb_spec in Ecc. subst ci'. rewrite Epn, Eci.
    clear - Hal Hin Hn Hoff0. Z.div_mod_to_equations. lia.
  - (* [comment removed for export] *)
    unfold page_at in Hp. destruct (iget pn (rg_pages rg)) as [p0|] eqn:Ep0.
    + injection Hp as <-. exact (proj2 (Hpages pn p0 Ep0) ci' Hci').
    + exfalso. apply Hci'.
      destruct (if (t =? 0)%uint63 then find_seg IM (pn << 12)%uint63 else None) as [sg|].
      * injection Hp as <-. cbn [pg_cells]. apply iget_iempty.
      * destruct (rg_dflt rg) as [k|]; [|discriminate Hp].
        destruct (page_in_region rg pn); [|discriminate Hp]. injection Hp as <-. cbn [pg_cells]. apply iget_iempty.
Qed.

Lemma fx_step_cells_inv F F' :
  cells_inv (f_mem F) -> fx_step IM code F = FNext F' -> cells_inv (f_mem F').
Proof.
  intros HM H. destruct (fx_step_mem IM code F F' H) as [E | (a & sz & v & Hst)].
  - rewrite E. exact HM.
  - exact (fm_store_cells_inv _ _ _ _ _ HM Hst).
Qed.

Theorem fx_run_cells_inv : forall bp k F F' r cnt,
  cells_inv (f_mem F) -> fx_run IM code bp k F = (F', r, cnt) -> cells_inv (f_mem F').
Proof.
  intros bp k. induction k as [|k IH]; intros F F' r cnt HM H.
  - cbn [fx_run] in H. destruct (f_pc F =? bp)%uint63; [injection H as <- <- <-; exact HM|].
    destruct (fx_step IM code F) as [s'| |c] eqn:Es; injection H as <- <- <-; try exact HM.
    exact (fx_step_cells_inv F s' HM Es).
  - cbn [fx_run] in H. destruct (fx_run IM code bp k F) as [[s1 r1] n1] eqn:E1.
    destruct (stop_is_fuel r1).
    + destruct (fx_run IM code bp k s1) as [[s2 r2] n2] eqn:E2. injection H as <- <- <-.
      exact (IH _ _ _ _ (IH _ _ _ _ HM E1) E2).
    + injection H as <- <- <-. exact (IH _ _ _ _ HM E1).
Qed.
End Exec.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lsl12_mod8 (x : int) : to_Z (x << 12) mod 8 = 0.
Proof.
  rewrite lsl_spec. change (2 ^ to_Z 12) with 4096. change wB with (2 ^ 63).
  pose proof (i63_range x). Z.div_mod_to_equations. lia.
Qed.

Lemma pg_up_mod8 (len : int) : to_Z (pg_up len) mod 8 = 0.
Proof. unfold pg_up. apply lsl12_mod8. Qed.

Lemma pg_up_lsr3_mod8 (len : int) : to_Z (pg_up len >> 3) mod 8 = 0.
Proof.
  unfold pg_up. rewrite lsr_spec, lsl_spec. change (2 ^ to_Z 12) with 4096. change (2 ^ to_Z 3) with 8.
  change wB with (2 ^ 63). pose proof (i63_range ((len + 4095) >> 12)). Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Definition dres3_inv (res : dres3) : Prop :=
  forall F' L' n', dres3_in (F', L', n') res -> cells_inv (f_mem F').

Lemma dres3_inv_one F L n : cells_inv (f_mem F) -> dres3_inv (D3One F L n).
Proof. intros H F' L' n' Hin. cbn [dres3_in] in Hin. injection Hin as -> _ _. exact H. Qed.

Lemma sys_grant_cells_inv Rb Rc Lim rl F L n len F' L' n' :
  cells_inv (f_mem F) -> sys_grant Rb Rc Lim rl F L n len = Some (DOne F' L' n') -> cells_inv (f_mem F').
Proof.
  intros HM H. unfold sys_grant in H. cbv zeta in H.
  match type of H with (if ?c then _ else _) = _ => destruct c end; [|discriminate].
  injection H as <- _ _. unfold fx_grant, fx_sysret. cbn [f_mem].
  apply cells_inv_iset; [exact HM|]. apply region_small_empty. apply pg_up_mod8.
Qed.

Lemma sys_grant3_cells_inv Rb Rc Lim nr F L3 n len res :
  cells_inv (f_mem F) -> sys_grant3 Rb Rc Lim nr F L3 n len = Some res -> dres3_inv res.
Proof.
  intros HM H. unfold sys_grant3 in H.
  destruct (sys_grant Rb Rc BIG RTgt F (fl3 L3) n len) as [[F1 L1 n1| ]|] eqn:Eg; try discriminate.
  cbv zeta in H. match type of H with (if ?c then _ else _) = _ => destruct c end; [|discriminate].
  injection H as <-. apply dres3_inv_one. exact (sys_grant_cells_inv _ _ _ _ _ _ _ _ _ _ _ HM Eg).
Qed.

Lemma sys_grant3p_cells_inv Rb Rc Lim shp nr F L3 n len res :
  cells_inv (f_mem F) -> sys_grant3p Rb Rc Lim shp nr F L3 n len = Some res -> dres3_inv res.
Proof.
  intros HM H. unfold sys_grant3p in H.
  destruct (sys_grant3 Rb Rc Lim nr F L3 n len) as [[F1 L31 n1| ]|] eqn:Eg; try discriminate.
  pose proof (sys_grant3_cells_inv _ _ _ _ _ _ _ _ _ HM Eg F1 L31 n1 eq_refl) as H1.
  destruct (shp (pg_up len)).
  - cbv zeta in H. match type of H with (if ?c then _ else _) = _ => destruct c end; [|discriminate].
    injection H as <-. apply dres3_inv_one. unfold add_region. cbn [f_mem].
    apply cells_inv_iset; [exact H1|]. unfold shadow_region. apply region_small_empty. apply pg_up_lsr3_mod8.
  - injection H as <-. apply dres3_inv_one. exact H1.
Qed.

Lemma sys_unmap3_cells_inv Lim keep F L3 n t off len res :
  cells_inv (f_mem F) -> sys_unmap3 Lim keep F L3 n t off len = Some res -> dres3_inv res.
Proof.
  intros HM H. unfold sys_unmap3 in H.
  destruct (sys_unmap keep F (fl3 L3) n t off len) as [[F1 L1 n1| ]|] eqn:Eu; try discriminate.
  destruct (iget t (f_mem F)) as [rg|] eqn:Eg; [|discriminate].
  cbv zeta in H. match type of H with (if ?c then _ else _) = _ => destruct c end; [|discriminate].
  injection H as <-. apply dres3_inv_one.
  unfold sys_unmap in Eu. rewrite Eg in Eu.
  match type of Eu with (if ?c then _ else _) = _ => destruct c end; [|discriminate].
  injection Eu as <- _ _. unfold fx_unmap, fx_sysret. cbn [f_mem]. apply cells_inv_iremove. exact HM.
Qed.

Lemma sys_unmap3p_cells_inv Lim keep F L3 n t off len res :
  cells_inv (f_mem F) -> sys_unmap3p Lim keep F L3 n t off len = Some res -> dres3_inv res.
Proof.
  intros HM H. unfold sys_unmap3p in H.
  destruct (shadow_clean keep (fl3 L3) (f_mem F) (t + 1)%uint63).
  - assert (HM' : cells_inv (f_mem (drop_region F (t + 1)%uint63))).
    { unfold drop_region. cbn [f_mem]. apply cells_inv_iremove. exact HM. }
    exact (sys_unmap3_cells_inv _ _ _ _ _ _ _ _ _ HM' H).
  - exact (sys_unmap3_cells_inv _ _ _ _ _ _ _ _ _ HM H).
Qed.

Lemma sys_commit3_cells_inv Lim keep F L3 n t off len res :
  cells_inv (f_mem F) -> sys_commit3 Lim keep F L3 n t off len = Some res -> dres3_inv res.
Proof.
  intros HM H. unfold sys_commit3 in H. cbv zeta in H.
  destruct (range_ok keep F n t off len && negb (t =? 0)%uint63) eqn:Er; [|discriminate].
  apply andb_true_iff in Er as [Er _].
  destruct (iget t (f_mem F)) as [rg|] eqn:Eg; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c end; [|discriminate].
  injection H as <-. apply dres3_inv_one.
  destruct (range_ok_sound [] keep F n t off len Er) as (rg' & _ & _ & _ & (Hl0 & Hl1) & Hoff & Hsum & _).
  unfold fx_commit, fx_sysret, upd_region. cbn [f_mem]. rewrite Eg.
  apply cells_inv_iset; [exact HM|].
  destruct (HM t rg Eg) as [Hal Hpages]. split; [exact Hal|]. cbn [rg_pages rg_len].
  intros pn p Hp.
  pose proof (i63_range off) as Hoff0.
  assert (Epn : to_Z (off >> 12) = to_Z off / 4096) by (rewrite lsr_spec; reflexivity).
  assert (Ek : Z.of_nat (Z.to_nat (to_Z (pg_up len >> 12))) = State.page_round_up_Z (to_Z len) / 4096).
  { rewrite lsr_spec, (pg_up_spec [] len Hl1). change (2 ^ to_Z 12) with 4096.
    apply Z2Nat.id. unfold State.page_round_up_Z, State.page_size. Z.div_mod_to_equations. lia. }
  assert (Hb : to_Z (off >> 12) + Z.of_nat (Z.to_nat (to_Z (pg_up len >> 12))) <= 2 ^ 50).
  { rewrite Epn, Ek. clear - Hsum Hoff0 Hl0.
    assert (0 <= State.page_round_up_Z (to_Z len)).
    { unfold State.page_round_up_Z, State.page_size. Z.div_mod_to_equations. lia. }
    Z.div_mod_to_equations. lia. }
  rewrite iget_zero_pages in Hp by lia.
  destruct ((to_Z (off >> 12) <=? to_Z pn) && (to_Z pn <? to_Z (off >> 12) + Z.of_nat (Z.to_nat (to_Z (pg_up len >> 12))))) eqn:Ein.
  - injection Hp as <-. apply andb_true_iff in Ein as [_ E2]. apply Z.ltb_lt in E2.
    split; [lia|]. intros ci Hci. exfalso. apply Hci. cbn [pg_cells]. apply iget_iempty.
  - exact (Hpages pn p Hp).
Qed.

(* [comment removed for export] *)
Lemma set_bounds_cells_inv F t rg clo chi :
  cells_inv (f_mem F) -> iget t (f_mem F) = Some rg -> cells_inv (f_mem (set_bounds F t rg clo chi)).
Proof.
  intros HM Hg. unfold set_bounds. cbn [f_mem]. apply cells_inv_iset; [exact HM|].
  apply region_small_rebound. exact (HM t rg Hg).
Qed.

Lemma snap_cells_inv L n F t : cells_inv (f_mem F) -> cells_inv (f_mem (snap L n F t)).
Proof.
  intros HM. unfold snap. destruct (iget t (f_mem F)) as [rg|] eqn:Eg; [|exact HM].
  match goal with |- context [if ?c then _ else _] => destruct c end; [|exact HM].
  exact (set_bounds_cells_inv F t rg _ _ HM Eg).
Qed.

Lemma refine3_cells_inv L F n t thr Fa Fb :
  cells_inv (f_mem F) -> refine3 L F n t thr = Some (Fa, Fb) -> cells_inv (f_mem Fa) /\ cells_inv (f_mem Fb).
Proof.
  intros HM H. unfold refine3 in H.
  destruct (refine_region F n t thr) as [[Fa0 Fb0]|] eqn:Er; [|discriminate]. injection H as <- <-.
  unfold refine_region in Er. destruct (iget t (f_mem F)) as [rg|] eqn:Eg; [|discriminate].
  match type of Er with (if ?c then _ else _) = _ => destruct c end; [|discriminate].
  injection Er as <- <-.
  split; apply snap_cells_inv; exact (set_bounds_cells_inv F t rg _ _ HM Eg).
Qed.

Lemma drive_sys_own3_cells_inv code Rb Rc Lim keep shp F L3 n res :
  cells_inv (f_mem F) -> drive_sys_own3 code Rb Rc Lim keep shp F L3 n = Some res -> dres3_inv res.
Proof.
  intros HM H. unfold drive_sys_own3 in H.
  repeat match type of H with
         | (if ?c then _ else _) = _ => destruct c; try discriminate
         | match ?x with _ => _ end = _ => destruct x; try discriminate
         end;
    first [ exact (sys_grant3p_cells_inv _ _ _ _ _ _ _ _ _ _ HM H)
          | exact (sys_commit3_cells_inv _ _ _ _ _ _ _ _ _ HM H)
          | exact (sys_unmap3p_cells_inv _ _ _ _ _ _ _ _ _ HM H) ].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition keeps_mem (x : fstate -> fledger3 -> int -> option dres3) : Prop :=
  forall F L3 n res, x F L3 n = Some res -> forall F' L' n', dres3_in (F', L', n') res -> f_mem F' = f_mem F.

Lemma keeps_mem_inv x : keeps_mem x ->
  forall F L3 n res, cells_inv (f_mem F) -> x F L3 n = Some res -> dres3_inv res.
Proof. intros Hk F L3 n res HM Hx F' L' n' Hin. rewrite (Hk F L3 n res Hx F' L' n' Hin). exact HM. Qed.

Lemma keeps_mem_or x1 x2 : keeps_mem x1 -> keeps_mem x2 -> keeps_mem (xpc_or x1 x2).
Proof.
  intros H1 H2 F L3 n res Hx. unfold xpc_or in Hx. destruct (x1 F L3 n) as [r|] eqn:E1.
  - injection Hx as <-. exact (H1 F L3 n r E1).
  - exact (H2 F L3 n res Hx).
Qed.

Local Ltac hook_mem H :=
  cbv zeta in H;
  repeat match type of H with
         | (if ?c then _ else _) = _ => destruct c; try discriminate
         | match ?x with _ => _ end = _ => destruct x; try discriminate
         end;
  injection H as <-;
  let Hin := fresh "Hin" in
  intros ? ? ? Hin; cbn [dres3_in] in Hin;
  repeat match type of Hin with _ \/ _ => destruct Hin as [Hin|Hin] end;
  injection Hin as -> _ _; reflexivity.

Lemma xpc_opaque_mem code : keeps_mem (xpc_opaque code).
Proof. intros F L3 n res H. unfold xpc_opaque in H. hook_mem H. Qed.

Lemma xpc_order_mem code : keeps_mem (xpc_order code).
Proof. intros F L3 n res H. unfold xpc_order in H. hook_mem H. Qed.

Lemma xpc_ltu_mem code : keeps_mem (xpc_ltu code).
Proof. intros F L3 n res H. unfold xpc_ltu in H. hook_mem H. Qed.

Lemma xpc_sltu_mem code : keeps_mem (xpc_sltu code).
Proof. intros F L3 n res H. unfold xpc_sltu in H. hook_mem H. Qed.

Lemma xpc_pgnz_mem code : keeps_mem (xpc_pgnz code).
Proof. intros F L3 n res H. unfold xpc_pgnz in H. hook_mem H. Qed.

Lemma xpc_align2_mem code : keeps_mem (xpc_align2 code).
Proof. intros F L3 n res H. unfold xpc_align2 in H. hook_mem H. Qed.

Lemma xpc_table_mem IM code : keeps_mem (xpc_table IM code).
Proof. intros F L3 n res H. unfold xpc_table in H. hook_mem H. Qed.

Lemma xpc_wload_mem IM code : keeps_mem (xpc_wload IM code).
Proof. intros F L3 n res H. unfold xpc_wload in H. hook_mem H. Qed.

Theorem xpc_builtin6_mem IM code : keeps_mem (xpc_builtin6 IM code).
Proof.
  unfold xpc_builtin6.
  repeat (apply keeps_mem_or; [first [apply xpc_order_mem | apply xpc_ltu_mem | apply xpc_sltu_mem | apply xpc_pgnz_mem
                                     | apply xpc_align2_mem | apply xpc_table_mem | apply xpc_wload_mem]|]).
  apply xpc_opaque_mem.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Drive3K.
Variable IM : fimage.
Variable code : itrie finstr.
Variable Rb Rc Lim : Z.
Variable keep : list int.
Variable shp : int -> bool.
Variable xsys3 : fstate -> fledger3 -> int -> option dres3.
Variable xask : fstate -> option (int * int).
Variable xpc : fstate -> fledger3 -> int -> option dres3.
(* [comment removed for export] *)
Hypothesis xsys3_inv : forall F L3 n res, cells_inv (f_mem F) -> xsys3 F L3 n = Some res -> dres3_inv res.
Hypothesis xpc_inv : forall F L3 n res, cells_inv (f_mem F) -> xpc F L3 n = Some res -> dres3_inv res.

Lemma drive_sys3_cells_inv F L3 n res :
  cells_inv (f_mem F) -> drive_sys3 code Rb Rc Lim keep shp xsys3 F L3 n = Some res -> dres3_inv res.
Proof.
  intros HM H. unfold drive_sys3 in H.
  destruct (drive_sys_own3 code Rb Rc Lim keep shp F L3 n) as [r|] eqn:Eo.
  - injection H as <-. exact (drive_sys_own3_cells_inv _ _ _ _ _ _ _ _ _ _ HM Eo).
  - exact (xsys3_inv F L3 n res HM H).
Qed.

Theorem drive3_cells_inv : forall bp k fuel F L3 n,
  cells_inv (f_mem F) ->
  forall F' L' n' r,
    leaf_in3 (F', L', n', r) (drive3 IM code Rb Rc Lim keep shp xsys3 xask xpc bp k fuel F L3 n) ->
    cells_inv (f_mem F').
Proof.
  intros bp k fuel. induction fuel as [|fuel IH]; intros F L3 n HM F' L' n' r Hleaf.
  - cbn [drive3 leaf_in3] in Hleaf. injection Hleaf as -> _ _ _. exact HM.
  - cbn [drive3] in Hleaf.
    destruct (fx_run IM code bp k F) as [[F1 r1] c1] eqn:Erun.
    pose proof (fx_run_cells_inv IM code bp k F F1 r1 c1 HM Erun) as HM1.
    assert (Hres : forall res, dres3_inv res ->
              leaf_in3 (F', L', n', r)
                (match res with
                 | D3One F2 L2 n2 => drive3 IM code Rb Rc Lim keep shp xsys3 xask xpc bp k fuel F2 L2 n2
                 | D3Two F2 L2 n2 F3 L3' n3 =>
                     D3Fork (drive3 IM code Rb Rc Lim keep shp xsys3 xask xpc bp k fuel F2 L2 n2)
                            (drive3 IM code Rb Rc Lim keep shp xsys3 xask xpc bp k fuel F3 L3' n3)
                 end) -> cells_inv (f_mem F')).
    { intros res Hr Hl. destruct res as [F2 L2 n2 | F2 L2 n2 F3 L3' n3].
      - exact (IH F2 L2 n2 (Hr F2 L2 n2 eq_refl) F' L' n' r Hl).
      - cbn [leaf_in3] in Hl. destruct Hl as [Hl|Hl].
        + exact (IH F2 L2 n2 (Hr F2 L2 n2 (or_introl eq_refl)) F' L' n' r Hl).
        + exact (IH F3 L3' n3 (Hr F3 L3' n3 (or_intror eq_refl)) F' L' n' r Hl). }
    destruct r1 as [| | |c].
    + exact (IH F1 L3 n HM1 F' L' n' r Hleaf).
    + destruct (drive_sys3 code Rb Rc Lim keep shp xsys3 F1 L3 n) as [res|] eqn:Es.
      * exact (Hres res (drive_sys3_cells_inv F1 L3 n res HM1 Es) Hleaf).
      * cbn [leaf_in3] in Hleaf. injection Hleaf as -> _ _ _. exact HM1.
    + cbn [leaf_in3] in Hleaf. injection Hleaf as -> _ _ _. exact HM1.
    + destruct (xpc F1 L3 n) as [res|] eqn:Ex.
      * exact (Hres res (xpc_inv F1 L3 n res HM1 Ex) Hleaf).
      * destruct (ask_split3 xask F1 L3 n) as [[Fa Fb]|] eqn:Ea.
        -- unfold ask_split3 in Ea. destruct (xask F1) as [[t thr]|]; [|discriminate].
           destruct (refine3_cells_inv _ _ _ _ _ _ _ HM1 Ea) as [Ha Hb].
           cbn [leaf_in3] in Hleaf. destruct Hleaf as [Hl|Hl].
           ++ exact (IH Fa L3 n Ha F' L' n' r Hl).
           ++ exact (IH Fb L3 n Hb F' L' n' r Hl).
        -- cbn [leaf_in3] in Hleaf. injection Hleaf as -> _ _ _. exact HM1.
Qed.
End Drive3K.

(* [comment removed for export] *)
Theorem drive3_cells_inv6 IM code Rb Rc Lim keep shp xask bp k fuel F L3 n :
  cells_inv (f_mem F) ->
  forall F' L' n' r,
    leaf_in3 (F', L', n', r)
      (drive3 IM code Rb Rc Lim keep shp (fun _ _ _ => None) xask (xpc_builtin6 IM code) bp k fuel F L3 n) ->
    cells_inv (f_mem F').
Proof.
  apply drive3_cells_inv.
  - intros F0 L0 n0 res _ H. discriminate H.
  - exact (keeps_mem_inv _ (xpc_builtin6_mem IM code)).
Qed.

(* [comment removed for export] *)
Corollary drive3_cells_small6 segs IM code Rb Rc Lim keep shp xask bp k fuel F L3 n :
  cells_inv_b (f_mem F) = true ->
  forall F' L' n' r,
    leaf_in3 (F', L', n', r)
      (drive3 IM code Rb Rc Lim keep shp (fun _ _ _ => None) xask (xpc_builtin6 IM code) bp k fuel F L3 n) ->
    forall rho m, mem_ok segs IM rho (f_mem F') m ->
    forall t rg pn p ci,
      iget t (f_mem F') = Some rg -> iget pn (rg_pages rg) = Some p -> iget ci (pg_cells p) <> None ->
      to_Z pn < 2 ^ 50 /\ to_Z ci < 512
      /\ to_Z (rg_lo rg) <= to_Z pn * 4096 /\ to_Z pn * 4096 + to_Z ci * 8 + 8 <= to_Z (rg_len rg).
Proof.
  intros Hb F' L' n' r Hleaf rho m Hmok t rg pn p ci.
  apply (cells_inv_spec_lo segs IM rho (f_mem F') m); [|exact Hmok].
  exact (drive3_cells_inv6 IM code Rb Rc Lim keep shp xask bp k fuel F L3 n (cells_inv_b_sound _ Hb) F' L' n' r Hleaf).
Qed.
