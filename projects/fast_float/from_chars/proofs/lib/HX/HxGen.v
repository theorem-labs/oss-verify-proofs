(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxMem FxFold FxRgs FxFacts FxImg FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan FxFrame.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxDrv FxCall FxWork FxWorkX.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFold OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv.FxGrow OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxWork OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxWorkX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition rkz (k : Z) : positive := rkey (Z_to_bv 5 k).
(* [comment removed for export] *)
Fixpoint set_fresh (R : tree lin) (keys : list Z) (n : positive) : tree lin :=
  match keys with [] => R | k :: ks => set_fresh (rset R (rkz k) (lvar n)) ks (Pos.succ n) end.
(* [comment removed for export] *)
Definition updv (E : valu) (x : positive) (v : word) : valu := fun y => if Pos.eqb y x then v else E y.
Fixpoint E_of (keys : list Z) (vs : list word) (n : positive) (E : valu) : valu :=
  match keys, vs with k :: ks, v :: vs' => E_of ks vs' (Pos.succ n) (updv E n v) | _, _ => E end.

Fixpoint nodupb (l : list Z) : bool := match l with [] => true | x :: l' => (negb (existsb (Z.eqb x) l') && nodupb l')%bool end.
Definition keys_ok (keys : list Z) : bool := (forallb (fun k => Z.leb 1 k && Z.leb k 31) keys && nodupb keys)%bool.

Lemma u5 : forall k, 0 <= k < 32 -> bv_unsigned (Z_to_bv 5 k) = k.
Proof. intros k Hk. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 5) with 32. apply Z.mod_small. exact Hk. Qed.
Lemma rkey_rkz : forall r : reg, rkey r = rkz (bv_unsigned r).
Proof. intros r. unfold rkz. rewrite Z_to_bv_bv_unsigned. reflexivity. Qed.
Lemma rkz_ne1 : forall k, 1 <= k <= 31 -> rkz k <> xH.
Proof.
  intros k Hk H. unfold rkz, rkey, bv_key in H. rewrite u5 in H by lia. apply (f_equal Zpos) in H. rewrite Z2Pos.id in H by lia. lia.
Qed.
Lemma rkz_rkey_ne : forall (r : reg) k, 1 <= k <= 31 -> r <> Z_to_bv 5 k -> rkey r <> rkz k.
Proof.
  intros r k Hk Hne H. apply Hne. unfold rkz, rkey, bv_key in H. rewrite u5 in H by lia. apply (f_equal Zpos) in H.
  pose proof (bv_unsigned_in_range _ r) as R. rewrite !Z2Pos.id in H by lia. apply bv_eq. rewrite u5 by lia. lia.
Qed.

Lemma E_of_old : forall keys vs n E x, (x < n)%positive -> E_of keys vs n E x = E x.
Proof.
  induction keys as [|k ks IH]; intros [|v vs] n E x Hx; cbn [E_of]; try reflexivity.
  rewrite (IH vs (Pos.succ n) (updv E n v) x ltac:(lia)). unfold updv. destruct (Pos.eqb x n) eqn:Hq; [apply Pos.eqb_eq in Hq; lia | reflexivity].
Qed.
Lemma E_of_agree : forall keys vs n E, agree n E (E_of keys vs n E).
Proof. intros keys vs n E x Hx. symmetry. apply E_of_old. exact Hx. Qed.
(* [comment removed for export] *)
Lemma E_of_nth : forall keys vs n E i v, length vs = length keys -> nth_error vs i = Some v ->
  E_of keys vs n E (Pos.of_nat (Pos.to_nat n + i)) = v.
Proof.
  induction keys as [|k ks IH]; intros [|v0 vs] n E i v Hl Hv; cbn [length] in Hl; try discriminate.
  - destruct i; discriminate.
  - injection Hl as Hl. cbn [E_of]. destruct i as [|i].
    + cbn in Hv. injection Hv as <-. rewrite E_of_old by lia. unfold updv. rewrite Nat.add_0_r, Pos2Nat.id, Pos.eqb_refl. reflexivity.
    + cbn in Hv. replace (Pos.of_nat (Pos.to_nat n + S i)) with (Pos.of_nat (Pos.to_nat (Pos.succ n) + i)) by (f_equal; lia).
      exact (IH vs (Pos.succ n) (updv E n v0) i v Hl Hv).
Qed.

(* [comment removed for export] *)
Lemma set_fresh_ok : forall keys vs n E R (g g' : reg -> word),
  keys_ok keys = true -> length vs = length keys ->
  (forall r, g r = lden E (rget R (rkey r))) -> (forall r, lwf n (rget R (rkey r)) = true) ->
  (forall r, ~ In (bv_unsigned r) keys -> g' r = g r) ->
  (forall i k v, nth_error keys i = Some k -> nth_error vs i = Some v -> g' (Z_to_bv 5 k) = v) ->
  forall r, g' r = lden (E_of keys vs n E) (rget (set_fresh R keys n) (rkey r)).
Proof.
  induction keys as [|k ks IH]; intros [|v vs] n E R g g' Hk Hl Hg Hw Hnk Hkv r; cbn [length] in Hl; try discriminate.
  - cbn [E_of set_fresh]. rewrite (Hnk r ltac:(intros [])). apply Hg.
  - injection Hl as Hl. unfold keys_ok in Hk. cbn [forallb nodupb] in Hk.
    apply andb_prop in Hk as [Hk1 Hk2]. apply andb_prop in Hk1 as [Hkk Hks1]. apply andb_prop in Hk2 as [Hkn Hks2].
    apply andb_prop in Hkk as [Hkk1 Hkk2]. apply Z.leb_le in Hkk1, Hkk2.
    cbn [E_of set_fresh].
    set (g1 := fun r0 : reg => if Z.eqb (bv_unsigned r0) k then v else g r0).
    apply (IH vs (Pos.succ n) (updv E n v) (rset R (rkz k) (lvar n)) g1 g'); [unfold keys_ok; rewrite Hks1, Hks2; reflexivity | exact Hl | | | | ].
    + intros r0. unfold g1. destruct (Z.eqb (bv_unsigned r0) k) eqn:Hq.
      * apply Z.eqb_eq in Hq. rewrite rkey_rkz, Hq. rewrite rget_rset_same by (apply rkz_ne1; lia).
        rewrite lden_lvar. unfold updv. rewrite Pos.eqb_refl. reflexivity.
      * assert (Hne : r0 <> Z_to_bv 5 k) by (intros X; subst r0; rewrite u5 in Hq by lia; rewrite Z.eqb_refl in Hq; discriminate).
        rewrite rget_rset_other by (apply rkz_rkey_ne; [lia | exact Hne]). rewrite Hg.
        apply (lden_agree n); [apply Hw|]. intros x Hx. unfold updv. destruct (Pos.eqb x n) eqn:X; [apply Pos.eqb_eq in X; lia | reflexivity].
    + intros r0. destruct (decide (r0 = Z_to_bv 5 k)) as [->|Hne].
      * rewrite rkey_rkz, u5 by lia. rewrite rget_rset_same by (apply rkz_ne1; lia). unfold lwf. apply forallb_forall. intros [x c] Hx.
        cbn [lvar l_t] in Hx. destruct Hx as [Hx|[]]. injection Hx as <- <-. apply Pos.ltb_lt. lia.
      * rewrite rget_rset_other by (apply rkz_rkey_ne; [lia | exact Hne]). apply (lwf_mono n); [lia | apply Hw].
    + intros r0 Hr0. unfold g1. destruct (Z.eqb (bv_unsigned r0) k) eqn:Hq.
      * apply Z.eqb_eq in Hq. assert (r0 = Z_to_bv 5 k) as -> by (apply bv_eq; rewrite u5 by lia; exact Hq).
        exact (Hkv 0%nat k v eq_refl eq_refl).
      * apply Hnk. intros [X|X]; [|exact (Hr0 X)]. rewrite X, Z.eqb_refl in Hq. discriminate.
    + intros i k' v' Hi Hv'. exact (Hkv (S i) k' v' Hi Hv').
Qed.

Section HxGen.
Variable segs : list Segment.
Variable xok : nat -> list word -> (word -> option byte) -> Prop.

(* [comment removed for export] *)
Definition hx_cont (pc1 : Z) (keys : list Z) (newf : sst -> list fact) (newx : sst -> list xfact) (X : xst) : xst :=
  let L := xs_st X in
  XST (SST pc1 (set_fresh (s_regs L) keys (s_next L)) (s_rgs L) (newf L ++ s_facts L) (Pos.of_nat (Pos.to_nat (s_next L) + length keys))
           (s_resv L))
      (newx L ++ xs_x X).
Definition hx_reg (pc0 pc1 : Z) (keys : list Z) (chk : sst -> bool) (newf : sst -> list fact) (newx : sst -> list xfact) (X : xst)
  : option (list xst) :=
  let K := hx_cont pc1 keys newf newx X in
  if (Z.eqb (s_pc (xs_st X)) pc0 && chk (xs_st X) && keys_ok keys && state_wf (xs_st X) && state_wf (xs_st K)
      && forallb (xwf (s_next (xs_st K))) (newx (xs_st X)))%bool
  then Some [K] else None.

(* [comment removed for export] *)
Definition hx_kit (pc0 pc1 : Z) (keys : list Z) (chk : sst -> bool) (newf : sst -> list fact) (newx : sst -> list xfact) : Prop :=
  forall L XL E ms (m0 : word -> option byte), s_pc L = pc0 -> chk L = true -> state_wf L = true -> sden segs E L ms ->
    Forall (xfact_ok xok E m0) XL -> (forall x, fr_pt E (s_rgs L) x -> ms_mem ms x = m0 x) ->
    exists ms' vs, isteps segs ms ms' /\ length vs = length keys /\
      ms_mem ms' = ms_mem ms /\ ms_fcsr ms' = ms_fcsr ms /\ ms_resv ms' = ms_resv ms /\ ms_svc_pending ms' = None /\
      ms_pc_val ms' = Z_to_bv 64 pc1 /\
      (forall r, ~ In (bv_unsigned r) keys -> getr (ms_regs ms') r = getr (ms_regs ms) r) /\
      (forall i k v, nth_error keys i = Some k -> nth_error vs i = Some v -> getr (ms_regs ms') (Z_to_bv 5 k) = v) /\
      Forall (fact_ok (E_of keys vs (s_next L) E)) (newf L) /\ Forall (xfact_ok xok (E_of keys vs (s_next L) E) m0) (newx L).

#[using="Type"] Theorem hx_ok : forall pc0 pc1 keys chk newf newx, hx_kit pc0 pc1 keys chk newf newx -> hand_okx segs xok (hx_reg pc0 pc1 keys chk newf newx).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros pc0 pc1 keys chk newf newx HK X Ks E ms m0 Hf Hd HxF Hxw Hm0. destruct X as [L XL]. cbn [xs_st xs_x] in *.
  unfold hx_reg, hx_cont in Hf. cbn [xs_st xs_x] in Hf.
  set (K := SST pc1 (set_fresh (s_regs L) keys (s_next L)) (s_rgs L) (newf L ++ s_facts L) (Pos.of_nat (Pos.to_nat (s_next L) + length keys))
                (s_resv L)) in *.
  destruct (Z.eqb (s_pc L) pc0 && chk L && keys_ok keys && state_wf L && state_wf K
            && forallb (xwf (s_next K)) (newx L))%bool eqn:Hc; [|discriminate].
  injection Hf as <-.
  apply andb_prop in Hc as [Hc HxwN]. apply andb_prop in Hc as [Hc HwK]. apply andb_prop in Hc as [Hc HwL].
  apply andb_prop in Hc as [Hc Hko]. apply andb_prop in Hc as [Hpc Hchk]. apply Z.eqb_eq in Hpc.
  destruct (HK L XL E ms m0 Hpc Hchk HwL Hd HxF Hm0)
    as (ms' & vs & Hst & Hlen & Hmem & Hfc & Hrv & Hsvc & Hpc' & Hnk & Hkv & HnF & HnX).
  set (E' := E_of keys vs (s_next L) E).
  assert (Hag : agree (s_next L) E E') by apply E_of_agree.
  assert (HnK : (s_next L <= Pos.of_nat (Pos.to_nat (s_next L) + length keys))%positive).
  { apply Pos2Nat.inj_le. rewrite Nat2Pos.id by lia. lia. }
  exists (XST K (newx L ++ XL)), ms', E'. split; [left; reflexivity|]. split; [exact Hst|].
  cbn [xs_st xs_x].
  pose proof (sden_0 _ _ _ _ Hd) as (Hpc0 & Hsvc0 & Hresv0 & HR0 & HG0 & HD0 & HF0 & Hfrm0).
  unfold state_wf in HwL. apply andb_prop in HwL as [HwL Hwv]. apply andb_prop in HwL as [HwL Hwf]. apply andb_prop in HwL as [Hwr Hwg].
  split; [|split; [exact Hag|split; [|split; [|split; [|split; [|split]]]]]].
  - apply sden0_sden; [exact HwK|]. unfold sden0. unfold K. cbn [s_pc s_regs s_rgs s_facts s_resv].
    split; [exact Hpc'|]. split; [exact Hsvc|].
    split.
    { rewrite Hrv. revert Hresv0 Hwv. destruct (s_resv L) as [|l|]; cbn [rsv_ok rsv_wf]; intros Hresv1 Hwv1.
      - exact Hresv1.
      - rewrite <- (lden_agree _ E E' l Hwv1 Hag). exact Hresv1.
      - exact I. }
    split; [|split; [|split; [|split]]].
    + intros r. apply (set_fresh_ok keys vs (s_next L) E (s_regs L) (getr (ms_regs ms)) (getr (ms_regs ms'))); try assumption.
      intros r0. destruct (decide (r0 = 0%bv)) as [->|Hr0]; [change (rkey 0%bv) with xH; reflexivity|].
      destruct (rkey_succ r0 Hr0) as (k & Hk & Ek). rewrite Ek. exact (regs_wf_n_spec _ _ 31 Hwr k Hk).
    + rewrite Hmem. apply Forall_forall. intros R HR. rewrite forallb_forall in Hwg. rewrite Forall_forall in HG0.
      exact (rg_ok_agree segs _ E E' _ R (Hwg R HR) Hag (HG0 R HR)).
    + exact (rgs_disj_agree _ E E' _ Hwg Hag HD0).
    + apply Forall_app. split; [exact HnF|]. apply Forall_forall. intros f Hf. rewrite forallb_forall in Hwf. rewrite Forall_forall in HF0.
      exact (fact_ok_agree _ E E' f (Hwf f Hf) Hag (HF0 f Hf)).
    + rewrite Hfc. exact Hfrm0.
  - intros x Hx. rewrite Hmem. reflexivity.
  - reflexivity.
  - exact HnK.
  - reflexivity.
  - apply Forall_app. split; [exact HnX|]. rewrite Forall_forall in *. intros f Hf. rewrite forallb_forall in Hxw.
    exact (xfact_ok_agree xok _ E E' m0 f (Hxw f Hf) Hag (HxF f Hf)).
  - rewrite forallb_app. rewrite HxwN. cbn [andb]. apply (xwf_mono (s_next L)); [exact HnK | exact Hxw].
Qed.
End HxGen.

(* [comment removed for export] *)
Section HxGenM.
Variable segs : list Segment.
Variable xok : nat -> list word -> (word -> option byte) -> Prop.

Definition hx_exit : Type := (Z * (sst -> list fact) * (sst -> list xfact))%type.
Definition hx_conts (keys : list Z) (exits : list hx_exit) (X : xst) : list xst :=
  List.map (fun '(pc1, newf, newx) => hx_cont pc1 keys newf newx X) exits.
Definition hx_regm (pc0 : Z) (keys : list Z) (chk : xst -> bool) (exits : list hx_exit) (X : xst) : option (list xst) :=
  let Ks := hx_conts keys exits X in
  if (Z.eqb (s_pc (xs_st X)) pc0 && chk X && keys_ok keys && state_wf (xs_st X)
      && forallb (fun '(pc1, newf, newx) =>
                    let K := hx_cont pc1 keys newf newx X in
                    (state_wf (xs_st K) && forallb (xwf (s_next (xs_st K))) (newx (xs_st X)))%bool) exits)%bool
  then Some Ks else None.

(* [comment removed for export] *)
Definition hx_kitm (pc0 : Z) (keys : list Z) (chk : xst -> bool) (exits : list hx_exit) : Prop :=
  forall L XL E ms (m0 : word -> option byte), s_pc L = pc0 -> chk (XST L XL) = true -> state_wf L = true -> sden segs E L ms ->
    Forall (xfact_ok xok E m0) XL -> (forall x, fr_pt E (s_rgs L) x -> ms_mem ms x = m0 x) ->
    exists pc1 newf newx ms' vs, In (pc1, newf, newx) exits /\ isteps segs ms ms' /\ length vs = length keys /\
      ms_mem ms' = ms_mem ms /\ ms_fcsr ms' = ms_fcsr ms /\ ms_resv ms' = ms_resv ms /\ ms_svc_pending ms' = None /\
      ms_pc_val ms' = Z_to_bv 64 pc1 /\
      (forall r, ~ In (bv_unsigned r) keys -> getr (ms_regs ms') r = getr (ms_regs ms) r) /\
      (forall i k v, nth_error keys i = Some k -> nth_error vs i = Some v -> getr (ms_regs ms') (Z_to_bv 5 k) = v) /\
      Forall (fact_ok (E_of keys vs (s_next L) E)) (newf L) /\ Forall (xfact_ok xok (E_of keys vs (s_next L) E) m0) (newx L).

#[using="Type"] Theorem hx_okm : forall pc0 keys chk exits, hx_kitm pc0 keys chk exits -> hand_okx segs xok (hx_regm pc0 keys chk exits).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros pc0 keys chk exits HK X Ks E ms m0 Hf Hd HxF Hxw Hm0. destruct X as [L XL]. cbn [xs_st xs_x] in *.
  unfold hx_regm in Hf. cbn [xs_st xs_x] in Hf.
  destruct (Z.eqb (s_pc L) pc0 && chk (XST L XL) && keys_ok keys && state_wf L
            && forallb (fun '(pc1, newf, newx) =>
                    let K := hx_cont pc1 keys newf newx (XST L XL) in
                    (state_wf (xs_st K) && forallb (xwf (s_next (xs_st K))) (newx L))%bool) exits)%bool eqn:Hc; [|discriminate].
  injection Hf as <-.
  apply andb_prop in Hc as [Hc Hall]. apply andb_prop in Hc as [Hc HwL].
  apply andb_prop in Hc as [Hc Hko]. apply andb_prop in Hc as [Hpc Hchk]. apply Z.eqb_eq in Hpc.
  destruct (HK L XL E ms m0 Hpc Hchk HwL Hd HxF Hm0)
    as (pc1 & newf & newx & ms' & vs & Hin & Hst & Hlen & Hmem & Hfc & Hrv & Hsvc & Hpc' & Hnk & Hkv & HnF & HnX).
  rewrite forallb_forall in Hall. pose proof (Hall _ Hin) as Hex. cbn beta iota in Hex. apply andb_prop in Hex as [HwK HxwN].
  set (K := SST pc1 (set_fresh (s_regs L) keys (s_next L)) (s_rgs L) (newf L ++ s_facts L) (Pos.of_nat (Pos.to_nat (s_next L) + length keys))
                (s_resv L)) in *.
  set (E' := E_of keys vs (s_next L) E).
  assert (Hag : agree (s_next L) E E') by apply E_of_agree.
  assert (HnK : (s_next L <= Pos.of_nat (Pos.to_nat (s_next L) + length keys))%positive).
  { apply Pos2Nat.inj_le. rewrite Nat2Pos.id by lia. lia. }
  exists (XST K (newx L ++ XL)), ms', E'.
  split; [unfold hx_conts; apply in_map_iff; exists (pc1, newf, newx); split; [reflexivity | exact Hin]|]. split; [exact Hst|].
  cbn [xs_st xs_x].
  pose proof (sden_0 _ _ _ _ Hd) as (Hpc0 & Hsvc0 & Hresv0 & HR0 & HG0 & HD0 & HF0 & Hfrm0).
  unfold state_wf in HwL. apply andb_prop in HwL as [HwL Hwv]. apply andb_prop in HwL as [HwL Hwf]. apply andb_prop in HwL as [Hwr Hwg].
  split; [|split; [exact Hag|split; [|split; [|split; [|split; [|split]]]]]].
  - apply sden0_sden; [exact HwK|]. unfold sden0. unfold K. cbn [s_pc s_regs s_rgs s_facts s_resv].
    split; [exact Hpc'|]. split; [exact Hsvc|].
    split.
    { rewrite Hrv. revert Hresv0 Hwv. destruct (s_resv L) as [|l|]; cbn [rsv_ok rsv_wf]; intros Hresv1 Hwv1.
      - exact Hresv1.
      - rewrite <- (lden_agree _ E E' l Hwv1 Hag). exact Hresv1.
      - exact I. }
    split; [|split; [|split; [|split]]].
    + intros r. apply (set_fresh_ok keys vs (s_next L) E (s_regs L) (getr (ms_regs ms)) (getr (ms_regs ms'))); try assumption.
      intros r0. destruct (decide (r0 = 0%bv)) as [->|Hr0]; [change (rkey 0%bv) with xH; reflexivity|].
      destruct (rkey_succ r0 Hr0) as (k & Hk & Ek). rewrite Ek. exact (regs_wf_n_spec _ _ 31 Hwr k Hk).
    + rewrite Hmem. apply Forall_forall. intros R HR. rewrite forallb_forall in Hwg. rewrite Forall_forall in HG0.
      exact (rg_ok_agree segs _ E E' _ R (Hwg R HR) Hag (HG0 R HR)).
    + exact (rgs_disj_agree _ E E' _ Hwg Hag HD0).
    + apply Forall_app. split; [exact HnF|]. apply Forall_forall. intros f Hf. rewrite forallb_forall in Hwf. rewrite Forall_forall in HF0.
      exact (fact_ok_agree _ E E' f (Hwf f Hf) Hag (HF0 f Hf)).
    + rewrite Hfc. exact Hfrm0.
  - intros x Hx. rewrite Hmem. reflexivity.
  - reflexivity.
  - exact HnK.
  - reflexivity.
  - apply Forall_app. split; [exact HnX|]. rewrite Forall_forall in *. intros f Hf. rewrite forallb_forall in Hxw.
    exact (xfact_ok_agree xok _ E E' m0 f (Hxw f Hf) Hag (HxF f Hf)).
  - rewrite forallb_app. apply andb_true_intro. split; [exact HxwN | apply (xwf_mono (s_next L)); [exact HnK | exact Hxw]].
Qed.
End HxGenM.

(* [comment removed for export] *)
Section HxRule.
Variable segs : list Segment.
Variable xok : nat -> list word -> (word -> option byte) -> Prop.
Definition nofacts (L : sst) : list fact := [].
Definition hx_rule (pc : Z) (chk : xst -> bool) (newx : sst -> list xfact) : xst -> option (list xst) :=
  hx_regm pc [] chk [(pc, nofacts, newx)].
#[using="Type"] Lemma hx_kitm_rule : forall pc chk newx,
  (forall L XL E ms (m0 : word -> option byte), s_pc L = pc -> chk (XST L XL) = true -> state_wf L = true -> sden segs E L ms ->
     Forall (xfact_ok xok E m0) XL -> (forall x, fr_pt E (s_rgs L) x -> ms_mem ms x = m0 x) -> Forall (xfact_ok xok E m0) (newx L)) ->
  hx_kitm segs xok pc [] chk [(pc, nofacts, newx)].
Proof. LiaFast.lf_pins LiaFast.u0.
  intros pc chk newx HR L XL E ms m0 Hpc Hchk Hw Hd HxF Hm0.
  pose proof (sden_0 _ _ _ _ Hd) as (Hpc0 & Hsvc0 & _).
  exists pc, nofacts, newx, ms, []. split; [left; reflexivity|]. split; [apply ist_refl|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact Hsvc0|]. split; [rewrite Hpc0, Hpc; reflexivity|].
  split; [intros; reflexivity|]. split; [intros i k v Hi; destruct i; discriminate|]. split; [constructor|].
  cbn [E_of]. exact (HR L XL E ms m0 Hpc Hchk Hw Hd HxF Hm0).
Qed.
#[using="Type"] Theorem hx_rule_ok : forall pc chk newx,
  (forall L XL E ms (m0 : word -> option byte), s_pc L = pc -> chk (XST L XL) = true -> state_wf L = true -> sden segs E L ms ->
     Forall (xfact_ok xok E m0) XL -> (forall x, fr_pt E (s_rgs L) x -> ms_mem ms x = m0 x) -> Forall (xfact_ok xok E m0) (newx L)) ->
  hand_okx segs xok (hx_rule pc chk newx).
Proof. LiaFast.lf_pins LiaFast.u0. intros pc chk newx H. apply hx_okm. apply hx_kitm_rule. exact H. Qed.
End HxRule.

(* [comment removed for export] *)
Section HxFold.
Variable segs : list Segment.
Variable xok : nat -> list word -> (word -> option byte) -> Prop.
Definition hx_fold (pc k : Z) (X : xst) : option (list xst) :=
  let L := xs_st X in
  let l := rget (s_regs L) (rkz k) in
  let r := irange (s_facts L) l in
  if (Z.eqb (s_pc L) pc && Z.eqb (fst r) (snd r) && Z.leb 1 k && Z.leb k 31)%bool
  then Some [XST (SST (s_pc L) (rset (s_regs L) (rkz k) (lconst (fst r))) (s_rgs L) (s_facts L) (s_next L) (s_resv L)) (xs_x X)]
  else None.
#[using="Type"] Theorem hx_fold_ok : forall pc k, hand_okx segs xok (hx_fold pc k).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros pc k X Ks E ms m0 Hf Hd HxF Hxw Hm0. destruct X as [L XL]. unfold hx_fold in Hf. cbn [xs_st xs_x] in *.
  destruct (Z.eqb (s_pc L) pc && Z.eqb (fst (irange (s_facts L) (rget (s_regs L) (rkz k)))) (snd (irange (s_facts L) (rget (s_regs L) (rkz k))))
            && Z.leb 1 k && Z.leb k 31)%bool eqn:Hc; [|discriminate].
  injection Hf as <-.
  apply andb_prop in Hc as [Hc Hk2]. apply andb_prop in Hc as [Hc Hk1]. apply andb_prop in Hc as [_ Heq].
  apply Z.eqb_eq in Heq. apply Z.leb_le in Hk1, Hk2.
  set (l := rget (s_regs L) (rkz k)) in *. set (c := fst (irange (s_facts L) l)) in *.
  eexists. exists ms, E. split; [left; reflexivity|]. split; [apply ist_refl|].
  cbn [xs_st xs_x s_pc s_regs s_rgs s_facts s_next s_resv].
  split; [|split; [intros x Hx; reflexivity|split; [intros; reflexivity|split; [reflexivity|split; [lia|split; [reflexivity|split; [exact HxF | exact Hxw]]]]]]].
  intros E' Ha. pose proof (Hd E' Ha) as (Hpc0 & Hsvc0 & Hresv0 & HR0 & HG0 & HD0 & HF0 & Hfrm0).
  unfold sden0. cbn [s_pc s_regs s_rgs s_facts s_resv s_next].
  refine (conj Hpc0 (conj Hsvc0 (conj Hresv0 (conj _ (conj HG0 (conj HD0 (conj HF0 Hfrm0))))))).
  unfold regs_ok. intros r. destruct (Pos.eq_dec (rkey r) (rkz k)) as [Hq|Hq].
  - rewrite Hq. rewrite rget_rset_same by (apply rkz_ne1; lia). rewrite lden_lconst. rewrite (HR0 r), Hq. fold l.
    pose proof (irange_sound E' (s_facts L) l HF0) as X. fold c in X. rewrite <- Heq in X. fold c in X.
    apply bv_eq. rewrite u_Z_to_bv. pose proof (bv_unsigned_in_range _ (lden E' l)) as B. unfold bv_modulus in B.
    change (2 ^ Z.of_N 64) with two64 in B. rewrite Z.mod_small by lia. lia.
  - rewrite rget_rset_other by exact Hq. exact (HR0 r).
Qed.
End HxFold.

(* [comment removed for export] *)
Section HxC2R.
Variable segs : list Segment.
Variable xok : nat -> list word -> (word -> option byte) -> Prop.
Definition T63c : Z := 9223372036854775808.
Definition c2r (fs : list fact) (f : fact) : list fact :=
  match f with
  | FCond c a b tk =>
      let ha := snd (irange fs a) in let hb := snd (irange fs b) in
      if (Z.ltb ha T63c && Z.ltb hb T63c)%bool then
        match c, tk with
        | BC_GEU, true | BC_LTU, false => [FRange (lsub a b) 0 ha]
        | BC_LTU, true | BC_GEU, false => [FRange (lsub b a) 1 hb]
        | _, _ => []
        end
      else []
  | _ => []
  end.
Definition hx_c2r (pc : Z) (X : xst) : option (list xst) :=
  let L := xs_st X in
  if Z.eqb (s_pc L) pc then Some [XST (SST (s_pc L) (s_regs L) (s_rgs L) (List.flat_map (c2r (s_facts L)) (s_facts L) ++ s_facts L) (s_next L) (s_resv L)) (xs_x X)]
  else None.
#[using="Type"] Lemma c2r_sound : forall E fs f, Forall (fact_ok E) fs -> fact_ok E f -> Forall (fact_ok E) (c2r fs f).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E fs f HF Hf. destruct f as [c a b tk|l lo hi|l k r|l m v|x' v' j'|xb bsb].
  2-6: apply Forall_nil.
  unfold c2r. cbv zeta.
  pose proof (irange_sound E fs a HF) as Ra. pose proof (irange_sound E fs b HF) as Rb.
  destruct (Z.ltb (snd (irange fs a)) T63c && Z.ltb (snd (irange fs b)) T63c)%bool eqn:Hs; [|apply Forall_nil].
  apply andb_prop in Hs as [Ha Hb]. apply Z.ltb_lt in Ha, Hb. cbn [fact_ok] in Hf. unfold branch_taken, bv_ltu in Hf.
  pose proof (u_range E a) as Ua. pose proof (u_range E b) as Ub. unfold T63c in *.
  destruct c; destruct tk.
  all: try apply Forall_nil.
  all: apply Forall_cons; [|apply Forall_nil]; cbn [fact_ok]; rewrite lden_lsub, bv_sub_unsigned; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 64) with two64; unfold two64 in *.
  all: destruct (Z.ltb_spec (bv_unsigned (lden E a)) (bv_unsigned (lden E b))) as [Hlt|Hge]; cbn in Hf; try discriminate; rewrite Z.mod_small by lia; lia.
Qed.
#[using="Type"] Theorem hx_c2r_okP : forall (Φ : machine_state -> machine_state -> Prop), (forall a, Φ a a) -> forall pc, hand_okxP segs xok Φ (hx_c2r pc).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros Φ HΦr pc X Ks E ms m0 Hf Hd HxF Hxw Hm0. destruct X as [L XL]. unfold hx_c2r in Hf. cbn [xs_st xs_x] in *.
  destruct (Z.eqb (s_pc L) pc) eqn:Hc; [|discriminate]. injection Hf as <-.
  eexists. exists ms, E. split; [left; reflexivity|]. split; [apply ist_refl|].
  cbn [xs_st xs_x s_pc s_regs s_rgs s_facts s_next s_resv].
  split; [|split; [intros x Hx; reflexivity|split; [intros; reflexivity|split; [reflexivity|split; [lia|split; [reflexivity|split; [exact HxF | split; [exact Hxw | apply HΦr]]]]]]]].
  intros E' Ha. pose proof (Hd E' Ha) as (Hpc0 & Hsvc0 & Hresv0 & HR0 & HG0 & HD0 & HF0 & Hfrm0).
  unfold sden0. cbn [s_pc s_regs s_rgs s_facts s_resv s_next].
  refine (conj Hpc0 (conj Hsvc0 (conj Hresv0 (conj HR0 (conj HG0 (conj HD0 (conj _ Hfrm0))))))).
  apply Forall_app. split; [|exact HF0].
  apply Forall_flat_map. rewrite Forall_forall in HF0 |- *. intros f Hf0. apply c2r_sound; [rewrite Forall_forall; exact HF0 | exact (HF0 f Hf0)].
Qed.
#[using="Type"] Theorem hx_c2r_ok : forall pc, hand_okx segs xok (hx_c2r pc).
Proof. LiaFast.lf_pins LiaFast.u0. intros pc. exact (hand_okxP_ok segs xok _ _ (hx_c2r_okP (fun _ _ => True) (fun _ => I) pc)). Qed.
#[using="Type"] Theorem hx_c2r_ok_fp : forall pc, hand_okx_fp segs xok (hx_c2r pc).
Proof. LiaFast.lf_pins LiaFast.u0. intros pc. exact (hx_c2r_okP fpeq fpeq_refl pc). Qed.
End HxC2R.

(* [comment removed for export] *)
Section HxPromote.
Variable segs : list Segment.
Variable xok : nat -> list word -> (word -> option byte) -> Prop.
Definition all_zero_tracked (R : region) : bool :=
  match is_const (rg_size R) with
  | Some n => (Z.leb 0 n && Z.leb n 64 &&
               forallb (fun j => match tget (okey (Z.of_nat j)) (rg_cont R) with Some (BK 0) => true | _ => false end) (seq 0 (Z.to_nat n)))%bool
  | None => false
  end.
Definition promote_rg (i : nat) (rgs : list region) : list region :=
  map_i (fun j R => if Nat.eqb j i then RG (rg_base R) (rg_size R) RZ (rg_cont R) else R) 0 rgs.
Definition hx_promote (pc : Z) (i : nat) (X : xst) : option (list xst) :=
  let L := xs_st X in
  match nth_error (s_rgs L) i with
  | Some R => if (Z.eqb (s_pc L) pc && match rg_kind R with RW => true | _ => false end && all_zero_tracked R)%bool
              then Some [XST (SST (s_pc L) (s_regs L) (promote_rg i (s_rgs L)) (s_facts L) (s_next L) (s_resv L)) (xs_x X)]
              else None
  | None => None
  end.
#[using="Type"] Lemma promote_nth : forall i rgs j R', nth_error (promote_rg i rgs) j = Some R' ->
  exists R, nth_error rgs j = Some R /\ R' = if Nat.eqb j i then RG (rg_base R) (rg_size R) RZ (rg_cont R) else R.
Proof. LiaFast.lf_pins LiaFast.u0. intros i rgs j R' H. unfold promote_rg in H. destruct (nth_map_i' _ _ _ _ H) as (R & HR & ->). exists R. split; [exact HR | reflexivity]. Qed.
#[using="Type"] Lemma promote_shape : forall i rgs, shape (promote_rg i rgs) = shape rgs.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros i rgs. unfold promote_rg, shape. generalize 0%nat. induction rgs as [|R rs IH]; intros k; [reflexivity|].
  cbn [map_i List.map]. rewrite IH. destruct (Nat.eqb k i); reflexivity.
Qed.
#[using="xok"] Lemma promote_rtm_k : forall rgs k i, (forall R, (k <= i)%nat -> nth_error rgs (i - k) = Some R -> rg_kind R = RW) ->
  List.map (fun R => is_rt (rg_kind R)) (map_i (fun j R => if Nat.eqb j i then RG (rg_base R) (rg_size R) RZ (rg_cont R) else R) k rgs)
  = List.map (fun R => is_rt (rg_kind R)) rgs.
Proof. LiaFast.lf_pins (fun (xok : LiaFast.U) => LiaFast.u0).
  induction rgs as [|R0 rs IH]; intros k i H; cbn [map_i List.map]; [reflexivity|]. f_equal.
  - destruct (Nat.eqb k i) eqn:E; [|reflexivity]. apply Nat.eqb_eq in E. subst k.
    rewrite (H R0 (le_n _)) by (rewrite Nat.sub_diag; reflexivity). reflexivity.
  - apply IH. intros R Hk HR. apply H; [lia|]. replace (i - k)%nat with (S (i - S k)) by lia. exact HR.
Qed.
#[using="xok"] Lemma promote_rtm : forall rgs i R, nth_error rgs i = Some R -> rg_kind R = RW -> rtm (promote_rg i rgs) = rtm rgs.
Proof. LiaFast.lf_pins (fun (xok : LiaFast.U) => LiaFast.u0).
  intros rgs i R HR Hk. unfold rtm, promote_rg. apply promote_rtm_k. intros R' _ HR'. rewrite Nat.sub_0_r in HR'.
  rewrite HR in HR'. injection HR' as <-. exact Hk.
Qed.
#[using="Type"] Theorem hx_promote_okP : forall (Φ : machine_state -> machine_state -> Prop), (forall a, Φ a a) -> forall pc i, hand_okxP segs xok Φ (hx_promote pc i).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros Φ HΦr pc i X Ks E ms m0 Hf Hd HxF Hxw Hm0. destruct X as [L XL]. unfold hx_promote in Hf. cbn [xs_st xs_x] in *.
  destruct (nth_error (s_rgs L) i) as [R|] eqn:HRi; [|discriminate].
  destruct (Z.eqb (s_pc L) pc && match rg_kind R with RW => true | _ => false end && all_zero_tracked R)%bool eqn:Hc; [|discriminate].
  injection Hf as <-.
  apply andb_prop in Hc as [Hc Hz]. apply andb_prop in Hc as [_ Hk].
  destruct (rg_kind R) eqn:EkR; try discriminate.
  unfold all_zero_tracked in Hz. destruct (is_const (rg_size R)) as [n|] eqn:Hn; [|discriminate].
  apply andb_prop in Hz as [Hz Hall]. apply andb_prop in Hz as [Hn0 Hn64]. apply Z.leb_le in Hn0, Hn64.
  rewrite forallb_forall in Hall.
  eexists. exists ms, E. split; [left; reflexivity|]. split; [apply ist_refl|].
  cbn [xs_st xs_x s_pc s_regs s_rgs s_facts s_next s_resv].
  split; [|split; [intros x Hx; reflexivity|split; [intros; reflexivity|split; [exact (promote_shape i (s_rgs L))|split; [lia|split; [exact (promote_rtm (s_rgs L) i R HRi EkR)|split; [exact HxF | split; [exact Hxw | apply HΦr]]]]]]]].
  intros E' Ha. pose proof (Hd E' Ha) as (Hpc0 & Hsvc0 & Hresv0 & HR0 & HG0 & HD0 & HF0 & Hfrm0).
  unfold sden0. cbn [s_pc s_regs s_rgs s_facts s_resv s_next].
  refine (conj Hpc0 (conj Hsvc0 (conj Hresv0 (conj HR0 (conj _ (conj _ (conj HF0 Hfrm0))))))).
  - apply Forall_nth'. intros j R' Hj. destruct (promote_nth i (s_rgs L) j R' Hj) as (R1 & HR1j & ->).
    rewrite Forall_nth' in HG0. destruct (Nat.eqb j i) eqn:Eji; [|exact (HG0 j R1 HR1j)].
    apply Nat.eqb_eq in Eji. subst j. rewrite HRi in HR1j. injection HR1j as <-.
    pose proof (HG0 i R HRi) as HRok. unfold rg_ok in HRok |- *. cbv zeta in HRok |- *. unfold rsz in *. cbn [rg_base rg_size rg_kind rg_cont].
    destruct HRok as (H1 & H2 & H3 & H4). refine (conj H1 (conj H2 (conj _ H4))).
    intros jj Hjj. pose proof (H3 jj Hjj) as X3. rewrite EkR in X3. split; [exact X3|].
    intros Hnone. exfalso.
    assert (Hsz : bv_unsigned (lden E' (rg_size R)) = n) by exact (is_const_u E' (rg_size R) n Hn).
    assert (Hj' : In (Z.to_nat jj) (seq 0 (Z.to_nat n))) by (apply in_seq; lia).
    pose proof (Hall _ Hj') as Hb. rewrite Z2Nat.id in Hb by lia. rewrite Hnone in Hb. discriminate.
  - apply rgs_disj_nth_inv. intros k k' R1 R2 Hkk H1 H2.
    destruct (promote_nth i _ k R1 H1) as (S1 & HS1 & ->). destruct (promote_nth i _ k' R2 H2) as (S2 & HS2 & ->).
    pose proof (rgs_disj_nth E' (s_rgs L) k k' S1 S2 HD0 ltac:(lia) HS1 HS2) as Hd12.
    destruct (Nat.eqb k i); destruct (Nat.eqb k' i); unfold rg_disj, rsz in *; cbn [rg_base rg_size] in *; exact Hd12.
Qed.
#[using="Type"] Theorem hx_promote_ok : forall pc i, hand_okx segs xok (hx_promote pc i).
Proof. LiaFast.lf_pins LiaFast.u0. intros pc i. exact (hand_okxP_ok segs xok _ _ (hx_promote_okP (fun _ _ => True) (fun _ => I) pc i)). Qed.
(* [comment removed for export] *)
#[using="Type"] Theorem hx_promote_ok_fp : forall pc i, hand_okx_fp segs xok (hx_promote pc i).
Proof. LiaFast.lf_pins LiaFast.u0. intros pc i. exact (hx_promote_okP fpeq fpeq_refl pc i). Qed.
End HxPromote.
