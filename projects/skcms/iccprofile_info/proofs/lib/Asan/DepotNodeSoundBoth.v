(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.skcms.iccprofile_info.images Require Import AsanUbsan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AxSymExec3B
  PropExec CatExec CatSim SeqExec StoreOk AgentLib AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound
  AsanPlanSoundSums KInvTable DepotInv DepotSymSeg DepotPutABoth DepotPutBoth SpinAlgCfg AsanPlanSoundCfg AsanPlanSoundSumsCfg DepotImgBoth DepotIntro DepotNodeBoth.
Unset Nia Cache.  (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS. Import APSX.
Open Scope Z_scope.
Unset Lia Cache.

Section WithFP. Context {FP : PropExec.FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma find_dinv_in : forall k K b17 b18,
  XDP.find_dinv k = Some (K, b17, b18) -> In (KInv 0 [ELit XDP.DEP_D; ELit XDP.DEP_SS; ELit K; b17; b18]) k.
Proof.
  induction k as [|K0 r IH]; intros K b17 b18 H; cbn [XDP.find_dinv] in H; [discriminate|].
  destruct K0 as [| | | | | | | | | |id args]; try (right; apply IH; exact H).
  destruct id as [|id']; [|right; apply IH; exact H].
  destruct args as [|d args]; [right; apply IH; exact H|]. destruct d as [d| | | | | | |]; try (right; apply IH; exact H).
  destruct args as [|ss args]; [right; apply IH; exact H|]. destruct ss as [ss| | | | | | |]; try (right; apply IH; exact H).
  destruct args as [|kk args]; [right; apply IH; exact H|]. destruct kk as [kk| | | | | | |]; try (right; apply IH; exact H).
  destruct args as [|e17 args]; [right; apply IH; exact H|]. destruct args as [|e18 args]; [right; apply IH; exact H|].
  destruct args as [|? ?]; [|right; apply IH; exact H].
  destruct (Z.eqb d XDP.DEP_D && Z.eqb ss XDP.DEP_SS)%bool eqn:Hc; [|right; apply IH; exact H].
  apply andb_prop in Hc as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst d ss.
  injection H as <- <- <-. left. reflexivity.
Qed.

Lemma has_rodata_sound : forall segs E M k,
  know_ok segs E M k -> XDP.has_rodata k = true ->
  forall i, 0x10000 <= i < 0x30000 -> M (Z_to_bv 64 i) = None.
Proof.
  intros segs E M k HK H i Hi. unfold XDP.has_rodata in H. apply existsb_exists in H as (K & Hin & HKb).
  destruct K as [| | | |lo hi| | | | | |]; try discriminate HKb.
  apply andb_prop in HKb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. unfold XDP.ROD_LO, XDP.ROD_HI in *.
  pose proof (proj1 (Forall_forall _ _) HK _ Hin) as HKK. cbn [kentry_ok] in HKK. destruct HKK as (_ & _ & HC).
  apply HC. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition inrb (a n : Z) (x : word) : bool := (Z.leb a (bv_unsigned x) && Z.ltb (bv_unsigned x) (a + n))%bool.

(* [comment removed for export] *)
Fixpoint mixm (rs : list (Z * Z)) (M M' : word -> option byte) : word -> option byte :=
  match rs with
  | [] => M
  | (a, n) :: rest => fun x => if inrb a n x then M' x else mixm rest M M' x
  end.

Lemma mixm_grows : forall rs M M', mem_grows M M' -> mem_grows M (mixm rs M M').
Proof.
  induction rs as [|[a n] rest IH]; intros M M' Hg; [apply mem_grows_refl|].
  intros x Hx. cbn [mixm]. destruct (inrb a n x); [exact (Hg x Hx) | exact (IH M M' Hg x Hx)].
Qed.

(* [comment removed for export] *)
Lemma mixm_step_out : forall rs a n M M' (x : word),
  bv_unsigned x < a \/ a + n <= bv_unsigned x -> mixm ((a, n) :: rs) M M' x = mixm rs M M' x.
Proof. intros rs a n M M' x Hx. cbn [mixm]. unfold inrb. destruct Hx; [rewrite (proj2 (Z.leb_gt _ _) H) | rewrite (proj2 (Z.ltb_ge _ _) H), andb_false_r]; reflexivity. Qed.

Lemma mixm_step_grows : forall rs a n M M', mem_grows M M' -> mem_grows (mixm rs M M') (mixm ((a, n) :: rs) M M').
Proof.
  intros rs a n M M' Hg x Hx. cbn [mixm]. destruct (inrb a n x) eqn:Hi; [|exact Hx].
  (* [comment removed for export] *)
  clear Hi. revert x Hx. induction rs as [|[b m] rest IH]; intros x Hx; [exact (Hg x Hx)|].
  cbn [mixm] in Hx. destruct (inrb b m x); [exact Hx | exact (IH x Hx)].
Qed.

Lemma mixm_full : forall rs M M' (x : word), existsb (fun r => inrb (fst r) (snd r) x) rs = true -> mixm rs M M' x = M' x.
Proof.
  induction rs as [|[a n] rest IH]; intros M M' x H; cbn [existsb] in H; [discriminate|].
  cbn [mixm fst snd] in *. destruct (inrb a n x); [reflexivity|]. cbn [orb] in H. exact (IH M M' x H).
Qed.

Lemma mixm_none : forall rs M M' (x : word), existsb (fun r => inrb (fst r) (snd r) x) rs = false -> mixm rs M M' x = M x.
Proof.
  induction rs as [|[a n] rest IH]; intros M M' x H; cbn [existsb] in H; [reflexivity|].
  cbn [mixm fst snd] in *. destruct (inrb a n x); [discriminate|]. cbn [orb] in H. exact (IH M M' x H).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Abbreviation SEGS := AsanUbsan.M.loaded_segments.

Section Sound.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Hypothesis SEGS_wx : AsanAcct.wx_segs_nowrap SEGS.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : hull_okP A.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Hypothesis NX0_sp : nx0_sp_ok nx0.
Variable FS0 : Fs.Fs.

(* [comment removed for export] *)
Local Ltac vm_refl_bv :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.
Definition W_RET : bv 32 := Z_to_bv 32 0x00008067.
Lemma F_RET : fetch_word SEGS (Z_to_bv 64 PUT_RET) = Some W_RET.
Proof. vm_refl_bv. Qed.
Lemma D_RET : decode_any W_RET = Some (Jalr 0%bv 1%bv 0%bv, 4%Z).
Proof. vm_refl_bv. Qed.

Lemma ret_step : forall (R : bvmap 5 word) (M : word -> option byte) (ret : Z),
  getr R (Z_to_bv 5 1) = Z_to_bv 64 ret -> Hoare.ret_ok (Z_to_bv 64 ret) ->
  msteps SEGS (mkst R (Z_to_bv 64 PUT_RET) M (seg_rom SEGS)) (mkst R (Z_to_bv 64 ret) M (seg_rom SEGS)).
Proof.
  intros R M ret H1 Hok. apply msteps_one; [reflexivity|].
  assert (H1' : getr R 1%bv = Z_to_bv 64 ret) by (rewrite <- H1; f_equal; apply bv_eq; reflexivity).
  rewrite (step_jalr_x0 SEGS R (Z_to_bv 64 PUT_RET) M (seg_rom SEGS) W_RET 1%bv 0%bv (Z_to_bv 64 ret) F_RET eq_refl D_RET H1').
  replace (bv_signed 0%bv) with 0 by reflexivity. unfold Hoare.ret_ok in Hok. rewrite Hok. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma kept_ok_of_KEPTI : forall R R' : bvmap 5 word,
  (forall i, In i KEPTI -> getr R' (Z_to_bv 5 (Z.of_nat i)) = getr R (Z_to_bv 5 (Z.of_nat i))) -> kept_ok R R'.
Proof.
  intros R R' H r Hr0 Hnc. rewrite (reg_of_ridx r (ridx r) eq_refl). apply H.
  pose proof (ridx_range r) as Hrr.
  assert (Hn0 : ridx r <> 0%nat).
  { intros E0. apply Hr0. rewrite (reg_of_ridx r 0%nat E0). apply bv_eq. reflexivity. }
  revert Hn0 Hnc Hrr. generalize (ridx r) as i. intros i Hn0 Hnc Hrr. clear r Hr0.
  assert (Hall : forallb (fun j => Nat.eqb j 0 || existsb (Nat.eqb j) caller_saved || existsb (Nat.eqb j) KEPTI)%bool (seq 0 32) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in Hall. specialize (Hall i ltac:(apply in_seq; lia)).
  apply orb_prop in Hall as [Hall|Hall]; [apply orb_prop in Hall as [Hall|Hall]|].
  - apply Nat.eqb_eq in Hall. contradiction.
  - exfalso. apply Hnc. apply existsb_exists in Hall as (x & Hx & E). apply Nat.eqb_eq in E. subst x. exact Hx.
  - apply existsb_exists in Hall as (x & Hx & E). apply Nat.eqb_eq in E. subst x. exact Hx.
Qed.

Lemma estart_lit0 : forall E z, 0 <= z < 2 ^ 64 -> estart E (SA (ELit 0) z) = z.
Proof. intros E z Hz. unfold estart. cbn [a_base a_off edenot]. rewrite u64_lit by lia. lia. Qed.
Lemma elenZ_lit' : forall E z, 0 <= z < 2 ^ 64 -> elenZ E (ELit z) = z.
Proof. intros E z Hz. unfold elenZ. cbn [edenot]. rewrite u64_lit by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma u_split : forall E e b k, split_lit e = (b, k) -> 0 <= estart E (SA b k) < 2 ^ 64 ->
  bv_unsigned (edenot E e) = estart E (SA b k).
Proof.
  intros E e b k Hs Hr. rewrite (split_lit_denot E e b k Hs). rewrite u64_lit; [reflexivity|]. unfold estart in Hr. cbn [a_base a_off] in Hr. lia.
Qed.

Theorem put_sound : APSC.node1_stmt_fp SEGS A nx0 LIMIT SINV argH FS0 FP APS.always (XDP.node_put nx0).
Proof.
  intros cs cs' E R FULL model T HC _ Hn Hk.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HKN.
  set (M := Mr A argH E cs model FULL) in *.
  unfold XDP.node_put in Hn. rewrite !kn_havocM_eq in Hn.   (* [comment removed for export] *)
  cbv zeta in Hn. rewrite ?AX2B.xloB_eqf, ?AX2B.xhiB_eqf, ?AX2B.ealignB_eqf, ?kwritable_xB_eqf, ?AX2B.ranges_apart_xB_eqf in Hn.   (* [comment removed for export] *)
  destruct (Z.eqb (pc cs) XDP.PUT_PC) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
  destruct (XDP.find_dinv (kn cs)) as [[[K b17e] b18e]|] eqn:Hfd; [|discriminate].
  destruct (ret_lit cs) as [ret|] eqn:Hret; [|discriminate].
  destruct (split_lit (reg cs 2)) as [sb sk] eqn:Hsps.
  destruct (split_lit (reg cs 10)) as [tb tk] eqn:Htrs.
  destruct (xlo (kn cs) (reg cs 2)) as [splo|] eqn:X1; [|discriminate].
  destruct (xhi (kn cs) (reg cs 2)) as [sphi|] eqn:X2; [|discriminate].
  destruct (xlo (kn cs) (reg cs 10)) as [trlo|] eqn:X3; [|discriminate].
  destruct (xhi (kn cs) (reg cs 10)) as [trhi|] eqn:X4; [|discriminate].
  destruct (xlo (kn cs) (reg cs 11)) as [slo|] eqn:X5; [|discriminate].
  destruct (xhi (kn cs) (reg cs 11)) as [shi|] eqn:X6; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  apply andb_prop in Hcond as [Hcond Hrod]. apply andb_prop in Hcond as [Hcond Ap18t]. apply andb_prop in Hcond as [Hcond Ap17t].
  apply andb_prop in Hcond as [Hcond Ap18s]. apply andb_prop in Hcond as [Hcond Ap17s]. apply andb_prop in Hcond as [Hcond Aptr].
  apply andb_prop in Hcond as [Hcond Wtr]. apply andb_prop in Hcond as [Hcond Wsp]. apply andb_prop in Hcond as [Hcond Altr].
  apply andb_prop in Hcond as [Hcond Alsp]. apply andb_prop in Hcond as [Hcond Cs2]. apply andb_prop in Hcond as [Hcond Cs1].
  apply andb_prop in Hcond as [Hcond Ctr2]. apply andb_prop in Hcond as [Hcond Ctr1]. apply andb_prop in Hcond as [Hcond Csp2].
  apply andb_prop in Hcond as [Hcond Csp1]. apply andb_prop in Hcond as [CK1 CK2].
  apply Z.leb_le in CK1. apply Z.ltb_lt in CK2. apply Z.leb_le in Csp1. apply Z.leb_le in Csp2. apply Z.leb_le in Ctr1.
  apply Z.leb_le in Ctr2. apply Z.leb_le in Cs1. apply Z.leb_le in Cs2. apply Z.leb_le in Alsp. apply Z.leb_le in Altr.
  unfold XDP.ACEILZ in *.
  (* [comment removed for export] *)
  pose proof (APSXC.w_reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 2 HC ltac:(lia)) as R2.
  pose proof (APSXC.w_reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 10 HC ltac:(lia)) as R10.
  pose proof (APSXC.w_reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 11 HC ltac:(lia)) as R11.
  destruct (APSXC.ret_lit_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model ret HC Hret) as (R1 & Hrok & Hrr).
  change (Z.of_nat 2) with 2 in R2. change (Z.of_nat 10) with 10 in R10. change (Z.of_nat 11) with 11 in R11.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN X1) as HX1. pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN X2) as HX2.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN X3) as HX3. pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN X4) as HX4.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN X5) as HX5. pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN X6) as HX6.
  set (sp := bv_unsigned (edenot E (reg cs 2))) in *. set (tr := bv_unsigned (edenot E (reg cs 10))) in *.
  set (s := bv_unsigned (edenot E (reg cs 11))) in *.
  (* [comment removed for export] *)
  destruct (kwritable_x_sound SEGS E M (kn cs) (kn cs) sb (sk - 272) (ELit 272) HKN HKN Wsp) as (Wst & W0 & W1).
  destruct (kwritable_x_sound SEGS E M (kn cs) (kn cs) tb tk (ELit 16) HKN HKN Wtr) as (Tst & T0 & T1).
  rewrite elenZ_lit' in W1, T1 by lia.
  assert (Esp : sp = estart E (SA sb sk)).
  { unfold estart in W0, W1 |- *. cbn [a_base a_off] in *.
    destruct (Z.eq_dec (bv_unsigned (edenot E sb) + sk) (2 ^ 64)) as [Heq|Hne].
    - exfalso. unfold sp in HX1. rewrite (split_lit_denot E (reg cs 2) sb sk Hsps), Heq in HX1. rewrite u_lit64 in HX1.
      unfold two64 in HX1. rewrite Z_mod_same_full in HX1. lia.
    - apply (u_split E (reg cs 2) sb sk Hsps). unfold estart. cbn [a_base a_off]. lia. }
  assert (Etr : tr = estart E (SA tb tk)).
  { apply (u_split E (reg cs 10) tb tk Htrs). unfold estart in T0, T1 |- *. cbn [a_base a_off] in *. lia. }
  assert (Efr : estart E (SA sb (sk - 272)) = sp - 272) by (rewrite Esp; unfold estart; cbn [a_base a_off]; lia).
  assert (Hframe : store_ok SEGS M (Z_to_bv 64 (sp - 272)) 272 = true) by (rewrite <- Efr; apply Wst; rewrite elenZ_lit' by lia; lia).
  assert (Htrok : store_ok SEGS M (Z_to_bv 64 tr) 16 = true) by (rewrite Etr; apply Tst; rewrite elenZ_lit' by lia; lia).
  (* [comment removed for export] *)
  assert (Hsp16 : sp mod 16 = 0).
  { destruct (ealign_sound SEGS E M (kn cs) (reg cs 2) HKN) as (EA & EB). apply Z.mod_divide; [lia|].
    eapply Z.divide_trans; [|exact EB]. exists (2 ^ (ealign (kn cs) (reg cs 2) - 4)).
    rewrite <- (Z.pow_add_r 2 _ 4) by lia. change 16 with (2 ^ 4). f_equal. lia. }
  assert (Htr8 : tr mod 8 = 0).
  { destruct (ealign_sound SEGS E M (kn cs) (reg cs 10) HKN) as (EA & EB). apply Z.mod_divide; [lia|].
    eapply Z.divide_trans; [|exact EB]. exists (2 ^ (ealign (kn cs) (reg cs 10) - 3)).
    rewrite <- (Z.pow_add_r 2 _ 3) by lia. change 8 with (2 ^ 3). f_equal. lia. }
  (* [comment removed for export] *)
  pose proof (ranges_apart_x_sound SEGS E M (kn cs) _ _ _ _ _ _ HKN Aptr) as Dtr.
  pose proof (ranges_apart_x_sound SEGS E M (kn cs) _ _ _ _ _ _ HKN Ap17s) as D17s.
  pose proof (ranges_apart_x_sound SEGS E M (kn cs) _ _ _ _ _ _ HKN Ap18s) as D18s.
  pose proof (ranges_apart_x_sound SEGS E M (kn cs) _ _ _ _ _ _ HKN Ap17t) as D17t.
  pose proof (ranges_apart_x_sound SEGS E M (kn cs) _ _ _ _ _ _ HKN Ap18t) as D18t.
  rewrite <- Etr, Efr in Dtr. rewrite Efr in D17s, D18s. rewrite <- Etr in D17t, D18t.
  rewrite !elenZ_lit' in Dtr, D17s, D18s, D17t, D18t by lia.
  set (b17 := bv_unsigned (edenot E b17e)) in *. set (b18 := bv_unsigned (edenot E b18e)) in *.
  assert (Es17 : estart E (SA b17e 0) = b17) by (unfold estart; cbn [a_base a_off]; lia).
  assert (Es18 : estart E (SA b18e 0) = b18) by (unfold estart; cbn [a_base a_off]; lia).
  rewrite Es17 in D17s, D17t. rewrite Es18 in D18s, D18t.
  (* [comment removed for export] *)
  pose proof (has_rodata_sound SEGS E M (kn cs) HKN Hrod) as Himg.
  pose proof (find_dinv_in _ _ _ _ Hfd) as HinI. pose proof (proj1 (Forall_forall _ _) HKN _ HinI) as HKI.
  cbn [kentry_ok inv_den edenot] in HKI. rewrite !u64_lit in HKI by (unfold XDP.DEP_D, XDP.DEP_SS; lia).
  fold b17 b18 in HKI. replace K with ((K - 1) + 1) in HKI by lia.
  (* [comment removed for export] *)
  assert (Hsprg : getr R (Z_to_bv 5 2) = Z_to_bv 64 sp) by (rewrite R2; unfold sp; rewrite Z_to_bv_bv_unsigned; reflexivity).
  assert (Htrrg : getr R (Z_to_bv 5 10) = Z_to_bv 64 tr) by (rewrite R10; unfold tr; rewrite Z_to_bv_bv_unsigned; reflexivity).
  assert (Hsrg : getr R (Z_to_bv 5 11) = Z_to_bv 64 s) by (rewrite R11; unfold s; rewrite Z_to_bv_bv_unsigned; reflexivity).
  destruct (as_depot_put R M (seg_rom SEGS) sp tr s (K - 1) b17 b18 Hsprg Hsp16 ltac:(unfold ACEILZ; lia) ltac:(lia) Htrrg Htr8
              ltac:(unfold ACEILZ; lia) ltac:(lia) Hsrg ltac:(lia) Hframe Htrok ltac:(lia) Himg ltac:(lia)
              ltac:(unfold disjZ; lia) ltac:(unfold disjZ, TCAP; lia) ltac:(unfold disjZ; lia) ltac:(unfold disjZ, TCAP; lia) HKI)
    as (R' & M' & id & Hms & Hkept & Ha0 & Hid & HI' & Hout & Hgr).
  (* [comment removed for export] *)
  eapply (APSXC.call_node_sound SEGS A nx0 LIMIT SEGS_wx SEGS_in_hull HULL_ok SINV argH argH_high argH_agree SINV_frame SINV_agree NX0_sp FS0
            cs cs' E R FULL model T ret None _ R' M' HC Hn).
  - rewrite Hpc. eapply msteps_trans; [exact Hms|]. apply ret_step; [|exact Hrok].
    pose proof (Hkept 1%nat ltac:(cbn; tauto)) as HK1. change (Z.of_nat 1) with 1 in HK1. rewrite HK1. exact R1.
  - apply kept_ok_of_KEPTI. exact Hkept.
  - exact I.
  - (* [comment removed for export] *)
    constructor.
    + cbn [kentry_ok inv_den edenot]. rewrite !u64_lit by (unfold XDP.DEP_D, XDP.DEP_SS; lia). exact HI'.
    + set (rs := [(b18, 4096); (b17, 1048576); (XDP.DEP_D, 0x400018); (XDP.DEP_SS, 32); (sp - 272, 272)]).
      assert (M5 : mixm rs M M' = M').
      { apply functional_extensionality. intros x.
        destruct (existsb (fun r => inrb (fst r) (snd r) x) rs) eqn:Hex; [apply mixm_full; exact Hex|].
        rewrite mixm_none by exact Hex. symmetry.
        assert (F : forall a n, inrb a n x = false -> bv_unsigned x < a \/ a + n <= bv_unsigned x).
        { intros a n H. unfold inrb in H. apply andb_false_iff in H as [H|H]; [apply Z.leb_gt in H | apply Z.ltb_ge in H]; lia. }
        subst rs. cbn [existsb fst snd] in Hex. rewrite !orb_false_iff in Hex. destruct Hex as (F18 & F17 & FD & FS & Ffr & _).
        apply F in F18, F17, FD, FS, Ffr.
        apply Hout; [lia|].
        intros C. unfold in_fp, depot_fp, TCAP in C. apply Exists_exists in C as (it & Hin & Hit).
        destruct Hin as [<- | [<- | [<- | [<- | []]]]]; cbn [fst snd] in Hit; unfold XDP.DEP_D, XDP.DEP_SS, D, SSA in *; lia. }
      rewrite <- M5. subst rs.
      apply (know_ok_havoc SEGS E (mixm [(b17, 1048576); (XDP.DEP_D, 0x400018); (XDP.DEP_SS, 32); (sp - 272, 272)] M M') _ _ b18e 0 (ELit 4096));
        [ | intros x Hx; rewrite Es18, elenZ_lit' in Hx by lia; apply mixm_step_out; exact Hx | apply mixm_step_grows; exact Hgr ].
      apply (know_ok_havoc SEGS E (mixm [(XDP.DEP_D, 0x400018); (XDP.DEP_SS, 32); (sp - 272, 272)] M M') _ _ b17e 0 (ELit 1048576));
        [ | intros x Hx; rewrite Es17, elenZ_lit' in Hx by lia; apply mixm_step_out; exact Hx | apply mixm_step_grows; exact Hgr ].
      apply (know_ok_havoc SEGS E (mixm [(XDP.DEP_SS, 32); (sp - 272, 272)] M M') _ _ (ELit 0) XDP.DEP_D (ELit 0x400018));
        [ | intros x Hx; rewrite estart_lit0, elenZ_lit' in Hx by (unfold XDP.DEP_D; lia); apply mixm_step_out; exact Hx
          | apply mixm_step_grows; exact Hgr ].
      apply (know_ok_havoc SEGS E (mixm [(sp - 272, 272)] M M') _ _ (ELit 0) XDP.DEP_SS (ELit 32));
        [ | intros x Hx; rewrite estart_lit0, elenZ_lit' in Hx by (unfold XDP.DEP_SS; lia); apply mixm_step_out; exact Hx
          | apply mixm_step_grows; exact Hgr ].
      apply (know_ok_havoc SEGS E (mixm [] M M') _ _ sb (sk - 272) (ELit 272));
        [ exact HKN | intros x Hx; rewrite Efr, elenZ_lit' in Hx by lia; apply mixm_step_out; exact Hx | apply mixm_step_grows; exact Hgr ].
  - exact Hk.
Qed.


(* [comment removed for export] *)
Theorem intro_sound : forall args, APSC.node1_stmt_fp SEGS A nx0 LIMIT SINV argH FS0 FP APS.always (XDP.xn_intro SEGS args).
Proof.
  intros args cs cs' E R FULL model T HC _ Hn Hk.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HKN.
  unfold XDP.xn_intro in Hn. destruct args as [|a rest]; [discriminate|]. destruct a as [K| | | | | | |]; try discriminate.
  destruct rest; [|discriminate].
  unfold XDP.node_intro in Hn.
  destruct (DIN.kreadE SEGS (kn cs) (ELit 0) (XDP.DEP_D + 0x400010) 8) as [e17|] eqn:He17; [|discriminate].
  destruct (DIN.kreadE SEGS (kn cs) (ELit 0) (XDP.DEP_SS + 16) 8) as [e18|] eqn:He18; [|discriminate].
  destruct (DIN.depot_intro_chk SEGS XDP.DEP_D XDP.DEP_SS K (kn cs)) eqn:Hchk; [|discriminate].
  injection Hn as <-.
  destruct (DIN.depot_intro_sound SEGS XDP.DEP_D XDP.DEP_SS E (Mr A argH E cs model FULL) (kn cs) K e17 e18
              img_byte_ok_d img_byte_ok_s HKN Hchk He17 He18) as (HK0 & HI).
  assert (HKb : K + 1 < 65535).
  { unfold DIN.depot_intro_chk in Hchk. rewrite He17, He18 in Hchk.
    destruct (DIN.kcellZ SEGS (kn cs) (XDP.DEP_D + 0x400000) 4); [|discriminate].
    destruct (DIN.kcellZ SEGS (kn cs) XDP.DEP_SS 8); [|discriminate].
    destruct (DIN.kcellZ SEGS (kn cs) (XDP.DEP_SS + 24) 4); [|discriminate].
    repeat match type of Hchk with (_ && _)%bool = true => apply andb_prop in Hchk as [Hchk ?X] end.
    match goal with X : Z.ltb (1 + K) 65535 = true |- _ => apply Z.ltb_lt in X; lia end. }
  apply (Hk E R FULL model); [split; apply env_agree_refl | | reflexivity].
  apply cs_ok_set_kn; [exact HC|]. constructor; [|exact HKN].
  cbn [kentry_ok inv_den edenot]. rewrite !u64_lit by (unfold XDP.DEP_D, XDP.DEP_SS; lia). exact HI.
Qed.

(* [comment removed for export] *)
Theorem xn_put_sound : forall args, APSC.node1_stmt_fp SEGS A nx0 LIMIT SINV argH FS0 FP APS.always (XDP.xn nx0 args).
Proof.
  intros [|a rest]; [exact put_sound|].
  intros cs cs' E R FULL model T HC _ Hn Hk. discriminate Hn.
Qed.

End Sound.
End WithFP.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section SoundCfg.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Hypothesis SEGS_wx : AsanAcct.wx_segs_nowrap SEGS.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : hull_okP A.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Hypothesis NX0_sp : nx0_sp_ok nx0.
Variable FS0 : Fs.Fs.
Variable FPS : PropExec.FPState -> Prop.

(* [comment removed for export] *)
Theorem xn_put_sound_cfg : forall args, APSC.node1_stmt_cfg SEGS A nx0 LIMIT SINV argH FS0 FPS APS.always (XDP.xn nx0 args).
Proof.
  intros args. apply APSC.node1_of_fp. intros FP _.
  exact (@xn_put_sound FP A nx0 LIMIT SEGS_wx SEGS_in_hull HULL_ok SINV argH argH_high argH_agree SINV_frame SINV_agree NX0_sp FS0 args).
Qed.

(* [comment removed for export] *)
Theorem xn_intro_sound_cfg : forall args, APSC.node1_stmt_cfg SEGS A nx0 LIMIT SINV argH FS0 FPS APS.always (XDP.xn_intro SEGS args).
Proof.
  intros args. apply APSC.node1_of_fp. intros FP _.
  eapply (@intro_sound FP); eassumption.
Qed.
End SoundCfg.
