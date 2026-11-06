(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon Require Import PropExec FastWord FastWordSem ShapeAlg ShapeAlgCfg AllocSim.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.BootWitness Require Import BootDefs BootStep.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import ExTrie.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AxLazy AxLin AxVal AxBytes AxMem AxZZ AxState AxEntryRel AxSys AxOcc AxAcct AxMeasure AxSysMmap AxGrant AsanWAcc AsanWLazy AxSysNode.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AxModelRel AxSysSound AxSysMmapS AxSys2.
Import ListNotations.

Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Lemma chk_brk (req : word) (eff : SyscallEffect) (m m' : Model) (evs : list event) :
  check_brk req eff m = CheckOk m' evs ->
  evs = [] /\ exists r, Mmap.brk_r_ok m req r = true
                        /\ eff = mkEffectU r [] (brk_zeros req r (vm_brk (m_vmmaps m))) (brk_unmaps r (vm_brk (m_vmmaps m))) [] []
                        /\ m' = with_brk_next m req r.
Proof.
  unfold check_brk. destruct eff as [r ws zs us cs ci]. destruct ws; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
  match goal with |- (if ?c then _ else _) = _ -> _ => destruct c eqn:Ec; [|discriminate] end.
  intros H. injection H as <- <-. split; [reflexivity|]. exists r.
  apply andb_prop in Ec as [Ec E3]. apply andb_prop in Ec as [E1 E2]. apply listNN_eqb_eq in E2. apply listNN_eqb_eq in E3. subst zs us.
  split; [exact E1 | split; reflexivity].
Qed.

Lemma chk_brk_ok (req r : word) (m : Model) :
  Mmap.brk_r_ok m req r = true ->
  check_brk req (mkEffectU r [] (brk_zeros req r (vm_brk (m_vmmaps m))) (brk_unmaps r (vm_brk (m_vmmaps m))) [] []) m
  = CheckOk (with_brk_next m req r) [].
Proof. intros H. unfold check_brk. rewrite H, !(proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity. Qed.

Lemma chk_brk_modeled (req : word) (eff : SyscallEffect) (m : Model) : check_brk req eff m <> CheckUnmodeled.
Proof.
  unfold check_brk. destruct eff as [r ws zs us cs ci]. destruct ws; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
  match goal with |- (if ?c then _ else _) <> _ => destruct c; discriminate end.
Qed.

(* [comment removed for export] *)
Lemma brk_query_r (m : Model) (req r : word) : w_is0 req = true -> Mmap.brk_r_ok m req r = true -> r = vm_brk (m_vmmaps m).
Proof. intros H0 H. unfold Mmap.brk_r_ok in H. rewrite H0 in H. cbn [orb] in H. apply bv_eqb_eq in H. exact H. Qed.

Lemma brk_query_ok (m : Model) (req : word) : w_is0 req = true -> Mmap.brk_r_ok m req (vm_brk (m_vmmaps m)) = true.
Proof. intros H0. unfold Mmap.brk_r_ok. rewrite H0. cbn [orb]. apply bv_eqb_refl. Qed.

(* [comment removed for export] *)
Lemma brk_grow_r (m : Model) (req r : word) :
  w_is0 req = false -> bv_unsigned (min_brk (m_vmmaps m)) <= bv_unsigned req ->
  bv_unsigned (vm_brk (m_vmmaps m)) < bv_unsigned req -> Mmap.brk_r_ok m req r = true ->
  (r = req /\ Mmap.brk_grow_ok m req req = true) \/ r = vm_brk (m_vmmaps m).
Proof.
  intros H0 Hmin Hlt H. unfold Mmap.brk_r_ok in H. rewrite H0 in H. cbn [orb] in H.
  rewrite (proj2 (Z.ltb_ge _ _) Hmin) in H. rewrite (proj2 (Z.ltb_ge _ _)) in H by lia.
  apply andb_prop in H as [H1 H2]. apply orb_prop in H1 as [H1|H1]; apply bv_eqb_eq in H1; subst r; [left | right]; auto.
Qed.

Lemma brk_keep_ok (m : Model) (req : word) :
  w_is0 req = false -> bv_unsigned (min_brk (m_vmmaps m)) <= bv_unsigned req ->
  bv_unsigned (vm_brk (m_vmmaps m)) < bv_unsigned req -> Mmap.brk_r_ok m req (vm_brk (m_vmmaps m)) = true.
Proof.
  intros H0 Hmin Hlt. unfold Mmap.brk_r_ok. rewrite H0. cbn [orb].
  rewrite (proj2 (Z.ltb_ge _ _) Hmin). rewrite (proj2 (Z.ltb_ge _ _)) by lia.
  rewrite bv_eqb_refl, orb_true_r. cbn [andb]. unfold Mmap.brk_grow_ok. rewrite Z.ltb_irrefl, andb_false_r. reflexivity.
Qed.

Lemma brk_grow_ok_r (m : Model) (req : word) :
  w_is0 req = false -> bv_unsigned (min_brk (m_vmmaps m)) <= bv_unsigned req ->
  bv_unsigned (vm_brk (m_vmmaps m)) < bv_unsigned req -> Mmap.brk_grow_ok m req req = true -> Mmap.brk_r_ok m req req = true.
Proof.
  intros H0 Hmin Hlt Hg. unfold Mmap.brk_r_ok. rewrite H0. cbn [orb].
  rewrite (proj2 (Z.ltb_ge _ _) Hmin). rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite bv_eqb_refl, Hg. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma with_brk_keep (m : Model) (req : word) : with_brk_next m req (vm_brk (m_vmmaps m)) = m.
Proof.
  unfold with_brk_next, brk_model_next, brk_maps_next. rewrite brk_unmaps_keep, brk_grants_keep.
  rewrite Z.ltb_irrefl, andb_false_r. cbn [forget_vm_ranges maps_subtract_ranges fold_left app].
  destruct m as [fd [[res maps na sb b lim mb sp] lazy mat] io fs proc lm tm]. reflexivity.
Qed.

(* [comment removed for export] *)
Definition brk_grow_maps (m : Model) (req : word) : VmMaps :=
  let h := m_vmmaps m in
  mkVmMapsFull (vm_reserved h) ((vm_brk h, req - vm_brk h)%bv :: vm_maps h) (vm_noaccess h) (vm_start_brk h) req (vm_limit h)
    (vm_mmap_base h) (vm_init_sp h).

Lemma with_brk_grow (m : Model) (req : word) :
  w_is0 req = false -> 0 < bv_unsigned (vm_brk (m_vmmaps m)) -> bv_unsigned (vm_brk (m_vmmaps m)) < bv_unsigned req ->
  with_brk_next m req req = with_vmmaps (brk_grow_maps m req) m.
Proof.
  intros H0 Hb Hlt. unfold with_brk_next, brk_model_next, brk_maps_next, brk_grow_maps.
  assert (Hne : req <> Z_to_bv 64 0) by (intros ->; unfold w_is0 in H0; rewrite bv_eqb_refl in H0; discriminate H0).
  rewrite (brk_unmaps_grow req (vm_brk (m_vmmaps m))) by lia. rewrite (brk_grants_grow req req _ Hne Hb Hlt).
  rewrite (proj2 (Z.ltb_ge (bv_unsigned req) _)) by lia. rewrite andb_false_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma brk_gate_aligned (m : Model) (req : word) :
  0 < bv_unsigned (vm_brk (m_vmmaps m)) -> bv_unsigned (vm_brk (m_vmmaps m)) < bv_unsigned req ->
  bv_unsigned (vm_brk (m_vmmaps m)) mod page_size = 0 -> bv_unsigned req mod page_size = 0 ->
  Mmap.brk_grow_ok m req req =
  (bv_unsigned req <=? alloc_top (m_vmmaps m))
  && region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) (vm_brk (m_vmmaps m))
       (Z_to_bv 64 (bv_unsigned req + page_size - bv_unsigned (vm_brk (m_vmmaps m))))
  && brk_budget_ok m req.
Proof.
  intros Hb Hlt Ha1 Ha2. unfold Mmap.brk_grow_ok. cbv zeta.
  rewrite (proj2 (Z.ltb_lt _ _) Hb), (proj2 (Z.ltb_lt _ _) Hlt). cbn [andb].
  rewrite (page_round_up_Z_aligned (bv_unsigned (vm_brk (m_vmmaps m))) ltac:(lia) Ha1), (page_round_up_Z_aligned (bv_unsigned req) ltac:(lia) Ha2).
  rewrite (proj2 (Z.ltb_lt _ _) Hlt). rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma brk_zeros_aligned (req old : word) :
  w_is0 req = false -> 0 < bv_unsigned old -> bv_unsigned old < bv_unsigned req ->
  bv_unsigned old mod page_size = 0 -> bv_unsigned req mod page_size = 0 ->
  brk_zeros req req old = [(old, Z_to_bv 64 (bv_unsigned req - bv_unsigned old))].
Proof.
  intros H0 Hb Hlt Ha1 Ha2.
  assert (Hne : req <> Z_to_bv 64 0) by (intros ->; unfold w_is0 in H0; rewrite bv_eqb_refl in H0; discriminate H0).
  rewrite (brk_zeros_grow req req old Hne Hb Hlt).
  rewrite (page_round_up_Z_aligned (bv_unsigned old) ltac:(lia) Ha1), (page_round_up_Z_aligned (bv_unsigned req) ltac:(lia) Ha2).
  unfold brk_page_range. rewrite (proj2 (Z.ltb_lt _ _) Hlt), Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma sub_unsigned (req old : word) : bv_unsigned old <= bv_unsigned req -> bv_unsigned (req - old)%bv = bv_unsigned req - bv_unsigned old.
Proof.
  intros H. rewrite bv_sub_unsigned. apply bv_wrap_small.
  pose proof (bv_unsigned_in_range 64 req). pose proof (bv_unsigned_in_range 64 old). lia.
Qed.

(* [comment removed for export] *)
Lemma brk_refusal_query (m : Model) (req ret : word) : w_is0 req = true -> brk_refusal_b m req ret = false.
Proof. intros H. unfold brk_refusal_b. rewrite H. reflexivity. Qed.

Lemma brk_refusal_grow (m : Model) (req : word) :
  bv_unsigned (vm_brk (m_vmmaps m)) < bv_unsigned req -> brk_refusal_b m req req = false.
Proof.
  intros Hlt. unfold brk_refusal_b. cbv zeta.
  assert (E : bv_eqb req (vm_brk (m_vmmaps m)) = false).
  { destruct (bv_eqb req (vm_brk (m_vmmaps m))) eqn:E; [|reflexivity]. apply bv_eqb_eq in E. rewrite E in Hlt. lia. }
  rewrite E. cbn [negb]. rewrite andb_false_r. reflexivity.
Qed.

Lemma brk_refusal_keep (m : Model) (req : word) :
  w_is0 req = false -> bv_unsigned (min_brk (m_vmmaps m)) <= bv_unsigned req ->
  bv_unsigned (vm_brk (m_vmmaps m)) < bv_unsigned req -> brk_refusal_b m req (vm_brk (m_vmmaps m)) = true.
Proof.
  intros H0 Hmin Hlt. unfold brk_refusal_b. cbv zeta. rewrite H0, (proj2 (Z.ltb_ge _ _) Hmin), bv_eqb_refl. cbn [negb andb].
  assert (E : bv_eqb req (vm_brk (m_vmmaps m)) = false).
  { destruct (bv_eqb req (vm_brk (m_vmmaps m))) eqn:E; [|reflexivity]. apply bv_eqb_eq in E. rewrite E in Hlt. lia. }
  rewrite E. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma region_free_shrink (l : list (word * word)) (a n1 n2 : word) :
  bv_unsigned n2 <= bv_unsigned n1 -> region_free l a n1 = true -> region_free l a n2 = true.
Proof.
  intros Hle H. apply region_free_disj. intros q Hq. pose proof (proj1 (region_free_disj l a n1) H q Hq) as D. unfold iv_disj in *. lia.
Qed.

Section Main.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Hypothesis Hcfg2 : sc_alloc cfg = false.
Variable LIM : Z.
Variable fs0 : Fs.Fs.
Variable KT : valuation -> list byte -> TSet.
Hypothesis Hlow : segs_low segs.

Notation MRm := (MR segs fs0).
Notation RR ρ := (R segs amodel (MRm ρ) LIM ρ).
Notation Snd B := (forall ρ c, RR ρ B c -> forall o, out_val ρ B o -> realizes_cfg segs cfg c (KT ρ o)).

Lemma is_zero_form_eq (f : lin) : is_zero_form f = true -> f = (0, []).
Proof.
  destruct f as [c ts]. unfold is_zero_form. cbn [fst snd]. intros H. apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1.
  destruct ts; [subst; reflexivity | discriminate H2].
Qed.

Theorem sys_brk2_sound (A : AST) (l : list AST) :
  pc_ok (npc A) = true -> xlit (aget (a_regs A) 17%uint63) = Some 214 ->
  sys_brk2 A = Some l -> (forall B, In B l -> Snd B) ->
  forall ρ c, RR ρ A c -> (exists w, fetch_word segs (ms_pc_val (cfg_ms c)) = Some w /\ is_ecall w = true) ->
  forall o, out_val ρ A o -> realizes_cfg segs cfg c (KT ρ o).
Proof.
  intros Hpc H17x Hs HS ρ [ms model] HR [w [Hf He]] o Ho. cbn [cfg_ms] in Hf.
  pose proof HR as [Hpc0 Hal Hsvc Hregs Hres Hrom Hmem HM Hh [Hb Hl] Hsat Hhs Hcov Hcomp Hna]. cbn [cfg_ms cfg_model] in *.
  assert (H17 : bv_unsigned (rg ms (Z_to_bv 5 17)) = 214) by exact (reg_lit ρ _ ms (Z_to_bv 5 17) 17%uint63 214 Hregs eq_refl H17x).
  set (x8 := rg ms (Z_to_bv 5 17)) in *. set (req := rg ms (Z_to_bv 5 10)).
  set (old := vm_brk (m_vmmaps model)).
  assert (Hold : bv_unsigned old = leval ρ (am_brk (a_model A))) by exact (mr_brk segs fs0 ρ _ _ HM).
  assert (Hchk : forall eff m0, check_syscall (sys_input segs (latch ms) x8) eff m0 = check_brk req eff m0)
    by (intros eff m0; exact (check_syscall_214 segs (latch ms) x8 eff m0 H17)).
  assert (Hrb : forall r0, refusal_b (sys_input segs (latch ms) x8) model r0 = brk_refusal_b model req r0)
    by (intros r0; exact (refusal_b_214 segs (latch ms) x8 model r0 H17)).
  assert (Hoffm : injected_family_off cfg (sys_input segs (latch ms) x8) = true).
  { apply family_off_alloc; [exact Hcfg2 | rewrite H17; cbn; tauto | rewrite H17; lia]. }
  (* [comment removed for export] *)
  assert (Hkeep : forall B, a_pc B = npc A -> a_regs B = aset (a_regs A) reg_a0 (of_form (am_brk (a_model A))) -> a_resv B = a_resv A ->
            a_mem B = a_mem A -> a_facts B = a_facts A -> a_model B = a_model A -> a_budget B = a_budget A -> Snd B ->
            realizes_cfg segs cfg (mkCfg (advance_past_svc (apply_effect (latch ms) (mkEffect old [] []))) model) (KT ρ o)).
  { intros B E1 E2 E3 E4 E5 E6 E7 HB. refine (HB ρ _ _ o _); [|unfold out_val in *; rewrite E6; exact Ho].
    apply (R_reg_sys segs LIM fs0 ρ A B ms model model old (of_form (am_brk (a_model A))) HR); try assumption; try reflexivity.
    - apply of_form_sound. rewrite <- Hold. symmetry. apply Z.mod_small. pose proof (bv_unsigned_in_range 64 old) as X. exact X.
    - rewrite E5. exact Hsat.
    - rewrite E6. exact HM.
    - rewrite E7. exact Hb. }
  unfold sys_brk2 in Hs. cbv zeta in Hs.
  destruct (xform (a_facts A) (aget (a_regs A) 10%uint63)) as [f|] eqn:Ef; [|discriminate Hs].
  pose proof (xform_sound ρ _ _ req f Hsat (Hregs (Z_to_bv 5 10)) Ef) as Hreq.
  apply (rzc_latch segs cfg ms model w _ Hh Hsvc Hf He).
  destruct (is_zero_form f) eqn:Ez.
  - (* [comment removed for export] *)
    apply is_zero_form_eq in Ez. subst f. change (leval ρ (0, [])) with 0 in Hreq.
    assert (Hr0 : w_is0 req = true).
    { unfold w_is0. apply bv_eqb_eq. apply bv_eq. rewrite Hreq. reflexivity. }
    destruct (lrange (a_facts A) (am_brk (a_model A))) as [[blo bhi]|] eqn:Eb; [|discriminate Hs].
    match type of Hs with (if ?c then _ else _) = _ => destruct c; [|discriminate Hs] end. injection Hs as <-.
    apply (rzc_sys_silent segs cfg (latch ms) model x8 (KT ρ o) Hh eq_refl).
    + rewrite Hchk. apply chk_brk_modeled.
    + intros eff m' evs Hc. rewrite Hchk in Hc. destruct (chk_brk req eff model m' evs Hc) as [-> [r0 [Hr [-> ->]]]].
      split; [reflexivity|]. rewrite (brk_query_r model req r0 Hr0 Hr). rewrite with_brk_keep. exact Hh.
    + exists (mkEffectU old [] (brk_zeros req old old) (brk_unmaps old old) [] []), (with_brk_next model req old). split.
      * rewrite Hchk. apply chk_brk_ok. apply brk_query_ok. exact Hr0.
      * rewrite Hrb. apply brk_refusal_query. exact Hr0.
    + intros eff m' Hc _. rewrite Hchk in Hc. destruct (chk_brk req eff model m' [] Hc) as [_ [r0 [Hr [-> ->]]]].
      rewrite (brk_query_r model req r0 Hr0 Hr). fold old. rewrite with_brk_keep, brk_zeros_keep, brk_unmaps_keep.
      exists model. split; [apply materialize_nil|].
      apply (Hkeep (with_model A (npc A) (aset (a_regs A) reg_a0 (of_form (am_brk (a_model A)))) (a_mem A) (a_facts A) (a_model A) (a_budget A)));
        try reflexivity. exact (HS _ (or_introl eq_refl)).
  - (* [comment removed for export] *)
    destruct (snd (lsub f (am_brk (a_model A)))) as [|t0 tr] eqn:Ed; [|discriminate Hs].
    set (d := fst (lsub f (am_brk (a_model A)))) in *.
    destruct (brk_grow_guard A (am_brk (a_model A)) d) eqn:Eg; [|discriminate Hs]. injection Hs as <-.
    unfold brk_grow_guard in Eg. cbv zeta in Eg.
    apply andb_prop in Eg as [Eg Gpos]. apply andb_prop in Eg as [Eg Gwit]. apply andb_prop in Eg as [Eg Geb]. apply andb_prop in Eg as [Eg Gsh].
    apply andb_prop in Eg as [Eg Grng]. apply andb_prop in Eg as [Eg Gc2]. apply andb_prop in Eg as [Eg Gc1]. apply andb_prop in Eg as [Eg Gal].
    apply andb_prop in Eg as [Eg Gd3]. apply andb_prop in Eg as [Gd1 Gd2].
    apply Z.ltb_lt in Gd1. apply Z.ltb_lt in Gd2. apply Z.eqb_eq in Gd3. apply Z.leb_le in Gc1. apply Z.ltb_lt in Gc2.
    destruct (lrange (a_facts A) (am_brk (a_model A))) as [[blo bhi]|] eqn:Eb; [|discriminate Grng].
    destruct (lrange (a_facts A) (lsub (am_brk (a_model A)) (am_brk0 (a_model A)))) as [[dlo dhi]|] eqn:Eb0; [|discriminate Grng].
    apply andb_prop in Grng as [Grng G3]. apply andb_prop in Grng as [G1 G2]. apply Z.ltb_lt in G1. apply Z.ltb_lt in G2. apply Z.leb_le in G3.
    pose proof (lrange_sound ρ _ _ Hsat _ Eb) as Rb. cbn [fst snd] in Rb.
    pose proof (lrange_sound ρ _ _ Hsat _ Eb0) as Rb0. cbn [fst snd] in Rb0. rewrite leval_lsub in Rb0.
    assert (Hdl : leval ρ f - leval ρ (am_brk (a_model A)) = d).
    { rewrite <- leval_lsub. unfold leval. rewrite Ed. cbn [teval]. unfold d. lia. }
    pose proof (mr_brk0 segs fs0 ρ _ _ HM) as Hb0.
    pose proof (lin_al_sound ρ 4096 _ ltac:(lia) Gal) as Hal_b.
    (* [comment removed for export] *)
    assert (Ao : 0 < bv_unsigned old) by (clear - Hold Rb G1; lia).
    assert (Ad : bv_unsigned req = bv_unsigned old + d) by (clear - Hold Hreq Hdl; lia).
    assert (Am : bv_unsigned (vm_start_brk (m_vmmaps model)) <= bv_unsigned old) by (clear - Hold Hb0 Rb0 G3; lia).
    assert (A47 : bv_unsigned old + d + 4096 < 140737488355328) by (clear - Hold Rb G2; lia).
    assert (Hr0 : w_is0 req = false).
    { unfold w_is0. destruct (bv_eqb req (Z_to_bv 64 0)) eqn:E; [|reflexivity]. apply bv_eqb_eq in E. rewrite E in Ad.
      change (bv_unsigned (Z_to_bv 64 0)) with 0 in Ad. clear - Ad Ao Gd1. lia. }
    assert (Hmin : bv_unsigned (min_brk (m_vmmaps model)) <= bv_unsigned req) by (unfold min_brk; clear - Am Ad Gd1; lia).
    assert (Hlt : bv_unsigned (vm_brk (m_vmmaps model)) < bv_unsigned req) by (fold old; clear - Ad Gd1; lia).
    assert (Hal_o : bv_unsigned old mod page_size = 0) by (unfold page_size; rewrite Hold; exact Hal_b).
    assert (Hal_r : bv_unsigned req mod page_size = 0).
    { unfold page_size in *. rewrite Ad. rewrite Z.add_mod, Hal_o, Gd3 by (clear; lia). reflexivity. }
    assert (Hdz : bv_unsigned (req - old)%bv = d) by (rewrite sub_unsigned by (clear - Ad Gd1; lia); clear - Ad; lia).
    assert (Hsubw : (req - old)%bv = Z_to_bv 64 d) by (apply bv_eq; rewrite Hdz, u_Z_to_bv; [reflexivity | unfold two64; clear - Gd1 Gd2; lia]).
    assert (Hold0 : 0 < bv_unsigned (vm_brk (m_vmmaps model))) by (fold old; exact Ao).
    destruct (Mmap.brk_grow_ok model req req) eqn:Egrow.
    + (* [comment removed for export] *)
      pose proof Egrow as Egate. rewrite (brk_gate_aligned model req Hold0 Hlt Hal_o Hal_r) in Egate.
      apply andb_prop in Egate as [Egate Gbud]. apply andb_prop in Egate as [Gtop Gfree]. apply Z.leb_le in Gtop. fold old in Gfree.
      assert (Hnull : null_ok model d old).
      { split; [exact Hal_o|]. split; [exact Ao|]. split; [clear - Gtop Ad; lia|].
        apply (region_free_shrink _ old (Z_to_bv 64 (bv_unsigned req + page_size - bv_unsigned old))); [|exact Gfree].
        unfold page_size. rewrite !u_Z_to_bv by (unfold two64; clear - Ad Ao Gd1 Gd2 A47; lia). clear - Ad; lia. }
      apply (rzc_sys_silent segs cfg (latch ms) model x8 (KT ρ o) Hh eq_refl).
      * rewrite Hchk. apply chk_brk_modeled.
      * intros eff m' evs Hc. rewrite Hchk in Hc. destruct (chk_brk req eff model m' evs Hc) as [-> [r0 [Hr [-> ->]]]].
        split; [reflexivity|]. destruct (brk_grow_r model req r0 Hr0 Hmin Hlt Hr) as [[-> _]| ->].
        -- rewrite (with_brk_grow model req Hr0 Hold0 Hlt). exact Hh.
        -- rewrite with_brk_keep. exact Hh.
      * exists (mkEffectU req [] (brk_zeros req req old) (brk_unmaps req old) [] []), (with_brk_next model req req). split.
        -- rewrite Hchk. apply chk_brk_ok. apply brk_grow_ok_r; assumption.
        -- rewrite Hrb. apply brk_refusal_grow. exact Hlt.
      * intros eff m' Hc Hnr. specialize (Hnr Hoffm). rewrite Hrb in Hnr. rewrite Hchk in Hc.
        destruct (chk_brk req eff model m' [] Hc) as [_ [r0 [Hr [-> ->]]]]. cbn [eff_ret] in Hnr.
        destruct (brk_grow_r model req r0 Hr0 Hmin Hlt Hr) as [[-> _]| ->]; [|rewrite (brk_refusal_keep model req Hr0 Hmin Hlt) in Hnr; discriminate Hnr].
        fold old. rewrite (with_brk_grow model req Hr0 Hold0 Hlt).
        assert (Hle : bv_unsigned old <= bv_unsigned req) by (clear - Ad Gd1; lia).
        rewrite (brk_zeros_aligned req old Hr0 Ao Hlt Hal_o Hal_r), (brk_unmaps_grow req old Hle).
        replace (bv_unsigned req - bv_unsigned old) with d by (clear - Ad; lia).
        exists (with_vmmaps (brk_grow_maps model req) model). split; [apply materialize_nil|].
        rewrite adv_effect, eff_mem_zeros. cbn [eff_ret].
        refine (HS _ (or_introl eq_refl) ρ _ _ o Ho).
        assert (Hb63 : 0 <= fst (am_brk (a_model A)) < 9223372036854775808) by (clear - Gc1 Gc2; lia).
        assert (Hgm : vm_maps (brk_grow_maps model req) = (old, Z_to_bv 64 d) :: vm_maps (m_vmmaps model)) by (unfold brk_grow_maps; cbn [vm_maps]; fold old; rewrite Hsubw; reflexivity).
        apply andb_prop in Gwit as [W1 W2].
        assert (Hd47 : 0 < d < 2 ^ 47) by (clear - Gd1 Gd2; lia).
        assert (Hposr : forall R0, In R0 (a_mem A) -> 0 < to_Z (rg_n R0)) by (intros R0 HIn; apply Z.ltb_lt; exact (lforall_forall _ _ Gpos R0 HIn)).
        apply (R_grant_rw_gen segs LIM fs0 Hlow ρ A ms model old d HR Hpc Hd47 Gd3 Hnull Gsh Geb Hposr
                 (snd (am_brk (a_model A))) (wofZ (fst (am_brk (a_model A)))) (of_form f) req (a_facts A) _ _ (a_budget A + d)).
        -- unfold smod. rewrite wZ_wofZ, Zplus_mod_idemp_r. rewrite Hold. unfold leval. rewrite Z.mod_small; [clear; lia|].
           pose proof (bv_unsigned_in_range 64 old) as X. change (bv_modulus 64) with two64 in X. unfold leval in Hold. clear - X Hold. lia.
        -- rewrite (wS_wofZ_small _ Hb63), Hold. unfold leval. clear. lia.
        -- exact (lin_al_tdiv8 _ Gal).
        -- rewrite (wS_wofZ_small _ Hb63). unfold lin_al in Gal. apply andb_prop in Gal as [X _]. apply Z.eqb_eq in X.
           pose proof (Z.div_mod (fst (am_brk (a_model A))) 4096 ltac:(clear; lia)) as D. rewrite X in D. rewrite D, Z.add_0_r.
           replace (4096 * (fst (am_brk (a_model A)) / 4096)) with (512 * (fst (am_brk (a_model A)) / 4096) * 8) by (clear; lia). apply Z_mod_mult.
        -- apply of_form_sound. rewrite Hreq. symmetry. apply Z.mod_small. rewrite <- Hreq. pose proof (bv_unsigned_in_range 64 req) as X. exact X.
        -- exact Hsat.
        -- assert (Hsp0 : bv_unsigned old + d <= sh_lo \/ sh_hi <= bv_unsigned old).
           { destruct Hnull as (_ & _ & N3 & N4). rewrite region_free_app in N4. apply andb_prop in N4 as [_ N4].
             pose proof (alloc_top_lt (m_vmmaps model)) as At. change two_pow_64 with two64 in At.
             exact (MR_free_span segs fs0 ρ _ model old d HM (proj1 Hd47) ltac:(clear - N3 At; lia) N4 Gsh). }
           assert (Hspan : am_shadow (a_model A) = true -> var_ent (AE (am_brk (a_model A)) d false) = true ->
                             bv_unsigned old + d <= sh_lo \/ sh_hi <= bv_unsigned old) by (intros _ _; exact Hsp0).
           (* [comment removed for export] *)
           assert (Hnfull : AxLz.lzfull (AE (am_brk (a_model A)) d false) = false).
           { destruct (AxLz.lzfull (AE (am_brk (a_model A)) d false)) eqn:Efl; [|reflexivity]. exfalso.
             destruct (AxLz.lzfull_in_span ρ _ Efl) as [S1 S2]. cbn [ae_base ae_size] in S1, S2. rewrite <- Hold in S1, S2.
             clear - S1 S2 Hsp0 Hd47. lia. }
           exact (MR_brk_grow segs fs0 ρ (a_model A) model HM (AE (am_brk (a_model A)) d false) old d (am_next (a_model A))
                    (eq_sym Hold) eq_refl (proj1 Hd47) Hnull Hspan (brk_grow_maps model req) f eq_refl Hnfull eq_refl Hgm eq_refl eq_refl eq_refl Hreq).
        -- exact Hgm.
        -- reflexivity.
        -- reflexivity.
        -- reflexivity.
        -- reflexivity.
        -- pose proof (used_cons_eager model old (Z_to_bv 64 d) (brk_grow_maps model req) Hgm eq_refl) as X.
           rewrite u_Z_to_bv in X by (unfold two64; clear - Hd47; lia). clear - X Hb. lia.
        -- exact W1.
        -- exact W2.
    + (* [comment removed for export] *)
      assert (Hall : forall eff m' evs, check_brk req eff model = CheckOk m' evs ->
                evs = [] /\ eff = mkEffect old [] [] /\ m' = model).
      { intros eff m' evs Hc. destruct (chk_brk req eff model m' evs Hc) as [-> [r0 [Hr [-> ->]]]]. split; [reflexivity|].
        destruct (brk_grow_r model req r0 Hr0 Hmin Hlt Hr) as [[_ X]| ->]; [rewrite X in Egrow; discriminate Egrow|].
        fold old. rewrite with_brk_keep, brk_zeros_keep, brk_unmaps_keep. split; reflexivity. }
      assert (Hkeep_ok : check_brk req (mkEffect old [] []) model = CheckOk model []).
      { pose proof (chk_brk_ok req old model (brk_keep_ok model req Hr0 Hmin Hlt)) as X. fold old in X.
        rewrite with_brk_keep, brk_zeros_keep, brk_unmaps_keep in X. exact X. }
      assert (Hforced : forall eff, ~ spurious_refusal_cfg cfg (sys_input segs (latch ms) x8) model eff).
      { intros eff. apply forced_not_spurious. intros eff' m' evs' Hc. rewrite Hchk in Hc. destruct (Hall _ _ _ Hc) as (_ & -> & _).
        rewrite Hrb. exact (brk_refusal_keep model req Hr0 Hmin Hlt). }
      apply (rzc_chk_silent segs cfg (latch ms) model x8 (KT ρ o) Hh eq_refl).
      * rewrite Hchk. apply chk_brk_modeled.
      * intros eff m' evs Hc. rewrite Hchk in Hc. destruct (Hall _ _ _ Hc) as (-> & _ & ->). split; [reflexivity | exact Hh].
      * exists (mkEffect old [] []), model. split; [rewrite Hchk; exact Hkeep_ok | apply Hforced].
      * intros eff m' Hc _. rewrite Hchk in Hc. destruct (Hall _ _ _ Hc) as (_ & -> & ->).
        exists model. split; [apply materialize_nil|].
        apply (Hkeep (with_model A (npc A) (aset (a_regs A) reg_a0 (of_form (am_brk (a_model A)))) (a_mem A) (a_facts A) (a_model A) (a_budget A)));
          try reflexivity. exact (HS _ (or_intror (or_introl eq_refl))).
Qed.

End Main.
