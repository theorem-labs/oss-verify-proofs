(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From Stdlib Require Import Uint63.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX Frame.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface RRealloc_iface RAligned_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Stdio HexModel Target Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Exit Printf_wfile F_memset Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Common Require Import FastWord FastWordSem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Common.Ax Require Import ExTrie.
From OssFuzzTheorems.Proofs.openssl.ct.lib.HX Require Import HxRegs HxVal HxBytes HxMem HxMemSound HxStep HxStepSound HxRunSound HxHook HxHookSound HxToolkit HxGlue.
From OssFuzzTheorems.Proofs.openssl.ct.lib.ApHX Require Import HkAligned.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpInit HxpImage HxpInv HxpHooks HxpHkAligned.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section HookAligned.
Context {CE__ : Ceiling} {RN__ : RunRnd} {LM : LibModel} {LSP : LibSpec}.
Variables (LB : list block) (lo B sp0 : Z) (m0 : word -> option byte) (F0 : bvmap 5 word) (fc0 : bv 32) (s0 : PState).
Variable ls0 : LS.
Variable POST : LS -> PState -> machine_state -> Prop.

Hypothesis H_LIBW : LIBW = LIBW_HX.
Hypothesis H_lo1 : alloc_ceiling <= lo.
Hypothesis H_lo2 : GLOBALS_TOP <= lo.
Hypothesis H_lo3 : lo <= sp0 - to_Z STK.
Hypothesis H_sp0B : sp0 <= B.
Hypothesis H_sp064 : sp0 < 2 ^ 64.

Hypothesis ALIGNED : rposix_memalign_stmt.

Notation FInvP := (FInv LB lo B sp0 m0 F0 fc0 s0).
Notation FMemP := (FMem LB lo B sp0 m0).
Notation JP := (J ls0 POST).
Notation InvP := (Inv ctusegs ghost FInvP).

Lemma bytes_at_mrd (m : word -> option byte) (A : Z) (bs : list byte) (i : Z) :
  bytes_at ctusegs m A bs -> 0 <= i < Z.of_nat (length bs) -> mrd ctusegs m (wa (A + i)) = nth_error bs (Z.to_nat i).
Proof. intros (_ & _ & H) Hi. specialize (H (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in H by lia. exact H. Qed.

(* [comment removed for export] *)
Lemma in_block_low (s : PState) (L : list block) (m : word -> option byte) (a : Z) : RHEAP s L m -> in_block L a -> a < alloc_ceiling.
Proof.
  intros H (b & Hin & Ha). destruct (LH_block_range s L m b H Hin) as (_ & _ & _ & R4 & _). lia.
Qed.

(* [comment removed for export] *)
Lemma pres_but_above (L : list block) (s : PState) (m m' : word -> option byte) (spc mp : Z) :
  RHEAP s L m -> rheap_pres_but L spc (mp, mp + 8) m m' -> spc <= sp0 -> mp + 8 <= sp0 -> lo <= mp ->
  rheap_pres L sp0 m m'.
Proof.
  intros HH HP Hspc Hmp Hlo a Ha Hc. apply (HP a Ha); cbn [fst snd].
  - destruct Hc as [Hc|[Hc|Hc]]; [left; lia | right; left; exact Hc | right; right; exact Hc].
  - destruct Hc as [Hc|[[Hc _]|Hc]]; [lia | unfold GLOBALS_TOP in H_lo2; lia |].
    pose proof (in_block_low s L m a HH Hc). lia.
Qed.

Lemma hkp_posix_memalign_ok : hook_ok' ctusegs ghost JP FInvP hkp_posix_memalign.
Proof.
  intros g rho cd S cd' S' ms [HRn HF] Hh K.
  unfold hkp_posix_memalign, hk_at in Hh. destruct (w_eqb (s_pc S) PC_POSIX_MEMALIGN) eqn:Epc; [|discriminate].
  apply w_eqb_true_iff in Epc.
  unfold hk_posix_memalign_v in Hh. destruct (tp_ok TPV S && sp_ok 1 S) eqn:Eg; [|discriminate].
  apply andb_prop in Eg as [Etp Esp].
  destruct (reset_errno T_ERRNO ERRNO_INT (s_mem S)) as [M1|] eqn:Ere; [|discriminate].
  unfold hk_posix_memalign in Hh. cbn [s_pc s_regs s_resv s_mem s_abs s_next] in Hh.
  destruct (a_ops cd) as [|[[c n] al] rest] eqn:Eops; [discriminate|].
  destruct c as [|c|c]; try discriminate. destruct c as [c|c|]; try discriminate. destruct c as [c|c|]; try discriminate.
  unfold hk_return, clobber_stack, rget in Hh. cbn [s_pc s_regs s_resv s_mem s_abs s_next] in Hh.
  destruct (rf_get vzero (s_regs S) X10) as [|ts o| |] eqn:Ea10; try discriminate.
  destruct (zval (rf_get vzero (s_regs S) X11)) as [al'|] eqn:Ea1; [|discriminate].
  destruct (zval (rf_get vzero (s_regs S) X12)) as [n'|] eqn:Ea2; [|discriminate].
  destruct (rf_get vzero (s_regs S) X2) as [|ts2 osp| |] eqn:Esp2; try discriminate.
  match type of Hh with (if ?cnd then _ else _) = _ => destruct cnd eqn:En; [|discriminate] end.
  apply andb_prop in En as [En Eole]. apply andb_prop in En as [En Eo7]. apply andb_prop in En as [En Ehosp]. apply andb_prop in En as [En Eho].
  apply andb_prop in En as [En En3]. apply andb_prop in En as [En En2]. apply andb_prop in En as [En Eal]. apply andb_prop in En as [En Eal'].
  apply andb_prop in En as [En En1]. apply andb_prop in En as [Ets Ets2].
  apply Uint63.eqb_spec in Ets. subst ts. apply Uint63.eqb_spec in Ets2. subst ts2. apply Z.eqb_eq in En1. subst n'. apply Z.eqb_eq in Eal'. subst al'. apply Z.eqb_eq in Eal. subst al.
  apply Z.ltb_lt in En2, En3. apply negb_true_iff in Eho. apply negb_true_iff in Ehosp. apply Uint63.eqb_spec in Eo7. apply leb_spec in Eole.
  destruct (mget M1 1%uint63) as [rg1|] eqn:Eg1; [|discriminate].
  match type of Hh with (if ?cnd then _ else _) = _ => destruct cnd eqn:Eck2; [|discriminate] end.
  apply andb_prop in Eck2 as [Eck2 Ewr1]. apply andb_prop in Eck2 as [Eo1 Eo8]. apply leb_spec in Eo1. apply leb_spec in Eo8.
  cbv zeta in Hh. rewrite Ehosp in Hh.
  set (t := s_next S) in *. set (rg1' := wr_cell rg1 (wl o >> 3)%uint63 (CP t w_zero)) in *.
  set (M1' := mset M1 1 rg1') in *. set (M2 := new_region M1' t (of_Z n) 6 DUnk) in *.
  destruct (rf_get vzero (s_regs S) X1) as [ra| | |] eqn:Era; try discriminate.
  destruct (mget M2 1%uint63) as [rgs|] eqn:Egs; [|discriminate].
  destruct (rg_abs rgs) eqn:Eabs; [discriminate|]. destruct (rg_dflt rgs) eqn:Edf; try discriminate.
  destruct ((wl osp land 15 =? 0)%uint63 && (HK_STACK <=? wl osp)%uint63 && (wl osp <=? rg_size rgs)%uint63 && rg_wr rgs) eqn:Eck; [|discriminate].
  destruct (s_resv S) eqn:Erv; try discriminate.
  injection Hh as <- <-.
  (* [comment removed for export] *)
  destruct HF as [HM (Hfr & Hfc & Hro & Hnf & Hps)].
  pose proof (Rn_R ctusegs rho S ms HRn) as (Hsvc & Hpc & HRg & Hrv & HRm).
  destruct Hnf as (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20
                   & x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & Eregs).
  rewrite Erv in Hrv. cbn [Rresv] in Hrv.
  assert (Ems : ms = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                        F0 (wbv PC_POSIX_MEMALIGN) fc0 None (ms_mem ms) (seg_rom ctusegs)).
  { rewrite (MS_eta ms Hsvc) at 1. rewrite Eregs, Hfr, Hfc, Hro, Hrv, Hpc, Epc. reflexivity. }
  unfold core_of in HRg. rewrite Eregs in HRg.
  set (m := ms_mem ms) in *. clearbody m. clear Hsvc Hpc Hrv Hfr Hfc Hro Eregs. subst ms.
  destruct (nf_regs rho S _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HRg) as (D1 & D2 & D4 & D10 & D11 & D12).
  unfold rget in D1, D2, D4, D10, D11, D12. rewrite Era in D1. rewrite Esp2 in D2. rewrite Ea10 in D10.
  unfold tp_ok, rget in Etp. destruct (rf_get vzero (s_regs S) X4) as [tpw| | |] eqn:Etp4; try discriminate.
  apply w_eqb_true_iff in Etp. subst tpw.
  unfold zval in Ea1, Ea2. destruct (rf_get vzero (s_regs S) X11) as [a1w| | |] eqn:Ea11; try discriminate. injection Ea1 as Ea1.
  destruct (rf_get vzero (s_regs S) X12) as [a2w| | |] eqn:Ea12; try discriminate. injection Ea2 as Ea2.
  cbn [den] in D1, D2, D4, D10, D11, D12.
  (* [comment removed for export] *)
  pose proof HM as (Hops & Hlen & Hn & Hnd & Htl & Htags & Hnx0 & Hnx & Hcls & Hlink & Hheap & Hrho1 & Hmi & Hstk & Haux & Hagr).
  fold t in Htl, Htags, Hnx0, Hnx.
  assert (Ht20 : to_Z t < to_Z TAGLIM) by (change (to_Z TAGLIM) with (2 ^ 20); lia).
  assert (Ht29 : 29 <= to_Z t) by (change (to_Z NEXT0) with 29 in Hnx0; lia).
  assert (H1lim : to_Z 1%uint63 < to_Z TAGLIM) by (vm_compute; reflexivity).
  (* [comment removed for export] *)
  destruct (reset_errno_inv _ _ _ _ Ere) as (rge & Ege & Eae & Ede & Ese & Ewe & EM1).
  set (rge' := RG (rg_abs rge) (rg_size rge) (rg_al rge) (rg_wr rge) DUnk (rg_d rge) IEmpty) in *.
  assert (Ergs : rgs = rg1').
  { unfold M2 in Egs. rewrite new_region_eq in Egs. rewrite mget_mset in Egs by exact Ht20.
    destruct (Z.eqb_spec (to_Z t) (to_Z 1%uint63)) as [E|E]; [change (to_Z 1%uint63) with 1 in E; lia |].
    unfold M1' in Egs. rewrite (mget_mset M1 1 1 _ H1lim), Z.eqb_refl in Egs. injection Egs as E'. symmetry. exact E'. }
  assert (Egs0 : mget (s_mem S) 1 = Some rg1).
  { pose proof Eg1 as Eg1'. rewrite EM1 in Eg1'. rewrite mget_mset in Eg1' by (exact (mget_lt _ _ _ Ege)).
    destruct (Z.eqb_spec (to_Z T_ERRNO) (to_Z 1%uint63)) as [E|E]; [discriminate E | exact Eg1']. }
  subst rgs. cbn [rg1' wr_cell rg_abs rg_dflt rg_size rg_wr] in Eabs, Edf, Eck.
  assert (Essz : rg_size rg1 = STK).
  { pose proof (Hcls 1%uint63 rg1 Egs0) as C. rewrite Eabs in C. destruct C as [[_ C]|(k & p & n0 & Hk & _)]; [exact C|].
    exfalso. apply nth_error_In in Hk. specialize (Htl _ Hk). change (to_Z NEXT0) with 29 in Htl. change (to_Z 1%uint63) with 1 in Htl. lia. }
  apply andb_prop in Eck as [Eck Ewr]. apply andb_prop in Eck as [Eck Eo3]. apply andb_prop in Eck as [Eos1 Eos2].
  apply Uint63.eqb_spec in Eos1. apply leb_spec in Eos2, Eo3. rewrite Essz in Eo3, Eo1, Eo8. change (to_Z HK_STACK) with 16384 in Eos2.
  pose proof STK_Z as ESTK. pose proof (to_Z_bounded (wl o)) as Bo. pose proof (to_Z_bounded (wl osp)) as Bosp.
  assert (EwZo : wZ o = to_Z (wl o)) by (unfold wZ; rewrite Eho; reflexivity).
  assert (EwZosp : wZ osp = to_Z (wl osp)) by (unfold wZ; rewrite Ehosp; reflexivity).
  assert (Eos16 : to_Z (wl osp) mod 16 = 0).
  { pose proof (f_equal to_Z Eos1) as E. rewrite land_spec' in E. change (to_Z 15%uint63) with (Z.ones 4) in E.
    rewrite Z.land_ones in E by lia. exact E. }
  assert (Eos8m : to_Z (wl osp) mod 8 = 0).
  { pose proof (Z.mod_divide (to_Z (wl osp)) 16 ltac:(lia)) as [X _]. destruct (X Eos16) as [q Eq]. rewrite Eq. replace (q * 16) with ((q * 2) * 8) by ring. apply Z.mod_mul. lia. }
  assert (Eom8 : to_Z (wl o) mod 8 = 0).
  { pose proof (f_equal to_Z Eo7) as E. rewrite land_spec' in E. change (to_Z 7%uint63) with (Z.ones 3) in E.
    rewrite Z.land_ones in E by lia. exact E. }
  assert (Eo8' : to_Z (wl o + 8)%uint63 = to_Z (wl o) + 8).
  { rewrite add_spec. change (to_Z 8%uint63) with 8. apply Z.mod_small. rewrite wB_eq. unfold two63. lia. }
  rewrite Eo8' in Eo8.
  set (spc := sp0 - to_Z STK + to_Z (wl osp)).
  set (mp := sp0 - to_Z STK + to_Z (wl o)).
  clear Esp. assert (Esp : bv_unsigned x2 = spc).
  { rewrite D2. unfold pword. rewrite Z_to_bv_unsigned, Hrho1, EwZosp. apply bv_wrap_small. unfold bv_modulus. unfold GLOBALS_TOP in H_lo2. lia. }
  assert (Emp : bv_unsigned x10 = mp).
  { rewrite D10. unfold pword. rewrite Z_to_bv_unsigned, Hrho1, EwZo. apply bv_wrap_small. unfold bv_modulus. unfold GLOBALS_TOP in H_lo2. lia. }
  (* [comment removed for export] *)
  assert (Herr : exists errv : word, rw_cells ctusegs m RMallocRep.RERRNO [C4 errv]).
  { destruct HRm as [HRg0 _]. pose proof (region_mapped ctusegs rho T_ERRNO rge m (HRg0 _ _ Ege)) as Hb.
    unfold rbase in Hb. rewrite Eae, Ese in Hb. change (to_Z ERRNO_INT) with RMallocRep.RERRNO in Hb. change (to_Z 4%uint63) with 4 in Hb.
    apply bytes_rw_C4; [unfold RMallocRep.RERRNO; lia | unfold RMallocRep.RERRNO; lia|].
    intros i Hi. destruct (Hb i Hi) as [Hm Hw]. split; [exact Hm | exact (Hw Ewe)]. }
  destruct Herr as [errv Herr].
  (* [comment removed for export] *)
  assert (Hwmp : wr_at ctusegs m mp 8).
  { destruct HRm as [HRg0 _]. pose proof (HRg0 _ _ Egs0) as (_ & _ & _ & _ & _ & _ & _ & Hby). unfold rbase in Hby. rewrite Eabs, Hrho1, Essz in Hby.
    split; [unfold mp, GLOBALS_TOP in *; lia|]. split; [unfold mp; lia|]. intros i Hi.
    replace (mp + i) with (sp0 - to_Z STK + (to_Z (wl o) + i)) by (unfold mp; lia). destruct (Hby (to_Z (wl o) + i) ltac:(lia)) as (b & _ & _ & W). exact (W Ewr). }
  (* [comment removed for export] *)
  unfold J. rewrite Hops, Eops. cbn [map dec_op Z.eqb run_ops lbind].
  eapply implM_interp_aligned.
  { eapply (ALIGNED x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
                     F0 fc0 m (g_s g) _ 64 n mp lo B errv Hheap Haux).
    - rewrite Esp. unfold spc. lia.
    - rewrite Esp. exact (proj1 (stk_split ctusegs _ lo spc sp0 Hstk ltac:(unfold spc; lia))).
    - exact H_lo1.
    - rewrite Esp. unfold spc, RALIGNED_STACK, RMALLOC_STACK. lia.
    - rewrite D4. change (bv_unsigned (wbv TPV) + -164) with RMallocRep.RERRNO. exact Herr.
    - exact Hmi.
    - rewrite D4. reflexivity.
    - apply bv_eq. rewrite Emp, Z_to_bv_unsigned. symmetry. apply bv_wrap_small. unfold bv_modulus, mp, GLOBALS_TOP in *. lia.
    - rewrite Esp. unfold spc, mp. lia.
    - unfold mp. lia.
    - exact Hwmp.
    - rewrite D11. apply bv_eq. rewrite wbv_unsigned, Ea1, Z_to_bv_unsigned. symmetry. apply bv_wrap_small. unfold bv_modulus. lia.
    - right. reflexivity.
    - rewrite D12. apply bv_eq. rewrite wbv_unsigned, Ea2, Z_to_bv_unsigned. symmetry. apply bv_wrap_small. unfold bv_modulus. lia.
    - lia.
    - unfold aligned_req, UNIT. lia. }
  intros r s' ms' HP. destruct r as [p|]; [|cbn [lbind]; apply implM_interp_unr].
  destruct HP as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & errv' & Ems' & Hmi' & Hstk'
                  & Herr' & Haux' & Hpresb & Hfa & Hso & A & junk & Ea0' & HA64 & Hrange & Hheap' & Hblk & Hmpc).
  rewrite Esp in Hstk', Hpresb. rewrite D4 in Herr'. change (bv_unsigned (wbv TPV) + -164) with RMallocRep.RERRNO in Herr'.
  destruct Hrange as (R1 & R2 & R3 & R4 & R5).
  (* [comment removed for export] *)
  assert (Hpres : rheap_pres (live_blocks rho (rev (a_tags cd)) (g_env g) ++ LB) sp0 m m').
  { apply (pres_but_above _ (g_s g) m m' spc mp Hheap Hpresb); unfold spc, mp; lia. }
  set (rho' := fun t' : int => if (t' =? t)%uint63 then A else rho t').
  assert (Hag' : agree_below t rho rho').
  { intros t' Ht'. unfold rho'. destruct (t' =? t)%uint63 eqn:E; [apply Uint63.eqb_spec in E; subst t'; lia | reflexivity]. }
  assert (Erho't : rho' t = A) by (unfold rho'; rewrite Uint63.eqb_refl; reflexivity).
  assert (Et1 : to_Z (t + 1)%uint63 = to_Z t + 1).
  { rewrite add_spec. change (to_Z 1%uint63) with 1. apply Z.mod_small. rewrite wB_eq. unfold two63. change (to_Z TAGLIM) with (2 ^ 20) in Ht20. lia. }
  assert (Ergq' : rg1' = wr_cell rg1 (wl o >> 3)%uint63 (CP t w_zero)) by reflexivity.
  assert (Hsd1 : same_dir rg1 rg1') by (rewrite Ergq'; apply same_dir_wr_cell).
  assert (Hsdq : same_dir rg1 (drop_below rg1' (wl osp))) by (rewrite Ergq'; repeat split).
  apply (K (GH s' (g_env g ++ [Some (p, n)]) (map dec_op rest)) rho' ms' Hag').
  subst ms'. split.
  - (* [comment removed for export] *)
    intros rho2 Hag2. cbn [s_next] in Hag2.
    assert (Hag02 : agree_below t rho rho2).
    { intros t' Ht'. rewrite (Hag2 t') by (rewrite Et1; lia). apply Hag'. exact Ht'. }
    assert (Erho2t : rho2 t = A) by (rewrite (Hag2 t) by (rewrite Et1; lia); exact Erho't).
    assert (Erho21 : rho2 1%uint63 = sp0 - to_Z STK) by (rewrite (Hag02 1%uint63) by (change (to_Z 1%uint63) with 1; lia); exact Hrho1).
    pose proof (HRn rho2 Hag02) as (_ & _ & HRg2 & _ & HRm2). change (Rmem ctusegs rho2 (s_mem S) m) in HRm2.
    pose proof HRm2 as [HRok2 Hsep2].
    unfold R. cbn [ms_svc_pending ms_pc_val ms_resv ms_mem MS s_pc s_regs s_resv s_mem].
    split; [reflexivity|]. split; [rewrite D1; apply ret_pc_wbv|]. split.
    { unfold core_of in HRg2 |- *. cbn [ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv MS] in HRg2 |- *.
      eapply (Rregs_return rho2 (s_regs S) (VC w_zero)); [exact HRg2|]. cbn [den]. rewrite Ea0'. reflexivity. }
    split; [reflexivity|].
    split.
    + intros t3 rg3 G3.
      destruct (mget_mset_cases M2 1%uint63 t3 _ rg3 H1lim G3) as [[-> ->]|[N1 G3a]].
      * (* [comment removed for export] *)
        pose proof (HRok2 _ _ Egs0) as Hoks. pose proof Hoks as (Q0 & Q1 & Q2 & Q3 & Q4 & _ & _ & Hbys).
        unfold rbase in Q0, Q1, Hbys. rewrite Eabs, Erho21 in Q0, Q1, Hbys. rewrite Essz in Q1, Q2, Q3, Hbys.
        apply (region_ok_upd ctusegs rho2 1%uint63 rg1 (drop_below rg1' (wl osp)) m m' Hoks Hsdq). intros i Hi. unfold rbase. rewrite Eabs, Erho21. rewrite Essz in Hi. rewrite Ewr.
        assert (Hk3 : to_Z (wl o >> 3)%uint63 < 2 ^ Z.of_nat (rg_d rg1)).
        { rewrite phi_shr3. set (X := 2 ^ Z.of_nat (rg_d rg1)) in *. Z.div_mod_to_equations. lia. }
        rewrite (rg_kb_drop_below ctusegs rg1' (wl osp) i ltac:(rewrite Ergq'; cbn [wr_cell rg_size]; rewrite Essz; exact Hi)
                   ltac:(rewrite Ergq'; cbn [wr_cell rg_size rg_d]; rewrite Essz; exact Q3) ltac:(rewrite Ergq'; cbn [wr_cell rg_size]; rewrite Essz; exact Q2)
                   ltac:(rewrite Ergq'; cbn [wr_cell rg_dflt]; exact Edf) Eos8m).
        destruct (Z.ltb_spec i (to_Z (wl osp))) as [Li|Li].
        -- (* [comment removed for export] *)
           destruct Hstk' as (_ & _ & Hs). destruct (Hs (sp0 - to_Z STK + i) ltac:(unfold spc; lia)) as [Hw [b Hb]].
           exists b. split; [exact Hb|]. split; [exact I | intros _; exact Hw].
        -- destruct ((to_Z (wl o) <=? i) && (i <? to_Z (wl o) + 8)) eqn:Ein.
           ++ (* [comment removed for export] *)
              apply andb_prop in Ein as [Ei1 Ei2]. apply Z.leb_le in Ei1. apply Z.ltb_lt in Ei2.
              destruct Hmpc as [[_ Hbp] Hwp]. cbn [cells_bytes cbytes] in Hbp. rewrite app_nil_r in Hbp.
              pose proof (bytes_at_mrd m' mp (le8 (Z_to_bv 64 A)) (i - to_Z (wl o)) Hbp ltac:(rewrite length_le8; lia)) as Eb.
              replace (mp + (i - to_Z (wl o))) with (sp0 - to_Z STK + i) in Eb by (unfold mp; lia).
              unfold le8, word_to_le_bytes in Eb. pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 A)) as HwA.
              rewrite (nth_Z_to_le_bytes 8 (bv_unsigned (Z_to_bv 64 A)) (Z.to_nat (i - to_Z (wl o))) ltac:(lia) ltac:(lia)) in Eb.
              rewrite Z2Nat.id in Eb by lia.
              exists (byte_of (bv_unsigned (Z_to_bv 64 A)) (i - to_Z (wl o))). split; [exact Eb|]. split.
              ** unfold rg_kb. destruct (cell_of_byte (wl o) (i - to_Z (wl o)) 8 ltac:(lia) ltac:(lia)) as [Ek Em].
                 replace (to_Z (wl o) + (i - to_Z (wl o))) with i in Ek, Em by lia. rewrite Ek.
                 rewrite Ergq', (rd_cell_wr_cell ctusegs rg1 _ _ (CP t w_zero) Hk3 Hk3), Z.eqb_refl.
                 cbn [cell_kb kb_ok]. rewrite Em, Eom8, Z.add_0_l. rewrite byte_of_unsigned. unfold pword. rewrite Erho2t. change (wZ w_zero) with 0. rewrite Z.add_0_r. reflexivity.
              ** intros _. destruct Hwp as (_ & _ & W). cbn [cells_size csize] in W. specialize (W (i - to_Z (wl o)) ltac:(lia)).
                 replace (mp + (i - to_Z (wl o))) with (sp0 - to_Z STK + i) in W by (unfold mp; lia). exact W.
           ++ apply andb_false_iff in Ein. rewrite Z.leb_gt, Z.ltb_ge in Ein.
              assert (Hki : to_Z (of_Z (i / 8)) < 2 ^ Z.of_nat (rg_d rg1)).
              { rewrite of_Z_spec, Z.mod_small by (rewrite wB_eq; unfold two63; Z.div_mod_to_equations; lia).
                set (X := 2 ^ Z.of_nat (rg_d rg1)) in *. Z.div_mod_to_equations. lia. }
              assert (Ekb : rg_kb ctusegs rg1' i = rg_kb ctusegs rg1 i).
              { unfold rg_kb. rewrite Ergq', (rd_cell_wr_cell ctusegs rg1 _ _ (CP t w_zero) Hk3 Hki). cbn [rg_d wr_cell].
                destruct (Z.eqb_spec (to_Z (wl o >> 3)%uint63) (to_Z (of_Z (i / 8)))) as [Ec|Ec]; [|reflexivity].
                exfalso. rewrite phi_shr3, of_Z_spec, Z.mod_small in Ec by (rewrite wB_eq; unfold two63; Z.div_mod_to_equations; lia). Z.div_mod_to_equations. lia. }
              rewrite Ekb.
              destruct (Hbys i Hi) as (b & Eb & Kb & Wb).
              destruct (Hpresb (sp0 - to_Z STK + i) ltac:(lia) ltac:(left; unfold spc; lia) ltac:(cbn [fst snd]; unfold mp; lia)) as [E W].
              exists b. split; [unfold mrd; rewrite E; exact Eb|]. split; [exact Kb | intros _; apply W, Wb, Ewr].
      * unfold M2 in G3a. rewrite new_region_eq in G3a. destruct (mget_mset_cases M1' t t3 _ rg3 Ht20 G3a) as [[-> ->]|[N2 G3b]].
        -- assert (En62 : to_Z (of_Z n) = n) by (apply of_Z_small; lia).
           destruct (depth_for_ok (of_Z n) ltac:(rewrite En62; lia)) as [Hd1 Hd2].
           apply region_ok_fresh; unfold rbase; cbn [rg_abs]; rewrite ?En62, ?Erho2t; try assumption.
           all: try (unfold two63; lia). all: try (change (to_Z 6%uint63) with 6; lia). all: try (change (2 ^ to_Z 6%uint63) with 64; exact HA64).
           intros i Hi. destruct (rw_CB_bytes ctusegs m' A _ _ Hblk i ltac:(lia)) as [Hb Hw]. split; [exact Hb | intros _; exact Hw].
        -- unfold M1' in G3b. destruct (mget_mset_cases M1 1%uint63 t3 _ rg3 H1lim G3b) as [[E1t _]|[_ G3c]]; [exfalso; exact (N1 E1t)|].
           rewrite EM1 in G3c. destruct (mget_mset_cases (s_mem S) T_ERRNO t3 _ rg3 (mget_lt _ _ _ Ege) G3c) as [[-> ->]|[N3 G3d]].
           ++ exact (errno_after_call rho2 rge m m' errv' (HRok2 _ _ Ege) Eae Ese Herr').
           ++ apply (region_ok_frame ctusegs rho2 t3 rg3 m m' (HRok2 _ _ G3d)).
              apply (old_region_kept LB lo B sp0 m0 g rho rho2 cd (s_mem S) t m m' s' _ _ sp0 rge HM HRm2 Hag02 Hmi' Hheap' Hpres Ege Eae Ese Ewe t3 rg3 G3d N1 N3).
              intros k p3 n3 Hk He. apply in_or_app. left. exact (live_blocks_in rho _ _ k t3 p3 n3 Hk He).
    + (* [comment removed for export] *)
      assert (Sep1 : regions_sep rho2 M1).
      { rewrite EM1. apply (regions_sep_mset_same rho2 (s_mem S) T_ERRNO rge rge' Ege); [|exact Hsep2]. unfold rge'. repeat split. cbn [rg_dflt]. symmetry. exact Ede. }
      assert (Sep1' : regions_sep rho2 M1') by (unfold M1'; exact (regions_sep_mset_same rho2 M1 1%uint63 rg1 rg1' Eg1 Hsd1 Sep1)).
      assert (Hfresh : mget M1' t = None).
      { unfold M1'. rewrite mget_mset by exact H1lim. destruct (Z.eqb_spec (to_Z 1%uint63) (to_Z t)) as [E|E]; [change (to_Z 1%uint63) with 1 in E; lia|].
        rewrite EM1. rewrite mget_mset by exact (mget_lt _ _ _ Ege). destruct (Z.eqb_spec (to_Z T_ERRNO) (to_Z t)) as [E'|E']; [change (to_Z T_ERRNO) with 9 in E'; lia|].
        destruct (mget (s_mem S) t) as [rgx|] eqn:Ex; [|reflexivity]. pose proof (Htags t rgx Ex). lia. }
      apply (regions_sep_mset_same rho2 M2 1%uint63 rg1' (drop_below rg1' (wl osp)) Egs); [repeat split|].
      unfold M2. rewrite new_region_eq. apply (regions_sep_new rho2 M1' t _ Sep1' Hfresh Ht20).
      intros t2 rg2 G2.
      assert (EB : rbase rho2 t (RG None (of_Z n) 6 true DUnk (depth_for 60 (of_Z n) 0) IEmpty) = A) by (unfold rbase; cbn [rg_abs]; exact Erho2t).
      rewrite EB. cbn [rg_size]. rewrite of_Z_small by lia.
      assert (X : forall rgx, mget (s_mem S) t2 = Some rgx -> A + n <= rbase rho2 t2 rgx \/ rbase rho2 t2 rgx + to_Z (rg_size rgx) <= A).
      { intros rgx Gx. apply (new_block_apart LB lo B sp0 m0 H_lo1 H_lo3 g rho rho2 cd (s_mem S) t m m' s' p A n _ HM HRm2 Hag02 Hheap' t2 rgx Gx).
        intros k p2 n2 Hk He. apply in_or_app. left. exact (live_blocks_in rho _ _ k t2 p2 n2 Hk He). }
      unfold M1' in G2. destruct (mget_mset_cases M1 1%uint63 t2 _ rg2 H1lim G2) as [[-> ->]|[_ G2a]].
      { rewrite (rbase_same_dir rho2 1%uint63 rg1 rg1' Hsd1). replace (rg_size rg1') with (rg_size rg1) by (rewrite Ergq'; reflexivity). exact (X rg1 Egs0). }
      rewrite EM1 in G2a. destruct (mget_mset_cases (s_mem S) T_ERRNO t2 _ rg2 (mget_lt _ _ _ Ege) G2a) as [[-> ->]|[N3 G2']]; [exact (X rge Ege) | exact (X rg2 G2')].
  - (* [comment removed for export] *)
    split; [|cbn [ms_fregs ms_fcsr ms_rom ms_regs MS g_s]; repeat (split; [reflexivity|]); split; [do 31 eexists; reflexivity | destruct Hps as [P1 P2]; split; congruence]].
    unfold FMem. cbn [a_ops a_tags a_n g_s g_env g_ops s_mem s_next ms_mem MS rev]. change (to_Z NEXT0) with 29 in *.
    set (tl := rev (a_tags cd)) in *. set (newrg := RG None (of_Z n) 6 true DUnk (depth_for 60 (of_Z n) 0) IEmpty).
    assert (Hcases : forall t3 rg3, mget (mset M2 1 (drop_below rg1' (wl osp))) t3 = Some rg3 ->
              (t3 = 1%uint63 /\ rg3 = drop_below rg1' (wl osp)) \/ (t3 = t /\ rg3 = newrg) \/ (t3 = T_ERRNO /\ rg3 = rge')
              \/ (t3 <> 1%uint63 /\ t3 <> t /\ t3 <> T_ERRNO /\ mget (s_mem S) t3 = Some rg3)).
    { intros t3 rg3 G3.
      destruct (mget_mset_cases M2 1%uint63 t3 _ rg3 H1lim G3) as [[-> ->]|[N1 G3a]]; [left; auto|].
      unfold M2 in G3a. rewrite new_region_eq in G3a. destruct (mget_mset_cases M1' t t3 _ rg3 Ht20 G3a) as [[-> ->]|[N2 G3b]]; [right; left; auto|].
      unfold M1' in G3b. destruct (mget_mset_cases M1 1%uint63 t3 _ rg3 H1lim G3b) as [[E1t _]|[_ G3c]]; [exfalso; exact (N1 E1t)|].
      rewrite EM1 in G3c. destruct (mget_mset_cases (s_mem S) T_ERRNO t3 _ rg3 (mget_lt _ _ _ Ege) G3c) as [[-> ->]|[N3 G3d]]; [right; right; left; auto|].
      right; right; right. auto. }
    split; [reflexivity|].
    split; [rewrite !length_app; cbn [length]; lia|].
    split; [rewrite length_app; cbn [length]; lia|].
    split.
    { apply (Permutation_NoDup (l := t :: tl)); [apply Permutation_cons_append|]. constructor; [|exact Hnd].
      intros Hin. specialize (Htl t Hin). lia. }
    split.
    { intros t' Hin. apply in_app_or in Hin. destruct Hin as [Hin|[<-|[]]]; [specialize (Htl t' Hin); lia | lia]. }
    split.
    { intros t3 rg3 G3. destruct (Hcases t3 rg3 G3) as [[-> _]|[[-> _]|[[-> _]|(_ & _ & _ & G)]]].
      - change (to_Z 1%uint63) with 1. lia.
      - lia.
      - change (to_Z T_ERRNO) with 9. lia.
      - specialize (Htags t3 rg3 G). lia. }
    split; [lia|]. split; [rewrite Eops in Hnx; cbn [length] in Hnx; lia|].
    split.
    { intros t3 rg3 G3. destruct (Hcases t3 rg3 G3) as [[-> ->]|[[-> ->]|[[-> ->]|(N1 & N2 & N3 & G)]]].
      - rewrite Ergq'. cbn [drop_below wr_cell rg_abs rg_size]. rewrite Eabs. left. split; [reflexivity | exact Essz].
      - cbn [newrg rg_abs rg_size]. right. exists (length tl), p, n.
        split; [rewrite nth_error_app2 by lia; rewrite Nat.sub_diag; reflexivity|].
        split; [rewrite nth_error_app2 by lia; rewrite Hlen, Nat.sub_diag; reflexivity|]. apply of_Z_small. lia.
      - pose proof (Hcls T_ERRNO rge Ege) as C. rewrite Eae in C. cbn [rge' rg_abs rg_size rg_wr]. rewrite Eae. exact C.
      - pose proof (Hcls t3 rg3 G) as C. destruct (rg_abs rg3); [exact C|]. destruct C as [C|(k & p3 & n3 & Hk & He & Es)]; [left; exact C|].
        right. exists k, p3, n3. split; [rewrite nth_error_app1 by (apply nth_error_Some; congruence); exact Hk|].
        split; [rewrite nth_error_app1 by (apply nth_error_Some; congruence); exact He | exact Es]. }
    split.
    { intros k0 t3 p3 n3 Hk He.
      assert (Hnew : mget (mset M2 1 (drop_below rg1' (wl osp))) t = Some newrg).
      { rewrite mget_mset by exact H1lim.
        destruct (Z.eqb_spec (to_Z 1%uint63) (to_Z t)) as [E|E]; [change (to_Z 1%uint63) with 1 in E; lia|].
        unfold M2. rewrite new_region_eq. rewrite mget_mset by exact Ht20. rewrite Z.eqb_refl. reflexivity. }
      destruct (Nat.lt_ge_cases k0 (length tl)) as [L|L].
      - rewrite nth_error_app1 in Hk by exact L. rewrite nth_error_app1 in He by lia.
        destruct (Hlink k0 t3 p3 n3 Hk He) as (rg3 & G3 & Ea3 & Es3 & Ew3). exists rg3. repeat split; try assumption.
        assert (N1 : t3 <> 1%uint63) by (intros ->; apply nth_error_In in Hk; specialize (Htl _ Hk); change (to_Z 1%uint63) with 1 in Htl; lia).
        assert (N2 : t3 <> t) by (intros ->; apply nth_error_In in Hk; specialize (Htl _ Hk); lia).
        assert (N3 : t3 <> T_ERRNO) by (intros ->; apply nth_error_In in Hk; specialize (Htl _ Hk); change (to_Z T_ERRNO) with 9 in Htl; lia).
        rewrite mget_mset by exact H1lim.
        destruct (Z.eqb_spec (to_Z 1%uint63) (to_Z t3)) as [E|E]; [apply to_Z_inj in E; congruence|].
        unfold M2. rewrite new_region_eq. rewrite mget_mset by exact Ht20.
        destruct (Z.eqb_spec (to_Z t) (to_Z t3)) as [E'|E']; [apply to_Z_inj in E'; congruence|].
        unfold M1'. rewrite mget_mset by exact H1lim.
        destruct (Z.eqb_spec (to_Z 1%uint63) (to_Z t3)) as [E0|E0]; [apply to_Z_inj in E0; congruence|].
        rewrite EM1. rewrite mget_mset by exact (mget_lt _ _ _ Ege).
        destruct (Z.eqb_spec (to_Z T_ERRNO) (to_Z t3)) as [E''|E'']; [apply to_Z_inj in E''; congruence | exact G3].
      - rewrite nth_error_app2 in Hk by exact L. rewrite nth_error_app2 in He by lia. rewrite Hlen in He.
        destruct (k0 - length tl)%nat as [|j] eqn:Ej; [|destruct j; discriminate]. cbn in Hk, He. injection Hk as <-. injection He as <- <-.
        exists newrg. split; [exact Hnew|]. cbn [newrg rg_abs rg_size rg_wr]. repeat split. apply of_Z_small. lia. }
    split.
    { rewrite live_blocks_snoc by exact Hlen. rewrite Erho't.
      rewrite (live_blocks_agree rho rho') by (intros t' Hin; apply Hag'; specialize (Htl t' Hin); lia).
      eapply RHEAP_perm; [exact Hheap'|]. rewrite <- app_assoc. cbn [app]. apply Permutation_middle. }
    split; [rewrite (Hag' 1%uint63) by (change (to_Z 1%uint63) with 1; lia); exact Hrho1|].
    split; [exact Hmi'|].
    split.
    { apply (stk_merge ctusegs m' lo spc sp0 Hstk'); [|unfold spc; lia].
      destruct (stk_split ctusegs _ lo spc sp0 Hstk ltac:(unfold spc; lia)) as [_ (U1 & U2 & U3)].
      split; [exact U1|]. split; [exact U2|]. intros a Ha.
      destruct (Z_le_gt_dec mp a) as [L1|L1]; [destruct (Z_lt_ge_dec a (mp + 8)) as [L2|L2]|].
      - destruct Hmpc as [[_ Hbp] Hwp]. cbn [cells_bytes cbytes] in Hbp. rewrite app_nil_r in Hbp. destruct Hwp as (_ & _ & W). cbn [cells_size csize] in W.
        replace a with (mp + (a - mp)) by lia. split; [exact (W (a - mp) ltac:(lia))|].
        rewrite (bytes_at_mrd m' mp (le8 (Z_to_bv 64 A)) (a - mp) Hbp ltac:(rewrite length_le8; lia)).
        destruct (nth_error (le8 (Z_to_bv 64 A)) (Z.to_nat (a - mp))) as [b|] eqn:Enb; [exists b; reflexivity | apply nth_error_None in Enb; rewrite length_le8 in Enb; lia].
      - destruct (Hpresb a ltac:(lia) ltac:(left; lia) ltac:(cbn [fst snd]; lia)) as [E W]. destruct (U3 a Ha) as [Hw Hb].
        split; [exact (W Hw) | unfold mrd; rewrite E; exact Hb].
      - destruct (Hpresb a ltac:(lia) ltac:(left; lia) ltac:(cbn [fst snd]; lia)) as [E W]. destruct (U3 a Ha) as [Hw Hb].
        split; [exact (W Hw) | unfold mrd; rewrite E; exact Hb]. }
    split; [exact Haux'|].
    eapply agree_on_trans; [exact Hagr|]. eapply agree_on_mono; [exact (agree_of_heap_pres _ _ _ _ Hpres)|].
    intros a [_ Hc]. destruct Hc as [Hc|[(b & Hb & Hr)|Hc]]; [left; lia | right; right; exists b; split; [apply in_or_app; right; exact Hb | exact Hr] | right; left; exact Hc].
Qed.

End HookAligned.
