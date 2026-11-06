(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Agree MonadX Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import RunWord.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts Globals IcptA0 AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import InitStack EntrySecret.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim STree Monad Stdio Driver Prog.
From OSSVerify.pupnp.FuzzHttp.images Require Import Asan.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import AsanAcct.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7 Require Import RealizeS SeamA0 A0Prog AssembleA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7A0 Require Import ShadowKit GlobalsShadow Stdio_base Printf_lib F_printf_iface Stdio_iface F_printf_diag Exit RDriverA_kit RDriverA_ctx RDriverA_main RDriverA_exit RF_mainA_A.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7A0 Require Import F_syscalls RDriverA_lib RDriverA_iface RF_mainA_B1 RF_mainA_B2 RF_mainA_B3 RF_mainA_B4 RF_mainA_C RF_mainA_T RF_mainA_post RDriverA_seams.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].

Section PARSER.
  Context {HC : HasCeiling} {HG : HasGuard}.
  Variable FI : fs_if.
  Variable AI : am_if FI.
  Hypothesis AMS : forall lo hi, a0_static lo hi -> am_static FI AI lo hi.
  Variable PZ : mem -> Prop.
  Hypothesis PZ_agree : forall (P : Z -> Prop) m m', gagree_on P m m' -> (forall a, pz_band a -> P a) -> PZ m -> PZ m'.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw) (TID : Z) (S4 S5 S6 S7 S8 S9 S10 S11 : word).
  Hypothesis VSP : valid_sp sp0.
  Hypothesis CEIL : alloc_ceiling = LO sp0.
  Hypothesis ESF : entry_stack_fits sp0 argv envp.
  Hypothesis HT : 0 < TID < 2^31.
  Hypothesis AC : am_contracts FI AI (JA FI AI).
  Hypothesis FZ : fuzz_one_stmtA FI AI (JA FI AI) PZ.
  Local Notation K := (am_K FI AI).
  Local Notation BL := (list (AllocIF.block K)).
  Notation usp0 := (bv_unsigned sp0).
  Notation rat_callA' := (rat_callA FI AI PZ sp0 argv envp uid hw rnd TID S4 S5 S6 S7 S8 S9 S10 S11).
  Notation rat_retA' := (rat_retA FI AI PZ sp0 argv envp uid hw rnd TID S4 S5 S6 S7 S8 S9 S10 S11).
  Notation rat_free_ownedA' := (rat_free_ownedA FI AI PZ sp0 argv envp uid hw rnd TID S4 S5 S6 S7 S8 S9 S10 S11).
  Notation rat_owned_retA' := (rat_owned_retA FI AI PZ sp0 argv envp uid hw rnd TID S4 S5 S6 S7 S8 S9 S10 S11).
  Notation rat_free_bufA' := (rat_free_bufA FI AI PZ sp0 argv envp uid hw rnd TID S4 S5 S6 S7 S8 S9 S10 S11).
  Notation rat_main_retA' := (rat_main_retA FI AI PZ sp0 argv envp uid hw rnd TID S4 S5 S6 S7 S8 S9 S10 S11).

  #[using="Type"] Lemma in_lb_removeA : forall (p : K) (b : AllocIF.block K) (LB : BL),
    In b LB -> blk_id b <> p -> In b (lb_remove (am_K_eqb FI AI) p LB).
  Proof.
    intros p b LB Hin Hne. unfold lb_remove.
    induction LB as [|c LB IH]; [destruct Hin|]. rewrite filter_cons. destruct Hin as [->|Hin].
    - destruct (decide _) as [Y|N]; [left; reflexivity|]. exfalso. apply N.
      destruct (am_K_eqb FI AI (blk_id b) p) eqn:E; [| exact I]. exfalso. apply Hne. apply (proj1 (am_K_eqb_eq FI AI _ _)). exact E.
    - destruct (decide _) as [Y|N]; [right|]; apply IH; exact Hin.
  Qed.

  #[using="Type"] Lemma lb_bytes_filter_le : forall (f : AllocIF.block K -> bool) (LB : BL),
    (forall b, In b LB -> 0 <= blk_size b) -> lb_bytes FI AI (filter f LB) <= lb_bytes FI AI LB /\ (length (filter f LB) <= length LB)%nat.
  Proof.
    intros f LB H. induction LB as [|b LB IH]; [cbn; lia|].
    rewrite filter_cons. pose proof (H b ltac:(left; reflexivity)) as Hb.
    destruct (IH ltac:(intros b' Hb'; apply H; right; exact Hb')) as [IH1 IH2].
    unfold lb_bytes in *. destruct (decide _); cbn [fold_right length]; lia.
  Qed.

  #[using="Type"] Lemma no_leak_perm : forall s s' (LB LB' : BL) m m', RHEAP_A FI AI s LB m -> RHEAP_A FI AI s' LB' m' ->
    (forall b, In b LB -> In b LB') -> (forall b, In b LB' -> In b LB) -> Permutation LB LB'.
  Proof.
    intros s s' LB LB' m m' H H' I1 I2.
    apply Stdlib.Sorting.Permutation.NoDup_Permutation;
      [exact (List.NoDup_map_inv _ _ (proj1 (NoDup_ListNoDup _) (am_blocks_nodup FI AI _ _ _ H)))
      | exact (List.NoDup_map_inv _ _ (proj1 (NoDup_ListNoDup _) (am_blocks_nodup FI AI _ _ _ H')))|].
    intros b. split; [apply I1| apply I2].
  Qed.

  #[using="PZ_agree VSP CEIL ESF HT"] Lemma DMEM_below : forall ap d so m m',
    DMEM FI AI PZ sp0 argv envp uid hw rnd TID S4 S5 S6 S7 false ap d so m -> munch [(usp0 - 8388608, usp0 + -208)] m m' -> wmono asegs m m' ->
    mem_inv asegs m' -> stk asegs m' (usp0 - 8388608) (usp0 + -208) -> asan_env asegs m' ->
    DMEM FI AI PZ sp0 argv envp uid hw rnd TID S4 S5 S6 S7 false ap d so m'.
  Proof.
    intros ap d so m m' (TF & FR & BA & CJ) MU WM MI' ST' ENV'. pose proof (valid_sp_facts sp0 VSP) as SF. pose proof (sp_facts sp0 VSP CEIL) as SF'.
    split. { unfold TRFRAME in *. eapply rw_cells_transport; [exact TF| exact MU| exact WM| cbn [disjoint_from]; simpl_sizes; lia]. }
    split. { unfold MFRAME in *. eapply rw_cells_transport; [exact FR| exact MU| exact WM| cbn [disjoint_from]; simpl_sizes; lia]. }
    split.
    { assert (STF : stk asegs m' (usp0 - 8388608) (usp0 + -128)).
      { destruct BA as (ST & _). unfold LO in ST. assert (HQ' : usp0 - 8388608 <= usp0 + -208 <= usp0 + -128) by lia.
        destruct (stk_split asegs m _ (usp0 + -208) _ ST HQ') as [_ SThi].
        eapply stk_merge; [exact ST'| | lia]. eapply stk_transport_disjoint; [exact SThi| exact MU| exact WM| cbn [disjoint_from]; lia]. }
      apply BASE_cb_A2. apply BASE_cb_A2 in BA.
      eapply (BASE_A2_munch PZ PZ_agree sp0 argv envp uid hw rnd TID VSP CEIL ESF HT so); [exact BA| | exact MU| exact WM| exact MI'| unfold LO; exact STF| exact ENV'].
      unfold WOKA. constructor; [left; cbn [fst snd]; unfold LO; lia| constructor]. }
    destruct CJ as [X1 X2]. split; (eapply rw_cells_transport; [eassumption| exact MU| exact WM| cbn [disjoint_from]; simpl_sizes; lia]).
  Qed.

  #[using="AMS PZ_agree VSP CEIL ESF HT FZ"] Theorem parser_seamA : forall k fl ap d so ms g,
    rat_callA' k fl ap d so ms g -> SEAMr (fun ms' g' => rat_retA' k 0 fl ap d so ms' g') ms g.
  Proof.
    intros k fl ap d so ms g (t0 & t1 & t2 & a2 & a3 & a4 & a5 & a6 & a7 & x19 & t3 & t4 & t5 & t6 & F & fc & m & s & st & LB & -> & FRM & -> & HK & SM).
    pose proof (valid_sp_facts sp0 VSP) as SF. pose proof (sp_facts sp0 VSP CEIL) as SF'. pose proof (IMGB_len47 sp0 argv envp uid hw rnd ESF) as IL47. pose proof alloc_ceiling_bounds as CB'.
    pose proof (am_stack_ok FI AI) as SOK.
    destruct SM as ((OK & DM & DB & DBL & HP & RF & [errv ERR] & ST) & (BUD1 & BUD2 & FSL & NSR)).
    pose proof DM as (TF & FR & BA & CJ).
    pose proof BA as (STm & MI & EX & MC & IMG & SE & SOF & RSS & SI & SZ & ENV & GSH & HPZ & CRT). destruct MC as (G28 & GSE & [GG GU]). unfold got_ssp, ssp_guard in GG, GU.
    pose proof OK as (HC0 & HL & HCNT & HK4 & LEN & CAPM & LR & SCR & BR & OWN).

    assert (INP : exists data, bytes_at asegs m (d_AL d) data /\ Z.of_nat (length data) = ap_payload_len ap
                               /\ ((ap_payload_len ap = 0 /\ d_AL d = EMPTY_OBJ_A) \/ (exists kk, In (kk, d_AL d, ap_payload_len ap) LB))).
    { destruct DB as [B1 B2]. destruct DBL as [BL1 BL2]. specialize (B2 eq_refl). specialize (BL2 eq_refl).
      destruct (ap_owned ap) as [p|].
      - destruct OWN as (PL & EOW & BR2 & NE). exists (skipn (Z.to_nat (6 + d_L d)) (d_DATA d)).
        split; [| split; [unfold ap_payload_len, HDR_MIN; rewrite HC0, HL; unfold zlength; rewrite length_map, length_skipn; unfold ap_payload_len, HDR_MIN, zlength in PL; rewrite HC0, HL, length_map in PL; lia| right; exists (d_kp d); exact BL2]].
        pose proof (rw_cells_bytes_at _ _ _ _ B2) as X. cbn [cells_bytes cbytes app] in X. rewrite app_nil_r in X. exact X.
      - destruct OWN as (PL & EAL & EOW). exists []. split; [| split; [cbn; lia| left; split; [exact PL| exact EAL]]].
        rewrite EAL. unfold EMPTY_OBJ_A. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia. }
    destruct INP as (data & DAT & DLEN & DWHERE).
    destruct SZ as (SZ1 & SZ2 & SZ3 & [Z4 R4]).
    eapply SEAMr_mono.
    { eapply (FZ) with (lo := usp0 - 8388608) (data := data); rewrite ?unsigned_lit by lia;
        first [ exact DAT | exact DLEN | exact DWHERE | exact HP | exact RF | exact ENV | exact BUD1 | exact BUD2 | exact ST | exact ERR | exact MI | exact HPZ | exact GG | exact GU | exact FRM
              | (split; [unfold RATPA; rewrite unsigned_lit by lia; reflexivity| rewrite FSL; cbn [length]; unfold A0_FS_DEPTH; lia])
              | (unfold FZ_NSEC in *; lia)
              | reflexivity | lia | unfold PARSER_STACK_A; lia
              | clear -SF; Z.div_mod_to_equations; lia
              | apply (SHZ_cli sp0 argv envp uid hw rnd); [split; [exact SZ1| split; [exact SZ2| split; [exact SZ3| split; [exact Z4| exact R4]]]] | lia | lia | lia]
              | apply (SHZ_ro sp0 argv envp uid hw rnd); split; [exact SZ1| split; [exact SZ2| split; [exact SZ3| split; [exact Z4| exact R4]]]]
              | idtac ].
      - unfold ap_payload_len, HDR_MIN, zlength. rewrite HC0, HL, length_map. lia.
      - eapply shz_sub; [exact Z4| unfold sh, SHADOW_OFF; Z.div_mod_to_equations; lia| unfold sh, SHADOW_OFF, SH_HI; Z.div_mod_to_equations; lia].
      - eapply shr_sub; [exact R4| unfold sh, SHADOW_OFF; Z.div_mod_to_equations; lia| unfold sh, SHADOW_OFF, SH_HI; Z.div_mod_to_equations; lia]. }
    cbv beta. intros ms' g' (s' & LB' & -> & PO).
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & st' & -> & MI' & ST' & ENV' & RF' & PK & LIVE & HP' & KEEP & GONE & NSQ & HPZ' & ERR' & SHZ' & GG' & GU').
    pose proof (no_leak_perm _ _ _ _ _ _ HP HP' KEEP GONE) as PERM.
    rewrite ?unsigned_lit in ST' by lia. rewrite ?unsigned_lit in PK by lia. rewrite ?unsigned_lit in SHZ' by lia.
    replace (ret_pc (Z_to_bv 64 0x86410)) with (Z_to_bv 64 0x86410) by (symmetry; rpc).
    unfold rat_retA. do 18 eexists. exists m', s', st', LB'. split; [reflexivity|].
    split; [exact FRM|]. split; [reflexivity|]. split; [exact HK|]. split; [lia|].
    split; [|
      unfold DBUD; split; [rewrite <- (Permutation_length PERM); exact BUD1|]; split; [rewrite <- (lb_bytes_perm FI AI _ _ PERM); exact BUD2|];
      split; [rewrite LIVE; exact FSL| unfold FZ_NSEC in *; lia] ].
    split; [exact OK|].
    split; [eapply (DMEM_pkeep FI AI AMS PZ PZ_agree sp0 argv envp uid hw rnd TID S4 S5 S6 S7 VSP CEIL ESF HT); [exact DM| exact PK| exact MI'| unfold LO; exact ST'| exact ENV']|].
    split; [eapply (DBYTES_pkeep FI AI); [exact OK| exact DBL| exact DB| exact PK]|].
    split; [eapply DBLOCKS_mono; [exact DBL| exact KEEP]|].
    split; [exact HP'|]. split; [exact RF'|].
    split; [exact ERR'|].
    exact ST'.
  Qed.

  #[using="AMS PZ_agree VSP CEIL ESF HT AC"] Theorem free_owned_seamA : forall fl ap d so ms g,
    rat_free_ownedA' fl ap d so ms g -> SEAMr (fun ms' g' => rat_owned_retA' fl ap d so ms' g') ms g.
  Proof.
    intros fl ap d so ms g (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & x19 & t3 & t4 & t5 & t6 & F & fc & m & s & st & LB & -> & FRM & -> & SM).
    pose proof (valid_sp_facts sp0 VSP) as SF. pose proof (sp_facts sp0 VSP CEIL) as SF'. pose proof alloc_ceiling_bounds as CB'.
    pose proof (am_stack_ok FI AI) as SOK.
    destruct SM as (OK & DM & DB & DBL & HP & RF & [errv ERR] & ST).
    pose proof DM as (TF & FR & BA & CJ).
    pose proof BA as (STm & MI & EX & MC & IMG & SE & SOF & RSS & SI & SZ & ENV & GSH & HPZ & CRT).
    pose proof OK as (HC0 & HL & HCNT & HK4 & LEN & CAPM & LR & SCR & BR & OWN).
    destruct DBL as [BL1 BL2]. specialize (BL2 eq_refl).
    destruct (ap_owned ap) as [p|] eqn:EOWN.
    -
      destruct OWN as (PL & EOW & BR2 & NE).
      eapply SEAMr_mono.
      { eapply ((ac_free FI AI (JA FI AI) AC)) with (lo := usp0 - 8388608) (k := d_kp d) (A := d_AL d) (n := ap_payload_len ap) (ras := []);
          rewrite ?unsigned_lit by lia;
          first [ exact HP | exact BL2 | exact ENV | exact RF | exact ST | exact MI | reflexivity | rewrite EOW; reflexivity | lia | unfold A0_RT_STACK; lia
                | cbn [fpchain]; unfold valid_frame; lia
                | cbn; tauto
                | clear -SF; Z.div_mod_to_equations; lia ]. }
      cbv beta. intros ms' g' (s' & LB' & -> & PO).
      destruct PO as (w0 & w1 & w2 & ra0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m' & -> & AFR & -> & HP' & _).
      rewrite ?unsigned_lit in AFR by lia.
      replace (ret_pc (Z_to_bv 64 0x8643c)) with (Z_to_bv 64 0x8643c) by (symmetry; rpc).
      pose proof AFR as (MI' & ST' & ENV' & RF' & AP).
      unfold rat_owned_retA. do 19 eexists. exists m', s', st, (lb_remove (am_K_eqb FI AI) (d_kp d) LB). split; [reflexivity|].
      split; [exact FRM|]. split; [reflexivity|].
      assert (DBL' : DBLOCKS FI AI false ap d (lb_remove (am_K_eqb FI AI) (d_kp d) LB)).
      { split; [| intros X; discriminate X]. apply in_lb_removeA; [exact BL1| cbn; intros E; apply NE; symmetry; exact E]. }
      split; [exact OK|].
      split; [eapply (DMEM_alloc FI AI AMS PZ PZ_agree sp0 argv envp uid hw rnd TID S4 S5 S6 S7 VSP CEIL ESF HT); [exact DM| unfold LO; exact AFR]|].
      split; [eapply (DBYTES_alloc FI AI); [exact OK| exact DBL'| apply DBYTES_drop; exact DB| unfold LO; exact AFR]|].
      split; [exact DBL'|].
      split; [exact HP'|]. split; [exact RF'|].
      split. { exists errv. unfold RERRNOA in *. eapply (apres_rw_cells FI AI); [exact AP| exact ERR| eapply (aclient_range_static FI AI _ _ _ _ 0x5e68c8 0x5e68d0); [apply AMS; unfold a0_static; lia| cbn; lia| cbn; lia]]. }
      exact ST'.
    -
      destruct OWN as (PL & EAL & EOW).
      eapply SEAMr_evt.
      { eapply ((ac_free_null FI AI (JA FI AI) AC)) with (lo := usp0 - 8388608) (ras := []); rewrite ?unsigned_lit by lia;
          first [ exact HP | exact ENV | exact RF | exact ST | exact MI | rewrite EOW; reflexivity | reflexivity | lia | unfold A0_RT_STACK; lia
                | cbn [fpchain]; unfold valid_frame; lia
                | cbn; tauto
                | clear -SF; Z.div_mod_to_equations; lia ]. }
      cbv beta. intros ms' (w0 & w1 & w2 & ra0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m' & -> & AFR & WM & HP').
      rewrite ?unsigned_lit in AFR by lia.
      replace (ret_pc (Z_to_bv 64 0x8643c)) with (Z_to_bv 64 0x8643c) by (symmetry; rpc).
      pose proof AFR as (MI' & ST' & ENV' & RF' & AP).
      apply SEAMr_ret. unfold rat_owned_retA. do 19 eexists. exists m', s, st, LB. split; [reflexivity|].
      split; [exact FRM|]. split; [reflexivity|].
      assert (DBL' : DBLOCKS FI AI false ap d LB) by (split; [exact BL1| intros X; discriminate X]).
      split; [exact OK|].
      split; [eapply (DMEM_alloc FI AI AMS PZ PZ_agree sp0 argv envp uid hw rnd TID S4 S5 S6 S7 VSP CEIL ESF HT); [exact DM| unfold LO; exact AFR]|].
      split; [eapply (DBYTES_alloc FI AI); [exact OK| exact DBL'| apply DBYTES_drop; exact DB| unfold LO; exact AFR]|].
      split; [exact DBL'|].
      split; [exact HP'|]. split; [exact RF'|].
      split. { exists errv. unfold RERRNOA in *. eapply (apres_rw_cells FI AI); [exact AP| exact ERR| eapply (aclient_range_static FI AI _ _ _ _ 0x5e68c8 0x5e68d0); [apply AMS; unfold a0_static; lia| cbn; lia| cbn; lia]]. }
      exact ST'.
  Qed.

  #[using="AMS PZ_agree VSP CEIL ESF HT AC"] Theorem free_buf_seamA : forall sts ap d so ms g,
    rat_free_bufA' sts ap d so ms g -> SEAMr (fun ms' g' => rat_main_retA' sts so ms' g') ms g.
  Proof.
    intros sts ap d so ms g (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & m & s & st & LB & -> & FRM & -> & HST
                              & OK & FR & BA & CJ & DB & DBL & HP & RF & [errv ERR] & ST).
    pose proof (valid_sp_facts sp0 VSP) as SF. pose proof (sp_facts sp0 VSP CEIL) as SF'. pose proof alloc_ceiling_bounds as CB'.
    pose proof (am_stack_ok FI AI) as SOK.
    pose proof BA as (STm & MI & EX & MC & IMG & SE & SOF & RSS & SI & SZ & ENV & GSH & HPZ & CRT).
    destruct DBL as [BL1 _].
    eapply SEAMr_mono.
    { eapply ((ac_free_any FI AI (JA FI AI) AC)) with (lo := usp0 - 8388608) (k := d_kb d) (A := d_A d) (n := d_cap d);
        rewrite ?unsigned_lit by lia;
        first [ exact HP | exact BL1 | exact ENV | exact RF | exact ST | exact MI | reflexivity | lia | unfold A0_RT_STACK; lia
              | cbn [fpchain]; unfold valid_frame; lia
              | cbn; tauto
              | clear -SF; Z.div_mod_to_equations; lia ]. }
    cbv beta. intros ms' g' (s' & LB' & -> & PO).
    destruct PO as (w0 & w1 & w2 & ra0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m' & -> & AFR & -> & HP' & _).
    rewrite ?unsigned_lit in AFR by lia.
    replace (ret_pc (Z_to_bv 64 0x86270)) with (Z_to_bv 64 0x86270) by (symmetry; rpc).
    pose proof AFR as (MI' & ST' & ENV' & RF' & AP).
    unfold rat_main_retA. do 23 eexists. exists m', (d_mpad d), s', st, (lb_remove (am_K_eqb FI AI) (d_kb d) LB). split; [reflexivity|].
    split; [reflexivity|]. split; [exact HST|].
    split; [unfold MFRAME in *; eapply (apres_rw_cells FI AI); [exact AP| exact FR| apply aclient_range_above; lia]|].
    split; [eapply (BASE_A2_alloc FI AI AMS PZ PZ_agree sp0 argv envp uid hw rnd TID VSP CEIL ESF HT so); [exact BA| unfold LO; exact AFR]|].
    split; [exact HP'|]. split; [exact RF'|]. exact ST'.
  Qed.
End PARSER.
