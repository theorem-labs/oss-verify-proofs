(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 BsWalk BXXRep RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_Own LbB_DStat LbB_ContStmt LbB_ContV4 LbB_ContVot LbB_TablStmt LbB_TablOS.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_TablPT4 LbB_TablPT6 LbB_TablPT8 LbB_TablPT9 LbB_TablPT11 LbB_TablXP1 LbB_TablXPk1 LbB_TablTF1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section TFk.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

  Record tfent : Type := TFEnt {
    t_ra : word; t_sp : word; t_gp : word; t_tp : word;
    t_s0 : word; t_s1 : word; t_s2 : word; t_s3 : word; t_s4 : word; t_s5 : word;
    t_s6 : word; t_s7 : word; t_s8 : word; t_s9 : word; t_s10 : word; t_s11 : word;
    t_F : bvmap 5 word; t_fc : bv 32; t_m : mem; t_mo : Model;
    t_s : as_St H; t_LB : list block; t_LF : list fframe;
    t_v : Z; t_b : Z; t_cap : Z; t_xs : list Z; t_pid : bptr;
    t_lo : Z; t_B : Z; t_shi : Z }.

  Definition tSP (e : tfent) : Z := bv_unsigned (t_sp e).
  Definition tcapm (e : tfent) : Z := capmax (Zlen (t_xs e) - 1) (t_cap e) 3.

  Definition tXE (e : tfent) (XS : list (Z * Z)) : list (Z * Z) := (t_v e, t_v e + 24) :: v4_oldx (t_b e) (4 * t_cap e) ++ XS.

  Definition tsaved (e : tfent) : list cell :=
    [C8 (t_s8 e); C8 (t_s7 e); C8 (t_s6 e); C8 (t_s5 e); C8 (t_s4 e); C8 (t_s3 e); C8 (t_s2 e); C8 (t_s1 e); C8 (t_s0 e); C8 (t_ra e)].

  Definition tpre (e : tfent) : Prop :=
    let SP := tSP e in let v := t_v e in let LB := t_LB e in let LF := t_LF e in let lo := t_lo e in
       SP mod 16 = 0 /\ SP <= 2 ^ 47 /\ SP <= t_B e /\ SP <= t_shi e /\ aceil <= lo /\ lo <= SP - TF_STACK
    /\ afsb_ok H /\ (length LF < AFS_MAXLIVE_BP)%nat
    /\ t_tp e = Z_to_bv 64 ATP /\ bv_unsigned (t_ra e) mod 2 = 0
    /\ v mod 8 = 0 /\ ((0x6e8000 <= v /\ v + 24 <= 0x7fff7000) \/ (0x10007fff8000 <= v /\ v + 24 <= 2 ^ 47))
    /\ obj_win H LB LF SP lo v 24
    /\ v4_oldblk LB (t_b e) (t_cap e) (t_pid e) /\ List.NoDup (map blk_id LB) /\ as_RHEAP H (t_s e) LB (t_m e)
    /\ (4 * tcapm e <= 2 ^ 26 /\ closs (t_cap e) (tcapm e) <= as_AL H (t_s e)) /\ lb_small LB + 3 * 64512 <= RT_SMALL_MAX
    /\ Z.of_nat (length LB) + 2 <= RT_CNT_MAX /\ nlarge LB + 2 <= RT_LARGE_MAX
    /\ trace_ok (as_TR H) APC0_FREE [v4_del_ra VOT_SLOW_CREF] /\ trace_ok (as_TR H) APC0_FREE [v4_del_ra VOT_SLOW_RREF]
    /\ 0 <= as_AL H (t_s e)
    /\ 1 <= Zlen (t_xs e) <= t_cap e /\ t_b e <> 0
    /\ ((0 <= t_b e /\ t_b e + 4 * t_cap e <= 0x7fff7000) \/ (0x10007fff8000 <= t_b e /\ t_b e + 4 * t_cap e <= 2 ^ 47))
    /\ (t_v e + 24 <= t_b e \/ t_b e + 4 * t_cap e <= t_v e)
    /\ Forall (fun t => 0 <= t < 2 ^ 31) (t_xs e)
    /\ relro0 (t_m e).

  Definition tgrown (e : tfent) (LBi : list block) (bi capi : Z) (pidi : bptr) : Prop :=
    (capi = t_cap e /\ bi = t_b e /\ LBi = t_LB e /\ pidi = t_pid e)
    \/ (t_cap e < capi <= tcapm e /\ LBi = v4_newLB H (t_LB e) (t_b e) (t_pid e) pidi bi (4 * capi)
        /\ ablock_range H bi (4 * capi)).

  Definition tframe (e : tfent) (mL : mem) (sL : as_St H) (LBi : list block) (eL : word) : Prop :=
    let SP := tSP e in
       mem_inv asegs mL /\ ACONST mL /\ stk asegs mL (t_lo e) SP /\ stack0 mL (t_lo e) (t_shi e)
    /\ rw_cells asegs mL (errno_addr (t_tp e)) [C4 eL] /\ as_rauxv_ok H mL (t_B e)
    /\ rw_cells asegs mL (SP - 80) (tsaved e)
    /\ as_RFS H (t_LF e) mL /\ as_RHEAP H sL LBi mL /\ lb_own LBi mL /\ relro0 mL.

  Definition tvec (e : tfent) (ys : list Z) (mL : mem) (LBi : list block) (bi capi : Z) (pidi : bptr) : Prop :=
    let v := t_v e in
       vec32A LBi mL v bi ys capi /\ (0 < capi -> SHAD mL bi (cc_gen (4 * capi) (4 * Zlen ys)))
    /\ addressable mL v 24 /\ wr_at asegs mL v 24
    /\ v4_oldblk LBi bi capi pidi /\ tgrown e LBi bi capi pidi /\ Forall (fun t => 0 <= t < 2 ^ 31) ys.

  Definition tmem (e : tfent) (ys : list Z) (XS : list (Z * Z)) (mL : mem) (sL : as_St H) (LBi : list block) (bi capi : Z)
      (pidi : bptr) (eL : word) : Prop :=
       tframe e mL sL LBi eL /\ tvec e ys mL LBi bi capi pidi
    /\ Forall (fs_scratch H (t_LF e)) XS /\ xpres H (t_LB e) (tSP e) (tXE e XS) (t_m e) mL
    /\ as_AL H sL >= as_AL H (t_s e) - closs (t_cap e) capi.

  Definition tregs (e : tfent) (R : bvmap 5 word) : Prop :=
    let v := t_v e in
       getr R 2 = Z_to_bv 64 (tSP e - 80) /\ getr R 3 = t_gp e /\ getr R 4 = t_tp e
    /\ getr R 8 = Z_to_bv 64 v /\ getr R 9 = Z_to_bv 64 (v + 8) /\ getr R 18 = Z_to_bv 64 (v + 16) /\ getr R 20 = Z_to_bv 64 5
    /\ getr R 21 = Z_to_bv 64 0x7fff8000 /\ getr R 22 = Z_to_bv 64 (sh (v + 8)) /\ getr R 23 = Z_to_bv 64 (sh v)
    /\ getr R 24 = Z_to_bv 64 (sh (v + 16)) /\ getr R 25 = t_s9 e /\ getr R 26 = t_s10 e /\ getr R 27 = t_s11 e.

  Definition th (e : tfent) (ys : list Z) (XS : list (Z * Z)) (LBi : list block) (bi capi : Z) (pidi : bptr) (cf : config) : Prop :=
    exists R mL sL eL,
      as_VIS H sL (cfg_ms cf) = MS R (t_F e) (Z_to_bv 64 TF_HEAD) (t_fc e) None mL (seg_rom asegs) /\ rfull R /\ tregs e R
      /\ as_AKREL H sL cf /\ as_MPRES H (t_mo e) (cfg_model cf)
      /\ tmem e ys XS mL sL LBi bi capi pidi eL.

  Definition tx (e : tfent) (ys : list Z) (t r : Z) (XS : list (Z * Z)) (LBi : list block) (bi capi : Z) (pidi : bptr) (cf : config) : Prop :=
    exists R mL sL eL,
      as_VIS H sL (cfg_ms cf) = MS R (t_F e) (Z_to_bv 64 TF_XP_RET) (t_fc e) None mL (seg_rom asegs) /\ rfull R /\ tregs e R
      /\ getr R 19 = Z_to_bv 64 t /\ getr R 10 = Z_to_bv 64 r
      /\ as_AKREL H sL cf /\ as_MPRES H (t_mo e) (cfg_model cf)
      /\ tmem e ys XS mL sL LBi bi capi pidi eL.
End TFk.
Arguments t_ra {H} _. Arguments t_sp {H} _. Arguments t_gp {H} _. Arguments t_tp {H} _.
Arguments t_s0 {H} _. Arguments t_s1 {H} _. Arguments t_s2 {H} _. Arguments t_s3 {H} _. Arguments t_s4 {H} _.
Arguments t_s5 {H} _. Arguments t_s6 {H} _. Arguments t_s7 {H} _. Arguments t_s8 {H} _. Arguments t_s9 {H} _.
Arguments t_s10 {H} _. Arguments t_s11 {H} _. Arguments t_F {H} _. Arguments t_fc {H} _. Arguments t_m {H} _.
Arguments t_mo {H} _. Arguments t_s {H} _. Arguments t_LB {H} _. Arguments t_LF {H} _.
Arguments t_v {H} _. Arguments t_b {H} _. Arguments t_cap {H} _. Arguments t_xs {H} _. Arguments t_pid {H} _.
Arguments t_lo {H} _. Arguments t_B {H} _. Arguments t_shi {H} _.
Arguments tSP {H} _. Arguments tcapm {H} _. Arguments tXE {H} _ _. Arguments tsaved {H} _.

Section TFkit.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HB : asan_rt_hyps H.

  Lemma tgrown_blocks : forall (e : tfent H) LBi bi capi pidi, tpre H e -> tgrown H e LBi bi capi pidi ->
    forall bb, In bb (t_LB e) -> In bb LBi \/ (bb = (t_pid e, t_b e, 4 * t_cap e) /\ 0 < t_cap e /\ t_b e <> 0).
  Proof.
    intros e LBi bi capi pidi P GR bb Hb.
    destruct P as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & OLD & ND & _).
    destruct GR as [(_ & _ & -> & _)|(_ & -> & _)]; [left; exact Hb|].
    unfold v4_newLB. destruct (Z.eqb_spec (t_b e) 0) as [B0|B0]; [left; right; exact Hb|].
    destruct OLD as [(E0 & _)|(C0 & HIn)]; [contradiction|].
    destruct (Z.eq_dec (blk_id bb) (t_pid e)) as [E|NE].
    - right. destruct bb as [[pb Ab] nb]. cbn [blk_id fst] in E. subst pb.
      pose proof (LbB_ContV4.nodup_id_same _ _ _ _ _ _ ND HIn Hb) as EQ. rewrite <- EQ. split; [reflexivity|]. split; [exact C0 | exact B0].
    - left. right. exact (LbB_ContV4.lb_remove_keep H HB _ _ _ ND Hb NE).
  Qed.

  Lemma tgrown_tail : forall (e : tfent H) LBi bi capi pidi, tpre H e ->
    LBi = v4_newLB H (t_LB e) (t_b e) (t_pid e) pidi bi (4 * capi) ->
    exists LBt, LBi = (pidi, bi, 4 * capi) :: LBt
      /\ (forall bb, In bb (t_LB e) -> In bb LBt \/ (bb = (t_pid e, t_b e, 4 * t_cap e) /\ 0 < t_cap e /\ t_b e <> 0)).
  Proof.
    intros e LBi bi capi pidi P EQ.
    destruct P as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & OLD & ND & _).
    unfold v4_newLB in EQ. destruct (Z.eqb_spec (t_b e) 0) as [B0|B0].
    - exists (t_LB e). split; [exact EQ|]. intros bb Hb. left. exact Hb.
    - exists (as_lb_remove H (t_pid e) (t_LB e)). split; [exact EQ|]. intros bb Hb.
      destruct OLD as [(E0 & _)|(C0 & HIn)]; [contradiction|].
      destruct (Z.eq_dec (blk_id bb) (t_pid e)) as [E|NE].
      + right. destruct bb as [[pb Ab] nb]. cbn [blk_id fst] in E. subst pb.
        pose proof (LbB_ContV4.nodup_id_same _ _ _ _ _ _ ND HIn Hb) as EQ2. rewrite <- EQ2. split; [reflexivity|]. split; [exact C0 | exact B0].
      + left. exact (LbB_ContV4.lb_remove_keep H HB _ _ _ ND Hb NE).
  Qed.

  Lemma tXE_old : forall (e : tfent H) XS a, 0 < t_cap e -> t_b e <> 0 ->
    (t_b e <= a < t_b e + 4 * t_cap e \/ sh (t_b e) <= a < sh (t_b e) + nsh (4 * t_cap e)) -> rin_ivs (tXE e XS) a.
  Proof.
    intros e XS a C0 B0 Ha. unfold tXE, v4_oldx. destruct (Z.eqb_spec (t_b e) 0) as [E|_]; [contradiction|].
    cbn [rin_ivs app fst snd]. right. destruct Ha as [Ha|Ha]; [left; exact Ha | right; left; exact Ha].
  Qed.

  Lemma tXE_mono : forall (e : tfent H) XS XS' a, rin_ivs (tXE e XS) a -> rin_ivs (tXE e (XS ++ XS')) a.
  Proof.
    intros e XS XS' a Ha. unfold tXE in *. cbn [rin_ivs] in *. destruct Ha as [Ha|Ha]; [left; exact Ha|]. right.
    rewrite rin_ivs_app in Ha. rewrite rin_ivs_app. destruct Ha as [Ha|Ha]; [left; exact Ha|]. right. rewrite rin_ivs_app. left. exact Ha.
  Qed.

  Lemma tf_xp_step : forall (e : tfent H) XS LBi bi capi pidi sL mL m1 m2 W,
    tpre H e -> tgrown H e LBi bi capi pidi -> as_RHEAP H sL LBi mL -> 0 < capi ->
    munch W m1 m2 -> wmono asegs m1 m2 ->
    Forall (fun iv : Z * Z => (bi <= fst iv /\ snd iv <= bi + 4 * capi) \/ (sh bi <= fst iv /\ snd iv <= sh bi + nsh (4 * capi))
                              \/ (aceil <= fst iv /\ snd iv <= tSP e) \/ (forall a, fst iv <= a < snd iv -> rin_ivs (tXE e XS) a)) W ->
    xpres H (t_LB e) (tSP e) (tXE e XS) m1 m2.
  Proof.
    intros e XS LBi bi capi pidi sL mL m1 m2 W P GR RH C0 MU WM FW.
    pose proof P as (_ & _ & _ & _ & CE & LO & _ & _ & _ & _ & _ & _ & _ & OLD & ND & RH0 & _).
    destruct GR as [(E1 & E2 & E3 & E4)|(G1 & G2 & G3)].
    - subst capi bi LBi pidi.
      assert (B0 : t_b e <> 0).
      { destruct OLD as [(X & Y)|(X & Y)]; [lia|].
        pose proof (ah_blocks H HB _ _ _ _ RH0 Y) as (A0 & _). unfold blk_addr in A0. cbn [fst snd] in A0. lia. }
      eapply (xpres_of_munch H (t_s e) (t_LB e) (tSP e) (tXE e XS) W (t_m e) m1 m2); [exact HB | exact RH0 | exact MU | exact WM |].
      eapply Forall_impl; [|exact FW]. intros [l h] K. cbn [fst snd] in *.
      destruct K as [K|[K|[K|K]]]; [right | right | left; exact K | right; exact K].
      + intros a Ha. apply tXE_old; [exact C0 | exact B0 | left; lia].
      + intros a Ha. apply tXE_old; [exact C0 | exact B0 | right; lia].
    - destruct (tgrown_tail e LBi bi capi pidi P G2) as (LBt & EL & BL).
      rewrite EL in RH.
      assert (NI : ~ In pidi (map blk_id LBt)).
      { pose proof (ah_nodup H HB _ _ _ RH) as NDi. cbn [map] in NDi. apply NoDup_cons_iff in NDi as [X _]. exact X. }
      pose proof (aceil_facts) as ACF.
      assert (SPc : aceil <= tSP e).
      { unfold TF_STACK, AFS_STACK, AINTRIN_STACK, V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LO. lia. }
      pose proof (pt_xp_munch H HB sL LBt pidi bi (4 * capi) (tSP e) (tXE e XS) W mL m1 m2 RH NI SPc MU WM FW) as XP.
      eapply (pt_xp_lift H LBt (tSP e) (tXE e XS) (t_LB e) (tSP e) (tXE e XS) m1 m2 XP ltac:(lia)); [|intros a Ha; exact Ha].
      intros bb Hb. destruct (BL bb Hb) as [IN|(EQ & Cc & Bc)]; [left; exact IN|].
      right. intros a Ha. subst bb. cbn [blk_addr blk_size fst snd] in Ha. apply tXE_old; [exact Cc | exact Bc | exact Ha].
  Qed.

  Lemma tvec_blk : forall (e : tfent H) ys mL sL LBi bi capi pidi, as_RHEAP H sL LBi mL -> tvec H e ys mL LBi bi capi pidi ->
    0 <= Zlen ys <= capi /\ ((capi = 0 /\ bi = 0) \/ (0 < capi /\ In (pidi, bi, 4 * capi) LBi /\ ablock_range H bi (4 * capi)))
    /\ (bi <> 0 -> t_v e + 24 <= bi \/ bi + 4 * capi <= t_v e).
  Proof.
    intros e ys mL sL LBi bi capi pidi RH PV. destruct PV as (VEC & _ & _ & _ & OB & _).
    pose proof VEC as (_ & _ & _ & Hlen & Hb & _).
    split; [exact Hlen|]. split.
    - destruct OB as [(E0 & E1)|(C0 & HIn)]; [left; split; assumption|].
      right. split; [exact C0|]. split; [exact HIn|]. exact (ah_blocks H HB _ _ _ _ RH HIn).
    - intros NZ. destruct Hb as [(E0 & _)|(_ & _ & _ & _ & _ & D)]; [contradiction | exact D].
  Qed.

  Lemma tframe_munch : forall (e : tfent H) mL M sL LBi eL W,
    tpre H e -> tframe H e mL sL LBi eL -> munch W mL M -> wmono asegs mL M -> mem_inv asegs M ->
    stk asegs M (t_lo e) (tSP e) ->
    Forall (fun iv => aclient_write_ok H LBi iv /\ afs_write_ok H (t_LF e) iv /\ aconst_ok iv /\ stack0_ok iv
                      /\ (snd iv <= ATP - 164 \/ ATP - 160 <= fst iv) /\ (snd iv <= tSP e - 80 \/ tSP e <= fst iv)
                      /\ (snd iv <= 0x17e000 \/ 0x186000 <= fst iv)) W ->
    tframe H e M sL LBi eL.
  Proof.
    intros e mL M sL LBi eL W P PF MU WM MI SK FW.
    destruct PF as (MI0 & AC0 & ST0 & S00 & ER0 & RA0 & SV0 & RF0 & RH0 & OW0 & RR0).
    pose proof P as (_ & _ & _ & _ & _ & _ & _ & _ & TP & _).
    destruct (client_frame H HB sL LBi (t_LF e) (t_B e) W mL M RH0 RF0 AC0 RA0 MU WM
                (Forall_impl _ (fun iv X => proj1 X) FW)
                (Forall_impl _ (fun iv X => proj1 (proj2 X)) FW)
                (Forall_impl _ (fun iv X => proj1 (proj2 (proj2 X))) FW)) as (RH1 & RF1 & AC1 & RA1).
    assert (ERA : errno_addr (t_tp e) = ATP - 164) by (rewrite TP, HLib.u64_of_Z by (unfold ATP; lia); lia).
    unfold tframe.
    split; [exact MI|]. split; [exact AC1|]. split; [exact SK|].
    split; [eapply stack0_transport; [exact S00 | exact MU | exact WM | exact (Forall_impl _ (fun iv X => proj1 (proj2 (proj2 (proj2 X)))) FW)]|].
    split.
    { eapply rw_cells_transport; [exact ER0 | exact MU | exact WM |]. rewrite ERA. apply dj_of_Forall.
      eapply Forall_impl; [|exact FW]. intros iv X. destruct X as (_ & _ & _ & _ & X & _). cbn. lia. }
    split; [exact RA1|].
    split.
    { eapply rw_cells_transport; [exact SV0 | exact MU | exact WM |]. apply dj_of_Forall.
      eapply Forall_impl; [|exact FW]. intros iv X. destruct X as (_ & _ & _ & _ & _ & X & _). cbn. lia. }
    split; [exact RF1|]. split; [exact RH1|]. split; [exact (lb_own_wmono _ _ _ OW0 WM)|].
    intros i Hi. rewrite (MU (Z_to_bv 64 i)); [apply RR0; exact Hi|].
    rewrite u64_of_Z by lia. eapply (disjoint_outside W 0x17e000 (0x186000 - 0x17e000)); [|lia].
    apply dj_of_Forall. eapply Forall_impl; [|exact FW]. intros iv X. destruct X as (_ & _ & _ & _ & _ & _ & X). cbn [fst snd]. lia.
  Qed.
End TFkit.
