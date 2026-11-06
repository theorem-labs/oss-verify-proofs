(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From stdpp Require list.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts ATac IcptA0 AllocA0 ATacAp.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.T7A0 Require Import ShadowKit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.AW Require Import HttpAllocA HttpRepA AWKit H_membuffer_assign_seg.
Import ListNotations.
Open Scope Z_scope.

Section W.
Context {HC : HasCeiling}.
Hypothesis IC : icpt_contracts.

Variable FI : fs_if.
Variable AI : am_if FI.
Variable J : a0_judg FI AI.
Variable AC : am_contracts FI AI J.
Hypothesis ASL : forall lo hi, am_static FI AI lo hi -> a0_static lo hi.
Hypothesis AMS : forall lo hi, a0_static lo hi -> am_static FI AI lo hi.
Local Notation K := (am_K FI AI).
Local Notation BL := (list (block K)).

#[using="IC AC ASL AMS"] Theorem membuffer_assign_spec_A : membuffer_assign_stmt_A FI AI J.
Proof.
  intros ra q gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB st ok MB SRC n A len cap lo src bs.
  intros HR RF AE ST CLO LO QAL QTOP MI MBC HLC HNC BUD OWN MBL MBHI AL SHWM SRCB LEN S0 MSRC SHWS SRCHI DJS -> -> ->.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (am_stack_ok FI AI) as (TK1 & TK2 & TK3 & TK4).
  pose proof (bytes_at_bound _ _ _ _ SRCB) as BB.
  assert (N0 : 0 <= n) by lia.
  assert (LO' : lo <= q - 96 - 4096) by (unfold A0_RT_STACK in LO; exact LO). clear LO.
  assert (QC : alloc_ceiling <= q + -96) by lia.
  assert (SUB : forall b, In b (lb_keepA FI AI ok LB) -> In b LB) by (intros b Hb; eapply (lb_keepA_sub FI AI); exact Hb).
  destruct (mblocA_range FI AI s LB _ q st m MB 32 HR SUB RF MBL ltac:(lia) ltac:(lia)) as (MBLO & _ & _).
  destruct (msrcA_lo FI AI s LB _ q st m SRC n HR SUB RF MSRC ltac:(lia) N0) as (_ & SLO & SHI47).
  assert (SLOx : SRC + n <= alloc_ceiling \/ (q <= SRC /\ SRC + n < 2^47)) by (clear - SLO SRCHI; lia). clear SLO. rename SLOx into SLO.
  pose proof (shw_win_ok _ _ _ SHWM) as WK.
  assert (SUBNE : forall k, ok = Some k -> forall b, In b (lb_keepA FI AI ok LB) -> In b LB /\ b <> (k, A, cap + 1)).
  { intros k -> b Hb. split; [apply SUB; exact Hb|]. cbn in Hb. intros ->. exact (lb_remove_neq FI AI _ _ _ Hb eq_refl). }
  assert (ARNG : 0 <= A < 2^64 /\ (ok <> None -> 0x609000 <= A /\ A + (cap + 1) + 16 <= alloc_ceiling /\ A mod 16 = 0)).
  { destruct ok as [k|]; cbn in OWN.
    - destruct OWN as [HIN _]. destruct (am_block_range FI AI s LB m _ HR HIN) as (R1 & R2 & R3 & R4 & R5 & R5d & _). cbn [blk_addr blk_size fst snd] in *. split; [lia|]. intros _. lia.
    - destruct OWN as (-> & _). split; [lia|]. intros X; contradiction. }
  destruct ARNG as [ARNG ABLK].

  eapply (aj_evt FI AI J). { eapply (asegA lo MB SRC n A len cap); try eassumption; try lia. exact (proj1 SHWM). }
  intros ms' (m1 & pad & x1 & a0' & a1' & a2' & a3' & x23 & x24 & x25 & pc & nsz & -> & MU1 & WM1 & MI1 & ST1 & FR1 & MBC1 & CASES).
  assert (BIV1 : Forall (blk_iv FI AI LB) [(lo, q)]) by (constructor; [left; cbn; lia| constructor]).
  pose proof (rheap_blk_write FI AI s LB m m1 _ HR MU1 WM1 BIV1) as HR1.
  pose proof (rfake_blk_write FI AI s LB st m m1 _ HR RF MU1 WM1 ltac:(constructor; [split; [left; cbn; lia| cbn; lia]| constructor])) as RF1.
  pose proof (asan_env_frame asegs m m1 _ AE MU1 WM1 (env_safe_blk FI AI s LB m _ HR BIV1)) as AE1.
  pose proof (shw_frame _ m m1 MB 32 SHWM MU1 (app_ivs_blk FI AI s LB m _ HR BIV1)) as SHWM1.
  pose proof (shw_frame _ m m1 SRC n SHWS MU1 (app_ivs_blk FI AI s LB m _ HR BIV1)) as SHWS1.
  pose proof (bytes_at_transport asegs _ m m1 _ _ SRCB MU1 ltac:(cbn; lia)) as SRCB1.
  assert (OWN1 : mownA FI AI m1 LB A cap ok bs).
  { destruct ok as [k|]; cbn in OWN |- *; [| exact OWN]. destruct OWN as [HIN BLK]. split; [exact HIN|].
    specialize (ABLK ltac:(discriminate)). eapply rw_cells_transport; [exact BLK| exact MU1| exact WM1| cbn [disjoint_from cells_size csize Nat.add]; lia]. }
  assert (HP1 : apx FI AI [(MB, MB + 32)] (lb_keepA FI AI ok LB) q m m1).
  { eapply (apx_seg FI AI ASL s LB _ q _ _ m m m1 HR SUB MU1 WM1). constructor; [left; cbn; lia| constructor]. }

  assert (FIN : forall sx (LBx : BL) m2 A' len' cap' (ok' : option K) (bs' : list byte)
                  (y1 b0 b2 b3 y23 y24 y25 u0 u1 u2 b4 b5 b6 b7 u3 u4 u5 u6 : word),
    mem_inv asegs m2 -> stk asegs m2 lo (q + -96) -> asan_env asegs m2 -> RFAKE FI st m2 -> RHEAP_A FI AI sx LBx m2 ->
    rw_cells asegs m2 (q + -96) [CB 8 pad; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs m2 MB (mbuf_cells A' len' cap') -> shw m2 MB 32 ->
    bytes_at asegs m2 SRC src -> shw m2 SRC n ->
    n <= cap' -> cap' <= cap + n + 5 -> mownA FI AI m2 LBx A' cap' ok' bs' ->
    ((ok' = ok /\ LBx = LB /\ A' = A /\ cap' = cap /\ am_nsec FI AI sx = am_nsec FI AI s)
     \/ (exists k', ok' = Some k' /\ LBx = (k', A', cap' + 1) :: lb_keepA FI AI ok LB /\ am_nsec FI AI sx = am_nsec FI AI s + nsec1 (cap' + 1))) ->
    apx FI AI [(MB, MB + 32)] (lb_keepA FI AI ok LB) q m m2 ->
    AJ FI AI J (membuffer_assign_post_A FI AI ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st s LB ok MB A cap n lo src m)
      (MS (mkR y1 (wz (q + -96)) gp (wz A0_TP) u0 u1 u2 (wz MB) (wz n) b0 (wz SRC) b2 b3 b4 b5 b6 b7
               (wz (MB + 8)) (wz (MB + 16)) (wz 0x7fff8000) (wz (Z.shiftr (MB + 8) 3 + 2147450880)) (wz (Z.shiftr MB 3))
               y23 y24 y25 s10 s11 u3 u4 u5 u6)
          F (wz 0x8cc08) fc None m2 (seg_rom asegs)) sx LBx).
  { intros sx LBx m2 A' len' cap' ok' bs' y1 b0 b2 b3 y23 y24 y25 u0 u1 u2 b4 b5 b6 b7 u3 u4 u5 u6.
    intros MI2 ST2 AE2 RF2 HR2 FR2 MBC2 SHWM2 SRCB2 SHWS2 NC CC OWN2 SHAPE HP2.
    assert (SUBx : forall b, In b (lb_keepA FI AI ok LB) -> In b LBx).
    { destruct SHAPE as [(_ & -> & _)|(k' & _ & -> & _)]; [exact SUB| intros b Hb; right; exact Hb]. }

    assert (SUBNEx : forall k', ok' = Some k' -> forall b, In b (lb_keepA FI AI ok LB) -> In b LBx /\ b <> (k', A', cap' + 1)).
    { intros k' E b Hb. destruct SHAPE as [(E1 & -> & -> & -> & _)|(k2 & E2 & -> & _)].
      - rewrite E in E1. exact (SUBNE k' (eq_sym E1) b Hb).
      - rewrite E in E2. inversion E2; subst k2. exact (cons_old FI AI sx _ _ m2 HR2 b Hb). }
    destruct (Z.eq_dec n 0) as [->|NZ].
    -
      eapply (aj_evt FI AI J). { eapply (asegM0 lo MB SRC A' len' cap' pad); try eassumption; try lia. exact (proj1 SHWM2). }
      intros ms' P. unfold asegM_post in P.
      destruct P as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m3 & -> & MU3 & WM3 & MI3 & ST3 & AE3 & MBC3).
      apply (aj_ret FI AI J). unfold membuffer_assign_post_A.
      do 14 eexists. exists m3, A', cap', ok', bs'. split; [reflexivity|].
      split; [exact MI3|]. split; [exact ST3|]. split; [exact AE3|].
      split. { eapply (rfake_frame FI); [exact RF2| exact MU3| exact WM3|].
               constructor; [eapply (rf_ok_mbloc FI AI sx LBx _ q st m2 MB 32 HR2 SUBx MBL); lia|].
               constructor; [apply (rf_ok_stack FI); cbn; lia| constructor]. }
      split. { eapply (apx_trans FI AI); [exact HP2|].
               eapply (apx_seg FI AI ASL sx LBx _ q _ _ m2 m2 m3 HR2 SUBx MU3 WM3).
               constructor; [right; right; cbn; lia|]. constructor; [left; cbn; lia| constructor]. }
      split. { eapply (am_heap_frame FI AI); [exact HR2| exact MU3| exact WM3|].
               constructor; [eapply (mblocA_hf FI AI LBx _ q st m2 MB 32 RF2 MBL ltac:(lia) SUBx)|].
               constructor; [left; cbn; lia| constructor]. }
      split; [exact SHAPE|]. split; [exact MBC3|]. split; [lia|]. split; [lia|].
      split; [| intros X; lia].
      destruct ok' as [k'|]; cbn in OWN2 |- *; [| exact OWN2]. destruct OWN2 as [HIN BLK]. split; [exact HIN|].
      destruct (am_block_range FI AI sx LBx m2 _ HR2 HIN) as (R1 & R2 & R3 & R4 & R5 & R5d & _). cbn [blk_addr blk_size fst snd] in *.
      pose proof (mblocA_other_block FI AI sx LBx _ q st m2 MB 32 (k', A', cap' + 1) HR2 (SUBNEx k' eq_refl) HIN RF2 MBL ltac:(lia)) as DJ.
      cbn [blk_addr blk_size fst snd] in DJ.
      eapply rw_cells_transport; [exact BLK| exact MU3| exact WM3| cbn [disjoint_from cells_size csize Nat.add]; lia].
    -
      destruct ok' as [k'|]; cbn in OWN2; [| exfalso; destruct OWN2 as (_ & E0 & _); lia].
      destruct OWN2 as [HIN BLK].
      destruct (am_block_range FI AI sx LBx m2 _ HR2 HIN) as (R1 & R2 & R3 & R4 & R5 & R5d & R6). cbn [blk_addr blk_size fst snd] in *.
      pose proof (mblocA_other_block FI AI sx LBx _ q st m2 MB 32 (k', A', cap' + 1) HR2 (SUBNEx k' eq_refl) HIN RF2 MBL ltac:(lia)) as DJM.
      pose proof (msrcA_other_block FI AI sx LBx _ q st m2 SRC n (k', A', cap' + 1) HR2 (SUBNEx k' eq_refl) HIN RF2 MSRC ltac:(lia)) as DJA.
      cbn [blk_addr blk_size fst snd] in DJM, DJA.
      pose proof (block_shw FI AI sx LBx m2 (k', A', cap' + 1) A' (cap' + 1) HR2 HIN ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)) as SHWA.
      eapply (aj_evt FI AI J).
      { eapply (asegM1 IC lo MB SRC n A' len' cap' src bs' pad); try eassumption; lia. }
      cbv beta. intros ms' (bs'' & P & (m3' & EM & BLK3) & FST). unfold asegM_post in P.
      destruct P as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m3 & -> & MU3 & WM3 & MI3 & ST3 & AE3 & MBC3).
      cbn [ms_mem] in EM. subst m3'.
      assert (NEWIV : exists b, In b LBx /\ blk_addr b <= fst (A', A' + (cap' + 1)) /\ snd (A', A' + (cap' + 1)) <= blk_addr b + blk_size b).
      { exists (k', A', cap' + 1). split; [exact HIN| cbn; lia]. }
      apply (aj_ret FI AI J). unfold membuffer_assign_post_A.
      do 14 eexists. exists m3, A', cap', (Some k'), bs''. split; [reflexivity|].
      split; [exact MI3|]. split; [exact ST3|]. split; [exact AE3|].
      split. { eapply (rfake_frame FI); [exact RF2| exact MU3| exact WM3|].
               constructor; [eapply (rf_ok_mbloc FI AI sx LBx _ q st m2 MB 32 HR2 SUBx MBL); lia|].
               constructor; [eapply (rf_ok_blk FI AI sx LBx m2 st (k', A', cap' + 1)); [exact HR2| exact HIN| cbn; lia| cbn; lia| lia]|].
               constructor; [apply (rf_ok_stack FI); cbn; lia| constructor]. }
      split. { eapply (apx_trans FI AI); [exact HP2|].
               eapply (apx_seg FI AI ASL sx LBx _ q _ _ m2 m2 m3 HR2 SUBx MU3 WM3).
               constructor; [right; right; cbn; lia|].
               constructor. { right; left. cbn [fst snd]. intros a Ha.
                              eapply (fresh_block_not_aclient FI AI ASL sx LBx _ (k', A', cap' + 1) q m2 a HR2 HIN (SUBNEx k' eq_refl)); [lia| cbn; lia]. }
               constructor; [left; cbn; lia| constructor]. }
      split. { eapply (am_heap_frame FI AI); [exact HR2| exact MU3| exact WM3|].
               constructor; [eapply (mblocA_hf FI AI LBx _ q st m2 MB 32 RF2 MBL ltac:(lia) SUBx)|].
               constructor; [right; right; left; exact NEWIV|].
               constructor; [left; cbn; lia| constructor]. }
      split; [exact SHAPE|]. split; [exact MBC3|]. split; [lia|]. split; [lia|].
      split; [| intros _; exact FST].
      cbn. split; [exact HIN| exact BLK3]. }
  destruct CASES as [(-> & -> & -> & NC)|(-> & -> & -> & -> & -> & -> & -> & N1 & N2 & N3)].
  -
    eapply (FIN s LB m1 A len cap ok bs); try eassumption; try lia. left. repeat split; reflexivity.
  -
    eapply (aj_bind FI AI J).
    { eapply (orealloc_spec_A FI AI J AC) with (lo := lo) (st := st) (ok := ok) (A := A) (sz := match ok with Some _ => cap + 1 | None => 0 end)
                                               (n := nsz + 1) (old := bs) (ras := []).

      - exact HR1.
      - destruct ok as [k|]; cbn in OWN1 |- *; [exact OWN1| destruct OWN1 as (E1 & E2 & E3); auto].
      - exact AE1.
      - exact RF1.
      - exact ST1.
      - exact CLO.
      - unfold A0_RT_STACK. clear - LO'. lia.
      - clear - QAL. Z.div_mod_to_equations. lia.
      - clear - QTOP. lia.
      - exact MI1.
      - cbn [fpchain]. unfold valid_frame. rewrite unsigned_lit by (clear - MBLO MBHI ACR; lia). clear - MBHI QC. lia.
      - rewrite unsigned_lit by (clear; lia). unfold A0_TRACES. repeat first [left; reflexivity | right].
      - reflexivity.
      - reflexivity.
      - unfold A0_MAXREQ. clear - N1 N2 N3 HNC HLC. lia.
      - apply (am_budget_le_at FI AI _ _ _ _ BUD); split; [clear - N1 N2 N3; lia| clear - N1 N2 N3; lia]. }
    intros s' LB' ms'' POST. unfold orealloc_post_A in POST.
    destruct POST as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & k' & B & junk & -> & AFR & -> & HR2 & BLK2 & NS2).
    destruct AFR as (MI2 & ST2 & AE2 & RF2 & AP2).
    replace (ret_pc (Z_to_bv 64 576452)) with (Z_to_bv 64 576452) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (NEW : In (k', B, nsz + 1) ((k', B, nsz + 1) :: lb_keepA FI AI ok LB)) by (left; reflexivity).
    destruct (am_block_range FI AI s' _ m2 _ HR2 NEW) as (U1 & U2 & U3 & U4 & U5 & U5d & U6). cbn [blk_addr blk_size fst snd] in U1, U2, U3, U4, U5, U5d, U6.
    assert (MBL2 : mblocA FI AI (lb_keepA FI AI ok LB) (q + -96) st MB 32) by (eapply (mblocA_weaken FI AI); [exact MBL| lia| auto| auto]).
    assert (MSRC2 : msrcA FI AI (lb_keepA FI AI ok LB) (q + -96) st SRC n) by (eapply (msrcA_weaken FI AI); [exact MSRC| lia| auto| auto]).
    assert (SUB2 : forall b, In b (lb_keepA FI AI ok LB) -> In b ((k', B, nsz + 1) :: lb_keepA FI AI ok LB)) by (intros b Hb; right; exact Hb).

    pose proof (apres_rw_cells FI AI _ _ _ _ _ _ AP2 FR1 ltac:(apply aclient_range_above; cbn; lia)) as FR2.
    assert (MBC2 : rw_cells asegs m2 MB (mbuf_cells A len cap)).
    { eapply (apres_rw_cells FI AI); [exact AP2| exact MBC1|]. unfold mbuf_cells. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul].
      eapply (mblocA_client FI AI); [exact RF1| exact MBL2]. }
    pose proof (apres_bytes_at FI AI _ _ _ _ _ _ AP2 SRCB1 ltac:(rewrite LEN; eapply (msrcA_client FI AI); [exact RF1| exact MSRC2])) as SRCB2.
    pose proof (mblocA_shw_apres FI AI AMS s' _ _ (q + -96) st m1 m2 MB 32 MBL2 SHWM1 AP2 RF1 HR2 SUB2 QC) as SHWM2.
    pose proof (msrcA_shw_apres FI AI AMS s' _ _ (q + -96) st m1 m2 SRC n MSRC2 SHWS1 AP2 RF1 HR2 SUB2 QC) as SHWS2.
    eapply (aj_evt FI AI J).
    { eapply (asegS lo MB SRC n A B len cap nsz) with (fr := [CB 8 pad; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]);
        first [ exact ST2 | exact MI2 | exact FR2 | exact MBC2 | exact (proj1 SHWM2) | exact WK | reflexivity | lia ]. }
    intros ms' P. unfold asegS_post in P. destruct P as (m3 & c0 & c2 & -> & MU3 & WM3 & MI3 & ST3 & FR3 & MBC3).
    pose proof (mblocA_other_block FI AI s' _ _ (q + -96) st m2 MB 32 (k', B, nsz + 1) HR2 (cons_old FI AI s' _ _ m2 HR2) NEW RF2 MBL2 QC) as DJB.
    cbn [blk_addr blk_size fst snd] in DJB.
    assert (AIV : app_ivs [(MB, MB + 32)]) by (unfold win_ok in WK; app_ivs_tac).
    eapply (FIN s' _ m3 B len nsz (Some k')); try eassumption; try lia.
    + eapply asan_env_frame; [exact AE2| exact MU3| exact WM3|]. unfold env_safe. constructor; [left; cbn; lia| constructor].
    + eapply (rfake_frame FI); [exact RF2| exact MU3| exact WM3|].
      constructor; [eapply (rf_ok_mbloc FI AI s' _ _ (q + -96) st m2 MB 32 HR2 SUB2 MBL2 QC); lia| constructor].
    + eapply (am_heap_frame FI AI); [exact HR2| exact MU3| exact WM3|].
      constructor; [eapply (mblocA_hf FI AI _ _ (q + -96) st m2 MB 32 RF2 MBL2 QC SUB2)| constructor].
    + exact (shw_frame _ m2 m3 MB 32 SHWM2 MU3 AIV).
    + eapply bytes_at_transport; [exact SRCB2| exact MU3| cbn [disjoint_from]; lia].
    + exact (shw_frame _ m2 m3 SRC n SHWS2 MU3 AIV).
    + cbn. split; [exact NEW|]. eapply rw_cells_transport; [exact BLK2| exact MU3| exact WM3| cbn [disjoint_from cells_size csize Nat.add]; lia].
    + right. exists k'. split; [reflexivity|]. split; [reflexivity| exact NS2].
    + eapply (apx_trans FI AI); [exact HP1|]. eapply (apx_trans FI AI).
      * apply apx_of_apres. eapply (apres_weaken FI AI); [exact AP2| lia| auto].
      * eapply (apx_seg FI AI ASL s' _ _ q _ _ m2 m2 m3 HR2 SUB2 MU3 WM3). constructor; [right; right; cbn; lia| constructor].
Qed.
End W.
