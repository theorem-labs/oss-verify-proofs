(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From stdpp Require list.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling Arr.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts ATac IcptA0 AllocA0 ATacAp.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7A0 Require Import ShadowKit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.AW Require Import HttpAllocA HttpRepA AWKit H_membuffer_delete_seg.
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

#[using="Type"] Lemma firstn_app_le : forall {A} (l1 l2 : list A) k, (k <= length l1)%nat -> firstn k (l1 ++ l2) = firstn k l1.
Proof. intros A l1 l2 k H. rewrite firstn_app. replace (k - length l1)%nat with 0%nat by lia. cbn [firstn]. apply app_nil_r. Qed.

#[using="Type"] Lemma nul_atA_firstn : forall bs nl, 0 <= nl -> (Z.to_nat nl < length bs)%nat ->
  firstn (Z.to_nat (nl + 1)) (nul_atA bs nl) = firstn (Z.to_nat nl) bs ++ [Z_to_bv 8 0].
Proof.
  intros bs nl H0 H1. unfold nul_atA.
  assert (LF : length (firstn (Z.to_nat nl) bs) = Z.to_nat nl) by (rewrite length_firstn; lia).
  rewrite app_assoc. rewrite firstn_app_le by (rewrite length_app, LF; cbn [length]; lia).
  apply firstn_all2. rewrite length_app, LF. cbn [length]. lia.
Qed.

#[using="IC AC ASL AMS"] Theorem membuffer_delete_spec_A : membuffer_delete_stmt_A FI AI J.
Proof.
  intros ra q gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB st ok MB idx num A len cap lo bs.
  intros HR RF AE ST CLO LO QAL QTOP MI MBC HLC HNC BUD OWN MBL MBHI AL SHWM HI HN HIDX -> -> ->.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (am_stack_ok FI AI) as (TK1 & TK2 & TK3 & TK4).
  assert (LO' : lo <= q - 80 - 4096) by (unfold A0_RT_STACK in LO; exact LO). clear LO.
  assert (QC : alloc_ceiling <= q + -80) by lia.
  assert (SUB : forall b, In b (lb_keepA FI AI ok LB) -> In b LB) by (intros b Hb; eapply (lb_keepA_sub FI AI); exact Hb).
  destruct (mblocA_range FI AI s LB _ q st m MB 32 HR SUB RF MBL ltac:(lia) ltac:(lia)) as (MBLO & _ & _).
  pose proof (shw_win_ok _ _ _ SHWM) as WK.
  assert (SUBNE : forall k, ok = Some k -> forall b, In b (lb_keepA FI AI ok LB) -> In b LB /\ b <> (k, A, cap + 1)).
  { intros k -> b Hb. split; [apply SUB; exact Hb|]. cbn in Hb. intros ->. exact (lb_remove_neq FI AI _ _ _ Hb eq_refl). }
  assert (BIV1 : Forall (blk_iv FI AI LB) [(lo, q)]) by (constructor; [left; cbn; lia| constructor]).
  destruct (Z.eq_dec len 0) as [->|NZ].
  {
    eapply (aj_evt FI AI J). { eapply (dsegZ lo MB A idx num cap); try eassumption; lia. }
    intros ms' (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m3 & -> & MU3 & WM3 & MI3 & ST3 & AE3 & MBC3).
    apply (aj_ret FI AI J). unfold membuffer_delete_post_A.
    do 15 eexists. exists m3, A, 0, cap, ok, bs. split; [reflexivity|].
    split; [exact MI3|]. split; [exact ST3|]. split; [exact AE3|].
    split. { eapply (rfake_blk_write FI AI s LB st m m3 _ HR RF MU3 WM3). constructor; [split; [left; cbn; lia| cbn; lia]| constructor]. }
    split. { eapply (apx_seg FI AI ASL s LB _ q _ _ m m m3 HR SUB MU3 WM3). constructor; [left; cbn; lia| constructor]. }
    split; [exact (rheap_blk_write FI AI s LB m m3 _ HR MU3 WM3 BIV1)|].
    split; [left; repeat split; reflexivity|]. split; [exact MBC3|]. split; [lia|]. split; [lia|].
    split. { destruct ok as [k|]; cbn in OWN |- *; [| exact OWN]. destruct OWN as [HIN BLK]. split; [exact HIN|].
             destruct (am_block_range FI AI s LB m _ HR HIN) as (R1 & R2 & R3 & R4 & R5 & R5d & _). cbn [blk_addr blk_size fst snd] in *.
             eapply rw_cells_transport; [exact BLK| exact MU3| exact WM3| cbn [disjoint_from cells_size csize Nat.add]; lia]. }
    left. auto. }

  assert (L1 : 1 <= len) by lia.
  destruct ok as [k0|]; cbn in OWN; [| exfalso; destruct OWN as (_ & E0 & _); lia].
  destruct OWN as [HIN0 BLK0].
  destruct (am_block_range FI AI s LB m _ HR HIN0) as (R1 & R2 & R3 & R4 & R5 & R5d & R6). cbn [blk_addr blk_size fst snd] in R1, R2, R3, R4, R5, R5d, R6.
  pose proof (mblocA_other_block FI AI s LB _ q st m MB 32 (k0, A, cap + 1) HR (SUBNE k0 eq_refl) HIN0 RF MBL ltac:(lia)) as DJM0.
  cbn [blk_addr blk_size fst snd] in DJM0.
  pose proof (block_shw FI AI s LB m (k0, A, cap + 1) A (cap + 1) HR HIN0 ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)) as SHWA0.
  assert (LBS0 : length bs = Z.to_nat (cap + 1)) by (destruct BLK0 as [[W _] _]; cbn in W; tauto).

  eapply (aj_evt FI AI J).
  { eapply (dsegA IC lo MB A idx num len cap bs); try eassumption; try lia. }
  intros ms' (m1 & x1 & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & x19 & t3' & t4' & t5' & t6' & pc & nsz & -> & MU1 & WM1 & MI1 & ST1 & FR1 & MBC1 & BLK1 & CASES).
  assert (BIV2 : Forall (blk_iv FI AI LB) [(A, A + (cap + 1)); (lo, q)]).
  { constructor; [right; exists (k0, A, cap + 1); split; [exact HIN0| cbn; lia]|]. constructor; [left; cbn; lia| constructor]. }
  pose proof (rheap_blk_write FI AI s LB m m1 _ HR MU1 WM1 BIV2) as HR1.
  pose proof (rfake_blk_write FI AI s LB st m m1 _ HR RF MU1 WM1
                ltac:(constructor; [split; [right; exists (k0, A, cap + 1); split; [exact HIN0| cbn; lia]| cbn; lia]|];
                      constructor; [split; [left; cbn; lia| cbn; lia]| constructor])) as RF1.
  pose proof (asan_env_frame asegs m m1 _ AE MU1 WM1 (env_safe_blk FI AI s LB m _ HR BIV2)) as AE1.
  pose proof (shw_frame _ m m1 MB 32 SHWM MU1 (app_ivs_blk FI AI s LB m _ HR BIV2)) as SHWM1.
  pose proof (shw_frame _ m m1 A (cap + 1) SHWA0 MU1 (app_ivs_blk FI AI s LB m _ HR BIV2)) as SHWA1.
  assert (HP1 : apx FI AI [(MB, MB + 32)] (lb_keepA FI AI (Some k0) LB) q m m1).
  { eapply (apx_seg FI AI ASL s LB _ q _ _ m m m1 HR SUB MU1 WM1).
    constructor. { right; left. cbn [fst snd]. intros a Ha.
                   eapply (fresh_block_not_aclient FI AI ASL s LB _ (k0, A, cap + 1) q m a HR HIN0 (SUBNE k0 eq_refl)); [lia| cbn; lia]. }
    constructor; [left; cbn; lia| constructor]. }
  assert (LD : length (del_bytesA bs idx num len) = Z.to_nat (cap + 1)).
  { unfold del_bytesA. rewrite upd_bytes_length; [exact LBS0|]. rewrite length_firstn, length_skipn. lia. }

  assert (FIN : forall sx (LBx : BL) m2 A' cap' (k' : K) (bs2 : list byte)
                  (y1 u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 y19 u3 u4 u5 u6 : word),
    mem_inv asegs m2 -> stk asegs m2 lo (q + -80) -> asan_env asegs m2 -> RFAKE FI st m2 -> RHEAP_A FI AI sx LBx m2 ->
    rw_cells asegs m2 (q + -80) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs m2 MB (mbuf_cells A' len cap') -> shw m2 MB 32 ->
    len - num <= cap' -> cap' <= cap -> In (k', A', cap' + 1) LBx -> rw_cells asegs m2 A' [CB (Z.to_nat (cap' + 1)) bs2] ->
    firstn (Z.to_nat (len - num)) bs2 = firstn (Z.to_nat (len - num)) (del_bytesA bs idx num len) ->
    ((Some k' = Some k0 /\ LBx = LB /\ A' = A /\ cap' = cap /\ am_nsec FI AI sx = am_nsec FI AI s)
     \/ (LBx = (k', A', cap' + 1) :: lb_keepA FI AI (Some k0) LB /\ am_nsec FI AI sx = am_nsec FI AI s + nsec1 (cap' + 1))) ->
    apx FI AI [(MB, MB + 32)] (lb_keepA FI AI (Some k0) LB) q m m2 ->
    AJ FI AI J (membuffer_delete_post_A FI AI ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st s LB (Some k0) MB A len cap idx num lo bs m)
      (MS (mkR y1 (wz (q + -80)) gp (wz A0_TP) u0 u1 u2 (wz MB) (wz (MB + 8)) b0 b1 b2 b3 b4 b5 b6 b7
               (wz (MB + 16)) y19 (wz 0x7fff8000) (wz (Z.shiftr (MB + 8) 3 + 2147450880)) (wz (Z.shiftr MB 3 + 2147450880))
               (wz (len - num)) (wz (Z.shiftr (MB + 16) 3 + 2147450880)) s9 s10 s11 u3 u4 u5 u6)
          F (wz 0x8c86c) fc None m2 (seg_rom asegs)) sx LBx).
  { intros sx LBx m2 A' cap' k' bs2 y1 u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 y19 u3 u4 u5 u6.
    intros MI2 ST2 AE2 RF2 HR2 FR2 MBC2 SHWM2 NC CC HIN BLK KEEP SHAPE HP2.
    assert (SUBx : forall b, In b (lb_keepA FI AI (Some k0) LB) -> In b LBx).
    { destruct SHAPE as [(_ & -> & _)| [-> _] ]; [exact SUB| intros b Hb; right; exact Hb]. }
    assert (SUBNEx : forall b, In b (lb_keepA FI AI (Some k0) LB) -> In b LBx /\ b <> (k', A', cap' + 1)).
    { intros b Hb. destruct SHAPE as [(E1 & -> & -> & -> & _)| [-> _] ].
      - inversion E1; subst k'. exact (SUBNE k0 eq_refl b Hb).
      - exact (cons_old FI AI sx _ _ m2 HR2 b Hb). }
    destruct (am_block_range FI AI sx LBx m2 _ HR2 HIN) as (U1 & U2 & U3 & U4 & U5 & U5d & U6). cbn [blk_addr blk_size fst snd] in *.
    pose proof (mblocA_other_block FI AI sx LBx _ q st m2 MB 32 (k', A', cap' + 1) HR2 SUBNEx HIN RF2 MBL ltac:(lia)) as DJM.
    cbn [blk_addr blk_size fst snd] in DJM.
    pose proof (block_shw FI AI sx LBx m2 (k', A', cap' + 1) A' (cap' + 1) HR2 HIN ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)) as SHWA.
    assert (LBS2 : length bs2 = Z.to_nat (cap' + 1)) by (destruct BLK as [[W _] _]; cbn in W; tauto).
    eapply (aj_evt FI AI J).
    { eapply (dsegM lo MB A' len (len - num) cap' bs2); try eassumption; try lia. }
    cbv beta. intros ms' P. unfold dsegM_post in P.
    destruct P as (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m3 & -> & MU3 & WM3 & MI3 & ST3 & AE3 & MBC3 & BLK3).
    assert (NEWIV : exists b, In b LBx /\ blk_addr b <= fst (A', A' + (cap' + 1)) /\ snd (A', A' + (cap' + 1)) <= blk_addr b + blk_size b).
    { exists (k', A', cap' + 1). split; [exact HIN| cbn; lia]. }
    apply (aj_ret FI AI J). unfold membuffer_delete_post_A.
    do 15 eexists. exists m3, A', (len - num), cap', (Some k'), (nul_atA bs2 (len - num)). split; [reflexivity|].
    split; [exact MI3|]. split; [exact ST3|]. split; [exact AE3|].
    split. { eapply (rfake_frame FI); [exact RF2| exact MU3| exact WM3|].
             constructor; [eapply (rf_ok_mbloc FI AI sx LBx _ q st m2 MB 32 HR2 SUBx MBL); lia|].
             constructor; [eapply (rf_ok_blk FI AI sx LBx m2 st (k', A', cap' + 1)); [exact HR2| exact HIN| cbn; lia| cbn; lia| lia]|].
             constructor; [apply (rf_ok_stack FI); cbn; lia| constructor]. }
    split. { eapply (apx_trans FI AI); [exact HP2|].
             eapply (apx_seg FI AI ASL sx LBx _ q _ _ m2 m2 m3 HR2 SUBx MU3 WM3).
             constructor; [right; right; cbn; lia|].
             constructor. { right; left. cbn [fst snd]. intros a Ha.
                            eapply (fresh_block_not_aclient FI AI ASL sx LBx _ (k', A', cap' + 1) q m2 a HR2 HIN SUBNEx); [lia| cbn; lia]. }
             constructor; [left; cbn; lia| constructor]. }
    split. { eapply (am_heap_frame FI AI); [exact HR2| exact MU3| exact WM3|].
             constructor; [eapply (mblocA_hf FI AI LBx _ q st m2 MB 32 RF2 MBL ltac:(lia) SUBx)|].
             constructor; [right; right; left; exact NEWIV|].
             constructor; [left; cbn; lia| constructor]. }
    split. { destruct SHAPE as [(E1 & E2 & E3 & E4 & E5)|[E E5]]; [left; auto 6| right; exists k'; split; [reflexivity| split; [exact E| exact E5]]]. }
    split; [exact MBC3|]. split; [lia|]. split; [lia|].
    split; [cbn; split; [exact HIN| exact BLK3]|].
    right. split; [lia|]. split; [reflexivity|].
    rewrite nul_atA_firstn by lia. rewrite KEEP. reflexivity. }
  destruct CASES as [(-> & ->)|(-> & -> & -> & -> & -> & NS & NLT & NUM1)].
  -
    eapply (FIN s LB m1 A cap k0 (del_bytesA bs idx num len)); try eassumption; try lia; [reflexivity| left; repeat split; reflexivity].
  -
    eapply (aj_bind FI AI J).
    { eapply (orealloc_spec_A FI AI J AC) with (lo := lo) (st := st) (ok := Some k0) (A := A) (sz := cap + 1)
                                               (n := nsz + 1) (old := del_bytesA bs idx num len) (ras := []).
      - exact HR1.
      - split; [exact HIN0| exact BLK1].
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
      - unfold A0_MAXREQ. clear - NS NLT HNC HLC HN HI HIDX. lia.
      - apply (am_budget_le_at FI AI _ _ _ _ BUD); split; [clear - NS NLT HN HI HIDX; lia| clear - NS NLT HN HI HIDX; lia]. }
    intros s' LB' ms'' POST. unfold orealloc_post_A in POST.
    destruct POST as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & k' & B & junk & -> & AFR & -> & HR2 & BLK2 & NS2).
    destruct AFR as (MI2 & ST2 & AE2 & RF2 & AP2).
    replace (ret_pc (Z_to_bv 64 575540)) with (Z_to_bv 64 575540) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (NEW : In (k', B, nsz + 1) ((k', B, nsz + 1) :: lb_keepA FI AI (Some k0) LB)) by (left; reflexivity).
    destruct (am_block_range FI AI s' _ m2 _ HR2 NEW) as (U1 & U2 & U3 & U4 & U5 & U5d & U6). cbn [blk_addr blk_size fst snd] in U1, U2, U3, U4, U5, U5d, U6.
    assert (MBL2 : mblocA FI AI (lb_keepA FI AI (Some k0) LB) (q + -80) st MB 32) by (eapply (mblocA_weaken FI AI); [exact MBL| lia| auto| auto]).
    assert (SUB2 : forall b, In b (lb_keepA FI AI (Some k0) LB) -> In b ((k', B, nsz + 1) :: lb_keepA FI AI (Some k0) LB)) by (intros b Hb; right; exact Hb).
    pose proof (apres_rw_cells FI AI _ _ _ _ _ _ AP2 FR1 ltac:(apply aclient_range_above; cbn; lia)) as FR2.
    assert (MBC2 : rw_cells asegs m2 MB (mbuf_cells A len cap)).
    { eapply (apres_rw_cells FI AI); [exact AP2| exact MBC1|]. unfold mbuf_cells. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul].
      eapply (mblocA_client FI AI); [exact RF1| exact MBL2]. }
    pose proof (mblocA_shw_apres FI AI AMS s' _ _ (q + -80) st m1 m2 MB 32 MBL2 SHWM1 AP2 RF1 HR2 SUB2 QC) as SHWM2.
    eapply (aj_evt FI AI J).
    { eapply (dsegS lo MB A B len cap nsz (len - num)) with (fr := [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]);
        first [ exact ST2 | exact MI2 | exact FR2 | exact MBC2 | exact (proj1 SHWM2) | exact WK | reflexivity | lia ]. }
    intros ms' P. unfold dsegS_post in P. destruct P as (m3 & c4 & c5 & -> & MU3 & WM3 & MI3 & ST3 & FR3 & MBC3).
    pose proof (mblocA_other_block FI AI s' _ _ (q + -80) st m2 MB 32 (k', B, nsz + 1) HR2 (cons_old FI AI s' _ _ m2 HR2) NEW RF2 MBL2 QC) as DJB.
    cbn [blk_addr blk_size fst snd] in DJB.
    assert (AIV : app_ivs [(MB, MB + 32)]) by (unfold win_ok in WK; app_ivs_tac).
    eapply (FIN s' _ m3 B nsz k' _); try eassumption; try lia.
    + eapply asan_env_frame; [exact AE2| exact MU3| exact WM3|]. unfold env_safe. constructor; [left; cbn; lia| constructor].
    + eapply (rfake_frame FI); [exact RF2| exact MU3| exact WM3|].
      constructor; [eapply (rf_ok_mbloc FI AI s' _ _ (q + -80) st m2 MB 32 HR2 SUB2 MBL2 QC); lia| constructor].
    + eapply (am_heap_frame FI AI); [exact HR2| exact MU3| exact WM3|].
      constructor; [eapply (mblocA_hf FI AI _ _ (q + -80) st m2 MB 32 RF2 MBL2 QC SUB2)| constructor].
    + exact (shw_frame _ m2 m3 MB 32 SHWM2 MU3 AIV).
    + eapply rw_cells_transport; [exact BLK2| exact MU3| exact WM3| cbn [disjoint_from cells_size csize Nat.add]; lia].
    +
      rewrite Z.min_l by lia. rewrite firstn_app_le by (rewrite length_firstn, LD; lia).
      rewrite firstn_firstn. f_equal. lia.
    + right. split; [reflexivity| exact NS2].
    + eapply (apx_trans FI AI); [exact HP1|]. eapply (apx_trans FI AI).
      * apply apx_of_apres. eapply (apres_weaken FI AI); [exact AP2| lia| auto].
      * eapply (apx_seg FI AI ASL s' _ _ q _ _ m2 m2 m3 HR2 SUB2 MU3 WM3). constructor; [right; right; cbn; lia| constructor].
Qed.
End W.
