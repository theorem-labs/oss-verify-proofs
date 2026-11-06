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
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.AW Require Import AWUb HttpAllocA HttpRepA AWKit AWRng.
Import ListNotations.
Open Scope Z_scope.

Section W.
Context {HC : HasCeiling}.
Hypothesis IC : icpt_contracts.

Definition dseg1_post (lo MB A len cap : Z) (ra : word) (q : Z) (gp tp s0 s1 : word)
    (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) : machine_state -> Prop :=
  fun ms' => exists m',
    ms' = MS (mkR (wz 0x8c9ac) (wz (q + -32)) gp tp t0 t1 t2 (wz MB) (wz 0x7fff8000) (wz A) a1 a2 a3 a4 a5 a6 a7
                  (wz (Z.shiftr MB 3 + 2147450880)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz A0_free) fc None m' (seg_rom asegs)
    /\ munch [(lo, q)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (q + -32)
    /\ rw_cells asegs m' (q + -32) [C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' MB (mbuf_cells A len cap).

#[using="Type"] Lemma dseg1 : forall (lo MB A len cap : Z) ra (q : Z) gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc m,
  stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 32 -> q < 2^64 -> mem_inv asegs m -> asan_env asegs m ->
  rw_cells asegs m MB (mbuf_cells A len cap) -> 0x609000 <= MB -> MB + 32 <= alloc_ceiling -> MB mod 8 = 0 ->
  accessible m MB 32 -> win_ok MB 32 ->
  evt asegs (dseg1_post lo MB A len cap ra q gp tp s0 s1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz MB) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz membuffer_destroy_entryA) fc None m (seg_rom asegs)).
Proof.
  intros lo MB A len cap ra q gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  intros ST CLO LO QHI MI AE0 MBC MBLO MBHI AL ACC WK. unfold membuffer_destroy_entryA. unfold mbuf_cells, MEMBUF_DEF_SIZE_INC in *.
  a0_prologue AE0 [(lo, q)]%Z m.
  carve_frame 32%nat ST.
  step. fix_lit_store. step. fix_lit_store. step. fix_lit_store. step. fix_lit_store. step. fix_lit_store.
  zstep. if_cases K0; zify_cond K0. { exfalso; lia. }
  zstep. ub_align.
  step. step. step. zstep. zstep.
  pose proof (accessible_frame _ _ _ _ _ ACC WK MU ltac:(app_ivs_tac)) as ACC1.
  acc_chk0 18 MB ACC1. clear ACC1.
  step. step. lit_branch.
  step. step.
  apply evt_done. unfold dseg1_post, A0_free. eexists. split; [reflexivity|].
  repeat (split; [assumption|]). exact MBC.
Qed.

Definition dseg2_post (lo MB : Z) (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(MB, MB + 32); (lo, q)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q /\ asan_env asegs m'
    /\ rw_cells asegs m' MB (mbuf_cells 0 0 0).

#[using="Type"] Lemma dseg2 : forall (lo MB A len cap : Z) ra (q : Z) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc m,
  stk asegs m lo (q + -32) -> alloc_ceiling <= lo -> lo <= q - 32 - A0_RT_STACK -> q < 2^64 -> mem_inv asegs m -> asan_env asegs m ->
  rw_cells asegs m (q + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m MB (mbuf_cells A len cap) -> 0x609000 <= MB -> MB + 32 <= alloc_ceiling -> MB mod 8 = 0 ->
  shw m MB 32 ->
  evt asegs (dseg2_post lo MB ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
    (MS (mkR (wz 0x8c9ac) (wz (q + -32)) gp tp t0 t1 t2 (wz MB) (wz 0x7fff8000) a0 a1 a2 a3 a4 a5 a6 a7
             (wz (Z.shiftr MB 3 + 2147450880)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x8c9ac) fc None m (seg_rom asegs)).
Proof.

  intros lo MB A len cap ra q gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  intros ST CLO LO QHI MI AE0 FR MBC MBLO MBHI AL SHW. unfold mbuf_cells, MEMBUF_DEF_SIZE_INC in *. unfold A0_RT_STACK in LO.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (munch_refl [(MB, MB + 32); (lo, q)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (shw_win_ok _ _ _ SHW) as WK.
  zstep. zstep. zstep.
  acc_chk0 11 (MB + 24) (proj1 SHW).
  step. step. lit_branch.
  zstep. step. fix_lit_store.
  pose proof (accessible_frame _ _ _ _ _ (proj1 SHW) WK MU ltac:(app_ivs_tac)) as ACC1.
  acc_chk0 18 MB ACC1. clear ACC1.
  step. step. lit_branch.
  step. fix_lit_store.
  zstep. zstep. zstep.
  pose proof (accessible_frame _ _ _ _ _ (proj1 SHW) WK MU ltac:(app_ivs_tac)) as ACC1.
  acc_chk0 11 (MB + 8) ACC1. clear ACC1.
  step. step. lit_branch.
  step. fix_lit_store.
  zstep. zstep. zstep.
  pose proof (accessible_frame _ _ _ _ _ (proj1 SHW) WK MU ltac:(app_ivs_tac)) as ACC1.
  acc_chk0 11 (MB + 16) ACC1. clear ACC1.
  step. step. lit_branch.
  step. fix_lit_store.
  step. step. step. step. step. env_now AE0 MU WM. release_to q. step.
  apply evt_done. unfold dseg2_post. repeat (lazymatch goal with |- ex _ => eexists end).
  split; [reflexivity|]. repeat (split; [assumption|]).
  lazymatch goal with P : rw_cells asegs _ MB _ |- _ => exact P end.
Qed.

Variable FI : fs_if.
Variable AI : am_if FI.
Variable J : a0_judg FI AI.
Variable AC : am_contracts FI AI J.
Hypothesis ASL : forall lo hi, am_static FI AI lo hi -> a0_static lo hi.
Hypothesis AMS : forall lo hi, a0_static lo hi -> am_static FI AI lo hi.
Local Notation K := (am_K FI AI).

#[using="AC ASL AMS"] Theorem membuffer_destroy_spec_A : membuffer_destroy_stmt_A FI AI J.
Proof.
  intros ra q gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB LBrest st MB A len cap lo.
  intros HR RF AE ST CLO LO QAL QTOP MI MBC MBL MBHI AL SHW CASE ->.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (am_stack_ok FI AI) as (TK1 & TK2 & TK3 & TK4).
  assert (SUB : forall b, In b LBrest -> In b LB).
  { destruct CASE as [[_ ->]|(k & _ & ->)]; [auto|]. intros b Hb. eapply (lb_remove_sub FI AI). exact Hb. }
  assert (QC : alloc_ceiling <= q) by (unfold A0_RT_STACK in LO; lia).
  destruct (mblocA_range FI AI s LB LBrest q st m MB 32 HR SUB RF MBL QC ltac:(lia)) as (MBLO & _ & _).
  pose proof (shw_win_ok _ _ _ SHW) as WK.

  eapply (aj_evt FI AI J). { eapply (dseg1 lo MB A len cap); try eassumption; try (unfold A0_RT_STACK in LO; lia). exact (proj1 SHW). }
  intros ms' (m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1 & MBC1).
  assert (BIV1 : Forall (blk_iv FI AI LB) [(lo, q)]) by (constructor; [left; cbn; lia| constructor]).
  pose proof (rheap_blk_write FI AI s LB m m1 _ HR MU1 WM1 BIV1) as HR1.
  pose proof (rfake_blk_write FI AI s LB st m m1 _ HR RF MU1 WM1 ltac:(constructor; [split; [left; cbn; lia| cbn; unfold A0_RT_STACK in LO; lia]| constructor])) as RF1.
  pose proof (asan_env_frame asegs m m1 _ AE MU1 WM1 (env_safe_blk FI AI s LB m _ HR BIV1)) as AE1.
  pose proof (shw_frame _ m m1 MB 32 SHW MU1 (app_ivs_blk FI AI s LB m _ HR BIV1)) as SHW1.
  assert (HP1 : apx FI AI [(MB, MB + 32)] LBrest q m m1).
  { eapply (apx_seg FI AI ASL s LB LBrest q _ _ m m m1 HR SUB MU1 WM1). constructor; [left; cbn; unfold A0_RT_STACK in LO; lia| constructor]. }

  assert (TAIL : forall sx m2 (a0' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
    mem_inv asegs m2 -> stk asegs m2 lo (q + -32) -> asan_env asegs m2 -> RFAKE FI st m2 ->
    RHEAP_A FI AI sx LBrest m2 ->
    rw_cells asegs m2 (q + -32) [C8 s2; C8 s1; C8 s0; C8 ra] -> rw_cells asegs m2 MB (mbuf_cells A len cap) ->
    shw m2 MB 32 -> apx FI AI [(MB, MB + 32)] LBrest q m m2 -> am_nsec FI AI sx = am_nsec FI AI s ->
    AJ FI AI J (membuffer_destroy_post_A FI AI ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st s LBrest MB lo m)
      (MS (mkR (wz 0x8c9ac) (wz (q + -32)) gp (wz A0_TP) t0' t1' t2' (wz MB) (wz 0x7fff8000) a0' a1' a2' a3' a4' a5' a6' a7' (wz (Z.shiftr MB 3 + 2147450880)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
          F (wz 0x8c9ac) fc None m2 (seg_rom asegs)) sx LBrest).
  { intros sx m2 a0' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' MI2 ST2 AE2 RF2 HR2 FR2 MBC2 SHW2 HP2 NSx.
    eapply (aj_evt FI AI J). { eapply (dseg2 lo MB A len cap); try eassumption; lia. }
    intros ms' P. unfold dseg2_post in P.
    destruct P as (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m3 & -> & MU3 & WM3 & MI3 & ST3 & AE3 & MBC3).
    apply (aj_ret FI AI J). unfold membuffer_destroy_post_A.
    do 15 eexists. exists m3. split; [reflexivity|].
    split; [exact MI3|]. split; [exact ST3|]. split; [exact AE3|].
    split. { eapply (rfake_frame FI); [exact RF2| exact MU3| exact WM3|].
             constructor; [eapply (mblocA_rf FI AI sx LBrest LBrest q st m2 MB 32 HR2 ltac:(auto) MBL QC ltac:(lia))|].
             constructor; [| constructor]. left. cbn [fst snd]. pose proof (fsb_ok FI) as (F1 & F2 & _ & _).
             unfold sh, SHADOW_OFF. split; [right; lia|]. right. Z.div_mod_to_equations. lia. }
    split. { eapply (apx_trans FI AI); [exact HP2|].
             eapply (apx_seg FI AI ASL sx LBrest LBrest q _ _ m2 m2 m3 HR2 ltac:(auto) MU3 WM3).
             constructor; [right; right; cbn; lia|]. constructor; [left; cbn; unfold A0_RT_STACK in LO; lia| constructor]. }
    split; [reflexivity|]. split; [| split; [exact MBC3| exact NSx]].
    eapply (am_heap_frame FI AI); [exact HR2| exact MU3| exact WM3|].
    constructor; [eapply (mblocA_hf FI AI LBrest LBrest q st m2 MB 32 RF2 MBL QC ltac:(auto))|].
    constructor; [left; cbn; lia| constructor]. }
  assert (FPC : forall mx, fpchain mx (am_stack_top FI AI) (q + -32) (bv_unsigned (wz MB)) []).
  { intros mx. cbn [fpchain]. unfold valid_frame. rewrite unsigned_lit by lia. unfold A0_RT_STACK in LO. lia. }
  destruct CASE as [[-> ->]|(k & HIN & ->)].
  -
    eapply (aj_evt FI AI J).
    { eapply (ac_free_null FI AI J AC) with (lo := lo) (st := st) (ras := []) (s := s) (LB := LB);
        first [ exact HR1 | exact AE1 | exact RF1 | exact ST1 | exact MI1 | exact CLO | exact (FPC m1) | reflexivity
              | (unfold A0_RT_STACK in *; lia) | (clear - QAL; Z.div_mod_to_equations; lia)
              | (rewrite unsigned_lit by lia; cbn; tauto) ]. }
    cbv beta. intros ms' P.

    destruct P as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & AFR & WM2 & HR2).
    destruct AFR as (MI2 & ST2 & AE2 & RF2 & AP2).
    replace (ret_pc (Z_to_bv 64 575916)) with (Z_to_bv 64 575916) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (MBL' : mblocA FI AI LB (q + -32) st MB 32).
    { eapply (mblocA_weaken FI AI); [exact MBL| lia| auto| auto]. }
    eapply TAIL; try eassumption.
    + eapply (apres_rw_cells FI AI); [exact AP2| exact FR1| apply aclient_range_above; cbn; lia].
    + eapply (apres_rw_cells FI AI); [exact AP2| exact MBC1|]. unfold mbuf_cells. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul].
      eapply (mblocA_client FI AI); [exact RF1| exact MBL'].
    + eapply (mblocA_shw_apres FI AI AMS s _ _ (q + -32) st m1 m2 MB 32 MBL' SHW1 AP2 RF1 HR2 ltac:(auto)). unfold A0_RT_STACK in LO. lia.
    + eapply (apx_trans FI AI); [exact HP1|]. apply apx_of_apres. eapply (apres_weaken FI AI); [exact AP2| lia| auto].
    + reflexivity.
  -
    eapply (aj_bind FI AI J).
    { eapply (ac_free FI AI J AC) with (lo := lo) (st := st) (ras := []) (k := k) (A := A) (n := cap + 1);
        first [ exact HR1 | exact HIN | exact AE1 | exact RF1 | exact ST1 | exact MI1 | exact CLO | exact (FPC m1) | reflexivity
              | (unfold A0_RT_STACK in *; lia) | (clear - QAL; Z.div_mod_to_equations; lia)
              | (rewrite unsigned_lit by lia; cbn; tauto) ]. }
    intros s' LB' ms'' POST. unfold free_post_A in POST.
    destruct POST as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & AFR & -> & HR2 & NS2).
    destruct AFR as (MI2 & ST2 & AE2 & RF2 & AP2).
    replace (ret_pc (Z_to_bv 64 575916)) with (Z_to_bv 64 575916) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (MBL' : mblocA FI AI (lb_remove (am_K_eqb FI AI) k LB) (q + -32) st MB 32).
    { eapply (mblocA_weaken FI AI); [exact MBL| lia| auto| auto]. }
    eapply TAIL; try eassumption.
    + eapply (apres_rw_cells FI AI); [exact AP2| exact FR1| apply aclient_range_above; cbn; lia].
    + eapply (apres_rw_cells FI AI); [exact AP2| exact MBC1|]. unfold mbuf_cells. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul].
      eapply (mblocA_client FI AI); [exact RF1| exact MBL'].
    + eapply (mblocA_shw_apres FI AI AMS s' _ _ (q + -32) st m1 m2 MB 32 MBL' SHW1 AP2 RF1 HR2 ltac:(auto)). unfold A0_RT_STACK in LO. lia.
    + eapply (apx_trans FI AI); [exact HP1|]. apply apx_of_apres. eapply (apres_weaken FI AI); [exact AP2| lia| auto].
Qed.
End W.
