(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From stdpp Require Import base list.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling Arr.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts ATac IcptA0 AllocA0 ATacAp.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7A0 Require Import ShadowKit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.AW Require Import HttpAllocA HttpRepA AWKit AWAuto HObjA H_membuffer_destroy.
Import ListNotations.
Open Scope Z_scope.

Definition httpheader_free_entryA : Z := 0x86998.
Definition httpheader_free_raA : Z := 0x8b774.

Section W.
Context {HC : HasCeiling}.
Hypothesis IC : icpt_contracts.

#[using="Type"] Lemma hseg1 : forall (lo H : Z) ra (q : Z) gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc m,
  stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 16 -> q < 2^64 -> mem_inv asegs m -> 0 <= H -> H + 88 < 2^64 ->
  evt asegs (fun ms' => exists m',
      ms' = MS (mkR (wz 0x869b0) (wz (q + -16)) gp tp t0 t1 t2 (wz H) s1 (wz (H + 56)) a1 a2 a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz membuffer_destroy_entryA) fc None m' (seg_rom asegs)
      /\ munch [(lo, q)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (q + -16) /\ rw_cells asegs m' (q + -16) [C8 s0; C8 ra])
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz H) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz httpheader_free_entryA) fc None m (seg_rom asegs)).
Proof.
  intros lo H ra q gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  intros ST CLO LO QHI MI H0 HHI. unfold httpheader_free_entryA, membuffer_destroy_entryA.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (munch_refl [(lo, q)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 16%nat ST.
  walk_lia_to 0x869ac%Z. step.
  apply evt_done. eexists. split; [reflexivity|]. repeat (split; [eassumption|]). assumption.
Qed.

#[using="Type"] Lemma hseg2 : forall (H : Z) ra (q : Z) gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc m,
  0 <= H -> H + 88 < 2^64 ->
  evt asegs (fun ms' => ms' = MS (mkR (wz 0x869b8) (wz q) gp tp t0 t1 t2 (wz H) s1 (wz (H + 24)) a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (wz membuffer_destroy_entryA) fc None m (seg_rom asegs))
    (MS (mkR ra (wz q) gp tp t0 t1 t2 (wz H) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x869b0) fc None m (seg_rom asegs)).
Proof.
  intros H ra q gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m H0 HHI.
  unfold membuffer_destroy_entryA.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. step. apply evt_done. reflexivity.
Qed.

#[using="Type"] Lemma hseg3 : forall (lo H : Z) ra (q : Z) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1
    (F : bvmap 5 word) fc m,
  stk asegs m lo (q + -16) -> alloc_ceiling <= lo -> lo <= q - 16 -> q < 2^64 -> mem_inv asegs m ->
  rw_cells asegs m (q + -16) [C8 s0; C8 ra] -> 0 <= H -> H + 88 < 2^64 ->
  evt asegs (fun ms' => ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz H) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (wz A0_free) fc None m (seg_rom asegs) /\ stk asegs m lo q)
    (MS (mkR x1 (wz (q + -16)) gp tp t0 t1 t2 (wz H) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x869b8) fc None m (seg_rom asegs)).
Proof.
  intros lo H ra q gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m.
  intros ST CLO LO QHI MI FR H0 HHI. unfold A0_free.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  walk_lia_to 0x869c4%Z. release_to q. step. step.
  apply evt_done. split; [reflexivity| assumption].
Qed.

Variable FI : fs_if.
Variable AI : am_if FI.
Variable J : a0_judg FI AI.
Variable AC : am_contracts FI AI J.
Hypothesis ASL : forall lo hi, am_static FI AI lo hi -> a0_static lo hi.
Hypothesis AMS : forall lo hi, a0_static lo hi -> am_static FI AI lo hi.
Local Notation K := (am_K FI AI).
Local Notation BLK := (block K).
Local Notation BL := (list (block K)).
Local Notation lbrm k LB := (lb_remove (am_K_eqb FI AI) k LB).
Local Notation bsub := (bsub FI AI).
Local Notation hdro := (hdro FI AI).
Local Notation hblocks := (hblocks FI AI).

Definition httpheader_free_post_A (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : fsstate FI) (ns0 : Z) (LB LBK : BL) (h : hdr FI AI) (lo : Z) (m : mem) : aps FI AI -> BL -> machine_state -> Prop :=
  fun s' LB' ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo q /\ asan_env asegs m' /\ RFAKE FI st m'
    /\ apx FI AI [] LBK q m m'
    /\ RHEAP_A FI AI s' LB' m' /\ bsub LBK LB'
    /\ LB' = lbrm (hk FI AI h) (lbrm (vk FI AI h) (lbrm (nk FI AI h) LB))
    /\ am_nsec FI AI s' = ns0.

Definition httpheader_free_stmt_A : Prop :=
  forall (ra : word) (q : Z) (gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : aps FI AI) (LB LBK : BL) (st : fsstate FI) (h : hdr FI AI) (lo : Z),
  RHEAP_A FI AI s LB m -> RFAKE FI st m -> asan_env asegs m ->
  stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 16 - 32 - A0_RT_STACK -> q mod 16 = 0 -> q + 16 < am_stack_top FI AI ->
  mem_inv asegs m ->
  ~ valid_frame (am_stack_top FI AI) q (bv_unsigned s0) ->
  hdro m LB h -> bsub LBK LB -> NoDup (map blk_id (hblocks h ++ LBK)) ->
  ra = wz httpheader_free_raA -> a0 = wz (hA FI AI h) ->
  AJ FI AI J (httpheader_free_post_A ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st (am_nsec FI AI s) LB LBK h lo m)
    (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz httpheader_free_entryA) fc None m (seg_rom asegs))
    s LB.

#[using="IC AC ASL AMS"] Theorem httpheader_free_spec_A : httpheader_free_stmt_A.
Proof.
  intros ra q gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB LBK st h lo.
  intros HR RF AE ST CLO LO QAL QTOP MI NVF HD KSUB ND -> ->.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (am_stack_ok FI AI) as (TK1 & TK2 & TK3 & TK4).
  assert (LO' : lo <= q - 16 - 32 - 4096) by (unfold A0_RT_STACK in LO; exact LO). clear LO.
  destruct h as [H kh id An nl nc kn Av vl vc kv].
  unfold HObjA.hdro, HObjA.hdro_mem, HObjA.hdro_pure, HObjA.hblocks in HD. unfold HObjA.hblocks in ND. cbn [hA hk hid nA nlen ncap nk vA vlen vcap vk] in *.
  destruct HD as (([pad HCc] & VC & [vbs [VBLK VN]] & NC & [nbs [NBLK NN]]) & (VL & VC5 & NL & NC5 & IDR) & HSUB).
  pose proof (HSUB _ (or_introl eq_refl)) as HIN. pose proof (HSUB _ (or_intror (or_introl eq_refl))) as VIN.
  pose proof (HSUB _ (or_intror (or_intror (or_introl eq_refl)))) as NIN.
  destruct (am_block_range FI AI s LB m _ HR HIN) as (R1 & R2 & _ & R4 & R5 & _). cbn [blk_addr blk_size fst snd] in R1, R2, R4, R5.
  destruct (am_block_range FI AI s LB m _ HR VIN) as (Q1 & _ & _ & Q4 & Q5 & _). cbn [blk_addr blk_size fst snd] in Q1, Q4, Q5.
  destruct (am_block_range FI AI s LB m _ HR NIN) as (P1 & _ & _ & P4 & P5 & _). cbn [blk_addr blk_size fst snd] in P1, P4, P5.

  cbn in ND. inversion ND as [|x l NI1 ND1]; subst. inversion ND1 as [|x l NI2 ND2]; subst. inversion ND2 as [|x l NI3 ND3]; subst.
  assert (NE12 : kh <> kv) by (intros E; apply NI1; rewrite E; left).
  assert (NE13 : kh <> kn) by (intros E; apply NI1; rewrite E; right; left).
  assert (NE23 : kv <> kn) by (intros E; apply NI2; rewrite E; left).
  assert (KK : forall b, In b LBK -> blk_id b <> kh /\ blk_id b <> kv /\ blk_id b <> kn).
  { intros b Hb. pose proof (in_map blk_id _ _ Hb) as Hi. apply base.list_elem_of_In in Hi.
    repeat split; intros E; rewrite E in Hi; [apply NI1; right; right; exact Hi| apply NI2; right; exact Hi| apply NI3; exact Hi]. }
  clear ND ND1 ND2 ND3 NI1 NI2 NI3.

  eapply (aj_evt FI AI J). { eapply (hseg1 lo H); try eassumption; lia. }
  intros ms' (m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1).
  assert (BIV1 : Forall (blk_iv FI AI LB) [(lo, q)]) by (constructor; [left; cbn; lia| constructor]).
  pose proof (rheap_blk_write FI AI s LB m m1 _ HR MU1 WM1 BIV1) as HR1.
  pose proof (rfake_blk_write FI AI s LB st m m1 _ HR RF MU1 WM1 ltac:(constructor; [split; [left; cbn; lia| cbn; lia]| constructor])) as RF1.
  pose proof (asan_env_frame asegs m m1 _ AE MU1 WM1 (env_safe_blk FI AI s LB m _ HR BIV1)) as AE1.
  pose proof (rw_cells_transport asegs _ m m1 _ _ NC MU1 WM1 ltac:(unfold mbuf_cells; cbn [disjoint_from cells_size csize Nat.add]; lia)) as NC1.
  pose proof (rw_cells_transport asegs _ m m1 _ _ VC MU1 WM1 ltac:(unfold mbuf_cells; cbn [disjoint_from cells_size csize Nat.add]; lia)) as VC1.
  assert (HP1 : apx FI AI [] LBK q m m1).
  { eapply (apx_seg FI AI ASL s LB _ q _ _ m m m1 HR KSUB MU1 WM1). constructor; [left; cbn; lia| constructor]. }
  pose proof (rw_cells_transport asegs _ m m1 _ _ VBLK MU1 WM1 ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)) as VBLK1.
  clear MU1 WM1 BIV1.

  assert (HIN2 : In (kh, H, 88) (lbrm kn LB)) by (apply (in_lb_remove FI AI); [exact HIN| cbn; congruence]).
  assert (VIN2 : In (kv, Av, vc + 1) (lbrm kn LB)) by (apply (in_lb_remove FI AI); [exact VIN| cbn; congruence]).
  eapply (aj_bind FI AI J).
  { eapply (membuffer_destroy_spec_A IC FI AI J AC ASL AMS) with (lo := lo) (MB := H + 56) (A := An) (len := nl) (cap := nc) (LBrest := lbrm kn LB) (st := st).
    - exact HR1.
    - exact RF1.
    - exact AE1.
    - exact ST1.
    - exact CLO.
    - unfold A0_RT_STACK. clear - LO'. lia.
    - clear - QAL. Z.div_mod_to_equations. lia.
    - clear - QTOP. lia.
    - exact MI1.
    - exact NC1.
    - eapply (mblocA_block FI AI) with (b := (kh, H, 88)); [exact HIN2| cbn; lia| cbn; lia].
    - clear - R4. lia.
    - clear - R2. Z.div_mod_to_equations. lia.
    - eapply (block_shw FI AI s LB m1 (kh, H, 88)); [exact HR1| exact HIN| cbn; lia| cbn; lia| lia].
    - right. exists kn. split; [exact NIN| reflexivity].
    - reflexivity. }
  intros sx2 LB2 ms2 P. unfold membuffer_destroy_post_A in P.
  destruct P as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & MI2 & ST2 & AE2 & RF2 & HP2 & -> & HR2 & NC2 & NS2).
  replace (ret_pc (Z_to_bv 64 0x869b0)) with (Z_to_bv 64 0x869b0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  pose proof (apx_rw_cells FI AI _ _ _ _ _ _ _ HP2 FR1 ltac:(apply aclient_range_above; cbn; lia) ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)) as FR2.
  pose proof (apx_rw_cells FI AI _ _ _ _ _ _ _ HP2 VC1 ltac:(eapply (aclient_range_block FI AI); [exact HIN2| cbn; lia| unfold mbuf_cells; cbn; lia]) ltac:(unfold mbuf_cells; cbn [disjoint_from cells_size csize Nat.add]; lia)) as VC2.
  assert (DHV : H + 88 <= Av \/ Av + (vc + 1) <= H).
  { pose proof (am_blocks_disjoint FI AI s LB m _ _ HR HIN VIN ltac:(congruence)) as D. cbn [blk_addr blk_size fst snd] in D. lia. }
  pose proof (rw_cells_bound asegs _ _ _ VBLK1) as VBB. cbn [cells_size csize Nat.add] in VBB.
  assert (VBLK2 : rw_cells asegs m2 Av [CB (Z.to_nat (vc + 1)) vbs]).
  { eapply (apx_rw_cells FI AI); [exact HP2| exact VBLK1| |].
    - eapply (aclient_range_block FI AI); [exact VIN2| cbn; lia| cbn [cells_size csize Nat.add blk_addr blk_size fst snd]; lia].
    - cbn [disjoint_from cells_size csize Nat.add]. lia. }
  assert (KSUB2 : bsub LBK (lbrm kn LB)) by (intros b Hb; apply (in_lb_remove FI AI); [apply KSUB; exact Hb| apply KK; exact Hb]).
  assert (QC : alloc_ceiling <= q) by lia.
  assert (HP12 : apx FI AI [] LBK q m m2).
  { eapply (apx_trans FI AI); [exact HP1|]. eapply (apx_drop FI AI); [exact HP2| lia| exact KSUB2|].
    intros a Ha Hc. cbn. split; [| exact I]. intros Hr.
    eapply (fresh_block_not_aclient FI AI ASL sx2 _ LBK (kh, H, 88) q m2 a HR2 HIN2); [| exact QC| cbn; lia| exact Hc].
    intros bx Hbx. split; [apply KSUB2; exact Hbx|]. intros E. rewrite E in Hbx. exact (proj1 (KK _ Hbx) eq_refl). }
  clear HP1 HP2 FR1 VC1 VBLK1 NC1 AE1 RF1 HR1 MI1 ST1 DHV VBB.

  eapply (aj_evt FI AI J). { eapply (hseg2 H); lia. }
  intros ms' ->.
  assert (HIN3 : In (kh, H, 88) (lbrm kv (lbrm kn LB))) by (apply (in_lb_remove FI AI); [exact HIN2| cbn; congruence]).
  eapply (aj_bind FI AI J).
  { eapply (membuffer_destroy_spec_A IC FI AI J AC ASL AMS) with (lo := lo) (MB := H + 24) (A := Av) (len := vl) (cap := vc) (LBrest := lbrm kv (lbrm kn LB)) (st := st).
    - exact HR2.
    - exact RF2.
    - exact AE2.
    - exact ST2.
    - exact CLO.
    - unfold A0_RT_STACK. clear - LO'. lia.
    - clear - QAL. Z.div_mod_to_equations. lia.
    - clear - QTOP. lia.
    - exact MI2.
    - exact VC2.
    - eapply (mblocA_block FI AI) with (b := (kh, H, 88)); [exact HIN3| cbn; lia| cbn; lia].
    - clear - R4. lia.
    - clear - R2. Z.div_mod_to_equations. lia.
    - eapply (block_shw FI AI sx2 _ m2 (kh, H, 88)); [exact HR2| exact HIN2| cbn; lia| cbn; lia| lia].
    - right. exists kv. split; [exact VIN2| reflexivity].
    - reflexivity. }
  intros sx3 LB3 ms3 P. unfold membuffer_destroy_post_A in P.
  destruct P as (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m3 & -> & MI3 & ST3 & AE3 & RF3 & HP3 & -> & HR3 & VC3 & NS3).
  replace (ret_pc (Z_to_bv 64 0x869b8)) with (Z_to_bv 64 0x869b8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  pose proof (apx_rw_cells FI AI _ _ _ _ _ _ _ HP3 FR2 ltac:(apply aclient_range_above; cbn; lia) ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)) as FR3.
  assert (KSUB3 : bsub LBK (lbrm kv (lbrm kn LB))) by (intros b Hb; apply (in_lb_remove FI AI); [apply KSUB2; exact Hb| apply KK; exact Hb]).
  assert (HP13 : apx FI AI [] LBK q m m3).
  { eapply (apx_trans FI AI); [exact HP12|]. eapply (apx_drop FI AI); [exact HP3| lia| exact KSUB3|].
    intros a Ha Hc. cbn. split; [| exact I]. intros Hr.
    eapply (fresh_block_not_aclient FI AI ASL sx3 _ LBK (kh, H, 88) q m3 a HR3 HIN3); [| exact QC| cbn; lia| exact Hc].
    intros bx Hbx. split; [apply KSUB3; exact Hbx|]. intros E. rewrite E in Hbx. exact (proj1 (KK _ Hbx) eq_refl). }
  clear HP12 HP3 FR2 VC2 VBLK2 NC2 AE2 RF2 HR2 MI2 ST2.

  eapply (aj_evt FI AI J). { eapply (hseg3 lo H); try eassumption; lia. }
  intros ms' [-> ST4].
  eapply (aj_mono FI AI J).
  { eapply (ac_free FI AI J AC) with (lo := lo) (k := kh) (A := H) (n := 88) (ras := []) (st := st).
    - exact HR3.
    - exact HIN3.
    - exact AE3.
    - exact RF3.
    - exact ST4.
    - exact CLO.
    - unfold A0_RT_STACK. clear - LO'. lia.
    - exact QAL.
    - exact QTOP.
    - exact MI3.
    - cbn [fpchain]. exact NVF.
    - unfold httpheader_free_raA. rewrite unsigned_lit by (clear; lia). unfold A0_TRACES. repeat first [left; reflexivity | right].
    - reflexivity. }
  intros s' LB' ms'' POST. unfold free_post_A in POST.
  destruct POST as (w0 & w1 & w2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m4 & -> & AFR & -> & HR4 & NS4).
  destruct AFR as (MI4 & ST5 & AE4 & RF4 & AP4).
  assert (KSUB4 : bsub LBK (lbrm kh (lbrm kv (lbrm kn LB)))) by (intros b Hb; apply (in_lb_remove FI AI); [apply KSUB3; exact Hb| apply KK; exact Hb]).
  unfold httpheader_free_post_A. cbn [hA hk hid nA nlen ncap nk vA vlen vcap vk].
  do 15 eexists. exists m4. split; [reflexivity|].
  split; [exact MI4|]. split; [exact ST5|]. split; [exact AE4|]. split; [exact RF4|].
  split. { eapply (apx_trans FI AI); [exact HP13|]. apply apx_of_apres. eapply (apres_weaken FI AI); [exact AP4| lia| exact KSUB4]. }
  split; [exact HR4|]. split; [exact KSUB4|]. split; [reflexivity| rewrite NS4, NS3, NS2; reflexivity].
Qed.

End W.
