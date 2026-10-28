(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun Stdio SjModel AtpModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_stage1_kit Atp_h_defs.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2 RT_iface3 RT_iface5. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_hkit2 Sj_new. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_num_akit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_h_alloc Sj_stage2_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_fzwA Atp_setcapA Atp_activewA Atp_defsA Atp_kitA Atp_h_defsA Atp_h_vkitA Atp_hkit6A Atp_h_emplA Atp_h_splitintoA RT_rtf Pj_rtkA Pj_lftoi1A Pj_defsA Pj_os_defsA Pj_cpsA El_defsA El_lf1A El_lf2A El_lf2bA El_costA El_phasesA El_frontA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition vl_st (usp sp' f : Z) (pc : Z) (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state :=
  MS (mkR ra (Z_to_bv 64 sp') gp (Z_to_bv 64 TPV_A) t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 sp') a0 a1 a2 a3 a4 a5 a6 a7
          (Z_to_bv 64 f) (Z_to_bv 64 (shad f)) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f + 96)) (Z_to_bv 64 (f + 208)) (Z_to_bv 64 SHB) (Z_to_bv 64 f) s9 s10 s11 t3 t4 t5 t6)
     F (Z_to_bv 64 pc) fc None m (seg_rom asegs).

Definition vl_at (pc : Z) (s10 : word) : Prop :=
  pc = EL_SPLITRET_A \/ (pc = EL_VLOOP_A /\ s10 = Z_to_bv 64 16) \/ (pc = 0xb18e8 /\ s10 = Z_to_bv 64 16).

Local Ltac vgo E :=
  repeat first
    [ let K := fresh "K" in if_cases K; zify_cond K; try (exfalso; lia)
    | lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 ?p) _ _ _ _) =>
          let b := eval vm_compute in (andb (Z.leb 0xb18cc p) (Z.ltb p 0xb18ec)) in
          lazymatch b with true => zstep; try rewrite E end
      end ].

Lemma vl_exit : forall (usp sp' f pc A cap sz : Z) (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  vl_at pc s10 ->
  0 < f -> f + 1024 < 2^63 -> 0 <= A -> A + 16 * cap < 2^63 -> 2 <= sz <= cap ->
  rw_cells asegs m (f + 32) [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (A + 16 * sz)); C8 (Z_to_bv 64 (A + 16 * cap))] -> mem_inv asegs m ->
  evt asegs (fun ms => exists ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s11' t3' t4' t5' t6' : word,
      ms = vl_st usp sp' f EL_VEC2_A ra' gp t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 A) (Z_to_bv 64 16) s11' t3' t4' t5' t6' F fc m)
    (vl_st usp sp' f pc ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s9 s10 s11 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros PC F0 FH A0 AH SZ SV MI. unfold vl_st, vl_at, EL_SPLITRET_A, EL_VLOOP_A, EL_VEC2_A in *.
  assert (EF : bv_unsigned (Z_to_bv 64 (f + 32)) = f + 32) by (apply unsigned_lit; lia).
  assert (E16 : A + 16 * sz + - A = 16 * sz) by lia.
  destruct PC as [-> | [(-> & ->) | (-> & ->)]]; vgo E16.
  all: apply evt_done; do 17 eexists; cbv delta [mkR]; reflexivity.
Qed.

Lemma vl_callf : forall (usp sp' f pc A cap sz : Z) (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  vl_at pc s10 ->
  0 < f -> f + 1024 < 2^63 -> 0 <= A -> A + 16 * cap < 2^63 -> 0 <= sz <= cap -> sz < 2 ->
  rw_cells asegs m (f + 32) [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (A + 16 * sz)); C8 (Z_to_bv 64 (A + 16 * cap))] -> mem_inv asegs m ->
  evt asegs (fun ms => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s9' s11' t3' t4' t5' t6' : word,
      ms = vl_st usp sp' f ATPA_EMPL (Z_to_bv 64 0xb18e8) gp t0' t1' t2' (Z_to_bv 64 (f + 32)) a1' a2' a3' a4' a5' a6' a7' s9' (Z_to_bv 64 16) s11' t3' t4' t5' t6' F fc m)
    (vl_st usp sp' f pc ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s9 s10 s11 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros PC F0 FH A0 AH SZ S2 SV MI. unfold vl_st, vl_at, EL_SPLITRET_A, EL_VLOOP_A, ATPA_EMPL in *.
  assert (EF : bv_unsigned (Z_to_bv 64 (f + 32)) = f + 32) by (apply unsigned_lit; lia).
  assert (E16 : A + 16 * sz + - A = 16 * sz) by lia.
  destruct PC as [-> | [(-> & ->) | (-> & ->)]]; vgo E16.
  all: apply evt_done; do 16 eexists; cbv delta [mkR]; reflexivity.
Qed.

Section Vec.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC2 : rt_contracts2 RT.
Variable PMc : Model -> Prop.

Local Ltac ul := unfold FUZZ_STACK, ATPA_SPLITINTO_STACK, ATPA_SPLIT_STACK, ATPA_PUSH_STACK in *; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Lemma vcap_iter_add : forall a b c s, vcap_iter (a + b) c s = vcap_iter b (vcap_iter a c s) (s + Z.of_nat a).
Proof.
  induction a as [|a IH]; intros b c s.
  - cbn [Nat.add vcap_iter]. rewrite Z.add_0_r. reflexivity.
  - cbn [Nat.add]. rewrite !vcap_iter_S0, IH. f_equal. lia.
Qed.

Theorem el_vec_ok : el_vec_cps RT PMc.
Proof using AF RC2.
  intros Σ0 m0 X d bs ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 K FDO MST LK LOW D0 BSL INLV LVPOS LVB CR0 CUTV.
  unfold cutS. intros Σ m t0 t1 t2 a2 a3 a4 a5 a6 a7 x9 x10 x11 t3 t4 t5 t6 F fc j0 j1 j2 j8 j10 j15 jr h3 t jv j56 jp j176 je j224 jos j528 idx act sel
    BASE FRl ACT SEL FS FV F56 FP F176 FE F224 FO F528 LV0 CR FRM.
  destruct BASE as (ARTg & MIg & STg & STp & FRs & FH & BS & LIB & PRES & FRSg & SPg).
  pose proof LK as [(SPR & SPA') (SPT & SPA) (LLO & LOR) (FPOS & F64 & FSEG & FLO) (FSELF & SHB0 & SHT)].
  destruct X as [usp sp' f lo]. cbn [lf_usp lf_S1 lf_F lf_lo] in *.
  pose proof (af_sp0_range RT AF Σ m ARTg) as SP0R. rewrite SPg in SP0R.
  assert (EU : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; ul).
  assert (INF : In (f, 4%nat) (rt_frames RT Σ)) by (rewrite FRSg; left; reflexivity).
  assert (SHF0 : shad f = f / 8 + SHB) by reflexivity.
  pose proof (af_frames_range RT AF Σ m f 4%nat ARTg INF) as (_ & _ & _ & FLV). change (fs_size 4) with 1024 in FLV.
  pose proof (rc2_rt RT RC2) as RC. pose proof (rtf_of_rt RT RC) as RTF.
  set (n := Z.of_nat (length bs)) in *. set (dd := chars (el_remA bs)). set (D := el_fddA d n).
  assert (EDD : zlength dd = el_fdsA n) by (subst dd n; rewrite chars_length; apply el_remA_length).
  assert (LDD : zlength dd <= n) by (rewrite EDD; unfold el_fdsA; subst n; destruct (10 <=? Z.of_nat (length bs)); lia).
  assert (DR : 0 <= D /\ (dd = [] \/ 0 < D) /\
               ((exists p k, In (p, k) (rt_live RT Σ) /\ p <= D /\ D + zlength dd <= p + k) \/ (dd = [] /\ D < SEGTOP_A))).
  { subst D dd. unfold el_fddA, el_remA. rewrite EDD. unfold el_fdsA. fold n. destruct (Z.leb_spec 10 n).
    - destruct INLV as [(p & k & Hin & P1 & P2)|(E0 & _)]; [| exfalso; subst bs n; cbn [length] in *; lia].
      split; [lia|]. split; [right; lia|]. left. exists p, k. rewrite LV0. split; [exact Hin| lia].
    - cbn. split; [lia|]. split; [left; reflexivity|]. right. split; [reflexivity| unfold SEGTOP_A; lia]. }
  destruct DR as (DZ & DPOS & INLVd).
  assert (BSd : bytes_at asegs m D (to_bytes dd)).
  { subst dd D. rewrite to_bytes_chars. unfold el_remA, el_fddA. fold n. destruct (Z.leb_spec 10 n); [| apply bytes_at_nil; lia].
    replace (d + 10) with (d + Z.of_nat 10) by lia. apply bytes_at_skipn; [exact BS| subst n; lia]. }
  assert (LENd : zlength dd < 2^26) by lia.
  pose proof (vcb_ok dd LENd) as VCB.
  assert (PLE : (length (poffs dd) <= atp_P dd)%nat) by (unfold atp_P; rewrite poffs_length; lia).
  assert (VMONO : forall a b, vcost_pushes a 0 0 <= vcost_pushes (a + b) 0 0).
  { intros a b. induction b as [|b IH]; [rewrite Nat.add_0_r; lia|].
    rewrite Nat.add_succ_r, vcost_pushes_snoc.
    pose proof (vcap_iter_inv (a + b) 0 0 ltac:(lia) ltac:(lia)) as VI.
    pose proof (vcost_push_nonneg (vcap_iter (a + b) 0 0) (0 + Z.of_nat (a + b)) ltac:(lia)). lia. }
  assert (VCM : vcost_pushes (length (poffs dd)) 0 0 <= vcost_pushes (atp_P dd) 0 0).
  { replace (atp_P dd) with (length (poffs dd) + (atp_P dd - length (poffs dd)))%nat by lia. apply VMONO. }

  assert (FOBJV : fobj RT Σ m (f + 32) 24).
  { split; [Z.div_mod_to_equations; lia|]. split; [lia|]. change ((24 + 7) / 8) with 3.
    split; [exists f, 4%nat; change (fs_size 4) with 1024; split; [exact INF| lia]|].
    replace (shad (f + 32)) with (shad f + 4) by (unfold shad, SHB; Z.div_mod_to_equations; lia).
    pose proof FS as XS. unfold el_shadowA, el_shbytesA in XS. cbn [map app repeat] in XS.
    lazymatch type of XS with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?e0 :: ?e1 :: ?e2 :: ?rest) =>
      change (c0 :: c1 :: c2 :: c3 :: e0 :: e1 :: e2 :: rest) with ([c0; c1; c2; c3] ++ [e0; e1; e2] ++ rest) in XS end.
    apply Sj_stage1_kit.rw_cells_app in XS. destruct XS as [_ XS]. apply Sj_stage1_kit.rw_cells_app in XS. destruct XS as [XS _].
    cbn [cells_size csize Nat.add] in XS. destruct XS as [[_ HB] _]. replace (shad f + Z.of_nat 4) with (shad f + 4) in HB by lia. exact HB. }
  pose proof FRl as FDC. unfold el_locals3 in FDC.
  lazymatch type of FDC with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?rest) =>
    change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: c9 :: c10 :: c11 :: c12 :: rest)
      with ([c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10] ++ [c11; c12] ++ rest) in FDC end.
  apply Sj_stage1_kit.rw_cells_app in FDC. destruct FDC as [FRlo FDC]. apply Sj_stage1_kit.rw_cells_app in FDC. destruct FDC as [FDC FRhi].
  cbn [cells_size csize Nat.add] in FDC, FRhi. replace (sp' + Z.of_nat 128) with (sp' + 128) in FDC, FRhi by lia. replace (sp' + 128 + Z.of_nat 16) with (sp' + 144) in FRhi by lia.
  fold n in FDC. fold D in FDC. rewrite <- EDD in FDC.

  eapply (aevt_rt RT PMc Σ K _ _
           (splitinto_closed RT AF RTF RC2 Σ PMc (wz EL_SPLITRET_A) (wz sp') gp (wz TPV_A) t0 t1 t2 (wz usp) (wz sp')
              (wz (f + 32)) (wz (sp' + 128)) a2 a3 a4 a5 a6 a7 (wz f) (wz (shad f)) (wz (f + 32)) (wz (f + 96)) (wz (f + 208)) (wz SHB) (wz f) x9 x10 x11 t3 t4 t5 t6
              F fc m (f + 32) (sp' + 128) D dd jv lo
              FDO MST eq_refl eq_refl eq_refl BSd (chars_range _) LENd DZ DPOS INLVd ltac:(rewrite LV0; exact LVPOS) FOBJV FV
              ltac:(rewrite EU; lia) ltac:(ul) ltac:(clear - SPA'; Z.div_mod_to_equations; lia) FDC
              ltac:(rewrite LV0; unfold FUZZ_LIVE in LVB; lia) ltac:(unfold FUZZ_COST in CR0; lia) ltac:(rewrite FRSg; cbn; unfold FRAMES_MAX2; lia)
              ARTg MIg ltac:(rewrite EU; exact STg) ltac:(rewrite SPg; exact LOW) ltac:(rewrite EU; ul) ltac:(rewrite EU; ul)
              ltac:(rewrite EU; clear - SPA'; Z.div_mod_to_equations; lia) FRM)); [exact FRM|].
  intros c (Σ1 & A1 & HA & VL1 & FRS1 & SP1 & CR1). eexists Σ1, _. split; [exact HA|].
  intros ms' (v & m1 & RS & (ART1 & MI1 & ST1) & PRES1 & VR1 & FD1) FRM1.
  destruct RS as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & ->). cbn [ms_fcsr] in FRM1.
  rewrite EU in ST1, PRES1. rewrite (ret_pc_even EL_SPLITRET_A) by (unfold EL_SPLITRET_A; lia). rewrite FRSg in PRES1, FRS1. rewrite SPg in SP1. rewrite LV0 in VL1.

  assert (P0Z : zlength (poffs dd) = Z.of_nat (length (poffs dd))) by reflexivity.
  assert (LOOP : forall (j k : nat) (Σx : rts RT) (mx : mem) (Ax pc : Z) (rax q0 q1 q2 a0x b1x b2x b3x b4x b5x b6x b7x s9x s10x s11x q3 q4 q5 q6 : word) (Fx : bvmap 5 word) (fcx : bv 32),
    let sz := (length (poffs dd) + k)%nat in
    (2 <= sz + j)%nat -> (k = 0%nat \/ (sz <= 2)%nat) ->
    vl_at pc s10x ->
    ART RT Σx mx -> mem_inv asegs mx -> stk asegs mx lo sp' -> frm0 fcx ->
    rt_frames RT Σx = [(f, 4%nat)] -> rt_sp0 RT Σx = rt_sp0 RT Σ0 ->
    vrepA mx (f + 32) Ax (vcap_iter sz 0 0) (Z.of_nat sz) (map (pview D) (poffs dd) ++ repeat (0, 0) k) ->
    vliveA (rt_live RT Σx) Ax (vcap_iter sz 0 0) (Z.of_nat sz) (rt_live RT Σ0) ->
    rt_credit RT Σ0 - 2 - vcost_pushes sz 0 0 <= rt_credit RT Σx ->
    (forall a : word, aclient (rt_live RT Σ0) [(f, 4%nat)] sp' (bv_unsigned a) -> outside [(f + 32, f + 56); (sp' + 128, sp' + 144)] (bv_unsigned a) -> mx a = m a) ->
    rw_cells asegs mx (sp' + 128) [C8 (wz (D + zlength dd)); C8 (wz 0)] ->
    aevt RT PMc Σx K (vl_st usp sp' f pc rax gp q0 q1 q2 a0x b1x b2x b3x b4x b5x b6x b7x s9x s10x s11x q3 q4 q5 q6 Fx fcx mx)).
  { induction j as [|j IH]; intros k Σx mx Ax pc rax q0 q1 q2 a0x b1x b2x b3x b4x b5x b6x b7x s9x s10x s11x q3 q4 q5 q6 Fx fcx sz J2 KB PC ARTx MIx STx FRMx FRSx SPx VRx VLx CRx AGX FDx.
    all: pose proof VRx as (ELS & SZC & CAPB & A0 & AH & SVx & BLKx).
    all: pose proof (vcap_iter_inv sz 0 0 ltac:(lia) ltac:(lia)) as CAPI; rewrite Z.add_0_l in CAPI.
    all: destruct (le_lt_dec 2 sz) as [SZ2|SZ2].
    2: { exfalso. lia. }
    1,2: apply (aevt_evt RT AF PMc MST);
         eapply evt_cut; [eapply (vl_exit usp sp' f pc Ax (vcap_iter sz 0 0) (Z.of_nat sz) rax gp q0 q1 q2 a0x b1x b2x b3x b4x b5x b6x b7x s9x s10x s11x q3 q4 q5 q6 Fx fcx mx
                                    PC FPOS ltac:(ul) A0 AH ltac:(lia) SVx MIx)|]; cbv beta;
         intros ms1 (er & e0 & e1 & e2 & ea0 & ea1 & ea2 & ea3 & ea4 & ea5 & ea6 & ea7 & e11 & e3 & e4 & e5 & e6 & ->); apply evt_done.
    1,2:
      assert (ESZ : sz = el_PA bs) by (unfold el_PA; fold dd; unfold atp_P; rewrite <- poffs_length; subst sz; lia);
      assert (EELS : map (pview D) (poffs dd) ++ repeat (0, 0) k = el_elsA d bs)
        by (unfold el_elsA, atp_elsA; fold n D dd; f_equal; f_equal; unfold atp_P; rewrite <- poffs_length; subst sz; lia);
      unfold vl_st;
      assert (AGP : forall (P : Z -> Prop), (forall x, P x -> aclient (rt_live RT Σ0) [(f, 4%nat)] sp' x /\ ~ (f + 32 <= x < f + 56) /\ ~ (sp' + 128 <= x < sp' + 144)) -> agree_on P m mx)
        by (intros P HP a Ha; destruct (HP _ Ha) as (H1 & H2 & H3); apply AGX; [exact H1| cbn [outside]; repeat split; assumption]);
      assert (INF' : forall lo' hi', f <= lo' -> hi' <= f + 1016 -> forall x, lo' <= x < hi' -> aclient (rt_live RT Σ0) [(f, 4%nat)] sp' x)
        by (intros lo' hi' H1 H2 x Hx; right; right; right; left; exists f, 4%nat; split; [left; reflexivity| change (fs_size 4) with 1024; lia]);
      assert (INS' : forall x, shad f <= x < shad f + 128 -> aclient (rt_live RT Σ0) [(f, 4%nat)] sp' x)
        by (intros x Hx; right; right; right; right; exists f, 4%nat; split; [left; reflexivity| rewrite SHF0 in Hx |- *; unfold shad, SHB in *; change (fs_size 4) with 1024; Z.div_mod_to_equations; lia]).
    1,2: eapply (CUTV Σx mx er e0 e1 e2 ea0 ea1 ea2 ea3 ea4 ea5 ea6 ea7 e11 e3 e4 e5 e6 Fx fcx j0 j1 j2 j8 j10 j15 jr h3 t j56 jp j176 je j224 jos j528 idx act sel Ax);
           cbn [lf_usp lf_S1 lf_F lf_lo];
           [| | exact ACT| exact SEL| | rewrite <- ESZ, <- EELS; exact VRx| | | | | | | | rewrite <- ESZ; exact VLx| unfold el_vcostA; rewrite <- ESZ; clear - CRx; lia| exact FRMx].
    all: try (eapply rw_cells_agree_nw; [first [exact FS| exact F56| exact FP| exact F176| exact FE| exact F224| exact FO| exact F528]|]; apply AGP; intros x Hx;
              first [rewrite el_shadowA_size in Hx; split; [apply INS'; lia| unfold shad, SHB in *; split; ul]
                    | cbn [cells_size csize Nat.add] in Hx; split; [eapply INF'; [| | exact Hx]; lia| split; ul]]).
    1,3:
      unfold el_baseA; cbn [lf_usp lf_S1 lf_F lf_lo];
      split; [exact ARTx|]; split; [exact MIx|]; split; [exact STx|];
      split; [eapply stk_agree_nw; [exact STp|]; apply AGP; intros x Hx; cbv beta in Hx; split; [left; ul| split; ul]|];
      split; [eapply rw_cells_agree_nw; [exact FRs|]; apply AGP; intros x Hx; unfold fa_saved in Hx; cbn [cells_size csize Nat.add] in Hx; split; [left; ul| split; ul]|];
      split; [eapply rw_cells_agree_nw; [exact FH|]; apply AGP; intros x Hx; unfold fz_hdr in Hx; cbn [cells_size csize Nat.add] in Hx; split; [apply (INF' f (f + 32)); lia| split; ul]|];
      split; [| split; [| split; [| split; [exact FRSx| exact SPx]]]].
    1,4: apply (bytes_at_agree asegs m mx _ _ BS); apply AGP; intros x Hx; cbv beta in Hx;
         destruct INLV as [(p & kk & Hin & P1 & P2)| (E0 & DL)]; [| subst n; rewrite E0 in Hx; cbn [length] in Hx; lia];
         pose proof (af_live_range RT AF Σ m p kk ARTg ltac:(rewrite LV0; exact Hin)) as (R0 & R1 & R2); rewrite SPg in R1;
         pose proof (FLV p kk ltac:(rewrite LV0; exact Hin)) as Y1;
         split; [right; right; left; exists p, kk; split; [exact Hin| subst n; lia]| clear - Hx P1 P2 R1 Y1 LOW LOR SPR; subst n; split; ul].
    1,3: eapply el_libA_agree; [exact LIB|]; apply AGP; intros x Hx; pose proof (el_lib_rng_static _ Hx) as [CS R]; pose proof (client_static_range _ CS);
         unfold SEGTOP_A in *; split; [right; left; exact CS| split; ul].
    1,2: intros a Ha Ho; rewrite <- (PRES a Ha Ho); apply AGX;
         [apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros q Hq; exact Hq| intros q []| lia]|];
         cbn [outside]; destruct Ha as [H|[H|[H|[H|H]]]]; [clear - H FLO SPR LOR LOW; split; [ul| split; [ul| exact I]]
           | pose proof (client_static_range _ H); unfold SEGTOP_A in *; split; [lia| split; [ul| exact I]]
           | destruct H as (p & kk & Hin & Hr); pose proof (af_live_range RT AF Σ m p kk ARTg ltac:(rewrite LV0; exact Hin)) as (R0 & R1 & R2); rewrite SPg in R1;
             pose proof (FLV p kk ltac:(rewrite LV0; exact Hin)) as Y1;
             clear - Hr R1 Y1 LOW LOR SPR; split; [lia| split; [ul| exact I]]
           | destruct H as (? & ? & [] & _)| destruct H as (? & ? & [] & _)].
    1,2:
      unfold el_locals3;
      lazymatch goal with |- rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?rest) =>
        change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: c9 :: c10 :: c11 :: c12 :: rest)
          with ([c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10] ++ [c11; c12] ++ rest) end;
      apply Sj_stage1_kit.rw_cells_app; split;
        [eapply rw_cells_agree_nw; [exact FRlo|]; apply AGP; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [left; ul| split; ul]|];
      cbn [cells_size csize Nat.add]; replace (sp' + Z.of_nat 128) with (sp' + 128) by lia;
      apply Sj_stage1_kit.rw_cells_app; split; [fold n D; rewrite <- EDD; exact FDx|];
      cbn [cells_size csize Nat.add]; replace (sp' + 128 + Z.of_nat 16) with (sp' + 144) by lia;
      eapply rw_cells_agree_nw; [exact FRhi|]; apply AGP; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [left; ul| split; ul].
    -
      assert (FOBJx : fobj RT Σx mx (f + 32) 24).
      { split; [Z.div_mod_to_equations; lia|]. split; [lia|]. change ((24 + 7) / 8) with 3.
        split; [exists f, 4%nat; change (fs_size 4) with 1024; split; [rewrite FRSx; left; reflexivity| lia]|].
        destruct FOBJV as (_ & _ & _ & HB). eapply bytes_at_agree; [exact HB|].
        intros a Ha. rewrite repeat_length in Ha. change (Z.of_nat (Z.to_nat ((24 + 7) / 8))) with 3 in Ha.
        apply AGX; [right; right; right; right; exists f, 4%nat; split; [left; reflexivity|] | cbn [outside]].
        - replace (shad (f + 32)) with (shad f + 4) in Ha by (unfold shad, SHB; Z.div_mod_to_equations; lia). rewrite SHF0 in Ha |- *. unfold shad, SHB in *. change (fs_size 4) with 1024. Z.div_mod_to_equations; lia.
        - replace (shad (f + 32)) with (shad f + 4) in Ha by (unfold shad, SHB; Z.div_mod_to_equations; lia). unfold shad, SHB in *. split; [lia|]. split; [ul| exact I]. }
      assert (CRP : vcost_push (vcap_iter sz 0 0) (Z.of_nat sz) <= rt_credit RT Σx).
      { pose proof (VMONO (S sz) (atp_P dd - S sz)%nat) as VM. replace (S sz + (atp_P dd - S sz))%nat with (atp_P dd) in VM by (unfold atp_P in *; lia).
        rewrite vcost_pushes_snoc, Z.add_0_l in VM. unfold FUZZ_COST in CR0. clear - VM VCB CRx CR0 CR. lia. }
      assert (ESZ1 : Z.of_nat sz + 1 = Z.of_nat (length (poffs dd) + S k)) by (subst sz; lia).
      assert (EELS1 : (map (pview D) (poffs dd) ++ repeat (0, 0) k) ++ [(0, 0)] = map (pview D) (poffs dd) ++ repeat (0, 0) (S k)).
      { first [rewrite <- (app_assoc (map (pview D) (poffs dd))) | rewrite (app_assoc (map (pview D) (poffs dd)))]. f_equal.
        clear. induction k as [|k IHk]; [reflexivity| cbn; rewrite IHk; reflexivity]. }

      assert (ECAP1 : vcap_after (vcap_iter sz 0 0) (Z.of_nat sz) = vcap_iter (length (poffs dd) + S k) 0 0).
      { replace (length (poffs dd) + S k)%nat with (S sz) by (subst sz; lia). rewrite vcap_iter_S. f_equal; lia. }
      apply (aevt_evt RT AF PMc MST).
      eapply evt_cut; [eapply (vl_callf usp sp' f pc Ax (vcap_iter sz 0 0) (Z.of_nat sz) rax gp q0 q1 q2 a0x b1x b2x b3x b4x b5x b6x b7x s9x s10x s11x q3 q4 q5 q6 Fx fcx mx
                                 PC FPOS ltac:(ul) A0 AH ltac:(lia) ltac:(lia) SVx MIx)|]; cbv beta.
      intros ms1 (e0 & e1 & e2 & ea1 & ea2 & ea3 & ea4 & ea5 & ea6 & ea7 & e9 & e11 & e3 & e4 & e5 & e6 & ->). apply evt_done. unfold vl_st.
      eapply (aevt_rt RT PMc Σx K _ _
               (empl_ok RT AF RTF (rc2_annotate RT RC2) Σx PMc (wz 0xb18e8) (wz sp') gp (wz TPV_A) e0 e1 e2 (wz usp) (wz sp') (wz (f + 32)) ea1 ea2 ea3 ea4 ea5 ea6 ea7
                  (wz f) (wz (shad f)) (wz (f + 32)) (wz (f + 96)) (wz (f + 208)) (wz SHB) (wz f) e9 (wz 16) e11 e3 e4 e5 e6 Fx fcx mx
                  (f + 32) Ax (vcap_iter sz 0 0) (Z.of_nat sz) (map (pview D) (poffs dd) ++ repeat (0, 0) k) (rt_live RT Σ0) lo
                  FDO MST eq_refl eq_refl VRx VLx LVPOS ltac:(clear - SZ2; lia) FOBJx ltac:(unfold FUZZ_LIVE in LVB; lia) CRP
                  ARTx MIx ltac:(rewrite EU; exact STx) ltac:(rewrite SPx; exact LOW) ltac:(rewrite EU; ul) ltac:(rewrite EU; ul)
                  ltac:(rewrite EU; clear - SPA'; Z.div_mod_to_equations; lia) FRMx)); [exact FRMx|].
      intros c2 (Σy & Ay & HA2 & VL2 & FRS2 & SP2 & CR2). eexists Σy, _. split; [exact HA2|].
      intros ms2 (v2 & my & RS2 & (ART2 & MI2 & ST2) & PRES2 & VR2) FRM2.
      destruct RS2 as (w0 & w1 & w2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & w3 & w4 & w5 & w6 & F2 & fc2 & ->). cbn [ms_fcsr] in FRM2.
      rewrite EU in ST2, PRES2. rewrite (ret_pc_even 0xb18e8) by lia. rewrite FRSx in PRES2, FRS2. rewrite SPx in SP2.
      apply (IH (S k) Σy my Ay 0xb18e8 (wz 0xb18e8) w0 w1 w2 v2 g1 g2 g3 g4 g5 g6 g7 e9 (wz 16) e11 w3 w4 w5 w6 F2 fc2); cbn zeta.
      + subst sz. lia.
      + right. subst sz. lia.
      + right. right. split; reflexivity.
      + exact ART2. + exact MI2. + exact ST2. + exact FRM2. + exact FRS2. + exact SP2.
      + rewrite <- ECAP1, <- ESZ1, <- EELS1. exact VR2.
      + rewrite <- ECAP1, <- ESZ1. exact VL2.
      + replace (length (poffs dd) + S k)%nat with (S sz) by (subst sz; lia). rewrite vcost_pushes_snoc. rewrite Z.add_0_l. clear - CR2 CRx. lia.
      + intros a Ha Ho. rewrite <- (AGX a Ha Ho). apply PRES2; [exact Ha|]. cbn [outside] in Ho |- *. destruct Ho as (H1 & _). split; [lia| exact I].
      + eapply rw_cells_agree_nw; [exact FDx|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply PRES2; [left; ul| cbn [outside]; split; [ul| exact I]]. }

  assert (AG1 : forall a : word, aclient (rt_live RT Σ0) [(f, 4%nat)] sp' (bv_unsigned a) -> outside [(f + 32, f + 56); (sp' + 128, sp' + 144)] (bv_unsigned a) -> m1 a = m a).
  { intros a Ha Ho. rewrite LV0 in PRES1. apply PRES1; [exact Ha|]. cbn [outside] in Ho |- *. destruct Ho as (H1 & H2 & _). split; [lia|]. split; [lia| exact I]. }
  apply (LOOP (2%nat) 0%nat Σ1 m1 A1 EL_SPLITRET_A (wz EL_SPLITRET_A) u0 u1 u2 v b1 b2 b3 b4 b5 b6 b7 x9 x10 x11 u3 u4 u5 u6 F1 fc1); cbn zeta.
  - lia.
  - left. reflexivity.
  - left. reflexivity.
  - exact ART1. - exact MI1. - exact ST1. - exact FRM1. - exact FRS1. - exact SP1.
  - rewrite Nat.add_0_r, app_nil_r. rewrite P0Z in VR1. exact VR1.
  - rewrite Nat.add_0_r. rewrite P0Z in VL1. exact VL1.
  - rewrite Nat.add_0_r. clear - CR1 CR. lia.
  - exact AG1.
  - exact FD1.
Qed.
End Vec.
