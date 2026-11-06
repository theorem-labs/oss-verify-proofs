(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjTape SjTapeList SjTapeTile.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.P Require Import Str_tac Sj_stage1_kit.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.A Require Import Layout Shadow RT_iface RT_iface2 RT_iface3 D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit
     Sj_num_akit Atp_fzwA Atp_defsA Atp_kitA Pj_rtkA Pj_defsA Pj_os_defsA El_defsA El_os_defsA El_ins_ifaceA Dmp_hdefsA Dmp_pj_ifaceA Dmp_insbA Dmp_pj_kitA Dmp_pj_leafA
     Dmp_pj_strA Dmp_pj_arrA Dmp_pj_objA Dmp_pj_aevtA Dmp_pj_entryA Dmp_pj_casesA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Local Ltac ulx := unfold DMP_PJ_LEAF_A, DMP_PJ_FRAME_A, EL_PUT_STACK_A, EL_INS_STACK_A, EL_INSD_STACK_A, SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, SHB in *; lia.
Local Ltac acc_in := unfold ACC_LITS; cbn [In]; repeat (try (left; reflexivity); right).

Definition pj_frAL (j0 : list byte) (f : Z) (j48 : list byte) (osp : Z) (jB : list byte) (sv : list cell) : list cell :=
  [CB 24 j0; C8 (Z_to_bv 64 DMP_LIT_RBRK_A); C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 f); CB 56 j48; C8 (Z_to_bv 64 4294967295); C8 (Z_to_bv 64 4294967297);
   C8 (Z_to_bv 64 osp); CB 16 jB; C8 (Z_to_bv 64 f)] ++ sv.

Definition pj_frOE (j0 j24 : list byte) (f : Z) (j48 j56 j64 j72 j80 j88 j96 j104 : list byte) (e osp : Z) (jB : list byte) (sv : list cell) : list cell :=
  [CB 24 j0; CB 8 j24; C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 f); CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104;
   C8 (Z_to_bv 64 e); C8 (Z_to_bv 64 osp); CB 16 jB; C8 (Z_to_bv 64 f)] ++ sv.

Definition pj_frOL (j0 : list byte) (E : aenvA) (f e osp : Z) (jB : list byte) (sv : list cell) : list cell :=
  ([CB 24 j0] ++ pj_oframe E f e osp ++ [CB 16 jB; C8 (Z_to_bv 64 f)]) ++ sv.

Lemma pj_frAL_24 : forall m S1 j0 f j48 osp jB sv, rw_cells asegs m S1 (pj_frAL j0 f j48 osp jB sv) ->
  rw_cells asegs m (S1 + 24) [C8 (Z_to_bv 64 DMP_LIT_RBRK_A); C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 f)].
Proof.
  intros. unfold pj_frAL in H. replace (S1 + 24) with (S1 + Z.of_nat (cells_size [CB 24 j0])) by (cbn; lia).
  eapply (rw_cells_mid m S1 [CB 24 j0] _ ([CB 56 j48; C8 (Z_to_bv 64 4294967295); C8 (Z_to_bv 64 4294967297); C8 (Z_to_bv 64 osp); CB 16 jB; C8 (Z_to_bv 64 f)] ++ sv)). exact H.
Qed.
Lemma pj_frAL_104 : forall m S1 j0 f j48 osp jB sv, rw_cells asegs m S1 (pj_frAL j0 f j48 osp jB sv) -> rw_cells asegs m (S1 + 104) [C8 (Z_to_bv 64 4294967295)].
Proof.
  intros. unfold pj_frAL in H. replace (S1 + 104) with (S1 + Z.of_nat (cells_size [CB 24 j0; C8 (Z_to_bv 64 DMP_LIT_RBRK_A); C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 f); CB 56 j48])) by (cbn; lia).
  eapply (rw_cells_mid m S1 _ _ ([C8 (Z_to_bv 64 4294967297); C8 (Z_to_bv 64 osp); CB 16 jB; C8 (Z_to_bv 64 f)] ++ sv)). exact H.
Qed.
Lemma pj_frAL_112 : forall m S1 j0 f j48 osp jB sv, rw_cells asegs m S1 (pj_frAL j0 f j48 osp jB sv) -> rw_cells asegs m (S1 + 112) [C8 (Z_to_bv 64 4294967297)].
Proof.
  intros. unfold pj_frAL in H. replace (S1 + 112) with (S1 + Z.of_nat (cells_size [CB 24 j0; C8 (Z_to_bv 64 DMP_LIT_RBRK_A); C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 f); CB 56 j48; C8 (Z_to_bv 64 4294967295)])) by (cbn; lia).
  eapply (rw_cells_mid m S1 _ _ ([C8 (Z_to_bv 64 osp); CB 16 jB; C8 (Z_to_bv 64 f)] ++ sv)). exact H.
Qed.
Lemma pj_frAL_120 : forall m S1 j0 f j48 osp jB sv, rw_cells asegs m S1 (pj_frAL j0 f j48 osp jB sv) -> rw_cells asegs m (S1 + 120) [C8 (Z_to_bv 64 osp)].
Proof.
  intros. unfold pj_frAL in H. replace (S1 + 120) with (S1 + Z.of_nat (cells_size [CB 24 j0; C8 (Z_to_bv 64 DMP_LIT_RBRK_A); C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 f); CB 56 j48; C8 (Z_to_bv 64 4294967295); C8 (Z_to_bv 64 4294967297)])) by (cbn; lia).
  eapply (rw_cells_mid m S1 _ _ ([CB 16 jB; C8 (Z_to_bv 64 f)] ++ sv)). exact H.
Qed.
Lemma pj_frOE_120 : forall m S1 j0 j24 f j48 j56 j64 j72 j80 j88 j96 j104 e osp jB sv, rw_cells asegs m S1 (pj_frOE j0 j24 f j48 j56 j64 j72 j80 j88 j96 j104 e osp jB sv) ->
  rw_cells asegs m (S1 + 120) [C8 (Z_to_bv 64 osp)].
Proof.
  intros. unfold pj_frOE in H.
  replace (S1 + 120) with (S1 + Z.of_nat (cells_size [CB 24 j0; CB 8 j24; C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 f); CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; C8 (Z_to_bv 64 e)])) by (cbn; lia).
  eapply (rw_cells_mid m S1 _ _ ([CB 16 jB; C8 (Z_to_bv 64 f)] ++ sv)). exact H.
Qed.
Lemma pj_frOL_24 : forall m S1 j0 E f e osp jB sv, rw_cells asegs m S1 (pj_frOL j0 E f e osp jB sv) -> rw_cells asegs m (S1 + 24) (pj_oframe E f e osp).
Proof.
  intros. unfold pj_frOL in H. rewrite <- app_assoc in H. replace (S1 + 24) with (S1 + Z.of_nat (cells_size [CB 24 j0])) by (cbn; lia).
  eapply (rw_cells_mid m S1 [CB 24 j0] _ _). rewrite <- app_assoc in H. exact H.
Qed.
Lemma pj_frOL_c1 : forall m S1 j0 E f e osp jB sv, rw_cells asegs m S1 (pj_frOL j0 E f e osp jB sv) ->
  rw_cells asegs m (S1 + 24) [C8 (Z_to_bv 64 DMP_LIT_RBRC_A); C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 f)].
Proof.
  intros. pose proof (pj_frOL_24 _ _ _ _ _ _ _ _ _ H) as X. unfold pj_oframe in X.
  lazymatch type of X with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?rest) => change (c0 :: c1 :: c2 :: rest) with ([c0; c1; c2] ++ rest) in X end.
  apply rw_cells_app in X. destruct X as [X _]. exact X.
Qed.
Lemma pj_frOL_120 : forall m S1 j0 E f e osp jB sv, rw_cells asegs m S1 (pj_frOL j0 E f e osp jB sv) -> rw_cells asegs m (S1 + 120) [C8 (Z_to_bv 64 osp)].
Proof.
  intros. pose proof (pj_frOL_24 _ _ _ _ _ _ _ _ _ H) as X. unfold pj_oframe in X.
  lazymatch type of X with rw_cells _ _ _ [?c0; ?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8; ?c9; ?c10; ?c11; ?c12] =>
    change [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12] with ([c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11] ++ [c12] ++ []) in X end.
  apply rw_cells_mid in X. cbn [cells_size csize Nat.add] in X. replace (S1 + 24 + Z.of_nat 96) with (S1 + 120) in X by lia. exact X.
Qed.
Lemma pj_frAL_size : forall j0 f j48 osp jB, cells_size [CB 24 j0; C8 (Z_to_bv 64 DMP_LIT_RBRK_A); C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 f); CB 56 j48; C8 (Z_to_bv 64 4294967295); C8 (Z_to_bv 64 4294967297);
   C8 (Z_to_bv 64 osp); CB 16 jB; C8 (Z_to_bv 64 f)] = 152%nat.
Proof. intros. reflexivity. Qed.
Lemma pj_frOL_size : forall j0 E f e osp jB, cells_size ([CB 24 j0] ++ pj_oframe E f e osp ++ [CB 16 jB; C8 (Z_to_bv 64 f)]) = 152%nat.
Proof. intros. reflexivity. Qed.

Lemma elem_kindA : forall T S sn d i j, elem T S sn ck_any d i j -> pj_kindA T S sn i j.
Proof.
  intros T S sn d i j EL. unfold pj_kindA. destruct d as [|d']; cbn [elem] in EL.
  - destruct EL as [SC|[]]. destruct SC as [X|[X|X]]; [left; exact X| right; left; exact X| right; right; left; exact X].
  - destruct EL as [SC|CO].
    + destruct SC as [X|[X|X]]; [left; exact X| right; left; exact X| right; right; left; exact X].
    + destruct CO as (e2 & c2 & cv2 & -> & CK & [(X & _ & _)|(X & _ & _)]); do 3 right; exists cv2; unfold ck_any in CK; (split; [exact CK|]); [left| right]; exact X.
Qed.

Section Loops.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis SM2 : stack_malloc2_contract RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Hypothesis PUT : os_put_cpsA RT PMc.
Notation aevt := (aevt RT PMc).
Notation PINVA := (PINVA RT).
Notation KEXITA := (KEXITA RT PMc).

Variable G : pctx.
Hypothesis GOK : pctx_ok G.
Hypothesis AI0 : AINV_A (g_E G) (g_m0 G).
Hypothesis IOS0 : io_ssp (g_m0 G).

Variable d' : nat.
Hypothesis GD : g_d G = S d'.
Hypothesis PJ : Dmp_pj_ifaceA.pj_cpsA RT PMc d'.
Notation E := (g_E G).
Notation n := (ae_n (g_E G)).
Notation T := (ae_T (g_E G)).
Notation S := (ae_S (g_E G)).
Notation sn := (ae_sn (g_E G)).
Notation osp := (g_OS G + 128).

Let facts : aenvA_ok E /\ 0x6c9000 <= g_q G - 256 /\ g_q G < 2^63 /\ 0 <= g_OS G + 128 < 2^64 /\ 0 < g_ff G /\ ae_n E < 2^32 /\ 0 <= ae_sn E < 2^56
            /\ g_ff G + 256 < 2^63 /\ shad (g_ff G) + 32 < 2^63 /\ ae_lo E <= g_q G - 256.
Proof.
  destruct GOK as [(Q32 & QT & LQ) (LO1 & LO2) (SP1 & SP2) (OK & _) (EIN & ELO & EHI & _) (F0 & F64 & FSEG & FLO & FHI & SHLO & _) _ _ RFR _ _ _].
  pose proof (RFR _ _ EIN) as (_ & ESEG & EL & _). pose proof (pj_needA_0 (g_d G)) as ND. pose proof (Atp_defsA.ok_wf E OK) as (NR & SNR & _).
  assert (0 <= fs_size (g_kO G)) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
  split; [exact OK|]. repeat split; try assumption; ulx.
Qed.

Definition KCLOSEA (fcs : list cell) (kc : Z) (K : config -> Prop) (gp : word) (lit : Z) : Prop :=
  forall (Σ : rts RT) (m : mem) (k : Z) (ra a0 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    PINVA G fcs k Σ m -> frm0 fc -> k + 2 <= kc ->
    aevt Σ K (MS (pjR (g_q G) (g_ff G) gp ra a0 (wz lit) a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6) F (wz DMP_PJ_CLOSE_A) fc None m (seg_rom asegs)).

Definition KLOOPXA (fcs : list cell) (kc : Z) (K : config -> Prop) (gp : word) : Prop :=
  forall (Σ : rts RT) (m : mem) (k : Z) (ra a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    PINVA G fcs k Σ m -> frm0 fc -> k + 2 <= kc ->
    aevt Σ K (MS (mkR ra (wz (g_S1 G)) gp (wz TPV_A) t0 t1 t2 (wz (g_q G)) (wz (g_S1 G)) a0 a1 a2 a3 a4 a5 a6 a7
                      (wz SHB) s3 s4 s5 s6 s7 s8 s9 (wz (shad (g_ff G))) s11 t3 t4 t5 t6) F (wz DMP_PJ_LOOPX_A) fc None m (seg_rom asegs)).

Lemma pa_close : forall (fcs : list cell) (kx : Z) (K : config -> Prop) (gp : word) (lit : Z),
  (lit = DMP_LIT_RBRK_A \/ lit = DMP_LIT_RBRC_A) ->
  (forall mx, rw_cells asegs mx (g_S1 G) fcs -> rw_cells asegs mx (g_S1 G + 120) [C8 (wz osp)]) ->
  kx <= g_cr G -> KEXITA G fcs kx K gp -> KCLOSEA fcs kx K gp lit.
Proof using AF FDO MST PUT GOK facts.
  intros fcs kx K gp lit LIT X120 KX HK. unfold KCLOSEA. intros until fc. intros GI FRM KB. pose proof facts as (OK & QLO & QH & OR & F0 & NR & SNR & FH & SFH & LOS).
  pose proof GI as (_ & MI & _ & _ & _ & _ & _ & _ & _ & _ & _ & (FR & _) & _). pose proof (X120 _ FR) as FO. replace (g_S1 G + 120) with (g_q G - 256 + 120) in FO by lia.
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (pj_close0 (g_q G) (g_ff G) osp gp ra a0 (wz lit) a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 F fc m QLO QH OR FO MI)|].
  cbv beta. intros ms1 ->. apply evt_done. unfold pjR.
  destruct LIT as [-> | ->]; unfold DMP_LIT_RBRK_A, DMP_LIT_RBRC_A.
  - eapply (p_put_lit RT AF PMc FDO MST G GOK _ k Σ K 0x23500 1 2 1%nat); [exact PUT| exact GI| acc_in| vm_compute; reflexivity| vm_compute; reflexivity
      | cbn; lia| cbn; lia| lia| unfold SEGTOP_A; lia| clear - KB KX; lia|].
    intros Σ2 u0 u1 u2 e1 e2 e3 e4 e5 e6 e7 u3 u4 u5 u6 F2 m2 GI2. rewrite (ret_pc_even DMP_PJ_EXIT_A) by (unfold DMP_PJ_EXIT_A; lia).
    eapply HK; [exact GI2| clear - KB; lia| exact FRM].
  - eapply (p_put_lit RT AF PMc FDO MST G GOK _ k Σ K 0x23580 1 2 1%nat); [exact PUT| exact GI| acc_in| vm_compute; reflexivity| vm_compute; reflexivity
      | cbn; lia| cbn; lia| lia| unfold SEGTOP_A; lia| clear - KB KX; lia|].
    intros Σ2 u0 u1 u2 e1 e2 e3 e4 e5 e6 e7 u3 u4 u5 u6 F2 m2 GI2. rewrite (ret_pc_even DMP_PJ_EXIT_A) by (unfold DMP_PJ_EXIT_A; lia).
    eapply HK; [exact GI2| clear - KB; lia| exact FRM].
Qed.

Lemma pa_xclose : forall (fcs : list cell) (kx : Z) (K : config -> Prop) (gp : word) (lit : Z),
  (lit = DMP_LIT_RBRK_A \/ lit = DMP_LIT_RBRC_A) ->
  (forall mx, rw_cells asegs mx (g_S1 G) fcs -> rw_cells asegs mx (g_S1 G + 24) [C8 (wz lit); C8 (wz (g_ff G)); C8 (wz (g_ff G))]) ->
  (forall mx, rw_cells asegs mx (g_S1 G) fcs -> rw_cells asegs mx (g_S1 G + 120) [C8 (wz osp)]) ->
  kx <= g_cr G -> KEXITA G fcs kx K gp -> KLOOPXA fcs kx K gp.
Proof using AF FDO MST PUT GOK facts.
  intros fcs kx K gp lit LIT X24 X120 KX HK. unfold KLOOPXA. intros until fc. intros GI FRM KB. pose proof facts as (OK & QLO & QH & OR & F0 & NR & SNR & FH & SFH & LOS).
  pose proof GI as (_ & MI & _ & _ & _ & _ & _ & _ & _ & _ & _ & (FR & _) & _).
  pose proof (X120 _ FR) as FO. replace (g_S1 G + 120) with (g_q G - 256 + 120) in FO by lia.
  pose proof (X24 _ FR) as F24. replace (g_S1 G + 24) with (g_q G - 256 + 24) in F24 by lia.
  assert (LR : 0 <= lit < 2^64) by (destruct LIT as [-> | ->]; unfold DMP_LIT_RBRK_A, DMP_LIT_RBRC_A; lia).
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (pj_close1 (g_q G) (g_ff G) osp lit gp ra a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 F fc m QLO QH OR LR F0 FH F24 FO MI)|].
  cbv beta. intros ms1 ->. apply evt_done. unfold pjR.
  destruct LIT as [-> | ->]; unfold DMP_LIT_RBRK_A, DMP_LIT_RBRC_A.
  - eapply (p_put_lit RT AF PMc FDO MST G GOK _ k Σ K 0x23500 1 2 1%nat); [exact PUT| exact GI| acc_in| vm_compute; reflexivity| vm_compute; reflexivity
      | cbn; lia| cbn; lia| lia| unfold SEGTOP_A; lia| clear - KB KX; lia|].
    intros Σ2 u0 u1 u2 e1 e2 e3 e4 e5 e6 e7 u3 u4 u5 u6 F2 m2 GI2. rewrite (ret_pc_even DMP_PJ_EXIT_A) by (unfold DMP_PJ_EXIT_A; lia).
    eapply HK; [exact GI2| clear - KB; lia| exact FRM].
  - eapply (p_put_lit RT AF PMc FDO MST G GOK _ k Σ K 0x23580 1 2 1%nat); [exact PUT| exact GI| acc_in| vm_compute; reflexivity| vm_compute; reflexivity
      | cbn; lia| cbn; lia| lia| unfold SEGTOP_A; lia| clear - KB KX; lia|].
    intros Σ2 u0 u1 u2 e1 e2 e3 e4 e5 e6 e7 u3 u4 u5 u6 F2 m2 GI2. rewrite (ret_pc_even DMP_PJ_EXIT_A) by (unfold DMP_PJ_EXIT_A; lia).
    eapply HK; [exact GI2| clear - KB; lia| exact FRM].
Qed.

Definition ALSA (e it pc : Z) (gp ra a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state :=
  MS (pjRL E (g_q G) (g_ff G) osp e gp ra a0 a1 a2 a3 a4 a5 a6 a7 (wz it) t0 t1 t2 t3 t4 t5 t6) F (wz pc) fc None m (seg_rom asegs).

Definition KALOOPA (fcs : list cell) (kx : Z) (K : config -> Prop) (gp : word) (e it : Z) : Prop :=
  forall (Σ : rts RT) (m : mem) (k : Z) (ra a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    PINVA G fcs k Σ m -> frm0 fc -> k + DMP_PJ_CW * (e - it) + 2 <= kx ->
    aevt Σ K (ALSA e it DMP_PJ_ALOOP_A gp ra a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 F fc m).

Lemma pa_step : forall (j0 j48 jB : list byte) (sv : list cell) (k kx : Z) (Σ : rts RT) (K : config -> Prop) (e it j : Z)
    (gp ra a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  let fcs := pj_frAL j0 (g_ff G) j48 osp jB sv in
  PINVA G fcs k Σ m -> frm0 fc -> elem T S sn ck_any d' it j -> 0 <= it -> j <= e -> e + 1 <= n ->
  k + pj_costE it j + 2 <= kx -> kx <= g_cr G ->
  (forall (Σ' : rts RT) (m' : mem) (k' : Z) (ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32),
     PINVA G fcs k' Σ' m' -> frm0 fc' -> k' <= k + pj_costE it j + 2 ->
     aevt Σ' K (ALSA e j DMP_PJ_ATEST_A gp ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' F' fc' m')) ->
  aevt Σ K (ALSA e it DMP_PJ_ALOOP_A gp ra a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 F fc m).
Proof using AF FDO MST PUT GOK AI0 IOS0 GD PJ facts.
  intros until m. cbv zeta. intros GI FRM EL I0 JE EN KB KX HK. pose proof facts as (OK & QLO & QH & OR & F0 & NR & SNR & FH & SFH & LOS).
  pose proof (elem_lt _ _ _ _ _ _ _ EL) as IJ.
  assert (CE : 0 <= pj_costE it j) by (unfold pj_costE, DMP_PJ_CW; clear - IJ; lia).
  pose proof GI as (_ & MI & _). unfold ALSA.

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (pj_aloop1 E (g_q G) (g_ff G) osp e it gp ra a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 F fc m MI)|].
  cbv beta. intros ms1 ->. apply evt_done. unfold pjRL.
  eapply (p_child RT AF PMc FDO MST G GOK d' _ k Σ K it j); [exact PJ| exact GI| exact AI0| exact IOS0| exact FRM| exact EL| exact I0| clear - JE EN; lia| exact GD| clear - KB KX; lia|].
  intros Σ2 u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F2 fc2 m2 GI2 FRM2. rewrite (ret_pc_even 0xaf628) by lia.
  pose proof GI2 as (_ & MI2 & _).

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (pj_aloop2 E (g_q G) (g_ff G) osp e it gp (wz 0xaf628) b0 b1 b2 b3 b4 b5 b6 b7 u0 u1 u2 u3 u4 u5 u6 F2 fc2 m2 MI2)|].
  cbv beta. intros ms3 ->. apply evt_done. unfold pjRL, DMP_LIT_COMMA_A.
  eapply (p_put_lit RT AF PMc FDO MST G GOK _ (k + pj_costE it j) Σ2 K 0x234e0 1 2 1%nat); [exact PUT| exact GI2| acc_in| vm_compute; reflexivity| vm_compute; reflexivity
    | cbn; lia| cbn; lia| lia| unfold SEGTOP_A; lia| clear - KB KX; lia|].
  intros Σ4 v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 F4 m4 GI4. rewrite (ret_pc_even DMP_PJ_ASTEP_A) by (unfold DMP_PJ_ASTEP_A; lia).
  pose proof GI4 as (_ & MI4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & (FR4 & _) & _).
  pose proof (PINVA_shz RT AF G GOK _ _ _ _ AI0 GI4) as (SHZT & _ & _). pose proof (PINVA_ainv RT AF G GOK _ _ _ _ AI0 GI4) as AI4.
  pose proof (pj_frAL_104 _ _ _ _ _ _ _ _ FR4) as F104. pose proof (pj_frAL_112 _ _ _ _ _ _ _ _ FR4) as F112.
  replace (g_S1 G + 104) with (g_q G - 256 + 104) in F104 by lia. replace (g_S1 G + 112) with (g_q G - 256 + 112) in F112 by lia.
  pose proof (elem_kindA _ _ _ _ _ _ EL) as KIND.

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (pj_astep3 E (g_q G) (g_ff G) osp e it j gp (wz DMP_PJ_ASTEP_A) (wz osp) c1 c2 c3 c4 c5 c6 c7 v0 v1 v2 v3 v4 v5 v6 F4 fc2 m4
                             OK I0 IJ ltac:(clear - JE EN; lia) NR KIND QLO QH OR ltac:(clear - I0 IJ JE EN NR; lia) F0 SFH AI4 SHZT F104 F112 MI4)|].
  cbv beta. intros ms5 (a0x & a1x & a2x & ->). apply evt_done.
  eapply HK; [exact GI4| exact FRM2| clear; lia].
Qed.

Lemma pa_loop : forall (j0 j48 jB : list byte) (sv : list cell) (kx : Z) (K : config -> Prop) (gp : word) (e c it : Z),
  let fcs := pj_frAL j0 (g_ff G) j48 osp jB sv in
  tiles (elem T S sn ck_any d') it e c -> it <> e -> 0 <= it -> e + 1 <= n -> kx <= g_cr G ->
  KLOOPXA fcs kx K gp -> KALOOPA fcs kx K gp e it.
Proof using AF FDO MST PUT GOK AI0 IOS0 GD PJ facts.
  intros j0 j48 jB sv kx K gp e c it. cbv zeta. intros HT. pose proof facts as (OK & QLO & QH & OR & F0 & NR & SNR & FH & SFH & LOS).
  induction HT as [it0|it0 j1 e0 c0 EL HT' IH]; intros NE I0 EN KX HC; [congruence|].
  unfold KALOOPA. intros until fc. intros GI FRM KB.
  pose proof (elem_lt _ _ _ _ _ _ _ EL) as IJ. pose proof (tiles_le _ (elem_lt _ _ _ _ d') _ _ _ HT') as [JE _].
  eapply (pa_step j0 j48 jB sv _ kx); [exact GI| exact FRM| exact EL| exact I0| exact JE| exact EN| unfold pj_costE, DMP_PJ_CW in *; clear - KB IJ JE; lia| exact KX|].
  intros Σ2 m2 k2 ra' b0 b1 b2 b3 b4 b5 b6 b7 u0 u1 u2 u3 u4 u5 u6 F2 fc2 GI2 FRM2 K2. unfold ALSA.
  pose proof GI2 as (_ & MI2 & _).

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (pj_atest E (g_q G) (g_ff G) osp e0 j1 gp ra' b0 b1 b2 b3 b4 b5 b6 b7 u0 u1 u2 u3 u4 u5 u6 F2 fc2 m2 ltac:(clear - I0 IJ JE EN NR; lia) ltac:(clear - I0 IJ JE EN NR; lia) MI2)|].
  cbv beta. intros ms3 ->. apply evt_done.
  destruct (Z.eqb_spec j1 e0) as [JE0|JNE].
  -
    unfold pjRL. eapply HC; [exact GI2| exact FRM2| unfold pj_costE, DMP_PJ_CW in *; clear - KB K2 IJ JE0; lia].
  -
    unfold KALOOPA, ALSA in IH. eapply IH; [exact JNE| clear - I0 IJ; lia| exact EN| exact KX| exact HC| exact GI2| exact FRM2| unfold pj_costE, DMP_PJ_CW in *; clear - KB K2 IJ; lia].
Qed.

Lemma pa_head : forall (jA jB : list byte) (sv : list cell) (k kx : Z) (Σ : rts RT) (K : config -> Prop) (i e cv : Z)
    (ra gp a0 a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  PINVA G (pj_frD jA osp jB (g_ff G) sv) k Σ m -> frm0 fc -> 0 <= i -> i < e -> e + 1 <= n -> 0 <= cv <= CNT_MAX -> T i = cword t_arr (e + 1) cv ->
  k + 2 <= kx -> kx <= g_cr G ->
  KCLOSEA (pj_frD jA osp jB (g_ff G) sv) kx K gp DMP_LIT_RBRK_A ->
  (i + 1 <> e -> forall j0 j48, KALOOPA (pj_frAL j0 (g_ff G) j48 osp jB sv) kx K gp e (i + 1)) ->
  k + 2 + DMP_PJ_CW * (e - (i + 1)) + 2 <= kx ->
  aevt Σ K (MS (pjR (g_q G) (g_ff G) gp ra a0 a1 a2 a3 a4 a5 a6 a7 (wz (ae_DOC E)) (wz i) s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6) F (wz DMP_PJ_DISP_A) fc None m (seg_rom asegs)).
Proof using AF FDO MST PUT GOK AI0 facts.
  intros until m. intros GI FRM I0 IE EN CV TI KB KX HC HL KBL. pose proof facts as (OK & QLO & QH & OR & F0 & NR & SNR & FH & SFH & LOS).
  pose proof GI as (_ & MI & _ & _ & _ & _ & _ & _ & _ & _ & _ & (FR & _) & _). pose proof (pj_frD_osp _ _ _ _ _ _ _ FR) as FO.
  replace (g_S1 G + 120) with (g_q G - 256 + 120) in FO by lia.
  pose proof (PINVA_shz RT AF G GOK _ _ _ _ AI0 GI) as (SHZT & _ & _). pose proof (PINVA_ainv RT AF G GOK _ _ _ _ AI0 GI) as AI.
  unfold CNT_MAX in CV.
  assert (TIR : 0 <= T i < 2^64) by (rewrite TI; apply cword_range; unfold t_arr, CNT_MAX; lia).
  assert (TY : ttype (T i) = 91) by (rewrite TI, ttype_cword by (unfold CNT_MAX; lia); reflexivity).

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (pj_open1 E 91 (g_q G) (g_ff G) osp i gp ra a0 a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 F fc m OK ltac:(clear - I0 IE EN; lia) TIR TY ltac:(left; reflexivity) QLO QH OR AI SHZT FO MI)|].
  cbv beta. intros ms1 (a3x & ->). apply evt_done. unfold pjR, pj_open_ret, pj_open_lit. cbn [Z.eqb Pos.eqb]. unfold DMP_LIT_LBRK_A.
  eapply (p_put_lit RT AF PMc FDO MST G GOK _ k Σ K 0x234c0 1 2 1%nat); [exact PUT| exact GI| acc_in| vm_compute; reflexivity| vm_compute; reflexivity
    | cbn; lia| cbn; lia| lia| unfold SEGTOP_A; lia| clear - KB KX; lia|].
  intros Σ2 u0 u1 u2 e1 e2 e3 e4 e5 e6 e7 u3 u4 u5 u6 F2 m2 GI2. rewrite (ret_pc_even 0xaf3ac) by lia. change 0xaf3ac with DMP_PJ_AHEAD_A.
  pose proof GI2 as (_ & MI2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & (FR2 & _) & _).
  pose proof (PINVA_shz RT AF G GOK _ _ _ _ AI0 GI2) as (SHZT2 & _ & _). pose proof (PINVA_ainv RT AF G GOK _ _ _ _ AI0 GI2) as AI2.

  pose proof FR2 as FRX. unfold pj_frD in FRX.
  apply (rw_cells_split_CB asegs _ _ [] 120 _ ([C8 (wz osp); CB 16 jB; C8 (wz (g_ff G))] ++ sv) [24; 8; 8; 8; 56; 8; 8]%nat) in FRX; [| reflexivity]. cbn [mk_CB_cells app] in FRX.
  repeat match type of FRX with context [CB ?kk ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FRX; clearbody j end.
  lazymatch type of FRX with rw_cells _ _ _ (CB 24 ?x0 :: CB 8 ?x24 :: CB 8 ?x32 :: CB 8 ?x40 :: CB 56 ?x48 :: CB 8 ?x104 :: CB 8 ?x112 :: ?rest) =>
    assert (F24 : rw_cells asegs m2 (g_q G - 256 + 24) [CB 8 x24; CB 8 x32; CB 8 x40])
      by (replace (g_q G - 256 + 24) with (g_S1 G + Z.of_nat (cells_size [CB 24 x0])) by (cbn; lia);
          apply (rw_cells_mid m2 (g_S1 G) [CB 24 x0] _ (CB 56 x48 :: CB 8 x104 :: CB 8 x112 :: rest)); exact FRX);
    assert (F104 : rw_cells asegs m2 (g_q G - 256 + 104) [CB 8 x104; CB 8 x112; C8 (wz osp)])
      by (replace (g_q G - 256 + 104) with (g_S1 G + Z.of_nat (cells_size [CB 24 x0; CB 8 x24; CB 8 x32; CB 8 x40; CB 56 x48])) by (cbn; lia);
          apply (rw_cells_mid m2 (g_S1 G) [CB 24 x0; CB 8 x24; CB 8 x32; CB 8 x40; CB 56 x48] _ ([CB 16 jB; C8 (wz (g_ff G))] ++ sv)); exact FRX)
  end.
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (pj_ahead2 E (g_q G) (g_ff G) osp i e cv gp (wz DMP_PJ_AHEAD_A) (wz osp) e1 e2 e3 e4 e5 e6 e7 s8 s9 s11 u0 u1 u2 u3 u4 u5 u6 _ _ _ _ _ F2 fc m2
                             OK I0 IE EN NR ltac:(unfold CNT_MAX; exact CV) TI QLO QH OR F0 FH SFH AI2 SHZT2 F24 F104 MI2)|].
  cbv beta. intros ms3 POST. apply evt_done.
  destruct POST as [(EQ & a0x & a2x & a3y & ->)|(NE & m3 & a0x & a1x & a2x & a3y & -> & MU3 & WM3 & MI3 & F24' & F104')].
  -
    eapply HC; [exact GI2| exact FRM| clear - KBL EQ; unfold DMP_PJ_CW in KBL; lia].
  -
    assert (OWN3 : forall a, outside [(g_q G - 256 + 24, g_q G - 256 + 48); (g_q G - 256 + 104, g_q G - 256 + 120)] a \/ own G a).
    { intros a. match goal with |- outside ?W _ \/ _ => destruct (outside_dec W a) as [O|IN]; [left; exact O| right] end. unfold own. cbn [inW] in IN. clear - IN. lia. }
    lazymatch type of FRX with rw_cells _ _ _ (CB 24 ?x0 :: _ :: _ :: _ :: CB 56 ?x48 :: _) =>
    assert (GI3 : PINVA G (pj_frAL x0 (g_ff G) x48 osp jB sv) (k + 2) Σ2 m3);
    [ eapply (PINVA_cw RT AF G GOK _ _ (k + 2) Σ2 m2 m3 _ GI2 MU3 WM3 MI3 OWN3); [| unfold pj_frAL; rewrite cells_size_app, pj_frAL_size; pose proof GI2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & SZ2) & _); unfold pj_frD in SZ2; rewrite cells_size_app in SZ2; cbn [cells_size csize Nat.add] in SZ2 |- *; lia]
    | unfold KALOOPA, ALSA in HL; eapply (HL NE x0 x48); [exact GI3| exact FRM| clear - KBL; lia] ]
    end.

    unfold pj_frAL.
    lazymatch type of FRX with rw_cells _ _ _ (CB 24 ?x0 :: CB 8 ?x24 :: CB 8 ?x32 :: CB 8 ?x40 :: CB 56 ?x48 :: CB 8 ?x104 :: CB 8 ?x112 :: ?rest) =>
      change (rw_cells asegs m3 (g_S1 G) ([CB 24 x0] ++ ([C8 (wz DMP_LIT_RBRK_A); C8 (wz (g_ff G)); C8 (wz (g_ff G))] ++ [CB 56 x48] ++ [C8 (wz 4294967295); C8 (wz 4294967297)]) ++ rest));
      apply (rw_cells_reasm m2 m3 (g_S1 G) [CB 24 x0] ([CB 8 x24; CB 8 x32; CB 8 x40] ++ [CB 56 x48] ++ [CB 8 x104; CB 8 x112]))
    end.
    + cbn [app]. exact FRX.
    + apply (agree_of_munch _ _ _ _ MU3). intros x Hx. rewrite !cells_size_app in Hx. cbn [cells_size csize Nat.add] in Hx.
      pose proof GI2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & SZ2) & _). unfold pj_frD in SZ2. rewrite cells_size_app in SZ2. cbn [cells_size csize Nat.add] in SZ2.
      cbn [outside]. clear - Hx SZ2. lia.
    + apply rw_cells_app. split; [cbn [cells_size csize Nat.add]; replace (g_S1 G + Z.of_nat 24) with (g_q G - 256 + 24) by lia; exact F24'|].
      apply rw_cells_app. split.
      * lazymatch type of FRX with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: CB 56 ?x48 :: ?rest) =>
          pose proof (rw_cells_mid m2 (g_S1 G) [c0; c1; c2; c3] [CB 56 x48] rest FRX) as F48 end.
        cbn [cells_size csize Nat.add] in F48 |- *. replace (g_S1 G + Z.of_nat 24 + Z.of_nat 24) with (g_S1 G + Z.of_nat 48) by lia.
        eapply rw_cells_agree_nw; [exact F48|]. apply (agree_of_munch _ _ _ _ MU3). intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbn [outside]. clear - Hx. lia.
      * cbn [cells_size csize Nat.add]. replace (g_S1 G + Z.of_nat 24 + Z.of_nat 24 + Z.of_nat 56) with (g_q G - 256 + 104) by lia.
        change [C8 (wz 4294967295); C8 (wz 4294967297); C8 (wz osp)] with ([C8 (wz 4294967295); C8 (wz 4294967297)] ++ [C8 (wz osp)]) in F104'.
        apply rw_cells_app in F104'. destruct F104' as [F104a _]. exact F104a.
    + reflexivity.
Qed.

Lemma pj_arr_caseA : forall (jA jB : list byte) (sv : list cell) (kx : Z) (Σ : rts RT) (K : config -> Prop) (i e c cv : Z)
    (ra gp a0 a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  PINVA G (pj_frD jA osp jB (g_ff G) sv) 1 Σ m -> frm0 fc -> 0 <= i -> i < e -> e + 1 <= n -> 0 <= cv <= CNT_MAX ->
  T i = cword t_arr (e + 1) cv -> tiles (elem T S sn ck_any d') (i + 1) e c ->
  pj_costE i (e + 1) <= kx -> kx <= g_cr G ->
  (forall LC, cells_size LC = 152%nat -> KEXITA G (LC ++ sv) kx K gp) ->
  aevt Σ K (MS (pjR (g_q G) (g_ff G) gp ra a0 a1 a2 a3 a4 a5 a6 a7 (wz (ae_DOC E)) (wz i) s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6) F (wz DMP_PJ_DISP_A) fc None m (seg_rom asegs)).
Proof using AF FDO MST PUT GOK AI0 IOS0 GD PJ facts.
  intros until m. intros GI FRM I0 IE EN CV TI HT KB KX HKX.
  assert (KXD : KEXITA G (pj_frD jA osp jB (g_ff G) sv) kx K gp) by (unfold pj_frD; apply HKX; reflexivity).
  eapply (pa_head jA jB sv 1 kx Σ K i e cv); [exact GI| exact FRM| exact I0| exact IE| exact EN| exact CV| exact TI| unfold pj_costE, DMP_PJ_CW in KB; clear - KB IE; lia| exact KX
    | | | unfold pj_costE, DMP_PJ_CW in *; clear - KB IE; lia].
  - apply pa_close; [left; reflexivity| intros mx H; unfold pj_frD in H; pose proof (pj_frD_osp mx (g_S1 G) jA osp jB (g_ff G) sv H) as X; exact X| exact KX| exact KXD].
  - intros NE j0 j48. eapply (pa_loop j0 j48 jB sv kx K gp e c (i + 1)); [exact HT| exact NE| clear - I0; lia| exact EN| exact KX|].
    apply (pa_xclose _ kx K gp DMP_LIT_RBRK_A); [left; reflexivity| intros mx H; exact (pj_frAL_24 _ _ _ _ _ _ _ _ H)| intros mx H; exact (pj_frAL_120 _ _ _ _ _ _ _ _ H)| exact KX|].
    unfold pj_frAL. apply HKX. apply pj_frAL_size.
Qed.

Definition OLSA (kk : Z) (gp ra a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s7 s8 s9 t0 t1 t2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state :=
  MS (pjRO E (g_q G) (g_ff G) gp ra a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s7 s8 s9 (wz kk) t0 t1 t2 t3 t4 t5 t6) F (wz DMP_PJ_OLOOP_A) fc None m (seg_rom asegs).
Definition KOLOOPA (fcs : list cell) (kx : Z) (K : config -> Prop) (gp : word) (e kk : Z) : Prop :=
  forall (Σ : rts RT) (m : mem) (k : Z) (ra a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s7 s8 s9 t0 t1 t2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    PINVA G fcs k Σ m -> frm0 fc -> k + DMP_PJ_CW * (e - kk) + 2 <= kx ->
    aevt Σ K (OLSA kk gp ra a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s7 s8 s9 t0 t1 t2 t3 t4 t5 t6 F fc m).

Lemma po_step : forall (j0 jB : list byte) (sv : list cell) (k kx : Z) (Σ : rts RT) (K : config -> Prop) (e kk b : Z)
    (gp ra a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s7 s8 s9 t0 t1 t2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  let fcs := pj_frOL j0 E (g_ff G) e osp jB sv in
  PINVA G fcs k Σ m -> frm0 fc -> is_str T S sn kk -> elem T S sn ck_any d' (kk + 1) b -> 0 <= kk -> b <= e -> e + 1 <= n ->
  k + 6 + pj_costE (kk + 1) b <= kx -> kx <= g_cr G ->
  (b <> e -> KOLOOPA fcs kx K gp e b) -> KLOOPXA fcs kx K gp ->
  k + 6 + pj_costE (kk + 1) b + DMP_PJ_CW * (e - b) + 2 <= kx ->
  aevt Σ K (OLSA kk gp ra a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s7 s8 s9 t0 t1 t2 t3 t4 t5 t6 F fc m).
Proof using AF FDO MST PUT GOK AI0 IOS0 GD PJ facts.
  intros until m. cbv zeta. intros GI FRM STR EL K0 BE EN KB KX HL HC KBL. pose proof facts as (OK & QLO & QH & OR & F0 & NR & SNR & FH & SFH & LOS).
  pose proof (elem_lt _ _ _ _ _ _ _ EL) as IJ.
  assert (CE : 0 <= pj_costE (kk + 1) b) by (unfold pj_costE, DMP_PJ_CW; clear - IJ; lia).
  assert (ER : 0 <= e < 2^63) by (clear - K0 IJ BE EN NR; lia). assert (ER' : 0 <= e < 2^64) by (clear - ER; lia).
  destruct (is_str_read _ _ _ (proj2 SNR) _ STR) as [KT (l & SA)].
  assert (TIR : 0 <= T kk < 2^64).
  { destruct STR as (o0 & l0 & X & SA0). rewrite X. apply tword_range; [unfold t_str; lia| pose proof (str_at_bounds _ _ (proj2 SNR) _ _ SA0); lia]. }
  pose proof GI as (_ & MI & _ & _ & _ & _ & _ & _ & _ & _ & _ & (FR & _) & _). pose proof (pj_frOL_24 _ _ _ _ _ _ _ _ _ FR) as FO.
  replace (g_S1 G + 24) with (g_q G - 256 + 24) in FO by lia.
  pose proof (PINVA_shz RT AF G GOK _ _ _ _ AI0 GI) as (SHZT & SHZS & _). pose proof (PINVA_ainv RT AF G GOK _ _ _ _ AI0 GI) as AI. unfold OLSA.

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (pj_okey1 E (g_q G) (g_ff G) osp e kk (tval (T kk)) l gp ra a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s7 s8 s9 t0 t1 t2 t3 t4 t5 t6 F fc m
                             OK ltac:(clear - K0 IJ BE EN; lia) TIR eq_refl SA QLO QH OR F0 SFH ER' AI SHZT SHZS FO MI)|].
  cbv beta. intros ms1 (a3x & ->). apply evt_done. unfold pjRO, DMP_LIT_QUOT_A.
  eapply (p_put_lit RT AF PMc FDO MST G GOK _ k Σ K 0x23540 1 2 1%nat); [exact PUT| exact GI| acc_in| vm_compute; reflexivity| vm_compute; reflexivity
    | cbn; lia| cbn; lia| lia| unfold SEGTOP_A; lia| clear - KB KX CE; lia|].
  intros Σ2 u0 u1 u2 e1 e2 e3 e4 e5 e6 e7 u3 u4 u5 u6 F2 m2 GI2. rewrite (ret_pc_even 0xaf91c) by lia. pose proof GI2 as (_ & MI2 & _).

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (pj_okey2 E (g_q G) (g_ff G) osp (tval (T kk)) l kk gp (wz 0xaf91c) e1 e2 e3 e4 e5 e6 e7 u0 u1 u2 u3 u4 u5 u6 F2 fc m2 OK SA OR MI2)|].
  cbv beta. intros ms3 (s5x & s7x & s8x & ->). apply evt_done. unfold pjRO.
  eapply (p_put_live RT AF PMc FDO MST G GOK _ (k + 2) Σ2 K (tval (T kk)) l); [exact PUT| exact GI2| exact AI0| exact SA| clear - KB KX CE; lia|].
  intros Σ4 v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 F4 m4 GI4. rewrite (ret_pc_even 0xaf93c) by lia.
  pose proof GI4 as (_ & MI4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & (FR4 & _) & _). pose proof (pj_frOL_24 _ _ _ _ _ _ _ _ _ FR4) as FO4.
  replace (g_S1 G + 24) with (g_q G - 256 + 24) in FO4 by lia.

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (pj_okey3 E (g_q G) (g_ff G) osp e gp (wz 0xaf93c) c1 c2 c3 c4 c5 c6 c7 (wz (S (tval (T kk)))) s5x s7x s8x (wz (ae_SBUF E + tval (T kk))) (wz kk) v0 v1 v2 v3 v4 v5 v6 F4 fc m4 QLO QH FO4 MI4)|].
  cbv beta. intros ms5 ->. apply evt_done. unfold pjRO, DMP_LIT_QCOL_A.
  eapply (p_put_lit RT AF PMc FDO MST G GOK _ (k + 2 + 2) Σ4 K 0x23560 3 4 3%nat); [exact PUT| exact GI4| acc_in| vm_compute; reflexivity| vm_compute; reflexivity
    | cbn; lia| cbn; lia| lia| unfold SEGTOP_A; lia| clear - KB KX CE; lia|].
  intros Σ6 w0 w1 w2 g1 g2 g3 g4 g5 g6 g7 w3 w4 w5 w6 F6 m6 GI6. rewrite (ret_pc_even 0xaf948) by lia.
  pose proof GI6 as (_ & MI6 & _ & _ & _ & _ & _ & _ & _ & _ & _ & (FR6 & _) & _). pose proof (pj_frOL_24 _ _ _ _ _ _ _ _ _ FR6) as FO6.
  replace (g_S1 G + 24) with (g_q G - 256 + 24) in FO6 by lia.

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (pj_ochild E (g_q G) (g_ff G) osp e kk gp (wz 0xaf948) (wz osp) g1 g2 g3 g4 g5 g6 g7 (wz (S (tval (T kk)))) s5x s7x s8x (wz (ae_SBUF E + tval (T kk))) w0 w1 w2 w3 w4 w5 w6 F6 fc m6
                             QLO QH K0 ltac:(clear - K0 IJ BE EN NR; lia) FO6 MI6)|].
  cbv beta. intros ms7 ->. apply evt_done. unfold pjRO.
  eapply (p_child RT AF PMc FDO MST G GOK d' _ (k + 2 + 2 + 2) Σ6 K (kk + 1) b); [exact PJ| exact GI6| exact AI0| exact IOS0| exact FRM| exact EL| clear - K0; lia| clear - BE EN; lia| exact GD| clear - KB KX; lia|].
  intros Σ8 x0 x1 x2 h0 h1 h2 h3 h4 h5 h6 h7 x3 x4 x5 x6 F8 fc8 m8 GI8 FRM8. rewrite (ret_pc_even 0xaf95c) by lia.
  pose proof GI8 as (_ & MI8 & _ & _ & _ & _ & _ & _ & _ & _ & _ & (FR8 & _) & _). pose proof (pj_frOL_24 _ _ _ _ _ _ _ _ _ FR8) as FO8.
  replace (g_S1 G + 24) with (g_q G - 256 + 24) in FO8 by lia.
  pose proof (PINVA_shz RT AF G GOK _ _ _ _ AI0 GI8) as (SHZT8 & _ & _). pose proof (PINVA_ainv RT AF G GOK _ _ _ _ AI0 GI8) as AI8.
  pose proof (elem_kindA _ _ _ _ _ _ EL) as KIND.

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (pj_ostep E (g_q G) (g_ff G) osp e kk (kk + 1) b gp (wz 0xaf95c) h0 h1 h2 h3 h4 h5 h6 h7 (wz (S (tval (T kk)))) s5x s7x s8x x0 x1 x2 x3 x4 x5 x6 F8 fc8 m8
                             OK eq_refl K0 IJ ltac:(clear - BE EN; lia) NR KIND QLO QH OR ER' F0 SFH AI8 SHZT8 FO8 MI8)|].
  cbv beta. intros ms9 (a0x & a1x & a2x & ->). apply evt_done.

  apply (aevt_evt RT AF PMc MST). change 0xaf9cc with DMP_PJ_OTEST_A.
  eapply evt_cut; [eapply (pj_otest E (g_q G) (g_ff G) osp e b gp (wz 0xaf95c) a0x a1x a2x h3 h4 h5 h6 h7 (wz (S (tval (T kk)))) s5x s7x s8x (wz (8 * (kk + 1))) x0 x1 x2 x3 x4 x5 x6 F8 fc8 m8
                             QLO QH ltac:(clear - K0 IJ BE EN NR; lia) ER FO8 MI8)|].
  cbv beta. intros ms10 ->. apply evt_done.
  destruct (Z.eqb_spec b e) as [BE0|BNE].
  - unfold pjRO. eapply HC; [exact GI8| exact FRM8| clear - KBL BE0 CE; lia].
  - unfold KOLOOPA, OLSA in HL. eapply (HL BNE); [exact GI8| exact FRM8| clear - KBL; lia].
Qed.

Lemma po_loop : forall (j0 jB : list byte) (sv : list cell) (kx : Z) (K : config -> Prop) (gp : word) (e c kk : Z),
  let fcs := pj_frOL j0 E (g_ff G) e osp jB sv in
  tiles (field T S sn (elem T S sn ck_any d')) kk e c -> kk <> e -> 0 <= kk -> e + 1 <= n -> kx <= g_cr G ->
  KLOOPXA fcs kx K gp -> KOLOOPA fcs kx K gp e kk.
Proof using AF FDO MST PUT GOK AI0 IOS0 GD PJ facts.
  intros j0 jB sv kx K gp e c kk. cbv zeta. intros HT. pose proof facts as (OK & QLO & QH & OR & F0 & NR & SNR & FH & SFH & LOS).
  induction HT as [k0|k0 b0 e0 c0 FL HT' IH]; intros NE K0 EN KX HC; [congruence|].
  unfold KOLOOPA. intros until fc. intros GI FRM KB.
  destruct FL as [STR EL]. pose proof (elem_lt _ _ _ _ _ _ _ EL) as IJ.
  pose proof (tiles_le _ (field_lt _ _ _ _ (elem_lt _ _ _ _ d')) _ _ _ HT') as [BE _].
  eapply (po_step j0 jB sv _ kx); [exact GI| exact FRM| exact STR| exact EL| exact K0| exact BE| exact EN| unfold pj_costE, DMP_PJ_CW in *; clear - KB IJ BE; lia| exact KX| | exact HC
    | unfold pj_costE, DMP_PJ_CW in *; clear - KB IJ BE; lia].
  intros BNE. unfold KOLOOPA, OLSA in IH |- *. intros. eapply IH; [exact BNE| clear - K0 IJ; lia| exact EN| exact KX| exact HC| eassumption| eassumption| eassumption].
Qed.

Lemma po_head : forall (jA jB : list byte) (sv : list cell) (k kx : Z) (Σ : rts RT) (K : config -> Prop) (i e cv : Z)
    (ra gp a0 a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  PINVA G (pj_frD jA osp jB (g_ff G) sv) k Σ m -> frm0 fc -> 0 <= i -> i < e -> e + 1 <= n -> 0 <= cv <= CNT_MAX -> T i = cword t_obj (e + 1) cv ->
  k + 2 <= kx -> kx <= g_cr G ->
  (forall j0 j24 j48 j56 j64 j72 j80 j88 j96 j104, KCLOSEA (pj_frOE j0 j24 (g_ff G) j48 j56 j64 j72 j80 j88 j96 j104 e osp jB sv) kx K gp DMP_LIT_RBRC_A) ->
  (i + 1 <> e -> forall j0, KOLOOPA (pj_frOL j0 E (g_ff G) e osp jB sv) kx K gp e (i + 1)) ->
  k + 2 + DMP_PJ_CW * (e - (i + 1)) + 2 <= kx ->
  aevt Σ K (MS (pjR (g_q G) (g_ff G) gp ra a0 a1 a2 a3 a4 a5 a6 a7 (wz (ae_DOC E)) (wz i) s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6) F (wz DMP_PJ_DISP_A) fc None m (seg_rom asegs)).
Proof using AF FDO MST PUT GOK AI0 facts.
  intros until m. intros GI FRM I0 IE EN CV TI KB KX HC HL KBL. pose proof facts as (OK & QLO & QH & OR & F0 & NR & SNR & FH & SFH & LOS).
  pose proof GI as (_ & MI & _ & _ & _ & _ & _ & _ & _ & _ & _ & (FR & _) & _). pose proof (pj_frD_osp _ _ _ _ _ _ _ FR) as FO.
  replace (g_S1 G + 120) with (g_q G - 256 + 120) in FO by lia.
  pose proof (PINVA_shz RT AF G GOK _ _ _ _ AI0 GI) as (SHZT & _ & _). pose proof (PINVA_ainv RT AF G GOK _ _ _ _ AI0 GI) as AI.
  unfold CNT_MAX in CV.
  assert (TIR : 0 <= T i < 2^64) by (rewrite TI; apply cword_range; unfold t_obj, CNT_MAX; lia).
  assert (TY : ttype (T i) = 123) by (rewrite TI, ttype_cword by (unfold CNT_MAX; lia); reflexivity).

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (pj_open1 E 123 (g_q G) (g_ff G) osp i gp ra a0 a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 F fc m OK ltac:(clear - I0 IE EN; lia) TIR TY ltac:(right; reflexivity) QLO QH OR AI SHZT FO MI)|].
  cbv beta. intros ms1 (a3x & ->). apply evt_done. unfold pjR, pj_open_ret, pj_open_lit. cbn [Z.eqb Pos.eqb]. unfold DMP_LIT_LBRC_A.
  eapply (p_put_lit RT AF PMc FDO MST G GOK _ k Σ K 0x23520 1 2 1%nat); [exact PUT| exact GI| acc_in| vm_compute; reflexivity| vm_compute; reflexivity
    | cbn; lia| cbn; lia| lia| unfold SEGTOP_A; lia| clear - KB KX; lia|].
  intros Σ2 u0 u1 u2 e1 e2 e3 e4 e5 e6 e7 u3 u4 u5 u6 F2 m2 GI2. rewrite (ret_pc_even 0xaf124) by lia. change 0xaf124 with DMP_PJ_OHEAD_A.
  pose proof GI2 as (_ & MI2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & (FR2 & SZ2) & _). pose proof (PINVA_ainv RT AF G GOK _ _ _ _ AI0 GI2) as AI2.

  pose proof FR2 as FRX. unfold pj_frD in FRX.
  apply (rw_cells_split_CB asegs _ _ [] 120 _ ([C8 (wz osp); CB 16 jB; C8 (wz (g_ff G))] ++ sv) [24; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FRX; [| reflexivity]. cbn [mk_CB_cells app] in FRX.
  repeat match type of FRX with context [CB ?kk ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FRX; clearbody j end.
  lazymatch type of FRX with rw_cells _ _ _ (CB 24 ?x0 :: ?c24 :: ?c32 :: ?c40 :: ?c48 :: ?c56 :: ?c64 :: ?c72 :: ?c80 :: ?c88 :: ?c96 :: ?c104 :: ?c112 :: ?rest) =>
    assert (F24 : rw_cells asegs m2 (g_q G - 256 + 24) [c24; c32; c40; c48; c56; c64; c72; c80; c88; c96; c104; c112; C8 (wz osp)])
      by (replace (g_q G - 256 + 24) with (g_S1 G + Z.of_nat (cells_size [CB 24 x0])) by (cbn; lia);
          apply (rw_cells_mid m2 (g_S1 G) [CB 24 x0] _ ([CB 16 jB; C8 (wz (g_ff G))] ++ sv)); exact FRX)
  end.

  assert (SHZM : forall m', munch [(g_q G - 256 + 24, g_q G - 256 + 120)] m2 m' -> wmono asegs m2 m' -> shz m' (ae_TAPE E) (8 * ae_n E)).
  { intros m' MU WM. eapply (PINVA_wfacts RT AF G GOK _ _ _ _ AI0 GI2 _ m' MU WM).
    intros a. match goal with |- outside ?W _ \/ _ => destruct (outside_dec W a) as [O|IN]; [left; exact O| right] end. unfold own. cbn [inW] in IN. clear - IN. lia. }
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (pj_ohead2 E (g_q G) (g_ff G) osp i e cv gp (wz DMP_PJ_OHEAD_A) (wz osp) e1 e2 e3 e4 e5 e6 e7 s8 s9 s11 u0 u1 u2 u3 u4 u5 u6 _ _ _ _ _ _ _ _ _ _ _ _ F2 fc m2
                             OK I0 IE EN NR ltac:(unfold CNT_MAX; exact CV) TI QLO LOS QH OR F0 FH SFH AI2 SHZM F24 MI2)|].
  cbv beta. intros ms3 (m3 & a0x & a1x & a2x & a3y & a4x & a5x & a6x & MU3 & WM3 & MI3 & POST). apply evt_done.
  assert (OWN3 : forall a, outside [(g_q G - 256 + 24, g_q G - 256 + 120)] a \/ own G a).
  { intros a. match goal with |- outside ?W _ \/ _ => destruct (outside_dec W a) as [O|IN]; [left; exact O| right] end. unfold own. cbn [inW] in IN. clear - IN. lia. }
  unfold pj_frD in SZ2. rewrite cells_size_app in SZ2. cbn [cells_size csize Nat.add] in SZ2.
  destruct POST as [(EQ & -> & F24')|(NE & -> & F24')].
  -
    lazymatch type of FRX with rw_cells _ _ _ (CB 24 ?x0 :: CB 8 ?x24 :: ?c32 :: ?c40 :: CB 8 ?x48 :: CB 8 ?x56 :: CB 8 ?x64 :: CB 8 ?x72 :: CB 8 ?x80 :: CB 8 ?x88 :: CB 8 ?x96 :: CB 8 ?x104 :: ?c112 :: ?cosp :: ?rest) =>
    assert (GI3 : PINVA G (pj_frOE x0 x24 (g_ff G) x48 x56 x64 x72 x80 x88 x96 x104 e osp jB sv) (k + 2) Σ2 m3);
    [ eapply (PINVA_cw RT AF G GOK _ _ (k + 2) Σ2 m2 m3 _ GI2 MU3 WM3 MI3 OWN3); [| unfold pj_frOE; rewrite cells_size_app; cbn [cells_size csize Nat.add] in *; lia];
      unfold pj_frOE;
      change (rw_cells asegs m3 (g_S1 G) ([CB 24 x0] ++ [CB 8 x24; C8 (wz (g_ff G)); C8 (wz (g_ff G)); CB 8 x48; CB 8 x56; CB 8 x64; CB 8 x72; CB 8 x80; CB 8 x88; CB 8 x96; CB 8 x104; C8 (wz e); C8 (wz osp)] ++ rest));
      apply (rw_cells_reasm m2 m3 (g_S1 G) [CB 24 x0] [CB 8 x24; c32; c40; CB 8 x48; CB 8 x56; CB 8 x64; CB 8 x72; CB 8 x80; CB 8 x88; CB 8 x96; CB 8 x104; c112; cosp] _ rest ltac:(cbn [app]; exact FRX));
      [ apply (agree_of_munch _ _ _ _ MU3); intros x Hx; rewrite !cells_size_app in Hx; cbn [cells_size csize Nat.add] in Hx; cbn [outside]; clear - Hx SZ2; lia
      | cbn [cells_size csize Nat.add]; replace (g_S1 G + Z.of_nat 24) with (g_q G - 256 + 24) by lia; exact F24'
      | reflexivity ]
    | eapply HC; [exact GI3| exact FRM| clear - KBL EQ; unfold DMP_PJ_CW in KBL; lia] ]
    end.
  -
    lazymatch type of FRX with rw_cells _ _ _ (CB 24 ?x0 :: ?c24 :: ?c32 :: ?c40 :: ?c48 :: ?c56 :: ?c64 :: ?c72 :: ?c80 :: ?c88 :: ?c96 :: ?c104 :: ?c112 :: ?cosp :: ?rest) =>
    assert (GI3 : PINVA G (pj_frOL x0 E (g_ff G) e osp jB sv) (k + 2) Σ2 m3);
    [ eapply (PINVA_cw RT AF G GOK _ _ (k + 2) Σ2 m2 m3 _ GI2 MU3 WM3 MI3 OWN3); [| unfold pj_frOL; rewrite cells_size_app, pj_frOL_size; lia];
      unfold pj_frOL; rewrite <- !app_assoc; cbn [app];
      change (rw_cells asegs m3 (g_S1 G) ([CB 24 x0] ++ pj_oframe E (g_ff G) e osp ++ rest));
      apply (rw_cells_reasm m2 m3 (g_S1 G) [CB 24 x0] [c24; c32; c40; c48; c56; c64; c72; c80; c88; c96; c104; c112; cosp] _ rest ltac:(cbn [app]; exact FRX));
      [ apply (agree_of_munch _ _ _ _ MU3); intros x Hx; rewrite !cells_size_app in Hx; cbn [cells_size csize Nat.add] in Hx; cbn [outside]; clear - Hx SZ2; lia
      | cbn [cells_size csize Nat.add]; replace (g_S1 G + Z.of_nat 24) with (g_q G - 256 + 24) by lia; exact F24'
      | reflexivity ]
    | unfold KOLOOPA, OLSA, pjRO in HL; eapply (HL NE x0); [exact GI3| exact FRM| clear - KBL; lia] ]
    end.
Qed.

Lemma pj_obj_caseA : forall (jA jB : list byte) (sv : list cell) (kx : Z) (Σ : rts RT) (K : config -> Prop) (i e c cv : Z)
    (ra gp a0 a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  PINVA G (pj_frD jA osp jB (g_ff G) sv) 1 Σ m -> frm0 fc -> 0 <= i -> i < e -> e + 1 <= n -> 0 <= cv <= CNT_MAX ->
  T i = cword t_obj (e + 1) cv -> tiles (field T S sn (elem T S sn ck_any d')) (i + 1) e c ->
  pj_costE i (e + 1) <= kx -> kx <= g_cr G ->
  (forall LC, cells_size LC = 152%nat -> KEXITA G (LC ++ sv) kx K gp) ->
  aevt Σ K (MS (pjR (g_q G) (g_ff G) gp ra a0 a1 a2 a3 a4 a5 a6 a7 (wz (ae_DOC E)) (wz i) s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6) F (wz DMP_PJ_DISP_A) fc None m (seg_rom asegs)).
Proof using AF FDO MST PUT GOK AI0 IOS0 GD PJ facts.
  intros until m. intros GI FRM I0 IE EN CV TI HT KB KX HKX.
  eapply (po_head jA jB sv 1 kx Σ K i e cv); [exact GI| exact FRM| exact I0| exact IE| exact EN| exact CV| exact TI| unfold pj_costE, DMP_PJ_CW in KB; clear - KB IE; lia| exact KX
    | | | unfold pj_costE, DMP_PJ_CW in *; clear - KB IE; lia].
  - intros. apply pa_close; [right; reflexivity| intros mx H; exact (pj_frOE_120 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H)| exact KX|].
    unfold pj_frOE. apply HKX. reflexivity.
  - intros NE j0. eapply (po_loop j0 jB sv kx K gp e c (i + 1)); [exact HT| exact NE| clear - I0; lia| exact EN| exact KX|].
    apply (pa_xclose _ kx K gp DMP_LIT_RBRC_A); [right; reflexivity| intros mx H; exact (pj_frOL_c1 _ _ _ _ _ _ _ _ _ H)| intros mx H; exact (pj_frOL_120 _ _ _ _ _ _ _ _ _ H)| exact KX|].
    unfold pj_frOL. apply HKX. apply pj_frOL_size.
Qed.
End Loops.
