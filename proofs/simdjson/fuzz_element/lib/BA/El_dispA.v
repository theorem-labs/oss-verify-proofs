(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun Stdio SjModel AtpModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList SjTapeTile.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_stage1_kit Atp_h_defs.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2 RT_iface3 RT_iface5. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx D_rlkit D_libiface D_auxv I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_hkit2 Sj_new Sj_h_dtor Sj_h_deldtor. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_num_akit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_h_alloc Sj_stage2_iface Sj_tables. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_fzwA Atp_setcapA Atp_activewA Atp_defsA Atp_kitA Atp_h_defsA Atp_h_vkitA Atp_hkit6A Atp_pidwA Atp_pidiA Atp_pdtorA RT_rtf Pj_rtkA Pj_lftoi1A Pj_defsA Pj_os_defsA Pj_cpsA El_defsA El_lf1A El_lf2A El_lf2bA El_phasesA El_frontA El_costA El_parsekA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition EJT_TAB : list Z :=
  [582976; 582724; 582724; 582724; 582724; 582724; 582724; 582724; 582724; 582724; 582724; 582724;
   582724; 582724; 583168; 583132; 583228; 583240; 583144; 582724; 583184; 583204; 583592; 583264].
Definition ejt (i : Z) : Z := nth (Z.to_nat i) EJT_TAB 0.
Definition EJT_WORDS : list word := map (Z_to_bv 64) EJT_TAB.

Lemma ejt_image : ro_bytes_b asegs EL_JTAB_A (u32s EJT_WORDS) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ejt_at : forall m, mem_inv asegs m -> bytes_at asegs m EL_JTAB_A (u32s EJT_WORDS).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI| unfold EL_JTAB_A; lia | rewrite u32s_length; unfold EL_JTAB_A, EJT_WORDS; rewrite length_map; cbn; lia |].
  apply ro_bytes_b_sound. exact ejt_image.
Qed.
Lemma ejt_read : forall (m : word -> option byte) i a, mem_inv asegs m -> 0 <= i < 24 -> a = wa (EL_JTAB_A + 4 * i) ->
  ov_read_bytes asegs m a 4 = Some (le4 (Z_to_bv 64 (ejt i))).
Proof.
  intros m i a MI Hi ->. eapply (u32ro_read m EL_JTAB_A EJT_WORDS i); [apply ejt_at; exact MI| | lia | reflexivity].
  unfold EJT_WORDS, ejt. rewrite nth_error_map. rewrite (nth_error_nth' EJT_TAB 0); [reflexivity|].
  change (length EJT_TAB) with 24%nat. lia.
Qed.
Lemma ejt_range : forall i, 0 <= i < 24 -> 0 <= ejt i < 2 ^ 31.
Proof.
  intros i Hi. unfold ejt.
  assert (F : forallb (fun x => (0 <=? x) && (x <? 2 ^ 31)) EJT_TAB = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in F. assert (L : (Z.to_nat i < length EJT_TAB)%nat) by (change (length EJT_TAB) with 24%nat; lia).
  specialize (F _ (nth_In EJT_TAB 0 L)). apply andb_true_iff in F. destruct F as [F1 F2]. apply Z.leb_le in F1. apply Z.ltb_lt in F2. lia.
Qed.
Lemma ejt_target : forall a, 8 <= a <= 31 -> EL_JTAB_A + ejt (a - 8) = el_arm_pcA a.
Proof.
  intros a Ha.
  assert (F : forallb (fun i => EL_JTAB_A + ejt (i - 8) =? el_arm_pcA i) (map Z.of_nat (seq 8 24)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in F. apply Z.eqb_eq. apply F.
  apply in_map_iff. exists (Z.to_nat a). split; [lia|]. apply in_seq. lia.
Qed.
Lemma ejt_mod4 : forall i, 0 <= i < 24 -> (ejt i) mod 4 = 0.
Proof.
  intros i Hi. unfold ejt.
  assert (F : forallb (fun x => x mod 4 =? 0) EJT_TAB = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in F. assert (L : (Z.to_nat i < length EJT_TAB)%nat) by (change (length EJT_TAB) with 24%nat; lia).
  specialize (F _ (nth_In EJT_TAB 0 L)). apply Z.eqb_eq in F. exact F.
Qed.
Lemma el_arm_pc_dead : forall a, el_liveA a = false -> el_arm_pcA a = EL_EXIT_A.
Proof.
  intros a H. unfold el_liveA, el_arm_pcA in *. destruct ((0 <=? a) && (a <? 32)) eqn:R; [| reflexivity].
  cbn [andb] in H. apply negb_false_iff in H. apply Z.eqb_eq in H. subst a. reflexivity.
Qed.

Lemma el_dispatch : forall (X : lfA) (rv act : Z) (x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word) (pre : list cell) (post : list cell) F fc (m : mem),
  lfA_ok X -> 0 <= rv < 64 -> 0 <= act < 32 -> cells_size pre = 56%nat ->
  rw_cells asegs m (lf_S1 X) (pre ++ C8 (Z_to_bv 64 act) :: post) -> mem_inv asegs m ->
  evt asegs (fun ms => exists (x1' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s9' s10' t3' t4' t5' t6' : word) (pc : Z),
      ms = lf_st X pc x1' gp t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s6 (Z_to_bv 64 rv) s8 s9' s10' s11 t3' t4' t5' t6' F fc m
      /\ (pc = EL_EXIT_A \/ (pc = el_arm_pcA act /\ rv = 0 /\ 8 <= act <= 31)))
    (lf_st X (el_gate_pcA (Z_to_bv 64 rv)) x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 (Z_to_bv 64 rv) s8 s9 s10 s11 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros LK RV ACT SZ FRl MI.
  destruct LK as [(SPR & SPA') (SPT & SPA) (LLO & LOR) (FPOS & F64 & FSEG & FLO) (FSELF & SHB0 & SHT)].
  destruct X as [usp sp' f lo]. cbn [lf_usp lf_S1 lf_F lf_lo] in *.
  unfold lf_st, el_gate_pcA, EL_DISPATCH_A, EL_EXIT_A in *. cbn [lf_usp lf_S1 lf_F lf_lo].
  unfold FUZZ_STACK, USTACK_TOP in *.
  assert (ES : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; lia).
  apply Sj_stage1_kit.rw_cells_app in FRl. destruct FRl as [_ FRl]. rewrite SZ in FRl. change (Z.of_nat 56) with 56 in FRl.
  change (C8 (Z_to_bv 64 act) :: post) with ([C8 (Z_to_bv 64 act)] ++ post) in FRl. apply Sj_stage1_kit.rw_cells_app in FRl. destruct FRl as [FA _].
  destruct (bv_eqb (Z_to_bv 64 rv) (Z_to_bv 64 0)) eqn:K0.
  2: { apply evt_done. do 19 eexists. split; [atp_st_eq_goal| left; reflexivity]. }
  assert (R0 : rv = 0).
  { apply bv_eqb_eq in K0. apply (f_equal bv_unsigned) in K0. rewrite !unsigned_lit in K0 by lia. exact K0. }
  subst rv.
  repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep end).
  if_cases KLT; zify_cond KLT.
  { apply evt_done. do 19 eexists. split; [atp_st_eq_goal| left; reflexivity]. }
  assert (A8 : 8 <= act).
  { destruct (Z_lt_le_dec act 8) as [H|H]; [exfalso|exact H]. rewrite ?land64_mod in KLT. Z.div_mod_to_equations. lia. }
  repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep end).
  rewrite ?land64_mod, ?(Z.mod_small (act + -8)) by lia.
  pose proof (ejt_range (act - 8) ltac:(lia)) as EJR. pose proof (ejt_mod4 (act - 8) ltac:(lia)) as EJ4.
  lazymatch goal with |- context [Z_to_bv 64 (Z.shiftl ?x 2 + ?c)] =>
    pose proof (ejt_read m (act - 8) (wa (Z.shiftl x 2 + c)) MI ltac:(lia) ltac:(unfold wa, EL_JTAB_A; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RJ end.
  zstep.
  repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep end).
  rewrite ?(a_swrap32_small (ejt (act - 8))) by lia.
  lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?z)) _ _ _ _) => rewrite (ret_pc_even z) by (Z.div_mod_to_equations; lia) end.
  apply evt_done. do 19 eexists. split; [atp_st_eq_goal| right]. split; [| lia].
  rewrite <- (ejt_target act) by lia. unfold EL_JTAB_A. lia.
Qed.

Lemma arm_costA_bound : forall a n sn L, 0 <= n -> 0 <= sn -> 0 <= L -> arm_costA a n sn L <= Z.max (2164327424 + 2 * L) (64 + 24 * n + 4 * sn) + 2^22.
Proof.
  intros a n sn L Hn Hs HL. unfold arm_costA, ATP_ROOT_COST_A, EL_DUMP_C0, EL_DUMP_CW, EL_DUMP_CSB, EXC_SIZE. rewrite LVL_C1_val.
  assert (M : mcost 144 <= 2^22) by (unfold mcost, DCOST; cbn; lia).
  destruct (a =? 26); [lia|]. destruct (a =? 31); [lia|]. destruct ((a =? 22) || (a =? 23) || (a =? 24)); lia.
Qed.
Lemma arm_needA_bound : forall a, arm_needA a <= 458976.
Proof.
  intros a. unfold arm_needA, ATP_ROOT_STACK_A, EL_DUMP_STACK_A, EL_THROW_STACK_A, NORET_DEPTH, RT_STACK.
  destruct (a =? 26); [lia|]. destruct (a =? 31); [lia|]. destruct ((a =? 22) || (a =? 23) || (a =? 24)); lia.
Qed.
Lemma arm_xliveA_bound : forall a, 0 <= arm_xliveA a <= 1.
Proof. intros a. unfold arm_xliveA. destruct ((a =? 26) || (a =? 22) || (a =? 23) || (a =? 24)); lia. Qed.
Lemma el_PA_ge2' : forall bs, (2 <= el_PA bs)%nat.
Proof. intros bs. unfold el_PA, atp_P. lia. Qed.

Lemma cutX_sigW : forall (RT : rt_sig) (PMc : Model -> Prop) (Wc Wx : rts RT -> mem -> Prop) Σ0 m0 X d bs (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) K,
  (forall crd, cutX (rt_sigW RT Wc) PMc Wx Σ0 m0 X d bs ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 crd K) ->
  forall crd, cutX RT PMc Wx Σ0 m0 X d bs ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 crd K.
Proof.
  intros until K. intros H crd. unfold cutX. intros Σ m x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x6 x7 x8 x9 x10 x11 t3 t4 t5 t6 F fc LCa LCb h3 t A L0 j56 j176 ce jq. intros.
  eapply (H (rt_credit (rt_sigW RT Wc) Σ) Σ m); try eassumption. apply Z.le_refl.
Qed.

Section Disp.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable W : Z -> rts RT -> mem -> Prop.
Variable PMc : Model -> Prop.

Local Ltac ul := unfold FUZZ_STACK, ATP_ROOT_STACK_A, EL_DUMP_STACK_A, EL_THROW_STACK_A, NORET_DEPTH in *; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Theorem el_disp_ok : el_disp_cps RT PMc W (fun c => cutX (rt_sigW RT (W c)) PMc (W c)).
Proof using AF.
  intros Σ0 m0 X d bs ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 K FDO MST LK LOW D0 BSL INLV LVPOS LVB CR0 NL0 IOS XD0 AUX0 SPB0 ARMS CUTX CUTXW.
  unfold cutG. intros Σ m x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x6 x7 t3 t4 t5 t6 F fc j0 j64 j96 j121 h3 t j56 j176 j224 jos j528 j20 idx act sel A impl ix oc ia tape sbuf cap r
    BASE FRl ACT SEL R64 FS VR F56 PD PST OKR CAPR F176 FE F224 FO F528 LV MODS CR FRM.
  destruct BASE as (ARTg & MIg & STg & STp & FRs & FH & BS & LIB & PRES & FRSg & SPg).
  pose proof LK as [(SPR & SPA') (SPT & SPA) (LLO & LOR) (FPOS & F64 & FSEG & FLO) (FSELF & SHB0 & SHT)].
  destruct X as [usp sp' f lo]. cbn [lf_usp lf_S1 lf_F lf_lo] in *.
  pose proof (af_sp0_range RT AF Σ m ARTg) as SP0R. rewrite SPg in SP0R.
  assert (EU : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; ul).
  pose proof (bv_unsigned_in_range 64 r) as RR. unfold bv_modulus in RR. change (2 ^ Z.of_N 64) with (2^64) in RR.
  pose proof (el_vcost_bound bs BSL) as VCB.
  assert (CRT : rt_credit RT Σ0 - FUZZ_COST <= rt_credit RT Σ) by (unfold FUZZ_COST in *; lia).
  set (L0 := vblockA A (vcap_iter (el_PA bs) 0 0) (Z.of_nat (el_PA bs)) ++ rt_live RT Σ0) in *.
  assert (INCL : forall q, In q L0 -> In q (rt_live RT Σ)) by (intros q Hq; rewrite LV; do 6 right; exact Hq).
  assert (LEN : Z.of_nat (length (rt_live RT Σ)) <= Z.of_nat (length L0) + 6) by (rewrite LV; cbn [length]; lia).

  assert (FQ : exists jq, rw_cells asegs m (f + 224) [CB 792 jq]).
  { assert (X3 : rw_cells asegs m (f + 224) ([CB 16 j224] ++ [CB 288 jos] ++ [CB 488 j528])).
    { apply Sj_stage1_kit.rw_cells_app. split; [exact F224|]. cbn [cells_size csize Nat.add]. replace (f + 224 + Z.of_nat 16) with (f + 240) by lia.
      apply Sj_stage1_kit.rw_cells_app. split; [exact FO|]. cbn [cells_size csize Nat.add]. replace (f + 240 + Z.of_nat 288) with (f + 528) by lia. exact F528. }
    destruct (rw_cells_forget asegs m _ _ X3) as [jq X4]. exists jq. exact X4. }
  destruct FQ as [jq FQ].

  pose proof FRl as FRX.
  assert (SZb : cells_size (el_localsG (mkLF usp sp' f lo) j0 (fst (el_s0A d bs)) (snd (el_s0A d bs)) idx act j64 j96 sel
                              (el_fddA d (Z.of_nat (length bs)) + el_fdsA (Z.of_nat (length bs))) j121 r j20) = 152%nat)
    by (unfold el_localsG, res_cellsA; destruct (bv_eqb r (Z_to_bv 64 0)); reflexivity).
  unfold el_localsG in FRl. cbn [lf_usp lf_S1 lf_F lf_lo] in FRl.

  assert (TOX : forall (x1' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x6' x7' x9' x10' x11' t3' t4' t5' t6' : word),
    aevt RT PMc Σ K (MS (mkR x1' (wz sp') gp (wz TPV_A) t0' t1' t2' (wz usp) (wz sp') a0' a1' a2' a3' a4' a5' a6' a7'
                         (wz f) (wz (shad f)) (wz (f + 32)) (wz (f + 96)) x6' x7' (wz f) x9' x10' x11' t3' t4' t5' t6')
                    F (wz EL_EXIT_A) fc None m (seg_rom asegs))).
  { intros x1' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x6' x7' x9' x10' x11' t3' t4' t5' t6'.
    eapply (CUTX Σ m x1' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x6' x7' x9' x10' x11' t3' t4' t5' t6' F fc _ h3 t A L0 j56 j176 _ jq);
      cbn [lf_usp lf_S1 lf_F lf_lo];
      [exact ARTg| exact MIg| exact STg| exact STp| exact FRs| exact FH| exact LIB| exact PRES| exact FRSg| exact SPg| exact SZb| exact FRX| exact FS| exact VR| exact F56| reflexivity
      | exact PD| exact INCL| exact LEN| exact F176| | exact FE| exact FQ| exact CRT| exact FRM].
    destruct (bv_eqb r (Z_to_bv 64 0)); reflexivity. }

  apply (aevt_evt RT AF PMc MST).
  assert (ER : Z_to_bv 64 (bv_unsigned r) = r) by (apply Z_to_bv_bv_unsigned).
  rewrite <- ER.
  eapply evt_cut; [eapply (el_dispatch (mkLF usp sp' f lo) (bv_unsigned r) act x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (wz (f + 208)) (wz f) x6 x7 (wz (f + 120)) t3 t4 t5 t6
                             [CB 24 j0; C8 (wz (fst (el_s0A d bs))); C8 (wz (snd (el_s0A d bs))); C8 idx; C8 (wz (f + 240))] _ F fc m
                             LK ltac:(lia) ACT eq_refl); [exact FRl| exact MIg]|].
  cbv beta. unfold lf_st. cbn [lf_usp lf_S1 lf_F lf_lo].
  intros ms1 (x1d & t0d & t1d & t2d & a0d & a1d & a2d & a3d & a4d & a5d & a6d & a7d & s9d & s10d & t3d & t4d & t5d & t6d & pc & -> & CASES). apply evt_done.
  destruct CASES as [-> | (-> & R0 & A031)]; [apply TOX|].
  destruct (el_liveA act) eqn:LA; [| rewrite (el_arm_pc_dead act LA); apply TOX].

  assert (ERZ : r = Z_to_bv 64 0) by (apply bv_eq; rewrite R0; reflexivity). subst r. rewrite unsigned_lit in * by lia.
  unfold res_cellsA in FRl. rewrite bv_eqb_refl in FRl, FE. clear FRX SZb.
  destruct OKR as [K0|(_ & tws & sbs & TAPEB & SBUFB & WFS & SBSR & LT & LS)]; [rewrite unsigned_lit in K0 by lia; lia|].
  pose proof (tape_wfS_wf _ _ _ _ _ WFS) as WF.
  set (tn := Z.of_nat (length tws)) in *. set (sn := Z.of_nat (length sbs)) in *.
  assert (INTg : In (tape, al_tape cap) (rt_live RT Σ)) by (rewrite LV; do 4 right; left; reflexivity).
  assert (INSg : In (sbuf, al_sbuf cap) (rt_live RT Σ)) by (rewrite LV; do 5 right; left; reflexivity).
  pose proof (af_live_range RT AF Σ m tape _ ARTg INTg) as (TR0 & TR1 & TR2). rewrite SPg in TR1.
  pose proof (af_live_range RT AF Σ m sbuf _ ARTg INSg) as (SR0 & SR1 & SR2). rewrite SPg in SR1.
  assert (CAPR2 : 32 <= cap <= 2^26) by lia.
  pose proof (al_tape_bounds cap CAPR2) as TPB. pose proof (al_sbuf_bounds cap CAPR2) as SBB.
  assert (INF : In (f, 4%nat) (rt_frames RT Σ)) by (rewrite FRSg; left; reflexivity).

  assert (S0X : exists (PTR : Z) (bsp : list byte) (PB NPB : Z),
            el_s0A d bs = (PTR, Z.of_nat (length bsp)) /\ bytes_at asegs m PTR bsp /\ 0 <= PTR /\ Z.of_nat (length bsp) <= Z.of_nat (length bs)
            /\ (bsp = [] \/ (In (PB, NPB) (rt_live RT Σ0) /\ 0 < PB /\ PB <= PTR /\ PTR + Z.of_nat (length bsp) <= PB + NPB))).
  { unfold el_s0A, el_elsA, atp_elsA, el_fddA.
    destruct (poffs (chars (el_remA bs))) as [|[o0 l0] pr] eqn:EP.
    - exists 0, [], 0, 0. cbn [map app length]. unfold atp_P. rewrite <- poffs_length, EP. cbn. split; [reflexivity|]. split; [apply bytes_at_nil; lia|]. split; [lia|]. split; [lia| left; reflexivity].
    - pose proof (poffs_bound (chars (el_remA bs)) (o0, l0) ltac:(rewrite EP; left; reflexivity)) as PB0. cbn [fst snd] in PB0.
      unfold chars in PB0. rewrite length_map in PB0.
      assert (NE : el_remA bs <> []) by (intros E0; unfold chars in EP; rewrite E0 in EP; cbn in EP; discriminate).
      assert (N10 : 10 <= Z.of_nat (length bs)) by (unfold el_remA in NE; destruct (Z.leb_spec 10 (Z.of_nat (length bs))); [lia| exfalso; exact (NE eq_refl)]).
      assert (ERM : el_remA bs = skipn 10 bs) by (unfold el_remA; destruct (Z.leb_spec 10 (Z.of_nat (length bs))); [reflexivity| lia]).
      rewrite ERM in PB0. rewrite length_skipn in PB0.
      replace (10 <=? Z.of_nat (length bs)) with true by (symmetry; apply Z.leb_le; lia). cbn [map app nth pview fst snd].
      destruct INLV as [(p & k & Hin & P1 & P2)|(E0 & _)]; [| exfalso; subst bs; cbn [length] in N10; lia].
      pose proof (af_live_range RT AF Σ m p k ARTg (INCL _ ltac:(subst L0; apply in_or_app; right; exact Hin))) as (RP0 & _ & _).
      exists (d + 10 + Z.of_nat o0), (firstn l0 (skipn o0 (skipn 10 bs))), p, k.
      assert (LB : length (firstn l0 (skipn o0 (skipn 10 bs))) = l0) by (rewrite length_firstn, !length_skipn; lia).
      rewrite LB. split; [reflexivity|]. split.
      { apply bytes_at_firstn. replace (d + 10 + Z.of_nat o0) with (d + Z.of_nat 10 + Z.of_nat o0) by lia.
        apply bytes_at_skipn; [| rewrite length_skipn; lia]. apply bytes_at_skipn; [exact BS| lia]. }
      split; [lia|]. split; [lia|]. right. split; [exact Hin| lia]. }
  destruct S0X as (PTR & bsp & PB & NPB & ES0 & BSP & PTR0 & LBSP & PBF). rewrite ES0 in *. cbn [fst snd] in *.
  set (E := mkAEA lo usp (f + 120) f 4%nat tape (al_tape cap) sbuf (al_sbuf cap) tws sbs PTR (chars bsp) PB NPB).
  assert (ECL : zlength (chars bsp) = Z.of_nat (length bsp)) by apply chars_length.
  assert (OKE : aenvA_ok E).
  { apply mkAEAok; subst E; cbn [ae_lo ae_hi ae_DOC ae_fD ae_kD ae_TAPE ae_NT ae_SBUF ae_NS ae_tws ae_sbs ae_PTR ae_p1 ae_PB ae_NPB].
    - exact WF.
    - exact SBSR.
    - apply chars_range.
    - rewrite ECL. lia.
    - split; [clear - MODS; lia|]. split; [unfold al_tape; rewrite Z.mul_comm, Z.mod_mul by lia; reflexivity|].
      split; [unfold al_tape; subst tn; clear - LT; lia|]. split; [exact TR0| clear - TR1 LOW; lia].
    - split; [clear - MODS; lia|]. split; [unfold al_sbuf, roundup64; clear; Z.div_mod_to_equations; lia|].
      split; [subst sn; clear - LS; lia|]. split; [exact SR0| clear - SR1 LOW; lia].
    - intros NE. destruct PBF as [E0|(INPB & Q0 & Q1 & Q2)]; [exfalso; apply NE; rewrite E0; reflexivity|].
      pose proof (af_live_range RT AF Σ m PB NPB ARTg (INCL _ ltac:(subst L0; apply in_or_app; right; exact INPB))) as (RB0 & RB1 & _). rewrite SPg in RB1.
      split; [exact RB0|]. rewrite ECL. clear - Q1 Q2 RB1 LOW. lia.
    - exact PTR0.
    - change (fs_size 4) with 1024. split; [clear - F64; Z.div_mod_to_equations; lia|]. split; [lia|]. split; [lia|]. split; [exact FSEG| exact FLO].
    - exact LLO.
    - clear - LOR SPT. ul. }
  assert (LVE : a_live RT Σ E).
  { unfold a_live; subst E; cbn [ae_lo ae_fD ae_kD ae_TAPE ae_NT ae_SBUF ae_NS ae_p1 ae_PB ae_NPB].
    split; [exact INTg|]. split; [exact INSg|].
    split; [destruct PBF as [->|(INPB & _)]; [left; reflexivity| right; apply INCL; subst L0; apply in_or_app; right; exact INPB]|].
    split; [exact INF| rewrite SPg; exact LOW]. }

  pose proof PST as (FOBJP & (q1 & q17 & q57 & PCg) & _).
  assert (DOCC : rw_cells asegs m (f + 120) [C8 (Z_to_bv 64 tape); C8 (Z_to_bv 64 sbuf)]).
  { unfold pid_cells in PCg.
    lazymatch type of PCg with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?rest) =>
      change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: rest) with ([c0; c1; c2; c3; c4; c5] ++ [c6; c7] ++ rest) in PCg end.
    apply Sj_stage1_kit.rw_cells_app in PCg. destruct PCg as [_ X]. apply Sj_stage1_kit.rw_cells_app in X. destruct X as [X _].
    cbn [cells_size csize Nat.add] in X. replace (f + 96 + Z.of_nat 24) with (f + 120) in X by lia. exact X. }
  assert (AI0 : AINV_A E m).
  { unfold AINV_A; subst E; cbn [ae_DOC ae_TAPE ae_SBUF ae_tws ae_sbs ae_PTR ae_p1].
    split; [exact TAPEB|]. split; [exact SBUFB|].
    split; [change (map (Z_to_bv 8) (chars bsp)) with (to_bytes (chars bsp)); rewrite to_bytes_chars; exact BSP|].
    split; [exact DOCC|].
    replace (shad (f + 120)) with (shad f + Z.of_nat 15) by (unfold shad, SHB; Z.div_mod_to_equations; lia).
    pose proof FS as X. unfold el_shadowA, el_shbytesA in X. cbn [map app repeat] in X.
    lazymatch type of X with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?c13 :: ?c14 :: ?d0 :: ?d1 :: ?rest) =>
      change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: c9 :: c10 :: c11 :: c12 :: c13 :: c14 :: d0 :: d1 :: rest)
        with ([c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13; c14] ++ [d0; d1] ++ rest) in X end.
    apply Sj_stage1_kit.rw_cells_app in X. destruct X as [_ X]. apply Sj_stage1_kit.rw_cells_app in X. destruct X as [X _].
    cbn [cells_size csize Nat.add] in X. destruct X as [[_ HB] _]. cbn [cells_bytes cbytes app] in HB. exact HB. }

  cbn [app] in FRl. pose proof FRl as L24.
  lazymatch type of L24 with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?rest) =>
    change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: rest) with ([c0] ++ [c1; c2; c3; c4; c5] ++ rest) in L24 end.
  apply Sj_stage1_kit.rw_cells_app in L24. destruct L24 as [_ L24]. apply Sj_stage1_kit.rw_cells_app in L24. destruct L24 as [L24 _].
  cbn [cells_size csize Nat.add] in L24. replace (sp' + Z.of_nat 24) with (sp' + 24) in L24 by lia.
  rewrite <- (Z_to_bv_bv_unsigned idx) in L24.
  pose proof FRl as L124.
  lazymatch type of L124 with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?c13 :: ?rest) =>
    change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: c9 :: c10 :: c11 :: c12 :: c13 :: rest)
      with ([c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12] ++ [c13] ++ rest) in L124 end.
  apply Sj_stage1_kit.rw_cells_app in L124. destruct L124 as [_ L124]. apply Sj_stage1_kit.rw_cells_app in L124. destruct L124 as [L124 _].
  cbn [cells_size csize Nat.add] in L124. replace (sp' + Z.of_nat 124) with (sp' + 124) in L124 by lia.
  pose proof FRl as L96.
  lazymatch type of L96 with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?rest) =>
    change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: c9 :: c10 :: c11 :: rest)
      with ([c0; c1; c2; c3; c4; c5; c6; c7] ++ [c8; c9; c10; c11] ++ rest) in L96 end.
  apply Sj_stage1_kit.rw_cells_app in L96. destruct L96 as [_ L96]. apply Sj_stage1_kit.rw_cells_app in L96. destruct L96 as [L96 _].
  cbn [cells_size csize Nat.add] in L96. replace (sp' + Z.of_nat 96) with (sp' + 96) in L96 by lia.
  destruct (rw_cells_forget asegs m _ _ L96) as [jr L96']. cbn [cells_size csize Nat.add] in L96'.

  assert (NL : libc_nl m).
  { apply (libc_nl_agree m0 m NL0). intros a Ha. apply PRES; [right; left; exact (libc_nl_static _ Ha)|].
    unfold LIBC_NL in Ha. unfold EL_LIB_FP, LIB_FP, EL_UNW_A, EL_EHG_A, EL_TPLOC_A, TPV_A. cbn [outside app]. repeat split; try exact I; lia. }
  assert (IOS1 : io_ssp m).
  { destruct IOS as (g & _ & G). exists g. split; [exact (proj1 (af_got_lib RT AF Σ m ARTg))|].
    apply (ro_cells_agree asegs m0 m _ _ G). intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply PRES; [right; left; apply client_static_intro; lia|].
    unfold EL_LIB_FP, LIB_FP, EL_UNW_A, EL_EHG_A, EL_TPLOC_A, TPV_A. cbn [outside app]. repeat split; try exact I; lia. }

  assert (XD : el_xdataA m).
  { apply (el_xdata_agree m0 m XD0). intros a Ha. apply PRES; [right; left; apply client_static_intro; cbv beta in Ha; lia|].
    cbv beta in Ha. unfold EL_LIB_FP, LIB_FP, EL_UNW_A, EL_EHG_A, EL_TPLOC_A, TPV_A. cbn [outside app]. repeat split; try exact I; lia. }
  assert (AUX : el_auxvA usp m).
  { apply (el_auxv_pres_fp _ _ _ _ _ _ _ AUX0 PRES); [lia|]. intros x Hx.
    assert (R : 0x6c8100 <= x < 0x6c8108 \/ usp <= x) by (destruct Hx as [Hx|Hx]; [left; exact (auxc_range _ Hx)| right; lia]).
    unfold EL_LIB_FP, LIB_FP, EL_UNW_A, EL_EHG_A, EL_TPLOC_A, TPV_A. cbn [outside app]. unfold FUZZ_STACK in LOR. repeat split; try exact I; clear - R LLO LOR; lia. }

  pose proof (af_frames_range RT AF Σ m f 4%nat ARTg INF) as (_ & _ & _ & FLV). change (fs_size 4) with 1024 in FLV.
  pose proof (af_fshadow_apart RT AF Σ m f 4%nat ARTg INF) as (FSL & _). change (fs_size 4) with 1024 in FSL.
  assert (SHF0 : shad f = f / 8 + SHB) by reflexivity.

  assert (OWA : forall a, (sp' <= a < sp' + 96 \/ sp' + 120 <= a < USTACK_TOP \/ f <= a < f + 240 \/ f + 528 <= a < f + 1016
                           \/ shad f <= a < shad f + 30 \/ shad f + 66 <= a < shad f + 128) -> outside (arm_WA (mkLF usp sp' f lo)) a).
  { intros a Ha. unfold arm_WA, EL_LIB_FP, LIB_FP, EL_UNW_A, EL_EHG_A, EL_TPLOC_A, TPV_A. cbn [lf_usp lf_S1 lf_F lf_lo outside app].
    unfold shad, SHB, SEGTOP_A, FUZZ_STACK, STACK_WIN, USTACK_TOP in *. clear - Ha FSEG FLO FSELF SHB0 SHT SPR LOR LLO.
    repeat split; try exact I; lia. }
  assert (OWL : forall a q k, In (q, k) (rt_live RT Σ) -> q <= a < q + k -> outside (arm_WA (mkLF usp sp' f lo)) a).
  { intros a q k Hin Ha. pose proof (af_live_range RT AF Σ m q k ARTg Hin) as (Y0 & Y1 & Y2). rewrite SPg in Y1. pose proof (FLV q k Hin) as Y3. pose proof (FSL q k Hin) as Y4.
    rewrite SHF0 in Y4. unfold arm_WA, EL_LIB_FP, LIB_FP, EL_UNW_A, EL_EHG_A, EL_TPLOC_A, TPV_A. cbn [lf_usp lf_S1 lf_F lf_lo outside app].
    unfold shad, SHB, SEGTOP_A, FUZZ_STACK, STACK_WIN, USTACK_TOP in *.
    replace ((f + 1024) / 8 + 2147450880) with (f / 8 + 2147450880 + 128) in Y4 by (Z.div_mod_to_equations; lia).
    clear - Ha Y0 Y1 Y2 Y3 Y4 SPR LOR LOW. repeat split; try exact I; lia. }

  assert (REPACK : forall (Wx : rts RT -> mem -> Prop) (crd : Z) (Σ' : rts RT) (m' : mem) (fc' : bv 32) (F' : bvmap 5 word)
                          (x1' t0' t1' t2' a0'' a1'' a2' a3' a4' a5' a6' a7' s6' s7' s9' s10' s11' t3' t4' t5' t6' : word),
      Wx Σ' m' -> mem_inv asegs m' -> stk asegs m' lo sp' -> frm0 fc' ->
      rt_live RT Σ' = rt_live RT Σ -> rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ -> crd <= rt_credit RT Σ' ->
      rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) sp' (arm_WA (mkLF usp sp' f lo)) m m' ->
      (exists jr' jos', arm_memA (mkLF usp sp' f lo) E act sel (bv_unsigned idx) jr' jos' t m') ->
      cutX RT PMc Wx Σ0 m0 (mkLF usp sp' f lo) d bs ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 crd K ->
      aevt RT PMc Σ' K (MS (mkR x1' (wz sp') gp (wz TPV_A) t0' t1' t2' (wz usp) (wz sp') a0'' a1'' a2' a3' a4' a5' a6' a7'
                             (wz f) (wz (shad f)) (wz (f + 32)) (wz (f + 96)) s6' s7' (wz f) s9' s10' s11' t3' t4' t5' t6')
                        F' (wz EL_EXIT_A) fc' None m' (seg_rom asegs))).
  { intros Wx crd Σ' m' fc' F' x1' t0' t1' t2' a0'' a1'' a2' a3' a4' a5' a6' a7' s6' s7' s9' s10' s11' t3' t4' t5' t6'
      AX MI' ST' FRM' LV' FRS' SP' CR' PRES' (jr' & jos' & AM') CUT.
    destruct AM' as (C24 & C124 & C96 & CE' & FO' & FS' & AI' & LIB' & _ & _). cbn [lf_usp lf_S1 lf_F lf_lo] in C24, C124, C96, CE', FO', FS'.
    rewrite FRSg in PRES'.
    assert (AGA : forall (P : Z -> Prop), (forall x, P x -> aclient (rt_live RT Σ) [(f, 4%nat)] sp' x /\ outside (arm_WA (mkLF usp sp' f lo)) x) -> agree_on P m m').
    { intros P HP a Ha. destruct (HP _ Ha) as [H1 H2]. exact (PRES' a H1 H2). }
    assert (INF' : forall lo' hi', f <= lo' -> hi' <= f + 1016 -> forall x, lo' <= x < hi' -> aclient (rt_live RT Σ) [(f, 4%nat)] sp' x).
    { intros lo' hi' H1 H2 x Hx. right; right; right; left. exists f, 4%nat. split; [left; reflexivity| change (fs_size 4) with 1024; lia]. }
    assert (INS' : forall x, shad f <= x < shad f + 128 -> aclient (rt_live RT Σ) [(f, 4%nat)] sp' x).
    { intros x Hx. right; right; right; right. exists f, 4%nat. split; [left; reflexivity| rewrite SHF0 in Hx |- *; unfold shad, SHB in *; change (fs_size 4) with 1024; Z.div_mod_to_equations; lia]. }

    pose proof FRl as K0.
    lazymatch type of K0 with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?rest) =>
      change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: c9 :: c10 :: c11 :: rest)
        with ([c0; c1; c2; c3; c4; c5; c6; c7] ++ [c8; c9; c10; c11] ++ rest) in K0 end.
    apply Sj_stage1_kit.rw_cells_app in K0. destruct K0 as [K0 KR]. apply Sj_stage1_kit.rw_cells_app in KR. destruct KR as [_ K120].
    cbn [cells_size csize Nat.add] in K120.
    replace (sp' + Z.of_nat 96 + Z.of_nat 24) with (sp' + 120) in K120 by lia.
    lazymatch type of K0 with rw_cells _ _ _ ?cs =>
      assert (K0' : rw_cells asegs m' sp' cs) by (eapply rw_cells_agree_nw; [exact K0|]; apply AGA; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [left; ul| apply OWA; lia]) end.
    lazymatch type of K120 with rw_cells _ _ _ ?cs =>
      assert (K120' : rw_cells asegs m' (sp' + 120) cs) by (eapply rw_cells_agree_nw; [exact K120|]; apply AGA; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [left; ul| apply OWA; lia]) end.
    lazymatch type of K0 with rw_cells _ _ _ ?cs0 => lazymatch type of K120 with rw_cells _ _ _ ?cs1 =>
      assert (LC' : rw_cells asegs m' sp' (cs0 ++ [CB 24 jr'] ++ cs1)) end end.
    { apply Sj_stage1_kit.rw_cells_app. split; [exact K0'|]. cbn [cells_size csize Nat.add]. replace (sp' + Z.of_nat 96) with (sp' + 96) by lia.
      apply Sj_stage1_kit.rw_cells_app. split; [exact C96|]. cbn [cells_size csize Nat.add]. replace (sp' + 96 + Z.of_nat 24) with (sp' + 120) by lia. exact K120'. }

    assert (FQ' : exists jq', rw_cells asegs m' (f + 224) [CB 792 jq']).
    { assert (X3 : rw_cells asegs m' (f + 224) ([CB 16 j224] ++ [CB 288 jos'] ++ [CB 488 j528])).
      { apply Sj_stage1_kit.rw_cells_app. split.
        { eapply rw_cells_agree_nw; [exact F224|]. apply AGA. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [apply (INF' (f + 224) (f + 240)); lia| apply OWA; lia]. }
        cbn [cells_size csize Nat.add]. replace (f + 224 + Z.of_nat 16) with (f + 240) by lia.
        apply Sj_stage1_kit.rw_cells_app. split; [exact FO'|]. cbn [cells_size csize Nat.add]. replace (f + 240 + Z.of_nat 288) with (f + 528) by lia.
        eapply rw_cells_agree_nw; [exact F528|]. apply AGA. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [apply (INF' (f + 528) (f + 1016)); lia| apply OWA; lia]. }
      destruct (rw_cells_forget asegs m' _ _ X3) as [jq' X4]. exists jq'. exact X4. }
    destruct FQ' as [jq' FQ'].

    assert (VR' : vrepA m' (f + 32) A (vcap_iter (el_PA bs) 0 0) (Z.of_nat (el_PA bs)) (el_elsA d bs)).
    { pose proof VR as (ELS & SZC & CAPB & A0 & AH & SV & BLK).
      split; [exact ELS|]. split; [exact SZC|]. split; [exact CAPB|]. split; [exact A0|]. split; [exact AH|]. split.
      - eapply rw_cells_agree_nw; [exact SV|]. apply AGA. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [apply (INF' (f + 32) (f + 56)); lia| apply OWA; lia].
      - destruct BLK as [B|(B1 & B2 & B3 & B4)]; [left; exact B| right]. split; [exact B1|]. split; [exact B2|]. split; [exact B3|].
        eapply rw_cells_agree_nw; [exact B4|]. apply AGA. intros x Hx.
        assert (INA : In (A, 16 * Z.of_nat (el_PA bs)) (rt_live RT Σ)).
        { apply INCL. subst L0. apply in_or_app. left. unfold vblockA. destruct (Z.eqb_spec (vcap_iter (el_PA bs) 0 0) 0); [pose proof (el_PA_ge2' bs); pose proof (vcap_iter_inv (el_PA bs) 0 0 ltac:(lia) ltac:(lia)); lia|]. apply ann_block_vis. }
        rewrite velts_size in Hx. unfold el_elsA in Hx. rewrite atp_elsA_length in Hx. fold (el_PA bs) in Hx.
        split; [right; right; left; exists A, (16 * Z.of_nat (el_PA bs)); split; [exact INA| lia]| exact (OWL x _ _ INA ltac:(lia))]. }
    assert (PD' : pdone RT Σ' m' (f + 96) L0).
    { apply (pdone_fp RT Σ Σ' m m' (f + 96) L0 PD FRS' LV'). apply AGA. intros x [Hx|[Hx|(q & k & Hin & Hx)]].
      - split; [apply (INF' (f + 96) (f + 176)); lia| apply OWA; lia].
      - replace (shad (f + 96)) with (shad f + 12) in Hx by (unfold shad, SHB; Z.div_mod_to_equations; lia). split; [apply INS'; lia| apply OWA; lia].
      - split; [right; right; left; exists q, k; split; [exact Hin| exact Hx]| exact (OWL x q k Hin Hx)]. }
    assert (F56' : rw_cells asegs m' (f + 56) [CB 40 j56]).
    { eapply rw_cells_agree_nw; [exact F56|]. apply AGA. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [apply (INF' (f + 56) (f + 96)); lia| apply OWA; lia]. }
    assert (F176' : rw_cells asegs m' (f + 176) [CB 32 j176]).
    { eapply rw_cells_agree_nw; [exact F176|]. apply AGA. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [apply (INF' (f + 176) (f + 208)); lia| apply OWA; lia]. }
    assert (FH' : rw_cells asegs m' f (fz_hdr (C8 (wz 0x41b58ab3)) (C8 (wz 0x126fb)) (C8 (wz 0xb1608)) h3)).
    { eapply rw_cells_agree_nw; [exact FH|]. apply AGA. intros x Hx. unfold fz_hdr in Hx. cbn [cells_size csize Nat.add] in Hx. split; [apply (INF' f (f + 32)); lia| apply OWA; lia]. }
    assert (STp' : stk asegs m' (sp' + 152) (usp - 104)).
    { eapply stk_agree_nw; [exact STp|]. apply AGA. intros x Hx. cbv beta in Hx. split; [left; ul| apply OWA; ul]. }
    assert (FRs' : rw_cells asegs m' (usp - 104) (fa_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
    { eapply rw_cells_agree_nw; [exact FRs|]. apply AGA. intros x Hx. unfold fa_saved in Hx. cbn [cells_size csize Nat.add] in Hx. split; [left; ul| apply OWA; ul]. }
    assert (PRES0' : rt_pres_fp (rt_live RT Σ0) [] usp EL_LIB_FP m0 m').
    { intros a Ha Ho. rewrite <- (PRES a Ha Ho). apply PRES'.
      - apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros q Hq; apply INCL; subst L0; apply in_or_app; right; exact Hq| intros q []| lia].
      - destruct Ha as [H|[H|[H|[H|H]]]]; [apply OWA; right; left; ul| | | destruct H as (? & ? & [] & _)| destruct H as (? & ? & [] & _)].
        + pose proof (client_static_range _ H) as R9. unfold arm_WA. cbn [lf_usp lf_S1 lf_F lf_lo].
          unfold EL_LIB_FP, LIB_FP, EL_UNW_A, EL_EHG_A, EL_TPLOC_A, TPV_A in Ho |- *. cbn [outside app] in Ho |- *.
          unfold shad, SHB, SEGTOP_A, FUZZ_STACK in *. clear - R9 Ho FSEG SHB0 SPR LOR LLO.
          decompose [and] Ho. repeat split; try exact I; try lia; assumption.
        + destruct H as (q & k & Hin & Hr). exact (OWL _ q k (INCL _ ltac:(subst L0; apply in_or_app; right; exact Hin)) Hr). }
    eapply (CUT Σ' m' x1' t0' t1' t2' a0'' a1'' a2' a3' a4' a5' a6' a7' s6' s7' s9' s10' s11' t3' t4' t5' t6' F' fc' _ h3 t A L0 j56 j176 [C8 (wz (ae_DOC E)); C8 (wz 1)] jq');
      cbn [lf_usp lf_S1 lf_F lf_lo];
      [exact AX| exact MI'| exact ST'| exact STp'| exact FRs'| exact FH'| exact LIB'| exact PRES0'| rewrite FRS'; exact FRSg| rewrite SP'; exact SPg| | exact LC'| exact FS'
      | exact VR'| exact F56'| reflexivity| exact PD'| rewrite LV'; exact INCL| rewrite LV'; exact LEN| exact F176'| reflexivity| exact CE'| exact FQ'| exact CR'| exact FRM'].
    reflexivity. }

  pose proof (ARMS act LA) as ARM. unfold arm_cpsA in ARM.
  assert (NTB : tn <= cap + 66) by (subst tn; pose proof (roundup64_lt (cap + 3)); lia).
  eapply (ARM Σ K (mkLF usp sp' f lo) E sel (bv_unsigned idx) jr jos t x1d gp t0d t1d t2d a0d a1d a2d a3d a4d a5d a6d a7d s9d s10d t3d t4d t5d t6d F fc m
            FDO MST LK OKE); cbn [lf_usp lf_S1 lf_F lf_lo].
  -   subst E. unfold lf_envA. cbn. repeat split; reflexivity.
  -   subst E. cbn. exact WFS.
  - exact SEL.
  - pose proof (bv_unsigned_in_range 64 idx) as XR. unfold bv_modulus in XR. change (2 ^ Z.of_N 64) with (2^64) in XR. lia.
  - exact LVE.
  - exact FRSg.
  -   change (lposx (rt_live RT Σ)). rewrite LV.
    pose proof (roundup64_ge cap) as RG1. pose proof (roundup64_ge (cap + 3)) as RG2. pose proof (roundup64_ge (5 * (cap / 3) + 64)) as RG3.
    do 6 (apply lposx_cons; [first [lia| unfold sc_idx, al_tape, al_sbuf; clear - CAPR RG1 RG2 RG3; Z.div_mod_to_equations; lia]|]).
    apply lposx_app; [| exact (lposx_of_pos _ LVPOS)].
    unfold vblockA. destruct (vcap_iter (el_PA bs) 0 0 =? 0); [intros p' k' []| apply lposx_ann_block; pose proof (el_PA_ge2' bs); lia].
  -   rewrite LV. cbn [length]. rewrite length_app. pose proof (vblockA_length A (vcap_iter (el_PA bs) 0 0) (Z.of_nat (el_PA bs))).
    pose proof (arm_xliveA_bound act). unfold FUZZ_LIVE in LVB. lia.
  -   subst E. cbn [ae_tws ae_sbs ae_p1]. rewrite ECL.
    pose proof (arm_costA_bound act (Z.of_nat (length tws)) (Z.of_nat (length sbs)) (Z.of_nat (length bsp)) ltac:(lia) ltac:(lia) ltac:(lia)). unfold FUZZ_COST in *. subst tn sn. lia.
  - exact ARTg.
  - exact MIg.
  - exact STg.
  - pose proof (arm_needA_bound act). ul.
  -   unfold arm_memA. cbn [lf_usp lf_S1 lf_F lf_lo]. subst E. cbn [ae_PTR ae_p1 ae_DOC]. rewrite ?ECL.
    split; [exact L24|]. split; [exact L124|]. split; [exact L96'|]. split; [exact FE|]. split; [exact FO|]. split; [exact FS|].
    split; [exact AI0|]. split; [exact LIB|]. split; [exact NL| exact IOS1].
  - exact FRM.
  - exact XD.
  - exact AUX.
  - rewrite SPg. exact SPB0.
  -
    intros w c Σ' m' fc' F' x1' t0' t1' t2' a0'' a1'' a2' a3' a4' a5' a6' a7' s6' s7' s9' s10' s11' t3' t4' t5' t6' POST.
    destruct POST as (AX & MI' & ST' & FRM' & LV' & FRS' & SP' & CRc & PRES' & AM' & WT). cbn [lf_usp lf_S1 lf_F lf_lo] in ST', PRES'.
    assert (CB : rt_credit RT Σ0 - FUZZ_COST <= c).
    { subst E. cbn [ae_tws ae_sbs ae_p1] in CRc. rewrite ECL in CRc.
      pose proof (arm_costA_bound act (Z.of_nat (length tws)) (Z.of_nat (length sbs)) (Z.of_nat (length bsp)) ltac:(lia) ltac:(lia) ltac:(lia)). unfold FUZZ_COST in *. subst tn sn. lia. }
    destruct w.
    +
      unfold artxA in AX.
      apply (REPACK (W c) (rt_credit RT Σ') Σ' m' fc' F' x1' t0' t1' t2' a0'' a1'' a2' a3' a4' a5' a6' a7' s6' s7' s9' s10' s11' t3' t4' t5' t6'
               AX MI' ST' FRM' LV' FRS' SP' ltac:(lia) PRES' AM').
      exact (cutX_sigW RT PMc (W c) (W c) Σ0 m0 _ d bs ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 K (fun crd => CUTXW c crd CB) (rt_credit RT Σ')).
    +
      unfold artxA in AX. destruct AX as [AX EC].
      apply (REPACK (ART RT) (rt_credit RT Σ0 - FUZZ_COST) Σ' m' fc' F' x1' t0' t1' t2' a0'' a1'' a2' a3' a4' a5' a6' a7' s6' s7' s9' s10' s11' t3' t4' t5' t6'
               AX MI' ST' FRM' LV' FRS' SP' ltac:(lia) PRES' AM').
      exact CUTX.
Qed.
End Disp.
