(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Image ZBridge SysStep ITree Nodes Decode Arr FP Tac InitMem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed HarnessP ProgA AsanProgDeps.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF ITreeA SysStepF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AImg RtCells AProto ABase AMalloc_iface I_asan_memset.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AU_kit AU_iface AHarnessU_iface AU_client_kit AU_fuzz_kit AU_parts_iface AU_steptac.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import StepF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import ShadowTac APC_kit APC_kit2 APC_setcap APC_setdepth.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac solve_load ::= first [ solve_load_tight | solve_load_image ].
Local Ltac solve_store ::= solve_store_tight.

Section CANSEC1. Context {rc : runConstT}.
Definition ACREATE : Z := 0x973cc.
Definition ACREATE_STACK : Z := 64 + ASETCAP_STACK.

(* [comment removed for export] *)
Definition aimpl_cells (p1 p2 pad : list byte) (ASI cap AOC AIA : Z) : list cell :=
  [C8 (Z_to_bv 64 AVTAB_DOM); C4 (Z_to_bv 64 0); CB 4 p1; C8 (Z_to_bv 64 ASI); C4 (Z_to_bv 64 0); CB 4 p2; C8 (Z_to_bv 64 cap);
   C8 (Z_to_bv 64 MAX_DEPTH); C2 (Z_to_bv 64 0); CB 6 pad; C8 (Z_to_bv 64 AOC); C8 (Z_to_bv 64 AIA); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].

Lemma le2_zero_run : le2 (Z_to_bv 64 0) = repeat (Z_to_bv 8 0) 2.
Proof. vm_compute. reflexivity. Qed.

Section S.
Variable AI : AMallocIface.
Notation CI := (aci AI).

Definition acreate_post (L : alayout) (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : APS) (LB : list ablock) (len lo DST : Z) (m : amem)
    (r : AsanCtrl.aptr * AsanCtrl.aptr * AsanCtrl.aptr * AsanCtrl.aptr) (s' : APS) (RNG' : footprint) : machine_state -> Prop :=
  fun ms' => fp_le RNG RNG' /\ exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ aheap_pres_x CI LB (bv_unsigned sp) DST 8 m m'
    /\ aps_rest s' = aps_rest s
    /\ let '(im, si, oc, ia) := r in
       exists AIM ASI AOC AIA p1 p2 pad jsi joc jia,
         ablock_range AIM IMPL_BYTES /\ ablock_range ASI (SIDX_BYTES len) /\ ablock_range AOC OC_BYTES /\ ablock_range AIA ISARR_BYTES
         /\ AHEAP AI L RNG' (aps_m s') (HB ia AIA ISARR_BYTES :: HB oc AOC OC_BYTES :: HB si ASI (SIDX_BYTES len) :: HB im AIM IMPL_BYTES :: LB) m'
         /\ rw_cells asegs m' DST [C8 (Z_to_bv 64 AIM)]
         /\ rw_cells asegs m' AIM (aimpl_cells p1 p2 pad ASI (CAP len) AOC AIA)
         /\ rw_cells asegs m' ASI [C4 (Z_to_bv 64 0); CB (Z.to_nat (SIDX_BYTES len - 4)) jsi]
         /\ rw_cells asegs m' AOC [CB (Z.to_nat OC_BYTES) joc] /\ rw_cells asegs m' AIA [CB (Z.to_nat ISARR_BYTES) jia].

Definition acreate_stmt : Prop :=
  forall (L : alayout) (RNG : footprint) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (s : APS) (LB : list ablock) (len lo DST : Z),
  AHEAP AI L RNG (aps_m s) LB m ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - ACREATE_STACK ->
  bv_unsigned sp < al_top L -> bv_unsigned sp mod 16 = 0 ->
  tp = Z_to_bv 64 ATP ->
  client_img m -> client_sh m ->
  rw_cells asegs m DST [C8 (Z_to_bv 64 0)] -> 0 <= DST -> DST + 8 <= ATOP -> DST mod 8 = 0 ->
  (exists cls FA FN, In (mkABlock (ABFake cls) FA FN) LB /\ FA <= DST /\ DST + 8 <= FA + FN /\ ablk FA (FA + FN)) ->
  shc m DST -> rng RNG DST 8 -> rng RNG (shx DST) 1 ->
  0 <= len < 2^26 ->
  In [AMALLOC_PC; AOPNEW_RET] (al_U L) ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_aimg_sh RNG -> aps_ok L s ->
  a1 = Z_to_bv 64 (CAP len) -> a2 = Z_to_bv 64 MAX_DEPTH -> a3 = Z_to_bv 64 DST ->
  implMA RNG (HarnessP.impl_create amalloc_M (new_handlerA AAllocAsan) len) s
        (acreate_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB len lo DST m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ACREATE) fc None m (seg_rom asegs)).

Section Proof.
  Hypothesis IMG_CI : forall iv, In iv client_ranges -> In iv CI.
  Hypothesis ONTA : opnew_nt_stmtA AI.
  Theorem acreate_proof : acreate_stmt.
  Proof.
    unfold acreate_stmt. intros until DST. intros AH MI ST LOA LOS STOP SP16 TP CI0 CSH DC D0 DTOP D8 FK SCD RD RSD HL TRM RSTK RI RISH AOK A1 A2 A3.
    destruct FK as (fcls & FA & FN & INF & FK1 & FK2 & FKB).
    pose proof (ablk_lin _ _ FKB) as (FKB1 & FKB2 & FKB3 & FKB4). unfold AIMG_HI in FKB1. band_ind FKB bF.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold ACREATE_STACK, ASETCAP_STACK, OPNEW_NT_STACK_A, OPNEW_STACK_A, AMALLOC_STACK in LOS. atop_facts.
    pose proof (proj1 ONTA) as ONT1. unfold opnew_nt_stmtA_at in ONT1.
    pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & _).
    pose proof (got_nothrow_of_aheap AI _ _ _ _ _ AH MI) as GNT. unfold AGOT_NOTHROW, ANOTHROW in GNT.
    pose proof (client_rt_of_aheap AI _ _ _ _ _ AH) as (GOT & RIC & REAL & SHB & SUA & INI & LAY).
    destruct CI0 as (CGOT & VTI & VTD & _). unfold AVTAB_IMPL, AVTAB_DOM, vtab_impl_cells, vtab_dom_cells in VTI, VTD.
    pose proof (client_sh_cell m 0x103f80 CSH ltac:(cbn; tauto)) as VSH6. pose proof (client_sh_cell m 0x103f88 CSH ltac:(cbn; tauto)) as VSH7.
    change (Z.shiftr 0x103f80 3 + 2147450880) with 2147583984 in VSH6. change (Z.shiftr 0x103f88 3 + 2147450880) with 2147583985 in VSH7.
    clear CSH CGOT VTI.
    unfold shc, shx, ASHOFF in SCD. unfold shx, ASHOFF in RSD.
    pose proof (blk_shx_bounds DST ltac:(lia) ltac:(lia)) as SBD.
    assert (CAPR : 32 <= CAP len < 2^26 + 32) by (unfold CAP; lia).
    assert (SIDXGE : 36 <= SIDX_BYTES len)
      by (unfold SIDX_BYTES; pose proof (ROUNDUP64_bounds (CAP len) ltac:(lia)); lia).
    unfold HarnessP.impl_create.
    apply implMA_from_evtF.
    pose proof (munch_refl [(lo, bv_unsigned sp); (DST, DST + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 64%nat ST.
    subst a1 a2 a3. unfold ACREATE, MAX_DEPTH in *.
    steps_to 0xe2e2c.
    apply evtF_done.
    lazymatch goal with |- implMA _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (AH1 : AHEAP AI L RNG (aps_m s) LB mx)
        by (eapply (AI_frame AI); [exact AH| exact MU| exact WM|];
            apply Forall_cons; [left; left; cbn; lia|]; apply Forall_cons; [right; left; exists (mkABlock (ABFake fcls) FA FN); split; [exact INF| cbn; lia]| apply Forall_nil])
    end.
    eapply implMA_bind.
    { eapply ONT1 with (lo := lo) (n := 96); try reflexivity; rewrite ?unsigned_lit by lia;
        first [exact AH1 | exact TP | exact RSTK | exact TRM | exact AOK | eassumption | (cbn; lia)
              | (unfold OPNEW_NT_STACK_A, OPNEW_STACK_A, AMALLOC_STACK; lia) | (unfold AREQMAX; lia) | lia]. }
    cbv beta. intros imp s1' RNG1 ms1 (FPL1 & u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & AIM & jim & -> & MI2 & ST2 & HPR1 & ARS1 & BRM & AH2 & BLKM & RIM & RSIM).
    rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in HPR1 by lia.
    retlit.
    assert (INF1 : In (mkABlock (ABFake fcls) FA FN) (HB imp AIM 96 :: LB)) by (right; exact INF).
    lazymatch type of FR with rw_cells _ _ _ ?cs =>
      assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -64) cs) by (eapply aheap_pres_rw_cells; [exact HPR1| exact FR| apply aclient_range_stack; cbn; lia]) end.
    assert (DC2 : rw_cells asegs m2 DST [C8 (Z_to_bv 64 0)])
      by (eapply aheap_pres_rw_cells; [exact HPR1| exact DC| eapply aclient_range_fake; [exact INF| lia| cbn; lia]]).
    assert (SCD2 : rw_cells asegs m2 (Z.shiftr DST 3 + 2147450880) [C1 (Z_to_bv 8 0)])
      by (eapply aheap_pres_rw_cells; [exact HPR1| exact SCD| eapply aclient_range_fake_sh; [exact INF| lia| lia| exact D8| lia]]).
    assert (VSH62 : rw_cells asegs m2 2147583984 [C1 (Z_to_bv 8 0)])
      by (eapply aheap_pres_rw_cells; [exact HPR1| exact VSH6| right; right; right; left; exists (0x103f50, 0x103fa0); split; [apply IMG_CI; cbn; tauto| cbn; unfold ASHOFF; lia]]).
    assert (VSH72 : rw_cells asegs m2 2147583985 [C1 (Z_to_bv 8 0)])
      by (eapply aheap_pres_rw_cells; [exact HPR1| exact VSH7| right; right; right; left; exists (0x103f50, 0x103fa0); split; [apply IMG_CI; cbn; tauto| cbn; unfold ASHOFF; lia]]).
    assert (VTD2 : rw_cells asegs m2 0x103f50 vtab_dom_cells)
      by (eapply aheap_pres_rw_cells; [exact HPR1| exact VTD| left; right; left; exists (0x103f50, 0x103fa0); split; [apply IMG_CI; cbn; tauto| cbn; lia]]).
    unfold vtab_dom_cells in VTD2.
    pose proof (client_rt_of_aheap AI _ _ _ _ _ AH2) as (GOT2 & RIC2 & REAL2 & SHB2 & SUA2 & INI2 & LAY2).
    clear FR DC SCD VSH6 VSH7 VTD GOT RIC REAL SHB SUA INI LAY GNT AH1.
    pose proof (rng_fp_le _ _ _ _ FPL1 RSTK) as RSTK1. pose proof (rng_fp_le _ _ _ _ FPL1 RI) as RI1. pose proof (rng_fp_le _ _ _ _ FPL1 RISH) as RISH1.
    pose proof (rng_fp_le _ _ _ _ FPL1 RSD) as RSD1. pose proof (rng_fp_le _ _ _ _ FPL1 RD) as RD1. clear RI RISH RSD RD.
    pose proof BRM as (BRM1 & BRM2 & BRM3 & BRM4). pose proof (ablk_lin _ _ BRM1) as (BRM1a & BRM1b & BRM1c & BRM1d). unfold AIMG_HI in BRM1a.
    band_ind BRM1 bM.
    assert (AM8 : AIM mod 8 = 0) by (Z.div_mod_to_equations; lia).
    pose proof (AI_blocks_disjoint AI _ _ _ _ _ _ _ AH2 (or_introl eq_refl) INF1 ltac:(discriminate)) as DJF. cbn [ab_addr ab_size] in DJF.
    destruct (blk_shc8 AI _ _ _ _ _ _ _ _ (AIM + 8) AH2 (or_introl eq_refl) ltac:(lia) ltac:(lia) ltac:(rewrite Z.add_mod by lia; rewrite AM8; reflexivity)) as (SM8 & RM8).
    destruct (blk_shc8 AI _ _ _ _ _ _ _ _ (AIM + 16) AH2 (or_introl eq_refl) ltac:(lia) ltac:(lia) ltac:(rewrite Z.add_mod by lia; rewrite AM8; reflexivity)) as (SM16 & RM16).
    destruct (blk_shc8 AI _ _ _ _ _ _ _ _ (AIM + 24) AH2 (or_introl eq_refl) ltac:(lia) ltac:(lia) ltac:(rewrite Z.add_mod by lia; rewrite AM8; reflexivity)) as (SM24 & RM24).
    destruct (blk_shc8 AI _ _ _ _ _ _ _ _ AIM AH2 (or_introl eq_refl) ltac:(lia) ltac:(lia) AM8) as (SM0 & RM0).
    pose proof (blk_shx_bounds AIM ltac:(lia) ltac:(lia)) as SB0. pose proof (blk_shx_bounds (AIM + 8) ltac:(lia) ltac:(lia)) as SB8.
    pose proof (blk_shx_bounds (AIM + 16) ltac:(lia) ltac:(lia)) as SB16. pose proof (blk_shx_bounds (AIM + 24) ltac:(lia) ltac:(lia)) as SB24.
    (* [comment removed for export] *)
    assert (BLKM' : rw_cells asegs m2 AIM (mk_CB_cells [8;4;4;8;4;4;18;6;40]%nat jim))
      by (pose proof (rw_cells_split_CB asegs m2 AIM [] 96%nat jim [] [8;4;4;8;4;4;18;6;40]%nat) as SPL;
          rewrite app_nil_r in SPL; cbn [app] in SPL; apply SPL; [exact BLKM| reflexivity]).
    cbn [mk_CB_cells] in BLKM'. clear BLKM.
    lazymatch type of BLKM' with rw_cells _ _ _ [?c0; ?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8] =>
      destruct (rw_cells_cut asegs _ AIM [c0; c1; c2; c3; c4; c5; c6; c7; c8] 6 BLKM') as [OBa OBb]; cbn [firstn skipn cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in OBa, OBb;
      clear BLKM' end.
    replace (AIM + 32) with (AIM + 32) in OBb by lia.
    lazymatch type of OBb with rw_cells _ _ _ [?c6; ?c7; ?c8] =>
      destruct (rw_cells_cut asegs _ (AIM + 32) [c6; c7; c8] 1 OBb) as [OB32 OBc]; cbn [firstn skipn cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in OB32, OBc;
      clear OBb end.
    lazymatch type of OBc with rw_cells _ _ _ [?c7; ?c8] =>
      destruct (rw_cells_cut asegs _ (AIM + 32 + 18) [c7; c8] 1 OBc) as [OB50 OB56]; cbn [firstn skipn cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in OB50, OB56;
      clear OBc end.
    replace (AIM + 32 + 18) with (AIM + 50) in OB50 by lia. replace (AIM + 32 + 18 + 6) with (AIM + 56) in OB56 by lia.
    apply implMA_from_evtF.
    pose proof (munch_refl [(lo, bv_unsigned sp); (DST, DST + 8); (AIM, AIM + 96)] m2) as MU2. pose proof (wmono_refl asegs m2) as WM2.
    steps_to 0x97418. zstep. if_cases K1; zify_cond K1; [exfalso; rewrite ?unsigned_lit in K1 by lia; lia| clear K1].
    steps_to 0x65f44.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (AH3 : AHEAP AI L RNG1 (aps_m s1') (HB imp AIM 96 :: LB) mx)
        by (eapply (AI_frame AI); [exact AH2| exact MU2| exact WM2|];
            apply Forall_cons; [left; left; cbn; lia|]; apply Forall_cons; [right; left; exists (mkABlock (ABFake fcls) FA FN); split; [exact INF1| cbn; lia]|];
            apply Forall_cons; [right; left; exists (HB imp AIM 96); split; [left; reflexivity| cbn; lia]| apply Forall_nil])
    end.
    destruct (blk_window_facts AI _ _ _ _ _ _ _ _ (AIM + 32) 18 AH3 (or_introl eq_refl) ltac:(lia) ltac:(lia) ltac:(lia)) as (APP32 & UNP32 & RW32 & (RLO32 & RHI32 & HU32 & WH32 & RH32)).
    eapply evtF_cut.
    { eapply asan_memset_spec with (lo := lo) (RLO2 := RLO32) (RHI2 := RHI32); rewrite ?unsigned_lit by lia;
        first [eassumption | (unfold KHIGH; lia) | lia | (eapply rng_sub'; [exact RSTK1| lia]) | (cbn; lia)]. }
    cbv beta. intros ms3 (y0 & y1 & y2 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & y3 & y4 & y5 & y6 & m3 & -> & MU3 & WM3 & MI3 & ST3 & SET3).
    rewrite ?unsigned_lit in MU3, ST3, SET3 by lia. rewrite (unsigned_lit (AIM + 32)), (unsigned_lit 18) in MU3 by lia. retlit.
    rewrite ?(unsigned_lit 18), ?(unsigned_lit 0) in SET3 by lia. change (Z.to_nat 18) with (8 + 10)%nat in SET3. change (0 mod 256) with 0 in SET3.
    apply rw_cells_run_split in SET3 as [S32 S40]. apply rw_cells_run_C8 in S32. change (Z.of_nat 8) with 8 in S40.
    trmA MU3 WM3.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (AH4 : AHEAP AI L RNG1 (aps_m s1') (HB imp AIM 96 :: LB) mx)
        by (eapply (AI_frame AI); [exact AH3| exact MU3| exact WM3|];
            apply Forall_cons; [left; left; cbn; lia|];
            apply Forall_cons; [right; left; exists (HB imp AIM 96); split; [left; reflexivity| cbn; lia]| apply Forall_nil])
    end.
    clear AH3 APP32 UNP32 RW32 HU32 WH32 RH32. boxm MU3. boxm WM3. boxm MU2. boxm WM2.
    pose proof (munch_refl [(lo, bv_unsigned sp); (DST, DST + 8); (AIM, AIM + 96)] m3) as MU4. pose proof (wmono_refl asegs m3) as WM4.
    steps_to 0x65f44.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (AH5 : AHEAP AI L RNG1 (aps_m s1') (HB imp AIM 96 :: LB) mx)
        by (eapply (AI_frame AI); [exact AH4| exact MU4| exact WM4|];
            apply Forall_cons; [left; left; cbn; lia|]; apply Forall_cons; [right; left; exists (mkABlock (ABFake fcls) FA FN); split; [exact INF1| cbn; lia]|];
            apply Forall_cons; [right; left; exists (HB imp AIM 96); split; [left; reflexivity| cbn; lia]| apply Forall_nil])
    end.
    destruct (blk_window_facts AI _ _ _ _ _ _ _ _ (AIM + 56) 40 AH5 (or_introl eq_refl) ltac:(lia) ltac:(lia) ltac:(lia)) as (APP56 & UNP56 & RW56 & (RLO56 & RHI56 & HU56 & WH56 & RH56)).
    eapply evtF_cut.
    { eapply asan_memset_spec with (lo := lo) (RLO2 := RLO56) (RHI2 := RHI56); rewrite ?unsigned_lit by lia;
        first [eassumption | (unfold KHIGH; lia) | lia | (eapply rng_sub'; [exact RSTK1| lia]) | (cbn; lia)]. }
    cbv beta. intros ms6 (z0 & z1 & z2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & z3 & z4 & z5 & z6 & m6 & -> & MU6 & WM6 & MI6 & ST6 & SET6).
    rewrite ?unsigned_lit in MU6, ST6, SET6 by lia. rewrite (unsigned_lit (AIM + 56)), (unsigned_lit 40) in MU6 by lia. retlit.
    rewrite ?(unsigned_lit (AIM + 56)), ?(unsigned_lit 40), ?(unsigned_lit 0) in SET6 by lia. change (Z.to_nat 40) with (8 + 32)%nat in SET6. change (0 mod 256) with 0 in SET6.
    apply rw_cells_run_split in SET6 as [S56 S64]. apply rw_cells_run_C8 in S56. change (Z.of_nat 8) with 8 in S64.
    change (32)%nat with (8 + 24)%nat in S64. apply rw_cells_run_split in S64 as [S64 S72]. apply rw_cells_run_C8 in S64. change (Z.of_nat 8) with 8 in S72.
    clear OB56.
    boxm MU4. boxm WM4.
    trmA MU6 WM6.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (AH6 : AHEAP AI L RNG1 (aps_m s1') (HB imp AIM 96 :: LB) mx)
        by (eapply (AI_frame AI); [exact AH5| exact MU6| exact WM6|];
            apply Forall_cons; [left; left; cbn; lia|];
            apply Forall_cons; [right; left; exists (HB imp AIM 96); split; [left; reflexivity| cbn; lia]| apply Forall_nil])
    end.
    clear AH4 AH5 APP56 UNP56 RW56 HU56 WH56 RH56. boxm MU6. boxm WM6.
    pose proof (munch_refl [(lo, bv_unsigned sp); (DST, DST + 8); (AIM, AIM + 96)] m6) as MU7. pose proof (wmono_refl asegs m6) as WM7.
    steps_to 0x974f8. zstep. if_cases K2; zify_cond K2; [exfalso; rewrite ?unsigned_lit in K2 by lia; lia| clear K2].
    steps_to 0xc0394.
    (* [comment removed for export] *)
    lazymatch goal with H : rw_cells _ _ AIM [?c0; ?c1; ?c2; ?c3; ?c4; ?c5] |- _ =>
      destruct (rw_cells_cut asegs _ AIM [c0; c1; c2; c3; c4; c5] 1 H) as [OB0 OB8]; cbn [firstn skipn cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in OB0, OB8;
      clear H end.
    lazymatch type of OB8 with rw_cells _ _ _ ?cs8 =>
      assert (IC8 : rw_cells asegs m5 (AIM + 8) (cs8 ++ [C8 (Z_to_bv 64 0)]))
        by (apply rw_cells_app_join; [exact OB8| cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; replace (AIM + 8 + 24) with (AIM + 32) by lia; exact S32]) end.
    cbn [app] in IC8. clear OB8 S32.
    apply evtF_done.
    lazymatch goal with |- implMA _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (AH7 : AHEAP AI L RNG1 (aps_m s1') (HB imp AIM 96 :: LB) mx)
        by (eapply (AI_frame AI); [exact AH6| exact MU7| exact WM7|];
            apply Forall_cons; [left; left; cbn; lia|]; apply Forall_cons; [right; left; exists (mkABlock (ABFake fcls) FA FN); split; [exact INF1| cbn; lia]|];
            apply Forall_cons; [right; left; exists (HB imp AIM 96); split; [left; reflexivity| cbn; lia]| apply Forall_nil])
    end.
    boxm MU7. boxm WM7.
    eapply implMA_bind.
    { eapply (asetcap_proof AI ONTA) with (lo := lo) (IMPL := AIM) (pim := imp) (len := len); try reflexivity; rewrite ?unsigned_lit by lia;
        first [exact AH7 | exact IC8 | exact HL | exact TRM | exact RSTK1 | exact RI1 | exact TP | eassumption
              | (left; reflexivity) | (eapply aps_ok_rest; [exact ARS1| exact AOK])
              | (unfold ASETCAP_STACK, OPNEW_NT_STACK_A, OPNEW_STACK_A, AMALLOC_STACK; lia) | lia]. }
    cbv beta. intros sip s2' RNG2 ms2 (FPL2 & v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m7 & -> & MI7 & ST7 & HPX & ARS2 & (ASI & jsi & BRS & AH8 & BLKS & IC9)).
    rewrite ?unsigned_lit in ST7 by lia. rewrite ?unsigned_lit in HPX by lia.
    retlit.
    assert (INF2 : In (mkABlock (ABFake fcls) FA FN) (HB sip ASI (SIDX_BYTES len) :: HB imp AIM 96 :: LB)) by (right; exact INF1).
    assert (INM2 : In (HB imp AIM 96) (HB sip ASI (SIDX_BYTES len) :: HB imp AIM 96 :: LB)) by (right; left; reflexivity).
    (* [comment removed for export] *)
    assert (TX : forall A cs, rw_cells asegs m5 A cs -> aclient_range CI (HB imp AIM 96 :: LB) (bv_unsigned sp + -64) A (Z.of_nat (cells_size cs)) ->
               (A + Z.of_nat (cells_size cs) <= AIM + 8 \/ AIM + 8 + 32 <= A) -> rw_cells asegs m7 A cs)
      by (intros A cs HC HR HD; exact (aheap_pres_x_rw_cells CI _ _ _ _ _ _ _ _ HPX HC HR HD)).
    lazymatch type of FR2 with rw_cells _ _ _ ?cs =>
      assert (FR7 : rw_cells asegs m7 (bv_unsigned sp + -64) cs) by (apply TX; [exact FR2| apply aclient_range_stack; cbn; lia| cbn; lia]) end.
    assert (DC7 : rw_cells asegs m7 DST [C8 (Z_to_bv 64 AIM)]) by (apply TX; [exact DC2| eapply aclient_range_fake; [exact INF1| lia| cbn; lia]| cbn; lia]).
    assert (SCD7 : rw_cells asegs m7 (Z.shiftr DST 3 + 2147450880) [C1 (Z_to_bv 8 0)])
      by (apply TX; [exact SCD2| eapply aclient_range_fake_sh; [exact INF1| lia| lia| exact D8| lia]| cbn; lia]).
    assert (VSH77 : rw_cells asegs m7 2147583985 [C1 (Z_to_bv 8 0)])
      by (apply TX; [exact VSH72| right; right; right; left; exists (0x103f50, 0x103fa0); split; [apply IMG_CI; cbn; tauto| cbn; unfold ASHOFF; lia]| cbn; lia]).
    lazymatch type of VTD2 with rw_cells _ _ _ ?cs =>
      assert (VTD7 : rw_cells asegs m7 0x103f50 cs)
        by (apply TX; [exact VTD2| left; right; left; exists (0x103f50, 0x103fa0); split; [apply IMG_CI; cbn; tauto| cbn; lia]| cbn; lia]) end.
    assert (OB07 : rw_cells asegs m7 AIM [C8 (Z_to_bv 64 1064784)]) by (apply TX; [exact OB0| right; left; exists (HB imp AIM 96); split; [left; reflexivity| cbn; lia]| cbn; lia]).
    assert (S407 : rw_cells asegs m7 (AIM + 32 + 8) [CB 10 (repeat (Z_to_bv 8 0) 10)]) by (apply TX; [exact S40| right; left; exists (HB imp AIM 96); split; [left; reflexivity| cbn; lia]| cbn; lia]).
    lazymatch type of OB50 with rw_cells _ _ _ ?cs =>
      assert (OB507 : rw_cells asegs m7 (AIM + 50) cs) by (apply TX; [exact OB50| right; left; exists (HB imp AIM 96); split; [left; reflexivity| cbn; lia]| cbn; lia]) end.
    assert (S567 : rw_cells asegs m7 (AIM + 56) [C8 (Z_to_bv 64 0)]) by (apply TX; [exact S56| right; left; exists (HB imp AIM 96); split; [left; reflexivity| cbn; lia]| cbn; lia]).
    assert (S647 : rw_cells asegs m7 (AIM + 56 + 8) [C8 (Z_to_bv 64 0)]) by (apply TX; [exact S64| right; left; exists (HB imp AIM 96); split; [left; reflexivity| cbn; lia]| cbn; lia]).
    assert (S727 : rw_cells asegs m7 (AIM + 56 + 8 + 8) [CB 24 (repeat (Z_to_bv 8 0) 24)]) by (apply TX; [exact S72| right; left; exists (HB imp AIM 96); split; [left; reflexivity| cbn; lia]| cbn; lia]).
    clear TX FR2 DC2 SCD2 VSH72 VSH62 VTD2 OB0 S40 OB50 S56 S64 S72 SM0 SM8 SM16 SM24.
    pose proof (client_rt_of_aheap AI _ _ _ _ _ AH8) as (GOT7 & RIC7 & REAL7 & SHB7 & SUA7 & INI7 & LAY7).
    destruct (blk_shc8 AI _ _ _ _ _ _ _ _ AIM AH8 INM2 ltac:(lia) ltac:(lia) AM8) as (SM07 & RM07).
    pose proof (rng_fp_le _ _ _ _ FPL2 RSTK1) as RSTK2. pose proof (rng_fp_le _ _ _ _ FPL2 RI1) as RI2. pose proof (rng_fp_le _ _ _ _ FPL2 RISH1) as RISH2.
    pose proof (rng_fp_le _ _ _ _ FPL2 RSD1) as RSD2. pose proof (rng_fp_le _ _ _ _ FPL2 RD1) as RD2.
    pose proof (rng_fp_le _ _ _ _ FPL2 RIM) as RIM2.
    clear RI1 RISH1 RSD1 RD1 RIM RM0 RM8 RM16 RM24.
    pose proof BRS as (BRS1 & BRS2 & BRS3 & BRS4). pose proof (ablk_lin _ _ BRS1) as (BRS1a & BRS1b & BRS1c & BRS1d). unfold AIMG_HI in BRS1a.
    (* [comment removed for export] *)
    apply implMA_from_evtF.
    steps_to 0xc04f4.
    release_frame FR7 ST7 (bv_unsigned sp).
    apply evtF_done.
    (* [comment removed for export] *)
    change (10%nat) with (8 + 2)%nat in S407. apply rw_cells_run_split in S407 as [S40a S48]. apply rw_cells_run_C8 in S40a.
    replace (AIM + 32 + 8) with (AIM + 40) in S40a by lia. replace (AIM + 32 + 8 + Z.of_nat 8) with (AIM + 48) in S48 by lia.
    lazymatch type of OB507 with rw_cells _ _ _ [CB 6 ?j6] =>
      assert (PF : rw_cells asegs m7 (AIM + 48) [CB 8 (repeat (Z_to_bv 8 0) 2 ++ j6)])
        by (eapply rw_cells_recast; [apply rw_cells_app_join; [exact S48| cbn [cells_size csize Nat.add]; replace (AIM + 48 + Z.of_nat 2) with (AIM + 50) by lia; exact OB507]
                                    | cbn [cells_wf cell_wf]; split; [| exact I]; rewrite length_app, repeat_length; destruct OB507 as [[[LJ _] _] _]; cbn [cells_wf cell_wf] in LJ; lia
                                    | cbn; rewrite !app_nil_r; reflexivity | reflexivity]) end.
    replace (AIM + 56 + 8) with (AIM + 64) in S647 by lia.
    lazymatch type of PF with rw_cells _ _ _ [CB 8 ?pf] =>
      assert (IC40 : rw_cells asegs m7 (AIM + 40) [C8 (Z_to_bv 64 0); CB 8 pf; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)])
        by (change [C8 (Z_to_bv 64 0); CB 8 pf; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] with ([C8 (Z_to_bv 64 0)] ++ [CB 8 pf] ++ [C8 (Z_to_bv 64 0)] ++ [C8 (Z_to_bv 64 0)]);
            apply rw_cells_app_join; [exact S40a| cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; replace (AIM + 40 + 8) with (AIM + 48) by lia];
            apply rw_cells_app_join; [exact PF| cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; replace (AIM + 48 + 8) with (AIM + 56) by lia];
            apply rw_cells_app_join; [exact S567| cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; replace (AIM + 56 + 8) with (AIM + 64) by lia; exact S647]) end.
    clear S40a S48 PF S567 S647.
    eapply implMA_bind.
    { eapply (asetdepth_proof AI ONTA) with (lo := lo) (IMPL := AIM) (pim := imp); try reflexivity; rewrite ?unsigned_lit by lia;
        first [exact AH8 | exact IC40 | exact TRM | exact RSTK2 | exact RI2 | exact TP | exact GOT7 | exact SHB7 | exact INM2 | exact ST7 | exact MI7
              | (eapply aps_ok_rest; [etransitivity; [exact ARS2| exact ARS1]| exact AOK])
              | (unfold ASETDEPTH_STACK, OPNEW_NT_STACK_A, OPNEW_STACK_A, AMALLOC_STACK; lia) | lia]. }
    cbv beta. intros [ocp iap] s3' RNG3 ms3
      (FPL3 & w0 & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m8 & -> & MI8 & ST8 & HPY & ARS3 & (AOC & AIA & joc & jia & BRO & BRI & AH9 & BLKO & BLKI & OB40)).
    cbn [fst snd] in AH9.
    apply implMA_ret. apply evtF_done. unfold acreate_post.
    split; [eapply fp_le_trans; [exact FPL1| eapply fp_le_trans; [exact FPL2| exact FPL3]]|].
    do 15 eexists. split; [reflexivity|].
    split; [exact MI8|]. split; [exact ST8|].
    assert (SPA : ATOP <= bv_unsigned sp) by lia.
    unfold boxed in MU2, WM2, MU3, WM3, MU4, WM4, MU6, WM6, MU7, WM7.
    split.
    { eapply aheap_pres_x_trans.
      { eapply aheap_pres_x_of_munch; [exact MU| exact WM|]. intros a Ha Hc Hx.
        destruct (aclient_lo_or_sp AI _ _ _ _ _ _ _ a AH (fun b Hb => Hb) Hc) as [Y|Y]; cbn; lia. }
      eapply aheap_pres_x_trans; [eapply aheap_pres_x_of_pres; [exact HPR1| lia| intros b Hb; exact Hb]|].
      eapply aheap_pres_x_trans.
      { eapply aheap_pres_x_of_munch; [exact MU2| exact WM2|]. intros a Ha Hc Hx.
        pose proof (fresh_not_client AI _ _ _ _ _ _ _ _ (bv_unsigned sp) a AH2 SPA Hc) as NF.
        destruct (aclient_lo_or_sp AI _ _ _ _ _ _ _ a AH (fun b Hb => Hb) Hc) as [Y|Y]; cbn; lia. }
      eapply aheap_pres_x_trans.
      { eapply aheap_pres_x_of_munch; [exact MU3| exact WM3|]. intros a Ha Hc Hx.
        pose proof (fresh_not_client AI _ _ _ _ _ _ _ _ (bv_unsigned sp) a AH2 SPA Hc) as NF.
        destruct (aclient_lo_or_sp AI _ _ _ _ _ _ _ a AH (fun b Hb => Hb) Hc) as [Y|Y]; cbn; lia. }
      eapply aheap_pres_x_trans.
      { eapply aheap_pres_x_of_munch; [exact MU4| exact WM4|]. intros a Ha Hc Hx.
        pose proof (fresh_not_client AI _ _ _ _ _ _ _ _ (bv_unsigned sp) a AH2 SPA Hc) as NF.
        destruct (aclient_lo_or_sp AI _ _ _ _ _ _ _ a AH (fun b Hb => Hb) Hc) as [Y|Y]; cbn; lia. }
      eapply aheap_pres_x_trans.
      { eapply aheap_pres_x_of_munch; [exact MU6| exact WM6|]. intros a Ha Hc Hx.
        pose proof (fresh_not_client AI _ _ _ _ _ _ _ _ (bv_unsigned sp) a AH2 SPA Hc) as NF.
        destruct (aclient_lo_or_sp AI _ _ _ _ _ _ _ a AH (fun b Hb => Hb) Hc) as [Y|Y]; cbn; lia. }
      eapply aheap_pres_x_trans.
      { eapply aheap_pres_x_of_munch; [exact MU7| exact WM7|]. intros a Ha Hc Hx.
        pose proof (fresh_not_client AI _ _ _ _ _ _ _ _ (bv_unsigned sp) a AH2 SPA Hc) as NF.
        destruct (aclient_lo_or_sp AI _ _ _ _ _ _ _ a AH (fun b Hb => Hb) Hc) as [Y|Y]; cbn; lia. }
      eapply aheap_pres_x_trans.
      { eapply aheap_pres_x_weaken; [exact HPX| lia| intros b Hb; right; exact Hb|]. intros a Hc Hy Hx.
        pose proof (fresh_not_client AI _ _ _ _ _ _ _ _ (bv_unsigned sp) a AH2 SPA Hc) as NF. lia. }
      eapply aheap_pres_x_weaken; [exact HPY| lia| intros b Hb; right; right; exact Hb|]. intros a Hc Hy Hx.
      pose proof (fresh_not_client AI _ _ _ _ _ _ _ _ (bv_unsigned sp) a AH2 SPA Hc) as NF. lia. }
    split; [rewrite ARS3, ARS2, ARS1; reflexivity|].
    clear MU WM MU2 WM2 MU3 WM3 MU4 WM4 MU6 WM6 MU7 WM7 HPR1 HPX.
    assert (DC8 : rw_cells asegs m8 DST [C8 (Z_to_bv 64 AIM)])
      by (eapply aheap_pres_x_rw_cells; [exact HPY| exact DC7| eapply aclient_range_fake; [exact INF2| lia| cbn; lia]| cbn; lia]).
    assert (OB08 : rw_cells asegs m8 AIM [C8 (Z_to_bv 64 1064784)])
      by (eapply aheap_pres_x_rw_cells; [exact HPY| exact OB07| right; left; exists (HB imp AIM 96); split; [exact INM2| cbn; lia]| cbn; lia]).
    lazymatch type of IC9 with rw_cells _ _ _ ?cs =>
      assert (IC98 : rw_cells asegs m8 (AIM + 8) cs)
        by (eapply aheap_pres_x_rw_cells; [exact HPY| exact IC9| right; left; exists (HB imp AIM 96); split; [exact INM2| cbn; lia]| cbn; lia]) end.
    assert (S728 : rw_cells asegs m8 (AIM + 72) [CB 24 (repeat (Z_to_bv 8 0) 24)])
      by (replace (AIM + 72) with (AIM + 56 + 8 + 8) by lia;
          eapply aheap_pres_x_rw_cells; [exact HPY| exact S727| right; left; exists (HB imp AIM 96); split; [exact INM2| cbn; lia]| cbn; lia]).
    pose proof (new_blk_apart AI _ _ _ _ _ _ _ _ (HB imp AIM 96) AH8 (or_introl eq_refl)) as DSI. cbn [ab_addr ab_size] in DSI.
    lazymatch type of BLKS with rw_cells _ _ _ ?cs =>
      assert (BLKS8 : rw_cells asegs m8 ASI cs)
        by (eapply aheap_pres_x_rw_cells; [exact HPY| exact BLKS| right; left; exists (HB sip ASI (SIDX_BYTES len)); split; [left; reflexivity| cbn; lia]| cbn; lia]) end.
    change (24%nat) with (8 + 16)%nat in S728. apply rw_cells_run_split in S728 as [S72a S80]. apply rw_cells_run_C8 in S72a.
    change (16%nat) with (8 + 8)%nat in S80. apply rw_cells_run_split in S80 as [S80a S88]. apply rw_cells_run_C8 in S80a. apply rw_cells_run_C8 in S88.
    replace (AIM + 72 + Z.of_nat 8) with (AIM + 80) in S80a by lia. replace (AIM + 72 + Z.of_nat 8 + Z.of_nat 8) with (AIM + 88) in S88 by lia.
    lazymatch type of OB40 with rw_cells _ _ _ [?c0; CB 8 (repeat _ 2 ++ ?q3); ?c2; ?c3] =>
      assert (OB40r : rw_cells asegs m8 (AIM + 40) [c0; C2 (Z_to_bv 64 0); CB 6 q3; c2; c3])
        by (eapply rw_cells_recast; [exact OB40| destruct OB40 as [[[_ [LQ _]] _] _]; cbn [cells_wf cell_wf] in LQ |- *; rewrite length_app, repeat_length in LQ;
                                     repeat split; lia
                                   | cbn [cells_bytes cbytes]; rewrite (le2_zero_run); rewrite <- ?app_assoc; reflexivity| reflexivity]) end.
    lazymatch type of OB08 with rw_cells _ _ _ ?cs0 =>
    lazymatch type of IC98 with rw_cells _ _ _ ?cs1 =>
    lazymatch type of OB40r with rw_cells _ _ _ ?cs2 =>
      assert (J : rw_cells asegs m8 AIM (cs0 ++ cs1 ++ cs2 ++ [C8 (Z_to_bv 64 0)] ++ [C8 (Z_to_bv 64 0)] ++ [C8 (Z_to_bv 64 0)]))
        by (apply rw_cells_app_join; [exact OB08|]; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
            apply rw_cells_app_join; [exact IC98|]; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
            replace (AIM + 8 + 32) with (AIM + 40) by lia;
            apply rw_cells_app_join; [exact OB40r|]; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
            replace (AIM + 40 + 32) with (AIM + 72) by lia;
            apply rw_cells_app_join; [exact S72a|]; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
            replace (AIM + 72 + 8) with (AIM + 80) by lia;
            apply rw_cells_app_join; [exact S80a|]; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
            replace (AIM + 80 + 8) with (AIM + 88) by lia; exact S88)
    end end end.
    cbn [app] in J.
    lazymatch type of IC98 with rw_cells _ _ _ [_; CB 4 ?q1; _; _; CB 4 ?q2; _] =>
    lazymatch type of OB40r with rw_cells _ _ _ [_; _; CB 6 ?q3; _; _] =>
    lazymatch type of BLKS8 with rw_cells _ _ _ [_; CB _ ?j1] =>
    lazymatch type of BLKO with rw_cells _ _ _ [CB _ ?j2] =>
    lazymatch type of BLKI with rw_cells _ _ _ [CB _ ?j3] =>
      exists AIM, ASI, AOC, AIA, q1, q2, q3, j1, j2, j3
    end end end end end.
    split; [exact BRM|]. split; [exact BRS|]. split; [exact BRO|]. split; [exact BRI|].
    split; [exact AH9|]. split; [exact DC8|].
    split; [unfold aimpl_cells, AVTAB_DOM; exact J|].
    split; [exact BLKS8|]. split; [exact BLKO| exact BLKI].
  Qed.
End Proof.
End S.
End CANSEC1.
