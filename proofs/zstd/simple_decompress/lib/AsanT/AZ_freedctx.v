(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Bytes.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit ZdFrameW ZdWalkKit ZdDctxRep.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed Harness ProgA AsanProgDeps.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF ITreeA SysStepF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXGoF KXAsan KXAutoA.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells AProto ABase ABytes AMalloc_iface AProg_kit
     AZ_kit AZ_frame_iface AZ_dframe_iface AZ_dctx_iface_m AZ_libc_iface AZ_libc AZ_kx AZ_harness_kit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac kxa_norm ::= unfold shspan in *.

Section CANSEC1. Context {rc : runConstT}.
Section Free.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).

  Lemma in_lb_remove : forall p LB b, In b (lb_remove p LB) -> In b LB /\ ab_kind b <> ABHeap p.
  Proof.
    intros p LB b. unfold lb_remove. induction LB as [|x LB IH].
    { intros H. exfalso. revert H. rewrite filter_nil. intros H; exact H. }
    rewrite filter_cons. destruct (decide _) as [Y|N]; intros H.
    - destruct H as [<-|H]; [| destruct (IH H) as [H1 H2]; split; [right; exact H1| exact H2]].
      split; [left; reflexivity|]. intros E. revert Y. rewrite E. cbn [abkind_eqb]. rewrite N.eqb_refl. cbn. intros Y; exact Y.
    - destruct (IH H) as [H1 H2]. split; [right; exact H1| exact H2].
  Qed.

  (* [comment removed for export] *)
  Lemma aheap_pres_freed : forall L RNG st LB m m' p A n lo SP,
    AHEAP AI L RNG st LB m -> In (HB p A n) LB -> munch [(A, A + n); (lo, SP)] m m' -> wmono bsegs m m' ->
    ATOP + 4096 <= lo -> lo <= SP -> SP <= 2^47 ->
    aheap_pres CI (lb_remove p LB) SP m m'.
  Proof.
    intros L RNG st LB m m' p A n lo SP AH HIN MU WM BOT LOSP TOP.
    pose proof (AI_block AI _ _ _ _ _ p A n AH HIN) as (_ & (BR1 & BR2 & BR3 & BR4) & _).
    pose proof (ablk_lin _ _ BR1) as (BL1 & BL2 & BL3 & BL4). unfold AIMG_HI in BL1.
    pose proof (AI_aci_img AI) as CIB.
    assert (RM : forall b, In b (lb_remove p LB) -> In b LB /\ HB p A n <> b).
    { intros b Hb. destruct (in_lb_remove p LB b Hb) as [Hb' Hk]. split; [exact Hb'|]. intros E. apply Hk. rewrite <- E. reflexivity. }
    eapply aheap_pres_of_munch; [exact MU| exact WM|]. intros a Hc. cbn [outside].
    destruct Hc as [Hc|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
    - split; [lia|]. split; [lia| exact I].
    - pose proof (CIB iv Hiv). unfold AIMG_HI in *. split; [lia|]. split; [lia| exact I].
    - destruct (RM b Hb) as [Hb' NE].
      pose proof (AI_blocks_disjoint AI _ _ _ _ _ (HB p A n) b AH HIN Hb' NE) as DJ. cbn [ab_addr ab_size] in DJ.
      pose proof (AI_block_bounds AI _ _ _ _ _ b AH Hb') as BB.
      split; [lia|]. split; [lia| exact I].
    - assert (A47 : 0 <= a' < 2^47).
      { destruct Ha' as [X|[(iv & Hiv & Hr)|(c & FA & fn & Hb & Hr)]]; [lia| pose proof (CIB iv Hiv); pose proof (AI_aci_lo AI iv Hiv); unfold AIMG_HI in *; lia|].
        destruct (RM _ Hb) as [Hb' _].
        pose proof (AI_block_bounds AI _ _ _ _ _ _ AH Hb'). cbn in *. unfold AIMG_HI in *. atop_facts. lia. }
      pose proof (shad_in_band a' A47) as SB. pose proof (ablk_clear_band _ _ (shad a') BR1) as CB0. unfold KLS in *.
      split; [intros X; apply CB0; [lia| exact X]|].
      split; [rewrite shad_div; unfold ASHOFF; atop_facts; clear - A47 BOT H; Z.div_mod_to_equations; lia| exact I].
  Qed.

  Lemma fd_ahull_wmono : forall RNG m m' X n, ahull RNG m X n -> wmono bsegs m m' -> ahull RNG m' X n.
  Proof.
    intros RNG m m' X n (RLO & RHI & H1 & H2 & H3 & H4 & H5 & H6 & W & R) WM. exists RLO, RHI.
    repeat (split; [assumption|]). split; [eapply wr_at_transport; [exact W| exact WM]| exact R].
  Qed.

  Theorem zd_freedctx_proofA : zd_freedctx_stmtA AI.
  Proof.
    unfold zd_freedctx_stmtA. intros until lo. intros AH HIN DA MI ST BOT LOS TOPS SP16 TP A0 HU RSTK RI AOK.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold FREEDCTX_STACK_A, AFREE_STACK in LOS.
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    pose proof (AI_layout AI _ _ _ _ _ AH) as (LAY1 & LAY2 & LAY3 & LAY4 & _).
    destruct (block_geom AI _ _ _ _ _ _ _ _ AH HIN) as (ABR & _ & ATOPB & A16 & ALO). unfold DCTX_SIZE, AIMG_HI in *.
    assert (AA : A + 95992 <= 0x7fff7000 \/ 0x10007fff8000 <= A) by (unfold ablk, AIMG_HI, KLS in ABR; lia).
    destruct (areg_block AI _ _ _ _ _ p A 95992 A 95992 AH HIN ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (_ & UA & RA & RAS).
    pose proof (ahull_block AI _ _ _ _ _ p A 95992 (A + 30184) 16 AH HIN ltac:(lia) ltac:(lia) ltac:(lia)) as HUL.
    pose proof (art_of_aheap AI _ _ _ _ _ AH) as ART. destruct ART as (GOT & RIC & SHB & INI & LAYC & REAL).
    subst tp a0.
    (* [comment removed for export] *)
    destruct DA as (llt & mlt & oft & huf & pde & pfx & vst & dend & expd & fp & pcs & dsz & bt & stg & le & fe & xs & ws & jhb & ovd & dcb & dce & trace &
                    PTRS & H1 & FP & H3 & XS & [H5C H5L] & H5OK & TX & OWN).
    destruct H5OK as (_ & _ & _ & _ & _ & K_CF & K_CO & K_SS & K_DL & K_DD & K_DU & K_DS & K_IB).
    h5_open ws H5L. unfold wz0 in *. subst.
    destruct OWN as [OWN1 OWN2]. destruct FP as [FP FPL]. destruct XS as [XS XSL]. unfold dctx_ptrs in PTRS. unfold dctx_h1 in H1.
    unfold dctx_h3 in H3. unfold dctx_tx in TX.
    (* [comment removed for export] *)
    destruct (rw_cells_forget _ _ _ _ FP) as [jfp FPB]. rewrite FPL in FPB. clear FP.
    destruct (rw_cells_forget _ _ _ _ XS) as [jxs XSB]. rewrite XSL in XSB. clear XS.
    apply implMA_from_evtF.
    pose proof (munch_refl [(A, A + 95992); (lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    carve_frame 64%nat ST. unfold APZD_FREEDCTX.
    (* [comment removed for export] *)
    remember (bv_unsigned sp) as SPV eqn:ESP.
    replace sp with (Z_to_bv 64 SPV) by (subst SPV; apply Z_to_bv_bv_unsigned).
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ ?Q _ => remember Q as KQ eqn:EKQ end.
    (* [comment removed for export] *)
    kx_autoFLAx [KAUnp (A + 30096) 276; KAApp (A + 30096) 276; KAApp (SPV - 64) 64] [] 60%nat
      [KZRange A 0x605000 (2^47 - 95992); KZAlign A 16; KZRange SPV 0x10007fff8000 (2^47 - 1);
       KZWr (SPV - 64) 64; KZDisj (SPV - 64) 64 (A + 30096) 276]
      [(SPV - 64, 64); (A + 30096, 276)] [(SPV - 64, 64); (A + 30096, 276)].
    all: try kx_cell_lit. all: try kx_acc RI. all: try kx_z.
    all: kx_mem.
    (* [comment removed for export] *)
    carve_frame 32%nat ST.
    do 5 zstep. zstep. if_cases KD; zify_cond KD; [| exfalso; exact (KD eq_refl)].
    do 6 zstep. zstep.
    lazymatch goal with FRc : rw_cells _ ?mc (SPV + -96) _, STc : stk _ ?mc lo _ |- _ => release_frame FRc STc (SPV + -64) end.
    (* [comment removed for export] *)
    unp_now UA MU UA3.
    (* [comment removed for export] *)
    replace ((A + 30184) mod 18446744073709551616 / 8 + 2147450880) with (2147450880 + (A + 30184) / 8) by (rewrite Z.mod_small by lia; lia).
    kx_autoFLAx [KAUnp (A + 30096) 276; KAApp (A + 30096) 276; KAShp (2147450880 + (A + 30184) / 8) (A + 30184)] [] 100%nat
      [KZRange A 0x605000 (2^47 - 95992); KZAlign A 16; KZRange SPV 0x10007fff8000 (2^47 - 1); KZWr (A + 30096) 276]
      [(A + 30096, 276)] [(A + 30096, 276)].
    all: try kx_cell_lit. all: try kx_acc RI. all: try kx_z.
    all: kx_mem. clear UA3.
    unp_now UA MU UA4.
    lazymatch goal with H : rw_cells bsegs _ (A + 30096) ?cs |- _ =>
      rewrite <- (firstn_skipn 14 cs) in H; apply (proj1 (rw_cells_app _ _ _ _ _)) in H; destruct H as [H5P H5W];
      cbn [firstn skipn cells_size csize Nat.add app] in H5P, H5W end.
    lazymatch type of H5W with rw_cells _ _ _ ?cs =>
      rewrite <- (firstn_skipn 2 cs) in H5W; apply (proj1 (rw_cells_app _ _ _ _ _)) in H5W; destruct H5W as [H5M H5Q];
      cbn [firstn skipn cells_size csize Nat.add app] in H5M, H5Q end.
    replace (A + 30096 + Z.of_nat 88 + Z.of_nat 16) with (A + 30200) in H5Q by lia.
    replace (A + 30096 + Z.of_nat 88) with (A + 30184) in H5M by lia.
    destruct (rw_cells_forget _ _ _ _ H5M) as [jm HJ]; clear H5M. cbn [cells_size csize Nat.add] in HJ.
    call (zd_memsetZ_proofA RNG (A + 30184) 16 0 (SPV + -64));
      [ exact HJ | lia | lia | eassumption | lia | lia | lia
      | apply ablk_app_blk; [eapply ablk_sub; [exact ABR| lia| lia] | lia]
      | eapply aro_sub; [split; [exact UA4| split; [exact RA| exact RAS]] | lia | lia | lia]
      | eapply fd_ahull_wmono; [exact HUL| exact WM]
      | split; [assumption|]; repeat (split; [assumption|]); assumption
      | split; [unfold KHIGH; lia|]; split; [eapply rng_sub; [exact RSTK| lia| lia] | exact RI]
      | eassumption
      | reflexivity | reflexivity | reflexivity | ].
    clear UA4.
    lazymatch goal with H : rw_cells _ ?mm (A + 30184) [CB _ (repeat _ _)] |- _ =>
      assert (Z2 : rw_cells bsegs mm (A + 30184) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)])
        by (eapply rw_cells_recell; [exact H | cbn; tauto | reflexivity]); clear H end.
    lazymatch type of H5P with rw_cells _ ?mm _ ?cp => lazymatch type of H5Q with rw_cells _ _ _ ?cq =>
      assert (H5W : rw_cells bsegs mm (A + 30096) (cp ++ [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ++ cq));
      [ apply (proj2 (rw_cells_app _ _ _ _ _)); split; [exact H5P|]; cbn [cells_size csize Nat.add];
        apply (proj2 (rw_cells_app _ _ _ _ _)); split; [replace (A + 30096 + Z.of_nat 88) with (A + 30184) by lia; exact Z2|];
        cbn [cells_size csize Nat.add];
        replace (A + 30096 + Z.of_nat 88 + Z.of_nat 16) with (A + 30200) by lia; exact H5Q |]
    end end.
    cbn [app] in H5W. clear H5P Z2 H5Q.
    unp_now UA MU UA5.
    kx_autoFLAx [KAUnp (A + 30096) 276; KAApp (A + 30096) 276] [] 100%nat
      [KZRange A 0x605000 (2^47 - 95992); KZAlign A 16; KZRange SPV 0x10007fff8000 (2^47 - 1); KZWr (A + 30096) 276]
      [(A + 30096, 276)] [(A + 30096, 276)].
    all: try kx_cell_lit. all: try kx_acc RI. all: try kx_z.
    all: kx_mem. clear UA5.
    (* [comment removed for export] *)
    subst KQ. apply evtF_done.
    lazymatch type of MU with munch _ _ ?mc =>
      assert (AHf : AHEAP AI L RNG (aps_m s) LB mc)
        by (eapply (AI_frame AI); [exact AH| exact MU| exact WM|]; constructor;
            [cbn [fst snd]; right; left; exists (HB p A 95992); split; [exact HIN| cbn; lia] | constructor; [cbn [fst snd]; left; left; lia| constructor]]) end.
    eapply implMA_post_evtF.
    { eapply (implMA_afree_call AI L RNG) with (lo := lo) (tr := []); rewrite ?unsigned_lit by lia;
        first [ exact AHf | exact HIN | eassumption | reflexivity
              | (apply aunw_data; rewrite ?unsigned_lit by lia; [lia | lia | unfold AFREEDCTX_FRET in HU; exact HU])
              | (unfold AFREE_STACK, AFREE_PC; cbn; lia)
              | (clear - SP16 RSP ESP; subst SPV; Z.div_mod_to_equations; lia) ]. }
    cbv beta. intros [] s' RNG' ms1 [REST PO].
    destruct PO as (LE1 & y0 & y1 & y2 & ya0 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & mZ & -> & MIZ & STZ & HPRZ & AHZ).
    rewrite ?unsigned_lit in STZ, HPRZ by lia.
    replace (ret_pc (Z_to_bv 64 537016)) with (Z_to_bv 64 537016) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    (* [comment removed for export] *)
    lazymatch goal with FRc : rw_cells _ ?mo (SPV + -64) [_; _; _; _; _; _; _; C8 ra] |- _ =>
      assert (FRZ : rw_cells bsegs mZ (SPV + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
        by (eapply aheap_pres_rw_cells; [exact HPRZ| exact FRc| left; left; cbn; lia]) end.
    pose proof (rng_fp_le _ _ _ _ LE1 RSTK) as RSTKZ. pose proof (rng_fp_le _ _ _ _ LE1 RI) as RIZ.
    (* [comment removed for export] *)
    zstep. do 8 zstep. zstep.
    release_frame FRZ STZ SPV.
    zstep.
    apply evtF_done. unfold zd_freedctx_postA. rewrite ?unsigned_lit by lia. split; [exact LE1|].
    do 14 eexists. exists mZ. split; [reflexivity|].
    split; [exact MIZ|]. split; [exact STZ|].
    split.
    { lazymatch type of HPRZ with aheap_pres _ _ _ ?mo _ =>
        eapply aheap_pres_trans;
        [ eapply (aheap_pres_freed L RNG (aps_m s) LB m mo p A 95992 lo SPV AH HIN); [assumption| assumption| lia| lia| lia]
        | eapply aheap_pres_weaken; [exact HPRZ| lia| intros bb Hbb; exact Hbb] ] end. }
    split; [exact REST| exact AHZ].
  Qed.
End Free.
End CANSEC1.
