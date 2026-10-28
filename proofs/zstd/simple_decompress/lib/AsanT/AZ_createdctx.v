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
     AZ_kit AZ_frame_iface AZ_dframe_iface AZ_dctx_iface_m AZ_libc_iface AZ_libc AZ_kx AZ_harness_kit AH_fse_malloc.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import ZdCellKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac kxa_norm ::= unfold shspan in *.


(* [comment removed for export] *)
Lemma le4_of_bytes : forall bs : list byte, length bs = 4%nat -> le4 (le_bytes_to_word bs) = bs.
Proof.
  intros bs HL. unfold le4, le_bytes_to_word.
  pose proof (le_val_range _ (bytes_ok_map bs)) as HR. rewrite length_map, HL in HR.
  change (256 ^ Z.of_nat 4) with 4294967296 in HR. rewrite <- bytes_le_to_Z_le_val in HR.
  rewrite unsigned_lit by lia. rewrite <- HL. apply Z_to_le_bytes_to_Z.
Qed.

Lemma cb4_as_c4 : forall segs m A pre j post,
  rw_cells segs m A (pre ++ CB 4 j :: post) -> exists w, rw_cells segs m A (pre ++ C4 w :: post).
Proof.
  intros segs m A pre j post H. exists (le_bytes_to_word j).
  pose proof H as [[WF _] _]. apply cells_wf_app in WF. destruct WF as [WF1 [WFJ WF2]]. cbn in WFJ.
  eapply rw_cells_recell; [exact H | |].
  - apply cells_wf_app. split; [exact WF1|]. split; [exact I| exact WF2].
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. rewrite le4_of_bytes by exact WFJ. reflexivity.
Qed.

(* [comment removed for export] *)
Ltac wordify_go H segs m A pre rest :=
  lazymatch rest with
  | CB 8 ?j :: ?post =>
      let w := fresh "w" in let H' := fresh "WH" in
      destruct (cb8_as_c8 segs m A pre j post H) as [w H']; clear H; rename H' into H;
      let pre' := eval cbn [app] in (pre ++ [C8 w]) in wordify_go H segs m A pre' post
  | CB 4 ?j :: ?post =>
      let w := fresh "w" in let H' := fresh "WH" in
      destruct (cb4_as_c4 segs m A pre j post H) as [w H']; clear H; rename H' into H;
      let pre' := eval cbn [app] in (pre ++ [C4 w]) in wordify_go H segs m A pre' post
  | ?c :: ?post => let pre' := eval cbn [app] in (pre ++ [c]) in wordify_go H segs m A pre' post
  | nil => cbn [app] in H
  end.
Ltac wordify H := lazymatch type of H with rw_cells ?segs ?m ?A ?cs => wordify_go H segs m A (@nil cell) cs end.

(* [comment removed for export] *)
Ltac znat_norm H :=
  repeat match type of H with context [Z.of_nat ?n] =>
    let v := eval vm_compute in (Z.of_nat n) in change (Z.of_nat n) with v in H end.
Ltac zaddr_norm H :=
  znat_norm H;
  repeat match type of H with
  | rw_cells _ _ (?a + ?x + ?y) _ => let v := eval vm_compute in (x + y) in replace (a + x + y) with (a + v) in H by lia
  | stk _ _ (?a + ?x + ?y) _ => let v := eval vm_compute in (x + y) in replace (a + x + y) with (a + v) in H by lia
  | stk _ _ _ (?a + ?x + ?y) => let v := eval vm_compute in (x + y) in replace (a + x + y) with (a + v) in H by lia
  end.

(* [comment removed for export] *)
Ltac gen_junk H :=
  repeat match type of H with context [CB ?n (take ?a ?b)] =>
    let j := fresh "jk" in set (j := take a b) in H; clearbody j end.

(* [comment removed for export] *)
Ltac csplit H n H1 :=
  lazymatch type of H with rw_cells _ _ _ ?cs =>
    rewrite <- (firstn_skipn n cs) in H; apply (proj1 (rw_cells_app _ _ _ _ _)) in H; destruct H as [H1 H];
    cbn [firstn skipn cells_size csize Nat.add app] in H1, H; zaddr_norm H end.

(* [comment removed for export] *)
Definition cw (c : cell) : word := match c with C8 w => w | C4 w => w | _ => wz0 end.

Section CANSEC1. Context {rc : runConstT}.
Section Create.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).

  (* [comment removed for export] *)
  Lemma ahc_of : forall L RNG st p A LB m2 mc lo SPV,
    AHEAP AI L RNG st (HB p A 95992 :: LB) m2 -> munch [(A, A + 95992); (lo, SPV)] m2 mc -> wmono bsegs m2 mc ->
    ATOP + 4096 <= lo -> SPV <= 2^47 -> AHEAP AI L RNG st (HB p A 95992 :: LB) mc.
  Proof.
    intros L RNG st p A LB m2 mc lo SPV AH MU WM BOT TOP.
    eapply (AI_frame AI); [exact AH| exact MU| exact WM|].
    constructor; [| constructor; [| constructor]]; cbn [fst snd].
    - right; left. exists (HB p A 95992). split; [left; reflexivity| cbn; lia].
    - left; left. lia.
  Qed.

  Lemma uac_of : forall A m2 mc lo SPV,
    unpoisoned m2 A (A + 95992) -> munch [(A, A + 95992); (lo, SPV)] m2 mc -> ablk A (A + 95992) -> ATOP + 4096 <= lo ->
    unpoisoned mc A (A + 95992).
  Proof.
    intros A m2 mc lo SPV U MU BR BOT. pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    pose proof (ablk_lin _ _ BR) as (L1 & L2 & L3 & L4). pose proof (ablk_disj_band _ _ BR) as DB. unfold AIMG_HI, KLS in *.
    eapply unpoisoned_munch; [exact U | exact MU |]. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF.
    repeat split; Z.div_mod_to_equations; lia.
  Qed.

  (* [comment removed for export] *)
  Ltac msetA M MZ :=
    lazymatch type of M with rw_cells _ ?mc (?A + ?off) [CB ?n _] =>
    lazymatch goal with AH2 : AHEAP _ ?L ?RNG' ?st (HB ?p A 95992 :: ?LB) ?m2, MU2 : munch _ ?m2 mc, WM2 : wmono _ ?m2 mc,
                        UA : unpoisoned ?m2 A _, BR1 : ablk A _, BOT : ATOP + 4096 <= ?lo, RA : rng ?RNG' A 95992, RAS' : rng ?RNG' (shad A) _,
                        LE : fp_le ?RNG ?RNG', RSTK : rng ?RNG ?lo _, RI : rng_aimg ?RNG |- _ =>
      let UAc := fresh "UAc" in let AHc := fresh "AHc" in let nz := eval vm_compute in (Z.of_nat n) in
      pose proof (uac_of A m2 mc lo _ UA MU2 BR1 BOT) as UAc;
      pose proof (ahc_of L RNG' st p A LB m2 mc lo _ AH2 MU2 WM2 BOT ltac:(lia)) as AHc;
      call (zd_memsetZ_proofA RNG' (A + off) nz 0);
      [ exact M
      | lia | lia
      | eassumption
      | lia | lia | lia
      | apply ablk_app_blk; [eapply ablk_sub; [exact BR1| lia| lia] | lia]
      | eapply aro_sub; [split; [exact UAc| split; [exact RA| exact RAS']] | lia | lia | lia]
      | exact (ahull_block AI _ _ _ _ _ p A 95992 (A + off) nz AHc ltac:(left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia))
      | split; [assumption|]; repeat (split; [assumption|]); assumption
      | split; [unfold KHIGH; lia|]; split; [eapply rng_sub; [exact (rng_fp_le _ _ _ _ LE RSTK)| lia| lia] | exact (rng_fp_le _ _ _ _ LE RI)]
      | eassumption
      | reflexivity | reflexivity | reflexivity | ];
      clear UAc AHc;
      lazymatch goal with H : rw_cells _ _ (A + off) [CB _ (repeat _ _)] |- _ => rename H into MZ end
    end end.

  Theorem zd_createdctx_proofA : zd_createdctx_stmtA AI.
  Proof.
    unfold zd_createdctx_stmtA. intros until lo. intros AH MI ST BOT LOS TOPS SP16 TP S0A HU RSTK RI AOK.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold CREATEDCTX_STACK_A, AMALLOC_STACK in LOS.
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    pose proof (AI_layout AI _ _ _ _ _ AH) as (LAY1 & LAY2 & LAY3 & LAY4 & _).
    pose proof (art_of_aheap AI _ _ _ _ _ AH) as ART. destruct ART as (GOT & RIC & SHB & INI & LAYC & REAL).
    subst tp.
    apply implMA_from_evtF.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    remember (bv_unsigned sp) as SPV eqn:ESP.
    replace sp with (Z_to_bv 64 SPV) by (subst SPV; apply Z_to_bv_bv_unsigned).
    carve_frame 64%nat ST. unfold APZD_CREATEDCTX.
    lazymatch goal with |- evtF _ _ ?Q _ => remember Q as KQ eqn:EKQ end.
    (* [comment removed for export] *)
    kx_autoFLAx [KAApp (SPV - 64) 64] [] 30%nat
      [KZRange SPV 0x10007fff8000 (2^47 - 1); KZWr (SPV - 64) 64]
      [(SPV - 64, 64)] [(SPV - 64, 64)].
    all: try kx_cell_lit. all: try kx_acc RI. all: try kx_z.
    all: kx_mem.
    subst KQ. apply evtF_done.
    lazymatch type of MU with munch _ _ ?mc =>
      assert (AH1 : AHEAP AI L RNG (aps_m s) LB mc)
        by (eapply (AI_frame AI); [exact AH| exact MU| exact WM|]; constructor; [cbn [fst snd]; left; left; lia| constructor]) end.
    eapply implMA_post_evtF.
    { eapply (implMA_amalloc_call AI L RNG) with (lo := lo) (tr := []); rewrite ?unsigned_lit by lia;
        first [ exact AH1 | eassumption | reflexivity
              | (unfold AREQMAX, DCTX_SIZE; lia)
              | (apply aunw_data; rewrite ?unsigned_lit by lia; [lia | lia | unfold ACREATEDCTX_MRET in HU; exact HU])
              | (unfold AMALLOC_PC, AMALLOC_STACK; cbn; lia)
              | (clear - SP16 RSP ESP; subst SPV; Z.div_mod_to_equations; lia) ]. }
    cbv beta. intros r s' RNG' ms1 [SOE PO].
    destruct PO as (LE & y0 & y1 & y2 & ya0 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & m2 & -> & MI2 & ST2 & HPR & RR).
    cbn [fst snd] in RR, HPR, ST2, MI2. rewrite ?unsigned_lit in ST2, HPR by lia.
    destruct r as [p|]; [| destruct RR].
    destruct RR as (A & junk2 & -> & BR & AH2 & BLK & RA & RSA & _).
    pose proof BR as (BR1 & BR2 & BR3 & BR4). pose proof (ablk_lin _ _ BR1) as (BL1 & BL2 & BL3 & BL4). unfold AIMG_HI in BL1.
    unfold DCTX_SIZE in *.
    replace (ret_pc (Z_to_bv 64 535768)) with (Z_to_bv 64 535768) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    lazymatch goal with FRc : rw_cells _ ?mo (SPV + -64) ?cs |- _ =>
      assert (FR2 : rw_cells bsegs m2 (SPV + -64) cs)
        by (eapply aheap_pres_rw_cells; [exact HPR| exact FRc| left; left; cbn; lia]); clear FRc end.
    clear AH1 GOT RIC SHB INI LAYC REAL.
    (* [comment removed for export] *)
    destruct (areg_block AI _ _ _ _ _ p A 95992 A 95992 AH2 ltac:(left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (_ & UA & _ & RAS').
    assert (AA : A + 95992 <= 0x7fff7000 \/ 0x10007fff8000 <= A) by (unfold ablk, AIMG_HI, KLS in BR1; lia).
    pose proof (art_of_aheap AI _ _ _ _ _ AH2) as ART. destruct ART as (GOT & RIC & SHB & INI & LAYC & REAL).
    pose proof (munch_refl [(A, A + 95992); (lo, SPV)] m2) as MU2. pose proof (wmono_refl bsegs m2) as WM2.
    (* [comment removed for export] *)
    change (Z.to_nat 95992) with 95992%nat in BLK.
    apply (rw_cells_split_CB _ _ _ [] _ _ _ [32; 29856; 40; 48; 32; 88; 276; 65568; 52]%nat) in BLK; [| reflexivity].
    cbn [mk_CB_cells app] in BLK.
    csplit BLK 1%nat BK0. csplit BLK 1%nat BKE. csplit BLK 1%nat BH1. csplit BLK 1%nat BFP. csplit BLK 1%nat BH3.
    csplit BLK 1%nat BXS. csplit BLK 1%nat BH5. csplit BLK 1%nat BKX. rename BLK into BTX.
    apply stk_of_rw_cells in BKE. cbn [cells_size csize Nat.add] in BKE. zaddr_norm BKE.
    apply stk_of_rw_cells in BKX. cbn [cells_size csize Nat.add] in BKX. zaddr_norm BKX.
    apply (rw_cells_split_CB _ _ _ [] _ _ _ [8;8;8;8;8]%nat) in BH1; [| reflexivity]. cbn [mk_CB_cells app] in BH1.
    apply (rw_cells_split_CB _ _ _ [] _ _ _ [8;8;4;4;4;4]%nat) in BH3; [| reflexivity]. cbn [mk_CB_cells app] in BH3.
    apply (rw_cells_split_CB _ _ _ [] _ _ _
             [8;4;4;4;4;8; 24; 8;8;8;4;4; 16; 4;4;4;4;8;4;4;4; 20; 8;8;8;8;8;8;8; 4;4;4;4; 8;8;8; 8;8; 4]%nat) in BH5; [| reflexivity].
    cbn [mk_CB_cells app] in BH5.
    apply (rw_cells_split_CB _ _ _ [] _ _ _ [20; 8;8;8;8]%nat) in BTX; [| reflexivity]. cbn [mk_CB_cells app] in BTX.
    (* [comment removed for export] *)
    csplit BH5 6%nat H5a. csplit BH5 1%nat M1. csplit BH5 5%nat H5b. csplit BH5 1%nat M2. csplit BH5 8%nat H5c. csplit BH5 1%nat M3.
    rename BH5 into H5r.
    gen_junk BK0. gen_junk BH1. gen_junk BFP. gen_junk BH3. gen_junk BXS. gen_junk H5a. gen_junk M1. gen_junk H5b. gen_junk M2.
    gen_junk H5c. gen_junk M3. gen_junk H5r. gen_junk BTX.
    lazymatch goal with |- evtF _ _ ?Q _ => remember Q as KQ eqn:EKQ end.
    (* [comment removed for export] *)
    pose proof (rng_fp_le _ _ _ _ LE RSTK) as RSTK'. pose proof (rng_fp_le _ _ _ _ LE RI) as RI'.
    kx_autoFLAx [KAUnp A 95992; KAApp A 95992; KAApp (SPV - 64) 64] [] 120%nat
      [KZRange A 0x605000 (2^47 - 95992); KZAlign A 16; KZRange SPV 0x10007fff8000 (2^47 - 1);
       KZWr (A + 29888) 40; KZWr (A + 30152) 32; KZWr (A + 30200) 36; KZWr (A + 30256) 116; KZWr (A + 95940) 52;
       KZDisj (SPV - 64) 64 A 95992]
      [(SPV - 64, 64)] [(A, 95992); (SPV - 64, 64)].
    all: try kx_cell_lit. all: try kx_acc RI'. all: try kx_acc RSTK'. all: try kx_z.
    all: kx_mem.
    msetA M2 MZ2.
    kx_autoFLAx [] [] 20%nat [KZRange A 0x605000 (2^47 - 95992); KZAlign A 16] [] [].
    all: try kx_cell_lit. all: try kx_acc RI'. all: try kx_z.
    all: kx_mem.
    msetA M3 MZ3.
    kx_autoFLAx [] [] 20%nat [KZRange A 0x605000 (2^47 - 95992); KZAlign A 16] [] [].
    all: try kx_cell_lit. all: try kx_acc RI'. all: try kx_z.
    all: kx_mem.
    msetA M1 MZ1.
    lazymatch type of MU2 with munch _ _ ?mc =>
      assert (Z2 : rw_cells bsegs mc (A + 30184) [C8 wz0; C8 wz0]) by (eapply rw_cells_recell; [exact MZ2 | cbn; tauto | reflexivity]);
      assert (Z3 : rw_cells bsegs mc (A + 30236) [C4 wz0; C8 wz0; C8 wz0]) by (eapply rw_cells_recell; [exact MZ3 | cbn; tauto | reflexivity]) end.
    clear MZ2 MZ3.
    lazymatch type of H5b with rw_cells _ ?mc _ ?cb => lazymatch type of H5c with rw_cells _ _ _ ?cc =>
    lazymatch type of H5r with rw_cells _ _ _ ?cr =>
      assert (H5s : rw_cells bsegs mc (A + 30152) (cb ++ [C8 wz0; C8 wz0] ++ cc ++ [C4 wz0; C8 wz0; C8 wz0] ++ cr));
      [ apply (proj2 (rw_cells_app _ _ _ _ _)); split; [exact H5b|]; cbn [cells_size csize Nat.add];
        apply (proj2 (rw_cells_app _ _ _ _ _)); split; [replace (A + 30152 + Z.of_nat 32) with (A + 30184) by lia; exact Z2|];
        cbn [cells_size csize Nat.add];
        apply (proj2 (rw_cells_app _ _ _ _ _)); split; [replace (A + 30152 + Z.of_nat 32 + Z.of_nat 16) with (A + 30200) by lia; exact H5c|];
        cbn [cells_size csize Nat.add];
        apply (proj2 (rw_cells_app _ _ _ _ _)); split;
        [replace (A + 30152 + Z.of_nat 32 + Z.of_nat 16 + Z.of_nat 36) with (A + 30236) by lia; exact Z3|];
        cbn [cells_size csize Nat.add];
        replace (A + 30152 + Z.of_nat 32 + Z.of_nat 16 + Z.of_nat 36 + Z.of_nat 20) with (A + 30256) by lia; exact H5r |]
    end end end.
    cbn [app] in H5s. clear H5b Z2 H5c Z3 H5r. rename H5s into H5r.
    (* [comment removed for export] *)
    lazymatch type of MU2 with munch _ _ ?mc => pose proof (uac_of A m2 mc lo SPV UA MU2 BR1 BOT) as UA4 end.
    kx_autoFLAx [KAUnp A 95992; KAApp A 95992; KAApp (SPV - 64) 64] [] 160%nat
      [KZRange A 0x605000 (2^47 - 95992); KZAlign A 16; KZRange SPV 0x10007fff8000 (2^47 - 1);
       KZWr (A + 29888) 40; KZWr (A + 30096) 32; KZWr (A + 30152) 220; KZWr (A + 95940) 52;
       KZDisj (SPV - 64) 64 A 95992]
      [(SPV - 64, 64)] [(A, 95992); (SPV - 64, 64)].
    all: try kx_cell_lit. all: try kx_acc RI'. all: try kx_acc RSTK'. all: try kx_z.
    all: kx_mem. clear UA4.
    (* [comment removed for export] *)
    zstep.
    lazymatch goal with FRc : rw_cells _ ?mf (SPV + -64) _, STc : stk _ ?mf lo (SPV + -64) |- _ => release_frame FRc STc SPV end.
    subst KQ. apply evtF_done.
    (* [comment removed for export] *)
    lazymatch type of MU2 with munch _ _ ?mc => rename mc into mF end.
    apply (rw_cells_split_CB _ _ _ [] _ _ _ [8;8;8;8]%nat) in BK0; [| reflexivity]. cbn [mk_CB_cells app] in BK0. gen_junk BK0.
    wordify BK0. wordify BH1. wordify BH3. wordify BTX. wordify H5a. wordify H5r.
    assert (Z1 : rw_cells bsegs mF (A + 30128) [C8 wz0; C8 wz0; C8 wz0]) by (eapply rw_cells_recell; [exact MZ1 | cbn; tauto | reflexivity]).
    clear MZ1.
    (* [comment removed for export] *)
    lazymatch type of H5a with rw_cells _ _ _ ?ca => lazymatch type of Z1 with rw_cells _ _ _ ?c1 => lazymatch type of H5r with rw_cells _ _ _ ?cr =>
      assert (H5 : rw_cells bsegs mF (A + 30096) (ca ++ c1 ++ cr));
      [ apply (proj2 (rw_cells_app _ _ _ _ _)); split; [exact H5a|]; cbn [cells_size csize Nat.add];
        apply (proj2 (rw_cells_app _ _ _ _ _)); split; [replace (A + 30096 + Z.of_nat 32) with (A + 30128) by lia; exact Z1|]; cbn [cells_size csize Nat.add];
        replace (A + 30096 + Z.of_nat 32 + Z.of_nat 24) with (A + 30152) by lia; exact H5r |]
    end end end.
    cbn [app] in H5. clear H5a H5r Z1.
    lazymatch type of H5 with rw_cells _ _ _ ?cs =>
      set (WS := map cw cs);
      assert (H5C : rw_cells bsegs mF (A + 30096) (h5_cells WS)) by (replace (h5_cells WS) with cs by reflexivity; exact H5) end.
    assert (H5OK : h5_frame_ok WS).
    { unfold h5_frame_ok, WS, wz0. cbv beta iota delta [map cw wnth nth H5_format H5_forceIgnoreChecksum H5_refMultipleDDicts H5_maxBlockSizeParam H5_customAlloc
        H5_customFree H5_customOpaque H5_staticSize H5_ddictLocal H5_ddict H5_dictUses H5_ddictSet H5_inBuff]. repeat split; reflexivity. }
    assert (DA : dctx_any mF A).
    { lazymatch type of BK0 with rw_cells _ _ _ [C8 ?llt; C8 ?mlt; C8 ?oft; C8 ?huf] =>
      lazymatch type of BH1 with rw_cells _ _ _ [C8 ?pde; C8 ?pfx; C8 ?vst; C8 ?dend; C8 ?expd] =>
      lazymatch type of BH3 with rw_cells _ _ _ [C8 ?pcs; C8 ?dsz; C4 ?bt; C4 ?stg; C4 ?le; C4 ?fe] =>
      lazymatch type of BTX with rw_cells _ _ _ [CB 20 ?jhb; C8 ?ovd; C8 ?dcb; C8 ?dce; C8 ?trace] =>
      lazymatch type of BFP with rw_cells _ _ _ ?fp => lazymatch type of BXS with rw_cells _ _ _ ?xs =>
        exists llt, mlt, oft, huf, pde, pfx, vst, dend, expd, fp, pcs, dsz, bt, stg, le, fe, xs, WS, jhb, ovd, dcb, dce, trace
      end end end end end end.
      split; [exact BK0|]. split; [exact BH1|]. split; [split; [exact BFP| reflexivity]|]. split; [exact BH3|]. split; [split; [exact BXS| reflexivity]|].
      split; [split; [exact H5C| reflexivity]|]. split; [exact H5OK|]. split; [exact BTX|]. split; [exact BKE| exact BKX]. }
    clear H5 H5C BK0 BH1 BFP BH3 BXS BTX BKE BKX H5OK.
    (* [comment removed for export] *)
    unfold zd_createdctx_postA. rewrite ?unsigned_lit by lia. split; [exact LE|].
    do 14 eexists. exists mF, p, A. split; [reflexivity|]. split; [reflexivity|].
    split; [assumption|]. split; [assumption|].
    split.
    { eapply aheap_pres_trans.
      - eapply (aheap_pres_frame AI L RNG (aps_m s) LB m _ _ lo SPV AH MU WM); [| exact BOT| lia]. constructor; [cbn; lia| constructor].
      - eapply aheap_pres_trans; [eapply aheap_pres_weaken; [exact HPR| lia| intros bb Hbb; exact Hbb]|].
        eapply (aheap_pres_fresh AI L RNG' (aps_m s') LB m2 mF p A 95992 lo SPV AH2 MU2 WM2 BOT ltac:(lia) ltac:(lia)). }
    split; [exact SOE|]. unfold DCTX_SIZE. split; [exact BR|].
    split; [exact (ahc_of L RNG' (aps_m s') p A LB m2 mF lo SPV AH2 MU2 WM2 BOT ltac:(lia))|].
    split; [exact DA|]. split; [exact RA| exact RSA].
  Qed.
End Create.
End CANSEC1.
