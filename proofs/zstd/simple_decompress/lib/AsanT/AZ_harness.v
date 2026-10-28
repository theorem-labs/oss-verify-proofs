(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas FuzzProducer ZdFrame ZdFrameThm ZdHarness.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Bytes InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import DrvAgree ZdWalkKit ZdDctxRep.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed Harness ProgA AsanProgDeps.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF ITreeA SysStepF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells AProto ABase ABytes AMalloc_iface AProg_kit AHarness_iface
     AFake_iface Stdio_kit ADriver_iface AD_kit AH_fse_malloc AZ_kit AZ_globals AZ_globalsR AZ_frame_iface AZ_dframe_iface AZ_dctx_iface AZ_dctx_iface_m
     AZ_prod_iface AH_fse_kit AZ_harness_kit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac cl := repeat match goal with H : _ |- _ => clear H end.
Ltac h_retlit := lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [cl; lia| reflexivity]) end.

Section CANSEC1. Context {rc : runConstT}.
Section Harness.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variable fflag : alayout -> Z -> Z -> Z.
  Variable rng_fs : alayout -> footprint -> Prop.
  Hypothesis MONO : forall L R R', fp_le R R' -> rng_fs L R -> rng_fs L R'.
  Hypothesis FHEAP : fake_heap_law AI.
  Hypothesis CLI_CI : forall iv, In iv cli_img_ranges -> In iv CI.
  Hypothesis DRV_CI : forall iv, In iv drv_img_ranges -> In iv CI.
  Hypothesis RESERVE : zd_reserve_stmtA.
  Hypothesis U32R : zd_u32r_stmtA.
  Hypothesis CREATEDCTX : zd_createdctx_stmtA AI.
  Hypothesis DDCTX : zd_ddctx_stmtA AI rng_fs.
  Hypothesis ISERR : zd_iserror_stmtA.
  Hypothesis FINDDSIZE : zd_finddsize_stmtA AI rng_fs.
  Hypothesis FREEDCTX : zd_freedctx_stmtA AI.

  Section Run.
    (* [comment removed for export] *)
    Variables (L : alayout) (RNG : footprint) (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
              (m : amem) (s : APS) (LB : list ablock) (D : Z) (payload : list Z) (lo : Z) (rstk : region).
    Notation SP := (bv_unsigned sp).
    Notation zlen l := (Z.of_nat (length l)).
    Hypothesis HLB : hb_heap LB.
    Hypothesis PAY : payload_atA LB D payload.
    Hypothesis PAYR : Forall (fun c => 0 <= c < 256) payload.
    Hypothesis D16 : D mod 16 = 0.
    Hypothesis SZ : zlen payload < 2^26.
    Hypothesis BOT : ATOP + 4096 <= lo.
    Hypothesis LOS : lo <= SP - AHARNESS_STACK.
    Hypothesis SPG : SP + ATRUN_DEPTH = al_sp0 L.
    Hypothesis SP16 : SP mod 16 = 0.
    Hypothesis RS1 : r_lo rstk <= lo.
    Hypothesis RS2 : SP <= r_hi rstk.
    Hypothesis RS3 : ATOP <= r_rlo rstk.
    Hypothesis FC : frm0 fc.
    Hypothesis HUL : HU L.
    Hypothesis RSTK : rng RNG lo (al_top L - lo).
    Hypothesis RI : rng_aimg RNG.
    Hypothesis RISH : rng_aimg_sh RNG.
    Hypothesis RFS : rng_fs L RNG.
    Hypothesis RRS : rrng RNG rstk.
    Hypothesis AOK : aps_ok L s.
    Hypothesis ALY : al_bot L + 0x800000 = al_top L /\ al_top L mod 4096 = 0 /\ al_top L <= 2^47 /\ (ATOP - 160 <= al_bot L <= ATOP + 3936).

    Notation POST := (fuzz_oneA_post AI L RNG ra sp gp (Z_to_bv 64 ATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB lo m).
    (* [comment removed for export] *)
    Definition HFR : list cell := [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

    (* [comment removed for export] *)
    Lemma geomH : 0 <= SP /\ SP + 16 <= al_top L /\ al_top L < SP + 48 + 4096 /\ SP < 2^47 /\ ATOP + 4096 + 16384 <= SP /\ lo + 16384 <= SP.
    Proof.
      pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
      pose proof (harness_topF L SP SPG ltac:(lia)) as [T1 T2]. pose proof ALY as (LY1 & LY2 & LY3 & LY4).
      unfold AHARNESS_STACK in LOS. repeat split; lia.
    Qed.

    (* [comment removed for export] *)
    Definition HK (K : list ablock) (RNGX : footprint) (sX : APS) (mX : amem) (cv : word) : Prop :=
      fp_le RNG RNGX /\ AHEAP AI L RNGX (aps_m sX) K mX /\ aps_rest sX = aps_rest s /\ mem_inv bsegs mX /\
      stk bsegs mX lo (SP + -64) /\ rw_cells bsegs mX (SP + -64) HFR /\ rw_cells bsegs mX APDCTX [C8 cv] /\
      bytes_at bsegs mX D (map (Z_to_bv 8) payload) /\ aro_clientM mX /\ magree bsegs (hcl CI LB SP) m mX.

    (* [comment removed for export] *)
    Lemma HK_apres : forall K K' RNGX RNGY sX sY mX mY cv,
      HK K RNGX sX mX cv -> (forall b, In b LB -> In b K') ->
      aheap_pres CI K' (SP + -64) mX mY -> fp_le RNGX RNGY -> aps_rest sY = aps_rest sX -> mem_inv bsegs mY -> stk bsegs mY lo (SP + -64) ->
      forall K'', AHEAP AI L RNGY (aps_m sY) K'' mY ->
      HK K'' RNGY sY mY cv.
    Proof.
      intros K K' RNGX RNGY sX sY mX mY cv (LE & AH & REST & MI & ST & FR & CELL & PL & ARO & HAG) HI HP LE' REST' MI' ST' K'' AH'.
      pose proof geomH as (G1 & G2 & G3 & G4 & G5 & G6).
      split; [eapply fp_le_trans; [exact LE| exact LE']|]. split; [exact AH'|]. split; [congruence|]. split; [exact MI'|]. split; [exact ST'|].
      split; [eapply (frame_apres AI K' (SP + -64) (SP + -64)); [exact HP| lia| cbn; lia| exact FR]|].
      split; [exact (cell_apres AI CLI_CI K' (SP + -64) mX mY cv HP CELL)|].
      split; [exact (payload_apres AI LB K' (SP + -64) mX mY D payload HP HI PAY PL)|].
      split; [exact (aroM_apres AI CLI_CI DRV_CI K' (SP + -64) mX mY HP ARO)|].
      eapply magree_trans; [exact HAG|]. eapply (hcl_of_aheap_pres AI LB K' SP (SP + -64)); [exact HP| exact HI| lia| lia].
    Qed.

    (* [comment removed for export] *)
    Lemma HK_kept : forall KA KA' K RNGX sX mX mY cv W,
      HK KA RNGX sX mX cv -> hb_heap K -> (forall b, In b LB -> In b K) -> (forall b, In b K -> In b KA) ->
      Forall (wok K KA L (SP + -64)) W -> munch W mX mY -> wmono bsegs mX mY -> mem_inv bsegs mY -> stk bsegs mY lo (SP + -64) ->
      AHEAP AI L RNGX (aps_m sX) KA' mY ->
      HK KA' RNGX sX mY cv /\ magree bsegs (kept K (SP + -64)) mX mY.
    Proof.
      intros KA KA' K RNGX sX mX mY cv W (LE & AH & REST & MI & ST & FR & CELL & PL & ARO & HAG) HH HI HI' FW MU WM MI' ST' AH'.
      pose proof geomH as (G1 & G2 & G3 & G4 & G5 & G6). pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
      pose proof (kept_of_munch AI FHEAP L RNGX (aps_m sX) K KA mX W (SP + -64) mX mY AH HH HI' ltac:(lia) FW MU WM) as AG.
      split; [| exact AG].
      split; [exact LE|]. split; [exact AH'|]. split; [exact REST|]. split; [exact MI'|]. split; [exact ST'|].
      split; [eapply (frame_kept K (SP + -64)); [exact AG| cbn; lia| exact FR]|].
      split; [exact (cell_kept K (SP + -64) mX mY cv AG CELL)|].
      split; [eapply (payload_kept K (SP + -64)); [exact AG| | exact PL]; pose proof PAY as [(q & Hq & POS)|E]; [left; exists q; split; [apply HI; exact Hq| exact POS]| right; exact E]|].
      split; [exact (aroM_kept K (SP + -64) mX mY AG ARO)|].
      eapply magree_trans; [exact HAG|]. eapply (hcl_of_munch AI FHEAP L RNGX (aps_m sX) LB KA mX W (SP + -64) SP); try eassumption; try lia.
      - intros b Hb. apply HI'. apply HI. exact Hb.
      - eapply Forall_impl; [| exact FW]. intros iv. apply wok_antimono. exact HI.
    Qed.

    (* [comment removed for export] *)
    Notation HST pc x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 t3 t4 t5 t6 P mm :=
      (MS (mkR x1 (Z_to_bv 64 (SP + -64)) gp (Z_to_bv 64 ATP) t0 t1 t2 (Z_to_bv 64 P) (Z_to_bv 64 D) a0 a1 a2 a3 a4 a5 a6 a7
               x18 x19 x20 (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 0x602a68) s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    Lemma hz_tail : forall RNGX sX mX (p pd : AsanCtrl.aptr) (P DC : Z) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 t3 t4 t5 t6 : word),
      HK (HB pd DC DCTX_SIZE :: HB p P PRODUCER_SIZE :: LB) RNGX sX mX (Z_to_bv 64 DC) -> dctx_any mX DC ->
      implMA RNGX (Harness.free_opt afree_M (Some p) ;;; (Harness.free_opt afree_M (Some pd) ;;; mret 0)) sX POST
             (HST 0x82afc x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 t3 t4 t5 t6 P mX).
    Proof.
      intros RNGX sX mX p pd P DC x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 t3 t4 t5 t6 HKX DAX.
      pose proof HKX as (LE & AH & REST & MI & ST & FR & CELL & PL & ARO & HAG).
      pose proof geomH as (G1 & G2 & G3 & G4 & G5 & G6). pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
      pose proof HUL as (HU1 & HU2 & HU3 & HU4 & HU5).
      destruct (block_geom AI _ _ _ _ _ _ _ _ AH ltac:(right; left; reflexivity)) as (PBR & _ & PTOP & P16 & PLO).
      destruct (block_geom AI _ _ _ _ _ _ _ _ AH ltac:(left; reflexivity)) as (DBR & _ & DTOP & DC16 & DLO). unfold DCTX_SIZE, PRODUCER_SIZE, AIMG_HI in *.
      pose proof (AI_hb_ids AI _ _ _ _ _ AH) as ND.
      pose proof (rng_fp_le _ _ _ _ LE RSTK) as RSTKX. pose proof (rng_fp_le _ _ _ _ LE RI) as RIX.
      pose proof (aps_ok_rest L sX s REST AOK) as AOKX.
      cbn [Harness.free_opt].
      apply implMA_from_evtF. zstep. zstep. apply evtF_done.
      eapply implMA_bind.
      { eapply (prod_free_proofA AI L RNGX) with (lo := lo) (A := P) (n := PRODUCER_SIZE) (tr := []); rewrite ?unsigned_lit by lia;
          first [ exact AH | exact MI | exact ST | exact AOKX | exact RSTKX | reflexivity
                | (right; left; reflexivity)
                | (apply uchain_data; lia)
                | (unfold AFREEP_RET in HU4; exact HU4)
                | (unfold FREEDCTX_STACK_A, AFREE_STACK, AFREE_PC, UDEPTH; cbn; lia)
                | (clear - SP16 G1; Z.div_mod_to_equations; lia) ]. }
      cbv beta. intros [] sY RNGY ms1 [REST1 PO].
      destruct PO as (LE1 & u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & mY & -> & MIY & STY & HPRY & AHY).
      rewrite (lb_remove_secondA p P 16 (HB pd DC 95992) LB ND) in HPRY, AHY.
      rewrite ?unsigned_lit in STY, HPRY by lia. h_retlit.
      pose proof (HK_apres _ (HB pd DC 95992 :: LB) RNGX RNGY sX sY mX mY _ HKX ltac:(intros b Hb; right; exact Hb) HPRY LE1 REST1 MIY STY _ AHY) as HKY.
      pose proof (dctx_apres AI _ (SP + -64) mX mY pd DC HPRY ltac:(left; reflexivity) DAX) as DAY.
      clear HKX DAX LE AH REST MI ST FR CELL PL ARO HAG HPRY MIY STY.
      pose proof HKY as (LE & AH & REST & MI & ST & FR & CELL & PL & ARO & HAG).
      pose proof (rng_fp_le _ _ _ _ LE RSTK) as RSTKY. pose proof (rng_fp_le _ _ _ _ LE RI) as RIY.
      pose proof (aps_ok_rest L sY s REST AOK) as AOKY.
      (* [comment removed for export] *)
      apply implMA_from_evtF. unfold APDCTX in CELL. zstep. zstep. apply evtF_done.
      eapply implMA_bind.
      { eapply (FREEDCTX L RNGY) with (lo := lo) (A := DC); rewrite ?unsigned_lit by lia;
          first [ exact AH | exact DAY | exact MI | exact ST | exact AOKY | exact RSTKY | exact RIY | reflexivity
                | (left; reflexivity)
                | (unfold AFDCTX_FRET in HU5; unfold AFREEDCTX_FRET; exact HU5)
                | (unfold FREEDCTX_STACK_A, AFREE_STACK; cbn; lia)
                | (clear - SP16 G1; Z.div_mod_to_equations; lia) ]. }
      cbv beta. intros [] sZ RNGZ ms2 PO.
      destruct PO as (LE2 & v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & mZ & -> & MIZ & STZ & HPRZ & REST2 & AHZ).
      pose proof (AI_hb_ids AI _ _ _ _ _ AH) as ND2.
      rewrite (lb_remove_headA pd DC 95992 LB ND2) in HPRZ, AHZ.
      rewrite ?unsigned_lit in STZ, HPRZ by lia. h_retlit.
      pose proof (HK_apres _ LB RNGY RNGZ sY sZ mY mZ _ HKY ltac:(intros b Hb; exact Hb) HPRZ LE2 REST2 MIZ STZ _ AHZ) as HKZ.
      clear HKY DAY LE AH REST MI ST FR CELL PL ARO HAG HPRZ MIZ STZ.
      pose proof HKZ as (LE & AH & REST & MI & ST & FR & CELL & PL & ARO & HAG).
      pose proof (rng_fp_le _ _ _ _ LE RSTK) as RSTKZ. pose proof (rng_fp_le _ _ _ _ LE RI) as RIZ.
      (* [comment removed for export] *)
      apply implMA_ret.
      pose proof (munch_refl [(APDCTX, APDCTX + 8)] mZ) as MUZ. pose proof (wmono_refl bsegs mZ) as WMZ. unfold APDCTX in CELL, MUZ.
      unfold HFR in FR.
      zstep. zstep.
      do 8 zstep. zstep.
      release_frame FR ST (bv_unsigned sp).
      zstep.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mW _) =>
        assert (AHW : AHEAP AI L RNGZ (aps_m sZ) LB mW);
        [ eapply (AI_frame AI); [exact AH| exact MUZ| exact WMZ|]; constructor; [| constructor]; cbn [fst snd];
          left; right; left; exists (0x602380, 0x6023a0); split; [apply CLI_CI; unfold cli_img_ranges; left; reflexivity| cbn; lia]
        | assert (HAGW : magree bsegs (hcl CI LB SP) m mW);
          [ eapply magree_trans; [exact HAG| exact (hcl_of_cell AI LB SP mZ mW MUZ WMZ)] |] ]
      end.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mW _) =>
        assert (AROW : aro_clientM mW)
          by (eapply aro_clientM_magree; [exact (magree_of_munch bsegs _ mZ mW MUZ WMZ)| | exact ARO];
              intros a Ha; cbn [outside]; split; [| exact I]; rewrite !shad_div in Ha; unfold ASHOFF in Ha; lia)
      end.
      destruct (hcl_post AI LB SP m _ ltac:(lia) HAGW) as [HPRW ASW].
      apply evtF_done. unfold fuzz_oneA_post. split; [exact LE|].
      do 14 eexists. exists F, fc. eexists. split; [reflexivity|].
      split; [lia|]. split; [assumption|]. split; [exact FC|]. split; [exact ST|].
      split; [exact HPRW|]. split; [exact ASW|]. split; [exact AHW|].
      split; [split; [unfold APDCTX; assumption| exact AROW]|]. exact REST.
    Qed.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    Definition K2 (p pd : AsanCtrl.aptr) (P DC : Z) : list ablock := HB pd DC DCTX_SIZE :: HB p P PRODUCER_SIZE :: LB.

    Lemma all_bytes_payload : all_bytes payload.
    Proof. apply Forall_all_bytes. exact PAYR. Qed.

    Lemma hz_lib : forall RNGX sX mX K' (p pd : AsanCtrl.aptr) (P DC DST bsz rem : Z)
        (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x19 t3 t4 t5 t6 : word),
      HK K' RNGX sX mX (Z_to_bv 64 DC) -> hb_heap K' -> (forall b, In b LB -> In b K') ->
      In (HB pd DC DCTX_SIZE) K' -> In (HB p P PRODUCER_SIZE) K' ->
      ~ In (HB pd DC DCTX_SIZE) (HB p P PRODUCER_SIZE :: LB) ->
      (bsz = 0 \/ exists pb, In (HB pb DST bsz) K' /\ ~ In (HB pb DST bsz) (HB p P PRODUCER_SIZE :: LB)) ->
      dctx_any mX DC -> rclean mX rstk -> stk bsegs mX DST (DST + bsz) ->
      0 <= rem <= zlen payload -> 0 <= bsz <= 10 * rem ->
      (DST = 0 -> bsz = 0) -> (DST <> 0 -> 0x625000 <= DST) -> (bsz = 0 -> DST = 0) -> DST + bsz <= ATOP -> 0 <= DST ->
      (DST + bsz <= DC \/ DC + 95992 <= DST) -> (DST + bsz <= D \/ D + zlen payload <= DST) ->
      (0 < bsz -> areg RNGX mX DST bsz /\ ahull RNGX mX DST bsz /\ ainblk K' DST bsz) ->
      evtF bsegs RNGX
        (fun ms' => exists (x1' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (r : Z) mY,
           ms' = HST 0x82af4 x1' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 rem) (Z_to_bv 64 DST) (Z_to_bv 64 r) t3' t4' t5' t6' P mY
           /\ HK K' RNGX sX mY (Z_to_bv 64 DC) /\ dctx_any mY DC)
        (HST 0x82aa8 x1 t0 t1 t2 (Z_to_bv 64 DST) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 rem) x19 (Z_to_bv 64 bsz) t3 t4 t5 t6 P mX).
    Proof.
      intros RNGX sX mX K' p pd P DC DST bsz rem x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x19 t3 t4 t5 t6
             HKX HH' HILB HDC HP NDC WB DAX RCX DSK REM BSZ BN0 BNN BZD BTOPX BNNEG DJ_BDC DJ_BD BASAN.
      pose proof HKX as (LE & AH & REST & MI & ST & FR & CELL & PL & ARO & HAG).
      pose proof geomH as (G1 & G2 & G3 & G4 & G5 & G6). pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
      destruct (block_geom AI _ _ _ _ _ _ _ _ AH HDC) as (DBR & _ & DTOP & DC16 & DLO).
      destruct (payload_facts AI _ _ _ LB K' mX D payload AH HILB PAY (rng_fp_le _ _ _ _ LE RI) (rng_fp_le _ _ _ _ LE RISH)) as (D4096 & DTOPP & D8 & DARO & DAREG & DAIN & _).
      pose proof (payload_newblock AI L RNGX (aps_m sX) LB K' mX D payload pd DC DCTX_SIZE AH HILB PAY HDC
                    ltac:(intros X; apply NDC; right; exact X)) as DJ_DCD.
      pose proof all_bytes_payload as AB8. unfold DCTX_SIZE, PRODUCER_SIZE, AIMG_HI, zlength in *.
      assert (WDC : wok (HB p P 16 :: LB) K' L (SP + -64) (DC, DC + 95992)).
      { right; left. exists pd, DC, 95992. split; [exact HDC|]. split; [exact NDC| cbn; lia]. }
      assert (WBZ : wok (HB p P 16 :: LB) K' L (SP + -64) (DST, DST + bsz)).
      { destruct WB as [E|(pb & HB0 & NB)]; [do 3 right; cbn; lia|].
        right; left. exists pb, DST, bsz. split; [exact HB0|]. split; [exact NB| cbn; lia]. }
      assert (WSTK : forall d, 0 <= d -> d <= 16384 - 64 -> wok (HB p P 16 :: LB) K' L (SP + -64) (SP + -64 - d, SP + -64)).
      { intros d Hd1 Hd2. left. cbn. lia. }
      assert (WFK : Forall (wok (HB p P 16 :: LB) K' L (SP + -64)) (fake_area L)).
      { unfold fake_area. constructor; [right; right; left; left; reflexivity| constructor; [right; right; left; right; left; reflexivity| constructor]]. }
      assert (HHK : hb_heap (HB p P 16 :: LB)) by (apply hb_heap_cons; exact HLB).
      assert (HIK : forall b, In b (HB p P 16 :: LB) -> In b K') by (intros b [<-|Hb]; [exact HP| exact (HILB b Hb)]).
      (* [comment removed for export] *)
      unfold APDCTX in CELL. unfold HFR in FR.
      pose proof (rng_fp_le _ _ _ _ LE RSTK) as RSTKX. pose proof (rng_fp_le _ _ _ _ LE RI) as RIX.
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      pose proof (art_of_aheap AI L RNGX (aps_m sX) K' mX AH) as ART.
      pose proof (got_trace_of_aheap AI L RNGX (aps_m sX) K' mX AH) as GOTT.
      eapply evtF_cut.
      { eapply (DDCTX L RNGX (aps_m sX) K') with (lo := lo) (DCTX := DC) (DST := DST) (CAP := bsz) (SRC := D) (src := payload) (size := rem);
          try reflexivity.
        all: try exact DAX. all: try exact GOTT. all: try exact PL. all: try exact AB8. all: try exact DSK. all: try exact ST. all: try exact MI.
        all: try exact DARO. all: try exact DAREG. all: try exact DAIN. all: try exact BN0. all: try exact BZD. all: try exact BASAN.
        all: try (intros HNZ'; exact (payload_ahull AI _ _ _ LB K' _ D payload AH HILB PAY HNZ')).   (* [comment removed for export] *)
        all: try (intros HNZ; pose proof (BNN HNZ); lia).
        all: try (clear - DC16; Z.div_mod_to_equations; lia).
        all: try (clear - G1 G2 G3 G4 G5 G6 ATR BOT LOS D4096 DTOPP DLO DTOP REM BSZ BTOPX BNNEG DJ_BDC DJ_BD DJ_DCD SZ BN0 BNN; lia).
        - (* [comment removed for export] *) split; [exact AH|]. split; [apply ashort_heap; exact HH'|]. split; [exact ART|].
          split; [split; [unfold KHIGH; lia| split; [eapply rng_sub; [exact (rng_fp_le _ _ _ _ LE RSTK)| lia| lia]| exact (rng_fp_le _ _ _ _ LE RI)]]|].
          split; [exact (MONO _ _ _ LE RFS)|]. split; [lia|]. split; [lia|]. split; [clear - SP16 G1; Z.div_mod_to_equations; lia|].
          split; [exact (rng_fp_le _ _ _ _ LE RSTK)| exact (ablkLB_heap AI _ _ _ _ _ AH HH')].
        - (* [comment removed for export] *) eapply (azstk_of_rclean RNGX mX rstk); [exact RCX| exact (rng_fp_le _ _ _ _ LE RRS)| lia| lia| lia].
        - (* [comment removed for export] *) apply aro_client_of_M; [exact ARO| exact (rng_fp_le _ _ _ _ LE RI)| exact (rng_fp_le _ _ _ _ LE RISH)].
        - (* [comment removed for export] *) exact (areg_block AI L RNGX (aps_m sX) K' mX pd DC 95992 DC 95992 AH HDC ltac:(lia) ltac:(lia) ltac:(lia)).
        - exact (ahull_block AI L RNGX (aps_m sX) K' mX pd DC 95992 DC 95992 AH HDC ltac:(lia) ltac:(lia) ltac:(lia)).
        - exact (ainblk_block K' pd DC 95992 DC 95992 HDC ltac:(lia) ltac:(lia)). }
      cbv beta. intros ms' PO.
      destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & mY & r & -> & MUY & WMY & MIY & STY & _ & AHY & DAY & DSKY & RR & ROK).
      h_retlit.
      assert (FWY : Forall (wok (HB p P 16 :: LB) K' L (SP + -64)) ([(DC, DC + 95992); (DST, DST + bsz); (SP + -64 - DMF_STACK_A, SP + -64)] ++ fake_area L)).
      { cbn [app]. constructor; [exact WDC|]. constructor; [exact WBZ|]. constructor; [apply WSTK; lia|]. exact WFK. }
      destruct (HK_kept K' K' (HB p P 16 :: LB) RNGX sX mX mY (Z_to_bv 64 DC) _ HKX HHK ltac:(intros b Hb; right; exact Hb) HIK FWY MUY WMY MIY STY AHY)
        as [HKY AGY].
      pose proof (rclean_kept _ _ mX mY rstk AGY RS3 RCX) as RCY.
      clear HKX LE AH REST MI ST FR CELL PL ARO HAG MUY WMY MIY STY AHY DAX RCX DSK FWY AGY ART GOTT DARO DAREG DAIN.
      pose proof HKY as (LE & AH & REST & MI & ST & FR & CELL & PL & ARO & HAG). unfold APDCTX in CELL. unfold HFR in FR.
      change (2^64) with 18446744073709551616 in RR.
      (* [comment removed for export] *)
      zstep. zstep.
      eapply evtF_cut; [eapply (ISERR RNGX); [exact RR| reflexivity]|]. cbv beta. intros ms' ->. h_retlit.
      (* [comment removed for export] *)
      assert (FIN : forall mm (x1' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
        HK K' RNGX sX mm (Z_to_bv 64 DC) -> dctx_any mm DC ->
        evtF bsegs RNGX
          (fun ms' => exists (x1'' t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' : word) (r0 : Z) mZ,
             ms' = HST 0x82af4 x1'' t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' (Z_to_bv 64 rem) (Z_to_bv 64 DST) (Z_to_bv 64 r0) t3'' t4'' t5'' t6'' P mZ
             /\ HK K' RNGX sX mZ (Z_to_bv 64 DC) /\ dctx_any mZ DC)
          (HST 0x82af4 x1' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 rem) (Z_to_bv 64 DST) (Z_to_bv 64 r) t3' t4' t5' t6' P mm)).
      { intros mm x1' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' HKM DAM. apply evtF_done.
        do 16 eexists. exists r, mm. split; [reflexivity|]. split; [exact HKM| exact DAM]. }
      zstep. destruct (zd_is_error r) eqn:EERR; cbn [Z.b2z].
      - (* [comment removed for export] *)
        if_true. eapply FIN; [exact HKY| exact DAY].
      - if_false.
        specialize (ROK eq_refl).
        pose proof (decompress_ok_finder payload all_bytes_payload rem bsz r ltac:(lia)
                      ltac:(unfold ZD_CONTENTSIZE_ERROR; lia) ROK) as (FNE & FEQ & FRG).
        (* [comment removed for export] *)
        zstep. zstep. zstep.
        destruct (payload_facts AI _ _ _ LB K' mY D payload AH HILB PAY (rng_fp_le _ _ _ _ LE RI) (rng_fp_le _ _ _ _ LE RISH)) as (_ & _ & _ & DARO & DAREG & DAIN & _).
        pose proof (art_of_aheap AI L RNGX (aps_m sX) K' mY AH) as ART.
        eapply evtF_cut.
        { eapply (FINDDSIZE L RNGX (aps_m sX) K') with (lo := lo) (SRC := D) (src := payload) (size := rem); try reflexivity.
          all: try exact PL. all: try exact AB8. all: try exact ST. all: try exact MI. all: try exact DAREG. all: try exact DAIN.
          all: try (clear - G1 G2 G3 G4 G5 G6 ATR BOT LOS D4096 DTOPP REM BSZ SZ; lia).
          - (* [comment removed for export] *) split; [exact AH|]. split; [apply ashort_heap; exact HH'|]. split; [exact ART|].
            split; [split; [unfold KHIGH; lia| split; [eapply rng_sub; [exact (rng_fp_le _ _ _ _ LE RSTK)| lia| lia]| exact (rng_fp_le _ _ _ _ LE RI)]]|].
            split; [exact (MONO _ _ _ LE RFS)|]. split; [lia|]. split; [lia|]. split; [clear - SP16 G1; Z.div_mod_to_equations; lia|].
            split; [exact (rng_fp_le _ _ _ _ LE RSTK)| exact (ablkLB_heap AI _ _ _ _ _ AH HH')].
          - apply aro_client_of_M; [exact ARO| exact (rng_fp_le _ _ _ _ LE RI)| exact (rng_fp_le _ _ _ _ LE RISH)].
          - (* [comment removed for export] *)
            eapply (azstk_of_rclean RNGX mY rstk); [exact RCY| exact (rng_fp_le _ _ _ _ LE RRS)| lia| lia| lia]. }
        cbv beta. intros ms' PO.
        destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & mZ & -> & MUZ & WMZ & MIZ & STZ & _ & AHZ).
        h_retlit.
        assert (FWZ : Forall (wok K' K' L (SP + -64)) ((SP + -64 - FINDDSIZE_STACK_A, SP + -64) :: fake_area L)).
        { constructor; [left; cbn; lia|].
          unfold fake_area. constructor; [right; right; left; left; reflexivity| constructor; [right; right; left; right; left; reflexivity| constructor]]. }
        destruct (HK_kept K' K' K' RNGX sX mY mZ (Z_to_bv 64 DC) _ HKY HH' HILB ltac:(intros b Hb; exact Hb) FWZ MUZ WMZ MIZ STZ AHZ) as [HKZ AGZ].
        pose proof (dctx_kept K' (SP + -64) mY mZ pd DC AGZ HDC DAY) as DAZ.
        clear HKY LE AH REST MI ST FR CELL PL ARO HAG MUZ WMZ MIZ STZ AHZ DAY ART DARO DAREG DAIN.
        pose proof HKZ as (LE & AH & REST & MI & ST & FR & CELL & PL & ARO & HAG).
        destruct FEQ as [FU|FR'].
        + rewrite FU. replace (Z_to_bv 64 ZD_CONTENTSIZE_UNKNOWN) with (Z_to_bv 64 (-1)) by (apply Z_to_bv_eqm; reflexivity).
          zstep. zstep. if_true. eapply FIN; [exact HKZ| exact DAZ].
        + rewrite FR'.
          zstep. zstep. if_cases KA; zify_cond KA.
          { eapply FIN; [exact HKZ| exact DAZ]. }
          zstep. zstep. if_cases KB; zify_cond KB; [exfalso; unfold ZD_CONTENTSIZE_ERROR in FNE; lia|].
          zstep. if_cases KC; zify_cond KC; [exfalso; lia|].
          eapply FIN; [exact HKZ| exact DAZ].
    Qed.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    Lemma hz_D : forall RNGX sX mX K' (p pd : AsanCtrl.aptr) (P DC DST bsz rem : Z) (rb : option AsanCtrl.aptr)
        (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x19 t3 t4 t5 t6 : word),
      HK K' RNGX sX mX (Z_to_bv 64 DC) -> ~ In (HB pd DC DCTX_SIZE) (HB p P PRODUCER_SIZE :: LB) ->
      ((rb = None /\ DST = 0 /\ bsz = 0 /\ K' = K2 p pd P DC) \/
       (exists pb, rb = Some pb /\ 0 < bsz /\ K' = HB pb DST bsz :: K2 p pd P DC)) ->
      dctx_any mX DC -> rclean mX rstk -> stk bsegs mX DST (DST + bsz) ->
      0 <= rem <= zlen payload -> 0 <= bsz <= 10 * rem ->
      implMA RNGX (Harness.free_opt afree_M rb ;;; (Harness.free_opt afree_M (Some p) ;;; (Harness.free_opt afree_M (Some pd) ;;; mret 0))) sX POST
             (HST 0x82aa8 x1 t0 t1 t2 (Z_to_bv 64 DST) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 rem) x19 (Z_to_bv 64 bsz) t3 t4 t5 t6 P mX).
    Proof.
      intros RNGX sX mX K' p pd P DC DST bsz rem rb x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x19 t3 t4 t5 t6 HKX NDC KSPEC DAX RCX DSK REM BSZ.
      pose proof HKX as (LE & AH & REST & MI & ST & FR & CELL & PL & ARO & HAG).
      pose proof geomH as (G1 & G2 & G3 & G4 & G5 & G6). pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
      pose proof HUL as (HU1 & HU2 & HU3 & HU4 & HU5).
      assert (HI2 : forall b, In b (K2 p pd P DC) -> In b K') by (destruct KSPEC as [(_ & _ & _ & ->)|(pb & _ & _ & ->)]; intros b Hb; [exact Hb| right; exact Hb]).
      assert (HILB : forall b, In b LB -> In b K') by (intros b Hb; apply HI2; right; right; exact Hb).
      assert (HDC : In (HB pd DC DCTX_SIZE) K') by (apply HI2; left; reflexivity).
      assert (HP : In (HB p P PRODUCER_SIZE) K') by (apply HI2; right; left; reflexivity).
      assert (HH' : hb_heap K').
      { destruct KSPEC as [(_ & _ & _ & ->)|(pb & _ & _ & ->)]; unfold K2; repeat apply hb_heap_cons; exact HLB. }
      destruct (block_geom AI _ _ _ _ _ _ _ _ AH HDC) as (DBR & _ & DTOP & DC16 & DLO).
      destruct (block_geom AI _ _ _ _ _ _ _ _ AH HP) as (PBR & _ & PTOP & P16 & PLO).
      destruct (payload_facts AI _ _ _ LB K' mX D payload AH HILB PAY (rng_fp_le _ _ _ _ LE RI) (rng_fp_le _ _ _ _ LE RISH)) as (D4096 & DTOPP & D8 & _).
      unfold DCTX_SIZE, PRODUCER_SIZE, AIMG_HI, zlength in *.
      (* [comment removed for export] *)
      assert (BF : (bsz = 0 \/ exists pb, In (HB pb DST bsz) K' /\ ~ In (HB pb DST bsz) (HB p P 16 :: LB)) /\
                   (DST = 0 -> bsz = 0) /\ (DST <> 0 -> 0x625000 <= DST) /\ (bsz = 0 -> DST = 0) /\ DST + bsz <= ATOP /\ 0 <= DST /\
                   (DST + bsz <= DC \/ DC + 95992 <= DST) /\ (DST + bsz <= D \/ D + zlen payload <= DST) /\
                   (0 < bsz -> areg RNGX mX DST bsz /\ ahull RNGX mX DST bsz /\ ainblk K' DST bsz)).
      { destruct KSPEC as [(_ & -> & -> & EK)|(pb & _ & BPOS & EK)].
        - split; [left; reflexivity|]. repeat split; intros; lia.
        - assert (HB0 : In (HB pb DST bsz) K') by (rewrite EK; left; reflexivity).
          pose proof (AI_blocks_nodup AI _ _ _ _ _ AH) as NDK. rewrite EK in NDK. inversion NDK as [|xb lb NB _]; subst xb lb.
          destruct (block_geom AI _ _ _ _ _ _ _ _ AH HB0) as (BBR & _ & BTOP & B16 & BLO). unfold AIMG_HI in BLO.
          assert (NE1 : HB pb DST bsz <> HB pd DC 95992) by (intros E; apply NB; rewrite E; left; reflexivity).
          pose proof (AI_blocks_disjoint AI _ _ _ _ _ _ _ AH HB0 HDC NE1) as DJ1. cbn [ab_addr ab_size] in DJ1.
          assert (NIB : ~ In (HB pb DST bsz) LB) by (intros X; apply NB; right; right; exact X).
          pose proof (payload_newblock AI L RNGX (aps_m sX) LB K' mX D payload pb DST bsz AH HILB PAY HB0 NIB) as DJ2. unfold zlength in DJ2.
          split; [right; exists pb; split; [exact HB0| intros [E|X]; [apply NB; right; left; exact E| exact (NIB X)]]|].
          split; [intros; lia|]. split; [intros; lia|]. split; [intros; lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
          intros _. split; [exact (areg_block AI L RNGX (aps_m sX) K' mX pb DST bsz DST bsz AH HB0 ltac:(lia) ltac:(lia) ltac:(lia))|].
          split; [exact (ahull_block AI L RNGX (aps_m sX) K' mX pb DST bsz DST bsz AH HB0 ltac:(lia) ltac:(lia) ltac:(lia))|].
          exact (ainblk_block K' pb DST bsz DST bsz HB0 ltac:(lia) ltac:(lia)). }
      destruct BF as (WB & BN0 & BNN & BZD & BTOPX & BNNEG & DJ_BDC & DJ_BD & BASAN).
      assert (LIB := hz_lib RNGX sX mX K' p pd P DC DST bsz rem x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x19 t3 t4 t5 t6
                       HKX HH' HILB HDC HP NDC WB DAX RCX DSK REM BSZ BN0 BNN BZD BTOPX BNNEG DJ_BDC DJ_BD BASAN).
      clear DAX RCX DSK BASAN.
      destruct KSPEC as [(-> & DST0 & BSZ0 & EK)|(pb & -> & BPOS & EK)]; cbn [Harness.free_opt].
      - (* [comment removed for export] *)
        apply implMA_retbH. apply implMA_from_evtF.
        eapply evtF_cut; [exact LIB|]. cbv beta. clear LIB HKX LE AH REST MI ST FR CELL PL ARO HAG.
        intros ms' (x1' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & r & mY & -> & HKY & DAY).
        pose proof HKY as (LE & AH & REST & MI & ST & FR & CELL & PL & ARO & HAG).
        zstep. zstep.
        subst DST.
        eapply evtF_cut.
        { eapply (implMA_afree_null AI L RNGX) with (lo := lo) (tr := []); rewrite ?unsigned_lit by lia;
            first [ exact AH | exact MI | exact ST | reflexivity
                  | exact (rng_fp_le _ _ _ _ LE RSTK)
                  | (apply aunw_data; rewrite ?unsigned_lit by lia; [lia | lia | unfold AFREEB_RET in HU3; exact HU3])
                  | (unfold AFREE_STACK, AFREE_PC; cbn; lia)
                  | (clear - SP16 G1; Z.div_mod_to_equations; lia) ]. }
        cbv beta. intros ms' PO.
        destruct PO as (u0 & u1 & u2 & xa0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & mZ & -> & MIZ & STZ & HPRZ & AHZ).
        rewrite ?unsigned_lit in STZ, HPRZ by lia. h_retlit.
        pose proof (HK_apres _ _ RNGX RNGX sX sX mY mZ _ HKY HILB HPRZ ltac:(intros b j H; exact H) eq_refl MIZ STZ _ AHZ) as HKZ.
        pose proof (dctx_apres AI _ (SP + -64) mY mZ pd DC HPRZ HDC DAY) as DAZ.
        apply evtF_done. rewrite EK in HKZ.
        exact (hz_tail RNGX sX mZ p pd P DC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HKZ DAZ).
      - (* [comment removed for export] *)
        apply implMA_from_evtF.
        eapply evtF_cut; [exact LIB|]. cbv beta. clear LIB HKX LE AH REST MI ST FR CELL PL ARO HAG.
        intros ms' (x1' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & r & mY & -> & HKY & DAY).
        pose proof HKY as (LE & AH & REST & MI & ST & FR & CELL & PL & ARO & HAG).
        assert (HB0 : In (HB pb DST bsz) K') by (rewrite EK; left; reflexivity).
        zstep. zstep. apply evtF_done.
        eapply implMA_bind.
        { eapply (implMA_afree_call AI L RNGX) with (lo := lo) (tr := []); rewrite ?unsigned_lit by lia;
            first [ exact AH | exact HB0 | exact MI | exact ST | reflexivity
                  | exact (rng_fp_le _ _ _ _ LE RSTK)
                  | exact (aps_ok_rest L sX s REST AOK)
                  | (apply aunw_data; rewrite ?unsigned_lit by lia; [lia | lia | unfold AFREEB_RET in HU3; exact HU3])
                  | (unfold AFREE_STACK, AFREE_PC; cbn; lia)
                  | (clear - SP16 G1; Z.div_mod_to_equations; lia) ]. }
        cbv beta. intros [] sZ RNGZ ms1 [REST1 PO].
        destruct PO as (LE1 & u0 & u1 & u2 & xa0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & mZ & -> & MIZ & STZ & HPRZ & AHZ).
        pose proof (AI_hb_ids AI _ _ _ _ _ AH) as ND. rewrite EK in ND, HPRZ, AHZ. unfold K2 in ND, HPRZ, AHZ.
        rewrite (lb_remove_headA pb DST bsz _ ND) in HPRZ, AHZ.
        rewrite ?unsigned_lit in STZ, HPRZ by lia. h_retlit.
        pose proof (HK_apres _ (HB pd DC DCTX_SIZE :: HB p P PRODUCER_SIZE :: LB) RNGX RNGZ sX sZ mY mZ _ HKY ltac:(intros b Hb; right; right; exact Hb) HPRZ LE1 REST1 MIZ STZ _ AHZ) as HKZ.
        pose proof (dctx_apres AI _ (SP + -64) mY mZ pd DC HPRZ ltac:(left; reflexivity) DAY) as DAZ.
        exact (hz_tail RNGZ sZ mZ p pd P DC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HKZ DAZ).
    Qed.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    Lemma hz_C : forall RNGX sX mX (p pd : AsanCtrl.aptr) (P DC rem eff : Z)
        (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x19 x20 t3 t4 t5 t6 : word),
      HK (K2 p pd P DC) RNGX sX mX (Z_to_bv 64 0) -> dctx_any mX DC -> rclean mX rstk ->
      prod_at mX P (D + rem) eff -> (rem, eff) = reserve_data_prefix payload (zlen payload) ->
      implMA RNGX (rbuf <- Harness.fuzz_malloc amalloc_M (new_handlerA AAllocAsan) (buff_size payload) ;;
                   (Harness.free_opt afree_M rbuf ;;; (Harness.free_opt afree_M (Some p) ;;; (Harness.free_opt afree_M (Some pd) ;;; mret 0)))) sX POST
             (HST 0x82a7c x1 t0 t1 t2 (Z_to_bv 64 DC) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 rem) x19 x20 t3 t4 t5 t6 P mX).
    Proof.
      intros RNGX sX mX p pd P DC rem eff x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x19 x20 t3 t4 t5 t6 HKX DAX RCX PRX ERDP.
      pose proof HKX as (LE & AH & REST & MI & ST & FR & CELL & PL & ARO & HAG).
      pose proof geomH as (G1 & G2 & G3 & G4 & G5 & G6). pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
      pose proof HUL as (HU1 & HU2 & HU3 & HU4 & HU5).
      assert (HDC : In (HB pd DC DCTX_SIZE) (K2 p pd P DC)) by (left; reflexivity).
      assert (HP : In (HB p P PRODUCER_SIZE) (K2 p pd P DC)) by (right; left; reflexivity).
      assert (HILB : forall b, In b LB -> In b (K2 p pd P DC)) by (intros b Hb; right; right; exact Hb).
      pose proof (AI_blocks_nodup AI _ _ _ _ _ AH) as NDK. unfold K2 in NDK.
      destruct (block_geom AI _ _ _ _ _ _ _ _ AH HDC) as (DBR & _ & DTOP & DC16 & DLO).
      destruct (block_geom AI _ _ _ _ _ _ _ _ AH HP) as (PBR & _ & PTOP & P16 & PLO).
      destruct (payload_facts AI _ _ _ LB (K2 p pd P DC) mX D payload AH HILB PAY (rng_fp_le _ _ _ _ LE RI) (rng_fp_le _ _ _ _ LE RISH)) as (D4096 & DTOPP & D8 & DARO & _).
      destruct (nodup_3 _ _ _ NDK) as (NDC & NPL & NEPD).
      pose proof (payload_newblock AI L RNGX (aps_m sX) LB _ mX D payload p P PRODUCER_SIZE AH HILB PAY HP NPL) as DJ_PD.
      pose proof (AI_blocks_disjoint AI _ _ _ _ _ _ _ AH HP HDC ltac:(exact NEPD)) as DJ_PDC. cbn [ab_addr ab_size] in DJ_PDC.
      unfold DCTX_SIZE, PRODUCER_SIZE, AIMG_HI, zlength in *.
      pose proof (reserve_data_prefix_range payload (zlen payload) ltac:(lia)) as RDP. rewrite <- ERDP in RDP. cbn [fst snd] in RDP.
      destruct RDP as (RDP1 & RDP2 & RDP3).
      (* [comment removed for export] *)
      unfold APDCTX in CELL. unfold HFR in FR. unfold prod_at in PRX.
      pose proof (munch_refl [(APDCTX, APDCTX + 8)] mX) as MUC. pose proof (wmono_refl bsegs mX) as WMC. unfold APDCTX in MUC.
      pose proof (rng_fp_le _ _ _ _ LE RSTK) as RSTKX. pose proof (rng_fp_le _ _ _ _ LE RI) as RIX.
      (* [comment removed for export] *)
      assert (DJC : D + zlen payload <= APDCTX \/ APDCTX + 8 <= D).
      { destruct PAY as [(q & Hq & _)|[EP ED]].
        - destruct (block_geom AI _ _ _ _ _ _ _ _ AH (HILB _ Hq)) as (_ & _ & _ & _ & QLO). unfold AIMG_HI in QLO. unfold APDCTX. right. lia.
        - rewrite ED. left. rewrite EP. unfold AEMPTY, APDCTX. cbn. lia. }
      unfold APDCTX in DJC.
      apply implMA_from_evtF.
      zstep.
      (* [comment removed for export] *)
      zstep. if_cases KN; zify_cond KN; [exfalso; rewrite ?unsigned_lit in KN by lia; lia|].
      (* [comment removed for export] *)
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
        assert (AHC : AHEAP AI L RNGX (aps_m sX) (K2 p pd P DC) mc);
        [ eapply (AI_frame AI); [exact AH| exact MUC| exact WMC|]; constructor; [| constructor]; cbn [fst snd];
          left; right; left; exists (0x602380, 0x6023a0); split; [apply CLI_CI; unfold cli_img_ranges; left; reflexivity| cbn; lia]
        | assert (HAGC : magree bsegs (hcl CI LB SP) m mc);
          [ eapply magree_trans; [exact HAG| exact (hcl_of_cell AI LB SP mX mc MUC WMC)]
          | assert (AROC : aro_clientM mc);
            [ eapply aro_clientM_magree; [exact (magree_of_munch bsegs _ mX mc MUC WMC)| | exact ARO];
              intros a Ha; cbn [outside]; split; [| exact I]; rewrite !shad_div in Ha; unfold ASHOFF in Ha; lia
            | assert (RCC : rclean mc rstk);
              [ eapply rclean_magree; [exact (magree_of_munch bsegs _ mX mc MUC WMC)| | exact RCX];
                intros a Ha; cbn [outside]; split; [| exact I]; destruct RCX as [(_ & HL & _) _]; unfold hull64 in HL;
                rewrite !shad_div in Ha; unfold ASHOFF in Ha; lia
              | assert (DAC : dctx_any mc DC);
                [ eapply (dctx_any_transport DC _ mX mc); [exact DAX| exact MUC| exact WMC| cbn [disjoint_from]; lia] |] ] ] ] ]
      end.
      clear MUC WMC HAG ARO RCX DAX AH.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep.
      set (pl2 := skipn (Z.to_nat rem) payload).
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
        assert (PL2 : bytes_at bsegs mc (D + rem) (map (Z_to_bv 8) pl2)) by (apply zd_src_skipn; [assumption| lia])
      end.
      assert (PL2B : Forall (fun c => 0 <= c < 256) pl2).
      { apply Forall_forall. intros c Hc. apply (proj1 (Forall_forall _ _) PAYR). unfold pl2 in Hc.
        rewrite <- (firstn_skipn (Z.to_nat rem) payload). apply in_or_app. right. exact Hc. }
      assert (PL2L : zlen pl2 = zlen payload - rem) by (unfold pl2; rewrite length_skipn; lia).
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
        pose proof (art_of_aheap AI L RNGX (aps_m sX) _ mc AHC) as ART
      end.
      eapply evtF_cut.
      { eapply (U32R RNGX) with (P := P) (D := D + rem) (pl := pl2) (size := eff) (mn := 0) (mx := rem * 10) (lo := lo); try reflexivity.
        all: try assumption.
        all: try (rewrite PL2L; lia).
        all: try (clear - P16; Z.div_mod_to_equations; lia).
        all: try (clear - G1 G2 G3 G4 G5 G6 ATR BOT LOS D4096 DTOPP PTOP PLO RDP1 RDP2 RDP3 DJ_PD PL2L SZ; rewrite ?PL2L; lia).
        - split; [exact PL2| exact PL2B].
        - eapply (areg_block AI L RNGX (aps_m sX) (K2 p pd P DC)); [exact AHC| exact HP| lia| lia| lia].
        - (* [comment removed for export] *)
          lazymatch goal with |- aro _ ?mc _ _ =>
            destruct (payload_facts AI _ _ _ LB (K2 p pd P DC) mc D payload AHC HILB PAY (rng_fp_le _ _ _ _ LE RI) (rng_fp_le _ _ _ _ LE RISH))
              as (_ & _ & _ & DARO2 & _) end.
          unfold zlength in DARO2. eapply aro_sub; [exact DARO2| lia| rewrite PL2L; lia| rewrite PL2L; lia].
        - split; [unfold KHIGH; lia| split; [eapply rng_sub; [exact (rng_fp_le _ _ _ _ LE RSTK)| lia| lia]| exact (rng_fp_le _ _ _ _ LE RI)]].
        - (* [comment removed for export] *)
          f_equal. unfold bv_swrap. rewrite bv_wrap_small; [lia|]. unfold bv_half_modulus, bv_modulus. cbn. lia. }
      cbv beta. intros ms' PO.
      destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & mY & -> & MUY & WMY & MIY & STY & PRY).
      h_retlit.
      assert (EBS : fst (uint32Range pl2 eff 0 (rem * 10)) = buff_size payload).
      { unfold buff_size, sd_buf_size, sd_draws, FseNCount.Zlength. unfold zlength in ERDP |- *. rewrite <- ERDP. fold pl2. rewrite (Z.mul_comm 10 rem).
        destruct (uint32Range pl2 eff 0 (rem * 10)) as [bb ee]. reflexivity. }
      pose proof (uint32Range_range pl2 eff 0 (rem * 10) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as URR.
      destruct (uint32Range pl2 eff 0 (rem * 10)) as [bsz eff2] eqn:EUR. cbn [fst snd] in *. destruct URR as (RB1 & RB2).
      (* [comment removed for export] *)
      assert (FWY : Forall (wok (HB pd DC 95992 :: LB) (K2 p pd P DC) L (SP + -64)) [(P + 8, P + 16); (SP + -64 - 16, SP + -64)]).
      { constructor; [right; left; exists p, P, 16; split; [exact HP| split; [intros [E|X]; [apply NEPD; symmetry; exact E| exact (NPL X)]| cbn; lia]]|].
        constructor; [left; cbn; lia| constructor]. }
      lazymatch type of CELL with rw_cells _ ?mc _ _ => assert (HKC : HK (K2 p pd P DC) RNGX sX mc (Z_to_bv 64 DC)) end.
      { split; [exact LE|]. split; [exact AHC|]. split; [exact REST|]. split; [assumption|]. split; [assumption|].
        split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [exact AROC| exact HAGC]. }
      (* [comment removed for export] *)
      assert (AHY : AHEAP AI L RNGX (aps_m sX) (K2 p pd P DC) mY).
      { eapply (AI_frame AI); [exact AHC| exact MUY| exact WMY|]. constructor; [| constructor; [| constructor]]; cbn [fst snd].
        - right; left. exists (HB p P 16). split; [exact HP| cbn; lia].
        - left; left. lia. }
      destruct (HK_kept _ (K2 p pd P DC) (HB pd DC 95992 :: LB) RNGX sX _ mY (Z_to_bv 64 DC) _ HKC ltac:(apply hb_heap_cons; exact HLB)
                  ltac:(intros b Hb; right; exact Hb) ltac:(intros b [E|Hb]; [rewrite <- E; exact HDC| exact (HILB b Hb)]) FWY MUY WMY MIY STY AHY)
        as [HKY AGY].
      pose proof (rclean_kept _ _ _ mY rstk AGY RS3 RCC) as RCY.
      pose proof (dctx_kept _ _ _ mY pd DC AGY ltac:(left; reflexivity) DAC) as DAY.
      clear HKC AGY MUY WMY MIY STY RCC DAC AROC HAGC ART PL2 FWY.
      clear LE REST MI ST FR CELL PL.
      pose proof HKY as (LE & AH & REST & MI & ST & FR & CELL & PL & ARO & HAG). unfold APDCTX in CELL. unfold HFR in FR.
      (* [comment removed for export] *)
      zstep. zstep.
      try (replace (Z.land bsz 4294967295) with bsz
        by (change 4294967295 with (Z.ones 32); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia)).
      zstep. zstep.
      destruct (Z.eq_dec bsz 0) as [BS0|BSP].
      - (* [comment removed for export] *)
        pose proof (munch_refl [(SP + -64 - 16, SP + -64)] mY) as MUF. pose proof (wmono_refl bsegs mY) as WMF.
        carve_frame 16%nat ST.
        rewrite BS0. zstep. zstep. zstep. zstep. if_true. zstep. zstep. zstep. zstep.
        lazymatch goal with FRc : rw_cells _ ?mc (?S + -80) _, STc : stk _ ?mc ?l (?S + -80) |- _ => release_frame FRc STc (S + -64) end.
        apply evtF_done.
        unfold Harness.fuzz_malloc at 1. rewrite <- EBS, BS0. change (0 <? 0) with false. cbv iota. apply implMA_retbH. cbv beta.
        (* [comment removed for export] *)
        lazymatch type of MUF with munch ?W _ ?mc =>
          assert (FWF : Forall (wok (K2 p pd P DC) (K2 p pd P DC) L (SP + -64)) W) by (constructor; [left; cbn [fst snd]; lia| constructor]);
          assert (AHF : AHEAP AI L RNGX (aps_m sX) (K2 p pd P DC) mc);
          [ eapply (AI_frame AI); [exact AH| exact MUF| exact WMF|]; constructor; [cbn [fst snd]; left; left; lia| constructor] |];
          lazymatch goal with MIc : mem_inv _ mc, STc : stk _ mc lo _ |- _ =>
            destruct (HK_kept _ (K2 p pd P DC) (K2 p pd P DC) RNGX sX mY mc (Z_to_bv 64 DC) W HKY
                        ltac:(unfold K2; repeat apply hb_heap_cons; exact HLB) HILB ltac:(intros b Hb; exact Hb) FWF MUF WMF MIc STc AHF)
              as [HKF AGF]
          end
        end.
        eapply (hz_D RNGX sX _ (K2 p pd P DC) p pd P DC 0 0 rem None); try eassumption.
        + left. repeat split; reflexivity.
        + exact (dctx_kept _ _ _ _ pd DC AGF HDC DAY).
        + exact (rclean_kept _ _ _ _ rstk AGF RS3 RCY).
        + apply stk_empty. lia.
        + lia.
        + lia.
      - (* [comment removed for export] *)
        apply evtF_done.
        eapply implMA_bind.
        { rewrite <- EBS. eapply (fuzz_malloc_proofA AI L RNGX) with (lo := lo) (n := bsz); rewrite ?unsigned_lit by lia;
            first [ exact AH | exact MI | exact ST | reflexivity
                  | exact (rng_fp_le _ _ _ _ LE RSTK) | exact (rng_fp_le _ _ _ _ LE RI)
                  | exact (aps_ok_rest L sX s REST AOK)
                  | (unfold AFMALLOC_RET in HU1; exact HU1)
                  | (unfold FUZZ_MALLOC_STACK_A, AMALLOC_STACK, AREQMAX; cbn; lia)
                  | (clear - SP16 G1; Z.div_mod_to_equations; lia) ]. }
        cbv beta. intros rb sZ RNGZ ms1 PO.
        destruct PO as (LE1 & w0 & w1 & w2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & w3 & w4 & w5 & w6 & mZ & pb & B & junk & -> & -> & MIZ & STZ & HPRZ & REST1 & BRB & AHZ & BLK & RB & RSB).
        rewrite ?unsigned_lit in STZ, HPRZ by lia. h_retlit.
        pose proof (HK_apres _ _ RNGX RNGZ sX sZ mY mZ _ HKY HILB HPRZ LE1 REST1 MIZ STZ _ AHZ) as HKZ.
        apply stk_of_rw_cells in BLK. cbn [cells_size csize Nat.add] in BLK. rewrite Nat.add_0_r, Z2Nat.id in BLK by lia.
        eapply (hz_D RNGZ sZ mZ _ p pd P DC B bsz rem (Some pb)); try eassumption.
        + right. exists pb. split; [reflexivity|]. split; [lia| reflexivity].
        + exact (dctx_apres AI _ (SP + -64) mY mZ pd DC HPRZ HDC DAY).
        + exact (rclean_apres AI _ (SP + -64) mY mZ rstk HPRZ RS3 RCY).
        + lia.
        + lia.
    Qed.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    Lemma hz_B : forall RNGX sX mX (p : AsanCtrl.aptr) (P : Z)
        (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      HK (HB p P PRODUCER_SIZE :: LB) RNGX sX mX (Z_to_bv 64 0) -> rclean mX rstk -> prod_at mX P D (zlen payload) ->
      implMA RNGX ((fun producer : option AsanCtrl.aptr =>
                      dctx <- Harness.fuzz_malloc amalloc_M (new_handlerA AAllocAsan) DCTX_SIZE ;;
                      rbuf <- Harness.fuzz_malloc amalloc_M (new_handlerA AAllocAsan) (buff_size payload) ;;
                      (Harness.free_opt afree_M rbuf ;;; (Harness.free_opt afree_M producer ;;; (Harness.free_opt afree_M dctx ;;; mret 0)))) (Some p)) sX POST
             (MS (mkR x1 (Z_to_bv 64 (SP + -64)) gp (Z_to_bv 64 ATP) t0 t1 t2 s0 (Z_to_bv 64 D) (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7
                      s2 s3 s4 (Z_to_bv 64 0x7fff8000) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x82a60) fc None mX (seg_rom bsegs)).
    Proof.
      intros RNGX sX mX p P x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HKX RCX PRX.
      pose proof HKX as (LE & AH & REST & MI & ST & FR & CELL & PL & ARO & HAG).
      pose proof geomH as (G1 & G2 & G3 & G4 & G5 & G6). pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
      pose proof HUL as (HU1 & HU2 & HU3 & HU4 & HU5).
      assert (HP : In (HB p P PRODUCER_SIZE) (HB p P PRODUCER_SIZE :: LB)) by (left; reflexivity).
      assert (HILB : forall b, In b LB -> In b (HB p P PRODUCER_SIZE :: LB)) by (intros b Hb; right; exact Hb).
      pose proof (fresh_not_in AI _ _ _ _ _ _ AH) as NPL.
      destruct (block_geom AI _ _ _ _ _ _ _ _ AH HP) as (PBR & _ & PTOP & P16 & PLO).
      destruct (payload_facts AI _ _ _ LB _ mX D payload AH HILB PAY (rng_fp_le _ _ _ _ LE RI) (rng_fp_le _ _ _ _ LE RISH)) as (D4096 & DTOPP & D8 & DARO & _).
      pose proof (payload_newblock AI L RNGX (aps_m sX) LB _ mX D payload p P PRODUCER_SIZE AH HILB PAY HP NPL) as DJ_PD.
      unfold DCTX_SIZE, PRODUCER_SIZE, AIMG_HI, zlength in *. unfold prod_at in PRX. unfold APDCTX in CELL. unfold HFR in FR.
      pose proof (art_of_aheap AI L RNGX (aps_m sX) _ mX AH) as ART.
      cbv beta.
      apply implMA_from_evtF.
      (* [comment removed for export] *)
      zstep. zstep.
      eapply evtF_cut.
      { eapply (RESERVE RNGX) with (P := P) (D := D) (pl := payload) (size := zlen payload) (lo := lo); try reflexivity.
        all: try assumption.
        all: try (clear - P16; Z.div_mod_to_equations; lia).
        all: try (clear - G1 G2 G3 G4 G5 G6 ATR BOT LOS D4096 DTOPP PTOP PLO DJ_PD SZ; lia).
        - split; [exact PL| exact PAYR].
        - eapply (areg_block AI L RNGX (aps_m sX)); [exact AH| exact HP| lia| lia| lia].
        - split; [unfold KHIGH; lia| split; [eapply rng_sub; [exact (rng_fp_le _ _ _ _ LE RSTK)| lia| lia]| exact (rng_fp_le _ _ _ _ LE RI)]]. }
      cbv beta. intros ms' PO.
      destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & mY & -> & MUY & WMY & MIY & STY & PRY).
      h_retlit.
      destruct (reserve_data_prefix payload (zlen payload)) as [rem eff] eqn:ERDP. cbn [fst snd] in *.
      assert (FWY : Forall (wok LB (HB p P 16 :: LB) L (SP + -64)) [(P, P + 16); (SP + -64 - 64, SP + -64)]).
      { constructor; [right; left; exists p, P, 16; split; [exact HP| split; [exact NPL| cbn; lia]]|].
        constructor; [left; cbn; lia| constructor]. }
      assert (AHY : AHEAP AI L RNGX (aps_m sX) (HB p P 16 :: LB) mY).
      { eapply (AI_frame AI); [exact AH| exact MUY| exact WMY|]. constructor; [| constructor; [| constructor]]; cbn [fst snd].
        - right; left. exists (HB p P 16). split; [exact HP| cbn; lia].
        - left; left. lia. }
      destruct (HK_kept _ (HB p P 16 :: LB) LB RNGX sX mX mY (Z_to_bv 64 0) _ HKX HLB ltac:(intros b Hb; exact Hb) HILB FWY MUY WMY MIY STY AHY)
        as [HKY AGY].
      pose proof (rclean_kept _ _ _ mY rstk AGY RS3 RCX) as RCY.
      clear HKX AGY MUY WMY MIY STY RCX ART PRX FWY LE AH REST MI ST FR CELL PL ARO HAG.
      pose proof HKY as (LE & AH & REST & MI & ST & FR & CELL & PL & ARO & HAG). unfold APDCTX in CELL. unfold HFR in FR.
      pose proof (rng_fp_le _ _ _ _ LE RSTK) as RSTKX. pose proof (rng_fp_le _ _ _ _ LE RI) as RIX.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. if_false. zstep.
      apply evtF_done.
      unfold Harness.fuzz_malloc at 1. change (0 <? 95992) with true. cbv iota.
      apply implMA_bind_assocH.
      eapply implMA_bind.
      { eapply (CREATEDCTX L RNGX) with (lo := lo); rewrite ?unsigned_lit by lia;
          first [ exact AH | exact MI | exact ST | reflexivity
                | exact (rng_fp_le _ _ _ _ LE RSTK) | exact (rng_fp_le _ _ _ _ LE RI)
                | exact (aps_ok_rest L sX s REST AOK)
                | (unfold ACDCTX_MRET in HU2; unfold ACREATEDCTX_MRET; exact HU2)
                | (unfold CREATEDCTX_STACK_A, AMALLOC_STACK; cbn; lia)
                | (clear - SP16 G1; Z.div_mod_to_equations; lia) ]. }
      cbv beta. intros r sZ RNGZ ms1 PO.
      destruct PO as (LE1 & v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & mZ & pd & DC & -> & -> & MIZ & STZ & HPRZ & REST1 & BRD & AHZ & DAZ & RD & RSD).
      rewrite ?unsigned_lit in STZ, HPRZ by lia. h_retlit.
      apply implMA_retbH. cbv beta.
      pose proof (HK_apres _ _ RNGX RNGZ sX sZ mY mZ _ HKY HILB HPRZ LE1 REST1 MIZ STZ _ AHZ) as HKZ.
      eapply (hz_C RNGZ sZ mZ p pd P DC rem eff); [exact HKZ| exact DAZ| | | symmetry; exact ERDP].
      - exact (rclean_apres AI _ (SP + -64) mY mZ rstk HPRZ RS3 RCY).
      - unfold prod_at. eapply (prod_apres AI (HB p P 16 :: LB) (SP + -64) mY mZ p P); [exact HPRZ| left; reflexivity| exact PRY| cbn; lia].
    Qed.
  End Run.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem zd_fuzz_one_proofA : fuzz_oneA_stmt AI rng_fs.
  Proof.
    unfold fuzz_oneA_stmt.
    intros L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB D payload lo rstk.
    intros AH HLB PAY PAYB PAYR D16 SZ HI ST BOT LOS SPG SP16 RC RS1 RS2 RS3 S0E MI FC TP A0 A1 RAE HUL RSTK RI RISH RFS RRS AOK.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (harness_topF L (bv_unsigned sp) SPG ltac:(lia)) as [T1 T2].
    pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & LY4 & _).
    assert (ALY : al_bot L + 0x800000 = al_top L /\ al_top L mod 4096 = 0 /\ al_top L <= 2^47 /\ (ATOP - 160 <= al_bot L <= ATOP + 3936))
      by (repeat split; lia).
    assert (HLB' : hb_heap LB) by exact HLB.
    unfold AHARNESS_STACK in LOS. pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    pose proof (art_of_aheap AI L RNG (aps_m s) LB m AH) as ART. pose proof ART as (GOT & RIC & SHB & INI & LAY & REAL).
    destruct HI as [CELL AROM]. unfold APDCTX in CELL.
    destruct (payload_facts AI _ _ _ LB LB m D payload AH ltac:(intros b Hb; exact Hb) PAY RI RISH) as (D4096 & DTOPP & D8 & _).
    unfold zlength in *.
    pose proof HUL as (HU1 & HU2 & HU3 & HU4 & HU5).
    unfold fuzz_oneA, Harness.fuzz_one.
    apply implMA_from_evtF.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    carve_frame 64%nat ST.
    subst a0 a1 tp. unfold AFUZZ_ENTRY.
    zstep. do 8 zstep. do 4 zstep.
    zstep. apply evtF_done.
    (* [comment removed for export] *)
    lazymatch goal with |- implMA _ _ _ _ (MS _ _ _ _ _ ?m1 _) =>
      assert (AH1 : AHEAP AI L RNG (aps_m s) LB m1);
      [ eapply (AI_frame AI); [exact AH| exact MU| exact WM|]; constructor; [cbn [fst snd]; left; left; lia| constructor] |];
      assert (AG1 : magree bsegs (kept LB (bv_unsigned sp)) m m1);
      [ eapply (kept_of_munch AI FHEAP L RNG (aps_m s) LB LB m); [exact AH| exact HLB'| intros b Hb; exact Hb| lia| | exact MU| exact WM];
        constructor; [left; cbn [fst snd]; lia| constructor] |];
      assert (HAG1 : magree bsegs (hcl CI LB (bv_unsigned sp)) m m1);
      [ eapply (hcl_of_munch AI FHEAP L RNG (aps_m s) LB LB m _ (bv_unsigned sp) (bv_unsigned sp)); [exact AH| exact HLB'| intros b Hb; exact Hb| lia| lia| lia| | exact MU| exact WM];
        constructor; [left; cbn [fst snd]; lia| constructor] |]
    end.
    pose proof (aroM_kept LB (bv_unsigned sp) m _ AG1 AROM) as ARO1.
    pose proof (rclean_kept LB (bv_unsigned sp) m _ rstk AG1 RS3 RC) as RC1.
    (* [comment removed for export] *)
    first [ rename PAYB into PL1 | pose proof (payload_kept LB (bv_unsigned sp) m _ D payload AG1 PAY PAYB) as PL1 ].
    clear AG1 MU WM.
    eapply implMA_bind.
    { eapply (prod_create_proofA AI (fuzz_malloc_proofA AI) L RNG) with (lo := lo); rewrite ?unsigned_lit by lia;
        first [ exact AH1 | exact ST | exact AOK | exact RSTK | exact RI | reflexivity | assumption
              | (unfold AFMALLOC_RET in HU1; exact HU1)
              | (unfold PROD_CREATE_STACK_A, FUZZ_MALLOC_STACK_A, AMALLOC_STACK; cbn; lia)
              | (clear - SP16 RSP; Z.div_mod_to_equations; lia) ]. }
    cbv beta. intros r sY RNGY ms1 PO.
    destruct PO as (LE1 & u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & mY & p & P & -> & -> & MIY & STY & HPRY & REST1 & BRP & AHY & PRC & RP & RSP').
    rewrite ?unsigned_lit in STY, HPRY by lia. h_retlit.
    assert (HKY : HK L RNG ra sp s0 s1 s2 s3 s4 s5 s6 m s LB D payload lo (HB p P PRODUCER_SIZE :: LB) RNGY sY mY (Z_to_bv 64 0)).
    { split; [exact LE1|]. split; [exact AHY|]. split; [exact REST1|]. split; [exact MIY|]. split; [exact STY|].
      split; [unfold HFR; eapply (frame_apres AI LB (bv_unsigned sp + -64)); [exact HPRY| lia| cbn; lia| assumption]|].
      split; [eapply (cell_apres AI CLI_CI LB (bv_unsigned sp + -64)); [exact HPRY| assumption]|].
      split; [exact (payload_apres AI LB LB (bv_unsigned sp + -64) _ mY D payload HPRY ltac:(intros b Hb; exact Hb) PAY PL1)|].
      split; [exact (aroM_apres AI CLI_CI DRV_CI LB (bv_unsigned sp + -64) _ mY HPRY ARO1)|].
      eapply magree_trans; [exact HAG1|]. eapply (hcl_of_aheap_pres AI LB LB (bv_unsigned sp) (bv_unsigned sp + -64)); [exact HPRY| intros b Hb; exact Hb| lia| lia]. }
    eapply hz_B; try eassumption; try exact HKY.
    all: try (unfold AHARNESS_STACK; lia).
    all: try exact (conj HU1 (conj HU2 (conj HU3 (conj HU4 HU5)))).
    all: try exact (rclean_apres AI LB (bv_unsigned sp + -64) _ mY rstk HPRY RS3 RC1).
    all: unfold prod_at; exact PRC.
  Qed.
End Harness.
End CANSEC1.
