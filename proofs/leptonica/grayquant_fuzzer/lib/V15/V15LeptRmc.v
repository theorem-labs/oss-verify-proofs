(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.grayquant_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac FPSteps FPStepsV.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import SumWalkTac WalksLib W2Lib LeptDefs LeptStructs LeptArith LeptRoom LeptRoomPC LeptRoom14 DitherLib DitherLoop LeptCmapArr LeptRmcLib LeptGrayFP.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15LeptBase.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15CL8a.
Import V15CL8a.V15LeptPixHdr.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15LeptPixCreate.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15CL10a.
Import V15CL10a.V15LeptCmapValid. Import V15CL10a.V15LeptPixCreateS.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15LeptCmap2 V15LeptPixCopy.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15CL14a.
Import V15CL14a.V15LeptDither_iface.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15LeptCmapArr V15LeptRmcSegs.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15CL2a.
Import V15CL2a.V15LeptRmcFP.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15LeptRmcLoops.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac rdn_solve4 :=
  lazymatch goal with
  | |- rdn _ (wbytes _ ?a _) ?b _ = _ =>
      tryif constr_eq a b then (lazymatch goal with |- rdn _ _ _ 4 = _ => apply rdn_wbytes_hit4 | |- rdn _ _ _ 8 = _ => apply rdn_wbytes_hit8 end; zsimp; lia)
      else (rdn_peel1; rdn_solve4)
  | |- _ => rdn_hyp
  end.

Section Rmc.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V15Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Definition rmc_cells (s : Z) (regs : bvmap 5 word) : list (Z * word) :=
  [((s - 8)%Z, getr regs 1); ((s - 16)%Z, getr regs 8); ((s - 24)%Z, getr regs 9); ((s - 32)%Z, getr regs 18); ((s - 40)%Z, getr regs 19);
   ((s - 48)%Z, getr regs 20); ((s - 56)%Z, getr regs 21); ((s - 64)%Z, getr regs 22); ((s - 72)%Z, getr regs 23); ((s - 80)%Z, getr regs 24);
   ((s - 88)%Z, getr regs 25); ((s - 96)%Z, getr regs 26); ((s - 104)%Z, getr regs 27)].

Lemma rmc_cells_RMCF : forall {fx : FPState} m s regs, (272 <= s)%Z -> (s < 2 ^ 63)%Z -> cellsZ (RMCF m s regs) (rmc_cells s regs).
Proof. intros fx m s regs Hs Hs63. unfold cellsZ, rmc_cells, RMCF. repeat split; rdn_solve. Qed.

Lemma cell_w2z : forall {fx : FPState} (M : word -> option byte) (a : Z) (v : word),
  rdn SEGS M (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 v) -> rdn SEGS M (Z_to_bv 64 a) 8 = Some (Z_to_le_bytes 8 (u v)).
Proof. intros fx M a v R. rewrite <- (w2b_Z 8 (u v)) by (pose proof (u64_range v); lia). rewrite zbv_self. exact R. Qed.

(* [comment removed for export] *)
Lemma wpl8_ge : forall w, (1 <= w)%Z -> (w <= 4 * wpl_of w 8)%Z.
Proof. intros w Hw. unfold wpl_of. pose proof (Z.div_mod (w * 8 + 31) 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (w * 8 + 31) 32 ltac:(lia)) as B. lia. Qed.

(* [comment removed for export] *)
Lemma rmc_c03_val : forall {fx : FPState}, rdn SEGS (fun _ => None) (Z_to_bv 64 0x11720) 4 = Some (Z_to_le_bytes 4 GC_03f). Proof. intros. vm_refl_bv. Qed.
Lemma rmc_c02_val : forall {fx : FPState}, rdn SEGS (fun _ => None) (Z_to_bv 64 0x11714) 4 = Some (Z_to_le_bytes 4 GC_02f). Proof. intros. vm_refl_bv. Qed.
Lemma rmc_c05_val : forall {fx : FPState}, rdn SEGS (fun _ => None) (Z_to_bv 64 0x11638) 8 = Some (Z_to_le_bytes 8 GC_05d). Proof. intros. vm_refl_bv. Qed.
Lemma rmc_cm1_val : forall {fx : FPState}, rdn SEGS (fun _ => None) (Z_to_bv 64 0x11608) 8 = Some (Z_to_le_bytes 8 GC_m1d). Proof. intros. vm_refl_bv. Qed.
Lemma rmc_c2p_val : forall {fx : FPState}, rdn SEGS (fun _ => None) (Z_to_bv 64 0x11618) 8 = Some (Z_to_le_bytes 8 GC_2p32d). Proof. intros. vm_refl_bv. Qed.
Lemma W_rmc_ro : forall {fx : FPState} C A m md (a : Z) (k : nat) bs, W C A m md -> (0x10000 <= a)%Z -> (a + Z.of_nat k <= 0x34000)%Z ->
  rdn SEGS (fun _ => None) (Z_to_bv 64 a) k = Some bs -> rdn SEGS m (Z_to_bv 64 a) k = Some bs.
Proof. intros fx C A m md a k bs HW Ha Hk R. rewrite <- p16_segs. rewrite (W_rdn_ro C A m md a k HW); [rewrite p16_segs; exact R | |]; cbn [fst snd ll_ro LLU16]; lia. Qed.

Theorem pixRemoveColormap_gray8_W : pixRemoveColormap_gray8_contract.
Proof.
  unfold pixRemoveColormap_gray8_contract.
  intros fx C A m md regs s pixs w h cm data cv ret S Hz CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 PX HOK Hw1 Hh1 Lp L0p Ld CMF kR bR Hrm HkR HbR HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  unfold RMC_STACK, LSF, PC_pixRemoveColormap, TP15, RK_rmc, RB_rmc, RK_pix, RB_pix14 in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  destruct HOK as (DV & Hw2 & Hh2 & Hsz).
  pose proof PX as (Hp0 & Hp64 & WFp & _).
  destruct (blk_range C A m md (Z_to_bv 64 pixs) 64 CK HW Lp ltac:(lia)) as [Gp TOPp]. rewrite u_Z2bv in Gp, TOPp by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lp) as (_ & ALp & _). rewrite u_Z2bv in ALp by lia.
  pose proof (wpl_of_range w 8 ltac:(lia) DV) as Hwpl. pose proof (wpl8_ge w Hw1) as Hw4.
  pose proof (PIX_rd_cmap SEGS m pixs _ PX) as Ccm. cbn [p_cmap hdv] in Ccm.
  pose proof (W_sok_win C A m md (s - 272) 272 CK HW ltac:(lia) ltac:(cbn; lia)) as SOK.
  assert (ALp8 : (pixs mod 8 = 0)%Z) by (clear - ALp; Z.div_mod_to_equations; lia).
  destruct CMF as [CM0 | (CM & CMOK & Lcm & Larr)].
  - (* [comment removed for export] *)
    subst cm.
    destruct (rmc_S0z al_rom fx regs m s pixs ltac:(lia) ltac:(lia) ltac:(lia) ALp8 SOK Ccm ltac:(left; lia) H2 H10) as (r1 & RUN1 & Q11 & Q12 & AG1).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
    assert (WP1 : W C A (RMCF m s regs) md /\ POSTM C A s m (RMCF m s regs)) by (unfold RMCF; wp_win CK).
    destruct WP1 as [HW1 PM1].
    assert (OUT1 : forall x : word, ~ (s - 272 <= u x < s)%Z -> RMCF m s regs x = m x).
    { intros x Hx. unfold RMCF. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
    assert (PX1 : PIXat (RMCF m s regs) pixs (hdv w h 8 0 data)) by (apply (PIXat_frame m); [exact PX | intros x Hx; apply OUT1; lia]).
    pose proof (PIX_rd_rc SEGS _ pixs _ PX1) as Crc. cbn [p_rc hdv] in Crc.
    pose proof (rmc_clone_tail al_rom fx r1 (RMCF m s regs) pixs ret ltac:(lia) ltac:(lia) ltac:(clear - ALp; Z.div_mod_to_equations; lia) Crc
                  (reg_sok SEGS _ _ pixs 64 (pixs + 20) 4 (mem_grows_refl _) (blk_sok C A _ md pixs 64 CK HW1 Lp ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia))
                  Hret ltac:(rewrite (AG1 1%bv) by notin_list; exact H1) Q11 Q12) as RUN2.
    replace (Z_to_bv 64 0x179d0) with (0x179d0 : word) in RUN1 |- * by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN2 |].
    rewrite <- (with_vmmaps_same md).
    apply (HK fx A _ (m_vmmaps md) r1 Hz).
    + rewrite with_vmmaps_same. rewrite <- (w2b_Z 4 2) by lia.
      apply (W_store_blk C A _ md (Z_to_bv 64 pixs) _ 64 _ CK HW1 Lp L0p); rewrite ?length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia.
    + apply cs_kept_intro; (rewrite (AG1 _) by notin_list; reflexivity).
    + left. split; [reflexivity|]. split; [rewrite (AG1 10%bv) by notin_list; exact H10|]. split; [reflexivity|].
      assert (HWr : W C A (wbytes m (Z_to_bv 64 (pixs + 20)) (Z_to_le_bytes 4 2)) md).
      { rewrite <- (w2b_Z 4 2) by lia. apply (W_store_blk C A _ md (Z_to_bv 64 pixs) _ 64 _ CK HW Lp L0p); rewrite ?length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia. }
      apply (POSTM_range C A _ md _ (s - 272) s s CK HWr); [|lia|lia|lia].
      intros x Hx.
      destruct (Z_le_gt_dec (pixs + 20) (u x)) as [G1|G1]; [destruct (Z_lt_ge_dec (u x) (pixs + 24)) as [G2|G2]|].
      * rewrite !wbytes_inside by (rewrite ?length_Z_to_le_bytes, ?u_Z2bv by lia; cbn; lia). reflexivity.
      * rewrite !wbytes_outside by (rewrite ?length_Z_to_le_bytes, ?u_Z2bv by lia; cbn; lia). apply OUT1. exact Hx.
      * rewrite !wbytes_outside by (rewrite ?length_Z_to_le_bytes, ?u_Z2bv by lia; cbn; lia). apply OUT1. exact Hx.
    + apply (aroom_mono A _ kR bR); [exact Hrm | lia | lia].
  - (* [comment removed for export] *)
    pose proof CMOK as (Hd & Hna & Hn & Harr1). pose proof CM as (Hc0 & Hc64 & WFc & _).
    assert (Hna256 : (c_nalloc cv <= 256)%Z) by (clear - Hd Hna; destruct Hd as [E|[E|[E|E]]]; rewrite Hna, E; cbn; lia).
    set (n := c_n cv) in *.
    destruct (blk_range C A m md (Z_to_bv 64 cm) 24 CK HW Lcm ltac:(lia)) as [Gcm TOPcm]. rewrite u_Z2bv in Gcm, TOPcm by lia.
    pose proof (PIX_rd_w SEGS m pixs _ PX) as Cw. pose proof (PIX_rd_h SEGS m pixs _ PX) as Ch. pose proof (PIX_rd_d SEGS m pixs _ PX) as Cd.
    cbn [p_w p_h p_d hdv] in Cw, Ch, Cd. rewrite <- (Z.add_0_r pixs) in Cw.
    (* [comment removed for export] *)
    pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lcm) as (_ & ALcm & _). rewrite u_Z2bv in ALcm by lia.
    assert (ALcm8 : (cm mod 8 = 0)%Z) by (clear - ALcm; Z.div_mod_to_equations; lia).
    destruct (rmc_S0 al_rom fx regs m s pixs cm w h n ltac:(lia) Hs16 ltac:(lia) ltac:(lia) ALp8 ltac:(lia) ltac:(lia) ALcm8 ltac:(lia) ltac:(lia) ltac:(lia) SOK Ccm Cw Ch Cd
                (CMAP_rd_n SEGS m cm cv CM) ltac:(left; lia) ltac:(left; lia) H2 H10 H11)
      as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q12 & Q13 & Q14 & Q19 & Q20 & Q22 & Q23 & AG1).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
    assert (WP1 : W C A (RMC0n m s w h n regs) md /\ POSTM C A s m (RMC0n m s w h n regs)) by (unfold RMC0n, RMC0, RMCF; wp_win CK).
    destruct WP1 as [HW1 PM1].
    assert (OUT1 : forall x : word, ~ (s - 272 <= u x < s)%Z -> RMC0n m s w h n regs x = m x).
    { intros x Hx. unfold RMC0n, RMC0, RMCF. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
    assert (CE1 : cellsZ (RMC0n m s w h n regs) (rmc_cells s regs)).
    { apply (cellsZ_out (RMCF m s regs) _ (s - 192) (s - 116)); [| | apply rmc_cells_RMCF; lia].
      - intros x Hx. unfold RMC0n, RMC0. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity.
      - unfold rmc_cells. repeat (apply Forall_cons; [cbn [fst]; split; [lia | split; [lia | left; lia]] |]). apply Forall_nil. }
    assert (FD1 : rdn SEGS (RMC0n m s w h n regs) (Z_to_bv 64 (s - 120)) 4 = Some (Z_to_le_bytes 4 w)
                  /\ rdn SEGS (RMC0n m s w h n regs) (Z_to_bv 64 (s - 124)) 4 = Some (Z_to_le_bytes 4 h)
                  /\ rdn SEGS (RMC0n m s w h n regs) (Z_to_bv 64 (s - 128)) 4 = Some (Z_to_le_bytes 4 8)
                  /\ rdn SEGS (RMC0n m s w h n regs) (Z_to_bv 64 (s - 192)) 8 = Some (Z_to_le_bytes 8 n)).
    { rewrite <- (w2b_Z 4 w), <- (w2b_Z 4 h), <- (w2b_Z 4 8), <- (w2b_Z 8 n) by lia. unfold RMC0n, RMC0. repeat split; rdn_solve4. }
    destruct FD1 as (Fw1 & Fh1 & Fd1 & Fn1).
    set (M1 := RMC0n m s w h n regs) in *.
    assert (CM1 : CMAPat M1 cm cv) by (apply (CMAPat_frame m); [exact CM | intros x Hx; apply OUT1; lia]).
    assert (Q4 : getr r1 4 = Z_to_bv 64 0x455c0) by (rewrite (AG1 4%bv) by notin_list; exact H4).
    replace (s - 152)%Z with (s - 176 + 24)%Z in Q11 by lia. replace (s - 160)%Z with (s - 176 + 16)%Z in Q12 by lia. replace (s - 168)%Z with (s - 176 + 8)%Z in Q13 by lia.
    apply (@pixcmapToArrays_W fx AL CL ASR PINS P16 C A M1 md r1 (s - 272) (s - 176) cm cv (Z_to_bv 64 0x1a0dc) S CK HW1 Q2
             ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold PTA_STACK, CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia) ltac:(lia)
             ltac:(clear - Hs16; Z.div_mod_to_equations; lia) Q1 ltac:(red; apply bv_eq; reflexivity) Q4 Q10 Q11 Q12 Q13 Q14 CM1 CMOK Lcm Larr
             kR bR Hrm ltac:(unfold RK_pta; lia) ltac:(unfold RB_pta; lia)).
    intros A2 m2 vm2 r2 rm gm bm am HW2 CS2 E10 PM2 KP2 PN2 Hrm2.
    destruct PN2 as (BNr & BNg & BNb & BNa & NErg & NErb & NEra & NEgb & NEga & NEba & LEQ2 & Qr & Qg & Qb & Qa & Ar2 & Ag2 & Ab2).
    apply box_i in NErg, NErb, NEra, NEgb, NEga, NEba. clear Hd.
    replace (s - 176 + 32)%Z with (s - 144)%Z in PM2 by lia.
    replace (s - 176 + 24)%Z with (s - 152)%Z in Qr by lia. replace (s - 176 + 16)%Z with (s - 160)%Z in Qg by lia. replace (s - 176 + 8)%Z with (s - 168)%Z in Qb by lia.
    unfold RK_pta, RB_pta in Hrm2.
    assert (SUB2 : sub_live A A2).
    { intros q k Lq. destruct BNr as (_ & _ & _ & Lr0 & _). destruct BNg as (_ & _ & _ & Lg0 & _). destruct BNb as (_ & _ & _ & Lb0 & _). destruct BNa as (_ & _ & _ & La0 & _).
      rewrite LEQ2; [exact Lq | | | |]; intros ->; congruence. }
    pose proof (cellsZ_frm C (s - 144) M1 m2 (rmc_cells s regs) CK (proj1 PM2) ltac:(lia) ltac:(unfold rmc_cells; repeat (apply Forall_cons; [cbn [fst]; lia|]); apply Forall_nil) CE1) as CE2.
    assert (PMa2 : POSTM C A s m m2) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PM2]; lia]).
    pose proof Fw1 as Fw2. pose proof Fh1 as Fh2. pose proof Fd1 as Fd2.
    assert (Fn2 : rdn SEGS m2 (Z_to_bv 64 (s - 192)) 8 = Some (Z_to_le_bytes 8 n)).
    { rewrite <- Fn1. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx. apply KP2. lia. }
    rewrite <- (FRM_rdn16 C (s - 144) M1 m2 (s - 120) 4 CK (proj1 PM2)) in Fw2 by (cbn; lia).
    rewrite <- (FRM_rdn16 C (s - 144) M1 m2 (s - 124) 4 CK (proj1 PM2)) in Fh2 by (cbn; lia).
    rewrite <- (FRM_rdn16 C (s - 144) M1 m2 (s - 128) 4 CK (proj1 PM2)) in Fd2 by (cbn; lia).
    assert (PX2 : PIXat m2 pixs (hdv w h 8 cm data)).
    { apply (PIXat_frame m); [exact PX|]. intros x Hx. exact (LIVK_at A m m2 pixs 64 x (proj2 PMa2) Lp ltac:(lia) ltac:(lia) Hx). }
    (* [comment removed for export] *)
    assert (E2r2 : getr r2 2 = Z_to_bv 64 (s - 272)) by (csr; reflexivity).
    assert (E19r2 : getr r2 19 = Z_to_bv 64 pixs) by (csr; reflexivity).
    assert (E23r2 : getr r2 23 = Z_to_bv 64 1) by (csr; reflexivity).
    assert (E4r2 : getr r2 4 = Z_to_bv 64 0x455c0) by (csr; reflexivity).
    pose proof (PIX_rd_data SEGS m2 pixs _ PX2) as Cdata2. pose proof (PIX_rd_wpl SEGS m2 pixs _ PX2) as Cwpl2. cbn [p_data p_wpl hdv] in Cdata2, Cwpl2.
    assert (Hraster : (0 < 4 * (wpl_of w 8 * h))%Z) by (clear - Hwpl Hh1 Hw1 Hw4; assert (1 <= wpl_of w 8)%Z by lia; nia).
    assert (Hdata64 : (0 <= data < 2 ^ 64)%Z) by (destruct WFp; cbn [p_data hdv] in *; assumption).
    destruct (blk_range C A m md (Z_to_bv 64 data) _ CK HW Ld Hraster) as [Gd TOPd]. rewrite u_Z2bv in Gd, TOPd by (clear - Hdata64; lia).
    destruct (rmc_S1 al_rom fx r2 m2 s pixs w h data (wpl_of w 8) ltac:(lia) ltac:(lia) ltac:(lia) ALp8 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                (W_sok_win C A2 m2 _ (s - 272) 272 CK HW2 ltac:(lia) ltac:(cbn; lia)) Cdata2 Cwpl2 Fw2 Fh2 ltac:(left; lia) E2r2 E10 E19r2 E23r2)
      as (r3 & RUN3 & X1 & X10 & X11 & X12 & X18 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN3 |].
    assert (WP3 : W C A2 (RMC1 m2 s data) (with_vmmaps vm2 md) /\ POSTM C A s m (RMC1 m2 s data)) by (unfold RMC1; wp_win CK).
    destruct WP3 as [HW3 PM3].
    assert (OUT3 : forall x : word, ~ (s - 184 <= u x < s - 176)%Z -> RMC1 m2 s data x = m2 x).
    { intros x Hx. unfold RMC1. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
    assert (Fds3 : rdn SEGS (RMC1 m2 s data) (Z_to_bv 64 (s - 184)) 8 = Some (Z_to_le_bytes 8 data)).
    { rewrite <- (w2b_Z 8 data) by lia. unfold RMC1. rdn_solve4. }
    set (M3 := RMC1 m2 s data) in *.
    pose proof (cellsZ_out m2 M3 (s - 184) (s - 176) (rmc_cells s regs) OUT3
                  ltac:(unfold rmc_cells; repeat (apply Forall_cons; [cbn [fst]; split; [lia | split; [lia | left; lia]] |]); apply Forall_nil) CE2) as CE3.
    assert (KEEP3 : forall (a : Z) (k : nat) bs, (s - 176 <= a \/ a + Z.of_nat k <= s - 184)%Z -> (0 <= a)%Z -> (a + Z.of_nat k <= 2 ^ 64)%Z ->
                    rdn SEGS m2 (Z_to_bv 64 a) k = Some bs -> rdn SEGS M3 (Z_to_bv 64 a) k = Some bs).
    { intros a k bs Ha Ha0 Ha64 R. rewrite <- R. destruct k as [|k']; [reflexivity|]. apply rdn_ext; rewrite u_Z2bv by lia; [lia|]. intros x Hx. apply OUT3. lia. }
    pose proof (KEEP3 (s - 120)%Z 4%nat _ ltac:(left; lia) ltac:(lia) ltac:(cbn; lia) Fw2) as Fw3. pose proof (KEEP3 (s - 124)%Z 4%nat _ ltac:(left; lia) ltac:(lia) ltac:(cbn; lia) Fh2) as Fh3.
    pose proof (KEEP3 (s - 128)%Z 4%nat _ ltac:(left; lia) ltac:(lia) ltac:(cbn; lia) Fd2) as Fd3.
    pose proof (KEEP3 (s - 152)%Z 8%nat _ ltac:(left; lia) ltac:(lia) ltac:(cbn; lia) Qr) as Qr3. pose proof (KEEP3 (s - 160)%Z 8%nat _ ltac:(left; lia) ltac:(lia) ltac:(cbn; lia) Qg) as Qg3.
    pose proof (KEEP3 (s - 168)%Z 8%nat _ ltac:(left; lia) ltac:(lia) ltac:(cbn; lia) Qb) as Qb3. pose proof (KEEP3 (s - 176)%Z 8%nat _ ltac:(left; lia) ltac:(lia) ltac:(cbn; lia) Qa) as Qa3.
    pose proof (KEEP3 (s - 192)%Z 8%nat _ ltac:(right; cbn; lia) ltac:(lia) ltac:(cbn; lia) Fn2) as Fn3.
    assert (X4 : getr r3 4 = Z_to_bv 64 0x455c0) by (rewrite (AG3 4%bv) by notin_list; exact E4r2).
    assert (X2 : getr r3 2 = Z_to_bv 64 (s - 272)) by (rewrite (AG3 2%bv) by notin_list; exact E2r2).
    (* [comment removed for export] *)
    replace (Z_to_bv 64 0x16b48) with (0x16b48 : word) by (apply bv_eq; reflexivity).
    apply (@pixCreate_sure_W fx AL CL ASR PINS P16 C A2 M3 _ r3 (s - 272) w h 8 (Z_to_bv 64 0x1a84c) S CK HW3 X2
             ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia) X1 ltac:(red; apply bv_eq; reflexivity) X4 X10 X11 X12 Hw1 Hh1
             ltac:(unfold hdr_ok; repeat split; assumption) (kR - 4) (bR - 4 * 2 ^ 17) ltac:(rewrite with_vmmaps_vmmaps; exact Hrm2) ltac:(unfold RK_pix; lia) ltac:(unfold RB_pix14; lia)).
    intros A4 m4 vm4 r4 pixd datad HW4 CS4 PM4 E10d PN4 Hrm4. rewrite with_vmmaps_twice. rewrite with_vmmaps_twice in HW4.
    destruct PN4 as (Gpd & TOPpd & ALpd & Gdd & TOPdd & ALdd & NEpd & LApd & LAdd & L0pd & L0dd & L4pd & L4dd & LEQ4 & PXd4 & _).
    cbn [p_wpl p_h set_data pix_hdr] in TOPdd, L4dd. apply box_i in NEpd.
    assert (SUB24 : sub_live A2 A4).
    { intros q k Lq. rewrite LEQ4; [exact Lq | |]; intros ->; congruence. }
    assert (SUB4 : sub_live A A4) by (exact (sub_live_trans _ _ _ SUB2 SUB24)).
    pose proof (cellsZ_frm C (s - 272) M3 m4 (rmc_cells s regs) CK (proj1 PM4) ltac:(lia) ltac:(unfold rmc_cells; repeat (apply Forall_cons; [cbn [fst]; lia|]); apply Forall_nil) CE3) as CE4.
    assert (PMa4 : POSTM C A s m m4).
    { eapply POSTM_trans; [exact PM3|]. apply (POSTM_sub C A A2); [exact SUB2|]. eapply POSTM_mono; [|exact PM4]. lia. }
    assert (FR4 : forall (a : Z) (k : nat) bs, (s - 272 <= a)%Z -> (a + Z.of_nat k <= s)%Z -> rdn SEGS M3 (Z_to_bv 64 a) k = Some bs -> rdn SEGS m4 (Z_to_bv 64 a) k = Some bs).
    { intros a k bs Ha1 Ha2 R. rewrite (FRM_rdn16 C (s - 272) M3 m4 a k CK (proj1 PM4)) by lia. exact R. }
    pose proof (FR4 (s - 120)%Z 4%nat _ ltac:(lia) ltac:(cbn; lia) Fw3) as Fw4. pose proof (FR4 (s - 124)%Z 4%nat _ ltac:(lia) ltac:(cbn; lia) Fh3) as Fh4. pose proof (FR4 (s - 128)%Z 4%nat _ ltac:(lia) ltac:(cbn; lia) Fd3) as Fd4.
    pose proof (FR4 (s - 152)%Z 8%nat _ ltac:(lia) ltac:(cbn; lia) Qr3) as Qr4. pose proof (FR4 (s - 160)%Z 8%nat _ ltac:(lia) ltac:(cbn; lia) Qg3) as Qg4.
    pose proof (FR4 (s - 168)%Z 8%nat _ ltac:(lia) ltac:(cbn; lia) Qb3) as Qb4. pose proof (FR4 (s - 176)%Z 8%nat _ ltac:(lia) ltac:(cbn; lia) Qa3) as Qa4.
    pose proof (FR4 (s - 184)%Z 8%nat _ ltac:(lia) ltac:(cbn; lia) Fds3) as Fds4. pose proof (FR4 (s - 192)%Z 8%nat _ ltac:(lia) ltac:(cbn; lia) Fn3) as Fn4.
    assert (PX4 : PIXat m4 pixs (hdv w h 8 cm data)).
    { apply (PIXat_frame m); [exact PX|]. intros x Hx. exact (LIVK_at A m m4 pixs 64 x (proj2 PMa4) Lp ltac:(lia) ltac:(lia) Hx). }
    (* [comment removed for export] *)
    assert (LApd' : live A (Z_to_bv 64 pixd) = None) by (destruct (live A (Z_to_bv 64 pixd)) as [z|] eqn:E; [rewrite (SUB2 _ _ E) in LApd; discriminate LApd | reflexivity]).
    assert (LAdd' : live A (Z_to_bv 64 datad) = None) by (destruct (live A (Z_to_bv 64 datad)) as [z|] eqn:E; [rewrite (SUB2 _ _ E) in LAdd; discriminate LAdd | reflexivity]).
    assert (NEppd : Z_to_bv 64 pixs <> Z_to_bv 64 pixd) by (intros E; rewrite E in Lp; rewrite LApd' in Lp; discriminate Lp).
    pose proof (blk_apart C A4 m4 _ _ _ _ _ CK HW4 (SUB4 _ _ Lp) L4pd NEppd ltac:(lia) ltac:(lia)) as APppd. rewrite !u_Z2bv in APppd by lia. apply box_i in APppd.
    assert (ALpd8 : (pixd mod 8 = 0)%Z) by (clear - ALpd; Z.div_mod_to_equations; lia).
    assert (E2r4 : getr r4 2 = Z_to_bv 64 (s - 272)) by (csr; reflexivity).
    assert (E19r4 : getr r4 19 = Z_to_bv 64 pixs) by (csr; reflexivity).
    assert (E22r4 : getr r4 22 = Z_to_bv 64 256) by (csr; reflexivity).
    assert (E18r4 : getr r4 18 = Z_to_bv 64 (wpl_of w 8)) by (csr; reflexivity).
    assert (E4r4 : getr r4 4 = Z_to_bv 64 0x455c0) by (csr; reflexivity).
    pose proof (PIX_rd_data SEGS m4 pixd _ PXd4) as Cdd4. pose proof (PIX_rd_wpl SEGS m4 pixd _ PXd4) as Cwd4. cbn [p_data p_wpl set_data pix_hdr] in Cdd4, Cwd4.
    destruct (rmc_S2 al_rom fx r4 m4 s pixs pixd datad (wpl_of w 8) (wpl_of w 8) ltac:(lia) ltac:(lia) ltac:(lia) ALp8 ltac:(lia) ltac:(lia) ALpd8 ltac:(lia) ltac:(lia) ltac:(lia)
                (W_sok_win C A4 m4 _ (s - 272) 272 CK HW4 ltac:(lia) ltac:(cbn; lia)) (blk_sok C A4 m4 _ pixd 64 CK HW4 L4pd ltac:(lia) ltac:(lia) ltac:(lia))
                (PIX_rd_res0 SEGS m4 pixs _ PX4 eq_refl eq_refl) (PIX_rd_fmt SEGS m4 pixs _ PX4) Cdd4 Cwd4 ltac:(left; lia) ltac:(left; lia) (box_e _ APppd)
                E2r4 E10d E19r4 E22r4 E18r4) as (r5 & RUN5 & Y1 & Y10 & Y11 & AG5).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact RUN5 |].
    set (Ma := wbytes m4 (Z_to_bv 64 (s - 256)) (word_to_le_bytes 8 (Z_to_bv 64 (wpl_of w 8)))).
    assert (WPa : W C A4 Ma (with_vmmaps vm4 md) /\ POSTM C A s m Ma) by (subst Ma; wp_win CK).
    set (Mb := wbytes (wbytes Ma (Z_to_bv 64 (pixd + 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (pixd + 32)) (word_to_le_bytes 4 (Z_to_bv 64 0))).
    assert (WPb : W C A4 Mb (with_vmmaps vm4 md) /\ POSTM C A s m Mb).
    { subst Mb. do 2 (apply (WP_blk C A A4 m _ _ (Z_to_bv 64 pixd) _ 64); [exact CK | | exact L4pd | exact LApd' | exact L0pd | exact SUB4 | rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia]).
      exact WPa. }
    destruct WPb as [HWb PMb].
    assert (WP5 : W C A4 (RMC2 m4 s (wpl_of w 8) pixd datad (wpl_of w 8)) (with_vmmaps vm4 md) /\ POSTM C A s m (RMC2 m4 s (wpl_of w 8) pixd datad (wpl_of w 8))) by (unfold RMC2; fold Ma; fold Mb; wp_win CK).
    destruct WP5 as [HW5 PM5].
    assert (OUT5 : forall x : word, ~ (pixd + 24 <= u x < pixd + 36)%Z -> ~ (s - 264 <= u x < s - 248)%Z -> ~ (s - 208 <= u x < s - 192)%Z ->
                   RMC2 m4 s (wpl_of w 8) pixd datad (wpl_of w 8) x = m4 x).
    { intros x Hx1 Hx2 Hx3. unfold RMC2. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
    assert (PXd5 : PIXat (RMC2 m4 s (wpl_of w 8) pixd datad (wpl_of w 8)) pixd (hdv w h 8 0 datad)).
    { unfold RMC2. apply (PIXat_frame Mb).
      - subst Mb. apply PIX_wr_fmt0; [|reflexivity]. apply PIX_wr_res0; [|reflexivity|reflexivity].
        apply (PIXat_frame m4); [exact PXd4|]. intros x Hx. subst Ma. apply wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; lia.
      - intros x Hx. fold Ma. fold Mb. do 3 (rewrite wbytes_outside by (rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; lia)). reflexivity. }
    assert (FS5 : rdn SEGS (RMC2 m4 s (wpl_of w 8) pixd datad (wpl_of w 8)) (Z_to_bv 64 (s - 200)) 8 = Some (Z_to_le_bytes 8 datad)
                  /\ rdn SEGS (RMC2 m4 s (wpl_of w 8) pixd datad (wpl_of w 8)) (Z_to_bv 64 (s - 264)) 8 = Some (Z_to_le_bytes 8 pixd)
                  /\ rdn SEGS (RMC2 m4 s (wpl_of w 8) pixd datad (wpl_of w 8)) (Z_to_bv 64 (s - 208)) 8 = Some (Z_to_le_bytes 8 (wpl_of w 8))
                  /\ rdn SEGS (RMC2 m4 s (wpl_of w 8) pixd datad (wpl_of w 8)) (Z_to_bv 64 (s - 256)) 8 = Some (Z_to_le_bytes 8 (wpl_of w 8))).
    { rewrite <- (w2b_Z 8 datad), <- (w2b_Z 8 pixd), <- (w2b_Z 8 (wpl_of w 8)) by lia. unfold RMC2. repeat split; rdn_solve4. }
    destruct FS5 as (Fdd5 & Fpd5 & Fwd5 & Fws5).
    set (M5 := RMC2 m4 s (wpl_of w 8) pixd datad (wpl_of w 8)) in *.
    assert (KEEP5 : forall (a : Z) (k : nat) bs, (s - 192 <= a)%Z -> (a + Z.of_nat k <= s)%Z ->
                    rdn SEGS m4 (Z_to_bv 64 a) k = Some bs -> rdn SEGS M5 (Z_to_bv 64 a) k = Some bs).
    { intros a k bs Ha Ha3 R. rewrite <- R. destruct k as [|k']; [reflexivity|]. apply rdn_ext; rewrite u_Z2bv by lia; [lia|]. intros x Hx. apply OUT5; lia. }
    pose proof (cellsZ_keep m4 M5 (rmc_cells s regs)
                  ltac:(unfold rmc_cells; repeat (apply Forall_cons; [cbn [fst]; split; [lia | split; [lia | intros x Hx; apply OUT5; lia]] |]); apply Forall_nil) CE4) as CE5.
    pose proof (KEEP5 (s - 120)%Z 4%nat _ ltac:(lia) ltac:(cbn; lia) Fw4) as Fw5. pose proof (KEEP5 (s - 124)%Z 4%nat _ ltac:(lia) ltac:(cbn; lia) Fh4) as Fh5.
    pose proof (KEEP5 (s - 128)%Z 4%nat _ ltac:(lia) ltac:(cbn; lia) Fd4) as Fd5.
    pose proof (KEEP5 (s - 152)%Z 8%nat _ ltac:(lia) ltac:(cbn; lia) Qr4) as Qr5. pose proof (KEEP5 (s - 160)%Z 8%nat _ ltac:(lia) ltac:(cbn; lia) Qg4) as Qg5.
    pose proof (KEEP5 (s - 168)%Z 8%nat _ ltac:(lia) ltac:(cbn; lia) Qb4) as Qb5. pose proof (KEEP5 (s - 176)%Z 8%nat _ ltac:(lia) ltac:(cbn; lia) Qa4) as Qa5.
    pose proof (KEEP5 (s - 184)%Z 8%nat _ ltac:(lia) ltac:(cbn; lia) Fds4) as Fds5. pose proof (KEEP5 (s - 192)%Z 8%nat _ ltac:(lia) ltac:(cbn; lia) Fn4) as Fn5.
    (* [comment removed for export] *)
    assert (Y4 : getr r5 4 = Z_to_bv 64 0x455c0) by (rewrite (AG5 4%bv) by notin_list; exact E4r4).
    assert (Y2 : getr r5 2 = Z_to_bv 64 (s - 272)) by (rewrite (AG5 2%bv) by notin_list; exact E2r4).
    pose proof (alloc_margin_small (256 * 4) ltac:(lia)) as MG.
    apply (@W_calloc16_sure fx AL CL ASR PINS P16 C A4 M5 _ r5 256 4 (kR - 4 - RK_pix) (bR - 4 * 2 ^ 17 - RB_pix14) (Z_to_bv 64 0x1a894) (s - 272) S CK HW5 Y10 Y11
             ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite with_vmmaps_vmmaps; exact Hrm4) ltac:(unfold RK_pix; lia) ltac:(rewrite MG; unfold RB_pix14; lia)
             ltac:(unfold ROOM_NMAX; lia) Y1 ltac:(red; apply bv_eq; reflexivity) Y4 Y2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
             ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)).
    intros A6 m6 vm6 r6 res HW6 Hres CS6 Hnz L0g L1g L00g LEQ6 ZERO6 AL16g TOPg PM6 Hrm6. rewrite with_vmmaps_twice. rewrite with_vmmaps_twice in HW6.
    assert (Eres : res = Z_to_bv 64 (u res)) by (symmetry; apply zbv_self).
    pose proof (u64_range res) as Rres. set (g := u res) in *. clearbody g. rewrite Eres in Hres, L0g, L1g, L00g, LEQ6, ZERO6. clear Eres.
    change (256 * 4)%Z with 1024%Z in *. rewrite MG in Hrm6.
    destruct (blk_range C A6 m6 _ (Z_to_bv 64 g) _ CK HW6 L1g ltac:(lia)) as [Gg TOPg']. rewrite u_Z2bv in Gg, TOPg' by lia.
    assert (SUB46 : sub_live A4 A6) by (eapply sub_live_new; eassumption).
    assert (SUB6 : sub_live A A6) by (exact (sub_live_trans _ _ _ SUB4 SUB46)).
    pose proof (cellsZ_frm C (s - 272) M5 m6 (rmc_cells s regs) CK (proj1 PM6) ltac:(lia) ltac:(unfold rmc_cells; repeat (apply Forall_cons; [cbn [fst]; lia|]); apply Forall_nil) CE5) as CE6.
    assert (PMa6 : POSTM C A s m m6).
    { eapply POSTM_trans; [exact PM5|]. apply (POSTM_sub C A A4); [exact SUB4|]. eapply POSTM_mono; [|exact PM6]. lia. }
    assert (FR6 : forall (a : Z) (k : nat) bs, (s - 272 <= a)%Z -> (a + Z.of_nat k <= s)%Z -> rdn SEGS M5 (Z_to_bv 64 a) k = Some bs -> rdn SEGS m6 (Z_to_bv 64 a) k = Some bs).
    { intros a k bs Ha1 Ha2 R. rewrite (FRM_rdn16 C (s - 272) M5 m6 a k CK (proj1 PM6)) by lia. exact R. }
    pose proof (FR6 (s - 120)%Z 4%nat _ ltac:(lia) ltac:(cbn; lia) Fw5) as Fw6. pose proof (FR6 (s - 124)%Z 4%nat _ ltac:(lia) ltac:(cbn; lia) Fh5) as Fh6.
    pose proof (FR6 (s - 128)%Z 4%nat _ ltac:(lia) ltac:(cbn; lia) Fd5) as Fd6.
    pose proof (FR6 (s - 152)%Z 8%nat _ ltac:(lia) ltac:(cbn; lia) Qr5) as Qr6. pose proof (FR6 (s - 160)%Z 8%nat _ ltac:(lia) ltac:(cbn; lia) Qg5) as Qg6.
    pose proof (FR6 (s - 168)%Z 8%nat _ ltac:(lia) ltac:(cbn; lia) Qb5) as Qb6. pose proof (FR6 (s - 176)%Z 8%nat _ ltac:(lia) ltac:(cbn; lia) Qa5) as Qa6.
    pose proof (FR6 (s - 184)%Z 8%nat _ ltac:(lia) ltac:(cbn; lia) Fds5) as Fds6. pose proof (FR6 (s - 192)%Z 8%nat _ ltac:(lia) ltac:(cbn; lia) Fn5) as Fn6.
    pose proof (FR6 (s - 200)%Z 8%nat _ ltac:(lia) ltac:(cbn; lia) Fdd5) as Fdd6. pose proof (FR6 (s - 208)%Z 8%nat _ ltac:(lia) ltac:(cbn; lia) Fwd5) as Fwd6.
    pose proof (FR6 (s - 256)%Z 8%nat _ ltac:(lia) ltac:(cbn; lia) Fws5) as Fws6. pose proof (FR6 (s - 264)%Z 8%nat _ ltac:(lia) ltac:(cbn; lia) Fpd5) as Fpd6.
    (* [comment removed for export] *)
    destruct BNr as (Grm & TOPrm & ALrm & LArm & L0rm & L2rm). destruct BNg as (Ggm & TOPgm & ALgm & LAgm & L0gm & L2gm).
    destruct BNb as (Gbm & TOPbm & ALbm & LAbm & L0bm & L2bm). destruct BNa as (Gam & TOPam & ALam & LAam & L0am & L2am).
    assert (ARR6 : forall z, In z [rm; gm; bm] -> live A2 (Z_to_bv 64 z) = Some (4 * n)%Z -> live A (Z_to_bv 64 z) = None -> (4096 <= z)%Z -> (z + 4 * n <= alloc_top (c_vm C))%Z ->
                   arr255 SEGS m2 z n -> arr255 SEGS m6 z n /\ boxed (g + 1024 <= z \/ z + 4 * n <= g)%Z).
    { intros z _ Lz LAz Gz TOPz Az.
      assert (NEzp : Z_to_bv 64 z <> Z_to_bv 64 pixd) by (intros E; rewrite E in Lz; rewrite LApd in Lz; discriminate Lz).
      pose proof (blk_apart C A4 m4 _ _ _ _ _ CK HW4 (SUB24 _ _ Lz) L4pd NEzp ltac:(lia) ltac:(lia)) as APzp. rewrite !u_Z2bv in APzp by lia.
      assert (NEzg : Z_to_bv 64 g <> Z_to_bv 64 z) by (intros E; rewrite <- E in Lz; rewrite (SUB24 _ _ Lz) in L0g; discriminate L0g).
      pose proof (blk_apart C A6 m6 _ _ _ _ _ CK HW6 L1g (SUB46 _ _ (SUB24 _ _ Lz)) NEzg ltac:(lia) ltac:(lia)) as APzg. rewrite !u_Z2bv in APzg by lia.
      split; [|apply box_i; exact APzg].
      apply (arr255_ext SEGS M5 m6 z n ltac:(lia) ltac:(lia)).
      { intros x Hx. exact (LIVK_at A4 M5 m6 z (4 * n) x (proj2 PM6) (SUB24 _ _ Lz) ltac:(lia) ltac:(lia) Hx). }
      apply (arr255_ext SEGS m4 M5 z n ltac:(lia) ltac:(lia)).
      { intros x Hx. apply OUT5; [clear - APzp Hx; lia | lia | lia]. }
      apply (arr255_ext SEGS M3 m4 z n ltac:(lia) ltac:(lia)).
      { intros x Hx. exact (LIVK_at A2 M3 m4 z (4 * n) x (proj2 PM4) Lz ltac:(lia) ltac:(lia) Hx). }
      apply (arr255_ext SEGS m2 M3 z n ltac:(lia) ltac:(lia)); [|exact Az].
      intros x Hx. apply OUT3. lia. }
    destruct (ARR6 rm ltac:(left; reflexivity) L2rm LArm Grm TOPrm Ar2) as (Ar6 & APgr).
    destruct (ARR6 gm ltac:(right; left; reflexivity) L2gm LAgm Ggm TOPgm Ag2) as (Ag6 & APgg).
    destruct (ARR6 bm ltac:(right; right; left; reflexivity) L2bm LAbm Gbm TOPbm Ab2) as (Ab6 & APgb).
    clear ARR6.
    (* [comment removed for export] *)
    assert (E2r6 : getr r6 2 = Z_to_bv 64 (s - 272)) by (csr; reflexivity).
    assert (E4r6 : getr r6 4 = Z_to_bv 64 0x455c0) by (csr; reflexivity).
    assert (ALg4 : (g mod 4 = 0)%Z) by (clear - AL16g; Z.div_mod_to_equations; lia).
    assert (M4 : forall z : Z, (z mod 16 = 0)%Z -> (z mod 4 = 0)%Z) by (clear; intros z E; Z.div_mod_to_equations; lia).
    destruct (rmc_S3a al_rom fx r6 m6 s n g rm gm bm ltac:(lia) ltac:(lia) ltac:(lia) ALg4 ltac:(lia) ltac:(lia) ltac:(lia) Fn6 Qr6 Qg6 Qb6 E2r6 Hres)
      as (r7 & RUN7 & Z30 & Z11 & Z12 & Z13 & Z14 & Z15 & Z16 & Z17 & Z5 & Z6 & Z7 & Z28 & Z29 & AG7).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW6)) | exact (mp_lazy _ (w_pure _ _ _ _ HW6)) | exact RUN7 |].
    replace (Z_to_bv 64 0x1a8d0) with (0x1a8d0 : word) by (apply bv_eq; reflexivity).
    destruct (rmc_S3f al_rom fx r7 m6 (W_rmc_ro C A6 m6 _ 0x11720 4 _ HW6 ltac:(lia) ltac:(cbn; lia) rmc_c03_val) (W_rmc_ro C A6 m6 _ 0x11714 4 _ HW6 ltac:(lia) ltac:(cbn; lia) rmc_c02_val)
                (W_rmc_ro C A6 m6 _ 0x11638 8 _ HW6 ltac:(lia) ltac:(cbn; lia) rmc_c05_val) (W_rmc_ro C A6 m6 _ 0x11608 8 _ HW6 ltac:(lia) ltac:(cbn; lia) rmc_cm1_val)
                (W_rmc_ro C A6 m6 _ 0x11618 8 _ HW6 ltac:(lia) ltac:(cbn; lia) rmc_c2p_val) Z17 Z5 Z6 Z7 Z28 Z29) as (fr7 & RUN7f & GC7).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW6)) | exact (mp_lazy _ (w_pure _ _ _ _ HW6)) | exact RUN7f |].
    replace (0x1a8e8 : word) with (Z_to_bv 64 0x1a8e8) by (apply bv_eq; reflexivity).
    destruct (rmc_S3b al_rom (mkFP fr7 (@fp_csr fx)) r7 m6 n rm gm bm ltac:(lia) ltac:(lia) (M4 _ ALrm) ltac:(lia) (M4 _ ALgm) ltac:(lia) (M4 _ ALbm) Z15 Z16 Z12 Z13 Z14 Z30)
      as (r7b & RUN7b & Y16 & Y17 & Y5 & Y6 & Y7 & Y28 & Y29 & Y30 & AG7b).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW6)) | exact (mp_lazy _ (w_pure _ _ _ _ HW6)) | exact RUN7b |].
    assert (T47 : (alloc_top (c_vm C) + 4096 < 2 ^ 63)%Z) by (clear - T1 T2 T3; pose proof LSTK_val; lia).
    assert (FR7 : fregs r7b g rm gm bm (4 * n)).
    { unfold fregs. split; [rewrite (AG7b 10%bv) by notin_list; rewrite (AG7 10%bv) by notin_list; exact Hres|].
      split; [rewrite (AG7b 12%bv) by notin_list; exact Z12|]. split; [rewrite (AG7b 13%bv) by notin_list; exact Z13|]. split; [rewrite (AG7b 14%bv) by notin_list; exact Z14|].
      split; [exact Y30|]. split; [rewrite (AG7b 15%bv) by notin_list; exact Z15|]. repeat split; assumption. }
    destruct (rmc_fill_loop al_rom (Z.to_nat n) (mkFP fr7 (@fp_csr fx)) r7b m6 m6 g rm gm bm n 0%Z Hz GC7 ltac:(rewrite Z2Nat.id by lia; lia) ltac:(lia) ltac:(lia)
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                (blk_sok C A6 m6 _ g 1024 CK HW6 L1g ltac:(lia) ltac:(lia) ltac:(lia)) Ar6 Ag6 Ab6 (box_e _ APgr) (box_e _ APgg) (box_e _ APgb) (rinv_refl _ _) FR7
                ltac:(rewrite (AG7b 11%bv) by notin_list; exact Z11))
      as (fr8 & cs8 & r8 & M8 & RUN8 & Hz8 & RI8 & AG8).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW6)) | exact (mp_lazy _ (w_pure _ _ _ _ HW6)) | exact RUN8 |].
    assert (LAg : live A (Z_to_bv 64 g) = None) by (destruct (live A (Z_to_bv 64 g)) as [z|] eqn:E; [rewrite (SUB4 _ _ E) in L0g; discriminate L0g | reflexivity]).
    destruct (rinv_WP C A A6 m6 _ M8 [(g, 1024%Z)] s CK HW6 SUB6 Hhi RI8) as [HW8 PM8].
    { unfold fresh_regions. apply Forall_cons; [|apply Forall_nil]. exists (Z_to_bv 64 g), 1024%Z. cbn [fst snd]. rewrite u_Z2bv by lia.
      split; [exact L1g | split; [exact LAg | split; [exact L00g | lia]]]. }
    assert (PMa8 : POSTM C A s m M8) by (eapply POSTM_trans; [exact PMa6 | exact PM8]).
    assert (OUT8 : forall x : word, ~ (g <= u x < g + 1024)%Z -> M8 x = m6 x).
    { intros x Hx. apply (proj2 RI8). intros r [<- | []]. unfold inreg. cbn [fst snd]. exact Hx. }
    pose proof (cellsZ_keep m6 M8 (rmc_cells s regs)
                  ltac:(unfold rmc_cells; repeat (apply Forall_cons; [cbn [fst]; split; [lia | split; [lia | intros x Hx; apply OUT8; lia]] |]); apply Forall_nil) CE6) as CE8.
    assert (KEEP8 : forall (a : Z) (k : nat) bs, (s - 272 <= a)%Z -> (a + Z.of_nat k <= s)%Z -> rdn SEGS m6 (Z_to_bv 64 a) k = Some bs -> rdn SEGS M8 (Z_to_bv 64 a) k = Some bs).
    { intros a k bs Ha Ha2 R. rewrite <- R. destruct k as [|k']; [reflexivity|]. apply rdn_ext; rewrite u_Z2bv by lia; [lia|]. intros x Hx. apply OUT8; lia. }
    pose proof (KEEP8 (s - 120)%Z 4%nat _ ltac:(lia) ltac:(cbn; lia) Fw6) as Fw8. pose proof (KEEP8 (s - 124)%Z 4%nat _ ltac:(lia) ltac:(cbn; lia) Fh6) as Fh8.
    pose proof (KEEP8 (s - 128)%Z 4%nat _ ltac:(lia) ltac:(cbn; lia) Fd6) as Fd8.
    pose proof (KEEP8 (s - 152)%Z 8%nat _ ltac:(lia) ltac:(cbn; lia) Qr6) as Qr8. pose proof (KEEP8 (s - 160)%Z 8%nat _ ltac:(lia) ltac:(cbn; lia) Qg6) as Qg8.
    pose proof (KEEP8 (s - 168)%Z 8%nat _ ltac:(lia) ltac:(cbn; lia) Qb6) as Qb8. pose proof (KEEP8 (s - 176)%Z 8%nat _ ltac:(lia) ltac:(cbn; lia) Qa6) as Qa8.
    pose proof (KEEP8 (s - 184)%Z 8%nat _ ltac:(lia) ltac:(cbn; lia) Fds6) as Fds8. pose proof (KEEP8 (s - 200)%Z 8%nat _ ltac:(lia) ltac:(cbn; lia) Fdd6) as Fdd8.
    pose proof (KEEP8 (s - 208)%Z 8%nat _ ltac:(lia) ltac:(cbn; lia) Fwd6) as Fwd8. pose proof (KEEP8 (s - 256)%Z 8%nat _ ltac:(lia) ltac:(cbn; lia) Fws6) as Fws8.
    pose proof (KEEP8 (s - 264)%Z 8%nat _ ltac:(lia) ltac:(cbn; lia) Fpd6) as Fpd8.
    (* [comment removed for export] *)
    assert (E2r8 : getr r8 2 = Z_to_bv 64 (s - 272)) by (rewrite (AG8 2%bv) by notin_list; rewrite (AG7b 2%bv) by notin_list; rewrite (AG7 2%bv) by notin_list; exact E2r6).
    assert (E10r8 : getr r8 10 = Z_to_bv 64 g) by (rewrite (AG8 10%bv) by notin_list; rewrite (AG7b 10%bv) by notin_list; rewrite (AG7 10%bv) by notin_list; exact Hres).
    assert (E4r8 : getr r8 4 = Z_to_bv 64 0x455c0) by (rewrite (AG8 4%bv) by notin_list; rewrite (AG7b 4%bv) by notin_list; rewrite (AG7 4%bv) by notin_list; exact E4r6).
    pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Ld) as (_ & ALd & _). rewrite u_Z2bv in ALd by lia.
    destruct (rmc_S4 al_rom (mkFP fr8 cs8) r8 M8 s g h data (wpl_of w 8) datad ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) (M4 _ ALd) ltac:(lia) ltac:(lia) (M4 _ ALdd)
                (W_sok_win C A6 M8 _ (s - 192) 8 CK HW8 ltac:(lia) ltac:(cbn; lia)) Fh8 Fdd8 Fws8 Fds8 E2r8 E10r8)
      as (r9 & RUN9 & V11 & V12 & V13 & V29 & V14 & V15 & V16 & V17 & V31 & V21 & AG9).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW8)) | exact (mp_lazy _ (w_pure _ _ _ _ HW8)) | exact RUN9 |].
    set (M9 := wbytes M8 (Z_to_bv 64 (s - 192)) (word_to_le_bytes 8 (Z_to_bv 64 0x3ffffff))) in *.
    assert (WP9 : W C A6 M9 (with_vmmaps vm6 md) /\ POSTM C A s m M9) by (subst M9; wp_win CK).
    destruct WP9 as [HW9 PMa9].
    assert (OUT9 : forall x : word, ~ (s - 192 <= u x < s - 184)%Z -> M9 x = M8 x).
    { intros x Hx. subst M9. apply wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; lia. }
    pose proof (cellsZ_out M8 M9 (s - 192) (s - 184) (rmc_cells s regs) OUT9
                  ltac:(unfold rmc_cells; repeat (apply Forall_cons; [cbn [fst]; split; [lia | split; [lia | left; lia]] |]); apply Forall_nil) CE8) as CE9.
    assert (KEEP9 : forall (a : Z) (k : nat) bs, (s - 184 <= a \/ a + Z.of_nat k <= s - 192)%Z -> (0 <= a)%Z -> (a + Z.of_nat k <= 2 ^ 64)%Z ->
                    rdn SEGS M8 (Z_to_bv 64 a) k = Some bs -> rdn SEGS M9 (Z_to_bv 64 a) k = Some bs).
    { intros a k bs Ha Ha0 Ha64 R. rewrite <- R. destruct k as [|k']; [reflexivity|]. apply rdn_ext; rewrite u_Z2bv by lia; [lia|]. intros x Hx. apply OUT9. lia. }
    pose proof (KEEP9 (s - 120)%Z 4%nat _ ltac:(left; lia) ltac:(lia) ltac:(cbn; lia) Fw8) as Fw9. pose proof (KEEP9 (s - 124)%Z 4%nat _ ltac:(left; lia) ltac:(lia) ltac:(cbn; lia) Fh8) as Fh9.
    pose proof (KEEP9 (s - 128)%Z 4%nat _ ltac:(left; lia) ltac:(lia) ltac:(cbn; lia) Fd8) as Fd9.
    pose proof (KEEP9 (s - 152)%Z 8%nat _ ltac:(left; lia) ltac:(lia) ltac:(cbn; lia) Qr8) as Qr9. pose proof (KEEP9 (s - 160)%Z 8%nat _ ltac:(left; lia) ltac:(lia) ltac:(cbn; lia) Qg8) as Qg9.
    pose proof (KEEP9 (s - 168)%Z 8%nat _ ltac:(left; lia) ltac:(lia) ltac:(cbn; lia) Qb8) as Qb9. pose proof (KEEP9 (s - 176)%Z 8%nat _ ltac:(left; lia) ltac:(lia) ltac:(cbn; lia) Qa8) as Qa9.
    pose proof (KEEP9 (s - 184)%Z 8%nat _ ltac:(left; lia) ltac:(lia) ltac:(cbn; lia) Fds8) as Fds9. pose proof (KEEP9 (s - 200)%Z 8%nat _ ltac:(right; cbn; lia) ltac:(lia) ltac:(cbn; lia) Fdd8) as Fdd9.
    pose proof (KEEP9 (s - 208)%Z 8%nat _ ltac:(right; cbn; lia) ltac:(lia) ltac:(cbn; lia) Fwd8) as Fwd9. pose proof (KEEP9 (s - 256)%Z 8%nat _ ltac:(right; cbn; lia) ltac:(lia) ltac:(cbn; lia) Fws8) as Fws9.
    pose proof (KEEP9 (s - 264)%Z 8%nat _ ltac:(right; cbn; lia) ltac:(lia) ltac:(cbn; lia) Fpd8) as Fpd9.
    assert (L6pd : live A6 (Z_to_bv 64 pixd) = Some 64%Z) by (exact (SUB46 _ _ L4pd)).
    assert (L6dd : live A6 (Z_to_bv 64 datad) = Some (4 * (wpl_of w 8 * h))%Z) by (exact (SUB46 _ _ L4dd)).
    assert (L6d : live A6 (Z_to_bv 64 data) = Some (4 * (wpl_of w 8 * h))%Z) by (exact (SUB6 _ _ Ld)).
    assert (Hwpl5 : (wpl_of w 8 <= 5000)%Z) by (clear - Hw2; unfold wpl_of; assert ((w * 8 + 31) / 32 < 5001)%Z by (apply Z.div_lt_upper_bound; lia); lia).
    assert (GEO : (4096 <= s - 272 /\ s <= 2 ^ 47 /\ 4096 <= g /\ g + 1024 <= s - 272 /\ g mod 4 = 0 /\ 4096 <= data /\ 0 <= 4 * (wpl_of w 8 * h) /\
                   data + 4 * (wpl_of w 8 * h) <= s - 272 /\ data + 4 * (wpl_of w 8 * h) + 20000 < 2 ^ 47 /\
                   4096 <= datad /\ 0 <= 4 * (wpl_of w 8 * h) /\ datad + 4 * (wpl_of w 8 * h) <= s - 272 /\ datad + 4 * (wpl_of w 8 * h) + 20000 < 2 ^ 47 /\
                   1 <= w <= 20000 /\ 1 <= h <= 20000 /\ w <= 4 * wpl_of w 8 /\ w <= 4 * wpl_of w 8 /\ 0 <= wpl_of w 8 <= 5000 /\ 0 <= wpl_of w 8 <= 5000 /\
                   wpl_of w 8 * h <= 16777216 /\ wpl_of w 8 * h <= 16777216)%Z).
    { clear - T1 T2 T3 Hlo Hhi Gg TOPg' Gd TOPd Gdd TOPdd Hraster Hw1 Hw2 Hh1 Hh2 Hw4 ALg4 Hwpl5 Hwpl Hsz. pose proof LSTK_val. repeat split; try lia; exact ALg4. }
    destruct (@rmc_rows al_rom (mkFP fr8 cs8) s g w h (wpl_of w 8) (wpl_of w 8) data (4 * (wpl_of w 8 * h)) datad (4 * (wpl_of w 8 * h)) M9 GEO
                (blk_sok C A6 M9 _ data _ CK HW9 L6d ltac:(lia) ltac:(lia) ltac:(lia))
                (blk_sok C A6 M9 _ g 1024 CK HW9 L1g ltac:(lia) ltac:(lia) ltac:(lia))
                (blk_sok C A6 M9 _ datad _ CK HW9 L6dd ltac:(lia) ltac:(lia) ltac:(lia))
                (W_sok_win C A6 M9 _ (s - 112) 4 CK HW9 ltac:(lia) ltac:(cbn; lia)) Fw9 Fh9 Fd9 Fwd9 Fws9 Fds9 Fdd9
                ltac:(repeat split; try reflexivity; [exact (M4 _ ALd) | exact (M4 _ ALdd)])
                (Z.to_nat h) r9 M9 0%Z ltac:(rewrite Z2Nat.id by lia; lia) ltac:(lia) (rinv_refl _ _))
      as (r10 & M10 & RUN10 & RI10 & AG10).
    { unfold rowregs. rewrite !Z.mul_0_r.
      split; [rewrite (AG9 2%bv) by notin_list; exact E2r8|]. split; [rewrite (AG9 10%bv) by notin_list; exact E10r8|].
      repeat split; assumption. }
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW9)) | exact (mp_lazy _ (w_pure _ _ _ _ HW9)) | exact RUN10 |].
    assert (LAdd6 : live A (Z_to_bv 64 datad) = None) by exact LAdd'.
    destruct (rinv_WP2 C A A6 M9 _ M10 (RR s datad (4 * (wpl_of w 8 * h))) s CK HW9 SUB6 Hhi RI10) as [HW10 PM10].
    { unfold local_regions, RR. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd].
      - right. exists (Z_to_bv 64 datad), (4 * (wpl_of w 8 * h))%Z. rewrite u_Z2bv by lia. split; [exact L6dd | split; [exact LAdd6 | split; [exact L0dd | lia]]].
      - left. lia. }
    assert (PMa10 : POSTM C A s m M10) by (eapply POSTM_trans; [exact PMa9 | exact PM10]).
    assert (OUT10 : forall x : word, ~ (datad <= u x < datad + 4 * (wpl_of w 8 * h))%Z -> ~ (s - 112 <= u x < s - 108)%Z -> M10 x = M9 x).
    { intros x Hx1 Hx2. apply (proj2 RI10). intros r Hr. unfold RR in Hr. cbn [In] in Hr. unfold inreg. destruct Hr as [<- | [<- | []]]; cbn [fst snd]; lia. }
    pose proof (cellsZ_keep M9 M10 (rmc_cells s regs)
                  ltac:(unfold rmc_cells; repeat (apply Forall_cons; [cbn [fst]; split; [lia | split; [lia | intros x Hx; apply OUT10; lia]] |]); apply Forall_nil) CE9) as CE10.
    assert (KEEP10 : forall (a : Z) (k : nat) bs, (s - 272 <= a)%Z -> (a + Z.of_nat k <= s - 112)%Z -> rdn SEGS M9 (Z_to_bv 64 a) k = Some bs -> rdn SEGS M10 (Z_to_bv 64 a) k = Some bs).
    { intros a k bs Ha Ha2 R. rewrite <- R. destruct k as [|k']; [reflexivity|]. apply rdn_ext; rewrite u_Z2bv by lia; [lia|]. intros x Hx. apply OUT10; lia. }
    pose proof (KEEP10 (s - 152)%Z 8%nat _ ltac:(lia) ltac:(cbn; lia) Qr9) as Qr10. pose proof (KEEP10 (s - 160)%Z 8%nat _ ltac:(lia) ltac:(cbn; lia) Qg9) as Qg10.
    pose proof (KEEP10 (s - 168)%Z 8%nat _ ltac:(lia) ltac:(cbn; lia) Qb9) as Qb10. pose proof (KEEP10 (s - 176)%Z 8%nat _ ltac:(lia) ltac:(cbn; lia) Qa9) as Qa10.
    pose proof (KEEP10 (s - 264)%Z 8%nat _ ltac:(lia) ltac:(cbn; lia) Fpd9) as Fpd10.
    (* [comment removed for export] *)
    assert (E2r10 : getr r10 2 = Z_to_bv 64 (s - 272)) by (rewrite (AG10 2%bv) by notin_list; rewrite (AG9 2%bv) by notin_list; exact E2r8).
    assert (E4r10 : getr r10 4 = Z_to_bv 64 0x455c0) by (rewrite (AG10 4%bv) by notin_list; rewrite (AG9 4%bv) by notin_list; exact E4r8).
    assert (E10r10 : getr r10 10 = Z_to_bv 64 g) by (rewrite (AG10 10%bv) by notin_list; rewrite (AG9 10%bv) by notin_list; exact E10r8).
    assert (L6rm : live A6 (Z_to_bv 64 rm) = Some (4 * n)%Z) by (exact (SUB46 _ _ (SUB24 _ _ L2rm))).
    assert (L6gm : live A6 (Z_to_bv 64 gm) = Some (4 * n)%Z) by (exact (SUB46 _ _ (SUB24 _ _ L2gm))).
    assert (L6bm : live A6 (Z_to_bv 64 bm) = Some (4 * n)%Z) by (exact (SUB46 _ _ (SUB24 _ _ L2bm))).
    assert (L6am : live A6 (Z_to_bv 64 am) = Some (4 * n)%Z) by (exact (SUB46 _ _ (SUB24 _ _ L2am))).
    assert (PXd10 : PIXat M10 pixd (hdv w h 8 0 datad)).
    { assert (NEpdd : Z_to_bv 64 pixd <> Z_to_bv 64 datad) by (intros E; apply (f_equal bv_unsigned) in E; rewrite !u_Z2bv in E by lia; exact (box_e _ NEpd E)).
      pose proof (blk_apart C A6 m6 _ _ _ _ _ CK HW6 L6pd L6dd NEpdd ltac:(lia) ltac:(lia)) as APpd. rewrite !u_Z2bv in APpd by lia.
      assert (NEpg : Z_to_bv 64 pixd <> Z_to_bv 64 g) by (intros E; rewrite E in L4pd; rewrite L0g in L4pd; discriminate L4pd).
      pose proof (blk_apart C A6 m6 _ _ _ _ _ CK HW6 L6pd L1g NEpg ltac:(lia) ltac:(lia)) as APpg. rewrite !u_Z2bv in APpg by lia.
      apply (PIXat_frame M5); [exact PXd5|]. intros x Hx.
      rewrite OUT10 by (clear - APpd Hx Hlo T1 TOPpd; pose proof LSTK_val; lia). rewrite OUT9 by (clear - Hx Hlo T1 TOPpd; pose proof LSTK_val; lia). rewrite OUT8 by (clear - APpg Hx; lia).
      exact (LIVK_at A4 M5 m6 pixd 64 x (proj2 PM6) L4pd ltac:(lia) ltac:(lia) Hx). }
    destruct (rmc_S5 al_rom (mkFP fr8 cs8) r10 M10 g ltac:(lia) E10r10) as (r11 & RUN11 & F1_0 & F10_0 & AGf0).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW10)) | exact (mp_lazy _ (w_pure _ _ _ _ HW10)) | exact RUN11 |].
    assert (F2_0 : getr r11 2 = Z_to_bv 64 (s - 272)) by (rewrite (AGf0 2%bv) by notin_list; exact E2r10).
    assert (F4_0 : getr r11 4 = Z_to_bv 64 0x455c0) by (rewrite (AGf0 4%bv) by notin_list; exact E4r10).
    assert (DISJ_rm_g : Z_to_bv 64 rm = Z_to_bv 64 g -> False) by (intros EE; pose proof (SUB24 _ _ L2rm) as X; rewrite EE in X; rewrite L0g in X; discriminate X).
    assert (DISJ_gm_g : Z_to_bv 64 gm = Z_to_bv 64 g -> False) by (intros EE; pose proof (SUB24 _ _ L2gm) as X; rewrite EE in X; rewrite L0g in X; discriminate X).
    assert (DISJ_bm_g : Z_to_bv 64 bm = Z_to_bv 64 g -> False) by (intros EE; pose proof (SUB24 _ _ L2bm) as X; rewrite EE in X; rewrite L0g in X; discriminate X).
    assert (DISJ_am_g : Z_to_bv 64 am = Z_to_bv 64 g -> False) by (intros EE; pose proof (SUB24 _ _ L2am) as X; rewrite EE in X; rewrite L0g in X; discriminate X).
    assert (DISJ_pixd_g : Z_to_bv 64 pixd = Z_to_bv 64 g -> False) by (intros EE; pose proof L4pd as X; rewrite EE in X; rewrite L0g in X; discriminate X).
    assert (DISJ_datad_g : Z_to_bv 64 datad = Z_to_bv 64 g -> False) by (intros EE; pose proof L4dd as X; rewrite EE in X; rewrite L0g in X; discriminate X).
    assert (DISJ_pixd_rm : Z_to_bv 64 pixd = Z_to_bv 64 rm -> False) by (intros EE; pose proof L2rm as X; rewrite <- EE in X; rewrite LApd in X; discriminate X).
    assert (DISJ_pixd_gm : Z_to_bv 64 pixd = Z_to_bv 64 gm -> False) by (intros EE; pose proof L2gm as X; rewrite <- EE in X; rewrite LApd in X; discriminate X).
    assert (DISJ_pixd_bm : Z_to_bv 64 pixd = Z_to_bv 64 bm -> False) by (intros EE; pose proof L2bm as X; rewrite <- EE in X; rewrite LApd in X; discriminate X).
    assert (DISJ_pixd_am : Z_to_bv 64 pixd = Z_to_bv 64 am -> False) by (intros EE; pose proof L2am as X; rewrite <- EE in X; rewrite LApd in X; discriminate X).
    assert (DISJ_datad_rm : Z_to_bv 64 datad = Z_to_bv 64 rm -> False) by (intros EE; pose proof L2rm as X; rewrite <- EE in X; rewrite LAdd in X; discriminate X).
    assert (DISJ_datad_gm : Z_to_bv 64 datad = Z_to_bv 64 gm -> False) by (intros EE; pose proof L2gm as X; rewrite <- EE in X; rewrite LAdd in X; discriminate X).
    assert (DISJ_datad_bm : Z_to_bv 64 datad = Z_to_bv 64 bm -> False) by (intros EE; pose proof L2bm as X; rewrite <- EE in X; rewrite LAdd in X; discriminate X).
    assert (DISJ_datad_am : Z_to_bv 64 datad = Z_to_bv 64 am -> False) by (intros EE; pose proof L2am as X; rewrite <- EE in X; rewrite LAdd in X; discriminate X).
    assert (DISJ_gm_rm : Z_to_bv 64 gm = Z_to_bv 64 rm -> False) by (intros EE; apply (f_equal bv_unsigned) in EE; rewrite !u_Z2bv in EE by lia; exact (box_e _ NErg (eq_sym EE))).
    assert (DISJ_bm_rm : Z_to_bv 64 bm = Z_to_bv 64 rm -> False) by (intros EE; apply (f_equal bv_unsigned) in EE; rewrite !u_Z2bv in EE by lia; exact (box_e _ NErb (eq_sym EE))).
    assert (DISJ_am_rm : Z_to_bv 64 am = Z_to_bv 64 rm -> False) by (intros EE; apply (f_equal bv_unsigned) in EE; rewrite !u_Z2bv in EE by lia; exact (box_e _ NEra (eq_sym EE))).
    assert (DISJ_bm_gm : Z_to_bv 64 bm = Z_to_bv 64 gm -> False) by (intros EE; apply (f_equal bv_unsigned) in EE; rewrite !u_Z2bv in EE by lia; exact (box_e _ NEgb (eq_sym EE))).
    assert (DISJ_am_gm : Z_to_bv 64 am = Z_to_bv 64 gm -> False) by (intros EE; apply (f_equal bv_unsigned) in EE; rewrite !u_Z2bv in EE by lia; exact (box_e _ NEga (eq_sym EE))).
    assert (DISJ_am_bm : Z_to_bv 64 am = Z_to_bv 64 bm -> False) by (intros EE; apply (f_equal bv_unsigned) in EE; rewrite !u_Z2bv in EE by lia; exact (box_e _ NEba (eq_sym EE))).
    (* [comment removed for export] *)
    apply (@W_free16 (mkFP fr8 cs8) AL CL ASR PINS P16 C A6 M10 _ r11 (Z_to_bv 64 g) (Z_to_bv 64 0x1a704) 1024 (s - 272) S CK HW10 F10_0 L1g L00g F1_0
             ltac:(red; apply bv_eq; reflexivity) F4_0 F2_0 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)).
    intros Af0 mf0 vmf0 rf0 HWf0 CSf0 Ldead0 LEQf0 PMf0 RTRf0. rewrite with_vmmaps_twice. rewrite with_vmmaps_twice in HWf0.
    assert (SUBf0 : sub_live A Af0).
    { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 g) by (intros ->; rewrite LAg in Lq; discriminate Lq). rewrite (LEQf0 q NEq). exact (SUB6 q kq Lq). }
    assert (PMaf0 : POSTM C A s m mf0).
    { eapply POSTM_trans; [exact PMa10|]. apply (POSTM_sub C A Af0); [exact SUBf0|]. eapply POSTM_mono; [|exact PMf0]. lia. }
    pose proof (cellsZ_frm C (s - 272) M10 mf0 (rmc_cells s regs) CK (proj1 PMf0) ltac:(lia) ltac:(unfold rmc_cells; repeat (apply Forall_cons; [cbn [fst]; lia|]); apply Forall_nil) CE10) as CEf0.
    pose proof (RTRf0 _ _ ltac:(rewrite with_vmmaps_vmmaps; exact Hrm6) ltac:(unfold RK_pix; lia) ltac:(unfold RB_pix14; lia)) as Hrmf0. rewrite !Z.sub_0_r in Hrmf0.
    assert (Lf0rm : live Af0 (Z_to_bv 64 rm) = Some (4 * n)%Z).
    { rewrite (LEQf0 (Z_to_bv 64 rm)); [exact L6rm|]. intros EE. pose proof L6rm as X. rewrite EE in X. exact (DISJ_rm_g EE). }
    assert (Lf0gm : live Af0 (Z_to_bv 64 gm) = Some (4 * n)%Z).
    { rewrite (LEQf0 (Z_to_bv 64 gm)); [exact L6gm|]. intros EE. pose proof L6gm as X. rewrite EE in X. exact (DISJ_gm_g EE). }
    assert (Lf0bm : live Af0 (Z_to_bv 64 bm) = Some (4 * n)%Z).
    { rewrite (LEQf0 (Z_to_bv 64 bm)); [exact L6bm|]. intros EE. pose proof L6bm as X. rewrite EE in X. exact (DISJ_bm_g EE). }
    assert (Lf0am : live Af0 (Z_to_bv 64 am) = Some (4 * n)%Z).
    { rewrite (LEQf0 (Z_to_bv 64 am)); [exact L6am|]. intros EE. pose proof L6am as X. rewrite EE in X. exact (DISJ_am_g EE). }
    assert (Lf0pixd : live Af0 (Z_to_bv 64 pixd) = Some 64%Z).
    { rewrite (LEQf0 (Z_to_bv 64 pixd)); [exact L6pd|]. intros EE. pose proof L6pd as X. rewrite EE in X. exact (DISJ_pixd_g EE). }
    assert (Lf0datad : live Af0 (Z_to_bv 64 datad) = Some (4 * (wpl_of w 8 * h))%Z).
    { rewrite (LEQf0 (Z_to_bv 64 datad)); [exact L6dd|]. intros EE. pose proof L6dd as X. rewrite EE in X. exact (DISJ_datad_g EE). }
    pose proof Qr10 as Qf0rm. rewrite <- (FRM_rdn16 C (s - 272) M10 mf0 (s - 152)%Z 8 CK (proj1 PMf0)) in Qf0rm by (cbn; lia).
    pose proof Qg10 as Qf0gm. rewrite <- (FRM_rdn16 C (s - 272) M10 mf0 (s - 160)%Z 8 CK (proj1 PMf0)) in Qf0gm by (cbn; lia).
    pose proof Qb10 as Qf0bm. rewrite <- (FRM_rdn16 C (s - 272) M10 mf0 (s - 168)%Z 8 CK (proj1 PMf0)) in Qf0bm by (cbn; lia).
    pose proof Qa10 as Qf0am. rewrite <- (FRM_rdn16 C (s - 272) M10 mf0 (s - 176)%Z 8 CK (proj1 PMf0)) in Qf0am by (cbn; lia).
    pose proof Fpd10 as Fpdf0. rewrite <- (FRM_rdn16 C (s - 272) M10 mf0 (s - 264)%Z 8 CK (proj1 PMf0)) in Fpdf0 by (cbn; lia).
    assert (PXdf0 : PIXat mf0 pixd (hdv w h 8 0 datad)).
    { apply (PIXat_frame M10); [exact PXd10|]. intros x Hx. exact (LIVK_at Af0 M10 mf0 pixd 64 x (proj2 PMf0) Lf0pixd ltac:(lia) ltac:(lia) Hx). }
    assert (G2f0 : getr rf0 2 = Z_to_bv 64 (s - 272)) by (csr; reflexivity).
    assert (G4f0 : getr rf0 4 = Z_to_bv 64 0x455c0) by (csr; reflexivity).
    destruct (rmc_S6 al_rom (mkFP fr8 cs8) rf0 mf0 s rm ltac:(lia) ltac:(lia) Qf0rm G2f0) as (rg0 & RUNg0 & F1_1 & F10_1 & AGg0).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWf0)) | exact (mp_lazy _ (w_pure _ _ _ _ HWf0)) | exact RUNg0 |].
    assert (F2_1 : getr rg0 2 = Z_to_bv 64 (s - 272)) by (rewrite (AGg0 2%bv) by notin_list; exact G2f0).
    assert (F4_1 : getr rg0 4 = Z_to_bv 64 0x455c0) by (rewrite (AGg0 4%bv) by notin_list; exact G4f0).
    (* [comment removed for export] *)
    apply (@W_free16 (mkFP fr8 cs8) AL CL ASR PINS P16 C Af0 mf0 _ rg0 (Z_to_bv 64 rm) (Z_to_bv 64 0x1b5a4) (4 * n) (s - 272) S CK HWf0 F10_1 Lf0rm L0rm F1_1
             ltac:(red; apply bv_eq; reflexivity) F4_1 F2_1 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)).
    intros Af1 mf1 vmf1 rf1 HWf1 CSf1 Ldead1 LEQf1 PMf1 RTRf1. rewrite with_vmmaps_twice. rewrite with_vmmaps_twice in HWf1.
    assert (SUBf1 : sub_live A Af1).
    { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 rm) by (intros ->; rewrite LArm in Lq; discriminate Lq). rewrite (LEQf1 q NEq). exact (SUBf0 q kq Lq). }
    assert (PMaf1 : POSTM C A s m mf1).
    { eapply POSTM_trans; [exact PMaf0|]. apply (POSTM_sub C A Af1); [exact SUBf1|]. eapply POSTM_mono; [|exact PMf1]. lia. }
    pose proof (cellsZ_frm C (s - 272) mf0 mf1 (rmc_cells s regs) CK (proj1 PMf1) ltac:(lia) ltac:(unfold rmc_cells; repeat (apply Forall_cons; [cbn [fst]; lia|]); apply Forall_nil) CEf0) as CEf1.
    pose proof (RTRf1 _ _ ltac:(rewrite with_vmmaps_vmmaps; exact Hrmf0) ltac:(unfold RK_pix; lia) ltac:(unfold RB_pix14; lia)) as Hrmf1. rewrite !Z.sub_0_r in Hrmf1.
    assert (Lf1gm : live Af1 (Z_to_bv 64 gm) = Some (4 * n)%Z).
    { rewrite (LEQf1 (Z_to_bv 64 gm)); [exact Lf0gm|]. intros EE. pose proof Lf0gm as X. rewrite EE in X. exact (DISJ_gm_rm EE). }
    assert (Lf1bm : live Af1 (Z_to_bv 64 bm) = Some (4 * n)%Z).
    { rewrite (LEQf1 (Z_to_bv 64 bm)); [exact Lf0bm|]. intros EE. pose proof Lf0bm as X. rewrite EE in X. exact (DISJ_bm_rm EE). }
    assert (Lf1am : live Af1 (Z_to_bv 64 am) = Some (4 * n)%Z).
    { rewrite (LEQf1 (Z_to_bv 64 am)); [exact Lf0am|]. intros EE. pose proof Lf0am as X. rewrite EE in X. exact (DISJ_am_rm EE). }
    assert (Lf1pixd : live Af1 (Z_to_bv 64 pixd) = Some 64%Z).
    { rewrite (LEQf1 (Z_to_bv 64 pixd)); [exact Lf0pixd|]. intros EE. pose proof Lf0pixd as X. rewrite EE in X. exact (DISJ_pixd_rm EE). }
    assert (Lf1datad : live Af1 (Z_to_bv 64 datad) = Some (4 * (wpl_of w 8 * h))%Z).
    { rewrite (LEQf1 (Z_to_bv 64 datad)); [exact Lf0datad|]. intros EE. pose proof Lf0datad as X. rewrite EE in X. exact (DISJ_datad_rm EE). }
    pose proof Qf0gm as Qf1gm. rewrite <- (FRM_rdn16 C (s - 272) mf0 mf1 (s - 160)%Z 8 CK (proj1 PMf1)) in Qf1gm by (cbn; lia).
    pose proof Qf0bm as Qf1bm. rewrite <- (FRM_rdn16 C (s - 272) mf0 mf1 (s - 168)%Z 8 CK (proj1 PMf1)) in Qf1bm by (cbn; lia).
    pose proof Qf0am as Qf1am. rewrite <- (FRM_rdn16 C (s - 272) mf0 mf1 (s - 176)%Z 8 CK (proj1 PMf1)) in Qf1am by (cbn; lia).
    pose proof Fpdf0 as Fpdf1. rewrite <- (FRM_rdn16 C (s - 272) mf0 mf1 (s - 264)%Z 8 CK (proj1 PMf1)) in Fpdf1 by (cbn; lia).
    assert (PXdf1 : PIXat mf1 pixd (hdv w h 8 0 datad)).
    { apply (PIXat_frame mf0); [exact PXdf0|]. intros x Hx. exact (LIVK_at Af1 mf0 mf1 pixd 64 x (proj2 PMf1) Lf1pixd ltac:(lia) ltac:(lia) Hx). }
    assert (G2f1 : getr rf1 2 = Z_to_bv 64 (s - 272)) by (csr; reflexivity).
    assert (G4f1 : getr rf1 4 = Z_to_bv 64 0x455c0) by (csr; reflexivity).
    destruct (rmc_S7 al_rom (mkFP fr8 cs8) rf1 mf1 s gm ltac:(lia) ltac:(lia) Qf1gm G2f1) as (rg1 & RUNg1 & F1_2 & F10_2 & AGg1).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWf1)) | exact (mp_lazy _ (w_pure _ _ _ _ HWf1)) | exact RUNg1 |].
    assert (F2_2 : getr rg1 2 = Z_to_bv 64 (s - 272)) by (rewrite (AGg1 2%bv) by notin_list; exact G2f1).
    assert (F4_2 : getr rg1 4 = Z_to_bv 64 0x455c0) by (rewrite (AGg1 4%bv) by notin_list; exact G4f1).
    (* [comment removed for export] *)
    apply (@W_free16 (mkFP fr8 cs8) AL CL ASR PINS P16 C Af1 mf1 _ rg1 (Z_to_bv 64 gm) (Z_to_bv 64 0x1b5ac) (4 * n) (s - 272) S CK HWf1 F10_2 Lf1gm L0gm F1_2
             ltac:(red; apply bv_eq; reflexivity) F4_2 F2_2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)).
    intros Af2 mf2 vmf2 rf2 HWf2 CSf2 Ldead2 LEQf2 PMf2 RTRf2. rewrite with_vmmaps_twice. rewrite with_vmmaps_twice in HWf2.
    assert (SUBf2 : sub_live A Af2).
    { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 gm) by (intros ->; rewrite LAgm in Lq; discriminate Lq). rewrite (LEQf2 q NEq). exact (SUBf1 q kq Lq). }
    assert (PMaf2 : POSTM C A s m mf2).
    { eapply POSTM_trans; [exact PMaf1|]. apply (POSTM_sub C A Af2); [exact SUBf2|]. eapply POSTM_mono; [|exact PMf2]. lia. }
    pose proof (cellsZ_frm C (s - 272) mf1 mf2 (rmc_cells s regs) CK (proj1 PMf2) ltac:(lia) ltac:(unfold rmc_cells; repeat (apply Forall_cons; [cbn [fst]; lia|]); apply Forall_nil) CEf1) as CEf2.
    pose proof (RTRf2 _ _ ltac:(rewrite with_vmmaps_vmmaps; exact Hrmf1) ltac:(unfold RK_pix; lia) ltac:(unfold RB_pix14; lia)) as Hrmf2. rewrite !Z.sub_0_r in Hrmf2.
    assert (Lf2bm : live Af2 (Z_to_bv 64 bm) = Some (4 * n)%Z).
    { rewrite (LEQf2 (Z_to_bv 64 bm)); [exact Lf1bm|]. intros EE. pose proof Lf1bm as X. rewrite EE in X. exact (DISJ_bm_gm EE). }
    assert (Lf2am : live Af2 (Z_to_bv 64 am) = Some (4 * n)%Z).
    { rewrite (LEQf2 (Z_to_bv 64 am)); [exact Lf1am|]. intros EE. pose proof Lf1am as X. rewrite EE in X. exact (DISJ_am_gm EE). }
    assert (Lf2pixd : live Af2 (Z_to_bv 64 pixd) = Some 64%Z).
    { rewrite (LEQf2 (Z_to_bv 64 pixd)); [exact Lf1pixd|]. intros EE. pose proof Lf1pixd as X. rewrite EE in X. exact (DISJ_pixd_gm EE). }
    assert (Lf2datad : live Af2 (Z_to_bv 64 datad) = Some (4 * (wpl_of w 8 * h))%Z).
    { rewrite (LEQf2 (Z_to_bv 64 datad)); [exact Lf1datad|]. intros EE. pose proof Lf1datad as X. rewrite EE in X. exact (DISJ_datad_gm EE). }
    pose proof Qf1bm as Qf2bm. rewrite <- (FRM_rdn16 C (s - 272) mf1 mf2 (s - 168)%Z 8 CK (proj1 PMf2)) in Qf2bm by (cbn; lia).
    pose proof Qf1am as Qf2am. rewrite <- (FRM_rdn16 C (s - 272) mf1 mf2 (s - 176)%Z 8 CK (proj1 PMf2)) in Qf2am by (cbn; lia).
    pose proof Fpdf1 as Fpdf2. rewrite <- (FRM_rdn16 C (s - 272) mf1 mf2 (s - 264)%Z 8 CK (proj1 PMf2)) in Fpdf2 by (cbn; lia).
    assert (PXdf2 : PIXat mf2 pixd (hdv w h 8 0 datad)).
    { apply (PIXat_frame mf1); [exact PXdf1|]. intros x Hx. exact (LIVK_at Af2 mf1 mf2 pixd 64 x (proj2 PMf2) Lf2pixd ltac:(lia) ltac:(lia) Hx). }
    assert (G2f2 : getr rf2 2 = Z_to_bv 64 (s - 272)) by (csr; reflexivity).
    assert (G4f2 : getr rf2 4 = Z_to_bv 64 0x455c0) by (csr; reflexivity).
    destruct (rmc_S8 al_rom (mkFP fr8 cs8) rf2 mf2 s bm ltac:(lia) ltac:(lia) Qf2bm G2f2) as (rg2 & RUNg2 & F1_3 & F10_3 & AGg2).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWf2)) | exact (mp_lazy _ (w_pure _ _ _ _ HWf2)) | exact RUNg2 |].
    assert (F2_3 : getr rg2 2 = Z_to_bv 64 (s - 272)) by (rewrite (AGg2 2%bv) by notin_list; exact G2f2).
    assert (F4_3 : getr rg2 4 = Z_to_bv 64 0x455c0) by (rewrite (AGg2 4%bv) by notin_list; exact G4f2).
    (* [comment removed for export] *)
    apply (@W_free16 (mkFP fr8 cs8) AL CL ASR PINS P16 C Af2 mf2 _ rg2 (Z_to_bv 64 bm) (Z_to_bv 64 0x1b5b4) (4 * n) (s - 272) S CK HWf2 F10_3 Lf2bm L0bm F1_3
             ltac:(red; apply bv_eq; reflexivity) F4_3 F2_3 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)).
    intros Af3 mf3 vmf3 rf3 HWf3 CSf3 Ldead3 LEQf3 PMf3 RTRf3. rewrite with_vmmaps_twice. rewrite with_vmmaps_twice in HWf3.
    assert (SUBf3 : sub_live A Af3).
    { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 bm) by (intros ->; rewrite LAbm in Lq; discriminate Lq). rewrite (LEQf3 q NEq). exact (SUBf2 q kq Lq). }
    assert (PMaf3 : POSTM C A s m mf3).
    { eapply POSTM_trans; [exact PMaf2|]. apply (POSTM_sub C A Af3); [exact SUBf3|]. eapply POSTM_mono; [|exact PMf3]. lia. }
    pose proof (cellsZ_frm C (s - 272) mf2 mf3 (rmc_cells s regs) CK (proj1 PMf3) ltac:(lia) ltac:(unfold rmc_cells; repeat (apply Forall_cons; [cbn [fst]; lia|]); apply Forall_nil) CEf2) as CEf3.
    pose proof (RTRf3 _ _ ltac:(rewrite with_vmmaps_vmmaps; exact Hrmf2) ltac:(unfold RK_pix; lia) ltac:(unfold RB_pix14; lia)) as Hrmf3. rewrite !Z.sub_0_r in Hrmf3.
    assert (Lf3am : live Af3 (Z_to_bv 64 am) = Some (4 * n)%Z).
    { rewrite (LEQf3 (Z_to_bv 64 am)); [exact Lf2am|]. intros EE. pose proof Lf2am as X. rewrite EE in X. exact (DISJ_am_bm EE). }
    assert (Lf3pixd : live Af3 (Z_to_bv 64 pixd) = Some 64%Z).
    { rewrite (LEQf3 (Z_to_bv 64 pixd)); [exact Lf2pixd|]. intros EE. pose proof Lf2pixd as X. rewrite EE in X. exact (DISJ_pixd_bm EE). }
    assert (Lf3datad : live Af3 (Z_to_bv 64 datad) = Some (4 * (wpl_of w 8 * h))%Z).
    { rewrite (LEQf3 (Z_to_bv 64 datad)); [exact Lf2datad|]. intros EE. pose proof Lf2datad as X. rewrite EE in X. exact (DISJ_datad_bm EE). }
    pose proof Qf2am as Qf3am. rewrite <- (FRM_rdn16 C (s - 272) mf2 mf3 (s - 176)%Z 8 CK (proj1 PMf3)) in Qf3am by (cbn; lia).
    pose proof Fpdf2 as Fpdf3. rewrite <- (FRM_rdn16 C (s - 272) mf2 mf3 (s - 264)%Z 8 CK (proj1 PMf3)) in Fpdf3 by (cbn; lia).
    assert (PXdf3 : PIXat mf3 pixd (hdv w h 8 0 datad)).
    { apply (PIXat_frame mf2); [exact PXdf2|]. intros x Hx. exact (LIVK_at Af3 mf2 mf3 pixd 64 x (proj2 PMf3) Lf3pixd ltac:(lia) ltac:(lia) Hx). }
    assert (G2f3 : getr rf3 2 = Z_to_bv 64 (s - 272)) by (csr; reflexivity).
    assert (G4f3 : getr rf3 4 = Z_to_bv 64 0x455c0) by (csr; reflexivity).
    destruct (rmc_S9 al_rom (mkFP fr8 cs8) rf3 mf3 s am ltac:(lia) ltac:(lia) Qf3am G2f3) as (rg3 & RUNg3 & F1_4 & F10_4 & AGg3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWf3)) | exact (mp_lazy _ (w_pure _ _ _ _ HWf3)) | exact RUNg3 |].
    assert (F2_4 : getr rg3 2 = Z_to_bv 64 (s - 272)) by (rewrite (AGg3 2%bv) by notin_list; exact G2f3).
    assert (F4_4 : getr rg3 4 = Z_to_bv 64 0x455c0) by (rewrite (AGg3 4%bv) by notin_list; exact G4f3).
    (* [comment removed for export] *)
    apply (@W_free16 (mkFP fr8 cs8) AL CL ASR PINS P16 C Af3 mf3 _ rg3 (Z_to_bv 64 am) (Z_to_bv 64 0x1b5bc) (4 * n) (s - 272) S CK HWf3 F10_4 Lf3am L0am F1_4
             ltac:(red; apply bv_eq; reflexivity) F4_4 F2_4 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)).
    intros Af4 mf4 vmf4 rf4 HWf4 CSf4 Ldead4 LEQf4 PMf4 RTRf4. rewrite with_vmmaps_twice. rewrite with_vmmaps_twice in HWf4.
    assert (SUBf4 : sub_live A Af4).
    { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 am) by (intros ->; rewrite LAam in Lq; discriminate Lq). rewrite (LEQf4 q NEq). exact (SUBf3 q kq Lq). }
    assert (PMaf4 : POSTM C A s m mf4).
    { eapply POSTM_trans; [exact PMaf3|]. apply (POSTM_sub C A Af4); [exact SUBf4|]. eapply POSTM_mono; [|exact PMf4]. lia. }
    pose proof (cellsZ_frm C (s - 272) mf3 mf4 (rmc_cells s regs) CK (proj1 PMf4) ltac:(lia) ltac:(unfold rmc_cells; repeat (apply Forall_cons; [cbn [fst]; lia|]); apply Forall_nil) CEf3) as CEf4.
    pose proof (RTRf4 _ _ ltac:(rewrite with_vmmaps_vmmaps; exact Hrmf3) ltac:(unfold RK_pix; lia) ltac:(unfold RB_pix14; lia)) as Hrmf4. rewrite !Z.sub_0_r in Hrmf4.
    assert (Lf4pixd : live Af4 (Z_to_bv 64 pixd) = Some 64%Z).
    { rewrite (LEQf4 (Z_to_bv 64 pixd)); [exact Lf3pixd|]. intros EE. pose proof Lf3pixd as X. rewrite EE in X. exact (DISJ_pixd_am EE). }
    assert (Lf4datad : live Af4 (Z_to_bv 64 datad) = Some (4 * (wpl_of w 8 * h))%Z).
    { rewrite (LEQf4 (Z_to_bv 64 datad)); [exact Lf3datad|]. intros EE. pose proof Lf3datad as X. rewrite EE in X. exact (DISJ_datad_am EE). }
    pose proof Fpdf3 as Fpdf4. rewrite <- (FRM_rdn16 C (s - 272) mf3 mf4 (s - 264)%Z 8 CK (proj1 PMf4)) in Fpdf4 by (cbn; lia).
    assert (PXdf4 : PIXat mf4 pixd (hdv w h 8 0 datad)).
    { apply (PIXat_frame mf3); [exact PXdf3|]. intros x Hx. exact (LIVK_at Af4 mf3 mf4 pixd 64 x (proj2 PMf4) Lf4pixd ltac:(lia) ltac:(lia) Hx). }
    assert (G2f4 : getr rf4 2 = Z_to_bv 64 (s - 272)) by (csr; reflexivity).
    assert (G4f4 : getr rf4 4 = Z_to_bv 64 0x455c0) by (csr; reflexivity).
    (* [comment removed for export] *)
    destruct CEf4 as (C1 & C8 & C9 & C18 & C19 & C20 & C21 & C22 & C23 & C24 & C25 & C26 & C27 & _).
    destruct (rmc_SE al_rom (mkFP fr8 cs8) rf4 mf4 s pixd (u (getr regs 1)) (u (getr regs 8)) (u (getr regs 9)) (u (getr regs 18)) (u (getr regs 19)) (u (getr regs 20))
                (u (getr regs 21)) (u (getr regs 22)) (u (getr regs 23)) (u (getr regs 24)) (u (getr regs 25)) (u (getr regs 26)) (u (getr regs 27)) ltac:(lia) ltac:(lia)
                (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _)
                (u64_range _) (u64_range _) (u64_range _) Fpdf4
                (cell_w2z _ _ _ C1) (cell_w2z _ _ _ C8) (cell_w2z _ _ _ C9) (cell_w2z _ _ _ C18) (cell_w2z _ _ _ C19) (cell_w2z _ _ _ C20) (cell_w2z _ _ _ C21)
                (cell_w2z _ _ _ C22) (cell_w2z _ _ _ C23) (cell_w2z _ _ _ C24) (cell_w2z _ _ _ C25) (cell_w2z _ _ _ C26) (cell_w2z _ _ _ C27) G2f4)
      as (r12 & RUN12 & Z10 & Z2 & Z1 & Z8 & Z9 & Z18 & Z19 & Z20 & Z21 & Z22 & Z23 & Z24 & Z25 & Z26 & Z27 & AG12).
    rewrite zbv_self in Z1, Z8, Z9, Z18, Z19, Z20, Z21, Z22, Z23, Z24, Z25, Z26, Z27.
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWf4)) | exact (mp_lazy _ (w_pure _ _ _ _ HWf4)) | exact RUN12 |].
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWf4)) | exact (mp_lazy _ (w_pure _ _ _ _ HWf4))
                      | exact (rmc_ret al_rom (mkFP fr8 cs8) r12 mf4 ret Hret ltac:(rewrite Z1; exact H1)) |].
    apply (HK (mkFP fr8 cs8) Af4 mf4 vmf4 r12 Hz8 HWf4).
    + apply cs_kept_intro; try (rewrite ?Z2, ?Z8, ?Z9, ?Z18, ?Z19, ?Z20, ?Z21, ?Z22, ?Z23, ?Z24, ?Z25, ?Z26, ?Z27; first [reflexivity | (symmetry; exact H2)]).
      all: rewrite (AG12 _) by notin_list; csr; reflexivity.
    + right. split; [clear - Gcm; lia|]. split; [exact PMaf4|]. exists pixd, datad. split; [exact Z10|].
      unfold pixt_new. split; [exact Gpd|]. split; [exact TOPpd|]. split; [exact ALpd|]. split; [exact Gdd|]. split; [exact TOPdd|]. split; [exact ALdd|].
      split; [exact (box_e _ NEpd)|]. split; [exact LApd'|]. split; [exact LAdd'|]. split; [exact L0pd|]. split; [exact L0dd|].
      split; [exact Lf4pixd|]. split; [exact Lf4datad|]. split; [exact PXdf4|].
      left. split; [reflexivity|]. intros q Nqp Nqd.
      destruct (bv_eq_dec _ q (Z_to_bv 64 am)) as [->|Nam]; [rewrite Ldead4, LAam; reflexivity|]. rewrite (LEQf4 q Nam).
      destruct (bv_eq_dec _ q (Z_to_bv 64 bm)) as [->|Nbm]; [rewrite Ldead3, LAbm; reflexivity|]. rewrite (LEQf3 q Nbm).
      destruct (bv_eq_dec _ q (Z_to_bv 64 gm)) as [->|Ngm]; [rewrite Ldead2, LAgm; reflexivity|]. rewrite (LEQf2 q Ngm).
      destruct (bv_eq_dec _ q (Z_to_bv 64 rm)) as [->|Nrm]; [rewrite Ldead1, LArm; reflexivity|]. rewrite (LEQf1 q Nrm).
      destruct (bv_eq_dec _ q (Z_to_bv 64 g)) as [->|Ng]; [rewrite Ldead0, LAg; reflexivity|]. rewrite (LEQf0 q Ng).
      rewrite (LEQ6 q Ng). rewrite (LEQ4 q Nqp Nqd). exact (LEQ2 q Nrm Ngm Nbm Nam).
    + replace (kR - (2 + 5))%Z with (kR - 4 - 2 - 1)%Z by lia. replace (bR - (2 ^ 26 + 2 ^ 23 + 2 ^ 22 + 5 * 2 ^ 17))%Z with (bR - 4 * 2 ^ 17 - (2 ^ 26 + 2 ^ 23 + 2 ^ 22) - 2 ^ 17)%Z by lia.
      exact Hrmf4.
Qed.

End Rmc.
