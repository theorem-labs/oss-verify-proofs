From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FuzzProducer HufPure_FseDecomp HufPure_HufX1 HufPure_HufX2.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree FseWalkKit FseRdKit HufWalkKit HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require KXTac KXGoM.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AH_huf_iface AF_huf_dec_iface AF_huf_z4s3_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_z4s2_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_tbl_iface2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXCell KXCell2.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_z4s1_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_z4s3b.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_z4s1mk.

Notation amem := (word -> option byte).
Notation Zw z := (Z_to_bv 64 z) (only parsing).


(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac z4r_addr :=
  rewrite adenot_wa; f_equal;
  lazymatch goal with |- estart ?E _ = _ =>
    let b := eval unfold E in E in
    lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
      change E with (kE zv xs); kx_estart_z zv; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia end end.
Ltac z4r_stok :=
  lazymatch goal with
  | |- store_ok ?segs ?m _ ?j = true =>
      match goal with H : rw_cells segs m ?A ?cs |- _ =>
        first [ (eapply (rw_cells_store_ok_at segs m A cs 0%nat _ j _ H eq_refl eq_refl); z4r_addr)
                | (eapply (rw_cells_store_ok_at segs m A cs 8%nat _ j _ H eq_refl eq_refl); z4r_addr)
                | (eapply (rw_cells_store_ok_at segs m A cs 12%nat _ j _ H eq_refl eq_refl); z4r_addr)
                | (eapply (rw_cells_store_ok_at segs m A cs 16%nat _ j _ H eq_refl eq_refl); z4r_addr)
                | (eapply (rw_cells_store_ok_at segs m A cs 24%nat _ j _ H eq_refl eq_refl); z4r_addr)
                | (eapply (rw_cells_store_ok_at segs m A cs 32%nat _ j _ H eq_refl eq_refl); z4r_addr)
                | (eapply (rw_cells_store_ok_at segs m A cs 40%nat _ j _ H eq_refl eq_refl); z4r_addr)
                | (eapply (rw_cells_store_ok_at segs m A cs 48%nat _ j _ H eq_refl eq_refl); z4r_addr)
                | (eapply (rw_cells_store_ok_at segs m A cs 56%nat _ j _ H eq_refl eq_refl); z4r_addr)
                | (eapply (rw_cells_store_ok_at segs m A cs 64%nat _ j _ H eq_refl eq_refl); z4r_addr)
                | (eapply (rw_cells_store_ok_at segs m A cs 72%nat _ j _ H eq_refl eq_refl); z4r_addr)
                | (eapply (rw_cells_store_ok_at segs m A cs 80%nat _ j _ H eq_refl eq_refl); z4r_addr)
                | (eapply (rw_cells_store_ok_at segs m A cs 88%nat _ j _ H eq_refl eq_refl); z4r_addr)
                | (eapply (rw_cells_store_ok_at segs m A cs 96%nat _ j _ H eq_refl eq_refl); z4r_addr)
                | (eapply (rw_cells_store_ok_at segs m A cs 104%nat _ j _ H eq_refl eq_refl); z4r_addr)
                | (eapply (rw_cells_store_ok_at segs m A cs 112%nat _ j _ H eq_refl eq_refl); z4r_addr) ]
      end
  end.

Ltac z4r_srl :=
  repeat match goal with |- context [edenot ?E (EAluw ALU_SRL (EVar ?i) (ELit 3))] =>
    let zv := lazymatch E with
              | kE ?zv _ => zv
              | _ => let b := eval unfold E in E in lazymatch b with kx_env (map (Z_to_bv 64) ?zv) _ => zv end
              end in
    let v := eval cbv [nth] in (nth i zv 0) in
    rewrite (z4_srlw3 E (EVar i) v) by (first [reflexivity | lia])
  end.
Ltac z4r_lin T :=
  lazymatch goal with
  | |- context [edenot ?E _] =>
      let b := eval unfold E in E in
      lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
        let na := eval vm_compute in (length zv) in
        change E with (kE zv xs);
        rewrite ?(ez_ok zv (kE zv xs) (kE_atoms zv xs));
        cbv [ez]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb];
        z4r_srl;
        repeat match goal with
        | |- context [?c mod 64] => z4m_zlit c; let v := eval vm_compute in (c mod 64) in change (c mod 64) with v
        end;
        kx_tbl_idx T;
        rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 64) with (2^64);
        rewrite ?Z.mod_small by lia;
        kx_abstract; first [lia | Z.div_mod_to_equations; lia]
      end
  | |- _ => first [lia | Z.div_mod_to_equations; lia]
  end.
Ltac z4r_brx :=
  lazymatch goal with
  | |- branch_taken BC_NE (edenot ?E (EAlu ALU_XOR (ELit 1) (EAlu ALU_SLTU (EAlu ALU_XOR ?P ?B) (ELit 1))))
         (edenot ?E (ELit 0)) = true =>
      apply (z4_br_nz E P B); z4r_srl; z4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
      rewrite ?Z.mod_small by lia; first [lia | Z.div_mod_to_equations; lia]
  end.
Ltac z4r_flat T FS DS TF TD :=
  lazymatch goal with
  | |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ ?E (ELit ?w)) /\ _ =>
      let AP := lazymatch k with Zneg _ => FS | _ => DS end in
      apply (z4m_shd_ap E X B O k w _ _ _ AP);
      [z4r_lin T | lia | lia | lia | lia | z4r_lin T | z4r_lin T | lia | lia]
  | |- flat ?E (SA ?A ?k1) (elenZ ?E (ELit ?w1)) /\ flat ?E (SA ?B ?k) (elenZ ?E (ELit ?w)) /\ _ =>
      let AP := lazymatch k with Zneg _ => TF | _ => TD end in
      apply (z4m_ap E A k1 w1 B k w _ _ _ _ (or_introl AP));
      [lia | lia | z4r_lin T | z4r_lin T | z4r_lin T | z4r_lin T | lia | lia | lia | lia]
  end.
Ltac z4r_acc H :=
  lazymatch type of H with rng _ ?L ?N =>
  lazymatch goal with |- accP ?R ?E (?a, ?n) =>
    let b := eval unfold E in E in
    lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
      change E with (kE zv xs);
      apply (kx_acc_rng zv xs R L N a n H); [lia | | |];
      let na := eval vm_compute in (length zv) in
      cbv [ez a_base a_off]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb];
      z4r_srl; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite ?Z.mod_small by lia;
      first [lia | Z.div_mod_to_equations; lia]
    end end end.

Definition z4R_res (r : bool) (o cq cr o' b' : Z) : Prop :=
  if r then o' = o - cq /\ b' = cr else o' = o /\ b' = 8 * cq + cr.
Definition z4R_fl (r : bool) : Z := if r then 0 else 3.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Lemma z4R_srcwin : forall (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock)
    (rng_fs : alayout -> footprint -> Prop) (sp tp : word) (m0 : amem) (DST dcap SS DT mtl tl lo : Z) (src : list Z)
    (cells : list deltX2) (cbs : list byte) (pdt : aptr) (SBL SBH : Z) (rstk : region) (mm : amem),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  munch [(lo, bv_unsigned sp); (DST, DST + dcap)] m0 mm -> 1 <= dcap -> 0 < zlen src ->
  unpoisoned mm SS (SS + zlen src) /\ SBL mod 8 = 0 /\ SBL <= SS /\ SS + zlen src <= SBH /\
  rng RNG (shad SBL) (shlen (SBH - SBL + 7)) /\ rng RNG SS (zlen src).
Proof.
  intros AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk mm C MU D1 NZ.
  pose proof (z4ctx_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C D1)
    as (FD1 & FD2 & FD3 & FD4 & FD5 & FSS & FSP1 & FSP2 & FRS).
  destruct C as (AH & NFK & ABL & MTL & TLM & HDT & TOK & ECB & LCB & DSTF & DC & BYS & NSM & S16 & SRCB & DJ1 & DJ2 & DJ3
                 & LOA & LOS & SPT & SP16 & TPA & HINV & RCL & RLO & RHI & RRL & RRS & WSK & WIM & WIS & WFS).
  destruct (SRCB NZ) as (psb & HSB & SB1 & SB2).
  destruct (hb_unpoisoned AI L RNG st LB m0 psb SBL (SBH - SBL) AH HSB) as (SU & SA16 & SN1 & SAB & SAT & SRG & SSH & SWR).
  replace (SBL + (SBH - SBL)) with SBH in SU by lia.
  pose proof (ablk_disj_band _ _ SAB) as SDB2.
  pose proof (AI_layout AI _ _ _ _ _ AH) as LY.
  split; [| split; [lia | split; [lia | split; [lia | split; [exact SSH | eapply rng_sub; [exact SRG | lia | lia]]]]]].
  eapply unpoisoned_munch; [eapply unpoisoned_sub; [exact SU | lia | lia] | exact MU |].
  destruct DSTF as [(E1 & E2)|(pb & HDB)]; [lia|].
  pose proof (ablk_lin _ _ (ABL _ HDB)) as HDL. cbn [ab_addr ab_size] in HDL.
  pose proof (bv_unsigned_in_range _ sp) as SPR. unfold bv_modulus in SPR.
  pose proof (ablk_disj_band _ _ (ABL _ HDB)) as HDB2. cbn [ab_addr ab_size] in HDB2.
  destruct RCL as (SHC & RLT).
  pose proof (shclean_hull _ _ _ _ _ SHC) as (H1 & H2 & H3 & H4 & H5 & H6).
  cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF, AIMG_HI, KEND, KLS in *. atop_facts.
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  Z.div_mod_to_equations; lia.
Qed.

Lemma z4R_srctop : forall (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock)
    (rng_fs : alayout -> footprint -> Prop) (sp tp : word) (m0 : amem) (DST dcap SS DT mtl tl lo : Z) (src : list Z)
    (cells : list deltX2) (cbs : list byte) (pdt : aptr) (SBL SBH : Z) (rstk : region),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk -> 0 < zlen src ->
  SBH <= ATOP.
Proof.
  intros AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk C NZ.
  destruct C as (AH & NFK & ABL & MTL & TLM & HDT & TOK & ECB & LCB & DSTF & DC & BYS & NSM & S16 & SRCB & DJ1 & DJ2 & DJ3
                 & LOA & LOS & SPT & SP16 & TPA & HINV & RCL & RLO & RHI & RRL & RRS & WSK & WIM & WIS & WFS).
  destruct (SRCB NZ) as (psb & HSB & SB1 & SB2).
  destruct (hb_unpoisoned AI L RNG st LB m0 psb SBL (SBH - SBL) AH HSB) as (SU & SA16 & SN1 & SAB & SAT & SRG & SSH & SWR).
  lia.
Qed.

Section Z4RI.
  Variable RNG : footprint.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cbs : list byte) (Q : machine_state -> Prop).
  Notation SP := (bv_unsigned sp).
  Notation n := (zlen src).
  Notation seg := ((dcap + 3) / 4).
  Notation Zw z := (Z_to_bv 64 z) (only parsing).
  Notation Z4SF' := (Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs).
  Notation ZR pc mm r1 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29
             r30 r31 :=
    (MS (mkR r1 (Zw (SP + -384)) gp tp r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23
             r24 r25 r26 r27 r28 r29 r30 r31) FR (Zw pc) fc None mm (seg_rom bsegs)) (only parsing).
  Notation BDS k b jp O o := (BD4A k (Zw b) jp (Zw (SS + O + o)) (Zw (SS + O)) (Zw (SS + O + 8))) (only parsing).
  Notation SPL w0 w4 w5 w7 k2 k4 k3 :=
    (SPD w0 (Zw (DST + 3 * seg)) (Zw (tl + 256 * mtl)) (Zw (DST + dcap - 7)) w4 w5 (Zw (DST + dcap)) w7 k2
         (Zw (DST + seg)) (Zw (DST + 2 * seg)) k4 k3 (Zw (DT + 4)) (Zw dcap)) (only parsing).
  Notation CTX AI L st LB rng_fs cells pdt SBL SBH rstk :=
    (z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk) (only parsing).
  Notation LAY l1 l2 l3 := (1 <= l1 /\ 1 <= l2 /\ 1 <= l3 /\ 6 + l1 + l2 + l3 + 1 <= n /\ 6 <= dcap /\ 3 * seg <= dcap)
    (only parsing).

  (* [comment removed for export] *)
  Definition z4R_s2_goal (r1 r2 : bool) : Prop :=
    forall (AI : AMallocIface) (L : alayout) (st : astate) (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
           (cells : list deltX2) (pdt : aptr) (SBL SBH : Z) (rstk : region)
           mm (l1 l2 l3 e1 e2 e3 e4 o1 b1 o2 cq2 cr2 o3 cq3 cr3 o4 cq4 cr4 : Z) (c1 k2 k3 k4 : word)
           (jp1 jp2 jp3 jp4 : list byte) (w0 l13 l14 l15 l16 v14 v22 v27 v28 v29 v31 : word),
    CTX AI L st LB rng_fs cells pdt SBL SBH rstk -> LAY l1 l2 l3 -> z4R_pre l2 o2 cq2 cr2 r2 ->
    Z4SF' mm (SPL w0 (Zw (z4R_fl r1)) l13 (Zw 3) k2 k4 k3)
      (BDS k4 (8 * cq4 + cr4) jp4 (6 + l1 + l2 + l3) o4) (BDS k3 (8 * cq3 + cr3) jp3 (6 + l1 + l2) o3)
      (BDS k2 (8 * cq2 + cr2) jp2 (6 + l1) o2) (BDS c1 b1 jp1 6 o1) ->
    (forall mm' (o2' b2' : Z) (c2 : word) (u15 u22 u27 u28 u29 u31 : word),
       Z4SF' mm' (SPL w0 (Zw (z4R_fl r1)) l13 (Zw (z4R_fl r2)) c2 k4 k3)
         (BDS k4 (8 * cq4 + cr4) jp4 (6 + l1 + l2 + l3) o4) (BDS k3 (8 * cq3 + cr3) jp3 (6 + l1 + l2) o3)
         (BDS c2 b2' jp2 (6 + l1) o2') (BDS c1 b1 jp1 6 o1) ->
       z4R_res r2 o2 cq2 cr2 o2' b2' ->
       evtF bsegs RNG Q (ZR (if r2 then 587076 else 587608) mm' (Zw b2') (Zw (2^61)) (Zw (64 - tl)) (Zw (- DT - 5)) l15
                           (Zw (DST + e4)) c1 l16 (Zw (DST + e1)) (Zw (SS + 6 + o1)) (Zw (SS + 6 + l1 + o2')) u15
                           (Zw (SS + 6 + l1 + l2 + o3)) c2 (Zw (DST + e3)) (Zw (DST + e2)) (Zw (8 * cq3 + cr3))
                           (Zw AZ4_SB) u22 (Zw (SS + 6 + l1 + l2 + l3 + o4)) (Zw (8 * cq4 + cr4)) l14 (Zw b1) u27 u28
                           u29 (Zw (DT + 4)) u31)) ->
    evtF bsegs RNG Q (ZR (if r1 then 586868 else 587592) mm (Zw (8 * cq2 + cr2)) (Zw (2^61)) (Zw (64 - tl)) (Zw (- DT - 5))
                        l15 (Zw (DST + e4)) c1 l16 (Zw (DST + e1)) (Zw (SS + 6 + o1)) v14 (Zw (SS + 6 + l1 + o2))
                        (Zw (SS + 6 + l1 + l2 + o3)) k2 (Zw (DST + e3)) (Zw (DST + e2)) (Zw (8 * cq3 + cr3))
                        (Zw AZ4_SB) v22 (Zw (SS + 6 + l1 + l2 + l3 + o4)) (Zw (8 * cq4 + cr4)) l14 (Zw b1) v27 v28
                        v29 (Zw (DT + 4)) v31).

  (* [comment removed for export] *)
  Definition z4R_s34_goal (r1 r2 r3 r4 : bool) : Prop :=
    forall (AI : AMallocIface) (L : alayout) (st : astate) (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
           (cells : list deltX2) (pdt : aptr) (SBL SBH : Z) (rstk : region)
           mm (l1 l2 l3 e1 e2 e3 e4 o1 b1 o2 b2 o3 cq3 cr3 o4 cq4 cr4 : Z) (c1 c2 k3 k4 : word)
           (jp1 jp2 jp3 jp4 : list byte) (w0 l13 l14 l15 l16 v15 v22 v27 v28 v29 v31 : word),
    CTX AI L st LB rng_fs cells pdt SBL SBH rstk -> LAY l1 l2 l3 -> z4R_pre l3 o3 cq3 cr3 r3 ->
    z4R_pre (n - (6 + l1 + l2 + l3)) o4 cq4 cr4 r4 ->
    Z4SF' mm (SPL w0 (Zw (z4R_fl r1)) l13 (Zw (z4R_fl r2)) c2 k4 k3)
      (BDS k4 (8 * cq4 + cr4) jp4 (6 + l1 + l2 + l3) o4) (BDS k3 (8 * cq3 + cr3) jp3 (6 + l1 + l2) o3)
      (BDS c2 b2 jp2 (6 + l1) o2) (BDS c1 b1 jp1 6 o1) ->
    (forall mm' (o3' b3' o4' b4' : Z) (c3 c4 : word) (u10 u17 u22 u27 u31 : word),
       Z4SF' mm' (SPL w0 (Zw (z4R_fl r1)) l13 (Zw (z4R_fl r2)) c2 c4 c3)
         (BDS c4 b4' jp4 (6 + l1 + l2 + l3) o4') (BDS c3 b3' jp3 (6 + l1 + l2) o3')
         (BDS c2 b2 jp2 (6 + l1) o2) (BDS c1 b1 jp1 6 o1) ->
       z4R_res r3 o3 cq3 cr3 o3' b3' -> z4R_res r4 o4 cq4 cr4 o4' b4' ->
       evtF bsegs RNG Q (ZR 587500 mm' (Zw b2) (Zw (2^61)) (Zw (64 - tl)) (Zw (- DT - 5)) l15 (Zw (DST + e4)) u10 l16
                           (Zw (DST + e1)) (Zw (SS + 6 + o1)) (Zw (SS + 6 + l1 + o2)) (Zw (SS + 6 + l1 + l2 + o3'))
                           (Zw (SS + 6 + l1 + l2 + l3 + o4')) u17 (Zw (DST + e3)) (Zw (DST + e2)) (Zw b3')
                           (Zw AZ4_SB) u22 c1 (Zw b4') l14 (Zw b1) u27 (Zw (z4R_fl r4)) (Zw (z4R_fl r3))
                           (Zw (DT + 4)) u31)) ->
    evtF bsegs RNG Q (ZR (if r2 then 587076 else 587608) mm (Zw b2) (Zw (2^61)) (Zw (64 - tl)) (Zw (- DT - 5)) l15
                        (Zw (DST + e4)) c1 l16 (Zw (DST + e1)) (Zw (SS + 6 + o1)) (Zw (SS + 6 + l1 + o2)) v15
                        (Zw (SS + 6 + l1 + l2 + o3)) c2 (Zw (DST + e3)) (Zw (DST + e2)) (Zw (8 * cq3 + cr3))
                        (Zw AZ4_SB) v22 (Zw (SS + 6 + l1 + l2 + l3 + o4)) (Zw (8 * cq4 + cr4)) l14 (Zw b1) v27 v28
                        v29 (Zw (DT + 4)) v31).
End Z4RI.
End CANSEC1.
