(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FuzzProducer HufPure_FseDecomp HufPure_HufX1 HufPure_HufX2.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM KXCell KXCell2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require HufHarness.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AH_huf_iface AF_huf_dec_iface AF_huf_ax2 AF_huf_ax2b AF_huf_ax2c.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).

Section CANSEC1. Context {rc : runConstT}.
Section AX2D.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variables (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr) (SBL SBH : Z).
  Notation SP := (bv_unsigned sp).
  Notation SPF := (SP + -64).
  Notation n := (zlen src).
  Notation DTL := (DTABLE_BYTES mtl).
  Hypothesis AH : AHEAP AI L RNG st LB m0.
  Hypothesis HDT : In (HB pdt DT DTL) LB.
  Hypothesis HOUT : (DST = 0 /\ dcap = 0) \/ (exists pb, In (HB pb DST dcap) LB).
  Hypothesis LOA : ATOP + 4096 <= lo.
  Hypothesis LOS : lo <= SP - HUF_DEC_STACK_A.
  Hypothesis SPT : SP + 16 < al_top L.
  Hypothesis SP16 : SP mod 16 = 0.
  (* [comment removed for export] *)
  Hypothesis TOK : x2_table_ok cells tl.
  Hypothesis ECB : cbs = firstn (Z.to_nat (4 * 2^tl)) (x2_bytes' cells).
  Hypothesis LCB : zlen cbs = 4 * 2^tl.
  Hypothesis MTL : 1 <= mtl <= 12.
  Hypothesis TLM : tl <= mtl.
  (* [comment removed for export] *)
  Hypothesis DC : 0 <= dcap < 2^32.
  Hypothesis NSM : 1 <= n < 2^26.
  Hypothesis S16 : 16 <= SS.
  Hypothesis SBB : SBL <= SS /\ SS + n <= SBH.
  Hypothesis SBA : ablk SBL SBH /\ SBL mod 8 = 0.
  Hypothesis BYS : Forall (fun c => 0 <= c < 256) src.
  (* [comment removed for export] *)
  Hypothesis DJ1 : KXGoM.apart DST dcap DT DTL.
  Hypothesis DJ2 : KXGoM.apart DST dcap SS n.
  Hypothesis DJ3 : KXGoM.apart SS n DT DTL.
  (* [comment removed for export] *)
  Hypothesis UDT : unpoisoned m0 DT (DT + DTL).
  Hypothesis UDB : unpoisoned m0 DST (DST + dcap).
  Hypothesis USB : unpoisoned m0 SBL SBH.
  Hypothesis WSK : rng RNG lo (al_top L - lo).
  Hypothesis WIM : rng_aimg RNG.
  Hypothesis WDT : rng RNG DT DTL.
  Hypothesis WSB : rng RNG SBL (SBH - SBL).
  Hypothesis WDTS : rng RNG (shad DT) (shlen (DTL + 7)).
  Hypothesis WSBS : rng RNG (shad SBL) (shlen (SBH - SBL + 7)).
  Hypothesis WDB : 0 < dcap -> rng RNG DST dcap.
  Hypothesis WDBS : 0 < dcap -> rng RNG (shad DST) (shlen (dcap + 7)).

  Notation POST := (huf_dec_postA AI L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB DST dcap lo m0).

  Notation A2 l := (l AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs
                      pdt SBL SBH AH HDT HOUT LOA LOS SPT SP16 TOK ECB LCB MTL TLM DC NSM S16 SBB SBA BYS DJ1 DJ2 DJ3 UDT UDB USB
                      WSK WIM WDT WSB WDTS WSBS WDB WDBS) (only parsing).
  Notation AX2M' mm := (AX2M ra sp s0 s1 s2 s3 s4 s5 m0 DST dcap SS DT lo src cbs mm).

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  Notation XST := (ax2_st sp gp tp s7 s8 s9 s10 s11 FR fc dcap DT).
  Notation XBD := (ax2_bd sp SS).
  Notation XF := (AX2F ra sp s0 s1 s2 s3 s4 s5 s6 m0 DST dcap SS DT lo src cbs).
  Notation XPI P := (P = SS \/ (SS + 1 <= P /\ P + 8 <= SS + n)).
  Notation ZB z := (Z_to_bv 64 z).
  Notation PE := (Z_to_bv 64 (DST + dcap)).
  Notation DL := (Z_to_bv 64 (tl + 256 * mtl)).
  Notation G3924 := (ax2_goal_3924 AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0
                       DST dcap SS DT mtl tl lo src cbs).
  Notation G276 := (ax2_goal_276 AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0
                      DST dcap SS DT mtl tl lo src cbs).

  Ltac x5ez :=
    lazymatch goal with
    | |- context [edenot ?E _] =>
        let b := eval unfold E in E in
        lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
          rewrite ?(ez_ok zv E (kE_atoms zv xs));
          let na := eval vm_compute in (length zv) in
          cbv [ez]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb]
        end
    | |- _ => idtac
    end.
  Ltac x5br :=
    lazymatch goal with
    | |- branch_taken _ _ _ = _ =>
        x5ez; unfold branch_taken; rewrite ?bv_ltu_Z, ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
        rewrite ?Z.mod_small by lia;
        first [ apply Bool.negb_true_iff, Z.ltb_ge; lia | apply Z.ltb_lt; lia
              | apply Bool.negb_false_iff, Z.ltb_lt; lia | apply Z.ltb_ge; lia ]
    end.
  Lemma x5_srlw3 : forall E a, 0 <= bv_unsigned (edenot E a) < 2^31 ->
    bv_unsigned (edenot E (EAluw ALU_SRL a (ELit 3))) = bv_unsigned (edenot E a) / 8.
  Proof using.
    intros E a H. clear - H. cbn [edenot].
    rewrite (u_srlw_small (edenot E a) (Z_to_bv 64 3) 3); [reflexivity | reflexivity | lia |].
    change (2 ^ (3 mod 32)) with 8. apply Z.div_lt_upper_bound; lia.
  Qed.
  Ltac x5ezu := x5ez; rewrite ?srl_lit_ez, ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (Z.of_N 64) with 64 in *;
    change (3 mod 64) with 3 in *; change (2^3) with 8 in *.
  Ltac x5clr := repeat match goal with H : context [Z.modulo _ _] |- _ => clear H | H : context [Z.div _ _] |- _ => clear H end.
  Ltac x5z := cbn [a_base a_off]; x5ezu;
    rewrite ?x5_srlw3 by (x5ezu; rewrite Z.mod_small by lia; lia); x5ezu;
    x5clr; Z.div_mod_to_equations; lia.
  Ltac x5dj := unfold flat, estart, elenZ; x5z.
  Lemma x5_rd : forall (m : amem) E (a : saddr) A (bs : list byte) k,
    bytes_at bsegs m A bs -> A <= estart E a -> estart E a + Z.of_nat k <= A + Z.of_nat (length bs) ->
    exists r, rdn bsegs m (adenot E a) k = Some r.
  Proof using.
    intros m E a A bs k H H1 H2. clear - H H1 H2.
    set (N := Z.to_nat (estart E a - A)).
    exists (firstn k (skipn N bs)).
    change (adenot E a) with (wa (estart E a)).
    replace (estart E a) with (A + Z.of_nat N) by (unfold N; lia).
    apply bytes_at_rdn; [exact H | unfold N; lia].
  Qed.
  Ltac x5rd H := eapply x5_rd; [exact H | unfold estart; x5z | unfold estart; rewrite ?length_map; x5z].

  Ltac x5side :=
    try (lazymatch goal with
         | |- evtF _ _ _ _ => fail
         | |- flat _ _ _ /\ _ => x5dj
         | |- flat _ _ _ => x5dj
         | |- exists _, rdn _ _ _ _ = Some _ => lazymatch goal with H : bytes_at bsegs _ SS _ |- _ => x5rd H end
         | |- branch_taken _ _ _ = _ => x5br
         | |- _ => unfold KXGoM.apart in *; lia
         end).
  Ltac x5lit :=
    unfold AX2_K8, ASHOFF in *;
    let a := eval cbv in (2^31 - 2^15) in change (2^31 - 2^15) with a;
    let b := eval cbv in (2^61) in change (2^61) with b.

  Definition x5_H276 (jb : Z) : Prop := forall mm j bc P cont cw pad (x1 x10 x12 x18 x20 x21 x22 : word),
    XF mm -> XBD mm cw bc pad P -> jb < j <= dcap -> 0 <= bc <= 64 -> XPI P ->
    evtF bsegs RNG POST (XST 276 mm x1 (ZB bc) (ZB (DST + dcap - 9)) (ZB (- DT - 5)) (ZB (DST + j)) x10 (ZB P) x12
                             PE DL cont x18 x20 x21 x22 (ZB 65) (ZB (64 - tl)) (ZB 1) (ZB AX2_K8)).
  Definition x5_g764 (jb : Z) : Prop := forall mm j bc P fl cont cw pad (x1 x11 x18 x20 x21 x22 : word),
    XF mm -> XBD mm cw bc pad P -> 1 <= dcap -> 0 <= jb <= j -> j <= dcap -> (fl = 0 \/ fl = 1) -> 0 <= bc <= 64 -> XPI P ->
    evtF bsegs RNG POST (XST 764 mm x1 (ZB bc) (ZB (DST + dcap - 9)) (ZB (- DT - 5)) (ZB (DST + j)) (ZB P) x11 (ZB fl)
                             PE DL cont x18 x20 x21 x22 (ZB 65) (ZB (64 - tl)) (ZB 1) (ZB AX2_K8)).
  Definition x5_gm (k room bcmax jb : Z) : Prop := forall mm j bc idx P cont cw bcw pad (x1 x12 x18 x20 x21 x22 : word),
    XF mm -> XBD mm cw bcw pad P -> 0 <= jb <= j -> room <= dcap - j -> 0 <= bc <= bcmax -> 0 <= idx < 2^tl -> XPI P ->
    evtF bsegs RNG POST (XST k mm x1 (ZB bc) (ZB (DST + dcap - 9)) (ZB (- DT - 5)) (ZB (DST + j)) (ZB P) (ZB (DT + 4 * idx + 4)) x12
                             PE DL cont x18 x20 x21 x22 (ZB 65) (ZB (64 - tl)) (ZB 1) (ZB AX2_K8)).
  Notation G1012 jb := (x5_gm 1012 8 400 jb).
  Notation G1192 jb := (x5_gm 1192 6 700 jb).
  Notation G1360 jb := (x5_gm 1360 4 1000 jb).
  Notation G1528 jb := (x5_gm 1528 2 1300 jb).

  Definition x5_A276 (j : Z) : Prop := forall mm bc P cont cw pad (x1 x10 x12 x18 x20 x21 x22 : word),
    XF mm -> XBD mm cw bc pad P -> 1 <= dcap -> 0 <= j <= dcap -> 0 <= bc <= 64 -> XPI P ->
    evtF bsegs RNG POST (XST 276 mm x1 (ZB bc) (ZB (DST + dcap - 9)) (ZB (- DT - 5)) (ZB (DST + j)) x10 (ZB P) x12
                             PE DL cont x18 x20 x21 x22 (ZB 65) (ZB (64 - tl)) (ZB 1) (ZB AX2_K8)).

  Lemma x5_loop :
    (forall j, x5_g764 j -> x5_A276 j) ->
    (forall jb, G3924 -> G1012 jb -> x5_g764 jb) ->
    (forall jb, G1192 jb -> G1012 jb) -> (forall jb, G1360 jb -> G1192 jb) -> (forall jb, G1528 jb -> G1360 jb) ->
    (forall jb, x5_H276 jb -> G3924 -> G1528 jb) ->
    G3924 -> G276.
  Proof using All.
    intros RL B1 M2 M3 M4 M5 G.
    assert (A : forall k j, 0 <= j -> dcap - j < Z.of_nat k -> x5_A276 j).
    { induction k as [|k IH]; intros j J0 Hk.
      - unfold x5_A276. intros. lia.
      - apply RL. apply B1; [exact G |]. apply M2. apply M3. apply M4. apply M5; [| exact G].
        unfold x5_H276. intros mm j' bc P cont cw pad x1 x10 x12 x18 x20 x21 x22 HF HB HJ HBC HP.
        pose proof (IH j' ltac:(lia) ltac:(lia)) as IA. unfold x5_A276 in IA.
        exact (IA mm bc P cont cw pad x1 x10 x12 x18 x20 x21 x22 HF HB ltac:(lia) ltac:(lia) HBC HP). }
    unfold ax2_goal_276. intros mm j bc P cont cw pad x1 x10 x12 x18 x20 x21 x22 HF HB HD HJ HBC HP.
    pose proof (A (S (Z.to_nat (dcap - j))) j ltac:(lia) ltac:(lia)) as IA. unfold x5_A276 in IA.
    exact (IA mm bc P cont cw pad x1 x10 x12 x18 x20 x21 x22 HF HB HD HJ HBC HP).
  Qed.
  Lemma x5m2_idx : forall E a s, bv_unsigned (edenot E s) = 64 - tl -> 1 <= tl <= 12 ->
    0 <= bv_unsigned (edenot E (EAlu ALU_SRL a s)) < 2^tl.
  Proof using.
    intros E a s H T. clear - H T. cbn [edenot]. rewrite u_srl64, H, Z.mod_small by lia.
    pose proof (bv_unsigned_in_range 64 (edenot E a)) as R. unfold bv_modulus in R. change (Z.of_N 64) with 64 in R.
    split; [apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia] |].
    apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia |].
    rewrite <- Z.pow_add_r by lia. replace (64 - tl + tl) with 64 by lia. lia.
  Time Qed.
  Ltac x5m2ix :=
    repeat match goal with |- context [bv_unsigned (edenot ?E (EAlu ALU_SRL ?a ?s))] =>
      let B := fresh "IXB" in let v := fresh "ix" in
      pose proof (x5m2_idx E a s ltac:(x5ezu; rewrite Z.mod_small by lia; lia) ltac:(lia)) as B;
      set (v := bv_unsigned (edenot E (EAlu ALU_SRL a s))) in *; clearbody v
    end.
  Ltac x5m2dj := unfold flat, estart, elenZ; cbn [a_base a_off]; x5ezu; x5m2ix; x5z.

  Lemma x5_m2 : forall jb, G1192 jb -> G1012 jb.
  Proof using All.
    intros jb HN. unfold x5_gm.
    intros mm j bc idx P cont cw bcw pad x1 x12 x18 x20 x21 x22 HF HB HJ HR HBC HI HP.
    pose proof HF as ((buf & OUT & LBF) & SRCB & CBS & STK & (g & GAP) & FRC & MI & MU & WM).
    pose proof (A2 ax2_sp_bounds) as SB. pose proof (A2 ax2_unp' mm MU) as (UDT' & UDB' & USB').
    unfold HUF_DEC_STACK_A in LOS. pose proof (AI_layout AI L RNG st LB m0 AH) as (_ & _ & TOP & _).
    destruct SBB as (SB1 & SB2).
    pose proof (A2 ax2_blocks) as (B1 & B2 & B3 & B4 & B5 & B6). pose proof (A2 ax2_outb) as OB.
    pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP.
    pose proof ATOP_range as ATR; unfold ATOP_MIN, ATOP_MAX in ATR. unfold AIMG_HI, KLS in *.
    assert (DTL0 : 0 <= DTL) by (unfold DTABLE_BYTES, HufHarness.DT_BYTES; assert (0 < 2^mtl) by lia; lia).
    pose proof (WDB ltac:(lia)) as WDB'. pose proof (WDBS ltac:(lia)) as WDBS'.
    pose proof (A2 ax2_tab mm CBS) as TB.
    pose proof TOK as (TL & TC & TCK); unfold HUF_TABLELOG_MAX in TL.
    assert (P2 : 2 <= 2 ^ tl <= 4096) by (split; [change 2 with (2^1) at 1 | change 4096 with (2^12)]; apply Z.pow_le_mono_r; lia).
    assert (DTLb : DT + 4 + 4 * 2^tl <= DT + DTABLE_BYTES mtl)
      by (unfold DTABLE_BYTES, HufHarness.DT_BYTES; assert (2^tl <= 2^mtl) by (apply Z.pow_le_mono_r; lia); lia).
    unfold ax2_bd in HB. unfold ax2_st. x5lit.
    assert (ND : - DT - 5 = -1 * DT - 5) by lia. rewrite ND.
    let p := eval cbv in (AHUF_DX2_1X + 1012) in change (AHUF_DX2_1X + 1012) with p.
    let s1 := eval cbv in (AHUF_DX2_1X + 1192) in
    kx_runFL [s1] 90%nat
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange tl 1 12; KZRange (2^tl) 2 4096;
       KZTab (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)];
       KZRange idx 0 4095; KZRange (2^tl - idx - 1) 0 4095;
       KZRange SP 4096 (2^47); KZRange DT 4096 (2^47); KZRange DST 4096 (2^47);
       KZRange (dcap - j) 8 (2^32); KZRange j 0 (2^32); KZRange dcap 0 (2^32); KZRange (DST + j) 4096 (2^47);
       KZRange bc 0 400; KZWr (DST + j) 2; KZDisj (DST + j) 2 (DT + 4) (4 * 2^tl);
       KZWr (SP + -104) 40; KZDisj (SP + -104) 40 (DT + 4) (4 * 2^tl); KZDisj (SP + -104) 40 (DST + j) 2]
      [(DT + 4, 4 * 2^tl)] [(DT + 4, 4 * 2^tl); (DST + j, 2); (SP + -112, 112)] [(DT + 4, 4 * 2^tl); (DST + j, 2)].
    all: try x5side.
    all: try (lazymatch goal with |- flat _ _ _ /\ _ => x5m2dj end).
    all: lazymatch goal with |- evtF _ _ _ _ => idtac | |- ?g => fail "SIDE" g end.
    kx_post_regs_keep.
    kx_range (EVar 29) R29. kx_range (EVar 31) R31.
    destruct (B6 ltac:(lia)) as (Q1 & Q2 & Q3 & Q4').
    assert (LCBn : Z.of_nat (length cbs) = 4 * 2 ^ tl) by exact LCB.
    assert (LSM : Z.of_nat (length (map (Z_to_bv 8) src)) = n) by (rewrite length_map; reflexivity).
    kx_cells_split HB.
    lazymatch goal with H : rw_cells bsegs mm (SP + -96) [C4 _] |- _ => kx_cell4 H end.
    lazymatch goal with HL : log_flat _ _ |- _ =>
      destruct (kx_u8arr_ex bsegs _ mm _ DST buf OUT HL) as (buf' & OUT' & LB') end.
    pose proof (munch_refl [(DST + j, DST + j + 2); (SP + -96, SP + -96 + 4)] mm) as MUW.
    pose proof (wmono_refl bsegs mm) as WMr.
    kx_munch_wins MUW [(DST + j, 2); (SP + -96, 4)]. kx_munch_wins MU [(DST + j, 2); (SP + -96, 4)].
    kx_post_mem_free.
    lazymatch goal with |- context [mem_denot ?E mm ?l] => remember (mem_denot E mm l) as m1 eqn:EM1 end.
    clear OUT.
    unfold KXGoM.apart in DJ1, DJ2, DJ3.
    transport_after_call bsegs mm m1 MUW WMr.
    assert (XF' : XF m1)
      by (unfold AX2F; split; [exists buf'; split; [exact OUT' | unfold zlen in *; rewrite LB'; exact LBF] |];
          repeat (split; [first [eassumption | eexists; eassumption] |]); first [eassumption | eexists; eassumption]).
    unfold x5_gm, ax2_st in HN. unfold AX2_K8 in HN.
    let p := eval cbv in (AHUF_DX2_1X + 1192) in change (AHUF_DX2_1X + 1192) with p in HN.
    let a := eval cbv in (2^31 - 2^15) in change (2^31 - 2^15) with a in HN.
    let b := eval cbv in (2^61) in change (2^61) with b in HN.
    eapply HN; [exact XF' | unfold ax2_bd; kx_cells_merge | ..].
    all: try lia.
    all: try (apply x5m2_idx; [x5ezu; rewrite Z.mod_small by lia; lia | lia]).
  Time Qed.
  Ltac x5b1g G HF HB :=
    kx_post_regs_keep;
    lazymatch goal with |- context [mem_denot ?E ?mm []] => change (mem_denot E mm []) with mm end;
    unfold ax2_goal_3924, ax2_st in G; eapply G; [exact HF | exact HB | lia | lia | intros; assumption].

  Lemma x5_b1 : forall jb, G3924 -> G1012 jb -> x5_g764 jb.
  Proof using All.
    intros jb G HN. unfold x5_g764.
    intros mm j bc P fl cont cw pad x1 x11 x18 x20 x21 x22 HF HB HD1 HJ HJD HFL HBC HP.
    pose proof HF as ((buf & OUT & LBF) & SRCB & CBS & STK & (g & GAP) & FRC & MI & MU & WM).
    pose proof (A2 ax2_sp_bounds) as SB. pose proof (A2 ax2_unp' mm MU) as (UDT' & UDB' & USB').
    unfold HUF_DEC_STACK_A in LOS. pose proof (AI_layout AI L RNG st LB m0 AH) as (_ & _ & TOP & _).
    destruct SBB as (SB1 & SB2).
    pose proof (A2 ax2_blocks) as (B1 & B2 & B3 & B4 & B5 & B6). pose proof (A2 ax2_outb) as OB.
    pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP.
    pose proof ATOP_range as ATR; unfold ATOP_MIN, ATOP_MAX in ATR. unfold AIMG_HI, KLS in *.
    assert (DTL0 : 0 <= DTL) by (unfold DTABLE_BYTES, HufHarness.DT_BYTES; assert (0 < 2^mtl) by lia; lia).
    pose proof (A2 ax2_tab mm CBS) as TB.
    pose proof TOK as (TL & TC & TCK); unfold HUF_TABLELOG_MAX in TL.
    assert (P2 : 2 <= 2 ^ tl <= 4096) by (split; [change 2 with (2^1) at 1 | change 4096 with (2^12)]; apply Z.pow_le_mono_r; lia).
    assert (DTLb : DT + 4 + 4 * 2^tl <= DT + DTABLE_BYTES mtl)
      by (unfold DTABLE_BYTES, HufHarness.DT_BYTES; assert (2^tl <= 2^mtl) by (apply Z.pow_le_mono_r; lia); lia).
    assert (DSTb : 4096 <= DST /\ DST + dcap <= 2^47) by lia.
    unfold ax2_bd in HB. unfold ax2_st. x5lit.
    assert (ND : - DT - 5 = -1 * DT - 5) by lia. rewrite ND.
    let p := eval cbv in (AHUF_DX2_1X + 764) in change (AHUF_DX2_1X + 764) with p.
    destruct HFL as [-> | ->]; destruct (Z_lt_ge_dec (dcap - j) 10) as [HR | HR].
    - let s1 := eval cbv in (AHUF_DX2_1X + 1012) in let s2 := eval cbv in (AHUF_DX2_1X + 3924) in
      kx_runFm [s1; s2] 20%nat
        [KZRange (dcap - j) 0 9; KZRange j 0 (2^32); KZRange dcap 1 (2^32); KZRange DST 4096 (2^47)]
        (@nil (Z * Z)) (@nil (Z * Z)) (@nil (Z * Z)).
      all: try x5side.
      x5b1g G HF HB.
    - let s1 := eval cbv in (AHUF_DX2_1X + 1012) in let s2 := eval cbv in (AHUF_DX2_1X + 3924) in
      kx_runFm [s1; s2] 20%nat
        [KZRange (dcap - j) 10 (2^32); KZRange j 0 (2^32); KZRange dcap 1 (2^32); KZRange DST 4096 (2^47)]
        (@nil (Z * Z)) (@nil (Z * Z)) (@nil (Z * Z)).
      all: try x5side.
      x5b1g G HF HB.
    - let s1 := eval cbv in (AHUF_DX2_1X + 1012) in let s2 := eval cbv in (AHUF_DX2_1X + 3924) in
      kx_runFm [s1; s2] 20%nat
        [KZRange (dcap - j) 0 9; KZRange j 0 (2^32); KZRange dcap 1 (2^32); KZRange DST 4096 (2^47)]
        (@nil (Z * Z)) (@nil (Z * Z)) (@nil (Z * Z)).
      all: try x5side.
      x5b1g G HF HB.
    - pose proof (WDB ltac:(lia)) as WDB'. pose proof (WDBS ltac:(lia)) as WDBS'.
      let s1 := eval cbv in (AHUF_DX2_1X + 1012) in let s2 := eval cbv in (AHUF_DX2_1X + 3924) in
      kx_runFL [s1; s2] 90%nat
        [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange tl 1 12; KZRange (2^tl) 2 4096;
         KZTab (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)];
         KZRange SP 4096 (2^47); KZRange DT 4096 (2^47); KZRange DST 4096 (2^47);
         KZRange (dcap - j) 10 (2^32); KZRange j 0 (2^32); KZRange dcap 0 (2^32); KZRange (DST + j) 4096 (2^47);
         KZRange bc 0 64; KZWr (DST + j) 2; KZDisj (DST + j) 2 (DT + 4) (4 * 2^tl);
         KZWr (SP + -104) 40; KZDisj (SP + -104) 40 (DT + 4) (4 * 2^tl); KZDisj (SP + -104) 40 (DST + j) 2]
        [(DT + 4, 4 * 2^tl)] [(DT + 4, 4 * 2^tl); (DST + j, 2); (SP + -112, 112)] [(DT + 4, 4 * 2^tl); (DST + j, 2)].
      all: try x5side.
      all: try (lazymatch goal with |- flat _ _ _ /\ _ => x5m2dj end).
      kx_post_regs_keep.
      kx_range (EVar 29) R29. kx_range (EVar 31) R31.
      destruct (B6 ltac:(lia)) as (Q1 & Q2 & Q3 & Q4').
      assert (LCBn : Z.of_nat (length cbs) = 4 * 2 ^ tl) by exact LCB.
      assert (LSM : Z.of_nat (length (map (Z_to_bv 8) src)) = n) by (rewrite length_map; reflexivity).
      kx_cells_split HB.
      lazymatch goal with H : rw_cells bsegs mm (SP + -96) [C4 _] |- _ => kx_cell4 H end.
      lazymatch goal with HL : log_flat _ _ |- _ =>
        destruct (kx_u8arr_ex bsegs _ mm _ DST buf OUT HL) as (buf' & OUT' & LB') end.
      pose proof (munch_refl [(DST + j, DST + j + 2); (SP + -96, SP + -96 + 4)] mm) as MUW.
      pose proof (wmono_refl bsegs mm) as WMr.
      kx_munch_wins MUW [(DST + j, 2); (SP + -96, 4)]. kx_munch_wins MU [(DST + j, 2); (SP + -96, 4)].
      kx_post_mem_free.
      lazymatch goal with |- context [mem_denot ?E mm ?l] => remember (mem_denot E mm l) as m1 eqn:EM1 end.
      clear OUT.
      unfold KXGoM.apart in DJ1, DJ2, DJ3.
      transport_after_call bsegs mm m1 MUW WMr.
      assert (XF' : XF m1)
        by (unfold AX2F; split; [exists buf'; split; [exact OUT' | unfold zlen in *; rewrite LB'; exact LBF] |];
            repeat (split; [first [eassumption | eexists; eassumption] |]); first [eassumption | eexists; eassumption]).
      unfold x5_gm, ax2_st in HN. unfold AX2_K8 in HN.
      let p := eval cbv in (AHUF_DX2_1X + 1012) in change (AHUF_DX2_1X + 1012) with p in HN.
      let a := eval cbv in (2^31 - 2^15) in change (2^31 - 2^15) with a in HN.
      let b := eval cbv in (2^61) in change (2^61) with b in HN.
      eapply HN; [exact XF' | unfold ax2_bd; kx_cells_merge | ..].
      all: try lia.
      all: try (apply x5m2_idx; [x5ezu; rewrite Z.mod_small by lia; lia | lia]).
  Time Qed.
  Lemma x5_m4 : forall jb, G1528 jb -> G1360 jb.
  Proof using All.
    intros jb HN. unfold x5_gm.
    intros mm j bc idx P cont cw bcw pad x1 x12 x18 x20 x21 x22 HF HB HJ HR HBC HI HP.
    pose proof HF as ((buf & OUT & LBF) & SRCB & CBS & STK & (g & GAP) & FRC & MI & MU & WM).
    pose proof (A2 ax2_sp_bounds) as SB. pose proof (A2 ax2_unp' mm MU) as (UDT' & UDB' & USB').
    unfold HUF_DEC_STACK_A in LOS. pose proof (AI_layout AI L RNG st LB m0 AH) as (_ & _ & TOP & _).
    destruct SBB as (SB1 & SB2).
    pose proof (A2 ax2_blocks) as (B1 & B2 & B3 & B4 & B5 & B6). pose proof (A2 ax2_outb) as OB.
    pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP.
    pose proof ATOP_range as ATR; unfold ATOP_MIN, ATOP_MAX in ATR. unfold AIMG_HI, KLS in *.
    assert (DTL0 : 0 <= DTL) by (unfold DTABLE_BYTES, HufHarness.DT_BYTES; assert (0 < 2^mtl) by lia; lia).
    pose proof (WDB ltac:(lia)) as WDB'. pose proof (WDBS ltac:(lia)) as WDBS'.
    pose proof (A2 ax2_tab mm CBS) as TB.
    pose proof TOK as (TL & TC & TCK); unfold HUF_TABLELOG_MAX in TL.
    assert (P2 : 2 <= 2 ^ tl <= 4096) by (split; [change 2 with (2^1) at 1 | change 4096 with (2^12)]; apply Z.pow_le_mono_r; lia).
    assert (DTLb : DT + 4 + 4 * 2^tl <= DT + DTABLE_BYTES mtl)
      by (unfold DTABLE_BYTES, HufHarness.DT_BYTES; assert (2^tl <= 2^mtl) by (apply Z.pow_le_mono_r; lia); lia).
    unfold ax2_bd in HB. unfold ax2_st. x5lit.
    assert (ND : - DT - 5 = -1 * DT - 5) by lia. rewrite ND.
    let p := eval cbv in (AHUF_DX2_1X + 1360) in change (AHUF_DX2_1X + 1360) with p.
    let s1 := eval cbv in (AHUF_DX2_1X + 1528) in
    kx_runFL [s1] 90%nat
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange tl 1 12; KZRange (2^tl) 2 4096;
       KZTab (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)];
       KZRange idx 0 4095; KZRange (2^tl - idx - 1) 0 4095;
       KZRange SP 4096 (2^47); KZRange DT 4096 (2^47); KZRange DST 4096 (2^47);
       KZRange (dcap - j) 4 (2^32); KZRange j 0 (2^32); KZRange dcap 0 (2^32); KZRange (DST + j) 4096 (2^47);
       KZRange bc 0 1000; KZWr (DST + j) 2; KZDisj (DST + j) 2 (DT + 4) (4 * 2^tl);
       KZWr (SP + -104) 40; KZDisj (SP + -104) 40 (DT + 4) (4 * 2^tl); KZDisj (SP + -104) 40 (DST + j) 2]
      [(DT + 4, 4 * 2^tl)] [(DT + 4, 4 * 2^tl); (DST + j, 2); (SP + -112, 112)] [(DT + 4, 4 * 2^tl); (DST + j, 2)].
    all: try x5side.
    all: try (lazymatch goal with |- flat _ _ _ /\ _ => x5m2dj end).
    all: lazymatch goal with |- evtF _ _ _ _ => idtac | |- ?g => fail "SIDE" g end.
    kx_post_regs_keep.
    kx_range (EVar 29) R29. kx_range (EVar 31) R31.
    destruct (B6 ltac:(lia)) as (Q1 & Q2 & Q3 & Q4').
    assert (LCBn : Z.of_nat (length cbs) = 4 * 2 ^ tl) by exact LCB.
    assert (LSM : Z.of_nat (length (map (Z_to_bv 8) src)) = n) by (rewrite length_map; reflexivity).
    kx_cells_split HB.
    lazymatch goal with H : rw_cells bsegs mm (SP + -96) [C4 _] |- _ => kx_cell4 H end.
    lazymatch goal with HL : log_flat _ _ |- _ =>
      destruct (kx_u8arr_ex bsegs _ mm _ DST buf OUT HL) as (buf' & OUT' & LB') end.
    pose proof (munch_refl [(DST + j, DST + j + 2); (SP + -96, SP + -96 + 4)] mm) as MUW.
    pose proof (wmono_refl bsegs mm) as WMr.
    kx_munch_wins MUW [(DST + j, 2); (SP + -96, 4)]. kx_munch_wins MU [(DST + j, 2); (SP + -96, 4)].
    kx_post_mem_free.
    lazymatch goal with |- context [mem_denot ?E mm ?l] => remember (mem_denot E mm l) as m1 eqn:EM1 end.
    clear OUT.
    unfold KXGoM.apart in DJ1, DJ2, DJ3.
    transport_after_call bsegs mm m1 MUW WMr.
    assert (XF' : XF m1)
      by (unfold AX2F; split; [exists buf'; split; [exact OUT' | unfold zlen in *; rewrite LB'; exact LBF] |];
          repeat (split; [first [eassumption | eexists; eassumption] |]); first [eassumption | eexists; eassumption]).
    unfold x5_gm, ax2_st in HN. unfold AX2_K8 in HN.
    let p := eval cbv in (AHUF_DX2_1X + 1528) in change (AHUF_DX2_1X + 1528) with p in HN.
    let a := eval cbv in (2^31 - 2^15) in change (2^31 - 2^15) with a in HN.
    let b := eval cbv in (2^61) in change (2^61) with b in HN.
    eapply HN; [exact XF' | unfold ax2_bd; kx_cells_merge | ..].
    all: try lia.
    all: try (apply x5m2_idx; [x5ezu; rewrite Z.mod_small by lia; lia | lia]).
  Time Qed.
  Lemma x5_m3 : forall jb, G1360 jb -> G1192 jb.
  Proof using All.
    intros jb HN. unfold x5_gm.
    intros mm j bc idx P cont cw bcw pad x1 x12 x18 x20 x21 x22 HF HB HJ HR HBC HI HP.
    pose proof HF as ((buf & OUT & LBF) & SRCB & CBS & STK & (g & GAP) & FRC & MI & MU & WM).
    pose proof (A2 ax2_sp_bounds) as SB. pose proof (A2 ax2_unp' mm MU) as (UDT' & UDB' & USB').
    unfold HUF_DEC_STACK_A in LOS. pose proof (AI_layout AI L RNG st LB m0 AH) as (_ & _ & TOP & _).
    destruct SBB as (SB1 & SB2).
    pose proof (A2 ax2_blocks) as (B1 & B2 & B3 & B4 & B5 & B6). pose proof (A2 ax2_outb) as OB.
    pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP.
    pose proof ATOP_range as ATR; unfold ATOP_MIN, ATOP_MAX in ATR. unfold AIMG_HI, KLS in *.
    assert (DTL0 : 0 <= DTL) by (unfold DTABLE_BYTES, HufHarness.DT_BYTES; assert (0 < 2^mtl) by lia; lia).
    pose proof (WDB ltac:(lia)) as WDB'. pose proof (WDBS ltac:(lia)) as WDBS'.
    pose proof (A2 ax2_tab mm CBS) as TB.
    pose proof TOK as (TL & TC & TCK); unfold HUF_TABLELOG_MAX in TL.
    assert (P2 : 2 <= 2 ^ tl <= 4096) by (split; [change 2 with (2^1) at 1 | change 4096 with (2^12)]; apply Z.pow_le_mono_r; lia).
    assert (DTLb : DT + 4 + 4 * 2^tl <= DT + DTABLE_BYTES mtl)
      by (unfold DTABLE_BYTES, HufHarness.DT_BYTES; assert (2^tl <= 2^mtl) by (apply Z.pow_le_mono_r; lia); lia).
    unfold ax2_bd in HB. unfold ax2_st. x5lit.
    assert (ND : - DT - 5 = -1 * DT - 5) by lia. rewrite ND.
    let p := eval cbv in (AHUF_DX2_1X + 1192) in change (AHUF_DX2_1X + 1192) with p.
    let s1 := eval cbv in (AHUF_DX2_1X + 1360) in
    kx_runFL [s1] 90%nat
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange tl 1 12; KZRange (2^tl) 2 4096;
       KZTab (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)];
       KZRange idx 0 4095; KZRange (2^tl - idx - 1) 0 4095;
       KZRange SP 4096 (2^47); KZRange DT 4096 (2^47); KZRange DST 4096 (2^47);
       KZRange (dcap - j) 6 (2^32); KZRange j 0 (2^32); KZRange dcap 0 (2^32); KZRange (DST + j) 4096 (2^47);
       KZRange bc 0 700; KZWr (DST + j) 2; KZDisj (DST + j) 2 (DT + 4) (4 * 2^tl);
       KZWr (SP + -104) 40; KZDisj (SP + -104) 40 (DT + 4) (4 * 2^tl); KZDisj (SP + -104) 40 (DST + j) 2]
      [(DT + 4, 4 * 2^tl)] [(DT + 4, 4 * 2^tl); (DST + j, 2); (SP + -112, 112)] [(DT + 4, 4 * 2^tl); (DST + j, 2)].
    all: try x5side.
    all: try (lazymatch goal with |- flat _ _ _ /\ _ => x5m2dj end).
    all: lazymatch goal with |- evtF _ _ _ _ => idtac | |- ?g => fail "SIDE" g end.
    kx_post_regs_keep.
    kx_range (EVar 29) R29. kx_range (EVar 31) R31.
    destruct (B6 ltac:(lia)) as (Q1 & Q2 & Q3 & Q4').
    assert (LCBn : Z.of_nat (length cbs) = 4 * 2 ^ tl) by exact LCB.
    assert (LSM : Z.of_nat (length (map (Z_to_bv 8) src)) = n) by (rewrite length_map; reflexivity).
    kx_cells_split HB.
    lazymatch goal with H : rw_cells bsegs mm (SP + -96) [C4 _] |- _ => kx_cell4 H end.
    lazymatch goal with HL : log_flat _ _ |- _ =>
      destruct (kx_u8arr_ex bsegs _ mm _ DST buf OUT HL) as (buf' & OUT' & LB') end.
    pose proof (munch_refl [(DST + j, DST + j + 2); (SP + -96, SP + -96 + 4)] mm) as MUW.
    pose proof (wmono_refl bsegs mm) as WMr.
    kx_munch_wins MUW [(DST + j, 2); (SP + -96, 4)]. kx_munch_wins MU [(DST + j, 2); (SP + -96, 4)].
    kx_post_mem_free.
    lazymatch goal with |- context [mem_denot ?E mm ?l] => remember (mem_denot E mm l) as m1 eqn:EM1 end.
    clear OUT.
    unfold KXGoM.apart in DJ1, DJ2, DJ3.
    transport_after_call bsegs mm m1 MUW WMr.
    assert (XF' : XF m1)
      by (unfold AX2F; split; [exists buf'; split; [exact OUT' | unfold zlen in *; rewrite LB'; exact LBF] |];
          repeat (split; [first [eassumption | eexists; eassumption] |]); first [eassumption | eexists; eassumption]).
    unfold x5_gm, ax2_st in HN. unfold AX2_K8 in HN.
    let p := eval cbv in (AHUF_DX2_1X + 1360) in change (AHUF_DX2_1X + 1360) with p in HN.
    let a := eval cbv in (2^31 - 2^15) in change (2^31 - 2^15) with a in HN.
    let b := eval cbv in (2^61) in change (2^61) with b in HN.
    eapply HN; [exact XF' | unfold ax2_bd; kx_cells_merge | ..].
    all: try lia.
    all: try (apply x5m2_idx; [x5ezu; rewrite Z.mod_small by lia; lia | lia]).
  Time Qed.
  Tactic Notation "x5m5_runFLd" uconstr(STOPS) uconstr(FUEL) uconstr(DIRS) uconstr(KZS) uconstr(RRS) uconstr(WWS) uconstr(UWS) :=
    let S := constr:(STOPS : list Z) in let Fu := constr:(FUEL : nat) in let D := constr:(DIRS : list bool) in
    let K := constr:(KZS : list kz) in let R := constr:(RRS : list (Z * Z)) in let W := constr:(WWS : list (Z * Z)) in
    let U := constr:(UWS : list (Z * Z)) in
    kx_prepFm S Fu K R W U; kx_goFL D.
  Lemma x5_m5 : forall jb, x5_H276 jb -> G3924 -> G1528 jb.
  Proof using All.
    intros jb H276 H3924. unfold x5_gm.
    intros mm j bc idx P cont cw bcw pad x1 x12 x18 x20 x21 x22 HF HB HJ HR HBC HI HP.
    pose proof HF as ((buf & OUT & LBF) & SRCB & CBS & STK & (g & GAP) & FRC & MI & MU & WM).
    pose proof (A2 ax2_sp_bounds) as SB. pose proof (A2 ax2_unp' mm MU) as (UDT' & UDB' & USB').
    unfold HUF_DEC_STACK_A in LOS. pose proof (AI_layout AI L RNG st LB m0 AH) as (_ & _ & TOP & _).
    destruct SBB as (SB1 & SB2).
    pose proof (A2 ax2_blocks) as (B1 & B2 & B3 & B4 & B5 & B6). pose proof (A2 ax2_outb) as OB.
    pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP.
    pose proof ATOP_range as ATR; unfold ATOP_MIN, ATOP_MAX in ATR. unfold AIMG_HI, KLS in *.
    assert (DTL0 : 0 <= DTL) by (unfold DTABLE_BYTES, HufHarness.DT_BYTES; assert (0 < 2^mtl) by lia; lia).
    pose proof (WDB ltac:(lia)) as WDB'. pose proof (WDBS ltac:(lia)) as WDBS'.
    pose proof (A2 ax2_tab mm CBS) as TB.
    pose proof TOK as (TL & TC & TCK); unfold HUF_TABLELOG_MAX in TL.
    assert (P2 : 2 <= 2 ^ tl <= 4096) by (split; [change 2 with (2^1) at 1 | change 4096 with (2^12)]; apply Z.pow_le_mono_r; lia).
    assert (DTLb : DT + 4 + 4 * 2^tl <= DT + DTABLE_BYTES mtl)
      by (unfold DTABLE_BYTES, HufHarness.DT_BYTES; assert (2^tl <= 2^mtl) by (apply Z.pow_le_mono_r; lia); lia).
    unfold ax2_bd in HB. unfold ax2_st. x5lit.
    assert (ND : - DT - 5 = -1 * DT - 5) by lia. rewrite ND.
    let p := eval cbv in (AHUF_DX2_1X + 1528) in change (AHUF_DX2_1X + 1528) with p.
    destruct (Z_lt_ge_dec (bc + bv_unsigned (rdval bsegs mm (Z_to_bv 64 (DT + 4 * idx + 6)) 1 false)) 65) as [HC | HC];
    [ let s1 := eval cbv in (AHUF_DX2_1X + 276) in let s2 := eval cbv in (AHUF_DX2_1X + 3924) in
      x5m5_runFLd [s1; s2] 90%nat (true :: repeat false 64)
        [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange tl 1 12; KZRange (2^tl) 2 4096;
         KZTab (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)];
         KZRange idx 0 4095; KZRange (2^tl - idx - 1) 0 4095;
         KZRange SP 4096 (2^47); KZRange DT 4096 (2^47); KZRange DST 4096 (2^47);
         KZRange (dcap - j) 2 (2^32); KZRange j 0 (2^32); KZRange dcap 0 (2^32); KZRange (DST + j) 4096 (2^47);
         KZRange bc 0 1300; KZWr (DST + j) 2; KZDisj (DST + j) 2 (DT + 4) (4 * 2^tl);
         KZWr (SP + -104) 40; KZDisj (SP + -104) 40 (DT + 4) (4 * 2^tl); KZDisj (SP + -104) 40 (DST + j) 2]
        [(DT + 4, 4 * 2^tl)] [(DT + 4, 4 * 2^tl); (DST + j, 2); (SP + -112, 112)] [(DT + 4, 4 * 2^tl); (DST + j, 2)]
    | let s1 := eval cbv in (AHUF_DX2_1X + 276) in let s2 := eval cbv in (AHUF_DX2_1X + 3924) in
      kx_runFL [s1; s2] 90%nat
        [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange tl 1 12; KZRange (2^tl) 2 4096;
         KZTab (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)];
         KZRange idx 0 4095; KZRange (2^tl - idx - 1) 0 4095;
         KZRange SP 4096 (2^47); KZRange DT 4096 (2^47); KZRange DST 4096 (2^47);
         KZRange (dcap - j) 2 (2^32); KZRange j 0 (2^32); KZRange dcap 0 (2^32); KZRange (DST + j) 4096 (2^47);
         KZRange bc 0 1300; KZWr (DST + j) 2; KZDisj (DST + j) 2 (DT + 4) (4 * 2^tl);
         KZWr (SP + -104) 40; KZDisj (SP + -104) 40 (DT + 4) (4 * 2^tl); KZDisj (SP + -104) 40 (DST + j) 2]
        [(DT + 4, 4 * 2^tl)] [(DT + 4, 4 * 2^tl); (DST + j, 2); (SP + -112, 112)] [(DT + 4, 4 * 2^tl); (DST + j, 2)] ].
    all: try x5side.
    all: try (lazymatch goal with |- flat _ _ _ /\ _ => x5m2dj end).
    all: kx_range (EVar 29) R29; try kx_range (EVar 31) R31.
    all: let H := fresh "RV" in kx_read_eq 29%nat H;
         unfold adenot in H; cbn [a_base a_off] in H; unfold PropExec.v_addi in H;
         lazymatch type of H with context [Z_to_bv 64 (bv_unsigned (edenot ?E ?b) + 6)] =>
           replace (Z_to_bv 64 (bv_unsigned (edenot E b) + 6)) with (ZB (DT + 4 * idx + 6)) in H
             by (f_equal; x5ezu; first [ rewrite ?Z.mod_small by lia; lia | x5clr; Z.div_mod_to_equations; lia ])
         end; rewrite <- H in HC.
    all: try x5br.
    all: kx_post_regs_keep.
    all: destruct (B6 ltac:(lia)) as (Q1 & Q2 & Q3 & Q4').
    all: assert (LCBn : Z.of_nat (length cbs) = 4 * 2 ^ tl) by exact LCB.
    all: assert (LSM : Z.of_nat (length (map (Z_to_bv 8) src)) = n) by (rewrite length_map; reflexivity).
    - kx_cells_split HB.
      lazymatch goal with H : rw_cells bsegs mm (SP + -96) [C4 _] |- _ => kx_cell4 H end.
      lazymatch goal with HL : log_flat _ _ |- _ =>
        destruct (kx_u8arr_ex bsegs _ mm _ DST buf OUT HL) as (buf' & OUT' & LB') end.
      pose proof (munch_refl [(DST + j, DST + j + 2); (SP + -96, SP + -96 + 4)] mm) as MUW.
      pose proof (wmono_refl bsegs mm) as WMr.
      kx_munch_wins MUW [(DST + j, 2); (SP + -96, 4)]. kx_munch_wins MU [(DST + j, 2); (SP + -96, 4)].
      kx_post_mem_free.
      lazymatch goal with |- context [mem_denot ?E mm ?l] => remember (mem_denot E mm l) as m1 eqn:EM1 end.
      clear OUT.
      unfold KXGoM.apart in DJ1, DJ2, DJ3.
      transport_after_call bsegs mm m1 MUW WMr.
      assert (XF' : XF m1)
        by (unfold AX2F; split; [exists buf'; split; [exact OUT' | unfold zlen in *; rewrite LB'; exact LBF] |];
            repeat (split; [first [eassumption | eexists; eassumption] |]); first [eassumption | eexists; eassumption]).
      unfold x5_H276, ax2_st in H276. unfold AX2_K8 in H276.
      let p := eval cbv in (AHUF_DX2_1X + 276) in change (AHUF_DX2_1X + 276) with p in H276.
      let a := eval cbv in (2^31 - 2^15) in change (2^31 - 2^15) with a in H276.
      let b := eval cbv in (2^61) in change (2^61) with b in H276.
      eapply H276; [exact XF' | unfold ax2_bd; kx_cells_merge | ..].
      all: lia.
    - kx_cells_split HB.
      lazymatch goal with H : rw_cells bsegs mm (SP + -96) [C4 _] |- _ => kx_cell4 H end.
      lazymatch goal with H : rw_cells bsegs mm (SP + -88) [C8 _] |- _ => kx_cell H end.
      lazymatch goal with HL : log_flat _ _ |- _ =>
        destruct (kx_u8arr_ex bsegs _ mm _ DST buf OUT HL) as (buf' & OUT' & LB') end.
      pose proof (munch_refl [(DST + j, DST + j + 2); (SP + -96, SP + -96 + 4); (SP + -88, SP + -88 + 8)] mm) as MUW.
      pose proof (wmono_refl bsegs mm) as WMr.
      kx_munch_wins MUW [(DST + j, 2); (SP + -96, 4); (SP + -88, 8)].
      kx_munch_wins MU [(DST + j, 2); (SP + -96, 4); (SP + -88, 8)].
      kx_post_mem_free.
      lazymatch goal with |- context [mem_denot ?E mm ?l] => remember (mem_denot E mm l) as m1 eqn:EM1 end.
      clear OUT.
      unfold KXGoM.apart in DJ1, DJ2, DJ3.
      transport_after_call bsegs mm m1 MUW WMr.
      assert (XF' : XF m1)
        by (unfold AX2F; split; [exists buf'; split; [exact OUT' | unfold zlen in *; rewrite LB'; exact LBF] |];
            repeat (split; [first [eassumption | eexists; eassumption] |]); first [eassumption | eexists; eassumption]).
      unfold ax2_goal_3924, ax2_st in H3924.
      let p := eval cbv in (AHUF_DX2_1X + 3924) in change (AHUF_DX2_1X + 3924) with p in H3924.
      let a := eval cbv in (2^31 - 2^15) in change (2^31 - 2^15) with a in H3924.
      let b := eval cbv in (2^61) in change (2^61) with b in H3924.
      eapply H3924; [exact XF' | unfold ax2_bd; kx_cells_merge | lia | lia | intros; exfalso; lia].
  Time Qed.

  Lemma x5_br_nz : forall E P B,
    bv_unsigned (edenot E B) <= 64 -> 64 < bv_unsigned (edenot E P) ->
    branch_taken BC_NE
      (edenot E (EAlu ALU_XOR (ELit 1) (EAlu ALU_SLTU (EAlu ALU_XOR P (EAluw ALU_SRL B (ELit 3))) (ELit 1))))
      (edenot E (ELit 0)) = true.
  Proof.
    intros E P B HB HP.
    pose proof (bv_unsigned_in_range _ (edenot E B)) as [RB _].
    cbn [edenot branch_taken].
    rewrite bv_eqb_Z, u_xor64, u_sltu64, u_xor64.
    rewrite (u_srlw_small (edenot E B) (Z_to_bv 64 3) 3) by
      (first [reflexivity | lia | change (2 ^ (3 mod 32)) with 8; Z.div_mod_to_equations; lia]).
    change (bv_unsigned (Z_to_bv 64 1)) with 1. change (bv_unsigned (Z_to_bv 64 0)) with 0.
    change (2 ^ (3 mod 32)) with 8.
    assert (HL : 0 < Z.lxor (bv_unsigned (edenot E P)) (bv_unsigned (edenot E B) / 8)).
    { assert (0 <= Z.lxor (bv_unsigned (edenot E P)) (bv_unsigned (edenot E B) / 8)).
      { apply Z.lxor_nonneg; split; intros; Z.div_mod_to_equations; lia. }
      assert (Z.lxor (bv_unsigned (edenot E P)) (bv_unsigned (edenot E B) / 8) <> 0).
      { assert (HB8 : bv_unsigned (edenot E B) / 8 <= 8) by (apply Z.div_le_upper_bound; lia).
        intros H0. pose proof (Z.lxor_eq _ _ H0). lia. }
      lia. }
    destruct (Z.ltb_spec (Z.lxor (bv_unsigned (edenot E P)) (bv_unsigned (edenot E B) / 8)) 1); [lia|].
    reflexivity.
  Qed.

  Lemma x5_rlA : forall j, x5_g764 j -> forall mm bc cont cw pad (x1 x10 x12 x18 x20 x21 x22 : word),
    XF mm -> XBD mm cw bc pad SS -> 1 <= dcap -> 0 <= j <= dcap -> 0 <= bc <= 64 ->
    evtF bsegs RNG POST (XST 276 mm x1 (ZB bc) (ZB (DST + dcap - 9)) (ZB (- DT - 5)) (ZB (DST + j)) x10 (ZB SS) x12
                             PE DL cont x18 x20 x21 x22 (ZB 65) (ZB (64 - tl)) (ZB 1) (ZB AX2_K8)).
  Proof using All.
    intros j HN mm bc cont cw pad x1 x10 x12 x18 x20 x21 x22 HF HB HD1 HJ HBC.
    pose proof HF as ((buf & OUT & LBF) & SRCB & CBS & STK & (g & GAP) & FRC & MI & MU & WM).
    pose proof (A2 ax2_sp_bounds) as SB. pose proof (A2 ax2_unp' mm MU) as (UDT' & UDB' & USB').
    unfold HUF_DEC_STACK_A in LOS. pose proof (AI_layout AI L RNG st LB m0 AH) as (_ & _ & TOP & _).
    destruct SBB as (SB1 & SB2).
    pose proof (A2 ax2_blocks) as (B1 & B2 & B3 & B4 & B5 & B6). pose proof (A2 ax2_outb) as OB.
    pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP.
    pose proof ATOP_range as ATR; unfold ATOP_MIN, ATOP_MAX in ATR. unfold AIMG_HI, KLS in *.
    assert (DTL0 : 0 <= DTL) by (unfold DTABLE_BYTES, HufHarness.DT_BYTES; assert (0 < 2^mtl) by lia; lia).
    assert (LSM : Z.of_nat (length (map (Z_to_bv 8) src)) = n) by (rewrite length_map; reflexivity).
    pose proof TOK as (TL & TC & TCK); unfold HUF_TABLELOG_MAX in TL.
    assert (P2 : 2 <= 2 ^ tl <= 4096) by (split; [change 2 with (2^1) at 1 | change 4096 with (2^12)]; apply Z.pow_le_mono_r; lia).
    assert (DTLb : DT + 4 + 4 * 2^tl <= DT + DTABLE_BYTES mtl)
      by (unfold DTABLE_BYTES, HufHarness.DT_BYTES; assert (2^tl <= 2^mtl) by (apply Z.pow_le_mono_r; lia); lia).
    unfold ax2_bd in HB. unfold ax2_st. x5lit.
    let p := eval cbv in (AHUF_DX2_1X + 276) in change (AHUF_DX2_1X + 276) with p.
    let s1 := eval cbv in (AHUF_DX2_1X + 764) in let s2 := eval cbv in (AHUF_DX2_1X + 5328) in
    kx_runFmd [s1; s2] 120%nat (repeat false 64)
      [KZRange SP 4096 (2^47); KZRange SS 16 (2^47); KZRange n 1 (2^26); KZRange bc 0 64;
       KZRange DST 0 (2^47); KZRange dcap 0 (2^32); KZRange j 0 (2^32); KZRange DT 4096 (2^47);
       KZWord (SP + -80) 8 SS; KZWord (SP + -72) 8 (SS + 8);
       KZWr (SP + -104) 40; KZDisj (SP + -104) 40 SS n; KZDisj (SP + -104) 40 DT DTL; KZDisj (SP + -104) 40 DST dcap]
      [(SS, n)] [(SS, n); (SP + -112, 112)] [(SS, n)].
    all: try x5side.
    kx_post_regs_keep.
    lazymatch goal with |- context [mem_denot ?E ?mm []] => change (mem_denot E mm []) with mm end.
    unfold x5_g764, ax2_st in HN. unfold AX2_K8 in HN.
    let p := eval cbv in (AHUF_DX2_1X + 764) in change (AHUF_DX2_1X + 764) with p in HN.
    let a := eval cbv in (2^31 - 2^15) in change (2^31 - 2^15) with a in HN.
    let b := eval cbv in (2^61) in change (2^61) with b in HN.
    eapply HN; [exact HF | unfold ax2_bd; exact HB | ..].
    all: lia.
  Time Qed.

  Lemma x5_rlF : forall j, x5_g764 j -> forall mm q r P cont cw pad (x1 x10 x12 x18 x20 x21 x22 : word),
    XF mm -> XBD mm cw (8 * q + r) pad P -> 1 <= dcap -> 0 <= j <= dcap -> 0 <= q <= 8 -> 0 <= r <= 7 -> 8 * q + r <= 64 ->
    SS + 8 <= P -> P + 8 <= SS + n ->
    evtF bsegs RNG POST (XST 276 mm x1 (ZB (8 * q + r)) (ZB (DST + dcap - 9)) (ZB (- DT - 5)) (ZB (DST + j)) x10 (ZB P) x12
                             PE DL cont x18 x20 x21 x22 (ZB 65) (ZB (64 - tl)) (ZB 1) (ZB AX2_K8)).
  Proof using All.
    intros j HN mm q r P cont cw pad x1 x10 x12 x18 x20 x21 x22 HF HB HD1 HJ HQ HR HBC HP1 HP2.
    pose proof HF as ((buf & OUT & LBF) & SRCB & CBS & STK & (g & GAP) & FRC & MI & MU & WM).
    pose proof (A2 ax2_sp_bounds) as SB. pose proof (A2 ax2_unp' mm MU) as (UDT' & UDB' & USB').
    unfold HUF_DEC_STACK_A in LOS. pose proof (AI_layout AI L RNG st LB m0 AH) as (_ & _ & TOP & _).
    destruct SBB as (SB1 & SB2).
    pose proof (A2 ax2_blocks) as (B1 & B2 & B3 & B4 & B5 & B6). pose proof (A2 ax2_outb) as OB.
    pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP.
    pose proof ATOP_range as ATR; unfold ATOP_MIN, ATOP_MAX in ATR. unfold AIMG_HI, KLS in *.
    assert (DTL0 : 0 <= DTL) by (unfold DTABLE_BYTES, HufHarness.DT_BYTES; assert (0 < 2^mtl) by lia; lia).
    assert (LSM : Z.of_nat (length (map (Z_to_bv 8) src)) = n) by (rewrite length_map; reflexivity).
    pose proof TOK as (TL & TC & TCK); unfold HUF_TABLELOG_MAX in TL.
    assert (P2 : 2 <= 2 ^ tl <= 4096) by (split; [change 2 with (2^1) at 1 | change 4096 with (2^12)]; apply Z.pow_le_mono_r; lia).
    assert (DTLb : DT + 4 + 4 * 2^tl <= DT + DTABLE_BYTES mtl)
      by (unfold DTABLE_BYTES, HufHarness.DT_BYTES; assert (2^tl <= 2^mtl) by (apply Z.pow_le_mono_r; lia); lia).
    unfold ax2_bd in HB. unfold ax2_st. x5lit.
    let p := eval cbv in (AHUF_DX2_1X + 276) in change (AHUF_DX2_1X + 276) with p.
    let s1 := eval cbv in (AHUF_DX2_1X + 764) in
    kx_runFmd [s1] 120%nat (true :: true :: repeat false 64)
      [KZRange SP 4096 (2^47); KZRange SS 16 (2^47); KZRange n 1 (2^26); KZRange (P - SS) 8 (2^26);
       KZRange (SS + n - P) 8 (2^26); KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64;
       KZRange DST 0 (2^47); KZRange dcap 0 (2^32); KZRange j 0 (2^32); KZRange DT 4096 (2^47);
       KZRange P 24 (2^47); KZWord (SP + -80) 8 SS; KZWord (SP + -72) 8 (SS + 8);
       KZWr (SP + -104) 40; KZDisj (SP + -104) 40 SS n; KZDisj (SP + -104) 40 DT DTL; KZDisj (SP + -104) 40 DST dcap]
      [(P + -8, 16)] [(P + -8, 16); (SP + -112, 112)] [(P + -8, 16)].
    all: try x5side.
    all: try (lazymatch goal with
         | |- branch_taken BC_NE (edenot ?E (EAlu ALU_XOR (ELit 1) (EAlu ALU_SLTU
                (EAlu ALU_XOR ?P (EAluw ALU_SRL ?B (ELit 3))) (ELit 1)))) (edenot ?E (ELit 0)) = true =>
             apply (x5_br_nz E P B); x5ezu; rewrite ?Z.mod_small by lia; lia end).
    kx_post_regs_keep.
    assert (LCBn : Z.of_nat (length cbs) = 4 * 2 ^ tl) by exact LCB.
    kx_cells_split HB.
    kx_cells_post.
    pose proof (munch_refl [(SP + -104, SP + -104 + 12); (SP + -88, SP + -88 + 8)] mm) as MUW.
    pose proof (wmono_refl bsegs mm) as WMr.
    kx_munch_wins MUW [(SP + -104, 12); (SP + -88, 8)]. kx_munch_wins MU [(SP + -104, 12); (SP + -88, 8)].
    kx_post_mem_free.
    lazymatch goal with |- context [mem_denot ?E mm ?l] => remember (mem_denot E mm l) as m1 eqn:EM1 end.
    unfold KXGoM.apart in *.
    transport_after_call bsegs mm m1 MUW WMr.
    assert (XF' : XF m1)
      by (unfold AX2F; split; [exists buf; split; [exact OUT | exact LBF] |];
          repeat (split; [first [eassumption | eexists; eassumption] |]); first [eassumption | eexists; eassumption]).
    unfold x5_g764, ax2_st in HN. unfold AX2_K8 in HN.
    let p := eval cbv in (AHUF_DX2_1X + 764) in change (AHUF_DX2_1X + 764) with p in HN.
    let a := eval cbv in (2^31 - 2^15) in change (2^31 - 2^15) with a in HN.
    let b := eval cbv in (2^61) in change (2^61) with b in HN.
    eapply HN; [exact XF' | unfold ax2_bd; kx_cells_merge | ..].
    all: try lia.
    x5z.
  Time Qed.

  Lemma x5c_srlw_srl : forall E a, 0 <= bv_unsigned (edenot E a) < 2^31 ->
    edenot E (EAlu ALU_SRL a (ELit 3)) = edenot E (EAluw ALU_SRL a (ELit 3)).
  Proof using.
    intros E a H. clear - H. apply bv_eq. rewrite u_srl_lit, (x5_srlw3 E a H). reflexivity.
  Qed.
  Ltac x5cw :=
    repeat match goal with
    | |- context [edenot ?E ?e] =>
        match e with context [EAluw ALU_SRL ?a (ELit 3)] =>
          rewrite <- (esubst_sound E (EAluw ALU_SRL a (ELit 3)) (EAlu ALU_SRL a (ELit 3)) e)
            by (apply x5c_srlw_srl; x5ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
                change (Z.of_N 64) with 64; rewrite Z.mod_small by lia; lia);
          let e' := eval vm_compute in (esubst (EAluw ALU_SRL a (ELit 3)) (EAlu ALU_SRL a (ELit 3)) e) in
          change (esubst (EAluw ALU_SRL a (ELit 3)) (EAlu ALU_SRL a (ELit 3)) e) with e'
        end
    end.
  Ltac x5czl := Z.div_mod_to_equations; lia.
  Ltac x5cdec :=
    repeat match goal with
    | |- context [Z.lxor ?x ?y <? 1] =>
        replace (Z.lxor x y <? 1) with false by
          (symmetry; apply Z.ltb_ge;
           assert (0 <= Z.lxor x y) by (apply (proj2 (Z.lxor_nonneg x y)); split; intro; x5czl);
           assert (Z.lxor x y <> 0) by (rewrite Z.lxor_eq_0_iff; x5czl); lia)
    | |- context [?a =? ?b] =>
        first [ replace (a =? b) with true by (symmetry; apply Z.eqb_eq; x5czl)
              | replace (a =? b) with false by (symmetry; apply Z.eqb_neq; x5czl) ]
    | |- context [?a <? ?b] =>
        first [ replace (a <? b) with true by (symmetry; apply Z.ltb_lt; x5czl)
              | replace (a <? b) with false by (symmetry; apply Z.ltb_ge; x5czl) ]
    end.
  Ltac x5cev :=
    unfold branch_taken; cbn [edenot]; rewrite ?bv_ltu_Z, ?bv_eqb_Z, ?bv_lts_lxor;
    repeat (rewrite ?u_add64, ?u_sub64, ?u_and64, ?u_xor64, ?u_sltu64, ?u_srl64, ?u_sll64, ?u_mul64, ?u_lit64);
    repeat (lazymatch goal with |- context [ev ?E ?j] =>
      lazymatch goal with KA : forall j, _ -> ev E j = _ |- _ => rewrite (KA j) by (vm_compute; lia) end end);
    cbn [nth]; rewrite ?u_lit64; unfold two64;
    repeat match goal with |- context [?a mod 64] => rewrite (Z.mod_small a 64) by lia end;
    repeat match goal with |- context [?a mod 2 ^ ?k] => rewrite (Z.mod_small a (2 ^ k)) by x5czl end;
    repeat match goal with |- context [2 ^ ?k] =>
      let v := eval vm_compute in (2 ^ k) in tryif is_Zlit v then change (2 ^ k) with v else fail end;
    x5cdec; cbn iota; try reflexivity.
  Ltac x5cside H :=
    lazymatch goal with |- evtF _ _ _ _ => idtac | |- _ =>
      try x5cw; first [ x5br | x5dj | x5rd H | x5cev | idtac ] end.
  Ltac x5rlw ofs ql qh bh q r j :=
    let s1 := eval cbv in (AHUF_DX2_1X + 764) in
    let nl := eval vm_compute in (8 + ofs) in
    let bl := eval vm_compute in (8 * ql) in
    kx_runFmd [s1] 120%nat (true :: true :: repeat false 64)
      [KZRange SP 4096 (2^47); KZRange SS 16 (2^47); KZRange n nl (2^26);
       KZRange (n - ofs) 8 (2^26); KZRange q ql qh; KZRange r 0 7; KZRange (8 * q + r) bl bh;
       KZWord (SP + -88) 8 (SS + ofs); KZWord (SP + -80) 8 SS; KZWord (SP + -72) 8 (SS + 8);
       KZWr (SP + -104) 40; KZDisj (SP + -104) 40 SS n; KZDisj (SP + -104) 40 DT DTL; KZDisj (SP + -104) 40 DST dcap;
       KZRange DST 0 (2^47); KZRange dcap 1 (2^32); KZRange j 0 (2^32); KZRange DT 4096 (2^47)]
      [(SS, n)] [(SS, n); (SP + -112, 112)] [(SS, n)].
  Ltac x5rlq HN OUT LBF MU buf :=
    kx_post_regs_keep;
    lazymatch goal with H : rw_cells bsegs _ (SP + -104) (_ :: _ :: _) |- _ => kx_cells_split H end;
    kx_cells_post;
    let MUW := fresh "MUW" in let WMr := fresh "WMr" in
    lazymatch goal with |- context [mem_denot _ ?mm _] =>
      pose proof (munch_refl [(SP + -104, SP + -104 + 12); (SP + -88, SP + -88 + 8)] mm) as MUW;
      pose proof (wmono_refl bsegs mm) as WMr end;
    kx_munch_wins MUW [(SP + -104, 12); (SP + -88, 8)]; kx_munch_wins MU [(SP + -104, 12); (SP + -88, 8)];
    kx_post_mem_free;
    let m1 := fresh "m1" in let EM1 := fresh "EM1" in
    lazymatch goal with |- context [mem_denot ?E ?mm ?l] => remember (mem_denot E mm l) as m1 eqn:EM1 end;
    unfold KXGoM.apart in *;
    lazymatch type of MUW with munch _ ?mm _ => transport_after_call bsegs mm m1 MUW WMr end;
    let XF' := fresh "XF'" in
    assert (XF' : XF m1)
      by (unfold AX2F; split; [exists buf; split; [exact OUT | exact LBF] |];
          repeat (split; [first [eassumption | eexists; eassumption] |]); first [eassumption | eexists; eassumption]);
    unfold x5_g764, ax2_st in HN; unfold AX2_K8 in HN;
    let p := eval cbv in (AHUF_DX2_1X + 764) in change (AHUF_DX2_1X + 764) with p in HN;
    let a := eval cbv in (2^31 - 2^15) in change (2^31 - 2^15) with a in HN;
    let b := eval cbv in (2^61) in change (2^61) with b in HN;
    eapply HN; [exact XF' | unfold ax2_bd; kx_cells_merge | ..];
    try lia; try x5z.
  Ltac x5rlc o ql qh bh q r j HN OUT LBF MU buf SRCB :=
    x5rlw o ql qh bh q r j;
    try x5side;
    try (lazymatch goal with
         | |- branch_taken BC_NE (edenot ?E (EAlu ALU_XOR (ELit 1) (EAlu ALU_SLTU
                (EAlu ALU_XOR ?P (EAluw ALU_SRL ?B (ELit 3))) (ELit 1)))) (edenot ?E (ELit 0)) = true =>
             apply (x5_br_nz E P B); x5ezu; rewrite ?Z.mod_small by lia; lia end);
    x5cside SRCB;
    lazymatch goal with |- evtF _ _ _ _ => x5rlq HN OUT LBF MU buf end.
  Lemma x5_rlC1 : forall j, x5_g764 j -> forall mm q r off cont cw pad (x1 x10 x12 x18 x20 x21 x22 : word),
    XF mm -> XBD mm cw (8 * q + r) pad (SS + off) -> 1 <= dcap -> 0 <= j <= dcap -> 0 <= q <= 8 -> 0 <= r <= 7 ->
    8 * q + r <= 64 -> 1 <= off <= 7 -> q <= off -> off + 8 <= n ->
    evtF bsegs RNG POST (XST 276 mm x1 (ZB (8 * q + r)) (ZB (DST + dcap - 9)) (ZB (- DT - 5)) (ZB (DST + j)) x10 (ZB (SS + off)) x12
                             PE DL cont x18 x20 x21 x22 (ZB 65) (ZB (64 - tl)) (ZB 1) (ZB AX2_K8)).
  Proof using All.
    intros j HN mm q r off cont cw pad x1 x10 x12 x18 x20 x21 x22 HF HB HD1 HJ HQ HR HBC HO HQO HP2.
    pose proof HF as ((buf & OUT & LBF) & SRCB & CBS & STK & (g & GAP) & FRC & MI & MU & WM).
    pose proof (A2 ax2_sp_bounds) as SB. pose proof (A2 ax2_unp' mm MU) as (UDT' & UDB' & USB').
    unfold HUF_DEC_STACK_A in LOS. pose proof (AI_layout AI L RNG st LB m0 AH) as (_ & _ & TOP & _).
    destruct SBB as (SB1 & SB2).
    pose proof (A2 ax2_blocks) as (B1 & B2 & B3 & B4 & B5 & B6). pose proof (A2 ax2_outb) as OB.
    pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP.
    pose proof ATOP_range as ATR; unfold ATOP_MIN, ATOP_MAX in ATR. unfold AIMG_HI, KLS in *.
    assert (DTL0 : 0 <= DTL) by (unfold DTABLE_BYTES, HufHarness.DT_BYTES; assert (0 < 2^mtl) by lia; lia).
    assert (LSM : Z.of_nat (length (map (Z_to_bv 8) src)) = n) by (rewrite length_map; reflexivity).
    pose proof TOK as (TL & TC & TCK); unfold HUF_TABLELOG_MAX in TL.
    assert (P2 : 2 <= 2 ^ tl <= 4096) by (split; [change 2 with (2^1) at 1 | change 4096 with (2^12)]; apply Z.pow_le_mono_r; lia).
    assert (DTLb : DT + 4 + 4 * 2^tl <= DT + DTABLE_BYTES mtl)
      by (unfold DTABLE_BYTES, HufHarness.DT_BYTES; assert (2^tl <= 2^mtl) by (apply Z.pow_le_mono_r; lia); lia).
    unfold ax2_bd in HB. unfold ax2_st. x5lit.
    assert (ND : - DT - 5 = -1 * DT - 5) by lia. rewrite ND.
    let p := eval cbv in (AHUF_DX2_1X + 276) in change (AHUF_DX2_1X + 276) with p.
    assert (HO' : off = 1 \/ off = 2 \/ off = 3 \/ off = 4 \/ off = 5 \/ off = 6 \/ off = 7) by lia.
    destruct HO' as [HO'|[HO'|[HO'|[HO'|[HO'|[HO'|HO']]]]]]; subst off.
    - x5rlc 1 0 1 15 q r j HN OUT LBF MU buf SRCB.
    - x5rlc 2 0 2 23 q r j HN OUT LBF MU buf SRCB.
    - x5rlc 3 0 3 31 q r j HN OUT LBF MU buf SRCB.
    - x5rlc 4 0 4 39 q r j HN OUT LBF MU buf SRCB.
    - x5rlc 5 0 5 47 q r j HN OUT LBF MU buf SRCB.
    - x5rlc 6 0 6 55 q r j HN OUT LBF MU buf SRCB.
    - x5rlc 7 0 7 63 q r j HN OUT LBF MU buf SRCB.
  Time Qed.

  Lemma x5_rlC2 : forall j, x5_g764 j -> forall mm q r off cont cw pad (x1 x10 x12 x18 x20 x21 x22 : word),
    XF mm -> XBD mm cw (8 * q + r) pad (SS + off) -> 1 <= dcap -> 0 <= j <= dcap -> 0 <= q <= 8 -> 0 <= r <= 7 ->
    8 * q + r <= 64 -> 1 <= off <= 7 -> off < q -> off + 8 <= n ->
    evtF bsegs RNG POST (XST 276 mm x1 (ZB (8 * q + r)) (ZB (DST + dcap - 9)) (ZB (- DT - 5)) (ZB (DST + j)) x10 (ZB (SS + off)) x12
                             PE DL cont x18 x20 x21 x22 (ZB 65) (ZB (64 - tl)) (ZB 1) (ZB AX2_K8)).
  Proof using All.
    intros j HN mm q r off cont cw pad x1 x10 x12 x18 x20 x21 x22 HF HB HD1 HJ HQ HR HBC HO HQO HP2.
    pose proof HF as ((buf & OUT & LBF) & SRCB & CBS & STK & (g & GAP) & FRC & MI & MU & WM).
    pose proof (A2 ax2_sp_bounds) as SB. pose proof (A2 ax2_unp' mm MU) as (UDT' & UDB' & USB').
    unfold HUF_DEC_STACK_A in LOS. pose proof (AI_layout AI L RNG st LB m0 AH) as (_ & _ & TOP & _).
    destruct SBB as (SB1 & SB2).
    pose proof (A2 ax2_blocks) as (B1 & B2 & B3 & B4 & B5 & B6). pose proof (A2 ax2_outb) as OB.
    pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP.
    pose proof ATOP_range as ATR; unfold ATOP_MIN, ATOP_MAX in ATR. unfold AIMG_HI, KLS in *.
    assert (DTL0 : 0 <= DTL) by (unfold DTABLE_BYTES, HufHarness.DT_BYTES; assert (0 < 2^mtl) by lia; lia).
    assert (LSM : Z.of_nat (length (map (Z_to_bv 8) src)) = n) by (rewrite length_map; reflexivity).
    pose proof TOK as (TL & TC & TCK); unfold HUF_TABLELOG_MAX in TL.
    assert (P2 : 2 <= 2 ^ tl <= 4096) by (split; [change 2 with (2^1) at 1 | change 4096 with (2^12)]; apply Z.pow_le_mono_r; lia).
    assert (DTLb : DT + 4 + 4 * 2^tl <= DT + DTABLE_BYTES mtl)
      by (unfold DTABLE_BYTES, HufHarness.DT_BYTES; assert (2^tl <= 2^mtl) by (apply Z.pow_le_mono_r; lia); lia).
    unfold ax2_bd in HB. unfold ax2_st. x5lit.
    assert (ND : - DT - 5 = -1 * DT - 5) by lia. rewrite ND.
    let p := eval cbv in (AHUF_DX2_1X + 276) in change (AHUF_DX2_1X + 276) with p.
    assert (HO' : off = 1 \/ off = 2 \/ off = 3 \/ off = 4 \/ off = 5 \/ off = 6 \/ off = 7) by lia.
    destruct HO' as [HO'|[HO'|[HO'|[HO'|[HO'|[HO'|HO']]]]]]; subst off.
    - x5rlc 1 2 8 64 q r j HN OUT LBF MU buf SRCB.
    - x5rlc 2 3 8 64 q r j HN OUT LBF MU buf SRCB.
    - x5rlc 3 4 8 64 q r j HN OUT LBF MU buf SRCB.
    - x5rlc 4 5 8 64 q r j HN OUT LBF MU buf SRCB.
    - x5rlc 5 6 8 64 q r j HN OUT LBF MU buf SRCB.
    - x5rlc 6 7 8 64 q r j HN OUT LBF MU buf SRCB.
    - x5rlc 7 8 8 64 q r j HN OUT LBF MU buf SRCB.
  Time Qed.

  Lemma x5_rl : forall j, x5_g764 j -> x5_A276 j.
  Proof using All.
    intros j HN. unfold x5_A276.
    intros mm bc P cont cw pad x1 x10 x12 x18 x20 x21 x22 HF HB HD HJ HBC HP.
    destruct HP as [-> | (HP1 & HP2)].
    - exact (x5_rlA j HN mm bc cont cw pad x1 x10 x12 x18 x20 x21 x22 HF HB HD HJ HBC).
    - assert (QR : exists q r, bc = 8 * q + r /\ 0 <= q <= 8 /\ 0 <= r <= 7)
        by (exists (bc / 8), (bc mod 8); Z.div_mod_to_equations; lia).
      destruct QR as (q & r & -> & HQ & HR).
      destruct (Z_le_gt_dec (SS + 8) P) as [HP3 | HP3].
      + exact (x5_rlF j HN mm q r P cont cw pad x1 x10 x12 x18 x20 x21 x22 HF HB HD HJ HQ HR ltac:(lia) HP3 HP2).
      + replace P with (SS + (P - SS)) in * by lia.
        destruct (Z_le_gt_dec q (P - SS)) as [HQO | HQO].
        * exact (x5_rlC1 j HN mm q r (P - SS) cont cw pad x1 x10 x12 x18 x20 x21 x22 HF HB HD HJ HQ HR ltac:(lia)
                   ltac:(lia) HQO ltac:(lia)).
        * exact (x5_rlC2 j HN mm q r (P - SS) cont cw pad x1 x10 x12 x18 x20 x21 x22 HF HB HD HJ HQ HR ltac:(lia)
                   ltac:(lia) ltac:(lia) ltac:(lia)).
  Time Qed.

  Lemma ax2_goal_276_ok : G3924 -> G276.
  Proof using All. exact (x5_loop x5_rl x5_b1 x5_m2 x5_m3 x5_m4 x5_m5). Qed.
End AX2D.
End CANSEC1.
