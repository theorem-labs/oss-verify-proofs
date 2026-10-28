(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image Frame.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require SysStep.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells ABase.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_x2t_hdefs.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Mem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import HufPure_HufX2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require MState.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_z4f_defs AF_huf_z4f_fij.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".

Section CANSEC1. Context {rc : runConstT}.
Section X42E.
  Variables (RNG : footprint).
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (SPV DST dcap SRC n DT DTB tl lo : Z) (src dtb : list byte).
  Hypothesis CTX : x42e_ctx SPV DST dcap SRC n DT DTB tl lo src dtb.
  Hypothesis X2OK : huf_x2_ok dtb tl.
  Hypothesis NBOK : huf_nb_ok true dtb tl.
  Hypothesis ACTX : x42e_actx RNG m0 SPV DST dcap SRC n DT DTB lo.
  Variable POST : machine_state -> Prop.
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -528)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Notation FRS mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 :=
    (rw_cells bsegs mm (SPV + -528) [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12;
                                     C8 w13; C8 w14; C8 w15; C8 w16; C8 w17]).
  Notation ARGS mm ip0 ip1 ip2 ip3 op0 op1 op2 op3 b0 b1 b2 b3 adt ilow oend ie0 ie1 ie2 ie3 :=
    (rw_cells bsegs mm (SPV + -384) [C8 ip0; C8 ip1; C8 ip2; C8 ip3; C8 op0; C8 op1; C8 op2; C8 op3; C8 b0; C8 b1; C8 b2; C8 b3;
                                     C8 adt; C8 ilow; C8 oend; C8 ie0; C8 ie1; C8 ie2; C8 ie3]).
  Notation LOC mm e0 e1 e2 e3 p0 p1 p2 p3 i0 i1 i2 i3 c0 c1 c2 c3 :=
    (rw_cells bsegs mm (SPV + -232) [C8 e0; C8 e1; C8 e2; C8 e3; C8 p0; C8 p1; C8 p2; C8 p3; C8 i0; C8 i1; C8 i2; C8 i3;
                                     C8 c0; C8 c1; C8 c2; C8 c3]).
  Notation FRQ mm := (rw_cells bsegs mm (SPV + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  Notation W0 := [(DST, DST + dcap); (SPV - 3136, SPV)].
  Notation WDF := [(DST, DST + dcap); (SPV - 528, SPV - 104)].
  Notation WD := [(DST, DST + dcap)].
  Notation SB := (Z_to_bv 64 0x7fff8000).
  Hypothesis TL11 : tl = 11.
  Notation WDL := [(DST, DST + dcap); (SPV - 232, SPV - 104)].
  Notation x42e_fi := (AF_huf_z4f_fij.x42e_fi RNG gp tp F fc m0 SPV DST dcap SRC n DT DTB tl lo src dtb CTX X2OK NBOK ACTX POST TL11).

  Definition X42PF (mm : amem) : Prop := FRQ mm /\ stk bsegs mm lo (SPV + -528).
  Lemma x42pf_transport : forall mm mm' W, X42PF mm -> munch W mm mm' -> wmono bsegs mm mm' ->
    disjoint_from W (SPV + -104) 104 -> disjoint_from W lo (SPV + -528 - lo) -> X42PF mm'.
  Proof.
    intros mm mm' W (SV & STK) MU WM D1 D2. split.
    - eapply (rw_cells_transport bsegs _ mm mm' _ _ SV MU WM). exact D1.
    - eapply (stk_transport_disjoint bsegs _ mm mm' _ _ STK MU WM). exact D2.
  Qed.

  Definition x42e_f2_stmt : Prop := forall mm l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 (ipa0 ipa1 ipa2 ipa3 opa0 opa1 opa2 opa3 ba0 ba1 ba2 ba3 : word)
      (e0 e1 e2 e3 c0 c1 c2 c3 : word)
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x27 x28 x29 x30 x31 : word)
      (w0 w1 w2 w9 w10 w11 w12 w13 w14 w15 : word),
    X42PF mm -> munch W0 m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm -> stk bsegs mm DST (DST + dcap) -> bytes_at bsegs mm DT dtb ->
    (FRS mm w0 w1 w2 (Z_to_bv 64 (SRC)) (Z_to_bv 64 (n)) (Z_to_bv 64 (DT)) (Z_to_bv 64 (DST)) (Z_to_bv 64 (dcap)) (Z_to_bv 64 (DST + dcap)) w9 w10 w11 w12 w13 w14 w15 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (66420))) ->
    (ARGS mm ipa0 ipa1 ipa2 ipa3 opa0 opa1 opa2 opa3 ba0 ba1 ba2 ba3 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (SRC + 6)) (Z_to_bv 64 (SRC + 6 + l1)) (Z_to_bv 64 (SRC + 6 + l1 + l2)) (Z_to_bv 64 (SRC + 6 + l1 + l2 + l3))) ->
    (LOC mm e0 e1 e2 e3 (Z_to_bv 64 (DST + o0)) (Z_to_bv 64 (DST + o1)) (Z_to_bv 64 (DST + o2)) (Z_to_bv 64 (DST + o3)) (Z_to_bv 64 (SRC + i0)) (Z_to_bv 64 (SRC + i1)) (Z_to_bv 64 (SRC + i2)) (Z_to_bv 64 (SRC + i3)) c0 c1 c2 c3) ->
    bytes_at bsegs mm SRC src ->
    DST + 3 * ((dcap + 3) / 4) < DST + dcap -> 8 <= l1 -> 8 <= l2 -> 8 <= l3 -> 6 + l1 + l2 + l3 + 8 <= n ->
    0 <= i0 -> i0 + 8 <= n -> 0 <= o0 <= dcap -> 1 <= bv_unsigned c0 -> 0 <= i1 -> i1 + 8 <= n -> 0 <= o1 <= dcap -> 1 <= bv_unsigned c1 -> 0 <= i2 -> i2 + 8 <= n -> 0 <= o2 <= dcap -> 1 <= bv_unsigned c2 -> 0 <= i3 -> i3 + 8 <= n -> 0 <= o3 <= dcap -> 1 <= bv_unsigned c3 ->
    evtF bsegs RNG POST (ST 0x86ae8 mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 SB x24 x25 (Z_to_bv 64 (134483)) x27 x28 x29 x30 x31).
  Hypothesis MC : forall (A S n SPz : Z) RNG ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (lo : Z) (src junk : list byte) (RLO1 RHI1 RLO2 RHI2 : Z),
    mem_inv bsegs m -> 0 <= SPz < 2^64 ->
    stk bsegs m lo SPz -> lo <= SPz - 2224 -> KHIGH <= lo ->
    rt_got m -> rt_got_ric m -> rt_shbase m -> rt_inited m -> rt_layout m -> rt_real_mem m ->
    bytes_at bsegs m S src -> length src = Z.to_nat n ->
    rw_cells bsegs m A [CB (Z.to_nat n) junk] ->
    (S + n <= A \/ A + n <= S) ->
    (S + n <= SPz - 2224 \/ SPz <= S) ->
    (A + n <= lo \/ SPz <= A) ->
    app_blk S (S + n) -> app_blk A (A + n) ->
    unpoisoned m S (S + n) -> unpoisoned m A (A + n) ->
    0 <= n <= 2^40 ->
    (RLO1 <= S /\ S + n <= RHI1 /\ RLO1 mod 64 = 0 /\ RHI1 mod 64 = 0 /\ 0 <= RLO1 /\ RHI1 <= KEND) ->
    (RLO2 <= A /\ A + n <= RHI2 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0 /\ 0 <= RLO2 /\ RHI2 <= KEND) ->
    wr_at bsegs m (shad RLO1) (shad RHI1 - shad RLO1) -> wr_at bsegs m (shad RLO2) (shad RHI2 - shad RLO2) ->
    rng_aimg RNG -> rng RNG lo (SPz - lo) -> rng RNG S n -> rng RNG A n ->
    rng RNG (shad RLO1) (shad RHI1 - shad RLO1) -> rng RNG (shad RLO2) (shad RHI2 - shad RLO2) ->
    a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 n ->
    evtF bsegs RNG (fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m', ms' = MS (mkR ra (Z_to_bv 64 SPz) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom bsegs) /\ munch [(SPz - 2224, SPz); (A, A + n)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo SPz /\ rw_cells bsegs m' A [CB (Z.to_nat n) src] /\ bytes_at bsegs m' S src)
      (MS (mkR ra (Z_to_bv 64 SPz) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 0x510d8) fc None m (seg_rom bsegs)).
  Hypothesis AZS : exists RLO RHI,
    (unpoisoned m0 lo SPV /\ (RLO <= lo /\ SPV <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND) /\
     wr_at bsegs m0 (shad RLO) (shad RHI - shad RLO) /\ app_blk lo SPV) /\
    rng RNG (shad RLO) (shad RHI - shad RLO).
  Definition x42e_f3_stmt : Prop := forall mm l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3
      (e0 e1 e2 e3 c0 c1 c2 c3 : word)
      (x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x27 x28 x29 x30 x31 : word)
      (w0 w1 w2 w9 w10 w11 w12 w13 w14 w15 : word),
    X42PF mm -> munch W0 m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm -> stk bsegs mm DST (DST + dcap) -> bytes_at bsegs mm DT dtb ->
    (FRS mm w0 w1 w2 (Z_to_bv 64 (SRC)) (Z_to_bv 64 (n)) (Z_to_bv 64 (DT)) (Z_to_bv 64 (DST)) (Z_to_bv 64 (dcap)) (Z_to_bv 64 (DST + dcap)) w9 w10 w11 w12 w13 w14 w15 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (66420))) ->
    (ARGS mm (Z_to_bv 64 (SRC + i0)) (Z_to_bv 64 (SRC + i1)) (Z_to_bv 64 (SRC + i2)) (Z_to_bv 64 (SRC + i3)) (Z_to_bv 64 (DST + o0)) (Z_to_bv 64 (DST + o1)) (Z_to_bv 64 (DST + o2)) (Z_to_bv 64 (DST + o3)) c0 c1 c2 c3 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (SRC + 6)) (Z_to_bv 64 (SRC + 6 + l1)) (Z_to_bv 64 (SRC + 6 + l1 + l2)) (Z_to_bv 64 (SRC + 6 + l1 + l2 + l3))) ->
    (LOC mm e0 e1 e2 e3 (Z_to_bv 64 (DST + o0)) (Z_to_bv 64 (DST + o1)) (Z_to_bv 64 (DST + o2)) (Z_to_bv 64 (DST + o3)) (Z_to_bv 64 (SRC + i0)) (Z_to_bv 64 (SRC + i1)) (Z_to_bv 64 (SRC + i2)) (Z_to_bv 64 (SRC + i3)) c0 c1 c2 c3) ->
    bytes_at bsegs mm SRC src ->
    DST + 3 * ((dcap + 3) / 4) < DST + dcap -> 8 <= l1 -> 8 <= l2 -> 8 <= l3 -> 6 + l1 + l2 + l3 + 8 <= n ->
    0 <= i0 -> i0 + 8 <= n -> 0 <= o0 <= dcap -> 1 <= bv_unsigned c0 -> 0 <= i1 -> i1 + 8 <= n -> 0 <= o1 <= dcap -> 1 <= bv_unsigned c1 -> 0 <= i2 -> i2 + 8 <= n -> 0 <= o2 <= dcap -> 1 <= bv_unsigned c2 -> 0 <= i3 -> i3 + 8 <= n -> 0 <= o3 <= dcap -> 1 <= bv_unsigned c3 ->
    evtF bsegs RNG POST (ST 0x86B18 mm (Z_to_bv 64 0x86B18) x5 x6 x7 x8 x9 (Z_to_bv 64 (SPV + -352)) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 SB x24 x25 (Z_to_bv 64 (134483)) x27 x28 x29 x30 x31).
  Hypothesis F3 : x42e_f3_stmt.
  Lemma F2 : x42e_f2_stmt.
  Proof using CTX X2OK NBOK ACTX TL11 MC AZS F3.
    pose proof CTX as CTX'. x42e_ctx_open CTX'. pose proof ACTX as ACTX'. x42e_actx_open ACTX'.
    unfold x42e_f2_stmt.
    intros mm l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 ipa0 ipa1 ipa2 ipa3 opa0 opa1 opa2 opa3 ba0 ba1 ba2 ba3 e0 e1 e2 e3 c0 c1 c2 c3
      x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x27 x28 x29 x30 x31
      w0 w1 w2 w9 w10 w11 w12 w13 w14 w15
      PV MU0 WM0 MI OUT DTBH FR AR LC SRCB H3Q HL1 HL2 HL3 HLN HI0 HN0 HO0 HB0 HI1 HN1 HO1 HB1 HI2 HN2 HO2 HB2 HI3 HN3 HO3 HB3.
    destruct PV as (SV & STK).
    destruct AZS as (RLO & RHI & (U0 & (HL0 & HH0 & HLm & HHm & HLp & HHk) & WR0 & APB) & RSH).
    assert (DP : 0 < dcap) by lia.
    pose proof (DHI DP) as DHI'. unfold ABase.AIMG_HI in DHI'.
    assert (UST : forall m, munch W0 m0 m -> unpoisoned m lo SPV).
    { intros m MU. eapply unpoisoned_munch; [exact U0 | exact MU |].
      cbn [disjoint_from]; rewrite !shad_div; unfold ASHOFF; repeat split; Z.div_mod_to_equations; lia. }
    assert (WST : forall m, wmono bsegs m0 m -> wr_at bsegs m (shad RLO) (shad RHI - shad RLO)).
    { intros m WM. eapply wr_at_transport; [exact WR0 | exact WM]. }
    assert (RC : forall m A (a b c d : word) bs, rw_cells bsegs m A [CB (Z.to_nat 32) bs] ->
              bs = cells_bytes [C8 a; C8 b; C8 c; C8 d] -> rw_cells bsegs m A [C8 a; C8 b; C8 c; C8 d]).
    { clear. intros m A a b c d bs [[_ HB] HW] ->. split; [split; [cbn [cells_wf cell_wf]; repeat split |] | exact HW].
      cbn [cells_bytes cbytes] in HB |- *. rewrite ?app_nil_r in HB |- *. exact HB. }
    unfold artcells in ART. decompose [and] ART. clear ART.
    transport_after_call bsegs m0 mm MU0 WM0.
    KXCell.kx_cells_split AR. KXCell.kx_cells_split LC.
    
    zstep. zstep. zstep. zstep. try kx_mkR_fold.
    assert (SB1 : bytes_at bsegs mm (SPV + -136) (cells_bytes [C8 c0; C8 c1; C8 c2; C8 c3]))
      by (apply SysStep.rw_cells_bytes_at; KXCell.kx_cells_merge).
    assert (A1 : rw_cells bsegs mm (SPV + -320) [C8 ba0; C8 ba1; C8 ba2; C8 ba3]) by KXCell.kx_cells_merge.
    destruct (rw_cells_forget _ _ _ _ A1) as [jb1 A1']. clear A1.
    eapply evtF_cut;
      [ eapply MC with (A := SPV + -320) (S := SPV + -136) (n := 32) (SPz := SPV + -528) (lo := lo)
          (src := cells_bytes [C8 c0; C8 c1; C8 c2; C8 c3]) (junk := jb1)
          (RLO1 := RLO) (RHI1 := RHI) (RLO2 := RLO) (RHI2 := RHI)
      | post_call bsegs mm ].
    all: lazymatch goal with
      | |- evtF _ _ _ _ => idtac
      | |- length _ = _ => cbn [cells_bytes cbytes app]; rewrite !length_app, !length_le8; reflexivity
      | |- rw_cells _ _ _ [CB _ _] => exact A1'
      | |- unpoisoned _ _ _ => eapply unpoisoned_sub; [apply UST; assumption | lia | lia]
      | |- wr_at _ _ _ _ => apply WST; assumption
      | |- app_blk _ _ => eapply app_blk_sub; [exact APB | lia | lia | lia]
      | |- rng_aimg _ => exact RI
      | |- rng _ (shad _) _ => exact RSH
      | |- rng _ _ _ => eapply rng_sub; [exact RSTK | lia | lia]
      | |- KHIGH <= _ => unfold KHIGH; lia
      | |- @eq word _ _ => first [reflexivity | f_equal; lia]
      | |- _ => first [assumption | lia | (repeat split; first [assumption | lia])]
      end.
    try clear SB1; try clear A1'.
    lazymatch goal with H : rw_cells bsegs ?m (SPV + -320) [CB _ _] |- _ =>
      pose proof (RC _ _ _ _ _ _ _ H eq_refl) as ARb; clear H end.
    KXCell.kx_cells_split ARb.
    
    zstep. zstep. zstep. zstep. try kx_mkR_fold.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m _) =>
      assert (SB2 : bytes_at bsegs m (SPV + -168) (cells_bytes [C8 (Z_to_bv 64 (SRC + i0)); C8 (Z_to_bv 64 (SRC + i1)); C8 (Z_to_bv 64 (SRC + i2)); C8 (Z_to_bv 64 (SRC + i3))]))
        by (apply SysStep.rw_cells_bytes_at; KXCell.kx_cells_merge);
      assert (A2 : rw_cells bsegs m (SPV + -384) [C8 ipa0; C8 ipa1; C8 ipa2; C8 ipa3]) by KXCell.kx_cells_merge;
      destruct (rw_cells_forget _ _ _ _ A2) as [jb2 A2']; clear A2;
      eapply evtF_cut;
        [ eapply MC with (A := SPV + -384) (S := SPV + -168) (n := 32) (SPz := SPV + -528) (lo := lo)
            (src := cells_bytes [C8 (Z_to_bv 64 (SRC + i0)); C8 (Z_to_bv 64 (SRC + i1)); C8 (Z_to_bv 64 (SRC + i2)); C8 (Z_to_bv 64 (SRC + i3))])
            (junk := jb2) (RLO1 := RLO) (RHI1 := RHI) (RLO2 := RLO) (RHI2 := RHI)
        | post_call bsegs m ]
    end.
    all: lazymatch goal with
      | |- evtF _ _ _ _ => idtac
      | |- length _ = _ => cbn [cells_bytes cbytes app]; rewrite !length_app, !length_le8; reflexivity
      | |- rw_cells _ _ _ [CB _ _] => exact A2'
      | |- unpoisoned _ _ _ => eapply unpoisoned_sub; [apply UST; assumption | lia | lia]
      | |- wr_at _ _ _ _ => apply WST; assumption
      | |- app_blk _ _ => eapply app_blk_sub; [exact APB | lia | lia | lia]
      | |- rng_aimg _ => exact RI
      | |- rng _ (shad _) _ => exact RSH
      | |- rng _ _ _ => eapply rng_sub; [exact RSTK | lia | lia]
      | |- KHIGH <= _ => unfold KHIGH; lia
      | |- @eq word _ _ => first [reflexivity | f_equal; lia]
      | |- _ => first [assumption | lia | (repeat split; first [assumption | lia])]
      end.
    try clear SB2; try clear A2'.
    lazymatch goal with H : rw_cells bsegs ?m (SPV + -384) [CB _ _] |- _ =>
      pose proof (RC _ _ _ _ _ _ _ H eq_refl) as ARi; clear H end.
    KXCell.kx_cells_split ARi.
    
    zstep. zstep. zstep. zstep. try kx_mkR_fold.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m _) =>
      assert (SB3 : bytes_at bsegs m (SPV + -200) (cells_bytes [C8 (Z_to_bv 64 (DST + o0)); C8 (Z_to_bv 64 (DST + o1)); C8 (Z_to_bv 64 (DST + o2)); C8 (Z_to_bv 64 (DST + o3))]))
        by (apply SysStep.rw_cells_bytes_at; KXCell.kx_cells_merge);
      assert (A3 : rw_cells bsegs m (SPV + -352) [C8 opa0; C8 opa1; C8 opa2; C8 opa3]) by KXCell.kx_cells_merge;
      destruct (rw_cells_forget _ _ _ _ A3) as [jb3 A3']; clear A3;
      eapply evtF_cut;
        [ eapply MC with (A := SPV + -352) (S := SPV + -200) (n := 32) (SPz := SPV + -528) (lo := lo)
            (src := cells_bytes [C8 (Z_to_bv 64 (DST + o0)); C8 (Z_to_bv 64 (DST + o1)); C8 (Z_to_bv 64 (DST + o2)); C8 (Z_to_bv 64 (DST + o3))])
            (junk := jb3) (RLO1 := RLO) (RHI1 := RHI) (RLO2 := RLO) (RHI2 := RHI)
        | post_call bsegs m ]
    end.
    all: lazymatch goal with
      | |- evtF _ _ _ _ => idtac
      | |- length _ = _ => cbn [cells_bytes cbytes app]; rewrite !length_app, !length_le8; reflexivity
      | |- rw_cells _ _ _ [CB _ _] => exact A3'
      | |- unpoisoned _ _ _ => eapply unpoisoned_sub; [apply UST; assumption | lia | lia]
      | |- wr_at _ _ _ _ => apply WST; assumption
      | |- app_blk _ _ => eapply app_blk_sub; [exact APB | lia | lia | lia]
      | |- rng_aimg _ => exact RI
      | |- rng _ (shad _) _ => exact RSH
      | |- rng _ _ _ => eapply rng_sub; [exact RSTK | lia | lia]
      | |- KHIGH <= _ => unfold KHIGH; lia
      | |- @eq word _ _ => first [reflexivity | f_equal; lia]
      | |- _ => first [assumption | lia | (repeat split; first [assumption | lia])]
      end.
    try clear SB3; try clear A3'.
    lazymatch goal with H : rw_cells bsegs ?m (SPV + -352) [CB _ _] |- _ =>
      pose proof (RC _ _ _ _ _ _ _ H eq_refl) as ARo; clear H end.
    KXCell.kx_cells_split ARo.
    
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m _) =>
      eapply (F3 m l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3) end.
    all: first [ eassumption | (unfold X42PF; split; eassumption) | KXCell.kx_cells_merge | lia ].
  Qed.

  Lemma x42_l10 : forall x, 0 <= x < 2^64 -> x mod 2^64 * 14757395258967641293 / 2^64 / 8 = x / 10.
  Proof using. intros x Hx. rewrite (Z.mod_small x) by lia. Z.div_mod_to_equations; lia. Qed.
  Lemma x42_l7 : forall x, 0 <= x < 2^64 ->
    ((x + -1 * (x mod 2^64 * 2635249153387078803 / 2^64)) mod 2^64 / 2 + x mod 2^64 * 2635249153387078803 / 2^64) mod 2^64 / 4 = x / 7.
  Proof using.
    intros x Hx. rewrite (Z.mod_small x) by lia.
    set (h := x * 2635249153387078803 / 2^64).
    assert (Hh : 0 <= h <= x) by (subst h; Z.div_mod_to_equations; lia).
    replace (x + -1 * h) with (x - h) by lia. rewrite (Z.mod_small (x - h)) by lia.
    rewrite (Z.mod_small ((x - h) / 2 + h)) by (Z.div_mod_to_equations; lia).
    subst h. Z.div_mod_to_equations; lia.
  Qed.
  Lemma x42_fo_eqs : forall q dcap o0 o1 o2 o3 i0 n,
    0 <= o0 <= q -> 0 <= o1 <= 2 * q -> 0 <= o2 <= 3 * q -> 0 <= o3 <= dcap -> 0 <= q -> 3 * q <= dcap -> dcap < 2^32 ->
    0 <= i0 -> i0 + 8 <= n -> n < 2^32 ->
    ((-1 * o0 + q) mod 2^64 * 14757395258967641293 / 2^64 / 8 = (q - o0) / 10) /\
    ((-1 * o1 + 2 * q) mod 2^64 * 14757395258967641293 / 2^64 / 8 = (2 * q - o1) / 10) /\
    ((-1 * o2 + 3 * q) mod 2^64 * 14757395258967641293 / 2^64 / 8 = (3 * q - o2) / 10) /\
    ((-1 * o3 + dcap) mod 2^64 * 14757395258967641293 / 2^64 / 8 = (dcap - o3) / 10) /\
    (((i0 + -1 * (i0 mod 2^64 * 2635249153387078803 / 2^64)) mod 2^64 / 2 + i0 mod 2^64 * 2635249153387078803 / 2^64) mod 2^64 / 4 = i0 / 7) /\
    (0 <= (q - o0) / 10 /\ 10 * ((q - o0) / 10) <= q - o0) /\ (0 <= (2 * q - o1) / 10 /\ 10 * ((2 * q - o1) / 10) <= 2 * q - o1) /\
    (0 <= (3 * q - o2) / 10 /\ 10 * ((3 * q - o2) / 10) <= 3 * q - o2) /\ (0 <= (dcap - o3) / 10 /\ 10 * ((dcap - o3) / 10) <= dcap - o3) /\
    (0 <= i0 / 7 /\ 7 * (i0 / 7) <= i0).
  Proof using.
    intros q dcap' o0 o1 o2 o3 i0 n' H0 H1 H2 H3 HQ HQ3 HD HI HJ HN.
    split; [rewrite x42_l10 by lia; f_equal; lia|]. split; [rewrite x42_l10 by lia; f_equal; lia|].
    split; [rewrite x42_l10 by lia; f_equal; lia|]. split; [rewrite x42_l10 by lia; f_equal; lia|].
    split; [apply x42_l7; lia|].
    repeat split; Z.div_mod_to_equations; lia.
  Qed.

  Notation KOR mb q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 :=
    (forall mm' i0' i1' i2' i3' o0' o1' o2' o3' (c0' c1' c2' c3' : word) (y1 y7 y18 y19 y20 y22 y24 y25 y28 y29 y30 y31 : word) (w'0 w'1 w'2 : word),
        munch WDL mb mm' -> wmono bsegs mb mm' -> munch W0 m0 mm' -> wmono bsegs m0 mm' -> mem_inv bsegs mm' ->
        stk bsegs mm' DST (DST + dcap) -> bytes_at bsegs mm' DT dtb ->
        (FRS mm' w'0 w'1 w'2 (Z_to_bv 64 (SRC)) (Z_to_bv 64 (n)) (Z_to_bv 64 (DT)) (Z_to_bv 64 (DST)) (Z_to_bv 64 (dcap)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (14757395258967641293)) (Z_to_bv 64 (2635249153387078803)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (DST + 3 * q)) (Z_to_bv 64 (DST + 2 * q)) (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (66420))) ->
        (ARGS mm' av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (SRC + 6)) (Z_to_bv 64 (SRC + 6 + l1)) (Z_to_bv 64 (SRC + 6 + l1 + l2)) (Z_to_bv 64 (SRC + 6 + l1 + l2 + l3))) ->
        (LOC mm' e0 e1 e2 e3 (Z_to_bv 64 (DST + o0')) (Z_to_bv 64 (DST + o1')) (Z_to_bv 64 (DST + o2')) (Z_to_bv 64 (DST + o3')) (Z_to_bv 64 (SRC + i0')) (Z_to_bv 64 (SRC + i1')) (Z_to_bv 64 (SRC + i2')) (Z_to_bv 64 (SRC + i3')) c0' c1' c2' c3') -> bytes_at bsegs mm' SRC src ->
        0 <= i0' <= i0 -> 0 <= i1' <= i1 -> 0 <= i2' <= i2 -> 0 <= i3' <= i3 ->
        o0 + 5 <= o0' <= q -> o1 + 5 <= o1' <= 2 * q -> o2 + 5 <= o2' <= 3 * q -> o3 + 5 <= o3' <= dcap -> OL <= o3' ->
        LBW 8 c0' -> LBW 8 c1' -> LBW 8 c2' -> LBW 8 c3' ->
        evtF bsegs RNG POST (ST 0x85278 mm' y1 (Z_to_bv 64 (SRC + i2')) (Z_to_bv 64 (SRC + i3')) y7 (Z_to_bv 64 (18446744073709551600)) (Z_to_bv 64 (SPV + -136)) (Z_to_bv 64 (nd)) c0' (Z_to_bv 64 (DST + o3')) (Z_to_bv 64 (DST + o0')) (Z_to_bv 64 (DST + o2')) (Z_to_bv 64 (DST + o1')) (Z_to_bv 64 (SRC + i0')) (Z_to_bv 64 (SRC + i1')) y18 y19 y20 (Z_to_bv 64 (SPV + -168)) y22 SB y24 y25 (Z_to_bv 64 (134483)) (Z_to_bv 64 (DT + 4)) y28 y29 y30 y31)).
  Notation KOUT q nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 :=
    (forall mm' i0' i1' i2' i3' o0' o1' o2' o3' (c0' c1' c2' c3' : word) (e0' e1' e2' e3' : word) (y1 y7 y18 y19 y20 y22 y24 y25 y26 y28 y29 y30 y31 : word) (w'0 w'1 w'2 w'17 : word),
        X42PF mm' -> munch W0 m0 mm' -> wmono bsegs m0 mm' -> mem_inv bsegs mm' -> stk bsegs mm' DST (DST + dcap) -> bytes_at bsegs mm' DT dtb ->
        (FRS mm' w'0 w'1 w'2 (Z_to_bv 64 (SRC)) (Z_to_bv 64 (n)) (Z_to_bv 64 (DT)) (Z_to_bv 64 (DST)) (Z_to_bv 64 (dcap)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (14757395258967641293)) (Z_to_bv 64 (2635249153387078803)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (DST + 3 * q)) (Z_to_bv 64 (DST + 2 * q)) (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DT + 4)) w'17) ->
        (ARGS mm' av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (SRC + 6)) (Z_to_bv 64 (SRC + 6 + l1)) (Z_to_bv 64 (SRC + 6 + l1 + l2)) (Z_to_bv 64 (SRC + 6 + l1 + l2 + l3))) ->
        (LOC mm' e0' e1' e2' e3' (Z_to_bv 64 (DST + o0')) (Z_to_bv 64 (DST + o1')) (Z_to_bv 64 (DST + o2')) (Z_to_bv 64 (DST + o3')) (Z_to_bv 64 (SRC + i0')) (Z_to_bv 64 (SRC + i1')) (Z_to_bv 64 (SRC + i2')) (Z_to_bv 64 (SRC + i3')) c0' c1' c2' c3') ->
        bytes_at bsegs mm' SRC src ->
        0 <= i0' <= i0 -> 0 <= i1' <= i1 -> 0 <= i2' <= i2 -> 0 <= i3' <= i3 ->
        o0 + 5 <= o0' <= q -> o1 + 5 <= o1' <= 2 * q -> o2 + 5 <= o2' <= 3 * q -> o3 + 5 <= o3' <= dcap ->
        LBW 8 c0' -> LBW 8 c1' -> LBW 8 c2' -> LBW 8 c3' ->
        evtF bsegs RNG POST (ST 0x85278 mm' y1 (Z_to_bv 64 (SRC + i2')) (Z_to_bv 64 (SRC + i3')) y7 (Z_to_bv 64 (18446744073709551600)) (Z_to_bv 64 (SPV + -136)) (Z_to_bv 64 (nd)) c0' (Z_to_bv 64 (DST + o3')) (Z_to_bv 64 (DST + o0')) (Z_to_bv 64 (DST + o2')) (Z_to_bv 64 (DST + o1')) (Z_to_bv 64 (SRC + i0')) (Z_to_bv 64 (SRC + i1')) y18 y19 y20 (Z_to_bv 64 (SPV + -168)) y22 SB y24 y25 y26 (Z_to_bv 64 (DT + 4)) y28 y29 y30 y31)).
  Notation WDA := [(DST, DST + dcap); (SPV - 528, SPV - 104)].

  Definition x42e_fo_b_case (P : Z -> Z -> Z -> Z -> Z -> Prop) : Prop := forall mm q R nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 (c0 c1 c2 c3 : word) (e0 e1 e2 e3 : word) (av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 : word)
      (x1 x18 x19 x20 x22 x24 x25 x26 x29 x30 x31 : word)
      (w0 w1 w2 w17 : word),
    P R i0 i1 i2 i3 ->
    X42PF mm -> munch W0 m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm -> stk bsegs mm DST (DST + dcap) -> bytes_at bsegs mm DT dtb ->
    (FRS mm w0 w1 w2 (Z_to_bv 64 (SRC)) (Z_to_bv 64 (n)) (Z_to_bv 64 (DT)) (Z_to_bv 64 (DST)) (Z_to_bv 64 (dcap)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (14757395258967641293)) (Z_to_bv 64 (2635249153387078803)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (DST + 3 * q)) (Z_to_bv 64 (DST + 2 * q)) (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DT + 4)) w17) ->
    (ARGS mm av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (SRC + 6)) (Z_to_bv 64 (SRC + 6 + l1)) (Z_to_bv 64 (SRC + 6 + l1 + l2)) (Z_to_bv 64 (SRC + 6 + l1 + l2 + l3))) ->
    (LOC mm e0 e1 e2 e3 (Z_to_bv 64 (DST + o0)) (Z_to_bv 64 (DST + o1)) (Z_to_bv 64 (DST + o2)) (Z_to_bv 64 (DST + o3)) (Z_to_bv 64 (SRC + i0)) (Z_to_bv 64 (SRC + i1)) (Z_to_bv 64 (SRC + i2)) (Z_to_bv 64 (SRC + i3)) c0 c1 c2 c3) ->
    bytes_at bsegs mm SRC src -> nd = -1 * DT + -5 ->
    0 < dcap -> 38 <= n -> 0 <= q -> 3 * q < dcap -> q = (dcap + 3) / 4 -> DST + 3 * ((dcap + 3) / 4) < DST + dcap ->
    8 <= l1 -> 8 <= l2 -> 8 <= l3 -> 6 + l1 + l2 + l3 + 8 <= n ->
    0 <= i0 -> i0 + 8 <= n -> 0 <= i1 -> i1 + 8 <= n -> 0 <= i2 -> i2 + 8 <= n -> 0 <= i3 -> i3 + 8 <= n ->
    0 <= o0 <= q -> q <= o1 <= 2 * q -> 2 * q <= o2 <= 3 * q -> 3 * q <= o3 <= dcap ->
    LBW 8 c0 -> LBW 8 c1 -> LBW 8 c2 -> LBW 8 c3 ->
    0 <= R -> 10 * R <= q - o0 -> 10 * R <= 2 * q - o1 -> 10 * R <= 3 * q - o2 -> 10 * R <= dcap - o3 -> 7 * R <= i0 ->
    KOUT q nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 ->
    evtF bsegs RNG POST (ST 0x85374 mm x1 (Z_to_bv 64 (SRC + i2)) (Z_to_bv 64 (SRC + i3)) (Z_to_bv 64 (R)) (Z_to_bv 64 (18446744073709551600)) (Z_to_bv 64 (SPV + -136)) (Z_to_bv 64 (nd)) c0 (Z_to_bv 64 (DST + o3)) (Z_to_bv 64 (DST + o0)) (Z_to_bv 64 (DST + o2)) (Z_to_bv 64 (DST + o1)) (Z_to_bv 64 (SRC + i0)) (Z_to_bv 64 (SRC + i1)) x18 x19 x20 (Z_to_bv 64 (SPV + -168)) x22 SB x24 x25 x26 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + (o3 + 5 * R))) x29 x30 x31).

  Local Ltac zfob D :=
    unfold x42e_fo_b_case;
    intros mm q R nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 c0 c1 c2 c3 e0 e1 e2 e3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11
      x1 x18 x19 x20 x22 x24 x25 x26 x29 x30 x31
      w0 w1 w2 w17 HC
      PV MU0 WM0 MI OUT DTBH FR AR LC SRCB HND DP N38 HQ0 HQ3 HQ H3Q HL1 HL2 HL3 HLN HI0 HN0 HI1 HN1 HI2 HN2 HI3 HN3
      HO0 HO1 HO2 HO3 HLB0 HLB1 HLB2 HLB3 HR0 HRA HRB HRC HRD HR7 KO;
    cbv beta in HC; subst nd;
    pose proof (lbw_pos _ _ HLB0) as HLP0; pose proof (lbw_pos _ _ HLB1) as HLP1;
    pose proof (lbw_pos _ _ HLB2) as HLP2; pose proof (lbw_pos _ _ HLB3) as HLP3;
    assert (RFR : rng RNG (SPV + -528) 424) by (apply (rng_sub RNG lo (SPV - lo)); [assumption | lia | lia]);
    assert (PVD1 : disjoint_from WDF (SPV + -104) 104) by (cbn [disjoint_from]; lia);
    assert (PVD2 : disjoint_from WDF lo (SPV + -528 - lo)) by (cbn [disjoint_from]; lia);
    pose proof (munch_refl WDF mm) as MUS; pose proof (wmono_refl bsegs mm) as WMS;
    rewrite <- (OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib.MState.Z_to_bv_bv_unsigned c1) in LC;
    rewrite <- (OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib.MState.Z_to_bv_bv_unsigned c2) in LC;
    rewrite <- (OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib.MState.Z_to_bv_bv_unsigned c3) in LC;
    do 12 (let H1 := fresh "KL" in
           apply (OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common.KXCell.kx_rwc_cons bsegs mm) in LC;
           destruct LC as [H1 LC]; cbn [csize] in LC;
           OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common.KXCell.kx_rwc_norm LC);
    kx_runFmd [545748; 551656] 60%nat D
      [KZRange R 0 (2^32); KZRange o0 0 (2^32); KZRange o1 0 (2^32); KZRange o2 0 (2^32); KZRange o3 0 (2^32);
       KZRange i0 0 (2^32); KZRange i1 0 (2^32); KZRange i2 0 (2^32); KZRange i3 0 (2^32); KZRange (o3 + 5 * R) 0 (2^32);
       KZRange q 0 (2^32); KZRange dcap 1 (2^32); KZRange n 38 (2^32);
       KZRange DST 4096 (2^47 - 1); KZRange SRC 4096 (2^47 - 1); KZRange DT 4096 (2^47 - 1); KZRange SPV 7232 (2^47 - 1);
       KZRange (bv_unsigned c0) 1 (2^64 - 1); KZRange (bv_unsigned c1) 1 (2^64 - 1);
       KZRange (bv_unsigned c2) 1 (2^64 - 1); KZRange (bv_unsigned c3) 1 (2^64 - 1);
       KZWr (SPV + -528) 144; KZWr (SPV + -384) 152; KZWr (SPV + -136) 32;
       KZWord (SPV + -168) 8 (SRC + i0); KZWord (SPV + -160) 8 (SRC + i1);
       KZWord (SPV + -152) 8 (SRC + i2); KZWord (SPV + -144) 8 (SRC + i3);
       KZWord (SPV + -128) 8 (bv_unsigned c1); KZWord (SPV + -120) 8 (bv_unsigned c2);
       KZWord (SPV + -112) 8 (bv_unsigned c3)]
      []
      [(SPV + -528, 424)]
      [];
    lazymatch goal with
    | |- evtF _ _ _ _ => idtac
    | |- 0 <= bv_unsigned ?w < _ => pose proof (bv_unsigned_in_range _ w); unfold bv_modulus in *; lia
    | |- 0 <= bv_unsigned ?w <= _ => pose proof (bv_unsigned_in_range _ w); unfold bv_modulus in *; lia
    | |- branch_taken _ _ _ = _ => OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW.AF_huf_w4s3b.w4br
    end;
    kx_post_regs; kx_post_mem_free; kx_munch MU0; kx_munch MUS; kx_frame DTBH; kx_frame SRCB;
    OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common.KXCell.kx_cells_split FR;
    OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common.KXCell.kx_cells_split AR;
    OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common.KXCell.kx_cells_split LC;
    OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common.KXCell.kx_cells_post;
    rewrite ?OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib.MState.Z_to_bv_bv_unsigned in *;
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
      set (M1 := m1) in *;
      pose proof (x42pf_transport mm M1 _ PV MUS WMS PVD1 PVD2) as PV2;
      try replace (Z_to_bv 64 (- DT + -5)) with (Z_to_bv 64 (-1 * DT + -5)) by (f_equal; lia);
      try replace (Z_to_bv 64 (-16)) with (Z_to_bv 64 18446744073709551600) by (apply bv_eq; vm_compute; reflexivity);
      lazymatch goal with
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 551656) _ _ _ _) =>
          eapply (F2 M1 l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3)
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 545748) _ _ _ _) =>
          assert (HR1 : 1 <= R) by lia;
          lazymatch goal with
          | |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?X28 _ _ _) _ _ _ _ _ _) =>
              replace X28 with (Z_to_bv 64 (DST + (o3 + 5 * R))) by (f_equal; lia)
          end;
          eapply (x42e_fi (Z.to_nat R) M1 M1 q (o3 + 5 * R) (-1 * DT + -5) l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3)
      end;
      lazymatch goal with
      | |- forall _, _ => idtac
      | |- munch _ ?a ?a => apply munch_refl
      | |- wmono _ ?a ?a => apply wmono_refl
      | |- X42PF _ => exact PV2
      | |- rw_cells _ _ _ _ => first [eassumption | OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common.KXCell.kx_cells_merge]
      | |- LBW _ _ => assumption
      | |- (1 <= Z.to_nat _)%nat => lia
      | |- context [Z.of_nat (Z.to_nat ?X)] => rewrite (Z2Nat.id X) by lia; lia
      | |- _ => first [eassumption | lia]
      end;
      lazymatch goal with
      | |- forall _, _ =>
          intros mm2 i0' i1' i2' i3' o0' o1' o2' o3' c0' c1' c2' c3' y1 y7 y18 y19 y20 y22 y24 y25 y28 y29 y30 y31 w'0 w'1 w'2
            MU' WM' MU0' WM0' MI' OUT' DTB' FR' AR' LC' SRCB' GI0 GI1 GI2 GI3 GO0 GO1 GO2 GO3 GOL GL0 GL1 GL2 GL3;
          assert (MU1 : munch WDF M1 mm2)
            by (eapply munch_weaken; [| exact MU']; unfold sub_fp; cbn [outside fst snd app]; intros; lia);
          pose proof (x42pf_transport mm mm2 _ PV (munch_trans _ _ _ _ MUS MU1) (wmono_trans _ _ _ _ WMS WM') PVD1 PVD2) as PV';
          eapply (KO _ i0' i1' i2' i3' o0' o1' o2' o3'); first [exact PV' | eassumption | lia]
      end
    end.

  Lemma x42e_fo_b_c0 : x42e_fo_b_case (fun R i0 i1 i2 i3 => R = 0).
  Proof using CTX X2OK NBOK ACTX TL11 MC AZS F3.
    pose proof CTX as CTX'. x42e_ctx_open CTX'. pose proof ACTX as ACTX'. x42e_actx_open ACTX'.
    clear UDST RDST RDSTS UDT USRC RSRC RSRCS.
    zfob constr:(repeat false 200).
  Qed.

  Lemma x42e_fo_b_c1 : x42e_fo_b_case (fun R i0 i1 i2 i3 => R <> 0 /\ i1 < i0).
  Proof using CTX X2OK NBOK ACTX TL11 MC AZS F3.
    pose proof CTX as CTX'. x42e_ctx_open CTX'. pose proof ACTX as ACTX'. x42e_actx_open ACTX'.
    clear UDST RDST RDSTS UDT USRC RSRC RSRCS.
    zfob constr:(true :: false :: repeat false 200).
  Qed.

  Lemma x42e_fo_b_c2 : x42e_fo_b_case (fun R i0 i1 i2 i3 => R <> 0 /\ i0 <= i1 /\ i2 < i1).
  Proof using CTX X2OK NBOK ACTX TL11 MC AZS F3.
    pose proof CTX as CTX'. x42e_ctx_open CTX'. pose proof ACTX as ACTX'. x42e_actx_open ACTX'.
    clear UDST RDST RDSTS UDT USRC RSRC RSRCS.
    zfob constr:(true :: true :: false :: repeat false 200).
  Qed.

  Lemma x42e_fo_b_c3 : x42e_fo_b_case (fun R i0 i1 i2 i3 => R <> 0 /\ i0 <= i1 /\ i1 <= i2 /\ i3 < i2).
  Proof using CTX X2OK NBOK ACTX TL11 MC AZS F3.
    pose proof CTX as CTX'. x42e_ctx_open CTX'. pose proof ACTX as ACTX'. x42e_actx_open ACTX'.
    clear UDST RDST RDSTS UDT USRC RSRC RSRCS.
    zfob constr:(true :: true :: true :: false :: repeat false 200).
  Qed.

  Lemma x42e_fo_b_c4 : x42e_fo_b_case (fun R i0 i1 i2 i3 => R <> 0 /\ i0 <= i1 /\ i1 <= i2 /\ i2 <= i3).
  Proof using CTX X2OK NBOK ACTX TL11 MC AZS F3.
    pose proof CTX as CTX'. x42e_ctx_open CTX'. pose proof ACTX as ACTX'. x42e_actx_open ACTX'.
    clear UDST RDST RDSTS UDT USRC RSRC RSRCS.
    zfob constr:(true :: true :: true :: true :: repeat false 200).
  Qed.

  Lemma x42e_fo_b : forall mm q R nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 (c0 c1 c2 c3 : word) (e0 e1 e2 e3 : word) (av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 : word)
      (x1 x18 x19 x20 x22 x24 x25 x26 x29 x30 x31 : word)
      (w0 w1 w2 w17 : word),
    X42PF mm -> munch W0 m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm -> stk bsegs mm DST (DST + dcap) -> bytes_at bsegs mm DT dtb ->
    (FRS mm w0 w1 w2 (Z_to_bv 64 (SRC)) (Z_to_bv 64 (n)) (Z_to_bv 64 (DT)) (Z_to_bv 64 (DST)) (Z_to_bv 64 (dcap)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (14757395258967641293)) (Z_to_bv 64 (2635249153387078803)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (DST + 3 * q)) (Z_to_bv 64 (DST + 2 * q)) (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DT + 4)) w17) ->
    (ARGS mm av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (SRC + 6)) (Z_to_bv 64 (SRC + 6 + l1)) (Z_to_bv 64 (SRC + 6 + l1 + l2)) (Z_to_bv 64 (SRC + 6 + l1 + l2 + l3))) ->
    (LOC mm e0 e1 e2 e3 (Z_to_bv 64 (DST + o0)) (Z_to_bv 64 (DST + o1)) (Z_to_bv 64 (DST + o2)) (Z_to_bv 64 (DST + o3)) (Z_to_bv 64 (SRC + i0)) (Z_to_bv 64 (SRC + i1)) (Z_to_bv 64 (SRC + i2)) (Z_to_bv 64 (SRC + i3)) c0 c1 c2 c3) ->
    bytes_at bsegs mm SRC src -> nd = -1 * DT + -5 ->
    0 < dcap -> 38 <= n -> 0 <= q -> 3 * q < dcap -> q = (dcap + 3) / 4 -> DST + 3 * ((dcap + 3) / 4) < DST + dcap ->
    8 <= l1 -> 8 <= l2 -> 8 <= l3 -> 6 + l1 + l2 + l3 + 8 <= n ->
    0 <= i0 -> i0 + 8 <= n -> 0 <= i1 -> i1 + 8 <= n -> 0 <= i2 -> i2 + 8 <= n -> 0 <= i3 -> i3 + 8 <= n ->
    0 <= o0 <= q -> q <= o1 <= 2 * q -> 2 * q <= o2 <= 3 * q -> 3 * q <= o3 <= dcap ->
    LBW 8 c0 -> LBW 8 c1 -> LBW 8 c2 -> LBW 8 c3 ->
    0 <= R -> 10 * R <= q - o0 -> 10 * R <= 2 * q - o1 -> 10 * R <= 3 * q - o2 -> 10 * R <= dcap - o3 -> 7 * R <= i0 ->
    KOUT q nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 ->
    evtF bsegs RNG POST (ST 0x85374 mm x1 (Z_to_bv 64 (SRC + i2)) (Z_to_bv 64 (SRC + i3)) (Z_to_bv 64 (R)) (Z_to_bv 64 (18446744073709551600)) (Z_to_bv 64 (SPV + -136)) (Z_to_bv 64 (nd)) c0 (Z_to_bv 64 (DST + o3)) (Z_to_bv 64 (DST + o0)) (Z_to_bv 64 (DST + o2)) (Z_to_bv 64 (DST + o1)) (Z_to_bv 64 (SRC + i0)) (Z_to_bv 64 (SRC + i1)) x18 x19 x20 (Z_to_bv 64 (SPV + -168)) x22 SB x24 x25 x26 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + (o3 + 5 * R))) x29 x30 x31).
  Proof using CTX X2OK NBOK ACTX TL11 MC AZS F3.
    intros mm q R nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 c0 c1 c2 c3 e0 e1 e2 e3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11
      x1 x18 x19 x20 x22 x24 x25 x26 x29 x30 x31 w0 w1 w2 w17.
    let k L H :=
      exact (L mm q R nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 c0 c1 c2 c3 e0 e1 e2 e3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11
               x1 x18 x19 x20 x22 x24 x25 x26 x29 x30 x31 w0 w1 w2 w17 H) in
    destruct (Z.eq_dec R 0) as [HR0 | HR0];
    [ k x42e_fo_b_c0 HR0
    | destruct (Z_lt_le_dec i1 i0) as [H10 | H10];
      [ k x42e_fo_b_c1 (conj HR0 H10)
      | destruct (Z_lt_le_dec i2 i1) as [H21 | H21];
        [ k x42e_fo_b_c2 (conj HR0 (conj H10 H21))
        | destruct (Z_lt_le_dec i3 i2) as [H32 | H32];
          [ k x42e_fo_b_c3 (conj HR0 (conj H10 (conj H21 H32)))
          | k x42e_fo_b_c4 (conj HR0 (conj H10 (conj H21 H32))) ] ] ] ].
  Qed.

  
  Local Ltac fo_ez :=
    repeat match goal with
    | |- context [KX2.edenot ?E (KX2.EMd M_MULHU ?a ?b)] =>
        change (KX2.edenot E (KX2.EMd M_MULHU a b)) with (mul_div M_MULHU (KX2.edenot E a) (KX2.edenot E b));
        rewrite ?KXS.u_mulhu64
    | |- context [KX2.edenot ?E ?x] =>
        let b := eval unfold E in E in
        lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
          rewrite (ez_ok zv E (kE_atoms zv xs) x);
          let na := eval vm_compute in (length zv) in
          cbv [ez]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb]
        end
    end.

  Lemma fo_mhs : forall a K, 0 <= K < 2 ^ 64 -> (a mod 2 ^ 64 * K / 2 ^ 64) mod 2 ^ 64 = a mod 2 ^ 64 * K / 2 ^ 64.
  Proof using.
    intros a K HK. pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as HA.
    set (x := a mod 2 ^ 64) in *. clearbody x.
    assert (HM : 0 <= x * K < 2 ^ 64 * 2 ^ 64) by nia.
    apply Z.mod_small. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
  Qed.

  
  Local Ltac fo_norm :=
    rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
    change (Z.of_N 64) with 64;
    repeat match goal with |- context [?K mod 2 ^ 64] =>
      lazymatch K with Zpos _ => rewrite (Z.mod_small K (2 ^ 64)) by lia end end;
    try change (2 ^ (3 mod 64)) with 8; try change (2 ^ (2 mod 64)) with 4; try change (2 ^ (1 mod 64)) with 2;
    repeat match goal with |- context [(?a mod 2 ^ 64 * ?K / 2 ^ 64) mod 2 ^ 64] =>
      rewrite (fo_mhs a K) by lia end.

  Lemma fo_ltu : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
    branch_taken BC_LTU (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
  Proof using.
    intros a b Ha Hb. unfold branch_taken; rewrite ?bv_ltu_Z, ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
    try change (Z.of_N 64) with 64; rewrite (Z.mod_small a), (Z.mod_small b) by lia; reflexivity.
  Qed.

  Lemma fo_geu : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
    branch_taken BC_GEU (Z_to_bv 64 a) (Z_to_bv 64 b) = negb (a <? b).
  Proof using.
    intros a b Ha Hb. unfold branch_taken; rewrite ?bv_ltu_Z, ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
    try change (Z.of_N 64) with 64; rewrite (Z.mod_small a), (Z.mod_small b) by lia; reflexivity.
  Qed.

  
  Local Ltac fo_br :=
    first [ rewrite fo_ltu by assumption | rewrite fo_geu by assumption ];
    first [ apply Z.ltb_lt; assumption | apply Z.ltb_ge; assumption
          | apply Bool.negb_true_iff, Z.ltb_ge; assumption | apply Bool.negb_false_iff, Z.ltb_lt; assumption
          | apply Z.ltb_lt; lia | apply Z.ltb_ge; lia
          | apply Bool.negb_true_iff, Z.ltb_ge; lia | apply Bool.negb_false_iff, Z.ltb_lt; lia ].

  Lemma x42e_fo : forall (k : nat) mm q nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 (c0 c1 c2 c3 : word) (e0 e1 e2 e3 : word) (av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 : word)
      (x1 x7 x18 x19 x20 x22 x24 x25 x26 x28 x29 x30 x31 : word)
      (w0 w1 w2 w17 : word),
    X42PF mm -> munch W0 m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm -> stk bsegs mm DST (DST + dcap) -> bytes_at bsegs mm DT dtb ->
    (FRS mm w0 w1 w2 (Z_to_bv 64 (SRC)) (Z_to_bv 64 (n)) (Z_to_bv 64 (DT)) (Z_to_bv 64 (DST)) (Z_to_bv 64 (dcap)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (14757395258967641293)) (Z_to_bv 64 (2635249153387078803)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (DST + 3 * q)) (Z_to_bv 64 (DST + 2 * q)) (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DT + 4)) w17) ->
    (ARGS mm av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (SRC + 6)) (Z_to_bv 64 (SRC + 6 + l1)) (Z_to_bv 64 (SRC + 6 + l1 + l2)) (Z_to_bv 64 (SRC + 6 + l1 + l2 + l3))) ->
    (LOC mm e0 e1 e2 e3 (Z_to_bv 64 (DST + o0)) (Z_to_bv 64 (DST + o1)) (Z_to_bv 64 (DST + o2)) (Z_to_bv 64 (DST + o3)) (Z_to_bv 64 (SRC + i0)) (Z_to_bv 64 (SRC + i1)) (Z_to_bv 64 (SRC + i2)) (Z_to_bv 64 (SRC + i3)) c0 c1 c2 c3) ->
    bytes_at bsegs mm SRC src -> nd = -1 * DT + -5 ->
    0 < dcap -> 38 <= n -> 0 <= q -> 3 * q < dcap -> q = (dcap + 3) / 4 -> DST + 3 * ((dcap + 3) / 4) < DST + dcap ->
    8 <= l1 -> 8 <= l2 -> 8 <= l3 -> 6 + l1 + l2 + l3 + 8 <= n ->
    0 <= i0 -> i0 + 8 <= n -> 0 <= i1 -> i1 + 8 <= n -> 0 <= i2 -> i2 + 8 <= n -> 0 <= i3 -> i3 + 8 <= n ->
    0 <= o0 <= q -> q <= o1 <= 2 * q -> 2 * q <= o2 <= 3 * q -> 3 * q <= o3 <= dcap ->
    LBW 8 c0 -> LBW 8 c1 -> LBW 8 c2 -> LBW 8 c3 ->
    dcap - o3 < Z.of_nat k ->
    evtF bsegs RNG POST (ST 0x85278 mm x1 (Z_to_bv 64 (SRC + i2)) (Z_to_bv 64 (SRC + i3)) x7 (Z_to_bv 64 (18446744073709551600)) (Z_to_bv 64 (SPV + -136)) (Z_to_bv 64 (nd)) c0 (Z_to_bv 64 (DST + o3)) (Z_to_bv 64 (DST + o0)) (Z_to_bv 64 (DST + o2)) (Z_to_bv 64 (DST + o1)) (Z_to_bv 64 (SRC + i0)) (Z_to_bv 64 (SRC + i1)) x18 x19 x20 (Z_to_bv 64 (SPV + -168)) x22 SB x24 x25 x26 (Z_to_bv 64 (DT + 4)) x28 x29 x30 x31).
  Proof using CTX X2OK NBOK ACTX TL11 MC AZS F3.
    pose proof CTX as CTX'. x42e_ctx_open CTX'. pose proof ACTX as ACTX'. x42e_actx_open ACTX'.
    induction k as [|k IH]; intros mm q nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 c0 c1 c2 c3 e0 e1 e2 e3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11
      x1 x7 x18 x19 x20 x22 x24 x25 x26 x28 x29 x30 x31 w0 w1 w2 w17
      PV MU0 WM0 MI OUT DTBH FR AR LC SRCB HND DP N38 HQ0 HQ3 HQ H3Q HL1 HL2 HL3 HLN HI0 HN0 HI1 HN1 HI2 HN2 HI3 HN3
      HO0 HO1 HO2 HO3 HLB0 HLB1 HLB2 HLB3 HK; [exfalso; clear - HK HO3; lia|]. subst nd.
    assert (RFR : rng RNG (SPV + -528) 424) by (eapply rng_sub; [exact RSTK | lia | lia]).
    assert (DTR : 4096 <= DT <= 2 ^ 47 - 1) by (rewrite TL11 in DTBF; lia).
    clear UDST RDST RDSTS UDT USRC RSTK ART RDT RDTS RSRC RSRCS.
    clear OS1 OS2 OS3 DJ1 DJ2 DSTA DHI DT2 SPA DTA DTBF TL SL DL.
    
    assert (P1 : 0 <= o1 <= 2 * q) by lia. assert (P2 : 0 <= o2 <= 3 * q) by lia. assert (P3 : 0 <= o3 <= dcap) by lia.
    assert (P4 : 3 * q <= dcap) by lia. assert (P5 : dcap < 2 ^ 32) by lia. assert (P6 : n < 2 ^ 32) by lia.
    
    set (QQ := (dcap + 3) / 4) in HQ, H3Q.
    set (Q0 := (q - o0) / 10). set (Q1 := (2 * q - o1) / 10). set (Q2 := (3 * q - o2) / 10).
    set (Q3 := (dcap - o3) / 10). set (Q7 := i0 / 7).
    assert (QB0 : 0 <= Q0 < 2 ^ 64) by (unfold Q0; Z.div_mod_to_equations; lia).
    assert (QB1 : 0 <= Q1 < 2 ^ 64) by (unfold Q1; Z.div_mod_to_equations; lia).
    assert (QB2 : 0 <= Q2 < 2 ^ 64) by (unfold Q2; Z.div_mod_to_equations; lia).
    assert (QB3 : 0 <= Q3 < 2 ^ 64) by (unfold Q3; Z.div_mod_to_equations; lia).
    assert (QB7 : 0 <= Q7 < 2 ^ 64) by (unfold Q7; Z.div_mod_to_equations; lia).
    pose proof FR as FRK. let T := type of FRK in change (@id Prop T) in FRK.
    let T := type of AR in change (@id Prop T) in AR. let T := type of LC in change (@id Prop T) in LC.
    do 9 (apply (OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common.KXCell.kx_rwc_cons bsegs mm) in FR;
          destruct FR as [_ FR]; cbn [csize] in FR;
          OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common.KXCell.kx_rwc_norm FR).
    do 7 (let H1 := fresh "KL" in
          apply (OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common.KXCell.kx_rwc_cons bsegs mm) in FR;
          destruct FR as [H1 FR]; cbn [csize] in FR;
          OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common.KXCell.kx_rwc_norm FR).
    clear FR.
    (lazymatch type of FRK with
      | @id Prop (rw_cells _ _ _ [_; _; _; _; _; _; _; _; _; C8 (Z_to_bv 64 ?K1); C8 (Z_to_bv 64 ?K2); _; _; _; _; _; _; _]) =>
    let run D := kx_runFmd [545652] 64%nat D
      [KZRange o0 0 (2^32 - 1); KZRange o1 0 (2^32 - 1); KZRange o2 0 (2^32 - 1); KZRange o3 0 (2^32 - 1);
       KZRange i0 0 (2^32 - 1); KZRange i1 0 (2^32 - 1); KZRange i2 0 (2^32 - 1); KZRange i3 0 (2^32 - 1);
       KZRange q 0 (2^32 - 1); KZRange dcap 1 (2^32 - 1); KZRange n 38 (2^32 - 1);
       KZRange DST 4096 (2^47 - 1); KZRange SRC 4096 (2^47 - 1); KZRange DT 4096 (2^47 - 1); KZRange SPV 8192 (2^47 - 1);
       KZRange (q - o0) 0 (2^32 - 1); KZRange (2 * q - o1) 0 (2^32 - 1); KZRange (3 * q - o2) 0 (2^32 - 1);
       KZRange (dcap - o3) 0 (2^32 - 1);
       KZWord (SPV + -456) 8 K1; KZWord (SPV + -448) 8 K2;
       KZWord (SPV + -440) 8 (DST + dcap); KZWord (SPV + -432) 8 (DST + 3 * q); KZWord (SPV + -424) 8 (DST + 2 * q);
       KZWord (SPV + -416) 8 (DST + q); KZWord (SPV + -408) 8 SRC]
      []
      [(SPV + -528, 424)]
      [] in
    
    let L4 m d1 d2 d3 a b := destruct (Z_lt_le_dec m Q3) as [C4|C4];
      [ run [d1; d2; d3; a] | run [d1; d2; d3; b] ] in
    let L3 m d1 d2 a b := destruct (Z_lt_le_dec m Q2) as [C3|C3];
      [ L4 m d1 d2 a true false | L4 Q2 d1 d2 b false true ] in
    let L2 m d1 a b := destruct (Z_lt_le_dec m Q1) as [C2|C2];
      [ L3 m d1 a true false | L3 Q1 d1 b false true ] in
    destruct (Z_lt_le_dec Q7 Q0) as [C1|C1]; [ L2 Q7 true true false | L2 Q0 false false true ]
    end).
    all: pose proof (x42_fo_eqs q dcap o0 o1 o2 o3 i0 n HO0 P1 P2 P3 HQ0 P4 P5 HI0 HN0 P6)
           as (E0 & E1 & E2 & E3 & E7 & HQA & HQB & HQC & HQD & HQ7);
         change ((q - o0) / 10) with Q0 in E0, HQA; change ((2 * q - o1) / 10) with Q1 in E1, HQB;
         change ((3 * q - o2) / 10) with Q2 in E2, HQC; change ((dcap - o3) / 10) with Q3 in E3, HQD;
         change (i0 / 7) with Q7 in E7, HQ7; unfold id in FRK, AR, LC.
    all: lazymatch goal with
      | |- branch_taken _ _ _ = _ => fo_ez; fo_norm; rewrite ?E0, ?E1, ?E2, ?E3, ?E7; fo_br
      | |- evtF _ _ _ _ => idtac
      | |- _ => lia
      end.
    all: kx_post_regs; fo_ez; fo_norm; rewrite ?E0, ?E1, ?E2, ?E3, ?E7.
    all: kx_post_mem_free.
    all: try replace (Z_to_bv 64 (- DT + -5)) with (Z_to_bv 64 (-1 * DT + -5)) by (f_equal; lia).
    all: try replace (Z_to_bv 64 (-16)) with (Z_to_bv 64 18446744073709551600) by (apply bv_eq; vm_compute; reflexivity).
    all: lazymatch goal with
      | |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ (Z_to_bv 64 ?R) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
          first [ eapply (x42e_fo_b mm q R (-1 * DT + -5) l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3)
                | lazymatch goal with |- ?G => fail 1 "FOEAPPLY" G end ]
      end.
    all: lazymatch goal with
      | |- forall _, _ => idtac
      | |- X42PF _ => exact PV
      | |- rw_cells _ _ _ _ => eassumption
      | |- LBW _ _ => assumption
      | |- _ => try first [exact HQ | exact H3Q | eassumption | reflexivity]
      end.
    all: lazymatch goal with
      | |- forall _, _ => idtac
      | |- _ => first [ clear - C1 C2 C3 C4 HQA HQB HQC HQD HQ7 QB0 QB1 QB2 QB3 QB7; lia
                      | lazymatch goal with |- ?G => fail 1 "FOPREM" G end ]
      end.
    all: intros mm' i0' i1' i2' i3' o0' o1' o2' o3' c0' c1' c2' c3' e0' e1' e2' e3'
           y1 y7 y18 y19 y20 y22 y24 y25 y26 y28 y29 y30 y31 w'0 w'1 w'2 w'17
           PV' MU0' WM0' MI' OUT' DTB' FR' AR' LC' SRCB' GI0 GI1 GI2 GI3 GO0 GO1 GO2 GO3 GL0 GL1 GL2 GL3;
         eapply (IH mm' q (-1 * DT + -5) l1 l2 l3 i0' i1' i2' i3' o0' o1' o2' o3');
         first [exact PV' | exact FR' | exact AR' | exact LC' | exact HQ | exact H3Q | eassumption | reflexivity
               | clear - GI0 GI1 GI2 GI3 GO0 GO1 GO2 GO3 HI0 HN0 HN1 HN2 HN3 HO0 HO1 HO2 HO3 HK HQ0; lia
               | lazymatch goal with |- ?G => fail 1 "FOIH" G end ].
  Qed.

End X42E.
End CANSEC1.
