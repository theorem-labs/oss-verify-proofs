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
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_x2t_hdefs AF_huf_z4f_defs.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

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
  Hypothesis TL11 : tl = 11.
  Hypothesis FI7 : x42e_fi7_stmt RNG gp tp F fc m0 SPV DST dcap SRC n DT src dtb POST.
  Notation z4fI := (AF_huf_z4f_defs.z4fI m0 SPV DST dcap SRC DT src dtb).

  Lemma x42e_fi6 : x42e_fi6_stmt RNG gp tp F fc m0 SPV DST dcap SRC n DT src dtb POST.
  Proof using CTX X2OK NBOK ACTX TL11 FI7.
    pose proof CTX as CTX'. x42e_ctx_open CTX'. pose proof ACTX as ACTX'. x42e_actx_open ACTX'.
    unfold x42e_fi6_stmt.
    intros r mb mm q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 u0 u1 u2 ix c0 c1 c2 c3 e0 e1 e2 e3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11
      x1 x6 x17 x18 x19 x24 x25
      w0 w1 w2
      MU WM MU0 WM0 MI OUT DTBb FR AR LC SRCB HND HR HOL HO0 HO1 HO2 HO3 HE0 HE1 HE2 HE3 HQ3 HQ0 HOLR HI0 HI1 HI2 HI3 HN0 HN1 HN2 HN3 HL1 HL2 HL3 HLN
      HU0 HU1 HU2 HIX HLBc0 HLBc1 HLBc2 HLBc3 KH KO. subst nd.
    destruct R1 as (R1a & R1b & R1c). destruct R2 as (R2a & R2b & R2c). destruct R3 as (R3a & R3b).
    assert (KF : 0 < dcap) by lia.
    assert (DTB8 : 8196 <= DTB) by (rewrite TL11 in DTBF; cbn in DTBF; lia).
    specialize (UDST KF). specialize (RDST KF). specialize (RDSTS KF).
    assert (TF : ztab_fact bsegs mm (DT + 4) 8192 4 [(2, 0, 11); (3, 1, 2)]) by (eapply x42f_tab; eassumption).
    assert (UQ : unpoisoned mm SRC (SRC + n) /\ unpoisoned mm DT (DT + DTB) /\ (0 < dcap -> unpoisoned mm DST (DST + dcap)))
      by (eapply x42f_unp; eassumption).
    destruct UQ as (USm & UDTm & UDSTm). specialize (UDSTm KF).
    assert (WRS : forall A k, DST <= A -> A + k <= DST + dcap -> 0 <= k -> wr_at bsegs mm A k)
      by (intros A k ? ? ?; destruct OUT as (OL0 & OH0 & OS); unfold wr_at; split; [lia|]; split; [lia|];
          intros i Hi; apply (OS (A + i)); lia).
    assert (WA0 : wr_at bsegs mm (DST + u0) 2) by (apply WRS; lia).
    assert (WA1 : wr_at bsegs mm (DST + u1) 2) by (apply WRS; lia).
    assert (RW0 : rng RNG (DST + u0) 2) by (apply (rng_sub RNG DST dcap); [exact RDST | lia | lia]).
    assert (RW1 : rng RNG (DST + u1) 2) by (apply (rng_sub RNG DST dcap); [exact RDST | lia | lia]).
    clear WRS.
    pose proof (bv_unsigned_in_range _ c1) as RGc1. pose proof (bv_unsigned_in_range _ c2) as RGc2.
    pose proof (bv_unsigned_in_range _ c0) as RGc0. pose proof (bv_unsigned_in_range _ c3) as RGc3.
    change (bv_modulus 64) with (2 ^ 64) in RGc0, RGc1, RGc2, RGc3.
    unfold shspan in RDTS, RDSTS.
    set (ND := 2^64 - DT - 5).
    replace (Z_to_bv 64 (-1 * DT + -5)) with (Z_to_bv 64 ND) by (apply bv_eq; rewrite !Z_to_bv_unsigned; unfold ND, bv_wrap, bv_modulus;
      Z.div_mod_to_equations; lia).
    assert (NDR : 2^64 - 2^47 <= ND <= 2^64 - 4101) by (unfold ND; lia).
    assert (NDE : Z_to_bv 64 ND = Z_to_bv 64 (-1 * DT + -5)) by (apply bv_eq; rewrite !Z_to_bv_unsigned; unfold ND, bv_wrap, bv_modulus;
      Z.div_mod_to_equations; lia).
    clearbody ND.
    kx_runFm [0x85e44] 140%nat
      [KZRange DT 4096 (2^47); KZRange (DT + DTB) 4096 (2^47); KZAlign DT 4; KZRange ND (2^64 - 2^47) (2^64 - 4101);
       KZRange ix 0 2047; KZAlign (4 * ix) 4;
       KZRange DST 4096 (2^47); KZRange dcap 1 (2^47); KZRange u0 0 (2^47); KZRange u1 0 (2^47); KZRange (DST + u0) 4096 (2^47); KZRange (DST + u1) 4096 (2^47);
       KZRange (DST + dcap - (DST + u0)) 2 (2^47); KZRange (DST + dcap - (DST + u1)) 2 (2^47);
       KZRange SPV 4096 (2^47);
       KZTab (DT + 4) 8192 4 [(2, 0, 11); (3, 1, 2)];
       KZWr (DST + u0) 2; KZWr (DST + u1) 2; KZWr (SPV + -232) 128;
       KZDisj (DST + u0) 2 (DT + 4) 8192; KZDisj (DST + u1) 2 (DT + 4) 8192; KZDisj (SPV + -232) 128 (DT + 4) 8192]
      [(DT + 4, 8192)] [(DST + u0, 2); (DST + u1, 2); (SPV + -232, 128)] [(DT + 4, 8192); (DST + u0, 2); (DST + u1, 2)].
    all: try z4fshd.
    all: try (z4facc RDT).
    kx_post_regs_keep.
    rewrite NDE.
    kx_erange R35 (EVar 35). kx_erange R36 (EVar 36). kx_erange R43 (EVar 43). kx_erange R44 (EVar 44).
    lazymatch goal with |- context [mem_denot ?E _ _] => cbn [mem_denot]; z4fan E end.
    lazymatch goal with FRh : rw_cells _ mm (SPV + -528) ?fr, ARh : rw_cells _ mm (SPV + -384) ?ar, LCh : rw_cells _ mm (SPV + -232) ?cs |- _ =>
      assert (I0 : z4fI mb mm fr ar cs) by (unfold z4fI; z4fsplit 12%nat; first [eassumption | reflexivity]) end.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?M _) => z4fmem M end.
    lazymatch goal with I0 : z4fI _ ?M ?fr ?ar ?cs |- _ =>
      destruct I0 as (MU' & WM' & MU0' & WM0' & MI' & STK' & DTB' & SRC' & FR' & AR' & LC' & LFR' & LAR') end.
    rewrite ?Z_to_bv_bv_unsigned in *.
    eapply (FI7 r mb _ q OL (-1 * DT + -5) l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 _ _ u2 _ _ _ c2 c3 e0 e1 e2 e3
              av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 _ c1 _ _ x19 _ _ w0 w1 w2).
    all: try eassumption.
    all: try reflexivity.
    all: cbn [edenot] in R35, R36, R43, R44.
    all: try (clear - R36 HU0; lia).
    all: try (clear - R44 HU1; lia).
    all: try (change (2 ^ (53 mod 64)) with (2 ^ 53); rewrite (Z.mod_small (bv_unsigned c2) (2 ^ 64)) by (clear - RGc2; lia);
        pose proof (z4f_div_rng (bv_unsigned c2) 53 ltac:(clear - RGc2; lia) ltac:(lia)) as DV0;
        change (2 ^ (64 - 53)) with 2048 in DV0; clear - DV0; lia).
    all: lazymatch goal with |- LBW _ (edenot (kE ?zv ?xs) _) => e42_lb_chain (kE_atoms zv xs) end.
  Qed.

End X42E.
End CANSEC1.
