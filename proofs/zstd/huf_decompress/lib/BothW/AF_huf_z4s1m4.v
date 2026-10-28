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
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_w4s3b.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_z4s1_iface AF_huf_z4s1mk.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.

Ltac z4f_stok8at H o :=
  lazymatch goal with
  | |- store_ok ?segs ?m (adenot ?E ?a) 8 = true =>
      let b := eval unfold E in E in
      lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
        eapply (rw_cells_store_ok_at segs m _ _ o _ 8%nat _ H eq_refl eq_refl);
        rewrite adenot_wa; f_equal; change E with (kE zv xs); kx_estart_z zv
      end
  end.

Ltac z4f_fr F H := z4m_frame H ltac:(idtac; clear - F; lia).

Section Z4L.
  Variables (RNG : footprint) (Q : machine_state -> Prop) (gp tp : word) (FR : bvmap 5 word) (fc : bv 32).
  Variables (SP DST dcap seg DT tl mtl dl DBL DBH : Z) (cbs : list byte).

  Lemma z4s1_md4 : z4L_md4_goal RNG Q gp tp FR fc SP DST dcap seg DT tl mtl dl DBL DBH cbs.
  Proof.
    unfold z4L_md4_goal, z4L_ctx, z4L_mem, z4L_bnd.
    intros (RS & TBL & UT1 & UT2 & UTS & UA8 & UB1 & UB2 & UDS & UDA & RT & RD & RI & A1 & A0 & A2 & A3 & A4 & A5 &
            J1 & J2 & J3 & J4 & DTA & H1 & H2 & H3 & H4 & H5 & H6 & AT1 & AT2 & AS3 & AS1 & AS2 & ATD)
      mm w0 w4 w5 w7 c1 c2 c3 c4 p1 p2 p3 p4 b1 b2 b3 b4 O1 O2 O3 O4 V1 V2 V3 V4 g1 g2 g3 g4
      jp1 jp2 jp3 jp4 s1 s2 s3 s4 e1 e2 e3 e4 l9 l10 l11 l12 x11 x13 x26 x27 x29
      (C0 & C1 & C2 & C3 & CA & C8c & CB & C11 & C12 & CC & BD4 & BD3 & BD2 & BD1 & MI & TAB & TB & (obuf & OB & OBL) & UT & UD)
      (Bc1 & Bc2 & Bc3 & Bc4 & Bp1 & Bp2 & Bp3 & Bp4 & Bb1 & Bb2 & Bb3 & Bb4 & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8)
      L9 L10 L11 L12 V1R V2R V3R V4R G1 G2 G3 G4 K.
    unfold AZ4_SB in *.
    assert (AIL : 4096 <= AIMG_LO /\ AIMG_LO <= AIMG_HI /\ AIMG_HI <= 2^47) by (unfold AIMG_LO, AIMG_HI; lia).
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    assert (exists u1, V1 = O1 + u1 /\ 2 <= u1 <= 4) as (u1 & -> & U1R) by (exists (V1 - O1); lia).
    assert (exists u2, V2 = O2 + u2 /\ 2 <= u2 <= 4) as (u2 & -> & U2R) by (exists (V2 - O2); lia).
    assert (exists u3, V3 = O3 + u3 /\ 2 <= u3 <= 4) as (u3 & -> & U3R) by (exists (V3 - O3); lia).
    assert (exists u4, V4 = O4 + u4 /\ 2 <= u4 <= 4) as (u4 & -> & U4R) by (exists (V4 - O4); lia).
    clear V1R V2R V3R V4R.
    assert (ZT : disjoint_from [(SP + -384, SP + -104); (DST, DST + dcap)] (DT + 4) (4 * 2^tl))
      by (cbn [disjoint_from]; unfold KXGoM.apart in *; lia).
    assert (SD1 : disjoint_from [(SP + -384, SP + -104); (DST, DST + dcap)] (shad DBL) (shad (DBH - 1) + 1 - shad DBL))
      by (eapply z4m_shd_dj; [exact AS3 | lia | lia | exact AS1 | lia | lia | lia | lia | lia]).
    assert (SD2 : disjoint_from [(SP + -384, SP + -104); (DST, DST + dcap)] (shad DST) (shad (DST + dcap - 1) + 1 - shad DST))
      by (eapply z4m_shd_dj; [exact AS3 | lia | lia | exact AS1 | lia | lia | lia | lia | lia]).
    pose proof (proj2 BD4) as WB4. pose proof (proj2 BD3) as WB3. pose proof (proj2 BD2) as WB2. pose proof (proj2 BD1) as WB1.
    cbn [cells_size csize BD4A] in WB4, WB3, WB2, WB1.
    pose proof (proj2 CA) as WCA. cbn [cells_size csize] in WCA.
    pose proof (proj2 OB) as WOB.
    kx_runFLd [586648] 2000%nat (repeat true 4096)
        [KZRange SP 8192 (2^47); KZRange DST 4096 (2^47); KZRange seg 0 (2^32); KZRange dcap 6 (2^32);
         KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange (64 - tl) 52 63; KZRange mtl 1 12; KZRange dl 0 4096; KZRange (2^tl) 2 4096;
         KZRange c1 0 (2^64 - 1); KZRange c2 0 (2^64 - 1); KZRange c3 0 (2^64 - 1); KZRange c4 0 (2^64 - 1);
         KZRange p1 0 (2^64 - 1); KZRange p2 0 (2^64 - 1); KZRange p3 0 (2^64 - 1); KZRange p4 0 (2^64 - 1);
         KZRange b1 0 64; KZRange b2 0 64; KZRange b3 0 64; KZRange b4 0 64;
         KZRange g1 0 100; KZRange g2 0 100; KZRange g3 0 100; KZRange g4 0 100;
         KZRange (bv_unsigned l9) 1 2; KZRange (bv_unsigned l10) 1 2; KZRange (bv_unsigned l11) 1 2; KZRange (bv_unsigned l12) 1 2;
         KZRange (DT + 4) 4096 (2^47); KZRange (DT + 4 + 4 * 2^tl) 4096 (2^47); KZAlign (DT + 4) 4;
         KZTab (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)]; KZIdx tl (2^tl);
         KZWord (SP + -376) 8 (DST + 3 * seg); KZWord (SP + -368) 8 dl; KZWord (SP + -360) 8 (DST + dcap - 7);
         KZWord (SP + -320) 8 c2; KZWord (SP + -296) 8 c4; KZWord (SP + -288) 8 c3;
         KZWord (SP + -336) 8 (DST + dcap); KZWord (SP + -312) 8 (DST + seg); KZWord (SP + -304) 8 (DST + 2 * seg);
         KZWord (SP + -280) 8 (DT + 4); KZWord (SP + -272) 8 dcap;
         KZWord (SP + -144) 8 c1; KZWord (SP + -184) 8 c2; KZWord (SP + -224) 8 c3; KZWord (SP + -264) 8 c4;
         KZWord (SP + -128) 8 p1; KZWord (SP + -168) 8 p2; KZWord (SP + -208) 8 p3; KZWord (SP + -248) 8 p4;
         KZRange u1 2 4; KZRange u2 2 4; KZRange u3 2 4; KZRange u4 2 4;
         KZRange O1 4096 (2^47 - 8); KZWr O1 8; KZDisj O1 8 (DT + 4) (4 * 2^tl); KZDisj O1 8 (SP + -384) 384; KZDisj O1 8 AIMG_LO (AIMG_HI - AIMG_LO);
         KZRange O2 4096 (2^47 - 8); KZWr O2 8; KZDisj O2 8 (DT + 4) (4 * 2^tl); KZDisj O2 8 (SP + -384) 384; KZDisj O2 8 AIMG_LO (AIMG_HI - AIMG_LO);
         KZRange O3 4096 (2^47 - 8); KZWr O3 8; KZDisj O3 8 (DT + 4) (4 * 2^tl); KZDisj O3 8 (SP + -384) 384; KZDisj O3 8 AIMG_LO (AIMG_HI - AIMG_LO);
         KZRange O4 4096 (2^47 - 8); KZWr O4 8; KZDisj O4 8 (DT + 4) (4 * 2^tl); KZDisj O4 8 (SP + -384) 384; KZDisj O4 8 AIMG_LO (AIMG_HI - AIMG_LO);
         KZWr (SP + -256) 4; KZWr (SP + -216) 4; KZWr (SP + -176) 4; KZWr (SP + -136) 4; KZWr (SP + -344) 8]
        [(DT + 4, 4 * 2^tl)]
        [(DT + 4, 4 * 2^tl); (SP + -384, 280); (O1, 8); (O2, 8); (O3, 8); (O4, 8)]
        [(DT + 4, 4 * 2^tl); (O1, 8); (O2, 8); (O3, 8); (O4, 8)].
    all: try (z4m_flat tl AS3 AS1 J2 J3).
    all: try (lazymatch goal with |- branch_taken _ _ _ = _ => z4m_br tl end).
    all: try (lazymatch goal with |- store_ok _ _ _ 4 = _ => z4m_stok4 end).
    all: try (lazymatch goal with |- store_ok _ _ _ 8 = _ => z4f_stok8at CA 8%nat end).
    pose proof J1 as J1u. pose proof J2 as J2u. pose proof J3 as J3u. unfold KXGoM.apart in J1u, J2u, J3u.
    pose proof (conj A5 (conj A1 (conj A2 (conj J1u (conj Q1 (conj Q2 (conj Q3 (conj Q4 (conj Q5 (conj Q6 (conj Q7 (conj Q8
      (conj U1R (conj U2R (conj U3R (conj U4R (conj L9 (conj L10 (conj L11 L12))))))))))))))))))) as FB.
    pose proof (munch_refl [(SP + -384, SP + -104); (DST, DST + dcap)] mm) as MUW.
    pose proof (wmono_refl bsegs mm) as WMr.
    kx_munch_wins MUW [(SP + -384, 280); (O1, 8); (O2, 8); (O3, 8); (O4, 8)].
    kx_post_mem_free.
    lazymatch goal with HL : log_flat ?E ?l |- context [mem_denot ?E ?m ?l] =>
      pose proof (kx_u8arr_replay bsegs E m l DST obuf OB HL) as OB';
      pose proof (replay_length E l DST obuf) as OL' end.
    z4m_frame TB ltac:(idtac; clear - A5 A1 A2 A3 A4 J2u J3u FB TBL; lia).
    z4f_fr FB C0. z4f_fr FB C1. z4f_fr FB C2. z4f_fr FB C3. z4f_fr FB C8c.
    z4f_fr FB CB. z4f_fr FB C11. z4f_fr FB C12. z4f_fr FB CC.
    apply (kx_rwc_cons bsegs) in CA; destruct CA as [CAa CA]; cbn [csize] in CA; kx_rwc_norm CA;
      apply (kx_rwc_cons bsegs) in CA; destruct CA as [CAb CA]; cbn [csize] in CA; kx_rwc_norm CA.
    z4f_fr FB CAa. z4f_fr FB CA.
    unfold BD4A in BD4, BD3, BD2, BD1.
    apply (kx_rwc_cons bsegs) in BD4; destruct BD4 as [BD4c BD4]; cbn [csize] in BD4; kx_rwc_norm BD4;
      apply (kx_rwc_cons bsegs) in BD4; destruct BD4 as [BD4b BD4]; cbn [csize] in BD4; kx_rwc_norm BD4.
    apply (kx_rwc_cons bsegs) in BD3; destruct BD3 as [BD3c BD3]; cbn [csize] in BD3; kx_rwc_norm BD3;
      apply (kx_rwc_cons bsegs) in BD3; destruct BD3 as [BD3b BD3]; cbn [csize] in BD3; kx_rwc_norm BD3.
    apply (kx_rwc_cons bsegs) in BD2; destruct BD2 as [BD2c BD2]; cbn [csize] in BD2; kx_rwc_norm BD2;
      apply (kx_rwc_cons bsegs) in BD2; destruct BD2 as [BD2b BD2]; cbn [csize] in BD2; kx_rwc_norm BD2.
    apply (kx_rwc_cons bsegs) in BD1; destruct BD1 as [BD1c BD1]; cbn [csize] in BD1; kx_rwc_norm BD1;
      apply (kx_rwc_cons bsegs) in BD1; destruct BD1 as [BD1b BD1]; cbn [csize] in BD1; kx_rwc_norm BD1.
    z4f_fr FB BD4c. z4f_fr FB BD3c. z4f_fr FB BD2c. z4f_fr FB BD1c.
    z4f_fr FB BD4. z4f_fr FB BD3. z4f_fr FB BD2. z4f_fr FB BD1.
    kx_cell4w BD4b. kx_cell4w BD3b. kx_cell4w BD2b. kx_cell4w BD1b. kx_cellw CAb.
    lazymatch goal with |- context [mem_denot ?E _ _] =>
      let b := eval unfold E in E in
      lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
        repeat match goal with
        | H : rw_cells _ _ _ [C4 (edenot E ?v)] |- _ => rewrite (ez_ok zv E (kE_atoms zv xs) v) in H
        | H : rw_cells _ _ _ [C8 (edenot E ?v)] |- _ => rewrite (ez_ok zv E (kE_atoms zv xs) v) in H
        end
      end
    end.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (mem_denot ?E ?m ?l) _) =>
      eapply evtF_eq; [| eapply (K (mem_denot E m l))] end.
    1: z4m_regs.
    all: try exact MUW.
    all: try exact WMr.
    all: try (lazymatch goal with |- rw_cells _ _ _ _ /\ _ =>
                repeat match goal with |- ?A /\ _ => lazymatch A with _ <= _ => fail | _ => split end end end).
    all: try (lazymatch goal with |- rw_cells _ _ _ (BD4A _ _ _ _ _ _) => unfold BD4A; kx_cells_merge end).
    all: try (lazymatch goal with |- rw_cells _ _ _ [C8 _; C8 _; C8 _; C8 _] => kx_cells_merge end).
    all: try (lazymatch goal with |- rw_cells _ _ _ _ => eassumption end).
    all: try (lazymatch goal with |- mem_inv _ _ => eassumption end).
    all: try (lazymatch goal with |- bytes_at _ _ _ _ => eassumption end).
    all: try (lazymatch goal with |- KXTac.ztab_fact _ _ _ _ _ _ => eapply w4_ztab_munch; [exact TAB | exact MUW | exact ZT | lia | lia] end).
    all: try (lazymatch goal with |- ex _ => eexists; split; [exact OB' | rewrite OL'; exact OBL] end).
    all: try (lazymatch goal with |- unpoisoned _ _ _ =>
                first [ eapply unpoisoned_munch; [exact UT | exact MUW | exact SD1]
                      | eapply unpoisoned_munch; [exact UD | exact MUW | exact SD2] ] end).
    all: try (lazymatch goal with |- _ <= _ <= _ => z4m_rng end).
    all: lazymatch goal with |- _ <= bv_unsigned (ev _ ?j) <= _ => let H := fresh "RG" in kx_range (EVar j) H; lia end.
  Qed.
End Z4L.
End CANSEC1.
