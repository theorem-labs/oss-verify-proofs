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

Lemma z4s1_md3 : forall RNG Q gp tp FR fc SP DST dcap seg DT tl mtl dl DBL DBH cbs,
  z4L_md3_goal RNG Q gp tp FR fc SP DST dcap seg DT tl mtl dl DBL DBH cbs.
Proof.
  intros RNG Q gp tp FR fc SP DST dcap seg DT tl mtl dl DBL DBH cbs CTX mm w0 w4 w5 w7 c1 c2 c3 c4 p1 p2 p3 p4
    b1 b2 b3 b4 O1 O2 O3 O4 U1 U2 U3 U4 f1 f2 f3 f4 jp1 jp2 jp3 jp4 s1 s2 s3 s4 e1 e2 e3 e4 l5 l6 l7 l8 x1 x11 x13 x28 x29
    MEM BND L5 L6 L7 L8 UU1 UU2 UU3 UU4 FF1 FF2 FF3 FF4 K.
  destruct CTX as (RS & TBL & UT1 & UT2 & UTS & UA8 & UB1 & UB2 & UDS & UDA & RT & RD & RI & A1 & A0 & A2 & A3 & A4 & A5
    & J1 & J2 & J3 & J4 & DTA & H1 & H2 & H3 & H4 & H5 & H6 & AT1 & AT2 & AS3 & AS1 & AS2 & DBA).
  destruct MEM as (C0 & C1 & C2 & C3 & CA & C8c & CB & C11 & C12 & CC & BD4 & BD3 & BD2 & BD1 & MI & TAB & TB
    & (obuf & OB & OBL) & UT & UD).
  destruct BND as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & B1 & B2 & B3 & B4 & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
  pose proof (Z_to_bv_bv_unsigned l5) as E5. remember (bv_unsigned l5) as n5 eqn:N5. clear N5. subst l5.
  pose proof (Z_to_bv_bv_unsigned l6) as E6. remember (bv_unsigned l6) as n6 eqn:N6. clear N6. subst l6.
  pose proof (Z_to_bv_bv_unsigned l7) as E7. remember (bv_unsigned l7) as n7 eqn:N7. clear N7. subst l7.
  pose proof (Z_to_bv_bv_unsigned l8) as E8. remember (bv_unsigned l8) as n8 eqn:N8. clear N8. subst l8.
  pose (u1 := U1 - O1). assert (EU1 : U1 = O1 + u1) by (unfold u1; lia). clearbody u1. subst U1.
  pose (u2 := U2 - O2). assert (EU2 : U2 = O2 + u2) by (unfold u2; lia). clearbody u2. subst U2.
  pose (u3 := U3 - O3). assert (EU3 : U3 = O3 + u3) by (unfold u3; lia). clearbody u3. subst U3.
  pose (u4 := U4 - O4). assert (EU4 : U4 = O4 + u4) by (unfold u4; lia). clearbody u4. subst U4.
  unfold AZ4_SB in *.
  assert (AIL : 4096 <= AIMG_LO /\ AIMG_LO <= AIMG_HI /\ AIMG_HI <= 2^47) by (unfold AIMG_LO, AIMG_HI; lia).
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  assert (ZT : disjoint_from [(SP + -384, SP + -104); (DST, DST + dcap)] (DT + 4) (4 * 2^tl))
    by (cbn [disjoint_from]; unfold KXGoM.apart in *; lia).
  assert (SD1 : disjoint_from [(SP + -384, SP + -104); (DST, DST + dcap)] (shad DBL) (shad (DBH - 1) + 1 - shad DBL))
    by (eapply z4m_shd_dj; [exact AS3 | lia | lia | exact AS1 | lia | lia | lia | lia | lia]).
  assert (SD2 : disjoint_from [(SP + -384, SP + -104); (DST, DST + dcap)] (shad DST) (shad (DST + dcap - 1) + 1 - shad DST))
    by (eapply z4m_shd_dj; [exact AS3 | lia | lia | exact AS1 | lia | lia | lia | lia | lia]).
  pose proof (proj2 BD4) as WB4. pose proof (proj2 BD3) as WB3. pose proof (proj2 BD2) as WB2. pose proof (proj2 BD1) as WB1.
  cbn [cells_size csize BD4A] in WB4, WB3, WB2, WB1.
  pose proof (proj2 OB) as WOB.
  kx_runFLd [585916] 2000%nat (repeat true 4096)
      [KZRange SP 8192 (2^47); KZRange DST 4096 (2^47); KZRange seg 0 (2^32); KZRange dcap 6 (2^32);
       KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange (64 - tl) 52 63; KZRange mtl 1 12; KZRange dl 0 4096; KZRange (2^tl) 2 4096;
       KZRange c1 0 (2^64 - 1); KZRange c2 0 (2^64 - 1); KZRange c3 0 (2^64 - 1); KZRange c4 0 (2^64 - 1);
       KZRange p1 0 (2^64 - 1); KZRange p2 0 (2^64 - 1); KZRange p3 0 (2^64 - 1); KZRange p4 0 (2^64 - 1);
       KZRange f1 0 88; KZRange f2 0 88; KZRange f3 0 88; KZRange f4 0 88;
       KZRange n5 1 2; KZRange n6 1 2; KZRange n7 1 2; KZRange n8 1 2;
       KZRange u1 1 2; KZRange u2 1 2; KZRange u3 1 2; KZRange u4 1 2;
       KZRange (DT + 4) 4096 (2^47); KZRange (DT + 4 + 4 * 2^tl) 4096 (2^47); KZAlign (DT + 4) 4;
       KZTab (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)]; KZIdx tl (2^tl);
       KZWord (SP + -296) 8 c4; KZWord (SP + -288) 8 c3;
       KZRange O1 4096 (2^47 - 8); KZWr O1 8; KZDisj O1 8 (DT + 4) (4 * 2^tl); KZDisj O1 8 (SP + -384) 384; KZDisj O1 8 AIMG_LO (AIMG_HI - AIMG_LO);
       KZRange O2 4096 (2^47 - 8); KZWr O2 8; KZDisj O2 8 (DT + 4) (4 * 2^tl); KZDisj O2 8 (SP + -384) 384; KZDisj O2 8 AIMG_LO (AIMG_HI - AIMG_LO);
       KZRange O3 4096 (2^47 - 8); KZWr O3 8; KZDisj O3 8 (DT + 4) (4 * 2^tl); KZDisj O3 8 (SP + -384) 384; KZDisj O3 8 AIMG_LO (AIMG_HI - AIMG_LO);
       KZRange O4 4096 (2^47 - 8); KZWr O4 8; KZDisj O4 8 (DT + 4) (4 * 2^tl); KZDisj O4 8 (SP + -384) 384; KZDisj O4 8 AIMG_LO (AIMG_HI - AIMG_LO)]
      [(DT + 4, 4 * 2^tl)]
      [(DT + 4, 4 * 2^tl); (SP + -384, 280); (O1, 8); (O2, 8); (O3, 8); (O4, 8)]
      [(DT + 4, 4 * 2^tl); (O1, 8); (O2, 8); (O3, 8); (O4, 8)].
  all: try (z4m_flat tl AS3 AS1 J2 J3).
  all: try (lazymatch goal with |- branch_taken _ _ _ = _ => z4m_br tl end).
  all: try (lazymatch goal with |- store_ok _ _ _ _ = _ => z4m_stok4 end).
  pose proof J1 as J1u. pose proof J2 as J2u. pose proof J3 as J3u. unfold KXGoM.apart in J1u, J2u, J3u.
  pose proof (munch_refl [(SP + -384, SP + -104); (DST, DST + dcap)] mm) as MUW.
  pose proof (wmono_refl bsegs mm) as WMr.
  kx_munch_wins MUW [(SP + -384, 280); (O1, 8); (O2, 8); (O3, 8); (O4, 8)].
  lazymatch goal with HLF : log_flat ?E ?l |- context [mem_denot ?E ?m ?l] =>
    assert (MI2 : mem_inv bsegs (mem_denot E m l))
      by (apply (kx_mem_inv_log bsegs E m l MI HLF); cbn [log_wr]; repeat (first [exact I | split]);
          first [ z4m_wrc tl WB4 ltac:(idtac; clear - A5 A1 A2 G1 G2 G3 G4 G5 G6 G7 G8 UU1 UU2 UU3 UU4 L5 L6 L7 L8 OBL; lia) | z4m_wrc tl WB3 ltac:(idtac; clear - A5 A1 A2 G1 G2 G3 G4 G5 G6 G7 G8 UU1 UU2 UU3 UU4 L5 L6 L7 L8 OBL; lia) | z4m_wrc tl WB2 ltac:(idtac; clear - A5 A1 A2 G1 G2 G3 G4 G5 G6 G7 G8 UU1 UU2 UU3 UU4 L5 L6 L7 L8 OBL; lia) | z4m_wrc tl WB1 ltac:(idtac; clear - A5 A1 A2 G1 G2 G3 G4 G5 G6 G7 G8 UU1 UU2 UU3 UU4 L5 L6 L7 L8 OBL; lia) | z4m_wrc tl WOB ltac:(idtac; clear - A5 A1 A2 G1 G2 G3 G4 G5 G6 G7 G8 UU1 UU2 UU3 UU4 L5 L6 L7 L8 OBL; lia) ]) end.
  kx_post_mem_free.
  lazymatch goal with HL : log_flat ?E ?l |- context [mem_denot ?E ?m ?l] =>
    pose proof (kx_u8arr_replay bsegs E m l DST obuf OB HL) as OB';
    pose proof (replay_length E l DST obuf) as OL' end.
  z4m_frame TB ltac:(idtac; clear - A5 A1 A2 A3 A4 J2u J3u G1 G2 G3 G4 G5 G6 G7 G8 UU1 UU2 UU3 UU4 L5 L6 L7 L8 TBL; lia).
  z4m_frame C0 ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 UU1 UU2 UU3 UU4 L5 L6 L7 L8; lia).
  z4m_frame C1 ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 UU1 UU2 UU3 UU4 L5 L6 L7 L8; lia).
  z4m_frame C2 ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 UU1 UU2 UU3 UU4 L5 L6 L7 L8; lia).
  z4m_frame C3 ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 UU1 UU2 UU3 UU4 L5 L6 L7 L8; lia).
  z4m_frame CA ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 UU1 UU2 UU3 UU4 L5 L6 L7 L8; lia).
  z4m_frame C8c ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 UU1 UU2 UU3 UU4 L5 L6 L7 L8; lia).
  z4m_frame CB ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 UU1 UU2 UU3 UU4 L5 L6 L7 L8; lia).
  z4m_frame C11 ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 UU1 UU2 UU3 UU4 L5 L6 L7 L8; lia).
  z4m_frame C12 ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 UU1 UU2 UU3 UU4 L5 L6 L7 L8; lia).
  z4m_frame CC ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 UU1 UU2 UU3 UU4 L5 L6 L7 L8; lia).
  unfold BD4A in BD4, BD3, BD2, BD1.
  apply (kx_rwc_cons bsegs) in BD4; destruct BD4 as [BD4c BD4]; cbn [csize] in BD4; kx_rwc_norm BD4;
    apply (kx_rwc_cons bsegs) in BD4; destruct BD4 as [BD4b BD4]; cbn [csize] in BD4; kx_rwc_norm BD4.
  apply (kx_rwc_cons bsegs) in BD3; destruct BD3 as [BD3c BD3]; cbn [csize] in BD3; kx_rwc_norm BD3;
    apply (kx_rwc_cons bsegs) in BD3; destruct BD3 as [BD3b BD3]; cbn [csize] in BD3; kx_rwc_norm BD3.
  apply (kx_rwc_cons bsegs) in BD2; destruct BD2 as [BD2c BD2]; cbn [csize] in BD2; kx_rwc_norm BD2;
    apply (kx_rwc_cons bsegs) in BD2; destruct BD2 as [BD2b BD2]; cbn [csize] in BD2; kx_rwc_norm BD2.
  apply (kx_rwc_cons bsegs) in BD1; destruct BD1 as [BD1c BD1]; cbn [csize] in BD1; kx_rwc_norm BD1;
    apply (kx_rwc_cons bsegs) in BD1; destruct BD1 as [BD1b BD1]; cbn [csize] in BD1; kx_rwc_norm BD1.
  z4m_frame BD4c ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 UU1 UU2 UU3 UU4 L5 L6 L7 L8; lia).
  z4m_frame BD3c ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 UU1 UU2 UU3 UU4 L5 L6 L7 L8; lia).
  z4m_frame BD2c ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 UU1 UU2 UU3 UU4 L5 L6 L7 L8; lia).
  z4m_frame BD1c ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 UU1 UU2 UU3 UU4 L5 L6 L7 L8; lia).
  z4m_frame BD4 ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 UU1 UU2 UU3 UU4 L5 L6 L7 L8; lia).
  z4m_frame BD3 ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 UU1 UU2 UU3 UU4 L5 L6 L7 L8; lia).
  z4m_frame BD2 ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 UU1 UU2 UU3 UU4 L5 L6 L7 L8; lia).
  z4m_frame BD1 ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 UU1 UU2 UU3 UU4 L5 L6 L7 L8; lia).
  kx_cell4w BD4b. kx_cell4w BD3b. kx_cell4w BD2b. kx_cell4w BD1b.
  lazymatch goal with |- context [mem_denot ?E _ _] =>
    let b := eval unfold E in E in
    lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
      repeat match goal with H : rw_cells _ _ _ [C4 (edenot E ?v)] |- _ => rewrite (ez_ok zv E (kE_atoms zv xs) v) in H end
    end
  end.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (mem_denot ?E ?m ?l) _) =>
    eapply evtF_eq; [| eapply (K (mem_denot E m l))] end.
  1: z4m_regs.
  all: try exact MUW.
  all: try exact WMr.
  all: try (progress unfold z4L_mem; repeat match goal with |- _ /\ _ => split end).
  all: try (lazymatch goal with |- rw_cells _ _ _ (BD4A _ _ _ _ _ _) => unfold BD4A; kx_cells_merge end).
  all: try (lazymatch goal with |- rw_cells _ _ _ _ => eassumption end).
  all: try (lazymatch goal with |- mem_inv _ _ => eassumption end).
  all: try (lazymatch goal with |- bytes_at _ _ _ _ => eassumption end).
  all: try (lazymatch goal with |- KXTac.ztab_fact _ _ _ _ _ _ => eapply w4_ztab_munch; [exact TAB | exact MUW | exact ZT | lia | lia] end).
  all: try (lazymatch goal with |- ex _ => eexists; split; [exact OB' | rewrite OL'; exact OBL] end).
  all: try (lazymatch goal with |- unpoisoned _ _ _ =>
              first [ eapply unpoisoned_munch; [exact UT | exact MUW | exact SD1]
                    | eapply unpoisoned_munch; [exact UD | exact MUW | exact SD2] ] end).
  all: try (lazymatch goal with |- _ <= _ <= _ => z4m_rng end).
Qed.

End CANSEC1.
