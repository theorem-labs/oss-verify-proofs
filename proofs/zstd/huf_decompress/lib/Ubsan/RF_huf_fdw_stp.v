From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_FseDecompRT.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit HufWalkKit STRW_tac.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_iface RF_huf_tbl_iface RF_huf_tbl_kit RF_huf_fdw_kit
  RF_huf_bdt_model RF_huf_fdw_stl RF_huf_fdw_kit_dsym RF_huf_fdw_cut.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac slia ::= slia_sep.

Section STP.
  Variables (SP : Z) (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem) (S DT DST dcap lo : Z) (bs : list Z)
            (dt : dtable) (POST : machine_state -> Prop).
  Hypothesis PRE : fdw_pre SP S DT DST dcap lo bs dt.

  Notation tl := (dt_tableLog dt).
  Notation STF pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation STH pc mm x1 j0 j x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (STF pc mm x1 (Z_to_bv 64 64) (Z_to_bv 64 (-1)) (Z_to_bv 64 (DST + j)) (Z_to_bv 64 DST)
         (Z_to_bv 64 (2^61)) (Z_to_bv 64 (-70)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 1) (Z_to_bv 64 1)
         (Z_to_bv 64 (DST + dcap + -2)) (Z_to_bv 64 (2^64 - 1 - BIT_MASK_TAB)) (Z_to_bv 64 2) (Z_to_bv 64 (DST + j + 1))
         (Z_to_bv 64 (2^16 - 1)) (Z_to_bv 64 BIT_MASK_TAB) (Z_to_bv 64 (DST + j0)) (Z_to_bv 64 (j0 - j))
         x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Notation TIb m out s1 s2 d := (exists jp, fdw_mem m0 m SP S DT DST dcap lo bs dt (mkDec out s1 s2 d) jp).

  Ltac stp_step := repeat (lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x20828) _ _ _ _) => fail
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1fe1c) _ _ _ _) => fail
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x20450) _ _ _ _) => fail
    | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep end).
  Ltac stp_walk := repeat (stp_step; fd_brk; try (exfalso; fd_clr; lia)); stp_step.
  Ltac stp_open MEM := pose proof PRE as PRE';
    destruct PRE' as (HTL & HCL & HCOK & HBY & HLO & HSP16 & HSPT & HS8 & HSE & HDT0 & HDT4 & HDTE & HD4 & HDE & HDC
                      & DJ1 & DJ2 & DJ3);
    let M := fresh "MEM" in pose proof MEM as M; unfold fdw_mem, sm_inv in M; cbn [de_out de_s1 de_s2 de_bd] in M;
    destruct M as (FS2 & FS1 & FBD & ((junk & OUTA & LJ) & MU & WM & MI) & TBB & SRCB & STK).


  Ltac stp_close KE KL := lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x20450) _ _ _ _) =>
        unfold fdw_K in KE; eapply KE;
        [ lia | eassumption | eassumption | eassumption | eassumption
        | unfold dres; split; [reflexivity | vm_compute; split; reflexivity] ]
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1fe1c) _ _ _ _) => apply KL; lia
    end.


  (* [comment removed for export] *)
  Lemma stp_tprep : forall m1 out s1 s2 d jp (y1 y5 y6 y7 y10 y15 y16 y17 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word),
    fdw_mem m0 m1 SP S DT DST dcap lo bs dt (mkDec out s1 s2 d) jp -> zlen out <= dcap ->
    (dcap - 2 < zlen out -> fdw_K SP gp tp F fc m0 DST dcap lo POST (Err ZSTD_error_dstSize_tooSmall)) ->
    (zlen out + 2 <= dcap -> forall (z1 z23 z24 z25 z26 z27 z28 z29 z30 z31 : word),
       evt usegs POST (STH 0x1fe1c m1 z1 (zlen out) (zlen out) z23 z24 z25 z26 z27 z28 z29 z30 z31)) ->
    evt usegs POST (MS (mkR y1 (Z_to_bv 64 SP) gp tp y5 y6 y7 (Z_to_bv 64 DST) (Z_to_bv 64 (2^61)) y10
                            (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 1) (Z_to_bv 64 1) y15 y16 y17
                            (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (2^16 - 1)) (Z_to_bv 64 BIT_MASK_TAB)
                            (Z_to_bv 64 (DST + zlen out)) y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
                        F (Z_to_bv 64 PFDW_T1) fc None m1 (seg_rom usegs)).
  Proof using All.
    intros until y31. intros MEM OL KE KL. stp_open MEM.
    unfold PFDW_T1. stp_walk.
    all: try replace (Z_to_bv 64 0) with (Z_to_bv 64 (zlen out - zlen out)) by (f_equal; lia).
    all: try stp_close KE KL.
  Qed.

  (* [comment removed for export] *)
  Lemma stp_j2 : forall m1 out s1 s2 d j0 j (x1 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    TIb m1 out s1 s2 d -> zlen out = j + 2 -> 0 <= j -> j + 2 <= dcap ->
    (dcap - 2 < zlen out -> fdw_K SP gp tp F fc m0 DST dcap lo POST (Err ZSTD_error_dstSize_tooSmall)) ->
    (zlen out + 2 <= dcap -> forall y28 : word,
       evt usegs POST (STH 0x1fe1c m1 x1 j0 (j + 2) x23 x24 x25 x26 x27 y28 x29 x30 x31)) ->
    evt usegs POST (STH 0x1fe08 m1 x1 j0 j x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof using All.
    intros until x31. intros (jp & MEM) OL J0 J2 KE KL. stp_open MEM.
    stp_walk.
    all: try replace (Z_to_bv 64 (j0 - j + -2)) with (Z_to_bv 64 (j0 - (j + 2))) by (f_equal; lia).
    all: try replace (Z_to_bv 64 (DST + j + 3)) with (Z_to_bv 64 (DST + (j + 2) + 1)) by (f_equal; lia).
    all: try replace (Z_to_bv 64 (DST + j + 2)) with (Z_to_bv 64 (DST + (j + 2))) by (f_equal; lia).
    all: try stp_close KE KL.
  Qed.
End STP.
