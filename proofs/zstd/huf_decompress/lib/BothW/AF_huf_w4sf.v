(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FuzzProducer HufPure_FseDecomp HufPure_HufX1 HufPure_HufX2.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree FseWalkKit FseWalkMem HufWalkKit HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require KXTac KXGoM KXCell.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_fa_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AH_huf_iface AF_huf_dec_iface AF_huf_fa_iface AF_huf_w4s_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_z4m AF_huf_w4m AF_huf_tbl_iface2 AF_huf_bitd AF_huf_w4s12_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_w4s3_iface AF_huf_w4s3_iface2 AF_huf_w4s3_iface3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require AF_huf_w4s0.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_w4s0f AF_huf_w4s1 AF_huf_w4s31 AF_huf_w4s32 AF_huf_w4s33 AF_huf_w4s34 AF_huf_w4s34z2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_dec4x1A AF_huf_afa6 AF_huf_w4fast AF_huf_w4fin2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).

Section CANSEC1. Context {rc : runConstT}.
Section W4SFIN.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variables (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock) (rng_fs : alayout -> footprint -> Prop).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX1) (cbs : list byte) (pdt : aptr)
            (SBL SBH : Z) (rstk : region).
  Notation SP := (bv_unsigned sp).
  Notation SPF := (SP + -480).
  Notation n := (zlen src).
  Notation seg := ((dcap + 3) / 4).
  Notation DTL := (DTABLE_BYTES mtl).
  Hypothesis AH : AHEAP AI L RNG st LB m0.
  Hypothesis NFK : forall F k, ~ In (mkABlock (ABFake 0) F k) LB.
  Hypothesis ABL : forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b).
  Hypothesis MTL : 1 <= mtl <= 12.
  Hypothesis TLM : tl <= mtl + 1.
  Hypothesis HDT : In (HB pdt DT DTL) LB.
  Hypothesis TOK : x1_table_ok cells tl.
  Hypothesis ECB : cbs = firstn (Z.to_nat (2 * 2^tl)) (x1_bytes cells).
  Hypothesis LCB : zlen cbs = 2 * 2^tl.
  Hypothesis DSTF : (DST = 0 /\ dcap = 0) \/ (exists pb, In (HB pb DST dcap) LB).
  Hypothesis DC : 0 <= dcap < 2^32.
  Hypothesis BYS : Forall (fun c => 0 <= c < 256) src.
  Hypothesis NSM : n < 2^26.
  Hypothesis S16 : 16 <= SS.
  Hypothesis SRCB : 0 < n -> exists p, In (HB p SBL (SBH - SBL)) LB /\ SBL <= SS /\ SS + n <= SBH.
  Hypothesis DJ1 : DT + DTL <= SS \/ SS + n <= DT.
  Hypothesis DJ2 : DST + dcap <= SS \/ SS + n <= DST.
  Hypothesis DJ3 : DT + DTL <= DST \/ DST + dcap <= DT.
  Hypothesis LOA : ATOP + 4096 <= lo.
  Hypothesis LOS : lo <= SP - HUF_DEC_STACK_A.
  Hypothesis SPT : SP + 16 < al_top L.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis TPA : tp = Z_to_bv 64 ATP.
  Hypothesis HINV : harness_invA m0.
  Hypothesis RCL : rclean m0 rstk.
  Hypothesis RLO : r_lo rstk <= lo.
  Hypothesis RHI : SP <= r_hi rstk.
  Hypothesis RRL : ATOP <= r_rlo rstk.
  Hypothesis RRS : rrng RNG rstk.
  Hypothesis WSK : rng RNG lo (al_top L - lo).
  Hypothesis WIM : rng_aimg RNG.
  Hypothesis WIS : rng_aimg_sh RNG.
  Hypothesis WFS : rng_fs L RNG.

  Notation DW := [(lo, SP); (DST, DST + dcap)].
  Notation POST := (huf_dec_postA AI L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB DST dcap lo m0).
  Notation FRS := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Hypothesis W4S0 : AF_huf_w4s0.w4s0c_goal AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
                      src cbs ->
                    w4_slow_goal AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT
                      mtl tl lo src cbs.

  Lemma w4sf_slow : w4_slow_goal AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT
                      mtl tl lo src cbs.
  Proof using All.
    destruct DSTF as [(E1 & E2)|(pb & HDB)].
    { apply W4S0. unfold AF_huf_w4s0.w4s0c_goal. intros. lia. }
    assert (C4 : w4s34_goal AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
                   src cbs) by (eapply w4s34_proof; first [eassumption | eapply w4s34_ck_proof; first [exact HDB | eassumption]]).
    assert (C3 : w4s33_goal AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
                   src cbs) by (eapply w4s33_proof; eassumption).
    assert (C2 : w4s32_goal AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
                   src cbs) by (eapply w4s32_proof; eassumption).
    assert (C1 : w4s2_goal AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
                   src cbs) by (eapply w4s31_proof; eassumption).
    assert (C0 : w4s1_goal AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
                   src cbs) by (eapply w4s1_proof; eassumption).
    eapply AF_huf_w4s0f.w4s0_slow; eassumption.
  Qed.
End W4SFIN.

Lemma w4f_unp : forall AI L RNG st LB m0 p A N, AHEAP AI L RNG st LB m0 -> In (HB p A N) LB -> unpoisoned m0 A (A + N).
Proof. intros AI L RNG st LB m0 p A N AH HB. exact (proj1 (hb_unpoisoned AI L RNG st LB m0 p A N AH HB)). Qed.

Lemma w4f_blk : forall AI L RNG st LB m0 p A N, AHEAP AI L RNG st LB m0 -> In (HB p A N) LB ->
  ablk A (A + N) /\ A mod 8 = 0 /\ rng RNG A N /\ rng RNG (shad A) (shlen (N + 7)).
Proof.
  intros AI L RNG st LB m0 p A N AH HB.
  destruct (AI_block AI L RNG st LB m0 p A N AH HB) as (_ & (R1 & _ & _ & R4) & W1 & W2 & _).
  split; [exact R1|]. split; [Z.div_mod_to_equations; lia|]. split; [exact W1|exact W2].
Qed.

Theorem w4_fast_proofA : w4_fast_stmtA.
Proof.
  unfold w4_fast_stmtA.
  intros AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs
    pdt SBL SBH rstk AH NFK ABL MTL TLM HDT TOK ECB LCB DSTF DC BYS NSM S16 SRCB DJ1 DJ2 DJ3 LOA LOS SPT SP16 TPA HINV
    RCL RLO RHI RRL RRS WSK WIM WIS WFS.
  unfold w4fa_goal.
  intros w0 w8 w16 w24 w32 w64 w96 j256 j296 j336 b0 b1 b2 b3 mm x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
    WF TL11 N10 J0 J2 J4 JS DCP DC3 HB0 HB1 HB2 HB3 MB0 MB1 MB2 MB3.
  destruct DSTF as [(E1 & E2)|(pb & HDB)]; [lia|].
  destruct (SRCB ltac:(lia)) as (psb & HSB & SB1 & SB2).
  pose proof (w4f_blk AI L RNG st LB m0 pdt DT (DTABLE_BYTES mtl) AH HDT) as (_ & _ & WDT & WDTS).
  pose proof (w4f_blk AI L RNG st LB m0 pb DST dcap AH HDB) as (_ & _ & WDB & WDBS).
  pose proof (w4f_blk AI L RNG st LB m0 psb SBL (SBH - SBL) AH HSB) as (SBA1 & SBA2 & WSB & WSBS).
  replace (SBL + (SBH - SBL)) with SBH in SBA1 by lia.
  pose proof (w4f_unp AI L RNG st LB m0 pdt DT (DTABLE_BYTES mtl) AH HDT) as UDT.
  pose proof (w4f_unp AI L RNG st LB m0 pb DST dcap AH HDB) as UDB.
  pose proof (w4f_unp AI L RNG st LB m0 psb SBL (SBH - SBL) AH HSB) as USB.
  replace (SBL + (SBH - SBL)) with SBH in USB by lia.
  assert (FX : w4fx_goal AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
                 src cbs).
  { eapply (w4fx_ok AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs
              pdt pb SBL SBH rstk).
    all: first [ eassumption | unfold KXGoM.apart; lia | lia ]. }
  eapply (w4_fast AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs
            pdt pb SBL SBH rstk).
  all: first [ eassumption | exact (conj SB1 SB2) | exact (conj SBA1 SBA2) | unfold KXGoM.apart; lia
             | rewrite LCB, TL11; reflexivity | lia ].
Qed.

Theorem w4_slow_proofA : w4_slow_stmtA.
Proof.
  unfold w4_slow_stmtA. intros.
  eapply w4sf_slow; try eassumption.
  eapply AF_huf_w4s0.w4s0_slow; eassumption.
Qed.

Theorem dec_4x1_closedA : forall (AI : AMallocIface) (rng_fs : alayout -> footprint -> Prop),
  dec4_int_stmtA AI rng_fs x1_tabA AHUF_DX1_4X.
Proof. intros AI rng_fs. exact (dec_4x1_proofA AI rng_fs w4_slow_proofA fast_args_proofA w4_fast_proofA). Qed.
End CANSEC1.
