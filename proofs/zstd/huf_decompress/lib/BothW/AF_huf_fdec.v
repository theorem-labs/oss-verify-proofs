(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import Shadow.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_tbl_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require RF_huf_tbl_kit RF_huf_fdw_kit RF_huf_fdw_sm RF_huf_fdw_pure RF_huf_fdw_st RF_huf_fdw_fm.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_bdt_model.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase RtCells Stdio_kit AHarness_iface AF_huf_tbl_iface AF_huf_bdt_kit
  AF_huf_tbl_iface2 AF_huf_fdw_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require AF_fse_rd_base.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_fse_rd_mem AF_huf_fdw_seg AF_huf_fdw_top1 AF_huf_ids AF_huf_bit AF_huf_sdec.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_reloadi.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require AF_huf_fdm AF_huf_fdt AF_huf_fdec1 AF_huf_fdec2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw FseRdKit HufWalkKit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require FseWalkKit FseRdKit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_hint ::= bdtA_acc_hint.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.

Section FDEC.
  Variables (RNG : footprint) (Q : machine_state -> Prop) (m0 : amem) (SPV FF DST dcap S0 DT lo RLO RHI : Z) (bs : list Z)
            (d : dtable) (gp tp : word) (FR : bvmap 5 word) (fc : bv 32) (j48 jd : list byte).
  Notation SP1 := (SPAf SPV).
  Notation tl := (dt_tableLog d).
  Notation FRC := [C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 2147450880)].
  Hypothesis FC32 : rw_cells bsegs m0 (SP1 + 32) FRC.
  Hypothesis FO : rw_cells bsegs m0 (SP1 + 80) [CB 72 j48].
  Hypothesis STK : stk bsegs m0 lo SP1.
  Hypothesis BOT : ATOP + 4096 <= lo.
  Hypothesis LO : lo <= SP1 - DEC_STACK.
  Hypothesis SP16 : SPV mod 16 = 0.
  Hypothesis SPH : SPV + 16 <= 2^47.
  Hypothesis ZOBJ : zshadow m0 (SP1 + 80) 72.
  Hypothesis SHC : shclean m0 (SP1 + 112) (SP1 + 152) RLO RHI.
  Hypothesis RRH : rng RNG (shad RLO) (shad RHI - shad RLO).
  Hypothesis RO : rng RNG (SP1 + 80) 72.
  Hypothesis ROs : rng RNG (shad (SP1 + 80)) 9.
  Hypothesis RO32 : rng RNG (SP1 + 32) 32.
  Hypothesis HTL : 5 <= tl <= 12.
  Hypothesis HCELLS : zlen (dt_cells d) = 2^tl.
  Hypothesis HCOK : RF_huf_fdw_sm.cells_ok tl (dt_cells d).
  Hypothesis FM : dt_fastMode d = 1.
  Hypothesis DTH : rw_cells bsegs m0 DT [C2 (Z_to_bv 64 tl); C2 (Z_to_bv 64 1)].
  Hypothesis TBB : bytes_at bsegs m0 (DT + 4) (concat (map fse_cell_bytes (dt_cells d))).
  Hypothesis HDT : ablk DT (DT + 4 + 4 * 2^tl).
  Hypothesis DT4 : DT mod 4 = 0.
  Hypothesis ZDT : zshadow m0 DT (4 + 4 * 2^tl).
  Hypothesis RDT : rng RNG DT (4 + 4 * 2^tl).
  Hypothesis RDTs : rng RNG (shad DT) (nshad (4 + 4 * 2^tl + DT mod 8)).
  Hypothesis SRC : bytes_at bsegs m0 S0 (map (Z_to_bv 8) bs).
  Hypothesis BY : Forall (fun c => 0 <= c < 256) bs.
  Hypothesis NS : zlen bs <= 65536.
  Hypothesis HS0 : ablk S0 (S0 + zlen bs).
  Hypothesis S8 : S0 + 8 <= 2^47.
  Hypothesis S16 : 16 <= S0.
  Hypothesis USRC : unpoisoned m0 S0 (S0 + zlen bs).
  Hypothesis RS : rng RNG S0 (zlen bs).
  Hypothesis RSs : rng RNG (shad S0) (nshad (zlen bs + S0 mod 8)).
  Hypothesis RESOK : dres_ok (decompress_usingDTable bs d dcap true).
  Hypothesis OUTA : u8arr bsegs m0 DST jd.
  Hypothesis LJD : zlen jd = dcap.
  Hypothesis DC : 0 <= dcap <= 255.
  Hypothesis HDST : ablk DST (DST + dcap).
  Hypothesis DST3 : 3 <= DST.
  Hypothesis ZDST : zshadow m0 DST dcap.
  Hypothesis RDST : rng RNG DST dcap.
  Hypothesis RDSTs : rng RNG (shad DST) (nshad (dcap + DST mod 8)).
  Hypothesis DJ2 : DST + dcap <= S0 \/ S0 + zlen bs <= DST.
  Hypothesis DJ1 : DST + dcap <= DT \/ DT + 4 + 4 * 2^tl <= DST.
  Hypothesis DJ3 : S0 + zlen bs <= DT \/ DT + 4 + 4 * 2^tl <= S0.
  Hypothesis MI : mem_inv bsegs m0.
  Hypothesis RTC : artcells m0.
  Hypothesis ZMK : zshadow m0 ABIT_MASK 128.
  Hypothesis RSTK : rng RNG lo (SP1 - lo).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RISH : rng_aimg_sh RNG.
  Notation W0 := [(lo, SP1); (SP1 + 80, SP1 + 152); (DST, DST + dcap)].
  Hypothesis K : forall m1 rv (j48' : list byte) (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word),
       munch W0 m0 m1 -> wmono bsegs m0 m1 ->
       mem_inv bsegs m1 -> stk bsegs m1 lo SP1 -> rw_cells bsegs m1 (SP1 + 80) [CB 72 j48'] -> rw_cells bsegs m1 (SP1 + 32) FRC ->
       dresA DST dcap (decompress_usingDTable bs d dcap true) m1 rv -> 0 <= rv < 2^64 ->
       evtF bsegs RNG Q
         (MS (mkR y1 (Z_to_bv 64 SP1) gp tp y5 y6 y7 (Z_to_bv 64 SPV) (Z_to_bv 64 SP1) (Z_to_bv 64 rv)
                  y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) y19
                  y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
             FR (Z_to_bv 64 0x98318) fc None m1 (seg_rom bsegs)).

  Notation SBI pc mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SP1) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SP1) x10
             x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880))
             (Z_to_bv 64 (DST + dcap - 3)) (Z_to_bv 64 DT) (Z_to_bv 64 (DST + dcap)) x22 x23 x24 x25
             (Z_to_bv 64 S0) (Z_to_bv 64 2147450880) x28 x29 x30 x31)
        FR (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation FDPRE db v1 d1 s1 d2 v2 d3 s2 d4 :=
    (init_dstream bs = Ok db /\ read_bits db tl = Ok (v1, d1) /\ reload_dstream bs d1 = Ok (s1, d2) /\
     read_bits d2 tl = Ok (v2, d3) /\ reload_dstream bs d3 = Ok (s2, d4)).
  Notation FDMEM m3 v1 v2 := (munch [(SP1 - DEC_STACK, SP1); (SP1 + 80, SP1 + 152)] m0 m3 /\ wmono bsegs m0 m3 /\ mem_inv bsegs m3 /\
     stk bsegs m3 lo SP1 /\ bytes_at bsegs m3 S0 (map (Z_to_bv 8) bs) /\
     rw_cells bsegs m3 (SP1 + 80) [C8 (Z_to_bv 64 v2); C8 (Z_to_bv 64 (DT + 4)); C8 (Z_to_bv 64 v1); C8 (Z_to_bv 64 (DT + 4))]).

  (* [comment removed for export] *)
  Definition fdA_K1636 (x22 x23 x24 x25 : word) : Prop :=
    forall m3 db v1 d1 s1 d2 v2 d3 s2 d4 st d5 jp (r1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      FDPRE db v1 d1 s1 d2 v2 d3 s2 d4 -> reload_dstream bs d4 = Ok (st, d5) -> dstatus_eqb st Overflow = false ->
      bitd_ok bs d5 -> bd_bits d5 <= 64 -> bd_zero d5 = false -> FDMEM m3 v1 v2 ->
      rw_cells bsegs m3 (SP1 + 112) (bitdz_cellsA S0 d5 jp) ->
      evtF bsegs RNG Q (SBI 0x987c4 m3 r1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x22 x23 x24 x25 t3 t4 t5 t6).

  (* [comment removed for export] *)
  Lemma fdA_main1636 : AF_huf_fdt.ftA_tail_stmtA -> forall (x22 x23 x24 x25 : word), fdA_K1636 x22 x23 x24 x25.
  Proof.
    intros TL x22 x23 x24 x25 m3 db v1 d1 s1 d2 v2 d3 s2 d4 st d5 jp r1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
      FP RL OV OK5 B5 BZ5 FM3 BD.
    pose proof FP as (EI & RB1 & RL1 & RB2 & RL2).
    pose proof FM3 as (MW3 & WM3 & MI3 & STK3 & SRC3 & DSC).
    (* [comment removed for export] *)
    assert (DEQ : decompress_usingDTable bs d dcap true =
                  bind (main_loop bs d dcap true (S (Z.to_nat dcap)) (mkDec [] v1 v2 d5))
                       (fun x => tail_loop bs d dcap true (S (Z.to_nat dcap)) x)).
    { unfold decompress_usingDTable. rewrite EI. cbn [bind]. rewrite RB1. cbn [bind]. rewrite RL1. cbn [bind].
      rewrite RB2. cbn [bind]. rewrite RL2. cbn [bind]. rewrite RL. cbn [bind]. rewrite OV. reflexivity. }
    (* [comment removed for export] *)
    destruct (main_loop bs d dcap true (S (Z.to_nat dcap)) (mkDec [] v1 v2 d5)) as [r|e| |] eqn:ML.
    (* [comment removed for export] *)
    2: { exfalso. exact (RF_huf_fdw_pure.main_loop_not_err _ _ _ _ _ _ _ ML). }
    (* [comment removed for export] *)
    2, 3: exfalso; pose proof RESOK as RK; rewrite DEQ in RK; rewrite ?ML in RK; exact RK.
    (* [comment removed for export] *)
    rewrite ?ML in DEQ. cbn [bind] in DEQ.
    pose proof TL as T. unfold AF_huf_fdt.ftA_tail_stmtA in T.
    (* [comment removed for export] *)
    eapply AF_huf_fdm.fmA_main with (m0 := m0) (lo := lo) (f := S (Z.to_nat dcap)) (x := mkDec [] v1 v2 d5) (r := r).
    all: cbn [de_out de_s1 de_s2 de_bd];
         try first [ exact ML | reflexivity | exact OK5 | exact B5 | exact BZ5 | exact BD | eassumption ].
    (* [comment removed for export] *)
    unfold AF_huf_fdm.fmA_K, AF_huf_fdm.fmA_okr, AF_huf_fdm.fmA_mem.
    intros mm jq junk y1 y5 y6 y7 y10 y11 y12 y13 y14 y19 y20 y22 y23 y24 y25 y26 y28 y29 y30 y31
      (OKr & BBr & ZLr & FAr) (MWm & WMm & MIm & STKm & FRm & DSm & BDm & OUTm & LJm & SRCm).
    (* [comment removed for export] *)
    eapply T with (m0 := m0) (m := mm) (lo := lo) (RLO := RLO) (RHI := RHI) (j48 := j48) (jd := jd) (x := r) (jp := jq) (junk := junk); first [ exact (eq_sym DEQ) | eassumption ].
  Qed.

  (* [comment removed for export] *)
  Lemma fdA_fast : AF_huf_fdt.ftA_tail_stmtA ->
    forall (x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x22 x23 x24 x25 x28 x29 x30 x31 : word),
    evtF bsegs RNG Q (SBI 0x984e8 m0 x1 x5 x6 x7 x10 x11 (Z_to_bv 64 (zlen bs)) x13 x14 x15 x16 x17 x22 x23 x24 x25 x28 x29 x30 x31).
  Proof.
    intros TL x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x22 x23 x24 x25 x28 x29 x30 x31.
    (* [comment removed for export] *)
    eapply AF_huf_fdec2.fast_decA_K; first [ exact (fdA_main1636 TL x22 x23 x24 x25) | eassumption ].
  Qed.

End FDEC.

(* [comment removed for export] *)
Theorem fast_decA_of_tail : AF_huf_fdt.ftA_tail_stmtA -> dec_stmtA 0x984e8 1 true.
Proof.
  (* [comment removed for export] *)
  intros TL. unfold dec_stmtA. intros. eapply fdA_fast; eassumption.
Qed.

Theorem fast_decA : dec_stmtA 0x984e8 1 true.
Proof. exact (fast_decA_of_tail AF_huf_fdt.ftA_tailA). Qed.

End CANSEC1.
