(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
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
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Walk RunConst Image Frame.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM KXCell.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_reloadi.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import Shadow.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_tbl_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require RF_huf_tbl_kit RF_huf_fdw_kit RF_huf_fdw_sm RF_huf_fdw_pure RF_huf_fdw_st.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_bdt_model.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase RtCells Stdio_kit AHarness_iface AF_huf_tbl_iface AF_huf_bdt_kit
  AF_huf_tbl_iface2 AF_huf_fdw_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require AF_fse_rd_base.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_fdw_seg AF_huf_fdw_top1.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw FseRdKit HufWalkKit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require FseWalkKit.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_hint ::= bdtA_acc_hint.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.

Section SDT.
  Variables (RNG : footprint) (Q : machine_state -> Prop) (m0 : amem) (SPV FF DST dcap S0 DT lo : Z) (bs : list Z)
            (d : dtable) (gp tp : word) (FR : bvmap 5 word) (fc : bv 32).
  Notation SP1 := (SPAf SPV).
  Notation tl := (dt_tableLog d).
  Hypothesis FC32 : rw_cells bsegs m0 (SP1 + 32) [C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 ASHOFF)].
  Hypothesis BOT : ATOP + 4096 <= lo.
  Hypothesis LO : lo <= SP1 - DEC_STACK.
  Hypothesis SP16 : SPV mod 16 = 0.
  Hypothesis SPH : SPV + 16 <= 2^47.
  Hypothesis ZOBJ : zshadow m0 (SP1 + 80) 72.
  Hypothesis RO : rng RNG (SP1 + 80) 72.
  Hypothesis ROs : rng RNG (shad (SP1 + 80)) 9.
  Hypothesis RO32 : rng RNG (SP1 + 32) 32.
  Hypothesis HTL : 5 <= tl <= 12.
  Hypothesis HCELLS : zlen (dt_cells d) = 2^tl.
  Hypothesis HCOK : RF_huf_fdw_sm.cells_ok tl (dt_cells d).
  Hypothesis FM : dt_fastMode d = 0.
  Hypothesis TBB : bytes_at bsegs m0 (DT + 4) (concat (map fse_cell_bytes (dt_cells d))).
  Hypothesis HDT : ablk DT (DT + 4 + 4 * 2^tl).
  Hypothesis DT4 : DT mod 4 = 0.
  Hypothesis ZDT : zshadow m0 DT (4 + 4 * 2^tl).
  Hypothesis RDT : rng RNG DT (4 + 4 * 2^tl).
  Hypothesis RDTs : rng RNG (shad DT) (nshad (4 + 4 * 2^tl + DT mod 8)).
  Hypothesis SRC : bytes_at bsegs m0 S0 (map (Z_to_bv 8) bs).
  Hypothesis BY : Forall (fun c => 0 <= c < 256) bs.
  Hypothesis HS0 : ablk S0 (S0 + zlen bs).
  Hypothesis S8 : S0 + 8 <= 2^47.
  Hypothesis S16 : 16 <= S0.
  Hypothesis USRC : unpoisoned m0 S0 (S0 + zlen bs).
  Hypothesis RS : rng RNG S0 (zlen bs).
  Hypothesis RSs : rng RNG (shad S0) (nshad (zlen bs + S0 mod 8)).
  Hypothesis DC : 0 <= dcap <= 255.
  Hypothesis HDST : ablk DST (DST + dcap).
  Hypothesis DST3 : 3 <= DST.
  Hypothesis ZDST : zshadow m0 DST dcap.
  Hypothesis RDST : rng RNG DST dcap.
  Hypothesis RDSTs : rng RNG (shad DST) (nshad (dcap + DST mod 8)).
  Hypothesis DJ2 : DST + dcap <= S0 \/ S0 + zlen bs <= DST.
  Hypothesis DJ1 : DST + dcap <= DT \/ DT + 4 + 4 * 2^tl <= DST.
  Hypothesis DJ3 : S0 + zlen bs <= DT \/ DT + 4 + 4 * 2^tl <= S0.
  Hypothesis NZ : 0 < zlen bs.
  Hypothesis RTC : artcells m0.
  Hypothesis ZMK : zshadow m0 ABIT_MASK 128.
  Hypothesis RSTK : rng RNG lo (SP1 - lo).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RISH : rng_aimg_sh RNG.
  Notation W0 := [(lo, SP1); (SP1 + 80, SP1 + 152); (DST, DST + dcap)].
  Notation cellAt s := (nth (Z.to_nat s) (dt_cells d) (mkDC 0 0 0)).

  Definition sdtK (R : res (list Z)) : Prop :=
    forall m1 rv (j48' : list byte) (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word),
      munch W0 m0 m1 -> wmono bsegs m0 m1 ->
      mem_inv bsegs m1 -> stk bsegs m1 lo SP1 -> rw_cells bsegs m1 (SP1 + 80) [CB 72 j48'] ->
      rw_cells bsegs m1 (SP1 + 32) [C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 ASHOFF)] ->
      dresA DST dcap R m1 rv -> 0 <= rv < 2^64 ->
      evtF bsegs RNG Q
        (MS (mkR y1 (Z_to_bv 64 SP1) gp tp y5 y6 y7 (Z_to_bv 64 SPV) (Z_to_bv 64 SP1) (Z_to_bv 64 rv)
                 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (Z.shiftr FF 3 + ASHOFF)) y19
                 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
            FR (Z_to_bv 64 (AFSE_DECOMP + 440)) fc None m1 (seg_rom bsegs)).

  Definition sdtM0 (m : amem) (out : list Z) (c1 c2 : Z) : Prop :=
    munch W0 m0 m /\ wmono bsegs m0 m /\ mem_inv bsegs m /\ stk bsegs m lo SP1 /\
    rw_cells bsegs m (SP1 + 80) [C8 (Z_to_bv 64 c2); C8 (Z_to_bv 64 (DT + 4))] /\
    rw_cells bsegs m (SP1 + 96) [C8 (Z_to_bv 64 c1); C8 (Z_to_bv 64 (DT + 4))] /\
    (exists junk, u8arr bsegs m DST (map (Z_to_bv 8) out ++ junk) /\ zlen junk = dcap - zlen out).
  Definition sdtM (m : amem) (out : list Z) (c1 c2 : Z) (bd : bitD) (jp : list byte) : Prop :=
    sdtM0 m out c1 c2 /\ rw_cells bsegs m (SP1 + 112) (bitdz_cellsA S0 bd jp).

  Definition sdtI (x : dec) (OP0 I : Z) : Prop :=
    bitd_ok bs (de_bd x) /\ bd_bits (de_bd x) <= 2^29 /\ zlen (de_out x) <= dcap - 2 /\
    OP0 + I = DST + zlen (de_out x) /\ DST <= OP0 /\ 0 <= I.

  Definition sdt_atS : Prop :=
    forall m, munch W0 m0 m -> wmono bsegs m0 m ->
      bytes_at bsegs m (DT + 4) (concat (map fse_cell_bytes (dt_cells d))) /\
      bytes_at bsegs m S0 (map (Z_to_bv 8) bs) /\
      rw_cells bsegs m (SP1 + 32) [C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 ASHOFF)] /\
      zshadow m DT (4 + 4 * 2^tl) /\ zshadow m ABIT_MASK 128 /\ zshadow m DST dcap /\ zshadow m (SP1 + 80) 72 /\
      unpoisoned m S0 (S0 + zlen bs) /\ artcells m.

  Notation TS pc mm ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 :=
    (MS (mkR ra (Z_to_bv 64 SP1) gp tp t0 t1 t2 (Z_to_bv 64 SPV) (Z_to_bv 64 SP1) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (Z.shiftr FF 3 + ASHOFF)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Notation TL pc mm ra OP0 I a1 a2 a3 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 :=
    (TS pc mm ra (Z_to_bv 64 OP0) (Z_to_bv 64 I) (Z_to_bv 64 (2^64 - 1 - ABIT_MASK)) (Z_to_bv 64 (-70)) a1 a2 a3
        (Z_to_bv 64 (DST + dcap - 2)) (Z_to_bv 64 (2^61)) (Z_to_bv 64 (2^16 - 1)) (Z_to_bv 64 ABIT_MASK)
        s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 2) (Z_to_bv 64 64) (Z_to_bv 64 (-1)) t6).

  Definition sdt_head (f : nat) : Prop :=
    forall x R m jp (OP0 I : Z) (ra a1 a2 a3 s3 s4 s5 s7 s8 s9 s10 s11 t6 : word),
      tail_loop bs d dcap false f x = R -> dres_ok R -> sdtK R -> sdtI x OP0 I ->
      sdtM m (de_out x) (de_s1 x) (de_s2 x) (de_bd x) jp ->
      evtF bsegs RNG Q (TL (AFSE_DECOMP + 5692) m ra OP0 I a1 a2 a3 s3 s4 s5 (Z_to_bv 64 ASHOFF) s7 s8 s9 s10 s11 t6).

  Definition sdt_c5792 (f : nat) : Prop :=
    forall x R m jp (OP0 I : Z) (ra a1 s3 s4 s5 s7 s8 s9 s10 s11 : word),
      tail_loop bs d dcap false (S f) x = R -> dres_ok R -> sdtK R -> sdtI x OP0 I ->
      sdtM m (de_out x) (de_s1 x) (de_s2 x) (de_bd x) jp ->
      evtF bsegs RNG Q (TL (AFSE_DECOMP + 5792) m ra OP0 I a1 (Z_to_bv 64 (DT + 4 + 4 * de_s1 x))
                           (Z_to_bv 64 (Z.shiftl (dc_symbol (cellAt (de_s1 x)) + 256 * dc_nbBits (cellAt (de_s1 x))) 16))
                           s3 s4 s5 (Z_to_bv 64 ASHOFF) s7 s8 s9 s10 s11 (Z_to_bv 64 (dc_nbBits (cellAt (de_s1 x))))).

  Definition sdt_c5916 (f : nat) : Prop :=
    forall x R m jp (OP0 I o0 s1a : Z) (d1 : bitD) (ra a1 a2 s3 s6 s7 s9 s10 s11 t6 : word),
      tail_loop bs d dcap false (S f) x = R -> dres_ok R -> sdtK R -> sdtI x OP0 I ->
      decode_sym d false (de_s1 x) (de_bd x) = Ok (o0, s1a, d1) -> bd_bits d1 <= 64 ->
      sdtM m (de_out x ++ [o0]) s1a (de_s2 x) d1 jp ->
      evtF bsegs RNG Q (TL (AFSE_DECOMP + 5916) m ra OP0 I a1 a2 (Z_to_bv 64 (bd_bits d1)) s3
                           (Z_to_bv 64 (OP0 + I)) (Z_to_bv 64 (OP0 + I + 1)) s6 s7 (Z_to_bv 64 ASHOFF) s9 s10 s11 t6).

  Definition sdt_c6892 (f : nat) : Prop :=
    forall x R m jp (OP0 I o0 s1a : Z) (d1 : bitD) (ra a1 a2 a3 s3 s6 s7 s8 s9 s10 s11 t6 : word),
      tail_loop bs d dcap false (S f) x = R -> dres_ok R -> sdtK R -> sdtI x OP0 I ->
      decode_sym d false (de_s1 x) (de_bd x) = Ok (o0, s1a, d1) -> 64 < bd_bits d1 ->
      sdtM m (de_out x ++ [o0]) s1a (de_s2 x) d1 jp ->
      evtF bsegs RNG Q (TL (AFSE_DECOMP + 6892) m ra OP0 I a1 a2 a3 s3
                           (Z_to_bv 64 (OP0 + I)) (Z_to_bv 64 (OP0 + I + 1)) s6 s7 s8 s9 s10 s11 t6).

  Definition sdt_c6200 (f : nat) : Prop :=
    forall x R m jp (OP0 I o0 s1a : Z) (d1 d1r : bitD) (st1 : dstatus) (ra a1 a2 a3 s3 s6 s7 s9 s10 s11 : word),
      tail_loop bs d dcap false (S f) x = R -> dres_ok R -> sdtK R -> sdtI x OP0 I ->
      decode_sym d false (de_s1 x) (de_bd x) = Ok (o0, s1a, d1) ->
      reload_dstream bs d1 = Ok (st1, d1r) -> dstatus_eqb st1 Overflow = false -> zlen (de_out x) + 1 <= dcap - 2 ->
      sdtM m (de_out x ++ [o0]) s1a (de_s2 x) d1r jp ->
      evtF bsegs RNG Q (TL (AFSE_DECOMP + 6200) m ra OP0 I a1 a2 a3 s3
                           (Z_to_bv 64 (OP0 + I)) (Z_to_bv 64 (OP0 + I + 1)) s6 s7 (Z_to_bv 64 ASHOFF) s9 s10 s11
                           (Z_to_bv 64 (S0 + 8))).

  Definition sdt_c6300 (f : nat) : Prop :=
    forall x R m jp (OP0 I o0 s1a : Z) (d1 d1r : bitD) (st1 : dstatus) (ra a1 s6 s7 s9 s10 s11 : word),
      tail_loop bs d dcap false (S f) x = R -> dres_ok R -> sdtK R -> sdtI x OP0 I ->
      decode_sym d false (de_s1 x) (de_bd x) = Ok (o0, s1a, d1) ->
      reload_dstream bs d1 = Ok (st1, d1r) -> dstatus_eqb st1 Overflow = false -> zlen (de_out x) + 1 <= dcap - 2 ->
      sdtM m (de_out x ++ [o0]) s1a (de_s2 x) d1r jp ->
      evtF bsegs RNG Q (TL (AFSE_DECOMP + 6300) m ra OP0 I a1 (Z_to_bv 64 (DT + 4 + 4 * de_s2 x))
                           (Z_to_bv 64 (Z.shiftl (dc_symbol (cellAt (de_s2 x)) + 256 * dc_nbBits (cellAt (de_s2 x))) 16))
                           (Z_to_bv 64 (dc_nbBits (cellAt (de_s2 x))))
                           (Z_to_bv 64 (OP0 + I)) (Z_to_bv 64 (OP0 + I + 1)) s6 s7 (Z_to_bv 64 ASHOFF) s9 s10 s11
                           (Z_to_bv 64 (S0 + 8))).

  Definition sdt_c6416 (f : nat) : Prop :=
    forall x R m jp (OP0 I o0 s1a o1 s2a : Z) (d1 d1r d2 : bitD) (st1 : dstatus) (ra a1 a2 s3 s7 s8 s9 s10 s11 : word),
      tail_loop bs d dcap false (S f) x = R -> dres_ok R -> sdtK R -> sdtI x OP0 I ->
      decode_sym d false (de_s1 x) (de_bd x) = Ok (o0, s1a, d1) ->
      reload_dstream bs d1 = Ok (st1, d1r) -> dstatus_eqb st1 Overflow = false -> zlen (de_out x) + 1 <= dcap - 2 ->
      decode_sym d false (de_s2 x) d1r = Ok (o1, s2a, d2) -> bd_bits d2 <= 64 ->
      sdtM m (de_out x ++ [o0; o1]) s1a s2a d2 jp ->
      evtF bsegs RNG Q (TL (AFSE_DECOMP + 6416) m ra OP0 I a1 a2 (Z_to_bv 64 (bd_bits d2)) s3
                           (Z_to_bv 64 (OP0 + I)) (Z_to_bv 64 (OP0 + I + 1)) (Z_to_bv 64 ASHOFF) s7 s8 s9 s10 s11
                           (Z_to_bv 64 (S0 + 8))).

  Definition sdt_c6956 (f : nat) : Prop :=
    forall x R m jp (OP0 I o0 s1a o1 s2a : Z) (d1 d1r d2 : bitD) (st1 : dstatus) (ra a1 a2 a3 s3 s6 s7 s8 s9 s10 s11 t6 : word),
      tail_loop bs d dcap false (S f) x = R -> dres_ok R -> sdtK R -> sdtI x OP0 I ->
      decode_sym d false (de_s1 x) (de_bd x) = Ok (o0, s1a, d1) ->
      reload_dstream bs d1 = Ok (st1, d1r) -> dstatus_eqb st1 Overflow = false -> zlen (de_out x) + 1 <= dcap - 2 ->
      decode_sym d false (de_s2 x) d1r = Ok (o1, s2a, d2) -> 64 < bd_bits d2 ->
      sdtM m (de_out x ++ [o0; o1]) s1a s2a d2 jp ->
      evtF bsegs RNG Q (TL (AFSE_DECOMP + 6956) m ra OP0 I a1 a2 a3 s3
                           (Z_to_bv 64 (OP0 + I)) (Z_to_bv 64 (OP0 + I + 1)) s6 s7 s8 s9 s10 s11 t6).

  Definition sdt_e5528 : Prop :=
    forall f x R m jp (ra t1 t2 a0 a1 a2 a3 a4 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
      tail_loop bs d dcap false f x = R -> dres_ok R -> sdtK R ->
      bitd_ok bs (de_bd x) -> bd_bits (de_bd x) <= 2^29 -> zlen (de_out x) <= dcap ->
      sdtM m (de_out x) (de_s1 x) (de_s2 x) (de_bd x) jp ->
      evtF bsegs RNG Q (TS (AFSE_DECOMP + 5528) m ra (Z_to_bv 64 (DST + zlen (de_out x))) t1 t2 a0 a1 a2 a3 a4
                           (Z_to_bv 64 (2^61)) (Z_to_bv 64 (2^16 - 1)) (Z_to_bv 64 ABIT_MASK) s3 s4 (Z_to_bv 64 (DST + dcap))
                           s6 s7 s8 s9 s10 s11 t3 t4 t5 t6).

  Definition sdt_seg_a : Prop := forall f, sdt_c5792 f -> sdt_head (S f).
  Definition sdt_seg_b : Prop := forall f, sdt_c5916 f -> sdt_c6892 f -> sdt_c5792 f.
  Definition sdt_seg_c : Prop := forall f, sdt_c6200 f -> sdt_c5916 f.
  Definition sdt_seg_d : Prop := forall f, sdt_c6300 f -> sdt_c6200 f.
  Definition sdt_seg_e : Prop := forall f, sdt_c6416 f -> sdt_c6956 f -> sdt_c6300 f.
  Definition sdt_seg_f : Prop := forall f, sdt_head f -> sdt_c6416 f.
  Definition sdt_seg_fin2 : Prop := forall f, sdt_c6892 f.
  Definition sdt_seg_fin1 : Prop := forall f, sdt_c6956 f.
  Definition sdt_seg_entry : Prop := (forall f, sdt_head f) -> sdt_e5528.

  Lemma HAT : sdt_atS.
  Proof.
    unfold sdt_atS. intros m MU WM.
    pose proof (spaf_props SPV SP16) as (SPAB & SPA32).
    pose proof LO as LOs. unfold DEC_STACK in LOs.
    pose proof ATOP_range as ATRa. unfold ATOP_MIN, ATOP_MAX in ATRa. pose proof BOT as BOTa.
    pose proof HDST as HDa. pose proof HDT as HDTa. pose proof HS0 as HSa. unfold ablk in HDa, HDTa, HSa.
    pose proof (Nat2Z.is_nonneg (length bs)) as LB.
    assert (P2 : 2^5 <= 2^tl <= 2^12) by (split; apply Z.pow_le_mono_r; lia).
    assert (AW : appW W0).
    { unfold appW. repeat (apply Forall_cons; [cbn [fst snd]; unfold KHIGH, KLOW, AIMG_HI, KLS in *;
        first [right; lia | destruct HDa as [HDa|HDa]; [left|right]; lia] |]); apply Forall_nil. }
    assert (LT : Z.of_nat (length (concat (map fse_cell_bytes (dt_cells d)))) = 4 * 2^tl).
    { rewrite fse_cells_length. lia. }
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))).
    - eapply bytes_at_transport; [exact TBB | exact MU | rewrite LT; cbn [disjoint_from]; unfold AIMG_HI, KLS in *; lia].
    - eapply bytes_at_transport; [exact SRC | exact MU | rewrite length_map; cbn [disjoint_from]; unfold AIMG_HI, KLS in *; lia].
    - eapply rw_cells_transport; [exact FC32 | exact MU | exact WM | cbn [disjoint_from cells_size csize]; unfold AIMG_HI, KLS in *; lia].
    - eapply zshadow_appW; [exact ZDT | exact MU | exact AW | unfold AIMG_HI, KLS in *; lia | unfold AIMG_HI, KLS in *; lia].
    - eapply zshadow_appW; [exact ZMK | exact MU | exact AW | unfold ABIT_MASK; lia | unfold ABIT_MASK; lia].
    - eapply zshadow_appW; [exact ZDST | exact MU | exact AW | unfold AIMG_HI, KLS in *; lia | unfold AIMG_HI, KLS in *; lia].
    - eapply zshadow_appW; [exact ZOBJ | exact MU | exact AW | unfold AIMG_HI, KLS in *; lia | unfold AIMG_HI, KLS in *; lia].
    - eapply unpoisoned_appW; [exact USRC | exact MU | exact AW | unfold AIMG_HI, KLS in *; lia | unfold AIMG_HI, KLS in *; lia].
    - pose proof RTC as RT. unfold artcells in RT |- *.
      repeat match goal with Hc : rw_cells _ _ _ _ /\ _ |- _ => destruct Hc end.
      repeat match goal with |- _ /\ _ => split end;
        (eapply rw_cells_transport; [eassumption | exact MU | exact WM | cbn [disjoint_from cells_size csize];
         unfold AIMG_HI, KLS in *; lia]).
  Qed.

  Lemma sdt_cb72 : forall m c1 c2 bd jp,
    rw_cells bsegs m (SP1 + 80) [C8 (Z_to_bv 64 c2); C8 (Z_to_bv 64 (DT + 4))] ->
    rw_cells bsegs m (SP1 + 96) [C8 (Z_to_bv 64 c1); C8 (Z_to_bv 64 (DT + 4))] ->
    rw_cells bsegs m (SP1 + 112) (bitdz_cellsA S0 bd jp) ->
    exists j48', rw_cells bsegs m (SP1 + 80) [CB 72 j48'].
  Proof.
    intros m c1 c2 bd jp A B C.
    assert (RC : rw_cells bsegs m (SP1 + 80) ([C8 (Z_to_bv 64 c2); C8 (Z_to_bv 64 (DT + 4))] ++
                   [C8 (Z_to_bv 64 c1); C8 (Z_to_bv 64 (DT + 4))] ++ bitdz_cellsA S0 bd jp)).
    { apply rw_cells_app. split; [exact A |]. apply rw_cells_app. split.
      - replace (SP1 + 80 + Z.of_nat (cells_size [C8 (Z_to_bv 64 c2); C8 (Z_to_bv 64 (DT + 4))])) with (SP1 + 96)
          by (cbn [cells_size csize]; lia). exact B.
      - replace (SP1 + 80 + Z.of_nat (cells_size [C8 (Z_to_bv 64 c2); C8 (Z_to_bv 64 (DT + 4))]) +
                 Z.of_nat (cells_size [C8 (Z_to_bv 64 c1); C8 (Z_to_bv 64 (DT + 4))])) with (SP1 + 112)
          by (cbn [cells_size csize]; lia). exact C. }
    exists (cells_bytes ([C8 (Z_to_bv 64 c2); C8 (Z_to_bv 64 (DT + 4))] ++
                   [C8 (Z_to_bv 64 c1); C8 (Z_to_bv 64 (DT + 4))] ++ bitdz_cellsA S0 bd jp)).
    pose proof RC as ((WFc & _) & _).
    eapply rw_cells_recast; [exact RC | | cbn [cells_bytes cbytes]; apply app_nil_r | ].
    - cbn [cells_wf cell_wf]. split; [| exact I]. rewrite cells_bytes_length by exact WFc.
      unfold bitdz_cellsA. cbn [cells_size csize app]. reflexivity.
    - unfold bitdz_cellsA. cbn [cells_size csize app]. reflexivity.
  Qed.

  Lemma sdt_exitK : forall R m out c1 c2 bd jp rv
      (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word),
    sdtK R -> sdtM m out c1 c2 bd jp -> dresA DST dcap R m rv -> 0 <= rv < 2^64 ->
    evtF bsegs RNG Q
      (MS (mkR y1 (Z_to_bv 64 SP1) gp tp y5 y6 y7 (Z_to_bv 64 SPV) (Z_to_bv 64 SP1) (Z_to_bv 64 rv)
               y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (Z.shiftr FF 3 + ASHOFF)) y19
               y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
          FR (Z_to_bv 64 (AFSE_DECOMP + 440)) fc None m (seg_rom bsegs)).
  Proof.
    intros R m out c1 c2 bd jp rv y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28
      y29 y30 y31 K ((MU & WM & MI & ST & C80 & C96 & _) & C112) DR RV.
    destruct (sdt_cb72 _ _ _ _ _ C80 C96 C112) as (j48' & CB).
    destruct (HAT m MU WM) as (_ & _ & FC & _).
    exact (K m rv j48' y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31
             MU WM MI ST CB FC DR RV).
  Qed.

  Lemma sdt_head0 : sdt_head O.
  Proof.
    unfold sdt_head. intros x R m jp OP0 I ra a1 a2 a3 s3 s4 s5 s7 s8 s9 s10 s11 t6 TL0 ROK.
    cbn [tail_loop] in TL0. subst R. contradiction.
  Qed.

  Ltac sdt_br b := lazymatch goal with |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
    replace c with b; [cbv iota | symmetry; rewrite ?bv_ltu_Z, ?bv_eqb_Z, ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N];
      first [apply Z.ltb_ge | apply Z.ltb_lt | apply Z.eqb_eq | apply Z.eqb_neq
            | apply Bool.negb_true_iff, Z.ltb_ge | apply Bool.negb_false_iff, Z.ltb_lt
            | apply Bool.negb_true_iff, Z.eqb_neq | apply Bool.negb_false_iff, Z.eqb_eq]; Z.div_mod_to_equations; lia] end.

  Lemma sdt_entry_pf : sdt_seg_entry.
  Proof.
    unfold sdt_seg_entry, sdt_e5528.
    intros HD f x R m jp ra t1 t2 a0 a1 a2 a3 a4 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 TLF ROK K BOK BB ZL M.
    pose proof M as M0. destruct M as ((MU & WM & MI & ST & C80 & C96 & UA) & C112).
    destruct (HAT m MU WM) as (TB & SB & FC & ZD & ZM & ZDS & ZO & US & RT).
    pose proof (spaf_props SPV SP16) as (SPAB & SPA32). pose proof LO as LOs. unfold DEC_STACK in LOs.
    pose proof HDST as HDa. unfold ablk, AIMG_HI, KLS in HDa. pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    destruct f as [| f']; [cbn [tail_loop] in TLF; subst R; contradiction |].
    pose proof (Nat2Z.is_nonneg (length (de_out x))) as LO0.
    do 2 zstep. sdt_br false. do 2 zstep. sdt_br false. do 3 zstep.
    destruct (Z_lt_le_dec (dcap - 2) (zlen (de_out x))) as [LT | GE].
    - sdt_br false. zstep.
      lazymatch goal with |- evtF _ _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC" pc end.
      assert (RE : R = Err ZSTD_error_dstSize_tooSmall).
      { rewrite <- TLF. cbn [tail_loop]. replace (dcap - 2 <? FseNCount.Zlength (de_out x)) with true; [reflexivity |].
        symmetry. apply Z.ltb_lt. unfold FseNCount.Zlength. lia. }
      replace (Z_to_bv 64 (-70)) with (Z_to_bv 64 (2^64 - ZSTD_error_dstSize_tooSmall))
        by (apply Z_to_bv_eqm; unfold ZSTD_error_dstSize_tooSmall; reflexivity).
      eapply sdt_exitK; [exact K | exact M0 | | unfold ZSTD_error_dstSize_tooSmall; lia].
      rewrite RE. cbn [dresA]. split; [reflexivity | unfold ZSTD_error_dstSize_tooSmall; lia].
    - sdt_br true. do 7 zstep.
      replace (Z.lxor (Z.land ABIT_MASK _) _) with (2^64 - 1 - ABIT_MASK) by (unfold ABIT_MASK; reflexivity).
      replace (DST + dcap + -2) with (DST + dcap - 2) by lia.
      eapply (HD (S f') x R m jp (DST + zlen (de_out x)) 0); [exact TLF | exact ROK | exact K | | exact M0].
      unfold sdtI. refine (conj BOK (conj BB _)). repeat split; lia.
  Qed.

  Lemma sdt_loop : sdt_seg_a -> sdt_seg_b -> sdt_seg_c -> sdt_seg_d -> sdt_seg_e -> sdt_seg_f ->
    sdt_seg_fin2 -> sdt_seg_fin1 -> forall f, sdt_head f.
  Proof.
    intros A B C D E F G H f. induction f as [| f IH].
    - exact sdt_head0.
    - apply A, B; [| apply G]. apply C, D, E; [| apply H]. apply F, IH.
  Qed.

  Lemma sdt_tail : sdt_seg_a -> sdt_seg_b -> sdt_seg_c -> sdt_seg_d -> sdt_seg_e -> sdt_seg_f ->
    sdt_seg_fin2 -> sdt_seg_fin1 -> sdt_seg_entry -> sdt_e5528.
  Proof.
    intros A B C D E F G H EN. exact (EN (sdt_loop A B C D E F G H)).
  Qed.

  Lemma sdt_bridge : sdt_e5528 -> dres_ok (decompress_usingDTable bs d dcap false) ->
    sdtK (decompress_usingDTable bs d dcap false) ->
    forall (r : dec) (m2 : amem) (jp junk : list byte)
           (x1 x6 x7 x10 x11 x12 x13 x14 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    decompress_usingDTable bs d dcap false = tail_loop bs d dcap false (Datatypes.S (Z.to_nat dcap)) r ->
    bitd_ok bs (de_bd r) -> bd_bits (de_bd r) <= 2^29 -> zlen (de_out r) <= dcap ->
    munch W0 m0 m2 -> wmono bsegs m0 m2 -> mem_inv bsegs m2 -> stk bsegs m2 lo SP1 ->
    u8arr bsegs m2 DST (map (Z_to_bv 8) (de_out r) ++ junk) -> zlen junk = dcap - zlen (de_out r) ->
    rw_cells bsegs m2 (SP1 + 80) [C8 (Z_to_bv 64 (de_s2 r)); C8 (Z_to_bv 64 (DT + 4))] ->
    rw_cells bsegs m2 (SP1 + 96) [C8 (Z_to_bv 64 (de_s1 r)); C8 (Z_to_bv 64 (DT + 4))] ->
    rw_cells bsegs m2 (SP1 + 112) (bitdz_cellsA S0 (de_bd r) jp) ->
    evtF bsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 SP1) gp tp (Z_to_bv 64 (DST + zlen (de_out r))) x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SP1)
               x10 x11 x12 x13 x14 (Z_to_bv 64 (2^61)) (Z_to_bv 64 (2^16 - 1)) (Z_to_bv 64 ABIT_MASK)
               (Z_to_bv 64 (Z.shiftr FF 3 + ASHOFF)) (Z_to_bv 64 (DST + dcap - 3)) x20 (Z_to_bv 64 (DST + dcap))
               x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          FR (Z_to_bv 64 (AFSE_DECOMP + 5528)) fc None m2 (seg_rom bsegs)).
  Proof.
    intros E ROK K r m2 jp junk x1 x6 x7 x10 x11 x12 x13 x14 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
      DEQ BOK BB ZL MU WM MI ST UA LJ C80 C96 C112.
    eapply (E (Datatypes.S (Z.to_nat dcap)) r); [exact (eq_sym DEQ) | exact ROK | exact K | exact BOK | exact BB
      | exact ZL | ].
    exact (conj (conj MU (conj WM (conj MI (conj ST (conj C80 (conj C96 (ex_intro _ junk (conj UA LJ)))))))) C112).
  Qed.


  Lemma l1_zsh : forall m X n a, zshadow m X n -> X <= a < X + n -> 0 <= a < 2^47 ->
    rw_cells bsegs m (Z.shiftr a 3 + ASHOFF) [C1 (Z_to_bv 8 0)].
  Proof.
    intros m X n a HZ H B. clear - HZ H B.
    assert (A8 : Z.shiftr a 3 = a / 8) by (apply Z.shiftr_div_pow2; lia).
    apply AProg_kit.c1_of_byte; [rewrite A8; unfold ASHOFF; Z.div_mod_to_equations; lia
                                | rewrite A8; unfold ASHOFF; Z.div_mod_to_equations; lia |].
    rewrite Z.add_comm. unfold zshadow, shad in HZ. apply HZ; lia.
  Qed.

  Lemma l1_ds_cases : forall s bd, (exists q, decode_sym d false s bd = Ok q) \/ decode_sym d false s bd = Ub.
  Proof.
    intros s bd. unfold decode_sym, HufPure_FseDecomp.cell.
    destruct ((0 <=? s) && (s <? _)); cbn [bind]; [| right; reflexivity].
    unfold read_bits, look_bits, bit_mask.
    destruct ((0 <=? _) && (_ <? 32)); cbn [bind]; [left; eexists; reflexivity | right; reflexivity].
  Qed.

  Lemma l1_step1 : forall f x R, tail_loop bs d dcap false (S f) x = R -> dres_ok R -> zlen (de_out x) <= dcap - 2 ->
    exists o0 s1a d1, decode_sym d false (de_s1 x) (de_bd x) = Ok (o0, s1a, d1).
  Proof.
    intros f x R TL ROK ZL. cbn [tail_loop] in TL.
    lazymatch type of TL with context [?a <? ?b] =>
      replace (a <? b) with false in TL by (symmetry; apply Z.ltb_ge; unfold FseNCount.Zlength; lia) end.
    destruct (l1_ds_cases (de_s1 x) (de_bd x)) as [[[[o0 s1a] d1] DS] | DS].
    - exists o0, s1a, d1. exact DS.
    - rewrite DS in TL. cbn [bind] in TL. subst R. contradiction.
  Qed.

  Ltac l1_zl :=
    repeat match goal with H : ?T |- _ =>
      lazymatch type of T with Prop =>
        lazymatch T with
        | _ <= _ => fail | _ < _ => fail | _ = _ :> Z => fail | _ <= _ <= _ => fail | _ <= _ < _ => fail
        | _ => clear H end end end;
    Z.div_mod_to_equations; lia.
  Ltac l1_p2 := repeat match goal with |- context [2 ^ ?k] =>
    lazymatch k with Zpos _ => let v := eval vm_compute in (2 ^ k) in change (2 ^ k) with v end end.
  Ltac l1_zdec :=
    repeat match goal with
    | |- context [?a =? ?b] =>
        first [ replace (a =? b) with true by (symmetry; apply Z.eqb_eq; l1_zl)
              | replace (a =? b) with false by (symmetry; apply Z.eqb_neq; l1_zl) ]
    | |- context [?a <? ?b] =>
        first [ replace (a <? b) with true by (symmetry; apply Z.ltb_lt; l1_zl)
              | replace (a <? b) with false by (symmetry; apply Z.ltb_ge; l1_zl) ]
    end.
  Ltac l1_zbr :=
    unfold zx32; rewrite ?bv_ltu_Z, ?bv_eqb_Z, ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N];
    rewrite ?Z.shiftr_div_pow2 by lia; l1_p2;
    repeat match goal with |- context [?a mod ?N] =>
      lazymatch N with Zpos _ => idtac end; rewrite (Z.mod_small a N) by l1_zl end;
    l1_zdec; reflexivity.
  Ltac l1_br :=
    lazymatch goal with |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      first [ replace c with false; [cbv iota | symmetry; l1_zbr]
            | replace c with true; [cbv iota | symmetry; l1_zbr] ] end.
  Ltac l1_n :=
    rewrite ?Z.shiftl_mul_pow2 by lia; try change (2^2) with 4;
    repeat match goal with |- context [Z.land ?x ?M] =>
      change (Z.land x M) with (Z.land x (Z.ones 64)); rewrite (Z.land_ones x 64) by lia;
      rewrite (Z.mod_small x (2^64)) by lia end.
  Ltac l1_goal := lazymatch goal with |- ?g => fail 0 "GOAL" g end.

  Lemma l1_cell_hi : forall ns sy nb, 0 <= sy < 256 -> 0 <= nb < 256 ->
    firstn 2 (skipn (Z.to_nat 2) (le2 (Z_to_bv 64 ns) ++ [Z_to_bv 8 sy; Z_to_bv 8 nb])) = le2 (Z_to_bv 64 (sy + 256 * nb)).
  Proof.
    intros ns sy nb Hs Hn.
    pose proof (length_le2 (Z_to_bv 64 ns)) as L.
    destruct (le2 (Z_to_bv 64 ns)) as [|x0 [|x1 [|x2 r]]]; try discriminate L.
    change (Z.to_nat 2) with 2%nat. cbn [app skipn firstn].
    unfold le2. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
    rewrite Z.mod_small by lia. cbn [Z_to_le_bytes].
    rewrite !Z.shiftr_div_pow2 by lia.
    replace ((sy + 256 * nb) / 2 ^ 8) with nb by (Z.div_mod_to_equations; lia).
    f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
    replace (sy + 256 * nb) with (sy + nb * 2 ^ 8) by lia. rewrite Z_mod_plus_full. reflexivity.
  Qed.

  Lemma sdt_seg_a_pf : sdt_seg_a.
  Proof.
    unfold sdt_seg_a, sdt_c5792, sdt_head.
    intros f C x R m jp OP0 I ra a1 a2 a3 s3 s4 s5 s7 s8 s9 s10 s11 t6 TLx ROK K HI HM.
    pose proof HI as (BOK & BB & ZL & OPI & DOP & I0).
    destruct (l1_step1 f x R TLx ROK ZL) as (o0 & s1a & d1 & DS).
    pose proof BOK as (BC & BBR & _).
    destruct (RF_huf_fdw_sm.dec_inv tl [] d ltac:(lia) HCELLS HCOK _ _ _ _ _ DS ltac:(lia))
      as (c & NC & S1R & SYR & NBR & NSR & NSR2 & _ & _ & _).
    pose proof HM as ((MU & WM & MI & STK & C80 & C96 & OUT) & C112).
    destruct (HAT m MU WM) as (TBm & SRCm & FCm & ZDTm & ZMKm & ZDSTm & ZOBJm & USRCm & RTCm).
    set (s := de_s1 x) in *.
    assert (EC : c = cellAt s) by (symmetry; apply nth_error_nth; exact NC). subst c.
    assert (P2 : 32 <= 2^tl <= 4096) by (split; [change 32 with (2^5) | change 4096 with (2^12)]; apply Z.pow_le_mono_r; lia).
    pose proof ATOP_range as AR; unfold ATOP_MIN, ATOP_MAX in AR.
    assert (DTL : 1 <= DT /\ DT + 4 + 4 * 2^tl <= ATOP)
      by (destruct HDT as [[H1 H2]|[H1 H2]]; [unfold AIMG_HI in H1; unfold KLS in H2|]; lia).
    assert (TBL : zlen (concat (map fse_cell_bytes (dt_cells d))) = 4 * 2^tl)
      by (rewrite RF_huf_bdt_model.fse_cells_length; lia).
    unfold ASHOFF.
    do 4 zstep. l1_n.
    lazymatch goal with |- context [Z_to_bv 64 (s * 4 + (DT + 4))] =>
      replace (s * 4 + (DT + 4)) with (DT + 4 + 4 * s) by lia end.
    do 2 zstep. l1_n.
    zstep. l1_br.
    do 2 zstep. l1_n. zstep. l1_br.
    zstep. l1_br.
    do 2 zstep. l1_n.
    wk_shz 11%Z. zstep. l1_br.
    do 3 zstep. l1_n.
    wk_shz 11%Z. zstep. l1_br.
    pose proof (RF_huf_fdw_kit.cell_rd_off bsegs m (DT + 4) (dt_cells d) s (cellAt s) 2 2 TBm NC ltac:(lia) ltac:(lia) ltac:(lia)) as CR2.
    unfold fse_cell_bytes in CR2. rewrite l1_cell_hi in CR2 by lia.
    replace (DT + 4 + (4 * s + 2)) with (DT + 4 + 4 * s + 2) in CR2 by lia.
    zstep. l1_n.
    assert (V16 : 0 <= dc_symbol (cellAt s) + 256 * dc_nbBits (cellAt s) < 3328) by lia.
    rewrite zx16_lit by lia.
    do 2 zstep. l1_n. zstep. l1_br. zstep. l1_n.
    set (V := dc_symbol (cellAt s) + 256 * dc_nbBits (cellAt s)) in *.
    lazymatch goal with |- context [Z_to_bv 64 ((V * ?K) ≫ 24)] =>
      replace ((V * K) ≫ 24) with (dc_nbBits (cellAt s))
        by (rewrite Z.shiftr_div_pow2 by lia; l1_p2; subst V; l1_zl) end.
    lazymatch goal with |- context [Z_to_bv 64 (V * ?K)] =>
      replace (V * K) with (Z.shiftl V 16) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity) end.
    subst V.
    exact (C x R m jp OP0 I ra _ _ s4 s5 s7 s8 s9 s10 s11 TLx ROK K HI HM).
  Qed.

  Lemma l1_zx32 : forall e, 0 <= e < 2^32 -> zx32 (Z_to_bv 64 e) = Z_to_bv 64 e.
  Proof.
    intros e H. unfold zx32. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
    rewrite !Z.mod_small by lia. reflexivity.
  Qed.

  Lemma l1_sx32 : forall e, 0 <= e < 2^31 -> sx32 (Z_to_bv 64 e) = Z_to_bv 64 e.
  Proof.
    intros e H. unfold sx32. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
    rewrite Z.mod_small by lia. rewrite FseWalkKit.swrap32_small by lia. reflexivity.
  Qed.

  Lemma l1_land16 : forall a b, 0 <= a -> 0 <= b < 2^16 -> Z.land (a * 2^16 + b) (2^16 - 1) = b.
  Proof.
    intros a b Ha Hb. change (2^16 - 1) with (Z.ones 16). rewrite Z.land_ones by lia.
    rewrite Z.add_comm, Z_mod_plus_full. apply Z.mod_small. lia.
  Qed.

  Lemma l1_lor : forall a b, 0 <= a -> 0 <= b < 2^16 -> Z.lor (a * 2^16) b = a * 2^16 + b.
  Proof.
    intros a b Ha Hb.
    rewrite <- Z.shiftl_mul_pow2 by lia.
    assert (HL : Z.land (Z.shiftl a 16) b = 0).
    { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
      destruct (Z.lt_ge_cases n 16) as [H|H].
      - rewrite Z.shiftl_spec_low by lia. reflexivity.
      - rewrite andb_comm. replace (Z.testbit b n) with false; [reflexivity|].
        symmetry. destruct (Z.eq_dec b 0) as [->|Hb0]; [apply Z.bits_0|].
        apply Z.bits_above_log2; [lia|].
        assert (Z.log2 b < 16) by (apply Z.log2_lt_pow2; lia). lia. }
    rewrite <- Z.lxor_lor by exact HL. rewrite <- Z.add_nocarry_lxor by exact HL. reflexivity.
  Qed.

  Lemma l1_modmod : forall y N, 0 < N -> N mod 64 = 0 -> (y mod N) mod 64 = y mod 64.
  Proof.
    intros y N HN HM.
    assert (EN : N = 64 * (N / 64)) by (Z.div_mod_to_equations; lia).
    assert (QN : 0 < N / 64) by (Z.div_mod_to_equations; lia).
    set (k := N / 64) in *. set (q := y / N).
    assert (E : y mod N = y + (- q * k) * 64) by (rewrite Z.mod_eq by lia; fold q; rewrite EN at 1; ring).
    rewrite E, Z_mod_plus_full. reflexivity.
  Qed.

  Lemma l1_s1v : forall cont X nb ns M N, M = Z.ones 64 -> N mod 64 = 0 -> 0 < N ->
    0 <= cont < 2^64 -> 0 <= X < 2^31 ->
    Z.land (Z.land (Z.shiftr cont (Z.land (Z.land (0 - X) M) 63)) M) (2^nb - 1) + ns =
    ns + Z.land (Z.shiftr cont ((bv_swrap 32 (0 - X) mod N) mod 64)) (2^nb - 1).
  Proof.
    intros cont X nb ns M N -> HN HN0 HC HX.
    change 63 with (Z.ones 6).
    rewrite (Z.land_ones (0 - X) 64) by lia.
    rewrite (Z.land_ones _ 6) by lia.
    rewrite FseWalkKit.swrap32_small by lia.
    change (2^6) with 64.
    rewrite (l1_modmod _ N) by lia.
    rewrite (l1_modmod _ (2^64)) by (l1_p2; first [reflexivity | lia]).
    set (k := (0 - X) mod 64).
    assert (K0 : 0 <= k) by (subst k; apply Z.mod_pos_bound; lia).
    assert (P0 : 0 < 2^k) by (apply Z.pow_pos_nonneg; lia).
    rewrite (Z.land_ones _ 64) by lia.
    rewrite (Z.mod_small (Z.shiftr cont k)).
    - lia.
    - rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia |].
      apply (Z.le_lt_trans _ cont); [apply Z.div_le_upper_bound; nia | lia].
  Qed.

  Lemma sdt_seg_b_pf : sdt_seg_b.
  Proof.
    unfold sdt_seg_b, sdt_c5916, sdt_c6892, sdt_c5792.
    intros f C16 C68 x R m jp OP0 I ra a1 s3 s4 s5 s7 s8 s9 s10 s11 TLx ROK K HI HM.
    pose proof HI as (BOK & BB & ZL & OPI & DOP & I0).
    destruct (l1_step1 f x R TLx ROK ZL) as (o0 & s1a & d1 & DS).
    pose proof BOK as (BC & BBR & _).
    destruct (RF_huf_fdw_sm.dec_inv tl [] d ltac:(lia) HCELLS HCOK _ _ _ _ _ DS ltac:(lia))
      as (c & NC & S1R & SYR & NBR & NSR & NSR2 & EO & ES & ED).
    pose proof HM as ((MU & WM & MI & STK & C80 & C96 & (junk & OUTA & LJ)) & C112).
    destruct (HAT m MU WM) as (TBm & SRCm & FCm & ZDTm & ZMKm & ZDSTm & ZOBJm & USRCm & RTCm).
    set (s := de_s1 x) in *.
    assert (EC : c = cellAt s) by (symmetry; apply nth_error_nth; exact NC). subst c.
    assert (P2 : 32 <= 2^tl <= 4096) by (split; [change 32 with (2^5) | change 4096 with (2^12)]; apply Z.pow_le_mono_r; lia).
    pose proof ATOP_range as AR; unfold ATOP_MIN, ATOP_MAX in AR.
    assert (DTL : 1 <= DT /\ DT + 4 + 4 * 2^tl <= ATOP)
      by (destruct HDT as [[H1 H2]|[H1 H2]]; [unfold AIMG_HI in H1; unfold KLS in H2|]; lia).
    assert (DSTL : DST + dcap <= ATOP)
      by (destruct HDST as [[H1 H2]|[H1 H2]]; [unfold AIMG_HI in H1; unfold KLS in H2|]; lia).
    assert (ABM : 1 <= ABIT_MASK <= 2^47 - 4096) by (unfold ABIT_MASK; lia).
    pose proof (rng_mask_sh RNG RISH) as RMS.
    pose proof LO as LO'. unfold DEC_STACK in LO'.
    pose proof (spaf_props SPV SP16) as (SPAB & SPA32).
    assert (NS16 : 0 <= dc_newState (cellAt s) < 2^16) by (assert (0 < 2^dc_nbBits (cellAt s)) by (apply Z.pow_pos_nonneg; lia); lia).
    assert (V16 : 0 <= dc_symbol (cellAt s) + 256 * dc_nbBits (cellAt s) < 3328) by lia.
    unfold bitdz_cellsA in C112.
    unfold ASHOFF. unfold ASHOFF in FCm.
    zstep. l1_n. zstep. l1_br.
    pose proof (RF_huf_fdw_kit.cell_rd_ns bsegs m (DT + 4) (dt_cells d) s (cellAt s) (wa (DT + 4 + 4 * s)) TBm NC ltac:(lia) ltac:(f_equal; lia)) as CR0.
    zstep. rewrite zx16_lit by lia. do 3 zstep. l1_n.
    wk_shz 19%Z.
    do 2 zstep. zstep. l1_br. do 3 zstep. l1_n.
    pose proof (maskA_rd m (dc_nbBits (cellAt s)) MI ltac:(lia)) as RMK.
    replace (4 * dc_nbBits (cellAt s)) with (dc_nbBits (cellAt s) * 4) in RMK by lia.
    pose proof (rng_acc_litZ' RNG _ _ (ABIT_MASK + dc_nbBits (cellAt s) * 4) 4 4 RI eq_refl eq_refl
                  ltac:(unfold ABIT_MASK; lia)) as ACM.
    zstep. l1_n. zstep. l1_n.
    rewrite (l1_sx32 (bd_bits (de_bd x))) by lia.
    rewrite ?Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
    rewrite (Z.mod_small (bd_bits (de_bd x))) by lia.
    rewrite (FseWalkKit.swrap32_small (bd_bits (de_bd x) + dc_nbBits (cellAt s))) by lia.
    l1_n.
    rewrite (FseWalkKit.swrap32_small (0 - (bd_bits (de_bd x) + dc_nbBits (cellAt s)))) by lia.
    assert (P12 : 1 <= 2 ^ dc_nbBits (cellAt s) <= 4096)
      by (split; [apply (Z.pow_le_mono_r 2 0); lia | change 4096 with (2^12); apply Z.pow_le_mono_r; lia]).
    rewrite (l1_zx32 (2 ^ dc_nbBits (cellAt s) - 1)) by lia.
    lazymatch goal with |- context [Z.lor (?V * ?K) (dc_newState (cellAt s))] =>
      replace (Z.lor (V * K) (dc_newState (cellAt s))) with (V * K + dc_newState (cellAt s))
        by (change K with (2^16); symmetry; apply l1_lor; lia) end.
    zstep. zstep. l1_n.
    lazymatch goal with |- context [Z.land (?V * ?K + dc_newState (cellAt s)) ?M] =>
      replace (Z.land (V * K + dc_newState (cellAt s)) M) with (dc_newState (cellAt s))
        by (change K with (2^16); change M with (2^16 - 1); symmetry; apply l1_land16; lia) end.
    do 4 zstep. l1_n.
    zstep. zstep. l1_br. do 3 zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (HAT mm MU WM) as (_ & _ & _ & _ & _ & ZD2 & _);
      pose proof (chkZ mm DST dcap (OP0 + I) ZD2 ltac:(lia) ltac:(lia)) as RDB end.
    pose proof (acc_shZ RNG DST dcap (OP0 + I) RDSTs ltac:(lia)) as ACO.
    zstep. rewrite ?sxb0. clear RDB. zstep. l1_br.
    zstep.
    lazymatch goal with |- context [(?V * ?K + dc_newState (cellAt s)) ≫ 16] =>
      replace ((V * K + dc_newState (cellAt s)) ≫ 16) with V
        by (change K with (2^16); rewrite Z.shiftr_div_pow2 by lia; l1_p2; l1_zl) end.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u8arr_store_ok bsegs mm DST _ (zlen (de_out x)) (wa (OP0 + I)) OUTA
                    ltac:(repeat (rewrite length_app || rewrite length_map); cbn [length]; lia) ltac:(f_equal; lia)) as SOK end.
    zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?mm (Z_to_bv 64 (OP0 + I)) ?bs) _) =>
      change (write_to_mem mm (Z_to_bv 64 (OP0 + I)) bs) with (write_to_mem mm (wa (OP0 + I)) bs);
      replace (write_to_mem mm (wa (OP0 + I)) bs) with (write_to_mem mm (wa (DST + zlen (de_out x))) bs)
        by (rewrite OPI; reflexivity) end.
    rewrite le1_lit.
    replace (Z_to_bv 8 (dc_symbol (cellAt s) + 256 * dc_nbBits (cellAt s))) with (Z_to_bv 8 (dc_symbol (cellAt s)))
      by (apply bv_eq; rewrite !Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N];
          replace (dc_symbol (cellAt s) + 256 * dc_nbBits (cellAt s)) with (dc_symbol (cellAt s) + dc_nbBits (cellAt s) * 2 ^ 8) by lia;
          rewrite Z_mod_plus_full; reflexivity).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ _) _) =>
      pose proof (RF_huf_fdw_kit.out_sb bsegs mm DST (de_out x) junk (dc_symbol (cellAt s)) OUTA
                    ltac:(lia)) as OUT2 end.
    assert (LJ2 : zlen (List.tl junk) = dcap - zlen (de_out x ++ [dc_symbol (cellAt s)]))
      by (rewrite length_app; cbn [length]; rewrite RF_huf_fdw_sm.zlen_tl by lia; lia).
    clear OUTA LJ. store_done.
    zstep.
    lazymatch type of C96 with rw_cells _ _ _ [C8 (Z_to_bv 64 ?V); _] =>
      replace V with s1a in C96 by (rewrite ES; symmetry; apply l1_s1v; first [reflexivity | lia]) end.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (SM : sdtM mm (de_out x ++ [o0]) s1a (de_s2 x) d1 jp)
        by (subst o0 d1; unfold sdtM, sdtM0;
            refine (conj (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (ex_intro _ (List.tl junk) (conj _ _)))))))) _);
            assumption) end.
    destruct (Z_lt_le_dec 64 (bd_bits (de_bd x) + dc_nbBits (cellAt s))) as [GT | LE].
    - l1_br. subst d1. exact (C68 x R _ jp OP0 I o0 s1a _ ra _ _ _ _ _ _ _ _ _ _ _ TLx ROK K HI DS GT SM).
    - l1_br. subst d1. exact (C16 x R _ jp OP0 I o0 s1a _ ra _ _ _ _ _ _ _ _ _ TLx ROK K HI DS LE SM).
  Qed.

  Lemma l1_step2 : forall f x R o0 s1a d1 st1 d1r, tail_loop bs d dcap false (S f) x = R -> dres_ok R ->
    zlen (de_out x) <= dcap - 2 -> decode_sym d false (de_s1 x) (de_bd x) = Ok (o0, s1a, d1) ->
    reload_dstream bs d1 = Ok (st1, d1r) -> dstatus_eqb st1 Overflow = false -> zlen (de_out x) + 1 <= dcap - 2 ->
    exists o1 s2a d2, decode_sym d false (de_s2 x) d1r = Ok (o1, s2a, d2).
  Proof.
    intros f x R o0 s1a d1 st1 d1r TL ROK ZL DS1 RL NO ZL1. cbn [tail_loop] in TL.
    lazymatch type of TL with context [?a <? ?b] =>
      replace (a <? b) with false in TL by (symmetry; apply Z.ltb_ge; unfold FseNCount.Zlength; lia) end.
    rewrite DS1 in TL. cbn [bind] in TL. rewrite RL in TL. cbn [bind] in TL. rewrite NO in TL. cbn [bind] in TL.
    lazymatch type of TL with context [?a <? ?b] =>
      replace (a <? b) with false in TL
        by (symmetry; apply Z.ltb_ge; unfold FseNCount.Zlength; rewrite length_app; cbn [length]; lia) end.
    cbn [bind] in TL.
    destruct (l1_ds_cases (de_s2 x) d1r) as [[[[o1 s2a] d2] DS2] | DS2].
    - exists o1, s2a, d2. exact DS2.
    - rewrite DS2 in TL. cbn [bind] in TL. subst R. contradiction.
  Qed.

  Lemma l1_d1ok : forall bd nb, bitd_ok bs bd -> bd_bits bd <= 2^29 -> 0 <= nb <= 12 ->
    bitd_ok bs (mkBD (bd_cont bd) (bd_bits bd + nb) (bd_ptr bd) (bd_zero bd)).
  Proof.
    intros bd nb (H1 & H2 & H3 & H4 & H5 & H6) HB HN. unfold bitd_ok; cbn [bd_cont bd_bits bd_ptr bd_zero].
    refine (conj H1 (conj _ (conj H3 (conj H4 (conj H5 _))))); [lia | intros HZ; specialize (H6 HZ); lia].
  Qed.

  Lemma sdt_seg_e_pf : sdt_seg_e.
  Proof.
    unfold sdt_seg_e, sdt_c6416, sdt_c6956, sdt_c6300.
    intros f C16 C68 x R m jp OP0 I o0 s1a d1 d1r st1 ra a1 s6 s7 s9 s10 s11 TLx ROK K HI DS1 RL NO ZL1 HM.
    pose proof HI as (BOK & BB & ZL & OPI & DOP & I0).
    destruct (RF_huf_fdw_sm.dec_inv tl [] d ltac:(lia) HCELLS HCOK _ _ _ _ _ DS1 ltac:(destruct BOK as (_ & ? & _); lia))
      as (c1 & _ & _ & _ & NBR1 & _ & _ & _ & _ & ED1).
    assert (D1OK : bitd_ok bs d1) by (rewrite ED1; apply l1_d1ok; [exact BOK | exact BB | lia]).
    destruct (RF_huf_fdw_pure.reload_facts2 bs d1 st1 d1r BY D1OK RL) as (R1OK & R1B & _ & _ & R1O).
    assert (B64 : bd_bits d1 <= 64)
      by (destruct (Z_lt_le_dec 64 (bd_bits d1)) as [G|G]; [destruct (R1O G) as [E _]; rewrite NO in E; discriminate | exact G]).
    clear R1O ED1 NBR1 c1.
    destruct (l1_step2 f x R o0 s1a d1 st1 d1r TLx ROK ZL DS1 RL NO ZL1) as (o1 & s2a & d2 & DS2).
    pose proof R1OK as (BC & BBR & _).
    destruct (RF_huf_fdw_sm.dec_inv tl [] d ltac:(lia) HCELLS HCOK _ _ _ _ _ DS2 ltac:(lia))
      as (c & NC & S1R & SYR & NBR & NSR & NSR2 & EO & ES & ED).
    pose proof HM as ((MU & WM & MI & STK & C80 & C96 & (junk & OUTA & LJ)) & C112).
    destruct (HAT m MU WM) as (TBm & SRCm & FCm & ZDTm & ZMKm & ZDSTm & ZOBJm & USRCm & RTCm).
    set (s := de_s2 x) in *.
    assert (EC : c = cellAt s) by (symmetry; apply nth_error_nth; exact NC). subst c.
    assert (P2 : 32 <= 2^tl <= 4096) by (split; [change 32 with (2^5) | change 4096 with (2^12)]; apply Z.pow_le_mono_r; lia).
    pose proof ATOP_range as AR; unfold ATOP_MIN, ATOP_MAX in AR.
    assert (DTL : 1 <= DT /\ DT + 4 + 4 * 2^tl <= ATOP)
      by (destruct HDT as [[H1 H2]|[H1 H2]]; [unfold AIMG_HI in H1; unfold KLS in H2|]; lia).
    assert (DSTL : DST + dcap <= ATOP)
      by (destruct HDST as [[H1 H2]|[H1 H2]]; [unfold AIMG_HI in H1; unfold KLS in H2|]; lia).
    assert (ABM : 1 <= ABIT_MASK <= 2^47 - 4096) by (unfold ABIT_MASK; lia).
    pose proof (rng_mask_sh RNG RISH) as RMS.
    pose proof LO as LO'. unfold DEC_STACK in LO'.
    pose proof (spaf_props SPV SP16) as (SPAB & SPA32).
    assert (NS16 : 0 <= dc_newState (cellAt s) < 2^16) by (assert (0 < 2^dc_nbBits (cellAt s)) by (apply Z.pow_pos_nonneg; lia); lia).
    assert (V16 : 0 <= dc_symbol (cellAt s) + 256 * dc_nbBits (cellAt s) < 3328) by lia.
    assert (ZO1 : zlen (de_out x ++ [o0]) = zlen (de_out x) + 1) by (rewrite length_app; cbn [length]; lia).
    unfold bitdz_cellsA in C112.
    unfold ASHOFF. unfold ASHOFF in FCm.
    zstep. l1_n. zstep. l1_br.
    pose proof (RF_huf_fdw_kit.cell_rd_ns bsegs m (DT + 4) (dt_cells d) s (cellAt s) (wa (DT + 4 + 4 * s)) TBm NC ltac:(lia) ltac:(f_equal; lia)) as CR0.
    zstep. rewrite zx16_lit by lia. do 3 zstep. l1_n.
    wk_shz 22%Z.
    do 2 zstep. zstep. l1_br. do 2 zstep. l1_n.
    pose proof (maskA_rd m (dc_nbBits (cellAt s)) MI ltac:(lia)) as RMK.
    replace (4 * dc_nbBits (cellAt s)) with (dc_nbBits (cellAt s) * 4) in RMK by lia.
    pose proof (rng_acc_litZ' RNG _ _ (ABIT_MASK + dc_nbBits (cellAt s) * 4) 4 4 RI eq_refl eq_refl
                  ltac:(unfold ABIT_MASK; lia)) as ACM.
    zstep. l1_n. zstep. l1_n.
    rewrite (l1_sx32 (bd_bits d1r)) by lia.
    rewrite ?Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
    rewrite (Z.mod_small (bd_bits d1r)) by lia.
    rewrite (FseWalkKit.swrap32_small (bd_bits d1r + dc_nbBits (cellAt s))) by lia.
    l1_n.
    rewrite (FseWalkKit.swrap32_small (0 - (bd_bits d1r + dc_nbBits (cellAt s)))) by lia.
    assert (P12 : 1 <= 2 ^ dc_nbBits (cellAt s) <= 4096)
      by (split; [apply (Z.pow_le_mono_r 2 0); lia | change 4096 with (2^12); apply Z.pow_le_mono_r; lia]).
    rewrite (l1_zx32 (2 ^ dc_nbBits (cellAt s) - 1)) by lia.
    lazymatch goal with |- context [Z.lor (?V * ?K) (dc_newState (cellAt s))] =>
      replace (Z.lor (V * K) (dc_newState (cellAt s))) with (V * K + dc_newState (cellAt s))
        by (change K with (2^16); symmetry; apply l1_lor; lia) end.
    do 4 zstep. l1_n.
    lazymatch goal with |- context [Z.land (?V * ?K + dc_newState (cellAt s)) ?M] =>
      replace (Z.land (V * K + dc_newState (cellAt s)) M) with (dc_newState (cellAt s))
        by (change K with (2^16); change M with (2^16 - 1); symmetry; apply l1_land16; lia) end.
    zstep. l1_n.
    zstep. zstep. l1_br. do 3 zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (HAT mm MU WM) as (_ & _ & _ & _ & _ & ZD2 & _);
      pose proof (chkZ mm DST dcap (OP0 + I + 1) ZD2 ltac:(lia) ltac:(lia)) as RDB end.
    pose proof (acc_shZ RNG DST dcap (OP0 + I + 1) RDSTs ltac:(lia)) as ACO.
    zstep. rewrite ?sxb0. clear RDB. zstep. l1_br.
    zstep.
    lazymatch goal with |- context [(?V * ?K + dc_newState (cellAt s)) ≫ 16] =>
      replace ((V * K + dc_newState (cellAt s)) ≫ 16) with V
        by (change K with (2^16); rewrite Z.shiftr_div_pow2 by lia; l1_p2; l1_zl) end.
    set (out1 := de_out x ++ [o0]) in *.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u8arr_store_ok bsegs mm DST _ (zlen out1) (wa (OP0 + I + 1)) OUTA
                    ltac:(repeat (rewrite length_app || rewrite length_map); cbn [length]; lia) ltac:(f_equal; lia)) as SOK end.
    zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?mm (Z_to_bv 64 (OP0 + I + 1)) ?bs) _) =>
      change (write_to_mem mm (Z_to_bv 64 (OP0 + I + 1)) bs) with (write_to_mem mm (wa (OP0 + I + 1)) bs);
      replace (write_to_mem mm (wa (OP0 + I + 1)) bs) with (write_to_mem mm (wa (DST + zlen out1)) bs)
        by (replace (DST + zlen out1) with (OP0 + I + 1) by lia; reflexivity) end.
    rewrite le1_lit.
    replace (Z_to_bv 8 (dc_symbol (cellAt s) + 256 * dc_nbBits (cellAt s))) with (Z_to_bv 8 (dc_symbol (cellAt s)))
      by (apply bv_eq; rewrite !Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N];
          replace (dc_symbol (cellAt s) + 256 * dc_nbBits (cellAt s)) with (dc_symbol (cellAt s) + dc_nbBits (cellAt s) * 2 ^ 8) by lia;
          rewrite Z_mod_plus_full; reflexivity).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ _) _) =>
      pose proof (RF_huf_fdw_kit.out_sb bsegs mm DST out1 junk (dc_symbol (cellAt s)) OUTA
                    ltac:(lia)) as OUT2 end.
    assert (LJ2 : zlen (List.tl junk) = dcap - zlen (out1 ++ [dc_symbol (cellAt s)]))
      by (rewrite length_app; cbn [length]; rewrite RF_huf_fdw_sm.zlen_tl by lia; lia).
    clear OUTA LJ. store_done.
    zstep.
    unfold out1 in OUT2, LJ2. rewrite <- app_assoc in OUT2, LJ2.
    lazymatch type of C80 with rw_cells _ _ _ [C8 (Z_to_bv 64 ?V); _] =>
      replace V with s2a in C80 by (rewrite ES; symmetry; apply l1_s1v; first [reflexivity | lia]) end.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (SM : sdtM mm (de_out x ++ [o0; o1]) s1a s2a d2 jp)
        by (subst o1 d2; unfold sdtM, sdtM0;
            refine (conj (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (ex_intro _ (List.tl junk) (conj _ _)))))))) _);
            assumption) end.
    destruct (Z_lt_le_dec 64 (bd_bits d1r + dc_nbBits (cellAt s))) as [GT | LE].
    - l1_br. subst d2.
      exact (C68 x R _ jp OP0 I o0 s1a o1 s2a d1 d1r _ st1 ra _ _ _ _ _ _ _ _ _ _ _ TLx ROK K HI DS1 RL NO ZL1 DS2 GT SM).
    - l1_br. subst d2.
      exact (C16 x R _ jp OP0 I o0 s1a o1 s2a d1 d1r _ st1 ra _ _ _ _ _ _ _ _ TLx ROK K HI DS1 RL NO ZL1 DS2 LE SM).
  Qed.

  Ltac l3_br b := lazymatch goal with |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
    replace c with b; [cbv iota | symmetry; try unfold bv_lts;
      rewrite ?signed_lit_small64 by (rewrite ?land7_mod; first [lia | Z.div_mod_to_equations; lia]); rewrite ?land7_mod;
      rewrite ?bv_ltu_Z, ?bv_eqb_Z, ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
      cbn [Z.of_N]; rewrite ?Z.mod_small by lia;
      first [ apply Z.ltb_ge; lia | apply Z.ltb_lt; lia | apply Z.eqb_eq; lia | apply Z.eqb_neq; lia
            | apply Bool.negb_true_iff, Z.ltb_ge; lia | apply Bool.negb_false_iff, Z.ltb_lt; lia
            | apply Bool.negb_true_iff, Z.eqb_neq; lia | apply Bool.negb_false_iff, Z.eqb_eq; lia ] ] end.

  Definition l3_K5680 (f : nat) : Prop :=
    forall x' R m jp (OP0 I : Z) (ra a1 a2 a3 s3 s4 s5 s7 s8 s9 s10 s11 t6 : word),
      tail_loop bs d dcap false f x' = R -> dres_ok R -> sdtK R ->
      bitd_ok bs (de_bd x') -> bd_bits (de_bd x') <= 2^29 -> 2 <= zlen (de_out x') <= dcap ->
      OP0 + I + 2 = DST + zlen (de_out x') -> DST <= OP0 -> 0 <= I ->
      sdtM m (de_out x') (de_s1 x') (de_s2 x') (de_bd x') jp ->
      evtF bsegs RNG Q (TL (AFSE_DECOMP + 5680) m ra OP0 I a1 a2 a3 s3 s4 s5 (Z_to_bv 64 ASHOFF) s7 s8 s9 s10 s11 t6).

  Lemma l3_k5680_pf : forall f, sdt_head f -> l3_K5680 f.
  Proof.
    intros f HD. unfold l3_K5680.
    intros x' R m jp OP0 I ra a1 a2 a3 s3 s4 s5 s7 s8 s9 s10 s11 t6 TLR ROK K BOK BB ZL OPI DO I0 SM.
    pose proof (spaf_props SPV SP16) as (SPAB & SPA32). pose proof (ablk_lin _ _ HDST) as LDS.
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR. pose proof LO as LO'. unfold DEC_STACK in LO'.
    repeat zstep.
    destruct (Z.ltb_spec (dcap - 2) (zlen (de_out x'))) as [CK|CK].
    - l3_br true. repeat zstep.
      destruct f as [|f]; [cbn [tail_loop] in TLR; subst R; contradiction|].
      cbn [tail_loop] in TLR. change (FseNCount.Zlength (de_out x')) with (zlen (de_out x')) in TLR.
      replace (dcap - 2 <? zlen (de_out x')) with true in TLR by (symmetry; apply Z.ltb_lt; lia).
      subst R.
      destruct SM as ((MU & WM & MI & STK & C80 & C96 & OUT) & C112).
      assert (C1 : rw_cells bsegs m (SP1 + 80) ([C8 (Z_to_bv 64 (de_s2 x')); C8 (Z_to_bv 64 (DT + 4))]
                     ++ [C8 (Z_to_bv 64 (de_s1 x')); C8 (Z_to_bv 64 (DT + 4))] ++ bitdz_cellsA S0 (de_bd x') jp)).
      { apply kx_rw_cells_app. split; [exact C80|].
        replace (SP1 + 80 + Z.of_nat (cells_size _)) with (SP1 + 96) by (cbn [cells_size csize Nat.add length]; lia).
        apply kx_rw_cells_app. split; [exact C96|].
        replace (SP1 + 96 + Z.of_nat (cells_size _)) with (SP1 + 112) by (cbn [cells_size csize Nat.add length]; lia).
        exact C112. }
      assert (C1' : rw_cells bsegs m (SP1 + 80) ([] ++ ([C8 (Z_to_bv 64 (de_s2 x')); C8 (Z_to_bv 64 (DT + 4))]
                     ++ [C8 (Z_to_bv 64 (de_s1 x')); C8 (Z_to_bv 64 (DT + 4))] ++ bitdz_cellsA S0 (de_bd x') jp) ++ []))
        by (rewrite app_nil_r; exact C1).
      pose proof (rw_cells_merge _ _ _ _ _ _ C1') as C2. cbn [app] in C2.
      replace (Z_to_bv 64 (-70)) with (Z_to_bv 64 (2^64 - 70)) by (apply Z_to_bv_eqm; reflexivity).
      eapply (K m (2^64 - 70)); [exact MU | exact WM | exact MI | exact STK | exact C2
        | eapply rw_cells_transport; [exact FC32 | exact MU | exact WM | cbn; repeat split; lia]
        | cbn [dresA]; unfold ZSTD_error_dstSize_tooSmall; split; [reflexivity | lia] | lia ].
    - l3_br false. eapply HD; [exact TLR | exact ROK | exact K | | exact SM].
      unfold sdtI. refine (conj BOK (conj BB (conj _ (conj _ (conj DO _))))); lia.
  Qed.

  Lemma l3_rsh : forall a, S0 <= a < S0 + zlen bs -> rng RNG (Z.shiftr a 3 + ASHOFF) 1.
  Proof.
    intros a HA. eapply rng_sub; [exact RSs | |];
      unfold shad, nshad; rewrite !Z.shiftr_div_pow2 by (Z.div_mod_to_equations; lia); change (2^3) with 8;
      Z.div_mod_to_equations; lia.
  Qed.

  Lemma l3_sh : forall mm a, unpoisoned mm S0 (S0 + zlen bs) -> S0 <= a < S0 + zlen bs ->
    exists b, rw_cells bsegs mm (Z.shiftr a 3 + ASHOFF) [C1 b] /\ (sval b = 0 \/ (0 < sval b <= 7 /\ a mod 8 < sval b)).
  Proof.
    intros mm a U HA.
    destruct (unpoisoned_check bsegs mm S0 (S0 + zlen bs) a 1 U ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia))
      as (b & C & SV).
    exists b. split; [| lia]. replace (Z.shiftr a 3 + ASHOFF) with (shad a) by (unfold shad; lia). exact C.
  Qed.

  Definition l3_K5588 (f : nat) : Prop :=
    forall x' R m jp (OP0 I p b c : Z) (w0 ra a1 a3 s3 s4 s5 s7 s8 s9 s10 s11 t6 : word),
      tail_loop bs d dcap false f x' = R -> dres_ok R -> sdtK R ->
      de_bd x' = mkBD c b p false -> readLE64 bs p = Ok c ->
      bitd_ok bs (de_bd x') -> bd_bits (de_bd x') <= 2^29 -> 2 <= zlen (de_out x') <= dcap ->
      OP0 + I + 2 = DST + zlen (de_out x') -> DST <= OP0 -> 0 <= I ->
      sdtM0 m (de_out x') (de_s1 x') (de_s2 x') ->
      rw_cells bsegs m (SP1 + 112) [C8 w0; C4 (Z_to_bv 64 b); CB 4 jp; C8 (Z_to_bv 64 (S0 + p)); C8 (Z_to_bv 64 S0); C8 (Z_to_bv 64 (S0 + 8))] ->
      evtF bsegs RNG Q (TL (AFSE_DECOMP + 5588) m ra OP0 I a1 (Z_to_bv 64 (S0 + p)) a3 s3 s4 s5 (Z_to_bv 64 ASHOFF) s7 s8 s9 s10 s11 t6).

  Definition l3_K6552 (f : nat) : Prop :=
    forall x' R m jp (OP0 I q p b c : Z) (w0 w1 w3 ra s3 s4 s5 s7 s8 s9 s10 s11 t6 : word),
      tail_loop bs d dcap false f x' = R -> dres_ok R -> sdtK R ->
      de_bd x' = mkBD c b p false -> readLE64 bs p = Ok c ->
      bitd_ok bs (de_bd x') -> bd_bits (de_bd x') <= 2^29 -> 2 <= zlen (de_out x') <= dcap ->
      OP0 + I + 2 = DST + zlen (de_out x') -> DST <= OP0 -> 0 <= I -> 0 <= q <= zlen bs ->
      sdtM0 m (de_out x') (de_s1 x') (de_s2 x') ->
      rw_cells bsegs m (SP1 + 112) [C8 w0; C4 w1; CB 4 jp; C8 w3; C8 (Z_to_bv 64 S0); C8 (Z_to_bv 64 (S0 + 8))] ->
      evtF bsegs RNG Q (TL (AFSE_DECOMP + 6552) m ra OP0 I (Z_to_bv 64 (S0 + q)) (Z_to_bv 64 (S0 + p)) (Z_to_bv 64 b)
                           s3 s4 s5 (Z_to_bv 64 ASHOFF) s7 s8 s9 s10 s11 t6).

  Lemma l3_k6552_pf : forall f, l3_K5588 f -> l3_K6552 f.
  Proof.
    intros f K55. unfold l3_K6552.
    intros x' R m jp OP0 I q p b c w0 w1 w3 ra s3 s4 s5 s7 s8 s9 s10 s11 t6 TLR ROK K XB RLE BOK BB ZL OPI DO I0 Q0 SM0 C112.
    pose proof (spaf_props SPV SP16) as (SPAB & SPA32). pose proof (ablk_lin _ _ HDST) as LDS. pose proof (ablk_lin _ _ HS0) as LS0.
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR. pose proof LO as LO'. unfold DEC_STACK in LO'.
    pose proof SM0 as (MU & WM & MI & STK & C80 & C96 & OUT). destruct OUT as (junk & UA & LJ). clear SM0.
    pose proof RLE as RLE'. unfold readLE64 in RLE'. change (FseNCount.Zlength bs) with (zlen bs) in RLE'.
    destruct ((0 <=? p) && (p + 8 <=? zlen bs)) eqn:PR; [|discriminate RLE']. clear RLE'.
    apply andb_true_iff in PR. destruct PR as [PR1 PR2]. apply Z.leb_le in PR1. apply Z.leb_le in PR2.
    pose proof BOK as (BK1 & BK2 & _). rewrite XB in BK1, BK2. cbn [bd_cont bd_bits] in BK1, BK2.
    repeat zstep. l3_br false. repeat zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      let MUx := fresh "MUx" in let WMx := fresh "WMx" in
      assert (MUx : munch W0 m0 mm) by assumption; assert (WMx : wmono bsegs m0 mm) by assumption;
      destruct (HAT mm MUx WMx) as (_ & SRCx & _ & _ & _ & _ & _ & USx & _);
      destruct (l3_sh mm (S0 + p) USx ltac:(lia)) as (b1 & SH1 & SV1);
      destruct (l3_sh mm (S0 + p + 7) USx ltac:(lia)) as (b2 & SH2 & SV2)
    end.
    pose proof (l3_rsh (S0 + p) ltac:(lia)) as RH1. pose proof (l3_rsh (S0 + p + 7) ltac:(lia)) as RH2.
    assert (SHB1 : 0 <= Z.shiftr (S0 + p) 3 <= S0 + p) by (rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
    assert (SHB2 : 0 <= Z.shiftr (S0 + p + 7) 3 <= S0 + p + 7) by (rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
    unfold ASHOFF in SH1, SH2, RH1, RH2 |- *.
    repeat zstep.
    rewrite sxb_sval. pose proof (sval_range b1) as SR1. pose proof (sval_range b2) as SR2.
    destruct SV1 as [Z1 | (P1 & L1)]; [l3_br false; repeat zstep | l3_br true; repeat zstep; l3_br true; repeat zstep].
    all: rewrite sxb_sval; destruct SV2 as [Z2 | (P2 & L2)]; [l3_br true | l3_br false; repeat zstep; l3_br true].
    all: lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply (K55 x' R mm jp OP0 I p b c); [exact TLR | exact ROK | exact K | exact XB | exact RLE | exact BOK | exact BB | exact ZL
        | exact OPI | exact DO | exact I0 | | eassumption ] end.
    all: unfold sdtM0; refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (ex_intro _ junk (conj _ LJ)))))))); eassumption.
  Qed.

  Lemma l3_fs1 : forall (l : list Z) n, (n < length l)%nat -> firstn 1 (skipn n (map (Z_to_bv 8) l)) = [Z_to_bv 8 (nth n l 0)].
  Proof.
    induction l as [|a l IH]; intros n Hn; [cbn in Hn; lia|].
    destruct n as [|n]; [reflexivity|]. cbn [skipn map nth]. apply IH. cbn in Hn. lia.
  Qed.

  Lemma l3_rd1 : forall mm k, bytes_at bsegs mm S0 (map (Z_to_bv 8) bs) -> 0 <= k < zlen bs ->
    ov_read_bytes bsegs mm (wa (S0 + k)) 1 = Some [Z_to_bv 8 (Znth k bs)].
  Proof.
    intros mm k H Hk. change (zlen bs) with (Z.of_nat (length bs)) in Hk.
    replace (S0 + k) with (S0 + Z.of_nat (Z.to_nat k)) by lia.
    rewrite (bytes_at_ov_read bsegs mm S0 _ (Z.to_nat k) 1 H) by (rewrite length_map; lia).
    rewrite l3_fs1 by lia. reflexivity.
  Qed.

  Lemma l3_by : forall k, 0 <= k < zlen bs -> 0 <= Znth k bs < 256.
  Proof.
    intros k Hk. pose proof BY as BY'. rewrite Forall_forall in BY'. apply BY'.
    change (zlen bs) with (Z.of_nat (length bs)) in Hk. unfold Znth. apply nth_In. lia.
  Qed.

  Lemma l3_k5588_pf : forall f, l3_K5680 f -> l3_K5588 f.
  Proof.
    intros f K5. unfold l3_K5588.
    intros x' R m jp OP0 I p b c w0 ra a1 a3 s3 s4 s5 s7 s8 s9 s10 s11 t6 TLR ROK K XB RLE BOK BB ZL OPI DO I0 SM0 C112.
    pose proof (spaf_props SPV SP16) as (SPAB & SPA32). pose proof (ablk_lin _ _ HDST) as LDS. pose proof (ablk_lin _ _ HS0) as LS0.
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR. pose proof LO as LO'. unfold DEC_STACK in LO'.
    pose proof SM0 as (MU & WM & MI & STK & C80 & C96 & OUT). destruct OUT as (junk & UA & LJ). clear SM0.
    destruct (HAT m MU WM) as (_ & SRCm & _ & _ & _ & _ & _ & _ & _).
    pose proof RLE as RLE'. unfold readLE64 in RLE'. change (FseNCount.Zlength bs) with (zlen bs) in RLE'.
    destruct ((0 <=? p) && (p + 8 <=? zlen bs)) eqn:PR; [|discriminate RLE']. injection RLE' as RLE'.
    apply andb_true_iff in PR. destruct PR as [PR1 PR2]. apply Z.leb_le in PR1. apply Z.leb_le in PR2.
    pose proof (l3_rd1 m p SRCm ltac:(lia)) as HR0. pose proof (l3_rd1 m (p + 1) SRCm ltac:(lia)) as HR1.
    pose proof (l3_rd1 m (p + 2) SRCm ltac:(lia)) as HR2. pose proof (l3_rd1 m (p + 3) SRCm ltac:(lia)) as HR3.
    pose proof (l3_rd1 m (p + 4) SRCm ltac:(lia)) as HR4. pose proof (l3_rd1 m (p + 5) SRCm ltac:(lia)) as HR5.
    pose proof (l3_rd1 m (p + 6) SRCm ltac:(lia)) as HR6. pose proof (l3_rd1 m (p + 7) SRCm ltac:(lia)) as HR7.
    do 23 zstep.
    match goal with H : rw_cells bsegs _ (SP1 + 112) _ |- _ => rewrite le64_lbu_land in H by (apply l3_by; lia) end.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply (K5 x' R mm jp OP0 I); [exact TLR | exact ROK | exact K | exact BOK | exact BB | exact ZL | exact OPI | exact DO | exact I0 | ] end.
    split.
    - unfold sdtM0; refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (ex_intro _ junk (conj _ LJ)))))))); eassumption.
    - rewrite XB. unfold bitdz_cellsA. cbn [bd_cont bd_bits bd_ptr bd_zero]. rewrite <- RLE'. eassumption.
  Qed.

  Lemma l3_ds : forall s bd o s' bd', decode_sym d false s bd = Ok (o, s', bd') -> 0 <= bd_bits bd < 2^30 ->
    bd_cont bd' = bd_cont bd /\ bd_ptr bd' = bd_ptr bd /\ bd_zero bd' = bd_zero bd /\ bd_bits bd <= bd_bits bd' <= bd_bits bd + 12.
  Proof.
    intros s bd o s' bd' H B. unfold decode_sym, HufPure_FseDecomp.cell in H.
    destruct ((0 <=? s) && (s <? FseNCount.Zlength (dt_cells d))) eqn:E; [|discriminate H].
    cbn [bind] in H. unfold read_bits in H.
    destruct (look_bits bd (dc_nbBits (nth (Z.to_nat s) (dt_cells d) (mkDC 0 0 0)))) eqn:LB; cbn [bind] in H; try discriminate H.
    injection H as _ _ <-. unfold skip_bits. cbn [bd_cont bd_bits bd_ptr bd_zero].
    assert (NB : 0 <= dc_nbBits (nth (Z.to_nat s) (dt_cells d) (mkDC 0 0 0)) <= tl).
    { pose proof HCOK as HC. unfold RF_huf_fdw_sm.cells_ok in HC. rewrite Forall_forall in HC.
      apply andb_true_iff in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
      change (FseNCount.Zlength (dt_cells d)) with (Z.of_nat (length (dt_cells d))) in E2.
      destruct (HC (nth (Z.to_nat s) (dt_cells d) (mkDC 0 0 0))) as (_ & HN & _); [apply nth_In; lia | lia]. }
    unfold u32. rewrite Z.mod_small by lia. repeat split; lia.
  Qed.

  Lemma l3_bok : forall x o0 s1a d1 st1 d1r o1 s2a d2,
    bitd_ok bs (de_bd x) ->
    decode_sym d false (de_s1 x) (de_bd x) = Ok (o0, s1a, d1) -> reload_dstream bs d1 = Ok (st1, d1r) ->
    dstatus_eqb st1 Overflow = false ->
    decode_sym d false (de_s2 x) d1r = Ok (o1, s2a, d2) -> bd_bits d2 <= 64 -> bitd_ok bs d2 /\ bd_zero d2 = false.
  Proof.
    intros x o0 s1a d1 st1 d1r o1 s2a d2 BK D1 R1 S1 D2 B2.
    pose proof BK as (K1 & K2 & K3 & K4 & K5 & K6).
    destruct (l3_ds _ _ _ _ _ D1 ltac:(lia)) as (E1 & E2 & E3 & E4).
    assert (B1 : bd_bits d1 <= 64).
    { destruct (Z.leb_spec (bd_bits d1) 64) as [|G]; [lia|]. unfold reload_dstream in R1.
      replace (64 <? bd_bits d1) with true in R1 by (symmetry; apply Z.ltb_lt; lia).
      injection R1 as <- _. discriminate S1. }
    assert (Z1 : bd_zero d1 = false).
    { rewrite E3. destruct (bd_zero (de_bd x)) eqn:ZX; [|reflexivity]. specialize (K6 eq_refl). lia. }
    assert (OK1 : bitd_ok bs d1).
    { unfold bitd_ok. rewrite E1, E2. repeat split; try lia. intros ZZ. rewrite Z1 in ZZ. discriminate ZZ. }
    pose proof (RF_huf_fdw_pure.reload_facts2 bs d1 st1 d1r BY OK1 R1) as (OK2 & BB2 & _ & Z2 & _).
    destruct (Z2 B1) as [ZZ2 _].
    pose proof OK2 as (L1 & L2 & L3 & L4 & L5 & L6).
    destruct (l3_ds _ _ _ _ _ D2 ltac:(lia)) as (F1 & F2 & F3 & F4).
    split; [| rewrite F3; exact ZZ2].
    unfold bitd_ok. rewrite F1, F2, F3. repeat split; try lia. intros ZZ. rewrite ZZ2 in ZZ. discriminate ZZ.
  Qed.

  Lemma l3_tl : forall f x R o0 s1a d1 st1 d1r o1 s2a d2 st2 d2r,
    tail_loop bs d dcap false (S f) x = R -> zlen (de_out x) <= dcap - 2 ->
    decode_sym d false (de_s1 x) (de_bd x) = Ok (o0, s1a, d1) ->
    reload_dstream bs d1 = Ok (st1, d1r) -> dstatus_eqb st1 Overflow = false -> zlen (de_out x) + 1 <= dcap - 2 ->
    decode_sym d false (de_s2 x) d1r = Ok (o1, s2a, d2) ->
    reload_dstream bs d2 = Ok (st2, d2r) -> dstatus_eqb st2 Overflow = false ->
    tail_loop bs d dcap false f (mkDec (de_out x ++ [o0; o1]) s1a s2a d2r) = R.
  Proof.
    intros f x R o0 s1a d1 st1 d1r o1 s2a d2 st2 d2r TL0 Z0 D1 R1 S1 Z1 D2 R2 S2. subst R. cbn [tail_loop].
    change (FseNCount.Zlength (de_out x)) with (zlen (de_out x)).
    replace (dcap - 2 <? zlen (de_out x)) with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite D1. cbn [bind]. rewrite R1. cbn [bind]. rewrite S1.
    replace (dcap - 2 <? FseNCount.Zlength (de_out x ++ [o0])) with false
      by (symmetry; apply Z.ltb_ge; change (FseNCount.Zlength (de_out x ++ [o0])) with (Z.of_nat (length (de_out x ++ [o0])));
          change (zlen (de_out x)) with (Z.of_nat (length (de_out x))) in Z1; rewrite length_app; cbn [length]; lia).
    rewrite D2. cbn [bind]. rewrite R2. cbn [bind]. rewrite S2. rewrite <- app_assoc. reflexivity.
  Qed.

  Lemma l3_zl2 : forall (l : list Z) a b, zlen (l ++ [a; b]) = zlen l + 2.
  Proof.
    intros l a b. change (zlen (l ++ [a; b])) with (Z.of_nat (length (l ++ [a; b]))).
    change (zlen l) with (Z.of_nat (length l)). rewrite length_app. cbn [length]. lia.
  Qed.

  Definition l3_C (P : bitD -> Prop) (f : nat) : Prop :=
    forall x R m jp (OP0 I o0 s1a o1 s2a : Z) (d1 d1r d2 : bitD) (st1 : dstatus) (ra a1 a2 s3 s7 s8 s9 s10 s11 : word),
      tail_loop bs d dcap false (S f) x = R -> dres_ok R -> sdtK R -> sdtI x OP0 I ->
      decode_sym d false (de_s1 x) (de_bd x) = Ok (o0, s1a, d1) ->
      reload_dstream bs d1 = Ok (st1, d1r) -> dstatus_eqb st1 Overflow = false -> zlen (de_out x) + 1 <= dcap - 2 ->
      decode_sym d false (de_s2 x) d1r = Ok (o1, s2a, d2) -> bd_bits d2 <= 64 ->
      bitd_ok bs d2 -> bd_zero d2 = false -> P d2 ->
      sdtM m (de_out x ++ [o0; o1]) s1a s2a d2 jp ->
      evtF bsegs RNG Q (TL (AFSE_DECOMP + 6416) m ra OP0 I a1 a2 (Z_to_bv 64 (bd_bits d2)) s3
                           (Z_to_bv 64 (OP0 + I)) (Z_to_bv 64 (OP0 + I + 1)) (Z_to_bv 64 ASHOFF) s7 s8 s9 s10 s11
                           (Z_to_bv 64 (S0 + 8))).

  Lemma l3_cases : forall f,
    l3_C (fun d2 => 8 <= bd_ptr d2) f -> l3_C (fun d2 => bd_ptr d2 = 0) f ->
    l3_C (fun d2 => 1 <= bd_ptr d2 <= 7 /\ bd_ptr d2 - Z.shiftr (bd_bits d2) 3 < 0) f ->
    l3_C (fun d2 => 1 <= bd_ptr d2 <= 7 /\ 0 <= bd_ptr d2 - Z.shiftr (bd_bits d2) 3) f -> sdt_c6416 f.
  Proof.
    intros f CF CZ CC CP. unfold sdt_c6416.
    intros x R m jp OP0 I o0 s1a o1 s2a d1 d1r d2 st1 ra a1 a2 s3 s7 s8 s9 s10 s11 TLR ROK K SI D1 R1 S1 ZO D2 B2 SM.
    destruct (l3_bok x o0 s1a d1 st1 d1r o1 s2a d2 (proj1 SI) D1 R1 S1 D2 B2) as [OK2 Z2].
    pose proof OK2 as (_ & _ & P0 & _).
    destruct (Z_le_gt_dec 8 (bd_ptr d2)) as [G8|G8]; [eapply CF; eassumption|].
    destruct (Z.eq_dec (bd_ptr d2) 0) as [E0|E0]; [eapply CZ; eassumption|].
    destruct (Z_lt_ge_dec (bd_ptr d2 - Z.shiftr (bd_bits d2) 3) 0) as [L0|L0].
    - eapply CC; [eassumption .. | split; lia | eassumption].
    - eapply CP; [eassumption .. | split; lia | eassumption].
  Qed.

  Lemma l3_ne : forall a k, 0 < a -> 0 <= k -> a <> k -> Z.lxor (Z.b2z (0 <? a)) (Z.b2z (Z.lxor a k <? 1)) = 1.
  Proof.
    intros a k A K N. replace (0 <? a) with true by (symmetry; apply Z.ltb_lt; lia).
    replace (Z.lxor a k <? 1) with false; [reflexivity|].
    symmetry. apply Z.ltb_ge.
    assert (0 <= Z.lxor a k) by (apply Z.lxor_nonneg; split; lia).
    assert (Z.lxor a k <> 0) by (intro E; apply Z.lxor_eq in E; lia). lia.
  Qed.

  Ltac l3_pre :=
    pose proof (spaf_props SPV SP16) as (SPAB & SPA32); pose proof (ablk_lin _ _ HDST) as LDS; pose proof (ablk_lin _ _ HS0) as LS0;
    pose proof ATOP_range as ATR; unfold ATOP_MIN, ATOP_MAX in ATR; pose proof LO as LO'; unfold DEC_STACK in LO'.

  Ltac l3_land32 := match goal with |- context [Z.land ?x ?M] =>
    replace (Z.land x M) with x by (symmetry; change M with (Z.ones 32); rewrite Z.land_ones by lia; apply Z.mod_small; lia) end.

  Ltac l3_sub3 B X :=
    match goal with |- context [bv_swrap 32 (B - Z.land (Z.shiftl X 3) ?M)] =>
      let LQ := fresh "LQ" in
      assert (LQ : Z.land (Z.shiftl X 3) M = X * 8)
        by (first [change M with (Z.ones 64) | change M with (Z.ones 32)]; rewrite Z.land_ones by lia;
            rewrite Z.shiftl_mul_pow2 by lia; change (2^3) with 8; apply Z.mod_small; lia);
      rewrite LQ; rewrite (swrap32_small (B - X * 8)) by lia; clear LQ
    end.

  Lemma l3_cfast : forall f, l3_K6552 f -> l3_C (fun d2 => 8 <= bd_ptr d2) f.
  Proof.
    intros f K6. unfold l3_C.
    intros x R m jp OP0 I o0 s1a o1 s2a d1 d1r d2 st1 ra a1 a2 s3 s7 s8 s9 s10 s11 TLR ROK K SI D1 R1 S1 ZO D2 B2 OK2 Z2 P8 SM.
    l3_pre.
    pose proof SI as (SI1 & SI2 & SI3 & SI4 & SI5 & SI6).
    pose proof OK2 as (O1 & O2 & O3 & O4 & O5 & O6).
    assert (ZL8 : 8 <= zlen bs) by (destruct (Z_lt_ge_dec (zlen bs) 8) as [h|h]; [specialize (O5 h); lia | lia]).
    assert (SH : Z.shiftr (bd_bits d2) 3 = bd_bits d2 / 8) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    pose (p := bd_ptr d2 - Z.shiftr (bd_bits d2) 3).
    assert (PB : 0 <= p /\ p + 8 <= zlen bs) by (unfold p; rewrite SH; Z.div_mod_to_equations; lia).
    assert (RLp : exists c, readLE64 bs p = Ok c).
    { unfold readLE64. change (FseNCount.Zlength bs) with (zlen bs).
      replace ((0 <=? p) && (p + 8 <=? zlen bs)) with true by (symmetry; apply andb_true_iff; split; apply Z.leb_le; lia).
      eexists; reflexivity. }
    destruct RLp as (c & RLp).
    assert (RL2 : reload_dstream bs d2 = Ok (Unfinished, mkBD c (Z.land (bd_bits d2) 7) p false)).
    { unfold reload_dstream. replace (64 <? bd_bits d2) with false by (symmetry; apply Z.ltb_ge; lia).
      replace (8 <=? bd_ptr d2) with true by (symmetry; apply Z.leb_le; lia). cbv zeta.
      change (bd_ptr d2 - Z.shiftr (bd_bits d2) 3) with p. rewrite RLp. reflexivity. }
    pose proof (RF_huf_fdw_pure.reload_facts2 bs d2 Unfinished _ BY OK2 RL2) as (OK3 & BB3 & _ & _ & _).
    assert (TL' : tail_loop bs d dcap false f (mkDec (de_out x ++ [o0; o1]) s1a s2a (mkBD c (Z.land (bd_bits d2) 7) p false)) = R)
      by (eapply l3_tl; [exact TLR | lia | exact D1 | exact R1 | exact S1 | exact ZO | exact D2 | exact RL2 | reflexivity]).
    destruct SM as (SM0 & C112). unfold bitdz_cellsA in C112. rewrite Z2 in C112.
    change (if false then AZEROFILLED else S0 + bd_ptr d2) with (S0 + bd_ptr d2) in C112.
    pose proof SM0 as (MU & WM & MI & STK & C80 & C96 & OUT).
    repeat zstep.
    l3_br true. repeat zstep.
    assert (SW : bv_swrap 32 (Z.shiftr (bv_wrap 32 (bd_bits d2)) 3) = Z.shiftr (bd_bits d2) 3).
    { replace (bv_wrap 32 (bd_bits d2)) with (bd_bits d2) by (unfold bv_wrap, bv_modulus; cbn [Z.of_N]; rewrite Z.mod_small by lia; reflexivity).
      apply swrap32_small. rewrite SH. Z.div_mod_to_equations; lia. }
    rewrite SW. l3_br false. repeat zstep.
    rewrite l3_ne by (rewrite ?SH; Z.div_mod_to_equations; lia). l3_br false. do 2 zstep.
    replace (Z_to_bv 64 (S0 + bd_ptr d2 - Z.shiftr (bd_bits d2) 3)) with (Z_to_bv 64 (S0 + p)) by (f_equal; unfold p; lia).
    eapply (K6 (mkDec (de_out x ++ [o0; o1]) s1a s2a (mkBD c (Z.land (bd_bits d2) 7) p false)) R m jp OP0 I (bd_ptr d2) p
              (Z.land (bd_bits d2) 7) c);
      [exact TL' | exact ROK | exact K | reflexivity | exact RLp | exact OK3 | cbn [de_bd bd_bits] in BB3 |- *; lia
      | cbn [de_out]; rewrite l3_zl2; lia | cbn [de_out]; rewrite l3_zl2; lia | exact SI5 | exact SI6 | lia | exact SM0 | exact C112].
  Qed.

  Lemma l3_czero : forall f, l3_K5680 f -> l3_C (fun d2 => bd_ptr d2 = 0) f.
  Proof.
    intros f K5. unfold l3_C.
    intros x R m jp OP0 I o0 s1a o1 s2a d1 d1r d2 st1 ra a1 a2 s3 s7 s8 s9 s10 s11 TLR ROK K SI D1 R1 S1 ZO D2 B2 OK2 Z2 P0 SM.
    l3_pre.
    pose proof SI as (SI1 & SI2 & SI3 & SI4 & SI5 & SI6).
    pose proof OK2 as (O1 & O2 & O3 & O4 & O5 & O6).
    assert (RL2 : reload_dstream bs d2 = Ok ((if bd_bits d2 <? 64 then EndOfBuffer else Completed), d2)).
    { unfold reload_dstream. replace (64 <? bd_bits d2) with false by (symmetry; apply Z.ltb_ge; lia).
      replace (8 <=? bd_ptr d2) with false by (symmetry; apply Z.leb_gt; lia). rewrite P0. reflexivity. }
    assert (TL' : tail_loop bs d dcap false f (mkDec (de_out x ++ [o0; o1]) s1a s2a d2) = R)
      by (eapply l3_tl; [exact TLR | lia | exact D1 | exact R1 | exact S1 | exact ZO | exact D2 | exact RL2
                        | destruct (bd_bits d2 <? 64); reflexivity]).
    pose proof SM as (SM0 & C112). unfold bitdz_cellsA in C112. rewrite Z2 in C112.
    change (if false then AZEROFILLED else S0 + bd_ptr d2) with (S0 + bd_ptr d2) in C112.
    pose proof SM0 as (MU & WM & MI & STK & C80 & C96 & OUT).
    repeat zstep. l3_br false. repeat zstep. l3_br true.
    eapply (K5 (mkDec (de_out x ++ [o0; o1]) s1a s2a d2) R m jp OP0 I);
      [exact TL' | exact ROK | exact K | exact OK2 | cbn [de_bd]; lia | cbn [de_out]; rewrite l3_zl2; lia
      | cbn [de_out]; rewrite l3_zl2; lia | exact SI5 | exact SI6 | exact SM].
  Qed.

  Lemma l3_cpart : forall f, l3_K6552 f -> l3_C (fun d2 => 1 <= bd_ptr d2 <= 7 /\ 0 <= bd_ptr d2 - Z.shiftr (bd_bits d2) 3) f.
  Proof.
    intros f K6. unfold l3_C.
    intros x R m jp OP0 I o0 s1a o1 s2a d1 d1r d2 st1 ra a1 a2 s3 s7 s8 s9 s10 s11 TLR ROK K SI D1 R1 S1 ZO D2 B2 OK2 Z2 (PQ & PN) SM.
    l3_pre.
    pose proof SI as (SI1 & SI2 & SI3 & SI4 & SI5 & SI6).
    pose proof OK2 as (O1 & O2 & O3 & O4 & O5 & O6).
    assert (ZL8 : 8 <= zlen bs) by (destruct (Z_lt_ge_dec (zlen bs) 8) as [h|h]; [specialize (O5 h); lia | lia]).
    assert (SH : Z.shiftr (bd_bits d2) 3 = bd_bits d2 / 8) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    pose (p := bd_ptr d2 - Z.shiftr (bd_bits d2) 3).
    assert (PB : 0 <= p /\ p + 8 <= zlen bs) by (unfold p; rewrite SH; Z.div_mod_to_equations; lia).
    assert (RLp : exists c, readLE64 bs p = Ok c).
    { unfold readLE64. change (FseNCount.Zlength bs) with (zlen bs).
      replace ((0 <=? p) && (p + 8 <=? zlen bs)) with true by (symmetry; apply andb_true_iff; split; apply Z.leb_le; lia).
      eexists; reflexivity. }
    destruct RLp as (c & RLp).
    assert (RL2 : reload_dstream bs d2 = Ok (Unfinished, mkBD c (bd_bits d2 - Z.shiftr (bd_bits d2) 3 * 8) p false)).
    { unfold reload_dstream. replace (64 <? bd_bits d2) with false by (symmetry; apply Z.ltb_ge; lia).
      replace (8 <=? bd_ptr d2) with false by (symmetry; apply Z.leb_gt; lia).
      replace (bd_ptr d2 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv beta iota zeta.
      replace (bd_ptr d2 - Z.shiftr (bd_bits d2) 3 <? 0) with false by (symmetry; apply Z.ltb_ge; lia). cbv beta iota zeta.
      change (bd_ptr d2 - Z.shiftr (bd_bits d2) 3) with p. rewrite RLp. reflexivity. }
    pose proof (RF_huf_fdw_pure.reload_facts2 bs d2 Unfinished _ BY OK2 RL2) as (OK3 & BB3 & _ & _ & _).
    assert (TL' : tail_loop bs d dcap false f
                    (mkDec (de_out x ++ [o0; o1]) s1a s2a (mkBD c (bd_bits d2 - Z.shiftr (bd_bits d2) 3 * 8) p false)) = R)
      by (eapply l3_tl; [exact TLR | lia | exact D1 | exact R1 | exact S1 | exact ZO | exact D2 | exact RL2 | reflexivity]).
    destruct SM as (SM0 & C112). unfold bitdz_cellsA in C112. rewrite Z2 in C112.
    change (if false then AZEROFILLED else S0 + bd_ptr d2) with (S0 + bd_ptr d2) in C112.
    pose proof SM0 as (MU & WM & MI & STK & C80 & C96 & OUT).
    assert (SHB : 0 <= Z.shiftr (bd_bits d2) 3 <= 8) by (rewrite SH; Z.div_mod_to_equations; lia).
    assert (SW : bv_swrap 32 (Z.shiftr (bv_wrap 32 (bd_bits d2)) 3) = Z.shiftr (bd_bits d2) 3).
    { replace (bv_wrap 32 (bd_bits d2)) with (bd_bits d2) by (unfold bv_wrap, bv_modulus; cbn [Z.of_N]; rewrite Z.mod_small by lia; reflexivity).
      apply swrap32_small. rewrite SH. Z.div_mod_to_equations; lia. }
    repeat zstep. l3_br false. repeat zstep. l3_br false. repeat zstep.
    rewrite SW. l3_br false. repeat zstep.
    rewrite l3_ne by (rewrite ?SH; Z.div_mod_to_equations; lia). l3_br false. repeat zstep.
    l3_br true. repeat zstep.
    l3_land32.
    l3_br false. repeat zstep.
    rewrite l3_ne by (rewrite ?SH; Z.div_mod_to_equations; lia). l3_br false. do 4 zstep.
    l3_sub3 (bd_bits d2) (Z.shiftr (bd_bits d2) 3).
    replace (Z_to_bv 64 (S0 + bd_ptr d2 - Z.shiftr (bd_bits d2) 3)) with (Z_to_bv 64 (S0 + p)) by (f_equal; unfold p; lia).
    eapply (K6 (mkDec (de_out x ++ [o0; o1]) s1a s2a (mkBD c (bd_bits d2 - Z.shiftr (bd_bits d2) 3 * 8) p false)) R m jp OP0 I
              (bd_ptr d2) p (bd_bits d2 - Z.shiftr (bd_bits d2) 3 * 8) c);
      [exact TL' | exact ROK | exact K | reflexivity | exact RLp | exact OK3 | cbn [de_bd bd_bits] in BB3 |- *; lia
      | cbn [de_out]; rewrite l3_zl2; lia | cbn [de_out]; rewrite l3_zl2; lia | exact SI5 | exact SI6 | lia | exact SM0 | exact C112].
  Qed.

  Lemma l3_cclamp : forall f, l3_K6552 f -> l3_C (fun d2 => 1 <= bd_ptr d2 <= 7 /\ bd_ptr d2 - Z.shiftr (bd_bits d2) 3 < 0) f.
  Proof.
    intros f K6. unfold l3_C.
    intros x R m jp OP0 I o0 s1a o1 s2a d1 d1r d2 st1 ra a1 a2 s3 s7 s8 s9 s10 s11 TLR ROK K SI D1 R1 S1 ZO D2 B2 OK2 Z2 (PQ & PN) SM.
    l3_pre.
    pose proof SI as (SI1 & SI2 & SI3 & SI4 & SI5 & SI6).
    pose proof OK2 as (O1 & O2 & O3 & O4 & O5 & O6).
    assert (ZL8 : 8 <= zlen bs) by (destruct (Z_lt_ge_dec (zlen bs) 8) as [h|h]; [specialize (O5 h); lia | lia]).
    assert (SH : Z.shiftr (bd_bits d2) 3 = bd_bits d2 / 8) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    assert (SHB : 0 <= Z.shiftr (bd_bits d2) 3 <= 8) by (rewrite SH; Z.div_mod_to_equations; lia).
    assert (RLp : exists c, readLE64 bs 0 = Ok c).
    { unfold readLE64. change (FseNCount.Zlength bs) with (zlen bs).
      replace ((0 <=? 0) && (0 + 8 <=? zlen bs)) with true by (symmetry; apply andb_true_iff; split; apply Z.leb_le; lia).
      eexists; reflexivity. }
    destruct RLp as (c & RLp).
    assert (RL2 : reload_dstream bs d2 = Ok (EndOfBuffer, mkBD c (bd_bits d2 - bd_ptr d2 * 8) 0 false)).
    { unfold reload_dstream. replace (64 <? bd_bits d2) with false by (symmetry; apply Z.ltb_ge; lia).
      replace (8 <=? bd_ptr d2) with false by (symmetry; apply Z.leb_gt; lia).
      replace (bd_ptr d2 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv beta iota zeta.
      replace (bd_ptr d2 - Z.shiftr (bd_bits d2) 3 <? 0) with true by (symmetry; apply Z.ltb_lt; lia). cbv beta iota zeta.
      replace (bd_ptr d2 - bd_ptr d2) with 0 by lia. rewrite RLp. reflexivity. }
    pose proof (RF_huf_fdw_pure.reload_facts2 bs d2 EndOfBuffer _ BY OK2 RL2) as (OK3 & BB3 & _ & _ & _).
    assert (TL' : tail_loop bs d dcap false f
                    (mkDec (de_out x ++ [o0; o1]) s1a s2a (mkBD c (bd_bits d2 - bd_ptr d2 * 8) 0 false)) = R)
      by (eapply l3_tl; [exact TLR | lia | exact D1 | exact R1 | exact S1 | exact ZO | exact D2 | exact RL2 | reflexivity]).
    destruct SM as (SM0 & C112). unfold bitdz_cellsA in C112. rewrite Z2 in C112.
    change (if false then AZEROFILLED else S0 + bd_ptr d2) with (S0 + bd_ptr d2) in C112.
    pose proof SM0 as (MU & WM & MI & STK & C80 & C96 & OUT).
    assert (SW : bv_swrap 32 (Z.shiftr (bv_wrap 32 (bd_bits d2)) 3) = Z.shiftr (bd_bits d2) 3).
    { replace (bv_wrap 32 (bd_bits d2)) with (bd_bits d2) by (unfold bv_wrap, bv_modulus; cbn [Z.of_N]; rewrite Z.mod_small by lia; reflexivity).
      apply swrap32_small. rewrite SH. Z.div_mod_to_equations; lia. }
    repeat zstep. l3_br false. repeat zstep. l3_br false. repeat zstep.
    rewrite SW. l3_br false. repeat zstep.
    rewrite l3_ne by (rewrite ?SH; Z.div_mod_to_equations; lia). l3_br false. repeat zstep.
    l3_br false. repeat zstep.
    try replace (S0 + bd_ptr d2 - S0) with (bd_ptr d2) by lia.
    l3_land32.
    l3_br false. repeat zstep.
    rewrite l3_ne by lia. l3_br false. do 4 zstep.
    l3_sub3 (bd_bits d2) (bd_ptr d2).
    replace (Z_to_bv 64 (S0 + bd_ptr d2 - bd_ptr d2)) with (Z_to_bv 64 (S0 + 0)) by (f_equal; lia).
    eapply (K6 (mkDec (de_out x ++ [o0; o1]) s1a s2a (mkBD c (bd_bits d2 - bd_ptr d2 * 8) 0 false)) R m jp OP0 I
              (bd_ptr d2) 0 (bd_bits d2 - bd_ptr d2 * 8) c);
      [exact TL' | exact ROK | exact K | reflexivity | exact RLp | exact OK3 | cbn [de_bd bd_bits] in BB3 |- *; lia
      | cbn [de_out]; rewrite l3_zl2; lia | cbn [de_out]; rewrite l3_zl2; lia | exact SI5 | exact SI6 | lia | exact SM0 | exact C112].
  Qed.

  Lemma sdt_seg_f_pf : sdt_seg_f.
  Proof.
    unfold sdt_seg_f. intros f HD.
    pose proof (l3_k5680_pf f HD) as K5. pose proof (l3_k5588_pf f K5) as K55. pose proof (l3_k6552_pf f K55) as K6.
    apply l3_cases; [exact (l3_cfast f K6) | exact (l3_czero f K5) | exact (l3_cclamp f K6) | exact (l3_cpart f K6)].
  Qed.

  Lemma l3_bok1 : forall s bd o s' bd', bitd_ok bs bd -> bd_bits bd <= 2^29 ->
    decode_sym d false s bd = Ok (o, s', bd') -> bitd_ok bs bd'.
  Proof.
    intros s bd o s' bd' BK BB DS. pose proof BK as (K1 & K2 & K3 & K4 & K5 & K6).
    destruct (l3_ds _ _ _ _ _ DS ltac:(lia)) as (E1 & E2 & E3 & E4).
    unfold bitd_ok. rewrite E1, E2, E3. repeat split; try lia; intros ZZ; specialize (K6 ZZ); lia.
  Qed.

  Lemma l3_step2 : forall f x R o0 s1a d1 st1 d1r,
    tail_loop bs d dcap false (S f) x = R -> dres_ok R -> zlen (de_out x) <= dcap - 2 ->
    decode_sym d false (de_s1 x) (de_bd x) = Ok (o0, s1a, d1) ->
    reload_dstream bs d1 = Ok (st1, d1r) -> dstatus_eqb st1 Overflow = false -> zlen (de_out x) + 1 <= dcap - 2 ->
    exists o1 s2a d2, decode_sym d false (de_s2 x) d1r = Ok (o1, s2a, d2).
  Proof.
    intros f x R o0 s1a d1 st1 d1r TL0 ROK Z0 D1 R1 S1 Z1. subst R. cbn [tail_loop] in ROK.
    change (FseNCount.Zlength (de_out x)) with (zlen (de_out x)) in ROK.
    replace (dcap - 2 <? zlen (de_out x)) with false in ROK by (symmetry; apply Z.ltb_ge; lia).
    rewrite D1 in ROK. cbn [bind] in ROK. rewrite R1 in ROK. cbn [bind] in ROK. rewrite S1 in ROK.
    replace (dcap - 2 <? FseNCount.Zlength (de_out x ++ [o0])) with false in ROK
      by (symmetry; apply Z.ltb_ge; change (FseNCount.Zlength (de_out x ++ [o0])) with (Z.of_nat (length (de_out x ++ [o0])));
          change (zlen (de_out x)) with (Z.of_nat (length (de_out x))) in Z1; rewrite length_app; cbn [length]; lia).
    destruct (l1_ds_cases (de_s2 x) d1r) as [[[[o1 s2a] d2] DS] | DS].
    - exists o1, s2a, d2. exact DS.
    - rewrite DS in ROK. cbn [bind] in ROK. contradiction.
  Qed.

  Lemma sdt_seg_d_pf : sdt_seg_d.
  Proof.
    unfold sdt_seg_d, sdt_c6300, sdt_c6200.
    intros f C x R m jp OP0 I o0 s1a d1 d1r st1 ra a1 a2 a3 s3 s6 s7 s9 s10 s11 TLx ROK K HI DS1 RL ST1 ZL1 HM.
    pose proof HI as (BOK & BB & ZL & OPI & DOP & I0).
    destruct (l3_step2 f x R o0 s1a d1 st1 d1r TLx ROK ZL DS1 RL ST1 ZL1) as (o1 & s2a & d2 & DS).
    pose proof (l3_bok1 _ _ _ _ _ BOK BB DS1) as BOK1.
    pose proof (RF_huf_fdw_pure.reload_facts2 bs d1 st1 d1r BY BOK1 RL) as (BOK2 & _).
    pose proof BOK2 as (BC & BBR & _).
    destruct (RF_huf_fdw_sm.dec_inv tl [] d ltac:(lia) HCELLS HCOK _ _ _ _ _ DS ltac:(lia))
      as (c & NC & S1R & SYR & NBR & NSR & NSR2 & _ & _ & _).
    pose proof HM as ((MU & WM & MI & STK & C80 & C96 & OUT) & C112).
    destruct (HAT m MU WM) as (TBm & SRCm & FCm & ZDTm & ZMKm & ZDSTm & ZOBJm & USRCm & RTCm).
    set (s := de_s2 x) in *.
    assert (EC : c = cellAt s) by (symmetry; apply nth_error_nth; exact NC). subst c.
    assert (P2 : 32 <= 2^tl <= 4096) by (split; [change 32 with (2^5) | change 4096 with (2^12)]; apply Z.pow_le_mono_r; lia).
    pose proof ATOP_range as AR; unfold ATOP_MIN, ATOP_MAX in AR.
    assert (DTL : 1 <= DT /\ DT + 4 + 4 * 2^tl <= ATOP)
      by (destruct HDT as [[H1 H2]|[H1 H2]]; [unfold AIMG_HI in H1; unfold KLS in H2|]; lia).
    assert (TBL : zlen (concat (map fse_cell_bytes (dt_cells d))) = 4 * 2^tl)
      by (rewrite RF_huf_bdt_model.fse_cells_length; lia).
    unfold ASHOFF.
    do 4 zstep. l1_n.
    lazymatch goal with |- context [Z_to_bv 64 (s * 4 + (DT + 4))] =>
      replace (s * 4 + (DT + 4)) with (DT + 4 + 4 * s) by lia end.
    do 2 zstep. l1_n.
    zstep. l1_br.
    do 2 zstep. l1_n. zstep. l1_br.
    zstep. l1_br.
    do 2 zstep. l1_n.
    wk_shz 11%Z. zstep. l1_br.
    do 3 zstep. l1_n.
    wk_shz 11%Z. zstep. l1_br.
    pose proof (RF_huf_fdw_kit.cell_rd_off bsegs m (DT + 4) (dt_cells d) s (cellAt s) 2 2 TBm NC ltac:(lia) ltac:(lia) ltac:(lia)) as CR2.
    unfold fse_cell_bytes in CR2. rewrite l1_cell_hi in CR2 by lia.
    replace (DT + 4 + (4 * s + 2)) with (DT + 4 + 4 * s + 2) in CR2 by lia.
    zstep. l1_n.
    assert (V16 : 0 <= dc_symbol (cellAt s) + 256 * dc_nbBits (cellAt s) < 3328) by lia.
    rewrite zx16_lit by lia.
    do 2 zstep. l1_n. zstep. l1_br. zstep. l1_n.
    set (V := dc_symbol (cellAt s) + 256 * dc_nbBits (cellAt s)) in *.
    lazymatch goal with |- context [Z_to_bv 64 ((V * ?K) ≫ 24)] =>
      replace ((V * K) ≫ 24) with (dc_nbBits (cellAt s))
        by (rewrite Z.shiftr_div_pow2 by lia; l1_p2; subst V; l1_zl) end.
    lazymatch goal with |- context [Z_to_bv 64 (V * ?K)] =>
      replace (V * K) with (Z.shiftl V 16) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity) end.
    subst V.
    exact (C x R m jp OP0 I o0 s1a d1 d1r st1 ra _ _ s7 s9 s10 s11 TLx ROK K HI DS1 RL ST1 ZL1 HM).
  Qed.

  Section L2_local. Import KXS.

  Ltac l2_ez :=
    repeat lazymatch goal with
    | |- context [edenot ?E _] =>
        let b := eval unfold E in E in
        lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
          rewrite ?(ez_ok zv E (kE_atoms zv xs));
          let na := eval vm_compute in (length zv) in
          cbv [ez]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb]
        end
    end.
  Ltac l2_br :=
    lazymatch goal with
    | |- branch_taken _ _ _ = _ =>
        l2_ez; unfold branch_taken; rewrite ?bv_ltu_Z, ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
        rewrite ?Z.mod_small by lia;
        first [ apply Bool.negb_true_iff, Z.ltb_ge; lia | apply Z.ltb_lt; lia
              | apply Bool.negb_false_iff, Z.ltb_lt; lia | apply Z.ltb_ge; lia ]
    end.

  Ltac l2_pc p :=
    lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?q) _ _ _ _) =>
      replace q with p by (unfold AFSE_DECOMP; reflexivity) end.
  Ltac l2_sha :=
    unfold adenot; cbn [a_base a_off]; l2_ez; unfold wa, shad; rewrite PropExec.v_addi_0; apply Z_to_bv_eqm;
    rewrite Z.shiftr_div_pow2 by lia; change (2 ^ (3 mod 64)) with (2 ^ 3);
    f_equal; f_equal; f_equal; apply Z.mod_small; lia.

  Lemma l2_flat0 : forall E b, flat E {| a_base := b; a_off := 0 |} (elenZ E (ELit 1)).
  Proof.
    intros E b. pose proof (bv_unsigned_in_range 64 (edenot E b)) as R.
    unfold flat, estart, elenZ; cbn [a_base a_off edenot]. rewrite ?Z_to_bv_unsigned.
    unfold bv_wrap, bv_modulus in *; cbn [Z.of_N] in *. change (1 mod 2 ^ 64) with 1. lia.
  Qed.

  Lemma l2_shq : forall X, 0 <= X < 2^47 -> 0 <= X / 8 < 2^44.
  Proof. intros X HX. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. Qed.

  Lemma l2_acc_sh : forall E a x, adenot E a = wa (shad x) -> S0 <= x < S0 + zlen bs ->
    rng RNG (shad S0) ((S0 + zlen bs + 7) / 8 - S0 / 8) -> accP RNG E (a, 1%nat).
  Proof.
    intros E a x EA X R. unfold accP. cbn [fst snd]. rewrite EA. unfold wa, shad in *.
    destruct R as (R0 & R1 & R).
    rewrite !Z.shiftr_div_pow2 in * by lia. change (2^3) with 8 in *.
    assert (Q1 : S0 / 8 <= x / 8) by (apply Z.div_le_mono; lia).
    assert (Q3 : x / 8 <= (S0 + zlen bs - 1) / 8) by (apply Z.div_le_mono; lia).
    assert (Q4 : (S0 + zlen bs + 7) / 8 = (S0 + zlen bs - 1) / 8 + 1).
    { replace (S0 + zlen bs + 7) with ((S0 + zlen bs - 1) + 1 * 8) by lia. apply Z.div_add. lia. }
    rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus; cbn [Z.of_N]. rewrite Z.mod_small by lia.
    apply (R _ 1%nat); change (Z.of_nat 1) with 1; lia.
  Qed.

  Lemma l2_firstn1 : forall (l : list Z) n, (n < length l)%nat -> firstn 1 (skipn n l) = [nth n l 0].
  Proof.
    induction l as [|x l IH]; intros n Hn; [cbn in Hn; lia|].
    destruct n as [|n]; [reflexivity|]. cbn [skipn nth]. apply IH. cbn in Hn. lia.
  Qed.

  Lemma l2_rd1 : forall (mm : amem) E j w k,
    bytes_at bsegs mm S0 (map (Z_to_bv 8) bs) ->
    ev E j = rdval bsegs mm w 1 false -> w = Z_to_bv 64 (S0 + k) -> 0 <= k < zlen bs ->
    bv_unsigned (ev E j) = Znth k bs.
  Proof.
    intros mm E j w k HB H Hw Hk. subst w. rewrite H. unfold rdval.
    replace (Z_to_bv 64 (S0 + k)) with (wa (S0 + Z.of_nat (Z.to_nat k))) by (unfold wa; f_equal; lia).
    rewrite (bytes_at_rdn bsegs mm S0 _ (Z.to_nat k) 1 HB) by (rewrite length_map; lia).
    rewrite skipn_map, firstn_map, l2_firstn1 by lia.
    assert (R : 0 <= nth (Z.to_nat k) bs 0 < 256).
    { rewrite Forall_forall in BY. apply BY. apply nth_In. lia. }
    unfold Znth. cbn [map extz bytes_le_to_Z]. change (0 ≪ 8) with 0. rewrite Z.lor_0_r.
    rewrite (Z_to_bv_small 8) by (unfold bv_modulus; cbn -[Z.pow]; lia).
    rewrite Z_to_bv_small by (unfold bv_modulus; cbn -[Z.pow]; lia). reflexivity.
  Qed.

  Ltac l2_ezh H :=
    lazymatch type of H with context [edenot ?E _] =>
      let b := eval unfold E in E in
      lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
        rewrite ?(ez_ok zv E (kE_atoms zv xs)) in H;
        let na := eval vm_compute in (length zv) in
        cbv [ez] in H; change (length zv) with na in H; cbv [nth Nat.ltb Nat.leb] in H
      end
    end.

  Ltac l2_rdall mm HB p :=
    repeat lazymatch goal with |- context [bv_unsigned (ev ?E ?j)] =>
      let H := fresh "HR" in kx_read_eq j H;
      lazymatch type of H with ev _ _ = rdval _ _ (adenot _ {| a_base := ?b; a_off := ?k |}) 1 false =>
        let Z1 := fresh "ZR" in
        assert (Z1 : bv_unsigned (ev E j) = Znth (p + k) bs);
        [ apply (l2_rd1 mm E j _ (p + k) HB H);
          [ unfold adenot; cbn [a_base a_off]; l2_ez; unfold PropExec.v_addi; apply Z_to_bv_eqm;
            rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N]; f_equal;
            rewrite Z.mod_small by lia; lia
          | lia ]
        | rewrite Z1; clear H Z1 ]
      end
    end.

  Ltac l2_dj :=
    unfold flat, estart, elenZ; cbn [a_base a_off]; l2_ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N];
    change (2 ^ (3 mod 64)) with 8;
    rewrite ?(Z.mod_small (_ + _ + 7) (2^64)) by lia;
    lazymatch goal with |- context [?X / 8] =>
      let Hq := fresh "Hq" in assert (Hq : 0 <= X / 8 < 2^44) by (apply l2_shq; lia);
      let q := fresh "q" in set (q := X / 8) in * end;
    rewrite ?(Z.mod_small (ASHOFF + _) (2^64)) by (unfold ASHOFF; lia);
    rewrite ?(Z.mod_small (SPAf SPV) (2^64)) by lia;
    try change (1 mod 2 ^ 64) with 1; try change (8 mod 2 ^ 64) with 8;
    unfold ASHOFF; lia.

  Lemma l2_cat80 : forall mm c1 c2 bd jp',
    rw_cells bsegs mm (SP1 + 80) [C8 (Z_to_bv 64 c2); C8 (Z_to_bv 64 (DT + 4))] ->
    rw_cells bsegs mm (SP1 + 96) [C8 (Z_to_bv 64 c1); C8 (Z_to_bv 64 (DT + 4))] ->
    rw_cells bsegs mm (SP1 + 112) (bitdz_cellsA S0 bd jp') ->
    exists j48', rw_cells bsegs mm (SP1 + 80) [CB 72 j48'].
  Proof.
    intros mm c1 c2 bd jp' H80 H96 H112.
    assert (H : rw_cells bsegs mm (SP1 + 80) ([] ++ ([C8 (Z_to_bv 64 c2); C8 (Z_to_bv 64 (DT + 4))]
                  ++ [C8 (Z_to_bv 64 c1); C8 (Z_to_bv 64 (DT + 4))] ++ bitdz_cellsA S0 bd jp') ++ [])).
    { rewrite app_nil_r, app_nil_l. apply (proj2 (kx_rw_cells_app _ _ _ _ _)). split; [exact H80 |].
      replace (SP1 + 80 + Z.of_nat (cells_size [C8 (Z_to_bv 64 c2); C8 (Z_to_bv 64 (DT + 4))])) with (SP1 + 96)
        by (cbn; lia).
      apply (proj2 (kx_rw_cells_app _ _ _ _ _)). split; [exact H96 |].
      replace (SP1 + 96 + Z.of_nat (cells_size [C8 (Z_to_bv 64 c1); C8 (Z_to_bv 64 (DT + 4))])) with (SP1 + 112)
        by (cbn; lia).
      exact H112. }
    pose proof (rw_cells_merge _ _ _ _ _ _ H) as H'. eexists. exact H'.
  Qed.

  Lemma l2_tl_err : forall f x o0 s1a d1 st1 d1r,
    zlen (de_out x) <= dcap - 2 -> decode_sym d false (de_s1 x) (de_bd x) = Ok (o0, s1a, d1) ->
    reload_dstream bs d1 = Ok (st1, d1r) -> dstatus_eqb st1 Overflow = false -> dcap - 2 < zlen (de_out x) + 1 ->
    tail_loop bs d dcap false (S f) x = Err ZSTD_error_dstSize_tooSmall.
  Proof.
    intros f x o0 s1a d1 st1 d1r ZL DS RL NO LT. cbn [tail_loop].
    rewrite DS. cbn [bind]. rewrite RL. cbn [bind]. rewrite NO.
    unfold FseNCount.Zlength. rewrite length_app. cbn [length].
    replace (dcap - 2 <? Z.of_nat (length (de_out x))) with false by (symmetry; apply Z.ltb_ge; lia).
    replace (dcap - 2 <? Z.of_nat (length (de_out x) + 1)) with true by (symmetry; apply Z.ltb_lt; lia).
    reflexivity.
  Qed.

  Lemma l2_k6196 : forall f x R m jp (OP0 I o0 s1a : Z) (d1 d1r : bitD) (st1 : dstatus)
      (ra a1 a2 a3 s3 s6 s7 s9 s10 s11 : word),
    sdt_c6200 f ->
    tail_loop bs d dcap false (S f) x = R -> dres_ok R -> sdtK R -> sdtI x OP0 I ->
    decode_sym d false (de_s1 x) (de_bd x) = Ok (o0, s1a, d1) ->
    reload_dstream bs d1 = Ok (st1, d1r) -> dstatus_eqb st1 Overflow = false ->
    sdtM m (de_out x ++ [o0]) s1a (de_s2 x) d1r jp ->
    evtF bsegs RNG Q (TL (AFSE_DECOMP + 6196) m ra OP0 I a1 a2 a3 s3
                         (Z_to_bv 64 (OP0 + I)) (Z_to_bv 64 (OP0 + I + 1)) s6 s7 (Z_to_bv 64 ASHOFF) s9 s10 s11
                         (Z_to_bv 64 (S0 + 8))).
  Proof.
    intros f x R m jp OP0 I o0 s1a d1 d1r st1 ra a1 a2 a3 s3 s6 s7 s9 s10 s11 C TLR ROK K HI DS RL NO HM.
    pose proof HI as (BOK & BB & ZL & EOP & DOP & I0).
    pose proof (ablk_lin _ _ HDST) as LDS. unfold AIMG_HI in LDS. pose proof LO as LO'.
    destruct (Z_lt_le_dec (dcap - 2) (zlen (de_out x) + 1)) as [LT | GE].
    - kx_runFmd [AFSE_DECOMP + 440] 10%nat [true]
        [KZRange DST 4096 (2^47); KZRange dcap 0 255; KZRange OP0 4096 (2^47); KZRange I 0 (2^47)]
        (@nil (Z * Z)) (@nil (Z * Z)) (@nil (Z * Z)).
      all: try lia.
      all: try l2_br.
      kx_post_regs; cbn [mem_denot].
      pose proof (l2_tl_err f x o0 s1a d1 st1 d1r ZL DS RL NO LT) as RE. rewrite TLR in RE. rewrite RE in K.
      destruct HM as ((MU & WM & MI & ST & C80 & C96 & OUT) & C112).
      destruct (l2_cat80 m _ _ _ _ C80 C96 C112) as (j48' & FM80).
      replace (Z_to_bv 64 (-70)) with (Z_to_bv 64 (2^64 - 70)) by (apply Z_to_bv_eqm; reflexivity).
      l2_pc (AFSE_DECOMP + 440).
      eapply (K m (2^64 - 70)); [exact MU | exact WM | exact MI | exact ST | exact FM80 | | | ].
      + eapply rw_cells_transport; [exact FC32 | exact MU | exact WM | cbn; unfold DEC_STACK in LO'; lia].
      + unfold dresA. split; [reflexivity | unfold ZSTD_error_dstSize_tooSmall; lia].
      + lia.
    - kx_runFmd [AFSE_DECOMP + 6200] 10%nat [false]
        [KZRange DST 4096 (2^47); KZRange dcap 0 255; KZRange OP0 4096 (2^47); KZRange I 0 (2^47)]
        (@nil (Z * Z)) (@nil (Z * Z)) (@nil (Z * Z)).
      all: try lia.
      all: try l2_br.
      kx_post_regs; cbn [mem_denot].
      l2_pc (AFSE_DECOMP + 6200).
      replace (2 ^ 64 + - ABIT_MASK + -1) with (2^64 - 1 - ABIT_MASK) by lia.
      replace (DST + dcap + -2) with (DST + dcap - 2) by lia.
      replace (2 ^ 16 + -1) with (2^16 - 1) by lia.
      exact (C x R m jp OP0 I o0 s1a d1 d1r st1 ra a1 a2 a3 s3 s6 s7 s9 s10 s11 TLR ROK K HI DS RL NO ltac:(lia) HM).
  Qed.

  Lemma l2_ld : forall f x R m jp (OP0 I o0 s1a : Z) (d1 d1r : bitD) (st1 : dstatus) (P1 : Z)
      (w1 w2 w3 ra s3 s6 s7 s9 s10 s11 : word),
    sdt_c6200 f ->
    tail_loop bs d dcap false (S f) x = R -> dres_ok R -> sdtK R -> sdtI x OP0 I ->
    decode_sym d false (de_s1 x) (de_bd x) = Ok (o0, s1a, d1) ->
    reload_dstream bs d1 = Ok (st1, d1r) -> dstatus_eqb st1 Overflow = false ->
    bd_zero d1r = false -> 0 <= bd_ptr d1r -> bd_ptr d1r + 8 <= zlen bs ->
    bd_cont d1r = le64v bs (bd_ptr d1r) -> 0 <= bd_bits d1r <= 64 -> 0 < P1 < 2^64 ->
    sdtM0 m (de_out x ++ [o0]) s1a (de_s2 x) ->
    rw_cells bsegs m (SP1 + 112) [C8 w1; C4 w2; CB 4 jp; C8 w3; C8 (Z_to_bv 64 S0); C8 (Z_to_bv 64 (S0 + 8))] ->
    evtF bsegs RNG Q (TL (AFSE_DECOMP + 6056) m ra OP0 I (Z_to_bv 64 P1) (Z_to_bv 64 (S0 + bd_ptr d1r))
                         (Z_to_bv 64 (bd_bits d1r)) s3 (Z_to_bv 64 (OP0 + I)) (Z_to_bv 64 (OP0 + I + 1)) s6 s7
                         (Z_to_bv 64 ASHOFF) s9 s10 s11 (Z_to_bv 64 (S0 + 8))).
  Proof.
    intros f x R m jp OP0 I o0 s1a d1 d1r st1 P1 w1 w2 w3 ra s3 s6 s7 s9 s10 s11
      C TLR ROK K HI DS RL NO BZ BP0 BP8 BC BB P1R HM0 C112.
    destruct HM0 as (MU & WM & MI & ST & C80 & C96 & OUT).
    destruct (HAT m MU WM) as (_ & SRCm & _ & _ & _ & _ & _ & USm & _).
    pose proof (ablk_lin _ _ HS0) as LS. unfold AIMG_HI in LS.
    pose proof LO as LO'. unfold DEC_STACK in LO'. pose proof (spaf_props SPV SP16) as (SPAB & SPA32).
    assert (RSs3 : rng RNG (shad S0) ((S0 + zlen bs + 7) / 8 - S0 / 8)).
    { eapply rng_sub; [exact RSs | lia | unfold nshad; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8;
        clear - S16; Z.div_mod_to_equations; lia]. }
    assert (C112W : exists jw, rw_cells bsegs m (SP1 + 112) [CB 40 jw]).
    { pose proof (rw_cells_merge bsegs m (SP1 + 112) [] _ [] ltac:(rewrite app_nil_r; exact C112)) as H'.
      eexists; exact H'. }
    destruct C112W as (jw & C112W).
    kx_cells_split C112.
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    kx_runFm [AFSE_DECOMP + 6196] 80%nat
      [KZRange (zlen bs) 8 (2^47); KZRange S0 16 (2^47); KZRange (S0 + zlen bs) 24 (2^47); KZRange (bd_ptr d1r) 0 (2^47);
       KZRange (zlen bs - bd_ptr d1r - 8) 0 (2^47); KZRange (bd_bits d1r) 0 64; KZRange P1 1 (2^64 - 1);
       KZRange SP1 4096 (2^47 - 152); KZWr (SP1 + 112) 40; KZDisj S0 (zlen bs) (SP1 + 112) 40]
      [(S0, zlen bs)] [(S0, zlen bs); (SP1 + 80, 72)] [(S0, zlen bs)].
    all: try lia.
    all: lazymatch goal with
      | |- branch_taken BC_LT (edenot ?E (EAlu ALU_SUB (EMd M_MUL (EAlu ALU_SLTU (ELit 0) (EVar ?j))
               (EAlu ALU_ADD (EAlu ALU_ADD (EAlu ALU_AND ?B (ELit 7)) (ELit ?k)) (ELit 1))) (ELit 1)))
               (edenot ?E (EVar ?j)) = true =>
          let H := fresh "HR" in kx_read_eq j H;
          eapply (chk_ob_unp bsegs m E (EVar j) B k S0 (S0 + zlen bs)); [exact USm | l2_ez; reflexivity | lia | lia | lia | lia | ];
          cbn [edenot]; rewrite H; f_equal; l2_sha
      | |- exists _, rdn _ _ (adenot ?E {| a_base := EAlu ALU_ADD (EVar _)
               (EAlu ALU_SRL (EAlu ALU_ADD (EAlu ALU_ADD (EVar _) (EVar _)) (ELit ?k)) (ELit 3)); a_off := 0 |}) 1 = Some _ =>
          let EA := fresh "EA" in
          lazymatch goal with |- context [adenot E ?a] =>
            assert (EA : adenot E a = wa (shad (S0 + bd_ptr d1r + k))) by l2_sha end;
          rewrite EA;
          destruct (unp_gran m S0 (S0 + zlen bs) (S0 + bd_ptr d1r + k) 1 USm ltac:(lia) ltac:(lia) ltac:(lia)) as (bsh & Hsh & _);
          exists [bsh]; apply rdn1_some; exact Hsh
      | |- exists _, rdn _ _ (adenot ?E {| a_base := EAlu ALU_ADD (EVar _)
               (EAlu ALU_SRL (EAlu ALU_ADD (EVar _) (EVar _)) (ELit 3)); a_off := 0 |}) 1 = Some _ =>
          let EA := fresh "EA" in
          lazymatch goal with |- context [adenot E ?a] =>
            assert (EA : adenot E a = wa (shad (S0 + bd_ptr d1r))) by l2_sha end;
          rewrite EA;
          destruct (unp_gran m S0 (S0 + zlen bs) (S0 + bd_ptr d1r) 1 USm ltac:(lia) ltac:(lia) ltac:(lia)) as (bsh & Hsh & _);
          exists [bsh]; apply rdn1_some; exact Hsh
      | |- flat _ _ _ /\ _ => l2_dj
      | |- flat _ {| a_base := _; a_off := 0 |} (elenZ _ (ELit 1)) => apply l2_flat0
      | |- accP _ ?E ({| a_base := EAlu ALU_ADD (EVar _)
               (EAlu ALU_SRL (EAlu ALU_ADD (EAlu ALU_ADD (EVar _) (EVar _)) (ELit ?k)) (ELit 3)); a_off := 0 |}, 1%nat) =>
          eapply (l2_acc_sh E _ (S0 + bd_ptr d1r + k)); [l2_sha | lia | exact RSs3]
      | |- accP _ ?E ({| a_base := EAlu ALU_ADD (EVar _)
               (EAlu ALU_SRL (EAlu ALU_ADD (EVar _) (EVar _)) (ELit 3)); a_off := 0 |}, 1%nat) =>
          eapply (l2_acc_sh E _ (S0 + bd_ptr d1r)); [l2_sha | lia | exact RSs3]
      | |- _ => idtac
    end.
    all: lazymatch goal with |- evtF _ _ _ _ => idtac | |- ?G => fail "L2SIDE" G end.
    kx_post_regs.
    clear C112W.
    destruct OUT as (junk & (OUTb & OUTw) & LJ).
    kx_cells_post.
    kx_frame C80. kx_frame C96. kx_frame OUTb.
    kx_munch MU.
    kx_post_mem_free.
    lazymatch type of KC0 with rw_cells _ _ _ [C4 ?v] =>
      assert (V0 : v = Z_to_bv 64 (bd_bits d1r)) by (l2_ez; reflexivity) end.
    lazymatch type of KC2 with rw_cells _ _ _ [C8 ?v] =>
      assert (V2 : v = Z_to_bv 64 (S0 + bd_ptr d1r)) by (l2_ez; reflexivity) end.
    lazymatch type of KC with rw_cells _ _ _ [C8 ?v] =>
      assert (VC : v = Z_to_bv 64 (le64v bs (bd_ptr d1r)))
        by (l2_ez; l2_rdall m SRCm (bd_ptr d1r); f_equal; unfold le64v; rewrite Z.add_0_r; first [lia | ring]) end.
    try rewrite V0 in KC0. try rewrite V2 in KC2. try rewrite VC in KC.
    lazymatch goal with |- context [mem_denot ?E ?mm ?l] => remember (mem_denot E mm l) as m1 eqn:EM1 end.
    assert (C112n : rw_cells bsegs m1 (SP1 + 112) (bitdz_cellsA S0 d1r jp)).
    { unfold bitdz_cellsA. rewrite BZ, BC. kx_cells_merge. }
    l2_pc (AFSE_DECOMP + 6196).
    replace (2 ^ 64 + - ABIT_MASK + -1) with (2^64 - 1 - ABIT_MASK) by lia.
    replace (DST + dcap + -2) with (DST + dcap - 2) by lia.
    replace (2 ^ 16 + -1) with (2^16 - 1) by lia.
    eapply (l2_k6196 f x R m1 jp OP0 I o0 s1a d1 d1r st1);
      [exact C | exact TLR | exact ROK | exact K | exact HI | exact DS | exact RL | exact NO | ].
    refine (conj (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (ex_intro _ junk (conj (conj OUTb OUTw) LJ)))))))) C112n);
      eassumption.
    all: try (pose proof (ablk_lin _ _ HDST) as LDS;
              repeat rewrite length_app in *; repeat rewrite length_map in *; repeat rewrite length_app in *;
              cbn [length] in *; first [right; lia | left; lia]).
    all: try (cbn [cells_size csize] in *; first [right; lia | left; lia]).
  Qed.

  Lemma l2_bok : forall x o0 s1a d1, bitd_ok bs (de_bd x) ->
    decode_sym d false (de_s1 x) (de_bd x) = Ok (o0, s1a, d1) -> bd_bits d1 <= 64 ->
    bitd_ok bs d1 /\ bd_zero d1 = false.
  Proof.
    intros x o0 s1a d1 BK D1 B1.
    pose proof BK as (K1 & K2 & K3 & K4 & K5 & K6).
    destruct (l3_ds _ _ _ _ _ D1 ltac:(lia)) as (E1 & E2 & E3 & E4).
    assert (Z1 : bd_zero d1 = false).
    { rewrite E3. destruct (bd_zero (de_bd x)) eqn:ZX; [|reflexivity]. specialize (K6 eq_refl). lia. }
    split; [| exact Z1].
    unfold bitd_ok. rewrite E1, E2. repeat split; try lia. intros ZZ. rewrite Z1 in ZZ. discriminate ZZ.
  Qed.

  Definition l2_C (P : bitD -> Prop) (f : nat) : Prop :=
    forall x R m jp (OP0 I o0 s1a : Z) (d1 : bitD) (ra a1 a2 s3 s6 s7 s9 s10 s11 t6 : word),
      tail_loop bs d dcap false (S f) x = R -> dres_ok R -> sdtK R -> sdtI x OP0 I ->
      decode_sym d false (de_s1 x) (de_bd x) = Ok (o0, s1a, d1) -> bd_bits d1 <= 64 ->
      bitd_ok bs d1 -> bd_zero d1 = false -> P d1 ->
      sdtM m (de_out x ++ [o0]) s1a (de_s2 x) d1 jp ->
      evtF bsegs RNG Q (TL (AFSE_DECOMP + 5916) m ra OP0 I a1 a2 (Z_to_bv 64 (bd_bits d1)) s3
                           (Z_to_bv 64 (OP0 + I)) (Z_to_bv 64 (OP0 + I + 1)) s6 s7 (Z_to_bv 64 ASHOFF) s9 s10 s11 t6).

  Lemma l2_cases : forall f,
    l2_C (fun d1 => 8 <= bd_ptr d1) f -> l2_C (fun d1 => bd_ptr d1 = 0) f ->
    l2_C (fun d1 => 1 <= bd_ptr d1 <= 7 /\ bd_ptr d1 - Z.shiftr (bd_bits d1) 3 < 0) f ->
    l2_C (fun d1 => 1 <= bd_ptr d1 <= 7 /\ 0 <= bd_ptr d1 - Z.shiftr (bd_bits d1) 3) f -> sdt_c5916 f.
  Proof.
    intros f CF CZ CC CP. unfold sdt_c5916.
    intros x R m jp OP0 I o0 s1a d1 ra a1 a2 s3 s6 s7 s9 s10 s11 t6 TLR ROK K SI D1 B1 SM.
    destruct (l2_bok x o0 s1a d1 (proj1 SI) D1 B1) as [OK1 Z1].
    pose proof OK1 as (_ & _ & P0 & _).
    destruct (Z_le_gt_dec 8 (bd_ptr d1)) as [G8|G8]; [eapply CF; eassumption|].
    destruct (Z.eq_dec (bd_ptr d1) 0) as [E0|E0]; [eapply CZ; eassumption|].
    destruct (Z_lt_ge_dec (bd_ptr d1 - Z.shiftr (bd_bits d1) 3) 0) as [L0|L0].
    - eapply CC; [eassumption .. | split; lia | eassumption].
    - eapply CP; [eassumption .. | split; lia | eassumption].
  Qed.

  Lemma l2_czero : forall f, sdt_c6200 f -> l2_C (fun d1 => bd_ptr d1 = 0) f.
  Proof.
    intros f C6. unfold l2_C.
    intros x R m jp OP0 I o0 s1a d1 ra a1 a2 s3 s6 s7 s9 s10 s11 t6 TLR ROK K SI D1 B1 OK1 Z1 P0 SM.
    l3_pre.
    pose proof SI as (SI1 & SI2 & SI3 & SI4 & SI5 & SI6).
    pose proof OK1 as (O1 & O2 & O3 & O4 & O5 & O6).
    assert (RL1 : reload_dstream bs d1 = Ok ((if bd_bits d1 <? 64 then EndOfBuffer else Completed), d1)).
    { unfold reload_dstream. replace (64 <? bd_bits d1) with false by (symmetry; apply Z.ltb_ge; lia).
      replace (8 <=? bd_ptr d1) with false by (symmetry; apply Z.leb_gt; lia). rewrite P0. reflexivity. }
    pose proof SM as (SM0 & C112). unfold bitdz_cellsA in C112. rewrite Z1 in C112.
    change (if false then AZEROFILLED else S0 + bd_ptr d1) with (S0 + bd_ptr d1) in C112.
    pose proof SM0 as (MU & WM & MI & STK & C80 & C96 & OUT).
    repeat zstep. l3_br false. repeat zstep. l3_br true.
    try l2_pc (AFSE_DECOMP + 6196).
    eapply (l2_k6196 f x R m jp OP0 I o0 s1a d1 d1);
      [exact C6 | exact TLR | exact ROK | exact K | exact SI | exact D1 | exact RL1
      | destruct (bd_bits d1 <? 64); reflexivity | exact SM].
  Qed.

  Lemma l2_cfast : forall f, sdt_c6200 f -> l2_C (fun d1 => 8 <= bd_ptr d1) f.
  Proof.
    intros f C6. unfold l2_C.
    intros x R m jp OP0 I o0 s1a d1 ra a1 a2 s3 s6 s7 s9 s10 s11 t6 TLR ROK K SI D1 B1 OK1 Z1 P8 SM.
    l3_pre.
    pose proof SI as (SI1 & SI2 & SI3 & SI4 & SI5 & SI6).
    pose proof OK1 as (O1 & O2 & O3 & O4 & O5 & O6).
    assert (ZL8 : 8 <= zlen bs) by (destruct (Z_lt_ge_dec (zlen bs) 8) as [h|h]; [specialize (O5 h); lia | lia]).
    assert (SH : Z.shiftr (bd_bits d1) 3 = bd_bits d1 / 8) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    pose (p := bd_ptr d1 - Z.shiftr (bd_bits d1) 3).
    assert (PB : 0 <= p /\ p + 8 <= zlen bs) by (unfold p; rewrite SH; Z.div_mod_to_equations; lia).
    assert (RLp : readLE64 bs p = Ok (le64v bs p)) by (rewrite readLE64_ok by lia; reflexivity).
    assert (RL1 : reload_dstream bs d1 = Ok (Unfinished, mkBD (le64v bs p) (Z.land (bd_bits d1) 7) p false)).
    { unfold reload_dstream. replace (64 <? bd_bits d1) with false by (symmetry; apply Z.ltb_ge; lia).
      replace (8 <=? bd_ptr d1) with true by (symmetry; apply Z.leb_le; lia). cbv zeta.
      change (bd_ptr d1 - Z.shiftr (bd_bits d1) 3) with p. rewrite RLp. reflexivity. }
    pose proof (RF_huf_fdw_pure.reload_facts2 bs d1 Unfinished _ BY OK1 RL1) as (OK2 & BB2 & _ & _ & _).
    pose proof OK2 as (Q1 & Q2 & _). cbn [bd_bits] in Q2, BB2.
    destruct SM as (SM0 & C112). unfold bitdz_cellsA in C112. rewrite Z1 in C112.
    change (if false then AZEROFILLED else S0 + bd_ptr d1) with (S0 + bd_ptr d1) in C112.
    pose proof SM0 as (MU & WM & MI & STK & C80 & C96 & OUT).
    repeat zstep.
    l3_br true. repeat zstep.
    assert (SW : bv_swrap 32 (Z.shiftr (bv_wrap 32 (bd_bits d1)) 3) = Z.shiftr (bd_bits d1) 3).
    { replace (bv_wrap 32 (bd_bits d1)) with (bd_bits d1) by (unfold bv_wrap, bv_modulus; cbn [Z.of_N]; rewrite Z.mod_small by lia; reflexivity).
      apply swrap32_small. rewrite SH. Z.div_mod_to_equations; lia. }
    rewrite SW. l3_br false. repeat zstep.
    rewrite l3_ne by (rewrite ?SH; Z.div_mod_to_equations; lia). l3_br false. do 2 zstep.
    replace (Z_to_bv 64 (S0 + bd_ptr d1 - Z.shiftr (bd_bits d1) 3)) with (Z_to_bv 64 (S0 + p)) by (f_equal; unfold p; lia).
    try l2_pc (AFSE_DECOMP + 6056).
    eapply (l2_ld f x R m jp OP0 I o0 s1a d1 (mkBD (le64v bs p) (Z.land (bd_bits d1) 7) p false) Unfinished (S0 + bd_ptr d1));
      [exact C6 | exact TLR | exact ROK | exact K | exact SI | exact D1 | exact RL1 | reflexivity | reflexivity
      | cbn [bd_ptr]; lia | cbn [bd_ptr]; lia | reflexivity | cbn [bd_bits]; lia | lia | exact SM0 | exact C112].
  Qed.

  Lemma l2_cpart : forall f, sdt_c6200 f ->
    l2_C (fun d1 => 1 <= bd_ptr d1 <= 7 /\ 0 <= bd_ptr d1 - Z.shiftr (bd_bits d1) 3) f.
  Proof.
    intros f C6. unfold l2_C.
    intros x R m jp OP0 I o0 s1a d1 ra a1 a2 s3 s6 s7 s9 s10 s11 t6 TLR ROK K SI D1 B1 OK1 Z1 (PQ & PN) SM.
    l3_pre.
    pose proof SI as (SI1 & SI2 & SI3 & SI4 & SI5 & SI6).
    pose proof OK1 as (O1 & O2 & O3 & O4 & O5 & O6).
    assert (ZL8 : 8 <= zlen bs) by (destruct (Z_lt_ge_dec (zlen bs) 8) as [h|h]; [specialize (O5 h); lia | lia]).
    assert (SH : Z.shiftr (bd_bits d1) 3 = bd_bits d1 / 8) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    pose (p := bd_ptr d1 - Z.shiftr (bd_bits d1) 3).
    assert (PB : 0 <= p /\ p + 8 <= zlen bs) by (unfold p; rewrite SH; Z.div_mod_to_equations; lia).
    assert (RLp : readLE64 bs p = Ok (le64v bs p)) by (rewrite readLE64_ok by lia; reflexivity).
    assert (RL1 : reload_dstream bs d1 = Ok (Unfinished, mkBD (le64v bs p) (bd_bits d1 - Z.shiftr (bd_bits d1) 3 * 8) p false)).
    { unfold reload_dstream. replace (64 <? bd_bits d1) with false by (symmetry; apply Z.ltb_ge; lia).
      replace (8 <=? bd_ptr d1) with false by (symmetry; apply Z.leb_gt; lia).
      replace (bd_ptr d1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv beta iota zeta.
      replace (bd_ptr d1 - Z.shiftr (bd_bits d1) 3 <? 0) with false by (symmetry; apply Z.ltb_ge; lia). cbv beta iota zeta.
      change (bd_ptr d1 - Z.shiftr (bd_bits d1) 3) with p. rewrite RLp. reflexivity. }
    pose proof (RF_huf_fdw_pure.reload_facts2 bs d1 Unfinished _ BY OK1 RL1) as (OK2 & BB2 & _ & _ & _).
    pose proof OK2 as (Q1 & Q2 & _). cbn [bd_bits] in Q2, BB2.
    destruct SM as (SM0 & C112). unfold bitdz_cellsA in C112. rewrite Z1 in C112.
    change (if false then AZEROFILLED else S0 + bd_ptr d1) with (S0 + bd_ptr d1) in C112.
    pose proof SM0 as (MU & WM & MI & STK & C80 & C96 & OUT).
    assert (SHB : 0 <= Z.shiftr (bd_bits d1) 3 <= 8) by (rewrite SH; Z.div_mod_to_equations; lia).
    assert (SW : bv_swrap 32 (Z.shiftr (bv_wrap 32 (bd_bits d1)) 3) = Z.shiftr (bd_bits d1) 3).
    { replace (bv_wrap 32 (bd_bits d1)) with (bd_bits d1) by (unfold bv_wrap, bv_modulus; cbn [Z.of_N]; rewrite Z.mod_small by lia; reflexivity).
      apply swrap32_small. rewrite SH. Z.div_mod_to_equations; lia. }
    repeat zstep. l3_br false. repeat zstep. l3_br false. repeat zstep.
    rewrite SW. l3_br false. repeat zstep.
    rewrite l3_ne by (rewrite ?SH; Z.div_mod_to_equations; lia). l3_br false. repeat zstep.
    l3_br true. repeat zstep.
    l3_land32.
    l3_br false. repeat zstep.
    rewrite l3_ne by (rewrite ?SH; Z.div_mod_to_equations; lia). l3_br false. do 4 zstep.
    l3_sub3 (bd_bits d1) (Z.shiftr (bd_bits d1) 3).
    replace (Z_to_bv 64 (S0 + bd_ptr d1 - Z.shiftr (bd_bits d1) 3)) with (Z_to_bv 64 (S0 + p)) by (f_equal; unfold p; lia).
    try l2_pc (AFSE_DECOMP + 6056).
    eapply (l2_ld f x R m jp OP0 I o0 s1a d1 (mkBD (le64v bs p) (bd_bits d1 - Z.shiftr (bd_bits d1) 3 * 8) p false) Unfinished
              (S0 + bd_ptr d1));
      [exact C6 | exact TLR | exact ROK | exact K | exact SI | exact D1 | exact RL1 | reflexivity | reflexivity
      | cbn [bd_ptr]; lia | cbn [bd_ptr]; lia | reflexivity | cbn [bd_bits]; lia | lia | exact SM0 | exact C112].
  Qed.

  Lemma l2_cclamp : forall f, sdt_c6200 f ->
    l2_C (fun d1 => 1 <= bd_ptr d1 <= 7 /\ bd_ptr d1 - Z.shiftr (bd_bits d1) 3 < 0) f.
  Proof.
    intros f C6. unfold l2_C.
    intros x R m jp OP0 I o0 s1a d1 ra a1 a2 s3 s6 s7 s9 s10 s11 t6 TLR ROK K SI D1 B1 OK1 Z1 (PQ & PN) SM.
    l3_pre.
    pose proof SI as (SI1 & SI2 & SI3 & SI4 & SI5 & SI6).
    pose proof OK1 as (O1 & O2 & O3 & O4 & O5 & O6).
    assert (ZL8 : 8 <= zlen bs) by (destruct (Z_lt_ge_dec (zlen bs) 8) as [h|h]; [specialize (O5 h); lia | lia]).
    assert (SH : Z.shiftr (bd_bits d1) 3 = bd_bits d1 / 8) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    assert (SHB : 0 <= Z.shiftr (bd_bits d1) 3 <= 8) by (rewrite SH; Z.div_mod_to_equations; lia).
    assert (RLp : readLE64 bs 0 = Ok (le64v bs 0)) by (rewrite readLE64_ok by lia; reflexivity).
    assert (RL1 : reload_dstream bs d1 = Ok (EndOfBuffer, mkBD (le64v bs 0) (bd_bits d1 - bd_ptr d1 * 8) 0 false)).
    { unfold reload_dstream. replace (64 <? bd_bits d1) with false by (symmetry; apply Z.ltb_ge; lia).
      replace (8 <=? bd_ptr d1) with false by (symmetry; apply Z.leb_gt; lia).
      replace (bd_ptr d1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv beta iota zeta.
      replace (bd_ptr d1 - Z.shiftr (bd_bits d1) 3 <? 0) with true by (symmetry; apply Z.ltb_lt; lia). cbv beta iota zeta.
      replace (bd_ptr d1 - bd_ptr d1) with 0 by lia. rewrite RLp. reflexivity. }
    pose proof (RF_huf_fdw_pure.reload_facts2 bs d1 EndOfBuffer _ BY OK1 RL1) as (OK2 & BB2 & _ & _ & _).
    pose proof OK2 as (Q1 & Q2 & _). cbn [bd_bits] in Q2, BB2.
    destruct SM as (SM0 & C112). unfold bitdz_cellsA in C112. rewrite Z1 in C112.
    change (if false then AZEROFILLED else S0 + bd_ptr d1) with (S0 + bd_ptr d1) in C112.
    pose proof SM0 as (MU & WM & MI & STK & C80 & C96 & OUT).
    assert (SW : bv_swrap 32 (Z.shiftr (bv_wrap 32 (bd_bits d1)) 3) = Z.shiftr (bd_bits d1) 3).
    { replace (bv_wrap 32 (bd_bits d1)) with (bd_bits d1) by (unfold bv_wrap, bv_modulus; cbn [Z.of_N]; rewrite Z.mod_small by lia; reflexivity).
      apply swrap32_small. rewrite SH. Z.div_mod_to_equations; lia. }
    repeat zstep. l3_br false. repeat zstep. l3_br false. repeat zstep.
    rewrite SW. l3_br false. repeat zstep.
    rewrite l3_ne by (rewrite ?SH; Z.div_mod_to_equations; lia). l3_br false. repeat zstep.
    l3_br false. repeat zstep.
    try replace (S0 + bd_ptr d1 - S0) with (bd_ptr d1) by lia.
    l3_land32.
    l3_br false. repeat zstep.
    rewrite l3_ne by lia. l3_br false. do 4 zstep.
    l3_sub3 (bd_bits d1) (bd_ptr d1).
    replace (Z_to_bv 64 (S0 + bd_ptr d1 - bd_ptr d1)) with (Z_to_bv 64 (S0 + 0)) by (f_equal; lia).
    try l2_pc (AFSE_DECOMP + 6056).
    eapply (l2_ld f x R m jp OP0 I o0 s1a d1 (mkBD (le64v bs 0) (bd_bits d1 - bd_ptr d1 * 8) 0 false) EndOfBuffer
              (S0 + bd_ptr d1));
      [exact C6 | exact TLR | exact ROK | exact K | exact SI | exact D1 | exact RL1 | reflexivity | reflexivity
      | cbn [bd_ptr]; lia | cbn [bd_ptr]; lia | reflexivity | cbn [bd_bits]; lia | lia | exact SM0 | exact C112].
  Qed.

  Lemma sdt_seg_c_pf : sdt_seg_c.
  Proof.
    unfold sdt_seg_c. intros f C6.
    apply l2_cases; [exact (l2_cfast f C6) | exact (l2_czero f C6) | exact (l2_cclamp f C6) | exact (l2_cpart f C6)].
  Qed.
  End L2_local.

  Lemma l4_ds_cases : forall s bd, (exists q, decode_sym d false s bd = Ok q) \/ decode_sym d false s bd = Ub.
  Proof.
    intros s bd. unfold decode_sym, HufPure_FseDecomp.cell.
    destruct ((0 <=? s) && (s <? _)); cbn [bind]; [| right; reflexivity].
    unfold read_bits, look_bits, bit_mask.
    destruct ((0 <=? _) && (_ <? 32)); cbn [bind]; [left; eexists; reflexivity | right; reflexivity].
  Qed.

  Lemma l4_pure : forall f x R o0 s1a d1, tail_loop bs d dcap false (S f) x = R -> dres_ok R ->
    zlen (de_out x) <= dcap - 2 -> decode_sym d false (de_s1 x) (de_bd x) = Ok (o0, s1a, d1) -> 64 < bd_bits d1 ->
    exists o1 s2a d2, decode_sym d false (de_s2 x) (mkBD (bd_cont d1) (bd_bits d1) (bd_ptr d1) true) = Ok (o1, s2a, d2)
      /\ R = Ok (de_out x ++ [o0; o1]).
  Proof.
    intros f x R o0 s1a d1 TL ROK ZL DS1 B. cbn [tail_loop] in TL.
    lazymatch type of TL with context [?a <? ?b] =>
      replace (a <? b) with false in TL by (symmetry; apply Z.ltb_ge; unfold FseNCount.Zlength; lia) end.
    rewrite DS1 in TL. cbn [bind] in TL.
    unfold reload_dstream at 1 in TL.
    replace (64 <? bd_bits d1) with true in TL by (symmetry; apply Z.ltb_lt; lia).
    cbn [bind dstatus_eqb] in TL.
    destruct (l4_ds_cases (de_s2 x) (mkBD (bd_cont d1) (bd_bits d1) (bd_ptr d1) true)) as [[[[o1 s2a] d2] DS2] | DS2];
      rewrite DS2 in TL; cbn [bind] in TL.
    - exists o1, s2a, d2. split; [exact DS2 | symmetry; exact TL].
    - subst R. contradiction.
  Qed.

  Ltac l4_zl :=
    repeat match goal with H : ?T |- _ =>
      lazymatch type of T with Prop =>
        lazymatch T with
        | _ <= _ => fail | _ < _ => fail | _ = _ :> Z => fail | _ <= _ <= _ => fail | _ <= _ < _ => fail
        | _ => clear H end end end;
    Z.div_mod_to_equations; lia.
  Ltac l4_p2 := repeat match goal with |- context [2 ^ ?k] =>
    lazymatch k with Zpos _ => let v := eval vm_compute in (2 ^ k) in change (2 ^ k) with v end end.
  Ltac l4_zdec :=
    repeat match goal with
    | |- context [?a =? ?b] =>
        first [ replace (a =? b) with true by (symmetry; apply Z.eqb_eq; l4_zl)
              | replace (a =? b) with false by (symmetry; apply Z.eqb_neq; l4_zl) ]
    | |- context [?a <? ?b] =>
        first [ replace (a <? b) with true by (symmetry; apply Z.ltb_lt; l4_zl)
              | replace (a <? b) with false by (symmetry; apply Z.ltb_ge; l4_zl) ]
    end.
  Ltac l4_zbr :=
    unfold zx32; rewrite ?bv_ltu_Z, ?bv_eqb_Z, ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N];
    rewrite ?Z.shiftr_div_pow2 by lia; l4_p2;
    repeat match goal with |- context [?a mod ?N] =>
      lazymatch N with Zpos _ => idtac end; rewrite (Z.mod_small a N) by l4_zl end;
    l4_zdec; reflexivity.
  Ltac l4_br :=
    lazymatch goal with |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      first [ replace c with false; [cbv iota | symmetry; l4_zbr]
            | replace c with true; [cbv iota | symmetry; l4_zbr] ] end.

  Lemma sdt_fin2_pf : sdt_seg_fin2.
  Proof.
    unfold sdt_seg_fin2, sdt_c6892.
    intros f x R m jp OP0 I o0 s1a d1 ra a1 a2 a3 s3 s6 s7 s8 s9 s10 s11 t6 TLx ROK K HI DS1 B64 HM.
    pose proof HI as (BOK & BB & ZL & OPI & DOP & I0).
    destruct (l4_pure f x R o0 s1a d1 TLx ROK ZL DS1 B64) as (o1 & s2a & d2 & DS2 & RE).
    destruct (RF_huf_fdw_sm.dec_inv tl [] d ltac:(lia) HCELLS HCOK _ _ _ _ _ DS1 ltac:(destruct BOK as (_ & ? & _); lia))
      as (c1 & _ & _ & _ & NBR1 & _ & _ & _ & _ & ED1).
    assert (D1B : 0 <= bd_cont d1 < 2^64 /\ 0 <= bd_bits d1 <= 2^30)
      by (rewrite ED1; cbn [bd_cont bd_bits]; destruct BOK as (? & ? & _); lia).
    clear ED1 NBR1 c1.
    pose proof HM as ((MU & WM & MI & STK & C80 & C96 & (junk & OUTA & LJ)) & C112).
    destruct (HAT m MU WM) as (TBm & SRCm & FCm & ZDTm & ZMKm & ZDSTm & ZOBJm & USRCm & RTCm).
    pose proof (spaf_props SPV SP16) as (SPAB & SPA32). pose proof LO as LO'. unfold DEC_STACK in LO'.
    pose proof ATOP_range as AR; unfold ATOP_MIN, ATOP_MAX in AR.
    pose proof (ablk_lin _ _ HDST) as LDS.
    unfold bitdz_cellsA in C112.
    do 3 zstep.
    lazymatch type of C112 with rw_cells _ _ _ [_; _; _; C8 (Z_to_bv 64 ?V); _; _] =>
      replace V with AZEROFILLED in C112 by (unfold AZEROFILLED, AFSE_DECOMP; lia) end.
    set (d1r := mkBD (bd_cont d1) (bd_bits d1) (bd_ptr d1) true) in *.
    lazymatch type of C112 with rw_cells _ ?mm _ _ =>
      change (rw_cells bsegs mm (SP1 + 112) (bitdz_cellsA S0 d1r jp)) in C112 end.
    do 3 zstep.
    destruct (HAT m1 MU WM) as (TB1 & SRC1 & FC1 & ZDT1 & ZMK1 & ZDST1 & ZOB1 & US1 & RT1).
    assert (ZDS1 : zshadow m1 (SP1 + 80) 16) by (eapply zshadow_sub; [exact ZOB1 | lia | lia]).
    assert (ZBD1 : zshadow m1 (SP1 + 112) 40) by (eapply zshadow_sub; [exact ZOB1 | lia | lia]).
    assert (RDS1 : rng RNG (SP1 + 80) 16) by (eapply rng_sub; [exact RO | lia | lia]).
    assert (RBD1 : rng RNG (SP1 + 112) 40) by (eapply rng_sub; [exact RO | lia | lia]).
    assert (RDSs : rng RNG (shad (SP1 + 80)) 2) by (eapply rng_sub; [exact ROs | lia | lia]).
    assert (RBDs : rng RNG (shad (SP1 + 112)) 5)
      by (eapply rng_sub; [exact ROs | |]; rewrite !shad_div; Z.div_mod_to_equations; lia).
    assert (RST1 : rng RNG (SP1 - DSYM_STACK) DSYM_STACK) by (unfold DSYM_STACK; eapply rng_sub; [exact RSTK | lia | lia]).
    assert (HTL1 : 1 <= tl <= 12) by lia.
    assert (D1R : 0 <= bd_cont d1r < 2^64 /\ 0 <= bd_bits d1r <= 2^30) by (unfold d1r; cbn [bd_cont bd_bits]; exact D1B).
    destruct D1R as (D1R1 & D1R2).
    pose proof fse_dsym_proofA as DSY. unfold dsym_stmtA in DSY.
    eapply evtF_cut.
    { eapply DSY with (DS := SP1 + 80) (BD := SP1 + 112) (DT := DT) (S := S0) (dt := d) (d := d1r) (jp := jp) (lo := lo)
                      (s := de_s2 x) (o := o1) (s' := s2a) (d' := d2);
        first [ assumption | (unfold DSYM_STACK; lia) | (Z.div_mod_to_equations; lia) ]. }
    intros ms' (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & m2 & -> & MU2 & WM2 & MI2 & STK2 & C80b & C112b).
    replace (ret_pc (Z_to_bv 64 (AFSE_DECOMP + 6916))) with (Z_to_bv 64 (AFSE_DECOMP + 6916))
      by (symmetry; apply ret_pc_even; [unfold AFSE_DECOMP; lia | reflexivity]).
    pose proof LDS as (LD1 & LD2 & LD3 & LD4).
    assert (MU02 : munch W0 m0 m2).
    { eapply munch_trans; [exact MU | eapply munch_weaken; [| exact MU2]].
      unfold sub_fp; intros z Hz; cbn [outside] in Hz |- *; unfold DSYM_STACK in *.
      destruct Hz as (H1 & H2 & H3 & _); repeat split; lia. }
    assert (WM02 : wmono bsegs m0 m2) by (eapply wmono_trans; [exact WM | exact WM2]).
    eapply rw_cells_transport in C96; [| exact MU2 | exact WM2 | cbn; unfold DSYM_STACK; lia].
    eapply u8arr_transport in OUTA; [| exact MU2 | exact WM2 |
      rewrite length_app, length_map; cbn [disjoint_from]; unfold DSYM_STACK; lia].
    clear MU2.
    destruct (HAT m2 MU02 WM02) as (TB2 & SRC2 & FC2 & ZDT2 & ZMK2 & ZDST2 & ZOB2 & US2 & RT2).
    unfold ASHOFF. unfold ASHOFF in FC2.
    assert (ZO1 : zlen (de_out x ++ [o0]) = zlen (de_out x) + 1) by (rewrite length_app; cbn [length]; lia).
    zstep. zstep. l4_br. do 3 zstep.
    pose proof (chkZ m2 DST dcap (OP0 + I + 1) ZDST2 ltac:(lia) ltac:(lia)) as RDB.
    pose proof (acc_shZ RNG DST dcap (OP0 + I + 1) RDSTs ltac:(lia)) as ACO.
    zstep. rewrite ?sxb0. clear RDB. zstep. l4_br.
    zstep.
    set (out1 := de_out x ++ [o0]) in *.
    pose proof (u8arr_store_ok bsegs m2 DST _ (zlen out1) (wa (OP0 + I + 1)) OUTA
                  ltac:(repeat (rewrite length_app || rewrite length_map); cbn [length]; lia) ltac:(f_equal; lia)) as SOK.
    zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?mm (Z_to_bv 64 (OP0 + I + 1)) ?bs) _) =>
      change (write_to_mem mm (Z_to_bv 64 (OP0 + I + 1)) bs) with (write_to_mem mm (wa (OP0 + I + 1)) bs);
      replace (write_to_mem mm (wa (OP0 + I + 1)) bs) with (write_to_mem mm (wa (DST + zlen out1)) bs)
        by (replace (DST + zlen out1) with (OP0 + I + 1) by lia; reflexivity) end.
    rewrite le1_lit.
    pose proof (RF_huf_fdw_kit.out_sb bsegs m2 DST out1 junk o1 OUTA ltac:(lia)) as OUT2.
    assert (LJ2 : zlen (List.tl junk) = dcap - zlen (out1 ++ [o1]))
      by (rewrite length_app; cbn [length]; rewrite RF_huf_fdw_sm.zlen_tl by lia; lia).
    clear OUTA LJ. store_done.
    do 4 zstep.
    zstep.
    unfold out1 in OUT2, LJ2. rewrite <- app_assoc in OUT2, LJ2. cbn [app] in OUT2, LJ2.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (SM : sdtM mm (de_out x ++ [o0; o1]) s1a s2a d2 jp)
        by (unfold sdtM, sdtM0;
            refine (conj (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (ex_intro _ (List.tl junk) (conj _ _)))))))) _);
            assumption);
      eapply (sdt_exitK R mm _ _ _ _ _ _); [exact K | exact SM | |] end.
    - rewrite RE. cbn [dresA]. split.
      + rewrite length_app. cbn [length]. lia.
      + exists (List.tl junk). split; [exact OUT2 | exact LJ2].
    - lia.
  Qed.


  Lemma l5_ds_cases : forall s bd, (exists q, decode_sym d false s bd = Ok q) \/ decode_sym d false s bd = Ub.
  Proof.
    intros s bd. unfold decode_sym, HufPure_FseDecomp.cell.
    destruct ((0 <=? s) && (s <? _)); cbn [bind]; [| right; reflexivity].
    unfold read_bits, look_bits, bit_mask.
    destruct ((0 <=? _) && (_ <? 32)); cbn [bind]; [left; eexists; reflexivity | right; reflexivity].
  Qed.

  Lemma l5_ds : forall s bd o s' bd', decode_sym d false s bd = Ok (o, s', bd') -> 0 <= bd_bits bd < 2^30 ->
    bd_cont bd' = bd_cont bd /\ bd_ptr bd' = bd_ptr bd /\ bd_zero bd' = bd_zero bd /\ bd_bits bd <= bd_bits bd' <= bd_bits bd + 12.
  Proof.
    intros s bd o s' bd' H B. unfold decode_sym, HufPure_FseDecomp.cell in H.
    destruct ((0 <=? s) && (s <? FseNCount.Zlength (dt_cells d))) eqn:E; [|discriminate H].
    cbn [bind] in H. unfold read_bits in H.
    destruct (look_bits bd (dc_nbBits (nth (Z.to_nat s) (dt_cells d) (mkDC 0 0 0)))) eqn:LB; cbn [bind] in H; try discriminate H.
    injection H as _ _ <-. unfold skip_bits. cbn [bd_cont bd_bits bd_ptr bd_zero].
    assert (NB : 0 <= dc_nbBits (nth (Z.to_nat s) (dt_cells d) (mkDC 0 0 0)) <= tl).
    { pose proof HCOK as HC. unfold RF_huf_fdw_sm.cells_ok in HC. rewrite Forall_forall in HC.
      apply andb_true_iff in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
      change (FseNCount.Zlength (dt_cells d)) with (Z.of_nat (length (dt_cells d))) in E2.
      destruct (HC (nth (Z.to_nat s) (dt_cells d) (mkDC 0 0 0))) as (_ & HN & _); [apply nth_In; lia | lia]. }
    unfold u32. rewrite Z.mod_small by lia. repeat split; lia.
  Qed.

  Lemma l5_ovf : forall bd, 64 < bd_bits bd ->
    reload_dstream bs bd = Ok (Overflow, mkBD (bd_cont bd) (bd_bits bd) (bd_ptr bd) true).
  Proof.
    intros bd H. unfold reload_dstream. replace (64 <? bd_bits bd) with true by (symmetry; apply Z.ltb_lt; lia).
    reflexivity.
  Qed.

  Lemma l5_pure : forall f x R o0 s1a d1 st1 d1r o1 s2a d2,
    tail_loop bs d dcap false (S f) x = R -> dres_ok R -> zlen (de_out x) <= dcap - 2 ->
    decode_sym d false (de_s1 x) (de_bd x) = Ok (o0, s1a, d1) ->
    reload_dstream bs d1 = Ok (st1, d1r) -> dstatus_eqb st1 Overflow = false -> zlen (de_out x) + 1 <= dcap - 2 ->
    decode_sym d false (de_s2 x) d1r = Ok (o1, s2a, d2) -> 64 < bd_bits d2 ->
    exists o2 s' d', decode_sym d false s1a (mkBD (bd_cont d2) (bd_bits d2) (bd_ptr d2) true) = Ok (o2, s', d') /\
      R = Ok ((de_out x ++ [o0]) ++ [o1; o2]).
  Proof.
    intros f x R o0 s1a d1 st1 d1r o1 s2a d2 TL0 ROK Z0 D1 R1 S1 Z1 D2 B2. cbn [tail_loop] in TL0.
    change (FseNCount.Zlength (de_out x)) with (zlen (de_out x)) in TL0.
    replace (dcap - 2 <? zlen (de_out x)) with false in TL0 by (symmetry; apply Z.ltb_ge; lia).
    rewrite D1 in TL0. cbn [bind] in TL0. rewrite R1 in TL0. cbn [bind] in TL0. rewrite S1 in TL0.
    replace (dcap - 2 <? FseNCount.Zlength (de_out x ++ [o0])) with false in TL0
      by (symmetry; apply Z.ltb_ge; change (FseNCount.Zlength (de_out x ++ [o0])) with (Z.of_nat (length (de_out x ++ [o0])));
          change (zlen (de_out x)) with (Z.of_nat (length (de_out x))) in Z1; rewrite length_app; cbn [length]; lia).
    rewrite D2 in TL0. cbn [bind] in TL0. rewrite (l5_ovf d2 B2) in TL0. cbn [bind dstatus_eqb] in TL0.
    destruct (l5_ds_cases s1a (mkBD (bd_cont d2) (bd_bits d2) (bd_ptr d2) true)) as [[[[o2 s'] d'] D3] | D3];
      rewrite D3 in TL0; cbn [bind] in TL0.
    - exists o2, s', d'. split; [exact D3 | symmetry; exact TL0].
    - subst R. contradiction.
  Qed.

  Ltac l5_retlit := lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
    replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; unfold AFSE_DECOMP; [lia | reflexivity]) end.
  Ltac l5_side := cbn [bd_cont bd_bits bd_ptr bd_zero]; unfold DSYM_STACK;
    first [ lia | (Z.div_mod_to_equations; lia)
          | (eapply rng_sub; [exact RO | lia | lia]) | (eapply rng_sub; [exact RSTK | lia | lia])
          | (eapply rng_sub; [exact ROs | |]; unfold shad; rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8;
             Z.div_mod_to_equations; lia) ].

  Lemma l5_zsub : forall m X n Y k, zshadow m X n -> X <= Y -> Y + k <= X + n -> zshadow m Y k.
  Proof. intros m X n Y k H A B a Ha. apply H. lia. Qed.

  Lemma sdt_fin1_pf : sdt_seg_fin1.
  Proof.
    unfold sdt_seg_fin1, sdt_c6956.
    intros f x R m jp OP0 I o0 s1a o1 s2a d1 d1r d2 st1 ra a1 a2 a3 s3 s6 s7 s8 s9 s10 s11 t6
      TLx ROK K HI DS1 RL NO ZL1 DS2 B2 HM.
    pose proof HI as (BOK & BB & ZL & OPI & DOP & I0).
    destruct (l5_pure f x R o0 s1a d1 st1 d1r o1 s2a d2 TLx ROK ZL DS1 RL NO ZL1 DS2 B2) as (o2 & s' & d' & DS3 & RE).
    pose proof BOK as (K1 & K2 & K3 & K4 & K5 & K6).
    destruct (l5_ds _ _ _ _ _ DS1 ltac:(lia)) as (E1 & E2 & E3 & E4).
    assert (OK1 : bitd_ok bs d1).
    { unfold bitd_ok. rewrite E1, E2, E3. repeat split; try lia. intros ZZ. specialize (K6 ZZ). lia. }
    destruct (RF_huf_fdw_pure.reload_facts2 bs d1 st1 d1r BY OK1 RL) as (OK2 & RB2 & _ & _ & _).
    pose proof OK2 as (L1 & L2 & _).
    destruct (l5_ds _ _ _ _ _ DS2 ltac:(lia)) as (F1 & F2 & F3 & F4).
    clear E1 E2 E3 F2 F3 K3 K4 K5 K6.
    pose proof HM as ((MU & WM & MI & STK & C80 & C96 & (junk & OUTA & LJ)) & C112).
    pose proof (spaf_props SPV SP16) as (SPAB & SPA32). pose proof LO as LO'. unfold DEC_STACK in LO'.
    pose proof (ablk_lin _ _ HDST) as LDS. pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    unfold bitdz_cellsA in C112.
    assert (ZO2 : zlen (de_out x ++ [o0; o1]) = zlen (de_out x) + 2) by (rewrite length_app; cbn [length]; lia).
    do 3 zstep.
    lazymatch type of C112 with rw_cells _ _ _ [_; _; _; C8 (Z_to_bv 64 ?E); _; _] =>
      replace E with AZEROFILLED in C112 by (unfold AZEROFILLED, AFSE_DECOMP; lia) end.
    do 3 zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    assert (C112z : rw_cells bsegs m1 (SP1 + 112) (bitdz_cellsA S0 (mkBD (bd_cont d2) (bd_bits d2) (bd_ptr d2) true) jp))
      by exact C112.
    destruct (HAT m1 MU WM) as (TBm & _ & _ & ZDTm & ZMKm & _ & ZOBJm & _ & RTCm).
    pose proof fse_dsym_proofA as DSY. unfold dsym_stmtA in DSY.
    eapply evtF_cut.
    { eapply DSY with (RNG := RNG) (SPV := SP1) (lo := lo) (DS := SP1 + 96) (BD := SP1 + 112) (DT := DT) (S := S0)
        (s := s1a) (o := o2) (s' := s') (dt := d) (d := mkBD (bd_cont d2) (bd_bits d2) (bd_ptr d2) true) (d' := d') (jp := jp);
      first [ exact C96 | exact C112z | exact TBm | exact HCELLS | exact HCOK | exact DS3 | exact HDT | exact STK | exact MI
            | exact RTCm | exact ZDTm | exact ZMKm | exact RDT | exact RDTs | exact RI | exact RISH
            | (eapply l5_zsub; [exact ZOBJm | lia | lia]) | l5_side ]. }
    intros ms' (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & m2 & -> & MU2 & WM2 & MI2 & STK2 & DSC & BDC).
    unfold DSYM_STACK in MU2. l5_retlit.
    assert (MU12 : munch W0 m0 m2).
    { eapply munch_trans; [exact MU | eapply munch_weaken; [| exact MU2]].
      intros z Hz; cbn [outside] in Hz |- *. destruct Hz as (H1 & H2 & H3 & _). repeat split; lia. }
    assert (WM12 : wmono bsegs m0 m2) by (eapply wmono_trans; [exact WM | exact WM2]).
    eapply rw_cells_transport in C80; [| exact MU2 | exact WM2 | cbn; lia].
    eapply u8arr_transport in OUTA; [| exact MU2 | exact WM2 | cbn [disjoint_from]; rewrite length_app, length_map; lia].
    clear MU WM MI STK C96 C112 C112z TBm ZDTm ZMKm ZOBJm RTCm DSY MU2 WM2.
    unfold bitdz_cellsA in BDC.
    destruct (HAT m2 MU12 WM12) as (_ & _ & FC2 & _ & _ & ZD2 & _).
    unfold ASHOFF. unfold ASHOFF in FC2.
    zstep. zstep. zstep. sdt_br false.
    do 3 zstep.
    pose proof (chkZ m2 DST dcap (OP0 + I + 2) ZD2 ltac:(lia) ltac:(lia)) as RDB.
    pose proof (acc_shZ RNG DST dcap (OP0 + I + 2) RDSTs ltac:(lia)) as ACO.
    zstep. rewrite ?sxb0. clear RDB. zstep. sdt_br false.
    zstep.
    pose proof (u8arr_store_ok bsegs m2 DST _ (zlen (de_out x ++ [o0; o1])) (wa (OP0 + I + 2)) OUTA
                  ltac:(repeat (rewrite length_app || rewrite length_map); cbn [length]; lia) ltac:(f_equal; lia)) as SOK.
    zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?mm (Z_to_bv 64 (OP0 + I + 2)) ?bs) _) =>
      change (write_to_mem mm (Z_to_bv 64 (OP0 + I + 2)) bs) with (write_to_mem mm (wa (OP0 + I + 2)) bs);
      replace (write_to_mem mm (wa (OP0 + I + 2)) bs) with (write_to_mem mm (wa (DST + zlen (de_out x ++ [o0; o1]))) bs)
        by (replace (DST + zlen (de_out x ++ [o0; o1])) with (OP0 + I + 2) by lia; reflexivity) end.
    rewrite le1_lit.
    pose proof (RF_huf_fdw_kit.out_sb bsegs m2 DST (de_out x ++ [o0; o1]) junk o2 OUTA ltac:(lia)) as OUT2.
    assert (LJ2 : zlen (List.tl junk) = dcap - zlen ((de_out x ++ [o0; o1]) ++ [o2]))
      by (rewrite length_app; cbn [length]; rewrite RF_huf_fdw_sm.zlen_tl by lia; lia).
    clear OUTA LJ. store_done.
    do 4 zstep.
    rewrite <- !app_assoc in OUT2, LJ2. cbn [app] in OUT2, LJ2.
    rewrite <- app_assoc in RE. cbn [app] in RE. rewrite RE in K.
    replace (OP0 + I + 3 - DST) with (zlen (de_out x ++ [o0; o1; o2]))
      by (rewrite length_app; cbn [length]; lia).
    eapply (sdt_exitK (Ok (de_out x ++ [o0; o1; o2])) _ (de_out x ++ [o0; o1; o2]) s' s2a d' jp);
      [exact K | | | ].
    - unfold sdtM, sdtM0.
      refine (conj (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (ex_intro _ (List.tl junk) (conj _ _)))))))) _);
        assumption.
    - cbn [dresA]. split; [reflexivity | exists (List.tl junk); split; assumption].
    - rewrite length_app in LJ2 |- *. cbn [length] in LJ2 |- *. lia.
  Qed.

  Lemma sdt_final : dres_ok (decompress_usingDTable bs d dcap false) ->
    sdtK (decompress_usingDTable bs d dcap false) ->
    forall (r : dec) (m2 : amem) (jp junk : list byte)
           (x1 x6 x7 x10 x11 x12 x13 x14 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    decompress_usingDTable bs d dcap false = tail_loop bs d dcap false (Datatypes.S (Z.to_nat dcap)) r ->
    bitd_ok bs (de_bd r) -> bd_bits (de_bd r) <= 2^29 -> zlen (de_out r) <= dcap ->
    munch W0 m0 m2 -> wmono bsegs m0 m2 -> mem_inv bsegs m2 -> stk bsegs m2 lo SP1 ->
    u8arr bsegs m2 DST (map (Z_to_bv 8) (de_out r) ++ junk) -> zlen junk = dcap - zlen (de_out r) ->
    rw_cells bsegs m2 (SP1 + 80) [C8 (Z_to_bv 64 (de_s2 r)); C8 (Z_to_bv 64 (DT + 4))] ->
    rw_cells bsegs m2 (SP1 + 96) [C8 (Z_to_bv 64 (de_s1 r)); C8 (Z_to_bv 64 (DT + 4))] ->
    rw_cells bsegs m2 (SP1 + 112) (bitdz_cellsA S0 (de_bd r) jp) ->
    evtF bsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 SP1) gp tp (Z_to_bv 64 (DST + zlen (de_out r))) x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SP1)
               x10 x11 x12 x13 x14 (Z_to_bv 64 (2^61)) (Z_to_bv 64 (2^16 - 1)) (Z_to_bv 64 ABIT_MASK)
               (Z_to_bv 64 (Z.shiftr FF 3 + ASHOFF)) (Z_to_bv 64 (DST + dcap - 3)) x20 (Z_to_bv 64 (DST + dcap))
               x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          FR (Z_to_bv 64 (AFSE_DECOMP + 5528)) fc None m2 (seg_rom bsegs)).
  Proof.
    exact (sdt_bridge (sdt_tail sdt_seg_a_pf sdt_seg_b_pf sdt_seg_c_pf sdt_seg_d_pf sdt_seg_e_pf sdt_seg_f_pf
                                sdt_fin2_pf sdt_fin1_pf sdt_entry_pf)).
  Qed.
End SDT.

Definition stA_tail_stmt : Prop :=
  forall (RNG : footprint) (Q : machine_state -> Prop) (m0 : amem) (SPV FF DST dcap S0 DT lo RLO RHI : Z) (bs : list Z)
         (d : dtable) (gp tp : word) (FR : bvmap 5 word) (fc : bv 32) (j48 jd : list byte),
    rw_cells bsegs m0 (SPAf SPV + 32) [C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 2147450880)] ->
    rw_cells bsegs m0 (SPAf SPV + 80) [CB 72 j48] -> stk bsegs m0 lo (SPAf SPV) -> ATOP + 4096 <= lo ->
    lo <= SPAf SPV - DEC_STACK -> SPV mod 16 = 0 -> SPV + 16 <= 2^47 ->
    zshadow m0 (SPAf SPV + 80) 72 -> shclean m0 (SPAf SPV + 112) (SPAf SPV + 152) RLO RHI ->
    rng RNG (shad RLO) (shad RHI - shad RLO) -> rng RNG (SPAf SPV + 80) 72 -> rng RNG (shad (SPAf SPV + 80)) 9 ->
    rng RNG (SPAf SPV + 32) 32 ->
    5 <= dt_tableLog d <= 12 -> zlen (dt_cells d) = 2^(dt_tableLog d) -> RF_huf_fdw_sm.cells_ok (dt_tableLog d) (dt_cells d) ->
    dt_fastMode d = 0 ->
    rw_cells bsegs m0 DT [C2 (Z_to_bv 64 (dt_tableLog d)); C2 (Z_to_bv 64 0)] ->
    bytes_at bsegs m0 (DT + 4) (concat (map fse_cell_bytes (dt_cells d))) ->
    ablk DT (DT + 4 + 4 * 2^(dt_tableLog d)) -> DT mod 4 = 0 -> zshadow m0 DT (4 + 4 * 2^(dt_tableLog d)) ->
    rng RNG DT (4 + 4 * 2^(dt_tableLog d)) -> rng RNG (shad DT) (nshad (4 + 4 * 2^(dt_tableLog d) + DT mod 8)) ->
    bytes_at bsegs m0 S0 (map (Z_to_bv 8) bs) -> Forall (fun c => 0 <= c < 256) bs -> zlen bs <= 65536 ->
    ablk S0 (S0 + zlen bs) -> S0 + 8 <= 2^47 -> 16 <= S0 -> unpoisoned m0 S0 (S0 + zlen bs) ->
    rng RNG S0 (zlen bs) -> rng RNG (shad S0) (nshad (zlen bs + S0 mod 8)) ->
    dres_ok (decompress_usingDTable bs d dcap false) ->
    u8arr bsegs m0 DST jd -> zlen jd = dcap -> 0 <= dcap <= 255 -> ablk DST (DST + dcap) -> 3 <= DST ->
    zshadow m0 DST dcap -> rng RNG DST dcap -> rng RNG (shad DST) (nshad (dcap + DST mod 8)) ->
    (DST + dcap <= S0 \/ S0 + zlen bs <= DST) -> (DST + dcap <= DT \/ DT + 4 + 4 * 2^(dt_tableLog d) <= DST) ->
    (S0 + zlen bs <= DT \/ DT + 4 + 4 * 2^(dt_tableLog d) <= S0) ->
    mem_inv bsegs m0 -> artcells m0 -> zshadow m0 ABIT_MASK 128 ->
    rng RNG lo (SPAf SPV - lo) -> rng_aimg RNG -> rng_aimg_sh RNG ->
    (forall m1 rv (j48' : list byte) (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word),
       munch [(lo, SPAf SPV); (SPAf SPV + 80, SPAf SPV + 152); (DST, DST + dcap)] m0 m1 -> wmono bsegs m0 m1 ->
       mem_inv bsegs m1 -> stk bsegs m1 lo (SPAf SPV) -> rw_cells bsegs m1 (SPAf SPV + 80) [CB 72 j48'] ->
       rw_cells bsegs m1 (SPAf SPV + 32) [C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 2147450880)] ->
       dresA DST dcap (decompress_usingDTable bs d dcap false) m1 rv -> 0 <= rv < 2^64 ->
       evtF bsegs RNG Q
         (MS (mkR y1 (Z_to_bv 64 (SPAf SPV)) gp tp y5 y6 y7 (Z_to_bv 64 SPV) (Z_to_bv 64 (SPAf SPV)) (Z_to_bv 64 rv)
                  y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) y19
                  y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
             FR (Z_to_bv 64 623384) fc None m1 (seg_rom bsegs))) ->
    forall (r : dec) (m2 : amem) (jp junk : list byte)
           (x1 x6 x7 x10 x11 x12 x13 x14 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    decompress_usingDTable bs d dcap false = tail_loop bs d dcap false (Datatypes.S (Z.to_nat dcap)) r ->
    0 < zlen bs -> bitd_ok bs (de_bd r) -> bd_bits (de_bd r) <= 2^29 -> zlen (de_out r) <= dcap -> Forall (fun c => 0 <= c < 256) (de_out r) ->
    munch [(lo, SPAf SPV); (SPAf SPV + 80, SPAf SPV + 152); (DST, DST + dcap)] m0 m2 -> wmono bsegs m0 m2 ->
    mem_inv bsegs m2 -> stk bsegs m2 lo (SPAf SPV) -> bytes_at bsegs m2 S0 (map (Z_to_bv 8) bs) ->
    u8arr bsegs m2 DST (map (Z_to_bv 8) (de_out r) ++ junk) -> zlen junk = dcap - zlen (de_out r) ->
    rw_cells bsegs m2 (SPAf SPV + 32) [C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 2147450880)] ->
    rw_cells bsegs m2 (SPAf SPV + 80) [C8 (Z_to_bv 64 (de_s2 r)); C8 (Z_to_bv 64 (DT + 4))] ->
    rw_cells bsegs m2 (SPAf SPV + 96) [C8 (Z_to_bv 64 (de_s1 r)); C8 (Z_to_bv 64 (DT + 4))] ->
    rw_cells bsegs m2 (SPAf SPV + 112) (bitdz_cellsA S0 (de_bd r) jp) ->
    evtF bsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 (SPAf SPV)) gp tp (Z_to_bv 64 (DST + zlen (de_out r))) x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 (SPAf SPV))
               x10 x11 x12 x13 x14 (Z_to_bv 64 (2^61)) (Z_to_bv 64 (2^16 - 1)) (Z_to_bv 64 ABIT_MASK)
               (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 (DST + dcap - 3)) x20 (Z_to_bv 64 (DST + dcap))
               x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          FR (Z_to_bv 64 628472) fc None m2 (seg_rom bsegs)).

Theorem stA_tailA : stA_tail_stmt.
Proof.
  unfold stA_tail_stmt.
  intros RNG Q m0 SPV FF DST dcap S0 DT lo RLO RHI bs d gp tp FR fc j48 jd FC32 C80j STK0 BOT LO SP16 SPH ZOBJ SHC
    RSH RO ROs RO32 HTL HCELLS HCOK FM DTH TBB HDT DT4 ZDT RDT RDTs SRC BY ZLB HS0 S8 S16 USRC RS RSs ROK
    UJD LJD DC HDST DST3 ZDST RDST RDSTs DJ2 DJ1 DJ3 MI0 RTC ZMK RSTK RI RISH KK
    r m2 jp junk x1 x6 x7 x10 x11 x12 x13 x14 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    DEQ NZ BOK BB ZL FO MU WM MI ST SRC2 UA LJ FC2 C80 C96 C112.
  eapply (sdt_final RNG Q m0 SPV FF DST dcap S0 DT lo bs d gp tp FR fc).
  all: first [exact KK | eassumption].
Qed.

End CANSEC1.
