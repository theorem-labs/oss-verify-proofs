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
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw FseRdKit HufWalkKit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require FseWalkKit FseRdKit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_hint ::= bdtA_acc_hint.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Lemma fdA_sh0 : forall (m : amem) lo hi a, unpoisoned m lo hi -> lo <= a -> 8 * (a / 8) + 8 <= hi -> hi <= KEND ->
  exists b, rw_cells bsegs m (Z.shiftr a 3 + ASHOFF) [C1 b] /\ Z.shiftr a 3 + ASHOFF + 1 <= KHIGH /\ sval b = 0.
Proof.
  intros m lo hi a U L H K.
  assert (A8 : Z.shiftr a 3 = a / 8) by (apply Z.shiftr_div_pow2; destruct U; lia).
  pose proof U as (U0 & U1 & U2).
  destruct (U2 (Z.shiftr a 3) ltac:(Z.div_mod_to_equations; lia) ltac:(rewrite A8; Z.div_mod_to_equations; lia)
             ltac:(rewrite A8; Z.div_mod_to_equations; lia)) as (b & MB & GB).
  exists b. split; [|split].
  - apply AProg_kit.c1_of_byte; [rewrite A8; unfold ASHOFF; Z.div_mod_to_equations; lia
                               | rewrite A8; unfold ASHOFF, KEND in *; Z.div_mod_to_equations; lia |].
    rewrite Z.add_comm; exact MB.
  - apply AProg_kit.shad_lt_KHIGH; Z.div_mod_to_equations; lia.
  - unfold gran_ok in GB. rewrite A8, Z.min_l in GB by lia. destruct GB as [G0|G0]; [exact G0 | lia].
Qed.

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
  Ltac fbr b := lazymatch goal with |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
    replace c with b; [cbv iota | symmetry; rewrite ?bv_ltu_Z, ?bv_eqb_Z, ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N];
      first [apply Z.ltb_ge | apply Z.ltb_lt | apply Z.eqb_eq | apply Z.eqb_neq
            | apply Bool.negb_true_iff, Z.ltb_ge | apply Bool.negb_false_iff, Z.ltb_lt
            | apply Bool.negb_true_iff, Z.eqb_neq | apply Bool.negb_false_iff, Z.eqb_eq]; Z.div_mod_to_equations; lia] end.

  (* [comment removed for export] *)
  Ltac fappW := unfold appW; repeat (apply Forall_cons; [cbn [fst snd]; right; unfold KHIGH; lia |]); apply Forall_nil.

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

  Definition fdA_K992 (x22 x23 x24 x25 : word) : Prop :=
    forall m3 db v1 d1 s1 d2 v2 d3 s2 d4 jp (r1 t0 t1 t2 a3 a5 a6 a7 t3 t4 t5 t6 : word),
      FDPRE db v1 d1 s1 d2 v2 d3 s2 d4 -> bitd_ok bs d4 -> bd_bits d4 <= 64 -> bd_zero d4 = false -> 0 < bd_ptr d4 < 8 ->
      FDMEM m3 v1 v2 -> rw_cells bsegs m3 (SP1 + 112) (bitdz_cellsA S0 d4 jp) ->
      evtF bsegs RNG Q (SBI 0x98540 m3 r1 t0 t1 t2 (Z_to_bv 64 (S0 + 8)) (Z_to_bv 64 (bd_bits d4)) (Z_to_bv 64 (S0 + bd_ptr d4))
                         a3 (Z_to_bv 64 S0) a5 a6 a7 x22 x23 x24 x25 t3 t4 t5 t6).

  (* [comment removed for export] *)
  Ltac fzlit x := lazymatch x with 0%Z => idtac | 1%Z => idtac end.
  Ltac fzx := repeat match goal with
    | |- context [Z.lxor ?x ?y <? 1] =>
        replace (Z.lxor x y <? 1) with false by
          (symmetry; apply Z.ltb_ge;
           assert (0 <= Z.lxor x y) by (apply (proj2 (Z.lxor_nonneg x y)); split; intro; Z.div_mod_to_equations; lia);
           assert (Z.lxor x y <> 0) by (rewrite Z.lxor_eq_0_iff; Z.div_mod_to_equations; lia); lia)
    | |- context [0 <? ?a] => replace (0 <? a) with true by (symmetry; apply Z.ltb_lt; Z.div_mod_to_equations; lia)
    | |- context [Z.lxor ?x ?y] => fzlit x; fzlit y; let v := eval vm_compute in (Z.lxor x y) in change (Z.lxor x y) with v
    | |- context [Z.land ?x ?M] =>
        replace (Z.land x M) with x by (symmetry; change M with (Z.ones 32); rewrite Z.land_ones by lia; apply Z.mod_small; Z.div_mod_to_equations; lia)
    end; cbn [Z.b2z Z.lxor].
  Ltac fwk := repeat first [ zstep | fbr true | fbr false | progress fzx ].
  Ltac fat n := lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?p) _ _ _ _) =>
    let dd := eval vm_compute in (p - 0x98160) in constr_eq dd n end.
  Ltac fwk_to n := repeat (tryif fat n then fail else first [ zstep | fbr true | fbr false | progress fzx ]).
  Ltac frd H := lazymatch goal with |- ov_read_bytes _ _ (Z_to_bv 64 ?a) 1 = Some [Z_to_bv 8 (Znth ?i _)] =>
    replace a with (S0 + i) by ring; apply src_rd; [exact H | lia] end.

  (* [comment removed for export] *)
  Lemma fdA_p1148 : forall (x22 x23 x24 x25 : word), fdA_K1636 x22 x23 x24 x25 ->
    forall m4 db v1 d1 s1 d2 v2 d3 s2 d4 jp nb (c0 r1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      FDPRE db v1 d1 s1 d2 v2 d3 s2 d4 -> bitd_ok bs d4 -> bd_bits d4 <= 64 -> bd_zero d4 = false -> 0 < bd_ptr d4 < 8 ->
      ((0 <= bd_ptr d4 - bd_bits d4 / 8 /\ nb = bd_bits d4 / 8) \/ (bd_ptr d4 - bd_bits d4 / 8 < 0 /\ nb = bd_ptr d4)) ->
      FDMEM m4 v1 v2 ->
      rw_cells bsegs m4 (SP1 + 112) [C8 c0; C4 (Z_to_bv 64 (bd_bits d4 - nb * 8)); CB 4 jp;
                                     C8 (Z_to_bv 64 (S0 + bd_ptr d4 - nb)); C8 (Z_to_bv 64 S0); C8 (Z_to_bv 64 (S0 + 8))] ->
      evtF bsegs RNG Q (SBI 0x985dc m4 r1 t0 t1 t2 (Z_to_bv 64 (S0 + bd_ptr d4 - nb)) a1 a2 a3 a4 a5 a6 a7
                         x22 x23 x24 x25 t3 t4 t5 t6).
  Proof.
    intros x22 x23 x24 x25 KE m4 db v1 d1 s1 d2 v2 d3 s2 d4 jp nb c0 r1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
      FP OK4 B4 BZ4 P8 NB FM4 BD4.
    pose proof (spaf_props SPV SP16) as (SPAB & SPA32). pose proof atop_range as ATR. unfold DEC_STACK in LO.
    pose proof (ablk_lin _ _ HS0) as HS0l.
    pose proof FM4 as (MW4 & WM4 & MI4 & STK4 & SRC4 & DSC). unfold DEC_STACK in MW4.
    pose proof OK4 as (O4c & O4b & O4p & O4p8 & O4z & _).
    assert (NB2 : 0 <= nb <= bd_ptr d4 /\ nb <= 8) by (destruct NB as [[? ->]|[? ->]]; Z.div_mod_to_equations; lia).
    assert (Q8 : bd_ptr d4 + 8 <= zlen bs)
      by (destruct (Z.ltb_spec (zlen bs) 8) as [L8|L8]; [specialize (O4z L8); lia | rewrite Z.max_r in O4p8 by lia; lia]).
    assert (RX0 : ov_read_bytes bsegs m4 (Z_to_bv 64 (S0 + bd_ptr d4 - nb)) 1
                  = Some [Z_to_bv 8 (Znth (bd_ptr d4 - nb) bs)]) by frd SRC4.
    assert (RX1 : ov_read_bytes bsegs m4 (Z_to_bv 64 (S0 + bd_ptr d4 - nb + 1)) 1
                  = Some [Z_to_bv 8 (Znth (bd_ptr d4 - nb + 1) bs)]) by frd SRC4.
    assert (RX2 : ov_read_bytes bsegs m4 (Z_to_bv 64 (S0 + bd_ptr d4 - nb + 2)) 1
                  = Some [Z_to_bv 8 (Znth (bd_ptr d4 - nb + 2) bs)]) by frd SRC4.
    assert (RX3 : ov_read_bytes bsegs m4 (Z_to_bv 64 (S0 + bd_ptr d4 - nb + 3)) 1
                  = Some [Z_to_bv 8 (Znth (bd_ptr d4 - nb + 3) bs)]) by frd SRC4.
    assert (RX4 : ov_read_bytes bsegs m4 (Z_to_bv 64 (S0 + bd_ptr d4 - nb + 4)) 1
                  = Some [Z_to_bv 8 (Znth (bd_ptr d4 - nb + 4) bs)]) by frd SRC4.
    assert (RX5 : ov_read_bytes bsegs m4 (Z_to_bv 64 (S0 + bd_ptr d4 - nb + 5)) 1
                  = Some [Z_to_bv 8 (Znth (bd_ptr d4 - nb + 5) bs)]) by frd SRC4.
    assert (RX6 : ov_read_bytes bsegs m4 (Z_to_bv 64 (S0 + bd_ptr d4 - nb + 6)) 1
                  = Some [Z_to_bv 8 (Znth (bd_ptr d4 - nb + 6) bs)]) by frd SRC4.
    assert (RX7 : ov_read_bytes bsegs m4 (Z_to_bv 64 (S0 + bd_ptr d4 - nb + 7)) 1
                  = Some [Z_to_bv 8 (Znth (bd_ptr d4 - nb + 7) bs)]) by frd SRC4.
    fwk_to 1636%Z.
    set (d5 := mkBD (le64v bs (bd_ptr d4 - nb)) (bd_bits d4 - nb * 8) (bd_ptr d4 - nb) false).
    assert (RL : exists st, reload_dstream bs d4 = Ok (st, d5))
      by (unfold reload_dstream, d5; replace (64 <? bd_bits d4) with false by (symmetry; apply Z.ltb_ge; lia);
          replace (8 <=? bd_ptr d4) with false by (symmetry; apply Z.leb_gt; lia);
          replace (bd_ptr d4 =? 0) with false by (symmetry; apply Z.eqb_neq; lia);
          rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8;
          destruct NB as [[N0 E]|[N0 E]]; rewrite E;
          [ replace (bd_ptr d4 - bd_bits d4 / 8 <? 0) with false by (symmetry; apply Z.ltb_ge; lia)
          | replace (bd_ptr d4 - bd_bits d4 / 8 <? 0) with true by (symmetry; apply Z.ltb_lt; lia) ];
          cbv beta iota zeta; rewrite readLE64_ok by lia; cbn [bind]; eexists; reflexivity).
    destruct RL as (st & RL).
    pose proof (RF_huf_fdw_pure.reload_facts2 bs d4 st d5 BY OK4 RL) as (OK5 & BB5 & _ & Z5 & _).
    destruct (Z5 B4) as [BZ5 OV5].
    pose proof (fun i => byte_Znth bs i BY) as BZ.
    eapply KE; [exact FP | exact RL | exact OV5 | exact OK5 | lia | exact BZ5 | repeat (split; [assumption |]); assumption | ].
    unfold bitdz_cellsA, d5; cbn [bd_cont bd_bits bd_ptr bd_zero].
    lazymatch goal with H : rw_cells bsegs ?mm (SP1 + 112) [C8 ?e0; _; CB 4 _; C8 ?e3; _; _]
                      |- rw_cells bsegs ?mm (SP1 + 112) _ =>
      replace e0 with (Z_to_bv 64 (le64v bs (bd_ptr d4 - nb))) in H
        by (f_equal; unfold le64v; rewrite le64_lbu_land by (apply BZ; lia); ring);
      replace e3 with (Z_to_bv 64 (S0 + (bd_ptr d4 - nb))) in H by (f_equal; ring);
      exact H end.
  Qed.

  (* [comment removed for export] *)
  Lemma fdA_p1040 : forall (x22 x23 x24 x25 : word), fdA_K1636 x22 x23 x24 x25 ->
    forall m3 db v1 d1 s1 d2 v2 d3 s2 d4 jp nb (r1 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      FDPRE db v1 d1 s1 d2 v2 d3 s2 d4 -> bitd_ok bs d4 -> bd_bits d4 <= 64 -> bd_zero d4 = false -> 0 < bd_ptr d4 < 8 ->
      ((0 <= bd_ptr d4 - bd_bits d4 / 8 /\ nb = bd_bits d4 / 8) \/ (bd_ptr d4 - bd_bits d4 / 8 < 0 /\ nb = bd_ptr d4)) ->
      FDMEM m3 v1 v2 -> rw_cells bsegs m3 (SP1 + 112) (bitdz_cellsA S0 d4 jp) ->
      evtF bsegs RNG Q (SBI 0x98570 m3 r1 t0 t1 t2 (Z_to_bv 64 1) (Z_to_bv 64 (bd_bits d4)) (Z_to_bv 64 (S0 + bd_ptr d4))
                         (Z_to_bv 64 nb) a4 a5 a6 a7 x22 x23 x24 x25 t3 t4 t5 t6).
  Proof.
    intros x22 x23 x24 x25 KE m3 db v1 d1 s1 d2 v2 d3 s2 d4 jp nb r1 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6
      FP OK4 B4 BZ4 P8 NB FM3 BD2.
    pose proof (spaf_props SPV SP16) as (SPAB & SPA32). pose proof atop_range as ATR. unfold DEC_STACK in LO.
    pose proof (ablk_lin _ _ HS0) as HS0l.
    pose proof FM3 as (MW3 & WM3 & MI3 & STK3 & SRC3 & DSC). unfold DEC_STACK in MW3.
    pose proof OK4 as (O4c & O4b & O4p & O4p8 & O4z & _).
    assert (NB2 : 0 <= nb <= bd_ptr d4 /\ nb <= 8) by (destruct NB as [[? ->]|[? ->]]; Z.div_mod_to_equations; lia).
    assert (AW : appW [(SP1 - 2240, SP1); (SP1 + 80, SP1 + 152)]) by fappW.
    assert (UBS : unpoisoned m3 S0 (S0 + zlen bs)) by (eapply unpoisoned_appW; [exact USRC | exact MW3 | fappW | lia | lia]).
    assert (KE0 : S0 + zlen bs <= KEND) by (unfold KEND; lia).
    destruct (fdA_sh0 m3 S0 (S0 + zlen bs) (S0 + bd_ptr d4 - nb) UBS ltac:(lia) ltac:(Z.div_mod_to_equations; lia) KE0)
      as (b1 & SS1 & SS1B & B1z).
    destruct (src_sh_cell m3 S0 (S0 + zlen bs) (S0 + bd_ptr d4 - nb + 7) UBS ltac:(lia) ltac:(lia) KE0)
      as (b2 & SS2 & SS2B & GB2).
    unfold ASHOFF in SS1, SS1B, SS2, SS2B.
    assert (KH : KHIGH + 4096 <= lo) by (unfold KHIGH; lia).
    assert (Q8 : bd_ptr d4 + 8 <= zlen bs)
      by (destruct (Z.ltb_spec (zlen bs) 8) as [L8|L8]; [specialize (O4z L8); lia | rewrite Z.max_r in O4p8 by lia; lia]).
    pose proof BD2 as BD3. unfold bitdz_cellsA in BD3. rewrite BZ4 in BD3. cbv iota in BD3.
    fwk. rewrite sxb_sval, B1z. fwk. rewrite sxb_sval.
    destruct GB2 as [G2|G2];
      [ (* [comment removed for export] *)
        rewrite G2; fwk
      | (* [comment removed for export] *)
        fwk;
        lazymatch goal with |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
          replace c with false; [cbv iota; fwk |
            symmetry; apply negb_false_iff; unfold bv_lts; rewrite land7_mod; pose proof (sval_range b2) as SR2;
            rewrite (signed_lit_small64 (sval b2)) by lia;
            rewrite signed_lit_small64
              by (lazymatch goal with |- context [?x mod 8] => pose proof (Z.mod_pos_bound x 8) end; lia);
            apply Z.ltb_lt; lia] end].
    all: lazymatch goal with H : rw_cells bsegs ?mm (SP1 + 112) [C8 _; C4 ?c1; CB 4 _; _; _; _]
                         |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      replace c1 with (Z_to_bv 64 (bd_bits d4 - nb * 8)) in H
        by (f_equal; rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 3) with 8;
            lazymatch goal with |- context [Z.land ?x ?M] =>
              replace (Z.land x M) with x
                by (symmetry; first [change M with (Z.ones 64) | change M with (Z.ones 32)];
                    rewrite Z.land_ones by lia; apply Z.mod_small; Z.div_mod_to_equations; lia) end;
            rewrite swrap32_small by lia; ring) end.
    all: eapply (fdA_p1148 x22 x23 x24 x25 KE);
      [exact FP | exact OK4 | exact B4 | exact BZ4 | exact P8 | exact NB | repeat (split; [assumption |]); assumption
      | eassumption].
  Qed.

  (* [comment removed for export] *)
  Lemma fdA_partial : forall (x22 x23 x24 x25 : word), fdA_K1636 x22 x23 x24 x25 -> fdA_K992 x22 x23 x24 x25.
  Proof.
    intros x22 x23 x24 x25 KE m3 db v1 d1 s1 d2 v2 d3 s2 d4 jp r1 t0 t1 t2 a3 a5 a6 a7 t3 t4 t5 t6
      FP OK4 B4 BZ4 P8 FM3 BD2.
    pose proof (spaf_props SPV SP16) as (SPAB & SPA32). pose proof atop_range as ATR. unfold DEC_STACK in LO.
    pose proof (ablk_lin _ _ HS0) as HS0l.
    pose proof FM3 as (MW3 & WM3 & MI3 & STK3 & SRC3 & DSC). unfold DEC_STACK in MW3.
    pose proof OK4 as (O4c & O4b & O4p & O4p8 & O4z & _).
    assert (Q8 : 8 <= zlen bs) by (destruct (Z.ltb_spec (zlen bs) 8) as [L8|L8]; [specialize (O4z L8); lia | lia]).
    assert (AW : appW [(SP1 - 2240, SP1); (SP1 + 80, SP1 + 152)]) by fappW.
    pose proof BD2 as BD3. unfold bitdz_cellsA in BD3. rewrite BZ4 in BD3. cbv iota in BD3.
    zstep.
    assert (WB : bv_wrap 32 (bd_bits d4) = bd_bits d4) by (unfold bv_wrap, bv_modulus; cbn [Z.of_N]; apply Z.mod_small; lia).
    assert (SB : bv_swrap 32 (bd_bits d4 ≫ 3) = bd_bits d4 / 8)
      by (rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; apply swrap32_small; Z.div_mod_to_equations; lia).
    rewrite ?WB, ?SB.
    fwk.
    destruct (Z.ltb_spec (bd_ptr d4 - bd_bits d4 / 8) 0) as [N0|N0].
    - fbr false. zstep.
      eapply (fdA_p1040 x22 x23 x24 x25 KE);
        [exact FP | exact OK4 | exact B4 | exact BZ4 | exact P8 | right; split; [exact N0 | lia] | exact FM3 | exact BD2].
    - fbr true.
      eapply (fdA_p1040 x22 x23 x24 x25 KE);
        [exact FP | exact OK4 | exact B4 | exact BZ4 | exact P8 | left; split; [exact N0 | lia] | exact FM3 | exact BD2].
  Qed.

End FDEC.

End CANSEC1.
