(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdDCtx ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Image.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit FseWalkMem MemRange ZdCellKit ZdWalkKit ZdTbl ZdSeqBuildW.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_globals AZ_globalsR AZ_blk_iface AZ_blk_iface6 AZ_kx.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac kxa_norm ::= unfold shspan in *.

(* [comment removed for export] *)
Lemma st_log_read : forall tt, 0 <= st_log tt <= 8 ->
  extz true 4 (bytes_le_to_Z (firstn 4 (skipn (Z.to_nat 4) (map (Z_to_bv 8) (seq_table_bytes tt))))) = st_log tt.
Proof.
  intros tt Htt. unfold seq_table_bytes. rewrite !map_app. unfold zle4. change (Z.to_nat 4) with 4%nat. cbn [map app skipn firstn].
  rewrite bytes_le_to_Z_le_val. cbn [map le_val]. rewrite !byte_lit by (Z.div_mod_to_equations; lia).
  unfold extz. cbv iota. cbn [firstn map le_val]. rewrite Z.mul_0_r, Z.add_0_r.
  rewrite !Z.mod_small by (Z.div_mod_to_equations; lia).
  rewrite (Z.div_small _ 256), (Z.div_small _ 65536), (Z.div_small _ 16777216) by lia.
  change (8 * N.of_nat 4)%N with 32%N.
  replace (st_log tt + 256 * (0 + 256 * (0 + 256 * 0))) with (st_log tt) by lia.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with 4294967296. change (2 ^ Z.of_N (32 - 1)) with 2147483648.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma tl_pow_range : forall tl, 0 <= tl <= 8 -> 1 <= 2^tl <= 256.
Proof. intros tl H. split; [apply (Z.pow_le_mono_r 2 0 tl); lia | change 256 with (2^8); apply Z.pow_le_mono_r; lia]. Qed.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Definition zd_offinfo_stmtA2 : Prop :=
  forall (RNG : footprint) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (SPV OFT : Z) (t : seq_table) (lo : Z),
  seq_tbl_at bsegs m K_OF OFT t -> 4096 <= OFT -> OFT + 2056 < 2^47 -> 0 <= SPV < 2^64 -> stk bsegs m lo SPV -> lo <= SPV - 16 -> SPV < 2^47 ->
  off_stack lo SPV OFT (8 * (1 + 2 ^ st_log t)) ->
  (* [comment removed for export] *)
  aro RNG m OFT (8 * (1 + 2 ^ st_log t)) -> art m -> astk RNG lo SPV ->
  OFT mod 4 = 0 ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 OFT ->
  evtF bsegs RNG (zd_offinfo_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV lo m)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 APZD_OFFINFO) fc None m (seg_rom bsegs)).

Section OI.
  Variables (RNG : footprint) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m m1 : amem) (SPV OFT tl lo : Z) (t : seq_table) (junk8 : list byte).
  Hypothesis TB : bytes_at bsegs m1 OFT (map (Z_to_bv 8) (seq_table_bytes t)).
  Hypothesis TLEN : Z.of_nat (length (map (Z_to_bv 8) (seq_table_bytes t))) = 8 * (1 + 2 ^ tl).
  Hypothesis TOK : seq_table_ok K_OF t.
  Hypothesis TLE : tl = st_log t.
  Hypothesis TLR : 0 <= tl <= 8.
  Hypothesis OL : 4096 <= OFT.
  Hypothesis OH : OFT + 2056 < 2^47.
  Hypothesis SPR : 0 <= SPV < 2^64.
  Hypothesis SPV47 : SPV < 2^47.
  Hypothesis LOS : lo <= SPV + -16.
  Hypothesis KLO : 17594333495296 <= lo.
  Hypothesis OFS : OFT + 8 * (1 + 2 ^ tl) <= lo \/ SPV <= OFT.
  Hypothesis UO1 : unpoisoned m1 OFT (OFT + 8 * (1 + 2 ^ tl)).
  Hypothesis RO : rng RNG OFT (8 * (1 + 2 ^ tl)).
  Hypothesis RSO : rng RNG (shad OFT) (shspan OFT (8 * (1 + 2 ^ tl))).
  Hypothesis RSTK : rng RNG lo (SPV - lo).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis FR : rw_cells bsegs m1 (SPV + -16) [CB 8 junk8; C8 ra].
  Hypothesis STK : stk bsegs m1 lo (SPV + -16).
  Hypothesis MU : munch [(SPV + -16, SPV)] m m1.
  Hypothesis WM : wmono bsegs m m1.
  Hypothesis MI1 : mem_inv bsegs m1.

  Notation POST := (zd_offinfo_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV lo m).
  (* [comment removed for export] *)
  Notation ST pc xt0 x6 x7 xa0 xa1 xa3 xa6 xa7 x28 x29 x30 x31 :=
    (MS (mkR ra (Z_to_bv 64 (SPV + -16)) gp tp xt0 x6 x7 s0 s1 xa0 xa1 (Z_to_bv 64 2147450880) xa3 (Z_to_bv 64 tl) (Z_to_bv 64 (OFT + 10)) xa6 xa7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None m1 (seg_rom bsegs)).

  (* [comment removed for export] *)
  Lemma oi_exitA : forall xt0 x6 x7 xa0 xa1 xa3 xa6 xa7 x28 x29 x30 x31,
    evtF bsegs RNG POST (ST 0x89928 xt0 x6 x7 xa0 xa1 xa3 xa6 xa7 x28 x29 x30 x31).
  Proof.
    intros.
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    kx_autoFLAx [KAApp (SPV - 16) 16] [] 30%nat
      [KZRange SPV 0x10007fff8000 (2^47); KZRange tl 0 8; KZWr (SPV - 16) 16]
      [(SPV - 16, 16)] [(SPV - 16, 16)].
    all: try kx_z. all: try kx_acc RI.
    all: kx_mem.
    all: kx_abs.
    all: zstep.
    all: lazymatch goal with FRc : rw_cells _ ?mc (?S + -16) [_; C8 _], STc : stk _ ?mc ?l (?S + -16) |- _ => release_frame FRc STc S end.
    all: lazymatch goal with |- context [MS _ _ _ _ _ ?mc _] => apply evtF_done; unfold zd_offinfo_postA; do 15 eexists; exists mc end.
    all: split; [reflexivity|].
    all: split; [eassumption|]. all: split; [eassumption|]. all: split; [eassumption|]. all: assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma oi_tailA : forall u b xt0 x6 x7 xa1 xa3 xa7 x28 x29 x30 x31,
    0 <= u < 2^tl -> 0 <= b < 256 ->
    (u + 1 < 2^tl -> forall xt0 x6 x7 xa0 xa1 xa3 xa7 x28 x29 x30 x31,
       evtF bsegs RNG POST (ST 0x898ec xt0 x6 x7 xa0 xa1 xa3 (Z_to_bv 64 (u + 1 + 1)) xa7 x28 x29 x30 x31)) ->
    evtF bsegs RNG POST (ST 0x898d4 xt0 x6 x7 (Z_to_bv 64 b) xa1 xa3 (Z_to_bv 64 (u + 1)) xa7 x28 x29 x30 x31).
  Proof.
    intros until x31. intros UR BR KONT.
    pose proof (tl_pow_range tl TLR) as P8.
    zstep. zstep. zstep. zstep. zstep.
    assert (EX : bv_swrap 32 (bv_wrap 32 (u + 1) ≫ (tl mod 32)) = if u + 1 =? 2^tl then 1 else 0).
    { replace (bv_wrap 32 (u + 1)) with (u + 1) by (unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 32) with 4294967296; rewrite Z.mod_small by lia; reflexivity).
      rewrite (Z.mod_small tl 32) by lia. rewrite Z.shiftr_div_pow2 by lia.
      destruct (Z.eqb_spec (u + 1) (2^tl)) as [E|NE].
      - rewrite E, Z.div_same by lia. reflexivity.
      - rewrite Z.div_small by lia. reflexivity. }
    rewrite EX. clear EX.
    destruct (Z.eqb_spec (u + 1) (2^tl)) as [E|NE].
    - zstep. kx_mkR_fold. apply oi_exitA.
    - zstep. kx_mkR_fold.
      replace (u + 2) with (u + 1 + 1) by lia. apply KONT. lia.
  Qed.

  (* [comment removed for export] *)
  Definition oi_held (P : Prop) : Prop := P.

  Lemma oi_loopA : forall (n : nat) u xt0 x6 x7 xa0 xa1 xa3 xa7 x28 x29 x30 x31,
    Z.of_nat n = 2^tl - u -> 0 <= u < 2^tl ->
    evtF bsegs RNG POST (ST 0x898ec xt0 x6 x7 xa0 xa1 xa3 (Z_to_bv 64 (u + 1)) xa7 x28 x29 x30 x31).
  Proof.
    induction n as [|n IH]; intros until x31; intros EN UR; [lia|].
    pose proof (tl_pow_range tl TLR) as P8.
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    assert (KONT : u + 1 < 2^tl -> forall xt0 x6 x7 xa0 xa1 xa3 xa7 x28 x29 x30 x31,
              evtF bsegs RNG POST (ST 0x898ec xt0 x6 x7 xa0 xa1 xa3 (Z_to_bv 64 (u + 1 + 1)) xa7 x28 x29 x30 x31)).
    { intros LT. intros. apply IH; lia. }
    clear IH.
    remember (2 ^ tl) as p eqn:PE. change (oi_held (p = 2 ^ tl)) in PE.
    kx_autoFLAx [KAUnp (OFT + 8 + 8 * u) 8] [0x898d4] 40%nat
      [KZRange SPV 0x10007fff8000 (2^47); KZRange u 0 255; KZRange OFT 4096 (2^47 - 2056)]
      [(OFT + 8 + 8 * u, 8)] [(OFT + 8 + 8 * u, 8)].
    all: try kx_cell_lit. all: try kx_z. all: try kx_acc RI.
    all: kx_read_ranges.
    all: kx_mem.
    all: kx_abs.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (ev ?E ?j) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
         pose proof (bv_unsigned_in_range 64 (ev E j)) as BR;
         rewrite <- (Z_to_bv_bv_unsigned (ev E j));
         set (bb := bv_unsigned (ev E j)) in *; clearbody bb
     end.
    all: unfold oi_held in PE; subst p.
    all: eapply oi_tailA; [exact UR | | exact KONT].
    all: lazymatch goal with H : 0 <= ?x <= 255 |- 0 <= ?x < 256 => clear - H; lia end.
Qed.
End OI.

Lemma zd_offinfo_proofA2 : zd_offinfo_stmtA2.
Proof.
  intros RNG ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SPV OFT t lo.
  intros TAT OL OH SPR ST LOS SPV47 OFS ARO ART AST OM4 MI ->.
  destruct TAT as (TB & TOK).
  destruct (seq_tbl_len K_OF t TOK) as (TLEN & TLR). cbn [kind_maxLog] in TLR.
  destruct ART as (GOT & RIC & SHB & INI & LAY & REAL).
  destruct AST as (KLO & RSTK & RI). unfold KHIGH in KLO.
  destruct ARO as (UO & RO & RSO).
  unfold off_stack in OFS.
  remember (st_log t) as tl eqn:TLE.
  assert (P8 : 1 <= 2^tl <= 256) by (split; [apply (Z.pow_le_mono_r 2 0 tl); lia | change 256 with (2^8); apply Z.pow_le_mono_r; lia]).
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  assert (MU : munch [(SPV - 16, SPV)] m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  carve_frame 16%nat ST.
  unfold APZD_OFFINFO.
  (* [comment removed for export] *)
  kx_autoFLAx [KAUnp OFT (8 + 8 * 2^tl); KAApp (SPV - 16) 16] [0x898ec] 80%nat
    [KZRange SPV 0x10007fff8000 (2^47); KZRange OFT 4096 (2^47 - 2056); KZAlign OFT 4; KZRange tl 0 8; KZRange (2^tl) 1 256;
     KZWr (SPV - 16) 16; KZDisj (SPV - 16) 16 OFT (8 + 8 * 2^tl)]
    [(SPV - 16, 16); (OFT, 8 + 8 * 2^tl)] [(SPV - 16, 16); (OFT, 8 + 8 * 2^tl)].
  all: try kx_cell_lit. all: try kx_z. all: try kx_acc RI.
  (* [comment removed for export] *)
  all: lazymatch goal with
       | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 563548) _ _ _ _) => idtac
       | |- _ => kx_read_eq 34%nat RD4;
                 rewrite (rdval_bytes_at bsegs m OFT _ 4 4 true TB ltac:(lia)
                   ltac:(rewrite length_map; pose proof (seq_table_bytes_length t); unfold FseNCount.Zlength in *; lia)) in RD4;
                 rewrite (st_log_read t), <- TLE in RD4 by lia
       end.
  all: try (rewrite RD4; clear RD4).
  all: kx_mem.
  { (* [comment removed for export] *)
    zstep. release_frame FR ST SPV.
    apply evtF_done. unfold zd_offinfo_postA. do 15 eexists. exists m0.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact KXMI|]. exact ST. }
  clear KXA KXRD KXK KXE.
  assert (UO1 : unpoisoned m0 OFT (OFT + 8 * (1 + 2 ^ tl))).
  { eapply unpoisoned_munch; [exact UO | exact MU | cbn [disjoint_from]; rewrite !shad_div; unfold ASHOFF;
      repeat split; Z.div_mod_to_equations; lia]. }
  replace (Z_to_bv 64 1) with (Z_to_bv 64 (0 + 1)) by reflexivity.
  eapply (oi_loopA RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m0 SPV OFT tl lo t) with (n := Z.to_nat (2^tl));
    try eassumption; try lia.
Qed.

(* [comment removed for export] *)
Theorem zd_offinfo_proofA : zd_offinfo_stmtA.
Proof. exact zd_offinfo_proofA2. Qed.

End CANSEC1.
