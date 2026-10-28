(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit ZdFrameW.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXGoF KXAsan KXAutoA.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_frame_iface AZ_kx.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Local Ltac rdb3 B3 :=
  lazymatch goal with
  | |- _ /\ _ /\ _ /\ rdn ?segs ?m (wa ?a) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 ?v)) =>
      split; [lia|]; split; [lia|]; split; [lia|];
      lazymatch type of B3 with bytes_at _ _ ?X _ =>
      first [ replace (wa a) with (wa (X + Z.of_nat 0)) by (f_equal; lia)
            | replace (wa a) with (wa (X + Z.of_nat 1)) by (f_equal; lia)
            | replace (wa a) with (wa (X + Z.of_nat 2)) by (f_equal; lia) ];
      rewrite (bytes_at_rdn segs m X _ _ 1 B3) by (cbn; lia); cbn [skipn firstn word_to_le_bytes Z_to_le_bytes];
      do 2 f_equal; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn; rewrite Z.mod_small by lia; reflexivity
      end
  end.
Local Ltac rdb3_any :=
  lazymatch goal with |- _ /\ _ /\ _ /\ rdn _ ?m _ _ = _ => match goal with B : bytes_at _ m _ [_; _; _] |- _ => rdb3 B end end.

Local Ltac gcb_close K RI RSS RBS :=
  try kx_cell_lit; try rdb3_any; try kx_z; try kx_acc RI; try kx_sh_acc RSS; try kx_sh_acc RBS; try kx_sh_rd_any;
  try (kx_sh_dead_any K).

Section CANSEC1. Context {rc : runConstT}.

Ltac kxa_norm ::= unfold shspan in *.

Lemma zd_getcblock_proofA : zd_getcblock_stmtA.
Proof.
  intros RNG ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SPV SRC BP src ip size cs0 lo.
  intros SB OK IP0 SZ0 IPS SRC0 BPC BPSZ BP0 BP4 ST LOS SPV47 SEPB SEPS ARS ARB ART AST MI -> -> ->.
  destruct ART as (GOT & RIC & SHB & INI & LAY & REAL).
  destruct AST as (KLO & RSTK & RI). unfold KHIGH in KLO.
  pose proof (bytes_at_bound _ _ _ _ SB) as DB. rewrite length_map in DB.
  destruct (rw_cells_forget _ _ _ _ BPC) as [junk BPC1]. rewrite BPSZ in BPC1. clear BPC.
  assert (MU : munch [(BP, BP + 12); (SPV - 16, SPV)] m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  carve_frame 16%nat ST.
  unfold APZD_GETCBLOCK.
  destruct (Z_lt_le_dec size 3) as [S3|S3].
  - (* [comment removed for export] *)
    clear ARS ARB.
    kx_autoFLx [] 30%nat [KZRange SPV 4096 (2^47); KZRange size 0 2; KZWr (SPV - 16) 16]
      [(SPV - 16, 16)] [(SPV - 16, 16)].
    all: try kx_cell_lit.
    kx_mem. zstep.
    release_frame FR ST SPV.
    assert (RES : get_cblock_size src ip size = None).
    { unfold get_cblock_size, ZD_blockHeaderSize. replace (size <? 3) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
    replace (Z_to_bv 64 18446744073709551544) with (Z_to_bv 64 (cblock_ret (get_cblock_size src ip size)))
      by (rewrite RES; apply Z_to_bv_eqm; reflexivity).
    apply evtF_done. unfold zd_getcblock_postA. do 14 eexists. exists m0, [CB 12 junk].
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact KXMI|]. split; [exact ST|]. split; [exact BPC1|].
    split; [reflexivity|].
    intros v bp E. rewrite RES in E. discriminate E.
  - (* [comment removed for export] *)
    assert (ZS : 0 < zlen src) by lia.
    destruct (ARS ZS) as (ABS & US & RS & RSS). destruct (ARB ltac:(lia)) as (ABB & UB & RB & RBS). clear ARS ARB.
    pose proof (OK ip) as OK0. pose proof (OK (ip + 1)) as OK1. pose proof (OK (ip + 2)) as OK2.
    assert (B3 : bytes_at bsegs m (SRC + ip) [Z_to_bv 8 (Znth ip src); Z_to_bv 8 (Znth (ip + 1) src); Z_to_bv 8 (Znth (ip + 2) src)]).
    { destruct SB as (H0 & H1 & H). rewrite length_map in H1. split; [lia|]. split; [cbn; lia|].
      intros i Hi. cbn [length] in Hi.
      replace (SRC + ip + Z.of_nat i) with (SRC + Z.of_nat (Z.to_nat ip + i)) by lia.
      rewrite H by (rewrite length_map; lia). rewrite nth_error_map.
      destruct i as [|[|[|i]]]; [| | | lia]; cbn [nth_error];
        rewrite (nth_error_nth' src 0) by lia; cbn [option_map]; unfold Znth; repeat f_equal; lia. }
    remember (SRC + ip) as X eqn:XE.
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    assert (BPR : 4096 <= BP /\ BP + 12 < 2^47) by (unfold ablk, AIMG_HI, KLS in ABB; lia).
    assert (XR : 4096 <= X /\ X + 3 <= SRC + zlen src /\ SRC + zlen src < 2^47) by (unfold ablk, AIMG_HI, KLS in ABS; lia).
    assert (BPA : BP + 12 <= 0x7fff7000 \/ 0x10007fff8000 <= BP) by (unfold ablk, AIMG_HI, KLS in ABB; lia).
    assert (SA : SRC + zlen src <= 0x7fff7000 \/ 0x10007fff8000 <= SRC) by (unfold ablk, AIMG_HI, KLS in ABS; lia).
    clear SB.
    (* [comment removed for export] *)
    Time kx_autoFLAx [KAUnp X 3; KAUnp BP 12; KAApp BP 12; KAApp (SPV - 16) 16] [] 120%nat
      [KZRange SPV 4096 (2^47); KZRange X 4096 (2^47 - 3); KZRange size 3 (2^47); KZRange BP 4096 (2^47 - 12);
       KZAlign BP 4;
       KZWr BP 12; KZWr (SPV - 16) 16; KZDisj (SPV - 16) 16 BP 12;
       KZWord X 1 (Znth ip src); KZWord (X + 1) 1 (Znth (ip + 1) src); KZWord (X + 2) 1 (Znth (ip + 2) src);
       KZRange (Znth ip src) 0 255; KZRange (Znth (ip + 1) src) 0 255; KZRange (Znth (ip + 2) src) 0 255]
      [(SPV - 16, 16); (BP, 12)] [(SPV - 16, 16); (BP, 12); (X, 3)].
    all: gcb_close 4 RI RSS RBS.
    all: kx_mem.
    all: set (bp := cblock_props (le24 src ip)) in *.
    all: assert (BTE : (2305843009213693952 * Znth ip src) mod 2 ^ 64 / 4611686018427387904 = bp_type bp)
           by (subst bp; unfold cblock_props, bp_type, le24; Z.div_mod_to_equations; lia).
    all: assert (CSE : (Znth ip src + (256 * Znth (ip + 1) src + 65536 * Znth (ip + 2) src)) mod 2 ^ 64 / 8 = bp_orig bp)
           by (subst bp; unfold cblock_props, bp_orig, le24; Z.div_mod_to_equations; lia).
    all: assert (LSE : Z.land (Znth ip src mod 2 ^ 64) 1 = bp_last bp)
           by (subst bp; unfold cblock_props, bp_last, le24; change 1 with (Z.ones 1); rewrite Z.land_ones by lia;
               Z.div_mod_to_equations; lia).
    all: assert (RES : get_cblock_size src ip size =
                  Some (if bp_type bp =? bt_rle then 1 else if bp_type bp =? bt_reserved then ZERR ZE_corruption_detected else bp_orig bp, bp))
           by (unfold get_cblock_size, ZD_blockHeaderSize; replace (size <? 3) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
    all: rewrite ?BTE, ?CSE, ?LSE in *.
    all: zstep.
    all: lazymatch goal with FRc : rw_cells _ ?mc (?S + -16) [_; C8 _], STc : stk _ ?mc ?l (?S + -16) |- _ => release_frame FRc STc S end.
    all: kx_mkR_fold.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ ?A0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
             replace A0 with (Z_to_bv 64 (cblock_ret (get_cblock_size src ip size)))
               by (rewrite RES; cbn [cblock_ret]; unfold bt_rle, bt_reserved;
                   destruct (Z.eqb_spec (bp_type bp) 1); destruct (Z.eqb_spec (bp_type bp) 3); try lia;
                   first [ f_equal; lia | apply Z_to_bv_eqm; unfold ZERR, ZE_corruption_detected; reflexivity | reflexivity ])
         end.
    all: apply evtF_done; unfold zd_getcblock_postA; do 14 eexists;
         lazymatch goal with |- context [MS _ _ _ _ _ ?mc _] => lazymatch goal with BPc : rw_cells _ mc _ [C4 _; C4 _; C4 _] |- _ =>
           lazymatch type of BPc with rw_cells _ _ _ ?cs => exists mc, cs end end end.
    all: split; [reflexivity|].
    all: split; [eassumption|]. all: split; [eassumption|]. all: split; [eassumption|]. all: split; [eassumption|].
    all: split; [eassumption|]. all: split; [reflexivity|].
    all: intros v bp' E; rewrite RES in E; injection E as _ <-; unfold bp_cells; rewrite ?LSE; reflexivity.
Qed.
End CANSEC1.
