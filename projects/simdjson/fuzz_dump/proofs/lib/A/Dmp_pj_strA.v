(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.P Require Import Str_tac Sj_stage1_kit.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjTape SjTapeList.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.A Require Import Layout Shadow RT_iface RT_iface2 D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_akit Sj_acps Sj_hkit Atp_fzwA
     Atp_defsA Atp_objwA Atp_objnA Pj_defsA El_defsA Dmp_hdefsA Dmp_pj_ifaceA Dmp_pj_kitA Dmp_pj_leafA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Lemma pj_low56 : forall w, 0 <= w < 2^64 -> Z.shiftr (Z.shiftl w 8 mod 18446744073709551616) 8 = tval w.
Proof.
  intros w W. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. unfold tval.
  change 18446744073709551616 with (2^56 * 2^8). rewrite Z.mul_mod_distr_r by lia. rewrite Z.div_mul by lia. reflexivity.
Qed.

Lemma pj_land56 : forall w, 0 <= w -> Z.land w 72057594037927935 = tval w.
Proof. intros w W. change 72057594037927935 with (Z.ones 56). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma pj_str1 : forall (E : aenvA) (q f osp i o l : Z) (gp ra a0 a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 : word) F fc (m : mem),
  aenvA_ok E -> 0 <= i < ae_n E -> 0 <= ae_T E i < 2^64 -> ttype (ae_T E i) = 34 -> tval (ae_T E i) = o -> str_at (ae_S E) (ae_sn E) o l ->
  0x6c9000 <= q - 256 -> q < 2^63 -> 0 <= osp < 2^64 ->
  AINV_A E m -> shz m (ae_TAPE E) (8 * ae_n E) -> shz m (ae_SBUF E) (ae_NS E) ->
  rw_cells asegs m (q - 256 + 120) [C8 (Z_to_bv 64 osp)] -> mem_inv asegs m ->
  evt asegs (fun ms => exists (a3x a4x : word),
      ms = MS (pjR q f gp (Z_to_bv 64 (pj_endl_pc 3)) (Z_to_bv 64 osp) (Z_to_bv 64 (ae_SBUF E + o + 4)) (Z_to_bv 64 l) a3x a4x a5 a6 a7
                   (Z_to_bv 64 (ae_DOC E)) (Z_to_bv 64 i) (Z_to_bv 64 (8 * i)) s8 s9 s11 t0 t1 t2 t3 t4 t5 t6)
              F (Z_to_bv 64 DMP_PJ_PUT_A) fc None m (seg_rom asegs))
    (MS (pjR q f gp ra a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (ae_DOC E)) (Z_to_bv 64 i) s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6)
        F (Z_to_bv 64 DMP_PJ_DISP_A) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros OK IR TR TY TV SA QLO QH OR AI SHZT SHZS FO MI.
  pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L (T16 & NT8 & TN & TS & TL) (S16 & NS8 & SN & SS & SL) _ _ (D8 & DF & DL & DS & DT) LOW [HL HT]].
  unfold USTACK_TOP in HT. unfold SEGTOP_A in *. assert (HSN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia).
  pose proof (str_at_bounds _ _ HSN _ _ SA) as (O0 & L0 & OL & LE & O56).
  pose proof AI as (TAPEB & SBUFB & _ & DOCC & DSH).
  assert (FS0 : 0 <= fs_size (ae_kD E)) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
  assert (ED : bv_unsigned (Z_to_bv 64 (ae_DOC E)) = ae_DOC E) by (apply unsigned_lit; lia).
  assert (EI : bv_unsigned (Z_to_bv 64 i) = i) by (apply unsigned_lit; lia).
  assert (ESP : bv_unsigned (Z_to_bv 64 (q - 256)) = q - 256) by (apply unsigned_lit; lia).
  unfold pjR, DMP_PJ_DISP_A, DMP_PJ_PUT_A. cbn [pj_endl_pc].
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (tape_read _ (ae_TAPE E) (ae_tws E) i TAPEB ltac:(lia)) as RDT.

  pose proof (proj2 (proj1 (rw_cells_app asegs m (ae_DOC E) [_] [_]) DOCC)) as DOC2. cbn [cells_size csize Nat.add] in DOC2.
  replace (ae_DOC E + Z.of_nat 8) with (ae_DOC E + 8) in DOC2 by lia.
  pose proof (shz_of_zero_run m (ae_DOC E) 2 D8 ltac:(lia) DSH) as SHZD. change (8 * Z.of_nat 2) with 16 in SHZD.

  zstep. astep. astep.
  chk0 SHZT (ae_TAPE E + 8 * i). step. if_false.
  step. astep. first [change (ae_T E i / 2 ^ 56) with (ttype (ae_T E i)) | idtac]. rewrite TY.

  step. step. if_true. step. step. if_true. step. step. if_false. step. step. if_true.

  astep. first [change (ae_T E i / 2 ^ 56) with (ttype (ae_T E i)) | idtac]. rewrite TY. step. if_false.
  zstep. chk0 SHZD (ae_DOC E + 8). step. if_false. zstep.

  zstep. zstep. rewrite ?(pj_low56 (ae_T E i)), ?(pj_land56 (ae_T E i)) by lia. rewrite !TV.
  astep.

  chk0 SHZS (ae_SBUF E + o). step. if_false. astep. chk0 SHZS (ae_SBUF E + o + 3). step. if_false.
  pose proof (sbuf_read1 m (ae_SBUF E) (ae_sbs E) o SBUFB ltac:(lia)) as RB0.
  pose proof (sbuf_read1 m (ae_SBUF E) (ae_sbs E) (o + 1) SBUFB ltac:(lia)) as RB1.
  pose proof (sbuf_read1 m (ae_SBUF E) (ae_sbs E) (o + 2) SBUFB ltac:(lia)) as RB2.
  pose proof (sbuf_read1 m (ae_SBUF E) (ae_sbs E) (o + 3) SBUFB ltac:(lia)) as RB3.
  pose proof (sbs_byteA E OK o ltac:(lia)) as Y0. pose proof (sbs_byteA E OK (o + 1) ltac:(lia)) as Y1.
  pose proof (sbs_byteA E OK (o + 2) ltac:(lia)) as Y2. pose proof (sbs_byteA E OK (o + 3) ltac:(lia)) as Y3.
  hide SBUFB. clear SHRD SHRD0 SHRD1 SHRD2.

  do 11 zstep.
  rewrite ?(a_u8_small (ae_S E o)), ?(a_u8_small (ae_S E (o + 1))), ?(a_u8_small (ae_S E (o + 2))), ?(a_u8_small (ae_S E (o + 3))) by (clear - Y0 Y1 Y2 Y3; lia).
  rewrite ?land64_mod. rewrite ?shl_mod_smallA by (clear - Y0 Y1 Y2 Y3; lia). rewrite le32_of_lbu4A by (clear - Y0 Y1 Y2 Y3; lia).
  change (ae_S E o + 2 ^ 8 * ae_S E (o + 1) + 2 ^ 16 * ae_S E (o + 2) + 2 ^ 24 * ae_S E (o + 3)) with (le32 (ae_S E) o). rewrite LE.
  clear RB0 RB1 RB2 RB3.

  zstep. zstep. zstep.
  apply evt_done. do 2 eexists. atp_st_eq_goal.
Qed.
