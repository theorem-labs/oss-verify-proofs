(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.P Require Import Str_tac Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface RT_iface2 D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_akit Sj_acps Sj_hkit Atp_fzwA Atp_defsA Atp_objwA Atp_objnA Pj_defsA El_defsA Dmp_hdefsA Dmp_pj_ifaceA Dmp_pj_kitA Dmp_pj_leafA.
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

Definition DMP_PJ_SCALL_A : Z := 0xafee0.
Definition DMP_PJ_SRET_A : Z := 0xaf0f0.
Definition DMP_PJ_SPUT_A : Z := 0xaf100.

Ltac pj_gt2 := let G := fresh "G" in if_cases G; zify_cond G;
  [|exfalso; rewrite ?unsigned_lit in G by lia; rewrite ?land7_mod in G by lia; lia]; try clear G.
Ltac pj_tyw := match goal with H : _ / 72057594037927936 = _ |- _ => progress rewrite H end.
Ltac pj_walk stop := repeat (tryif pj_at stop then fail else
  first [ls | if_false | if_true | zstep | (rewrite shr3_div; ls) | (shz_norm; ls) | pj_gt | pj_gt2
        | (progress rewrite ?Z.shiftr_div_pow2 by lia) | pj_tyw]).

Lemma pj_str1 : forall (E : aenvA) (q f osp i : Z) (j80 : list byte) (gp ra a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 : word) F fc (m : mem),
  aenvA_ok E -> 0 <= i < ae_n E -> 0 <= ae_T E i < 2^64 -> ttype (ae_T E i) = 34 ->
  0x6d5000 <= q - 256 -> q < 2^63 ->
  AINV_A E m -> shz m (ae_TAPE E) (8 * ae_n E) -> rw_cells bsegs m (q - 256 + 80) [CB 8 j80; C8 (Z_to_bv 64 osp)] -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m' : mem),
      ms = MS (pjR q f gp (Z_to_bv 64 DMP_PJ_SRET_A) (Z_to_bv 64 (q - 256 + 112)) (Z_to_bv 64 (q - 256 + 136)) a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 (ae_DOC E)) (Z_to_bv 64 i) s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6)
              F (Z_to_bv 64 DMP_PJ_SCALL_A) fc None m' (seg_rom bsegs)
      /\ munch [(q - 256 + 80, q - 256 + 88)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ rw_cells bsegs m' (q - 256 + 80) [C8 (Z_to_bv 64 SHB); C8 (Z_to_bv 64 osp)])
    (MS (pjR q f gp ra (Z_to_bv 64 (ae_TAPE E + 8 * i)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (ae_DOC E)) (Z_to_bv 64 i) s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6)
        F (Z_to_bv 64 DMP_PJ_DISP_A) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros OK IR TR TY QLO QH AI SHZT FR MI.
  pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L (T16 & NT8 & TN & TS & TL) (S16 & NS8 & SN & SS & SL) _ _ (D8 & DF & DL & DS & DT) LOW [HL HT]].
  unfold USTACK_TOP in HT. unfold SEGTOP_A in *.
  pose proof AI as (TAPEB & SBUFB & _ & DOCC & DSH).
  assert (FS0 : 0 <= fs_size (ae_kD E)) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
  assert (EI : bv_unsigned (Z_to_bv 64 i) = i) by (apply unsigned_lit; lia).
  assert (ESP : bv_unsigned (Z_to_bv 64 (q - 256)) = q - 256) by (apply unsigned_lit; lia).
  assert (ETI : bv_unsigned (Z_to_bv 64 (ae_TAPE E + 8 * i)) = ae_TAPE E + 8 * i) by (apply unsigned_lit; lia).
  unfold ttype in TY. pose proof TY as TY2. change (2^56) with 72057594037927936 in TY2.
  unfold pjR, DMP_PJ_DISP_A, DMP_PJ_SCALL_A, DMP_PJ_SRET_A.
  pose proof (tape_read _ (ae_TAPE E) (ae_tws E) i TAPEB ltac:(lia)) as RDT.
  pose proof (munch_refl [(q - 256 + 80, q - 256 + 88)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  chk0 SHZT (ae_TAPE E + 8 * i).
  pj_walk 0xafee0.
  apply evt_done. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. assumption.
Qed.

Lemma pj_str2 : forall (q f osp p l : Z) (gp ra a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 : word) F fc (m : mem),
  0x6d5000 <= q - 256 -> q < 2^63 ->
  rw_cells bsegs m (q - 256 + 88) [C8 (Z_to_bv 64 osp)] -> rw_cells bsegs m (q - 256 + 112) [C8 (Z_to_bv 64 p); C8 (Z_to_bv 64 l)] ->
  mem_inv bsegs m ->
  evt bsegs (fun ms =>
      ms = MS (pjR q f gp (Z_to_bv 64 DMP_PJ_SPUT_A) (Z_to_bv 64 osp) (Z_to_bv 64 p) (Z_to_bv 64 l) a3 a4 a5 a6 a7 s4 s5 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6)
              F (Z_to_bv 64 DMP_PJ_PUT_A) fc None m (seg_rom bsegs))
    (MS (pjR q f gp ra a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6) F (Z_to_bv 64 DMP_PJ_SRET_A) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros QLO QH FO FR MI.
  assert (ESP : bv_unsigned (Z_to_bv 64 (q - 256)) = q - 256) by (apply unsigned_lit; lia).
  unfold pjR, DMP_PJ_SRET_A, DMP_PJ_SPUT_A, DMP_PJ_PUT_A.
  pj_walk 0xb13cc.
  apply evt_done. reflexivity.
Qed.
