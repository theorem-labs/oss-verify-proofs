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
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjTape SjTapeList SjTapeTile.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.A Require Import Layout Shadow RT_iface RT_iface2 D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_akit Sj_acps Sj_hkit Atp_fzwA
     Atp_defsA Atp_objwA Atp_objnA Pj_defsA El_defsA Dmp_hdefsA Dmp_pj_ifaceA Dmp_pj_kitA Dmp_pj_leafA Dmp_pj_strA Dmp_pj_arrA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Ltac clear_shrd := repeat match goal with H : ov_read_bytes _ _ _ 1 = Some [Z_to_bv 8 0] |- _ => clear H end.

Definition DMP_LIT_RBRC_A : Z := 0x23580.   Definition DMP_LIT_QUOT_A : Z := 0x23540.   Definition DMP_LIT_QCOL_A : Z := 0x23560.
Definition DMP_PJ_OHEAD_A : Z := 0xaf124.

Definition pj_oframe (E : aenvA) (f e osp : Z) : list cell :=
  [C8 (Z_to_bv 64 DMP_LIT_RBRC_A); C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 4294967295); C8 (Z_to_bv 64 4294967297);
   C8 (Z_to_bv 64 0x4020200); C8 (Z_to_bv 64 DMP_LIT_QCOL_A); C8 (Z_to_bv 64 (shad (ae_DOC E + 8))); C8 (Z_to_bv 64 DMP_LIT_QUOT_A);
   C8 (Z_to_bv 64 72057594037927935); C8 (Z_to_bv 64 (ae_DOC E + 8)); C8 (Z_to_bv 64 e); C8 (Z_to_bv 64 osp)].

Lemma pj_ohead2 : forall (E : aenvA) (q f osp i e cv : Z) (gp ra a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 : word)
    (j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 : list byte) F fc (m : mem),
  aenvA_ok E -> 0 <= i -> i < e -> e + 1 <= ae_n E -> ae_n E < 2^32 -> 0 <= cv <= CNT_MAX -> ae_T E i = cword t_obj (e + 1) cv ->
  0x6c9000 <= q - 256 -> ae_lo E <= q - 256 -> q < 2^63 -> 0 <= osp < 2^64 -> 0 < f -> f + 256 < 2^63 -> shad f + 32 < 2^63 ->
  AINV_A E m -> (forall m', munch [(q - 256 + 24, q - 256 + 120)] m m' -> wmono asegs m m' -> shz m' (ae_TAPE E) (8 * ae_n E)) ->
  rw_cells asegs m (q - 256 + 24) [CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; C8 (Z_to_bv 64 osp)] ->
  mem_inv asegs m ->
  evt asegs (fun ms => exists (m' : mem) (a0x a1x a2x a3x a4x a5x a6x : word),
      munch [(q - 256 + 24, q - 256 + 120)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\
      ((i + 1 = e /\
         ms = MS (pjR q f gp ra a0x (Z_to_bv 64 DMP_LIT_RBRC_A) a2x a3x a4x a5 a6 a7 (Z_to_bv 64 (shad (ae_DOC E))) (Z_to_bv 64 i) (Z_to_bv 64 (ae_DOC E))
                      s8 s9 (Z_to_bv 64 (i + 1)) t0 t1 t2 t3 t4 t5 t6) F (Z_to_bv 64 DMP_PJ_CLOSE_A) fc None m' (seg_rom asegs)
         /\ rw_cells asegs m' (q - 256 + 24) [CB 8 j24; C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 f); CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104;
                                            C8 (Z_to_bv 64 e); C8 (Z_to_bv 64 osp)])
      \/ (i + 1 <> e /\
         ms = MS (mkR ra (Z_to_bv 64 (q - 256)) gp (Z_to_bv 64 TPV_A) t0 t1 t2 (Z_to_bv 64 q) (Z_to_bv 64 (q - 256)) a0x a1x a2x a3x a4x a5x a6x a7
                      (Z_to_bv 64 SHB) (Z_to_bv 64 f) (Z_to_bv 64 (shad (ae_DOC E))) (Z_to_bv 64 i) (Z_to_bv 64 (ae_DOC E)) (Z_to_bv 64 f) s8 s9
                      (Z_to_bv 64 (shad f)) (Z_to_bv 64 (i + 1)) t3 t4 t5 t6)
                 F (Z_to_bv 64 DMP_PJ_OLOOP_A) fc None m' (seg_rom asegs)
         /\ rw_cells asegs m' (q - 256 + 24) (pj_oframe E f e osp))))
    (MS (pjR q f gp ra a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (ae_DOC E)) (Z_to_bv 64 i) (Z_to_bv 64 (8 * i)) s8 s9 s11 t0 t1 t2 t3 t4 t5 t6)
        F (Z_to_bv 64 DMP_PJ_OHEAD_A) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros OK I0 IE EN N32 CV TW QLO LOQ QH OR F0 FH SFH AI SHZT FR MI.
  pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L (T16 & NT8 & TN & TS & TL) _ _ _ (D8 & DF & DL & DS & DT) LOW [HL HT]].
  unfold USTACK_TOP in HT. unfold SEGTOP_A in *.
  pose proof AI as (TAPEB & _ & _ & DOCC & DSH).
  assert (FS0 : 0 <= fs_size (ae_kD E)) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
  assert (ED : bv_unsigned (Z_to_bv 64 (ae_DOC E)) = ae_DOC E) by (apply unsigned_lit; lia).
  assert (EI : bv_unsigned (Z_to_bv 64 i) = i) by (apply unsigned_lit; lia).
  assert (ESP : bv_unsigned (Z_to_bv 64 (q - 256)) = q - 256) by (apply unsigned_lit; lia).
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  pose proof (shz_of_zero_run m (ae_DOC E) 2 D8 ltac:(lia) DSH) as SHZD. change (8 * Z.of_nat 2) with 16 in SHZD.
  unfold CNT_MAX in CV.
  assert (TIR : 0 <= ae_T E i < 2^64) by (rewrite TW; unfold cword, tword, t_obj; lia).
  unfold pjR, pj_oframe, DMP_PJ_OHEAD_A, DMP_PJ_CLOSE_A, DMP_PJ_OLOOP_A, DMP_LIT_RBRC_A, DMP_LIT_QUOT_A, DMP_LIT_QCOL_A, shad, SHB in *.
  pose proof (munch_refl [(q - 256 + 24, q - 256 + 120)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (tape_read _ (ae_TAPE E) (ae_tws E) i TAPEB ltac:(lia)) as RDT.
  pose proof (tape_read_typeA m (ae_TAPE E) (ae_tws E) i TAPEB ltac:(lia) TIR) as RTY.
  rewrite TW in RTY. rewrite ttype_cword in RTY by (unfold CNT_MAX; lia). unfold t_obj in RTY.

  chk0 SHZD (ae_DOC E). step. if_false. clear_shrd.

  zstep. astep. chk0 SHZT (ae_TAPE E + 8 * i). step. if_false. clear_shrd.
  step. astep. astep. astep. astep. rewrite mask_allA by lia.

  chk0 SHZD (ae_DOC E). step. if_false. clear_shrd.

  clear RDT RTY. ls. ls.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
    pose proof (AINV_A_munch E _ m m1 OK AI MU ltac:(constructor; [cbn [fst]; lia| constructor])) as (TAPEB1 & _);
    pose proof (tape_read _ (ae_TAPE E) (ae_tws E) i TAPEB1 ltac:(lia)) as RDT end.

  step. astep. rewrite mask_allA by lia. astep. astep. chk0 SHZT (ae_TAPE E + 8 * i). step. if_false. clear_shrd. step. astep.

  astep. rewrite TW, ttype_cword by (unfold CNT_MAX; lia). unfold t_obj. astep. step. step. step. if_false.
  astep. astep. astep. astep. step. if_true.

  step. astep. astep. astep. astep. step. step. if_false. astep. astep. rewrite low32_cwordA by (unfold CNT_MAX; lia). astep.
  replace (e + 1 + -1) with e by lia. step. step. ls. step.
  if_cases KE; zify_cond KE; rewrite ?unsigned_lit in KE by lia.
  -
    ls. step. astep. step. step. step. step. astep. ls. astep. ls. ls.
    astep. step. ls. step. ls. astep. ls. astep. astep. ls. astep. ls.
    apply evt_done. do 8 eexists.
    split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|].
    right. split; [lia|]. split; [atp_st_eq_goal| eassumption].
  -
    zstep. zstep.
    apply evt_done. do 8 eexists.
    split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|].
    left. split; [lia|]. split; [atp_st_eq_goal| eassumption].
  Unshelve. all: exact (Z_to_bv 64 0).
Qed.

Definition pjRO (E : aenvA) (q f : Z) (gp ra a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s7 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 : word) : bvmap 5 word :=
  mkR ra (Z_to_bv 64 (q - 256)) gp (Z_to_bv 64 TPV_A) t0 t1 t2 (Z_to_bv 64 q) (Z_to_bv 64 (q - 256)) a0 a1 a2 a3 a4 a5 a6 a7
      (Z_to_bv 64 SHB) s3 (Z_to_bv 64 (shad (ae_DOC E))) s5 (Z_to_bv 64 (ae_DOC E)) s7 s8 s9 (Z_to_bv 64 (shad f)) s11 t3 t4 t5 t6.

Lemma pj_okey1 : forall (E : aenvA) (q f osp e k o l : Z) (gp ra a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s7 s8 s9 t0 t1 t2 t3 t4 t5 t6 : word) F fc (m : mem),
  aenvA_ok E -> 0 <= k < ae_n E -> 0 <= ae_T E k < 2^64 -> tval (ae_T E k) = o -> str_at (ae_S E) (ae_sn E) o l ->
  0x6c9000 <= q - 256 -> q < 2^63 -> 0 <= osp < 2^64 -> 0 < f -> shad f + 32 < 2^63 -> 0 <= e < 2^64 ->
  AINV_A E m -> shz m (ae_TAPE E) (8 * ae_n E) -> shz m (ae_SBUF E) (ae_NS E) ->
  rw_cells asegs m (q - 256 + 24) (pj_oframe E f e osp) -> mem_inv asegs m ->
  evt asegs (fun ms => exists (a3x : word),
      ms = MS (pjRO E q f gp (Z_to_bv 64 0xaf91c) (Z_to_bv 64 osp) (Z_to_bv 64 DMP_LIT_QUOT_A) (Z_to_bv 64 1) a3x a4 a5 a6 a7
                   (Z_to_bv 64 (ae_S E o)) (Z_to_bv 64 (ae_S E (o + 1))) (Z_to_bv 64 (ae_S E (o + 2))) (Z_to_bv 64 (ae_S E (o + 3)))
                   (Z_to_bv 64 (ae_SBUF E + o)) (Z_to_bv 64 k) t0 t1 t2 t3 t4 t5 t6)
              F (Z_to_bv 64 DMP_PJ_PUT_A) fc None m (seg_rom asegs))
    (MS (pjRO E q f gp ra a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s7 s8 s9 (Z_to_bv 64 k) t0 t1 t2 t3 t4 t5 t6) F (Z_to_bv 64 DMP_PJ_OLOOP_A) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros OK KR TR TV SA QLO QH OR F0 SFH ER AI SHZT SHZS FR MI.
  pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L (T16 & NT8 & TN & TS & TL) (S16 & NS8 & SN & SS & SL) _ _ (D8 & DF & DL & DS & DT) LOW [HL HT]].
  unfold USTACK_TOP in HT. unfold SEGTOP_A in *. assert (HSN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia).
  pose proof (str_at_bounds _ _ HSN _ _ SA) as (O0 & L0 & OL & LE & O56).
  pose proof AI as (TAPEB & SBUFB & _ & DOCC & DSH).
  assert (FS0 : 0 <= fs_size (ae_kD E)) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
  assert (ED : bv_unsigned (Z_to_bv 64 (ae_DOC E)) = ae_DOC E) by (apply unsigned_lit; lia).
  assert (EK : bv_unsigned (Z_to_bv 64 k) = k) by (apply unsigned_lit; lia).
  assert (ESP : bv_unsigned (Z_to_bv 64 (q - 256)) = q - 256) by (apply unsigned_lit; lia).
  pose proof (shz_of_zero_run m (ae_DOC E) 2 D8 ltac:(lia) DSH) as SHZD. change (8 * Z.of_nat 2) with 16 in SHZD.
  unfold pjRO, pj_oframe, DMP_PJ_OLOOP_A, DMP_PJ_PUT_A, DMP_LIT_RBRC_A, DMP_LIT_QUOT_A, DMP_LIT_QCOL_A, shad, SHB in *.
  assert (ESD : bv_unsigned (Z_to_bv 64 (ae_DOC E / 8 + 2147450880)) = ae_DOC E / 8 + 2147450880) by (apply unsigned_lit; lia).
  assert (ESD8 : bv_unsigned (Z_to_bv 64 ((ae_DOC E + 8) / 8 + 2147450880)) = (ae_DOC E + 8) / 8 + 2147450880) by (apply unsigned_lit; lia).
  assert (ED8 : bv_unsigned (Z_to_bv 64 (ae_DOC E + 8)) = ae_DOC E + 8) by (apply unsigned_lit; lia).
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (tape_read _ (ae_TAPE E) (ae_tws E) k TAPEB ltac:(lia)) as RDT.
  pose proof (proj2 (proj1 (rw_cells_app asegs m (ae_DOC E) [_] [_]) DOCC)) as DOC2. cbn [cells_size csize Nat.add] in DOC2.
  replace (ae_DOC E + Z.of_nat 8) with (ae_DOC E + 8) in DOC2 by lia.

  shz_pose SHZD (ae_DOC E). zstep. shz_norm. zstep. if_false. clear_shrd.

  zstep. astep. astep. chk0 SHZT (ae_TAPE E + 8 * k). step. if_false. clear_shrd.

  zstep. shz_pose SHZD (ae_DOC E + 8). zstep. shz_norm. zstep. if_false. clear_shrd.

  step. zstep. zstep. zstep. zstep. rewrite ?(pj_land56 (ae_T E k)) by lia. rewrite !TV. astep.

  chk0 SHZS (ae_SBUF E + o). step. if_false. clear_shrd. astep. chk0 SHZS (ae_SBUF E + o + 3). step. if_false. clear_shrd.
  pose proof (sbuf_read1 m (ae_SBUF E) (ae_sbs E) o SBUFB ltac:(lia)) as RB0.
  pose proof (sbuf_read1 m (ae_SBUF E) (ae_sbs E) (o + 1) SBUFB ltac:(lia)) as RB1.
  pose proof (sbuf_read1 m (ae_SBUF E) (ae_sbs E) (o + 2) SBUFB ltac:(lia)) as RB2.
  pose proof (sbuf_read1 m (ae_SBUF E) (ae_sbs E) (o + 3) SBUFB ltac:(lia)) as RB3.
  pose proof (sbs_byteA E OK o ltac:(lia)) as Y0. pose proof (sbs_byteA E OK (o + 1) ltac:(lia)) as Y1.
  pose proof (sbs_byteA E OK (o + 2) ltac:(lia)) as Y2. pose proof (sbs_byteA E OK (o + 3) ltac:(lia)) as Y3.
  hide SBUFB.

  zstep. zstep. zstep. zstep.
  rewrite ?(a_u8_small (ae_S E o)), ?(a_u8_small (ae_S E (o + 1))), ?(a_u8_small (ae_S E (o + 2))), ?(a_u8_small (ae_S E (o + 3))) by (clear - Y0 Y1 Y2 Y3; lia).
  zstep. zstep. zstep. zstep.
  apply evt_done. eexists. atp_st_eq_goal.
Qed.

Lemma pj_okey2 : forall (E : aenvA) (q f osp o l k : Z) (gp ra a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 : word) F fc (m : mem),
  aenvA_ok E -> str_at (ae_S E) (ae_sn E) o l -> 0 <= osp < 2^64 -> mem_inv asegs m ->
  evt asegs (fun ms => exists (s5x s7x s8x : word),
      ms = MS (pjRO E q f gp (Z_to_bv 64 0xaf93c) (Z_to_bv 64 osp) (Z_to_bv 64 (ae_SBUF E + o + 4)) (Z_to_bv 64 l) a3 a4 a5 a6 a7
                   (Z_to_bv 64 (ae_S E o)) s5x s7x s8x (Z_to_bv 64 (ae_SBUF E + o)) (Z_to_bv 64 k) t0 t1 t2 t3 t4 t5 t6)
              F (Z_to_bv 64 DMP_PJ_PUT_A) fc None m (seg_rom asegs))
    (MS (pjRO E q f gp ra (Z_to_bv 64 osp) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (ae_S E o)) (Z_to_bv 64 (ae_S E (o + 1))) (Z_to_bv 64 (ae_S E (o + 2)))
             (Z_to_bv 64 (ae_S E (o + 3))) (Z_to_bv 64 (ae_SBUF E + o)) (Z_to_bv 64 k) t0 t1 t2 t3 t4 t5 t6) F (Z_to_bv 64 0xaf91c) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros OK SA OR MI.
  pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L (T16 & NT8 & TN & TS & TL) (S16 & NS8 & SN & SS & SL) _ _ (D8 & DF & DL & DS & DT) LOW [HL HT]].
  unfold USTACK_TOP in HT. unfold SEGTOP_A in *. assert (HSN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia).
  pose proof (str_at_bounds _ _ HSN _ _ SA) as (O0 & L0 & OL & LE & O56).
  pose proof (sbs_byteA E OK o ltac:(lia)) as Y0. pose proof (sbs_byteA E OK (o + 1) ltac:(lia)) as Y1.
  pose proof (sbs_byteA E OK (o + 2) ltac:(lia)) as Y2. pose proof (sbs_byteA E OK (o + 3) ltac:(lia)) as Y3.
  assert (EP : bv_unsigned (Z_to_bv 64 (ae_SBUF E + o)) = ae_SBUF E + o) by (apply unsigned_lit; lia).
  unfold pjRO, DMP_PJ_PUT_A.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.

  do 8 zstep.
  rewrite ?(a_u8_small (ae_S E o)), ?(a_u8_small (ae_S E (o + 1))), ?(a_u8_small (ae_S E (o + 2))), ?(a_u8_small (ae_S E (o + 3))) by (clear - Y0 Y1 Y2 Y3; lia).
  rewrite ?land64_mod. rewrite ?shl_mod_smallA by (clear - Y0 Y1 Y2 Y3; lia). rewrite le32_of_lbu4A by (clear - Y0 Y1 Y2 Y3; lia).
  change (ae_S E o + 2 ^ 8 * ae_S E (o + 1) + 2 ^ 16 * ae_S E (o + 2) + 2 ^ 24 * ae_S E (o + 3)) with (le32 (ae_S E) o). rewrite LE.
  apply evt_done. do 3 eexists. atp_st_eq_goal.
Qed.

Lemma pj_okey3 : forall (E : aenvA) (q f osp e : Z) (gp ra a1 a2 a3 a4 a5 a6 a7 s3 s5 s7 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 : word) F fc (m : mem),
  0x6c9000 <= q - 256 -> q < 2^63 -> rw_cells asegs m (q - 256 + 24) (pj_oframe E f e osp) -> mem_inv asegs m ->
  evt asegs (fun ms =>
      ms = MS (pjRO E q f gp (Z_to_bv 64 0xaf948) (Z_to_bv 64 osp) (Z_to_bv 64 DMP_LIT_QCOL_A) (Z_to_bv 64 3) a3 a4 a5 a6 a7 s3 s5 s7 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6)
              F (Z_to_bv 64 DMP_PJ_PUT_A) fc None m (seg_rom asegs))
    (MS (pjRO E q f gp ra (Z_to_bv 64 osp) a1 a2 a3 a4 a5 a6 a7 s3 s5 s7 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6) F (Z_to_bv 64 0xaf93c) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros QLO QH FR MI. assert (ESP : bv_unsigned (Z_to_bv 64 (q - 256)) = q - 256) by (apply unsigned_lit; lia).
  unfold pjRO, pj_oframe, DMP_PJ_PUT_A, DMP_LIT_QCOL_A in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. zstep. zstep. apply evt_done. atp_st_eq_goal.
Qed.

Lemma pj_ochild : forall (E : aenvA) (q f osp e k : Z) (gp ra a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s7 s8 s9 t0 t1 t2 t3 t4 t5 t6 : word) F fc (m : mem),
  0x6c9000 <= q - 256 -> q < 2^63 -> 0 <= k -> k + 1 < 2^63 -> rw_cells asegs m (q - 256 + 24) (pj_oframe E f e osp) -> mem_inv asegs m ->
  evt asegs (fun ms =>
      ms = MS (pjRO E q f gp (Z_to_bv 64 0xaf95c) (Z_to_bv 64 osp) (Z_to_bv 64 (ae_DOC E)) (Z_to_bv 64 (k + 1)) a3 a4 a5 a6 a7 s3 s5 s7 s8 (Z_to_bv 64 (k + 1))
                   (Z_to_bv 64 k) t0 t1 t2 t3 t4 t5 t6)
              F (Z_to_bv 64 DMP_PJ_A) fc None m (seg_rom asegs))
    (MS (pjRO E q f gp ra a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s7 s8 s9 (Z_to_bv 64 k) t0 t1 t2 t3 t4 t5 t6) F (Z_to_bv 64 0xaf948) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros QLO QH K0 KH FR MI. assert (ESP : bv_unsigned (Z_to_bv 64 (q - 256)) = q - 256) by (apply unsigned_lit; lia).
  assert (EK : bv_unsigned (Z_to_bv 64 k) = k) by (apply unsigned_lit; lia).
  unfold pjRO, pj_oframe, DMP_PJ_A in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. zstep. zstep. zstep. zstep. apply evt_done. atp_st_eq_goal.
Qed.

Lemma pj_ostep : forall (E : aenvA) (q f osp e k it j : Z) (gp ra a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s7 s8 t0 t1 t2 t3 t4 t5 t6 : word) F fc (m : mem),
  aenvA_ok E -> it = k + 1 -> 0 <= k -> it < j -> j <= ae_n E -> ae_n E < 2^32 -> pj_kindA (ae_T E) (ae_S E) (ae_sn E) it j ->
  0x6c9000 <= q - 256 -> q < 2^63 -> 0 <= osp < 2^64 -> 0 <= e < 2^64 -> 0 < f -> shad f + 32 < 2^63 ->
  AINV_A E m -> shz m (ae_TAPE E) (8 * ae_n E) ->
  rw_cells asegs m (q - 256 + 24) (pj_oframe E f e osp) -> mem_inv asegs m ->
  evt asegs (fun ms => exists (a0x a1x a2x : word),
      ms = MS (pjRO E q f gp ra a0x a1x a2x a3 a4 a5 a6 a7 s3 s5 s7 s8 (Z_to_bv 64 (8 * it)) (Z_to_bv 64 j) t0 t1 t2 t3 t4 t5 t6)
              F (Z_to_bv 64 0xaf9cc) fc None m (seg_rom asegs))
    (MS (pjRO E q f gp ra a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s7 s8 (Z_to_bv 64 it) (Z_to_bv 64 k) t0 t1 t2 t3 t4 t5 t6) F (Z_to_bv 64 0xaf95c) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros OK IT K0 IJ JN N32 KIND QLO QH OR ER F0 SFH AI SHZT FR MI.
  pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L (T16 & NT8 & TN & TS & TL) _ _ _ (D8 & DF & DL & DS & DT) LOW [HL HT]].
  unfold USTACK_TOP in HT. unfold SEGTOP_A in *. assert (HSN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia).
  pose proof AI as (TAPEB & _ & _ & DOCC & DSH).
  assert (FS0 : 0 <= fs_size (ae_kD E)) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
  assert (ED : bv_unsigned (Z_to_bv 64 (ae_DOC E)) = ae_DOC E) by (apply unsigned_lit; lia).
  assert (EI : bv_unsigned (Z_to_bv 64 it) = it) by (apply unsigned_lit; lia).
  assert (EK : bv_unsigned (Z_to_bv 64 k) = k) by (apply unsigned_lit; lia).
  assert (ESP : bv_unsigned (Z_to_bv 64 (q - 256)) = q - 256) by (apply unsigned_lit; lia).
  pose proof (shz_of_zero_run m (ae_DOC E) 2 D8 ltac:(lia) DSH) as SHZD. change (8 * Z.of_nat 2) with 16 in SHZD.
  unfold pjRO, pj_oframe, DMP_LIT_RBRC_A, DMP_LIT_QUOT_A, DMP_LIT_QCOL_A, shad, SHB in *.
  assert (ESD : bv_unsigned (Z_to_bv 64 (ae_DOC E / 8 + 2147450880)) = ae_DOC E / 8 + 2147450880) by (apply unsigned_lit; lia).
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (tape_read _ (ae_TAPE E) (ae_tws E) it TAPEB ltac:(lia)) as RDT.

  shz_pose SHZD (ae_DOC E). zstep. shz_norm. zstep. if_false. clear_shrd.

  zstep. astep. astep. chk0 SHZT (ae_TAPE E + 8 * it). step. if_false. clear_shrd.
  destruct KIND as [[-> TY]|[[-> TY]|[[-> STRI]|(cv & CV & CO)]]].
  -
    assert (TIR : 0 <= ae_T E it < 2^64) by (destruct TY as [E'|[E'|E']]; rewrite E'; unfold tword, t_true, t_false, t_null; lia).
    step. astep.
    destruct TY as [E'|[E'|E']]; rewrite E', ttype_tword by lia; unfold t_true, t_false, t_null; astep; step;
      (step; if_false; zstep; astep; astep; step; if_true; zstep; astep; astep; step; if_true; astep;
       apply evt_done; do 3 eexists; atp_st_eq_goal).
  -
    assert (TIR : 0 <= ae_T E it < 2^64) by (destruct TY as [E'|[E'|E']]; rewrite E'; unfold tword, t_i64, t_u64, t_dbl; lia).
    step. astep.
    destruct TY as [E'|[E'|E']]; rewrite E', ttype_tword by lia; unfold t_i64, t_u64, t_dbl; astep; step;
      (step; if_false; zstep; astep; astep; step; if_false; astep; step;
       apply evt_done; do 3 eexists; atp_st_eq_goal).
  -
    pose proof (key_word_rangeA _ _ _ _ STRI HSN) as (TIR & _ & KT).
    step. astep. rewrite KT. unfold t_str. astep. step.
    step. if_true. astep.
    apply evt_done. do 3 eexists. atp_st_eq_goal.
  -
    unfold CNT_MAX in CV.
    destruct CO as [E'|E'];
      (assert (TIR : 0 <= ae_T E it < 2^64) by (rewrite E'; unfold cword, tword, t_arr, t_obj; lia));
      step; astep; rewrite E', ttype_cword by (unfold CNT_MAX; lia); unfold t_arr, t_obj; astep; step;
      (step; if_false; zstep; astep; astep; step; if_true; zstep; astep; astep; step; if_false; zstep; astep);
      [rewrite (low32_cwordA 91) by (unfold CNT_MAX; lia)| rewrite (low32_cwordA 123) by (unfold CNT_MAX; lia)]; step;
      (apply evt_done; do 3 eexists; atp_st_eq_goal).
Qed.

Definition DMP_PJ_OTEST_A : Z := 0xaf9cc.
Lemma pj_otest : forall (E : aenvA) (q f osp e b : Z) (gp ra a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s7 s8 s9 t0 t1 t2 t3 t4 t5 t6 : word) F fc (m : mem),
  0x6c9000 <= q - 256 -> q < 2^63 -> 0 <= b < 2^63 -> 0 <= e < 2^63 ->
  rw_cells asegs m (q - 256 + 24) (pj_oframe E f e osp) -> mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (pjRO E q f gp ra (Z_to_bv 64 e) a1 a2 a3 a4 a5 a6 a7 s3 s5 s7 s8 s9 (Z_to_bv 64 b) t0 t1 t2 t3 t4 t5 t6)
                               F (Z_to_bv 64 (if b =? e then DMP_PJ_LOOPX_A else DMP_PJ_OLOOP_A)) fc None m (seg_rom asegs))
    (MS (pjRO E q f gp ra a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s7 s8 s9 (Z_to_bv 64 b) t0 t1 t2 t3 t4 t5 t6) F (Z_to_bv 64 DMP_PJ_OTEST_A) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros QLO QH BR ER FR MI. assert (ESP : bv_unsigned (Z_to_bv 64 (q - 256)) = q - 256) by (apply unsigned_lit; lia).
  unfold pjRO, pj_oframe, DMP_PJ_OTEST_A, DMP_PJ_LOOPX_A, DMP_PJ_OLOOP_A in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.

  zstep. step. if_cases KJ; zify_cond KJ; rewrite ?unsigned_lit in KJ by lia.
  - replace (b =? e) with false by (symmetry; apply Z.eqb_neq; lia). apply evt_done. atp_st_eq_goal.
  - replace (b =? e) with true by (symmetry; apply Z.eqb_eq; lia). zstep. apply evt_done. atp_st_eq_goal.
Qed.
