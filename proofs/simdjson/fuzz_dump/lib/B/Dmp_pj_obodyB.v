From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.P Require Import Str_tac Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjTape SjTapeList SjTapeTile.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface RT_iface2 D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_akit Sj_acps Sj_hkit Atp_fzwA Atp_defsA Atp_objwA Atp_objnA Pj_defsA El_defsA Dmp_hdefsA Dmp_pj_ifaceA Dmp_pj_kitA Dmp_pj_leafA Dmp_pj_strA Dmp_pj_arrA Dmp_pj_objA El_os_defsA Pj_ser_trefA Dmp_pj_oheadB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma pj_okey1 : forall (E : aenvA) (q f osp e kk o l : Z) (gp ra a0 a1 a2 a3 a4 a5 a6 a7 s4 s8 s10 t0 t1 t2 t3 t4 t5 t6 : word) F fc (m : mem),
  aenvA_ok E -> 0 <= kk < ae_n E -> ae_n E < 2^32 -> 0 <= ae_T E kk < 2^64 -> tval (ae_T E kk) = o -> str_at (ae_S E) (ae_sn E) o l ->
  0x6d5000 <= q - 256 -> ae_lo E <= q - 272 -> q < 2^63 ->
  AINV_A E m -> client_consts m -> stk bsegs m (ae_lo E) (q - 256) ->
  shz m (ae_TAPE E) (8 * ae_n E) -> shz m (ae_SBUF E) (ae_NS E) -> shz m (ae_DOC E) 16 ->
  rw_cells bsegs m (q - 256) (pj_oframe E f e osp) -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m' : mem) (a3x a4x : word),
      munch [(q - 272, q - 256)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' (ae_lo E) (q - 256) /\
      ms = MS (mkR (Z_to_bv 64 0xaf810) (Z_to_bv 64 (q - 256)) gp (Z_to_bv 64 TPV_A) t0 t1 t2 (Z_to_bv 64 q) (Z_to_bv 64 (q - 256))
                   (Z_to_bv 64 osp) (Z_to_bv 64 DMP_LIT_QUOT_A) (Z_to_bv 64 1) a3x a4x a5 a6 a7
                   (Z_to_bv 64 (2^56 - 1)) (Z_to_bv 64 (ae_S E (o + 2))) (Z_to_bv 64 (ae_S E (o + 1))) (Z_to_bv 64 (shad (ae_DOC E + 8)))
                   (Z_to_bv 64 kk) (Z_to_bv 64 (ae_S E (o + 3))) (Z_to_bv 64 (ae_DOC E + 8)) (Z_to_bv 64 (ae_S E o))
                   (Z_to_bv 64 (ae_SBUF E + o + 4)) (Z_to_bv 64 (shad f)) t3 t4 t5 t6)
              F (Z_to_bv 64 DMP_PJ_PUT_A) fc None m' (seg_rom bsegs))
    (MS (pjRO E q f kk gp ra a0 a1 a2 a3 a4 a5 a6 a7 s4 s8 s10 t0 t1 t2 t3 t4 t5 t6) F (Z_to_bv 64 DMP_PJ_OLOOP_A) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros OK KR N32 TR TV SA QLO LOQ QH AI CC ST SHZ0 SHZS0 SHZD0 FR MI.
  pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L (T16 & NT8 & TN & TS & TL) (S16 & NS8 & SN & SS & SL) _ _ (D8 & DF & DL & DS & DT) LOW [HL HT]].
  unfold USTACK_TOP in HT. unfold SEGTOP_A in *. assert (HSN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia).
  pose proof (str_at_bounds _ _ HSN _ _ SA) as (O0 & L0 & OL & LE & O56).
  assert (SHZT : forall m', munch [(q - 272, q - 256)] m m' -> wmono bsegs m m' -> shz m' (ae_TAPE E) (8 * ae_n E)).
  { intros m' MU' _. eapply shz_munch_hi; [exact SHZ0| exact MU'| lia| lia|]. intros y Hy. cbn [outside]. repeat (split; try exact I); lia. }
  assert (SHZS : forall m', munch [(q - 272, q - 256)] m m' -> wmono bsegs m m' -> shz m' (ae_SBUF E) (ae_NS E)).
  { intros m' MU' _. eapply shz_munch_hi; [exact SHZS0| exact MU'| lia| lia|]. intros y Hy. cbn [outside]. repeat (split; try exact I); lia. }
  assert (SHZD : forall m', munch [(q - 272, q - 256)] m m' -> wmono bsegs m m' -> shz m' (ae_DOC E) 16).
  { intros m' MU' _. eapply shz_munch_hi; [exact SHZD0| exact MU'| lia| lia|]. intros y Hy. cbn [outside]. repeat (split; try exact I); lia. }
  clear SHZ0 SHZS0 SHZD0.
  assert (FS0 : 0 <= fs_size (ae_kD E)) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
  assert (ED : bv_unsigned (Z_to_bv 64 (ae_DOC E)) = ae_DOC E) by (apply unsigned_lit; lia).
  assert (EK : bv_unsigned (Z_to_bv 64 kk) = kk) by (apply unsigned_lit; lia).
  assert (ESP : bv_unsigned (Z_to_bv 64 (q - 256)) = q - 256) by (apply unsigned_lit; lia).
  pose proof (sbs_byteA E OK o ltac:(lia)) as Y0. pose proof (sbs_byteA E OK (o + 1) ltac:(lia)) as Y1.
  pose proof (sbs_byteA E OK (o + 2) ltac:(lia)) as Y2. pose proof (sbs_byteA E OK (o + 3) ltac:(lia)) as Y3.
  unfold pjRO, pj_oframe, DMP_PJ_OLOOP_A, DMP_PJ_PUT_A, DMP_LIT_RBRC_A, DMP_LIT_QUOT_A, DMP_LIT_QCOL_A, shad, SHB in *.
  assert (ESD8 : bv_unsigned (Z_to_bv 64 ((ae_DOC E + 8) / 8 + 2147450880)) = (ae_DOC E + 8) / 8 + 2147450880) by (apply unsigned_lit; lia).
  assert (ED8 : bv_unsigned (Z_to_bv 64 (ae_DOC E + 8)) = ae_DOC E + 8) by (apply unsigned_lit; lia).
  pose proof (munch_refl [(q - 272, q - 256)] m) as MU. pose proof (wmono_refl bsegs m) as WM.

  zstep. zstep. zstep.
  oh_tix 0xaf744.
  match goal with A : AINV_A E ?mm, MUx : munch _ m ?mm |- _ =>
    pose proof A as (TAPEB & _ & _ & DOCC & _);
    pose proof (tape_read _ (ae_TAPE E) (ae_tws E) kk TAPEB ltac:(lia)) as RDT;
    pose proof (proj2 (proj1 (rw_cells_app bsegs mm (ae_DOC E) [_] [_]) DOCC)) as DOC2 end.
  cbn [cells_size csize Nat.add] in DOC2. replace (ae_DOC E + Z.of_nat 8) with (ae_DOC E + 8) in DOC2 by lia.
  clear TAPEB DOCC.
  chk0 SHZT (ae_TAPE E + 8 * kk). step. if_false.
  shz_pose SHZD (ae_DOC E + 8). zstep. shz_norm. step. if_false.
  zstep. step. oh_gt.
  zstep. zstep. rewrite ?(pj_land56 (ae_T E kk)) by lia. rewrite ?TV.
  zstep. zstep. step. oh_gt. step. oh_gt.
  zstep. zstep. zstep.
  clear RDT.
  oh_tix 0xaf788.
  match goal with A : AINV_A E ?mm, MUx : munch _ m ?mm |- _ =>
    pose proof A as (TAPEB & SBUFB & _ & _ & _);
    pose proof (tape_read _ (ae_TAPE E) (ae_tws E) kk TAPEB ltac:(lia)) as RDT;
    assert (SNL : ae_sn E = Z.of_nat (length (ae_sbs E))) by reflexivity;
    pose proof (sbuf_read1 mm (ae_SBUF E) (ae_sbs E) o SBUFB ltac:(lia)) as RS0;
    pose proof (sbuf_read1 mm (ae_SBUF E) (ae_sbs E) (o + 1) SBUFB ltac:(lia)) as RS1;
    pose proof (sbuf_read1 mm (ae_SBUF E) (ae_sbs E) (o + 2) SBUFB ltac:(lia)) as RS2;
    pose proof (sbuf_read1 mm (ae_SBUF E) (ae_sbs E) (o + 3) SBUFB ltac:(lia)) as RS3 end.
  replace (ae_SBUF E + (o + 1)) with (ae_SBUF E + o + 1) in RS1 by lia.
  replace (ae_SBUF E + (o + 2)) with (ae_SBUF E + o + 2) in RS2 by lia.
  replace (ae_SBUF E + (o + 3)) with (ae_SBUF E + o + 3) in RS3 by lia.
  clear TAPEB SBUFB.
  chk0 SHZT (ae_TAPE E + 8 * kk). step. if_false.
  shz_pose SHZD (ae_DOC E + 8). zstep. shz_norm. step. if_false.
  zstep. zstep. zstep. rewrite ?(pj_land56 (ae_T E kk)) by lia. rewrite ?TV.
  zstep. step. oh_gt.
  zstep. zstep.
  replace (0 <? ae_SBUF E) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (ae_SBUF E + o <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
  zstep. step. if_false. step. oh_gt.
  chk0 SHZS (ae_SBUF E + o). step. if_false.
  zstep. zstep. chk0 SHZS (ae_SBUF E + o + 3). step. if_false.
  zstep. zstep. zstep. zstep.
  rewrite ?(a_u8_small (Tf (ae_sbs E) o)), ?(a_u8_small (Tf (ae_sbs E) (o + 1))), ?(a_u8_small (Tf (ae_sbs E) (o + 2))), ?(a_u8_small (Tf (ae_sbs E) (o + 3))) by (clear - Y0 Y1 Y2 Y3; unfold Tf in *; lia).
  zstep. zstep. zstep. zstep.
  apply evt_done. do 3 eexists. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
  atp_st_eq_goal.
Unshelve. all: exact (Z_to_bv 64 0).
Qed.

Lemma pj_okey2 : forall (E : aenvA) (q f kk o l : Z) (gp ra a0 a1 a2 a3 a4 a5 a6 a7 s8 t0 t1 t2 t3 t4 t5 t6 : word) F fc (m : mem),
  aenvA_ok E -> str_at (ae_S E) (ae_sn E) o l -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (s3x s4x s7x : word),
      ms = MS (mkR (Z_to_bv 64 0xaf830) (Z_to_bv 64 (q - 256)) gp (Z_to_bv 64 TPV_A) t0 t1 t2 (Z_to_bv 64 q) (Z_to_bv 64 (q - 256))
                   a0 (Z_to_bv 64 (ae_SBUF E + o + 4)) (Z_to_bv 64 l) a3 a4 a5 a6 a7
                   (Z_to_bv 64 (2^56 - 1)) s3x s4x (Z_to_bv 64 (shad (ae_DOC E + 8))) (Z_to_bv 64 kk) s7x s8 (Z_to_bv 64 (ae_S E o))
                   (Z_to_bv 64 (ae_SBUF E + o + 4)) (Z_to_bv 64 (shad f)) t3 t4 t5 t6)
              F (Z_to_bv 64 DMP_PJ_PUT_A) fc None m (seg_rom bsegs))
    (MS (mkR ra (Z_to_bv 64 (q - 256)) gp (Z_to_bv 64 TPV_A) t0 t1 t2 (Z_to_bv 64 q) (Z_to_bv 64 (q - 256))
             a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (2^56 - 1)) (Z_to_bv 64 (ae_S E (o + 2))) (Z_to_bv 64 (ae_S E (o + 1))) (Z_to_bv 64 (shad (ae_DOC E + 8)))
             (Z_to_bv 64 kk) (Z_to_bv 64 (ae_S E (o + 3))) s8 (Z_to_bv 64 (ae_S E o))
             (Z_to_bv 64 (ae_SBUF E + o + 4)) (Z_to_bv 64 (shad f)) t3 t4 t5 t6)
        F (Z_to_bv 64 0xaf810) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros OK SA MI.
  pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L (T16 & NT8 & TN & TS & TL) (S16 & NS8 & SN & SS & SL) _ _ (D8 & DF & DL & DS & DT) LOW [HL HT]].
  unfold USTACK_TOP in HT. unfold SEGTOP_A in *. assert (HSN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia).
  pose proof (str_at_bounds _ _ HSN _ _ SA) as (O0 & L0 & OL & LE & O56).
  pose proof (sbs_byteA E OK o ltac:(lia)) as Y0. pose proof (sbs_byteA E OK (o + 1) ltac:(lia)) as Y1.
  pose proof (sbs_byteA E OK (o + 2) ltac:(lia)) as Y2. pose proof (sbs_byteA E OK (o + 3) ltac:(lia)) as Y3.
  unfold DMP_PJ_PUT_A.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  do 8 zstep.
  rewrite ?(a_u8_small (ae_S E o)), ?(a_u8_small (ae_S E (o + 1))), ?(a_u8_small (ae_S E (o + 2))), ?(a_u8_small (ae_S E (o + 3))) by (clear - Y0 Y1 Y2 Y3; lia).
  rewrite ?(a_u64_small (ae_S E o)), ?(a_u64_small (ae_S E (o + 1))), ?(a_u64_small (ae_S E (o + 2))), ?(a_u64_small (ae_S E (o + 3))) by (clear - Y0 Y1 Y2 Y3; lia).
  rewrite ?land64_mod. rewrite ?shl_mod_smallA by (clear - Y0 Y1 Y2 Y3; lia). rewrite le32_of_lbu4A by (clear - Y0 Y1 Y2 Y3; lia).
  change (ae_S E o + 2 ^ 8 * ae_S E (o + 1) + 2 ^ 16 * ae_S E (o + 2) + 2 ^ 24 * ae_S E (o + 3)) with (le32 (ae_S E) o). rewrite LE.
  apply evt_done. do 3 eexists. atp_st_eq_goal.
Qed.

Lemma pj_okey3 : forall (E : aenvA) (q f osp e kk : Z) (gp ra a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s7 s8 s9 s10 t0 t1 t2 t3 t4 t5 t6 : word) F fc (m : mem),
  0x6d5000 <= q - 256 -> q < 2^63 -> rw_cells bsegs m (q - 256) (pj_oframe E f e osp) -> mem_inv bsegs m ->
  evt bsegs (fun ms =>
      ms = MS (mkR (Z_to_bv 64 0xaf83c) (Z_to_bv 64 (q - 256)) gp (Z_to_bv 64 TPV_A) t0 t1 t2 (Z_to_bv 64 q) (Z_to_bv 64 (q - 256))
                   a0 (Z_to_bv 64 DMP_LIT_QCOL_A) (Z_to_bv 64 3) a3 a4 a5 a6 a7
                   (Z_to_bv 64 (2^56 - 1)) s3 s4 (Z_to_bv 64 (shad (ae_DOC E + 8))) (Z_to_bv 64 kk) s7 s8 s9 s10 (Z_to_bv 64 (shad f)) t3 t4 t5 t6)
              F (Z_to_bv 64 DMP_PJ_PUT_A) fc None m (seg_rom bsegs))
    (MS (mkR ra (Z_to_bv 64 (q - 256)) gp (Z_to_bv 64 TPV_A) t0 t1 t2 (Z_to_bv 64 q) (Z_to_bv 64 (q - 256))
             a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (2^56 - 1)) s3 s4 (Z_to_bv 64 (shad (ae_DOC E + 8))) (Z_to_bv 64 kk) s7 s8 s9 s10 (Z_to_bv 64 (shad f)) t3 t4 t5 t6)
        F (Z_to_bv 64 0xaf830) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros QLO QH FR MI. assert (ESP : bv_unsigned (Z_to_bv 64 (q - 256)) = q - 256) by (apply unsigned_lit; lia).
  unfold pj_oframe, DMP_PJ_PUT_A, DMP_LIT_QCOL_A in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep. zstep. zstep. apply evt_done. atp_st_eq_goal.
Qed.

Lemma pj_ochild : forall (E : aenvA) (q f osp e kk : Z) (gp ra a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s7 s8 s9 s10 t0 t1 t2 t3 t4 t5 t6 : word) F fc (m : mem),
  0x6d5000 <= q - 256 -> q < 2^63 -> 0 <= kk -> kk + 1 < 2^63 -> rw_cells bsegs m (q - 256) (pj_oframe E f e osp) -> mem_inv bsegs m ->
  evt bsegs (fun ms =>
      ms = MS (mkR (Z_to_bv 64 0xaf854) (Z_to_bv 64 (q - 256)) gp (Z_to_bv 64 TPV_A) t0 t1 t2 (Z_to_bv 64 q) (Z_to_bv 64 (q - 256))
                   (Z_to_bv 64 osp) (Z_to_bv 64 (ae_DOC E)) (Z_to_bv 64 (kk + 1)) a3 a4 a5 a6 a7
                   (Z_to_bv 64 (2^56 - 1)) s3 s4 (Z_to_bv 64 (shad (ae_DOC E + 8))) (Z_to_bv 64 kk) (Z_to_bv 64 (ae_DOC E)) s8 s9
                   (Z_to_bv 64 (kk + 1)) (Z_to_bv 64 (shad f)) t3 t4 t5 t6)
              F (Z_to_bv 64 DMP_PJ_A) fc None m (seg_rom bsegs))
    (MS (mkR ra (Z_to_bv 64 (q - 256)) gp (Z_to_bv 64 TPV_A) t0 t1 t2 (Z_to_bv 64 q) (Z_to_bv 64 (q - 256))
             a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (2^56 - 1)) s3 s4 (Z_to_bv 64 (shad (ae_DOC E + 8))) (Z_to_bv 64 kk) s7 s8 s9 s10 (Z_to_bv 64 (shad f)) t3 t4 t5 t6)
        F (Z_to_bv 64 0xaf83c) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros QLO QH K0 KH FR MI. assert (ESP : bv_unsigned (Z_to_bv 64 (q - 256)) = q - 256) by (apply unsigned_lit; lia).
  assert (EK : bv_unsigned (Z_to_bv 64 kk) = kk) by (apply unsigned_lit; lia).
  unfold pj_oframe, DMP_PJ_A in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  do 6 zstep. apply evt_done. atp_st_eq_goal.
Qed.
