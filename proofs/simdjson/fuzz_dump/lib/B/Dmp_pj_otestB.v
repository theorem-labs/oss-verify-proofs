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

Local Ltac os_notat := tryif pr_at [0xafc0c; 0xaf8e0] then fail else idtac.
Local Tactic Notation "os_walk" int_or_var(n) := do n (try (os_notat; oh_step)).
Local Ltac os_done := apply evt_done; do 7 eexists; split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
  split; [eassumption|]; atp_st_eq_goal.

Lemma pj_otest : forall (E : aenvA) (q f osp e b : Z) (gp ra a0 a1 a2 a3 a4 a5 a6 a7 s4 s8 s10 t0 t1 t2 t3 t4 t5 t6 : word) F fc (m : mem),
  0x6d5000 <= q - 256 -> q < 2^63 -> 0 <= b < 2^63 -> 0 <= e < 2^63 ->
  rw_cells bsegs m (q - 256) (pj_oframe E f e osp) -> mem_inv bsegs m ->
  evt bsegs (fun ms =>
      (b <> e /\ ms = MS (pjRO E q f b gp ra (Z_to_bv 64 e) a1 a2 a3 a4 a5 a6 a7 s4 s8 s10 t0 t1 t2 t3 t4 t5 t6)
                         F (Z_to_bv 64 DMP_PJ_OLOOP_A) fc None m (seg_rom bsegs))
      \/ (b = e /\ ms = MS (pjRO E q f b gp ra (Z_to_bv 64 e) a1 a2 a3 a4 a5 a6 a7 s4 s8 s10 t0 t1 t2 t3 t4 t5 t6)
                           F (Z_to_bv 64 DMP_PJ_LOOPX_A) fc None m (seg_rom bsegs)))
    (MS (pjRO E q f b gp ra a0 a1 a2 a3 a4 a5 a6 a7 s4 s8 s10 t0 t1 t2 t3 t4 t5 t6) F (Z_to_bv 64 DMP_PJ_OTEST_A) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros QLO QH BR ER FR MI. assert (ESP : bv_unsigned (Z_to_bv 64 (q - 256)) = q - 256) by (apply unsigned_lit; lia).
  unfold pjRO, pj_oframe, DMP_PJ_OTEST_A, DMP_PJ_LOOPX_A, DMP_PJ_OLOOP_A in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  repeat (tryif pr_at [DMP_PJ_OLOOP_A; DMP_PJ_LOOPX_A] then fail else
          first [ls | if_false | if_true | (let KJ := fresh "KJ" in if_cases KJ; zify_cond KJ; rewrite ?unsigned_lit in KJ by lia)]).
  all: apply evt_done; first [left; split; [lia| atp_st_eq_goal] | right; split; [lia| atp_st_eq_goal]].
Qed.

Lemma pj_ostep : forall (E : aenvA) (q f osp e kk b : Z) (gp ra a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s9 t0 t1 t2 t3 t4 t5 t6 : word) F fc (m : mem),
  aenvA_ok E -> 0 <= kk -> kk + 1 < b -> b <= ae_n E -> ae_n E < 2^32 -> pj_kindA (ae_T E) (ae_S E) (ae_sn E) (kk + 1) b ->
  0x6d5000 <= q - 256 -> ae_lo E <= q - 272 -> q < 2^63 ->
  AINV_A E m -> client_consts m -> stk bsegs m (ae_lo E) (q - 256) -> shz m (ae_TAPE E) (8 * ae_n E) ->
  rw_cells bsegs m (q - 256) (pj_oframe E f e osp) -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m' : mem) (rax a0x a1x a2x a3x a4x : word),
      munch [(q - 272, q - 256)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' (ae_lo E) (q - 256) /\
      ms = MS (pjRO E q f b gp rax a0x a1x a2x a3x a4x a5 a6 a7 s4 (Z_to_bv 64 (ae_DOC E + 8)) (Z_to_bv 64 (kk + 1)) t0 t1 t2 t3 t4 t5 t6)
              F (Z_to_bv 64 DMP_PJ_OTEST_A) fc None m' (seg_rom bsegs))
    (MS (mkR ra (Z_to_bv 64 (q - 256)) gp (Z_to_bv 64 TPV_A) t0 t1 t2 (Z_to_bv 64 q) (Z_to_bv 64 (q - 256))
             a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (2^56 - 1)) s3 s4 (Z_to_bv 64 (shad (ae_DOC E + 8))) (Z_to_bv 64 kk) (Z_to_bv 64 (ae_DOC E))
             (Z_to_bv 64 (ae_DOC E + 8)) s9 (Z_to_bv 64 (kk + 1)) (Z_to_bv 64 (shad f)) t3 t4 t5 t6)
        F (Z_to_bv 64 0xaf854) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros OK K0 KB BN N32 KIND QLO LOQ QH AI CC ST SHZ0 FR MI.
  pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L (T16 & NT8 & TN & TS & TL) _ _ _ (D8 & DF & DL & DS & DT) LOW [HL HT]].
  unfold USTACK_TOP in HT. unfold SEGTOP_A in *. assert (HSN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia).
  assert (SHZT : forall m', munch [(q - 272, q - 256)] m m' -> wmono bsegs m m' -> shz m' (ae_TAPE E) (8 * ae_n E)).
  { intros m' MU' _. eapply shz_munch_hi; [exact SHZ0| exact MU'| lia| lia|]. intros y Hy. cbn [outside]. repeat (split; try exact I); lia. }
  clear SHZ0.
  assert (FS0 : 0 <= fs_size (ae_kD E)) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
  assert (ED : bv_unsigned (Z_to_bv 64 (ae_DOC E)) = ae_DOC E) by (apply unsigned_lit; lia).
  assert (EK : bv_unsigned (Z_to_bv 64 kk) = kk) by (apply unsigned_lit; lia).
  assert (EK1 : bv_unsigned (Z_to_bv 64 (kk + 1)) = kk + 1) by (apply unsigned_lit; lia).
  assert (ESP : bv_unsigned (Z_to_bv 64 (q - 256)) = q - 256) by (apply unsigned_lit; lia).
  assert (ED8 : bv_unsigned (Z_to_bv 64 (ae_DOC E + 8)) = ae_DOC E + 8) by (apply unsigned_lit; lia).
  unfold pjRO, pj_oframe, DMP_PJ_OTEST_A, DMP_LIT_RBRC_A, DMP_LIT_QUOT_A, DMP_LIT_QCOL_A, shad, SHB in *.
  pose proof (munch_refl [(q - 272, q - 256)] m) as MU. pose proof (wmono_refl bsegs m) as WM.

  os_walk 20.
  oh_tix 0xaf860.
  match goal with A : AINV_A E ?mm, MUx : munch _ m ?mm |- _ =>
    pose proof A as (TAPEB & _ & _ & _ & _);
    pose proof (tape_read _ (ae_TAPE E) (ae_tws E) (kk + 1) TAPEB ltac:(lia)) as RDT;
    pose proof (tape_read4A mm (ae_TAPE E) (ae_tws E) (kk + 1) TAPEB ltac:(lia)) as RD4 end.
  shz_pose SHZT (ae_TAPE E + 8 * (kk + 1)).
  os_walk 30.
  destruct KIND as [[-> TY]|[[-> TY]|[[-> STRI]|(cv & CV & CO)]]].
  - destruct TY as [E'|[E'|E']];
      (assert (TIR : 0 <= ae_T E (kk + 1) < 2^64) by (rewrite E'; unfold tword, t_true, t_false, t_null; lia));
      pose proof (tape_read_typeA _ (ae_TAPE E) (ae_tws E) (kk + 1) TAPEB ltac:(lia) TIR) as RTY;
      rewrite E' in RTY, RDT, RD4; rewrite ttype_tword in RTY by lia; unfold t_true, t_false, t_null in RTY.
    all: os_walk 40.
    all: os_done.
  - destruct TY as [E'|[E'|E']];
      (assert (TIR : 0 <= ae_T E (kk + 1) < 2^64) by (rewrite E'; unfold tword, t_i64, t_u64, t_dbl; lia));
      pose proof (tape_read_typeA _ (ae_TAPE E) (ae_tws E) (kk + 1) TAPEB ltac:(lia) TIR) as RTY;
      rewrite E' in RTY, RDT, RD4; rewrite ttype_tword in RTY by lia; unfold t_i64, t_u64, t_dbl in RTY.
    all: os_walk 40.
    all: os_done.
  - pose proof (key_word_rangeA _ _ _ _ STRI HSN) as (TIR & _ & KT).
    pose proof (tape_read_typeA _ (ae_TAPE E) (ae_tws E) (kk + 1) TAPEB ltac:(lia) TIR) as RTY.
    rewrite KT in RTY. unfold t_str in RTY.
    os_walk 40.
    os_done.
  - unfold CNT_MAX in CV.
    destruct CO as [E'|E'];
      (assert (TIR : 0 <= ae_T E (kk + 1) < 2^64) by (rewrite E'; unfold cword, tword, t_arr, t_obj; lia));
      pose proof (tape_read_typeA _ (ae_TAPE E) (ae_tws E) (kk + 1) TAPEB ltac:(lia) TIR) as RTY;
      rewrite E' in RTY; rewrite ttype_cword in RTY by (unfold CNT_MAX; lia); unfold t_arr, t_obj in RTY.
    all: os_walk 40.
    all: clear RDT RD4 TAPEB.
    all: oh_tix 0xaf8bc.
    all: match goal with A : AINV_A _ ?mm, MUx : munch _ _ ?mm |- _ =>
      pose proof A as (TAPEB & _ & _ & _ & _);
      pose proof (tape_read _ (ae_TAPE E) (ae_tws E) (kk + 1) TAPEB ltac:(lia)) as RDT end.
    all: rewrite E' in RDT.
    all: shz_pose SHZT (ae_TAPE E + 8 * (kk + 1)).
    all: os_walk 40.
    all: rewrite ?low32_cwordA' by (unfold t_arr, t_obj, CNT_MAX; lia).
    all: os_done.
Unshelve. all: exact (Z_to_bv 64 0).
Qed.
