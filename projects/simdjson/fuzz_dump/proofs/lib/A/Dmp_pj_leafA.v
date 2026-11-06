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
     Atp_defsA Pj_defsA El_defsA Dmp_hdefsA Dmp_pj_ifaceA Dmp_pj_kitA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition DMP_PJ_PUT_A : Z := 0xb0b14.
Definition DMP_LIT_NULL_A : Z := 0x23460.
Definition pjR (q f : Z) (gp ra a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 : word) : bvmap 5 word :=
  mkR ra (Z_to_bv 64 (q - 256)) gp (Z_to_bv 64 TPV_A) t0 t1 t2 (Z_to_bv 64 q) (Z_to_bv 64 (q - 256)) a0 a1 a2 a3 a4 a5 a6 a7
      (Z_to_bv 64 SHB) (Z_to_bv 64 f) s4 s5 s6 (Z_to_bv 64 f) s8 s9 (Z_to_bv 64 (shad f)) s11 t3 t4 t5 t6.

Definition pj_slot (f k : Z) : Z := f + (32 + 16 * k).
Definition pj_gofs (k : Z) : Z := 4 + 2 * k.

Definition pj_endl_pc (k : Z) : Z :=
  match k with 1 => 0xaf2f0 | 2 => 0xaf468 | 3 => 0xaf57c | 4 => 0xaf2a4 | 5 => 0xaf50c | 6 => 0xaf4bc | _ => 0xaf544 end.

Ltac pj_endl_consts f :=
  lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc0) _ _ _ _) =>
    lazymatch pc0 with context [pj_endl_pc ?k] =>
      let v := eval cbv in (32 + 16 * k) in change (pj_slot f k) with (f + v) in *;
      let g := eval cbv in (pj_gofs k) in change (pj_gofs k) with g in *;
      let p := eval cbv in (pj_endl_pc k) in
      let p' := eval cbv in (p + 28) in
      change (pj_endl_pc k + 28) with p' in *; change (pj_endl_pc k) with p in *
    end end.

Lemma pj_endl1 : forall (k q f : Z) (gp ra a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 : word) (g b : list byte) F fc (m : mem),
  1 <= k <= 6 -> 0 < f -> f + 256 < 2^63 -> 0 <= shad f -> shad f + 32 < 2^63 -> (f + 256 <= shad f \/ shad f + 32 <= f) ->
  rw_cells asegs m (shad f + pj_gofs k) [CB 1 g] -> rw_cells asegs m (pj_slot f k) [CB 1 b] -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m' : mem),
      ms = MS (pjR q f gp (Z_to_bv 64 (pj_endl_pc k + 28)) a0 (Z_to_bv 64 (pj_slot f k)) (Z_to_bv 64 1) a3 a4 a5 a6 a7 s4 s5 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6)
              F (Z_to_bv 64 DMP_PJ_PUT_A) fc None m' (seg_rom asegs)
      /\ munch [(shad f + pj_gofs k, shad f + pj_gofs k + 1); (pj_slot f k, pj_slot f k + 1)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ rw_cells asegs m' (shad f + pj_gofs k) [C1 (Z_to_bv 8 1)] /\ rw_cells asegs m' (pj_slot f k) [C1 (Z_to_bv 8 10)])
    (MS (pjR q f gp ra a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6) F (Z_to_bv 64 (pj_endl_pc k)) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros K F0 FH SH0 SHH SEP FG FB MI.
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 (shad f)) = shad f) by (apply unsigned_lit; lia).
  unfold pjR, DMP_PJ_PUT_A.
  assert (KC : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6) by lia. clear K.
  destruct KC as [-> |[-> |[-> |[-> |[-> | ->]]]]]; pj_endl_consts f;
  (pose proof (wmono_refl asegs m) as WM;
   lazymatch goal with |- evt _ (fun _ => exists _, _ /\ (munch ?W _ _ /\ _)) _ => pose proof (munch_refl W m) as MU end;

   zstep; zstep; ls; zstep; ls; zstep; zstep;
   apply evt_done; eexists; split; [cbv delta [mkR]; reflexivity|];
   split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]; split; [exact WM|]; split; [eassumption|]; split; eassumption).
Qed.

Lemma pj_endl2 : forall (k q f : Z) (gp ra a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 : word) (g : list byte) F fc (m : mem),
  1 <= k <= 6 -> 0 <= shad f -> shad f + 32 < 2^63 ->
  rw_cells asegs m (shad f + pj_gofs k) [CB 1 g] -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m' : mem) (a0' : word),
      ms = MS (pjR q f gp ra a0' a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6) F (Z_to_bv 64 DMP_PJ_EXIT_A) fc None m' (seg_rom asegs)
      /\ munch [(shad f + pj_gofs k, shad f + pj_gofs k + 1)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ rw_cells asegs m' (shad f + pj_gofs k) [C1 (Z_to_bv 8 (-8))])
    (MS (pjR q f gp ra a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6) F (Z_to_bv 64 (pj_endl_pc k + 28)) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros K SH0 SHH FG MI.
  assert (ES : bv_unsigned (Z_to_bv 64 (shad f)) = shad f) by (apply unsigned_lit; lia).
  unfold pjR, DMP_PJ_EXIT_A.
  assert (KC : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6) by lia. clear K.
  destruct KC as [-> |[-> |[-> |[-> |[-> | ->]]]]]; pj_endl_consts f;
  (pose proof (wmono_refl asegs m) as WM;
   lazymatch goal with |- evt _ (fun _ => exists _ _, _ /\ (munch ?W _ _ /\ _)) _ => pose proof (munch_refl W m) as MU end;

   zstep; ls; zstep;
   apply evt_done; do 2 eexists; split; [cbv delta [mkR]; reflexivity|];
   split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]; split; [exact WM|]; split; [eassumption|]; eassumption).
Qed.

Lemma pj_null1 : forall (E : aenvA) (q f osp i : Z) (gp ra a0 a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 : word) F fc (m : mem),
  aenvA_ok E -> 0 <= i < ae_n E -> 0 <= ae_T E i < 2^64 -> ttype (ae_T E i) = 110 ->
  0x6c9000 <= q - 256 -> q < 2^63 -> 0 <= osp < 2^64 ->
  AINV_A E m -> shz m (ae_TAPE E) (8 * ae_n E) ->
  rw_cells asegs m (q - 256 + 120) [C8 (Z_to_bv 64 osp)] -> mem_inv asegs m ->
  evt asegs (fun ms =>
      ms = MS (pjR q f gp (Z_to_bv 64 (pj_endl_pc 1)) (Z_to_bv 64 osp) (Z_to_bv 64 DMP_LIT_NULL_A) (Z_to_bv 64 4) (Z_to_bv 64 108) a4 a5 a6 a7
                   (Z_to_bv 64 (ae_DOC E)) (Z_to_bv 64 i) (Z_to_bv 64 (8 * i)) s8 s9 s11 t0 t1 t2 t3 t4 t5 t6)
              F (Z_to_bv 64 DMP_PJ_PUT_A) fc None m (seg_rom asegs))
    (MS (pjR q f gp ra a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (ae_DOC E)) (Z_to_bv 64 i) s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6)
        F (Z_to_bv 64 DMP_PJ_DISP_A) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros OK IR TR TY QLO QH OR AI SHZT FO MI.
  pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L (T16 & NT8 & TN & TS & TL) _ _ _ (D8 & DF & DL & DS & DT) LOW [HL HT]].
  unfold USTACK_TOP in HT. unfold SEGTOP_A in *.
  pose proof AI as (TAPEB & _ & _ & DOCC & _).
  assert (FS0 : 0 <= fs_size (ae_kD E)) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
  assert (ED : bv_unsigned (Z_to_bv 64 (ae_DOC E)) = ae_DOC E) by (apply unsigned_lit; lia).
  assert (EI : bv_unsigned (Z_to_bv 64 i) = i) by (apply unsigned_lit; lia).
  assert (ESP : bv_unsigned (Z_to_bv 64 (q - 256)) = q - 256) by (apply unsigned_lit; lia).
  unfold pjR, DMP_PJ_DISP_A, DMP_PJ_PUT_A, DMP_LIT_NULL_A. cbn [pj_endl_pc].
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (tape_read _ (ae_TAPE E) (ae_tws E) i TAPEB ltac:(lia)) as RDT.

  zstep. astep. astep.

  chk0 SHZT (ae_TAPE E + 8 * i). step. if_false.

  step. astep. first [change (ae_T E i / 2 ^ 56) with (ttype (ae_T E i)) | idtac]. rewrite TY.

  step. step. if_true. step. step. if_false. step. step. if_true. step. step. if_false. step. step. if_false.

  zstep. zstep. zstep. zstep. zstep.
  apply evt_done. atp_st_eq_goal.
Qed.

Definition DMP_INS_B_A : Z := 0x105770.  Definition DMP_INS_L_A : Z := 0x10593c.  Definition DMP_INS_UL_A : Z := 0x105b08.  Definition DMP_INS_D_A : Z := 0x105cd4.
Definition pj_boolv (w : Z) : Z := if w =? 116 * 2^56 then 1 else 0.

Lemma pj_boolv_xor : forall w, 0 <= w -> Z.b2z (Z.lxor w 8358680908399640576 <? 1) = pj_boolv w.
Proof.
  intros w W. unfold pj_boolv. change (116 * 2^56) with 8358680908399640576.
  destruct (Z.eqb_spec w 8358680908399640576) as [->|NE].
  - rewrite Z.lxor_nilpotent. reflexivity.
  - assert (0 <= Z.lxor w 8358680908399640576) by (apply (proj2 (Z.lxor_nonneg _ _)); lia).
    assert (Z.lxor w 8358680908399640576 <> 0) by (intros H0; apply NE; apply Z.lxor_eq; exact H0).
    destruct (Z.ltb_spec (Z.lxor w 8358680908399640576) 1); [lia| reflexivity].
Qed.

Lemma pj_bool1 : forall (E : aenvA) (q f osp i : Z) (gp ra a0 a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 : word) F fc (m : mem),
  aenvA_ok E -> 0 <= i < ae_n E -> 0 <= ae_T E i < 2^64 -> (ttype (ae_T E i) = 116 \/ ttype (ae_T E i) = 102) ->
  0x6c9000 <= q - 256 -> q < 2^63 -> 0 <= osp < 2^64 ->
  AINV_A E m -> shz m (ae_TAPE E) (8 * ae_n E) ->
  rw_cells asegs m (q - 256 + 120) [C8 (Z_to_bv 64 osp)] -> mem_inv asegs m ->
  evt asegs (fun ms =>
      ms = MS (pjR q f gp (Z_to_bv 64 (pj_endl_pc 2)) (Z_to_bv 64 osp) (Z_to_bv 64 (pj_boolv (ae_T E i))) (Z_to_bv 64 116) (Z_to_bv 64 116) a4 a5 a6 a7
                   (Z_to_bv 64 (ae_DOC E)) (Z_to_bv 64 i) (Z_to_bv 64 (8 * i)) s8 s9 s11 t0 t1 t2 t3 t4 t5 t6)
              F (Z_to_bv 64 DMP_INS_B_A) fc None m (seg_rom asegs))
    (MS (pjR q f gp ra a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (ae_DOC E)) (Z_to_bv 64 i) s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6)
        F (Z_to_bv 64 DMP_PJ_DISP_A) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros OK IR TR TY QLO QH OR AI SHZT FO MI.
  pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L (T16 & NT8 & TN & TS & TL) _ _ _ (D8 & DF & DL & DS & DT) LOW [HL HT]].
  unfold USTACK_TOP in HT. unfold SEGTOP_A in *.
  pose proof AI as (TAPEB & _ & _ & DOCC & _).
  assert (FS0 : 0 <= fs_size (ae_kD E)) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
  assert (ED : bv_unsigned (Z_to_bv 64 (ae_DOC E)) = ae_DOC E) by (apply unsigned_lit; lia).
  assert (EI : bv_unsigned (Z_to_bv 64 i) = i) by (apply unsigned_lit; lia).
  assert (ESP : bv_unsigned (Z_to_bv 64 (q - 256)) = q - 256) by (apply unsigned_lit; lia).
  unfold pjR, DMP_PJ_DISP_A, DMP_INS_B_A. cbn [pj_endl_pc].
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (tape_read _ (ae_TAPE E) (ae_tws E) i TAPEB ltac:(lia)) as RDT.

  zstep. astep. astep.
  chk0 SHZT (ae_TAPE E + 8 * i). step. if_false.
  step. astep. first [change (ae_T E i / 2 ^ 56) with (ttype (ae_T E i)) | idtac].
  destruct TY as [TY|TY]; rewrite TY.
  -
    step. step. if_true. step. step. if_false. step. step. if_false. step. step. if_true.

    zstep. zstep. zstep. zstep. zstep. zstep. rewrite (pj_boolv_xor (ae_T E i)) by lia.
    apply evt_done. atp_st_eq_goal.
  -
    step. step. if_false. step. step. step. if_false. step. step. if_false. step. step. if_true.
    zstep. zstep. zstep. zstep. zstep. zstep. rewrite (pj_boolv_xor (ae_T E i)) by lia.
    apply evt_done. atp_st_eq_goal.
Qed.

Definition pj_num_ins (t : Z) : Z := if t =? 108 then DMP_INS_L_A else DMP_INS_UL_A.
Definition pj_num_slot (t : Z) : Z := if t =? 108 then 6 else 5.

Lemma pj_num1 : forall (E : aenvA) (t q f osp i : Z) (gp ra a0 a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 : word) F fc (m : mem),
  aenvA_ok E -> 0 <= i -> i + 1 < ae_n E -> (t = 108 \/ t = 117) -> ae_T E i = t * 2^56 ->
  0x6c9000 <= q - 256 -> q < 2^63 -> 0 <= osp < 2^64 ->
  AINV_A E m -> shz m (ae_TAPE E) (8 * ae_n E) ->
  rw_cells asegs m (q - 256 + 120) [C8 (Z_to_bv 64 osp)] -> mem_inv asegs m ->
  evt asegs (fun ms => exists (a2x a3x : word),
      ms = MS (pjR q f gp (Z_to_bv 64 (pj_endl_pc (pj_num_slot t))) (Z_to_bv 64 osp) (Z_to_bv 64 (ae_T E (i + 1))) a2x a3x a4 a5 a6 a7
                   (Z_to_bv 64 (ae_DOC E)) (Z_to_bv 64 i) (Z_to_bv 64 (8 * i)) s8 s9 s11 t0 t1 t2 t3 t4 t5 t6)
              F (Z_to_bv 64 (pj_num_ins t)) fc None m (seg_rom asegs))
    (MS (pjR q f gp ra a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (ae_DOC E)) (Z_to_bv 64 i) s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6)
        F (Z_to_bv 64 DMP_PJ_DISP_A) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros OK I0 IR TY WX QLO QH OR AI SHZT FO MI.
  pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L (T16 & NT8 & TN & TS & TL) _ _ _ (D8 & DF & DL & DS & DT) LOW [HL HT]].
  unfold USTACK_TOP in HT. unfold SEGTOP_A in *.
  pose proof AI as (TAPEB & _ & _ & DOCC & _).
  assert (FS0 : 0 <= fs_size (ae_kD E)) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
  assert (ED : bv_unsigned (Z_to_bv 64 (ae_DOC E)) = ae_DOC E) by (apply unsigned_lit; lia).
  assert (EI : bv_unsigned (Z_to_bv 64 i) = i) by (apply unsigned_lit; lia).
  assert (ESP : bv_unsigned (Z_to_bv 64 (q - 256)) = q - 256) by (apply unsigned_lit; lia).
  unfold pjR, DMP_PJ_DISP_A, pj_num_ins, pj_num_slot, DMP_INS_L_A, DMP_INS_UL_A.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (tape_read _ (ae_TAPE E) (ae_tws E) i TAPEB ltac:(lia)) as RDT.
  pose proof (tape_read _ (ae_TAPE E) (ae_tws E) (i + 1) TAPEB ltac:(lia)) as RDT1.
  replace (ae_TAPE E + 8 * (i + 1)) with (ae_TAPE E + 8 * i + 8) in RDT1 by lia.

  zstep. astep. astep.
  chk0 SHZT (ae_TAPE E + 8 * i). step. if_false.
  step. rewrite WX. destruct TY as [-> | ->]; cbn [Z.eqb Pos.eqb pj_endl_pc]; zstep.
  -
    step. step. if_true. step. step. if_false. step. step. if_true. step. step. if_true.

    zstep. zstep. step. if_false. zstep.
    chk0 SHZT (ae_TAPE E + 8 * i + 8). step. if_false.
    step. zstep. zstep.
    apply evt_done. do 2 eexists. atp_st_eq_goal.
  -
    step. step. if_true. step. step. if_false. step. step. if_false. step. step. if_false. step. step. if_true.

    zstep. step. if_false. zstep.
    chk0 SHZT (ae_TAPE E + 8 * i + 8). step. if_false.
    step. zstep. zstep.
    apply evt_done. do 2 eexists. atp_st_eq_goal.
Qed.

Lemma pj_dbl1 : forall (E : aenvA) (q f osp i : Z) (gp ra a0 a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 : word) F fc (m : mem),
  aenvA_ok E -> 0 <= i -> i + 1 < ae_n E -> ae_T E i = 100 * 2^56 ->
  0x6c9000 <= q - 256 -> q < 2^63 -> 0 <= osp < 2^64 ->
  AINV_A E m -> shz m (ae_TAPE E) (8 * ae_n E) ->
  rw_cells asegs m (q - 256 + 120) [C8 (Z_to_bv 64 osp)] -> mem_inv asegs m ->
  evt asegs (fun ms => exists (a1x a2x a3x : word),
      ms = MS (pjR q f gp (Z_to_bv 64 (pj_endl_pc 4)) (Z_to_bv 64 osp) a1x a2x a3x a4 a5 a6 a7
                   (Z_to_bv 64 (ae_DOC E)) (Z_to_bv 64 i) (Z_to_bv 64 (8 * i)) s8 s9 s11 t0 t1 t2 t3 t4 t5 t6)
              (bvmap_set 10 (Z_to_bv 64 (ae_T E (i + 1))) F) (Z_to_bv 64 DMP_INS_D_A) fc None m (seg_rom asegs))
    (MS (pjR q f gp ra a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (ae_DOC E)) (Z_to_bv 64 i) s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6)
        F (Z_to_bv 64 DMP_PJ_DISP_A) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros OK I0 IR WX QLO QH OR AI SHZT FO MI.
  pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L (T16 & NT8 & TN & TS & TL) _ _ _ (D8 & DF & DL & DS & DT) LOW [HL HT]].
  unfold USTACK_TOP in HT. unfold SEGTOP_A in *.
  pose proof AI as (TAPEB & _ & _ & DOCC & _).
  assert (FS0 : 0 <= fs_size (ae_kD E)) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
  assert (ED : bv_unsigned (Z_to_bv 64 (ae_DOC E)) = ae_DOC E) by (apply unsigned_lit; lia).
  assert (EI : bv_unsigned (Z_to_bv 64 i) = i) by (apply unsigned_lit; lia).
  assert (ESP : bv_unsigned (Z_to_bv 64 (q - 256)) = q - 256) by (apply unsigned_lit; lia).
  unfold pjR, DMP_PJ_DISP_A, DMP_INS_D_A. cbn [pj_endl_pc].
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (tape_read _ (ae_TAPE E) (ae_tws E) i TAPEB ltac:(lia)) as RDT.
  pose proof (tape_read _ (ae_TAPE E) (ae_tws E) (i + 1) TAPEB ltac:(lia)) as RDT1.
  replace (ae_TAPE E + 8 * (i + 1)) with (ae_TAPE E + 8 * i + 8) in RDT1 by lia.
  zstep. astep. astep.
  chk0 SHZT (ae_TAPE E + 8 * i). step. if_false.
  step. rewrite WX. zstep.

  step. step. if_true. step. step. if_true. step. step. if_true. step. step. if_false. step. step. if_false.

  zstep. zstep. step. if_false. zstep.
  chk0 SHZT (ae_TAPE E + 8 * i + 8). step. if_false.
  step. zstep. zstep.
  apply evt_done. do 3 eexists. atp_st_eq_goal.
Qed.

Definition DMP_LIT_LBRK_A : Z := 0x234c0.  Definition DMP_LIT_LBRC_A : Z := 0x23520.
Definition pj_open_lit (t : Z) : Z := if t =? 91 then DMP_LIT_LBRK_A else DMP_LIT_LBRC_A.
Definition pj_open_ret (t : Z) : Z := if t =? 91 then 0xaf3ac else 0xaf124.

Lemma pj_open1 : forall (E : aenvA) (t q f osp i : Z) (gp ra a0 a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 : word) F fc (m : mem),
  aenvA_ok E -> 0 <= i < ae_n E -> 0 <= ae_T E i < 2^64 -> ttype (ae_T E i) = t -> (t = 91 \/ t = 123) ->
  0x6c9000 <= q - 256 -> q < 2^63 -> 0 <= osp < 2^64 ->
  AINV_A E m -> shz m (ae_TAPE E) (8 * ae_n E) ->
  rw_cells asegs m (q - 256 + 120) [C8 (Z_to_bv 64 osp)] -> mem_inv asegs m ->
  evt asegs (fun ms => exists (a3x : word),
      ms = MS (pjR q f gp (Z_to_bv 64 (pj_open_ret t)) (Z_to_bv 64 osp) (Z_to_bv 64 (pj_open_lit t)) (Z_to_bv 64 1) a3x a4 a5 a6 a7
                   (Z_to_bv 64 (ae_DOC E)) (Z_to_bv 64 i) (Z_to_bv 64 (8 * i)) s8 s9 s11 t0 t1 t2 t3 t4 t5 t6)
              F (Z_to_bv 64 DMP_PJ_PUT_A) fc None m (seg_rom asegs))
    (MS (pjR q f gp ra a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (ae_DOC E)) (Z_to_bv 64 i) s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6)
        F (Z_to_bv 64 DMP_PJ_DISP_A) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros OK IR TR TY TT QLO QH OR AI SHZT FO MI.
  pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L (T16 & NT8 & TN & TS & TL) _ _ _ (D8 & DF & DL & DS & DT) LOW [HL HT]].
  unfold USTACK_TOP in HT. unfold SEGTOP_A in *.
  pose proof AI as (TAPEB & _ & _ & DOCC & _).
  assert (FS0 : 0 <= fs_size (ae_kD E)) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
  assert (ED : bv_unsigned (Z_to_bv 64 (ae_DOC E)) = ae_DOC E) by (apply unsigned_lit; lia).
  assert (EI : bv_unsigned (Z_to_bv 64 i) = i) by (apply unsigned_lit; lia).
  assert (ESP : bv_unsigned (Z_to_bv 64 (q - 256)) = q - 256) by (apply unsigned_lit; lia).
  unfold pjR, DMP_PJ_DISP_A, DMP_PJ_PUT_A, pj_open_lit, pj_open_ret, DMP_LIT_LBRK_A, DMP_LIT_LBRC_A.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (tape_read _ (ae_TAPE E) (ae_tws E) i TAPEB ltac:(lia)) as RDT.
  zstep. astep. astep.
  chk0 SHZT (ae_TAPE E + 8 * i). step. if_false.
  step. astep. first [change (ae_T E i / 2 ^ 56) with (ttype (ae_T E i)) | idtac]. rewrite TY.
  destruct TT as [-> | ->]; cbn [Z.eqb Pos.eqb].
  -
    step. step. if_true. step. step. if_true. step. step. if_true. step. step. if_true.
    zstep. zstep. zstep. zstep. zstep.
    apply evt_done. eexists. atp_st_eq_goal.
  -
    step. step. if_true. step. step. if_false. step. step. if_false. step. step. if_false. step. step. if_false. step. step. if_false.
    zstep. zstep. zstep. zstep. zstep.
    apply evt_done. eexists. atp_st_eq_goal.
Qed.

Lemma pj_close0 : forall (q f osp : Z) (gp ra a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 : word) F fc (m : mem),
  0x6c9000 <= q - 256 -> q < 2^63 -> 0 <= osp < 2^64 ->
  rw_cells asegs m (q - 256 + 120) [C8 (Z_to_bv 64 osp)] -> mem_inv asegs m ->
  evt asegs (fun ms =>
      ms = MS (pjR q f gp (Z_to_bv 64 DMP_PJ_EXIT_A) (Z_to_bv 64 osp) a1 (Z_to_bv 64 1) a3 a4 a5 a6 a7 s4 s5 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6)
              F (Z_to_bv 64 DMP_PJ_PUT_A) fc None m (seg_rom asegs))
    (MS (pjR q f gp ra a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6) F (Z_to_bv 64 DMP_PJ_CLOSE_A) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros QLO QH OR FO MI.
  assert (ESP : bv_unsigned (Z_to_bv 64 (q - 256)) = q - 256) by (apply unsigned_lit; lia).
  unfold pjR, DMP_PJ_CLOSE_A, DMP_PJ_PUT_A, DMP_PJ_EXIT_A.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. zstep. zstep. apply evt_done. atp_st_eq_goal.
Qed.

Lemma pj_close1 : forall (q f osp lit : Z) (gp ra a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 : word) F fc (m : mem),
  0x6c9000 <= q - 256 -> q < 2^63 -> 0 <= osp < 2^64 -> 0 <= lit < 2^64 -> 0 < f -> f + 256 < 2^63 ->
  rw_cells asegs m (q - 256 + 24) [C8 (Z_to_bv 64 lit); C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 f)] ->
  rw_cells asegs m (q - 256 + 120) [C8 (Z_to_bv 64 osp)] -> mem_inv asegs m ->
  evt asegs (fun ms =>
      ms = MS (pjR q f gp (Z_to_bv 64 DMP_PJ_EXIT_A) (Z_to_bv 64 osp) (Z_to_bv 64 lit) (Z_to_bv 64 1) a3 a4 a5 a6 a7 s4 s5 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6)
              F (Z_to_bv 64 DMP_PJ_PUT_A) fc None m (seg_rom asegs))
    (MS (mkR ra (Z_to_bv 64 (q - 256)) gp (Z_to_bv 64 TPV_A) t0 t1 t2 (Z_to_bv 64 q) (Z_to_bv 64 (q - 256)) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 SHB) s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 (shad f)) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 DMP_PJ_LOOPX_A) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros QLO QH OR LR F0 FH FR FO MI.
  assert (ESP : bv_unsigned (Z_to_bv 64 (q - 256)) = q - 256) by (apply unsigned_lit; lia).
  unfold pjR, DMP_PJ_LOOPX_A, DMP_PJ_PUT_A, DMP_PJ_EXIT_A.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.

  pose proof (proj1 (rw_cells_app asegs m (q - 256 + 24) [_] [_; _]) FR) as [F24 X2].
  cbn [cells_size csize Nat.add app] in X2. replace (q - 256 + 24 + Z.of_nat 8) with (q - 256 + 32) in X2 by lia.
  pose proof (proj1 (rw_cells_app asegs m (q - 256 + 32) [_] [_]) X2) as [F32 F40]. clear X2.
  cbn [cells_size csize Nat.add app] in F40. replace (q - 256 + 32 + Z.of_nat 8) with (q - 256 + 40) in F40 by lia.

  zstep. zstep. zstep. zstep. zstep. zstep. zstep. apply evt_done. atp_st_eq_goal.
Qed.
