From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.Riscv Require Import Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import check_reject_clean_starved_c CrsHash CrsSegA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require
  fuzz_alloc_live_c fuzz_alloc_count_c fuzz_alloc_fail_c fuzz_alloc_ran_out_c fuzz_alloc_ran_out LedgerCells.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import SRCF.
Import ListNotations.
Open Scope Z_scope.

Lemma crsb_remu : forall a b, 0 <= a < 2 ^ 64 -> 0 < b < 2 ^ 64 ->
  mul_div M_REMU (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a mod b).
Proof.
  intros a b Ha Hb. unfold mul_div. rewrite (unsigned_lit b) by lia.
  replace (b =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  pose proof (Z.mod_pos_bound a b ltac:(lia)) as R.
  apply bv_eq. rewrite bv_modu_unsigned. rewrite !unsigned_lit by lia. reflexivity.
Qed.

Lemma crsb_djb2_range : forall x h, 0 <= h < 2 ^ 64 -> 0 <= djb2 h x < 2 ^ 64.
Proof.
  induction x as [|c r IH]; intros h Hh; cbn [djb2]; [exact Hh|].
  apply IH. apply Z.mod_pos_bound. lia.
Qed.

Lemma crsb_pick : forall x n, 0 < n -> pick x n = djb2 5381 x mod n.
Proof. intros x n Hn. unfold pick. rewrite (proj2 (Z.eqb_neq n 0)) by lia. reflexivity. Qed.

Lemma crsb_tr : forall m m' A v,
  munch [(fuzz_alloc_fail_c.G_FAIL_AT, fuzz_alloc_fail_c.G_FAIL_AT + 8)] m m' ->
  A + 8 <= fuzz_alloc_fail_c.G_FAIL_AT \/ fuzz_alloc_fail_c.G_FAIL_AT + 8 <= A ->
  bytes_at rsegs m A (le8 v) -> bytes_at rsegs m' A (le8 v).
Proof.
  intros m m' A v MU D H. eapply bytes_at_transport; [exact H | exact MU |].
  cbn [disjoint_from]. rewrite length_le8. split; [lia | exact I].
Qed.

Lemma crsb_tr1 : forall m m' A v,
  munch [(fuzz_alloc_fail_c.G_FAIL_AT, fuzz_alloc_fail_c.G_FAIL_AT + 8)] m m' ->
  A + 1 <= fuzz_alloc_fail_c.G_FAIL_AT \/ fuzz_alloc_fail_c.G_FAIL_AT + 8 <= A ->
  bytes_at rsegs m A (le1 v) -> bytes_at rsegs m' A (le1 v).
Proof.
  intros m m' A v MU D H. eapply bytes_at_transport; [exact H | exact MU |].
  cbn [disjoint_from]. rewrite length_le1. split; [lia | exact I].
Qed.

Lemma crsb_cells_tr : forall m m' S xra xs0 xs1 xs2 xs3 xs4 xs5,
  munch [(fuzz_alloc_fail_c.G_FAIL_AT, fuzz_alloc_fail_c.G_FAIL_AT + 8)] m m' -> 0x56000 <= S - 112 ->
  crs_cells m S xra xs0 xs1 xs2 xs3 xs4 xs5 -> crs_cells m' S xra xs0 xs1 xs2 xs3 xs4 xs5.
Proof.
  intros m m' S xra xs0 xs1 xs2 xs3 xs4 xs5 MU HS (C1 & C2 & C3 & C4 & C5 & C6 & C7).
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))); eapply crsb_tr; try eassumption;
    unfold fuzz_alloc_fail_c.G_FAIL_AT; lia.
Qed.

(* the two flag cells lie apart from g_fail_at, so a fuzz_alloc_fail call keeps them *)
Lemma crsb_flags_tr : forall m m',
  munch [(fuzz_alloc_fail_c.G_FAIL_AT, fuzz_alloc_fail_c.G_FAIL_AT + 8)] m m' ->
  bytes_at rsegs m LedgerCells.GL_OWN_RAN_OUT (le1 (Z_to_bv 64 0)) ->
  bytes_at rsegs m fuzz_alloc_ran_out_c.G_RAN_OUT (le1 (Z_to_bv 64 0)) ->
  bytes_at rsegs m' LedgerCells.GL_OWN_RAN_OUT (le1 (Z_to_bv 64 0)) /\
  bytes_at rsegs m' fuzz_alloc_ran_out_c.G_RAN_OUT (le1 (Z_to_bv 64 0)).
Proof.
  intros m m' MU HO HR.
  split; (eapply crsb_tr1; [exact MU | | eassumption]);
    unfold fuzz_alloc_fail_c.G_FAIL_AT, LedgerCells.GL_OWN_RAN_OUT, fuzz_alloc_ran_out_c.G_RAN_OUT; lia.
Qed.

Ltac crsb_ret :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity])
  end.

(* out_of_memory() at a test of the walk: the lbu of g_own_ran_out through s5 and its bnez, the call of
   fuzz_alloc_ran_out and its branch (taken iff the flag is set: `bnez` falls through, `beqz` jumps). *)
Ltac crsb_oom HO HR :=
  let RD := fresh "RD" in
  pose proof (crs_rd1 _ _ _ HO) as RD; unfold LedgerCells.GL_OWN_RAN_OUT in RD;
  step; step; if_false;
  step;
  eapply evt_cut; [eapply fuzz_alloc_ran_out.fuzz_alloc_ran_out_holds; [exact crs_zero8 | exact HR]|];
  let ms' := fresh "ms'" in intros ms' ->; crsb_ret;
  clear RD.

(* after the pretty full write and its fuzz_free: the count test, out_of_memory(), fuzz_alloc_count, fuzz_pick
   inlined (djb2 of the input mod the writer's calls), fuzz_alloc_fail and the call of the starved pj_write(doc, 1). *)
Lemma crs_s4 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (data before cnt : Z) (tb : list byte),
  fuzz_alloc_count_c.fuzz_alloc_count_contract -> fuzz_alloc_fail_c.fuzz_alloc_fail_contract ->
  bytes_at rsegs m fuzz_alloc_fail_c.G_COUNT (le8 (Z_to_bv 64 cnt)) -> 0 <= before < cnt -> cnt < 2 ^ 64 ->
  wr_at rsegs m fuzz_alloc_fail_c.G_FAIL_AT 8 ->
  bytes_at rsegs m data tb -> data + Z.of_nat (length tb) < 2 ^ 64 -> 0 < data ->
  bytes_at rsegs m LedgerCells.GL_OWN_RAN_OUT (le1 (Z_to_bv 64 0)) ->
  bytes_at rsegs m fuzz_alloc_ran_out_c.G_RAN_OUT (le1 (Z_to_bv 64 0)) ->
  evt rsegs
    (fun ms' => exists (t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
       ms' = MS (mkR (Z_to_bv 64 0x13dbc) sp gp tp t0' t1' t2' s0 s1 s1 (Z_to_bv 64 1) a2' a3' a4' a5' a6' a7'
                     (Z_to_bv 64 (Z.of_nat (length tb))) (Z_to_bv 64 data) (Z_to_bv 64 before)
                     (Z_to_bv 64 CRS_S5) s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x16838) fc None m' (seg_rom rsegs) /\
       munch [(fuzz_alloc_fail_c.G_FAIL_AT, fuzz_alloc_fail_c.G_FAIL_AT + 8)] m m' /\ wmono rsegs m m' /\
       bytes_at rsegs m' fuzz_alloc_fail_c.G_FAIL_AT
         (le8 (fuzz_alloc_fail_c.fail_at_of (Z_to_bv 64 cnt) (Z_to_bv 64 (pick (zb tb) (cnt - before))))))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (Z.of_nat (length tb))) (Z_to_bv 64 data) (Z_to_bv 64 before)
             (Z_to_bv 64 CRS_S5) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13d2c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m data before cnt tb
    CNT FAIL HC HB HCN HW HD HDL HD0 HO HR.
  assert (Ucnt : bv_unsigned (Z_to_bv 64 cnt) = cnt) by (apply unsigned_lit; lia).
  assert (Ubef : bv_unsigned (Z_to_bv 64 before) = before) by (apply unsigned_lit; lia).
  unfold CRS_S5.
  step.
  eapply evt_cut; [eapply CNT; exact HC|]. intros ms' ->. crsb_ret.
  step. if_false.
  crsb_oom HO HR.
  step. if_false.
  step.
  eapply evt_cut; [eapply CNT; exact HC|]. intros ms' ->. crsb_ret.
  step. step.
  rewrite (crsb_pick (zb tb) (cnt - before)) by lia.
  assert (TB : tb = [] \/ tb <> []) by (destruct tb; [left; reflexivity | right; discriminate]).
  destruct TB as [-> | NE].
  - cbn [length Z.of_nat] in *. step. if_true. step. if_true. step. step.
    rewrite Ucnt, Ubef, crsb_remu by lia.
    step.
    eapply evt_cut; [eapply FAIL; [exact HC | exact HW]|].
    intros ms' (a1' & m' & -> & HFA & MU & WM). crsb_ret.
    do 3 step.
    change (djb2 5381 (zb [])) with 5381.
    finish.
  - assert (LP : (0 < length tb)%nat) by (destruct tb; [congruence | cbn; lia]).
    pose proof HD as (Hd0 & _).
    assert (Ulen : bv_unsigned (Z_to_bv 64 (Z.of_nat (length tb))) = Z.of_nat (length tb)) by (apply unsigned_lit; lia).
    pose proof (crsb_djb2_range (zb tb) 5381 ltac:(lia)) as DR.
    step. if_false. do 4 step.
    rewrite (crsu_snez data) by lia.
    eapply evt_cut.
    { eapply crsu_l2 with (D := data) (E := data + Z.of_nat (length tb)) (tl := tb) (p := data) (h := 5381);
        [exact HD | exact NE | lia | reflexivity | lia | lia]. }
    intros ms' (a6' & a7' & ->).
    step. if_true. step. step.
    rewrite Ucnt, Ubef, crsb_remu by lia.
    step.
    eapply evt_cut; [eapply FAIL; [exact HC | exact HW]|].
    intros ms' (a1' & m' & -> & HFA & MU & WM). crsb_ret.
    do 3 step.
    finish.
Qed.

(* after the starved pretty write (text = NULL): fuzz_alloc_fail(SIZE_MAX), out_of_memory() (reads 0, so the beqz
   jumps to the check), the text and live checks, fuzz_alloc_count and the call of the compact full write. *)
Lemma crs_s5 : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cnt : Z),
  fuzz_alloc_fail_c.fuzz_alloc_fail_contract -> fuzz_alloc_live_c.fuzz_alloc_live_contract ->
  fuzz_alloc_count_c.fuzz_alloc_count_contract ->
  bytes_at rsegs m fuzz_alloc_live_c.G_LIVE (le8 s0) ->
  bytes_at rsegs m fuzz_alloc_fail_c.G_COUNT (le8 (Z_to_bv 64 cnt)) -> 0 <= cnt < 2 ^ 64 ->
  wr_at rsegs m fuzz_alloc_fail_c.G_FAIL_AT 8 ->
  bytes_at rsegs m LedgerCells.GL_OWN_RAN_OUT (le1 (Z_to_bv 64 0)) ->
  bytes_at rsegs m fuzz_alloc_ran_out_c.G_RAN_OUT (le1 (Z_to_bv 64 0)) ->
  evt rsegs
    (fun ms' => exists (t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
       ms' = MS (mkR (Z_to_bv 64 0x13e24) sp gp tp t0' t1' t2' s0 s1 s1 (Z_to_bv 64 0) a2' a3' a4' a5' a6' a7'
                     s2 s3 (Z_to_bv 64 cnt) (Z_to_bv 64 CRS_S5) s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x16838) fc None m' (seg_rom rsegs) /\
       munch [(fuzz_alloc_fail_c.G_FAIL_AT, fuzz_alloc_fail_c.G_FAIL_AT + 8)] m m' /\ wmono rsegs m m' /\
       bytes_at rsegs m' fuzz_alloc_fail_c.G_FAIL_AT
         (le8 (fuzz_alloc_fail_c.fail_at_of (Z_to_bv 64 cnt) (Z_to_bv 64 (-1)))))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 (Z_to_bv 64 CRS_S5) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13dbc) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m cnt
    FAIL LIVE CNT HL HC HCN HW HO HR.
  unfold CRS_S5.
  do 3 step.
  eapply evt_cut; [eapply FAIL; [exact HC | exact HW]|].
  intros ms' (a1' & m' & -> & HFA & MU & WM). crsb_ret.
  apply (crsb_tr m m') in HL; [| exact MU | unfold fuzz_alloc_live_c.G_LIVE, fuzz_alloc_fail_c.G_FAIL_AT; lia].
  apply (crsb_tr m m') in HC; [| exact MU | unfold fuzz_alloc_fail_c.G_COUNT, fuzz_alloc_fail_c.G_FAIL_AT; lia].
  destruct (crsb_flags_tr m m' MU HO HR) as [HO' HR'].
  crsb_oom HO' HR'.
  step. if_true.
  step. if_false.
  step.
  eapply evt_cut; [eapply LIVE; exact HL|]. intros ms' ->. crsb_ret.
  step. if_false.
  step.
  eapply evt_cut; [eapply CNT; exact HC|]. intros ms' ->. crsb_ret.
  do 4 step.
  finish.
Qed.

(* after the compact full write and its fuzz_free: the count test, out_of_memory(), fuzz_alloc_count, the call of
   fuzz_pick (out of line here: crsu_pick), fuzz_alloc_fail and the call of the starved pj_write(doc, 0). *)
Lemma crs_s7 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (data before cnt : Z) (tb : list byte),
  fuzz_alloc_count_c.fuzz_alloc_count_contract -> fuzz_alloc_fail_c.fuzz_alloc_fail_contract ->
  bytes_at rsegs m fuzz_alloc_fail_c.G_COUNT (le8 (Z_to_bv 64 cnt)) -> 0 <= before < cnt -> cnt < 2 ^ 64 ->
  wr_at rsegs m fuzz_alloc_fail_c.G_FAIL_AT 8 ->
  bytes_at rsegs m data tb -> data + Z.of_nat (length tb) < 2 ^ 64 -> 0 < data ->
  bytes_at rsegs m LedgerCells.GL_OWN_RAN_OUT (le1 (Z_to_bv 64 0)) ->
  bytes_at rsegs m fuzz_alloc_ran_out_c.G_RAN_OUT (le1 (Z_to_bv 64 0)) ->
  evt rsegs
    (fun ms' => exists (t0' t1' t2' a2' a3' a4' a5' a6' a7' s2' s3' t3' t4' t5' t6' : word) (m' : word -> option byte),
       ms' = MS (mkR (Z_to_bv 64 0x13e64) sp gp tp t0' t1' t2' s0 s1 s1 (Z_to_bv 64 0) a2' a3' a4' a5' a6' a7'
                     s2' s3' (Z_to_bv 64 before) (Z_to_bv 64 CRS_S5) s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x16838) fc None m' (seg_rom rsegs) /\
       munch [(fuzz_alloc_fail_c.G_FAIL_AT, fuzz_alloc_fail_c.G_FAIL_AT + 8)] m m' /\ wmono rsegs m m' /\
       bytes_at rsegs m' fuzz_alloc_fail_c.G_FAIL_AT
         (le8 (fuzz_alloc_fail_c.fail_at_of (Z_to_bv 64 cnt) (Z_to_bv 64 (pick (zb tb) (cnt - before))))))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (Z.of_nat (length tb))) (Z_to_bv 64 data) (Z_to_bv 64 before)
             (Z_to_bv 64 CRS_S5) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13e28) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m data before cnt tb
    CNT FAIL HC HB HCN HW HD HDL HD0 HO HR.
  assert (Ucnt : bv_unsigned (Z_to_bv 64 cnt) = cnt) by (apply unsigned_lit; lia).
  assert (Ubef : bv_unsigned (Z_to_bv 64 before) = before) by (apply unsigned_lit; lia).
  unfold CRS_S5.
  step.
  eapply evt_cut; [eapply CNT; exact HC|]. intros ms' ->. crsb_ret.
  step. if_false.
  crsb_oom HO HR.
  step. if_false.
  step.
  eapply evt_cut; [eapply CNT; exact HC|]. intros ms' ->. crsb_ret.
  do 4 step.
  rewrite ?Ucnt, ?Ubef.
  eapply evt_cut.
  { eapply crsu_pick with (data := data) (n := cnt - before) (tb := tb); [exact HD | exact HDL | exact HD0 | lia]. }
  intros ms' (t0' & a1' & a3' & a4' & a5' & a6' & a7' & ->). crsb_ret.
  step.
  eapply evt_cut; [eapply FAIL; [exact HC | exact HW]|].
  intros ms' (a1'' & m' & -> & HFA & MU & WM). crsb_ret.
  do 3 step.
  finish.
Qed.

(* after the starved compact write (text = NULL): fuzz_alloc_fail(SIZE_MAX), out_of_memory() (reads 0), the text and
   live checks (the beq to the epilogue is taken), and the epilogue. *)
Lemma crs_s8 : forall (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S cnt : Z) (xra xs0 xs1 xs2 xs3 xs4 xs5 : word),
  fuzz_alloc_fail_c.fuzz_alloc_fail_contract -> fuzz_alloc_live_c.fuzz_alloc_live_contract ->
  0x56000 <= S - 112 -> S <= 2 ^ 63 -> crs_cells m S xra xs0 xs1 xs2 xs3 xs4 xs5 ->
  bytes_at rsegs m fuzz_alloc_live_c.G_LIVE (le8 s0) ->
  bytes_at rsegs m fuzz_alloc_fail_c.G_COUNT (le8 (Z_to_bv 64 cnt)) -> 0 <= cnt < 2 ^ 64 ->
  wr_at rsegs m fuzz_alloc_fail_c.G_FAIL_AT 8 ->
  bytes_at rsegs m LedgerCells.GL_OWN_RAN_OUT (le1 (Z_to_bv 64 0)) ->
  bytes_at rsegs m fuzz_alloc_ran_out_c.G_RAN_OUT (le1 (Z_to_bv 64 0)) ->
  evt rsegs
    (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
       ms' = MS (mkR xra (Z_to_bv 64 S) gp tp t0' t1' t2' xs0 xs1 a0' a1' a2' a3' a4' a5' a6' a7'
                     xs2 xs3 xs4 xs5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc xra) fc None m' (seg_rom rsegs) /\
       munch [(fuzz_alloc_fail_c.G_FAIL_AT, fuzz_alloc_fail_c.G_FAIL_AT + 8)] m m' /\ wmono rsegs m m' /\
       bytes_at rsegs m' fuzz_alloc_fail_c.G_FAIL_AT
         (le8 (fuzz_alloc_fail_c.fail_at_of (Z_to_bv 64 cnt) (Z_to_bv 64 (-1)))))
    (MS (mkR ra (Z_to_bv 64 (S - 112)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 (Z_to_bv 64 CRS_S5) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13e64) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m S cnt
    xra xs0 xs1 xs2 xs3 xs4 xs5 FAIL LIVE HS1 HS2 CC HL HC HCN HW HO HR.
  unfold CRS_S5.
  do 3 step.
  eapply evt_cut; [eapply FAIL; [exact HC | exact HW]|].
  intros ms' (a1' & m' & -> & HFA & MU & WM). crsb_ret.
  apply (crsb_tr m m') in HL; [| exact MU | unfold fuzz_alloc_live_c.G_LIVE, fuzz_alloc_fail_c.G_FAIL_AT; lia].
  apply (crsb_cells_tr m m') in CC; [| exact MU | exact HS1].
  destruct (crsb_flags_tr m m' MU HO HR) as [HO' HR'].
  crsb_oom HO' HR'.
  step. if_false.
  step. if_false.
  step.
  eapply evt_cut; [eapply LIVE; exact HL|]. intros ms' ->. crsb_ret.
  step. if_true.
  eapply evt_cut; [eapply (crs_epi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m' S xra xs0 xs1 xs2 xs3 xs4 xs5 HS1 HS2 CC)|].
  intros ms' ->.
  finish.
Qed.
