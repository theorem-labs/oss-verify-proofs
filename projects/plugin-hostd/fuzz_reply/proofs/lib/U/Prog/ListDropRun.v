From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes Arr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import memmove_c list_drop_run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma ldu_res_len : forall (us : list byte) (i N CAP : Z), 0 <= i < N -> N <= CAP ->
  Z.of_nat (length us) = 16 * CAP ->
  Z.of_nat (length (mm_result us (Z.to_nat (16 * i + 16)) (Z.to_nat (16 * i)) (Z.to_nat (16 * (N - i - 1))))) =
  16 * CAP.
Proof.
  intros us i N CAP H1 H2 H3. unfold mm_result. rewrite upd_bytes_length; [lia|].
  unfold slice. rewrite length_firstn, length_skipn. lia.
Qed.

Definition ldu_end (rav sp0 gp tp s0v s1v s2v s3v s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (LA i V N CAP : Z) (us : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR rav sp0 gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc rav) fc None m' (seg_rom rsegs)
    /\ munch [(V + 16 * i, V + 16 * (N - 1)); (LA + 8, LA + 12)] m m' /\ wmono rsegs m m'
    /\ rw_cells rsegs m' LA [C8 (Z_to_bv 64 V); C4 (Z_to_bv 64 (N - 1)); C4 (Z_to_bv 64 CAP)]
    /\ u8arr rsegs m' V (mm_result us (Z.to_nat (16 * i + 16)) (Z.to_nat (16 * i)) (Z.to_nat (16 * (N - i - 1)))).

Lemma ldu_run2 : memmove_contract ->
  forall ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (sp0 : word) (LA IX V N CAP : Z) (us : list byte)
    (s0v s1v s2v s3v rav : word) (j0 : list byte),
  rw_cells rsegs m (bv_unsigned sp0 - 48) [CB 8 j0; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  rw_cells rsegs m LA [C8 (Z_to_bv 64 V); C4 (Z_to_bv 64 N); C4 (Z_to_bv 64 CAP)] ->
  u8arr rsegs m V us -> Z.of_nat (length us) = 16 * CAP ->
  0 <= IX < N -> N <= CAP -> CAP < 2 ^ 30 -> 8 <= V -> V mod 8 = 0 -> V + 16 * CAP <= 2 ^ 63 ->
  0 <= LA -> LA + 16 <= 2 ^ 64 -> (LA + 16 <= V \/ V + 16 * CAP <= LA) ->
  (LA + 16 <= bv_unsigned sp0 - 48 \/ bv_unsigned sp0 <= LA) ->
  V + 16 * CAP <= bv_unsigned sp0 - 48 -> 48 <= bv_unsigned sp0 -> mem_inv rsegs m ->
  evt rsegs (ldu_end rav sp0 gp tp s0v s1v s2v s3v s4 s5 s6 s7 s8 s9 s10 s11 F fc LA IX V N CAP us m)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 - 48)) gp tp t0 t1 t2 (Z_to_bv 64 LA) (Z_to_bv 64 IX) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (16 * IX)) (Z_to_bv 64 0) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14dc0) fc None m (seg_rom rsegs)).
Proof.
  intros MMV ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m sp0 LA IX V N CAP us
    s0v s1v s2v s3v rav j0 FR LC ARR LUS HI HN HC HV HVA HVC HL0 HL1 DLV DLS DVS SP48 MI.
  pose proof (bv_unsigned_in_range 64 sp0) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  eapply evt_cut.
  { eapply ldu_mid with (LA := LA) (V := V) (N := N) (i := IX) (c := Z_to_bv 64 CAP);
      [reflexivity | reflexivity | reflexivity | reflexivity | lia | lia | lia | exact HVA | lia | lia | lia | exact LC]. }
  intros ms1 (a3' & a4' & a5' & a6' & a7' & ->).
  assert (UA0 : bv_unsigned (Z_to_bv 64 (V + 16 * IX)) = V + 16 * IX) by (apply unsigned_lit; lia).
  assert (UA1 : bv_unsigned (Z_to_bv 64 (V + 16 * (IX + 1))) = V + 16 * (IX + 1)) by (apply unsigned_lit; lia).
  assert (UA2 : bv_unsigned (Z_to_bv 64 (16 * (N - IX - 1))) = 16 * (N - IX - 1)) by (apply unsigned_lit; lia).
  eapply evt_cut.
  { eapply (MMV _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ V us);
      [exact ARR | lia | rewrite UA1, UA2; lia | rewrite UA0, UA2; lia | rewrite UA2; lia | exact MI]. }
  intros ms2 (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & m2 & -> & MU2 & WM2 & MI2
    & ARR2).
  rewrite UA0, UA2 in MU2. rewrite UA0, UA1, UA2 in ARR2.
  replace (V + 16 * (IX + 1) - V) with (16 * IX + 16) in ARR2 by lia.
  replace (V + 16 * IX - V) with (16 * IX) in ARR2 by lia.
  replace (ret_pc (Z_to_bv 64 0x14e48)) with (Z_to_bv 64 0x14e48) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  assert (LC2 : rw_cells rsegs m2 LA [C8 (Z_to_bv 64 V); C4 (Z_to_bv 64 N); C4 (Z_to_bv 64 CAP)]).
  { apply (rw_cells_transport rsegs _ m m2 _ _ LC MU2 WM2). cbn [disjoint_from cells_size csize Nat.add].
    split; [lia | exact I]. }
  assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp0 - 48) [CB 8 j0; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav]).
  { apply (rw_cells_transport rsegs _ m m2 _ _ FR MU2 WM2). cbn [disjoint_from cells_size csize Nat.add].
    split; [lia | exact I]. }
  pose proof (ldu_res_len us IX N CAP ltac:(lia) HN LUS) as LR.
  eapply evt_mono.
  { eapply ldu_tail with (LA := LA) (B := bv_unsigned sp0 - 48) (N := N);
      [reflexivity | lia | lia | reflexivity | lia | lia | lia | lia | exact MI2 | exact LC2 | exact FR2]. }
  intros ms' (a0' & a1' & m3 & -> & MU3 & WM3 & MI3 & LC3 & FR3).
  replace (Z_to_bv 64 (bv_unsigned sp0 - 48 + 48)) with sp0
    by (rewrite Z.sub_add; symmetry; apply Z_to_bv_bv_unsigned).
  unfold ldu_end.
  do 16 eexists. split; [reflexivity|].
  split.
  { apply (munch_trans _ m m2 m3).
    - apply (munch_weaken [(V + 16 * IX, V + 16 * IX + 16 * (N - IX - 1))]); [|exact MU2].
      unfold sub_fp. cbn [outside]. intros x (X1 & X2 & _). split; [lia | exact I].
    - apply (munch_weaken [(LA + 8, LA + 12)]); [|exact MU3].
      unfold sub_fp. cbn [outside]. intros x (X1 & X2 & _). split; [exact X2 | exact I]. }
  split; [exact (wmono_trans rsegs _ _ _ WM2 WM3)|].
  split; [exact LC3|].
  apply (u8arr_transport rsegs _ m2 m3 _ _ ARR2 MU3 WM3). cbn [disjoint_from]. rewrite LR. split; [lia | exact I].
Qed.
