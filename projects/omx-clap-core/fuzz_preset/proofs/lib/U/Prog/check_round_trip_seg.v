From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import strlen_c memset_c check_round_trip_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require LedgerCells fuzz_alloc_ran_out_c
  round_trip_text_c pj_free_c pj_string_c pj_set_c PjWriteHyp parse_noting_c.
Import ListNotations.
Open Scope Z_scope.

(* The straight-line segments of check_round_trip in the #102 ubsan twin (27566683952ebd54..., the unstripped twin of
   the pin 45b0357d18ff66cd...): check_round_trip FUNC 0x1408c size 1024 (check_round_trip_c.CHECK_ROUND_TRIP).
   fuzz_preset.c:772-781 of #102: `copy = empty` is the memset call, then the two round_trip_text calls with their
   `||` exits, then the inlined round_trip_rewrite (715-769) with its three out_of_memory() tests, each
   `lbu g_own_ran_out` (s2 + 0xf8, s2 = auipc 0x21 at 0x14158) and then `jal fuzz_alloc_ran_out`.  The callee entries are
   the contracts' constants (memset_c.MEMSET, round_trip_text_c.ROUND_TRIP_TEXT, pj_free_c.PJ_FREE, ...), the flag cells
   LedgerCells.GL_OWN_RAN_OUT and fuzz_alloc_ran_out_c.G_RAN_OUT.  The interior pcs are the twin's. *)

Definition crt_cells (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* s2 after `auipc s2, 0x21` at 0x14158: the base of the out_of_memory() loads `lbu a0, 0xf8(s2)` *)
Definition CRT_OWN_BASE : Z := LedgerCells.GL_OWN_RAN_OUT - 248.

Lemma crt_sx32 : forall z, 0 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. rewrite unsigned_lit by lia. rewrite bv_swrap_small; [reflexivity|].
  change (bv_half_modulus 32) with (2^31). lia.
Qed.

Lemma crt_rd8 : forall m a v, bytes_at rsegs m a (le8 v) -> ov_read_bytes rsegs m (wa a) 8 = Some (le8 v).
Proof.
  intros m a v B.
  replace (wa a) with (wa (a + 0)) by (f_equal; lia).
  rewrite (bytes_at_read rsegs m a (le8 v) 0 8 B ltac:(lia)) by (rewrite length_le8; lia).
  reflexivity.
Qed.

Lemma crt_rd4 : forall m a v, bytes_at rsegs m a (le4 v) -> ov_read_bytes rsegs m (wa a) 4 = Some (le4 v).
Proof.
  intros m a v B.
  replace (wa a) with (wa (a + 0)) by (f_equal; lia).
  rewrite (bytes_at_read rsegs m a (le4 v) 0 4 B ltac:(lia)) by (rewrite length_le4; lia).
  reflexivity.
Qed.

Lemma crt_rd1 : forall m a v, bytes_at rsegs m a (le1 v) -> ov_read_bytes rsegs m (wa a) 1 = Some (le1 v).
Proof.
  intros m a v B.
  replace (wa a) with (wa (a + 0)) by (f_equal; lia).
  rewrite (bytes_at_read rsegs m a (le1 v) 0 1 B ltac:(lia)) by (rewrite length_le1; lia).
  reflexivity.
Qed.

Lemma crtu_land7 : forall x : Z, x mod 8 = 0 -> Z.land x 7 = 0.
Proof.
  intros x H. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8. exact H.
Qed.

Lemma crt_zx8_0 : zx8 (Z_to_bv 64 0) = Z_to_bv 64 0.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

(* entry -> memset's entry: the frame (0x110, 13 saves), s0 := doc, memset (sp, 0, 56) *)
Lemma crt_pro :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
    stk rsegs m lo (bv_unsigned sp) -> lo + CRT_F <= bv_unsigned sp ->
    evt rsegs
      (fun ms => exists m1,
         ms = MS (mkR (Z_to_bv 64 0x140d8) (Z_to_bv 64 (bv_unsigned sp + -272)) gp tp t0 t1 t2 a0 s1
                      (Z_to_bv 64 (bv_unsigned sp + -272)) (Z_to_bv 64 0) (Z_to_bv 64 56) a3 a4 a5 a6 a7
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 MEMSET) fc None m1 (seg_rom rsegs) /\
         munch [(bv_unsigned sp + -104, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\
         stk rsegs m1 lo (bv_unsigned sp + -104) /\
         rw_cells rsegs m1 (bv_unsigned sp + -104) (crt_cells ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_ROUND_TRIP) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo ST LO.
  unfold CHECK_ROUND_TRIP. unfold CRT_F in LO.
  pose proof (munch_refl [(bv_unsigned sp + -104, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof ST as (ST0 & ST1 & _).
  carve_frame 104%nat ST.
  do 19 step.
  apply evt_done. eexists. split; [reflexivity|].
  unfold crt_cells. exact (conj MU (conj WM (conj ST FR))).
Qed.

(* memset's entry -> round_trip_text (doc, 0, &copy): the memset contract writes the 56 zero bytes of copy *)
Lemma crt_ms : memset_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (junk : list byte),
    rw_cells rsegs m (bv_unsigned sp) [CB 56 junk] -> mem_inv rsegs m ->
    evt rsegs
      (fun ms => exists (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
         ms = MS (mkR (Z_to_bv 64 0x140e8) sp gp tp t0' t1' t2' s0 s1 s0 (Z_to_bv 64 0) sp
                      a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 round_trip_text_c.ROUND_TRIP_TEXT) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp, bv_unsigned sp + 56)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
         rw_cells rsegs m' (bv_unsigned sp) [CB 56 (repeat (Z_to_bv 8 0) 56)])
      (MS (mkR (Z_to_bv 64 0x140d8) sp gp tp t0 t1 t2 s0 s1 sp (Z_to_bv 64 0) (Z_to_bv 64 56)
               a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 MEMSET) fc None m (seg_rom rsegs)).
Proof.
  intros HMS ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m junk
    FR MI.
  eapply evt_cut.
  { apply HMS with (junk := junk); [exact FR | exact MI]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MU & WM & MI' & FR').
  subst ms'.
  replace (ret_pc (Z_to_bv 64 0x140d8)) with (Z_to_bv 64 0x140d8) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  change (Z.to_nat (bv_unsigned (Z_to_bv 64 56))) with 56%nat in FR'.
  change (bv_unsigned (Z_to_bv 64 56)) with 56 in MU.
  replace (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 0) mod 256)) with (Z_to_bv 8 0) in FR' by (apply bv_eq; vm_compute; reflexivity).
  do 4 step.
  apply evt_done. exists t0', t1', t2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  split; [reflexivity|]. exact (conj MU (conj WM (conj MI' FR'))).
Qed.

(* round_trip_text (doc, 0, &copy) returned 1 (memory had run out): s1 := 1, then pj_free (&copy) at 0x14438 *)
Lemma crt_x0 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    evt rsegs
      (fun ms => ms = MS (mkR (Z_to_bv 64 0x14440) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 1) sp a1 a2
                            a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 pj_free_c.PJ_FREE) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
               t3 t4 t5 t6)
          F (Z_to_bv 64 0x140e8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  step. if_false.
  do 4 step.
  apply evt_done. reflexivity.
Qed.

(* round_trip_text (doc, 0, &copy) returned 0: round_trip_text (doc, 1, NULL), with s1 := 1 *)
Lemma crt_r1 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    evt rsegs
      (fun ms => ms = MS (mkR (Z_to_bv 64 0x14108) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 1) s0 (Z_to_bv 64 1)
                            (Z_to_bv 64 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 round_trip_text_c.ROUND_TRIP_TEXT) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
               t3 t4 t5 t6)
          F (Z_to_bv 64 0x140e8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  step. if_true.
  do 5 step.
  apply evt_done. reflexivity.
Qed.

(* round_trip_text (doc, 1, NULL) returned 0: the doc->type test; not an object -> s1 := 0 and pj_free (&copy) at
   0x14434; an object -> the inlined round_trip_rewrite: s4 := doc->n, pj_string (&v, STAMP) *)
Lemma crt_r2 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ty : Z) (n : word),
    bv_unsigned s0 mod 8 = 0 ->
    bytes_at rsegs m (bv_unsigned s0) (le4 (Z_to_bv 64 ty)) -> 0 <= ty <= 6 ->
    bytes_at rsegs m (bv_unsigned s0 + 40) (le8 n) ->
    evt rsegs
      (fun ms =>
         (ty <> 6 /\
          ms = MS (mkR (Z_to_bv 64 0x14440) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 0) sp (Z_to_bv 64 6) a2
                       a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 pj_free_c.PJ_FREE) fc None m (seg_rom rsegs)) \/
         (ty = 6 /\
          ms = MS (mkR (Z_to_bv 64 0x14134) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (bv_unsigned sp + 56))
                       (Z_to_bv 64 STAMP_A) a2 a3 a4 a5 a6 a7 s2 s3 n s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 pj_string_c.PJ_STRING) fc None m (seg_rom rsegs)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
               t3 t4 t5 t6)
          F (Z_to_bv 64 0x14108) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ty n
    AL BT TY BN.
  pose proof (crt_rd4 _ _ _ BT) as R4. pose proof (crt_rd8 _ _ _ BN) as R8.
  rewrite (wa_of_var s0 (bv_unsigned s0) eq_refl) in R4.
  assert (U : bv_unsigned (Z_to_bv 64 ty) = ty) by (apply unsigned_lit; lia).
  step. if_false.
  step. rewrite (crtu_land7 _ AL).
  step. if_false.
  step.
  rewrite (crt_sx32 ty) by lia.
  do 2 step.
  destruct (Z.eq_dec ty 6) as [E6|N6].
  - subst ty. if_false.
    do 5 step.
    apply evt_done. right. split; reflexivity.
  - if_true.
    do 3 step.
    apply evt_done. left. split; [exact N6 | reflexivity].
Qed.

(* pj_string returned 0: pj_set (copy, REWRITTEN, &v) *)
Lemma crt_ps :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    evt rsegs
      (fun ms => ms = MS (mkR (Z_to_bv 64 0x14154) sp gp tp t0 t1 t2 s0 s1 sp (Z_to_bv 64 MOD_AT_A)
                            (Z_to_bv 64 (bv_unsigned sp + 56)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                            t3 t4 t5 t6)
                        F (Z_to_bv 64 pj_set_c.PJ_SET) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
               t3 t4 t5 t6)
          F (Z_to_bv 64 0x14134) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  step. if_true.
  do 5 step.
  apply evt_done. reflexivity.
Qed.

(* pj_set returned 0 (set = 1): out_of_memory() with both flags 0 (g_own_ran_out read, fuzz_alloc_ran_out called),
   `if (!set) abort()` not taken, then pj_write (copy, 1) *)
Lemma crt_set : fuzz_alloc_ran_out_c.fuzz_alloc_ran_out_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    bytes_at rsegs m LedgerCells.GL_OWN_RAN_OUT (le1 (Z_to_bv 64 0)) ->
    bytes_at rsegs m fuzz_alloc_ran_out_c.G_RAN_OUT (le1 (Z_to_bv 64 0)) ->
    evt rsegs
      (fun ms => ms = MS (mkR (Z_to_bv 64 0x14184) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 1) sp (Z_to_bv 64 1)
                            a2 a3 a4 a5 a6 a7 (Z_to_bv 64 CRT_OWN_BASE) (Z_to_bv 64 1) s4 s5 s6 s7 s8 s9 s10 s11
                            t3 t4 t5 t6)
                        F (Z_to_bv 64 PjWriteHyp.PJ_WRITE) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
               t3 t4 t5 t6)
          F (Z_to_bv 64 0x14154) fc None m (seg_rom rsegs)).
Proof.
  intros HRAN ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    BO BR.
  pose proof (crt_rd1 _ _ _ BO) as R1.
  let g := eval vm_compute in LedgerCells.GL_OWN_RAN_OUT in change LedgerCells.GL_OWN_RAN_OUT with g in R1.
  let v := eval vm_compute in CRT_OWN_BASE in change CRT_OWN_BASE with v.
  do 3 step.
  rewrite ?crt_zx8_0.
  step.
  step. if_false.
  step.
  eapply evt_cut; [eapply HRAN with (ran_out := Z_to_bv 64 0); [vm_compute; reflexivity | exact BR] |].
  intros ms' ->.
  replace (ret_pc (Z_to_bv 64 0x1416c)) with (Z_to_bv 64 0x1416c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  step. if_false.
  step. if_false.
  do 4 step.
  apply evt_done. reflexivity.
Qed.

(* pj_write returned the text q <> 0 (saved): out_of_memory() with both flags 0, strlen (saved), and the call of
   parse_noting (saved, len, &back) *)
Lemma crt_w : fuzz_alloc_ran_out_c.fuzz_alloc_ran_out_contract -> strlen_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (q : Z) (txt slack : list byte),
    0 < q < 2 ^ 64 ->
    bytes_at rsegs m q (txt ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) txt ->
    (- (q + Z.of_nat (length txt) + 1)) mod 8 <= Z.of_nat (length slack) ->
    mem_inv rsegs m ->
    bytes_at rsegs m LedgerCells.GL_OWN_RAN_OUT (le1 (Z_to_bv 64 0)) ->
    bytes_at rsegs m fuzz_alloc_ran_out_c.G_RAN_OUT (le1 (Z_to_bv 64 0)) ->
    evt rsegs
      (fun ms => exists (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
         ms = MS (mkR (Z_to_bv 64 0x141b4) sp gp tp t0' t1' t2' s0 (Z_to_bv 64 q) (Z_to_bv 64 q)
                      (Z_to_bv 64 (Z.of_nat (length txt))) (Z_to_bv 64 (bv_unsigned sp + 112))
                      a3' a4' a5' a6' a7' (Z_to_bv 64 CRT_OWN_BASE) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 parse_noting_c.PARSE_NOTING) fc None m' (seg_rom rsegs) /\
         munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 CRT_OWN_BASE) s3 s4 s5 s6
               s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x14184) fc None m (seg_rom rsegs)).
Proof.
  intros HRAN HS ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m q txt
    slack Q BY NZ AL MI BO BR.
  assert (U : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  pose proof (crt_rd1 _ _ _ BO) as R1.
  let g := eval vm_compute in LedgerCells.GL_OWN_RAN_OUT in change LedgerCells.GL_OWN_RAN_OUT with g in R1.
  let v := eval vm_compute in CRT_OWN_BASE in change CRT_OWN_BASE with v.
  step.
  step. if_false.
  step.
  rewrite ?crt_zx8_0.
  step. if_false.
  step.
  eapply evt_cut; [eapply HRAN with (ran_out := Z_to_bv 64 0); [vm_compute; reflexivity | exact BR] |].
  intros ms' ->.
  replace (ret_pc (Z_to_bv 64 0x14198)) with (Z_to_bv 64 0x14198) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  step. if_false.
  do 2 step.
  eapply evt_cut.
  { apply HS; [rewrite U; exact BY | exact NZ | rewrite U; exact AL | exact MI]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MU & WM & MI' & _).
  subst ms'.
  replace (ret_pc (Z_to_bv 64 0x141a4)) with (Z_to_bv 64 0x141a4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  do 4 step.
  apply evt_done.
  exists t0', t1', t2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  split; [reflexivity|]. exact (conj MU (conj WM MI')).
Qed.

(* parse_noting returned rc = 0: s3 := (rc != 0) = 0, out_of_memory() with both flags 0, and the jump to
   `if (!saved || rc != 0) abort()` at 0x141d4, where the walk of the rewrite's loops starts
   (check_round_trip_loop.crt_cmp) *)
Lemma crt_pn : fuzz_alloc_ran_out_c.fuzz_alloc_ran_out_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    bytes_at rsegs m LedgerCells.GL_OWN_RAN_OUT (le1 (Z_to_bv 64 0)) ->
    bytes_at rsegs m fuzz_alloc_ran_out_c.G_RAN_OUT (le1 (Z_to_bv 64 0)) ->
    evt rsegs
      (fun ms => ms = MS (mkR (Z_to_bv 64 0x141c4) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                            (Z_to_bv 64 CRT_OWN_BASE) (Z_to_bv 64 0) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x141d4) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 CRT_OWN_BASE) s3 s4 s5 s6
               s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x141b4) fc None m (seg_rom rsegs)).
Proof.
  intros HRAN ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m BO BR.
  pose proof (crt_rd1 _ _ _ BO) as R1.
  let g := eval vm_compute in LedgerCells.GL_OWN_RAN_OUT in change LedgerCells.GL_OWN_RAN_OUT with g in R1.
  let v := eval vm_compute in CRT_OWN_BASE in change CRT_OWN_BASE with v.
  do 2 step.
  rewrite ?crt_zx8_0.
  step. if_false.
  step.
  eapply evt_cut; [eapply HRAN with (ran_out := Z_to_bv 64 0); [vm_compute; reflexivity | exact BR] |].
  intros ms' ->.
  replace (ret_pc (Z_to_bv 64 0x141c4)) with (Z_to_bv 64 0x141c4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  step. if_true.
  apply evt_done. reflexivity.
Qed.

(* fuzz_free (saved) returned: pj_free (&back) *)
Lemma crt_ff :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    evt rsegs
      (fun ms => ms = MS (mkR (Z_to_bv 64 0x14434) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (bv_unsigned sp + 112))
                            a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 pj_free_c.PJ_FREE) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1442c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  do 2 step.
  apply evt_done. reflexivity.
Qed.

(* pj_free (&back) returned (or the type test failed): s1 := 0, pj_free (&copy) *)
Lemma crt_pf1 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    evt rsegs
      (fun ms => ms = MS (mkR (Z_to_bv 64 0x14440) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 0) sp
                            a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 pj_free_c.PJ_FREE) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x14434) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  do 3 step.
  apply evt_done. reflexivity.
Qed.

(* pj_free (&copy) returned: a0 := s1 (the value returned: 1 when memory ran out, else 0), the frame popped, ret *)
Lemma crt_epi :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (ra' s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' : word),
    bv_unsigned sp + 272 < 2 ^ 64 ->
    rw_cells rsegs m (bv_unsigned sp + 168) (crt_cells ra' s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11') ->
    evt rsegs
      (fun ms => ms = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + 272)) gp tp t0 t1 t2 s0' s1' s1
                            a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3 t4 t5 t6)
                        F (ret_pc ra') fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x14440) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    ra' s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' SPB FR.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  unfold crt_cells in FR.
  do 16 step.
  apply evt_done. reflexivity.
Qed.
