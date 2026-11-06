From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import strlen_c memset_c fuzz_alloc_ran_out_c
LedgerCells.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import check_round_trip_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import SRCF.
Import ListNotations.
Open Scope Z_scope.

(* The straight-line segments of check_round_trip in the #102 ubsan twin (pau-preset-102/omx-clap-core/unstripped/
   fuzz_preset/fuzz_preset.ubsan, sha256 27566683952ebd54...; check_round_trip FUNC LOCAL 0x1408c size 1024; every pc
   below is that symbol plus an offset of the twin's listing).  s2 holds CRT_S2 from 0x14158 (auipc s2, 0x21) on;
   every out_of_memory() test reads g_own_ran_out (LedgerCells.GL_OWN_RAN_OUT) at 0xf8(s2) by lbu and then calls
   fuzz_alloc_ran_out (g_ran_out, fuzz_alloc_ran_out_c.G_RAN_OUT).  Callee entries (the twin's .symtab): memset
   0x22924, round_trip_text 0x15334, pj_string 0x167c4, pj_set 0x165d4, fuzz_alloc_ran_out 0x15f90, pj_write
   0x16838, strlen 0x22a54, parse_noting 0x13a38, fuzz_free 0x15ea8, pj_free 0x16340. *)

Definition crt_cells (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* auipc s2, 0x21 at 0x14158; 0xf8(s2) is g_own_ran_out *)
Definition CRT_S2 : Z := 0x35158.

Lemma crt_s2_own : CRT_S2 + 0xf8 = GL_OWN_RAN_OUT.
Proof. reflexivity. Qed.

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

(* 0x1408c .. 0x140e4: the frame, memset (sp, 0, 56) (copy = empty, ra 0x140d8), then round_trip_text (doc, 0,
   &copy), ra 0x140e8 *)
Lemma crt_pro : memset_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
    stk rsegs m lo (bv_unsigned sp) -> lo + CRT_F <= bv_unsigned sp -> mem_inv rsegs m ->
    evt rsegs
      (fun ms => exists (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m1,
         ms = MS (mkR (Z_to_bv 64 0x140e8) (Z_to_bv 64 (bv_unsigned sp + -272)) gp tp t0' t1' t2' a0 s1 a0
                      (Z_to_bv 64 0) (Z_to_bv 64 (bv_unsigned sp + -272)) a3' a4' a5' a6' a7'
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x15334) fc None m1 (seg_rom rsegs) /\
         munch [(bv_unsigned sp + -104, bv_unsigned sp); (bv_unsigned sp + -272, bv_unsigned sp + -216)] m m1 /\
         wmono rsegs m m1 /\ mem_inv rsegs m1 /\
         rw_cells rsegs m1 (bv_unsigned sp + -104) (crt_cells ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) /\
         rw_cells rsegs m1 (bv_unsigned sp + -272) [CB 56 (repeat (Z_to_bv 8 0) 56)])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_ROUND_TRIP) fc None m (seg_rom rsegs)).
Proof.
  intros HMS ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    ST LO MI.
  unfold CHECK_ROUND_TRIP. unfold CRT_F in LO.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof ST as (ST0 & ST1 & _).
  destruct (stk_split rsegs m lo (bv_unsigned sp + -216) (bv_unsigned sp) ST ltac:(lia)) as [STa _].
  destruct (stk_carve rsegs m lo (bv_unsigned sp + -216) 56 STa ltac:(lia)) as [_ (junk2 & RV)].
  replace (bv_unsigned sp + -216 - Z.of_nat 56) with (bv_unsigned sp + -272) in RV by lia.
  clear STa.
  pose proof (munch_refl [(bv_unsigned sp + -104, bv_unsigned sp); (bv_unsigned sp + -272, bv_unsigned sp + -216)] m)
    as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 104%nat ST.
  do 19 step.
  eapply evt_cut.
  { eapply HMS with (junk := junk2).
    - rewrite unsigned_lit by lia. change (Z.to_nat (bv_unsigned (Z_to_bv 64 56))) with 56%nat. exact RV.
    - exact MI. }
  intros ms' POST. unfold memset_post in POST.
  destruct POST as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 &
    E & MUc & WMc & MIc & RVc).
  subst ms'.
  rewrite unsigned_lit in MUc, RVc by lia.
  change (bv_unsigned (Z_to_bv 64 56)) with 56 in MUc.
  change (Z.to_nat (bv_unsigned (Z_to_bv 64 56))) with 56%nat in RVc.
  change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 0) mod 256)) with (Z_to_bv 8 0) in RVc.
  replace (ret_pc (Z_to_bv 64 0x140d8)) with (Z_to_bv 64 0x140d8) by (apply bv_eq; vm_compute; reflexivity).
  assert (MU2 : munch [(bv_unsigned sp + -104, bv_unsigned sp); (bv_unsigned sp + -272, bv_unsigned sp + -216)] m m2).
  { apply (munch_trans _ m m0 m2 MU). eapply munch_weaken; [|exact MUc].
    unfold sub_fp. intros x Hx. cbn [outside] in Hx |- *. lia. }
  pose proof (wmono_trans rsegs m m0 m2 WM WMc) as WM2.
  apply (rw_cells_transport rsegs [(bv_unsigned sp + -272, bv_unsigned sp + -272 + 56)] m0 m2) in FR;
    [| exact MUc | exact WMc | cbn [disjoint_from cells_size csize]; lia].
  clear MU WM MI MUc WMc.
  do 4 step.
  apply evt_done.
  exists t0', t1', t2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m2.
  split; [reflexivity|].
  split; [exact MU2|]. split; [exact WM2|]. split; [exact MIc|].
  split; [unfold crt_cells; exact FR | exact RVc].
Qed.

(* 0x140e8: round_trip_text returned 0; 0x140f4 .. 0x14104: round_trip_text (doc, 1, NULL), ra 0x14108 *)
Lemma crt_r1 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    evt rsegs
      (fun ms => ms = MS (mkR (Z_to_bv 64 0x14108) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 1) s0 (Z_to_bv 64 1)
                            (Z_to_bv 64 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x15334) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
               t3 t4 t5 t6)
          F (Z_to_bv 64 0x140e8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  step. if_true.
  do 5 step.
  apply evt_done. reflexivity.
Qed.

(* 0x140e8: round_trip_text returned 1 (memory had run out): s1 = 1, on to 0x14438 *)
Lemma crt_r1o :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    evt rsegs
      (fun ms => ms = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 1) (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
                            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x14438) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
               t3 t4 t5 t6)
          F (Z_to_bv 64 0x140e8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  step. if_false.
  do 2 step.
  apply evt_done. reflexivity.
Qed.

(* 0x14108: round_trip_text returned 0; the alignment test of doc (UBSan, 0x1410c); doc->type: not an object ->
   0x14434 (s1 = 0) .. pj_free (&copy), ra 0x14440; an object -> s4 = doc->n, pj_string (&v, STAMP), ra 0x14134 *)
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
                   F (Z_to_bv 64 0x16340) fc None m (seg_rom rsegs)) \/
         (ty = 6 /\
          ms = MS (mkR (Z_to_bv 64 0x14134) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (bv_unsigned sp + 56))
                       (Z_to_bv 64 STAMP_A) a2 a3 a4 a5 a6 a7 s2 s3 n s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 0x167c4) fc None m (seg_rom rsegs)))
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

(* 0x14134: pj_string returned 0; 0x14140 .. 0x14150: pj_set (&copy, REWRITTEN, &v), ra 0x14154 *)
Lemma crt_ps :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    evt rsegs
      (fun ms => ms = MS (mkR (Z_to_bv 64 0x14154) sp gp tp t0 t1 t2 s0 s1 sp (Z_to_bv 64 MOD_AT_A)
                            (Z_to_bv 64 (bv_unsigned sp + 56)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                            t3 t4 t5 t6)
                        F (Z_to_bv 64 0x165d4) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
               t3 t4 t5 t6)
          F (Z_to_bv 64 0x14134) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  step. if_true.
  do 5 step.
  apply evt_done. reflexivity.
Qed.

(* 0x14154: pj_set returned 0 (s3 = set = 1); out_of_memory() is 0 (both flag bytes 0: lbu 0x1415c, bnez 0x14164 not
   taken, fuzz_alloc_ran_out ra 0x1416c returns 0, bnez 0x1416c not taken); beqz s3 (0x14170) not taken;
   0x14174 .. 0x14180: pj_write (&copy, 1), ra 0x14184 *)
Lemma crt_set : fuzz_alloc_ran_out_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    bytes_at rsegs m GL_OWN_RAN_OUT (le1 (Z_to_bv 64 0)) ->
    bytes_at rsegs m G_RAN_OUT (le1 (Z_to_bv 64 0)) ->
    evt rsegs
      (fun ms => ms = MS (mkR (Z_to_bv 64 0x14184) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 1) sp (Z_to_bv 64 1)
                            a2 a3 a4 a5 a6 a7 (Z_to_bv 64 CRT_S2) (Z_to_bv 64 1) s4 s5 s6 s7 s8 s9 s10 s11
                            t3 t4 t5 t6)
                        F (Z_to_bv 64 0x16838) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
               t3 t4 t5 t6)
          F (Z_to_bv 64 0x14154) fc None m (seg_rom rsegs)).
Proof.
  intros HRO ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m BO BR.
  unfold GL_OWN_RAN_OUT in BO. pose proof (crt_rd1 _ _ _ BO) as R1.
  do 5 step. if_false.
  step.
  eapply evt_cut.
  { apply HRO with (ran_out := Z_to_bv 64 0); [rewrite unsigned_lit by lia; lia | exact BR]. }
  intros ms' E. cbv beta in E. subst ms'.
  replace (ret_pc (Z_to_bv 64 0x1416c)) with (Z_to_bv 64 0x1416c) by (apply bv_eq; vm_compute; reflexivity).
  step. if_false.
  step. if_false.
  do 4 step.
  apply evt_done. reflexivity.
Qed.

(* 0x14184: pj_write returned q <> 0 (s1 = saved); out_of_memory() is 0 (lbu 0x1418c, fuzz_alloc_ran_out ra
   0x14198); strlen (saved), ra 0x141a4; 0x141a4 .. 0x141b0: parse_noting (saved, strlen (saved), &back), ra 0x141b4 *)
Lemma crt_w : fuzz_alloc_ran_out_contract -> strlen_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (q : Z) (txt slack : list byte),
    0 < q < 2 ^ 64 ->
    bytes_at rsegs m GL_OWN_RAN_OUT (le1 (Z_to_bv 64 0)) ->
    bytes_at rsegs m G_RAN_OUT (le1 (Z_to_bv 64 0)) ->
    bytes_at rsegs m q (txt ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) txt ->
    (- (q + Z.of_nat (length txt) + 1)) mod 8 <= Z.of_nat (length slack) ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms => exists (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
         ms = MS (mkR (Z_to_bv 64 0x141b4) sp gp tp t0' t1' t2' s0 (Z_to_bv 64 q) (Z_to_bv 64 q)
                      (Z_to_bv 64 (Z.of_nat (length txt))) (Z_to_bv 64 (bv_unsigned sp + 112))
                      a3' a4' a5' a6' a7' (Z_to_bv 64 CRT_S2) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x13a38) fc None m' (seg_rom rsegs) /\
         munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 CRT_S2) s3 s4 s5 s6 s7 s8 s9
               s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x14184) fc None m (seg_rom rsegs)).
Proof.
  intros HRO HS ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m q
    txt slack Q BO BR BY NZ AL MI.
  unfold GL_OWN_RAN_OUT in BO. pose proof (crt_rd1 _ _ _ BO) as R1.
  assert (U : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  step. step. if_false.
  step. step. if_false.
  step.
  eapply evt_cut.
  { apply HRO with (ran_out := Z_to_bv 64 0); [rewrite unsigned_lit by lia; lia | exact BR]. }
  intros ms' E. cbv beta in E. subst ms'.
  replace (ret_pc (Z_to_bv 64 0x14198)) with (Z_to_bv 64 0x14198) by (apply bv_eq; vm_compute; reflexivity).
  step. if_false.
  do 2 step.
  eapply evt_cut.
  { apply HS; [rewrite U; exact BY | exact NZ | rewrite U; exact AL | exact MI]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MU & WM & MI' & _).
  subst ms'.
  replace (ret_pc (Z_to_bv 64 0x141a4)) with (Z_to_bv 64 0x141a4) by (apply bv_eq; vm_compute; reflexivity).
  do 4 step.
  apply evt_done.
  exists t0', t1', t2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  split; [reflexivity|]. exact (conj MU (conj WM MI')).
Qed.

(* 0x141b4: parse_noting returned 0 (s3 = 0); out_of_memory() is 0 (lbu 0x141b8, fuzz_alloc_ran_out ra 0x141c4);
   beqz 0x141c4 goes to 0x141d4 *)
Lemma crt_pn : fuzz_alloc_ran_out_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    bytes_at rsegs m GL_OWN_RAN_OUT (le1 (Z_to_bv 64 0)) ->
    bytes_at rsegs m G_RAN_OUT (le1 (Z_to_bv 64 0)) ->
    evt rsegs
      (fun ms => ms = MS (mkR (Z_to_bv 64 0x141c4) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                            (Z_to_bv 64 CRT_S2) (Z_to_bv 64 0) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x141d4) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 CRT_S2) s3 s4 s5 s6 s7 s8
               s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x141b4) fc None m (seg_rom rsegs)).
Proof.
  intros HRO ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m BO BR.
  unfold GL_OWN_RAN_OUT in BO. pose proof (crt_rd1 _ _ _ BO) as R1.
  do 2 step. step. if_false.
  step.
  eapply evt_cut.
  { apply HRO with (ran_out := Z_to_bv 64 0); [rewrite unsigned_lit by lia; lia | exact BR]. }
  intros ms' E. cbv beta in E. subst ms'.
  replace (ret_pc (Z_to_bv 64 0x141c4)) with (Z_to_bv 64 0x141c4) by (apply bv_eq; vm_compute; reflexivity).
  step. if_true.
  apply evt_done. reflexivity.
Qed.

(* 0x1442c .. 0x14430: pj_free (&back), ra 0x14434 *)
Lemma crt_ff :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    evt rsegs
      (fun ms => ms = MS (mkR (Z_to_bv 64 0x14434) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (bv_unsigned sp + 112))
                            a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x16340) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1442c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  do 2 step.
  apply evt_done. reflexivity.
Qed.

(* 0x14434 .. 0x1443c: s1 = 0, pj_free (&copy), ra 0x14440 *)
Lemma crt_pfz :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    evt rsegs
      (fun ms => ms = MS (mkR (Z_to_bv 64 0x14440) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 0) sp
                            a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x16340) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x14434) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  do 3 step.
  apply evt_done. reflexivity.
Qed.

(* 0x14438 .. 0x1443c: pj_free (&copy), ra 0x14440 *)
Lemma crt_pf1 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    evt rsegs
      (fun ms => ms = MS (mkR (Z_to_bv 64 0x14440) sp gp tp t0 t1 t2 s0 s1 sp
                            a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x16340) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x14438) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  do 2 step.
  apply evt_done. reflexivity.
Qed.

(* 0x14440 .. 0x1447c: a0 = s1 (the value returned), the frame restored, ret *)
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
