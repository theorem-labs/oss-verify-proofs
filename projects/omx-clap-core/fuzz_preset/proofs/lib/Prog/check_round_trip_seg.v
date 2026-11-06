From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import strlen_c memset_c fuzz_alloc_ran_out_c
LedgerCells check_round_trip_c.
Import ListNotations.
Open Scope Z_scope.

(* The straight-line segments of check_round_trip in the #102 plain twin (pau-preset-102 fuzz_preset.plain, sha256
   c8f4d6b8e567b0b1...; check_round_trip 0x13fe4 size 680).  s2 holds 0x340a0 from 0x140a0 (auipc s2, 0x20) on; every
   out_of_memory() test reads g_own_ran_out (LedgerCells.GL_OWN_RAN_OUT) at 0x700(s2) by lbu and then calls
   fuzz_alloc_ran_out (g_ran_out, fuzz_alloc_ran_out_c.G_RAN_OUT). *)

Definition crt_cells (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : word) : list cell :=
  [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* auipc s2, 0x20 at 0x140a0 *)
Definition CRT_S2 : Z := 0x340a0.

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

(* 0x13fe4 .. 0x14034: the frame, memset (sp, 0, 56) (copy = empty), then round_trip_text (doc, 0, &copy), ra 0x14038 *)
Lemma crt_pro : memset_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
    stk rsegs m lo (bv_unsigned sp) -> lo + CRT_F <= bv_unsigned sp -> mem_inv rsegs m ->
    evt rsegs
      (fun ms => exists (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m1,
         ms = MS (mkR (Z_to_bv 64 0x14038) (Z_to_bv 64 (bv_unsigned sp + -256)) gp tp t0' t1' t2' a0 s1 a0
                      (Z_to_bv 64 0) (Z_to_bv 64 (bv_unsigned sp + -256)) a3' a4' a5' a6' a7'
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x14d88) fc None m1 (seg_rom rsegs) /\
         munch [(bv_unsigned sp + -88, bv_unsigned sp); (bv_unsigned sp + -256, bv_unsigned sp + -200)] m m1 /\
         wmono rsegs m m1 /\ mem_inv rsegs m1 /\
         rw_cells rsegs m1 (bv_unsigned sp + -88) (crt_cells ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9) /\
         rw_cells rsegs m1 (bv_unsigned sp + -256) [CB 56 (repeat (Z_to_bv 8 0) 56)])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_ROUND_TRIP) fc None m (seg_rom rsegs)).
Proof.
  intros HMS ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    ST LO MI.
  unfold CHECK_ROUND_TRIP. unfold CRT_F in LO.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof ST as (ST0 & ST1 & _).
  destruct (stk_split rsegs m lo (bv_unsigned sp + -200) (bv_unsigned sp) ST ltac:(lia)) as [STa _].
  destruct (stk_carve rsegs m lo (bv_unsigned sp + -200) 56 STa ltac:(lia)) as [_ (junk2 & RV)].
  replace (bv_unsigned sp + -200 - Z.of_nat 56) with (bv_unsigned sp + -256) in RV by lia.
  clear STa.
  pose proof (munch_refl [(bv_unsigned sp + -88, bv_unsigned sp); (bv_unsigned sp + -256, bv_unsigned sp + -200)] m)
    as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 88%nat ST.
  do 17 zstep.
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
  replace (ret_pc (Z_to_bv 64 0x14028)) with (Z_to_bv 64 0x14028) by (apply bv_eq; vm_compute; reflexivity).
  assert (MU2 : munch [(bv_unsigned sp + -88, bv_unsigned sp); (bv_unsigned sp + -256, bv_unsigned sp + -200)] m m2).
  { apply (munch_trans _ m m0 m2 MU). eapply munch_weaken; [|exact MUc].
    unfold sub_fp. intros x Hx. cbn [outside] in Hx |- *. lia. }
  pose proof (wmono_trans rsegs m m0 m2 WM WMc) as WM2.
  apply (rw_cells_transport rsegs [(bv_unsigned sp + -256, bv_unsigned sp + -256 + 56)] m0 m2) in FR;
    [| exact MUc | exact WMc | cbn [disjoint_from cells_size csize]; lia].
  clear MU WM MI MUc WMc.
  do 4 zstep.
  apply evt_done.
  exists t0', t1', t2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m2.
  split; [reflexivity|].
  split; [exact MU2|]. split; [exact WM2|]. split; [exact MIc|].
  split; [unfold crt_cells; exact FR | exact RVc].
Qed.

(* 0x14038: round_trip_text returned 0; 0x14044 .. 0x14054: round_trip_text (doc, 1, NULL), ra 0x14058 *)
Lemma crt_r1 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    evt rsegs
      (fun ms => ms = MS (mkR (Z_to_bv 64 0x14058) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 1) s0 (Z_to_bv 64 1)
                            (Z_to_bv 64 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x14d88) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
               t3 t4 t5 t6)
          F (Z_to_bv 64 0x14038) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  step. if_true.
  do 5 step.
  apply evt_done. reflexivity.
Qed.

(* 0x14038: round_trip_text returned 1 (memory had run out): s1 = 1, on to 0x14248 *)
Lemma crt_r1o :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    evt rsegs
      (fun ms => ms = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 1) (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
                            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x14248) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
               t3 t4 t5 t6)
          F (Z_to_bv 64 0x14038) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  step. if_false.
  do 2 step.
  apply evt_done. reflexivity.
Qed.

(* 0x14058: round_trip_text returned 0; doc->type: not an object -> 0x14244 (s1 = 0) .. pj_free (&copy), ra 0x14250;
   an object -> s3 = doc->n, pj_string (&v, STAMP), ra 0x1407c *)
Lemma crt_r2 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ty : Z) (n : word),
    bytes_at rsegs m (bv_unsigned s0) (le4 (Z_to_bv 64 ty)) -> 0 <= ty <= 6 ->
    bytes_at rsegs m (bv_unsigned s0 + 40) (le8 n) ->
    evt rsegs
      (fun ms =>
         (ty <> 6 /\
          ms = MS (mkR (Z_to_bv 64 0x14250) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 0) sp (Z_to_bv 64 6) a2
                       a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 0x15c08) fc None m (seg_rom rsegs)) \/
         (ty = 6 /\
          ms = MS (mkR (Z_to_bv 64 0x1407c) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (bv_unsigned sp + 56))
                       (Z_to_bv 64 STAMP_A) a2 a3 a4 a5 a6 a7 s2 n s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 0x15ef4) fc None m (seg_rom rsegs)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
               t3 t4 t5 t6)
          F (Z_to_bv 64 0x14058) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ty n
    BT TY BN.
  pose proof (crt_rd4 _ _ _ BT) as R4. pose proof (crt_rd8 _ _ _ BN) as R8.
  rewrite (wa_of_var s0 (bv_unsigned s0) eq_refl) in R4.
  assert (U : bv_unsigned (Z_to_bv 64 ty) = ty) by (apply unsigned_lit; lia).
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

(* 0x1407c: pj_string returned 0; 0x14088 .. 0x14098: pj_set (&copy, REWRITTEN, &v), ra 0x1409c *)
Lemma crt_ps :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    evt rsegs
      (fun ms => ms = MS (mkR (Z_to_bv 64 0x1409c) sp gp tp t0 t1 t2 s0 s1 sp (Z_to_bv 64 MOD_AT_A)
                            (Z_to_bv 64 (bv_unsigned sp + 56)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                            t3 t4 t5 t6)
                        F (Z_to_bv 64 0x15d7c) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
               t3 t4 t5 t6)
          F (Z_to_bv 64 0x1407c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  step. if_true.
  do 5 step.
  apply evt_done. reflexivity.
Qed.

(* 0x1409c: pj_set returned 0 (s4 = set = 1); out_of_memory() is 0 (both flag bytes 0); 0x140bc .. 0x140c8:
   pj_write (&copy, 1), ra 0x140cc *)
Lemma crt_set : fuzz_alloc_ran_out_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    bytes_at rsegs m GL_OWN_RAN_OUT (le1 (Z_to_bv 64 0)) ->
    bytes_at rsegs m G_RAN_OUT (le1 (Z_to_bv 64 0)) ->
    evt rsegs
      (fun ms => ms = MS (mkR (Z_to_bv 64 0x140cc) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 1) sp (Z_to_bv 64 1)
                            a2 a3 a4 a5 a6 a7 (Z_to_bv 64 CRT_S2) s3 (Z_to_bv 64 1) s5 s6 s7 s8 s9 s10 s11
                            t3 t4 t5 t6)
                        F (Z_to_bv 64 0x15f58) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
               t3 t4 t5 t6)
          F (Z_to_bv 64 0x1409c) fc None m (seg_rom rsegs)).
Proof.
  intros HRO ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m BO BR.
  unfold GL_OWN_RAN_OUT in BO. pose proof (crt_rd1 _ _ _ BO) as R1.
  do 5 step. if_false.
  step.
  eapply evt_cut.
  { apply HRO with (ran_out := Z_to_bv 64 0); [rewrite unsigned_lit by lia; lia | exact BR]. }
  intros ms' E. cbv beta in E. subst ms'.
  replace (ret_pc (Z_to_bv 64 0x140b4)) with (Z_to_bv 64 0x140b4) by (apply bv_eq; vm_compute; reflexivity).
  step. if_false.
  step. if_false.
  do 4 step.
  apply evt_done. reflexivity.
Qed.

(* 0x140cc: pj_write returned q <> 0 (s1 = saved); out_of_memory() is 0; strlen (saved); 0x140ec .. 0x140f8:
   parse_noting (saved, strlen (saved), &back), ra 0x140fc *)
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
         ms = MS (mkR (Z_to_bv 64 0x140fc) sp gp tp t0' t1' t2' s0 (Z_to_bv 64 q) (Z_to_bv 64 q)
                      (Z_to_bv 64 (Z.of_nat (length txt))) (Z_to_bv 64 (bv_unsigned sp + 112))
                      a3' a4' a5' a6' a7' (Z_to_bv 64 CRT_S2) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x13a04) fc None m' (seg_rom rsegs) /\
         munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 CRT_S2) s3 s4 s5 s6 s7 s8 s9
               s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x140cc) fc None m (seg_rom rsegs)).
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
  replace (ret_pc (Z_to_bv 64 0x140e0)) with (Z_to_bv 64 0x140e0) by (apply bv_eq; vm_compute; reflexivity).
  step. if_false.
  do 2 step.
  eapply evt_cut.
  { apply HS; [rewrite U; exact BY | exact NZ | rewrite U; exact AL | exact MI]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MU & WM & MI' & _).
  subst ms'.
  replace (ret_pc (Z_to_bv 64 0x140ec)) with (Z_to_bv 64 0x140ec) by (apply bv_eq; vm_compute; reflexivity).
  do 4 step.
  apply evt_done.
  exists t0', t1', t2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  split; [reflexivity|]. exact (conj MU (conj WM MI')).
Qed.

(* 0x140fc: parse_noting returned 0 (s4 = 0); out_of_memory() is 0; on to 0x1411c *)
Lemma crt_pn : fuzz_alloc_ran_out_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    bytes_at rsegs m GL_OWN_RAN_OUT (le1 (Z_to_bv 64 0)) ->
    bytes_at rsegs m G_RAN_OUT (le1 (Z_to_bv 64 0)) ->
    evt rsegs
      (fun ms => ms = MS (mkR (Z_to_bv 64 0x1410c) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                            (Z_to_bv 64 CRT_S2) s3 (Z_to_bv 64 0) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x1411c) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 CRT_S2) s3 s4 s5 s6 s7 s8
               s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x140fc) fc None m (seg_rom rsegs)).
Proof.
  intros HRO ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m BO BR.
  unfold GL_OWN_RAN_OUT in BO. pose proof (crt_rd1 _ _ _ BO) as R1.
  do 2 step. step. if_false.
  step.
  eapply evt_cut.
  { apply HRO with (ran_out := Z_to_bv 64 0); [rewrite unsigned_lit by lia; lia | exact BR]. }
  intros ms' E. cbv beta in E. subst ms'.
  replace (ret_pc (Z_to_bv 64 0x1410c)) with (Z_to_bv 64 0x1410c) by (apply bv_eq; vm_compute; reflexivity).
  step. if_true.
  apply evt_done. reflexivity.
Qed.

(* 0x1423c .. 0x14240: pj_free (&back), ra 0x14244 *)
Lemma crt_ff :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    evt rsegs
      (fun ms => ms = MS (mkR (Z_to_bv 64 0x14244) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (bv_unsigned sp + 112))
                            a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x15c08) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1423c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  do 2 step.
  apply evt_done. reflexivity.
Qed.

(* 0x14244 .. 0x1424c: s1 = 0, pj_free (&copy), ra 0x14250 *)
Lemma crt_pfz :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    evt rsegs
      (fun ms => ms = MS (mkR (Z_to_bv 64 0x14250) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 0) sp
                            a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x15c08) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x14244) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  do 3 step.
  apply evt_done. reflexivity.
Qed.

(* 0x14248 .. 0x1424c: pj_free (&copy), ra 0x14250 *)
Lemma crt_pf1 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    evt rsegs
      (fun ms => ms = MS (mkR (Z_to_bv 64 0x14250) sp gp tp t0 t1 t2 s0 s1 sp
                            a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x15c08) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x14248) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  do 2 step.
  apply evt_done. reflexivity.
Qed.

(* 0x14250 .. 0x14284: a0 = s1 (the value returned), the frame restored, ret *)
Lemma crt_epi :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (ra' s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' : word),
    bv_unsigned sp + 256 < 2 ^ 64 ->
    rw_cells rsegs m (bv_unsigned sp + 168) (crt_cells ra' s0' s1' s2' s3' s4' s5' s6' s7' s8' s9') ->
    evt rsegs
      (fun ms => ms = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + 256)) gp tp t0 t1 t2 s0' s1' s1
                            a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8' s9' s10 s11 t3 t4 t5 t6)
                        F (ret_pc ra') fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x14250) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    ra' s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' SPB FR.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  unfold crt_cells in FR.
  do 14 step.
  apply evt_done. reflexivity.
Qed.
