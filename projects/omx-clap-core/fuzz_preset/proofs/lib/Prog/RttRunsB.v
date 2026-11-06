From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Tac Bytes Step ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct strcmp_c strlen_c same_c memcpy_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import LedgerCells fuzz_alloc_ran_out_c.
Import ListNotations.
Open Scope Z_scope.

(* round_trip_text of the #102 plain twin c8f4d6b8 (lib/Prog/round_trip_text_c.v): the runs that step over the
   evt-level contracts strcmp, strlen, same, memcpy and fuzz_alloc_ran_out (0x158cc), and the flag loads
   `lbu a0, -0x684(s5)` of g_own_ran_out (GL_OWN_RAN_OUT, s5 = 0x34e24 from `auipc s5, 0x20` at 0x14e24). *)

Lemma rb_roc8 : forall m A v, bytes_at rsegs m A (le8 v) -> ro_cells rsegs m A [C8 v].
Proof. intros m A v HB. split; [cbn; tauto | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact HB]. Qed.

Lemma rb_roc4 : forall m A v, bytes_at rsegs m A (le4 v) -> ro_cells rsegs m A [C4 v].
Proof. intros m A v HB. split; [cbn; tauto | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact HB]. Qed.

Lemma rb_prefix : forall m a bs1 bs2, bytes_at rsegs m a (bs1 ++ bs2) -> bytes_at rsegs m a bs1.
Proof. intros m a bs1 bs2 H. apply bytes_at_app in H. exact (proj1 H). Qed.

Lemma rb_zx8 : forall v : word, bv_unsigned v < 2^8 -> zx8 v = v.
Proof.
  intros v H. unfold zx8. pose proof (bv_unsigned_in_range 64 v) as R.
  rewrite Z.mod_small by lia. apply Z_to_bv_bv_unsigned.
Qed.

Lemma rb_byte_read : forall m a v, bytes_at rsegs m a (le1 v) -> ov_read_bytes rsegs m (wa a) 1 = Some (le1 v).
Proof.
  intros m a v HR. replace (wa a) with (wa (a + 0)) by (f_equal; lia).
  rewrite (bytes_at_read rsegs m a (le1 v) 0 1 HR ltac:(lia)) by (rewrite length_le1; lia). reflexivity.
Qed.

Section KA.
Hypothesis HSC : strcmp_contract.
Hypothesis HSL : strlen_contract.
Hypothesis HSM : same_contract.
Hypothesis HMC : memcpy_contract.
Hypothesis HFR : fuzz_alloc_ran_out_contract.

(* 0x14e0c: lw a0, 24(sp) (failed = 0); ld s3, 0(sp) (want); beqz; auipc s5; lbu a0 (g_own_ran_out); bnez to the
   ran-out arm 0x14e38; jal fuzz_alloc_ran_out; beqz to 0x14e74, else on to 0x14e38 *)
Lemma rtt_segF : forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P want ro oo : Z),
  0 <= P -> P + 32 <= 2 ^ 64 -> 0 <= want < 2 ^ 64 -> 0 <= ro < 256 -> 0 <= oo < 256 ->
  bytes_at rsegs m P (le8 (Z_to_bv 64 want)) -> bytes_at rsegs m (P + 24) (le4 (Z_to_bv 64 0)) ->
  bytes_at rsegs m GL_OWN_RAN_OUT (le1 (Z_to_bv 64 oo)) ->
  bytes_at rsegs m G_RAN_OUT (le1 (Z_to_bv 64 ro)) ->
  evt rsegs (fun ms' => exists ra' a0' : word,
      ((ro <> 0 \/ oo <> 0) /\
       ms' = MS (mkR ra' (Z_to_bv 64 P) gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 want) s4
                     (Z_to_bv 64 0x34e24) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14e38) fc None m (seg_rom rsegs))
      \/
      (ro = 0 /\ oo = 0 /\
       ms' = MS (mkR ra' (Z_to_bv 64 P) gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 want) s4
                     (Z_to_bv 64 0x34e24) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14e74) fc None m (seg_rom rsegs)))
    (MS (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14e0c) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P want ro oo
    HP0 HP1 HW Hro Hoo HQ HF HOWN HRAN.
  pose proof HFR as FR. unfold fuzz_alloc_ran_out_contract, FUZZ_ALLOC_RAN_OUT in FR.
  apply rb_roc8 in HQ. apply rb_roc4 in HF.
  pose proof (rb_byte_read m _ _ HOWN) as ROWN. unfold GL_OWN_RAN_OUT in ROWN.
  assert (Uoo : bv_unsigned (Z_to_bv 64 oo) < 2 ^ 8) by (rewrite unsigned_lit by lia; lia).
  assert (Uro : bv_unsigned (Z_to_bv 64 ro) < 2 ^ 8) by (rewrite unsigned_lit by lia; lia).
  do 2 step. step. try if_true.
  do 2 step. rewrite (rb_zx8 _ Uoo).
  step. if_cases HB; zify_cond HB.
  - (* g_own_ran_out <> 0: bnez to the ran-out arm *)
    apply evt_done. do 2 eexists. left. split; [right; lia|]. reflexivity.
  - (* g_own_ran_out = 0: fuzz_alloc_ran_out () *)
    step.
    eapply evt_cut.
    { eapply FR; [exact Uro | exact HRAN]. }
    intros ms' E. cbv beta in E. subst ms'.
    rewrite ret_pc_even by first [lia | reflexivity].
    step. if_cases HC; zify_cond HC.
    + apply evt_done. do 2 eexists. right. split; [lia|]. split; [lia|]. reflexivity.
    + apply evt_done. do 2 eexists. left. split; [left; lia|]. reflexivity.
Qed.

(* 0x14e74: beqz s2 (text nonzero); strcmp(text, want) = 0; strlen(text); jal parse_noting(text, len, &back = P) *)
Lemma rtt_seg4 : forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P text want : Z) (W slack : list byte),
  0 <= P < 2 ^ 64 -> 0 < text < 2 ^ 64 -> 0 <= want < 2 ^ 64 ->
  bytes_at rsegs m text (W ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) W ->
  (- (text + Z.of_nat (length W) + 1)) mod 8 <= Z.of_nat (length slack) ->
  bytes_at rsegs m want (W ++ [Z_to_bv 8 0]) -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
      munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
      ms' = MS (mkR (Z_to_bv 64 0x14ea0) (Z_to_bv 64 P) gp tp t0' t1' t2' s0 s1
                    (Z_to_bv 64 text) (Z_to_bv 64 (Z.of_nat (length W))) (Z_to_bv 64 P) a3' a4' a5' a6' a7'
                    (Z_to_bv 64 text) (Z_to_bv 64 want) s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x13a04) fc None m' (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 text) (Z_to_bv 64 want) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14e74) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P text want W slack
    HP HT HW0 HB HZ HA HWB HI.
  pose proof HSC as SC. unfold strcmp_contract, STRCMP in SC.
  pose proof HSL as SL. unfold strlen_contract, STRLEN in SL.
  pose proof (bytes_at_bound rsegs m text _ HB) as HBb. rewrite length_app in HBb. cbn [length] in HBb.
  assert (HB0 : bytes_at rsegs m text (W ++ [Z_to_bv 8 0])).
  { apply (rb_prefix m text _ slack). rewrite <- app_assoc. exact HB. }
  step.
  assert (C0 : bv_eqb (Z_to_bv 64 text) (Z_to_bv 64 0) = false)
    by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
  rewrite C0; cbv iota.
  do 3 step.
  eapply evt_cut.
  { eapply SC with (sx := W) (sy := W);
      [rewrite unsigned_lit by lia; exact HB0 | exact HZ | rewrite unsigned_lit by lia; exact HWB | exact HZ]. }
  intros ms' (r & x11 & x12 & x13 & E & HR). subst ms'.
  assert (Er : r = Z_to_bv 64 0) by (apply HR; reflexivity). subst r.
  rewrite ret_pc_even by first [lia | reflexivity].
  step. try if_false.
  do 2 step.
  eapply evt_cut.
  { eapply SL with (str := W) (slack := slack);
      [rewrite unsigned_lit by lia; exact HB | exact HZ | rewrite unsigned_lit by lia; exact HA | exact HI]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MU & WM & MI & _).
  subst ms'.
  rewrite ret_pc_even by first [lia | reflexivity].
  do 4 step.
  apply evt_done. do 13 eexists.
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. reflexivity.
Qed.

(* 0x14eb4: lbu g_own_ran_out (0); s2 := 1; jal fuzz_alloc_ran_out (0); bnez s4 (rc = 0); same(doc = s1, &back = P),
   nonzero; on to 0x14edc *)
Lemma rtt_seg5 : forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P doc lo : Z) (L : Z -> Z -> Prop) (t : jv)
    (D Db : list (Z * Z)),
  0 <= P < 2 ^ 64 -> 0 <= doc < 2 ^ 64 -> s1 = Z_to_bv 64 doc ->
  bytes_at rsegs m GL_OWN_RAN_OUT (le1 (Z_to_bv 64 0)) -> bytes_at rsegs m G_RAN_OUT (le1 (Z_to_bv 64 0)) ->
  pj_node rsegs m L doc t D -> pj_node rsegs m L P t Db ->
  mem_inv rsegs m -> stk rsegs m lo P -> lo + same_k t <= P ->
  (forall z, pj_foot doc D z -> outside [(P - same_k t, P)] z) ->
  (forall z, pj_foot P Db z -> outside [(P - same_k t, P)] z) ->
  evt rsegs (fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                               (m' : word -> option byte),
      munch [(P - same_k t, P)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo P /\
      pj_node rsegs m' L doc t D /\ pj_node rsegs m' L P t Db /\
      ms' = MS (mkR ra' (Z_to_bv 64 P) gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                    (Z_to_bv 64 1) s3 (Z_to_bv 64 0) (Z_to_bv 64 0x34e24) s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x14edc) fc None m' (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 (Z_to_bv 64 0) (Z_to_bv 64 0x34e24) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14eb4) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P doc lo L t D Db
    HP HD HS1 HOWN HRAN N1 N2 HI HK HL O1 O2. subst s1.
  pose proof HSM as SM. unfold same_contract, SAME in SM.
  pose proof HFR as FR. unfold fuzz_alloc_ran_out_contract, FUZZ_ALLOC_RAN_OUT in FR.
  pose proof (rb_byte_read m _ _ HOWN) as ROWN. unfold GL_OWN_RAN_OUT in ROWN.
  assert (U0 : bv_unsigned (Z_to_bv 64 0) < 2 ^ 8) by (rewrite unsigned_lit by lia; lia).
  step. rewrite (rb_zx8 _ U0).
  step. step. try if_false.
  step.
  eapply evt_cut.
  { eapply FR; [exact U0 | exact HRAN]. }
  intros ms' E. cbv beta in E. subst ms'.
  rewrite ret_pc_even by first [lia | reflexivity].
  step. try if_false.
  step. try if_false.
  do 3 step.
  eapply evt_cut.
  { eapply SM; [reflexivity | reflexivity | exact N1 | exact N2 | exact HI
              | rewrite unsigned_lit by lia; exact HK | rewrite unsigned_lit by lia; exact HL
              | rewrite unsigned_lit by lia; exact O1 | rewrite unsigned_lit by lia; exact O2]. }
  intros ms' (t0' & t1' & t2' & r & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
              E & MU & WM & MI & ST & HR & N1' & N2').
  subst ms'. rewrite unsigned_lit in MU, ST by lia.
  destruct HR as [[_ ->] | [Hne _]]; [|congruence].
  rewrite ret_pc_even by first [lia | reflexivity].
  step. try if_false.
  apply evt_done. do 17 eexists.
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
  split; [exact N1'|]. split; [exact N2'|]. reflexivity.
Qed.

(* 0x14edc with copy <> 0: memcpy(copy, &back = P, 56); s2 := 0; a0 := s2; restore; ret *)
Lemma rtt_seg7a : forall (ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P copy : Z) (bs junk : list byte)
    (rav s0v s1v s2v s3v s4v s5v : word),
  0 <= P -> P + 112 <= copy -> copy + 56 <= 2 ^ 64 -> length bs = 56%nat ->
  bytes_at rsegs m P bs -> rw_cells rsegs m copy [CB 56 junk] ->
  bytes_at rsegs m (P + 104) (le8 rav) -> bytes_at rsegs m (P + 96) (le8 s0v) ->
  bytes_at rsegs m (P + 88) (le8 s1v) -> bytes_at rsegs m (P + 80) (le8 s2v) ->
  bytes_at rsegs m (P + 72) (le8 s3v) -> bytes_at rsegs m (P + 64) (le8 s4v) ->
  bytes_at rsegs m (P + 56) (le8 s5v) -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                               (m' : word -> option byte),
      munch [(copy, copy + 56)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ bytes_at rsegs m' copy bs /\
      ms' = MS (mkR rav (Z_to_bv 64 (P + 112)) gp tp t0' t1' t2' s0v s1v (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7'
                    s2v s3v s4v s5v s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc rav) fc None m' (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 (Z_to_bv 64 copy) s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14edc) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P copy bs junk
    rav s0v s1v s2v s3v s4v s5v HP HC1 HC2 HL HB HD K1 K2 K3 K4 K5 K6 K7 HI.
  pose proof HMC as MC. unfold memcpy_contract in MC.
  step.
  assert (C0 : bv_eqb (Z_to_bv 64 copy) (Z_to_bv 64 0) = false)
    by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
  rewrite C0; cbv iota.
  do 4 step.
  eapply evt_cut.
  { eapply MC with (src := bs) (junk := junk);
      [ rewrite unsigned_lit by lia; exact HB
      | rewrite unsigned_lit by lia; exact HL
      | rewrite !unsigned_lit by lia; exact HD
      | rewrite !unsigned_lit by lia; lia
      | exact HI ]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MU & WM & MI & RW & _).
  subst ms'. rewrite !unsigned_lit in MU, RW by lia.
  apply (bytes_at_transport rsegs [(copy, copy + 56)] m m') in K1; [| exact MU | cbn [disjoint_from]; rewrite length_le8; lia].
  apply (bytes_at_transport rsegs [(copy, copy + 56)] m m') in K2; [| exact MU | cbn [disjoint_from]; rewrite length_le8; lia].
  apply (bytes_at_transport rsegs [(copy, copy + 56)] m m') in K3; [| exact MU | cbn [disjoint_from]; rewrite length_le8; lia].
  apply (bytes_at_transport rsegs [(copy, copy + 56)] m m') in K4; [| exact MU | cbn [disjoint_from]; rewrite length_le8; lia].
  apply (bytes_at_transport rsegs [(copy, copy + 56)] m m') in K5; [| exact MU | cbn [disjoint_from]; rewrite length_le8; lia].
  apply (bytes_at_transport rsegs [(copy, copy + 56)] m m') in K6; [| exact MU | cbn [disjoint_from]; rewrite length_le8; lia].
  apply (bytes_at_transport rsegs [(copy, copy + 56)] m m') in K7; [| exact MU | cbn [disjoint_from]; rewrite length_le8; lia].
  apply rb_roc8 in K1. apply rb_roc8 in K2. apply rb_roc8 in K3. apply rb_roc8 in K4. apply rb_roc8 in K5.
  apply rb_roc8 in K6. apply rb_roc8 in K7.
  rewrite ret_pc_even by first [lia | reflexivity].
  do 13 step.
  apply evt_done. do 15 eexists.
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
  split; [destruct RW as ((_ & HB') & _); cbn [cells_bytes cbytes] in HB'; rewrite app_nil_r in HB'; exact HB'|].
  reflexivity.
Qed.

End KA.
