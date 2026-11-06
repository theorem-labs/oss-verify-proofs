From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import Tac Bytes ZBridge.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac tl_cf H :=
  zify_cond H; unfold zxb in H; rewrite ?unsigned_lit in H by lia;
  try (apply andb_false_iff in H; destruct H as [H|H]; zify_bool H).

Ltac tl_zl := first [ lia | Z.div_mod_to_equations; lia ].

Ltac tl_weq := first [ reflexivity | word_eq_tac | (rewrite ?unsigned_lit by lia; reflexivity) ].

Lemma tl_pro : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (j : list byte),
  rw_cells rsegs m (bv_unsigned sp + -32) [CB 32 j] -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists m',
      ms' = MS (mkR (Z_to_bv 64 0x15aa0) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 a1 a0 a0
                    (Z_to_bv 64 0x10392) (Z_to_bv 64 1) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x154b8) fc None m' (seg_rom rsegs) /\
      munch [(bv_unsigned sp + -32, bv_unsigned sp + -32 + 32)] m m' /\ wmono rsegs m m' /\
      rw_cells rsegs m' (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15a70) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m j FRJ MI.
  pose proof (rw_cells_bound _ _ _ _ FRJ) as FB. cbn [cells_size csize] in FB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp + -32 + 32)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  apply (rw_cells_split_CB rsegs _ _ [] 32%nat j [] [8; 8; 8; 8]%nat) in FRJ; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FRJ.
  do 12 step.
  apply evt_done.
  eexists. split; [reflexivity|]. split; [intros x H; apply MU; cbn [outside] in H |- *; lia|].
  split; [exact WM|]. exact FRJ.
Qed.

Lemma tl_test : forall (Q : machine_state -> Prop) ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7
    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (k : Z),
  0 <= k < 2 ^ 31 ->
  (k = 0 ->
     evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 k) s1 a0 a1 a2 a3 a4 a5 a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x15ac4) fc None m (seg_rom rsegs))) ->
  (0 < k -> forall x10 y18 : word, y18 = Z_to_bv 64 0x1039d ->
     evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 k) s1 x10 a1 a2 a3 a4 a5 a6 a7
                          y18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x15aac) fc None m (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 k) s1 a0 a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x15aa0) fc None m (seg_rom rsegs)).
Proof.
  intros Q ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m k
    Hk KE KL.
  step. if_cases HC.
  - tl_cf HC; first [ eapply KE; tl_zl | exfalso; tl_zl | eapply KL; [tl_zl | tl_weq] ].
  - tl_cf HC; first [ exfalso; tl_zl | step; step; eapply KL; [tl_zl | tl_weq] ].
Qed.

Lemma tl_call : forall (Q : machine_state -> Prop) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  (forall r1 x12 : word, r1 = Z_to_bv 64 0x15abc -> x12 = Z_to_bv 64 2 ->
     evt rsegs Q (MS (mkR r1 sp gp tp t0 t1 t2 s0 s1 s1 s2 x12 a3 a4 a5 a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x154b8) fc None m (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x15aac) fc None m (seg_rom rsegs)).
Proof.
  intros Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m K.
  do 4 step.
  eapply K; tl_weq.
Qed.

Lemma tl_back : forall (Q : machine_state -> Prop) ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7
    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (k : Z),
  1 <= k < 2 ^ 31 ->
  (k - 1 = 0 -> forall y8 : word, y8 = Z_to_bv 64 (k - 1) ->
     evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 y8 s1 a0 a1 a2 a3 a4 a5 a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x15ac4) fc None m (seg_rom rsegs))) ->
  (0 < k - 1 -> forall y8 : word, y8 = Z_to_bv 64 (k - 1) ->
     evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 y8 s1 a0 a1 a2 a3 a4 a5 a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x15aac) fc None m (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 k) s1 a0 a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x15abc) fc None m (seg_rom rsegs)).
Proof.
  intros Q ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m k
    Hk KE KL.
  step.
  replace (bv_swrap 32 (bv_unsigned (Z_to_bv 64 k) + -1)) with (k - 1)
    by (rewrite unsigned_lit by lia; rewrite bv_swrap_small; [lia | change (bv_half_modulus 32) with (2 ^ 31); lia]).
  step. if_cases HC.
  - tl_cf HC;
      first [ eapply KL; [tl_zl | tl_weq] | exfalso; tl_zl | eapply KE; [tl_zl | tl_weq] ].
  - tl_cf HC;
      first [ eapply KE; [tl_zl | tl_weq] | exfalso; tl_zl | eapply KL; [tl_zl | tl_weq] ].
Qed.

Lemma tl_epi : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (rav s0v s1v s2v : word),
  bv_unsigned sp + 32 < 2 ^ 64 ->
  rw_cells rsegs m (bv_unsigned sp) [C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  evt rsegs (fun ms' => exists x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
      ms' = MS (mkR rav (Z_to_bv 64 (bv_unsigned sp + 32)) gp tp x5 x6 x7 s0v s1v x10 x11 x12 x13 x14 x15 x16 x17
                    s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
               F (ret_pc rav) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15ac4) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    rav s0v s1v s2v Hsp FR.
  pose proof (rw_cells_bound _ _ _ _ FR) as FB. cbn [cells_size csize] in FB.
  do 6 step.
  apply evt_done.
  do 15 eexists. reflexivity.
Qed.

Definition tl_Q (k : Z) (sp gp tp s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 rav s0v s1v s2v : word) (F : bvmap 5 word)
    (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
  fun ms =>
    (0 < k /\ exists t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
       ms = MS (mkR (Z_to_bv 64 0x15abc) sp gp tp t0 t1 t2 (Z_to_bv 64 k) s1 s1 (Z_to_bv 64 0x1039d) (Z_to_bv 64 2)
                   a3 a4 a5 a6 a7 (Z_to_bv 64 0x1039d) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x154b8) fc None m (seg_rom rsegs)) \/
    (k = 0 /\ exists x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
       ms = MS (mkR rav (Z_to_bv 64 (bv_unsigned sp + 32)) gp tp x5 x6 x7 s0v s1v x10 x11 x12 x13 x14 x15 x16 x17
                   s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
               F (ret_pc rav) fc None m (seg_rom rsegs)).

Lemma tl_seg1 : forall ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (rav s0v s1v s2v : word) (k : Z),
  0 <= k < 2 ^ 31 -> bv_unsigned sp + 32 < 2 ^ 64 ->
  rw_cells rsegs m (bv_unsigned sp) [C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  evt rsegs (tl_Q k sp gp tp s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 rav s0v s1v s2v F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 k) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15aa0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    rav s0v s1v s2v k Hk Hsp FR.
  apply tl_test; [exact Hk | |].
  - intros Hk0. eapply evt_mono; [eapply tl_epi; [exact Hsp | exact FR] |].
    intros ms' H. right. split; [exact Hk0 | exact H].
  - intros Hk0 x10 y18 Ey. subst y18. apply tl_call. intros r1 x12 E1 E2. subst r1 x12.
    apply evt_done. left. split; [exact Hk0|]. do 12 eexists. reflexivity.
Qed.

Lemma tl_seg2 : forall ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (rav s0v s1v s2v : word) (k : Z),
  1 <= k < 2 ^ 31 -> bv_unsigned sp + 32 < 2 ^ 64 ->
  rw_cells rsegs m (bv_unsigned sp) [C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  evt rsegs (tl_Q (k - 1) sp gp tp s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 rav s0v s1v s2v F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 k) s1 a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 0x1039d) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15abc) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    rav s0v s1v s2v k Hk Hsp FR.
  apply tl_back; [exact Hk | |].
  - intros Hk0 y8 Ey. subst y8. eapply evt_mono; [eapply tl_epi; [exact Hsp | exact FR] |].
    intros ms' H. right. split; [exact Hk0 | exact H].
  - intros Hk0 y8 Ey. subst y8. apply tl_call. intros r1 x12 E1 E2. subst r1 x12.
    apply evt_done. left. split; [exact Hk0|]. do 12 eexists. reflexivity.
Qed.
