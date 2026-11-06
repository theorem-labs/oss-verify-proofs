From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import ManifestModel ManifestMem LibcNeeds_c plain_c.
Import ListNotations.
Open Scope Z_scope.

Lemma plain_skipn_S : forall (l rest : list byte) i b, skipn i l = b :: rest -> skipn (S i) l = rest.
Proof.
  induction l as [|a l IH]; intros rest i b H; destruct i; cbn in *; try discriminate.
  - inversion H; reflexivity.
  - eapply IH. exact H.
Qed.

Lemma plain_name_snoc : forall (t : list Z) c, plain_name (t ++ [c]) = negb (c =? 46) && forallb plain_ok (t ++ [c]).
Proof.
  intros t c. unfold plain_name. rewrite last_last.
  destruct (t ++ [c]) eqn:E; [exfalso; exact (app_cons_not_nil t [] c (eq_sym E)) | reflexivity].
Qed.

Lemma plain_byte_all : forall (P : Z -> bool), forallb P (map Z.of_nat (seq 0 256)) = true ->
  forall b : byte, P (bv_unsigned b) = true.
Proof.
  intros P H b. rewrite forallb_forall in H. apply H. apply in_map_iff.
  assert (R : 0 <= bv_unsigned b < 256) by (pose proof (bv_unsigned_in_range 8 b) as R; exact R).
  exists (Z.to_nat (bv_unsigned b)). split; [apply Z2Nat.id; lia | apply in_seq; lia].
Qed.

Definition plain_t1 (z : Z) : bool := bv_ltu (Z_to_bv 64 (-11)) (Z_to_bv 64 (z + -58)).
Definition plain_t2 (z : Z) : bool := bv_ltu (Z_to_bv 64 (-27)) (Z_to_bv 64 (Z.land z 223 + -91)).
Definition plain_t3 (z : Z) : bool := bv_ltu (Z_to_bv 64 50) (Z_to_bv 64 (z + -45)).
Definition plain_t4 (z : Z) : bool :=
  bv_eqb (Z_to_bv 64 (Z.land (Z.shiftr 1125899906850819 (((z + -45) mod 18446744073709551616) mod 64)) 1))
    (Z_to_bv 64 0).

Lemma plain_t1_ok : forall b : byte, plain_t1 (bv_unsigned b) = true -> plain_ok (bv_unsigned b) = true.
Proof.
  intros b H. pose proof (plain_byte_all (fun z => implb (plain_t1 z) (plain_ok z)) ltac:(vm_compute; reflexivity) b) as BF.
  cbv beta in BF. rewrite H in BF. exact BF.
Qed.

Lemma plain_t2_ok : forall b : byte, plain_t2 (bv_unsigned b) = true -> plain_ok (bv_unsigned b) = true.
Proof.
  intros b H. pose proof (plain_byte_all (fun z => implb (plain_t2 z) (plain_ok z)) ltac:(vm_compute; reflexivity) b) as BF.
  cbv beta in BF. rewrite H in BF. exact BF.
Qed.

Lemma plain_t3_bad : forall b : byte, plain_t1 (bv_unsigned b) = false -> plain_t2 (bv_unsigned b) = false ->
  plain_t3 (bv_unsigned b) = true -> plain_ok (bv_unsigned b) = false.
Proof.
  intros b H1 H2 H3.
  pose proof (plain_byte_all (fun z => implb (negb (plain_t1 z) && negb (plain_t2 z) && plain_t3 z) (negb (plain_ok z)))
    ltac:(vm_compute; reflexivity) b) as BF.
  cbv beta in BF. rewrite H1, H2, H3 in BF. exact (proj1 (negb_true_iff _) BF).
Qed.

Lemma plain_t4_bad : forall b : byte, plain_t1 (bv_unsigned b) = false -> plain_t2 (bv_unsigned b) = false ->
  plain_t3 (bv_unsigned b) = false -> plain_t4 (bv_unsigned b) = true -> plain_ok (bv_unsigned b) = false.
Proof.
  intros b H1 H2 H3 H4.
  pose proof (plain_byte_all (fun z => implb (negb (plain_t1 z) && negb (plain_t2 z) && negb (plain_t3 z) && plain_t4 z) (negb (plain_ok z)))
    ltac:(vm_compute; reflexivity) b) as BF.
  cbv beta in BF. rewrite H1, H2, H3, H4 in BF. exact (proj1 (negb_true_iff _) BF).
Qed.

Lemma plain_t4_ok : forall b : byte, plain_t1 (bv_unsigned b) = false -> plain_t2 (bv_unsigned b) = false ->
  plain_t3 (bv_unsigned b) = false -> plain_t4 (bv_unsigned b) = false -> plain_ok (bv_unsigned b) = true.
Proof.
  intros b H1 H2 H3 H4.
  pose proof (plain_byte_all (fun z => implb (negb (plain_t1 z) && negb (plain_t2 z) && negb (plain_t3 z) && negb (plain_t4 z)) (plain_ok z))
    ltac:(vm_compute; reflexivity) b) as BF.
  cbv beta in BF. rewrite H1, H2, H3, H4 in BF. exact BF.
Qed.

Section Loop.
Variables (ra sp gp tp t0 t1 t2 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (s : Z) (l : list byte).
Hypothesis BL : bytes_at rsegs m s l.

Definition plain_at (pc : Z) (p q a1 a6 : word) : machine_state :=
  MS (mkR ra sp gp tp t0 t1 t2 p s1 q a1 (Z_to_bv 64 (-11)) (Z_to_bv 64 (-27)) (Z_to_bv 64 50)
        (Z_to_bv 64 1125899906850819) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
     F (Z_to_bv 64 pc) fc None m (seg_rom rsegs).

Definition plain_out (r : Z) : machine_state -> Prop :=
  fun ms' => exists p q a6, ms' = plain_at 0x13bf0 p q (Z_to_bv 64 r) a6.

Lemma plain_loop : forall k i p q a1 a6, (i + S k = length l)%nat ->
  bv_unsigned p = s + Z.of_nat i -> bv_unsigned q = Z.of_nat (S k) ->
  evt rsegs (plain_out (if forallb plain_ok (zbytes (skipn i l)) then 1 else 0)) (plain_at 0x13bb0 p q a1 a6).
Proof.
  induction k as [k IH] using lt_wf_ind.
  intros i p q a1 a6 HI Hp Hq.
  pose proof (bytes_at_bound _ _ _ _ BL) as BB.
  destruct (skipn i l) as [|b rest] eqn:SK.
  { exfalso. apply (f_equal (@length byte)) in SK. rewrite length_skipn in SK. cbn in SK. lia. }
  pose proof (f_equal (@length byte) SK) as LR. rewrite length_skipn in LR. cbn [length] in LR.
  assert (HR : ov_read_bytes rsegs m p 1 = Some [b]).
  { rewrite <- (wa_of_var p _ Hp). rewrite (bytes_at_read rsegs m s l (Z.of_nat i) 1 BL) by lia.
    rewrite Nat2Z.id, SK. reflexivity. }
  change (zbytes (b :: rest)) with (bv_unsigned b :: zbytes rest). cbn [forallb].
  assert (ACC : plain_ok (bv_unsigned b) = true -> forall a1' a6',
    evt rsegs (plain_out (if plain_ok (bv_unsigned b) && forallb plain_ok (zbytes rest) then 1 else 0))
      (plain_at 0x13be0 p q a1' a6')).
  { intros POK a1' a6'. rewrite POK. cbn [andb].
    unfold plain_at. zstep. zstep. rewrite Hq. zstep.
    if_cases HC; zify_cond HC.
    - destruct k as [|k']; [exfalso; lia|].
      rewrite <- (plain_skipn_S _ _ _ _ SK).
      eapply (IH k' (Nat.lt_succ_diag_r k') (S i)); [lia| |].
      + rewrite inr64_unsigned_lit by (unfold inr64; lia). lia.
      + rewrite inr64_unsigned_lit by (unfold inr64; lia). lia.
    - assert (k = 0)%nat by lia. subst k. destruct rest; [|cbn in LR; lia].
      zstep. apply evt_done. unfold plain_out, plain_at. do 3 eexists. reflexivity. }
  unfold plain_at. do 3 zstep.
  if_cases H1.
  { eapply ACC. exact (plain_t1_ok b H1). }
  do 3 zstep.
  if_cases H2.
  { eapply ACC. exact (plain_t2_ok b H2). }
  do 3 zstep.
  if_cases H3.
  { rewrite (plain_t3_bad b H1 H2 H3). cbn [andb].
    apply evt_done. unfold plain_out, plain_at. do 3 eexists. reflexivity. }
  do 3 zstep.
  if_cases H4.
  { rewrite (plain_t4_bad b H1 H2 H3 H4). cbn [andb].
    apply evt_done. unfold plain_out, plain_at. do 3 eexists. reflexivity. }
  eapply ACC. exact (plain_t4_ok b H1 H2 H3 H4).
Qed.

End Loop.

Theorem plain_holds : strlen_contract -> plain_contract.
Proof.
  intros STRLEN. unfold plain_contract, PLAIN, PLAIN_K.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    bs slack CS MI ST LO DJ.
  destruct CS as [BA [NZ AL]]. unfold off_stack in DJ.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  assert (L0 : 0 <= lo) by (destruct ST as [? _]; lia).
  pose proof (bytes_at_bound _ _ _ _ BA) as BB. rewrite length_app in BB. cbn [length] in BB.
  carve_frame 16%nat ST.
  do 5 zstep.
  assert (SP16 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16)) = bv_unsigned sp + -16)
    by (apply inr64_unsigned_lit; unfold inr64; lia).
  eapply evt_cut.
  { eapply STRLEN with (bs := bs) (slack := slack).
    - split; [exact BA | split; assumption].
    - exact MI.
    - rewrite SP16. exact ST. }
  intros ms' POST.
  destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 &
    E & MUc & WMc & MIc & STc & Ra0).
  subst ms' a0'. rewrite SP16 in MUc, STc.
  replace (ret_pc (Z_to_bv 64 80744)) with (Z_to_bv 64 80744) by (apply bv_eq; vm_compute; reflexivity).
  transport_after_call rsegs m1 m2 MUc WMc.
  clear SP16 MUc WMc MI.
  destruct (Nat.eq_dec (length bs) 0) as [HB0|HB0].
  - apply length_zero_iff_nil in HB0. subst bs. cbn [length Z.of_nat] in *.
    zstep. if_true. do 6 zstep.
    release_frame FR ST (bv_unsigned sp). zstep. finish. reflexivity.
  - destruct (exists_last (l := bs) ltac:(destruct bs; [contradiction|discriminate])) as [pre [x EB]].
    assert (HLB : length bs = S (length pre)) by (rewrite EB, length_app; cbn; lia).
    zstep.
    if_cases HC.
    + exfalso. zify_cond HC. lia.
    + do 3 zstep.
      if_cases HU.
      { exfalso. zify_cond HU. rewrite zb_lxor_ones in HU by (apply zr_word). lia. }
      assert (HR : ov_read_bytes rsegs m2 (wa (bv_unsigned a0 + Z.of_nat (length pre))) 1 = Some [x]).
      { rewrite (bytes_at_read rsegs m2 (bv_unsigned a0) _ (Z.of_nat (length pre)) 1 BA) by
          (rewrite ?length_app; cbn [length]; lia).
        rewrite Nat2Z.id, EB, <- app_assoc. rewrite skipn_app, skipn_all, Nat.sub_diag. reflexivity. }
      do 4 zstep.
      if_cases HC2.
      * zify_cond HC2.
        do 8 zstep.
        pose proof (proj1 (bytes_at_app rsegs m2 (bv_unsigned a0) bs (Z_to_bv 8 0 :: slack)) BA) as [BS _].
        eapply evt_cut.
        { eapply plain_loop with (s := bv_unsigned a0) (l := bs) (k := length pre) (i := 0%nat).
          all: first [ exact BS | lia | rewrite inr64_unsigned_lit by (unfold inr64; lia); lia ]. }
        intros ms' (pl & ql & a6l & ->). unfold plain_at.
        do 4 zstep.
        release_frame FR ST (bv_unsigned sp). zstep. finish.
        change (skipn 0 bs) with bs. rewrite EB. unfold zbytes. rewrite map_app. cbn [map]. rewrite plain_name_snoc.
        rewrite (proj2 (Z.eqb_neq _ _) HC2). reflexivity.
      * zify_cond HC2.
        do 6 zstep.
        release_frame FR ST (bv_unsigned sp). zstep. finish.
        rewrite EB. unfold zbytes. rewrite map_app. cbn [map]. rewrite plain_name_snoc, HC2. reflexivity.
Qed.
