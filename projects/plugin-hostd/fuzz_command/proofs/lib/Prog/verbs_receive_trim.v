From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes Image Arr.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Import Verbs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import VerbsMem verbs_receive_words verbs_receive_disp strtok_r_c strlen_c.
Import ListNotations.
Open Scope Z_scope.

Definition TRIM_AT : Z := 0x17468.
Definition VR_STRDUP : Z := 0x20d64.
Definition trim_s (U : list byte) : list byte := rev (dropw is_trail (rev U)).

Definition trim_post (sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lb : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (U slack : list byte) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR (Z_to_bv 64 0x174b4) sp gp tp t0' t1' t2' lb s1 lb a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (Z_to_bv 64 VR_STRDUP) fc None m' (seg_rom rsegs) /\
    u8arr rsegs m' (bv_unsigned lb)
      (trim_s U ++ repeat (Z_to_bv 8 0) (length U - length (trim_s U)) ++ [Z_to_bv 8 0]) /\
    bytes_at rsegs m' (bv_unsigned lb + Z.of_nat (length U) + 1) slack /\
    rw_cells rsegs m' (bv_unsigned sp) [C8 (Z_to_bv 64 0)] /\
    munch [(bv_unsigned sp, bv_unsigned sp + 8); (bv_unsigned lb, bv_unsigned lb + Z.of_nat (length U) + 1)] m m' /\
    wmono rsegs m m' /\ mem_inv rsegs m'.

Lemma upd_mid : forall {X} (l1 : list X) y x l2 i, i = length l1 -> upd (l1 ++ y :: l2) i x = l1 ++ x :: l2.
Proof. intros X l1 y x l2 i ->. induction l1 as [|z l1 IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma nth_mid : forall {X} (l1 : list X) y l2 i, i = length l1 -> nth_error (l1 ++ y :: l2) i = Some y.
Proof. intros X l1 y l2 i ->. induction l1 as [|z l1 IH]; cbn; [reflexivity | exact IH]. Qed.

Lemma firstn_S_snoc : forall (U : list byte) j b, nth_error U j = Some b -> firstn (S j) U = firstn j U ++ [b].
Proof.
  induction U as [|x U IH]; intros [|j] b H; cbn in H |- *; try discriminate.
  - inversion H. reflexivity.
  - rewrite (IH j b H). reflexivity.
Qed.

Lemma trim_snoc_t : forall P b, is_trail b = true -> trim_s (P ++ [b]) = trim_s P.
Proof. intros P b H. unfold trim_s. rewrite rev_app_distr. cbn [rev app dropw]. rewrite H. reflexivity. Qed.

Lemma trim_snoc_k : forall P b, is_trail b = false -> trim_s (P ++ [b]) = P ++ [b].
Proof.
  intros P b H. unfold trim_s. rewrite rev_app_distr. cbn [rev app dropw]. rewrite H.
  cbn [rev]. rewrite rev_involutive. reflexivity.
Qed.

Lemma trail_bit : forall b : byte, bv_unsigned b <= 32 ->
  Z.land (Z.shiftr 4294977024 (bv_unsigned b mod 64)) 1 = if is_trail b then 1 else 0.
Proof.
  intros b Hb. unfold is_trail, is_sep.
  pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R.
  remember (bv_unsigned b) as z eqn:Ez. clear Ez.
  rewrite <- (Z2Nat.id z) by lia. assert (N : (Z.to_nat z <= 32)%nat) by lia.
  remember (Z.to_nat z) as n eqn:En. clear En.
  do 33 (destruct n as [|n]; [vm_compute; reflexivity|]). lia.
Qed.

Lemma trail_gt : forall b : byte, 32 < bv_unsigned b -> is_trail b = false.
Proof.
  intros b H. unfold is_trail, is_sep.
  rewrite (proj2 (Z.eqb_neq (bv_unsigned b) 32)), (proj2 (Z.eqb_neq (bv_unsigned b) 9)),
    (proj2 (Z.eqb_neq (bv_unsigned b) 10)), (proj2 (Z.eqb_neq (bv_unsigned b) 13)) by lia.
  reflexivity.
Qed.

Lemma ltu_lit_byte : forall (b : byte) c, 0 <= c < 2^64 ->
  bv_ltu (Z_to_bv 64 c) (Z_to_bv 64 (bv_unsigned b)) = (c <? bv_unsigned b).
Proof.
  intros b c Hc. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R.
  unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity.
Qed.

Lemma trim_exit : forall (sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lb : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 : word -> option byte) (U slack : list byte)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : word -> option byte),
  u8arr rsegs m (bv_unsigned lb) (trim_s U ++ repeat (Z_to_bv 8 0) (length U - length (trim_s U)) ++ [Z_to_bv 8 0]) ->
  bytes_at rsegs m (bv_unsigned lb + Z.of_nat (length U) + 1) slack ->
  rw_cells rsegs m (bv_unsigned sp) [C8 (Z_to_bv 64 0)] ->
  munch [(bv_unsigned sp, bv_unsigned sp + 8); (bv_unsigned lb, bv_unsigned lb + Z.of_nat (length U) + 1)] m0 m ->
  wmono rsegs m0 m -> mem_inv rsegs m ->
  evt rsegs (trim_post sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lb F fc m0 U slack)
    (MS (mkR ra sp gp tp t0 t1 t2 lb s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x174ac) fc None m (seg_rom rsegs)).
Proof.
  intros sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lb F fc m0 U slack ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m
    HA HS HSP MU WM HMI.
  do 2 zstep.
  apply evt_done. unfold trim_post. do 15 eexists. split; [reflexivity|].
  exact (conj HA (conj HS (conj HSP (conj MU (conj WM HMI))))).
Qed.

Lemma trim_loop : forall (sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lb : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 : word -> option byte) (U slack : list byte),
  bv_unsigned lb + Z.of_nat (length U) + 1 + Z.of_nat (length slack) <= bv_unsigned sp \/
    bv_unsigned sp + 8 <= bv_unsigned lb ->
  0 < bv_unsigned lb ->
  forall (k : nat) (ra t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : word -> option byte),
  (1 <= k <= length U)%nat ->
  u8arr rsegs m (bv_unsigned lb) (firstn k U ++ repeat (Z_to_bv 8 0) (length U - k) ++ [Z_to_bv 8 0]) ->
  trim_s U = trim_s (firstn k U) ->
  bytes_at rsegs m (bv_unsigned lb + Z.of_nat (length U) + 1) slack ->
  rw_cells rsegs m (bv_unsigned sp) [C8 (Z_to_bv 64 0)] ->
  munch [(bv_unsigned sp, bv_unsigned sp + 8); (bv_unsigned lb, bv_unsigned lb + Z.of_nat (length U) + 1)] m0 m ->
  wmono rsegs m0 m -> mem_inv rsegs m ->
  evt rsegs (trim_post sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lb F fc m0 U slack)
    (MS (mkR ra sp gp tp t0 t1 t2 lb s1 (Z_to_bv 64 (bv_unsigned lb + Z.of_nat k)) (Z_to_bv 64 32)
             (Z_to_bv 64 4294977024) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1748c) fc None m (seg_rom rsegs)).
Proof.
  intros sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lb F fc m0 U slack HDJ HLB k.
  induction k as [|j IH]; intros ra t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m HK HA HT HS HSP MU WM HMI; [lia|].
  destruct (nth_error U j) as [b|] eqn:NB; [| apply nth_error_None in NB; lia].
  rewrite (firstn_S_snoc U j b NB) in HA, HT.
  rewrite <- app_assoc in HA. cbn [app] in HA.
  assert (LJ : length (firstn j U) = j) by (apply firstn_length_le; lia).
  assert (LA : length (firstn j U ++ b :: repeat (Z_to_bv 8 0) (length U - S j) ++ [Z_to_bv 8 0]) = S (length U)).
  { rewrite length_app, LJ. cbn [length]. rewrite length_app, repeat_length. cbn [length]. lia. }
  pose proof (u8arr_bound rsegs _ _ _ HA) as BA. rewrite LA in BA.
  pose proof (bv_unsigned_in_range 8 b) as RB. unfold bv_modulus in RB. change (2 ^ Z.of_N 8) with 256 in RB.
  pose proof (bytes_at_bound rsegs _ _ _ HS) as BS.
  assert (RD : ov_read_bytes rsegs m (wa (bv_unsigned lb + Z.of_nat j)) 1 = Some [b]).
  { eapply u8arr_read with (i := Z.of_nat j); [exact HA | | lia | reflexivity].
    rewrite Nat2Z.id. apply nth_mid. symmetry. exact LJ. }
  zstep. zstep.
  rewrite ltu_lit_byte by lia.
  destruct (Z.ltb_spec 32 (bv_unsigned b)) as [GT|LE]; cbv beta iota.
  - eapply trim_exit; [| eassumption | eassumption | eassumption | eassumption | eassumption].
    rewrite HT, trim_snoc_k by (apply trail_gt; lia).
    rewrite length_app, LJ. cbn [length].
    replace (length U - (j + 1))%nat with (length U - S j)%nat by lia.
    rewrite <- app_assoc. exact HA.
  - zstep. zstep. zstep.
    rewrite trail_bit by lia. rewrite eqb_ite.
    destruct (is_trail b) eqn:TB; cbv beta iota delta [negb].
    + zstep.
      pose proof (u8arr_store_ok rsegs m (bv_unsigned lb) _ (Z.of_nat j) (wa (bv_unsigned lb + Z.of_nat j)) HA
                    ltac:(rewrite LA; lia) eq_refl) as SOK.
      pose proof (u8arr_write rsegs m (bv_unsigned lb) _ (Z.of_nat j) (Z_to_bv 8 0) HA ltac:(rewrite LA; lia)) as HA2.
      zstep.
      replace (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0] by reflexivity.
      store_done.
      rewrite Nat2Z.id, (upd_mid (firstn j U) b (Z_to_bv 8 0) _ j (eq_sym LJ)) in HA2.
      replace (Z_to_bv 8 0 :: repeat (Z_to_bv 8 0) (length U - S j) ++ [Z_to_bv 8 0])
        with (repeat (Z_to_bv 8 0) (length U - j) ++ [Z_to_bv 8 0]) in HA2
        by (replace (length U - j)%nat with (S (length U - S j)) by lia; reflexivity).
      rewrite (trim_snoc_t _ _ TB) in HT.
      zstep.
      unfold bv_ltu. rewrite (unsigned_lit (bv_unsigned lb + Z.of_nat (S j) + -1)) by lia.
      destruct j as [|j'].
      * if_false.
        eapply trim_exit; [| eassumption | eassumption | eassumption | eassumption | eassumption].
        rewrite HT. exact HA2.
      * if_true.
        replace (bv_unsigned lb + Z.of_nat (S (S j')) + -1) with (bv_unsigned lb + Z.of_nat (S j')) by lia.
        eapply IH; [lia | exact HA2 | exact HT | eassumption | eassumption | eassumption | eassumption | eassumption].
    + eapply trim_exit; [| eassumption | eassumption | eassumption | eassumption | eassumption].
      rewrite HT, trim_snoc_k by exact TB.
      rewrite length_app, LJ. cbn [length].
      replace (length U - (j + 1))%nat with (length U - S j)%nat by lia.
      rewrite <- app_assoc. exact HA.
Qed.

Theorem vr_trim : strlen_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (U slack junk : list byte),
    u8arr rsegs m (bv_unsigned a0) (U ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) U ->
    bytes_at rsegs m (bv_unsigned a0 + Z.of_nat (length U) + 1) slack ->
    (- (bv_unsigned a0 + Z.of_nat (length U) + 1)) mod 8 <= Z.of_nat (length slack) ->
    0 < bv_unsigned a0 ->
    rw_cells rsegs m (bv_unsigned sp) [CB 8 junk] ->
    bv_unsigned a0 + Z.of_nat (length U) + 1 + Z.of_nat (length slack) <= bv_unsigned sp \/
      bv_unsigned sp + 8 <= bv_unsigned a0 ->
    mem_inv rsegs m ->
    evt rsegs (trim_post sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 F fc m U slack)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 TRIM_AT) fc None m (seg_rom rsegs)).
Proof.
  intros SLEN ra sp gp tp t0 t1 t2 s0 s1 lb a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m U slack junk HU HZ HS HAL HLB HSP HDJ HMI.
  pose proof (munch_refl [(bv_unsigned sp, bv_unsigned sp + 8);
    (bv_unsigned lb, bv_unsigned lb + Z.of_nat (length U) + 1)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (u8arr_bound rsegs _ _ _ HU) as BU. rewrite length_app in BU. cbn [length] in BU.
  pose proof (bytes_at_bound rsegs _ _ _ HS) as BS.
  pose proof (rw_cells_bound rsegs _ _ _ HSP) as BSP. cbn [cells_size csize Nat.add] in BSP.
  unfold TRIM_AT.
  zstep.
  assert (SOK : store_ok rsegs m sp 8 = true).
  { exact (rw_cells_store_ok_at rsegs m (bv_unsigned sp) [CB 8 junk] 0%nat (CB 8 junk) 8%nat sp HSP eq_refl eq_refl
             ltac:(symmetry; apply wa_of_var; lia)). }
  zstep.
  replace (write_to_mem m sp) with (write_to_mem m (wa (bv_unsigned sp + Z.of_nat 0)))
    by (f_equal; first [apply wa_of_var | symmetry; apply wa_of_var]; lia).
  clear SOK.
  mem_after_store.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  zstep.
  eapply evt_cut.
  { eapply SLEN with (str := U) (slack := slack).
    - replace (U ++ Z_to_bv 8 0 :: slack) with ((U ++ [Z_to_bv 8 0]) ++ slack) by (rewrite <- app_assoc; reflexivity).
      apply bytes_at_app. split; [exact (proj1 HU) |].
      rewrite length_app. cbn [length].
      replace (bv_unsigned lb + Z.of_nat (length U + 1)) with (bv_unsigned lb + Z.of_nat (length U) + 1) by lia.
      exact HS.
    - exact HZ.
    - exact HAL.
    - exact HMI. }
  post_call rsegs m1.
  zstep.
  rewrite eqb_lit by lia.
  destruct (Z.eqb_spec (Z.of_nat (length U)) 0) as [L0|L0]; cbv beta iota.
  - assert (UE : U = []) by (apply length_zero_iff_nil; lia). subst U.
    eapply trim_exit; [exact HU | eassumption | eassumption | eassumption | eassumption | eassumption].
  - do 5 zstep.
    eapply trim_loop; [exact HDJ | exact HLB | lia | | | eassumption | eassumption | eassumption | eassumption |
                       eassumption].
    + rewrite firstn_all, Nat.sub_diag. exact HU.
    + rewrite firstn_all. reflexivity.
Qed.
