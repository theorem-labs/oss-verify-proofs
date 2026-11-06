From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import rec_code_declared_c.
Import ListNotations.
Open Scope Z_scope.

Lemma rec_codes_range : Forall (fun v => -2^31 <= v < 2^31) rec_codes.
Proof. unfold rec_codes. repeat apply Forall_cons; try apply Forall_nil; cbv beta; lia. Qed.

Lemma rec_codes_bytes_length : length rec_codes_bytes = 232%nat.
Proof. reflexivity. Qed.

Lemma skipn_forall : forall (P : Z -> Prop) (x l : list Z) i v, Forall P x -> skipn i x = v :: l -> P v.
Proof.
  intros P x. induction x as [|y x IH]; intros l i v HF H; destruct i; cbn in H; try discriminate.
  - inversion H; subst. inversion HF; assumption.
  - inversion HF; subst. eapply IH; eassumption.
Qed.

Lemma skipn_next : forall (x l : list Z) i v, skipn i x = v :: l -> skipn (S i) x = l.
Proof.
  induction x as [|y x IH]; intros l i v H; destruct i; cbn in *; try discriminate.
  - inversion H; reflexivity.
  - eapply IH; eassumption.
Qed.

Lemma skipn_concat4 : forall (f : Z -> list byte) (x : list Z) i,
  (forall v, length (f v) = 4%nat) -> skipn (4 * i) (concat (map f x)) = concat (map f (skipn i x)).
Proof.
  intros f x. induction x as [|y x IH]; intros i Hf.
  - cbn [map concat]. rewrite !skipn_nil. reflexivity.
  - destruct i as [|i]; [reflexivity|].
    cbn [map concat skipn]. rewrite skipn_app, skipn_all2 by (rewrite Hf; lia). cbn [app].
    rewrite Hf. replace (4 * S i - 4)%nat with (4 * i)%nat by lia. apply IH. exact Hf.
Qed.

Lemma code_index : forall i v l, skipn i rec_codes = v :: l -> (i + S (length l) = 58)%nat.
Proof.
  intros i v l Hs. pose proof (f_equal (@length Z) Hs) as L. rewrite length_skipn in L.
  cbn [length] in L. change (length rec_codes) with 58%nat in L. lia.
Qed.

Lemma bytes_code : forall v, Z_to_le_bytes 4 (v mod 2^32) = le4 (Z_to_bv 64 v).
Proof.
  intros v. unfold le4. rewrite unsigned_lit_wrap.
  rewrite (Z_to_le_bytes_mod 4 v 32) by (cbn; lia). rewrite (Z_to_le_bytes_mod 4 v 64) by (cbn; lia). reflexivity.
Qed.

Lemma code_read : forall m i v l,
  bytes_at rsegs m REC_CODES rec_codes_bytes -> skipn i rec_codes = v :: l ->
  ov_read_bytes rsegs m (wa (REC_CODES + 4 * Z.of_nat i)) 4 = Some (le4 (Z_to_bv 64 v)).
Proof.
  intros m i v l HB Hs. pose proof (code_index i v l Hs) as Hi.
  rewrite (bytes_at_read rsegs m REC_CODES rec_codes_bytes (4 * Z.of_nat i) 4 HB)
    by (rewrite ?rec_codes_bytes_length; lia).
  f_equal. replace (Z.to_nat (4 * Z.of_nat i)) with (4 * i)%nat by lia.
  unfold rec_codes_bytes. rewrite skipn_concat4 by (intros; apply length_Z_to_le_bytes).
  rewrite Hs. cbn [map concat]. rewrite bytes_code.
  rewrite firstn_app, length_le4, Nat.sub_diag, firstn_O, app_nil_r.
  apply firstn_all2. rewrite length_le4. lia.
Qed.

Lemma sx32_lit : forall z, -2^31 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. f_equal. rewrite unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  change (2^64) with 18446744073709551616. change (2^31) with 2147483648 in Hz.
  Z.div_mod_to_equations. lia.
Qed.

Lemma eqb_lit : forall x y, -2^63 <= x < 2^63 -> -2^63 <= y < 2^63 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = Z.eqb x y.
Proof.
  intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit_wrap.
  change (2^64) with 18446744073709551616. change (2^63) with 9223372036854775808 in Hx, Hy.
  destruct (Z.eqb_spec x y) as [E|E]; [subst; apply Z.eqb_refl|].
  apply Z.eqb_neq. intros E'. apply E. Z.div_mod_to_equations. lia.
Qed.

Lemma rec_loop : forall (l : list Z) (i : nat) (A N : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : Z),
  -2^31 <= c < 2^31 ->
  bytes_at rsegs m REC_CODES rec_codes_bytes ->
  A = REC_CODES + 4 * Z.of_nat i -> N = 58 - Z.of_nat i ->
  skipn i rec_codes = l -> l <> [] ->
  evt rsegs
    (fun ms' => exists a1' a2' a3' : word,
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (if existsb (Z.eqb c) l then 1 else 0)) a1' a2' a3' a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (ret_pc ra) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 c) (Z_to_bv 64 A) (Z_to_bv 64 N) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x153e8) fc None m (seg_rom rsegs)).
Proof.
  induction l as [|v l IH];
    intros i A N ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m c
      Hc HB HA HN Hs Hne; [congruence|].
  pose proof (code_read m i v l HB Hs) as RD. rewrite <- HA in RD.
  pose proof (code_index i v l Hs) as Hi.
  pose proof (skipn_forall _ rec_codes l i v rec_codes_range Hs) as Hv. cbv beta in Hv.
  step. rewrite (sx32_lit v Hv).
  step. rewrite (eqb_lit v c) by lia.
  if_cases E1; zify_bool E1.
  - subst v. step. step. apply evt_done. cbn [existsb]. rewrite Z.eqb_refl. cbn [orb].
    do 3 eexists. reflexivity.
  - replace (existsb (Z.eqb c) (v :: l)) with (existsb (Z.eqb c) l)
      by (cbn [existsb]; rewrite (proj2 (Z.eqb_neq c v)) by congruence; reflexivity).
    step. step. step. rewrite (eqb_lit (N + -1) 0) by lia.
    if_cases E2; zify_bool E2.
    + destruct l as [|v' l']; [cbn [length] in Hi; lia|].
      eapply (IH (S i)); [exact Hc | exact HB | lia | lia | eapply skipn_next; exact Hs | congruence].
    + destruct l as [|v' l']; [|cbn [length] in Hi; lia].
      step. step. apply evt_done. do 3 eexists. reflexivity.
Qed.

Lemma rec_codes_in_image : forall m, mem_inv rsegs m -> bytes_at rsegs m REC_CODES rec_codes_bytes.
Proof.
  intros m Hm. apply ro_bytes_at; [exact Hm | unfold REC_CODES; lia | rewrite rec_codes_bytes_length; unfold REC_CODES; lia |].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Theorem rec_code_declared_holds : rec_code_declared_contract.
Proof.
  unfold rec_code_declared_contract, REC_CODE_DECLARED, declared.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m c Hc -> HB.
  step. step. step.
  eapply (rec_loop rec_codes 0%nat);
    [exact Hc | exact HB | reflexivity | reflexivity | reflexivity | unfold rec_codes; discriminate].
Qed.
