(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require NDestr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Tac.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require StrwF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module F_memchr.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Section CANSEC1. Context {rc : runConstT}.
Definition memchr_entry := 0x9e5a4%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section ZFacts.
  Open Scope Z_scope.
  #[using="Type"] Lemma lxor_lt_256 : forall a b, 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lxor a b < 256.
  Proof.
    intros a b Ha Hb. pose proof (Z.lxor_nonneg a b) as Hnn. split; [lia|].
    destruct (Z.eq_dec (Z.lxor a b) 0) as [->|Hnz]; [lia|].
    apply (proj2 (Z.log2_lt_pow2 (Z.lxor a b) 8 ltac:(lia))).
    pose proof (Z.log2_lxor a b ltac:(lia) ltac:(lia)) as Hl.
    assert (Z.log2 a < 8). { destruct (Z.eq_dec a 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia. }
    assert (Z.log2 b < 8). { destruct (Z.eq_dec b 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia. }
    lia.
  Qed.

  #[using="Type"] Lemma lxor_split : forall x y x' y', 0 <= x < 256 -> 0 <= x' < 256 -> 0 <= y -> 0 <= y' ->
    Z.lxor (x + 256 * y) (x' + 256 * y') = Z.lxor x x' + 256 * Z.lxor y y'.
  Proof.
    intros x y x' y' Hx Hx' Hy Hy'.
    pose proof (lxor_lt_256 x x' Hx Hx') as Hl.
    apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec, !testbit_split by lia.
    destruct (i <? 8); rewrite Z.lxor_spec; reflexivity.
  Qed.

  #[using="Type"] Lemma le_val_nonneg : forall bs, bytes_ok bs -> 0 <= le_val bs.
  Proof. intros bs H. pose proof (le_val_range bs H). lia. Qed.

  #[using="Type"] Lemma le_val_xor_bcast : forall bs c, bytes_ok bs -> 0 <= c < 256 ->
    Z.lxor (le_val bs) (c * ones (length bs)) = le_val (map (fun b => Z.lxor b c) bs).
  Proof.
    induction bs as [|b bs IH]; intros c Hok Hc.
    - cbn. rewrite Z.mul_0_r. reflexivity.
    - inversion Hok as [|b0 bs0 Hb Hbs]; subst. cbn [le_val ones length map].
      replace (c * (1 + 256 * ones (length bs))) with (c + 256 * (c * ones (length bs))) by lia.
      rewrite lxor_split; try lia.
      + rewrite IH by assumption. reflexivity.
      + apply le_val_nonneg. exact Hbs.
      + pose proof (le_val_range (repeat 1 (length bs))) as Hr. assert (0 <= ones (length bs)); [|nia].
        clear. induction (length bs); cbn; lia.
  Qed.

  #[using="Type"] Lemma bytes_ok_xor : forall bs c, bytes_ok bs -> 0 <= c < 256 -> bytes_ok (map (fun b => Z.lxor b c) bs).
  Proof.
    intros bs c H Hc. unfold bytes_ok in *. rewrite Forall_map. eapply Forall_impl; [|exact H].
    intros b Hb. apply lxor_lt_256; assumption.
  Qed.

  #[using="Type"] Lemma In0_xor : forall bs c, In 0 (map (fun b => Z.lxor b c) bs) <-> In c bs.
  Proof.
    intros bs c. rewrite in_map_iff. split.
    - intros (b & Hb & Hin). apply Z.lxor_eq in Hb. subst. exact Hin.
    - intros Hin. exists c. split; [apply Z.lxor_nilpotent| exact Hin].
  Qed.
End ZFacts.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition memchr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 a2 : word) (buf : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
                 (Z_to_bv 64 (memchr_res (bv_unsigned a0) (bv_unsigned a1 mod 256) (bv_unsigned a2) buf))
                 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ bytes_at asegs m' (bv_unsigned a0) buf.

Section Proofs.
  Variables (RNG : footprint) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (buf : list byte).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis BUF : bytes_at asegs m (bv_unsigned a0) buf.
  Hypothesis OK : memchr_ok (bv_unsigned a0) (bv_unsigned a1 mod 256) (bv_unsigned a2) buf.
  (* [comment removed for export] *)
  Hypothesis RB : rng RNG (bv_unsigned a0) (Z.of_nat (length buf)).
  Hypothesis RIMG : rng_aimg RNG.
  Let MU : munch [] m m := munch_refl [] m.
  Let WM : wmono asegs m m := wmono_refl asegs m.

  Notation A := (bv_unsigned a0).
  Notation n := (bv_unsigned a2).
  Notation c := ((bv_unsigned a1) mod 256)%Z.
  Notation len := (Z.of_nat (length buf)).
  Notation POST := (memchr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 buf m).
  (* [comment removed for export] *)
  Notation ST pc x5 x10 x12 x13 x14 x15 x16 x17 :=
    (MS (mkR ra sp gp tp x5 t1 t2 s0 s1 x10 (Z_to_bv 64 c) x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom asegs)).
  Notation CMAGIC := 72340172838076672%Z.      (* [comment removed for export] *)
  Notation HIGHS := 9259542123273814144%Z.     (* [comment removed for export] *)
  Notation ONES := 72340172838076673%Z.       (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition NOB (i : Z) : Prop :=
    forall j b, (j < Z.to_nat i)%nat -> nth_error buf j = Some b -> bv_unsigned b <> c.

  #[using="m BUF"] Lemma A_bound : (0 <= A /\ A + len <= 2^64 /\ 0 <= n < 2^64 /\ 0 <= c < 256)%Z.
  Proof.
    pose proof (bytes_at_bound _ _ _ _ BUF).
    pose proof (bv_unsigned_in_range 64 a2) as R. unfold bv_modulus in R. cbn in R.
    pose proof (Z.mod_pos_bound (bv_unsigned a1) 256). cbn. lia.
  Qed.

  #[using="Type"] Lemma NOB_0 : NOB 0.
  Proof. intros j b Hj. cbn in Hj. lia. Qed.

  #[using="Type"] Lemma NOB_S : forall i b, (0 <= i)%Z -> NOB i -> nth_error buf (Z.to_nat i) = Some b -> bv_unsigned b <> c -> NOB (i + 1).
  Proof.
    intros i b Hi H Hn Hb j b' Hj Hn'.
    destruct (Nat.eq_dec j (Z.to_nat i)) as [->|NE]. { rewrite Hn in Hn'. injection Hn' as <-. exact Hb. }
    eapply H; [|exact Hn']. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="OK"] Lemma ok_cases :
    (exists j b, Z.of_nat j < n /\ nth_error buf j = Some b /\ bv_unsigned b = c /\
       (forall j' b', (j' < j)%nat -> nth_error buf j' = Some b' -> bv_unsigned b' <> c) /\
       (n <= len \/ Z.of_nat j + 1 + (- (A + Z.of_nat j + 1)) mod 8 <= len))%Z
    \/ ((forall j b, (Z.of_nat j < n)%Z -> nth_error buf j = Some b -> bv_unsigned b <> c) /\ (n <= len)%Z).
  Proof.
    pose proof OK as H. unfold memchr_ok in H.
    destruct (find_byte c (firstn (Z.to_nat n) buf)) as [j|] eqn:FB.
    - left. (nd_pre (find_byte_Some _ _ _ FB) 3%nat; intros Hl (b & Hn & Hb) Hmin; nd_post).
      rewrite firstn_length in Hl.
      rewrite nth_error_firstn in Hn. replace (Nat.ltb j (Z.to_nat n)) with true in Hn by (symmetry; apply Nat.ltb_lt; lia).
      exists j, b. repeat split; try assumption; try lia.
      intros j' b' Hj' Hn'. eapply Hmin; [exact Hj'|]. rewrite nth_error_firstn.
      replace (Nat.ltb j' (Z.to_nat n)) with true by (symmetry; apply Nat.ltb_lt; lia). exact Hn'.
    - right. split; [|exact H]. intros j b Hj Hn. eapply (find_byte_None _ _ FB j). rewrite nth_error_firstn.
      replace (Nat.ltb j (Z.to_nat n)) with true by (symmetry; apply Nat.ltb_lt; lia). exact Hn.
  Qed.

  #[using="a0 OK"] Lemma readable : forall i, (0 <= i < n)%Z -> NOB i -> exists b, nth_error buf (Z.to_nat i) = Some b.
  Proof.
    intros i Hi HN. destruct (nth_error buf (Z.to_nat i)) as [b|] eqn:E; [exists b; reflexivity|].
    exfalso. apply nth_error_None in E.
    destruct ok_cases as [(j & b & Hj & Hn & Hb & Hmin & _)|(Hall & Hlen)]; [|lia].
    pose proof (nth_error_lt _ _ _ Hn).
    destruct (Nat.lt_ge_cases j (Z.to_nat i)) as [Hlt|Hge]; [|lia].
    exact (HN _ _ Hlt Hn Hb).
  Qed.

  #[using="OK"] Lemma readable8 : forall i, (0 <= i)%Z -> (i + 8 <= n)%Z -> ((A + i) mod 8 = 0)%Z -> NOB i ->
    (Z.to_nat i + 8 <= length buf)%nat.
  Proof.
    intros i Hi Hi8 Hal HN.
    destruct ok_cases as [(j & b & Hj & Hn & Hb & Hmin & Hsl)|(Hall & Hlen)]; [|lia].
    pose proof (nth_error_lt _ _ _ Hn).
    destruct (Nat.lt_ge_cases j (Z.to_nat i)) as [Hlt|Hge]. { exfalso. exact (HN _ _ Hlt Hn Hb). }
    destruct Hsl as [Hsl|Hsl]; [lia|].
    destruct (Nat.lt_ge_cases j (Z.to_nat i + 8)) as [Hlt8|]; [|lia].
    Z.div_mod_to_equations. lia.
  Qed.

  #[using="Type"] Lemma res_found : forall i b, (0 <= i < n)%Z -> NOB i -> nth_error buf (Z.to_nat i) = Some b -> bv_unsigned b = c ->
    memchr_res A c n buf = (A + i)%Z.
  Proof.
    intros i b Hi HN Hn Hb. unfold memchr_res.
    rewrite (find_byte_charact c _ (Z.to_nat i) b); [lia| | exact Hb|].
    - rewrite nth_error_firstn. replace (Nat.ltb _ _) with true by (symmetry; apply Nat.ltb_lt; lia). exact Hn.
    - intros j b' Hj Hn'. rewrite nth_error_firstn in Hn'. destruct (Nat.ltb j (Z.to_nat n)); [|discriminate].
      exact (HN _ _ Hj Hn').
  Qed.

  #[using="Type"] Lemma res_none : NOB n -> memchr_res A c n buf = 0%Z.
  Proof.
    intros HN. unfold memchr_res. rewrite find_byte_None_intro; [reflexivity|].
    intros j b Hn. rewrite nth_error_firstn in Hn. destruct (Nat.ltb_spec0 j (Z.to_nat n)); [|discriminate].
    exact (HN j b ltac:(lia) Hn).
  Qed.

  (* [comment removed for export] *)
  #[using="MI BUF OK RB MU WM"] Lemma memchr_tail : forall (k : nat) (i : Z) (x5 x12 x14 x15 x16 x17 : word),
    Z.to_nat (n - i) = k -> (0 <= i < n)%Z -> NOB i ->
    evtF asegs RNG POST (ST 0x9e644 x5 (Z_to_bv 64 (A + i)) x12 (Z_to_bv 64 (n - i)) x14 x15 x16 x17).
  Proof.
    induction k as [|k IH]; intros i x5 x12 x14 x15 x16 x17 Hk Hi HN; pose proof A_bound as AB; [lia|].
    destruct (readable i Hi HN) as [b Hn]. pose proof (nth_error_lt _ _ _ Hn).
    pose proof (u8ro_read asegs m A buf i b _ BUF Hn ltac:(lia) eq_refl) as RD.
    zstep. zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *) zstep. rewrite <- (res_found i b Hi HN Hn K). finish.
    - zstep. zstep. zstep. if_cases K0; zify_cond K0.
      + replace (n - i + -1)%Z with (n - (i + 1))%Z by lia. replace (A + i + 1)%Z with (A + (i + 1))%Z by lia.
        apply (IH (i + 1)%Z); try lia. eapply NOB_S; eauto; lia.
      + (* [comment removed for export] *) zstep. zstep. rewrite <- res_none at 1. { finish. }
        replace n with (i + 1)%Z by lia. eapply NOB_S; eauto; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="MI BUF OK RB MU WM"] Lemma memchr_tail_entry : forall (i : Z) (x5 x13 x14 x15 x16 x17 : word),
    (0 <= i <= n)%Z -> NOB i ->
    evtF asegs RNG POST (ST 0x9e63c x5 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (n - i)) x13 x14 x15 x16 x17).
  Proof.
    intros i x5 x13 x14 x15 x16 x17 Hi HN; pose proof A_bound as AB.
    zstep. zstep. if_cases K; zify_cond K.
    - zstep. zstep. rewrite <- res_none at 1. { finish. } replace n with i by lia. exact HN.
    - apply (memchr_tail (Z.to_nat (n - i)) i); lia || assumption.
  Qed.

  (* [comment removed for export] *)
  #[using="MI BUF OK RB MU WM"] Lemma memchr_words : forall (k : nat) (i : Z) (x5 x17 : word),
    Z.to_nat (n - i) = k -> (0 <= i)%Z -> (i + 8 <= n)%Z -> ((A + i) mod 8 = 0)%Z -> NOB i ->
    evtF asegs RNG POST (ST 0x9e618 x5 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (n - i)) (Z_to_bv 64 CMAGIC) (Z_to_bv 64 HIGHS)
                       (Z_to_bv 64 (c * ONES)) (Z_to_bv 64 7) x17).
  Proof.
    induction k as [k IH] using lt_wf_ind; intros i x5 x17 Hk Hi Hi8 Hal HN; pose proof A_bound as AB.
    pose proof (readable8 i Hi Hi8 Hal HN) as HW.
    pose proof (bytes_at_read asegs m A buf i 8 BUF ltac:(lia) HW) as RD.
    set (chunk := firstn 8 (skipn (Z.to_nat i) buf)) in RD.
    assert (CL : length chunk = 8%nat). { subst chunk. rewrite firstn_length, skipn_length. lia. }
    pose proof (le_val_range _ (bytes_ok_map chunk)) as WR. rewrite length_map, CL in WR.
    change (256 ^ Z.of_nat 8)%Z with (2^64)%Z in WR.
    pose proof (le_val_range _ (bytes_ok_xor _ c (bytes_ok_map chunk) ltac:(lia))) as XR. rewrite !length_map, CL in XR.
    change (256 ^ Z.of_nat 8)%Z with (2^64)%Z in XR.
    do 6 zstep.
    rewrite (load8_le_val chunk CL).
    replace (Z.lxor (le_val (map bv_unsigned chunk)) (c * ONES)) with (le_val (map (fun b => Z.lxor b c) (map bv_unsigned chunk))).
    2:{ change ONES with ONES64b. rewrite <- ones_8, <- CL, <- (length_map bv_unsigned). symmetry. apply le_val_xor_bcast; [apply bytes_ok_map| lia]. }
    if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      clear K. destruct (readable i ltac:(lia) HN) as [b Hn].
      pose proof (u8ro_read asegs m A buf i b _ BUF Hn ltac:(lia) eq_refl) as RD1.
      zstep. zstep. zstep. if_cases Kb; zify_cond Kb.
      + zstep. zstep. zstep. if_cases Kz; zify_cond Kz; [|exfalso; lia].
        replace (n - i + -1)%Z with (n - (i + 1))%Z by lia. replace (A + i + 1)%Z with (A + (i + 1))%Z by lia.
        apply (memchr_tail (Z.to_nat (n - (i + 1))) (i + 1)); try lia. eapply NOB_S; eauto; lia.
      + zstep. zstep. rewrite <- (res_found i b ltac:(lia) HN Hn Kb). finish.
    - apply (haszero64_clang _ (bytes_ok_xor _ c (bytes_ok_map chunk) ltac:(lia)) ltac:(rewrite !length_map; exact CL)) in K.
      rewrite In0_xor in K.
      (* [comment removed for export] *)
      assert (HN8 : NOB (i + 8)).
      { intros j b Hj Hn. destruct (Nat.lt_ge_cases j (Z.to_nat i)) as [Hlt|Hge]. { exact (HN _ _ Hlt Hn). }
        intros Hb. apply K. rewrite <- Hb. apply in_map. subst chunk.
        apply nth_error_In with (n := (j - Z.to_nat i)%nat).
        rewrite nth_error_firstn. replace (Nat.ltb _ _) with true by (symmetry; apply Nat.ltb_lt; lia).
        rewrite nth_error_skipn, <- Hn. f_equal. lia. }
      zstep. zstep. zstep. if_cases K8; zify_cond K8.
      + replace (A + i + 8)%Z with (A + (i + 8))%Z by lia. replace (n - i + -8)%Z with (n - (i + 8))%Z by lia.
        apply (IH (Z.to_nat (n - (i + 8)))); try lia; try exact HN8. all: Z.div_mod_to_equations; lia.
      + replace (A + i + 8)%Z with (A + (i + 8))%Z by lia. replace (n - i + -8)%Z with (n - (i + 8))%Z by lia.
        apply (memchr_tail_entry (i + 8)); try lia; exact HN8.
  Qed.

  (* [comment removed for export] *)
  #[using="MI BUF OK RB RIMG MU WM"] Lemma memchr_mid : forall (i : Z) (x5 x13 x14 x15 x16 x17 : word),
    (0 <= i <= n)%Z -> NOB i -> ((bv_unsigned x14 = 0)%Z <-> i = n) -> (i = n \/ (A + i) mod 8 = 0)%Z ->
    evtF asegs RNG POST (ST 0x9e5e8 x5 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (n - i)) x13 x14 x15 x16 x17).
  Proof.
    intros i x5 x13 x14 x15 x16 x17 Hi HN H14 Hal; pose proof A_bound as AB.
    zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *) apply H14 in K. subst i. zstep. zstep. rewrite <- res_none at 1; [finish| exact HN].
    - assert (Hin : (i < n)%Z). { destruct (Z.eq_dec i n) as [E|]; [|lia]. exfalso. apply K. apply H14. exact E. }
      destruct Hal as [|Hal]; [lia|].
      destruct (readable i ltac:(lia) HN) as [b Hn].
      pose proof (u8ro_read asegs m A buf i b _ BUF Hn ltac:(lia) eq_refl) as RD.
      zstep. zstep. if_cases Kb; zify_cond Kb.
      + apply memchr_tail_entry; [lia| exact HN].
      + zstep. zstep. if_cases K8; zify_cond K8.
        * apply memchr_tail_entry; [lia| exact HN].
        * do 7 zstep.
          apply (memchr_words (Z.to_nat (n - i)) i); try lia. exact HN.
  Qed.

  #[using="a1"] Lemma b2z_word_zero_iff : forall t, bv_unsigned (Z_to_bv 64 (Z.b2z t)) = 0%Z <-> t = false.
  Proof. intros t. rewrite unsigned_lit by (destruct t; cbn; lia). destruct t; cbn; split; intros; first [congruence | lia]. Qed.

  (* [comment removed for export] *)
  #[using="MI BUF OK RB RIMG MU WM"] Lemma memchr_head : forall (k : nat) (i : Z) (x5 x13 x14 x17 : word),
    Z.to_nat (n - i) = k -> (0 <= i < n)%Z -> NOB i -> ((A + i) mod 8 <> 0)%Z ->
    evtF asegs RNG POST (ST 0x9e5c0 x5 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (n - i)) x13 x14 (Z_to_bv 64 (A + i + 1)) (Z_to_bv 64 1) x17).
  Proof.
    induction k as [|k IH]; intros i x5 x13 x14 x17 Hk Hi HN Hal; pose proof A_bound as AB; [lia|].
    destruct (readable i Hi HN) as [b Hn]. pose proof (nth_error_lt _ _ _ Hn).
    pose proof (u8ro_read asegs m A buf i b _ BUF Hn ltac:(lia) eq_refl) as RD.
    zstep. zstep. zstep. if_cases Kb; zify_cond Kb.
    - (* [comment removed for export] *) apply (memchr_tail (Z.to_nat (n - i)) i); try lia. exact HN.
    - pose proof (NOB_S i b ltac:(lia) HN Hn Kb) as HN1.
      zstep. zstep. zstep. zstep. zstep. if_cases Kal; zify_cond Kal.
      + replace (A + i + 1)%Z with (A + (i + 1))%Z by lia. replace (n - i + -1)%Z with (n - (i + 1))%Z by lia.
        apply (memchr_mid (i + 1)); try lia; try exact HN1.
        * rewrite b2z_word_zero_iff, Z.ltb_ge. lia.
        * right. revert Kal. zb_masks. intros Kal. Z.div_mod_to_equations; lia.
      + zstep. zstep. if_cases K1; zify_cond K1.
        * replace (A + i + 2)%Z with (A + (i + 1) + 1)%Z by lia.
          replace (A + i + 1)%Z with (A + (i + 1))%Z by lia. replace (n - i + -1)%Z with (n - (i + 1))%Z by lia.
          apply (IH (i + 1)%Z); try lia; try exact HN1. revert Kal. zb_masks. intros Kal. Z.div_mod_to_equations; lia.
        * replace (A + i + 1)%Z with (A + (i + 1))%Z by lia. replace (n - i + -1)%Z with (n - (i + 1))%Z by lia.
          apply (memchr_mid (i + 1)); try lia; try exact HN1. rewrite b2z_word_zero_iff, Z.ltb_ge. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="MI BUF OK RB RIMG MU WM"] Lemma memchr_body :
    evtF asegs RNG POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x9e5a4) fc None m (seg_rom asegs)).
  Proof.
    pose proof A_bound as AB. pose proof (zr_word a1) as R1. unfold inr64 in R1.
    zstep. replace (Z.land (bv_unsigned a1) 255) with c.
    2:{ change 255%Z with (2^8 - 1)%Z. rewrite zb_land_mask by lia. reflexivity. }
    zstep. zstep. zstep. if_cases Kal; zify_cond Kal.
    - (* [comment removed for export] *)
      eapply evtF_eq.
      2:{ apply (memchr_mid 0 t0 (Z_to_bv 64 (Z.land A 7)) (Z_to_bv 64 (Z.b2z (0 <? n)%Z)) a5 a6 a7); try lia.
          - apply NOB_0. - rewrite b2z_word_zero_iff, Z.ltb_ge. lia.
          - right. revert Kal. zb_masks. intros Kal. rewrite Z.add_0_r. exact Kal. }
      unfold mkR. rewrite Z_to_bv_plus0, Z.sub_0_r, Z_to_bv_bv_unsigned. reflexivity.
    - zstep. if_cases K0; zify_cond K0.
      + (* [comment removed for export] *)
        eapply evtF_eq.
        2:{ apply (memchr_mid 0 t0 (Z_to_bv 64 (Z.land A 7)) (Z_to_bv 64 (Z.b2z (0 <? n)%Z)) a5 a6 a7); try lia.
            - apply NOB_0. - rewrite b2z_word_zero_iff, Z.ltb_ge. lia. }
        unfold mkR. rewrite Z_to_bv_plus0, Z.sub_0_r, Z_to_bv_bv_unsigned. reflexivity.
      + zstep. zstep.
        eapply evtF_eq.
        2:{ apply (memchr_head (Z.to_nat n) 0 t0 (Z_to_bv 64 (Z.land A 7)) (Z_to_bv 64 (Z.b2z (0 <? n)%Z)) a7); try lia.
            - apply NOB_0. - revert Kal. zb_masks. intros Kal. rewrite Z.add_0_r. exact Kal. }
        unfold mkR. rewrite Z_to_bv_plus0, Z.sub_0_r, Z_to_bv_bv_unsigned, Z.add_0_r. reflexivity.
  Qed.
End Proofs.

#[using="Type"] Lemma memchr_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (buf : list byte),
  bytes_at asegs m (bv_unsigned a0) buf ->
  memchr_ok (bv_unsigned a0) (bv_unsigned a1 mod 256) (bv_unsigned a2) buf ->
  mem_inv asegs m ->
  rng RNG (bv_unsigned a0) (Z.of_nat (length buf)) ->
  rng_aimg RNG ->
  evtF asegs RNG (memchr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 buf m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x9e5a4) fc None m (seg_rom asegs)).
Proof. intros until buf. intros BUF OK MI RB RIMG. apply memchr_body; assumption. Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Section CANSEC1. Context {rc : runConstT}.
Definition memchr_entry := 0x9e988%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section ZFacts.
  Open Scope Z_scope.
  #[using="Type"] Lemma lxor_lt_256 : forall a b, 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lxor a b < 256.
  Proof.
    intros a b Ha Hb. pose proof (Z.lxor_nonneg a b) as Hnn. split; [lia|].
    destruct (Z.eq_dec (Z.lxor a b) 0) as [->|Hnz]; [lia|].
    apply (proj2 (Z.log2_lt_pow2 (Z.lxor a b) 8 ltac:(lia))).
    pose proof (Z.log2_lxor a b ltac:(lia) ltac:(lia)) as Hl.
    assert (Z.log2 a < 8). { destruct (Z.eq_dec a 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia. }
    assert (Z.log2 b < 8). { destruct (Z.eq_dec b 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia. }
    lia.
  Qed.

  #[using="Type"] Lemma lxor_split : forall x y x' y', 0 <= x < 256 -> 0 <= x' < 256 -> 0 <= y -> 0 <= y' ->
    Z.lxor (x + 256 * y) (x' + 256 * y') = Z.lxor x x' + 256 * Z.lxor y y'.
  Proof.
    intros x y x' y' Hx Hx' Hy Hy'.
    pose proof (lxor_lt_256 x x' Hx Hx') as Hl.
    apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec, !testbit_split by lia.
    destruct (i <? 8); rewrite Z.lxor_spec; reflexivity.
  Qed.

  #[using="Type"] Lemma le_val_nonneg : forall bs, bytes_ok bs -> 0 <= le_val bs.
  Proof. intros bs H. pose proof (le_val_range bs H). lia. Qed.

  #[using="Type"] Lemma le_val_xor_bcast : forall bs c, bytes_ok bs -> 0 <= c < 256 ->
    Z.lxor (le_val bs) (c * ones (length bs)) = le_val (map (fun b => Z.lxor b c) bs).
  Proof.
    induction bs as [|b bs IH]; intros c Hok Hc.
    - cbn. rewrite Z.mul_0_r. reflexivity.
    - inversion Hok as [|b0 bs0 Hb Hbs]; subst. cbn [le_val ones length map].
      replace (c * (1 + 256 * ones (length bs))) with (c + 256 * (c * ones (length bs))) by lia.
      rewrite lxor_split; try lia.
      + rewrite IH by assumption. reflexivity.
      + apply le_val_nonneg. exact Hbs.
      + pose proof (le_val_range (repeat 1 (length bs))) as Hr. assert (0 <= ones (length bs)); [|nia].
        clear. induction (length bs); cbn; lia.
  Qed.

  #[using="Type"] Lemma bytes_ok_xor : forall bs c, bytes_ok bs -> 0 <= c < 256 -> bytes_ok (map (fun b => Z.lxor b c) bs).
  Proof.
    intros bs c H Hc. unfold bytes_ok in *. rewrite Forall_map. eapply Forall_impl; [|exact H].
    intros b Hb. apply lxor_lt_256; assumption.
  Qed.

  #[using="Type"] Lemma In0_xor : forall bs c, In 0 (map (fun b => Z.lxor b c) bs) <-> In c bs.
  Proof.
    intros bs c. rewrite in_map_iff. split.
    - intros (b & Hb & Hin). apply Z.lxor_eq in Hb. subst. exact Hin.
    - intros Hin. exists c. split; [apply Z.lxor_nilpotent| exact Hin].
  Qed.
End ZFacts.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition memchr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 a2 : word) (buf : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
                 (Z_to_bv 64 (memchr_res (bv_unsigned a0) (bv_unsigned a1 mod 256) (bv_unsigned a2) buf))
                 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ bytes_at asegs m' (bv_unsigned a0) buf.

Section Proofs.
  Variables (RNG : footprint) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (buf : list byte).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis BUF : bytes_at asegs m (bv_unsigned a0) buf.
  Hypothesis OK : memchr_ok (bv_unsigned a0) (bv_unsigned a1 mod 256) (bv_unsigned a2) buf.
  (* [comment removed for export] *)
  Hypothesis RB : rng RNG (bv_unsigned a0) (Z.of_nat (length buf)).
  Hypothesis RIMG : rng_aimg RNG.
  Let MU : munch [] m m := munch_refl [] m.
  Let WM : wmono asegs m m := wmono_refl asegs m.

  Notation A := (bv_unsigned a0).
  Notation n := (bv_unsigned a2).
  Notation c := ((bv_unsigned a1) mod 256)%Z.
  Notation len := (Z.of_nat (length buf)).
  Notation POST := (memchr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 buf m).
  (* [comment removed for export] *)
  Notation ST pc x5 x10 x12 x13 x14 x15 x16 x17 :=
    (MS (mkR ra sp gp tp x5 t1 t2 s0 s1 x10 (Z_to_bv 64 c) x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom asegs)).
  Notation CMAGIC := 72340172838076672%Z.      (* [comment removed for export] *)
  Notation HIGHS := 9259542123273814144%Z.     (* [comment removed for export] *)
  Notation ONES := 72340172838076673%Z.       (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition NOB (i : Z) : Prop :=
    forall j b, (j < Z.to_nat i)%nat -> nth_error buf j = Some b -> bv_unsigned b <> c.

  #[using="m BUF"] Lemma A_bound : (0 <= A /\ A + len <= 2^64 /\ 0 <= n < 2^64 /\ 0 <= c < 256)%Z.
  Proof.
    pose proof (bytes_at_bound _ _ _ _ BUF).
    pose proof (bv_unsigned_in_range 64 a2) as R. unfold bv_modulus in R. cbn in R.
    pose proof (Z.mod_pos_bound (bv_unsigned a1) 256). cbn. lia.
  Qed.

  #[using="Type"] Lemma NOB_0 : NOB 0.
  Proof. intros j b Hj. cbn in Hj. lia. Qed.

  #[using="Type"] Lemma NOB_S : forall i b, (0 <= i)%Z -> NOB i -> nth_error buf (Z.to_nat i) = Some b -> bv_unsigned b <> c -> NOB (i + 1).
  Proof.
    intros i b Hi H Hn Hb j b' Hj Hn'.
    destruct (Nat.eq_dec j (Z.to_nat i)) as [->|NE]. { rewrite Hn in Hn'. injection Hn' as <-. exact Hb. }
    eapply H; [|exact Hn']. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="OK"] Lemma ok_cases :
    (exists j b, Z.of_nat j < n /\ nth_error buf j = Some b /\ bv_unsigned b = c /\
       (forall j' b', (j' < j)%nat -> nth_error buf j' = Some b' -> bv_unsigned b' <> c) /\
       (n <= len \/ Z.of_nat j + 1 + (- (A + Z.of_nat j + 1)) mod 8 <= len))%Z
    \/ ((forall j b, (Z.of_nat j < n)%Z -> nth_error buf j = Some b -> bv_unsigned b <> c) /\ (n <= len)%Z).
  Proof.
    pose proof OK as H. unfold memchr_ok in H.
    destruct (find_byte c (firstn (Z.to_nat n) buf)) as [j|] eqn:FB.
    - left. (nd_pre (find_byte_Some _ _ _ FB) 3%nat; intros Hl (b & Hn & Hb) Hmin; nd_post).
      rewrite firstn_length in Hl.
      rewrite nth_error_firstn in Hn. replace (Nat.ltb j (Z.to_nat n)) with true in Hn by (symmetry; apply Nat.ltb_lt; lia).
      exists j, b. repeat split; try assumption; try lia.
      intros j' b' Hj' Hn'. eapply Hmin; [exact Hj'|]. rewrite nth_error_firstn.
      replace (Nat.ltb j' (Z.to_nat n)) with true by (symmetry; apply Nat.ltb_lt; lia). exact Hn'.
    - right. split; [|exact H]. intros j b Hj Hn. eapply (find_byte_None _ _ FB j). rewrite nth_error_firstn.
      replace (Nat.ltb j (Z.to_nat n)) with true by (symmetry; apply Nat.ltb_lt; lia). exact Hn.
  Qed.

  #[using="a0 OK"] Lemma readable : forall i, (0 <= i < n)%Z -> NOB i -> exists b, nth_error buf (Z.to_nat i) = Some b.
  Proof.
    intros i Hi HN. destruct (nth_error buf (Z.to_nat i)) as [b|] eqn:E; [exists b; reflexivity|].
    exfalso. apply nth_error_None in E.
    destruct ok_cases as [(j & b & Hj & Hn & Hb & Hmin & _)|(Hall & Hlen)]; [|lia].
    pose proof (nth_error_lt _ _ _ Hn).
    destruct (Nat.lt_ge_cases j (Z.to_nat i)) as [Hlt|Hge]; [|lia].
    exact (HN _ _ Hlt Hn Hb).
  Qed.

  #[using="OK"] Lemma readable8 : forall i, (0 <= i)%Z -> (i + 8 <= n)%Z -> ((A + i) mod 8 = 0)%Z -> NOB i ->
    (Z.to_nat i + 8 <= length buf)%nat.
  Proof.
    intros i Hi Hi8 Hal HN.
    destruct ok_cases as [(j & b & Hj & Hn & Hb & Hmin & Hsl)|(Hall & Hlen)]; [|lia].
    pose proof (nth_error_lt _ _ _ Hn).
    destruct (Nat.lt_ge_cases j (Z.to_nat i)) as [Hlt|Hge]. { exfalso. exact (HN _ _ Hlt Hn Hb). }
    destruct Hsl as [Hsl|Hsl]; [lia|].
    destruct (Nat.lt_ge_cases j (Z.to_nat i + 8)) as [Hlt8|]; [|lia].
    Z.div_mod_to_equations. lia.
  Qed.

  #[using="Type"] Lemma res_found : forall i b, (0 <= i < n)%Z -> NOB i -> nth_error buf (Z.to_nat i) = Some b -> bv_unsigned b = c ->
    memchr_res A c n buf = (A + i)%Z.
  Proof.
    intros i b Hi HN Hn Hb. unfold memchr_res.
    rewrite (find_byte_charact c _ (Z.to_nat i) b); [lia| | exact Hb|].
    - rewrite nth_error_firstn. replace (Nat.ltb _ _) with true by (symmetry; apply Nat.ltb_lt; lia). exact Hn.
    - intros j b' Hj Hn'. rewrite nth_error_firstn in Hn'. destruct (Nat.ltb j (Z.to_nat n)); [|discriminate].
      exact (HN _ _ Hj Hn').
  Qed.

  #[using="Type"] Lemma res_none : NOB n -> memchr_res A c n buf = 0%Z.
  Proof.
    intros HN. unfold memchr_res. rewrite find_byte_None_intro; [reflexivity|].
    intros j b Hn. rewrite nth_error_firstn in Hn. destruct (Nat.ltb_spec0 j (Z.to_nat n)); [|discriminate].
    exact (HN j b ltac:(lia) Hn).
  Qed.

  (* [comment removed for export] *)
  #[using="MI BUF OK RB MU WM"] Lemma memchr_tail : forall (k : nat) (i : Z) (x5 x12 x14 x15 x16 x17 : word),
    Z.to_nat (n - i) = k -> (0 <= i < n)%Z -> NOB i ->
    evtF asegs RNG POST (ST 0x9ea28 x5 (Z_to_bv 64 (A + i)) x12 (Z_to_bv 64 (n - i)) x14 x15 x16 x17).
  Proof.
    induction k as [|k IH]; intros i x5 x12 x14 x15 x16 x17 Hk Hi HN; pose proof A_bound as AB; [lia|].
    destruct (readable i Hi HN) as [b Hn]. pose proof (nth_error_lt _ _ _ Hn).
    pose proof (u8ro_read asegs m A buf i b _ BUF Hn ltac:(lia) eq_refl) as RD.
    zstep. zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *) zstep. rewrite <- (res_found i b Hi HN Hn K). finish.
    - zstep. zstep. zstep. if_cases K0; zify_cond K0.
      + replace (n - i + -1)%Z with (n - (i + 1))%Z by lia. replace (A + i + 1)%Z with (A + (i + 1))%Z by lia.
        apply (IH (i + 1)%Z); try lia. eapply NOB_S; eauto; lia.
      + (* [comment removed for export] *) zstep. zstep. rewrite <- res_none at 1. { finish. }
        replace n with (i + 1)%Z by lia. eapply NOB_S; eauto; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="MI BUF OK RB MU WM"] Lemma memchr_tail_entry : forall (i : Z) (x5 x13 x14 x15 x16 x17 : word),
    (0 <= i <= n)%Z -> NOB i ->
    evtF asegs RNG POST (ST 0x9ea20 x5 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (n - i)) x13 x14 x15 x16 x17).
  Proof.
    intros i x5 x13 x14 x15 x16 x17 Hi HN; pose proof A_bound as AB.
    zstep. zstep. if_cases K; zify_cond K.
    - zstep. zstep. rewrite <- res_none at 1. { finish. } replace n with i by lia. exact HN.
    - apply (memchr_tail (Z.to_nat (n - i)) i); lia || assumption.
  Qed.

  (* [comment removed for export] *)
  #[using="MI BUF OK RB MU WM"] Lemma memchr_words : forall (k : nat) (i : Z) (x5 x17 : word),
    Z.to_nat (n - i) = k -> (0 <= i)%Z -> (i + 8 <= n)%Z -> ((A + i) mod 8 = 0)%Z -> NOB i ->
    evtF asegs RNG POST (ST 0x9e9fc x5 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (n - i)) (Z_to_bv 64 CMAGIC) (Z_to_bv 64 HIGHS)
                       (Z_to_bv 64 (c * ONES)) (Z_to_bv 64 7) x17).
  Proof.
    induction k as [k IH] using lt_wf_ind; intros i x5 x17 Hk Hi Hi8 Hal HN; pose proof A_bound as AB.
    pose proof (readable8 i Hi Hi8 Hal HN) as HW.
    pose proof (bytes_at_read asegs m A buf i 8 BUF ltac:(lia) HW) as RD.
    set (chunk := firstn 8 (skipn (Z.to_nat i) buf)) in RD.
    assert (CL : length chunk = 8%nat). { subst chunk. rewrite firstn_length, skipn_length. lia. }
    pose proof (le_val_range _ (bytes_ok_map chunk)) as WR. rewrite length_map, CL in WR.
    change (256 ^ Z.of_nat 8)%Z with (2^64)%Z in WR.
    pose proof (le_val_range _ (bytes_ok_xor _ c (bytes_ok_map chunk) ltac:(lia))) as XR. rewrite !length_map, CL in XR.
    change (256 ^ Z.of_nat 8)%Z with (2^64)%Z in XR.
    do 6 zstep.
    rewrite (load8_le_val chunk CL).
    replace (Z.lxor (le_val (map bv_unsigned chunk)) (c * ONES)) with (le_val (map (fun b => Z.lxor b c) (map bv_unsigned chunk))).
    2:{ change ONES with ONES64b. rewrite <- ones_8, <- CL, <- (length_map bv_unsigned). symmetry. apply le_val_xor_bcast; [apply bytes_ok_map| lia]. }
    if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      clear K. destruct (readable i ltac:(lia) HN) as [b Hn].
      pose proof (u8ro_read asegs m A buf i b _ BUF Hn ltac:(lia) eq_refl) as RD1.
      zstep. zstep. zstep. if_cases Kb; zify_cond Kb.
      + zstep. zstep. zstep. if_cases Kz; zify_cond Kz; [|exfalso; lia].
        replace (n - i + -1)%Z with (n - (i + 1))%Z by lia. replace (A + i + 1)%Z with (A + (i + 1))%Z by lia.
        apply (memchr_tail (Z.to_nat (n - (i + 1))) (i + 1)); try lia. eapply NOB_S; eauto; lia.
      + zstep. zstep. rewrite <- (res_found i b ltac:(lia) HN Hn Kb). finish.
    - apply (haszero64_clang _ (bytes_ok_xor _ c (bytes_ok_map chunk) ltac:(lia)) ltac:(rewrite !length_map; exact CL)) in K.
      rewrite In0_xor in K.
      (* [comment removed for export] *)
      assert (HN8 : NOB (i + 8)).
      { intros j b Hj Hn. destruct (Nat.lt_ge_cases j (Z.to_nat i)) as [Hlt|Hge]. { exact (HN _ _ Hlt Hn). }
        intros Hb. apply K. rewrite <- Hb. apply in_map. subst chunk.
        apply nth_error_In with (n := (j - Z.to_nat i)%nat).
        rewrite nth_error_firstn. replace (Nat.ltb _ _) with true by (symmetry; apply Nat.ltb_lt; lia).
        rewrite nth_error_skipn, <- Hn. f_equal. lia. }
      zstep. zstep. zstep. if_cases K8; zify_cond K8.
      + replace (A + i + 8)%Z with (A + (i + 8))%Z by lia. replace (n - i + -8)%Z with (n - (i + 8))%Z by lia.
        apply (IH (Z.to_nat (n - (i + 8)))); try lia; try exact HN8. all: Z.div_mod_to_equations; lia.
      + replace (A + i + 8)%Z with (A + (i + 8))%Z by lia. replace (n - i + -8)%Z with (n - (i + 8))%Z by lia.
        apply (memchr_tail_entry (i + 8)); try lia; exact HN8.
  Qed.

  (* [comment removed for export] *)
  #[using="MI BUF OK RB RIMG MU WM"] Lemma memchr_mid : forall (i : Z) (x5 x13 x14 x15 x16 x17 : word),
    (0 <= i <= n)%Z -> NOB i -> ((bv_unsigned x14 = 0)%Z <-> i = n) -> (i = n \/ (A + i) mod 8 = 0)%Z ->
    evtF asegs RNG POST (ST 0x9e9cc x5 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (n - i)) x13 x14 x15 x16 x17).
  Proof.
    intros i x5 x13 x14 x15 x16 x17 Hi HN H14 Hal; pose proof A_bound as AB.
    zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *) apply H14 in K. subst i. zstep. zstep. rewrite <- res_none at 1; [finish| exact HN].
    - assert (Hin : (i < n)%Z). { destruct (Z.eq_dec i n) as [E|]; [|lia]. exfalso. apply K. apply H14. exact E. }
      destruct Hal as [|Hal]; [lia|].
      destruct (readable i ltac:(lia) HN) as [b Hn].
      pose proof (u8ro_read asegs m A buf i b _ BUF Hn ltac:(lia) eq_refl) as RD.
      zstep. zstep. if_cases Kb; zify_cond Kb.
      + apply memchr_tail_entry; [lia| exact HN].
      + zstep. zstep. if_cases K8; zify_cond K8.
        * apply memchr_tail_entry; [lia| exact HN].
        * do 7 zstep.
          apply (memchr_words (Z.to_nat (n - i)) i); try lia. exact HN.
  Qed.

  #[using="a1"] Lemma b2z_word_zero_iff : forall t, bv_unsigned (Z_to_bv 64 (Z.b2z t)) = 0%Z <-> t = false.
  Proof. intros t. rewrite unsigned_lit by (destruct t; cbn; lia). destruct t; cbn; split; intros; first [congruence | lia]. Qed.

  (* [comment removed for export] *)
  #[using="MI BUF OK RB RIMG MU WM"] Lemma memchr_head : forall (k : nat) (i : Z) (x5 x13 x14 x17 : word),
    Z.to_nat (n - i) = k -> (0 <= i < n)%Z -> NOB i -> ((A + i) mod 8 <> 0)%Z ->
    evtF asegs RNG POST (ST 0x9e9a4 x5 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (n - i)) x13 x14 (Z_to_bv 64 (A + i + 1)) (Z_to_bv 64 1) x17).
  Proof.
    induction k as [|k IH]; intros i x5 x13 x14 x17 Hk Hi HN Hal; pose proof A_bound as AB; [lia|].
    destruct (readable i Hi HN) as [b Hn]. pose proof (nth_error_lt _ _ _ Hn).
    pose proof (u8ro_read asegs m A buf i b _ BUF Hn ltac:(lia) eq_refl) as RD.
    zstep. zstep. zstep. if_cases Kb; zify_cond Kb.
    - (* [comment removed for export] *) apply (memchr_tail (Z.to_nat (n - i)) i); try lia. exact HN.
    - pose proof (NOB_S i b ltac:(lia) HN Hn Kb) as HN1.
      zstep. zstep. zstep. zstep. zstep. if_cases Kal; zify_cond Kal.
      + replace (A + i + 1)%Z with (A + (i + 1))%Z by lia. replace (n - i + -1)%Z with (n - (i + 1))%Z by lia.
        apply (memchr_mid (i + 1)); try lia; try exact HN1.
        * rewrite b2z_word_zero_iff, Z.ltb_ge. lia.
        * right. revert Kal. zb_masks. intros Kal. Z.div_mod_to_equations; lia.
      + zstep. zstep. if_cases K1; zify_cond K1.
        * replace (A + i + 2)%Z with (A + (i + 1) + 1)%Z by lia.
          replace (A + i + 1)%Z with (A + (i + 1))%Z by lia. replace (n - i + -1)%Z with (n - (i + 1))%Z by lia.
          apply (IH (i + 1)%Z); try lia; try exact HN1. revert Kal. zb_masks. intros Kal. Z.div_mod_to_equations; lia.
        * replace (A + i + 1)%Z with (A + (i + 1))%Z by lia. replace (n - i + -1)%Z with (n - (i + 1))%Z by lia.
          apply (memchr_mid (i + 1)); try lia; try exact HN1. rewrite b2z_word_zero_iff, Z.ltb_ge. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="MI BUF OK RB RIMG MU WM"] Lemma memchr_body :
    evtF asegs RNG POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x9e988) fc None m (seg_rom asegs)).
  Proof.
    pose proof A_bound as AB. pose proof (zr_word a1) as R1. unfold inr64 in R1.
    zstep. replace (Z.land (bv_unsigned a1) 255) with c.
    2:{ change 255%Z with (2^8 - 1)%Z. rewrite zb_land_mask by lia. reflexivity. }
    zstep. zstep. zstep. if_cases Kal; zify_cond Kal.
    - (* [comment removed for export] *)
      eapply evtF_eq.
      2:{ apply (memchr_mid 0 t0 (Z_to_bv 64 (Z.land A 7)) (Z_to_bv 64 (Z.b2z (0 <? n)%Z)) a5 a6 a7); try lia.
          - apply NOB_0. - rewrite b2z_word_zero_iff, Z.ltb_ge. lia.
          - right. revert Kal. zb_masks. intros Kal. rewrite Z.add_0_r. exact Kal. }
      unfold mkR. rewrite Z_to_bv_plus0, Z.sub_0_r, Z_to_bv_bv_unsigned. reflexivity.
    - zstep. if_cases K0; zify_cond K0.
      + (* [comment removed for export] *)
        eapply evtF_eq.
        2:{ apply (memchr_mid 0 t0 (Z_to_bv 64 (Z.land A 7)) (Z_to_bv 64 (Z.b2z (0 <? n)%Z)) a5 a6 a7); try lia.
            - apply NOB_0. - rewrite b2z_word_zero_iff, Z.ltb_ge. lia. }
        unfold mkR. rewrite Z_to_bv_plus0, Z.sub_0_r, Z_to_bv_bv_unsigned. reflexivity.
      + zstep. zstep.
        eapply evtF_eq.
        2:{ apply (memchr_head (Z.to_nat n) 0 t0 (Z_to_bv 64 (Z.land A 7)) (Z_to_bv 64 (Z.b2z (0 <? n)%Z)) a7); try lia.
            - apply NOB_0. - revert Kal. zb_masks. intros Kal. rewrite Z.add_0_r. exact Kal. }
        unfold mkR. rewrite Z_to_bv_plus0, Z.sub_0_r, Z_to_bv_bv_unsigned, Z.add_0_r. reflexivity.
  Qed.
End Proofs.

#[using="Type"] Lemma memchr_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (buf : list byte),
  bytes_at asegs m (bv_unsigned a0) buf ->
  memchr_ok (bv_unsigned a0) (bv_unsigned a1 mod 256) (bv_unsigned a2) buf ->
  mem_inv asegs m ->
  rng RNG (bv_unsigned a0) (Z.of_nat (length buf)) ->
  rng_aimg RNG ->
  evtF asegs RNG (memchr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 buf m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x9e988) fc None m (seg_rom asegs)).
Proof. intros until buf. intros BUF OK MI RB RIMG. apply memchr_body; assumption. Qed.
End CANSEC1.
End TwB.
End F_memchr.

(* [comment removed for export] *)
Module FsKit.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac is_Zlit a := lazymatch a with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.
Ltac lit_in H :=
  repeat match type of H with
  | context [Z.add ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.add a b) in change (Z.add a b) with v in H
  | context [Z.sub ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.sub a b) in change (Z.sub a b) with v in H
  | context [Z.mul ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.mul a b) in change (Z.mul a b) with v in H
  end.
Ltac lit_goal :=
  repeat match goal with
  | |- context [Z.add ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.add a b) in change (Z.add a b) with v
  | |- context [Z.sub ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.sub a b) in change (Z.sub a b) with v
  | |- context [Z.mul ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.mul a b) in change (Z.mul a b) with v
  end.

(* [comment removed for export] *)
Ltac addr_diff_g E A :=
  let k := addr_diff E A in
  let ok := eval vm_compute in (Z.ltb k 65536) in
  lazymatch ok with true => k end.

Ltac solve_load_g :=
  match goal with
  | |- context [ov_read_bytes ?segs ?m ?a ?n] =>
    let E := addr_expr a in
    match goal with
    | H : rw_cells segs m ?A ?cs0 |- _ =>
        let k := addr_diff_g E A in
        let kn := eval vm_compute in (Z.to_nat k) in
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          rewrite (rw_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
        end
    | H : ro_cells segs m ?A ?cs0 |- _ =>
        let k := addr_diff_g E A in
        let kn := eval vm_compute in (Z.to_nat k) in
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with ro_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          rewrite (ro_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
        end
    | HR : ov_read_bytes segs m ?a' n = Some ?bs |- _ =>
        cbv delta [wa] in HR;
        first [ rewrite HR
              | replace (ov_read_bytes segs m a n) with (Some bs)
                  by (rewrite <- HR; f_equal; word_eq_tac) ]
    end
  end;
  load_post.

Ltac solve_store_g :=
  match goal with
  | |- context [store_ok ?segs ?m ?a ?n] =>
    rewrite ?store_bytes_8', ?store_bytes_4', ?store_bytes_2', ?store_bytes_1';
    let E := addr_expr a in
    match goal with
    | H : rw_cells segs m ?A ?cs0 |- _ =>
        let k := addr_diff_g E A in
        let kn := eval vm_compute in (Z.to_nat k) in
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          rewrite (rw_cells_store_ok_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac]);
          cbv beta iota;
          match goal with
          | |- context [write_to_mem m a ?bs] =>
              replace (write_to_mem m a bs) with (write_to_mem m (wa (A + Z.of_nat kn)) bs) by (f_equal; addr_eq_tac)
          end
        end
    | HS : store_ok segs m ?a' n = true |- _ =>
        cbv delta [wa] in HS;
        first [ rewrite HS
              | replace (store_ok segs m a n) with true
                  by (rewrite <- HS; f_equal; word_eq_tac);
                try replace (write_to_mem m a) with (write_to_mem m a')
                  by (f_equal; word_eq_tac) ];
        cbv beta iota
    end
  end.

Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma disjoint_from_sub : forall W A n A' n', disjoint_from W A n -> A <= A' -> A' + n' <= A + n -> 0 <= n' ->
  disjoint_from W A' n'.
Proof.
  induction W as [|[lo hi] W IH]; intros A n A' n' H H1 H2 H3; cbn in *; [exact I|].
  destruct H as [D H]. split; [lia|]. eapply IH; eauto.
Qed.

(* [comment removed for export] *)
Definition dc_at (m : word -> option byte) (A n : Z) : Prop :=
  exists bs, rw_cells asegs m A [CB (Z.to_nat n) bs].

#[using="Type"] Lemma dc_split : forall m A a b, dc_at m A (a + b) -> 0 <= a -> 0 <= b ->
  dc_at m A a /\ dc_at m (A + a) b.
Proof.
  intros m A a b [bs H] Ha Hb.
  pose proof (rw_cells_split_CB asegs m A [] (Z.to_nat (a + b)) bs [] [Z.to_nat a; Z.to_nat b] H ltac:(cbn; lia)) as H2.
  cbn [app mk_CB_cells] in H2. apply (proj1 (rw_cells_app asegs m A [_] [_])) in H2. destruct H2 as [H1 H2].
  cbn [cells_size csize Nat.add] in H2. rewrite Nat.add_0_r, Z2Nat.id in H2 by lia.
  split; [eexists; exact H1 | eexists; exact H2].
Qed.

#[using="Type"] Lemma dc_merge : forall m A a b, dc_at m A a -> dc_at m (A + a) b -> 0 <= a -> 0 <= b -> dc_at m A (a + b).
Proof.
  intros m A a b [bs1 H1] [bs2 H2] Ha Hb.
  assert (H : rw_cells asegs m A ([CB (Z.to_nat a) bs1] ++ [CB (Z.to_nat b) bs2])).
  { apply rw_cells_app. split; [exact H1|]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact H2. }
  pose proof (rw_cells_merge asegs m A [] ([CB (Z.to_nat a) bs1] ++ [CB (Z.to_nat b) bs2]) [] ) as M.
  rewrite !app_nil_r in M. cbn [app] in M, H. specialize (M H). cbn [cells_size cells_bytes csize cbytes Nat.add app] in M.
  rewrite app_nil_r, Nat.add_0_r in M. exists (bs1 ++ bs2). rewrite Z2Nat.inj_add by lia. exact M.
Qed.

#[using="Type"] Lemma dc_take : forall m A n k, dc_at m A n -> 0 <= k <= n -> dc_at m A k /\ dc_at m (A + k) (n - k).
Proof. intros m A n k H Hk. apply dc_split; [replace (k + (n - k)) with n by lia; exact H| lia| lia]. Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma dc_sub : forall m A n B k, dc_at m A n -> A <= B -> 0 <= k -> B + k <= A + n -> dc_at m B k.
Proof.
  intros m A n B k H H1 H2 H3.
  destruct (dc_take m A n (B - A) H ltac:(lia)) as [_ D]. replace (A + (B - A)) with B in D by lia.
  destruct (dc_take m B (n - (B - A)) k D ltac:(lia)) as [D' _]. exact D'.
Qed.

#[using="Type"] Lemma c8_of_dc : forall m A, dc_at m A 8 -> exists w : word, rw_cells asegs m A [C8 w].
Proof. intros m A [bs H]. destruct (c8_of_CB m A bs H) as [w [H' _]]. exists w. exact H'. Qed.
#[using="Type"] Lemma c8c8_of_dc : forall m A, dc_at m A 16 -> exists w1 w2 : word, rw_cells asegs m A [C8 w1; C8 w2].
Proof. intros m A [bs H]. exact (c8c8_of_CB m A bs H). Qed.
#[using="Type"] Lemma c1_of_dc : forall m A, dc_at m A 1 -> exists b : byte, rw_cells asegs m A [C1 b].
Proof.
  intros m A [bs H]. pose proof H as H0. destruct H0 as [[[L _] _] _]. cbn in L.
  destruct bs as [|b [|]]; cbn in L; try lia. exists b.
  eapply rw_cells_recast; [exact H | cbn; tauto | reflexivity | reflexivity].
Qed.
#[using="Type"] Lemma dc_of_cells : forall m A cs, rw_cells asegs m A cs -> dc_at m A (Z.of_nat (cells_size cs)).
Proof.
  intros m A cs H. exists (cells_bytes cs). rewrite Nat2Z.id.
  pose proof H as H0. destruct H0 as [[WF _] _].
  eapply rw_cells_recast; [exact H | cbn; split; [symmetry; symmetry; apply cells_bytes_length; exact WF| exact I]
    | cbn; rewrite app_nil_r; reflexivity | cbn; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma dc_at_any2 : forall m m' A n,
  dc_at m A n -> wmono asegs m m' -> (0 <= A /\ A + n <= 0x10000 \/ 0x603000 <= A) -> dc_at m' A n.
Proof.
  intros m m' A n [bs [[[WF _] [B0 [B1 BR]]] [W0 [W1 WR]]]] WM HA. cbn [cells_size csize cells_bytes cbytes app Nat.add] in *.
  rewrite app_nil_r in B1, BR. cbn in WF. rewrite Nat.add_0_r in W1, WR.
  assert (RD : forall i, 0 <= i < Z.of_nat (length bs) -> exists b, m' (wa (A + i)) = Some b).
  { intros i Hi. specialize (WR i ltac:(lia)). apply WM in WR.
    rewrite ref_wview_overlay in WR by (rewrite wa_unsigned by lia; lia).
    destruct (m' (wa (A + i))) as [b|]; [exists b; reflexivity| congruence]. }
  (* [comment removed for export] *)
  assert (BS : forall k, (k <= length bs)%nat -> exists bs' : list byte, length bs' = k /\
            forall i, (i < k)%nat -> m' (wa (A + Z.of_nat i)) = nth_error bs' i).
  { induction k as [|k IH]; intros Hk.
    - exists []. split; [reflexivity|]. intros i Hi. lia.
    - (nd_pre (IH ltac:(lia)) 3%nat; intros bs' L E; nd_post). destruct (RD (Z.of_nat k) ltac:(lia)) as [b Hb].
      exists (bs' ++ [b]). split; [rewrite length_app; cbn; lia|].
      intros i Hi. destruct (Nat.eq_dec i k) as [->|NE].
      + rewrite nth_error_app2 by lia. rewrite L, Nat.sub_diag. cbn. exact Hb.
      + rewrite nth_error_app1 by lia. apply E. lia. }
  (nd_pre (BS (length bs) ltac:(lia)) 3%nat; intros bs' L E; nd_post).
  exists bs'. split; [split; [cbn; destruct WF as [WF _]; split; [lia| exact I]|]|].
  - cbn [cells_bytes cbytes app]. rewrite app_nil_r. split; [lia|]. split; [rewrite L; lia|].
    intros i Hi. unfold mrd. rewrite (E i ltac:(lia)).
    destruct (nth_error bs' i) eqn:N; [reflexivity|]. apply nth_error_None in N. lia.
  - cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. split; [lia|]. split; [lia|].
    intros i Hi. apply WM. apply WR. lia.
Qed.
#[using="Type"] Lemma dc_at_any : forall m m' A n,
  dc_at m A n -> wmono asegs m m' -> 0x603000 <= A -> dc_at m' A n.
Proof. intros m m' A n D W H. eapply dc_at_any2; [exact D | exact W | right; exact H]. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma seg_rom_high : forall a : word, 0x603000 <= bv_unsigned a -> seg_rom asegs a = None.
Proof. intros a Ha. unfold seg_rom. rewrite ref_memory_read_none; [reflexivity| cbn; lia| lia]. Qed.
#[using="Type"] Lemma mrd_high : forall m a, 0x603000 <= a < 2^64 -> mrd asegs m (wa a) = m (wa a).
Proof.
  intros m a Ha. unfold mrd. destruct (m (wa a)); [reflexivity|]. apply seg_rom_high. rewrite wa_unsigned by lia. lia.
Qed.
#[using="Type"] Lemma rw_C1_high : forall m a (b : byte), rw_cells asegs m a [C1 b] -> 0x603000 <= a -> m (wa a) = Some b.
Proof.
  intros m a b [[WF [B0 [B1 BR]]] _] Ha. specialize (BR 0%nat ltac:(cbn; lia)). cbn in BR, B1.
  rewrite Z.add_0_r in BR. rewrite <- mrd_high by lia. exact BR.
Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac is_Zlit a := lazymatch a with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.
Ltac lit_in H :=
  repeat match type of H with
  | context [Z.add ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.add a b) in change (Z.add a b) with v in H
  | context [Z.sub ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.sub a b) in change (Z.sub a b) with v in H
  | context [Z.mul ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.mul a b) in change (Z.mul a b) with v in H
  end.
Ltac lit_goal :=
  repeat match goal with
  | |- context [Z.add ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.add a b) in change (Z.add a b) with v
  | |- context [Z.sub ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.sub a b) in change (Z.sub a b) with v
  | |- context [Z.mul ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.mul a b) in change (Z.mul a b) with v
  end.

(* [comment removed for export] *)
Ltac addr_diff_g E A :=
  let k := addr_diff E A in
  let ok := eval vm_compute in (Z.ltb k 65536) in
  lazymatch ok with true => k end.

Ltac solve_load_g :=
  match goal with
  | |- context [ov_read_bytes ?segs ?m ?a ?n] =>
    let E := addr_expr a in
    match goal with
    | H : rw_cells segs m ?A ?cs0 |- _ =>
        let k := addr_diff_g E A in
        let kn := eval vm_compute in (Z.to_nat k) in
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          rewrite (rw_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
        end
    | H : ro_cells segs m ?A ?cs0 |- _ =>
        let k := addr_diff_g E A in
        let kn := eval vm_compute in (Z.to_nat k) in
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with ro_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          rewrite (ro_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
        end
    | HR : ov_read_bytes segs m ?a' n = Some ?bs |- _ =>
        cbv delta [wa] in HR;
        first [ rewrite HR
              | replace (ov_read_bytes segs m a n) with (Some bs)
                  by (rewrite <- HR; f_equal; word_eq_tac) ]
    end
  end;
  load_post.

Ltac solve_store_g :=
  match goal with
  | |- context [store_ok ?segs ?m ?a ?n] =>
    rewrite ?store_bytes_8', ?store_bytes_4', ?store_bytes_2', ?store_bytes_1';
    let E := addr_expr a in
    match goal with
    | H : rw_cells segs m ?A ?cs0 |- _ =>
        let k := addr_diff_g E A in
        let kn := eval vm_compute in (Z.to_nat k) in
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          rewrite (rw_cells_store_ok_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac]);
          cbv beta iota;
          match goal with
          | |- context [write_to_mem m a ?bs] =>
              replace (write_to_mem m a bs) with (write_to_mem m (wa (A + Z.of_nat kn)) bs) by (f_equal; addr_eq_tac)
          end
        end
    | HS : store_ok segs m ?a' n = true |- _ =>
        cbv delta [wa] in HS;
        first [ rewrite HS
              | replace (store_ok segs m a n) with true
                  by (rewrite <- HS; f_equal; word_eq_tac);
                try replace (write_to_mem m a) with (write_to_mem m a')
                  by (f_equal; word_eq_tac) ];
        cbv beta iota
    end
  end.

Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma disjoint_from_sub : forall W A n A' n', disjoint_from W A n -> A <= A' -> A' + n' <= A + n -> 0 <= n' ->
  disjoint_from W A' n'.
Proof.
  induction W as [|[lo hi] W IH]; intros A n A' n' H H1 H2 H3; cbn in *; [exact I|].
  destruct H as [D H]. split; [lia|]. eapply IH; eauto.
Qed.

(* [comment removed for export] *)
Definition dc_at (m : word -> option byte) (A n : Z) : Prop :=
  exists bs, rw_cells asegs m A [CB (Z.to_nat n) bs].

#[using="Type"] Lemma dc_split : forall m A a b, dc_at m A (a + b) -> 0 <= a -> 0 <= b ->
  dc_at m A a /\ dc_at m (A + a) b.
Proof.
  intros m A a b [bs H] Ha Hb.
  pose proof (rw_cells_split_CB asegs m A [] (Z.to_nat (a + b)) bs [] [Z.to_nat a; Z.to_nat b] H ltac:(cbn; lia)) as H2.
  cbn [app mk_CB_cells] in H2. apply (proj1 (rw_cells_app asegs m A [_] [_])) in H2. destruct H2 as [H1 H2].
  cbn [cells_size csize Nat.add] in H2. rewrite Nat.add_0_r, Z2Nat.id in H2 by lia.
  split; [eexists; exact H1 | eexists; exact H2].
Qed.

#[using="Type"] Lemma dc_merge : forall m A a b, dc_at m A a -> dc_at m (A + a) b -> 0 <= a -> 0 <= b -> dc_at m A (a + b).
Proof.
  intros m A a b [bs1 H1] [bs2 H2] Ha Hb.
  assert (H : rw_cells asegs m A ([CB (Z.to_nat a) bs1] ++ [CB (Z.to_nat b) bs2])).
  { apply rw_cells_app. split; [exact H1|]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact H2. }
  pose proof (rw_cells_merge asegs m A [] ([CB (Z.to_nat a) bs1] ++ [CB (Z.to_nat b) bs2]) [] ) as M.
  rewrite !app_nil_r in M. cbn [app] in M, H. specialize (M H). cbn [cells_size cells_bytes csize cbytes Nat.add app] in M.
  rewrite app_nil_r, Nat.add_0_r in M. exists (bs1 ++ bs2). rewrite Z2Nat.inj_add by lia. exact M.
Qed.

#[using="Type"] Lemma dc_take : forall m A n k, dc_at m A n -> 0 <= k <= n -> dc_at m A k /\ dc_at m (A + k) (n - k).
Proof. intros m A n k H Hk. apply dc_split; [replace (k + (n - k)) with n by lia; exact H| lia| lia]. Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma dc_sub : forall m A n B k, dc_at m A n -> A <= B -> 0 <= k -> B + k <= A + n -> dc_at m B k.
Proof.
  intros m A n B k H H1 H2 H3.
  destruct (dc_take m A n (B - A) H ltac:(lia)) as [_ D]. replace (A + (B - A)) with B in D by lia.
  destruct (dc_take m B (n - (B - A)) k D ltac:(lia)) as [D' _]. exact D'.
Qed.

#[using="Type"] Lemma c8_of_dc : forall m A, dc_at m A 8 -> exists w : word, rw_cells asegs m A [C8 w].
Proof. intros m A [bs H]. destruct (c8_of_CB m A bs H) as [w [H' _]]. exists w. exact H'. Qed.
#[using="Type"] Lemma c8c8_of_dc : forall m A, dc_at m A 16 -> exists w1 w2 : word, rw_cells asegs m A [C8 w1; C8 w2].
Proof. intros m A [bs H]. exact (c8c8_of_CB m A bs H). Qed.
#[using="Type"] Lemma c1_of_dc : forall m A, dc_at m A 1 -> exists b : byte, rw_cells asegs m A [C1 b].
Proof.
  intros m A [bs H]. pose proof H as H0. destruct H0 as [[[L _] _] _]. cbn in L.
  destruct bs as [|b [|]]; cbn in L; try lia. exists b.
  eapply rw_cells_recast; [exact H | cbn; tauto | reflexivity | reflexivity].
Qed.
#[using="Type"] Lemma dc_of_cells : forall m A cs, rw_cells asegs m A cs -> dc_at m A (Z.of_nat (cells_size cs)).
Proof.
  intros m A cs H. exists (cells_bytes cs). rewrite Nat2Z.id.
  pose proof H as H0. destruct H0 as [[WF _] _].
  eapply rw_cells_recast; [exact H | cbn; split; [symmetry; symmetry; apply cells_bytes_length; exact WF| exact I]
    | cbn; rewrite app_nil_r; reflexivity | cbn; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma dc_at_any2 : forall m m' A n,
  dc_at m A n -> wmono asegs m m' -> (0 <= A /\ A + n <= 0x10000 \/ 0x604000 <= A) -> dc_at m' A n.
Proof.
  intros m m' A n [bs [[[WF _] [B0 [B1 BR]]] [W0 [W1 WR]]]] WM HA. cbn [cells_size csize cells_bytes cbytes app Nat.add] in *.
  rewrite app_nil_r in B1, BR. cbn in WF. rewrite Nat.add_0_r in W1, WR.
  assert (RD : forall i, 0 <= i < Z.of_nat (length bs) -> exists b, m' (wa (A + i)) = Some b).
  { intros i Hi. specialize (WR i ltac:(lia)). apply WM in WR.
    rewrite ref_wview_overlay in WR by (rewrite wa_unsigned by lia; lia).
    destruct (m' (wa (A + i))) as [b|]; [exists b; reflexivity| congruence]. }
  (* [comment removed for export] *)
  assert (BS : forall k, (k <= length bs)%nat -> exists bs' : list byte, length bs' = k /\
            forall i, (i < k)%nat -> m' (wa (A + Z.of_nat i)) = nth_error bs' i).
  { induction k as [|k IH]; intros Hk.
    - exists []. split; [reflexivity|]. intros i Hi. lia.
    - (nd_pre (IH ltac:(lia)) 3%nat; intros bs' L E; nd_post). destruct (RD (Z.of_nat k) ltac:(lia)) as [b Hb].
      exists (bs' ++ [b]). split; [rewrite length_app; cbn; lia|].
      intros i Hi. destruct (Nat.eq_dec i k) as [->|NE].
      + rewrite nth_error_app2 by lia. rewrite L, Nat.sub_diag. cbn. exact Hb.
      + rewrite nth_error_app1 by lia. apply E. lia. }
  (nd_pre (BS (length bs) ltac:(lia)) 3%nat; intros bs' L E; nd_post).
  exists bs'. split; [split; [cbn; destruct WF as [WF _]; split; [lia| exact I]|]|].
  - cbn [cells_bytes cbytes app]. rewrite app_nil_r. split; [lia|]. split; [rewrite L; lia|].
    intros i Hi. unfold mrd. rewrite (E i ltac:(lia)).
    destruct (nth_error bs' i) eqn:N; [reflexivity|]. apply nth_error_None in N. lia.
  - cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. split; [lia|]. split; [lia|].
    intros i Hi. apply WM. apply WR. lia.
Qed.
#[using="Type"] Lemma dc_at_any : forall m m' A n,
  dc_at m A n -> wmono asegs m m' -> 0x604000 <= A -> dc_at m' A n.
Proof. intros m m' A n D W H. eapply dc_at_any2; [exact D | exact W | right; exact H]. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma seg_rom_high : forall a : word, 0x604000 <= bv_unsigned a -> seg_rom asegs a = None.
Proof. intros a Ha. unfold seg_rom. rewrite ref_memory_read_none; [reflexivity| cbn; lia| lia]. Qed.
#[using="Type"] Lemma mrd_high : forall m a, 0x604000 <= a < 2^64 -> mrd asegs m (wa a) = m (wa a).
Proof.
  intros m a Ha. unfold mrd. destruct (m (wa a)); [reflexivity|]. apply seg_rom_high. rewrite wa_unsigned by lia. lia.
Qed.
#[using="Type"] Lemma rw_C1_high : forall m a (b : byte), rw_cells asegs m a [C1 b] -> 0x604000 <= a -> m (wa a) = Some b.
Proof.
  intros m a b [[WF [B0 [B1 BR]]] _] Ha. specialize (BR 0%nat ltac:(cbn; lia)). cbn in BR, B1.
  rewrite Z.add_0_r in BR. rewrite <- mrd_high by lia. exact BR.
Qed.
End CANSEC1.
End TwB.
End FsKit.

(* [comment removed for export] *)
Module F_memset.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StrwF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Section CANSEC1. Context {rc : runConstT}.
Definition memset_entry := 0x9ead4%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End CANSEC1.
Ltac with_arr tac :=
  lazymatch goal with
  | ARR : u8arr ?segs ?m ?A ?bs, FIL : filled ?cb ?bs _, LEN : length ?bs = _ |- _ => tac segs ARR FIL LEN A cb
  end.

(* [comment removed for export] *)
Ltac brute256 c Rc :=
  first [ apply word_eq_of_eqb | apply Z.eqb_eq | idtac ];
  repeat match goal with H : context [c] |- _ => tryif constr_eq H Rc then fail else clear H end;
  revert c Rc; apply brute256_ok; vm_compute; reflexivity.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section CANSEC2. Context {rc : runConstT}.
#[using="Type"] Lemma land4_of_aligned : forall x, (0 <= x)%Z -> (x mod 4 = 0)%Z -> Z.land x 4 = (x mod 8)%Z.
Proof.
  intros x Hx H4.
  transitivity (Z.land (x mod 8) 4).
  { change 8%Z with (2^3)%Z. rewrite <- Z.land_ones by lia. change (Z.ones 3) with 7%Z.
    rewrite <- Z.land_assoc. reflexivity. }
  assert (R : (x mod 8 = 0 \/ x mod 8 = 4)%Z) by (Z.div_mod_to_equations; lia).
  destruct R as [R|R]; rewrite R; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition memset_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 a2 : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned a0)
         [CB (Z.to_nat (bv_unsigned a2)) (repeat (Z_to_bv 8 (bv_unsigned a1 mod 256)) (Z.to_nat (bv_unsigned a2)))].

Section Proofs.
  Variables (RNG : footprint) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Hypothesis MI0 : mem_inv asegs m.
  Hypothesis AB : (0 <= bv_unsigned a0 /\ bv_unsigned a0 + bv_unsigned a2 <= 2^64 /\ 0 <= bv_unsigned a2 < 2^64)%Z.
  (* [comment removed for export] *)
  Hypothesis RR : rng RNG (bv_unsigned a0) (bv_unsigned a2).

  Notation A := (bv_unsigned a0).
  Notation n := (bv_unsigned a2).
  Notation W := [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z.
  Notation POST := (memset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 m).
  (* [comment removed for export] *)
  Notation ST pc mm x11 x12 x13 x14 x15 x16 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 x11 x12 x13 x14 x15 x16 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

  (* [comment removed for export] *)
  Ltac fin_with cover :=
    zstep;
    with_arr ltac:(fun segs ARR FIL LEN A cb =>
      let E := fresh "E" in
      pose proof (filled_all _ _ _ FIL ltac:(cover)) as E;
      rewrite LEN in E; rewrite E in ARR;
      apply rw_cells_of_u8arr in ARR; rewrite repeat_length in ARR);
    finish; subst; assumption.
  Ltac fin := fin_with ltac:(intros j Hj; cbv beta; lia).
  Ltac disj_lia := first [ lia | right; lia | left; disj_lia ].

  (* [comment removed for export] *)
  Lemma memset_loop : forall (K : nat) (c p r e : Z) (m1 : word -> option byte) (bs : list byte) (Q : Z -> Prop)
      (x15 x16 : word),
    Z.to_nat r = K ->
    c = (bv_unsigned a1 mod 256)%Z ->
    u8arr asegs m1 A bs -> filled (Z_to_bv 8 c) bs Q -> length bs = Z.to_nat n ->
    mem_inv asegs m1 -> munch W m m1 -> wmono asegs m m1 ->
    (forall j, (0 <= j < p \/ e <= j < n) -> Q j)%Z ->
    (0 <= p)%Z -> (32 <= r)%Z -> (exists q, r = 4 * q)%Z -> (p + r <= n)%Z -> (e + 28 <= p + r)%Z ->
    evtF asegs RNG POST (ST 0x9ebac m1 (Z_to_bv 64 (A + p)) (Z_to_bv 64 (c * BC8)) (Z_to_bv 64 31) (Z_to_bv 64 r) x15 x16).
  Proof using AB RR.
    induction K as [K IH] using lt_wf_ind; intros c p r e m1 bs Q x15 x16 HK Hc ARR FIL LEN MI MU WM HQ Hp Hr [q4 Hq4] Hpr He;
      assert (Rc : (0 <= c < 256)%Z) by (subst c; apply Z.mod_pos_bound; lia).
    mst p 8%nat ltac:(symmetry; apply le8_bcast; lia).
    mst (p + 8)%Z 8%nat ltac:(symmetry; apply le8_bcast; lia).
    mst (p + 16)%Z 8%nat ltac:(symmetry; apply le8_bcast; lia).
    mst (p + 24)%Z 8%nat ltac:(symmetry; apply le8_bcast; lia).
    zstep. zstep. zstep.
    if_cases KK; zify_cond KK.
    - (* [comment removed for export] *)
      replace (A + p + 32)%Z with (A + (p + 32))%Z by lia.
      replace (r + -32)%Z with (r - 32)%Z by lia.
      eapply (IH (Z.to_nat (r - 32)) ltac:(lia) c (p + 32)%Z (r - 32)%Z e _ _ _ x15 x16 eq_refl Hc ARR); try eassumption; try lia.
      2:{ exists (q4 - 8)%Z. lia. }
      intros j Hj.
      destruct (Z_lt_le_dec j p) as [Hlt|Hge]. { left; left; left; left. apply HQ. lia. }
      destruct (Z_lt_le_dec j (p + 32)) as [Hlt2|Hge2]. 2:{ left; left; left; left. apply HQ. lia. }
      assert (D : ((p <= j < p + 8 \/ p + 8 <= j < p + 16) \/ (p + 16 <= j < p + 24 \/ p + 24 <= j < p + 32))%Z) by lia.
      destruct D as [[?|?]|[?|?]]; [left; left; left; right| left; left; right| left; right| right]; lia.
    - fin_with ltac:(intros j Hj; destruct (Z_lt_le_dec j p); [repeat left; apply HQ; lia|];
                      destruct (Z_lt_le_dec j (p + 32)); [|repeat left; apply HQ; lia]; disj_lia).
  Qed.

  Lemma memset_body : forall junk,
    rw_cells asegs m A [CB (Z.to_nat n) junk] ->
    evtF asegs RNG POST (ST 0x9ead4 m a1 a2 a3 a4 a5 a6).
  Proof using AB MI0 RR.
    intros junk DST. pose proof MI0 as MI.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (zr_word a1) as R1. unfold inr64 in R1.
    remember (bv_unsigned a1 mod 256)%Z as c eqn:Hc.
    assert (Rc : (0 <= c < 256)%Z) by (subst c; apply Z.mod_pos_bound; lia).
    pose proof (u8arr_of_rw_cells _ _ _ _ _ DST) as ARR.
    pose proof (rw_cells_CB_length _ _ _ _ _ DST) as LEN.
    pose proof (filled_init (Z_to_bv 8 c) junk) as FIL.
    (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0. { fin. }
    assert (MF : ms_facts A n 0 1) by (unfold ms_facts; lia).
    pose proof (ms_store_ok asegs _ A n _ 0 1 a0 ARR LEN MF (eq_sym (Z_to_bv_plus0 a0))) as SOK.
    zstep. ms_arr_store MF ltac:(rewrite Hc, le1_byte; reflexivity).
    zstep. zstep. mst (n - 1)%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
    zstep. if_cases K3; zify_cond K3. { fin. }
    mst 1%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
    mst 2%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
    zstep.
    mst (n - 3)%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
    mst (n - 2)%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
    zstep. if_cases K7; zify_cond K7. { fin. }
    mst 3%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
    zstep.
    mst (n - 4)%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
    zstep. if_cases K9; zify_cond K9. { fin. }
    (* [comment removed for export] *)
    zstep. zstep.
    setreg 16%Z (Z_to_bv 64 (c * 2^56)) ltac:(apply Z_to_bv_eqm; rewrite Z.shiftl_mul_pow2 by lia; subst c; Z.div_mod_to_equations; lia).
    zstep. zstep.
    remember (Z.land (bv_swrap 32 (0 - A) mod 18446744073709551616) 3) as k eqn:Hk.
    assert (Rk : (0 <= k < 4 /\ (A + k) mod 4 = 0)%Z).
    { subst k. change 3%Z with (2^2 - 1)%Z. rewrite zb_land_mask by lia.
      unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
      change (2 ^ (Z.of_N 32 - 1))%Z with (2^31)%Z. change (2 ^ Z.of_N 32)%Z with (2^32)%Z.
      Z.div_mod_to_equations. lia. }
    clear Hk.
    zstep. zstep. zstep. zstep. zstep.
    change 18446744073709551612%Z with (2^64 - 2^2)%Z. rewrite land_align_down by lia.
    remember (n - k - (n - k) mod 2^2)%Z as n4 eqn:Hn4.
    assert (Rn4 : (exists q, n4 = 4 * q)%Z /\ (n - k - 3 <= n4 <= n - k)%Z).
    { split. { exists ((n - k) / 4)%Z. subst n4. Z.div_mod_to_equations. lia. } subst n4. Z.div_mod_to_equations. lia. }
    clear Hn4. destruct Rn4 as [[q4 Hq4] Rn4].
    zstep. setreg 12%Z (Z_to_bv 64 (c * BC4)) ltac:(unfold BC4; brute256 c Rc).
    (* [comment removed for export] *)
    mst k 4%nat ltac:(symmetry; apply le4_bcast; lia).
    zstep. mst (k + n4 - 4)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    zstep. if_cases K9'; zify_cond K9'. { fin. }
    mst (k + 4)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    mst (k + 8)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    zstep.
    mst (k + n4 - 12)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    mst (k + n4 - 8)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    zstep. if_cases K25; zify_cond K25. { fin. }
    mst (k + 12)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    mst (k + 16)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    mst (k + 20)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    mst (k + 24)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    (* [comment removed for export] *)
    zstep.
    remember (Z.land (A + k) 4) as k4 eqn:Hk4.
    assert (Rk4 : ((k4 = 0 \/ k4 = 4) /\ (A + k + k4 + 24) mod 8 = 0)%Z).
    { subst k4. rewrite land4_of_aligned by lia. Z.div_mod_to_equations. lia. }
    clear Hk4.
    zstep. zstep. zstep.
    mst (k + n4 - 28)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    mst (k + n4 - 24)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    mst (k + n4 - 20)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    mst (k + n4 - 16)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    zstep. if_cases K32; zify_cond K32. { fin. }
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. setreg 12%Z (Z_to_bv 64 (c * BC8)) ltac:(unfold BC4, BC8; brute256 c Rc).
    zstep.
    replace (A + k + (k4 + 24))%Z with (A + (k + k4 + 24))%Z by lia.
    eapply (memset_loop _ c (k + k4 + 24) _ (k + n4 - 28) _ _ _ _ _ eq_refl Hc ARR); try eassumption; try lia.
    exists (q4 - Z.div k4 4 - 6)%Z. lia.
  Qed.
End Proofs.

#[using="Type"] Lemma memset_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (junk : list byte),
  rw_cells asegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
  mem_inv asegs m ->
  rng RNG (bv_unsigned a0) (bv_unsigned a2) ->
  evtF asegs RNG (memset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x9ead4) fc None m (seg_rom asegs)).
Proof.
  intros until junk. intros DST MI RR.
  eapply memset_body; [exact MI | | exact RR | exact DST].
  pose proof (rw_cells_bound _ _ _ _ DST) as B. cbn [cells_size csize Nat.add] in B.
  pose proof (bv_unsigned_in_range 64 a2) as R. unfold bv_modulus in R. cbn in R. cbn. lia.
Qed.
End CANSEC2.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StrwF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Section CANSEC1. Context {rc : runConstT}.
Definition memset_entry := 0x9eeb8%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End CANSEC1.
Ltac with_arr tac :=
  lazymatch goal with
  | ARR : u8arr ?segs ?m ?A ?bs, FIL : filled ?cb ?bs _, LEN : length ?bs = _ |- _ => tac segs ARR FIL LEN A cb
  end.

(* [comment removed for export] *)
Ltac brute256 c Rc :=
  first [ apply word_eq_of_eqb | apply Z.eqb_eq | idtac ];
  repeat match goal with H : context [c] |- _ => tryif constr_eq H Rc then fail else clear H end;
  revert c Rc; apply brute256_ok; vm_compute; reflexivity.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section CANSEC2. Context {rc : runConstT}.
#[using="Type"] Lemma land4_of_aligned : forall x, (0 <= x)%Z -> (x mod 4 = 0)%Z -> Z.land x 4 = (x mod 8)%Z.
Proof.
  intros x Hx H4.
  transitivity (Z.land (x mod 8) 4).
  { change 8%Z with (2^3)%Z. rewrite <- Z.land_ones by lia. change (Z.ones 3) with 7%Z.
    rewrite <- Z.land_assoc. reflexivity. }
  assert (R : (x mod 8 = 0 \/ x mod 8 = 4)%Z) by (Z.div_mod_to_equations; lia).
  destruct R as [R|R]; rewrite R; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition memset_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 a2 : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned a0)
         [CB (Z.to_nat (bv_unsigned a2)) (repeat (Z_to_bv 8 (bv_unsigned a1 mod 256)) (Z.to_nat (bv_unsigned a2)))].

Section Proofs.
  Variables (RNG : footprint) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Hypothesis MI0 : mem_inv asegs m.
  Hypothesis AB : (0 <= bv_unsigned a0 /\ bv_unsigned a0 + bv_unsigned a2 <= 2^64 /\ 0 <= bv_unsigned a2 < 2^64)%Z.
  (* [comment removed for export] *)
  Hypothesis RR : rng RNG (bv_unsigned a0) (bv_unsigned a2).

  Notation A := (bv_unsigned a0).
  Notation n := (bv_unsigned a2).
  Notation W := [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z.
  Notation POST := (memset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 m).
  (* [comment removed for export] *)
  Notation ST pc mm x11 x12 x13 x14 x15 x16 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 x11 x12 x13 x14 x15 x16 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

  (* [comment removed for export] *)
  Ltac fin_with cover :=
    zstep;
    with_arr ltac:(fun segs ARR FIL LEN A cb =>
      let E := fresh "E" in
      pose proof (filled_all _ _ _ FIL ltac:(cover)) as E;
      rewrite LEN in E; rewrite E in ARR;
      apply rw_cells_of_u8arr in ARR; rewrite repeat_length in ARR);
    finish; subst; assumption.
  Ltac fin := fin_with ltac:(intros j Hj; cbv beta; lia).
  Ltac disj_lia := first [ lia | right; lia | left; disj_lia ].

  (* [comment removed for export] *)
  Lemma memset_loop : forall (K : nat) (c p r e : Z) (m1 : word -> option byte) (bs : list byte) (Q : Z -> Prop)
      (x15 x16 : word),
    Z.to_nat r = K ->
    c = (bv_unsigned a1 mod 256)%Z ->
    u8arr asegs m1 A bs -> filled (Z_to_bv 8 c) bs Q -> length bs = Z.to_nat n ->
    mem_inv asegs m1 -> munch W m m1 -> wmono asegs m m1 ->
    (forall j, (0 <= j < p \/ e <= j < n) -> Q j)%Z ->
    (0 <= p)%Z -> (32 <= r)%Z -> (exists q, r = 4 * q)%Z -> (p + r <= n)%Z -> (e + 28 <= p + r)%Z ->
    evtF asegs RNG POST (ST 0x9ef90 m1 (Z_to_bv 64 (A + p)) (Z_to_bv 64 (c * BC8)) (Z_to_bv 64 31) (Z_to_bv 64 r) x15 x16).
  Proof using AB RR.
    induction K as [K IH] using lt_wf_ind; intros c p r e m1 bs Q x15 x16 HK Hc ARR FIL LEN MI MU WM HQ Hp Hr [q4 Hq4] Hpr He;
      assert (Rc : (0 <= c < 256)%Z) by (subst c; apply Z.mod_pos_bound; lia).
    mst p 8%nat ltac:(symmetry; apply le8_bcast; lia).
    mst (p + 8)%Z 8%nat ltac:(symmetry; apply le8_bcast; lia).
    mst (p + 16)%Z 8%nat ltac:(symmetry; apply le8_bcast; lia).
    mst (p + 24)%Z 8%nat ltac:(symmetry; apply le8_bcast; lia).
    zstep. zstep. zstep.
    if_cases KK; zify_cond KK.
    - (* [comment removed for export] *)
      replace (A + p + 32)%Z with (A + (p + 32))%Z by lia.
      replace (r + -32)%Z with (r - 32)%Z by lia.
      eapply (IH (Z.to_nat (r - 32)) ltac:(lia) c (p + 32)%Z (r - 32)%Z e _ _ _ x15 x16 eq_refl Hc ARR); try eassumption; try lia.
      2:{ exists (q4 - 8)%Z. lia. }
      intros j Hj.
      destruct (Z_lt_le_dec j p) as [Hlt|Hge]. { left; left; left; left. apply HQ. lia. }
      destruct (Z_lt_le_dec j (p + 32)) as [Hlt2|Hge2]. 2:{ left; left; left; left. apply HQ. lia. }
      assert (D : ((p <= j < p + 8 \/ p + 8 <= j < p + 16) \/ (p + 16 <= j < p + 24 \/ p + 24 <= j < p + 32))%Z) by lia.
      destruct D as [[?|?]|[?|?]]; [left; left; left; right| left; left; right| left; right| right]; lia.
    - fin_with ltac:(intros j Hj; destruct (Z_lt_le_dec j p); [repeat left; apply HQ; lia|];
                      destruct (Z_lt_le_dec j (p + 32)); [|repeat left; apply HQ; lia]; disj_lia).
  Qed.

  Lemma memset_body : forall junk,
    rw_cells asegs m A [CB (Z.to_nat n) junk] ->
    evtF asegs RNG POST (ST 0x9eeb8 m a1 a2 a3 a4 a5 a6).
  Proof using AB MI0 RR.
    intros junk DST. pose proof MI0 as MI.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (zr_word a1) as R1. unfold inr64 in R1.
    remember (bv_unsigned a1 mod 256)%Z as c eqn:Hc.
    assert (Rc : (0 <= c < 256)%Z) by (subst c; apply Z.mod_pos_bound; lia).
    pose proof (u8arr_of_rw_cells _ _ _ _ _ DST) as ARR.
    pose proof (rw_cells_CB_length _ _ _ _ _ DST) as LEN.
    pose proof (filled_init (Z_to_bv 8 c) junk) as FIL.
    (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0. { fin. }
    assert (MF : ms_facts A n 0 1) by (unfold ms_facts; lia).
    pose proof (ms_store_ok asegs _ A n _ 0 1 a0 ARR LEN MF (eq_sym (Z_to_bv_plus0 a0))) as SOK.
    zstep. ms_arr_store MF ltac:(rewrite Hc, le1_byte; reflexivity).
    zstep. zstep. mst (n - 1)%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
    zstep. if_cases K3; zify_cond K3. { fin. }
    mst 1%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
    mst 2%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
    zstep.
    mst (n - 3)%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
    mst (n - 2)%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
    zstep. if_cases K7; zify_cond K7. { fin. }
    mst 3%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
    zstep.
    mst (n - 4)%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
    zstep. if_cases K9; zify_cond K9. { fin. }
    (* [comment removed for export] *)
    zstep. zstep.
    setreg 16%Z (Z_to_bv 64 (c * 2^56)) ltac:(apply Z_to_bv_eqm; rewrite Z.shiftl_mul_pow2 by lia; subst c; Z.div_mod_to_equations; lia).
    zstep. zstep.
    remember (Z.land (bv_swrap 32 (0 - A) mod 18446744073709551616) 3) as k eqn:Hk.
    assert (Rk : (0 <= k < 4 /\ (A + k) mod 4 = 0)%Z).
    { subst k. change 3%Z with (2^2 - 1)%Z. rewrite zb_land_mask by lia.
      unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
      change (2 ^ (Z.of_N 32 - 1))%Z with (2^31)%Z. change (2 ^ Z.of_N 32)%Z with (2^32)%Z.
      Z.div_mod_to_equations. lia. }
    clear Hk.
    zstep. zstep. zstep. zstep. zstep.
    change 18446744073709551612%Z with (2^64 - 2^2)%Z. rewrite land_align_down by lia.
    remember (n - k - (n - k) mod 2^2)%Z as n4 eqn:Hn4.
    assert (Rn4 : (exists q, n4 = 4 * q)%Z /\ (n - k - 3 <= n4 <= n - k)%Z).
    { split. { exists ((n - k) / 4)%Z. subst n4. Z.div_mod_to_equations. lia. } subst n4. Z.div_mod_to_equations. lia. }
    clear Hn4. destruct Rn4 as [[q4 Hq4] Rn4].
    zstep. setreg 12%Z (Z_to_bv 64 (c * BC4)) ltac:(unfold BC4; brute256 c Rc).
    (* [comment removed for export] *)
    mst k 4%nat ltac:(symmetry; apply le4_bcast; lia).
    zstep. mst (k + n4 - 4)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    zstep. if_cases K9'; zify_cond K9'. { fin. }
    mst (k + 4)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    mst (k + 8)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    zstep.
    mst (k + n4 - 12)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    mst (k + n4 - 8)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    zstep. if_cases K25; zify_cond K25. { fin. }
    mst (k + 12)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    mst (k + 16)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    mst (k + 20)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    mst (k + 24)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    (* [comment removed for export] *)
    zstep.
    remember (Z.land (A + k) 4) as k4 eqn:Hk4.
    assert (Rk4 : ((k4 = 0 \/ k4 = 4) /\ (A + k + k4 + 24) mod 8 = 0)%Z).
    { subst k4. rewrite land4_of_aligned by lia. Z.div_mod_to_equations. lia. }
    clear Hk4.
    zstep. zstep. zstep.
    mst (k + n4 - 28)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    mst (k + n4 - 24)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    mst (k + n4 - 20)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    mst (k + n4 - 16)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    zstep. if_cases K32; zify_cond K32. { fin. }
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. setreg 12%Z (Z_to_bv 64 (c * BC8)) ltac:(unfold BC4, BC8; brute256 c Rc).
    zstep.
    replace (A + k + (k4 + 24))%Z with (A + (k + k4 + 24))%Z by lia.
    eapply (memset_loop _ c (k + k4 + 24) _ (k + n4 - 28) _ _ _ _ _ eq_refl Hc ARR); try eassumption; try lia.
    exists (q4 - Z.div k4 4 - 6)%Z. lia.
  Qed.
End Proofs.

#[using="Type"] Lemma memset_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (junk : list byte),
  rw_cells asegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
  mem_inv asegs m ->
  rng RNG (bv_unsigned a0) (bv_unsigned a2) ->
  evtF asegs RNG (memset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x9eeb8) fc None m (seg_rom asegs)).
Proof.
  intros until junk. intros DST MI RR.
  eapply memset_body; [exact MI | | exact RR | exact DST].
  pose proof (rw_cells_bound _ _ _ _ DST) as B. cbn [cells_size csize Nat.add] in B.
  pose proof (bv_unsigned_in_range 64 a2) as R. unfold bv_modulus in R. cbn in R. cbn. lia.
Qed.
End CANSEC2.
End TwB.
End F_memset.
