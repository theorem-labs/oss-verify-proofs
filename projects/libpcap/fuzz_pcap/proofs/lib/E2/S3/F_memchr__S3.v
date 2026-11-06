(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Tac Bytes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim.
From Stdlib Require String.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ZBridge Mem Cells.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require PcapPrelim PcapTypes PcapPure Pcap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Fmt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module F_memchr.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
(* [comment removed for export] *)

Definition memchr_entry := 0x20714%Z.

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
             F (ret_pc ra) fc None m' (seg_rom ssegs)
    /\ munch [] m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
    /\ bytes_at ssegs m' (bv_unsigned a0) buf.

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (buf : list byte).
  Hypothesis MI : mem_inv ssegs m.
  Hypothesis BUF : bytes_at ssegs m (bv_unsigned a0) buf.
  Hypothesis OK : memchr_ok (bv_unsigned a0) (bv_unsigned a1 mod 256) (bv_unsigned a2) buf.
  Let MU : munch [] m m := munch_refl [] m.
  Let WM : wmono ssegs m m := wmono_refl ssegs m.

  Notation A := (bv_unsigned a0).
  Notation n := (bv_unsigned a2).
  Notation c := ((bv_unsigned a1) mod 256)%Z.
  Notation len := (Z.of_nat (length buf)).
  Notation POST := (memchr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 buf m).
  (* [comment removed for export] *)
  Notation ST pc x5 x10 x12 x13 x14 x15 x16 x17 :=
    (MS (mkR ra sp gp tp x5 t1 t2 s0 s1 x10 (Z_to_bv 64 c) x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom ssegs)).
  Notation CMAGIC := 72340172838076672%Z.      (* [comment removed for export] *)
  Notation HIGHS := 9259542123273814144%Z.     (* [comment removed for export] *)
  Notation ONES := 72340172838076673%Z.       (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition NOB (i : Z) : Prop :=
    forall j b, (j < Z.to_nat i)%nat -> nth_error buf j = Some b -> bv_unsigned b <> c.

  Lemma A_bound : (0 <= A /\ A + len <= 2^64 /\ 0 <= n < 2^64 /\ 0 <= c < 256)%Z.
  Proof using BUF. pin_using (fun (BUF : unit) => tt).
    pose proof (bytes_at_bound _ _ _ _ BUF).
    pose proof (bv_unsigned_in_range 64 a2) as R. unfold bv_modulus in R. cbn in R.
    pose proof (Z.mod_pos_bound (bv_unsigned a1) 256). cbn. lia.
  Qed.

  Lemma NOB_0 : NOB 0.
  Proof using Type. pin_using tt. intros j b Hj. cbn in Hj. lia. Qed.

  Lemma NOB_S : forall i b, (0 <= i)%Z -> NOB i -> nth_error buf (Z.to_nat i) = Some b -> bv_unsigned b <> c -> NOB (i + 1).
  Proof using Type. pin_using tt.
    intros i b Hi H Hn Hb j b' Hj Hn'.
    destruct (Nat.eq_dec j (Z.to_nat i)) as [->|NE]. { rewrite Hn in Hn'. injection Hn' as <-. exact Hb. }
    eapply H; [|exact Hn']. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma ok_cases :
    (exists j b, Z.of_nat j < n /\ nth_error buf j = Some b /\ bv_unsigned b = c /\
       (forall j' b', (j' < j)%nat -> nth_error buf j' = Some b' -> bv_unsigned b' <> c) /\
       (n <= len \/ Z.of_nat j + 1 + (- (A + Z.of_nat j + 1)) mod 8 <= len))%Z
    \/ ((forall j b, (Z.of_nat j < n)%Z -> nth_error buf j = Some b -> bv_unsigned b <> c) /\ (n <= len)%Z).
  Proof using OK. pin_using (fun (OK : unit) => tt).
    pose proof OK as H. unfold memchr_ok in H.
    destruct (find_byte c (firstn (Z.to_nat n) buf)) as [j|] eqn:FB.
    - left. destruct (find_byte_Some _ _ _ FB) as (Hl & (b & Hn & Hb) & Hmin).
      rewrite firstn_length in Hl.
      rewrite nth_error_firstn in Hn. replace (Nat.ltb j (Z.to_nat n)) with true in Hn by (symmetry; apply Nat.ltb_lt; lia).
      exists j, b. repeat split; try assumption; try lia.
      intros j' b' Hj' Hn'. eapply Hmin; [exact Hj'|]. rewrite nth_error_firstn.
      replace (Nat.ltb j' (Z.to_nat n)) with true by (symmetry; apply Nat.ltb_lt; lia). exact Hn'.
    - right. split; [|exact H]. intros j b Hj Hn. eapply (find_byte_None _ _ FB j). rewrite nth_error_firstn.
      replace (Nat.ltb j (Z.to_nat n)) with true by (symmetry; apply Nat.ltb_lt; lia). exact Hn.
  Qed.

  Lemma readable : forall i, (0 <= i < n)%Z -> NOB i -> exists b, nth_error buf (Z.to_nat i) = Some b.
  Proof using OK. pin_using (fun (OK : unit) => tt).
    intros i Hi HN. destruct (nth_error buf (Z.to_nat i)) as [b|] eqn:E; [exists b; reflexivity|].
    exfalso. apply nth_error_None in E.
    destruct ok_cases as [(j & b & Hj & Hn & Hb & Hmin & _)|(Hall & Hlen)]; [|lia].
    pose proof (nth_error_lt _ _ _ Hn).
    destruct (Nat.lt_ge_cases j (Z.to_nat i)) as [Hlt|Hge]; [|lia].
    exact (HN _ _ Hlt Hn Hb).
  Qed.

  Lemma readable8 : forall i, (0 <= i)%Z -> (i + 8 <= n)%Z -> ((A + i) mod 8 = 0)%Z -> NOB i ->
    (Z.to_nat i + 8 <= length buf)%nat.
  Proof using OK. pin_using (fun (OK : unit) => tt).
    intros i Hi Hi8 Hal HN.
    destruct ok_cases as [(j & b & Hj & Hn & Hb & Hmin & Hsl)|(Hall & Hlen)]; [|lia].
    pose proof (nth_error_lt _ _ _ Hn).
    destruct (Nat.lt_ge_cases j (Z.to_nat i)) as [Hlt|Hge]. { exfalso. exact (HN _ _ Hlt Hn Hb). }
    destruct Hsl as [Hsl|Hsl]; [lia|].
    destruct (Nat.lt_ge_cases j (Z.to_nat i + 8)) as [Hlt8|]; [|lia].
    Z.div_mod_to_equations. lia.
  Qed.

  Lemma res_found : forall i b, (0 <= i < n)%Z -> NOB i -> nth_error buf (Z.to_nat i) = Some b -> bv_unsigned b = c ->
    memchr_res A c n buf = (A + i)%Z.
  Proof using Type. pin_using tt.
    intros i b Hi HN Hn Hb. unfold memchr_res.
    rewrite (find_byte_charact c _ (Z.to_nat i) b); [lia| | exact Hb|].
    - rewrite nth_error_firstn. replace (Nat.ltb _ _) with true by (symmetry; apply Nat.ltb_lt; lia). exact Hn.
    - intros j b' Hj Hn'. rewrite nth_error_firstn in Hn'. destruct (Nat.ltb j (Z.to_nat n)); [|discriminate].
      exact (HN _ _ Hj Hn').
  Qed.

  Lemma res_none : NOB n -> memchr_res A c n buf = 0%Z.
  Proof using Type. pin_using tt.
    intros HN. unfold memchr_res. rewrite find_byte_None_intro; [reflexivity|].
    intros j b Hn. rewrite nth_error_firstn in Hn. destruct (Nat.ltb_spec0 j (Z.to_nat n)); [|discriminate].
    exact (HN j b ltac:(lia) Hn).
  Qed.

  (* [comment removed for export] *)
  Lemma memchr_tail : forall (k : nat) (i : Z) (x5 x12 x14 x15 x16 x17 : word),
    Z.to_nat (n - i) = k -> (0 <= i < n)%Z -> NOB i ->
    evt ssegs POST (ST 0x207b4 x5 (Z_to_bv 64 (A + i)) x12 (Z_to_bv 64 (n - i)) x14 x15 x16 x17).
  Proof using BUF MI OK. pin_using (fun (BUF MI OK : unit) => tt).
    induction k as [|k IH]; intros i x5 x12 x14 x15 x16 x17 Hk Hi HN; pose proof A_bound as AB; [lia|].
    destruct (readable i Hi HN) as [b Hn]. pose proof (nth_error_lt _ _ _ Hn).
    pose proof (u8ro_read ssegs m A buf i b _ BUF Hn ltac:(lia) eq_refl) as RD.
    zstep. zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *) zstep. rewrite <- (res_found i b Hi HN Hn K). finish.
    - zstep. zstep. zstep. if_cases K0; zify_cond K0.
      + replace (n - i + -1)%Z with (n - (i + 1))%Z by lia. replace (A + i + 1)%Z with (A + (i + 1))%Z by lia.
        apply (IH (i + 1)%Z); try lia. eapply NOB_S; eauto; lia.
      + (* [comment removed for export] *) zstep. zstep. rewrite <- res_none at 1. { finish. }
        replace n with (i + 1)%Z by lia. eapply NOB_S; eauto; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma memchr_tail_entry : forall (i : Z) (x5 x13 x14 x15 x16 x17 : word),
    (0 <= i <= n)%Z -> NOB i ->
    evt ssegs POST (ST 0x207ac x5 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (n - i)) x13 x14 x15 x16 x17).
  Proof using BUF MI OK. pin_using (fun (BUF MI OK : unit) => tt).
    intros i x5 x13 x14 x15 x16 x17 Hi HN; pose proof A_bound as AB.
    zstep. zstep. if_cases K; zify_cond K.
    - zstep. zstep. rewrite <- res_none at 1. { finish. } replace n with i by lia. exact HN.
    - apply (memchr_tail (Z.to_nat (n - i)) i); lia || assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma memchr_words : forall (k : nat) (i : Z) (x5 x17 : word),
    Z.to_nat (n - i) = k -> (0 <= i)%Z -> (i + 8 <= n)%Z -> ((A + i) mod 8 = 0)%Z -> NOB i ->
    evt ssegs POST (ST 0x20788 x5 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (n - i)) (Z_to_bv 64 CMAGIC) (Z_to_bv 64 HIGHS)
                       (Z_to_bv 64 (c * ONES)) (Z_to_bv 64 7) x17).
  Proof using BUF MI OK. pin_using (fun (BUF MI OK : unit) => tt).
    induction k as [k IH] using lt_wf_ind; intros i x5 x17 Hk Hi Hi8 Hal HN; pose proof A_bound as AB.
    pose proof (readable8 i Hi Hi8 Hal HN) as HW.
    pose proof (bytes_at_read ssegs m A buf i 8 BUF ltac:(lia) HW) as RD.
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
      pose proof (u8ro_read ssegs m A buf i b _ BUF Hn ltac:(lia) eq_refl) as RD1.
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
  Lemma memchr_mid : forall (i : Z) (x5 x13 x14 x15 x16 x17 : word),
    (0 <= i <= n)%Z -> NOB i -> ((bv_unsigned x14 = 0)%Z <-> i = n) -> (i = n \/ (A + i) mod 8 = 0)%Z ->
    evt ssegs POST (ST 0x20758 x5 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (n - i)) x13 x14 x15 x16 x17).
  Proof using BUF MI OK. pin_using (fun (BUF MI OK : unit) => tt).
    intros i x5 x13 x14 x15 x16 x17 Hi HN H14 Hal; pose proof A_bound as AB.
    zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *) apply H14 in K. subst i. zstep. zstep. rewrite <- res_none at 1; [finish| exact HN].
    - assert (Hin : (i < n)%Z). { destruct (Z.eq_dec i n) as [E|]; [|lia]. exfalso. apply K. apply H14. exact E. }
      destruct Hal as [|Hal]; [lia|].
      destruct (readable i ltac:(lia) HN) as [b Hn].
      pose proof (u8ro_read ssegs m A buf i b _ BUF Hn ltac:(lia) eq_refl) as RD.
      zstep. zstep. if_cases Kb; zify_cond Kb.
      + apply memchr_tail_entry; [lia| exact HN].
      + zstep. zstep. if_cases K8; zify_cond K8.
        * apply memchr_tail_entry; [lia| exact HN].
        * do 7 zstep.
          apply (memchr_words (Z.to_nat (n - i)) i); try lia. exact HN.
  Qed.

  Lemma b2z_word_zero_iff : forall t, bv_unsigned (Z_to_bv 64 (Z.b2z t)) = 0%Z <-> t = false.
  Proof using a1. pin_using (fun (a1 : unit) => tt). intros t. rewrite unsigned_lit by (destruct t; cbn; lia). destruct t; cbn; split; intros; fastfirst (first [ noevar_assumption |congruence | lia]). Qed.

  (* [comment removed for export] *)
  Lemma memchr_head : forall (k : nat) (i : Z) (x5 x13 x14 x17 : word),
    Z.to_nat (n - i) = k -> (0 <= i < n)%Z -> NOB i -> ((A + i) mod 8 <> 0)%Z ->
    evt ssegs POST (ST 0x20730 x5 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (n - i)) x13 x14 (Z_to_bv 64 (A + i + 1)) (Z_to_bv 64 1) x17).
  Proof using BUF MI OK. pin_using (fun (BUF MI OK : unit) => tt).
    induction k as [|k IH]; intros i x5 x13 x14 x17 Hk Hi HN Hal; pose proof A_bound as AB; [lia|].
    destruct (readable i Hi HN) as [b Hn]. pose proof (nth_error_lt _ _ _ Hn).
    pose proof (u8ro_read ssegs m A buf i b _ BUF Hn ltac:(lia) eq_refl) as RD.
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
  Lemma memchr_body :
    evt ssegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x20714) fc None m (seg_rom ssegs)).
  Proof using BUF MI OK. pin_using (fun (BUF MI OK : unit) => tt).
    pose proof A_bound as AB. pose proof (zr_word a1) as R1. unfold inr64 in R1.
    zstep. replace (Z.land (bv_unsigned a1) 255) with c.
    2:{ change 255%Z with (2^8 - 1)%Z. rewrite zb_land_mask by lia. reflexivity. }
    zstep. zstep. zstep. if_cases Kal; zify_cond Kal.
    - (* [comment removed for export] *)
      eapply evt_eq.
      2:{ apply (memchr_mid 0 t0 (Z_to_bv 64 (Z.land A 7)) (Z_to_bv 64 (Z.b2z (0 <? n)%Z)) a5 a6 a7); try lia.
          - apply NOB_0. - rewrite b2z_word_zero_iff, Z.ltb_ge. lia.
          - right. revert Kal. zb_masks. intros Kal. rewrite Z.add_0_r. exact Kal. }
      unfold mkR. rewrite Z_to_bv_plus0, Z.sub_0_r, Z_to_bv_bv_unsigned. reflexivity.
    - zstep. if_cases K0; zify_cond K0.
      + (* [comment removed for export] *)
        eapply evt_eq.
        2:{ apply (memchr_mid 0 t0 (Z_to_bv 64 (Z.land A 7)) (Z_to_bv 64 (Z.b2z (0 <? n)%Z)) a5 a6 a7); try lia.
            - apply NOB_0. - rewrite b2z_word_zero_iff, Z.ltb_ge. lia. }
        unfold mkR. rewrite Z_to_bv_plus0, Z.sub_0_r, Z_to_bv_bv_unsigned. reflexivity.
      + zstep. zstep.
        eapply evt_eq.
        2:{ apply (memchr_head (Z.to_nat n) 0 t0 (Z_to_bv 64 (Z.land A 7)) (Z_to_bv 64 (Z.b2z (0 <? n)%Z)) a7); try lia.
            - apply NOB_0. - revert Kal. zb_masks. intros Kal. rewrite Z.add_0_r. exact Kal. }
        unfold mkR. rewrite Z_to_bv_plus0, Z.sub_0_r, Z_to_bv_bv_unsigned, Z.add_0_r. reflexivity.
  Qed.
End Proofs.

Lemma memchr_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (buf : list byte),
  bytes_at ssegs m (bv_unsigned a0) buf ->
  memchr_ok (bv_unsigned a0) (bv_unsigned a1 mod 256) (bv_unsigned a2) buf ->
  mem_inv ssegs m ->
  evt ssegs (memchr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 buf m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x20714) fc None m (seg_rom ssegs)).
Proof. intros until buf. intros BUF OK MI. apply memchr_body; assumption. Qed.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
(* [comment removed for export] *)

Definition memchr_entry := 0x20ed4%Z.

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
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ bytes_at usegs m' (bv_unsigned a0) buf.

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (buf : list byte).
  Hypothesis MI : mem_inv usegs m.
  Hypothesis BUF : bytes_at usegs m (bv_unsigned a0) buf.
  Hypothesis OK : memchr_ok (bv_unsigned a0) (bv_unsigned a1 mod 256) (bv_unsigned a2) buf.
  Let MU : munch [] m m := munch_refl [] m.
  Let WM : wmono usegs m m := wmono_refl usegs m.

  Notation A := (bv_unsigned a0).
  Notation n := (bv_unsigned a2).
  Notation c := ((bv_unsigned a1) mod 256)%Z.
  Notation len := (Z.of_nat (length buf)).
  Notation POST := (memchr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 buf m).
  (* [comment removed for export] *)
  Notation ST pc x5 x10 x12 x13 x14 x15 x16 x17 :=
    (MS (mkR ra sp gp tp x5 t1 t2 s0 s1 x10 (Z_to_bv 64 c) x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom usegs)).
  Notation CMAGIC := 72340172838076672%Z.      (* [comment removed for export] *)
  Notation HIGHS := 9259542123273814144%Z.     (* [comment removed for export] *)
  Notation ONES := 72340172838076673%Z.       (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition NOB (i : Z) : Prop :=
    forall j b, (j < Z.to_nat i)%nat -> nth_error buf j = Some b -> bv_unsigned b <> c.

  Lemma A_bound : (0 <= A /\ A + len <= 2^64 /\ 0 <= n < 2^64 /\ 0 <= c < 256)%Z.
  Proof using BUF. pin_using (fun (BUF : unit) => tt).
    pose proof (bytes_at_bound _ _ _ _ BUF).
    pose proof (bv_unsigned_in_range 64 a2) as R. unfold bv_modulus in R. cbn in R.
    pose proof (Z.mod_pos_bound (bv_unsigned a1) 256). cbn. lia.
  Qed.

  Lemma NOB_0 : NOB 0.
  Proof using Type. pin_using tt. intros j b Hj. cbn in Hj. lia. Qed.

  Lemma NOB_S : forall i b, (0 <= i)%Z -> NOB i -> nth_error buf (Z.to_nat i) = Some b -> bv_unsigned b <> c -> NOB (i + 1).
  Proof using Type. pin_using tt.
    intros i b Hi H Hn Hb j b' Hj Hn'.
    destruct (Nat.eq_dec j (Z.to_nat i)) as [->|NE]. { rewrite Hn in Hn'. injection Hn' as <-. exact Hb. }
    eapply H; [|exact Hn']. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma ok_cases :
    (exists j b, Z.of_nat j < n /\ nth_error buf j = Some b /\ bv_unsigned b = c /\
       (forall j' b', (j' < j)%nat -> nth_error buf j' = Some b' -> bv_unsigned b' <> c) /\
       (n <= len \/ Z.of_nat j + 1 + (- (A + Z.of_nat j + 1)) mod 8 <= len))%Z
    \/ ((forall j b, (Z.of_nat j < n)%Z -> nth_error buf j = Some b -> bv_unsigned b <> c) /\ (n <= len)%Z).
  Proof using OK. pin_using (fun (OK : unit) => tt).
    pose proof OK as H. unfold memchr_ok in H.
    destruct (find_byte c (firstn (Z.to_nat n) buf)) as [j|] eqn:FB.
    - left. destruct (find_byte_Some _ _ _ FB) as (Hl & (b & Hn & Hb) & Hmin).
      rewrite firstn_length in Hl.
      rewrite nth_error_firstn in Hn. replace (Nat.ltb j (Z.to_nat n)) with true in Hn by (symmetry; apply Nat.ltb_lt; lia).
      exists j, b. repeat split; try assumption; try lia.
      intros j' b' Hj' Hn'. eapply Hmin; [exact Hj'|]. rewrite nth_error_firstn.
      replace (Nat.ltb j' (Z.to_nat n)) with true by (symmetry; apply Nat.ltb_lt; lia). exact Hn'.
    - right. split; [|exact H]. intros j b Hj Hn. eapply (find_byte_None _ _ FB j). rewrite nth_error_firstn.
      replace (Nat.ltb j (Z.to_nat n)) with true by (symmetry; apply Nat.ltb_lt; lia). exact Hn.
  Qed.

  Lemma readable : forall i, (0 <= i < n)%Z -> NOB i -> exists b, nth_error buf (Z.to_nat i) = Some b.
  Proof using OK. pin_using (fun (OK : unit) => tt).
    intros i Hi HN. destruct (nth_error buf (Z.to_nat i)) as [b|] eqn:E; [exists b; reflexivity|].
    exfalso. apply nth_error_None in E.
    destruct ok_cases as [(j & b & Hj & Hn & Hb & Hmin & _)|(Hall & Hlen)]; [|lia].
    pose proof (nth_error_lt _ _ _ Hn).
    destruct (Nat.lt_ge_cases j (Z.to_nat i)) as [Hlt|Hge]; [|lia].
    exact (HN _ _ Hlt Hn Hb).
  Qed.

  Lemma readable8 : forall i, (0 <= i)%Z -> (i + 8 <= n)%Z -> ((A + i) mod 8 = 0)%Z -> NOB i ->
    (Z.to_nat i + 8 <= length buf)%nat.
  Proof using OK. pin_using (fun (OK : unit) => tt).
    intros i Hi Hi8 Hal HN.
    destruct ok_cases as [(j & b & Hj & Hn & Hb & Hmin & Hsl)|(Hall & Hlen)]; [|lia].
    pose proof (nth_error_lt _ _ _ Hn).
    destruct (Nat.lt_ge_cases j (Z.to_nat i)) as [Hlt|Hge]. { exfalso. exact (HN _ _ Hlt Hn Hb). }
    destruct Hsl as [Hsl|Hsl]; [lia|].
    destruct (Nat.lt_ge_cases j (Z.to_nat i + 8)) as [Hlt8|]; [|lia].
    Z.div_mod_to_equations. lia.
  Qed.

  Lemma res_found : forall i b, (0 <= i < n)%Z -> NOB i -> nth_error buf (Z.to_nat i) = Some b -> bv_unsigned b = c ->
    memchr_res A c n buf = (A + i)%Z.
  Proof using Type. pin_using tt.
    intros i b Hi HN Hn Hb. unfold memchr_res.
    rewrite (find_byte_charact c _ (Z.to_nat i) b); [lia| | exact Hb|].
    - rewrite nth_error_firstn. replace (Nat.ltb _ _) with true by (symmetry; apply Nat.ltb_lt; lia). exact Hn.
    - intros j b' Hj Hn'. rewrite nth_error_firstn in Hn'. destruct (Nat.ltb j (Z.to_nat n)); [|discriminate].
      exact (HN _ _ Hj Hn').
  Qed.

  Lemma res_none : NOB n -> memchr_res A c n buf = 0%Z.
  Proof using Type. pin_using tt.
    intros HN. unfold memchr_res. rewrite find_byte_None_intro; [reflexivity|].
    intros j b Hn. rewrite nth_error_firstn in Hn. destruct (Nat.ltb_spec0 j (Z.to_nat n)); [|discriminate].
    exact (HN j b ltac:(lia) Hn).
  Qed.

  (* [comment removed for export] *)
  Lemma memchr_tail : forall (k : nat) (i : Z) (x5 x12 x14 x15 x16 x17 : word),
    Z.to_nat (n - i) = k -> (0 <= i < n)%Z -> NOB i ->
    evt usegs POST (ST 0x20f74 x5 (Z_to_bv 64 (A + i)) x12 (Z_to_bv 64 (n - i)) x14 x15 x16 x17).
  Proof using BUF MI OK. pin_using (fun (BUF MI OK : unit) => tt).
    induction k as [|k IH]; intros i x5 x12 x14 x15 x16 x17 Hk Hi HN; pose proof A_bound as AB; [lia|].
    destruct (readable i Hi HN) as [b Hn]. pose proof (nth_error_lt _ _ _ Hn).
    pose proof (u8ro_read usegs m A buf i b _ BUF Hn ltac:(lia) eq_refl) as RD.
    zstep. zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *) zstep. rewrite <- (res_found i b Hi HN Hn K). finish.
    - zstep. zstep. zstep. if_cases K0; zify_cond K0.
      + replace (n - i + -1)%Z with (n - (i + 1))%Z by lia. replace (A + i + 1)%Z with (A + (i + 1))%Z by lia.
        apply (IH (i + 1)%Z); try lia. eapply NOB_S; eauto; lia.
      + (* [comment removed for export] *) zstep. zstep. rewrite <- res_none at 1. { finish. }
        replace n with (i + 1)%Z by lia. eapply NOB_S; eauto; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma memchr_tail_entry : forall (i : Z) (x5 x13 x14 x15 x16 x17 : word),
    (0 <= i <= n)%Z -> NOB i ->
    evt usegs POST (ST 0x20f6c x5 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (n - i)) x13 x14 x15 x16 x17).
  Proof using BUF MI OK. pin_using (fun (BUF MI OK : unit) => tt).
    intros i x5 x13 x14 x15 x16 x17 Hi HN; pose proof A_bound as AB.
    zstep. zstep. if_cases K; zify_cond K.
    - zstep. zstep. rewrite <- res_none at 1. { finish. } replace n with i by lia. exact HN.
    - apply (memchr_tail (Z.to_nat (n - i)) i); lia || assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma memchr_words : forall (k : nat) (i : Z) (x5 x17 : word),
    Z.to_nat (n - i) = k -> (0 <= i)%Z -> (i + 8 <= n)%Z -> ((A + i) mod 8 = 0)%Z -> NOB i ->
    evt usegs POST (ST 0x20f48 x5 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (n - i)) (Z_to_bv 64 CMAGIC) (Z_to_bv 64 HIGHS)
                       (Z_to_bv 64 (c * ONES)) (Z_to_bv 64 7) x17).
  Proof using BUF MI OK. pin_using (fun (BUF MI OK : unit) => tt).
    induction k as [k IH] using lt_wf_ind; intros i x5 x17 Hk Hi Hi8 Hal HN; pose proof A_bound as AB.
    pose proof (readable8 i Hi Hi8 Hal HN) as HW.
    pose proof (bytes_at_read usegs m A buf i 8 BUF ltac:(lia) HW) as RD.
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
      pose proof (u8ro_read usegs m A buf i b _ BUF Hn ltac:(lia) eq_refl) as RD1.
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
  Lemma memchr_mid : forall (i : Z) (x5 x13 x14 x15 x16 x17 : word),
    (0 <= i <= n)%Z -> NOB i -> ((bv_unsigned x14 = 0)%Z <-> i = n) -> (i = n \/ (A + i) mod 8 = 0)%Z ->
    evt usegs POST (ST 0x20f18 x5 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (n - i)) x13 x14 x15 x16 x17).
  Proof using BUF MI OK. pin_using (fun (BUF MI OK : unit) => tt).
    intros i x5 x13 x14 x15 x16 x17 Hi HN H14 Hal; pose proof A_bound as AB.
    zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *) apply H14 in K. subst i. zstep. zstep. rewrite <- res_none at 1; [finish| exact HN].
    - assert (Hin : (i < n)%Z). { destruct (Z.eq_dec i n) as [E|]; [|lia]. exfalso. apply K. apply H14. exact E. }
      destruct Hal as [|Hal]; [lia|].
      destruct (readable i ltac:(lia) HN) as [b Hn].
      pose proof (u8ro_read usegs m A buf i b _ BUF Hn ltac:(lia) eq_refl) as RD.
      zstep. zstep. if_cases Kb; zify_cond Kb.
      + apply memchr_tail_entry; [lia| exact HN].
      + zstep. zstep. if_cases K8; zify_cond K8.
        * apply memchr_tail_entry; [lia| exact HN].
        * do 7 zstep.
          apply (memchr_words (Z.to_nat (n - i)) i); try lia. exact HN.
  Qed.

  Lemma b2z_word_zero_iff : forall t, bv_unsigned (Z_to_bv 64 (Z.b2z t)) = 0%Z <-> t = false.
  Proof using a1. pin_using (fun (a1 : unit) => tt). intros t. rewrite unsigned_lit by (destruct t; cbn; lia). destruct t; cbn; split; intros; fastfirst (first [ noevar_assumption |congruence | lia]). Qed.

  (* [comment removed for export] *)
  Lemma memchr_head : forall (k : nat) (i : Z) (x5 x13 x14 x17 : word),
    Z.to_nat (n - i) = k -> (0 <= i < n)%Z -> NOB i -> ((A + i) mod 8 <> 0)%Z ->
    evt usegs POST (ST 0x20ef0 x5 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (n - i)) x13 x14 (Z_to_bv 64 (A + i + 1)) (Z_to_bv 64 1) x17).
  Proof using BUF MI OK. pin_using (fun (BUF MI OK : unit) => tt).
    induction k as [|k IH]; intros i x5 x13 x14 x17 Hk Hi HN Hal; pose proof A_bound as AB; [lia|].
    destruct (readable i Hi HN) as [b Hn]. pose proof (nth_error_lt _ _ _ Hn).
    pose proof (u8ro_read usegs m A buf i b _ BUF Hn ltac:(lia) eq_refl) as RD.
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
  Lemma memchr_body :
    evt usegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x20ed4) fc None m (seg_rom usegs)).
  Proof using BUF MI OK. pin_using (fun (BUF MI OK : unit) => tt).
    pose proof A_bound as AB. pose proof (zr_word a1) as R1. unfold inr64 in R1.
    zstep. replace (Z.land (bv_unsigned a1) 255) with c.
    2:{ change 255%Z with (2^8 - 1)%Z. rewrite zb_land_mask by lia. reflexivity. }
    zstep. zstep. zstep. if_cases Kal; zify_cond Kal.
    - (* [comment removed for export] *)
      eapply evt_eq.
      2:{ apply (memchr_mid 0 t0 (Z_to_bv 64 (Z.land A 7)) (Z_to_bv 64 (Z.b2z (0 <? n)%Z)) a5 a6 a7); try lia.
          - apply NOB_0. - rewrite b2z_word_zero_iff, Z.ltb_ge. lia.
          - right. revert Kal. zb_masks. intros Kal. rewrite Z.add_0_r. exact Kal. }
      unfold mkR. rewrite Z_to_bv_plus0, Z.sub_0_r, Z_to_bv_bv_unsigned. reflexivity.
    - zstep. if_cases K0; zify_cond K0.
      + (* [comment removed for export] *)
        eapply evt_eq.
        2:{ apply (memchr_mid 0 t0 (Z_to_bv 64 (Z.land A 7)) (Z_to_bv 64 (Z.b2z (0 <? n)%Z)) a5 a6 a7); try lia.
            - apply NOB_0. - rewrite b2z_word_zero_iff, Z.ltb_ge. lia. }
        unfold mkR. rewrite Z_to_bv_plus0, Z.sub_0_r, Z_to_bv_bv_unsigned. reflexivity.
      + zstep. zstep.
        eapply evt_eq.
        2:{ apply (memchr_head (Z.to_nat n) 0 t0 (Z_to_bv 64 (Z.land A 7)) (Z_to_bv 64 (Z.b2z (0 <? n)%Z)) a7); try lia.
            - apply NOB_0. - revert Kal. zb_masks. intros Kal. rewrite Z.add_0_r. exact Kal. }
        unfold mkR. rewrite Z_to_bv_plus0, Z.sub_0_r, Z_to_bv_bv_unsigned, Z.add_0_r. reflexivity.
  Qed.
End Proofs.

Lemma memchr_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (buf : list byte),
  bytes_at usegs m (bv_unsigned a0) buf ->
  memchr_ok (bv_unsigned a0) (bv_unsigned a1 mod 256) (bv_unsigned a2) buf ->
  mem_inv usegs m ->
  evt usegs (memchr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 buf m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x20ed4) fc None m (seg_rom usegs)).
Proof. intros until buf. intros BUF OK MI. apply memchr_body; assumption. Qed.
End TwB.
End F_memchr.

(* [comment removed for export] *)
Module F_memset.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_memset.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
(* [comment removed for export] *)

Definition memset_entry := 0x20d60%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
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
Ltac reg_val r :=
  lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
    let p := eval vm_compute in (bv_key (Z_to_bv 5 r)) in
    eval cbv beta iota delta [tget mkR] in (match tget p R with Some v => v | None => w0 end)
  end.
(* [comment removed for export] *)
Ltac setreg r v' tac := let v := reg_val r in replace v with v' by tac.

Lemma land4_of_aligned : forall x, (0 <= x)%Z -> (x mod 4 = 0)%Z -> Z.land x 4 = (x mod 8)%Z.
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
             F (ret_pc ra) fc None m' (seg_rom ssegs)
    /\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
    /\ rw_cells ssegs m' (bv_unsigned a0)
         [CB (Z.to_nat (bv_unsigned a2)) (repeat (Z_to_bv 8 (bv_unsigned a1 mod 256)) (Z.to_nat (bv_unsigned a2)))].

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Hypothesis MI0 : mem_inv ssegs m.
  Hypothesis AB : (0 <= bv_unsigned a0 /\ bv_unsigned a0 + bv_unsigned a2 <= 2^64 /\ 0 <= bv_unsigned a2 < 2^64)%Z.

  Notation A := (bv_unsigned a0).
  Notation n := (bv_unsigned a2).
  Notation W := [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z.
  Notation POST := (memset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 m).
  (* [comment removed for export] *)
  Notation ST pc mm x11 x12 x13 x14 x15 x16 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 x11 x12 x13 x14 x15 x16 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom ssegs)).

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
  Ltac disj_lia := fastfirst (first [ noevar_assumption | lia | right; lia | left; disj_lia ]).

  (* [comment removed for export] *)
  Lemma memset_loop : forall (K : nat) (c p r e : Z) (m1 : word -> option byte) (bs : list byte) (Q : Z -> Prop)
      (x15 x16 : word),
    Z.to_nat r = K ->
    c = (bv_unsigned a1 mod 256)%Z ->
    u8arr ssegs m1 A bs -> filled (Z_to_bv 8 c) bs Q -> length bs = Z.to_nat n ->
    mem_inv ssegs m1 -> munch W m m1 -> wmono ssegs m m1 ->
    (forall j, (0 <= j < p \/ e <= j < n) -> Q j)%Z ->
    (0 <= p)%Z -> (32 <= r)%Z -> (exists q, r = 4 * q)%Z -> (p + r <= n)%Z -> (e + 28 <= p + r)%Z ->
    evt ssegs POST (ST 0x20e38 m1 (Z_to_bv 64 (A + p)) (Z_to_bv 64 (c * BC8)) (Z_to_bv 64 31) (Z_to_bv 64 r) x15 x16).
  Proof using AB.
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
    rw_cells ssegs m A [CB (Z.to_nat n) junk] ->
    evt ssegs POST (ST 0x20d60 m a1 a2 a3 a4 a5 a6).
  Proof using AB MI0.
    intros junk DST. pose proof MI0 as MI.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl ssegs m) as WM.
    pose proof (zr_word a1) as R1. unfold inr64 in R1.
    remember (bv_unsigned a1 mod 256)%Z as c eqn:Hc.
    assert (Rc : (0 <= c < 256)%Z) by (subst c; apply Z.mod_pos_bound; lia).
    pose proof (u8arr_of_rw_cells _ _ _ _ _ DST) as ARR.
    pose proof (rw_cells_CB_length _ _ _ _ _ DST) as LEN.
    pose proof (filled_init (Z_to_bv 8 c) junk) as FIL.
    (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0. { fin. }
    assert (MF : ms_facts A n 0 1) by (unfold ms_facts; lia).
    pose proof (ms_store_ok ssegs _ A n _ 0 1 a0 ARR LEN MF (eq_sym (Z_to_bv_plus0 a0))) as SOK.
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

Lemma memset_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (junk : list byte),
  rw_cells ssegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
  mem_inv ssegs m ->
  evt ssegs (memset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x20d60) fc None m (seg_rom ssegs)).
Proof.
  intros until junk. intros DST MI.
  eapply memset_body; [exact MI | | exact DST].
  pose proof (rw_cells_bound _ _ _ _ DST) as B. cbn [cells_size csize Nat.add] in B.
  pose proof (bv_unsigned_in_range 64 a2) as R. unfold bv_modulus in R. cbn in R. cbn. lia.
Qed.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_memset.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
(* [comment removed for export] *)

Definition memset_entry := 0x21520%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
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
Ltac reg_val r :=
  lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
    let p := eval vm_compute in (bv_key (Z_to_bv 5 r)) in
    eval cbv beta iota delta [tget mkR] in (match tget p R with Some v => v | None => w0 end)
  end.
(* [comment removed for export] *)
Ltac setreg r v' tac := let v := reg_val r in replace v with v' by tac.

Lemma land4_of_aligned : forall x, (0 <= x)%Z -> (x mod 4 = 0)%Z -> Z.land x 4 = (x mod 8)%Z.
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
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ rw_cells usegs m' (bv_unsigned a0)
         [CB (Z.to_nat (bv_unsigned a2)) (repeat (Z_to_bv 8 (bv_unsigned a1 mod 256)) (Z.to_nat (bv_unsigned a2)))].

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Hypothesis MI0 : mem_inv usegs m.
  Hypothesis AB : (0 <= bv_unsigned a0 /\ bv_unsigned a0 + bv_unsigned a2 <= 2^64 /\ 0 <= bv_unsigned a2 < 2^64)%Z.

  Notation A := (bv_unsigned a0).
  Notation n := (bv_unsigned a2).
  Notation W := [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z.
  Notation POST := (memset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 m).
  (* [comment removed for export] *)
  Notation ST pc mm x11 x12 x13 x14 x15 x16 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 x11 x12 x13 x14 x15 x16 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

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
  Ltac disj_lia := fastfirst (first [ noevar_assumption | lia | right; lia | left; disj_lia ]).

  (* [comment removed for export] *)
  Lemma memset_loop : forall (K : nat) (c p r e : Z) (m1 : word -> option byte) (bs : list byte) (Q : Z -> Prop)
      (x15 x16 : word),
    Z.to_nat r = K ->
    c = (bv_unsigned a1 mod 256)%Z ->
    u8arr usegs m1 A bs -> filled (Z_to_bv 8 c) bs Q -> length bs = Z.to_nat n ->
    mem_inv usegs m1 -> munch W m m1 -> wmono usegs m m1 ->
    (forall j, (0 <= j < p \/ e <= j < n) -> Q j)%Z ->
    (0 <= p)%Z -> (32 <= r)%Z -> (exists q, r = 4 * q)%Z -> (p + r <= n)%Z -> (e + 28 <= p + r)%Z ->
    evt usegs POST (ST 0x215f8 m1 (Z_to_bv 64 (A + p)) (Z_to_bv 64 (c * BC8)) (Z_to_bv 64 31) (Z_to_bv 64 r) x15 x16).
  Proof using AB.
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
    rw_cells usegs m A [CB (Z.to_nat n) junk] ->
    evt usegs POST (ST 0x21520 m a1 a2 a3 a4 a5 a6).
  Proof using AB MI0.
    intros junk DST. pose proof MI0 as MI.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof (zr_word a1) as R1. unfold inr64 in R1.
    remember (bv_unsigned a1 mod 256)%Z as c eqn:Hc.
    assert (Rc : (0 <= c < 256)%Z) by (subst c; apply Z.mod_pos_bound; lia).
    pose proof (u8arr_of_rw_cells _ _ _ _ _ DST) as ARR.
    pose proof (rw_cells_CB_length _ _ _ _ _ DST) as LEN.
    pose proof (filled_init (Z_to_bv 8 c) junk) as FIL.
    (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0. { fin. }
    assert (MF : ms_facts A n 0 1) by (unfold ms_facts; lia).
    pose proof (ms_store_ok usegs _ A n _ 0 1 a0 ARR LEN MF (eq_sym (Z_to_bv_plus0 a0))) as SOK.
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

Lemma memset_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (junk : list byte),
  rw_cells usegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
  mem_inv usegs m ->
  evt usegs (memset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x21520) fc None m (seg_rom usegs)).
Proof.
  intros until junk. intros DST MI.
  eapply memset_body; [exact MI | | exact DST].
  pose proof (rw_cells_bound _ _ _ _ DST) as B. cbn [cells_size csize Nat.add] in B.
  pose proof (bv_unsigned_in_range 64 a2) as R. unfold bv_modulus in R. cbn in R. cbn. lia.
Qed.
End TwB.
End F_memset.

(* [comment removed for export] *)
Module F_strlen.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
(* [comment removed for export] *)

Definition strlen_entry := 0x2100c%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition strlen_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 : word) (str slack : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat (length str))) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ssegs)
    /\ munch [] m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
    /\ bytes_at ssegs m' (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack).

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (str slack : list byte).
  Hypothesis MI : mem_inv ssegs m.
  Hypothesis STR : bytes_at ssegs m (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack).
  Hypothesis NONUL : ~ In (Z_to_bv 8 0) str.
  Hypothesis PAD : ((- (bv_unsigned a0 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z.
  Let MU : munch [] m m := munch_refl [] m.
  Let WM : wmono ssegs m m := wmono_refl ssegs m.

  Notation A := (bv_unsigned a0).
  Notation len := (Z.of_nat (length str)).
  Notation full := (str ++ Z_to_bv 8 0 :: slack).
  Notation POST := (strlen_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 str slack m).
  (* [comment removed for export] *)
  Notation ST pc x11 x12 x13 x14 x15 x16 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 x11 x12 x13 x14 x15 x16 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom ssegs)).
  Notation CMAGIC := 72340172838076672%Z.      (* [comment removed for export] *)
  Notation HIGHS := 9259542123273814144%Z.     (* [comment removed for export] *)

  Lemma full_length : length full = (length str + S (length slack))%nat.
  Proof using a0. pin_using (fun (a0 : unit) => tt). rewrite length_app. cbn. lia. Qed.

  Lemma A_bound : (0 <= A /\ A + len + 1 + Z.of_nat (length slack) <= 2^64)%Z.
  Proof using STR. pin_using (fun (STR : unit) => tt). pose proof (bytes_at_bound _ _ _ _ STR) as B. rewrite full_length in B. lia. Qed.

  Lemma full_nth_lt : forall i, (0 <= i < len)%Z ->
    exists b, nth_error full (Z.to_nat i) = Some b /\ bv_unsigned b <> 0%Z.
  Proof using NONUL a0. pin_using (fun (NONUL a0 : unit) => tt).
    intros i Hi. destruct (nth_error str (Z.to_nat i)) as [b|] eqn:E.
    - exists b. split. { rewrite nth_error_app1 by lia. exact E. }
      intros Hb. apply NONUL. replace (Z_to_bv 8 0) with b. { eapply nth_error_In; eauto. }
      apply bv_eq. rewrite Hb. reflexivity.
    - apply nth_error_None in E. lia.
  Qed.

  Lemma full_nth_len : nth_error full (Z.to_nat len) = Some (Z_to_bv 8 0).
  Proof using a0. pin_using (fun (a0 : unit) => tt). rewrite nth_error_app2, Nat2Z.id, Nat.sub_diag by lia. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma strlen_tail : forall (k : nat) (i : Z) (a3 a4 a5 a6 : word),
    (Z.to_nat (len - i) = k) -> (0 <= i <= len)%Z ->
    evt ssegs POST (ST 0x2107c (Z_to_bv 64 (A + i - 1)) (Z_to_bv 64 (A + i)) a3 a4 a5 a6).
  Proof using MI NONUL STR. pin_using (fun (MI NONUL STR : unit) => tt).
    induction k as [|k IH]; intros i a3 a4 a5 a6 Hk Hi; pose proof A_bound as AB.
    - assert (Ei : i = len) by lia. subst i.
      pose proof (u8ro_read ssegs m A full len _ _ STR full_nth_len ltac:(lia) eq_refl) as RD.
      do 4 zstep. if_false. zstep. zstep.
      replace (A + len - 1 + 1 - A)%Z with len by lia. finish.
    - destruct (full_nth_lt i ltac:(lia)) as (b & Hn & Hb).
      pose proof (u8ro_read ssegs m A full i b _ STR Hn ltac:(lia) eq_refl) as RD.
      do 4 zstep. if_cases K; zify_cond K. 2:{ exfalso. exact (Hb K). }
      replace (A + i - 1 + 1)%Z with (A + (i + 1) - 1)%Z by lia.
      replace (A + i + 1)%Z with (A + (i + 1))%Z by lia.
      apply (IH (i + 1)%Z); lia.
  Qed.

  (* [comment removed for export] *)
  Lemma strlen_words : forall (k : nat) (j : Z) (a5 a6 : word),
    (Z.to_nat (len - j) = k) -> (0 <= j <= len)%Z -> ((A + j) mod 8 = 0)%Z ->
    evt ssegs POST (ST 0x21060 (Z_to_bv 64 (A + j - 9)) (Z_to_bv 64 (A + j - 8)) (Z_to_bv 64 CMAGIC) (Z_to_bv 64 HIGHS) a5 a6).
  Proof using MI NONUL PAD STR. pin_using (fun (MI NONUL PAD STR : unit) => tt).
    induction k as [k IH] using lt_wf_ind; intros j a5 a6 Hk Hj Hal; pose proof A_bound as AB.
    assert (HW : (Z.to_nat j + 8 <= length full)%nat).
    { rewrite full_length. Z.div_mod_to_equations. lia. }
    pose proof (bytes_at_read ssegs m A full j 8 STR ltac:(lia) HW) as RD.
    set (chunk := firstn 8 (skipn (Z.to_nat j) full)) in RD.
    assert (CL : length chunk = 8%nat). { subst chunk. rewrite firstn_length, skipn_length. lia. }
    pose proof (le_val_range _ (bytes_ok_map chunk)) as WR. rewrite length_map, CL in WR.
    change (256 ^ Z.of_nat 8)%Z with (2^64)%Z in WR.
    do 7 zstep.
    replace (A + j - 8 + 8)%Z with (A + j)%Z by lia.
    replace (A + j - 9 + 8)%Z with (A + j - 1)%Z by lia.
    rewrite (load8_le_val chunk CL).
    if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      apply (haszero64_clang _ (bytes_ok_map chunk) ltac:(rewrite length_map; exact CL)) in K.
      rewrite In0_map_unsigned in K.
      assert (Hj8 : (j + 8 <= len)%Z).
      { destruct (Z.lt_ge_cases len (j + 8)); [|assumption]. exfalso. apply K. subst chunk.
        apply nth_error_In with (n := (Z.to_nat len - Z.to_nat j)%nat).
        rewrite nth_error_firstn. replace (Nat.ltb _ _) with true by (symmetry; apply Nat.ltb_lt; lia).
        rewrite nth_error_skipn, <- full_nth_len. f_equal. lia. }
      replace (A + j - 1)%Z with (A + (j + 8) - 9)%Z by lia.
      replace (Z_to_bv 64 (A + j)) with (Z_to_bv 64 (A + (j + 8) - 8)) by (f_equal; lia).
      apply (IH (Z.to_nat (len - (j + 8)))); try lia. all: Z.div_mod_to_equations; lia.
    - (* [comment removed for export] *)
      apply (strlen_tail (Z.to_nat (len - j)) j); lia.
  Qed.

  (* [comment removed for export] *)
  Lemma strlen_wentry : forall (j : Z) (a1 a3 a4 a5 a6 : word),
    (0 <= j <= len)%Z -> ((A + j) mod 8 = 0)%Z ->
    evt ssegs POST (ST 0x21048 a1 (Z_to_bv 64 (A + j)) a3 a4 a5 a6).
  Proof using MI NONUL PAD STR. pin_using (fun (MI NONUL PAD STR : unit) => tt).
    intros j a1 a3 a4 a5 a6 Hj Hal. pose proof A_bound as AB.
    do 6 zstep.
    replace (A + j + -9)%Z with (A + j - 9)%Z by lia.
    replace (A + j + -8)%Z with (A + j - 8)%Z by lia.
    apply (strlen_words (Z.to_nat (len - j)) j); lia.
  Qed.

  (* [comment removed for export] *)
  Lemma strlen_head : forall (k : nat) (i : Z) (a3 a4 a5 a6 : word),
    (Z.to_nat (len - i) = k) -> (0 <= i < len)%Z ->
    evt ssegs POST (ST 0x21028 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (A + i + 1)) a3 a4 a5 a6).
  Proof using MI NONUL PAD STR. pin_using (fun (MI NONUL PAD STR : unit) => tt).
    induction k as [|k IH]; intros i a3 a4 a5 a6 Hk Hi; pose proof A_bound as AB; [lia|].
    do 3 zstep. if_cases Kal; zify_cond Kal.
    - replace (A + i + 1)%Z with (A + (i + 1))%Z by lia.
      apply strlen_wentry; [lia|]. revert Kal. zb_masks. intros Kal. Z.div_mod_to_equations; lia.
    - destruct (Z.eq_dec (i + 1) len) as [E|NE].
      + pose proof (u8ro_read ssegs m A full len _ _ STR full_nth_len ltac:(lia) eq_refl) as RD.
        do 4 zstep. if_false. do 3 zstep.
        replace (A + i + 1 - A)%Z with len by lia. finish.
      + destruct (full_nth_lt (i + 1) ltac:(lia)) as (b & Hn & Hb).
        pose proof (u8ro_read ssegs m A full (i + 1) b _ STR Hn ltac:(lia) eq_refl) as RD.
        replace (A + i + 1)%Z with (A + (i + 1))%Z by lia.
        do 4 zstep. if_cases K; zify_cond K. 2:{ exfalso. exact (Hb K). }
        replace (A + i + 1)%Z with (A + (i + 1))%Z by lia.
        apply (IH (i + 1)%Z); lia.
  Qed.
End Proofs.

Lemma strlen_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (str slack : list byte),
  bytes_at ssegs m (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack) ->
  ~ In (Z_to_bv 8 0) str ->
  ((- (bv_unsigned a0 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  mem_inv ssegs m ->
  evt ssegs (strlen_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 str slack m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x2100c) fc None m (seg_rom ssegs)).
Proof.
  intros until slack. intros STR NONUL PAD MI.
  pose proof (bytes_at_bound _ _ _ _ STR) as AB. rewrite length_app in AB. cbn [length] in AB.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl ssegs m) as WM.
  do 3 zstep. if_cases Kal; zify_cond Kal.
  - (* [comment removed for export] *)
    eapply evt_eq.
    2:{ eapply (strlen_wentry _ _ _ _ _ _ _ _ _ a0) with (j := 0%Z); try eassumption; try lia.
        revert Kal. zb_masks. intros Kal. rewrite Z.add_0_r. exact Kal. }
    unfold mkR. rewrite Z_to_bv_plus0. reflexivity.
  - destruct str as [|c str'] eqn:Es.
    + (* [comment removed for export] *)
      pose proof (u8ro_read ssegs m (bv_unsigned a0) _ 0 _ a0 STR eq_refl ltac:(lia) ltac:(symmetry; apply Z_to_bv_plus0)) as RD.
      do 2 zstep. if_true. do 2 zstep.
      replace (bv_unsigned a0 - bv_unsigned a0)%Z with 0%Z by lia. finish.
    + assert (Hc : bv_unsigned c <> 0%Z).
      { intros Hc. apply NONUL. left. apply bv_eq. rewrite Hc. reflexivity. }
      pose proof (u8ro_read ssegs m (bv_unsigned a0) _ 0 _ a0 STR eq_refl ltac:(lia) ltac:(symmetry; apply Z_to_bv_plus0)) as RD.
      do 2 zstep. if_cases K; zify_cond K. { exfalso. exact (Hc K). }
      do 2 zstep.
      eapply evt_eq.
      2:{ eapply (strlen_head _ _ _ _ _ _ _ _ _ a0) with (i := 0%Z) (k := length (c :: str')); try eassumption; cbn [length]; lia. }
      unfold mkR. rewrite Z.add_0_r, Z_to_bv_lit_self. reflexivity.
Qed.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan SecDiet.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
(* [comment removed for export] *)

Definition strlen_entry := 0x217cc%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition strlen_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 : word) (str slack : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat (length str))) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ bytes_at usegs m' (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack).

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (str slack : list byte).
  Hypothesis MI : mem_inv usegs m.
  Hypothesis STR : bytes_at usegs m (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack).
  Hypothesis NONUL : ~ In (Z_to_bv 8 0) str.
  Hypothesis PAD : ((- (bv_unsigned a0 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z.
  Let MU : munch [] m m := munch_refl [] m.
  Let WM : wmono usegs m m := wmono_refl usegs m.

  Notation A := (bv_unsigned a0).
  Notation len := (Z.of_nat (length str)).
  Notation full := (str ++ Z_to_bv 8 0 :: slack).
  Notation POST := (strlen_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 str slack m).
  (* [comment removed for export] *)
  Notation ST pc x11 x12 x13 x14 x15 x16 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 x11 x12 x13 x14 x15 x16 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom usegs)).
  Notation CMAGIC := 72340172838076672%Z.      (* [comment removed for export] *)
  Notation HIGHS := 9259542123273814144%Z.     (* [comment removed for export] *)

  Lemma full_length : length full = (length str + S (length slack))%nat.
  Proof using a0. pin_using (fun (a0 : unit) => tt). rewrite length_app. cbn. lia. Qed.

  Lemma A_bound : (0 <= A /\ A + len + 1 + Z.of_nat (length slack) <= 2^64)%Z.
  Proof using STR. pin_using (fun (STR : unit) => tt). pose proof (bytes_at_bound _ _ _ _ STR) as B. rewrite full_length in B. lia. Qed.

  Lemma full_nth_lt : forall i, (0 <= i < len)%Z ->
    exists b, nth_error full (Z.to_nat i) = Some b /\ bv_unsigned b <> 0%Z.
  Proof using NONUL a0. pin_using (fun (NONUL a0 : unit) => tt).
    intros i Hi. destruct (nth_error str (Z.to_nat i)) as [b|] eqn:E.
    - exists b. split. { rewrite nth_error_app1 by lia. exact E. }
      intros Hb. apply NONUL. replace (Z_to_bv 8 0) with b. { eapply nth_error_In; eauto. }
      apply bv_eq. rewrite Hb. reflexivity.
    - apply nth_error_None in E. lia.
  Qed.

  Lemma full_nth_len : nth_error full (Z.to_nat len) = Some (Z_to_bv 8 0).
  Proof using a0. pin_using (fun (a0 : unit) => tt). rewrite nth_error_app2, Nat2Z.id, Nat.sub_diag by lia. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma strlen_tail : forall (k : nat) (i : Z) (a3 a4 a5 a6 : word),
    (Z.to_nat (len - i) = k) -> (0 <= i <= len)%Z ->
    evt usegs POST (ST 0x2183c (Z_to_bv 64 (A + i - 1)) (Z_to_bv 64 (A + i)) a3 a4 a5 a6).
  Proof using MI NONUL STR. pin_using (fun (MI NONUL STR : unit) => tt).
    induction k as [|k IH]; intros i a3 a4 a5 a6 Hk Hi; pose proof A_bound as AB.
    - assert (Ei : i = len) by lia. subst i.
      pose proof (u8ro_read usegs m A full len _ _ STR full_nth_len ltac:(lia) eq_refl) as RD.
      do 4 zstep. if_false. zstep. zstep.
      replace (A + len - 1 + 1 - A)%Z with len by lia. finish.
    - destruct (full_nth_lt i ltac:(lia)) as (b & Hn & Hb).
      pose proof (u8ro_read usegs m A full i b _ STR Hn ltac:(lia) eq_refl) as RD.
      do 4 zstep. if_cases K; zify_cond K. 2:{ exfalso. exact (Hb K). }
      replace (A + i - 1 + 1)%Z with (A + (i + 1) - 1)%Z by lia.
      replace (A + i + 1)%Z with (A + (i + 1))%Z by lia.
      apply (IH (i + 1)%Z); lia.
  Qed.

  (* [comment removed for export] *)
  Lemma strlen_words : forall (k : nat) (j : Z) (a5 a6 : word),
    (Z.to_nat (len - j) = k) -> (0 <= j <= len)%Z -> ((A + j) mod 8 = 0)%Z ->
    evt usegs POST (ST 0x21820 (Z_to_bv 64 (A + j - 9)) (Z_to_bv 64 (A + j - 8)) (Z_to_bv 64 CMAGIC) (Z_to_bv 64 HIGHS) a5 a6).
  Proof using MI NONUL PAD STR. pin_using (fun (MI NONUL PAD STR : unit) => tt).
    induction k as [k IH] using lt_wf_ind; intros j a5 a6 Hk Hj Hal; pose proof A_bound as AB.
    assert (HW : (Z.to_nat j + 8 <= length full)%nat).
    { rewrite full_length. Z.div_mod_to_equations. lia. }
    pose proof (bytes_at_read usegs m A full j 8 STR ltac:(lia) HW) as RD.
    set (chunk := firstn 8 (skipn (Z.to_nat j) full)) in RD.
    assert (CL : length chunk = 8%nat). { subst chunk. rewrite firstn_length, skipn_length. lia. }
    pose proof (le_val_range _ (bytes_ok_map chunk)) as WR. rewrite length_map, CL in WR.
    change (256 ^ Z.of_nat 8)%Z with (2^64)%Z in WR.
    do 7 zstep.
    replace (A + j - 8 + 8)%Z with (A + j)%Z by lia.
    replace (A + j - 9 + 8)%Z with (A + j - 1)%Z by lia.
    rewrite (load8_le_val chunk CL).
    if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      apply (haszero64_clang _ (bytes_ok_map chunk) ltac:(rewrite length_map; exact CL)) in K.
      rewrite In0_map_unsigned in K.
      assert (Hj8 : (j + 8 <= len)%Z).
      { destruct (Z.lt_ge_cases len (j + 8)); [|assumption]. exfalso. apply K. subst chunk.
        apply nth_error_In with (n := (Z.to_nat len - Z.to_nat j)%nat).
        rewrite nth_error_firstn. replace (Nat.ltb _ _) with true by (symmetry; apply Nat.ltb_lt; lia).
        rewrite nth_error_skipn, <- full_nth_len. f_equal. lia. }
      replace (A + j - 1)%Z with (A + (j + 8) - 9)%Z by lia.
      replace (Z_to_bv 64 (A + j)) with (Z_to_bv 64 (A + (j + 8) - 8)) by (f_equal; lia).
      apply (IH (Z.to_nat (len - (j + 8)))); try lia. all: Z.div_mod_to_equations; lia.
    - (* [comment removed for export] *)
      apply (strlen_tail (Z.to_nat (len - j)) j); lia.
  Qed.

  (* [comment removed for export] *)
  Lemma strlen_wentry : forall (j : Z) (a1 a3 a4 a5 a6 : word),
    (0 <= j <= len)%Z -> ((A + j) mod 8 = 0)%Z ->
    evt usegs POST (ST 0x21808 a1 (Z_to_bv 64 (A + j)) a3 a4 a5 a6).
  Proof using MI NONUL PAD STR. pin_using (fun (MI NONUL PAD STR : unit) => tt).
    intros j a1 a3 a4 a5 a6 Hj Hal. pose proof A_bound as AB.
    do 6 zstep.
    replace (A + j + -9)%Z with (A + j - 9)%Z by lia.
    replace (A + j + -8)%Z with (A + j - 8)%Z by lia.
    apply (strlen_words (Z.to_nat (len - j)) j); lia.
  Qed.

  (* [comment removed for export] *)
  Lemma strlen_head : forall (k : nat) (i : Z) (a3 a4 a5 a6 : word),
    (Z.to_nat (len - i) = k) -> (0 <= i < len)%Z ->
    evt usegs POST (ST 0x217e8 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (A + i + 1)) a3 a4 a5 a6).
  Proof using MI NONUL PAD STR. pin_using (fun (MI NONUL PAD STR : unit) => tt).
    induction k as [|k IH]; intros i a3 a4 a5 a6 Hk Hi; pose proof A_bound as AB; [lia|].
    do 3 zstep. if_cases Kal; zify_cond Kal.
    - replace (A + i + 1)%Z with (A + (i + 1))%Z by lia.
      apply strlen_wentry; [lia|]. revert Kal. zb_masks. intros Kal. Z.div_mod_to_equations; lia.
    - destruct (Z.eq_dec (i + 1) len) as [E|NE].
      + pose proof (u8ro_read usegs m A full len _ _ STR full_nth_len ltac:(lia) eq_refl) as RD.
        do 4 zstep. if_false. do 3 zstep.
        replace (A + i + 1 - A)%Z with len by lia. finish.
      + destruct (full_nth_lt (i + 1) ltac:(lia)) as (b & Hn & Hb).
        pose proof (u8ro_read usegs m A full (i + 1) b _ STR Hn ltac:(lia) eq_refl) as RD.
        replace (A + i + 1)%Z with (A + (i + 1))%Z by lia.
        do 4 zstep. if_cases K; zify_cond K. 2:{ exfalso. exact (Hb K). }
        replace (A + i + 1)%Z with (A + (i + 1))%Z by lia.
        apply (IH (i + 1)%Z); lia.
  Qed.
End Proofs.

Definition strlen_spec__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (str slack : list byte),
  bytes_at usegs m (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack) ->
  ~ In (Z_to_bv 8 0) str ->
  ((- (bv_unsigned a0 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  mem_inv usegs m ->
  evt usegs (strlen_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 str slack m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x217cc) fc None m (seg_rom usegs)).
Section Sz9.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m str slack : ltac2:(SecDiet.SzSec.tyM 'strlen_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
#[using="Type"] Lemma strlen_spec__body : ltac2:(SecDiet.SzSec.bodyP 'strlen_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
 intros STR NONUL PAD MI.
  pose proof (bytes_at_bound _ _ _ _ STR) as AB. rewrite length_app in AB. cbn [length] in AB.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl usegs m) as WM.
  do 3 zstep. if_cases Kal; zify_cond Kal.
  - (* [comment removed for export] *)
    eapply evt_eq.
    2:{ eapply (strlen_wentry _ _ _ _ _ _ _ _ _ a0) with (j := 0%Z); try eassumption; try lia.
        revert Kal. zb_masks. intros Kal. rewrite Z.add_0_r. exact Kal. }
    unfold mkR. rewrite Z_to_bv_plus0. reflexivity.
  - destruct str as [|c str'] eqn:Es.
    + (* [comment removed for export] *)
      pose proof (u8ro_read usegs m (bv_unsigned a0) _ 0 _ a0 STR eq_refl ltac:(lia) ltac:(symmetry; apply Z_to_bv_plus0)) as RD.
      do 2 zstep. if_true. do 2 zstep.
      replace (bv_unsigned a0 - bv_unsigned a0)%Z with 0%Z by lia. finish.
    + assert (Hc : bv_unsigned c <> 0%Z).
      { intros Hc. apply NONUL. left. apply bv_eq. rewrite Hc. reflexivity. }
      pose proof (u8ro_read usegs m (bv_unsigned a0) _ 0 _ a0 STR eq_refl ltac:(lia) ltac:(symmetry; apply Z_to_bv_plus0)) as RD.
      do 2 zstep. if_cases K; zify_cond K. { exfalso. exact (Hc K). }
      do 2 zstep.
      eapply evt_eq.
      2:{ eapply (strlen_head _ _ _ _ _ _ _ _ _ a0) with (i := 0%Z) (k := length (c :: str')); try eassumption; cbn [length]; lia. }
      unfold mkR. rewrite Z.add_0_r, Z_to_bv_lit_self. reflexivity.
Qed.
End Sz9.
Lemma strlen_spec : ltac:(let t := eval cbv delta [strlen_spec__stmt] in strlen_spec__stmt in exact t).
Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m str slack. ltac2:(SecDiet.SzSec.closeP 'strlen_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End TwB.
End F_strlen.

(* [comment removed for export] *)
Module F_strnlen.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.F_memchr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.

Definition strnlen_entry := 0x2109c%Z.

(* [comment removed for export] *)
Definition strnlen_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 : word) (buf : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
                 (Z_to_bv 64 (strnlen_res (bv_unsigned a1) buf))
                 a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ssegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
    /\ stk ssegs m' lo (bv_unsigned sp)
    /\ bytes_at ssegs m' (bv_unsigned a0) buf.

Definition strnlen_spec__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (buf : list byte) (lo : Z),
  stk ssegs m lo (bv_unsigned sp) ->
  bytes_at ssegs m (bv_unsigned a0) buf ->
  memchr_ok (bv_unsigned a0) 0 (bv_unsigned a1) buf ->
  mem_inv ssegs m ->
  (lo <= bv_unsigned sp - 32)%Z ->
  (bv_unsigned a0 + Z.of_nat (length buf) <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  (0 < bv_unsigned a0)%Z ->
  evt ssegs (strnlen_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 buf lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x2109c) fc None m (seg_rom ssegs)).
Section Sz1.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m buf lo : ltac2:(SecDiet.SzSec.tyM 'strnlen_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
#[using="Type"] Lemma strnlen_spec__body : ltac2:(SecDiet.SzSec.bodyP 'strnlen_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
 intros ST BUF OK MI LO SEP A0.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ssegs m) as WM.
  pose proof (bytes_at_bound _ _ _ _ BUF) as AB.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  carve_frame 32%nat ST.
  do 9 zstep.
  call memchr_spec.
  1:{ exact BUF. }
  1:{ rewrite unsigned_lit by lia. exact OK. }
  1:{ assumption. }
  rewrite unsigned_lit by lia. change (0 mod 256)%Z with 0%Z.
  unfold memchr_res.
  destruct (find_byte 0 (firstn (Z.to_nat (bv_unsigned a1)) buf)) as [i|] eqn:FB.
  - pose proof (find_byte_Some _ _ _ FB) as (Hl & _). rewrite firstn_length in Hl.
    zstep. if_cases K; zify_cond K. { exfalso. lia. }
    do 7 zstep.
    replace (bv_unsigned a0 + Z.of_nat i - bv_unsigned a0)%Z with (strnlen_res (bv_unsigned a1) buf)
      by (unfold strnlen_res; rewrite FB; lia).
    release_frame FR ST (bv_unsigned sp). finish.
  - zstep. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
    do 6 zstep.
    lazymatch goal with |- evt _ ?Q _ => set (P := Q) end.
    replace a1 with (Z_to_bv 64 (strnlen_res (bv_unsigned a1) buf))
      by (unfold strnlen_res; rewrite FB; apply Z_to_bv_bv_unsigned).
    release_frame FR ST (bv_unsigned sp). finish.
Qed.
End Sz1.
Lemma strnlen_spec : ltac:(let t := eval cbv delta [strnlen_spec__stmt] in strnlen_spec__stmt in exact t).
Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m buf lo. ltac2:(SecDiet.SzSec.closeP 'strnlen_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.F_memchr.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.

Definition strnlen_entry := 0x2185c%Z.

(* [comment removed for export] *)
Definition strnlen_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 : word) (buf : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
                 (Z_to_bv 64 (strnlen_res (bv_unsigned a1) buf))
                 a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ bytes_at usegs m' (bv_unsigned a0) buf.

Definition strnlen_spec__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (buf : list byte) (lo : Z),
  stk usegs m lo (bv_unsigned sp) ->
  bytes_at usegs m (bv_unsigned a0) buf ->
  memchr_ok (bv_unsigned a0) 0 (bv_unsigned a1) buf ->
  mem_inv usegs m ->
  (lo <= bv_unsigned sp - 32)%Z ->
  (bv_unsigned a0 + Z.of_nat (length buf) <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  (0 < bv_unsigned a0)%Z ->
  evt usegs (strnlen_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 buf lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x2185c) fc None m (seg_rom usegs)).
Section Sz1.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m buf lo : ltac2:(SecDiet.SzSec.tyM 'strnlen_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
#[using="Type"] Lemma strnlen_spec__body : ltac2:(SecDiet.SzSec.bodyP 'strnlen_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
 intros ST BUF OK MI LO SEP A0.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bytes_at_bound _ _ _ _ BUF) as AB.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  carve_frame 32%nat ST.
  do 9 zstep.
  call memchr_spec.
  1:{ exact BUF. }
  1:{ rewrite unsigned_lit by lia. exact OK. }
  1:{ assumption. }
  rewrite unsigned_lit by lia. change (0 mod 256)%Z with 0%Z.
  unfold memchr_res.
  destruct (find_byte 0 (firstn (Z.to_nat (bv_unsigned a1)) buf)) as [i|] eqn:FB.
  - pose proof (find_byte_Some _ _ _ FB) as (Hl & _). rewrite firstn_length in Hl.
    zstep. if_cases K; zify_cond K. { exfalso. lia. }
    do 7 zstep.
    replace (bv_unsigned a0 + Z.of_nat i - bv_unsigned a0)%Z with (strnlen_res (bv_unsigned a1) buf)
      by (unfold strnlen_res; rewrite FB; lia).
    release_frame FR ST (bv_unsigned sp). finish.
  - zstep. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
    do 6 zstep.
    lazymatch goal with |- evt _ ?Q _ => set (P := Q) end.
    replace a1 with (Z_to_bv 64 (strnlen_res (bv_unsigned a1) buf))
      by (unfold strnlen_res; rewrite FB; apply Z_to_bv_bv_unsigned).
    release_frame FR ST (bv_unsigned sp). finish.
Qed.
End Sz1.
Lemma strnlen_spec : ltac:(let t := eval cbv delta [strnlen_spec__stmt] in strnlen_spec__stmt in exact t).
Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m buf lo. ltac2:(SecDiet.SzSec.closeP 'strnlen_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End TwB.
End F_strnlen.

(* [comment removed for export] *)
Module F_strrchr.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Bytes ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.F_strlen.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition memrchr_entry := 0x2111c%Z.
Definition strrchr_entry := 0x210e0%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition memrchr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 : word) (buf : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
                 (Z_to_bv 64 (memrchr_res (bv_unsigned a0) (bv_unsigned a1 mod 256) buf))
                 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom ssegs)
    /\ munch [] m m /\ wmono ssegs m m /\ mem_inv ssegs m
    /\ bytes_at ssegs m (bv_unsigned a0) buf.

Section MemrchrProof.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (buf : list byte).
  Hypothesis MI : mem_inv ssegs m.
  Hypothesis BUF : bytes_at ssegs m (bv_unsigned a0) buf.
  Hypothesis LEN : length buf = Z.to_nat (bv_unsigned a2).
  Let MU : munch [] m m := munch_refl [] m.
  Let WM : wmono ssegs m m := wmono_refl ssegs m.

  Notation A := (bv_unsigned a0).
  Notation n := (bv_unsigned a2).
  Notation c := ((bv_unsigned a1) mod 256)%Z.
  Notation POST := (memrchr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 buf m).
  (* [comment removed for export] *)
  Notation ST pc x10 x12 x13 x14 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 (Z_to_bv 64 c) x12 x13 x14 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom ssegs)).

  (* [comment removed for export] *)
  Definition NOA (k : Z) : Prop :=
    forall j b, (Z.to_nat k <= j)%nat -> nth_error buf j = Some b -> bv_unsigned b <> c.

  Lemma A_bound : (0 <= A /\ A + n <= 2^64 /\ 0 <= n < 2^64 /\ 0 <= c < 256)%Z.
  Proof using BUF LEN. pin_using (fun (BUF LEN : unit) => tt).
    pose proof (bytes_at_bound _ _ _ _ BUF). rewrite LEN in H.
    pose proof (bv_unsigned_in_range 64 a2) as R. unfold bv_modulus in R. cbn in R.
    pose proof (Z.mod_pos_bound (bv_unsigned a1) 256). cbn. lia.
  Qed.

  Lemma res_found : forall k b, (1 <= k <= n)%Z -> NOA k -> nth_error buf (Z.to_nat (k - 1)) = Some b -> bv_unsigned b = c ->
    memrchr_res A c buf = (A + (k - 1))%Z.
  Proof using LEN. pin_using (fun (LEN : unit) => tt).
    intros k b Hk HN Hn Hb. unfold memrchr_res.
    rewrite (last_byte_charact c buf (Z.to_nat (k - 1)) b Hn Hb). { f_equal. lia. }
    intros j b' Hj Hn'. eapply HN; [|exact Hn']. lia.
  Qed.

  Lemma res_none : NOA 0 -> memrchr_res A c buf = 0%Z.
  Proof using LEN. pin_using (fun (LEN : unit) => tt).
    intros HN. unfold memrchr_res. rewrite last_byte_None_intro; [reflexivity|].
    intros j b Hn. eapply HN; [|exact Hn]. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma memrchr_loop : forall (kn : nat) (k : Z) (x10 x14 : word),
    Z.to_nat k = kn -> (0 <= k <= n)%Z -> NOA k ->
    evt ssegs POST (ST 0x21128 x10 (Z_to_bv 64 (A + k)) (Z_to_bv 64 (- k)) x14).
  Proof using BUF LEN MI. pin_using (fun (BUF LEN MI : unit) => tt).
    induction kn as [|kn IH]; intros k x10 x14 Hk Hkn HN; pose proof A_bound as AB.
    - zstep. if_cases K; zify_cond K. 2:{ exfalso. lia. }
      zstep. zstep. rewrite <- res_none at 1. { finish. } replace 0%Z with k by lia. exact HN.
    - zstep. if_cases K; zify_cond K.
      { exfalso. replace (-k)%Z with ((2^64 - k) + (-1) * 2^64)%Z in K by lia.
        rewrite Z.mod_add in K by lia. rewrite Z.mod_small in K by lia. lia. }
      destruct (nth_error buf (Z.to_nat (k - 1))) as [b|] eqn:Hn.
      2:{ exfalso. apply nth_error_None in Hn. lia. }
      pose proof (u8ro_read ssegs m A buf (k - 1) b (wa (A + k + -1)) BUF Hn ltac:(lia) ltac:(f_equal; lia)) as RD.
      zstep. zstep. zstep. zstep. zstep. if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        replace (A + k + -1)%Z with (A + (k - 1))%Z by lia. replace (- k + 1)%Z with (- (k - 1))%Z by lia.
        apply (IH (k - 1)%Z); [lia|lia|].
        intros j b' Hj Hn'. destruct (Nat.eq_dec j (Z.to_nat (k - 1))) as [->|NE].
        { rewrite Hn in Hn'. injection Hn' as <-. exact K2. }
        eapply HN; [|exact Hn']. lia.
      + (* [comment removed for export] *)
        zstep. replace (A + k + -1)%Z with (A + (k - 1))%Z by lia. rewrite <- (res_found k b ltac:(lia) HN Hn K2). finish.
  Qed.
End MemrchrProof.

Definition memrchr_spec__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (buf : list byte),
  bytes_at ssegs m (bv_unsigned a0) buf ->
  length buf = Z.to_nat (bv_unsigned a2) ->
  mem_inv ssegs m ->
  evt ssegs (memrchr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 buf m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x2111c) fc None m (seg_rom ssegs)).
Section Sz5.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m buf : ltac2:(SecDiet.SzSec.tyM 'memrchr_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
#[using="Type"] Lemma memrchr_spec__body : ltac2:(SecDiet.SzSec.bodyP 'memrchr_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
  intros BUF LEN MI.
  pose proof (bytes_at_bound _ _ _ _ BUF) as AB. rewrite LEN in AB.
  pose proof (bv_unsigned_in_range 64 a2) as R2. unfold bv_modulus in R2. cbn in R2.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl ssegs m) as WM.
  zstep. rewrite (Z.land_ones _ 8) by lia. change (Z.ones 8) with 255%Z. rewrite <- (Z.land_ones (bv_unsigned a1) 8) by lia.
  change (Z.land (bv_unsigned a1) (Z.ones 8)) with (Z.land (bv_unsigned a1) 255).
  replace (Z.land (bv_unsigned a1) 255) with ((bv_unsigned a1) mod 256)%Z.
  2:{ change 255%Z with (Z.ones 8). rewrite Z.land_ones by (pose proof (bv_unsigned_in_range 64 a1); lia). reflexivity. }
  zstep. zstep.
  replace (0 - bv_unsigned a2)%Z with (- bv_unsigned a2)%Z by lia.
  eapply (memrchr_loop ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m buf
            MI BUF LEN (Z.to_nat (bv_unsigned a2)) (bv_unsigned a2)); [reflexivity|lia|].
  intros j b Hj Hn. exfalso. apply nth_error_lt in Hn. lia.
Qed.
End Sz5.
Lemma memrchr_spec : ltac:(let t := eval cbv delta [memrchr_spec__stmt] in memrchr_spec__stmt in exact t).
Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m buf. ltac2:(SecDiet.SzSec.closeP 'memrchr_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition strrchr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 : word) (str slack : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
                 (Z_to_bv 64 (strrchr_res (bv_unsigned a0) (bv_unsigned a1 mod 256) str))
                 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ssegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
    /\ stk ssegs m' lo (bv_unsigned sp)
    /\ bytes_at ssegs m' (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack).

Definition strrchr_spec__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (str slack : list byte) (lo : Z),
  stk ssegs m lo (bv_unsigned sp) ->
  bytes_at ssegs m (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack) ->
  ~ In (Z_to_bv 8 0) str ->
  ((- (bv_unsigned a0 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  mem_inv ssegs m ->
  (lo <= bv_unsigned sp - 32)%Z ->
  (bv_unsigned a0 + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  evt ssegs (strrchr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 str slack lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x210e0) fc None m (seg_rom ssegs)).
Section Sz6.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m str slack lo : ltac2:(SecDiet.SzSec.tyM 'strrchr_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
#[using="Type"] Lemma strrchr_spec__body : ltac2:(SecDiet.SzSec.bodyP 'strrchr_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
  intros ST STR NONUL PAD MI LO SEP.
  pose proof (bytes_at_bound _ _ _ _ STR) as AB. rewrite length_app in AB. cbn [length] in AB.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ssegs m) as WM.
  pose proof (proj1 ST) as LO0. cbn beta in LO0. pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. cbn in Rsp.
  carve_frame 32%nat ST.
  do 6 step.
  step. call strlen_spec. 1:{ exact STR. } 1:{ exact NONUL. } 1:{ exact PAD. } 1:{ exact MI. }
  do 3 zstep.
  do 4 step. release_frame FR ST (bv_unsigned sp).
  step.
  (* [comment removed for export] *)
  pose proof POST as P2.
  replace (str ++ Z_to_bv 8 0 :: slack) with ((str ++ [Z_to_bv 8 0]) ++ slack) in P2 by (rewrite <- app_assoc; reflexivity).
  apply (proj1 (bytes_at_app _ _ _ _ _)) in P2. destruct P2 as [STR0 _].
  eapply evt_mono. { eapply memrchr_spec; [exact STR0 | | exact MI0].
    rewrite length_app. cbn [length]. rewrite unsigned_lit by lia. lia. }
  intros ms' H. unfold memrchr_post in H. unfold strrchr_post, strrchr_res. destruct_exs H.
  destruct H as (-> & _ & _ & _ & _).
  do 15 eexists. split; [reflexivity|]. repeat (split; [assumption|]). exact POST.
Qed.
End Sz6.
Lemma strrchr_spec : ltac:(let t := eval cbv delta [strrchr_spec__stmt] in strrchr_spec__stmt in exact t).
Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m str slack lo. ltac2:(SecDiet.SzSec.closeP 'strrchr_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.F_strlen.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition memrchr_entry := 0x218dc%Z.
Definition strrchr_entry := 0x218a0%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition memrchr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 : word) (buf : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
                 (Z_to_bv 64 (memrchr_res (bv_unsigned a0) (bv_unsigned a1 mod 256) buf))
                 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom usegs)
    /\ munch [] m m /\ wmono usegs m m /\ mem_inv usegs m
    /\ bytes_at usegs m (bv_unsigned a0) buf.

Section MemrchrProof.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (buf : list byte).
  Hypothesis MI : mem_inv usegs m.
  Hypothesis BUF : bytes_at usegs m (bv_unsigned a0) buf.
  Hypothesis LEN : length buf = Z.to_nat (bv_unsigned a2).
  Let MU : munch [] m m := munch_refl [] m.
  Let WM : wmono usegs m m := wmono_refl usegs m.

  Notation A := (bv_unsigned a0).
  Notation n := (bv_unsigned a2).
  Notation c := ((bv_unsigned a1) mod 256)%Z.
  Notation POST := (memrchr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 buf m).
  (* [comment removed for export] *)
  Notation ST pc x10 x12 x13 x14 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 (Z_to_bv 64 c) x12 x13 x14 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition NOA (k : Z) : Prop :=
    forall j b, (Z.to_nat k <= j)%nat -> nth_error buf j = Some b -> bv_unsigned b <> c.

  Lemma A_bound : (0 <= A /\ A + n <= 2^64 /\ 0 <= n < 2^64 /\ 0 <= c < 256)%Z.
  Proof using BUF LEN. pin_using (fun (BUF LEN : unit) => tt).
    pose proof (bytes_at_bound _ _ _ _ BUF). rewrite LEN in H.
    pose proof (bv_unsigned_in_range 64 a2) as R. unfold bv_modulus in R. cbn in R.
    pose proof (Z.mod_pos_bound (bv_unsigned a1) 256). cbn. lia.
  Qed.

  Lemma res_found : forall k b, (1 <= k <= n)%Z -> NOA k -> nth_error buf (Z.to_nat (k - 1)) = Some b -> bv_unsigned b = c ->
    memrchr_res A c buf = (A + (k - 1))%Z.
  Proof using LEN. pin_using (fun (LEN : unit) => tt).
    intros k b Hk HN Hn Hb. unfold memrchr_res.
    rewrite (last_byte_charact c buf (Z.to_nat (k - 1)) b Hn Hb). { f_equal. lia. }
    intros j b' Hj Hn'. eapply HN; [|exact Hn']. lia.
  Qed.

  Lemma res_none : NOA 0 -> memrchr_res A c buf = 0%Z.
  Proof using LEN. pin_using (fun (LEN : unit) => tt).
    intros HN. unfold memrchr_res. rewrite last_byte_None_intro; [reflexivity|].
    intros j b Hn. eapply HN; [|exact Hn]. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma memrchr_loop : forall (kn : nat) (k : Z) (x10 x14 : word),
    Z.to_nat k = kn -> (0 <= k <= n)%Z -> NOA k ->
    evt usegs POST (ST 0x218e8 x10 (Z_to_bv 64 (A + k)) (Z_to_bv 64 (- k)) x14).
  Proof using BUF LEN MI. pin_using (fun (BUF LEN MI : unit) => tt).
    induction kn as [|kn IH]; intros k x10 x14 Hk Hkn HN; pose proof A_bound as AB.
    - zstep. if_cases K; zify_cond K. 2:{ exfalso. lia. }
      zstep. zstep. rewrite <- res_none at 1. { finish. } replace 0%Z with k by lia. exact HN.
    - zstep. if_cases K; zify_cond K.
      { exfalso. replace (-k)%Z with ((2^64 - k) + (-1) * 2^64)%Z in K by lia.
        rewrite Z.mod_add in K by lia. rewrite Z.mod_small in K by lia. lia. }
      destruct (nth_error buf (Z.to_nat (k - 1))) as [b|] eqn:Hn.
      2:{ exfalso. apply nth_error_None in Hn. lia. }
      pose proof (u8ro_read usegs m A buf (k - 1) b (wa (A + k + -1)) BUF Hn ltac:(lia) ltac:(f_equal; lia)) as RD.
      zstep. zstep. zstep. zstep. zstep. if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        replace (A + k + -1)%Z with (A + (k - 1))%Z by lia. replace (- k + 1)%Z with (- (k - 1))%Z by lia.
        apply (IH (k - 1)%Z); [lia|lia|].
        intros j b' Hj Hn'. destruct (Nat.eq_dec j (Z.to_nat (k - 1))) as [->|NE].
        { rewrite Hn in Hn'. injection Hn' as <-. exact K2. }
        eapply HN; [|exact Hn']. lia.
      + (* [comment removed for export] *)
        zstep. replace (A + k + -1)%Z with (A + (k - 1))%Z by lia. rewrite <- (res_found k b ltac:(lia) HN Hn K2). finish.
  Qed.
End MemrchrProof.

Definition memrchr_spec__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (buf : list byte),
  bytes_at usegs m (bv_unsigned a0) buf ->
  length buf = Z.to_nat (bv_unsigned a2) ->
  mem_inv usegs m ->
  evt usegs (memrchr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 buf m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x218dc) fc None m (seg_rom usegs)).
Section Sz5.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m buf : ltac2:(SecDiet.SzSec.tyM 'memrchr_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
#[using="Type"] Lemma memrchr_spec__body : ltac2:(SecDiet.SzSec.bodyP 'memrchr_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
 intros BUF LEN MI.
  pose proof (bytes_at_bound _ _ _ _ BUF) as AB. rewrite LEN in AB.
  pose proof (bv_unsigned_in_range 64 a2) as R2. unfold bv_modulus in R2. cbn in R2.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl usegs m) as WM.
  zstep. rewrite (Z.land_ones _ 8) by lia. change (Z.ones 8) with 255%Z. rewrite <- (Z.land_ones (bv_unsigned a1) 8) by lia.
  change (Z.land (bv_unsigned a1) (Z.ones 8)) with (Z.land (bv_unsigned a1) 255).
  replace (Z.land (bv_unsigned a1) 255) with ((bv_unsigned a1) mod 256)%Z.
  2:{ change 255%Z with (Z.ones 8). rewrite Z.land_ones by (pose proof (bv_unsigned_in_range 64 a1); lia). reflexivity. }
  zstep. zstep.
  replace (0 - bv_unsigned a2)%Z with (- bv_unsigned a2)%Z by lia.
  eapply (memrchr_loop ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m buf
            MI BUF LEN (Z.to_nat (bv_unsigned a2)) (bv_unsigned a2)); [reflexivity|lia|].
  intros j b Hj Hn. exfalso. apply nth_error_lt in Hn. lia.
Qed.
End Sz5.
Lemma memrchr_spec : ltac:(let t := eval cbv delta [memrchr_spec__stmt] in memrchr_spec__stmt in exact t).
Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m buf. ltac2:(SecDiet.SzSec.closeP 'memrchr_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition strrchr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 : word) (str slack : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
                 (Z_to_bv 64 (strrchr_res (bv_unsigned a0) (bv_unsigned a1 mod 256) str))
                 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ bytes_at usegs m' (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack).

Definition strrchr_spec__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (str slack : list byte) (lo : Z),
  stk usegs m lo (bv_unsigned sp) ->
  bytes_at usegs m (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack) ->
  ~ In (Z_to_bv 8 0) str ->
  ((- (bv_unsigned a0 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  mem_inv usegs m ->
  (lo <= bv_unsigned sp - 32)%Z ->
  (bv_unsigned a0 + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  evt usegs (strrchr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 str slack lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x218a0) fc None m (seg_rom usegs)).
Section Sz6.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m str slack lo : ltac2:(SecDiet.SzSec.tyM 'strrchr_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
#[using="Type"] Lemma strrchr_spec__body : ltac2:(SecDiet.SzSec.bodyP 'strrchr_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
 intros ST STR NONUL PAD MI LO SEP.
  pose proof (bytes_at_bound _ _ _ _ STR) as AB. rewrite length_app in AB. cbn [length] in AB.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (proj1 ST) as LO0. cbn beta in LO0. pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. cbn in Rsp.
  carve_frame 32%nat ST.
  do 6 step.
  step. call strlen_spec. 1:{ exact STR. } 1:{ exact NONUL. } 1:{ exact PAD. } 1:{ exact MI. }
  do 3 zstep.
  do 4 step. release_frame FR ST (bv_unsigned sp).
  step.
  (* [comment removed for export] *)
  pose proof POST as P2.
  replace (str ++ Z_to_bv 8 0 :: slack) with ((str ++ [Z_to_bv 8 0]) ++ slack) in P2 by (rewrite <- app_assoc; reflexivity).
  apply (proj1 (bytes_at_app _ _ _ _ _)) in P2. destruct P2 as [STR0 _].
  eapply evt_mono. { eapply memrchr_spec; [exact STR0 | | exact MI0].
    rewrite length_app. cbn [length]. rewrite unsigned_lit by lia. lia. }
  intros ms' H. unfold memrchr_post in H. unfold strrchr_post, strrchr_res. destruct_exs H.
  destruct H as (-> & _ & _ & _ & _).
  do 15 eexists. split; [reflexivity|]. repeat (split; [assumption|]). exact POST.
Qed.
End Sz6.
Lemma strrchr_spec : ltac:(let t := eval cbv delta [strrchr_spec__stmt] in strrchr_spec__stmt in exact t).
Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m str slack lo. ltac2:(SecDiet.SzSec.closeP 'strrchr_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End TwB.
End F_strrchr.

(* [comment removed for export] *)
Module F_pop_arg.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.F_memset.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.

Definition pop_arg_entry := 0x1cb8c%Z.
Definition T_PTR := 9%Z. Definition T_INT := 10%Z. Definition T_UINT := 11%Z. Definition T_SIZET := 20%Z.

(* [comment removed for export] *)
Definition va_area (m : word -> option byte) (VA : Z) (slots : list word) : Prop :=
  bytes_at ssegs m VA (u64s slots).

(* [comment removed for export] *)
Definition pop_arg_lo (ty : Z) (slot : word) : word :=
  if (ty =? T_INT)%Z then sx32 slot
  else if (ty =? T_UINT)%Z then zx32 slot
  else slot.                                   (* [comment removed for export] *)
Definition pop_arg_hi (ty : Z) (slot y : word) : word := y.

Definition pop_arg_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (ARG AP VA : Z) (slots : list word) (i ty : Z) (slot y : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Ft m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             Ft (ret_pc ra) fc None m' (seg_rom ssegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (AP, AP + 8); (ARG, ARG + 16)]%Z m m'
    /\ wmono ssegs m m' /\ mem_inv ssegs m'
    /\ stk ssegs m' (bv_unsigned sp - 16) (bv_unsigned sp)
    /\ rw_cells ssegs m' AP [C8 (Z_to_bv 64 (VA + 8 * (i + 1)))]
    /\ rw_cells ssegs m' ARG [C8 (pop_arg_lo ty slot); C8 (pop_arg_hi ty slot y)]
    /\ va_area m' VA slots
    /\ Ft = F.   (* [comment removed for export] *)

Lemma firstn4_le8 : forall w : word, firstn 4 (le8 w) = le4 w.
Proof. intros w. reflexivity. Qed.

Definition va_read8__stmt : Prop := forall m VA slots (i : Z) w a,
  bytes_at ssegs m VA (u64s slots) -> nth_error slots (Z.to_nat i) = Some w -> (0 <= i)%Z -> a = wa (VA + 8 * i) ->
  ov_read_bytes ssegs m a 8 = Some (le8 w).
Section Sz2.
Variables m VA slots i w a : ltac2:(SecDiet.SzSec.tyM 'va_read8__stmt "vvvvvv" @m).
#[using="Type"] Lemma va_read8__body : ltac2:(SecDiet.SzSec.bodyP 'va_read8__stmt "vvvvvv").
Proof.
  intros Hb Hn Hi ->.
  destruct (u64s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
  replace (8 * i)%Z with (Z.of_nat (8 * Z.to_nat i))%Z by lia.
  rewrite (bytes_at_ov_read ssegs m VA (u64s slots) (8 * Z.to_nat i) 8 Hb).
  2:{ rewrite Eu, !length_app, length_le8, Hlu. lia. }
  rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
  rewrite firstn_app, firstn_all2 by (rewrite length_le8; lia).
  rewrite length_le8, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.
End Sz2.
Lemma va_read8 : ltac:(let t := eval cbv delta [va_read8__stmt] in va_read8__stmt in exact t).
Proof. intros m VA slots i w a. ltac2:(SecDiet.SzSec.closeP 'va_read8__body "vvvvvv"). Qed.

Definition va_read4__stmt : Prop := forall m VA slots (i : Z) w a,
  bytes_at ssegs m VA (u64s slots) -> nth_error slots (Z.to_nat i) = Some w -> (0 <= i)%Z -> a = wa (VA + 8 * i) ->
  ov_read_bytes ssegs m a 4 = Some (le4 w).
Section Sz3.
Variables m VA slots i w a : ltac2:(SecDiet.SzSec.tyM 'va_read4__stmt "vvvvvv" @m).
#[using="Type"] Lemma va_read4__body : ltac2:(SecDiet.SzSec.bodyP 'va_read4__stmt "vvvvvv").
Proof.
  intros Hb Hn Hi ->.
  destruct (u64s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
  replace (8 * i)%Z with (Z.of_nat (8 * Z.to_nat i))%Z by lia.
  rewrite (bytes_at_ov_read ssegs m VA (u64s slots) (8 * Z.to_nat i) 4 Hb).
  2:{ rewrite Eu, !length_app, length_le8, Hlu. lia. }
  rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
  rewrite firstn_app. rewrite length_le8. change (4 - 8)%nat with 0%nat. rewrite firstn_O, app_nil_r.
  rewrite firstn4_le8. reflexivity.
Qed.
End Sz3.
Lemma va_read4 : ltac:(let t := eval cbv delta [va_read4__stmt] in va_read4__stmt in exact t).
Proof. intros m VA slots i w a. ltac2:(SecDiet.SzSec.closeP 'va_read4__body "vvvvvv"). Qed.

Lemma va_area_bound : forall m VA slots, va_area m VA slots -> (0 <= VA /\ VA + 8 * Z.of_nat (length slots) <= 2^64)%Z.
Proof. intros m VA slots H. pose proof (bytes_at_bound _ _ _ _ H) as B. rewrite u64s_length in B. lia. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac if_lit :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let v := eval vm_compute in c in change c with v; cbv iota
  end.

Definition pop_arg_spec__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte)
    (VA : Z) (slots : list word) (i ty : Z) (slot x y : word),
  rw_cells ssegs m (bv_unsigned a2) [C8 (Z_to_bv 64 (VA + 8 * i))] ->
  va_area m VA slots -> nth_error slots (Z.to_nat i) = Some slot -> (0 <= i)%Z ->
  rw_cells ssegs m (bv_unsigned a0) [C8 x; C8 y] ->
  stk ssegs m (bv_unsigned sp - 16) (bv_unsigned sp) ->
  mem_inv ssegs m ->
  a1 = Z_to_bv 64 ty -> (ty = T_PTR \/ ty = T_INT \/ ty = T_UINT \/ ty = T_SIZET) ->
  (16 <= bv_unsigned sp)%Z ->
  (bv_unsigned sp <= bv_unsigned a2)%Z -> (bv_unsigned sp <= bv_unsigned a0)%Z ->
  (bv_unsigned a2 + 8 <= bv_unsigned a0 \/ bv_unsigned a0 + 16 <= bv_unsigned a2)%Z ->
  (VA + 8 * Z.of_nat (length slots) <= bv_unsigned sp - 16 \/ bv_unsigned sp <= VA)%Z ->
  (VA + 8 * Z.of_nat (length slots) <= bv_unsigned a2 \/ bv_unsigned a2 + 8 <= VA)%Z ->
  (VA + 8 * Z.of_nat (length slots) <= bv_unsigned a0 \/ bv_unsigned a0 + 16 <= VA)%Z ->
  evt ssegs (pop_arg_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               (bv_unsigned a0) (bv_unsigned a2) VA slots i ty slot y m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1cb8c) fc None m (seg_rom ssegs)).
Section Sz5.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m VA slots i ty slot x y : ltac2:(SecDiet.SzSec.tyM 'pop_arg_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
#[using="Type"] Lemma pop_arg_spec__body : ltac2:(SecDiet.SzSec.bodyP 'pop_arg_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
  intros APC VAA NTH Hi ARGC ST MI -> TY SPLO A2 A0 SEP1 SEP2 SEP3 SEP4.
  pose_word_ranges.
  pose proof (va_area_bound _ _ _ VAA) as VB. unfold va_area in VAA.
  assert (IL : (Z.to_nat i < length slots)%nat) by (apply nth_error_Some; rewrite NTH; discriminate).
  set (AP := bv_unsigned a2) in *. replace a2 with (Z_to_bv 64 AP) by (unfold AP; rewrite Z_to_bv_bv_unsigned; reflexivity).
  set (ARG := bv_unsigned a0) in *. replace a0 with (Z_to_bv 64 ARG) by (unfold ARG; rewrite Z_to_bv_bv_unsigned; reflexivity).
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (AP, AP + 8); (ARG, ARG + 16)]%Z m) as MU.
  pose proof (wmono_refl ssegs m) as WM.
  destruct TY as [-> | [-> | [-> | ->]]]; unfold T_PTR, T_INT, T_UINT, T_SIZET, pop_arg_lo, pop_arg_hi; cbn [Z.eqb Pos.eqb].
  - (* [comment removed for export] *)
    zstep. zstep. zstep. if_lit. do 7 zstep.
    zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (va_read8 mc VA slots i slot _ VAA NTH Hi eq_refl) as RD end.
    zstep. clear RD. zstep. zstep.
    replace (VA + 8 * i + 8)%Z with (VA + 8 * (i + 1))%Z in APC by lia.
    finish. { reflexivity. }
  - (* [comment removed for export] *)
    zstep. zstep. zstep. if_lit. do 7 zstep.
    zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (va_read4 mc VA slots i slot _ VAA NTH Hi eq_refl) as RD end.
    zstep. clear RD. zstep. zstep.
    replace (VA + 8 * i + 8)%Z with (VA + 8 * (i + 1))%Z in APC by lia.
    finish. { reflexivity. }
  - (* [comment removed for export] *)
    zstep. zstep. zstep. if_lit. do 7 zstep.
    zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (va_read4 mc VA slots i slot _ VAA NTH Hi eq_refl) as RD end.
    zstep. clear RD. zstep. zstep.
    replace (VA + 8 * i + 8)%Z with (VA + 8 * (i + 1))%Z in APC by lia.
    finish. { reflexivity. }
  - (* [comment removed for export] *)
    zstep. zstep. zstep. if_lit. do 7 zstep.
    zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (va_read8 mc VA slots i slot _ VAA NTH Hi eq_refl) as RD end.
    zstep. clear RD. zstep. zstep.
    replace (VA + 8 * i + 8)%Z with (VA + 8 * (i + 1))%Z in APC by lia.
    finish. { reflexivity. }
Qed.
End Sz5.
Lemma pop_arg_spec : ltac:(let t := eval cbv delta [pop_arg_spec__stmt] in pop_arg_spec__stmt in exact t).
Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m VA slots i ty slot x y. ltac2:(SecDiet.SzSec.closeP 'pop_arg_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.F_memset.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.

Definition pop_arg_entry := 0x1d34c%Z.
Definition T_PTR := 9%Z. Definition T_INT := 10%Z. Definition T_UINT := 11%Z. Definition T_SIZET := 20%Z.

(* [comment removed for export] *)
Definition va_area (m : word -> option byte) (VA : Z) (slots : list word) : Prop :=
  bytes_at usegs m VA (u64s slots).

(* [comment removed for export] *)
Definition pop_arg_lo (ty : Z) (slot : word) : word :=
  if (ty =? T_INT)%Z then sx32 slot
  else if (ty =? T_UINT)%Z then zx32 slot
  else slot.                                   (* [comment removed for export] *)
Definition pop_arg_hi (ty : Z) (slot y : word) : word := y.

Definition pop_arg_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (ARG AP VA : Z) (slots : list word) (i ty : Z) (slot y : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Ft m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             Ft (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (AP, AP + 8); (ARG, ARG + 16)]%Z m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' (bv_unsigned sp - 16) (bv_unsigned sp)
    /\ rw_cells usegs m' AP [C8 (Z_to_bv 64 (VA + 8 * (i + 1)))]
    /\ rw_cells usegs m' ARG [C8 (pop_arg_lo ty slot); C8 (pop_arg_hi ty slot y)]
    /\ va_area m' VA slots
    /\ Ft = F.   (* [comment removed for export] *)

Lemma firstn4_le8 : forall w : word, firstn 4 (le8 w) = le4 w.
Proof. intros w. reflexivity. Qed.

Definition va_read8__stmt : Prop := forall m VA slots (i : Z) w a,
  bytes_at usegs m VA (u64s slots) -> nth_error slots (Z.to_nat i) = Some w -> (0 <= i)%Z -> a = wa (VA + 8 * i) ->
  ov_read_bytes usegs m a 8 = Some (le8 w).
Section Sz2.
Variables m VA slots i w a : ltac2:(SecDiet.SzSec.tyM 'va_read8__stmt "vvvvvv" @m).
#[using="Type"] Lemma va_read8__body : ltac2:(SecDiet.SzSec.bodyP 'va_read8__stmt "vvvvvv").
Proof.
  intros Hb Hn Hi ->.
  destruct (u64s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
  replace (8 * i)%Z with (Z.of_nat (8 * Z.to_nat i))%Z by lia.
  rewrite (bytes_at_ov_read usegs m VA (u64s slots) (8 * Z.to_nat i) 8 Hb).
  2:{ rewrite Eu, !length_app, length_le8, Hlu. lia. }
  rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
  rewrite firstn_app, firstn_all2 by (rewrite length_le8; lia).
  rewrite length_le8, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.
End Sz2.
Lemma va_read8 : ltac:(let t := eval cbv delta [va_read8__stmt] in va_read8__stmt in exact t).
Proof. intros m VA slots i w a. ltac2:(SecDiet.SzSec.closeP 'va_read8__body "vvvvvv"). Qed.

Definition va_read4__stmt : Prop := forall m VA slots (i : Z) w a,
  bytes_at usegs m VA (u64s slots) -> nth_error slots (Z.to_nat i) = Some w -> (0 <= i)%Z -> a = wa (VA + 8 * i) ->
  ov_read_bytes usegs m a 4 = Some (le4 w).
Section Sz3.
Variables m VA slots i w a : ltac2:(SecDiet.SzSec.tyM 'va_read4__stmt "vvvvvv" @m).
#[using="Type"] Lemma va_read4__body : ltac2:(SecDiet.SzSec.bodyP 'va_read4__stmt "vvvvvv").
Proof.
  intros Hb Hn Hi ->.
  destruct (u64s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
  replace (8 * i)%Z with (Z.of_nat (8 * Z.to_nat i))%Z by lia.
  rewrite (bytes_at_ov_read usegs m VA (u64s slots) (8 * Z.to_nat i) 4 Hb).
  2:{ rewrite Eu, !length_app, length_le8, Hlu. lia. }
  rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
  rewrite firstn_app. rewrite length_le8. change (4 - 8)%nat with 0%nat. rewrite firstn_O, app_nil_r.
  rewrite firstn4_le8. reflexivity.
Qed.
End Sz3.
Lemma va_read4 : ltac:(let t := eval cbv delta [va_read4__stmt] in va_read4__stmt in exact t).
Proof. intros m VA slots i w a. ltac2:(SecDiet.SzSec.closeP 'va_read4__body "vvvvvv"). Qed.

Lemma va_area_bound : forall m VA slots, va_area m VA slots -> (0 <= VA /\ VA + 8 * Z.of_nat (length slots) <= 2^64)%Z.
Proof. intros m VA slots H. pose proof (bytes_at_bound _ _ _ _ H) as B. rewrite u64s_length in B. lia. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac if_lit :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let v := eval vm_compute in c in change c with v; cbv iota
  end.

Definition pop_arg_spec__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte)
    (VA : Z) (slots : list word) (i ty : Z) (slot x y : word),
  rw_cells usegs m (bv_unsigned a2) [C8 (Z_to_bv 64 (VA + 8 * i))] ->
  va_area m VA slots -> nth_error slots (Z.to_nat i) = Some slot -> (0 <= i)%Z ->
  rw_cells usegs m (bv_unsigned a0) [C8 x; C8 y] ->
  stk usegs m (bv_unsigned sp - 16) (bv_unsigned sp) ->
  mem_inv usegs m ->
  a1 = Z_to_bv 64 ty -> (ty = T_PTR \/ ty = T_INT \/ ty = T_UINT \/ ty = T_SIZET) ->
  (16 <= bv_unsigned sp)%Z ->
  (bv_unsigned sp <= bv_unsigned a2)%Z -> (bv_unsigned sp <= bv_unsigned a0)%Z ->
  (bv_unsigned a2 + 8 <= bv_unsigned a0 \/ bv_unsigned a0 + 16 <= bv_unsigned a2)%Z ->
  (VA + 8 * Z.of_nat (length slots) <= bv_unsigned sp - 16 \/ bv_unsigned sp <= VA)%Z ->
  (VA + 8 * Z.of_nat (length slots) <= bv_unsigned a2 \/ bv_unsigned a2 + 8 <= VA)%Z ->
  (VA + 8 * Z.of_nat (length slots) <= bv_unsigned a0 \/ bv_unsigned a0 + 16 <= VA)%Z ->
  evt usegs (pop_arg_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               (bv_unsigned a0) (bv_unsigned a2) VA slots i ty slot y m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1d34c) fc None m (seg_rom usegs)).
Section Sz5.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m VA slots i ty slot x y : ltac2:(SecDiet.SzSec.tyM 'pop_arg_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
#[using="Type"] Lemma pop_arg_spec__body : ltac2:(SecDiet.SzSec.bodyP 'pop_arg_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
 intros APC VAA NTH Hi ARGC ST MI -> TY SPLO A2 A0 SEP1 SEP2 SEP3 SEP4.
  pose_word_ranges.
  pose proof (va_area_bound _ _ _ VAA) as VB. unfold va_area in VAA.
  assert (IL : (Z.to_nat i < length slots)%nat) by (apply nth_error_Some; rewrite NTH; discriminate).
  set (AP := bv_unsigned a2) in *. replace a2 with (Z_to_bv 64 AP) by (unfold AP; rewrite Z_to_bv_bv_unsigned; reflexivity).
  set (ARG := bv_unsigned a0) in *. replace a0 with (Z_to_bv 64 ARG) by (unfold ARG; rewrite Z_to_bv_bv_unsigned; reflexivity).
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (AP, AP + 8); (ARG, ARG + 16)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  destruct TY as [-> | [-> | [-> | ->]]]; unfold T_PTR, T_INT, T_UINT, T_SIZET, pop_arg_lo, pop_arg_hi; cbn [Z.eqb Pos.eqb].
  - (* [comment removed for export] *)
    zstep. zstep. zstep. if_lit. do 7 zstep.
    zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (va_read8 mc VA slots i slot _ VAA NTH Hi eq_refl) as RD end.
    zstep. clear RD. zstep. zstep.
    replace (VA + 8 * i + 8)%Z with (VA + 8 * (i + 1))%Z in APC by lia.
    finish. { reflexivity. }
  - (* [comment removed for export] *)
    zstep. zstep. zstep. if_lit. do 7 zstep.
    zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (va_read4 mc VA slots i slot _ VAA NTH Hi eq_refl) as RD end.
    zstep. clear RD. zstep. zstep.
    replace (VA + 8 * i + 8)%Z with (VA + 8 * (i + 1))%Z in APC by lia.
    finish. { reflexivity. }
  - (* [comment removed for export] *)
    zstep. zstep. zstep. if_lit. do 7 zstep.
    zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (va_read4 mc VA slots i slot _ VAA NTH Hi eq_refl) as RD end.
    zstep. clear RD. zstep. zstep.
    replace (VA + 8 * i + 8)%Z with (VA + 8 * (i + 1))%Z in APC by lia.
    finish. { reflexivity. }
  - (* [comment removed for export] *)
    zstep. zstep. zstep. if_lit. do 7 zstep.
    zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (va_read8 mc VA slots i slot _ VAA NTH Hi eq_refl) as RD end.
    zstep. clear RD. zstep. zstep.
    replace (VA + 8 * i + 8)%Z with (VA + 8 * (i + 1))%Z in APC by lia.
    finish. { reflexivity. }
Qed.
End Sz5.
Lemma pop_arg_spec : ltac:(let t := eval cbv delta [pop_arg_spec__stmt] in pop_arg_spec__stmt in exact t).
Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m VA slots i ty slot x y. ltac2:(SecDiet.SzSec.closeP 'pop_arg_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End TwB.
End F_pop_arg.

(* [comment removed for export] *)
Module SfKit.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Bytes ZBridge Mem Cells.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim PcapPrelim PcapTypes PcapPure Pcap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma le_of_bytes_le_val : forall bs, le_of_bytes bs = le_val bs.
Proof. induction bs as [|b bs IH]; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.

Lemma le_of_bytes_4 : forall a b c d, le_of_bytes [a; b; c; d] = a + 256 * b + 65536 * c + 16777216 * d.
Proof. intros. cbn. lia. Qed.
Lemma le_of_bytes_2 : forall a b, le_of_bytes [a; b] = a + 256 * b.
Proof. intros. cbn. lia. Qed.

Lemma le_bytes_4_of : forall a b c d, 0 <= a < 256 -> 0 <= b < 256 -> 0 <= c < 256 -> 0 <= d < 256 ->
  le_bytes 4 (le_of_bytes [a; b; c; d]) = [a; b; c; d].
Proof.
  intros a b c d Ha Hb Hc Hd. rewrite le_of_bytes_4. unfold le_bytes. change (Z.to_nat 4) with 4%nat. cbn [le_bytes_nat].
  f_equal; [Z.div_mod_to_equations; lia|]. f_equal; [Z.div_mod_to_equations; lia|].
  f_equal; [Z.div_mod_to_equations; lia|]. f_equal. Z.div_mod_to_equations; lia.
Qed.

Lemma bswap32_bytes : forall a b c d, 0 <= a < 256 -> 0 <= b < 256 -> 0 <= c < 256 -> 0 <= d < 256 ->
  bswap32 (le_of_bytes [a; b; c; d]) = le_of_bytes [d; c; b; a].
Proof. intros. unfold bswap32. rewrite le_bytes_4_of by lia. reflexivity. Qed.

Lemma le_bytes_2_of : forall a b, 0 <= a < 256 -> 0 <= b < 256 -> le_bytes 2 (le_of_bytes [a; b]) = [a; b].
Proof.
  intros a b Ha Hb. rewrite le_of_bytes_2. unfold le_bytes. change (Z.to_nat 2) with 2%nat. cbn [le_bytes_nat].
  f_equal; [Z.div_mod_to_equations; lia|]. f_equal. Z.div_mod_to_equations; lia.
Qed.
Lemma bswap16_bytes : forall a b, 0 <= a < 256 -> 0 <= b < 256 -> bswap16 (le_of_bytes [a; b]) = le_of_bytes [b; a].
Proof. intros. unfold bswap16. rewrite le_bytes_2_of by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma le4_inv : forall a b c d v, 0 <= a < 256 -> 0 <= b < 256 -> 0 <= c < 256 -> 0 <= d < 256 ->
  a + 256 * b + 65536 * c + 16777216 * d = v ->
  a = v mod 256 /\ b = (v / 256) mod 256 /\ c = (v / 65536) mod 256 /\ d = v / 16777216.
Proof.
  intros a b c d v Ha Hb Hc Hd E.
  assert (Q1 : v / 256 = b + 256 * c + 65536 * d) by (symmetry; apply Z.div_unique with (r := a); lia).
  assert (Q2 : v / 65536 = c + 256 * d) by (symmetry; apply Z.div_unique with (r := a + 256 * b); lia).
  repeat split.
  - apply Z.mod_unique with (q := b + 256 * c + 65536 * d); lia.
  - rewrite Q1. apply Z.mod_unique with (q := c + 256 * d); lia.
  - rewrite Q2. apply Z.mod_unique with (q := d); lia.
  - apply Z.div_unique with (r := a + 256 * b + 65536 * c); lia.
Qed.

Ltac magic_bytes E :=
  apply le4_inv in E; [| lia | lia | lia | lia];
  let E1 := fresh in let E2 := fresh in let E3 := fresh in let E4 := fresh in
  destruct E as (E1 & E2 & E3 & E4); vm_compute in E1; vm_compute in E2; vm_compute in E3; vm_compute in E4.

(* [comment removed for export] *)
Lemma magic_cases : forall m0 m1 m2 m3, 0 <= m0 < 256 -> 0 <= m1 < 256 -> 0 <= m2 < 256 -> 0 <= m3 < 256 ->
  let V := le_of_bytes [m0; m1; m2; m3] in
     (m0 = 212 /\ m1 = 195 /\ m2 = 178 /\ m3 = 161)    (* [comment removed for export] *)
  \/ (m0 = 52 /\ m1 = 205 /\ m2 = 178 /\ m3 = 161)     (* [comment removed for export] *)
  \/ (m0 = 77 /\ m1 = 60 /\ m2 = 178 /\ m3 = 161)      (* [comment removed for export] *)
  \/ (m0 = 161 /\ m1 = 178 /\ m2 = 195 /\ m3 = 212)    (* [comment removed for export] *)
  \/ (m0 = 161 /\ m1 = 178 /\ m2 = 205 /\ m3 = 52)     (* [comment removed for export] *)
  \/ (m0 = 161 /\ m1 = 178 /\ m2 = 60 /\ m3 = 77)      (* [comment removed for export] *)
  \/ (is_pcap_magic V = false /\ is_pcap_magic (bswap32 V) = false).
Proof.
  intros m0 m1 m2 m3 H0 H1 H2 H3 V.
  destruct (is_pcap_magic V) eqn:E1.
  - unfold is_pcap_magic, TCPDUMP_MAGIC, KUZNETZOV_TCPDUMP_MAGIC, NSEC_TCPDUMP_MAGIC in E1. subst V. rewrite le_of_bytes_4 in E1.
    apply Bool.orb_true_iff in E1 as [E1|E1]; [apply Bool.orb_true_iff in E1 as [E1|E1]|]; apply Z.eqb_eq in E1; magic_bytes E1; subst.
    + left. repeat split; reflexivity.
    + right; left. repeat split; reflexivity.
    + right; right; left. repeat split; reflexivity.
  - destruct (is_pcap_magic (bswap32 V)) eqn:E2; [|right; right; right; right; right; right; split; reflexivity].
    unfold is_pcap_magic, TCPDUMP_MAGIC, KUZNETZOV_TCPDUMP_MAGIC, NSEC_TCPDUMP_MAGIC in E2. subst V. rewrite bswap32_bytes, le_of_bytes_4 in E2 by lia.
    apply Bool.orb_true_iff in E2 as [E2|E2]; [apply Bool.orb_true_iff in E2 as [E2|E2]|]; apply Z.eqb_eq in E2; magic_bytes E2; subst.
    + right; right; right; left. repeat split; reflexivity.
    + right; right; right; right; left. repeat split; reflexivity.
    + right; right; right; right; right; left. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma zxb_lit : forall a, 0 <= a < 256 -> zxb (Z_to_bv 8 a) = Z_to_bv 64 a.
Proof. intros a Ha. unfold zxb. f_equal. apply Z_to_bv_small. unfold bv_modulus. cbn. lia. Qed.

Lemma sxb_lit : forall a, 0 <= a < 256 -> sxb (Z_to_bv 8 a) = Z_to_bv 64 (a - 256 * (a / 128)).
Proof.
  intros a Ha. unfold sxb. f_equal. rewrite Z_to_bv_signed. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn -[Z.add Z.sub Z.modulo Z.div Z.mul].
  Z.div_mod_to_equations; lia.
Qed.

Lemma Z_to_bv8_mod : forall x y, x mod 256 = y mod 256 -> Z_to_bv 8 x = Z_to_bv 8 y.
Proof. intros x y E. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N Z.pow_pos Pos.iter Z.mul]. exact E. Qed.

Lemma le2_bytes : forall a b, 0 <= a < 256 -> 0 <= b < 256 -> le2 (Z_to_bv 64 (a + 256 * b)) = [Z_to_bv 8 a; Z_to_bv 8 b].
Proof.
  intros a b Ha Hb. unfold le2. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes].
  f_equal; [apply Z_to_bv8_mod; Z.div_mod_to_equations; lia|]. f_equal. apply Z_to_bv8_mod. rewrite Z.shiftr_div_pow2 by lia. Z.div_mod_to_equations; lia.
Qed.

Lemma le4_bytes : forall a b c d, 0 <= a < 256 -> 0 <= b < 256 -> 0 <= c < 256 -> 0 <= d < 256 ->
  le4 (Z_to_bv 64 (a + 256 * b + 65536 * c + 16777216 * d)) = [Z_to_bv 8 a; Z_to_bv 8 b; Z_to_bv 8 c; Z_to_bv 8 d].
Proof.
  intros a b c d Ha Hb Hc Hd. unfold le4. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes]. rewrite !Z.shiftr_shiftr, !Z.shiftr_div_pow2 by lia.
  cbn [Z.add Z.pow Z.pow_pos Pos.iter Z.mul].
  f_equal; [apply Z_to_bv8_mod; Z.div_mod_to_equations; lia|]. f_equal; [apply Z_to_bv8_mod; Z.div_mod_to_equations; lia|].
  f_equal; [apply Z_to_bv8_mod; Z.div_mod_to_equations; lia|]. f_equal. apply Z_to_bv8_mod. Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
Lemma land_high_low : forall x y k, 0 <= x -> 0 <= y < 2^k -> 0 <= k -> Z.land (x * 2^k) y = 0.
Proof.
  intros x y k Hx Hy Hk. apply Z.bits_inj_0. intros n.
  destruct (Z.lt_ge_cases n 0) as [Hn|Hn]; [apply Z.testbit_neg_r; exact Hn|].
  rewrite Z.land_spec. destruct (Z.lt_ge_cases n k) as [Hnk|Hnk].
  - rewrite Z.mul_pow2_bits_low by lia. reflexivity.
  - destruct (Z.eq_dec y 0) as [->|Hy0]; [rewrite Z.testbit_0_l; apply Bool.andb_false_r|].
    rewrite (Z.bits_above_log2 y n); [apply Bool.andb_false_r| lia|].
    apply (proj1 (Z.log2_lt_pow2 y n ltac:(lia))). eapply Z.lt_le_trans; [apply (proj2 Hy)|]. apply Z.pow_le_mono_r; lia.
Qed.

Lemma lor_high_low : forall x y k, 0 <= x -> 0 <= y < 2^k -> 0 <= k -> Z.lor (x * 2^k) y = x * 2^k + y.
Proof.
  intros x y k Hx Hy Hk. rewrite <- Z.lxor_lor by (apply land_high_low; lia).
  symmetry. apply Z.add_nocarry_lxor. apply land_high_low; lia.
Qed.
Lemma lor_low_high : forall x y k, 0 <= x -> 0 <= y < 2^k -> 0 <= k -> Z.lor y (x * 2^k) = x * 2^k + y.
Proof. intros. rewrite Z.lor_comm. apply lor_high_low; lia. Qed.

(* [comment removed for export] *)
Definition magic_sx (m0 m1 m2 m3 : Z) : Z :=
  m0 + 256 * m1 + 65536 * m2 + 16777216 * m3 + (m3 / 128) * (2^64 - 2^32).

Lemma magic_word : forall m0 m1 m2 m3, 0 <= m0 < 256 -> 0 <= m1 < 256 -> 0 <= m2 < 256 -> 0 <= m3 < 256 ->
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (m3 - 256 * (m3 / 128)))) 24)))
                                                  (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 m2)) 16))))))
                    (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 m1)) 8)))
                                                  (bv_unsigned (Z_to_bv 64 m0))))))
  = Z_to_bv 64 (magic_sx m0 m1 m2 m3).
Proof.
  intros m0 m1 m2 m3 H0 H1 H2 H3. unfold magic_sx.
  rewrite !Z.shiftl_mul_pow2 by lia.
  rewrite (unsigned_lit m0), (unsigned_lit m1), (unsigned_lit m2) by lia.
  rewrite (unsigned_lit (m1 * 2^8)), (unsigned_lit (m2 * 2^16)) by lia.
  rewrite (lor_high_low m1 m0 8) by lia. rewrite (unsigned_lit (m1 * 2^8 + m0)) by lia.
  assert (D : m3 / 128 = 0 \/ m3 / 128 = 1) by (Z.div_mod_to_equations; lia).
  destruct D as [D|D]; rewrite D.
  - replace (m3 - 256 * 0) with m3 by lia. rewrite (unsigned_lit m3) by lia. rewrite (unsigned_lit (m3 * 2^24)) by lia.
    rewrite (lor_high_low m3 (m2 * 2^16) 24) by lia. rewrite (unsigned_lit (m3 * 2 ^ 24 + m2 * 2 ^ 16)) by lia.
    replace (m3 * 2 ^ 24 + m2 * 2 ^ 16) with ((m3 * 2^8 + m2) * 2^16) by lia.
    rewrite (lor_high_low (m3 * 2^8 + m2) (m1 * 2^8 + m0) 16) by lia. f_equal. lia.
  - rewrite (Z_to_bv_unsigned 64 (m3 - 256 * 1)). unfold bv_wrap. change (bv_modulus 64) with (2^64)%Z.
    replace ((m3 - 256 * 1) mod 2^64) with (2^64 - 256 + m3) by (Z.div_mod_to_equations; lia).
    rewrite (Z_to_bv_unsigned 64 ((2 ^ 64 - 256 + m3) * 2 ^ 24)). unfold bv_wrap. change (bv_modulus 64) with (2^64)%Z.
    replace (((2 ^ 64 - 256 + m3) * 2 ^ 24) mod 2 ^ 64) with ((2^40 - 256 + m3) * 2^24) by (Z.div_mod_to_equations; lia).
    rewrite (lor_high_low (2^40 - 256 + m3) (m2 * 2^16) 24) by lia.
    rewrite (unsigned_lit ((2 ^ 40 - 256 + m3) * 2 ^ 24 + m2 * 2 ^ 16)) by lia.
    replace ((2 ^ 40 - 256 + m3) * 2 ^ 24 + m2 * 2 ^ 16) with (((2 ^ 40 - 256 + m3) * 2^8 + m2) * 2^16) by lia.
    rewrite (lor_high_low ((2 ^ 40 - 256 + m3) * 2^8 + m2) (m1 * 2^8 + m0) 16) by lia. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma magic_sx_range : forall m0 m1 m2 m3, 0 <= m0 < 256 -> 0 <= m1 < 256 -> 0 <= m2 < 256 -> 0 <= m3 < 256 ->
  0 <= magic_sx m0 m1 m2 m3 < 2^64.
Proof. intros. unfold magic_sx. Z.div_mod_to_equations; lia. Qed.

Lemma magic_none : forall m0 m1 m2 m3, 0 <= m0 < 256 -> 0 <= m1 < 256 -> 0 <= m2 < 256 -> 0 <= m3 < 256 ->
  is_pcap_magic (le_of_bytes [m0; m1; m2; m3]) = false -> is_pcap_magic (bswap32 (le_of_bytes [m0; m1; m2; m3])) = false ->
  let W := magic_sx m0 m1 m2 m3 in
  W <> 18446744072127431636 (* [comment removed for export] *) /\ W <> 18446744072127434036 (* [comment removed for export] *) /\ W <> 18446744072127396941 (* [comment removed for export] *)
  /\ W <> 18446744072984179361 (* [comment removed for export] *) /\ W <> 1295823521 (* [comment removed for export] *) /\ W <> 885895841 (* [comment removed for export] *).
Proof.
  intros m0 m1 m2 m3 H0 H1 H2 H3 NM1 NM2 W.
  unfold is_pcap_magic, TCPDUMP_MAGIC, KUZNETZOV_TCPDUMP_MAGIC, NSEC_TCPDUMP_MAGIC in NM1, NM2.
  rewrite bswap32_bytes, le_of_bytes_4 in NM2 by lia. rewrite le_of_bytes_4 in NM1.
  assert (D : m3 / 128 = 0 \/ m3 / 128 = 1) by (Z.div_mod_to_equations; lia).
  subst W. unfold magic_sx.
  repeat split; intros E; exfalso; destruct D as [D|D]; rewrite D in E;
    match type of E with (?v + ?d * ?k = ?c)%Z =>
      let c' := eval vm_compute in (c - d * k)%Z in
      assert (E' : v = c') by lia end;
    clear E;
    fastfirst (first [ lia
          | magic_bytes E'; subst; vm_compute in D; vm_compute in NM1; vm_compute in NM2;
            first [discriminate D | discriminate NM1 | discriminate NM2] ]).
Qed.

(* [comment removed for export] *)
Section ChkRest.
  Context {M : Type -> Type} (MO : MonadOps M) {fh ptr : Type} (P : Prims M fh ptr).
  Local Notation "x <- m ;; k" := (mo_bind MO m (fun x => k)) (at level 100, m at next level, right associativity).
  Local Notation "m ;;; k" := (mo_bind MO m (fun _ => k)) (at level 100, right associativity).
  Local Notation "' pat <- m ;; k" := (mo_bind MO m (fun x => let 'pat := x in k)) (at level 100, pat pattern, m at next level, right associativity).
  Local Notation "'ret' x" := (mo_ret MO x) (at level 10).
  Local Notation "'fret' f x" := (e_fret P f x) (at level 10, f at level 0).

  (* [comment removed for export] *)
  Definition chk_buf_model (self : ptr) (fp : fh) (precision : Z) (swapped : bool)
             (version_major version_minor lt lt_ext hdrsize snapshot : Z) (LS : lenswap_t) (SC : sf_scale_t) : M check_result :=
    let bufsize := if 2048 <? snapshot then 2048 else snapshot in
    b <- e_malloc P bufsize ;;
    match b with
    | None => e_free P self ;;; fret FF_CHECK_HEADER (CH_Err Msg.out_of_memory)
    | Some buf =>
      fret FF_CHECK_HEADER (CH_Ok (mkPcap self fp bufsize bufsize buf [] swapped version_major version_minor
                    snapshot lt lt_ext precision 0 [] hdr0
                    (PrivPcap (mkSf hdrsize LS SC))))
    end.
  (* [comment removed for export] *)
  Definition chk_sf_model (self : ptr) (fp : fh) (precision magic_int : Z) (swapped : bool)
             (version_major version_minor lt lt_ext snapshot : Z) (LS : lenswap_t) (SC : sf_scale_t) : M check_result :=
    let '(hdrsize, snapshot) :=
      if magic_int =? KUZNETZOV_TCPDUMP_MAGIC then
        (24, if lt =? DLT_EN10MB then (if snapshot <=? INT_MAX - 14 then snapshot + 14 else INT_MAX) else snapshot)
      else (16, snapshot) in
    chk_buf_model self fp precision swapped version_major version_minor lt lt_ext hdrsize snapshot LS SC.
  (* [comment removed for export] *)
  Definition chk_fill_model (self : ptr) (fp : fh) (precision magic_int : Z) (swapped : bool)
             (version_major version_minor snaplen linktype : Z) : M check_result :=
      let lt := linktype_to_dlt (Z.land linktype 65535) in
      let lt_ext := s32 (Z.land linktype 4294901760) in
      let snapshot := pcapint_adjust_snapshot lt snaplen in
      let scale := if precision =? PCAP_TSTAMP_PRECISION_MICRO then
                     Some (if magic_int =? NSEC_TCPDUMP_MAGIC then SF_SCALE_DOWN else SF_PASS_THROUGH)
                   else if precision =? PCAP_TSTAMP_PRECISION_NANO then
                     Some (if magic_int =? NSEC_TCPDUMP_MAGIC then SF_PASS_THROUGH else SF_SCALE_UP)
                   else None in
      match scale with
      | None => e_free P self ;;; fret FF_CHECK_HEADER (CH_Err (Msg.unknown_tstamp_resolution precision))
      | Some scale_type =>
        let lengths_swapped :=
          if version_major =? 2 then
            (if version_minor <? 3 then SWAPPED else if version_minor =? 3 then MAYBE_SWAPPED else NOT_SWAPPED)
          else if version_major =? 543 then SWAPPED else NOT_SWAPPED in
        chk_sf_model self fp precision magic_int swapped version_major version_minor lt lt_ext snapshot lengths_swapped scale_type
      end.

  (* [comment removed for export] *)
  Definition chk_rest2 (fp : fh) (precision magic_int : Z) (swapped : bool)
             (version_major version_minor snaplen linktype : Z) : M check_result :=
    if negb (((version_major =? 2) && (version_minor <=? 4)) ||
             ((version_major =? 543) && (version_minor =? 0)))
    then fret FF_CHECK_HEADER (CH_Err (Msg.unsupported_pcap_version version_major version_minor))
    else if negb (Z.land linktype 67043328 =? 0)
    then fret FF_CHECK_HEADER (CH_Err (Msg.reserved_not_zero (Z.land linktype 67043328)))
    else
    r <- pcapint_open_offline_common MO P PCAP_SF_TOTAL ;;
    match r with
    | inl m => fret FF_CHECK_HEADER (CH_Err m)
    | inr self => chk_fill_model self fp precision magic_int swapped version_major version_minor snaplen linktype
    end.

  (* [comment removed for export] *)
  Definition chk_rest (fp : fh) (precision magic_int : Z) (swapped : bool) : M check_result :=
    rest <- e_fread P fp (DStack SitePcapHdrRest 0) 20 ;;
    if negb (zlength rest =? 20) then
      m <- read_fail_msg MO P fp (Msg.trunc_file_header 24 (zlength rest)) ;; fret FF_CHECK_HEADER (CH_Err m)
    else
    let version_major := if swapped then bswap16 (get_le16 rest 0) else get_le16 rest 0 in
    let version_minor := if swapped then bswap16 (get_le16 rest 2) else get_le16 rest 2 in
    let snaplen := if swapped then bswap32 (get_le32 rest 12) else get_le32 rest 12 in
    let linktype := if swapped then bswap32 (get_le32 rest 16) else get_le32 rest 16 in
    chk_rest2 fp precision magic_int swapped version_major version_minor snaplen linktype.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition np_read_model (fp : fh) (p : pcap ptr fh) (hdr : pkthdr) (n : Z) : M (Z * pkthdr * pcap ptr fh) :=
    got <- e_fread P fp (DHeap (pc_buffer p) 0) n ;;
    let p := set_bufdata got p in
    if negb (zlength got =? n) then
      m <- read_fail_msg MO P fp (Msg.trunc_captured_u n (zlength got)) ;;
      fret FF_NEXT_PACKET (-1, hdr, set_errbuf m p)
    else
    let '(hdr, d) := pcapint_post_process (pc_linktype p) (pc_swapped p) hdr (pc_bufdata p) in
    fret FF_NEXT_PACKET (1, hdr, set_bufdata d p).
  (* [comment removed for export] *)
  Definition np_norm_model (p : pcap ptr fh) (hdr : pkthdr) (caplen : Z) : M (Z * pkthdr * pcap ptr fh) :=
    let fp := pc_rfile p in
    let snapshot := pc_snapshot p in
    '(ok, p) <- (if pc_bufsize p <? caplen then
                   let new_bufsize := roundup_pow2_u32 caplen in
                   let new_bufsize := if snapshot <? new_bufsize then snapshot else new_bufsize in
                   grow_buffer MO P p new_bufsize
                 else ret (true, p)) ;;
    if negb ok then fret FF_NEXT_PACKET (-1, hdr, p) else np_read_model fp p hdr caplen.
  (* [comment removed for export] *)
  Definition np_oread_model (fp : fh) (snapshot : Z) (p : pcap ptr fh) (hdr : pkthdr) (caplen len sec usec : Z) : M (Z * pkthdr * pcap ptr fh) :=
    got <- e_fread P fp (DHeap (pc_buffer p) 0) snapshot ;;
    let p := set_bufdata got p in
    if negb (zlength got =? snapshot) then
      m <- read_fail_msg MO P fp (Msg.trunc_captured_d snapshot (zlength got)) ;;
      fret FF_NEXT_PACKET (-1, hdr, set_errbuf m p)
    else
    r <- discard_loop MO P (Z.to_nat ((caplen - snapshot) / 4096 + 2)) fp caplen (caplen - snapshot) snapshot ;;
    match r with
    | inl m => fret FF_NEXT_PACKET (-1, hdr, set_errbuf m p)
    | inr _ =>
      let hdr := mkHdr sec usec snapshot len in
      let '(hdr, d) := pcapint_post_process (pc_linktype p) (pc_swapped p) hdr (pc_bufdata p) in
      fret FF_NEXT_PACKET (1, hdr, set_bufdata d p)
    end.
  Definition np_over_model (p : pcap ptr fh) (hdr : pkthdr) (caplen len sec usec : Z) : M (Z * pkthdr * pcap ptr fh) :=
    let fp := pc_rfile p in
    let snapshot := pc_snapshot p in
    '(ok, p) <- (if pc_bufsize p <? caplen then grow_buffer MO P p snapshot else ret (true, p)) ;;
    if negb ok then fret FF_NEXT_PACKET (-1, hdr, p) else np_oread_model fp snapshot p hdr caplen len sec usec.
  (* [comment removed for export] *)
  Definition np_tail (p : pcap ptr fh) (hdr : pkthdr) (caplen len sec usec : Z) : M (Z * pkthdr * pcap ptr fh) :=
    let snapshot := pc_snapshot p in
    if max_snaplen_for_dlt (pc_linktype p) <? caplen then
      (if snapshot <? caplen
       then fret FF_NEXT_PACKET (-1, hdr, set_errbuf (Msg.invalid_caplen_snaplen caplen snapshot) p)
       else fret FF_NEXT_PACKET (-1, hdr, set_errbuf (Msg.invalid_caplen_maximum caplen (max_snaplen_for_dlt (pc_linktype p))) p))
    else if snapshot <? caplen then np_over_model p hdr caplen len sec usec
    else np_norm_model p hdr caplen.

  (* [comment removed for export] *)
  Definition np_body_model (p : pcap ptr fh) (sec usec caplen len : Z) : M (Z * pkthdr * pcap ptr fh) :=
    let ps := sf_of p in
    let usec := match sf_scale_type ps with
                | SF_PASS_THROUGH => usec
                | SF_SCALE_UP => usec * 1000
                | SF_SCALE_DOWN => usec / 1000
                end in
    let '(caplen, len) := match sf_lengths_swapped ps with
                         | NOT_SWAPPED => (caplen, len)
                         | MAYBE_SWAPPED => if caplen <=? len then (caplen, len) else (len, caplen)
                         | SWAPPED => (len, caplen)
                         end in
    let hdr := mkHdr sec usec caplen len in
    np_tail p hdr caplen len sec usec.

  Lemma np_model_eq : forall p,
    pcap_next_packet MO P p =
    e_fenter P FF_NEXT_PACKET (hb <- e_fread P (pc_rfile p) (DStack SiteSfHdr 0) (sf_hdrsize (sf_of p)) ;;
     if negb (zlength hb =? sf_hdrsize (sf_of p)) then
       e <- e_ferror P (pc_rfile p) ;;
       if e then (m <- errmsg_for_errno MO P "error reading dump file"%string [] ;; fret FF_NEXT_PACKET (-1, hdr0, set_errbuf m p))
       else if negb (zlength hb =? 0) then fret FF_NEXT_PACKET (-1, hdr0, set_errbuf (Msg.trunc_header (sf_hdrsize (sf_of p)) (zlength hb)) p)
       else fret FF_NEXT_PACKET (0, hdr0, p)
     else
       let sw (v : Z) := if pc_swapped p then bswap32 v else v in
       np_body_model p (sw (get_le32 hb 0)) (sw (get_le32 hb 4)) (sw (get_le32 hb 8)) (sw (get_le32 hb 12))).
  Proof using Type. pin_using tt. intros. reflexivity. Qed.

  Lemma chk_live_1 : forall fp prec, pcap_check_header MO P [212; 195; 178; 161] fp prec = e_fenter P FF_CHECK_HEADER (chk_rest fp prec TCPDUMP_MAGIC false).
  Proof using Type. pin_using tt. intros. reflexivity. Qed.
  Lemma chk_live_2 : forall fp prec, pcap_check_header MO P [52; 205; 178; 161] fp prec = e_fenter P FF_CHECK_HEADER (chk_rest fp prec KUZNETZOV_TCPDUMP_MAGIC false).
  Proof using Type. pin_using tt. intros. reflexivity. Qed.
  Lemma chk_live_3 : forall fp prec, pcap_check_header MO P [77; 60; 178; 161] fp prec = e_fenter P FF_CHECK_HEADER (chk_rest fp prec NSEC_TCPDUMP_MAGIC false).
  Proof using Type. pin_using tt. intros. reflexivity. Qed.
  Lemma chk_live_4 : forall fp prec, pcap_check_header MO P [161; 178; 195; 212] fp prec = e_fenter P FF_CHECK_HEADER (chk_rest fp prec TCPDUMP_MAGIC true).
  Proof using Type. pin_using tt. intros. reflexivity. Qed.
  Lemma chk_live_5 : forall fp prec, pcap_check_header MO P [161; 178; 205; 52] fp prec = e_fenter P FF_CHECK_HEADER (chk_rest fp prec KUZNETZOV_TCPDUMP_MAGIC true).
  Proof using Type. pin_using tt. intros. reflexivity. Qed.
  Lemma chk_live_6 : forall fp prec, pcap_check_header MO P [161; 178; 60; 77] fp prec = e_fenter P FF_CHECK_HEADER (chk_rest fp prec NSEC_TCPDUMP_MAGIC true).
  Proof using Type. pin_using tt. intros. reflexivity. Qed.
End ChkRest.

Lemma cells_size_map_C1 : forall l, cells_size (map (fun z => C1 (Z_to_bv 8 z)) l) = length l.
Proof. induction l as [|x l IH]; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.

(* [comment removed for export] *)

Definition le4val (a b c d : Z) : Z := a + 256 * b + 65536 * c + 16777216 * d.

(* [comment removed for export] *)
Lemma land_ff00 : forall x, 0 <= x -> Z.land x 65280 = ((x / 256) mod 256) * 256.
Proof.
  intros x Hx. apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec.
  change 65280 with (Z.shiftl (Z.ones 8) 8). rewrite Z.shiftl_spec by lia.
  replace (x / 256 mod 256 * 256) with (Z.shiftl ((Z.shiftr x 8) mod 2^8) 8)
    by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; reflexivity).
  rewrite Z.shiftl_spec by lia.
  destruct (Z.lt_ge_cases i 8) as [Hlo|Hhi].
  - rewrite (Z.testbit_neg_r (Z.ones 8)) by lia. rewrite (Z.testbit_neg_r _ (i - 8)) by lia. apply Bool.andb_false_r.
  - rewrite Z.testbit_ones_nonneg by lia.
    destruct (Z.lt_ge_cases (i - 8) 8) as [H1|H1].
    + rewrite Z.mod_pow2_bits_low by lia. rewrite Z.shiftr_spec by lia. replace (i - 8 + 8) with i by lia.
      replace (i - 8 <? 8) with true by (symmetry; apply Z.ltb_lt; lia). apply Bool.andb_true_r.
    + rewrite Z.mod_pow2_bits_high by lia. replace (i - 8 <? 8) with false by (symmetry; apply Z.ltb_ge; lia). apply Bool.andb_false_r.
Qed.

Lemma bv_wrap32_eq : forall x, bv_wrap 32 x = x mod 2^32.
Proof. intros. reflexivity. Qed.
Lemma bv_swrap32_small : forall x, 0 <= x < 2^31 -> bv_swrap 32 x = x.
Proof. intros x Hx. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn -[Z.add Z.sub Z.modulo Z.mul]. Z.div_mod_to_equations; lia. Qed.

(* [comment removed for export] *)
Lemma le2_of_val : forall (w : word) a b hi, 0 <= a < 256 -> 0 <= b < 256 -> 0 <= hi ->
  bv_unsigned w = a + 256 * b + 65536 * hi -> le2 w = [Z_to_bv 8 a; Z_to_bv 8 b].
Proof.
  intros w a b hi Ha Hb Hhi E. unfold le2. rewrite E. cbn [Z_to_le_bytes]. rewrite !Z.shiftr_div_pow2 by lia.
  f_equal; [apply Z_to_bv8_mod; Z.div_mod_to_equations; lia|]. f_equal. apply Z_to_bv8_mod. Z.div_mod_to_equations; lia.
Qed.
Lemma le4_of_val : forall (w : word) a b c d hi, 0 <= a < 256 -> 0 <= b < 256 -> 0 <= c < 256 -> 0 <= d < 256 -> 0 <= hi ->
  bv_unsigned w = a + 256 * b + 65536 * c + 16777216 * d + 4294967296 * hi -> le4 w = [Z_to_bv 8 a; Z_to_bv 8 b; Z_to_bv 8 c; Z_to_bv 8 d].
Proof.
  intros w a b c d hi Ha Hb Hc Hd Hhi E. unfold le4. rewrite E. cbn [Z_to_le_bytes]. rewrite !Z.shiftr_shiftr, !Z.shiftr_div_pow2 by lia.
  cbn [Z.add Z.pow Z.pow_pos Pos.iter Z.mul].
  f_equal; [apply Z_to_bv8_mod; Z.div_mod_to_equations; lia|]. f_equal; [apply Z_to_bv8_mod; Z.div_mod_to_equations; lia|].
  f_equal; [apply Z_to_bv8_mod; Z.div_mod_to_equations; lia|]. f_equal. apply Z_to_bv8_mod. Z.div_mod_to_equations; lia.
Qed.

Lemma le2_lit : forall a b, 0 <= a < 256 -> 0 <= b < 256 -> le2 (Z_to_bv 64 (a + 256 * b)) = [Z_to_bv 8 a; Z_to_bv 8 b].
Proof. intros. apply (le2_of_val _ a b 0); [lia|lia|lia|]. rewrite unsigned_lit by lia. lia. Qed.
Lemma le4_lit : forall a b c d, 0 <= a < 256 -> 0 <= b < 256 -> 0 <= c < 256 -> 0 <= d < 256 ->
  le4 (Z_to_bv 64 (le4val a b c d)) = [Z_to_bv 8 a; Z_to_bv 8 b; Z_to_bv 8 c; Z_to_bv 8 d].
Proof. intros. apply (le4_of_val _ a b c d 0); [lia|lia|lia|lia|lia|]. unfold le4val. rewrite unsigned_lit by lia. lia. Qed.

(* [comment removed for export] *)
Lemma zx16_lit : forall x, 0 <= x < 2^16 -> zx16 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof. intros x Hx. unfold zx16. rewrite unsigned_lit by lia. f_equal. apply Z.mod_small. lia. Qed.
Lemma unsigned_zx16 : forall x, 0 <= x < 2^16 -> bv_unsigned (zx16 (Z_to_bv 64 x)) = x.
Proof. intros x Hx. rewrite zx16_lit by lia. apply unsigned_lit. lia. Qed.

Definition sxv (a b c d : Z) : Z := le4val a b c d + 4294967296 * ((d / 128) * 4294967295).
Lemma unsigned_sx32 : forall a b c d, 0 <= a < 256 -> 0 <= b < 256 -> 0 <= c < 256 -> 0 <= d < 256 ->
  bv_unsigned (sx32 (Z_to_bv 64 (le4val a b c d))) = sxv a b c d.
Proof.
  intros a b c d Ha Hb Hc Hd. unfold sx32, sxv. rewrite (unsigned_lit (le4val a b c d)) by (unfold le4val; lia). rewrite unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus, le4val. cbn -[Z.add Z.sub Z.modulo Z.mul Z.div].
  Z.div_mod_to_equations. lia.
Qed.
Lemma sx32_lit : forall a b c d, 0 <= a < 256 -> 0 <= b < 256 -> 0 <= c < 256 -> 0 <= d < 256 ->
  sx32 (Z_to_bv 64 (le4val a b c d)) = Z_to_bv 64 (sxv a b c d).
Proof. intros. apply bv_eq. rewrite unsigned_sx32 by lia. symmetry. apply unsigned_lit. unfold sxv, le4val. Z.div_mod_to_equations; lia. Qed.

(* [comment removed for export] *)
Lemma swap16_val : forall (w : word) a b, 0 <= a < 256 -> 0 <= b < 256 -> bv_unsigned w = a + 256 * b ->
  bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned w) 8))) (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned w) 8)))))
  = b + 256 * a + 65536 * b.
Proof.
  intros w a b Ha Hb E. rewrite E. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  replace ((a + 256 * b) / 2^8) with b by (Z.div_mod_to_equations; lia).
  rewrite (unsigned_lit ((a + 256 * b) * 2^8)), (unsigned_lit b) by lia.
  rewrite lor_high_low by lia. rewrite unsigned_lit by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma swap32_val : forall (w : word) a b c d hi, 0 <= a < 256 -> 0 <= b < 256 -> 0 <= c < 256 -> 0 <= d < 256 -> 0 <= hi < 2^32 ->
  bv_unsigned w = a + 256 * b + 65536 * c + 16777216 * d + 4294967296 * hi ->
  bv_unsigned (Z_to_bv 64
    (Z.lor (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned w) 24)))
                                            (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned w) 65280))) 8))))))
           (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned w) 8))) 65280)))
                                            (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned w)) 24)))))))))
  = d + 256 * c + 65536 * b + 16777216 * a + 4294967296 * (b + 256 * c + 65536 * d + 16777216 * (hi mod 256)).
Proof.
  intros w a b c d hi Ha Hb Hc Hd Hhi E. rewrite E. clear E w.
  set (U := a + 256 * b + 65536 * c + 16777216 * d + 4294967296 * hi).
  assert (HU : 0 <= U < 2^64) by (subst U; lia).
  rewrite !Z.shiftl_mul_pow2, !Z.shiftr_div_pow2 by lia.
  (* [comment removed for export] *)
  rewrite (land_ff00 U) by lia. replace (U / 256 mod 256) with b by (subst U; Z.div_mod_to_equations; lia).
  rewrite (unsigned_lit (b * 256)) by lia.
  rewrite (unsigned_lit (U / 2^8)) by (Z.div_mod_to_equations; lia).
  rewrite (land_ff00 (U / 2^8)) by (Z.div_mod_to_equations; lia).
  replace (U / 2^8 / 256 mod 256) with c by (subst U; Z.div_mod_to_equations; lia).
  rewrite (unsigned_lit (c * 256)) by lia.
  (* [comment removed for export] *)
  rewrite bv_wrap32_eq. replace (U mod 2^32 / 2^24) with d by (subst U; Z.div_mod_to_equations; lia).
  rewrite bv_swrap32_small by lia. rewrite (unsigned_lit d) by lia.
  (* [comment removed for export] *)
  replace (c * 256) with (c * 2^8) by lia. rewrite (lor_high_low c d 8) by lia. rewrite (unsigned_lit (c * 2^8 + d)) by lia.
  (* [comment removed for export] *)
  rewrite (unsigned_lit_wrap (U * 2^24)).
  replace ((U * 2^24) mod 2^64) with ((a + 256 * b + 65536 * c + 16777216 * d + 4294967296 * (hi mod 256)) * 2^24)
    by (subst U; Z.div_mod_to_equations; lia).
  replace (b * 256 * 2^8) with (65536 * b) by lia. rewrite (unsigned_lit (65536 * b)) by lia.
  rewrite (lor_high_low _ (65536 * b) 24) by (Z.div_mod_to_equations; lia).
  rewrite (unsigned_lit ((a + 256 * b + 65536 * c + 16777216 * d + 4294967296 * (hi mod 256)) * 2 ^ 24 + 65536 * b)) by (Z.div_mod_to_equations; lia).
  replace ((a + 256 * b + 65536 * c + 16777216 * d + 4294967296 * (hi mod 256)) * 2 ^ 24 + 65536 * b)
    with (((a + 256 * b + 65536 * c + 16777216 * d + 4294967296 * (hi mod 256)) * 2^8 + b) * 2^16) by lia.
  rewrite lor_high_low by (Z.div_mod_to_equations; lia).
  rewrite unsigned_lit by (Z.div_mod_to_equations; lia). lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma land_ones_shift : forall x k s, 0 <= x -> 0 <= k -> 0 <= s ->
  Z.land x (Z.shiftl (Z.ones k) s) = Z.shiftl ((Z.shiftr x s) mod 2^k) s.
Proof.
  intros x k s Hx Hk Hs. apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec. rewrite !Z.shiftl_spec by lia.
  destruct (Z.lt_ge_cases i s) as [Hlo|Hhi].
  - rewrite (Z.testbit_neg_r (Z.ones k)) by lia. rewrite (Z.testbit_neg_r _ (i - s)) by lia. apply Bool.andb_false_r.
  - rewrite Z.testbit_ones_nonneg by lia.
    destruct (Z.lt_ge_cases (i - s) k) as [H1|H1].
    + rewrite Z.mod_pow2_bits_low by lia. rewrite Z.shiftr_spec by lia. replace (i - s + s) with i by lia.
      replace (i - s <? k) with true by (symmetry; apply Z.ltb_lt; lia). apply Bool.andb_true_r.
    + rewrite Z.mod_pow2_bits_high by lia. replace (i - s <? k) with false by (symmetry; apply Z.ltb_ge; lia). apply Bool.andb_false_r.
Qed.
Lemma land_ones_shift' : forall x k s, 0 <= x -> 0 <= k -> 0 <= s ->
  Z.land x (Z.shiftl (Z.ones k) s) = ((x / 2^s) mod 2^k) * 2^s.
Proof. intros. rewrite land_ones_shift by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma lt16_word : forall l0 l1 l2 l3, 0 <= l0 < 256 -> 0 <= l1 < 256 -> 0 <= l2 < 256 -> 0 <= l3 < 256 ->
  Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (sxv l0 l1 l2 l3))) 48))) 48) = Z_to_bv 64 (l0 + 256 * l1).
Proof.
  intros l0 l1 l2 l3 B0 B1 B2 B3. f_equal. unfold sxv, le4val.
  rewrite (unsigned_lit (_ + 4294967296 * _)) by (Z.div_mod_to_equations; lia). rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  rewrite unsigned_lit_wrap. Z.div_mod_to_equations. lia.
Qed.
Lemma land_ffff : forall l0 l1 l2 l3, 0 <= l0 < 256 -> 0 <= l1 < 256 -> 0 <= l2 < 256 -> 0 <= l3 < 256 ->
  Z.land (le4val l0 l1 l2 l3) 65535 = l0 + 256 * l1.
Proof.
  intros l0 l1 l2 l3 B0 B1 B2 B3. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. unfold le4val. Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
Lemma reserved_word : forall l0 l1 l2 l3, 0 <= l0 < 256 -> 0 <= l1 < 256 -> 0 <= l2 < 256 -> 0 <= l3 < 256 ->
  Z.land (bv_unsigned (Z_to_bv 64 (sxv l0 l1 l2 l3))) 67043328 = (l2 + 256 * (l3 mod 4)) * 65536.
Proof.
  intros l0 l1 l2 l3 B0 B1 B2 B3. unfold sxv, le4val. rewrite (unsigned_lit (_ + 4294967296 * _)) by (Z.div_mod_to_equations; lia).
  change 67043328 with (Z.shiftl (Z.ones 10) 16). rewrite land_ones_shift' by (Z.div_mod_to_equations; lia).
  Z.div_mod_to_equations. lia.
Qed.
Lemma reserved_val : forall l0 l1 l2 l3, 0 <= l0 < 256 -> 0 <= l1 < 256 -> 0 <= l2 < 256 -> 0 <= l3 < 256 ->
  Z.land (le4val l0 l1 l2 l3) 67043328 = (l2 + 256 * (l3 mod 4)) * 65536.
Proof.
  intros l0 l1 l2 l3 B0 B1 B2 B3. unfold le4val.
  change 67043328 with (Z.shiftl (Z.ones 10) 16). rewrite land_ones_shift' by lia.
  Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma ltext_word : forall l0 l1 l2 l3, 0 <= l0 < 256 -> 0 <= l1 < 256 -> 0 <= l2 < 256 -> 0 <= l3 < 256 ->
  l2 = 0 -> l3 mod 4 = 0 ->
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (sxv l0 l1 l2 l3))) 18446744073642442752) = Z_to_bv 64 (s32 (Z.land (le4val l0 l1 l2 l3) 4294901760)).
Proof.
  intros l0 l1 l2 l3 B0 B1 B2 B3 Z2 Z3.
  unfold sxv, le4val. rewrite (unsigned_lit (_ + 4294967296 * _)) by (Z.div_mod_to_equations; lia).
  apply bv_eq. rewrite !Z_to_bv_unsigned.
  change 18446744073642442752 with (Z.shiftl (Z.ones 38) 26). rewrite land_ones_shift' by (Z.div_mod_to_equations; lia).
  change 4294901760 with (Z.shiftl (Z.ones 16) 16). rewrite land_ones_shift' by lia.
  unfold s32, bv_wrap, bv_modulus. cbn -[Z.add Z.sub Z.modulo Z.mul Z.div Z.pow]. cbn [Z.pow Z.pow_pos Pos.iter Z.mul].
  Z.div_mod_to_equations. lia.
Qed.

Lemma sx32_s32 : forall x, 0 <= x < 2^32 -> sx32 (Z_to_bv 64 x) = Z_to_bv 64 (s32 x).
Proof.
  intros x Hx. unfold sx32. rewrite unsigned_lit by lia. apply bv_eq. rewrite !Z_to_bv_unsigned.
  f_equal; unfold bv_swrap, s32, bv_wrap, bv_half_modulus, bv_modulus; cbn -[Z.add Z.sub Z.modulo Z.mul Z.div]; reflexivity.
Qed.
Lemma sx32_small : forall x, 0 <= x < 2^31 -> sx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof. intros x Hx. rewrite sx32_s32 by lia. f_equal. unfold s32. Z.div_mod_to_equations; lia. Qed.

(* [comment removed for export] *)
Lemma linktype_to_dlt_range : forall x, 0 <= x < 65536 -> 0 <= linktype_to_dlt x < 65536.
Proof. intros x Hx. unfold linktype_to_dlt. repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) end; lia. Qed.
Lemma max_snaplen_range : forall d, 1 <= max_snaplen_for_dlt d <= INT_MAX.
Proof. intros d. unfold max_snaplen_for_dlt, MAXIMUM_SNAPLEN, INT_MAX. repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) end; lia. Qed.
Lemma adjust_snapshot_range : forall d sn, 0 <= sn -> 1 <= pcapint_adjust_snapshot d sn <= INT_MAX.
Proof.
  intros d sn Hsn. unfold pcapint_adjust_snapshot. pose proof (max_snaplen_range d).
  destruct (Z.eqb_spec sn 0); cbn [orb]; [lia|]. destruct (Z.ltb_spec INT_MAX sn); lia.
Qed.
Lemma s32_range : forall x, -2^31 <= s32 x < 2^31.
Proof. intros. unfold s32. Z.div_mod_to_equations; lia. Qed.

(* [comment removed for export] *)
Lemma addiw_small : forall x k, 0 <= x < 2^64 -> 0 <= x + k < 2^31 ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 x) + k)) = Z_to_bv 64 (x + k).
Proof. intros x k Hx Hk. rewrite unsigned_lit by lia. f_equal. apply bv_swrap32_small. lia. Qed.

Lemma signed_lit_small : forall x, 0 <= x < 2^63 -> bv_signed (Z_to_bv 64 x) = x.
Proof.
  intros x Hx. rewrite zb_signed, unsigned_lit by lia.
  replace (x <? 2^63) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma zx32_lit : forall x, 0 <= x < 2^32 -> zx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof. intros x Hx. unfold zx32. rewrite unsigned_lit by lia. f_equal. apply Z.mod_small. lia. Qed.
(* [comment removed for export] *)
Lemma zext32_shifts : forall (w : word),
  Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned w) 32))) 32) = Z_to_bv 64 (bv_unsigned w mod 2^32).
Proof.
  intros w. pose proof (bv_unsigned_in_range 64 w) as R. unfold bv_modulus in R. cbn in R.
  f_equal. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. rewrite unsigned_lit_wrap. Z.div_mod_to_equations. lia.
Qed.
Lemma zext32_shifts_lit : forall x, 0 <= x < 2^32 ->
  Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 x)) 32))) 32) = Z_to_bv 64 x.
Proof. intros x Hx. rewrite zext32_shifts, unsigned_lit by lia. f_equal. apply Z.mod_small. lia. Qed.
(* [comment removed for export] *)
Lemma sextw_small : forall x, 0 <= x < 2^31 -> Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 x) + 0)) = Z_to_bv 64 x.
Proof. intros x Hx. rewrite unsigned_lit, Z.add_0_r by lia. f_equal. apply bv_swrap32_small. lia. Qed.
Lemma sextw_small' : forall x, 0 <= x < 2^31 -> Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 x))) = Z_to_bv 64 x.
Proof. intros x Hx. rewrite unsigned_lit by lia. f_equal. apply bv_swrap32_small. lia. Qed.

(* [comment removed for export] *)
Lemma lor_lt_pow2 : forall a b k, 0 <= k -> 0 <= a < 2^k -> 0 <= b < 2^k -> 0 <= Z.lor a b < 2^k.
Proof.
  intros a b k Hk Ha Hb. split; [apply Z.lor_nonneg; lia|].
  destruct (Z.eq_dec a 0) as [->|Na]; [rewrite Z.lor_0_l; lia|].
  destruct (Z.eq_dec b 0) as [->|Nb]; [rewrite Z.lor_0_r; lia|].
  assert (Hp : 0 < Z.lor a b).
  { destruct (Z.eq_dec (Z.lor a b) 0) as [E|NE]; [apply Z.lor_eq_0_iff in E; lia| pose proof (Z.lor_nonneg a b); lia]. }
  apply (proj2 (Z.log2_lt_pow2 (Z.lor a b) k Hp)). rewrite Z.log2_lor by lia.
  apply Z.max_lub_lt; [apply (proj1 (Z.log2_lt_pow2 a k ltac:(lia))); lia | apply (proj1 (Z.log2_lt_pow2 b k ltac:(lia))); lia].
Qed.
Lemma lor_shr_lt : forall x s k, 0 <= k -> 0 <= s -> 0 <= x < 2^k -> 0 <= Z.lor x (Z.shiftr x s) < 2^k.
Proof.
  intros x s k Hk Hs Hx. apply lor_lt_pow2; [lia|lia|]. rewrite Z.shiftr_div_pow2 by lia.
  pose proof (Z.pow_pos_nonneg 2 s). split; [apply Z.div_pos; lia|]. apply Z.le_lt_trans with x; [|lia].
  apply Z.div_le_upper_bound; [lia|]. nia.
Qed.
Lemma srliw_or : forall x s, 0 <= x < 2^31 -> 0 <= s ->
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (Z_to_bv 64 x))) s)))) (bv_unsigned (Z_to_bv 64 x)))
  = Z_to_bv 64 (Z.lor x (Z.shiftr x s)).
Proof.
  intros x s Hx Hs. rewrite (unsigned_lit x) by lia. rewrite bv_wrap32_eq, (Z.mod_small x) by lia.
  assert (R : 0 <= Z.shiftr x s <= x).
  { rewrite Z.shiftr_div_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 s). split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; [lia|]. nia. }
  rewrite bv_swrap32_small by lia. rewrite unsigned_lit by lia. f_equal. apply Z.lor_comm.
Qed.
Lemma addi_lit : forall x k, 0 <= x + k < 2^64 -> 0 <= x < 2^64 -> Z_to_bv 64 (bv_unsigned (Z_to_bv 64 x) + k) = Z_to_bv 64 (x + k).
Proof. intros x k H1 H2. rewrite unsigned_lit by lia. reflexivity. Qed.
End SfKit.

(* [comment removed for export] *)
Module NpArith.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Bytes ZBridge Mem Cells.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Fmt PcapPrelim PcapTypes PcapPure Pcap.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma div1000_magic : forall u, 0 <= u < 2^32 -> u * 274877907 / 2^38 = u / 1000.
Proof. intros u Hu. Z.div_mod_to_equations. lia. Qed.

Lemma u32_s32 : forall c, u32 (s32 c) = u32 c.
Proof. intros c. unfold u32, s32. Z.div_mod_to_equations. lia. Qed.

Lemma s32_mod : forall c, s32 (c mod 2^32) = s32 c.
Proof. intros c. unfold s32. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
Lemma zext32_shifts_mod : forall x, 0 <= x ->
  Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 x)) 32))) 32) = Z_to_bv 64 (x mod 2^32).
Proof.
  intros x Hx. rewrite zext32_shifts. f_equal. rewrite unsigned_lit_wrap. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma swrap32_s32 : forall z, bv_swrap 32 z = s32 z.
Proof. intros z. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus, s32. cbn -[Z.add Z.sub Z.modulo Z.mul Z.div]. reflexivity. Qed.
Lemma sextw_mod : forall x, 0 <= x ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 x) + 0)) = Z_to_bv 64 (s32 (x mod 2^32)).
Proof.
  intros x Hx. rewrite Z.add_0_r, swrap32_s32, unsigned_lit_wrap. f_equal. unfold s32. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma unsigned_s32 : forall r, 0 <= r < 2^32 ->
  bv_unsigned (Z_to_bv 64 (s32 r)) = (if Z.ltb r (2^31) then r else r + 2^64 - 2^32)%Z.
Proof.
  intros r Hr. rewrite unsigned_lit_wrap. unfold s32. destruct (Z.ltb_spec r (2^31)); Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
Lemma le4_mod32 : forall x, 0 <= x -> le4 (Z_to_bv 64 x) = le4 (Z_to_bv 64 (x mod 2^32)).
Proof.
  intros x Hx.
  set (r := x mod 2^32).
  assert (Hr : 0 <= r < 2^32) by (subst r; Z.div_mod_to_equations; lia).
  rewrite (le4_of_val (Z_to_bv 64 x) (r mod 256) ((r / 256) mod 256) ((r / 65536) mod 256) (r / 16777216) ((x mod 2^64) / 2^32));
    [| Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia | subst r; Z.div_mod_to_equations; lia
     | Z.div_mod_to_equations; lia | rewrite unsigned_lit_wrap; subst r; Z.div_mod_to_equations; lia ].
  rewrite (le4_of_val (Z_to_bv 64 r) (r mod 256) ((r / 256) mod 256) ((r / 65536) mod 256) (r / 16777216) 0);
    [ reflexivity | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia | subst r; Z.div_mod_to_equations; lia
    | lia | rewrite unsigned_lit by lia; subst r; Z.div_mod_to_equations; lia ].
Qed.

(* [comment removed for export] *)
Lemma snp_caplen_snaplen_s32 : forall c s,
  Fmt.snprintf 256 "invalid packet capture length %u, bigger than snaplen of %d" [AInt (s32 c); AInt s]
  = Fmt.snprintf 256 "invalid packet capture length %u, bigger than snaplen of %d" [AInt c; AInt s].
Proof.
  intros c s. unfold Fmt.snprintf, snprintf_out, fmt_output.
  let items := eval vm_compute in (fmt "invalid packet capture length %u, bigger than snaplen of %d") in
  change (fmt "invalid packet capture length %u, bigger than snaplen of %d") with items.
  cbn [fmt_pieces hd tl app conv_pieces]. rewrite u32_s32. reflexivity.
Qed.
Lemma snp_caplen_max_s32 : forall c mx,
  Fmt.snprintf 256 "invalid packet capture length %u, bigger than maximum of %u" [AInt (s32 c); AInt mx]
  = Fmt.snprintf 256 "invalid packet capture length %u, bigger than maximum of %u" [AInt c; AInt mx].
Proof.
  intros c mx. unfold Fmt.snprintf, snprintf_out, fmt_output.
  let items := eval vm_compute in (fmt "invalid packet capture length %u, bigger than maximum of %u") in
  change (fmt "invalid packet capture length %u, bigger than maximum of %u") with items.
  cbn [fmt_pieces hd tl app conv_pieces]. rewrite u32_s32. reflexivity.
Qed.

Lemma s32_id : forall c, 0 <= c < 2^31 -> s32 c = c.
Proof. intros c Hc. unfold s32. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
Lemma usec_div1000_word : forall x, 0 <= x ->
  Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 x)) 32)) * 1180591620957929472) 64))) 38)
  = Z_to_bv 64 ((x mod 2^32) / 1000).
Proof.
  intros x Hx.
  assert (E1 : bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 x)) 32)) = ((x mod 2^32) * 2^32)%Z).
  { rewrite unsigned_lit_wrap, Z.shiftl_mul_pow2, unsigned_lit_wrap by lia. Z.div_mod_to_equations. nia. }
  rewrite E1. rewrite (Z.shiftr_div_pow2 _ 64) by lia.
  replace ((x mod 2^32) * 2^32 * 1180591620957929472 / 2^64)%Z with ((x mod 2^32) * 274877907)%Z
    by (rewrite <- (Z.div_mul ((x mod 2^32) * 274877907) (2^64)) by lia; f_equal; lia).
  assert (R : (0 <= x mod 2^32 < 2^32)%Z) by (Z.div_mod_to_equations; lia).
  rewrite unsigned_lit by lia. rewrite Z.shiftr_div_pow2 by lia. f_equal. apply div1000_magic. exact R.
Qed.

(* [comment removed for export] *)
Lemma mul_lit_l : forall u k, 0 <= u < 2^64 -> Z_to_bv 64 (bv_unsigned (Z_to_bv 64 u) * k) = Z_to_bv 64 (u * k).
Proof. intros u k Hu. rewrite unsigned_lit by lia. reflexivity. Qed.
Lemma usec_div1000_word_u3 : forall u, 0 <= u < 2^32 ->
  Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (u * 274877907))) 38) = Z_to_bv 64 (u / 1000).
Proof. intros u Hu. rewrite unsigned_lit by lia. rewrite Z.shiftr_div_pow2 by lia. f_equal. apply div1000_magic. exact Hu. Qed.

(* [comment removed for export] *)
Lemma usec_mul1000_word : forall u, 0 <= u < 2^32 ->
  Z_to_bv 64 (bv_unsigned (Z_to_bv 64 u) * bv_unsigned (Z_to_bv 64 1000)) = Z_to_bv 64 (u * 1000).
Proof. intros u Hu. rewrite !unsigned_lit by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma sxv_range : forall a b c d, 0 <= a < 256 -> 0 <= b < 256 -> 0 <= c < 256 -> 0 <= d < 256 -> 0 <= sxv a b c d < 2^64.
Proof. intros. unfold sxv, le4val. Z.div_mod_to_equations. lia. Qed.
Lemma sxv_mod32 : forall a b c d, 0 <= a < 256 -> 0 <= b < 256 -> 0 <= c < 256 -> 0 <= d < 256 -> (sxv a b c d) mod 2^32 = le4val a b c d.
Proof. intros. unfold sxv, le4val. Z.div_mod_to_equations. lia. Qed.

Lemma bswap32_le4val : forall a b c d, 0 <= a < 256 -> 0 <= b < 256 -> 0 <= c < 256 -> 0 <= d < 256 ->
  bswap32 (le4val a b c d) = le4val d c b a.
Proof. intros. unfold le4val. rewrite <- (le_of_bytes_4 a b c d), bswap32_bytes, le_of_bytes_4 by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma get_le32_hdr : forall g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 rest,
  let hb := g0 :: g1 :: g2 :: g3 :: g4 :: g5 :: g6 :: g7 :: g8 :: g9 :: g10 :: g11 :: g12 :: g13 :: g14 :: g15 :: rest in
  get_le32 hb 0 = le4val g0 g1 g2 g3 /\ get_le32 hb 4 = le4val g4 g5 g6 g7 /\ get_le32 hb 8 = le4val g8 g9 g10 g11 /\ get_le32 hb 12 = le4val g12 g13 g14 g15.
Proof.
  intros. unfold get_le32, zslice, zfirstn, zskipn. subst hb.
  change (Z.to_nat 0) with 0%nat. change (Z.to_nat 4) with 4%nat. change (Z.to_nat 8) with 8%nat. change (Z.to_nat 12) with 12%nat.
  cbn [firstn skipn]. rewrite !le_of_bytes_4. unfold le4val. repeat split; reflexivity.
Qed.

Lemma if_b_true : forall {A} (b : bool) (x y : A), b = true -> (if b then x else y) = x.
Proof. intros A b x y ->. reflexivity. Qed.
Lemma if_b_false : forall {A} (b : bool) (x y : A), b = false -> (if b then x else y) = y.
Proof. intros A b x y ->. reflexivity. Qed.
End NpArith.
