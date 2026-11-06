(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Require OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Ox.F64_001.   (* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Tac Arr Bytes SysStep ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3.
From LinuxProcessSemantics.LinuxProcessSem Require StackLayout Specs.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ITree Nodes Decode RegsEquiv.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Monad.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim StdioCore.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module F_memmove.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes SysStep ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Import F_memcpy.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition memmove_entry := 0x20be4%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section ListFacts.
  Local Open Scope nat_scope.

  Definition mm_state (k p : nat) (bs : list byte) : list byte := firstn p (skipn k bs) ++ skipn p bs.

  #[using="Type"] Lemma mm_state_length : forall k p bs, p <= length bs -> k + p <= length bs -> length (mm_state k p bs) = length bs.
  Proof. intros. unfold mm_state. rewrite length_app, length_firstn, !length_skipn. lia. Qed.

  #[using="Type"] Lemma mm_state_0 : forall k bs, mm_state k 0 bs = bs.
  Proof. intros. reflexivity. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma mm_state_nth_hi : forall k p bs j, p <= j -> k + p <= length bs -> nth_error (mm_state k p bs) j = nth_error bs j.
  Proof.
    intros k p bs j Hj Hk. unfold mm_state.
    rewrite nth_error_app2 by (rewrite length_firstn, length_skipn; lia).
    rewrite length_firstn, length_skipn, Nat.min_l by lia. rewrite nth_error_skipn. f_equal. lia.
  Qed.

  #[using="Type"] Lemma mm_state_skipn_hi : forall k p bs j, p <= j -> k + p <= length bs -> skipn j (mm_state k p bs) = skipn j bs.
  Proof.
    intros k p bs j Hj Hk. unfold mm_state.
    rewrite skipn_app, length_firstn, length_skipn, Nat.min_l by lia.
    rewrite skipn_all2 by (rewrite length_firstn, length_skipn; lia). cbn [app].
    rewrite skipn_skipn. f_equal. lia.
  Qed.

  #[using="Type"] Lemma firstn_plus : forall {X} (a b : nat) (l : list X), firstn (a + b) l = firstn a l ++ firstn b (skipn a l).
  Proof.
    intros X a. induction a as [|a IH]; intros b l; [reflexivity|].
    destruct l as [|x l]; cbn; [now destruct b|]. rewrite IH. reflexivity.
  Qed.

  #[using="Type"] Lemma skipn_skipn' : forall {X} (a b : nat) (l : list X), skipn a (skipn b l) = skipn (b + a) l.
  Proof. intros X a b l. revert l. induction b as [|b IH]; intros l; [reflexivity|]. destruct l; cbn; [now destruct a| apply IH]. Qed.

  (* [comment removed for export] *)
  Definition mm_state_upd__stmt : Prop := forall k p bs xs,
    k + p + length xs <= length bs -> xs = firstn (length xs) (skipn (k + p) bs) ->
    upd_bytes (mm_state k p bs) p xs = mm_state k (p + length xs) bs.
  Section Sz7.
  Variables k p bs xs : ltac2:(SecDiet.SzSec.tyM 'mm_state_upd__stmt "vvvv" @k).
  #[using="Type"] Lemma mm_state_upd__body : ltac2:(SecDiet.SzSec.bodyP 'mm_state_upd__stmt "vvvv").
  Proof.
    intros Hl Hxs.
 unfold upd_bytes, mm_state.
    assert (LA : length (firstn p (skipn k bs)) = p) by (rewrite length_firstn, length_skipn; lia).
    rewrite firstn_app, LA, Nat.sub_diag, firstn_O, app_nil_r.
    rewrite (firstn_all2 (firstn p (skipn k bs))) by (rewrite LA; lia).
    rewrite skipn_app, LA. rewrite (skipn_all2 (firstn p (skipn k bs))) by (rewrite LA; lia). cbn [app].
    rewrite skipn_skipn'. replace (p + (p + length xs - p)) with (p + length xs) by lia.
    rewrite app_assoc. f_equal.
    rewrite firstn_plus. f_equal. rewrite skipn_skipn'. exact Hxs.
  Qed.
  End Sz7.
  #[using="Type"] Lemma mm_state_upd : ltac:(let t := eval cbv delta [mm_state_upd__stmt] in mm_state_upd__stmt in exact t).
  Proof. intros k p bs xs. ltac2:(SecDiet.SzSec.closeP 'mm_state_upd__body "vvvv"). Qed.

  #[using="Type"] Lemma mm_state_all : forall k n bs, mm_state k n bs = firstn n (skipn k bs) ++ skipn n bs.
  Proof. reflexivity. Qed.
End ListFacts.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section ZFacts.
  Local Open Scope Z_scope.
  Notation M64 := 18446744073709551616.

  (* [comment removed for export] *)
  Definition mm_test_taken__stmt : Prop := forall D k n, 0 <= D -> 1 <= k -> 0 <= n < 2^62 -> D + k + n <= 2^64 -> D + k < 2^64 ->
    (D + k - (n + D)) mod M64 <= (0 - (Z.shiftl n 1) mod M64) mod M64 -> 1 <= n <= k.
  Section Sz9.
  Variables D k n : ltac2:(SecDiet.SzSec.tyM 'mm_test_taken__stmt "vvv" @D).
  #[using="Type"] Lemma mm_test_taken__body : ltac2:(SecDiet.SzSec.bodyP 'mm_test_taken__stmt "vvv").
  Proof.
    intros HD Hk Hn HB HB2 H.
 rewrite Z.shiftl_mul_pow2 in H by lia. change (2^1) with 2 in H.
    rewrite (Z.mod_small (n * 2)) in H by lia.
    destruct (Z.eq_dec n 0) as [->|Hn0].
    { exfalso. rewrite (Z.mod_small (D + k - (0 + D))) in H by lia. change ((0 - 0 * 2) mod M64) with 0 in H. lia. }
    replace ((0 - n * 2) mod M64) with (M64 - n * 2) in H.
    2:{ replace (0 - n * 2) with ((M64 - n * 2) + (-1) * M64) by lia. rewrite Z.mod_add by lia. symmetry. apply Z.mod_small. lia. }
    destruct (Z.lt_ge_cases k n); [|lia]. exfalso.
    replace ((D + k - (n + D)) mod M64) with (M64 + k - n) in H; [lia|].
    replace (D + k - (n + D)) with ((M64 + k - n) + (-1) * M64) by lia. rewrite Z.mod_add by lia. symmetry. apply Z.mod_small. lia.
  Qed.
  End Sz9.
  #[using="Type"] Lemma mm_test_taken : ltac:(let t := eval cbv delta [mm_test_taken__stmt] in mm_test_taken__stmt in exact t).
  Proof. intros D k n. ltac2:(SecDiet.SzSec.closeP 'mm_test_taken__body "vvv"). Qed.

  Definition mm_test_not_taken__stmt : Prop := forall D k n, 0 <= D -> 1 <= k -> 0 <= n < 2^62 -> D + k + n <= 2^64 -> D + k < 2^64 ->
    (0 - (Z.shiftl n 1) mod M64) mod M64 < (D + k - (n + D)) mod M64 -> n = 0 \/ k < n.
  Section Sz10.
  Variables D k n : ltac2:(SecDiet.SzSec.tyM 'mm_test_not_taken__stmt "vvv" @D).
  #[using="Type"] Lemma mm_test_not_taken__body : ltac2:(SecDiet.SzSec.bodyP 'mm_test_not_taken__stmt "vvv").
  Proof.
    intros HD Hk Hn HB HB2 H.
 rewrite Z.shiftl_mul_pow2 in H by lia. change (2^1) with 2 in H.
    rewrite (Z.mod_small (n * 2)) in H by lia.
    destruct (Z.eq_dec n 0) as [->|Hn0]; [left; reflexivity| right].
    replace ((0 - n * 2) mod M64) with (M64 - n * 2) in H.
    2:{ replace (0 - n * 2) with ((M64 - n * 2) + (-1) * M64) by lia. rewrite Z.mod_add by lia. symmetry. apply Z.mod_small. lia. }
    destruct (Z.lt_ge_cases k n); [assumption|]. exfalso.
    rewrite Z.mod_small in H by lia. lia.
  Qed.
  End Sz10.
  #[using="Type"] Lemma mm_test_not_taken : ltac:(let t := eval cbv delta [mm_test_not_taken__stmt] in mm_test_not_taken__stmt in exact t).
  Proof. intros D k n. ltac2:(SecDiet.SzSec.closeP 'mm_test_not_taken__body "vvv"). Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma land_lxor_distr : forall a b c, Z.land (Z.lxor a b) c = Z.lxor (Z.land a c) (Z.land b c).
  Proof.
    intros. apply Z.bits_inj'. intros i Hi.
    rewrite Z.land_spec, !Z.lxor_spec, !Z.land_spec. destruct (Z.testbit a i), (Z.testbit b i), (Z.testbit c i); reflexivity.
  Qed.

  #[using="Type"] Lemma land7_lxor : forall a b, 0 <= a -> 0 <= b -> (Z.land (Z.lxor a b) 7 = 0 <-> a mod 8 = b mod 8).
  Proof.
    intros a b Ha Hb. rewrite land_lxor_distr.
    change 7 with (Z.ones 3). rewrite !Z.land_ones by lia. change (2^3) with 8.
    split.
    - intros H. apply Z.lxor_eq in H. exact H.
    - intros H. rewrite H. apply Z.lxor_nilpotent.
  Qed.
End ZFacts.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition memmove_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 : word) (k n : Z) (bs : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ssegs)
    /\ munch [(bv_unsigned a0, bv_unsigned a0 + n)]%Z m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
    /\ u8arr ssegs m' (bv_unsigned a0) (firstn (Z.to_nat n) (skipn (Z.to_nat k) bs) ++ skipn (Z.to_nat n) bs).

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (k n : Z).
  Notation D := (bv_unsigned a0).
  Notation kn := (Z.to_nat k).
  Hypothesis LEN : length bs = Z.to_nat (k + n).
  Hypothesis HK : (1 <= k)%Z.
  Hypothesis HN : (0 <= n < 2^62)%Z.
  Hypothesis DB : (0 <= D /\ D + k + n <= 2^64)%Z.

  Notation POST := (memmove_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 k n bs m).
  (* [comment removed for export] *)
  Notation AT pc mm x5 x11 x12 x13 x14 x15 x16 x17 :=
    (MS (mkR ra sp gp tp x5 t1 t2 s0 s1 a0 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom ssegs)).

  (* [comment removed for export] *)
  Definition INV (m1 : word -> option byte) (p : Z) : Prop :=
    u8arr ssegs m1 D (mm_state kn (Z.to_nat p) bs) /\ mem_inv ssegs m1 /\
    munch [(D, D + n)]%Z m m1 /\ wmono ssegs m m1 /\ (0 <= p <= n)%Z.

  Lemma inv_init : u8arr ssegs m D bs -> mem_inv ssegs m -> INV m 0.
  Proof using HN LEN. pin_using (fun (HN LEN : unit) => tt).
    intros REG MI. split; [rewrite mm_state_0; exact REG|]. split; [exact MI|].
    split; [apply munch_refl|]. split; [apply wmono_refl| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma mm_ret : forall m1 x5 x11 x12 x13 x14 x15 x16 x17, INV m1 n ->
    evt ssegs POST (AT 0x20c70 m1 x5 x11 x12 x13 x14 x15 x16 x17).
  Proof using Type. pin_using tt.
    intros m1 x5 x11 x12 x13 x14 x15 x16 x17 (REG & MI & MU & WM & _).
    step. unfold memmove_post. finish.
  Qed.

  (* [comment removed for export] *)
  Definition mm_read1__stmt : Prop := forall m1 p, INV m1 p -> (p < n)%Z ->
    exists b, nth_error bs (Z.to_nat (k + p)) = Some b /\ ov_read_bytes ssegs m1 (wa (D + (k + p))) 1 = Some [b].
  Section Sz15.
  Variables m1 p : ltac2:(SecDiet.SzSec.tyM 'mm_read1__stmt "vv" @m1).
  Lemma mm_read1__body : ltac2:(SecDiet.SzSec.bodyP 'mm_read1__stmt "vv").
  Proof using HK LEN. pin_using (fun (HK LEN : unit) => tt).
    intros (REG & _ & _ & _ & Hp) Hpn.
    destruct (nth_error bs (Z.to_nat (k + p))) as [b|] eqn:E.
    2:{ exfalso. apply nth_error_None in E. lia. }
    exists b. split; [reflexivity|].
    apply (u8arr_read ssegs m1 D _ (k + p) b _ REG); [|lia|reflexivity].
    rewrite mm_state_nth_hi; [exact E| lia | rewrite LEN; lia].
  Qed.
  End Sz15.
  Lemma mm_read1 : ltac:(let t := eval cbv delta [mm_read1__stmt] in mm_read1__stmt in exact t).
  Proof using HK LEN. intros m1 p. ltac2:(SecDiet.SzSec.closeP 'mm_read1__body "vv"). Qed.

  (* [comment removed for export] *)
  Definition mm_store__stmt : Prop := forall m1 p xs,
    INV m1 p -> (p + Z.of_nat (length xs) <= n)%Z -> xs = firstn (length xs) (skipn (Z.to_nat (k + p)) bs) ->
    store_ok ssegs m1 (wa (D + p)) (length xs) = true /\
    INV (write_to_mem m1 (wa (D + p)) xs) (p + Z.of_nat (length xs)).
  Section Sz16.
  Variables m1 p xs : ltac2:(SecDiet.SzSec.tyM 'mm_store__stmt "vvv" @m1).
  Lemma mm_store__body : ltac2:(SecDiet.SzSec.bodyP 'mm_store__stmt "vvv").
  Proof using DB HK HN LEN. pin_using (fun (DB HK HN LEN : unit) => tt).
    intros (REG & MI & MU & WM & Hp) Hpn Hxs.
    assert (L1 : length (mm_state kn (Z.to_nat p) bs) = length bs) by (apply mm_state_length; rewrite LEN; lia).
    assert (SOK : store_ok ssegs m1 (wa (D + p)) (length xs) = true).
    { eapply (u8arr_store_ok_n ssegs m1 D _ p (length xs) _ REG); [lia| rewrite L1, LEN; lia | reflexivity]. }
    split; [exact SOK|]. split; [|split; [|split; [|split]]].
    - pose proof (u8arr_write_bytes ssegs m1 D _ p xs REG ltac:(lia) ltac:(rewrite L1, LEN; lia)) as REG'.
      rewrite mm_state_upd in REG'; [| rewrite LEN; lia | rewrite Hxs at 1; f_equal; f_equal; lia].
      replace (Z.to_nat p + length xs)%nat with (Z.to_nat (p + Z.of_nat (length xs))) in REG' by lia. exact REG'.
    - apply mem_inv_store; assumption.
    - apply munch_write; [exact MU | lia | lia |]. cbn [inside]. left. lia.
    - apply wmono_write. exact WM.
    - lia.
  Qed.
  End Sz16.
  Lemma mm_store : ltac:(let t := eval cbv delta [mm_store__stmt] in mm_store__stmt in exact t).
  Proof using DB HK HN LEN. intros m1 p xs. ltac2:(SecDiet.SzSec.closeP 'mm_store__body "vvv"). Qed.

  (* [comment removed for export] *)
  Lemma le8_ld : forall w : list byte, length w = 8%nat -> le8 (bv_extract 0 64 (le_bytes_to_word w)) = w.
  Proof using Type. pin_using tt.
    intros w Hl. unfold le8, word_to_le_bytes. rewrite load8_le_val by exact Hl.
    rewrite <- bytes_le_to_Z_le_val, <- Hl. apply Z_to_le_bytes_to_Z.
  Qed.

  (* [comment removed for export] *)
  Ltac mm_arr_store p xs bytes_tac :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m1 ?a ?bs0) _) =>
      replace (write_to_mem m1 a bs0) with (write_to_mem m1 (wa (D + p)%Z) xs)
        by (apply (f_equal2 (write_to_mem m1)); [ unfold wa; fastfirst (first [ noevar_assumption |reflexivity | f_equal; lia]) | first [bytes_tac | symmetry; bytes_tac] ]);
      repeat match goal with
      | H : store_ok ssegs m1 _ _ = true |- _ => clear H
      | H : ov_read_bytes ssegs m1 _ _ = Some _ |- _ => clear H
      | H : INV m1 _ |- _ => clear H
      | H : mem_inv ssegs m1 |- _ => clear H
      | H : u8arr ssegs m1 _ _ |- _ => clear H
      end;
      let m' := fresh "m" in remember (write_to_mem m1 (wa (D + p)%Z) xs) as m' eqn:Heqm; clear Heqm; try clear m1
    end.

  (* [comment removed for export] *)
  Lemma mm_bytes : forall (cnt : nat) (p : Z) m1 x5 x11 x13 x14 x15 x16 x17,
    Z.to_nat (n - p) = cnt -> (p < n)%Z -> INV m1 p ->
    x13 = Z_to_bv 64 (D + p) -> x14 = Z_to_bv 64 (D + k + p) ->
    evt ssegs POST (AT 0x20c1c m1 x5 x11 (Z_to_bv 64 (D + n)) x13 x14 x15 x16 x17).
  Proof using DB HK HN LEN. pin_using (fun (DB HK HN LEN : unit) => tt).
    induction cnt as [|cnt IH]; intros p m1 x5 x11 x13 x14 x15 x16 x17 Hc Hp I -> ->; [lia|].
    pose proof I as I0. destruct I0 as (REG & MI & _ & _ & Hp0).
    destruct (mm_read1 m1 p I Hp) as (b & Hnth & RD).
    replace (D + (k + p))%Z with (D + k + p)%Z in RD by lia.
    destruct (mm_store m1 p [b] I ltac:(cbn [length]; lia)
                ltac:(cbn [length]; symmetry; apply nth_error_first1; rewrite <- Hnth; f_equal; lia)) as [SOK I2].
    cbn [length Z.of_nat Pos.of_succ_nat] in SOK, I2.
    zstep. zstep. zstep.
    zstep; [ mm_arr_store p [b] ltac:(apply le1_zxb) | .. ].
    zstep. zstep. if_cases K; zify_cond K.
    - apply (IH (p + 1)%Z); try reflexivity; try lia; try (f_equal; lia). exact I2.
    - zstep. apply mm_ret. replace n with (p + 1)%Z by lia. exact I2.
  Qed.

  (* [comment removed for export] *)
  Lemma mm_bytes_entry : forall (p : Z) m1 x5 x11 x13 x14 x15 x16 x17,
    INV m1 p -> x13 = Z_to_bv 64 (D + p) -> x14 = Z_to_bv 64 (D + k + p) ->
    evt ssegs POST (AT 0x20c14 m1 x5 x11 (Z_to_bv 64 (n - p)) x13 x14 x15 x16 x17).
  Proof using DB HK HN LEN. pin_using (fun (DB HK HN LEN : unit) => tt).
    intros p m1 x5 x11 x13 x14 x15 x16 x17 I -> ->. pose proof I as I0. destruct I0 as (REG & MI & _ & _ & Hp0).
    zstep. if_cases K; zify_cond K.
    - apply mm_ret. replace n with p by lia. exact I.
    - zstep. replace (D + p + (n - p))%Z with (D + n)%Z by lia.
      apply (mm_bytes (Z.to_nat (n - p)) p); try reflexivity; try lia. exact I.
  Qed.

  (* [comment removed for export] *)
  Lemma mm_read8 : forall m1 p, INV m1 p -> (p + 8 <= n)%Z ->
    ov_read_bytes ssegs m1 (wa (D + (k + p))) 8 = Some (firstn 8 (skipn (Z.to_nat (k + p)) bs)).
  Proof using HK LEN. pin_using (fun (HK LEN : unit) => tt).
    intros m1 p (REG & _ & _ & _ & Hp) Hpn.
    assert (L1 : length (mm_state kn (Z.to_nat p) bs) = length bs) by (apply mm_state_length; rewrite LEN; lia).
    rewrite <- (mm_state_skipn_hi kn (Z.to_nat p) bs (Z.to_nat (k + p))) by (rewrite ?LEN; lia).
    apply (bytes_at_read ssegs m1 D _ (k + p) 8 (proj1 REG)); [lia|]. rewrite L1, LEN. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma mm_words : forall (cnt : nat) (p : Z) m1 x5 x13 x14 x15 x16 x17,
    Z.to_nat (n - p) = cnt -> (p + 8 <= n)%Z -> INV m1 p ->
    x13 = Z_to_bv 64 (D + p) -> x14 = Z_to_bv 64 (D + k + p) ->
    evt ssegs POST (AT 0x20d44 m1 x5 (Z_to_bv 64 7) (Z_to_bv 64 (n - p)) x13 x14 x15 x16 x17).
  Proof using DB HK HN LEN. pin_using (fun (DB HK HN LEN : unit) => tt).
    induction cnt as [cnt IH] using lt_wf_ind; intros p m1 x5 x13 x14 x15 x16 x17 Hc Hp I -> ->.
    pose proof I as I0. destruct I0 as (REG & MI & _ & _ & Hp0).
    pose proof (mm_read8 m1 p I Hp) as RD. replace (D + (k + p))%Z with (D + k + p)%Z in RD by lia.
    set (chunk := firstn 8 (skipn (Z.to_nat (k + p)) bs)) in RD.
    assert (CL : length chunk = 8%nat) by (subst chunk; rewrite length_firstn, length_skipn, LEN; lia).
    destruct (mm_store m1 p chunk I ltac:(rewrite CL; cbn; lia) ltac:(rewrite CL; reflexivity)) as [SOK I2].
    rewrite CL in SOK, I2. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in I2.
    zstep. zstep.
    zstep; [ mm_arr_store p chunk ltac:(apply le8_ld; exact CL) | .. ].
    zstep. zstep. zstep. if_cases K; zify_cond K.
    - replace (n - p + -8)%Z with (n - (p + 8))%Z by lia.
      apply (IH (Z.to_nat (n - (p + 8))) ltac:(lia) (p + 8)%Z); try reflexivity; try lia; try (f_equal; lia). exact I2.
    - zstep. replace (n - p + -8)%Z with (n - (p + 8))%Z by lia.
      apply (mm_bytes_entry (p + 8)); try reflexivity; try (f_equal; lia). exact I2.
  Qed.

  (* [comment removed for export] *)
  Lemma mm_wentry : forall (p : Z) m1 x5 x11 x13 x14 x15 x16 x17,
    INV m1 p -> x13 = Z_to_bv 64 (D + p) -> x14 = Z_to_bv 64 (D + k + p) ->
    evt ssegs POST (AT 0x20d38 m1 x5 x11 (Z_to_bv 64 (n - p)) x13 x14 x15 x16 x17).
  Proof using DB HK HN LEN. pin_using (fun (DB HK HN LEN : unit) => tt).
    intros p m1 x5 x11 x13 x14 x15 x16 x17 I -> ->. pose proof I as I0. destruct I0 as (REG & MI & _ & _ & Hp0).
    zstep. zstep. if_cases K; zify_cond K.
    - apply (mm_bytes_entry p); try reflexivity. exact I.
    - zstep. apply (mm_words (Z.to_nat (n - p)) p); try reflexivity; try lia. exact I.
  Qed.

  (* [comment removed for export] *)
  Lemma mm_align : forall (cnt : nat) (p : Z) m1 x5 x11 x13 x14 x15 x16 x17,
    Z.to_nat (n - p) = cnt -> INV m1 p ->
    x11 = Z_to_bv 64 (D + k + p) -> x15 = Z_to_bv 64 (D + p + 1) -> x16 = Z_to_bv 64 (D + p) ->
    evt ssegs POST (AT 0x20c84 m1 x5 x11 (Z_to_bv 64 (n - p)) x13 x14 x15 x16 x17).
  Proof using DB HK HN LEN. pin_using (fun (DB HK HN LEN : unit) => tt).
    induction cnt as [|cnt IH]; intros p m1 x5 x11 x13 x14 x15 x16 x17 Hc I -> -> ->;
      pose proof I as I0; destruct I0 as (REG & MI & _ & _ & Hp0).
    - zstep. if_cases K; zify_cond K; [|exfalso; lia]. apply mm_ret. replace n with p by lia. exact I.
    - zstep. if_cases K; zify_cond K. { apply mm_ret. replace n with p by lia. exact I. }
      destruct (mm_read1 m1 p I ltac:(lia)) as (b & Hnth & RD).
      replace (D + (k + p))%Z with (D + k + p)%Z in RD by lia.
      destruct (mm_store m1 p [b] I ltac:(cbn [length]; lia)
                  ltac:(cbn [length]; symmetry; apply nth_error_first1; rewrite <- Hnth; f_equal; lia)) as [SOK I2].
      cbn [length Z.of_nat Pos.of_succ_nat] in SOK, I2.
      zstep. zstep. zstep. zstep. zstep.
      zstep; [ mm_arr_store p [b] ltac:(apply le1_zxb) | .. ].
      zstep. zstep. zstep. zstep. if_cases Kal; zify_cond Kal.
      + replace (n - p + -1)%Z with (n - (p + 1))%Z by lia.
        apply (IH (p + 1)%Z); try reflexivity; try lia; try (f_equal; lia). exact I2.
      + zstep. replace (D + p + 1)%Z with (D + (p + 1))%Z by lia.
        replace (n - p + -1)%Z with (n - (p + 1))%Z by lia.
        apply (mm_wentry (p + 1)); try reflexivity; try (f_equal; lia). exact I2.
  Qed.
End Proofs.

Lemma firstn_skipn_mid : forall {X} (n k : nat) (l : list X), (n <= k <= length l)%nat ->
  skipn n l = skipn n (firstn k l) ++ skipn k l.
Proof.
  intros X n k l H. rewrite <- (firstn_skipn k l) at 1. rewrite skipn_app, length_firstn.
  rewrite Nat.min_l by lia. replace (n - k)%nat with 0%nat by lia. reflexivity.
Qed.

Definition memmove_spec__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (bs : list byte) (k n : Z),
  u8arr ssegs m (bv_unsigned a0) bs ->
  mem_inv ssegs m ->
  bv_unsigned a1 = (bv_unsigned a0 + k)%Z ->        (* [comment removed for export] *)
  a2 = Z_to_bv 64 n ->
  (1 <= k)%Z -> (0 <= n < 2^62)%Z -> length bs = Z.to_nat (k + n) ->
  evt ssegs (memmove_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 k n bs m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x20be4) fc None m (seg_rom ssegs)).
Section Sz25.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs k n : ltac2:(SecDiet.SzSec.tyM 'memmove_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
#[using="Type"] Lemma memmove_spec__body : ltac2:(SecDiet.SzSec.bodyP 'memmove_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
  intros REG MI HS -> Hk Hn LEN.
  pose proof (u8arr_bound _ _ _ _ REG) as B. rewrite LEN in B.
  pose proof (bv_unsigned_in_range 64 a1) as R1. unfold bv_modulus in R1. cbn in R1.
  assert (DB : (0 <= bv_unsigned a0 /\ bv_unsigned a0 + k + n <= 2^64)%Z) by lia.
  assert (I0 : INV a0 m bs k n m 0). { apply inv_init; fastfirst (first [ noevar_assumption |assumption | lia]). }
  zstep. if_cases K0; zify_cond K0. { exfalso. lia. }
  do 5 zstep. if_cases K1; zify_cond K1.
  - (* [comment removed for export] *)
    rewrite HS in K1. apply mm_test_taken in K1; try lia.
    step.
    (* [comment removed for export] *)
    destruct REG as [BY WR].
    rewrite <- (firstn_skipn (Z.to_nat n) bs) in BY. apply (proj1 (bytes_at_app _ _ _ _ _)) in BY. destruct BY as [BYD BY].
    rewrite length_firstn, Nat.min_l in BY by (rewrite LEN; lia).
    rewrite (firstn_skipn_mid (Z.to_nat n) (Z.to_nat k) bs) in BY by (rewrite LEN; lia).
    apply (proj1 (bytes_at_app _ _ _ _ _)) in BY. destruct BY as [GAP SRC].
    rewrite length_skipn, length_firstn, Nat.min_l in SRC by (rewrite LEN; lia).
    replace (bv_unsigned a0 + Z.of_nat (Z.to_nat n) + Z.of_nat (Z.to_nat k - Z.to_nat n))%Z with (bv_unsigned a1) in SRC by lia.
    assert (DST : rw_cells ssegs m (bv_unsigned a0) [CB (Z.to_nat n) (firstn (Z.to_nat n) bs)]).
    { pose proof (rw_cells_of_u8arr ssegs m (bv_unsigned a0) (firstn (Z.to_nat n) bs)) as X.
      rewrite length_firstn, Nat.min_l in X by (rewrite LEN; lia). apply X. split; [exact BYD|].
      rewrite length_firstn, Nat.min_l by (rewrite LEN; lia).
      apply (proj1 (proj1 (wr_at_app ssegs m (bv_unsigned a0) (Z.of_nat (Z.to_nat n)) (Z.of_nat (length bs) - Z.of_nat (Z.to_nat n)) ltac:(lia) ltac:(rewrite LEN; lia))
               ltac:(replace (Z.of_nat (Z.to_nat n) + (Z.of_nat (length bs) - Z.of_nat (Z.to_nat n)))%Z with (Z.of_nat (length bs)) by lia; exact WR))). }
    clear BYD.
    pose proof (munch_refl [(bv_unsigned a0, bv_unsigned a0 + n)]%Z m) as MU. pose proof (wmono_refl ssegs m) as WM.
    remember (Z_to_bv 64 n) as c2 eqn:Ec2.
    assert (Hc2 : bv_unsigned c2 = n) by (subst c2; apply unsigned_lit; lia).
    call memcpy_spec.
    1:{ exact SRC. } 1:{ rewrite length_skipn, LEN, Hc2. lia. } 1:{ rewrite Hc2. exact DST. } 1:{ rewrite Hc2. lia. } 1:{ exact MI. }
    unfold memmove_post. apply evt_done. do 15 eexists. split; [reflexivity|].
    rewrite Hc2 in *. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
    split.
    2:{ match goal with |- wr_at _ _ _ ?len => replace len with (Z.of_nat (length bs)); [assumption|] end.
        rewrite length_app, length_firstn, !length_skipn, LEN. lia. }
    rewrite (firstn_skipn_mid (Z.to_nat n) (Z.to_nat k) bs) by (rewrite LEN; lia).
    apply (proj2 (bytes_at_app _ _ _ _ _)). split.
    { lazymatch goal with H : rw_cells ssegs _ (bv_unsigned a0) [CB _ (skipn (Z.to_nat k) bs)] |- _ =>
        pose proof (rw_cells_bytes_at _ _ _ _ H) as X; cbn [cells_bytes cbytes] in X; rewrite app_nil_r in X end.
      rewrite firstn_all2 by (rewrite length_skipn, LEN; lia). exact X. }
    rewrite (firstn_all2 (skipn (Z.to_nat k) bs)) by (rewrite length_skipn, LEN; lia).
    rewrite length_skipn, LEN. replace (Z.of_nat (Z.to_nat (k + n) - Z.to_nat k)) with (Z.of_nat (Z.to_nat n)) by lia.
    apply (proj2 (bytes_at_app _ _ _ _ _)). split; [assumption|].
    match goal with |- bytes_at _ _ ?adr _ => replace adr with (bv_unsigned a1); [assumption|] end.
    rewrite length_skipn, length_firstn, LEN. lia.
  - rewrite HS in K1. apply mm_test_not_taken in K1; try lia.
    do 3 zstep. if_cases K2; zify_cond K2. { exfalso. lia. }
    zstep. if_cases K3; zify_cond K3.
    + (* [comment removed for export] *)
      rewrite HS in K3. apply (proj1 (land7_lxor (bv_unsigned a0 + k) (bv_unsigned a0) ltac:(lia) ltac:(lia))) in K3.
      zstep. zstep. if_cases K4; zify_cond K4.
      * do 2 zstep. replace (Z_to_bv 64 n) with (Z_to_bv 64 (n - 0)) by (f_equal; lia).
        eapply mm_wentry with (p := 0%Z); try eassumption; try lia; try (f_equal; lia);
          try (rewrite Z.add_0_r; symmetry; apply Z_to_bv_bv_unsigned);
          try (rewrite Z.add_0_r, <- HS; symmetry; apply Z_to_bv_bv_unsigned).
      * do 2 zstep. replace (Z_to_bv 64 n) with (Z_to_bv 64 (n - 0)) by (f_equal; lia).
        eapply mm_align with (p := 0%Z); try reflexivity; try eassumption; try lia; try (f_equal; lia);
          try (rewrite Z.add_0_r; symmetry; apply Z_to_bv_bv_unsigned);
          try (rewrite Z.add_0_r, <- HS; symmetry; apply Z_to_bv_bv_unsigned).
    + do 2 zstep. replace (Z_to_bv 64 n) with (Z_to_bv 64 (n - 0)) by (f_equal; lia).
      eapply mm_bytes_entry with (p := 0%Z); try eassumption; try lia; try (f_equal; lia);
        try (rewrite Z.add_0_r; symmetry; apply Z_to_bv_bv_unsigned);
        try (rewrite Z.add_0_r, <- HS; symmetry; apply Z_to_bv_bv_unsigned).
Qed.
End Sz25.
Lemma memmove_spec : ltac:(let t := eval cbv delta [memmove_spec__stmt] in memmove_spec__stmt in exact t).
Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs k n. ltac2:(SecDiet.SzSec.closeP 'memmove_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition memmove_entry := 0x213a4%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section ListFacts.
  Local Open Scope nat_scope.

  Definition mm_state (k p : nat) (bs : list byte) : list byte := firstn p (skipn k bs) ++ skipn p bs.

  #[using="Type"] Lemma mm_state_length : forall k p bs, p <= length bs -> k + p <= length bs -> length (mm_state k p bs) = length bs.
  Proof. intros. unfold mm_state. rewrite length_app, length_firstn, !length_skipn. lia. Qed.

  #[using="Type"] Lemma mm_state_0 : forall k bs, mm_state k 0 bs = bs.
  Proof. intros. reflexivity. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma mm_state_nth_hi : forall k p bs j, p <= j -> k + p <= length bs -> nth_error (mm_state k p bs) j = nth_error bs j.
  Proof.
    intros k p bs j Hj Hk. unfold mm_state.
    rewrite nth_error_app2 by (rewrite length_firstn, length_skipn; lia).
    rewrite length_firstn, length_skipn, Nat.min_l by lia. rewrite nth_error_skipn. f_equal. lia.
  Qed.

  #[using="Type"] Lemma mm_state_skipn_hi : forall k p bs j, p <= j -> k + p <= length bs -> skipn j (mm_state k p bs) = skipn j bs.
  Proof.
    intros k p bs j Hj Hk. unfold mm_state.
    rewrite skipn_app, length_firstn, length_skipn, Nat.min_l by lia.
    rewrite skipn_all2 by (rewrite length_firstn, length_skipn; lia). cbn [app].
    rewrite skipn_skipn. f_equal. lia.
  Qed.

  #[using="Type"] Lemma firstn_plus : forall {X} (a b : nat) (l : list X), firstn (a + b) l = firstn a l ++ firstn b (skipn a l).
  Proof.
    intros X a. induction a as [|a IH]; intros b l; [reflexivity|].
    destruct l as [|x l]; cbn; [now destruct b|]. rewrite IH. reflexivity.
  Qed.

  #[using="Type"] Lemma skipn_skipn' : forall {X} (a b : nat) (l : list X), skipn a (skipn b l) = skipn (b + a) l.
  Proof. intros X a b l. revert l. induction b as [|b IH]; intros l; [reflexivity|]. destruct l; cbn; [now destruct a| apply IH]. Qed.

  (* [comment removed for export] *)
  Definition mm_state_upd__stmt : Prop := forall k p bs xs,
    k + p + length xs <= length bs -> xs = firstn (length xs) (skipn (k + p) bs) ->
    upd_bytes (mm_state k p bs) p xs = mm_state k (p + length xs) bs.
  Section Sz7.
  Variables k p bs xs : ltac2:(SecDiet.SzSec.tyM 'mm_state_upd__stmt "vvvv" @k).
  #[using="Type"] Lemma mm_state_upd__body : ltac2:(SecDiet.SzSec.bodyP 'mm_state_upd__stmt "vvvv").
  Proof.
    intros Hl Hxs.
 unfold upd_bytes, mm_state.
    assert (LA : length (firstn p (skipn k bs)) = p) by (rewrite length_firstn, length_skipn; lia).
    rewrite firstn_app, LA, Nat.sub_diag, firstn_O, app_nil_r.
    rewrite (firstn_all2 (firstn p (skipn k bs))) by (rewrite LA; lia).
    rewrite skipn_app, LA. rewrite (skipn_all2 (firstn p (skipn k bs))) by (rewrite LA; lia). cbn [app].
    rewrite skipn_skipn'. replace (p + (p + length xs - p)) with (p + length xs) by lia.
    rewrite app_assoc. f_equal.
    rewrite firstn_plus. f_equal. rewrite skipn_skipn'. exact Hxs.
  Qed.
  End Sz7.
  #[using="Type"] Lemma mm_state_upd : ltac:(let t := eval cbv delta [mm_state_upd__stmt] in mm_state_upd__stmt in exact t).
  Proof. intros k p bs xs. ltac2:(SecDiet.SzSec.closeP 'mm_state_upd__body "vvvv"). Qed.

  #[using="Type"] Lemma mm_state_all : forall k n bs, mm_state k n bs = firstn n (skipn k bs) ++ skipn n bs.
  Proof. reflexivity. Qed.
End ListFacts.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section ZFacts.
  Local Open Scope Z_scope.
  Notation M64 := 18446744073709551616.

  (* [comment removed for export] *)
  Definition mm_test_taken__stmt : Prop := forall D k n, 0 <= D -> 1 <= k -> 0 <= n < 2^62 -> D + k + n <= 2^64 -> D + k < 2^64 ->
    (D + k - (n + D)) mod M64 <= (0 - (Z.shiftl n 1) mod M64) mod M64 -> 1 <= n <= k.
  Section Sz9.
  Variables D k n : ltac2:(SecDiet.SzSec.tyM 'mm_test_taken__stmt "vvv" @D).
  #[using="Type"] Lemma mm_test_taken__body : ltac2:(SecDiet.SzSec.bodyP 'mm_test_taken__stmt "vvv").
  Proof.
    intros HD Hk Hn HB HB2 H.
 rewrite Z.shiftl_mul_pow2 in H by lia. change (2^1) with 2 in H.
    rewrite (Z.mod_small (n * 2)) in H by lia.
    destruct (Z.eq_dec n 0) as [->|Hn0].
    { exfalso. rewrite (Z.mod_small (D + k - (0 + D))) in H by lia. change ((0 - 0 * 2) mod M64) with 0 in H. lia. }
    replace ((0 - n * 2) mod M64) with (M64 - n * 2) in H.
    2:{ replace (0 - n * 2) with ((M64 - n * 2) + (-1) * M64) by lia. rewrite Z.mod_add by lia. symmetry. apply Z.mod_small. lia. }
    destruct (Z.lt_ge_cases k n); [|lia]. exfalso.
    replace ((D + k - (n + D)) mod M64) with (M64 + k - n) in H; [lia|].
    replace (D + k - (n + D)) with ((M64 + k - n) + (-1) * M64) by lia. rewrite Z.mod_add by lia. symmetry. apply Z.mod_small. lia.
  Qed.
  End Sz9.
  #[using="Type"] Lemma mm_test_taken : ltac:(let t := eval cbv delta [mm_test_taken__stmt] in mm_test_taken__stmt in exact t).
  Proof. intros D k n. ltac2:(SecDiet.SzSec.closeP 'mm_test_taken__body "vvv"). Qed.

  Definition mm_test_not_taken__stmt : Prop := forall D k n, 0 <= D -> 1 <= k -> 0 <= n < 2^62 -> D + k + n <= 2^64 -> D + k < 2^64 ->
    (0 - (Z.shiftl n 1) mod M64) mod M64 < (D + k - (n + D)) mod M64 -> n = 0 \/ k < n.
  Section Sz10.
  Variables D k n : ltac2:(SecDiet.SzSec.tyM 'mm_test_not_taken__stmt "vvv" @D).
  #[using="Type"] Lemma mm_test_not_taken__body : ltac2:(SecDiet.SzSec.bodyP 'mm_test_not_taken__stmt "vvv").
  Proof.
    intros HD Hk Hn HB HB2 H.
 rewrite Z.shiftl_mul_pow2 in H by lia. change (2^1) with 2 in H.
    rewrite (Z.mod_small (n * 2)) in H by lia.
    destruct (Z.eq_dec n 0) as [->|Hn0]; [left; reflexivity| right].
    replace ((0 - n * 2) mod M64) with (M64 - n * 2) in H.
    2:{ replace (0 - n * 2) with ((M64 - n * 2) + (-1) * M64) by lia. rewrite Z.mod_add by lia. symmetry. apply Z.mod_small. lia. }
    destruct (Z.lt_ge_cases k n); [assumption|]. exfalso.
    rewrite Z.mod_small in H by lia. lia.
  Qed.
  End Sz10.
  #[using="Type"] Lemma mm_test_not_taken : ltac:(let t := eval cbv delta [mm_test_not_taken__stmt] in mm_test_not_taken__stmt in exact t).
  Proof. intros D k n. ltac2:(SecDiet.SzSec.closeP 'mm_test_not_taken__body "vvv"). Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma land_lxor_distr : forall a b c, Z.land (Z.lxor a b) c = Z.lxor (Z.land a c) (Z.land b c).
  Proof.
    intros. apply Z.bits_inj'. intros i Hi.
    rewrite Z.land_spec, !Z.lxor_spec, !Z.land_spec. destruct (Z.testbit a i), (Z.testbit b i), (Z.testbit c i); reflexivity.
  Qed.

  #[using="Type"] Lemma land7_lxor : forall a b, 0 <= a -> 0 <= b -> (Z.land (Z.lxor a b) 7 = 0 <-> a mod 8 = b mod 8).
  Proof.
    intros a b Ha Hb. rewrite land_lxor_distr.
    change 7 with (Z.ones 3). rewrite !Z.land_ones by lia. change (2^3) with 8.
    split.
    - intros H. apply Z.lxor_eq in H. exact H.
    - intros H. rewrite H. apply Z.lxor_nilpotent.
  Qed.
End ZFacts.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition memmove_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 : word) (k n : Z) (bs : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned a0, bv_unsigned a0 + n)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ u8arr usegs m' (bv_unsigned a0) (firstn (Z.to_nat n) (skipn (Z.to_nat k) bs) ++ skipn (Z.to_nat n) bs).

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (k n : Z).
  Notation D := (bv_unsigned a0).
  Notation kn := (Z.to_nat k).
  Hypothesis LEN : length bs = Z.to_nat (k + n).
  Hypothesis HK : (1 <= k)%Z.
  Hypothesis HN : (0 <= n < 2^62)%Z.
  Hypothesis DB : (0 <= D /\ D + k + n <= 2^64)%Z.

  Notation POST := (memmove_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 k n bs m).
  (* [comment removed for export] *)
  Notation AT pc mm x5 x11 x12 x13 x14 x15 x16 x17 :=
    (MS (mkR ra sp gp tp x5 t1 t2 s0 s1 a0 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition INV (m1 : word -> option byte) (p : Z) : Prop :=
    u8arr usegs m1 D (mm_state kn (Z.to_nat p) bs) /\ mem_inv usegs m1 /\
    munch [(D, D + n)]%Z m m1 /\ wmono usegs m m1 /\ (0 <= p <= n)%Z.

  Lemma inv_init : u8arr usegs m D bs -> mem_inv usegs m -> INV m 0.
  Proof using HN LEN. pin_using (fun (HN LEN : unit) => tt).
    intros REG MI. split; [rewrite mm_state_0; exact REG|]. split; [exact MI|].
    split; [apply munch_refl|]. split; [apply wmono_refl| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma mm_ret : forall m1 x5 x11 x12 x13 x14 x15 x16 x17, INV m1 n ->
    evt usegs POST (AT 0x21430 m1 x5 x11 x12 x13 x14 x15 x16 x17).
  Proof using Type. pin_using tt.
    intros m1 x5 x11 x12 x13 x14 x15 x16 x17 (REG & MI & MU & WM & _).
    step. unfold memmove_post. finish.
  Qed.

  (* [comment removed for export] *)
  Definition mm_read1__stmt : Prop := forall m1 p, INV m1 p -> (p < n)%Z ->
    exists b, nth_error bs (Z.to_nat (k + p)) = Some b /\ ov_read_bytes usegs m1 (wa (D + (k + p))) 1 = Some [b].
  Section Sz15.
  Variables m1 p : ltac2:(SecDiet.SzSec.tyM 'mm_read1__stmt "vv" @m1).
  Lemma mm_read1__body : ltac2:(SecDiet.SzSec.bodyP 'mm_read1__stmt "vv").
  Proof using HK LEN. pin_using (fun (HK LEN : unit) => tt).
    intros (REG & _ & _ & _ & Hp) Hpn.
    destruct (nth_error bs (Z.to_nat (k + p))) as [b|] eqn:E.
    2:{ exfalso. apply nth_error_None in E. lia. }
    exists b. split; [reflexivity|].
    apply (u8arr_read usegs m1 D _ (k + p) b _ REG); [|lia|reflexivity].
    rewrite mm_state_nth_hi; [exact E| lia | rewrite LEN; lia].
  Qed.
  End Sz15.
  Lemma mm_read1 : ltac:(let t := eval cbv delta [mm_read1__stmt] in mm_read1__stmt in exact t).
  Proof using HK LEN. intros m1 p. ltac2:(SecDiet.SzSec.closeP 'mm_read1__body "vv"). Qed.

  (* [comment removed for export] *)
  Definition mm_store__stmt : Prop := forall m1 p xs,
    INV m1 p -> (p + Z.of_nat (length xs) <= n)%Z -> xs = firstn (length xs) (skipn (Z.to_nat (k + p)) bs) ->
    store_ok usegs m1 (wa (D + p)) (length xs) = true /\
    INV (write_to_mem m1 (wa (D + p)) xs) (p + Z.of_nat (length xs)).
  Section Sz16.
  Variables m1 p xs : ltac2:(SecDiet.SzSec.tyM 'mm_store__stmt "vvv" @m1).
  Lemma mm_store__body : ltac2:(SecDiet.SzSec.bodyP 'mm_store__stmt "vvv").
  Proof using DB HK HN LEN. pin_using (fun (DB HK HN LEN : unit) => tt).
    intros (REG & MI & MU & WM & Hp) Hpn Hxs.
    assert (L1 : length (mm_state kn (Z.to_nat p) bs) = length bs) by (apply mm_state_length; rewrite LEN; lia).
    assert (SOK : store_ok usegs m1 (wa (D + p)) (length xs) = true).
    { eapply (u8arr_store_ok_n usegs m1 D _ p (length xs) _ REG); [lia| rewrite L1, LEN; lia | reflexivity]. }
    split; [exact SOK|]. split; [|split; [|split; [|split]]].
    - pose proof (u8arr_write_bytes usegs m1 D _ p xs REG ltac:(lia) ltac:(rewrite L1, LEN; lia)) as REG'.
      rewrite mm_state_upd in REG'; [| rewrite LEN; lia | rewrite Hxs at 1; f_equal; f_equal; lia].
      replace (Z.to_nat p + length xs)%nat with (Z.to_nat (p + Z.of_nat (length xs))) in REG' by lia. exact REG'.
    - apply mem_inv_store; assumption.
    - apply munch_write; [exact MU | lia | lia |]. cbn [inside]. left. lia.
    - apply wmono_write. exact WM.
    - lia.
  Qed.
  End Sz16.
  Lemma mm_store : ltac:(let t := eval cbv delta [mm_store__stmt] in mm_store__stmt in exact t).
  Proof using DB HK HN LEN. intros m1 p xs. ltac2:(SecDiet.SzSec.closeP 'mm_store__body "vvv"). Qed.

  (* [comment removed for export] *)
  Lemma le8_ld : forall w : list byte, length w = 8%nat -> le8 (bv_extract 0 64 (le_bytes_to_word w)) = w.
  Proof using Type. pin_using tt.
    intros w Hl. unfold le8, word_to_le_bytes. rewrite load8_le_val by exact Hl.
    rewrite <- bytes_le_to_Z_le_val, <- Hl. apply Z_to_le_bytes_to_Z.
  Qed.

  (* [comment removed for export] *)
  Ltac mm_arr_store p xs bytes_tac :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m1 ?a ?bs0) _) =>
      replace (write_to_mem m1 a bs0) with (write_to_mem m1 (wa (D + p)%Z) xs)
        by (apply (f_equal2 (write_to_mem m1)); [ unfold wa; fastfirst (first [ noevar_assumption |reflexivity | f_equal; lia]) | first [bytes_tac | symmetry; bytes_tac] ]);
      repeat match goal with
      | H : store_ok usegs m1 _ _ = true |- _ => clear H
      | H : ov_read_bytes usegs m1 _ _ = Some _ |- _ => clear H
      | H : INV m1 _ |- _ => clear H
      | H : mem_inv usegs m1 |- _ => clear H
      | H : u8arr usegs m1 _ _ |- _ => clear H
      end;
      let m' := fresh "m" in remember (write_to_mem m1 (wa (D + p)%Z) xs) as m' eqn:Heqm; clear Heqm; try clear m1
    end.

  (* [comment removed for export] *)
  Lemma mm_bytes : forall (cnt : nat) (p : Z) m1 x5 x11 x13 x14 x15 x16 x17,
    Z.to_nat (n - p) = cnt -> (p < n)%Z -> INV m1 p ->
    x13 = Z_to_bv 64 (D + p) -> x14 = Z_to_bv 64 (D + k + p) ->
    evt usegs POST (AT 0x213dc m1 x5 x11 (Z_to_bv 64 (D + n)) x13 x14 x15 x16 x17).
  Proof using DB HK HN LEN. pin_using (fun (DB HK HN LEN : unit) => tt).
    induction cnt as [|cnt IH]; intros p m1 x5 x11 x13 x14 x15 x16 x17 Hc Hp I -> ->; [lia|].
    pose proof I as I0. destruct I0 as (REG & MI & _ & _ & Hp0).
    destruct (mm_read1 m1 p I Hp) as (b & Hnth & RD).
    replace (D + (k + p))%Z with (D + k + p)%Z in RD by lia.
    destruct (mm_store m1 p [b] I ltac:(cbn [length]; lia)
                ltac:(cbn [length]; symmetry; apply nth_error_first1; rewrite <- Hnth; f_equal; lia)) as [SOK I2].
    cbn [length Z.of_nat Pos.of_succ_nat] in SOK, I2.
    zstep. zstep. zstep.
    zstep; [ mm_arr_store p [b] ltac:(apply le1_zxb) | .. ].
    zstep. zstep. if_cases K; zify_cond K.
    - apply (IH (p + 1)%Z); try reflexivity; try lia; try (f_equal; lia). exact I2.
    - zstep. apply mm_ret. replace n with (p + 1)%Z by lia. exact I2.
  Qed.

  (* [comment removed for export] *)
  Lemma mm_bytes_entry : forall (p : Z) m1 x5 x11 x13 x14 x15 x16 x17,
    INV m1 p -> x13 = Z_to_bv 64 (D + p) -> x14 = Z_to_bv 64 (D + k + p) ->
    evt usegs POST (AT 0x213d4 m1 x5 x11 (Z_to_bv 64 (n - p)) x13 x14 x15 x16 x17).
  Proof using DB HK HN LEN. pin_using (fun (DB HK HN LEN : unit) => tt).
    intros p m1 x5 x11 x13 x14 x15 x16 x17 I -> ->. pose proof I as I0. destruct I0 as (REG & MI & _ & _ & Hp0).
    zstep. if_cases K; zify_cond K.
    - apply mm_ret. replace n with p by lia. exact I.
    - zstep. replace (D + p + (n - p))%Z with (D + n)%Z by lia.
      apply (mm_bytes (Z.to_nat (n - p)) p); try reflexivity; try lia. exact I.
  Qed.

  (* [comment removed for export] *)
  Lemma mm_read8 : forall m1 p, INV m1 p -> (p + 8 <= n)%Z ->
    ov_read_bytes usegs m1 (wa (D + (k + p))) 8 = Some (firstn 8 (skipn (Z.to_nat (k + p)) bs)).
  Proof using HK LEN. pin_using (fun (HK LEN : unit) => tt).
    intros m1 p (REG & _ & _ & _ & Hp) Hpn.
    assert (L1 : length (mm_state kn (Z.to_nat p) bs) = length bs) by (apply mm_state_length; rewrite LEN; lia).
    rewrite <- (mm_state_skipn_hi kn (Z.to_nat p) bs (Z.to_nat (k + p))) by (rewrite ?LEN; lia).
    apply (bytes_at_read usegs m1 D _ (k + p) 8 (proj1 REG)); [lia|]. rewrite L1, LEN. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma mm_words : forall (cnt : nat) (p : Z) m1 x5 x13 x14 x15 x16 x17,
    Z.to_nat (n - p) = cnt -> (p + 8 <= n)%Z -> INV m1 p ->
    x13 = Z_to_bv 64 (D + p) -> x14 = Z_to_bv 64 (D + k + p) ->
    evt usegs POST (AT 0x21504 m1 x5 (Z_to_bv 64 7) (Z_to_bv 64 (n - p)) x13 x14 x15 x16 x17).
  Proof using DB HK HN LEN. pin_using (fun (DB HK HN LEN : unit) => tt).
    induction cnt as [cnt IH] using lt_wf_ind; intros p m1 x5 x13 x14 x15 x16 x17 Hc Hp I -> ->.
    pose proof I as I0. destruct I0 as (REG & MI & _ & _ & Hp0).
    pose proof (mm_read8 m1 p I Hp) as RD. replace (D + (k + p))%Z with (D + k + p)%Z in RD by lia.
    set (chunk := firstn 8 (skipn (Z.to_nat (k + p)) bs)) in RD.
    assert (CL : length chunk = 8%nat) by (subst chunk; rewrite length_firstn, length_skipn, LEN; lia).
    destruct (mm_store m1 p chunk I ltac:(rewrite CL; cbn; lia) ltac:(rewrite CL; reflexivity)) as [SOK I2].
    rewrite CL in SOK, I2. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in I2.
    zstep. zstep.
    zstep; [ mm_arr_store p chunk ltac:(apply le8_ld; exact CL) | .. ].
    zstep. zstep. zstep. if_cases K; zify_cond K.
    - replace (n - p + -8)%Z with (n - (p + 8))%Z by lia.
      apply (IH (Z.to_nat (n - (p + 8))) ltac:(lia) (p + 8)%Z); try reflexivity; try lia; try (f_equal; lia). exact I2.
    - zstep. replace (n - p + -8)%Z with (n - (p + 8))%Z by lia.
      apply (mm_bytes_entry (p + 8)); try reflexivity; try (f_equal; lia). exact I2.
  Qed.

  (* [comment removed for export] *)
  Lemma mm_wentry : forall (p : Z) m1 x5 x11 x13 x14 x15 x16 x17,
    INV m1 p -> x13 = Z_to_bv 64 (D + p) -> x14 = Z_to_bv 64 (D + k + p) ->
    evt usegs POST (AT 0x214f8 m1 x5 x11 (Z_to_bv 64 (n - p)) x13 x14 x15 x16 x17).
  Proof using DB HK HN LEN. pin_using (fun (DB HK HN LEN : unit) => tt).
    intros p m1 x5 x11 x13 x14 x15 x16 x17 I -> ->. pose proof I as I0. destruct I0 as (REG & MI & _ & _ & Hp0).
    zstep. zstep. if_cases K; zify_cond K.
    - apply (mm_bytes_entry p); try reflexivity. exact I.
    - zstep. apply (mm_words (Z.to_nat (n - p)) p); try reflexivity; try lia. exact I.
  Qed.

  (* [comment removed for export] *)
  Lemma mm_align : forall (cnt : nat) (p : Z) m1 x5 x11 x13 x14 x15 x16 x17,
    Z.to_nat (n - p) = cnt -> INV m1 p ->
    x11 = Z_to_bv 64 (D + k + p) -> x15 = Z_to_bv 64 (D + p + 1) -> x16 = Z_to_bv 64 (D + p) ->
    evt usegs POST (AT 0x21444 m1 x5 x11 (Z_to_bv 64 (n - p)) x13 x14 x15 x16 x17).
  Proof using DB HK HN LEN. pin_using (fun (DB HK HN LEN : unit) => tt).
    induction cnt as [|cnt IH]; intros p m1 x5 x11 x13 x14 x15 x16 x17 Hc I -> -> ->;
      pose proof I as I0; destruct I0 as (REG & MI & _ & _ & Hp0).
    - zstep. if_cases K; zify_cond K; [|exfalso; lia]. apply mm_ret. replace n with p by lia. exact I.
    - zstep. if_cases K; zify_cond K. { apply mm_ret. replace n with p by lia. exact I. }
      destruct (mm_read1 m1 p I ltac:(lia)) as (b & Hnth & RD).
      replace (D + (k + p))%Z with (D + k + p)%Z in RD by lia.
      destruct (mm_store m1 p [b] I ltac:(cbn [length]; lia)
                  ltac:(cbn [length]; symmetry; apply nth_error_first1; rewrite <- Hnth; f_equal; lia)) as [SOK I2].
      cbn [length Z.of_nat Pos.of_succ_nat] in SOK, I2.
      zstep. zstep. zstep. zstep. zstep.
      zstep; [ mm_arr_store p [b] ltac:(apply le1_zxb) | .. ].
      zstep. zstep. zstep. zstep. if_cases Kal; zify_cond Kal.
      + replace (n - p + -1)%Z with (n - (p + 1))%Z by lia.
        apply (IH (p + 1)%Z); try reflexivity; try lia; try (f_equal; lia). exact I2.
      + zstep. replace (D + p + 1)%Z with (D + (p + 1))%Z by lia.
        replace (n - p + -1)%Z with (n - (p + 1))%Z by lia.
        apply (mm_wentry (p + 1)); try reflexivity; try (f_equal; lia). exact I2.
  Qed.
End Proofs.

Lemma firstn_skipn_mid : forall {X} (n k : nat) (l : list X), (n <= k <= length l)%nat ->
  skipn n l = skipn n (firstn k l) ++ skipn k l.
Proof.
  intros X n k l H. rewrite <- (firstn_skipn k l) at 1. rewrite skipn_app, length_firstn.
  rewrite Nat.min_l by lia. replace (n - k)%nat with 0%nat by lia. reflexivity.
Qed.

Definition memmove_spec__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (bs : list byte) (k n : Z),
  u8arr usegs m (bv_unsigned a0) bs ->
  mem_inv usegs m ->
  bv_unsigned a1 = (bv_unsigned a0 + k)%Z ->        (* [comment removed for export] *)
  a2 = Z_to_bv 64 n ->
  (1 <= k)%Z -> (0 <= n < 2^62)%Z -> length bs = Z.to_nat (k + n) ->
  evt usegs (memmove_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 k n bs m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x213a4) fc None m (seg_rom usegs)).
Section Sz25.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs k n : ltac2:(SecDiet.SzSec.tyM 'memmove_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
#[using="Type"] Lemma memmove_spec__body : ltac2:(SecDiet.SzSec.bodyP 'memmove_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
 intros REG MI HS -> Hk Hn LEN.
  pose proof (u8arr_bound _ _ _ _ REG) as B. rewrite LEN in B.
  pose proof (bv_unsigned_in_range 64 a1) as R1. unfold bv_modulus in R1. cbn in R1.
  assert (DB : (0 <= bv_unsigned a0 /\ bv_unsigned a0 + k + n <= 2^64)%Z) by lia.
  assert (I0 : INV a0 m bs k n m 0). { apply inv_init; fastfirst (first [ noevar_assumption |assumption | lia]). }
  zstep. if_cases K0; zify_cond K0. { exfalso. lia. }
  do 5 zstep. if_cases K1; zify_cond K1.
  - (* [comment removed for export] *)
    rewrite HS in K1. apply mm_test_taken in K1; try lia.
    step.
    (* [comment removed for export] *)
    destruct REG as [BY WR].
    rewrite <- (firstn_skipn (Z.to_nat n) bs) in BY. apply (proj1 (bytes_at_app _ _ _ _ _)) in BY. destruct BY as [BYD BY].
    rewrite length_firstn, Nat.min_l in BY by (rewrite LEN; lia).
    rewrite (firstn_skipn_mid (Z.to_nat n) (Z.to_nat k) bs) in BY by (rewrite LEN; lia).
    apply (proj1 (bytes_at_app _ _ _ _ _)) in BY. destruct BY as [GAP SRC].
    rewrite length_skipn, length_firstn, Nat.min_l in SRC by (rewrite LEN; lia).
    replace (bv_unsigned a0 + Z.of_nat (Z.to_nat n) + Z.of_nat (Z.to_nat k - Z.to_nat n))%Z with (bv_unsigned a1) in SRC by lia.
    assert (DST : rw_cells usegs m (bv_unsigned a0) [CB (Z.to_nat n) (firstn (Z.to_nat n) bs)]).
    { pose proof (rw_cells_of_u8arr usegs m (bv_unsigned a0) (firstn (Z.to_nat n) bs)) as X.
      rewrite length_firstn, Nat.min_l in X by (rewrite LEN; lia). apply X. split; [exact BYD|].
      rewrite length_firstn, Nat.min_l by (rewrite LEN; lia).
      apply (proj1 (proj1 (wr_at_app usegs m (bv_unsigned a0) (Z.of_nat (Z.to_nat n)) (Z.of_nat (length bs) - Z.of_nat (Z.to_nat n)) ltac:(lia) ltac:(rewrite LEN; lia))
               ltac:(replace (Z.of_nat (Z.to_nat n) + (Z.of_nat (length bs) - Z.of_nat (Z.to_nat n)))%Z with (Z.of_nat (length bs)) by lia; exact WR))). }
    clear BYD.
    pose proof (munch_refl [(bv_unsigned a0, bv_unsigned a0 + n)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    remember (Z_to_bv 64 n) as c2 eqn:Ec2.
    assert (Hc2 : bv_unsigned c2 = n) by (subst c2; apply unsigned_lit; lia).
    call memcpy_spec.
    1:{ exact SRC. } 1:{ rewrite length_skipn, LEN, Hc2. lia. } 1:{ rewrite Hc2. exact DST. } 1:{ rewrite Hc2. lia. } 1:{ exact MI. }
    unfold memmove_post. apply evt_done. do 15 eexists. split; [reflexivity|].
    rewrite Hc2 in *. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
    split.
    2:{ match goal with |- wr_at _ _ _ ?len => replace len with (Z.of_nat (length bs)); [assumption|] end.
        rewrite length_app, length_firstn, !length_skipn, LEN. lia. }
    rewrite (firstn_skipn_mid (Z.to_nat n) (Z.to_nat k) bs) by (rewrite LEN; lia).
    apply (proj2 (bytes_at_app _ _ _ _ _)). split.
    { lazymatch goal with H : rw_cells usegs _ (bv_unsigned a0) [CB _ (skipn (Z.to_nat k) bs)] |- _ =>
        pose proof (rw_cells_bytes_at _ _ _ _ H) as X; cbn [cells_bytes cbytes] in X; rewrite app_nil_r in X end.
      rewrite firstn_all2 by (rewrite length_skipn, LEN; lia). exact X. }
    rewrite (firstn_all2 (skipn (Z.to_nat k) bs)) by (rewrite length_skipn, LEN; lia).
    rewrite length_skipn, LEN. replace (Z.of_nat (Z.to_nat (k + n) - Z.to_nat k)) with (Z.of_nat (Z.to_nat n)) by lia.
    apply (proj2 (bytes_at_app _ _ _ _ _)). split; [assumption|].
    match goal with |- bytes_at _ _ ?adr _ => replace adr with (bv_unsigned a1); [assumption|] end.
    rewrite length_skipn, length_firstn, LEN. lia.
  - rewrite HS in K1. apply mm_test_not_taken in K1; try lia.
    do 3 zstep. if_cases K2; zify_cond K2. { exfalso. lia. }
    zstep. if_cases K3; zify_cond K3.
    + (* [comment removed for export] *)
      rewrite HS in K3. apply (proj1 (land7_lxor (bv_unsigned a0 + k) (bv_unsigned a0) ltac:(lia) ltac:(lia))) in K3.
      zstep. zstep. if_cases K4; zify_cond K4.
      * do 2 zstep. replace (Z_to_bv 64 n) with (Z_to_bv 64 (n - 0)) by (f_equal; lia).
        eapply mm_wentry with (p := 0%Z); try eassumption; try lia; try (f_equal; lia);
          try (rewrite Z.add_0_r; symmetry; apply Z_to_bv_bv_unsigned);
          try (rewrite Z.add_0_r, <- HS; symmetry; apply Z_to_bv_bv_unsigned).
      * do 2 zstep. replace (Z_to_bv 64 n) with (Z_to_bv 64 (n - 0)) by (f_equal; lia).
        eapply mm_align with (p := 0%Z); try reflexivity; try eassumption; try lia; try (f_equal; lia);
          try (rewrite Z.add_0_r; symmetry; apply Z_to_bv_bv_unsigned);
          try (rewrite Z.add_0_r, <- HS; symmetry; apply Z_to_bv_bv_unsigned).
    + do 2 zstep. replace (Z_to_bv 64 n) with (Z_to_bv 64 (n - 0)) by (f_equal; lia).
      eapply mm_bytes_entry with (p := 0%Z); try eassumption; try lia; try (f_equal; lia);
        try (rewrite Z.add_0_r; symmetry; apply Z_to_bv_bv_unsigned);
        try (rewrite Z.add_0_r, <- HS; symmetry; apply Z_to_bv_bv_unsigned).
Qed.
End Sz25.
Lemma memmove_spec : ltac:(let t := eval cbv delta [memmove_spec__stmt] in memmove_spec__stmt in exact t).
Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs k n. ltac2:(SecDiet.SzSec.closeP 'memmove_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End TwB.
End F_memmove.

(* [comment removed for export] *)
Module F_strchr.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Bytes SysStep ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.F_strlen OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.F_memchr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition strchrnul_entry := 0x20e94%Z.
Definition strchr_entry := 0x20e58%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition strchrnul_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 : word) (str slack : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
                 (Z_to_bv 64 (bv_unsigned a0 + Z.of_nat (strchrnul_idx (bv_unsigned a1 mod 256) str)))
                 a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ssegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
    /\ stk ssegs m' lo (bv_unsigned sp)
    /\ bytes_at ssegs m' (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack).

Section StrchrnulProof.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m m1 : word -> option byte) (str slack : list byte) (lo : Z).
  (* [comment removed for export] *)
  Hypothesis MI : mem_inv ssegs m1.
  Hypothesis STR : bytes_at ssegs m1 (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack).
  Hypothesis NONUL : ~ In (Z_to_bv 8 0) str.
  Hypothesis PAD : ((- (bv_unsigned a0 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z.
  Hypothesis MU : munch [(bv_unsigned sp + -16, bv_unsigned sp)]%Z m m1.
  Hypothesis WM : wmono ssegs m m1.
  Hypothesis ST : stk ssegs m1 lo (bv_unsigned sp + -16).
  Hypothesis FR : rw_cells ssegs m1 (bv_unsigned sp + -16) [C8 s0; C8 ra].
  Hypothesis LO : (0 <= lo <= bv_unsigned sp - 16)%Z.
  Hypothesis SPR : (bv_unsigned sp < 2^64)%Z.

  Notation A := (bv_unsigned a0).
  Notation c := ((bv_unsigned a1) mod 256)%Z.
  Notation len := (Z.of_nat (length str)).
  Notation full := (str ++ Z_to_bv 8 0 :: slack).
  Notation POST := (strchrnul_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 str slack lo m).
  (* [comment removed for export] *)
  Notation AT pc xra xs0 x10 x12 x13 x14 x15 x16 x17 :=
    (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 xs0 s1 x10 (Z_to_bv 64 c) x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m1 (seg_rom ssegs)).
  Notation CMAGIC := 72340172838076672%Z.      (* [comment removed for export] *)
  Notation HIGHS := 9259542123273814144%Z.     (* [comment removed for export] *)
  Notation ONES := 72340172838076673%Z.       (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition NOB (i : Z) : Prop :=
    forall j b, (j < Z.to_nat i)%nat -> nth_error str j = Some b -> bv_unsigned b <> c.

  Lemma full_length : length full = (length str + S (length slack))%nat.
  Proof using a0. pin_using (fun (a0 : unit) => tt). rewrite length_app. cbn. lia. Qed.

  Lemma A_bound : (0 <= A /\ A + len + 1 + Z.of_nat (length slack) <= 2^64 /\ 0 <= c < 256)%Z.
  Proof using STR. pin_using (fun (STR : unit) => tt).
    pose proof (bytes_at_bound _ _ _ _ STR) as B. rewrite full_length in B.
    pose proof (Z.mod_pos_bound (bv_unsigned a1) 256). lia.
  Qed.

  Lemma full_nth_lt : forall i, (0 <= i < len)%Z ->
    exists b, nth_error full (Z.to_nat i) = Some b /\ nth_error str (Z.to_nat i) = Some b /\ bv_unsigned b <> 0%Z.
  Proof using NONUL a0. pin_using (fun (NONUL a0 : unit) => tt).
    intros i Hi. destruct (nth_error str (Z.to_nat i)) as [b|] eqn:E.
    - exists b. split. { rewrite nth_error_app1 by lia. exact E. } split; [reflexivity|].
      intros Hb. apply NONUL. replace (Z_to_bv 8 0) with b. { eapply nth_error_In; eauto. }
      apply bv_eq. rewrite Hb. reflexivity.
    - apply nth_error_None in E. lia.
  Qed.

  Lemma full_nth_len : nth_error full (Z.to_nat len) = Some (Z_to_bv 8 0).
  Proof using a0. pin_using (fun (a0 : unit) => tt). rewrite nth_error_app2, Nat2Z.id, Nat.sub_diag by lia. reflexivity. Qed.

  Lemma NOB_0 : NOB 0.
  Proof using Type. pin_using tt. intros j b Hj. exfalso. exact (Nat.nlt_0_r _ Hj). Qed.

  Lemma NOB_S : forall i b, (0 <= i)%Z -> NOB i -> nth_error str (Z.to_nat i) = Some b -> bv_unsigned b <> c -> NOB (i + 1).
  Proof using a0 slack. pin_using (fun (a0 slack : unit) => tt).
    intros i b Hi H Hn Hb j b' Hj Hn'.
    destruct (Nat.eq_dec j (Z.to_nat i)) as [->|NE]. { rewrite Hn in Hn'. injection Hn' as <-. exact Hb. }
    eapply H; [|exact Hn']. lia.
  Qed.

  Lemma idx_found : forall i b, (0 <= i < len)%Z -> NOB i -> nth_error str (Z.to_nat i) = Some b -> bv_unsigned b = c ->
    Z.of_nat (strchrnul_idx c str) = i.
  Proof using a0 slack. pin_using (fun (a0 slack : unit) => tt).
    intros i b Hi HN Hn Hb. unfold strchrnul_idx.
    rewrite (find_byte_charact c str (Z.to_nat i) b Hn Hb). { lia. }
    intros j b' Hj Hn'. exact (HN _ _ Hj Hn').
  Qed.

  Lemma idx_end : NOB len -> Z.of_nat (strchrnul_idx c str) = len.
  Proof using a0 slack. pin_using (fun (a0 slack : unit) => tt).
    intros HN. unfold strchrnul_idx. rewrite find_byte_None_intro; [reflexivity|].
    intros j b Hn. apply (HN j b); [|exact Hn]. apply nth_error_lt in Hn. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma strchrnul_ret : forall x12 x13 x14 x15 x16 x17,
    evt ssegs POST (AT 0x20f64 (Z_to_bv 64 0x20e6c) s0 (Z_to_bv 64 (A + Z.of_nat (strchrnul_idx c str))) x12 x13 x14 x15 x16 x17).
  Proof using FR LO MI MU ST STR WM. pin_using (fun (FR LO MI MU ST STR WM : unit) => tt).
    intros. pose proof A_bound as AB. pose proof FR as FR'. pose proof ST as ST'. pose proof MI as MI'.
    do 3 step. release_frame FR' ST' (bv_unsigned sp). step. unfold strchrnul_post. finish.
  Qed.

  (* [comment removed for export] *)
  Lemma strchrnul_ret_any : forall xra xs0 x12 x13 x14 x15 x16 x17,
    evt ssegs POST (AT 0x20f64 xra xs0 (Z_to_bv 64 (A + Z.of_nat (strchrnul_idx c str))) x12 x13 x14 x15 x16 x17).
  Proof using FR LO MI MU ST STR WM. pin_using (fun (FR LO MI MU ST STR WM : unit) => tt).
    intros. pose proof A_bound as AB. pose proof FR as FR'. pose proof ST as ST'. pose proof MI as MI'.
    do 3 step. release_frame FR' ST' (bv_unsigned sp). step. unfold strchrnul_post. finish.
  Qed.

  (* [comment removed for export] *)
  Lemma strchrnul_tail : forall (k : nat) (i : Z) xra xs0 x12 x13 x14 x15 x16 x17,
    Z.to_nat (len - i) = k -> (0 <= i <= len)%Z -> NOB i ->
    evt ssegs POST (AT 0x20f54 xra xs0 (Z_to_bv 64 (A + i - 1)) x12 x13 x14 x15 x16 x17).
  Proof using FR LO MI MU NONUL ST STR WM. pin_using (fun (FR LO MI MU NONUL ST STR WM : unit) => tt).
    induction k as [|k IH]; intros i xra xs0 x12 x13 x14 x15 x16 x17 Hk Hi HN; pose proof A_bound as AB.
    - assert (Ei : i = len) by lia. subst i.
      pose proof (u8ro_read ssegs m1 A full len _ (wa (A + len - 1 + 1)) STR full_nth_len ltac:(lia) ltac:(f_equal; lia)) as RD.
      do 3 zstep. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
      replace (A + len - 1 + 1)%Z with (A + Z.of_nat (strchrnul_idx c str))%Z by (rewrite idx_end; [lia|exact HN]).
      apply strchrnul_ret_any.
    - destruct (full_nth_lt i ltac:(lia)) as (b & Hn & Hns & Hb).
      pose proof (u8ro_read ssegs m1 A full i b (wa (A + i - 1 + 1)) STR Hn ltac:(lia) ltac:(f_equal; lia)) as RD.
      do 3 zstep. if_cases K; zify_cond K. { exfalso. exact (Hb K). }
      zstep. if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        replace (A + i - 1 + 1)%Z with (A + (i + 1) - 1)%Z by lia.
        apply (IH (i + 1)%Z); try lia. eapply NOB_S; eauto; lia.
      + (* [comment removed for export] *)
        replace (A + i - 1 + 1)%Z with (A + Z.of_nat (strchrnul_idx c str))%Z by (rewrite (idx_found i b); [lia|lia|exact HN|exact Hns|exact K2]).
        apply strchrnul_ret_any.
  Qed.

  (* [comment removed for export] *)
  Lemma strchrnul_words : forall (k : nat) (j : Z) xra xs0 (chunk : list byte) x16 x17,
    Z.to_nat (len - j) = k -> (0 <= j)%Z -> (j + 8 <= len)%Z -> ((A + j) mod 8 = 0)%Z -> NOB j ->
    chunk = firstn 8 (skipn (Z.to_nat j) full) ->
    evt ssegs POST (AT 0x20efc xra xs0 (Z_to_bv 64 (A + j)) (Z_to_bv 64 CMAGIC) (Z_to_bv 64 HIGHS)
                       (bv_extract 0 64 (le_bytes_to_word chunk)) (Z_to_bv 64 (c * ONES)) x16 x17).
  Proof using FR LO MI MU NONUL PAD ST STR WM. pin_using (fun (FR LO MI MU NONUL PAD ST STR WM : unit) => tt).
    induction k as [k IH] using lt_wf_ind; intros j xra xs0 chunk x16 x17 Hk Hj Hj8 Hal HN Hch; pose proof A_bound as AB.
    assert (CL : length chunk = 8%nat). { subst chunk. rewrite length_firstn, length_skipn, full_length. lia. }
    pose proof (le_val_range _ (bytes_ok_map chunk)) as WR. rewrite length_map, CL in WR.
    change (256 ^ Z.of_nat 8)%Z with (2^64)%Z in WR.
    pose proof (le_val_range _ (bytes_ok_xor _ c (bytes_ok_map chunk) ltac:(lia))) as XR. rewrite !length_map, CL in XR.
    change (256 ^ Z.of_nat 8)%Z with (2^64)%Z in XR.
    zstep. rewrite (load8_le_val chunk CL).
    replace (Z.lxor (le_val (map bv_unsigned chunk)) (c * ONES)) with (le_val (map (fun b => Z.lxor b c) (map bv_unsigned chunk))).
    2:{ change ONES with ONES64b. rewrite <- ones_8, <- CL, <- (length_map bv_unsigned). symmetry. apply le_val_xor_bcast; [apply bytes_ok_map| lia]. }
    do 4 zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      do 2 zstep. replace (A + j + -1)%Z with (A + j - 1)%Z by lia.
      apply (strchrnul_tail (Z.to_nat (len - j)) j); try lia. exact HN.
    - apply (haszero64_clang _ (bytes_ok_xor _ c (bytes_ok_map chunk) ltac:(lia)) ltac:(rewrite !length_map; exact CL)) in K.
      rewrite In0_xor in K.
      assert (HN8 : NOB (j + 8)).
      { intros i b Hi Hn. destruct (Nat.lt_ge_cases i (Z.to_nat j)) as [Hlt|Hge]. { exact (HN _ _ Hlt Hn). }
        intros Hb. apply K. rewrite <- Hb. apply in_map. subst chunk.
        apply nth_error_In with (n := (i - Z.to_nat j)%nat).
        rewrite nth_error_firstn. replace (Nat.ltb _ _) with true by (symmetry; apply Nat.ltb_lt; lia).
        rewrite nth_error_skipn. rewrite nth_error_app1 by (apply nth_error_lt in Hn; lia). rewrite <- Hn. f_equal. lia. }
      (* [comment removed for export] *)
      assert (HW : (Z.to_nat (j + 8) + 8 <= length full)%nat).
      { rewrite full_length. Z.div_mod_to_equations. lia. }
      pose proof (bytes_at_read ssegs m1 A full (j + 8) 8 STR ltac:(lia) HW) as RD.
      set (chunk2 := firstn 8 (skipn (Z.to_nat (j + 8)) full)) in RD.
      assert (CL2 : length chunk2 = 8%nat). { subst chunk2. rewrite length_firstn, length_skipn. lia. }
      pose proof (le_val_range _ (bytes_ok_map chunk2)) as WR2. rewrite length_map, CL2 in WR2.
      change (256 ^ Z.of_nat 8)%Z with (2^64)%Z in WR2.
      replace (wa (A + (j + 8))) with (wa (A + j + 8)) in RD by (f_equal; lia).
      do 7 zstep. rewrite (load8_le_val chunk2 CL2).
      if_cases K8; zify_cond K8.
      + (* [comment removed for export] *)
        apply (haszero64_clang _ (bytes_ok_map chunk2) ltac:(rewrite length_map; exact CL2)) in K8.
        rewrite In0_map_unsigned in K8.
        assert (Hj16 : (j + 16 <= len)%Z).
        { destruct (Z.lt_ge_cases len (j + 16)); [|assumption]. exfalso. apply K8. subst chunk2.
          apply nth_error_In with (n := (Z.to_nat len - Z.to_nat (j + 8))%nat).
          rewrite nth_error_firstn. replace (Nat.ltb _ _) with true by (symmetry; apply Nat.ltb_lt; lia).
          rewrite nth_error_skipn, <- full_nth_len. f_equal. lia. }
        replace (A + j + 8)%Z with (A + (j + 8))%Z by lia.
        apply (IH (Z.to_nat (len - (j + 8))) ltac:(lia) (j + 8)%Z); try lia; try exact HN8; try reflexivity.
        all: Z.div_mod_to_equations; lia.
      + (* [comment removed for export] *)
        zstep. zstep. replace (A + j + 7)%Z with (A + (j + 8) - 1)%Z by lia.
        apply (strchrnul_tail (Z.to_nat (len - (j + 8))) (j + 8)); try lia. exact HN8.
  Qed.

  (* [comment removed for export] *)
  Definition strchrnul_wentry__stmt : Prop := forall (j : Z) xra xs0 x10 x12 x13 x14 x15 x16 x17,
    (0 <= j <= len)%Z -> ((A + j) mod 8 = 0)%Z -> NOB j -> x10 = Z_to_bv 64 (A + j) ->
    evt ssegs POST (AT 0x20ed0 xra xs0 x10 x12 x13 x14 x15 x16 x17).
  Section Sz13.
  Variables j xra xs0 x10 x12 x13 x14 x15 x16 x17 : ltac2:(SecDiet.SzSec.tyM 'strchrnul_wentry__stmt "vvvvvvvvvv" @j).
  Lemma strchrnul_wentry__body : ltac2:(SecDiet.SzSec.bodyP 'strchrnul_wentry__stmt "vvvvvvvvvv").
  Proof using FR LO MI MU NONUL PAD ST STR WM. pin_using (fun (FR LO MI MU NONUL PAD ST STR WM : unit) => tt).
    intros Hj Hal HN ->.
 pose proof A_bound as AB.
    assert (HW : (Z.to_nat j + 8 <= length full)%nat).
    { rewrite full_length. Z.div_mod_to_equations. lia. }
    pose proof (bytes_at_read ssegs m1 A full j 8 STR ltac:(lia) HW) as RD.
    set (chunk := firstn 8 (skipn (Z.to_nat j) full)) in RD.
    assert (CL : length chunk = 8%nat). { subst chunk. rewrite length_firstn, length_skipn. lia. }
    pose proof (le_val_range _ (bytes_ok_map chunk)) as WR. rewrite length_map, CL in WR.
    change (256 ^ Z.of_nat 8)%Z with (2^64)%Z in WR.
    do 9 zstep. rewrite (load8_le_val chunk CL).
    if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      do 2 zstep. replace (A + j + -1)%Z with (A + j - 1)%Z by lia.
      apply (strchrnul_tail (Z.to_nat (len - j)) j); try lia. exact HN.
    - apply (haszero64_clang _ (bytes_ok_map chunk) ltac:(rewrite length_map; exact CL)) in K.
      rewrite In0_map_unsigned in K.
      assert (Hj8 : (j + 8 <= len)%Z).
      { destruct (Z.lt_ge_cases len (j + 8)); [|assumption]. exfalso. apply K. subst chunk.
        apply nth_error_In with (n := (Z.to_nat len - Z.to_nat j)%nat).
        rewrite nth_error_firstn. replace (Nat.ltb _ _) with true by (symmetry; apply Nat.ltb_lt; lia).
        rewrite nth_error_skipn, <- full_nth_len. f_equal. lia. }
      do 2 zstep.
      replace (c * (CMAGIC + 1))%Z with (c * ONES)%Z by reflexivity.
      apply (strchrnul_words (Z.to_nat (len - j)) j xra xs0 chunk); try lia; try exact HN. reflexivity.
  Qed.
  End Sz13.
  Lemma strchrnul_wentry : ltac:(let t := eval cbv delta [strchrnul_wentry__stmt] in strchrnul_wentry__stmt in exact t).
  Proof using FR LO MI MU NONUL PAD ST STR WM. intros j xra xs0 x10 x12 x13 x14 x15 x16 x17. ltac2:(SecDiet.SzSec.closeP 'strchrnul_wentry__body "vvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Lemma strchrnul_head : forall (k : nat) (i : Z) xra xs0 x10 x12 x13 x14 x15 x16 x17,
    Z.to_nat (len - i) = k -> (0 <= i <= len)%Z -> NOB i -> x10 = Z_to_bv 64 (A + i) -> x12 = Z_to_bv 64 (A + i + 1) ->
    evt ssegs POST (AT 0x20eb4 xra xs0 x10 x12 x13 x14 x15 x16 x17).
  Proof using FR LO MI MU NONUL PAD ST STR WM. pin_using (fun (FR LO MI MU NONUL PAD ST STR WM : unit) => tt).
    induction k as [|k IH]; intros i xra xs0 x10 x12 x13 x14 x15 x16 x17 Hk Hi HN -> ->; pose proof A_bound as AB.
    - assert (Ei : i = len) by lia. subst i.
      pose proof (u8ro_read ssegs m1 A full len _ _ STR full_nth_len ltac:(lia) eq_refl) as RD.
      zstep. zstep. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
      replace (A + len)%Z with (A + Z.of_nat (strchrnul_idx c str))%Z by (rewrite idx_end; [lia|exact HN]).
      apply strchrnul_ret_any.
    - destruct (full_nth_lt i ltac:(lia)) as (b & Hn & Hns & Hb).
      pose proof (u8ro_read ssegs m1 A full i b _ STR Hn ltac:(lia) eq_refl) as RD.
      zstep. zstep. if_cases K; zify_cond K. { exfalso. exact (Hb K). }
      zstep. if_cases K2; zify_cond K2.
      { (* [comment removed for export] *)
        rewrite <- (idx_found i b ltac:(lia) HN Hns K2). apply strchrnul_ret_any. }
      pose proof (NOB_S i b ltac:(lia) HN Hns K2) as HN1.
      do 4 zstep. if_cases Kal; zify_cond Kal.
      + apply (IH (i + 1)%Z); try lia; try (f_equal; lia). exact HN1.
      + apply (strchrnul_wentry (i + 1)); try lia; try exact HN1; try (f_equal; lia).
        revert Kal. zb_masks. intros Kal. Z.div_mod_to_equations; lia.
  Qed.
End StrchrnulProof.

Lemma strchrnul_idx_nul : forall str, ~ In (Z_to_bv 8 0) str -> strchrnul_idx 0 str = length str.
Proof.
  intros str H. unfold strchrnul_idx. rewrite find_byte_notin; [reflexivity|].
  intros b Hb E. apply H. replace (Z_to_bv 8 0) with b; [exact Hb|]. apply bv_eq. rewrite E. reflexivity.
Qed.

Definition strchrnul_spec__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (str slack : list byte) (lo : Z),
  stk ssegs m lo (bv_unsigned sp) ->
  bytes_at ssegs m (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack) ->
  ~ In (Z_to_bv 8 0) str ->
  ((- (bv_unsigned a0 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  mem_inv ssegs m ->
  (lo <= bv_unsigned sp - 16)%Z ->
  (bv_unsigned a0 + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= bv_unsigned sp - 16 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  evt ssegs (strchrnul_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 str slack lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x20e94) fc None m (seg_rom ssegs)).
Section Sz16.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m str slack lo : ltac2:(SecDiet.SzSec.tyM 'strchrnul_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
#[using="Type"] Lemma strchrnul_spec__body : ltac2:(SecDiet.SzSec.bodyP 'strchrnul_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
  intros ST STR NONUL PAD MI LO SEP.
  pose proof (bytes_at_bound _ _ _ _ STR) as AB. rewrite length_app in AB. cbn [length] in AB.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ssegs m) as WM.
  pose proof (proj1 ST) as LO0. cbn beta in LO0. pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. cbn in Rsp.
  pose proof (zr_word a1) as R1. unfold inr64 in R1.
  carve_frame 16%nat ST.
  do 3 step.
  zstep. replace (Z.land (bv_unsigned a1) 255) with ((bv_unsigned a1) mod 256)%Z.
  2:{ change 255%Z with (2^8 - 1)%Z. rewrite zb_land_mask by lia. reflexivity. }
  zstep. if_cases K0; zify_cond K0.
  - (* [comment removed for export] *)
    step. step. call strlen_spec. 1:{ exact STR. } 1:{ exact NONUL. } 1:{ exact PAD. } 1:{ exact MI. }
    zstep. do 3 step. release_frame FR ST (bv_unsigned sp). step.
    unfold strchrnul_post. rewrite K0. rewrite (strchrnul_idx_nul str NONUL). finish.
  - zstep. zstep. if_cases Kal; zify_cond Kal.
    + (* [comment removed for export] *)
      eapply strchrnul_wentry with (j := 0%Z); try reflexivity; try eassumption; try lia; try apply NOB_0.
      * revert Kal. zb_masks. intros Kal. rewrite Z.add_0_r. exact Kal.
      * rewrite Z.add_0_r. symmetry. apply Z_to_bv_bv_unsigned.
    + zstep.
      eapply strchrnul_head with (i := 0%Z); try reflexivity; try eassumption; try lia; try apply NOB_0; try (f_equal; lia).
      rewrite Z.add_0_r. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
End Sz16.
Lemma strchrnul_spec : ltac:(let t := eval cbv delta [strchrnul_spec__stmt] in strchrnul_spec__stmt in exact t).
Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m str slack lo. ltac2:(SecDiet.SzSec.closeP 'strchrnul_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition strchr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 : word) (str slack : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
                 (Z_to_bv 64 (strchr_res (bv_unsigned a0) (bv_unsigned a1 mod 256) str))
                 a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ssegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
    /\ stk ssegs m' lo (bv_unsigned sp)
    /\ bytes_at ssegs m' (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack).

Definition strchr_spec__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (str slack : list byte) (lo : Z),
  stk ssegs m lo (bv_unsigned sp) ->
  bytes_at ssegs m (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack) ->
  ~ In (Z_to_bv 8 0) str ->
  ((- (bv_unsigned a0 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  mem_inv ssegs m ->
  (lo <= bv_unsigned sp - 32)%Z ->
  (bv_unsigned a0 + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  evt ssegs (strchr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 str slack lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x20e58) fc None m (seg_rom ssegs)).
Section Sz17.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m str slack lo : ltac2:(SecDiet.SzSec.tyM 'strchr_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
#[using="Type"] Lemma strchr_spec__body : ltac2:(SecDiet.SzSec.bodyP 'strchr_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
  intros ST STR NONUL PAD MI LO SEP.
  pose proof (bytes_at_bound _ _ _ _ STR) as AB. rewrite length_app in AB. cbn [length] in AB.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ssegs m) as WM.
  pose proof (proj1 ST) as LO0. cbn beta in LO0. pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. cbn in Rsp.
  pose proof (zr_word a1) as R1. unfold inr64 in R1.
  carve_frame 16%nat ST.
  do 4 step.
  step. call_sp strchrnul_spec; [exact ST | exact STR | exact NONUL | exact PAD | exact MI | lia | lia | ].
  rename PC into ST; clear STR; rename POST into STR.
  (* [comment removed for export] *)
  set (i := strchrnul_idx (bv_unsigned a1 mod 256) str) in *.
  pose proof (strchrnul_idx_le (bv_unsigned a1 mod 256) str) as Hi. fold i in Hi.
  assert (Hb : exists b, nth_error (str ++ Z_to_bv 8 0 :: slack) i = Some b /\
                         (bv_unsigned b = bv_unsigned a1 mod 256 -> strchr_res (bv_unsigned a0) (bv_unsigned a1 mod 256) str = bv_unsigned a0 + Z.of_nat i)%Z /\
                         (bv_unsigned b <> bv_unsigned a1 mod 256 -> strchr_res (bv_unsigned a0) (bv_unsigned a1 mod 256) str = 0)%Z).
  { unfold strchr_res. subst i. unfold strchrnul_idx.
    destruct (find_byte (bv_unsigned a1 mod 256) str) as [j|] eqn:FB.
    - destruct (find_byte_Some _ _ _ FB) as (Hj & (b & Hn & Hbb) & _). exists b.
      rewrite nth_error_app1 by lia. split; [exact Hn|].
      destruct (Z.eqb_spec (bv_unsigned a1 mod 256) 0) as [E|NE].
      { exfalso. apply NONUL. replace (Z_to_bv 8 0) with b. { eapply nth_error_In; eauto. } apply bv_eq. rewrite Hbb, E. reflexivity. }
      split; [intros _; reflexivity | intros X; exfalso; exact (X Hbb)].
    - exists (Z_to_bv 8 0). rewrite nth_error_app2, Nat.sub_diag by lia. split; [reflexivity|].
      destruct (Z.eqb_spec (bv_unsigned a1 mod 256) 0) as [E|NE].
      + split; [intros _; reflexivity | intros X; exfalso; apply X; rewrite E; reflexivity].
      + split; [intros X; exfalso; apply NE; rewrite <- X; reflexivity | intros _; reflexivity]. }
  destruct Hb as (b & Hn & Heq & Hne).
  pose proof (u8ro_read ssegs _ (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack) (Z.of_nat i) b (wa (bv_unsigned a0 + Z.of_nat i + 0)) STR
                ltac:(rewrite Nat2Z.id; exact Hn) ltac:(lia) ltac:(f_equal; lia)) as RD.
  pose proof (byte_range b) as Rb.
  do 6 zstep.
  replace (Z.land (bv_unsigned a1) 255) with ((bv_unsigned a1) mod 256)%Z.
  2:{ change 255%Z with (2^8 - 1)%Z. rewrite zb_land_mask by lia. reflexivity. }
  do 3 step. release_frame FR ST (bv_unsigned sp). step.
  destruct (Z.eq_dec (bv_unsigned b) (bv_unsigned a1 mod 256)) as [E|NE].
  - rewrite E, Z.lxor_nilpotent. change (Z.b2z (0 <? 0) + -1)%Z with (-1)%Z.
    replace (Z.land ((-1) mod 18446744073709551616) (bv_unsigned a0 + Z.of_nat i))%Z with (bv_unsigned a0 + Z.of_nat i)%Z.
    2:{ change ((-1) mod 18446744073709551616)%Z with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia. rewrite Z.mod_small by lia. reflexivity. }
    rewrite <- (Heq E). unfold strchr_post. finish.
  - assert (Hx : (0 <? Z.lxor (bv_unsigned b) (bv_unsigned a1 mod 256))%Z = true).
    { apply Z.ltb_lt. pose proof (Z.lxor_nonneg (bv_unsigned b) (bv_unsigned a1 mod 256)).
      destruct (Z.eq_dec (Z.lxor (bv_unsigned b) (bv_unsigned a1 mod 256)) 0) as [E0|]; [|lia].
      apply Z.lxor_eq in E0. exfalso. exact (NE E0). }
    rewrite Hx. change (Z.b2z true + -1)%Z with 0%Z. change (0 mod 18446744073709551616)%Z with 0%Z. rewrite Z.land_0_l.
    rewrite <- (Hne NE). unfold strchr_post. finish.
Qed.
End Sz17.
Lemma strchr_spec : ltac:(let t := eval cbv delta [strchr_spec__stmt] in strchr_spec__stmt in exact t).
Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m str slack lo. ltac2:(SecDiet.SzSec.closeP 'strchr_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.F_strlen.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.F_memchr.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition strchrnul_entry := 0x21654%Z.
Definition strchr_entry := 0x21618%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition strchrnul_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 : word) (str slack : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
                 (Z_to_bv 64 (bv_unsigned a0 + Z.of_nat (strchrnul_idx (bv_unsigned a1 mod 256) str)))
                 a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ bytes_at usegs m' (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack).

Section StrchrnulProof.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m m1 : word -> option byte) (str slack : list byte) (lo : Z).
  (* [comment removed for export] *)
  Hypothesis MI : mem_inv usegs m1.
  Hypothesis STR : bytes_at usegs m1 (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack).
  Hypothesis NONUL : ~ In (Z_to_bv 8 0) str.
  Hypothesis PAD : ((- (bv_unsigned a0 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z.
  Hypothesis MU : munch [(bv_unsigned sp + -16, bv_unsigned sp)]%Z m m1.
  Hypothesis WM : wmono usegs m m1.
  Hypothesis ST : stk usegs m1 lo (bv_unsigned sp + -16).
  Hypothesis FR : rw_cells usegs m1 (bv_unsigned sp + -16) [C8 s0; C8 ra].
  Hypothesis LO : (0 <= lo <= bv_unsigned sp - 16)%Z.
  Hypothesis SPR : (bv_unsigned sp < 2^64)%Z.

  Notation A := (bv_unsigned a0).
  Notation c := ((bv_unsigned a1) mod 256)%Z.
  Notation len := (Z.of_nat (length str)).
  Notation full := (str ++ Z_to_bv 8 0 :: slack).
  Notation POST := (strchrnul_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 str slack lo m).
  (* [comment removed for export] *)
  Notation AT pc xra xs0 x10 x12 x13 x14 x15 x16 x17 :=
    (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 xs0 s1 x10 (Z_to_bv 64 c) x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m1 (seg_rom usegs)).
  Notation CMAGIC := 72340172838076672%Z.      (* [comment removed for export] *)
  Notation HIGHS := 9259542123273814144%Z.     (* [comment removed for export] *)
  Notation ONES := 72340172838076673%Z.       (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition NOB (i : Z) : Prop :=
    forall j b, (j < Z.to_nat i)%nat -> nth_error str j = Some b -> bv_unsigned b <> c.

  Lemma full_length : length full = (length str + S (length slack))%nat.
  Proof using a0. pin_using (fun (a0 : unit) => tt). rewrite length_app. cbn. lia. Qed.

  Lemma A_bound : (0 <= A /\ A + len + 1 + Z.of_nat (length slack) <= 2^64 /\ 0 <= c < 256)%Z.
  Proof using STR. pin_using (fun (STR : unit) => tt).
    pose proof (bytes_at_bound _ _ _ _ STR) as B. rewrite full_length in B.
    pose proof (Z.mod_pos_bound (bv_unsigned a1) 256). lia.
  Qed.

  Lemma full_nth_lt : forall i, (0 <= i < len)%Z ->
    exists b, nth_error full (Z.to_nat i) = Some b /\ nth_error str (Z.to_nat i) = Some b /\ bv_unsigned b <> 0%Z.
  Proof using NONUL a0. pin_using (fun (NONUL a0 : unit) => tt).
    intros i Hi. destruct (nth_error str (Z.to_nat i)) as [b|] eqn:E.
    - exists b. split. { rewrite nth_error_app1 by lia. exact E. } split; [reflexivity|].
      intros Hb. apply NONUL. replace (Z_to_bv 8 0) with b. { eapply nth_error_In; eauto. }
      apply bv_eq. rewrite Hb. reflexivity.
    - apply nth_error_None in E. lia.
  Qed.

  Lemma full_nth_len : nth_error full (Z.to_nat len) = Some (Z_to_bv 8 0).
  Proof using a0. pin_using (fun (a0 : unit) => tt). rewrite nth_error_app2, Nat2Z.id, Nat.sub_diag by lia. reflexivity. Qed.

  Lemma NOB_0 : NOB 0.
  Proof using Type. pin_using tt. intros j b Hj. exfalso. exact (Nat.nlt_0_r _ Hj). Qed.

  Lemma NOB_S : forall i b, (0 <= i)%Z -> NOB i -> nth_error str (Z.to_nat i) = Some b -> bv_unsigned b <> c -> NOB (i + 1).
  Proof using a0 slack. pin_using (fun (a0 slack : unit) => tt).
    intros i b Hi H Hn Hb j b' Hj Hn'.
    destruct (Nat.eq_dec j (Z.to_nat i)) as [->|NE]. { rewrite Hn in Hn'. injection Hn' as <-. exact Hb. }
    eapply H; [|exact Hn']. lia.
  Qed.

  Lemma idx_found : forall i b, (0 <= i < len)%Z -> NOB i -> nth_error str (Z.to_nat i) = Some b -> bv_unsigned b = c ->
    Z.of_nat (strchrnul_idx c str) = i.
  Proof using a0 slack. pin_using (fun (a0 slack : unit) => tt).
    intros i b Hi HN Hn Hb. unfold strchrnul_idx.
    rewrite (find_byte_charact c str (Z.to_nat i) b Hn Hb). { lia. }
    intros j b' Hj Hn'. exact (HN _ _ Hj Hn').
  Qed.

  Lemma idx_end : NOB len -> Z.of_nat (strchrnul_idx c str) = len.
  Proof using a0 slack. pin_using (fun (a0 slack : unit) => tt).
    intros HN. unfold strchrnul_idx. rewrite find_byte_None_intro; [reflexivity|].
    intros j b Hn. apply (HN j b); [|exact Hn]. apply nth_error_lt in Hn. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma strchrnul_ret : forall x12 x13 x14 x15 x16 x17,
    evt usegs POST (AT 0x21724 (Z_to_bv 64 0x2162c) s0 (Z_to_bv 64 (A + Z.of_nat (strchrnul_idx c str))) x12 x13 x14 x15 x16 x17).
  Proof using FR LO MI MU ST STR WM. pin_using (fun (FR LO MI MU ST STR WM : unit) => tt).
    intros. pose proof A_bound as AB. pose proof FR as FR'. pose proof ST as ST'. pose proof MI as MI'.
    do 3 step. release_frame FR' ST' (bv_unsigned sp). step. unfold strchrnul_post. finish.
  Qed.

  (* [comment removed for export] *)
  Lemma strchrnul_ret_any : forall xra xs0 x12 x13 x14 x15 x16 x17,
    evt usegs POST (AT 0x21724 xra xs0 (Z_to_bv 64 (A + Z.of_nat (strchrnul_idx c str))) x12 x13 x14 x15 x16 x17).
  Proof using FR LO MI MU ST STR WM. pin_using (fun (FR LO MI MU ST STR WM : unit) => tt).
    intros. pose proof A_bound as AB. pose proof FR as FR'. pose proof ST as ST'. pose proof MI as MI'.
    do 3 step. release_frame FR' ST' (bv_unsigned sp). step. unfold strchrnul_post. finish.
  Qed.

  (* [comment removed for export] *)
  Lemma strchrnul_tail : forall (k : nat) (i : Z) xra xs0 x12 x13 x14 x15 x16 x17,
    Z.to_nat (len - i) = k -> (0 <= i <= len)%Z -> NOB i ->
    evt usegs POST (AT 0x21714 xra xs0 (Z_to_bv 64 (A + i - 1)) x12 x13 x14 x15 x16 x17).
  Proof using FR LO MI MU NONUL ST STR WM. pin_using (fun (FR LO MI MU NONUL ST STR WM : unit) => tt).
    induction k as [|k IH]; intros i xra xs0 x12 x13 x14 x15 x16 x17 Hk Hi HN; pose proof A_bound as AB.
    - assert (Ei : i = len) by lia. subst i.
      pose proof (u8ro_read usegs m1 A full len _ (wa (A + len - 1 + 1)) STR full_nth_len ltac:(lia) ltac:(f_equal; lia)) as RD.
      do 3 zstep. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
      replace (A + len - 1 + 1)%Z with (A + Z.of_nat (strchrnul_idx c str))%Z by (rewrite idx_end; [lia|exact HN]).
      apply strchrnul_ret_any.
    - destruct (full_nth_lt i ltac:(lia)) as (b & Hn & Hns & Hb).
      pose proof (u8ro_read usegs m1 A full i b (wa (A + i - 1 + 1)) STR Hn ltac:(lia) ltac:(f_equal; lia)) as RD.
      do 3 zstep. if_cases K; zify_cond K. { exfalso. exact (Hb K). }
      zstep. if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        replace (A + i - 1 + 1)%Z with (A + (i + 1) - 1)%Z by lia.
        apply (IH (i + 1)%Z); try lia. eapply NOB_S; eauto; lia.
      + (* [comment removed for export] *)
        replace (A + i - 1 + 1)%Z with (A + Z.of_nat (strchrnul_idx c str))%Z by (rewrite (idx_found i b); [lia|lia|exact HN|exact Hns|exact K2]).
        apply strchrnul_ret_any.
  Qed.

  (* [comment removed for export] *)
  Lemma strchrnul_words : forall (k : nat) (j : Z) xra xs0 (chunk : list byte) x16 x17,
    Z.to_nat (len - j) = k -> (0 <= j)%Z -> (j + 8 <= len)%Z -> ((A + j) mod 8 = 0)%Z -> NOB j ->
    chunk = firstn 8 (skipn (Z.to_nat j) full) ->
    evt usegs POST (AT 0x216bc xra xs0 (Z_to_bv 64 (A + j)) (Z_to_bv 64 CMAGIC) (Z_to_bv 64 HIGHS)
                       (bv_extract 0 64 (le_bytes_to_word chunk)) (Z_to_bv 64 (c * ONES)) x16 x17).
  Proof using FR LO MI MU NONUL PAD ST STR WM. pin_using (fun (FR LO MI MU NONUL PAD ST STR WM : unit) => tt).
    induction k as [k IH] using lt_wf_ind; intros j xra xs0 chunk x16 x17 Hk Hj Hj8 Hal HN Hch; pose proof A_bound as AB.
    assert (CL : length chunk = 8%nat). { subst chunk. rewrite length_firstn, length_skipn, full_length. lia. }
    pose proof (le_val_range _ (bytes_ok_map chunk)) as WR. rewrite length_map, CL in WR.
    change (256 ^ Z.of_nat 8)%Z with (2^64)%Z in WR.
    pose proof (le_val_range _ (bytes_ok_xor _ c (bytes_ok_map chunk) ltac:(lia))) as XR. rewrite !length_map, CL in XR.
    change (256 ^ Z.of_nat 8)%Z with (2^64)%Z in XR.
    zstep. rewrite (load8_le_val chunk CL).
    replace (Z.lxor (le_val (map bv_unsigned chunk)) (c * ONES)) with (le_val (map (fun b => Z.lxor b c) (map bv_unsigned chunk))).
    2:{ change ONES with ONES64b. rewrite <- ones_8, <- CL, <- (length_map bv_unsigned). symmetry. apply le_val_xor_bcast; [apply bytes_ok_map| lia]. }
    do 4 zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      do 2 zstep. replace (A + j + -1)%Z with (A + j - 1)%Z by lia.
      apply (strchrnul_tail (Z.to_nat (len - j)) j); try lia. exact HN.
    - apply (haszero64_clang _ (bytes_ok_xor _ c (bytes_ok_map chunk) ltac:(lia)) ltac:(rewrite !length_map; exact CL)) in K.
      rewrite In0_xor in K.
      assert (HN8 : NOB (j + 8)).
      { intros i b Hi Hn. destruct (Nat.lt_ge_cases i (Z.to_nat j)) as [Hlt|Hge]. { exact (HN _ _ Hlt Hn). }
        intros Hb. apply K. rewrite <- Hb. apply in_map. subst chunk.
        apply nth_error_In with (n := (i - Z.to_nat j)%nat).
        rewrite nth_error_firstn. replace (Nat.ltb _ _) with true by (symmetry; apply Nat.ltb_lt; lia).
        rewrite nth_error_skipn. rewrite nth_error_app1 by (apply nth_error_lt in Hn; lia). rewrite <- Hn. f_equal. lia. }
      (* [comment removed for export] *)
      assert (HW : (Z.to_nat (j + 8) + 8 <= length full)%nat).
      { rewrite full_length. Z.div_mod_to_equations. lia. }
      pose proof (bytes_at_read usegs m1 A full (j + 8) 8 STR ltac:(lia) HW) as RD.
      set (chunk2 := firstn 8 (skipn (Z.to_nat (j + 8)) full)) in RD.
      assert (CL2 : length chunk2 = 8%nat). { subst chunk2. rewrite length_firstn, length_skipn. lia. }
      pose proof (le_val_range _ (bytes_ok_map chunk2)) as WR2. rewrite length_map, CL2 in WR2.
      change (256 ^ Z.of_nat 8)%Z with (2^64)%Z in WR2.
      replace (wa (A + (j + 8))) with (wa (A + j + 8)) in RD by (f_equal; lia).
      do 7 zstep. rewrite (load8_le_val chunk2 CL2).
      if_cases K8; zify_cond K8.
      + (* [comment removed for export] *)
        apply (haszero64_clang _ (bytes_ok_map chunk2) ltac:(rewrite length_map; exact CL2)) in K8.
        rewrite In0_map_unsigned in K8.
        assert (Hj16 : (j + 16 <= len)%Z).
        { destruct (Z.lt_ge_cases len (j + 16)); [|assumption]. exfalso. apply K8. subst chunk2.
          apply nth_error_In with (n := (Z.to_nat len - Z.to_nat (j + 8))%nat).
          rewrite nth_error_firstn. replace (Nat.ltb _ _) with true by (symmetry; apply Nat.ltb_lt; lia).
          rewrite nth_error_skipn, <- full_nth_len. f_equal. lia. }
        replace (A + j + 8)%Z with (A + (j + 8))%Z by lia.
        apply (IH (Z.to_nat (len - (j + 8))) ltac:(lia) (j + 8)%Z); try lia; try exact HN8; try reflexivity.
        all: Z.div_mod_to_equations; lia.
      + (* [comment removed for export] *)
        zstep. zstep. replace (A + j + 7)%Z with (A + (j + 8) - 1)%Z by lia.
        apply (strchrnul_tail (Z.to_nat (len - (j + 8))) (j + 8)); try lia. exact HN8.
  Qed.

  (* [comment removed for export] *)
  Definition strchrnul_wentry__stmt : Prop := forall (j : Z) xra xs0 x10 x12 x13 x14 x15 x16 x17,
    (0 <= j <= len)%Z -> ((A + j) mod 8 = 0)%Z -> NOB j -> x10 = Z_to_bv 64 (A + j) ->
    evt usegs POST (AT 0x21690 xra xs0 x10 x12 x13 x14 x15 x16 x17).
  Section Sz13.
  Variables j xra xs0 x10 x12 x13 x14 x15 x16 x17 : ltac2:(SecDiet.SzSec.tyM 'strchrnul_wentry__stmt "vvvvvvvvvv" @j).
  Lemma strchrnul_wentry__body : ltac2:(SecDiet.SzSec.bodyP 'strchrnul_wentry__stmt "vvvvvvvvvv").
  Proof using FR LO MI MU NONUL PAD ST STR WM. pin_using (fun (FR LO MI MU NONUL PAD ST STR WM : unit) => tt).
    intros Hj Hal HN ->.
 pose proof A_bound as AB.
    assert (HW : (Z.to_nat j + 8 <= length full)%nat).
    { rewrite full_length. Z.div_mod_to_equations. lia. }
    pose proof (bytes_at_read usegs m1 A full j 8 STR ltac:(lia) HW) as RD.
    set (chunk := firstn 8 (skipn (Z.to_nat j) full)) in RD.
    assert (CL : length chunk = 8%nat). { subst chunk. rewrite length_firstn, length_skipn. lia. }
    pose proof (le_val_range _ (bytes_ok_map chunk)) as WR. rewrite length_map, CL in WR.
    change (256 ^ Z.of_nat 8)%Z with (2^64)%Z in WR.
    do 9 zstep. rewrite (load8_le_val chunk CL).
    if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      do 2 zstep. replace (A + j + -1)%Z with (A + j - 1)%Z by lia.
      apply (strchrnul_tail (Z.to_nat (len - j)) j); try lia. exact HN.
    - apply (haszero64_clang _ (bytes_ok_map chunk) ltac:(rewrite length_map; exact CL)) in K.
      rewrite In0_map_unsigned in K.
      assert (Hj8 : (j + 8 <= len)%Z).
      { destruct (Z.lt_ge_cases len (j + 8)); [|assumption]. exfalso. apply K. subst chunk.
        apply nth_error_In with (n := (Z.to_nat len - Z.to_nat j)%nat).
        rewrite nth_error_firstn. replace (Nat.ltb _ _) with true by (symmetry; apply Nat.ltb_lt; lia).
        rewrite nth_error_skipn, <- full_nth_len. f_equal. lia. }
      do 2 zstep.
      replace (c * (CMAGIC + 1))%Z with (c * ONES)%Z by reflexivity.
      apply (strchrnul_words (Z.to_nat (len - j)) j xra xs0 chunk); try lia; try exact HN. reflexivity.
  Qed.
  End Sz13.
  Lemma strchrnul_wentry : ltac:(let t := eval cbv delta [strchrnul_wentry__stmt] in strchrnul_wentry__stmt in exact t).
  Proof using FR LO MI MU NONUL PAD ST STR WM. intros j xra xs0 x10 x12 x13 x14 x15 x16 x17. ltac2:(SecDiet.SzSec.closeP 'strchrnul_wentry__body "vvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Lemma strchrnul_head : forall (k : nat) (i : Z) xra xs0 x10 x12 x13 x14 x15 x16 x17,
    Z.to_nat (len - i) = k -> (0 <= i <= len)%Z -> NOB i -> x10 = Z_to_bv 64 (A + i) -> x12 = Z_to_bv 64 (A + i + 1) ->
    evt usegs POST (AT 0x21674 xra xs0 x10 x12 x13 x14 x15 x16 x17).
  Proof using FR LO MI MU NONUL PAD ST STR WM. pin_using (fun (FR LO MI MU NONUL PAD ST STR WM : unit) => tt).
    induction k as [|k IH]; intros i xra xs0 x10 x12 x13 x14 x15 x16 x17 Hk Hi HN -> ->; pose proof A_bound as AB.
    - assert (Ei : i = len) by lia. subst i.
      pose proof (u8ro_read usegs m1 A full len _ _ STR full_nth_len ltac:(lia) eq_refl) as RD.
      zstep. zstep. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
      replace (A + len)%Z with (A + Z.of_nat (strchrnul_idx c str))%Z by (rewrite idx_end; [lia|exact HN]).
      apply strchrnul_ret_any.
    - destruct (full_nth_lt i ltac:(lia)) as (b & Hn & Hns & Hb).
      pose proof (u8ro_read usegs m1 A full i b _ STR Hn ltac:(lia) eq_refl) as RD.
      zstep. zstep. if_cases K; zify_cond K. { exfalso. exact (Hb K). }
      zstep. if_cases K2; zify_cond K2.
      { (* [comment removed for export] *)
        rewrite <- (idx_found i b ltac:(lia) HN Hns K2). apply strchrnul_ret_any. }
      pose proof (NOB_S i b ltac:(lia) HN Hns K2) as HN1.
      do 4 zstep. if_cases Kal; zify_cond Kal.
      + apply (IH (i + 1)%Z); try lia; try (f_equal; lia). exact HN1.
      + apply (strchrnul_wentry (i + 1)); try lia; try exact HN1; try (f_equal; lia).
        revert Kal. zb_masks. intros Kal. Z.div_mod_to_equations; lia.
  Qed.
End StrchrnulProof.

Lemma strchrnul_idx_nul : forall str, ~ In (Z_to_bv 8 0) str -> strchrnul_idx 0 str = length str.
Proof.
  intros str H. unfold strchrnul_idx. rewrite find_byte_notin; [reflexivity|].
  intros b Hb E. apply H. replace (Z_to_bv 8 0) with b; [exact Hb|]. apply bv_eq. rewrite E. reflexivity.
Qed.

Definition strchrnul_spec__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (str slack : list byte) (lo : Z),
  stk usegs m lo (bv_unsigned sp) ->
  bytes_at usegs m (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack) ->
  ~ In (Z_to_bv 8 0) str ->
  ((- (bv_unsigned a0 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  mem_inv usegs m ->
  (lo <= bv_unsigned sp - 16)%Z ->
  (bv_unsigned a0 + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= bv_unsigned sp - 16 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  evt usegs (strchrnul_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 str slack lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x21654) fc None m (seg_rom usegs)).
Section Sz16.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m str slack lo : ltac2:(SecDiet.SzSec.tyM 'strchrnul_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
#[using="Type"] Lemma strchrnul_spec__body : ltac2:(SecDiet.SzSec.bodyP 'strchrnul_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
 intros ST STR NONUL PAD MI LO SEP.
  pose proof (bytes_at_bound _ _ _ _ STR) as AB. rewrite length_app in AB. cbn [length] in AB.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (proj1 ST) as LO0. cbn beta in LO0. pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. cbn in Rsp.
  pose proof (zr_word a1) as R1. unfold inr64 in R1.
  carve_frame 16%nat ST.
  do 3 step.
  zstep. replace (Z.land (bv_unsigned a1) 255) with ((bv_unsigned a1) mod 256)%Z.
  2:{ change 255%Z with (2^8 - 1)%Z. rewrite zb_land_mask by lia. reflexivity. }
  zstep. if_cases K0; zify_cond K0.
  - (* [comment removed for export] *)
    step. step. call strlen_spec. 1:{ exact STR. } 1:{ exact NONUL. } 1:{ exact PAD. } 1:{ exact MI. }
    zstep. do 3 step. release_frame FR ST (bv_unsigned sp). step.
    unfold strchrnul_post. rewrite K0. rewrite (strchrnul_idx_nul str NONUL). finish.
  - zstep. zstep. if_cases Kal; zify_cond Kal.
    + (* [comment removed for export] *)
      eapply strchrnul_wentry with (j := 0%Z); try reflexivity; try eassumption; try lia; try apply NOB_0.
      * revert Kal. zb_masks. intros Kal. rewrite Z.add_0_r. exact Kal.
      * rewrite Z.add_0_r. symmetry. apply Z_to_bv_bv_unsigned.
    + zstep.
      eapply strchrnul_head with (i := 0%Z); try reflexivity; try eassumption; try lia; try apply NOB_0; try (f_equal; lia).
      rewrite Z.add_0_r. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
End Sz16.
Lemma strchrnul_spec : ltac:(let t := eval cbv delta [strchrnul_spec__stmt] in strchrnul_spec__stmt in exact t).
Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m str slack lo. ltac2:(SecDiet.SzSec.closeP 'strchrnul_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition strchr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 : word) (str slack : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
                 (Z_to_bv 64 (strchr_res (bv_unsigned a0) (bv_unsigned a1 mod 256) str))
                 a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ bytes_at usegs m' (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack).

Definition strchr_spec__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (str slack : list byte) (lo : Z),
  stk usegs m lo (bv_unsigned sp) ->
  bytes_at usegs m (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack) ->
  ~ In (Z_to_bv 8 0) str ->
  ((- (bv_unsigned a0 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  mem_inv usegs m ->
  (lo <= bv_unsigned sp - 32)%Z ->
  (bv_unsigned a0 + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  evt usegs (strchr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 str slack lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x21618) fc None m (seg_rom usegs)).
Section Sz17.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m str slack lo : ltac2:(SecDiet.SzSec.tyM 'strchr_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
#[using="Type"] Lemma strchr_spec__body : ltac2:(SecDiet.SzSec.bodyP 'strchr_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
 intros ST STR NONUL PAD MI LO SEP.
  pose proof (bytes_at_bound _ _ _ _ STR) as AB. rewrite length_app in AB. cbn [length] in AB.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (proj1 ST) as LO0. cbn beta in LO0. pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. cbn in Rsp.
  pose proof (zr_word a1) as R1. unfold inr64 in R1.
  carve_frame 16%nat ST.
  do 4 step.
  step. call_sp strchrnul_spec; [exact ST | exact STR | exact NONUL | exact PAD | exact MI | lia | lia | ].
  rename PC into ST; clear STR; rename POST into STR.
  (* [comment removed for export] *)
  set (i := strchrnul_idx (bv_unsigned a1 mod 256) str) in *.
  pose proof (strchrnul_idx_le (bv_unsigned a1 mod 256) str) as Hi. fold i in Hi.
  assert (Hb : exists b, nth_error (str ++ Z_to_bv 8 0 :: slack) i = Some b /\
                         (bv_unsigned b = bv_unsigned a1 mod 256 -> strchr_res (bv_unsigned a0) (bv_unsigned a1 mod 256) str = bv_unsigned a0 + Z.of_nat i)%Z /\
                         (bv_unsigned b <> bv_unsigned a1 mod 256 -> strchr_res (bv_unsigned a0) (bv_unsigned a1 mod 256) str = 0)%Z).
  { unfold strchr_res. subst i. unfold strchrnul_idx.
    destruct (find_byte (bv_unsigned a1 mod 256) str) as [j|] eqn:FB.
    - destruct (find_byte_Some _ _ _ FB) as (Hj & (b & Hn & Hbb) & _). exists b.
      rewrite nth_error_app1 by lia. split; [exact Hn|].
      destruct (Z.eqb_spec (bv_unsigned a1 mod 256) 0) as [E|NE].
      { exfalso. apply NONUL. replace (Z_to_bv 8 0) with b. { eapply nth_error_In; eauto. } apply bv_eq. rewrite Hbb, E. reflexivity. }
      split; [intros _; reflexivity | intros X; exfalso; exact (X Hbb)].
    - exists (Z_to_bv 8 0). rewrite nth_error_app2, Nat.sub_diag by lia. split; [reflexivity|].
      destruct (Z.eqb_spec (bv_unsigned a1 mod 256) 0) as [E|NE].
      + split; [intros _; reflexivity | intros X; exfalso; apply X; rewrite E; reflexivity].
      + split; [intros X; exfalso; apply NE; rewrite <- X; reflexivity | intros _; reflexivity]. }
  destruct Hb as (b & Hn & Heq & Hne).
  pose proof (u8ro_read usegs _ (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack) (Z.of_nat i) b (wa (bv_unsigned a0 + Z.of_nat i + 0)) STR
                ltac:(rewrite Nat2Z.id; exact Hn) ltac:(lia) ltac:(f_equal; lia)) as RD.
  pose proof (byte_range b) as Rb.
  do 6 zstep.
  replace (Z.land (bv_unsigned a1) 255) with ((bv_unsigned a1) mod 256)%Z.
  2:{ change 255%Z with (2^8 - 1)%Z. rewrite zb_land_mask by lia. reflexivity. }
  do 3 step. release_frame FR ST (bv_unsigned sp). step.
  destruct (Z.eq_dec (bv_unsigned b) (bv_unsigned a1 mod 256)) as [E|NE].
  - rewrite E, Z.lxor_nilpotent. change (Z.b2z (0 <? 0) + -1)%Z with (-1)%Z.
    replace (Z.land ((-1) mod 18446744073709551616) (bv_unsigned a0 + Z.of_nat i))%Z with (bv_unsigned a0 + Z.of_nat i)%Z.
    2:{ change ((-1) mod 18446744073709551616)%Z with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia. rewrite Z.mod_small by lia. reflexivity. }
    rewrite <- (Heq E). unfold strchr_post. finish.
  - assert (Hx : (0 <? Z.lxor (bv_unsigned b) (bv_unsigned a1 mod 256))%Z = true).
    { apply Z.ltb_lt. pose proof (Z.lxor_nonneg (bv_unsigned b) (bv_unsigned a1 mod 256)).
      destruct (Z.eq_dec (Z.lxor (bv_unsigned b) (bv_unsigned a1 mod 256)) 0) as [E0|]; [|lia].
      apply Z.lxor_eq in E0. exfalso. exact (NE E0). }
    rewrite Hx. change (Z.b2z true + -1)%Z with 0%Z. change (0 mod 18446744073709551616)%Z with 0%Z. rewrite Z.land_0_l.
    rewrite <- (Hne NE). unfold strchr_post. finish.
Qed.
End Sz17.
Lemma strchr_spec : ltac:(let t := eval cbv delta [strchr_spec__stmt] in strchr_spec__stmt in exact t).
Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m str slack lo. ltac2:(SecDiet.SzSec.closeP 'strchr_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End TwB.
End F_strchr.

(* [comment removed for export] *)
Module F_fmodeflags.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Bytes SysStep ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memmove__S3.F_strchr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition fmodeflags_entry := 0x1b168%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section ZFacts.
  Local Open Scope Z_scope.
  Notation M64 := 18446744073709551616.

  #[using="Type"] Lemma snez_sub_byte : forall v k k', 0 <= v < 256 -> 0 <= k < 256 -> k + k' = 0 -> (0 <? (v + k') mod M64) = negb (v =? k).
  Proof.
    intros v k k' Hv Hk Hkk. replace k' with (- k) by lia. destruct (Z.eqb_spec v k) as [->|NE].
    - replace (k + - k) with 0 by lia. reflexivity.
    - cbn [negb]. apply Z.ltb_lt. destruct (Z.lt_ge_cases v k).
      + replace (v + - k) with ((M64 + v - k) + (-1) * M64) by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
      + rewrite Z.mod_small by lia. lia.
  Qed.

  #[using="Type"] Lemma seqz_sub_byte : forall v k k', 0 <= v < 256 -> 0 <= k < 256 -> k + k' = 0 -> ((v + k') mod M64 <? 1) = (v =? k).
  Proof.
    intros v k k' Hv Hk Hkk. replace k' with (- k) by lia. destruct (Z.eqb_spec v k) as [->|NE].
    - replace (k + - k) with 0 by lia. reflexivity.
    - apply Z.ltb_ge. destruct (Z.lt_ge_cases v k).
      + replace (v + - k) with ((M64 + v - k) + (-1) * M64) by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
      + rewrite Z.mod_small by lia. lia.
  Qed.

  #[using="Type"] Lemma b2z_shiftl_mod : forall (b : bool) k, 0 <= k < 64 -> (Z.shiftl (Z.b2z b) k) mod M64 = Z.shiftl (Z.b2z b) k.
  Proof.
    intros b k Hk. apply Z.mod_small. rewrite Z.shiftl_mul_pow2 by lia.
    assert (2 ^ k < 2 ^ 64) by (apply Z.pow_lt_mono_r; lia).
    destruct b; cbn [Z.b2z]; lia.
  Qed.

  #[using="Type"] Lemma strchr_res_found : forall A c str, 0 < A -> c <> 0 -> A + Z.of_nat (length str) < M64 ->
    (0 <? strchr_res A c str mod M64) = has_byte c str.
  Proof.
    intros A c str HA Hc HB. unfold strchr_res, has_byte.
    replace (c =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hc).
    destruct (find_byte c str) as [i|] eqn:FB.
    - destruct (find_byte_Some _ _ _ FB) as (Hi & _). rewrite Z.mod_small by lia. apply Z.ltb_lt. lia.
    - reflexivity.
  Qed.
End ZFacts.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition fmodeflags_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 : word) (str slack : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (fmodeflags str)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ssegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
    /\ stk ssegs m' lo (bv_unsigned sp)
    /\ bytes_at ssegs m' (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack).

Local Ltac mi := match goal with H : mem_inv ssegs _ |- _ => exact H end.

(* [comment removed for export] *)
Local Ltac read_b0 STR FULL RD :=
  lazymatch type of STR with bytes_at _ ?mm (bv_unsigned ?a) _ =>
    pose proof (u8ro_read ssegs mm (bv_unsigned a) _ 0 _ a STR ltac:(rewrite FULL; reflexivity) ltac:(lia)
                  ltac:(rewrite Z.add_0_r; symmetry; apply Z_to_bv_bv_unsigned)) as RD
  end.

Definition fmodeflags_spec__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (str slack : list byte) (lo : Z),
  stk ssegs m lo (bv_unsigned sp) ->
  bytes_at ssegs m (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack) ->
  ~ In (Z_to_bv 8 0) str ->
  ((- (bv_unsigned a0 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  mem_inv ssegs m ->
  (lo <= bv_unsigned sp - 64)%Z ->
  (bv_unsigned a0 + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= bv_unsigned sp - 64 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  (0 < bv_unsigned a0)%Z ->
  evt ssegs (fmodeflags_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 str slack lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1b168) fc None m (seg_rom ssegs)).
Section Sz5.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m str slack lo : ltac2:(SecDiet.SzSec.tyM 'fmodeflags_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
#[using="Type"] Lemma fmodeflags_spec__body : ltac2:(SecDiet.SzSec.bodyP 'fmodeflags_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
  intros ST STR NONUL PAD MI LO SEP A0.
  pose proof (bytes_at_bound _ _ _ _ STR) as AB. rewrite length_app in AB. cbn [length] in AB.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ssegs m) as WM.
  pose proof (proj1 ST) as LO0. cbn beta in LO0. pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. cbn in Rsp.
  destruct (str ++ Z_to_bv 8 0 :: slack) as [|b0 rest] eqn:FULL. { destruct str; discriminate. }
  rewrite <- FULL in STR. pose proof (byte_range b0) as Rb0.
  assert (M0 : mode_m0 str = bv_unsigned b0). { destruct str; cbn in FULL; injection FULL; intros; subst; reflexivity. }
  carve_frame 32%nat ST.
  do 7 step.
  step. call_sp strchr_spec; [exact ST | exact STR | exact NONUL | exact PAD | mi | lia | lia | ].
  rename PC into ST; clear STR; rename POST into STR.
  zstep.
  (* [comment removed for export] *)
  assert (JOIN : forall (s1v xa0 : word) mm,
    s1v = Z_to_bv 64 (if has_byte 43 str then 2 else Z.b2z (negb (mode_m0 str =? 114)))%Z ->
    mem_inv ssegs mm -> munch [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m mm -> wmono ssegs m mm ->
    rw_cells ssegs mm (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
    bytes_at ssegs mm (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack) ->
    stk ssegs mm lo (bv_unsigned sp + -32) ->
    evt ssegs (fmodeflags_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 str slack lo m)
      (MS (mkR (Z_to_bv 64 0x1b188) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp x x0 x1 a0 s1v xa0 x2 x3 x4 x5 x6 x7 x8 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x9 x10 x11 x12)
          F (Z_to_bv 64 0x1b1a0) fc None mm (seg_rom ssegs))).
  { clear dependent x13. intros s1v xa0 mm -> MI MU WM FR STR ST.
    zstep. zstep. step. call_sp strchr_spec; [exact ST | exact STR | exact NONUL | exact PAD | mi | lia | lia | ].
    rename PC into ST; clear STR; rename POST into STR.
    zstep. zstep. zstep. zstep. step. call_sp strchr_spec; [exact ST | exact STR | exact NONUL | exact PAD | mi | lia | lia | ].
    rename PC into ST; clear STR; rename POST into STR.
    zstep. read_b0 STR FULL RD.
    do 16 zstep.
    rewrite !b2z_shiftl_mod by lia.
    rewrite !(strchr_res_found (bv_unsigned a0)) by lia.
    rewrite !(snez_sub_byte (bv_unsigned b0) 114 (-114)), !(seqz_sub_byte (bv_unsigned b0) 119 (-119)), !(seqz_sub_byte (bv_unsigned b0) 97 (-97)) by lia.
    rewrite <- !M0.
    setreg 10%Z (Z_to_bv 64 (fmodeflags str)) ltac:(unfold fmodeflags, fmodeflags_w; destruct (has_byte 43 str); reflexivity).
    do 5 step. release_frame FR ST (bv_unsigned sp). step.
    unfold fmodeflags_post. finish. }
  if_cases K1; zify_cond K1.
  - (* [comment removed for export] *)
    read_b0 STR FULL RD. zstep. zstep. zstep.
    eapply JOIN; try eassumption.
    rewrite (snez_sub_byte (bv_unsigned b0) 114 (-114)), <- M0 by lia.
    replace (has_byte 43 str) with false; [reflexivity|].
    rewrite <- (strchr_res_found (bv_unsigned a0)) by lia. symmetry. apply Z.ltb_ge. pose proof (Z.mod_pos_bound (strchr_res (bv_unsigned a0) 43 str) 18446744073709551616). lia.
  - zstep. zstep.
    eapply JOIN; try eassumption.
    replace (has_byte 43 str) with true; [reflexivity|].
    rewrite <- (strchr_res_found (bv_unsigned a0)) by lia. symmetry. apply Z.ltb_lt. pose proof (Z.mod_pos_bound (strchr_res (bv_unsigned a0) 43 str) 18446744073709551616). lia.
Qed.
End Sz5.
Lemma fmodeflags_spec : ltac:(let t := eval cbv delta [fmodeflags_spec__stmt] in fmodeflags_spec__stmt in exact t).
Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m str slack lo. ltac2:(SecDiet.SzSec.closeP 'fmodeflags_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memmove__S3.F_strchr.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition fmodeflags_entry := 0x1b928%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section ZFacts.
  Local Open Scope Z_scope.
  Notation M64 := 18446744073709551616.

  #[using="Type"] Lemma snez_sub_byte : forall v k k', 0 <= v < 256 -> 0 <= k < 256 -> k + k' = 0 -> (0 <? (v + k') mod M64) = negb (v =? k).
  Proof.
    intros v k k' Hv Hk Hkk. replace k' with (- k) by lia. destruct (Z.eqb_spec v k) as [->|NE].
    - replace (k + - k) with 0 by lia. reflexivity.
    - cbn [negb]. apply Z.ltb_lt. destruct (Z.lt_ge_cases v k).
      + replace (v + - k) with ((M64 + v - k) + (-1) * M64) by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
      + rewrite Z.mod_small by lia. lia.
  Qed.

  #[using="Type"] Lemma seqz_sub_byte : forall v k k', 0 <= v < 256 -> 0 <= k < 256 -> k + k' = 0 -> ((v + k') mod M64 <? 1) = (v =? k).
  Proof.
    intros v k k' Hv Hk Hkk. replace k' with (- k) by lia. destruct (Z.eqb_spec v k) as [->|NE].
    - replace (k + - k) with 0 by lia. reflexivity.
    - apply Z.ltb_ge. destruct (Z.lt_ge_cases v k).
      + replace (v + - k) with ((M64 + v - k) + (-1) * M64) by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
      + rewrite Z.mod_small by lia. lia.
  Qed.

  #[using="Type"] Lemma b2z_shiftl_mod : forall (b : bool) k, 0 <= k < 64 -> (Z.shiftl (Z.b2z b) k) mod M64 = Z.shiftl (Z.b2z b) k.
  Proof.
    intros b k Hk. apply Z.mod_small. rewrite Z.shiftl_mul_pow2 by lia.
    assert (2 ^ k < 2 ^ 64) by (apply Z.pow_lt_mono_r; lia).
    destruct b; cbn [Z.b2z]; lia.
  Qed.

  #[using="Type"] Lemma strchr_res_found : forall A c str, 0 < A -> c <> 0 -> A + Z.of_nat (length str) < M64 ->
    (0 <? strchr_res A c str mod M64) = has_byte c str.
  Proof.
    intros A c str HA Hc HB. unfold strchr_res, has_byte.
    replace (c =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hc).
    destruct (find_byte c str) as [i|] eqn:FB.
    - destruct (find_byte_Some _ _ _ FB) as (Hi & _). rewrite Z.mod_small by lia. apply Z.ltb_lt. lia.
    - reflexivity.
  Qed.
End ZFacts.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition fmodeflags_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 : word) (str slack : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (fmodeflags str)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ bytes_at usegs m' (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack).

Local Ltac mi := match goal with H : mem_inv usegs _ |- _ => exact H end.

(* [comment removed for export] *)
Local Ltac read_b0 STR FULL RD :=
  lazymatch type of STR with bytes_at _ ?mm (bv_unsigned ?a) _ =>
    pose proof (u8ro_read usegs mm (bv_unsigned a) _ 0 _ a STR ltac:(rewrite FULL; reflexivity) ltac:(lia)
                  ltac:(rewrite Z.add_0_r; symmetry; apply Z_to_bv_bv_unsigned)) as RD
  end.

Definition fmodeflags_spec__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (str slack : list byte) (lo : Z),
  stk usegs m lo (bv_unsigned sp) ->
  bytes_at usegs m (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack) ->
  ~ In (Z_to_bv 8 0) str ->
  ((- (bv_unsigned a0 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  mem_inv usegs m ->
  (lo <= bv_unsigned sp - 64)%Z ->
  (bv_unsigned a0 + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= bv_unsigned sp - 64 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  (0 < bv_unsigned a0)%Z ->
  evt usegs (fmodeflags_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 str slack lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1b928) fc None m (seg_rom usegs)).
Section Sz5.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m str slack lo : ltac2:(SecDiet.SzSec.tyM 'fmodeflags_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
#[using="Type"] Lemma fmodeflags_spec__body : ltac2:(SecDiet.SzSec.bodyP 'fmodeflags_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
 intros ST STR NONUL PAD MI LO SEP A0.
  pose proof (bytes_at_bound _ _ _ _ STR) as AB. rewrite length_app in AB. cbn [length] in AB.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (proj1 ST) as LO0. cbn beta in LO0. pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. cbn in Rsp.
  destruct (str ++ Z_to_bv 8 0 :: slack) as [|b0 rest] eqn:FULL. { destruct str; discriminate. }
  rewrite <- FULL in STR. pose proof (byte_range b0) as Rb0.
  assert (M0 : mode_m0 str = bv_unsigned b0). { destruct str; cbn in FULL; injection FULL; intros; subst; reflexivity. }
  carve_frame 32%nat ST.
  do 7 step.
  step. call_sp strchr_spec; [exact ST | exact STR | exact NONUL | exact PAD | mi | lia | lia | ].
  rename PC into ST; clear STR; rename POST into STR.
  zstep.
  (* [comment removed for export] *)
  assert (JOIN : forall (s1v xa0 : word) mm,
    s1v = Z_to_bv 64 (if has_byte 43 str then 2 else Z.b2z (negb (mode_m0 str =? 114)))%Z ->
    mem_inv usegs mm -> munch [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m mm -> wmono usegs m mm ->
    rw_cells usegs mm (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
    bytes_at usegs mm (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack) ->
    stk usegs mm lo (bv_unsigned sp + -32) ->
    evt usegs (fmodeflags_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 str slack lo m)
      (MS (mkR (Z_to_bv 64 0x1b948) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp x x0 x1 a0 s1v xa0 x2 x3 x4 x5 x6 x7 x8 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x9 x10 x11 x12)
          F (Z_to_bv 64 0x1b960) fc None mm (seg_rom usegs))).
  { clear dependent x13. intros s1v xa0 mm -> MI MU WM FR STR ST.
    zstep. zstep. step. call_sp strchr_spec; [exact ST | exact STR | exact NONUL | exact PAD | mi | lia | lia | ].
    rename PC into ST; clear STR; rename POST into STR.
    zstep. zstep. zstep. zstep. step. call_sp strchr_spec; [exact ST | exact STR | exact NONUL | exact PAD | mi | lia | lia | ].
    rename PC into ST; clear STR; rename POST into STR.
    zstep. read_b0 STR FULL RD.
    do 16 zstep.
    rewrite !b2z_shiftl_mod by lia.
    rewrite !(strchr_res_found (bv_unsigned a0)) by lia.
    rewrite !(snez_sub_byte (bv_unsigned b0) 114 (-114)), !(seqz_sub_byte (bv_unsigned b0) 119 (-119)), !(seqz_sub_byte (bv_unsigned b0) 97 (-97)) by lia.
    rewrite <- !M0.
    setreg 10%Z (Z_to_bv 64 (fmodeflags str)) ltac:(unfold fmodeflags, fmodeflags_w; destruct (has_byte 43 str); reflexivity).
    do 5 step. release_frame FR ST (bv_unsigned sp). step.
    unfold fmodeflags_post. finish. }
  if_cases K1; zify_cond K1.
  - (* [comment removed for export] *)
    read_b0 STR FULL RD. zstep. zstep. zstep.
    eapply JOIN; try eassumption.
    rewrite (snez_sub_byte (bv_unsigned b0) 114 (-114)), <- M0 by lia.
    replace (has_byte 43 str) with false; [reflexivity|].
    rewrite <- (strchr_res_found (bv_unsigned a0)) by lia. symmetry. apply Z.ltb_ge. pose proof (Z.mod_pos_bound (strchr_res (bv_unsigned a0) 43 str) 18446744073709551616). lia.
  - zstep. zstep.
    eapply JOIN; try eassumption.
    replace (has_byte 43 str) with true; [reflexivity|].
    rewrite <- (strchr_res_found (bv_unsigned a0)) by lia. symmetry. apply Z.ltb_lt. pose proof (Z.mod_pos_bound (strchr_res (bv_unsigned a0) 43 str) 18446744073709551616). lia.
Qed.
End Sz5.
Lemma fmodeflags_spec : ltac:(let t := eval cbv delta [fmodeflags_spec__stmt] in fmodeflags_spec__stmt in exact t).
Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m str slack lo. ltac2:(SecDiet.SzSec.closeP 'fmodeflags_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End TwB.
End F_fmodeflags.

(* [comment removed for export] *)
Module Startup_A.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Monad. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Import F_memcpy.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac us_hide H := lazymatch type of H with ?T => let X := fresh "AUX" in pose (X := T); change T with X in H end.
Local Ltac us_unhide H := lazymatch type of H with ?X => subst X end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation LIBC := 0x53d28%Z (only parsing).       (* [comment removed for export] *)
Notation TLL := 0x53aa0%Z (only parsing).        (* [comment removed for export] *)
Notation SYSINFO := 0x53d10%Z (only parsing).    (* [comment removed for export] *)
Notation DEFSTACK := 0x23930%Z (only parsing).   (* [comment removed for export] *)
Notation GOT_DYNAMIC := 0x22580%Z (only parsing). (* [comment removed for export] *)
Notation TLS_IMAGE := 0x2154c%Z (only parsing).  (* [comment removed for export] *)

Section WithCeil.
Context {CEILV : CEIL}.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition memcpy0_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ssegs)
    /\ munch [] m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'.

Definition memcpy0_spec__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  mem_inv ssegs m -> a2 = z64 ->
  evt ssegs (memcpy0_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x207e0) fc None m (seg_rom ssegs)).
Section Sz3.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m : ltac2:(SecDiet.SzSec.tyM 'memcpy0_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma memcpy0_spec__body : ltac2:(SecDiet.SzSec.bodyP 'memcpy0_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
  intros MI ->.
  pose proof (bv_unsigned_in_range 64 a0) as R0. pose proof (bv_unsigned_in_range 64 a1) as R1. unfold bv_modulus in R0, R1. cbn in R0, R1.
  assert (E2 : bv_unsigned z64 = 0%Z) by reflexivity.
  eapply evt_mono.
  { eapply (memcpy_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m [] []); rewrite ?E2.
    - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
    - reflexivity.
    - split; [split; [cbn; split; [reflexivity|exact I] |] |].
      + split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
      + cbn [cells_size csize Nat.add]. split; [lia|]. split; [lia|]. intros i Hi. lia.
    - lia.
    - exact MI. }
  intros ms' PO. unfold memcpy_post in PO.
  destruct PO as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m' & E & MU & WM & MI' & _).
  unfold memcpy0_post. do 15 eexists. split; [exact E|]. split; [|split; [exact WM|exact MI']].
  intros x _. apply MU. cbn. lia.
Qed.
End Sz3.
Lemma memcpy0_spec : ltac:(let t := eval cbv delta [memcpy0_spec__stmt] in memcpy0_spec__stmt in exact t).
Proof using CEILV. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m. ltac2:(SecDiet.SzSec.closeP 'memcpy0_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section InitTls.
  Context {St : Type} (set_tls : Z -> St -> St).

  Definition init_tls_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo : Z) (aux : Z) (can_do threaded secure need_locks : byte) (tm1 auxvp page_size sysinfo lock : word) (locale : list byte)
      (m : word -> option byte) (s : St) : unit -> St -> machine_state -> Prop :=
    fun _ s' ms' => exists (tb t : Z) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      (tls_block_ok tb /\ (0 < t < 4194304)%Z /\ s' = set_tls tb s)
      /\ ms' = MS (mkR ra sp gp (Z_to_bv 64 (tb + 200)) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom ssegs)
      /\ munch [(tb, tb + 4096); (bv_unsigned sp - 64, bv_unsigned sp); (0x53aa8, 0x53ad8); (LIBC, 0x53d58)]%Z m m'
      /\ wmono ssegs m m' /\ mem_inv ssegs m'
      /\ stk ssegs m' lo (bv_unsigned sp)
      /\ rw_cells ssegs m' tb (tls_cells (Z_to_bv 64 tb) (Z_to_bv 64 tb) (Z_to_bv 64 tb) sysinfo (Z_to_bv 64 t) z64 (Z_to_bv 64 2)
                                      (Z_to_bv 64 (tb + 120)) (Z_to_bv 64 0x53d60) (* [comment removed for export] *) z64 (Z_to_bv 64 (tb + 464))
                                      (repeat (Z_to_bv 8 0) 256) (Z_to_bv 64 1) (Z_to_bv 64 (tb + 2248)))
      /\ rw_cells ssegs m' LIBC (libc_cells (Z_to_bv 8 1) threaded secure need_locks tm1 auxvp
                                   (Z_to_bv 64 0x53aa8) (Z_to_bv 64 480) (Z_to_bv 64 8) (Z_to_bv 64 1) page_size locale)
      /\ rw_cells ssegs m' TLL (tll_cells lock z64 (Z_to_bv 64 TLS_IMAGE) z64 (Z_to_bv 64 0x100) (Z_to_bv 64 8) z64)
      /\ rw_cells ssegs m' (aux + 24) [C8 (Z_to_bv 64 0x10040); C8 (Z_to_bv 64 56); C8 (Z_to_bv 64 11)]
      /\ rw_cells ssegs m' SYSINFO [C8 sysinfo]
      /\ rw_cells ssegs m' DEFSTACK [C4 (Z_to_bv 64 0x20000)]
      /\ rw_cells ssegs m' GOT_DYNAMIC [C8 z64].

  Definition init_tls_spec__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : word -> option byte) (lo aux : Z)
      (can_do threaded secure need_locks : byte) (tm1 auxvp page_size sysinfo lock : word) (locale : list byte) (s : St),
    stk ssegs m lo (bv_unsigned sp) ->
    (* [comment removed for export] *)
    rw_cells ssegs m (aux + 24) [C8 (Z_to_bv 64 0x10040); C8 (Z_to_bv 64 56); C8 (Z_to_bv 64 11)] ->
    rw_cells ssegs m LIBC (libc_cells can_do threaded secure need_locks tm1 auxvp z64 z64 z64 z64 page_size locale) ->
    rw_cells ssegs m TLL (tll_cells lock z64 z64 z64 z64 z64 z64) ->
    rw_cells ssegs m SYSINFO [C8 sysinfo] ->
    rw_cells ssegs m DEFSTACK [C4 (Z_to_bv 64 0x20000)] ->
    rw_cells ssegs m GOT_DYNAMIC [C8 z64] ->
    rw_cells ssegs m 0x339d0 [CB 4096 (repeat (Z_to_bv 8 0) 4096)] ->
    mem_inv ssegs m ->
    a0 = Z_to_bv 64 aux ->
    (lo <= bv_unsigned sp - 64)%Z -> (alloc_ceiling <= lo)%Z ->
    (bv_unsigned sp <= aux)%Z -> (aux + 48 <= 2^64)%Z ->
    implM ssegs (startup_model set_tls 0x339d0) s
          (init_tls_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo aux can_do threaded secure need_locks tm1 auxvp page_size sysinfo lock locale m s)
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x17f0c) fc None m (seg_rom ssegs)).
  Section Sz4.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo aux can_do threaded secure need_locks tm1 auxvp page_size sysinfo lock locale s : ltac2:(SecDiet.SzSec.tyM 'init_tls_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma init_tls_spec__body : ltac2:(SecDiet.SzSec.bodyP 'init_tls_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt. ceil_facts.
    intros ST AUX LC MT SI DS GD ZNEW MI -> LO LOLO A0LO A0HI.
    unfold tll_cells, libc_cells in *.
    pose proof (munch_refl [(0x339d0, 0x339d0 + 4096); (bv_unsigned sp - 64, bv_unsigned sp); (0x53aa8, 0x53ad8); (LIBC, 0x53d58)]%Z m) as MU.
    pose proof (wmono_refl ssegs m) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    apply (rw_cells_recast ssegs _ _ _ (tls_cells z64 z64 z64 z64 z64 z64 z64 z64 z64 z64 z64 (repeat (Z_to_bv 8 0) 256) z64 z64)) in ZNEW;
      [| cbn; repeat split; reflexivity | vm_compute; reflexivity | reflexivity].
    unfold tls_cells in ZNEW. rename ZNEW into TLS.
    (* [comment removed for export] *)
    lazymatch type of TLS with rw_cells ?sg ?mm ?A ?cs =>
      apply (proj1 (rw_cells_app sg mm A (firstn 18 cs) (skipn 18 cs))) in TLS;
      lazymatch type of MU with munch (_ :: ?WR) _ _ => pose proof (munch_refl ((0x339d0, 0x339d0 + 480)%Z :: WR) mm) as MUR end;
      pose proof (wmono_refl sg mm) as WMR end.
    destruct TLS as [TLS TLSR]. cbn [firstn skipn cells_size csize Nat.add] in TLS, TLSR. change (Z.of_nat 480) with 480%Z in TLSR.
    us_hide TLSR.
    unfold startup_model. apply implM_upd_bind. apply implM_sys_bind.
    carve_frame 64%nat ST.
    steps_to 0x17f94%Z.
    steps_to 0x17fe4%Z.
    steps_to 0x18118%Z.
    (* [comment removed for export] *)
    astep. call memcpy0_spec; [first [exact MI0 | exact MI] | reflexivity |].
    steps_to 0x1813c%Z.
    (* [comment removed for export] *)
    steps_to 0x18168%Z.
    step_ecall.
    split. { at_node_solve. }
    intros rsp t Hdec. apply dec_set_tid_Some in Hdec. destruct Hdec as [-> Ht]. unfold Fork.PID_MAX_ENVELOPE in Ht.
    apply implM_ret. unfold eff0. sys_nret.
    (* [comment removed for export] *)
    steps_to 0x181b4%Z. astep.
    release_frame FR ST (bv_unsigned sp). astep.
    us_unhide TLSR.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let T2 := fresh "TLSR" in
      pose proof (rw_cells_transport _ _ _ mm _ _ TLSR MUR WMR ltac:(sl_lit_sizes; cbn [disjoint_from cells_size csize Nat.add]; lia)) as T2;
      clear TLSR; rename T2 into TLSR end.
    clear MUR WMR.
    lazymatch type of TLS with rw_cells ?sg ?mm ?A ?csF =>
      lazymatch type of TLSR with rw_cells _ _ ?A2 ?csR =>
        replace A2 with (A + Z.of_nat (cells_size csF))%Z in TLSR by (sl_lit_sizes; cbn [cells_size csize Nat.add]; lia);
        let TLS2 := fresh "TLS" in pose proof (proj2 (rw_cells_app sg mm A csF csR) (conj TLS TLSR)) as TLS2; clear TLS TLSR; rename TLS2 into TLS end end.
    cbn [app] in TLS.
    apply evt_done. unfold init_tls_post, tls_cells, libc_cells, tll_cells.
    (* [comment removed for export] *)
    let z := fresh "sblz" in pose (z := repeat (Z_to_bv 8 0) 3616); change (repeat (Z_to_bv 8 0) 3616) with z.
    let x := fresh "sbl" in pose (x := 3616%nat); change 3616%nat with x.
    let z := fresh "sblz" in pose (z := repeat (Z_to_bv 8 0) 256); change (repeat (Z_to_bv 8 0) 256) with z.
    exists 0x339d0%Z, t.
    repeat (lazymatch goal with |- ex _ => eexists end).
    split. { unfold tls_block_ok. repeat split; fastfirst (first [lia | reflexivity]). }
    split. { cbv delta [mkR]. reflexivity. }
    repeat match goal with |- _ /\ _ => split end; fastfirst (first [hyp_by_addr | assumption | lia]).
  Qed.
  End Sz4.
  Lemma init_tls_spec : ltac:(let t := eval cbv delta [init_tls_spec__stmt] in init_tls_spec__stmt in exact t).
  Proof using Type. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo aux can_do threaded secure need_locks tm1 auxvp page_size sysinfo lock locale s. ltac2:(SecDiet.SzSec.closeP 'init_tls_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End InitTls.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.RegsEquiv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac us_hide H := lazymatch type of H with ?T => let X := fresh "AUX" in pose (X := T); change T with X in H end.
Local Ltac us_unhide H := lazymatch type of H with ?X => subst X end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation LIBC := 0x544e8%Z (only parsing).       (* [comment removed for export] *)
Notation TLL := 0x54260%Z (only parsing).        (* [comment removed for export] *)
Notation SYSINFO := 0x544d0%Z (only parsing).    (* [comment removed for export] *)
Notation DEFSTACK := 0x240f0%Z (only parsing).   (* [comment removed for export] *)
Notation GOT_DYNAMIC := 0x22d40%Z (only parsing). (* [comment removed for export] *)
Notation TLS_IMAGE := 0x21d0c%Z (only parsing).  (* [comment removed for export] *)

Section WithCeil.
Context {CEILV : CEIL}.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition memcpy0_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [] m m' /\ wmono usegs m m' /\ mem_inv usegs m'.

Definition memcpy0_spec__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  mem_inv usegs m -> a2 = z64 ->
  evt usegs (memcpy0_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x20fa0) fc None m (seg_rom usegs)).
Section Sz3.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m : ltac2:(SecDiet.SzSec.tyM 'memcpy0_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma memcpy0_spec__body : ltac2:(SecDiet.SzSec.bodyP 'memcpy0_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
 intros MI ->.
  pose proof (bv_unsigned_in_range 64 a0) as R0. pose proof (bv_unsigned_in_range 64 a1) as R1. unfold bv_modulus in R0, R1. cbn in R0, R1.
  assert (E2 : bv_unsigned z64 = 0%Z) by reflexivity.
  eapply evt_mono.
  { eapply (memcpy_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m [] []); rewrite ?E2.
    - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
    - reflexivity.
    - split; [split; [cbn; split; [reflexivity|exact I] |] |].
      + split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
      + cbn [cells_size csize Nat.add]. split; [lia|]. split; [lia|]. intros i Hi. lia.
    - lia.
    - exact MI. }
  intros ms' PO. unfold memcpy_post in PO.
  destruct PO as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m' & E & MU & WM & MI' & _).
  unfold memcpy0_post. do 15 eexists. split; [exact E|]. split; [|split; [exact WM|exact MI']].
  intros x _. apply MU. cbn. lia.
Qed.
End Sz3.
Lemma memcpy0_spec : ltac:(let t := eval cbv delta [memcpy0_spec__stmt] in memcpy0_spec__stmt in exact t).
Proof using CEILV. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m. ltac2:(SecDiet.SzSec.closeP 'memcpy0_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section InitTls.
  Context {St : Type} (set_tls : Z -> St -> St).

  Definition init_tls_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo : Z) (aux : Z) (can_do threaded secure need_locks : byte) (tm1 auxvp page_size sysinfo lock : word) (locale : list byte)
      (m : word -> option byte) (s : St) : unit -> St -> machine_state -> Prop :=
    fun _ s' ms' => exists (tb t : Z) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      (tls_block_ok_u tb /\ (0 < t < 4194304)%Z /\ s' = set_tls tb s)
      /\ ms' = MS (mkR ra sp gp (Z_to_bv 64 (tb + 200)) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ munch [(tb, tb + 4096); (bv_unsigned sp - 64, bv_unsigned sp); (0x54268, 0x54298); (LIBC, 0x54518)]%Z m m'
      /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ stk usegs m' lo (bv_unsigned sp)
      /\ rw_cells usegs m' tb (tls_cells (Z_to_bv 64 tb) (Z_to_bv 64 tb) (Z_to_bv 64 tb) sysinfo (Z_to_bv 64 t) z64 (Z_to_bv 64 2)
                                      (Z_to_bv 64 (tb + 120)) (Z_to_bv 64 0x54520) (* [comment removed for export] *) z64 (Z_to_bv 64 (tb + 464))
                                      (repeat (Z_to_bv 8 0) 256) (Z_to_bv 64 1) (Z_to_bv 64 (tb + 2248)))
      /\ rw_cells usegs m' LIBC (libc_cells (Z_to_bv 8 1) threaded secure need_locks tm1 auxvp
                                   (Z_to_bv 64 0x54268) (Z_to_bv 64 480) (Z_to_bv 64 8) (Z_to_bv 64 1) page_size locale)
      /\ rw_cells usegs m' TLL (tll_cells lock z64 (Z_to_bv 64 TLS_IMAGE) z64 (Z_to_bv 64 0x100) (Z_to_bv 64 8) z64)
      /\ rw_cells usegs m' (aux + 24) [C8 (Z_to_bv 64 0x10040); C8 (Z_to_bv 64 56); C8 (Z_to_bv 64 11)]
      /\ rw_cells usegs m' SYSINFO [C8 sysinfo]
      /\ rw_cells usegs m' DEFSTACK [C4 (Z_to_bv 64 0x20000)]
      /\ rw_cells usegs m' GOT_DYNAMIC [C8 z64].

  Definition init_tls_spec__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : word -> option byte) (lo aux : Z)
      (can_do threaded secure need_locks : byte) (tm1 auxvp page_size sysinfo lock : word) (locale : list byte) (s : St),
    stk usegs m lo (bv_unsigned sp) ->
    (* [comment removed for export] *)
    rw_cells usegs m (aux + 24) [C8 (Z_to_bv 64 0x10040); C8 (Z_to_bv 64 56); C8 (Z_to_bv 64 11)] ->
    rw_cells usegs m LIBC (libc_cells can_do threaded secure need_locks tm1 auxvp z64 z64 z64 z64 page_size locale) ->
    rw_cells usegs m TLL (tll_cells lock z64 z64 z64 z64 z64 z64) ->
    rw_cells usegs m SYSINFO [C8 sysinfo] ->
    rw_cells usegs m DEFSTACK [C4 (Z_to_bv 64 0x20000)] ->
    rw_cells usegs m GOT_DYNAMIC [C8 z64] ->
    rw_cells usegs m 0x34190 [CB 4096 (repeat (Z_to_bv 8 0) 4096)] ->
    mem_inv usegs m ->
    a0 = Z_to_bv 64 aux ->
    (lo <= bv_unsigned sp - 64)%Z -> (alloc_ceiling <= lo)%Z ->
    (bv_unsigned sp <= aux)%Z -> (aux + 48 <= 2^64)%Z ->
    implM usegs (startup_model set_tls 0x34190) s
          (init_tls_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo aux can_do threaded secure need_locks tm1 auxvp page_size sysinfo lock locale m s)
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x186cc) fc None m (seg_rom usegs)).
  Section Sz4.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo aux can_do threaded secure need_locks tm1 auxvp page_size sysinfo lock locale s : ltac2:(SecDiet.SzSec.tyM 'init_tls_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma init_tls_spec__body : ltac2:(SecDiet.SzSec.bodyP 'init_tls_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt. ceil_facts.
 intros ST AUX LC MT SI DS GD ZNEW MI -> LO LOLO A0LO A0HI.
    unfold tll_cells, libc_cells in *.
    pose proof (munch_refl [(0x34190, 0x34190 + 4096); (bv_unsigned sp - 64, bv_unsigned sp); (0x54268, 0x54298); (LIBC, 0x54518)]%Z m) as MU.
    pose proof (wmono_refl usegs m) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    apply (rw_cells_recast usegs _ _ _ (tls_cells z64 z64 z64 z64 z64 z64 z64 z64 z64 z64 z64 (repeat (Z_to_bv 8 0) 256) z64 z64)) in ZNEW;
      [| cbn; repeat split; reflexivity | vm_compute; reflexivity | reflexivity].
    unfold tls_cells in ZNEW. rename ZNEW into TLS.
    (* [comment removed for export] *)
    lazymatch type of TLS with rw_cells ?sg ?mm ?A ?cs =>
      apply (proj1 (rw_cells_app sg mm A (firstn 18 cs) (skipn 18 cs))) in TLS;
      lazymatch type of MU with munch (_ :: ?WR) _ _ => pose proof (munch_refl ((0x34190, 0x34190 + 480)%Z :: WR) mm) as MUR end;
      pose proof (wmono_refl sg mm) as WMR end.
    destruct TLS as [TLS TLSR]. cbn [firstn skipn cells_size csize Nat.add] in TLS, TLSR. change (Z.of_nat 480) with 480%Z in TLSR.
    us_hide TLSR.
    unfold startup_model. apply implM_upd_bind. apply implM_sys_bind.
    carve_frame 64%nat ST.
    steps_to 0x18754%Z.
    steps_to 0x187a4%Z.
    steps_to 0x188d8%Z.
    (* [comment removed for export] *)
    astep. call memcpy0_spec; [first [exact MI0 | exact MI] | reflexivity |].
    steps_to 0x188fc%Z.
    (* [comment removed for export] *)
    steps_to 0x18928%Z.
    step_ecall.
    split. { at_node_solve. }
    intros rsp t Hdec. apply dec_set_tid_Some in Hdec. destruct Hdec as [-> Ht]. unfold Fork.PID_MAX_ENVELOPE in Ht.
    apply implM_ret. unfold eff0. sys_nret.
    (* [comment removed for export] *)
    steps_to 0x18974%Z. astep.
    release_frame FR ST (bv_unsigned sp). astep.
    us_unhide TLSR.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let T2 := fresh "TLSR" in
      pose proof (rw_cells_transport _ _ _ mm _ _ TLSR MUR WMR ltac:(sl_lit_sizes; cbn [disjoint_from cells_size csize Nat.add]; lia)) as T2;
      clear TLSR; rename T2 into TLSR end.
    clear MUR WMR.
    lazymatch type of TLS with rw_cells ?sg ?mm ?A ?csF =>
      lazymatch type of TLSR with rw_cells _ _ ?A2 ?csR =>
        replace A2 with (A + Z.of_nat (cells_size csF))%Z in TLSR by (sl_lit_sizes; cbn [cells_size csize Nat.add]; lia);
        let TLS2 := fresh "TLS" in pose proof (proj2 (rw_cells_app sg mm A csF csR) (conj TLS TLSR)) as TLS2; clear TLS TLSR; rename TLS2 into TLS end end.
    cbn [app] in TLS.
    apply evt_done. unfold init_tls_post, tls_cells, libc_cells, tll_cells.
    (* [comment removed for export] *)
    let z := fresh "sblz" in pose (z := repeat (Z_to_bv 8 0) 3616); change (repeat (Z_to_bv 8 0) 3616) with z.
    let x := fresh "sbl" in pose (x := 3616%nat); change 3616%nat with x.
    let z := fresh "sblz" in pose (z := repeat (Z_to_bv 8 0) 256); change (repeat (Z_to_bv 8 0) 256) with z.
    exists 0x34190%Z, t.
    repeat (lazymatch goal with |- ex _ => eexists end).
    split. { unfold tls_block_ok_u. repeat split; fastfirst (first [lia | reflexivity]). }
    split. { cbv delta [mkR]. reflexivity. }
    repeat match goal with |- _ /\ _ => split end; fastfirst (first [hyp_by_addr | assumption | lia]).
  Qed.
  End Sz4.
  Lemma init_tls_spec : ltac:(let t := eval cbv delta [init_tls_spec__stmt] in init_tls_spec__stmt in exact t).
  Proof using Type. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo aux can_do threaded secure need_locks tm1 auxvp page_size sysinfo lock locale s. ltac2:(SecDiet.SzSec.closeP 'init_tls_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End InitTls.

End WithCeil.
End TwB.
End Startup_A.

(* [comment removed for export] *)
Module F_fopen.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad StdioCore. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.F_memset OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_lock OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memmove__S3.F_strchr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memmove__S3.F_fmodeflags OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition FOPEN : Z := 0x1b08c.
Definition FDOPEN : Z := 0x1b21c.
Definition OFL_ADD : Z := 0x1b9a4.
Definition STR_RWA : Z := 0x10e6a.

Local Ltac mi := match goal with H : mem_inv ssegs _ |- _ => exact H end.

(* [comment removed for export] *)
Lemma rwa_bytes : forall m, mem_inv ssegs m ->
  bytes_at ssegs m STR_RWA ([Z_to_bv 8 114; Z_to_bv 8 119; Z_to_bv 8 97] ++ Z_to_bv 8 0 :: [Z_to_bv 8 47; Z_to_bv 8 100]).
Proof.
  intros m MI. unfold STR_RWA. apply ro_bytes_at; [exact MI | lia | cbn; lia |]. apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Lemma rwa_has : forall c, c = 114 \/ c = 119 -> has_byte c [Z_to_bv 8 114; Z_to_bv 8 119; Z_to_bv 8 97] = true.
Proof. intros c [-> | ->]; reflexivity. Qed.

(* [comment removed for export] *)
Definition flk_cells (flags : word)
    (rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd : Z)
    (mode lock lbf : word) (tail : list byte) : list cell :=
  [C4 flags; C4 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 rpos); C8 (Z_to_bv 64 rend); C8 (Z_to_bv 64 closefn);
   C8 (Z_to_bv 64 wend); C8 (Z_to_bv 64 wpos); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 wbase);
   C8 (Z_to_bv 64 readfn); C8 (Z_to_bv 64 writefn); C8 (Z_to_bv 64 seekfn);
   C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 bufsize);
   C8 (Z_to_bv 64 prev); C8 (Z_to_bv 64 next);
   C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C4 mode; C4 lock; C4 lbf; C4 (Z_to_bv 64 0);
   CB 80 tail].

Lemma bytes_eq_of_unsigned' : forall bs bs' : list byte, map bv_unsigned bs = map bv_unsigned bs' -> bs = bs'.
Proof.
  induction bs as [|b bs IH]; intros [|b' bs'] E; cbn in E; try discriminate E; [reflexivity|].
  injection E as E1 E2. f_equal; [apply bv_eq; exact E1 | apply IH; exact E2].
Qed.

Lemma zero_file_cells : forall m P,
  rw_cells ssegs m P [CB (Z.to_nat 232) (repeat (Z_to_bv 8 (0 mod 256)) (Z.to_nat 232))] ->
  rw_cells ssegs m P (flk_cells (Z_to_bv 64 0) 0 0 0 0 0 0 0 0 0 0 0 0 0 0 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (repeat (Z_to_bv 8 0) 80)).
Proof.
  intros m P H. eapply rw_cells_recast; [exact H | | |].
  - vm_compute. repeat split; exact I.
  - apply bytes_eq_of_unsigned'. vm_compute. reflexivity.
  - reflexivity.
Qed.

Definition memset_postv (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Dst V N : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ssegs)
    /\ munch [(Dst, Dst + N)] m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
    /\ rw_cells ssegs m' Dst [CB (Z.to_nat N) (repeat (Z_to_bv 8 (V mod 256)) (Z.to_nat N))].
Definition memset_callw__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (Dst V N : Z) (junk : list byte),
  rw_cells ssegs m Dst [CB (Z.to_nat N) junk] ->
  (0 <= N) -> (0 <= Dst) -> (Dst + N < 2^64) -> (0 <= V < 2^64) -> mem_inv ssegs m ->
  evt ssegs (memset_postv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Dst V N m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) (Z_to_bv 64 V) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x20d60) fc None m (seg_rom ssegs)).
Section Sz5.
Variables ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Dst V N junk : ltac2:(SecDiet.SzSec.tyM 'memset_callw__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
#[using="Type"] Lemma memset_callw__body : ltac2:(SecDiet.SzSec.bodyP 'memset_callw__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
  intros DST HN HD HDN HV MI.
  assert (ED : bv_unsigned (Z_to_bv 64 Dst : word) = Dst) by (apply unsigned_lit; lia).
  assert (EV : bv_unsigned (Z_to_bv 64 V : word) = V) by (apply unsigned_lit; lia).
  assert (EN : bv_unsigned (Z_to_bv 64 N : word) = N) by (apply unsigned_lit; lia).
  eapply evt_mono. { eapply memset_spec with (junk := junk); rewrite ?ED, ?EN; [exact DST | exact MI]. }
  intros ms' PO. unfold memset_post, memset_postv in *. rewrite ED, EV, EN in PO. exact PO.
Qed.
End Sz5.
Lemma memset_callw : ltac:(let t := eval cbv delta [memset_callw__stmt] in memset_callw__stmt in exact t).
Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Dst V N junk. ltac2:(SecDiet.SzSec.closeP 'memset_callw__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

Lemma le4_m1 : le4 (Z_to_bv 64 (-1)) = le4 (Z_to_bv 64 4294967295).
Proof. apply bytes_eq_of_unsigned'. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma fdopen_cells_recast : forall m P flags closefn readfn writefn seekfn buf bufsize prev next fd mode tail,
  rw_cells ssegs m P (flk_cells flags 0 0 closefn 0 0 0 readfn writefn seekfn buf bufsize prev next fd mode (Z_to_bv 64 (-1)) (Z_to_bv 64 (-1)) tail) ->
  rw_cells ssegs m P (file_cells flags 0 0 closefn 0 0 0 readfn writefn seekfn buf bufsize prev next fd mode 4294967295 tail).
Proof.
  intros. eapply rw_cells_recast; [exact H | | |].
  - destruct H as [[W _] _]. unfold flk_cells, file_cells in *. cbn in W |- *. exact W.
  - unfold flk_cells, file_cells. cbn [cells_bytes cbytes app]. rewrite !le4_m1. reflexivity.
  - reflexivity.
Qed.

Lemma strchr_res_notfound : forall A c str, c <> 0 -> has_byte c str = false -> strchr_res A c str = 0.
Proof.
  intros A c str Hc H. unfold strchr_res, has_byte in *. replace (c =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hc).
  destruct (find_byte c str); [discriminate H| reflexivity].
Qed.

Section Fopen.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (NAME MODE lo : Z) (md slack : list byte) (m : mem).

  Hypothesis LO : lo <= bv_unsigned sp - 512.
  Hypothesis GLO : 0x55000 <= lo.
  Hypothesis SP47 : bv_unsigned sp <= 2^47.
  Hypothesis MDR : 0x10000 <= MODE /\ MODE + Z.of_nat (length md) + 1 + Z.of_nat (length slack) <= 0x13000.
  Hypothesis NONUL : ~ In (Z_to_bv 8 0) md.
  Hypothesis PAD : (- (MODE + Z.of_nat (length md) + 1)) mod 8 <= Z.of_nat (length slack).
  Hypothesis M0 : mode_m0 md = 114 \/ mode_m0 md = 119.
  Hypothesis NAMER : 0 <= NAME < 2^64.
  (* [comment removed for export] *)
  Hypothesis TPR : bv_unsigned tp + -200 = 0x339d0.
  Hypothesis TPLO : bv_unsigned tp + -160 <= lo.
  Hypothesis TP200 : 200 <= bv_unsigned tp.

  (* [comment removed for export] *)
  Definition fopen_S1_post : machine_state -> Prop :=
    fun ms' => exists (x1 t0 t1 t2 a4 a5 a6 t3 t4 t5 t6 : word) (m1 : mem),
      ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 MODE) (Z_to_bv 64 NAME)
                   (Z_to_bv 64 (-100)) (Z_to_bv 64 NAME) (Z_to_bv 64 (Z.lor (fmodeflags md mod 18446744073709551616) 32768)) (Z_to_bv 64 438) a4 a5 a6 (Z_to_bv 64 56)
                   (Z_to_bv 64 (fmodeflags md)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x1b0e0) fc None m1 (seg_rom ssegs)
      /\ rw_cells ssegs m1 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra]
      /\ munch [(lo, bv_unsigned sp)] m m1 /\ wmono ssegs m m1 /\ mem_inv ssegs m1
      /\ stk ssegs m1 lo (bv_unsigned sp + -32).

  Lemma md_bytes : ro_bytes ssegs MODE (md ++ Z_to_bv 8 0 :: slack) ->
    forall m', mem_inv ssegs m' -> bytes_at ssegs m' (bv_unsigned (Z_to_bv 64 MODE : word)) (md ++ Z_to_bv 8 0 :: slack).
  Proof using MDR. pin_using (fun (MDR : unit) => tt).
    intros ROMD m' MI. rewrite unsigned_lit by lia. apply ro_bytes_at; [exact MI | lia | rewrite length_app; cbn [length]; lia | exact ROMD].
  Qed.

  Definition fopen_S1__stmt : Prop := forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    ro_bytes ssegs MODE (md ++ Z_to_bv 8 0 :: slack) ->
    stk ssegs m lo (bv_unsigned sp) -> mem_inv ssegs m ->
    evt ssegs fopen_S1_post
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 NAME) (Z_to_bv 64 MODE) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FOPEN) fc None m (seg_rom ssegs)).
  Section Sz10.
  Variables t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : ltac2:(SecDiet.SzSec.tyM 'fopen_S1__stmt "vvvvvvvvvvvvv" @t0).
  Lemma fopen_S1__body : ltac2:(SecDiet.SzSec.bodyP 'fopen_S1__stmt "vvvvvvvvvvvvv").
  Proof using GLO LO M0 MDR NAMER NONUL PAD SP47 TPLO TPR. pin_using (fun (GLO LO M0 MDR NAMER NONUL PAD SP47 TPLO TPR : unit) => tt).
    intros ROMD ST MI.
    pose proof (md_bytes ROMD) as MDB.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl ssegs m) as WM.
    unfold FOPEN, fopen_S1_post.
    destruct md as [|b0 mdt]. { exfalso. cbn in M0. lia. }
    pose proof (byte_range b0) as Rb0.
    assert (E0 : mode_m0 (b0 :: mdt) = bv_unsigned b0) by reflexivity. rewrite E0 in M0.
    carve_frame 32%nat ST.
    do 5 zs.
    zs. (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u8ro_read ssegs mm (bv_unsigned (Z_to_bv 64 MODE : word)) _ 0 _ (Z_to_bv 64 MODE) (MDB mm ltac:(mi)) ltac:(reflexivity) ltac:(lia)
                  ltac:(rewrite Z.add_0_r; symmetry; apply Z_to_bv_bv_unsigned)) as RD end.
    zs. (* [comment removed for export] *)
    clear RD.
    zs. zs. zs.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (rwa_bytes mm ltac:(mi)) as RWA end. rewrite <- (unsigned_lit STR_RWA) in RWA by (unfold STR_RWA; lia).
    zs. call_sp strchr_spec; [exact ST | exact RWA | cbn; clear; intuition discriminate | unfold STR_RWA; rewrite unsigned_lit by lia; cbn; lia | mi | lia | unfold STR_RWA; rewrite unsigned_lit by lia; cbn [length]; lia | ].
    rename PC into ST; try clear RWA; try clear POST.
    zs. if_cases K; zify_cond K.
    { exfalso. revert K. rewrite (Z.mod_small (bv_unsigned b0) 256) by lia.
      pose proof (strchr_res_found STR_RWA (bv_unsigned b0) [Z_to_bv 8 114; Z_to_bv 8 119; Z_to_bv 8 97] ltac:(unfold STR_RWA; lia) ltac:(lia) ltac:(unfold STR_RWA; cbn; lia)) as HF.
      rewrite (rwa_has (bv_unsigned b0)) in HF by lia. unfold STR_RWA in HF. intros K. rewrite K in HF. discriminate HF. }
    zs. zs.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (MDB mm ltac:(mi)) as STR end.
    call_sp fmodeflags_spec; [exact ST | exact STR | exact NONUL | rewrite unsigned_lit by lia; exact PAD | mi | lia | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia | ].
    rename PC into ST; try clear POST.
    do 7 zs.
    apply evt_done.
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact FR|]. split; [exact MU|]. split; [exact WM|]. split; [mi| exact ST].
  Qed.
  End Sz10.
  Lemma fopen_S1 : ltac:(let t := eval cbv delta [fopen_S1__stmt] in fopen_S1__stmt in exact t).
  Proof using GLO LO M0 MDR NAMER NONUL PAD SP47 TPLO TPR. intros t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6. ltac2:(SecDiet.SzSec.closeP 'fopen_S1__body "vvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition fopen_S5__stmt : Prop := forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x20 x21 x22 t3 t4 t5 t6 : word) (m1 : mem) W,
    rw_cells ssegs m1 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk ssegs m1 lo (bv_unsigned sp + -32) -> mem_inv ssegs m1 -> munch W m m1 -> wmono ssegs m m1 ->
    evt ssegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
        ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (ret_pc ra) fc None m1 (seg_rom ssegs)
        /\ munch W m m1 /\ wmono ssegs m m1 /\ mem_inv ssegs m1 /\ stk ssegs m1 lo (bv_unsigned sp))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 x20 x21 a0 a1 a2 a3 a4 a5 a6 a7 x22 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1b134) fc None m1 (seg_rom ssegs)).
  Section Sz11.
  Variables x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x20 x21 x22 t3 t4 t5 t6 m1 W : ltac2:(SecDiet.SzSec.tyM 'fopen_S5__stmt "vvvvvvvvvvvvvvvvvvvvv" @x1).
  Lemma fopen_S5__body : ltac2:(SecDiet.SzSec.bodyP 'fopen_S5__stmt "vvvvvvvvvvvvvvvvvvvvv").
  Proof using LO MODE md slack. pin_using (fun (LO MODE md slack : unit) => tt).
    intros FR ST MI MU WM.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    zs. zs. do 6 zs.
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
  Qed.
  End Sz11.
  Lemma fopen_S5 : ltac:(let t := eval cbv delta [fopen_S5__stmt] in fopen_S5__stmt in exact t).
  Proof using LO MODE md slack. intros x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x20 x21 x22 t3 t4 t5 t6 m1 W. ltac2:(SecDiet.SzSec.closeP 'fopen_S5__body "vvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition fopen_S2_fail__stmt : Prop := forall (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x22 t3 t4 t5 t6 : word) (m1 : mem) (e : Z) (errv : word),
    rw_cells ssegs m1 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells ssegs m1 (bv_unsigned tp + -164) [C4 errv] ->
    1 <= e <= 4095 ->
    stk ssegs m1 lo (bv_unsigned sp + -32) -> mem_inv ssegs m1 -> munch [(lo, bv_unsigned sp)] m m1 -> wmono ssegs m m1 ->
    evt ssegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
        ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (ret_pc ra) fc None m' (seg_rom ssegs)
        /\ munch [(lo, bv_unsigned sp); (bv_unsigned tp + -164, bv_unsigned tp + -160)] m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
        /\ stk ssegs m' lo (bv_unsigned sp)
        /\ rw_cells ssegs m' (bv_unsigned tp + -164) [C4 (Z_to_bv 64 e)])
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 MODE) (Z_to_bv 64 NAME) (errno_ret e) a1 a2 a3 a4 a5 a6 a7 x22 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1b0e4) fc None m1 (seg_rom ssegs)).
  Section Sz12.
  Variables x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x22 t3 t4 t5 t6 m1 e errv : ltac2:(SecDiet.SzSec.tyM 'fopen_S2_fail__stmt "vvvvvvvvvvvvvvvvvvv" @x1).
  Lemma fopen_S2_fail__body : ltac2:(SecDiet.SzSec.bodyP 'fopen_S2_fail__stmt "vvvvvvvvvvvvvvvvvvv").
  Proof using GLO LO SP47 TP200 TPLO md slack. pin_using (fun (GLO LO SP47 TP200 TPLO md slack : unit) => tt).
    intros FR ERR HE ST MI MU WM.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    apply (munch_weaken [(lo, bv_unsigned sp)] [(lo, bv_unsigned sp); (bv_unsigned tp + -164, bv_unsigned tp + -160)]) in MU.
    2:{ unfold sub_fp. cbn [outside]. intros x Hx. lia. }
    zs. call_sp sysret_spec; [exact ST | exact ERR | mi | lia | lia | lia |].
    rename PC into ST.
    unfold sysret_val, sysret_errno in *. rewrite (errno_of_errno_ret e) in * by lia.
    zs. zs. if_cases K; zify_cond K.
    2:{ exfalso. lia. }
    eapply evt_mono; [eapply (fopen_S5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); [exact FR| exact ST| mi| exact MU| exact WM]|].
    cbv beta. intros ms' PO. destruct_exs PO. destruct PO as (-> & MU' & WM' & MI' & ST').
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|]. split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'|]. split; [exact ST'|]. assumption.
  Qed.
  End Sz12.
  Lemma fopen_S2_fail : ltac:(let t := eval cbv delta [fopen_S2_fail__stmt] in fopen_S2_fail__stmt in exact t).
  Proof using GLO LO SP47 TP200 TPLO md slack. intros x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x22 t3 t4 t5 t6 m1 e errv. ltac2:(SecDiet.SzSec.closeP 'fopen_S2_fail__body "vvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition fopen_S2_post (fd : Z) (canary errv : word) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 sv2 : word) (j0 : list byte) (m2 : mem),
      ms' = MS (mkR (Z_to_bv 64 0x1b268) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 MODE) (Z_to_bv 64 fd)
                   (Z_to_bv 64 1264) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 MODE) (Z_to_bv 64 ssp_guard) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x188cc) fc None m2 (seg_rom ssegs)
      /\ rw_cells ssegs m2 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra]
      /\ rw_cells ssegs m2 (bv_unsigned sp + -96) [CB 16 j0; C8 canary; C8 s3; C8 sv2; C8 (Z_to_bv 64 fd); C8 (Z_to_bv 64 MODE); C8 (Z_to_bv 64 0x1b120)]
      /\ rw_cells ssegs m2 (bv_unsigned tp + -164) [C4 errv]
      /\ ssp_cells m2 canary
      /\ munch [(lo, bv_unsigned sp); (bv_unsigned tp + -164, bv_unsigned tp + -160)] m m2 /\ wmono ssegs m m2 /\ mem_inv ssegs m2
      /\ stk ssegs m2 lo (bv_unsigned sp + -96).

  Definition fopen_S2_ok__stmt : Prop := forall (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m1 : mem) (fd : Z) (canary errv : word),
    ro_bytes ssegs MODE (md ++ Z_to_bv 8 0 :: slack) ->
    rw_cells ssegs m1 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells ssegs m1 (bv_unsigned tp + -164) [C4 errv] -> ssp_cells m1 canary ->
    3 <= fd <= 4096 ->
    (fmodeflags md = 0 \/ fmodeflags md = 577) ->
    stk ssegs m1 lo (bv_unsigned sp + -32) -> mem_inv ssegs m1 -> munch [(lo, bv_unsigned sp)] m m1 -> wmono ssegs m m1 ->
    evt ssegs (fopen_S2_post fd canary errv)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 MODE) (Z_to_bv 64 NAME) (Z_to_bv 64 fd) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (fmodeflags md)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1b0e4) fc None m1 (seg_rom ssegs)).
  Section Sz13.
  Variables x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m1 fd canary errv : ltac2:(SecDiet.SzSec.tyM 'fopen_S2_ok__stmt "vvvvvvvvvvvvvvvvvvv" @x1).
  Lemma fopen_S2_ok__body : ltac2:(SecDiet.SzSec.bodyP 'fopen_S2_ok__stmt "vvvvvvvvvvvvvvvvvvv").
  Proof using GLO LO M0 MDR NAMER NONUL PAD SP47 TP200 TPLO TPR. pin_using (fun (GLO LO M0 MDR NAMER NONUL PAD SP47 TP200 TPLO TPR : unit) => tt).
    intros ROMD FR ERR SSP FD FLV ST MI MU WM.
    pose proof (md_bytes ROMD) as MDB.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in *. unfold fopen_S2_post, ssp_cells, got_ssp, ssp_guard.
    destruct md as [|b0 mdt]. { exfalso. cbn in M0. lia. }
    pose proof (byte_range b0) as Rb0.
    assert (E0 : mode_m0 (b0 :: mdt) = bv_unsigned b0) by reflexivity. rewrite E0 in M0.
    apply (munch_weaken [(lo, bv_unsigned sp)] [(lo, bv_unsigned sp); (bv_unsigned tp + -164, bv_unsigned tp + -160)]) in MU.
    2:{ unfold sub_fp. cbn [outside]. intros x Hx. lia. }
    zs. call_sp sysret_spec; [exact ST | exact ERR | mi | lia | lia | lia |].
    rename PC into ST. rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite (errno_of_lit fd) in * by lia.
    zs. rewrite ?(sextw_small fd), ?(sx32_small fd) by lia.
    zs. if_cases K; zify_cond K. 1:{ exfalso. revert K. rewrite Z.add_0_r, (swrap32_small fd) by lia. rewrite Z.mod_small by lia. lia. }
    rewrite Z.add_0_r, (swrap32_small fd) by lia.
    zs. zs. zs. if_cases K2; zify_cond K2.
    2:{ exfalso. revert K2. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mod_small by (destruct FLV as [E|E]; rewrite E; lia). destruct FLV as [E|E]; rewrite E; lia. }
    zs. zs. zs.
    (* [comment removed for export] *)
    carve_frame 64%nat ST.
    do 6 zs. zs. zs. zs. zs. zs.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u8ro_read ssegs mm (bv_unsigned (Z_to_bv 64 MODE : word)) _ 0 _ (Z_to_bv 64 MODE) (MDB mm ltac:(mi)) ltac:(reflexivity) ltac:(lia)
                  ltac:(rewrite Z.add_0_r; symmetry; apply Z_to_bv_bv_unsigned)) as RD end.
    zs. clear RD. zs. zs. zs.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (rwa_bytes mm ltac:(mi)) as RWA end. rewrite <- (unsigned_lit STR_RWA) in RWA by (unfold STR_RWA; lia).
    zs. call_sp strchr_spec; [exact ST | exact RWA | cbn; clear; intuition discriminate | unfold STR_RWA; rewrite unsigned_lit by lia; cbn; lia | mi | lia | unfold STR_RWA; rewrite unsigned_lit by lia; cbn [length]; lia | ].
    rename PC into ST; try clear RWA; try clear POST.
    zs. if_cases K3; zify_cond K3.
    { exfalso. revert K3. rewrite (Z.mod_small (bv_unsigned b0) 256) by lia.
      pose proof (strchr_res_found STR_RWA (bv_unsigned b0) [Z_to_bv 8 114; Z_to_bv 8 119; Z_to_bv 8 97] ltac:(unfold STR_RWA; lia) ltac:(lia) ltac:(unfold STR_RWA; cbn; lia)) as HF.
      rewrite (rwa_has (bv_unsigned b0)) in HF by lia. unfold STR_RWA in HF. intros K3. rewrite K3 in HF. discriminate HF. }
    zs. zs.
    apply evt_done.
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split; [assumption|]. split; [eassumption|].
    split; [assumption|]. split; [split; assumption|].
    split; [assumption|]. split; [assumption|]. split; [mi| assumption].
  Qed.
  End Sz13.
  Lemma fopen_S2_ok : ltac:(let t := eval cbv delta [fopen_S2_ok__stmt] in fopen_S2_ok__stmt in exact t).
  Proof using GLO LO M0 MDR NAMER NONUL PAD SP47 TP200 TPLO TPR. intros x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m1 fd canary errv. ltac2:(SecDiet.SzSec.closeP 'fopen_S2_ok__body "vvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition fopen_S4__stmt : Prop := forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 sv2 : word) (j0 : list byte) (m2 : mem) (fd : Z) (canary : word),
    rw_cells ssegs m2 (bv_unsigned sp + -96) [CB 16 j0; C8 canary; C8 s3; C8 sv2; C8 (Z_to_bv 64 fd); C8 (Z_to_bv 64 MODE); C8 (Z_to_bv 64 0x1b120)] ->
    ssp_cells m2 canary -> 3 <= fd <= 4096 -> mem_inv ssegs m2 ->
    evt ssegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' t3' t4' t5' t6' : word),
        ms' = MS (mkR (Z_to_bv 64 0x1b120) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0' t1' t2' (Z_to_bv 64 MODE) (Z_to_bv 64 fd)
                     (Z_to_bv 64 fd) a1' a2' a3' a4' a5' a6' (Z_to_bv 64 57) sv2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (Z_to_bv 64 0x1b130) fc None m2 (seg_rom ssegs))
      (MS (mkR (Z_to_bv 64 0x1b268) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 MODE) (Z_to_bv 64 fd)
               (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 MODE) (Z_to_bv 64 ssp_guard) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1b268) fc None m2 (seg_rom ssegs)).
  Section Sz14.
  Variables t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 sv2 j0 m2 fd canary : ltac2:(SecDiet.SzSec.tyM 'fopen_S4__stmt "vvvvvvvvvvvvvvvvvvv" @t0).
  Lemma fopen_S4__body : ltac2:(SecDiet.SzSec.bodyP 'fopen_S4__stmt "vvvvvvvvvvvvvvvvvvv").
  Proof using md slack. pin_using (fun (md slack : unit) => tt).
    intros FRI SSP FD MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in *.
    pose proof (munch_refl [] m2) as MU. pose proof (wmono_refl ssegs m2) as WM.
    zs. if_true.
    zs. zs. zs. if_cases K; zify_cond K. 1:{ exfalso. apply K. reflexivity. }
    do 7 zs.
    replace (ret_pc (Z_to_bv 64 0x1b120)) with (Z_to_bv 64 0x1b120 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    zs. if_cases K2; zify_cond K2. 1:{ exfalso. rewrite ?Z.mod_small in K2 by lia. lia. }
    zs. zs. zs. rewrite (Z.mod_small fd 2147483648) by lia.
    apply evt_done. repeat (lazymatch goal with |- ex _ => eexists end). cbv delta [mkR]. reflexivity.
  Qed.
  End Sz14.
  Lemma fopen_S4 : ltac:(let t := eval cbv delta [fopen_S4__stmt] in fopen_S4__stmt in exact t).
  Proof using md slack. intros t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 sv2 j0 m2 fd canary. ltac2:(SecDiet.SzSec.closeP 'fopen_S4__body "vvvvvvvvvvvvvvvvvvv"). Qed.

  Hypothesis NOPLUS : has_byte 43 md = false.
  Hypothesis NOE : has_byte 101 md = false.

  (* [comment removed for export] *)
  Definition fopen_S6_post (fl P fd : Z) (canary : word) (junk2 : list byte) (m2 : mem) : machine_state -> Prop :=
    fun ms' => exists (x1 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m3 : mem),
      ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 P) (Z_to_bv 64 fd)
                   (Z_to_bv 64 (Z.land fl 8)) (Z_to_bv 64 (P + 240)) (Z_to_bv 64 1024) (Z_to_bv 64 (-1)) a4 a5 a6 a7
                   (Z_to_bv 64 MODE) (Z_to_bv 64 ssp_guard) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x1b354) fc None m3 (seg_rom ssegs)
      /\ rw_cells ssegs m3 P (flk_cells (Z_to_bv 64 fl) 0 0 0 0 0 0 0 0 0 (P + 240) 1024 0 0 fd
                               (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (-1)) (repeat (Z_to_bv 8 0) 80))
      /\ rw_cells ssegs m3 (P + 232) [CB 1032 junk2]
      /\ rw_cells ssegs m3 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra]
      /\ (exists sv2 j0, rw_cells ssegs m3 (bv_unsigned sp + -96) [CB 16 j0; C8 canary; C8 s3; C8 sv2; C8 (Z_to_bv 64 fd); C8 (Z_to_bv 64 MODE); C8 (Z_to_bv 64 0x1b120)])
      /\ ssp_cells m3 canary
      /\ munch [(lo, bv_unsigned sp); (P, P + 232)] m2 m3 /\ wmono ssegs m2 m3 /\ mem_inv ssegs m3
      /\ stk ssegs m3 lo (bv_unsigned sp + -96).

  Definition fopen_S6__stmt : Prop := forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 sv2 : word) (j0 junk : list byte) (m2 : mem) (P fd : Z) (canary : word),
    ro_bytes ssegs MODE (md ++ Z_to_bv 8 0 :: slack) ->
    rw_cells ssegs m2 P [CB (Z.to_nat 1264) junk] -> 0 < P -> (P + 1264 <= 0x10000 \/ 0x55000 <= P) -> P + 1264 <= lo ->
    rw_cells ssegs m2 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells ssegs m2 (bv_unsigned sp + -96) [CB 16 j0; C8 canary; C8 s3; C8 sv2; C8 (Z_to_bv 64 fd); C8 (Z_to_bv 64 MODE); C8 (Z_to_bv 64 0x1b120)] ->
    ssp_cells m2 canary -> 3 <= fd <= 4096 ->
    stk ssegs m2 lo (bv_unsigned sp + -96) -> mem_inv ssegs m2 ->
    evt ssegs (fopen_S6_post (if mode_m0 md =? 114 then 8 else 4) P fd canary (skipn 232 junk) m2)
      (MS (mkR (Z_to_bv 64 0x1b268) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 MODE) (Z_to_bv 64 fd)
               (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 MODE) (Z_to_bv 64 ssp_guard) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1b268) fc None m2 (seg_rom ssegs)).
  Section Sz15.
  Variables t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 sv2 j0 junk m2 P fd canary : ltac2:(SecDiet.SzSec.tyM 'fopen_S6__stmt "vvvvvvvvvvvvvvvvvvvvv" @t0).
  Lemma fopen_S6__body : ltac2:(SecDiet.SzSec.bodyP 'fopen_S6__stmt "vvvvvvvvvvvvvvvvvvvvv").
  Proof using GLO LO M0 MDR NOE NONUL NOPLUS PAD SP47 TPLO. pin_using (fun (GLO LO M0 MDR NOE NONUL NOPLUS PAD SP47 TPLO : unit) => tt).
    intros ROMD BLK P0 PST PLO FRO FRI SSP FD ST MI.
    pose proof (md_bytes ROMD) as MDB.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in *. unfold ssp_cells, got_ssp, ssp_guard.
    destruct md as [|b0 mdt]. { exfalso. cbn in M0. lia. }
    pose proof (byte_range b0) as Rb0.
    assert (E0 : mode_m0 (b0 :: mdt) = bv_unsigned b0) by reflexivity. rewrite E0 in M0 |- *.
    set (fl := if bv_unsigned b0 =? 114 then 8 else 4).
    assert (FLR : (bv_unsigned b0 = 114 /\ fl = 8) \/ (bv_unsigned b0 = 119 /\ fl = 4)).
    { subst fl. destruct (Z.eqb_spec (bv_unsigned b0) 114) as [E|E]; [left | right]; lia. }
    clearbody fl.
    pose proof (munch_refl [(lo, bv_unsigned sp); (P, P + 232)] m2) as MU. pose proof (wmono_refl ssegs m2) as WM.
    assert (LJ : length junk = 1264%nat) by (destruct BLK as [[WF _] _]; cbn in WF; exact (proj1 WF)).
    apply (rw_cells_split_CB ssegs _ _ [] (Z.to_nat 1264) junk [] [232; 1032]%nat) in BLK; [| cbn; lia].
    cbn [mk_CB_cells app] in BLK. apply (proj1 (rw_cells_app ssegs _ _ [_] _)) in BLK. destruct BLK as [BLK1 BLK2].
    cbn [cells_size csize Nat.add] in BLK2. rewrite firstn_all2 in BLK2 by (rewrite length_skipn; lia).
    zs. if_cases K; zify_cond K. 1:{ exfalso. rewrite ?Z.mod_small in K by lia. lia. }
    zs. zs. zs. zs.
    call_sp memset_callw; [exact BLK1 | lia | lia | lia | lia | mi |].
    lazymatch goal with H : rw_cells ssegs _ P [CB (Z.to_nat 232) (repeat _ _)] |- _ => apply zero_file_cells in H; rename H into FC end.
    unfold flk_cells in FC.
    (* [comment removed for export] *)
    zs. zs.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (MDB mm ltac:(mi)) as STR end.
    zs. call_sp strchr_spec; [exact ST | exact STR | exact NONUL | rewrite unsigned_lit by lia; exact PAD | mi | lia | rewrite unsigned_lit by lia; lia | ].
    rename PC into ST; try clear POST; try clear STR.
    rewrite !unsigned_lit by lia. change (43 mod 256) with 43.
    rewrite (strchr_res_notfound MODE 43 (b0 :: mdt) ltac:(lia) NOPLUS).
    zs. if_cases K2; zify_cond K2. 1:{ exfalso. apply K2. reflexivity. }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u8ro_read ssegs mm (bv_unsigned (Z_to_bv 64 MODE : word)) _ 0 _ (Z_to_bv 64 MODE) (MDB mm ltac:(mi)) ltac:(reflexivity) ltac:(lia)
                  ltac:(rewrite Z.add_0_r; symmetry; apply Z_to_bv_bv_unsigned)) as RD end.
    zs. clear RD. zs.
    (* [comment removed for export] *)
    assert (JOIN : forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) mm,
      mem_inv ssegs mm -> munch [(lo, bv_unsigned sp); (P, P + 232)] m2 mm -> wmono ssegs m2 mm ->
      stk ssegs mm lo (bv_unsigned sp + -96) ->
      rw_cells ssegs mm P (flk_cells (Z_to_bv 64 fl) 0 0 0 0 0 0 0 0 0 0 0 0 0 0 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (repeat (Z_to_bv 8 0) 80)) ->
      rw_cells ssegs mm (P + 232) [CB 1032 (skipn 232 junk)] ->
      rw_cells ssegs mm (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells ssegs mm (bv_unsigned sp + -96) [CB 16 j0; C8 canary; C8 s3; C8 sv2; C8 (Z_to_bv 64 fd); C8 (Z_to_bv 64 MODE); C8 (Z_to_bv 64 0x1b120)] ->
      rw_cells ssegs mm 140832 [C8 (Z_to_bv 64 343304)] -> rw_cells ssegs mm 343304 [C8 canary] ->
      evt ssegs (fopen_S6_post fl P fd canary (skipn 232 junk) m2)
        (MS (mkR (Z_to_bv 64 0x1b288) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0' t1' t2' (Z_to_bv 64 P) (Z_to_bv 64 fd)
                 (Z_to_bv 64 fl) a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 MODE) (Z_to_bv 64 343304) s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
            F (Z_to_bv 64 0x1b2c0) fc None mm (seg_rom ssegs))).
    { intros until mm. intros MIj MUj WMj STj FCj BLKj FROj FRIj GOTj GUARDj. unfold flk_cells in FCj.
      zs. zs.
      pose proof (MDB mm MIj) as STR.
      zs. call_sp strchr_spec; [exact STj | exact STR | exact NONUL | rewrite unsigned_lit by lia; exact PAD | mi | lia | rewrite unsigned_lit by lia; lia | ].
      rename PC into STj; try clear POST; try clear STR.
      rewrite !unsigned_lit by lia. change (101 mod 256) with 101.
      rewrite (strchr_res_notfound MODE 101 (b0 :: mdt) ltac:(lia) NOE).
      zs. if_true.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm2 _) =>
        pose proof (u8ro_read ssegs mm2 (bv_unsigned (Z_to_bv 64 MODE : word)) _ 0 _ (Z_to_bv 64 MODE) (MDB mm2 ltac:(mi)) ltac:(reflexivity) ltac:(lia)
                    ltac:(rewrite Z.add_0_r; symmetry; apply Z_to_bv_bv_unsigned)) as RD end.
      zs. clear RD. zs. zs. if_cases K3; zify_cond K3. 2:{ exfalso. rewrite ?unsigned_lit, ?Z.mod_small in K3 by lia. lia. }
      zs. rewrite (sx32_small fl) by lia. zs. zs. zs. zs. rewrite ?(unsigned_lit fl) by lia. zs. zs. zs. zs.
      apply evt_done. unfold fopen_S6_post, flk_cells.
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|].
      split; [match goal with H : rw_cells ssegs _ P _ |- _ => exact H end|].
      split; [assumption|]. split; [assumption|]. split; [do 2 eexists; eassumption|]. split; [split; assumption|].
      split; [assumption|]. split; [assumption|]. split; [mi| assumption]. }
    zs. if_cases K4; zify_cond K4.
    - (* [comment removed for export] *) zs. zs.
      assert (EF : fl = 8) by (rewrite ?unsigned_lit, ?Z.mod_small in K4 by lia; lia). rewrite <- EF in FC |- *.
      eapply JOIN; try eassumption; mi.
    - (* [comment removed for export] *) zs. zs. zs.
      assert (EF : fl = 4) by (rewrite ?unsigned_lit, ?Z.mod_small in K4 by lia; lia). rewrite <- EF in FC |- *.
      eapply JOIN; try eassumption; mi.
  Qed.
  End Sz15.
  Lemma fopen_S6 : ltac:(let t := eval cbv delta [fopen_S6__stmt] in fopen_S6__stmt in exact t).
  Proof using GLO LO M0 MDR NOE NONUL NOPLUS PAD SP47 TPLO. intros t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 sv2 j0 junk m2 P fd canary. ltac2:(SecDiet.SzSec.closeP 'fopen_S6__body "vvvvvvvvvvvvvvvvvvvvv"). Qed.

  Definition fopen_S7_post (fl P fd hd : Z) (canary : word) (junk2 : list byte) (m2 : mem) (W : list (Z * Z)) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom ssegs)
      /\ rw_cells ssegs m' P (file_cells (Z_to_bv 64 fl) 0 0 F_STDIO_CLOSE 0 0 0 F_STDIO_READ F_STDIO_WRITE F_STDIO_SEEK (P + 240) 1024 0 hd fd
                               (Z_to_bv 64 0) 4294967295 (repeat (Z_to_bv 8 0) 80))
      /\ rw_cells ssegs m' (P + 232) [CB 1032 junk2]
      /\ rw_cells ssegs m' A_OFL_LOCK [C4 (Z_to_bv 64 0)] /\ rw_cells ssegs m' A_OFL_HEAD [C8 (Z_to_bv 64 P)]
      /\ (hd <> 0 -> rw_cells ssegs m' (hd + 104) [C8 (Z_to_bv 64 P)])
      /\ ssp_cells m' canary
      /\ munch W m2 m' /\ wmono ssegs m2 m' /\ mem_inv ssegs m'
      /\ stk ssegs m' lo (bv_unsigned sp).

  (* [comment removed for export] *)
  Definition fopen_S7_tail__stmt : Prop := forall (fl P fd hd wt : Z) (canary sv2 : word) (j0 junk2 : list byte) (m2 : mem),
    0 < P -> (P + 1264 <= 0x10000 \/ 0x55000 <= P) -> P + 1264 <= lo -> 3 <= fd <= 4096 -> 0 <= hd -> hd + 232 < 2^63 ->
    ((hd = 0 /\ wt = 104) \/ (hd <> 0 /\ wt = 112 /\ hd + 232 <= lo /\ (hd + 232 <= P \/ P + 1264 <= hd) /\ (hd + 232 <= 65536 \/ 348160 <= hd))) ->
    forall (x1' t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) mm,
      mem_inv ssegs mm -> munch [(lo, bv_unsigned sp); (P, P + 232); (344400, 344400 + 8); (hd + 104, hd + wt)] m2 mm -> wmono ssegs m2 mm ->
      stk ssegs mm lo (bv_unsigned sp + -112) ->
      rw_cells ssegs mm (bv_unsigned sp + -112) [C8 (Z_to_bv 64 P); C8 (Z_to_bv 64 0x1b3c8)] ->
      rw_cells ssegs mm P [C4 (Z_to_bv 64 fl); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 F_STDIO_CLOSE);
                           C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                           C8 (Z_to_bv 64 F_STDIO_READ); C8 (Z_to_bv 64 F_STDIO_WRITE); C8 (Z_to_bv 64 F_STDIO_SEEK);
                           C8 (Z_to_bv 64 (P + 240)); C8 (Z_to_bv 64 1024); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 hd);
                           C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                           C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 0); CB 80 (repeat (Z_to_bv 8 0) 80)] ->
      rw_cells ssegs mm (P + 232) [CB 1032 junk2] ->
      rw_cells ssegs mm (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells ssegs mm (bv_unsigned sp + -96) [CB 16 j0; C8 canary; C8 s3; C8 sv2; C8 (Z_to_bv 64 fd); C8 (Z_to_bv 64 MODE); C8 (Z_to_bv 64 0x1b120)] ->
      rw_cells ssegs mm 140832 [C8 (Z_to_bv 64 343304)] -> rw_cells ssegs mm 343304 [C8 canary] ->
      rw_cells ssegs mm 344392 [C4 (Z_to_bv 64 0)] -> rw_cells ssegs mm 344400 [C8 (Z_to_bv 64 hd)] ->
      (hd <> 0 -> rw_cells ssegs mm (hd + 104) [C8 (Z_to_bv 64 P)]) ->
      evt ssegs (fopen_S7_post fl P fd hd canary junk2 m2 [(lo, bv_unsigned sp); (P, P + 232); (344400, 344400 + 8); (hd + 104, hd + wt)])
        (MS (mkR x1' (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0' t1' t2' (Z_to_bv 64 P) (Z_to_bv 64 fd)
                 (Z_to_bv 64 344400) (Z_to_bv 64 hd) a2' a3' a4' a5' a6' a7' (Z_to_bv 64 MODE) (Z_to_bv 64 343304) s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
            F (Z_to_bv 64 0x1b9c8) fc None mm (seg_rom ssegs)).
  Section Sz16.
  Variables fl P fd hd wt canary sv2 j0 junk2 m2 : ltac2:(SecDiet.SzSec.tyM 'fopen_S7_tail__stmt "vvvvvvvvvv" @fl).
  Lemma fopen_S7_tail__body : ltac2:(SecDiet.SzSec.bodyP 'fopen_S7_tail__stmt "vvvvvvvvvv").
  Proof using GLO LO SP47 TPLO md slack. pin_using (fun (GLO LO SP47 TPLO md slack : unit) => tt).
    intros P0 PST PLO FD HD0 HDHI HFACTS.
    (* [comment removed for export] *)
    try change (344400 + 8)%Z with 344408%Z. try change (346384 + 8)%Z with 346392%Z.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
      intros until mm. intros MIj MUj WMj STj FRAj FCj BLKj FROj FRIj GOTj GUARDj OLj OHj OLDHj.
      destruct HFACTS as [[HZ ->] | (HNZ & -> & HL1 & HL2 & HL3)]; [| specialize (OLDHj HNZ)].
      all: zs. (* [comment removed for export] *)
      all: zs; zs; zs; zs.
      all: call_sp unlock_spec0; [rewrite unsigned_lit by lia; exact OLj | mi |].
      all: zs; zs; zs; zs; release_frame FRAj STj (bv_unsigned sp + -96); zs.
      (* [comment removed for export] *)
      all: zs; zs; zs; if_cases KC; zify_cond KC; [exfalso; apply KC; reflexivity|].
      all: do 6 zs; release_frame FRIj STj (bv_unsigned sp + -32); zs.
      all: replace (ret_pc (Z_to_bv 64 0x1b120)) with (Z_to_bv 64 0x1b120 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      all: zs; if_cases KP; zify_cond KP; [| exfalso; rewrite ?Z.mod_small in KP by lia; lia].
      all: do 5 zs; release_frame FROj STj (bv_unsigned sp); zs.
      all: apply evt_done; unfold fopen_S7_post.
      all: repeat (lazymatch goal with |- ex _ => eexists end).
      all: split; [cbv delta [mkR]; reflexivity|].
      all: split; [apply fdopen_cells_recast; unfold flk_cells; exact FCj|].
      all: split; [assumption|]; split; [assumption|]; split; [assumption|].
      all: split; [intros NZ; first [assumption | exfalso; exact (NZ HZ)]|].
      all: split; [split; assumption|]; split; [assumption|]; split; [assumption|]; split; [mi| assumption].
  Qed.
  End Sz16.
  Lemma fopen_S7_tail : ltac:(let t := eval cbv delta [fopen_S7_tail__stmt] in fopen_S7_tail__stmt in exact t).
  Proof using GLO LO SP47 TPLO md slack. intros fl P fd hd wt canary sv2 j0 junk2 m2. ltac2:(SecDiet.SzSec.closeP 'fopen_S7_tail__body "vvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition fopen_S7__stmt : Prop := forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 sv2 : word) (j0 junk2 : list byte) (m2 m3 : mem) (fl P fd hd : Z) (canary : word) W,
    rw_cells ssegs m3 P (flk_cells (Z_to_bv 64 fl) 0 0 0 0 0 0 0 0 0 (P + 240) 1024 0 0 fd (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (-1)) (repeat (Z_to_bv 8 0) 80)) ->
    rw_cells ssegs m3 (P + 232) [CB 1032 junk2] -> 0 < P -> (P + 1264 <= 0x10000 \/ 0x55000 <= P) -> P + 1264 <= lo -> 3 <= fd <= 4096 ->
    rw_cells ssegs m3 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells ssegs m3 (bv_unsigned sp + -96) [CB 16 j0; C8 canary; C8 s3; C8 sv2; C8 (Z_to_bv 64 fd); C8 (Z_to_bv 64 MODE); C8 (Z_to_bv 64 0x1b120)] ->
    ssp_cells m3 canary ->
    rw_cells ssegs m3 0x53d29 [C1 (Z_to_bv 8 0)] -> rw_cells ssegs m3 NEED_LOCKS [C1 (Z_to_bv 8 0)] ->
    rw_cells ssegs m3 A_OFL_LOCK [C4 (Z_to_bv 64 0)] -> rw_cells ssegs m3 A_OFL_HEAD [C8 (Z_to_bv 64 hd)] ->
    0 <= hd -> hd + 232 < 2^63 ->
    (hd = 0 \/ (hd <> 0 /\ (exists pvo : word, rw_cells ssegs m3 (hd + 104) [C8 pvo]) /\ hd + 232 <= lo /\ (hd + 232 <= P \/ P + 1264 <= hd) /\ (hd + 232 <= 0x10000 \/ 0x55000 <= hd))) ->
    munch W m2 m3 -> wmono ssegs m2 m3 ->
    sub_fp W [(lo, bv_unsigned sp); (P, P + 232); (A_OFL_HEAD, A_OFL_HEAD + 8); (hd + 104, hd + (if hd =? 0 then 104 else 112))] ->
    stk ssegs m3 lo (bv_unsigned sp + -96) -> mem_inv ssegs m3 ->
    evt ssegs (fopen_S7_post fl P fd hd canary junk2 m2 [(lo, bv_unsigned sp); (P, P + 232); (A_OFL_HEAD, A_OFL_HEAD + 8); (hd + 104, hd + (if hd =? 0 then 104 else 112))])
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 P) (Z_to_bv 64 fd)
               a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 MODE) (Z_to_bv 64 ssp_guard) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1b37c) fc None m3 (seg_rom ssegs)).
  Section Sz17.
  Variables x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 sv2 j0 junk2 m2 m3 fl P fd hd canary W : ltac2:(SecDiet.SzSec.tyM 'fopen_S7__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvv" @x1).
  Lemma fopen_S7__body : ltac2:(SecDiet.SzSec.bodyP 'fopen_S7__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GLO LO SP47 TPLO md slack. pin_using (fun (GLO LO SP47 TPLO md slack : unit) => tt).
    intros FC BLK2 P0 PST PLO FD FRO FRI SSP THR NL OL OH HD0 HDHI OLDH MU WM SUB ST MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard, A_OFL_LOCK, A_OFL_HEAD, NEED_LOCKS in *. unfold fopen_S7_post, ssp_cells, got_ssp, ssp_guard, A_OFL_LOCK, A_OFL_HEAD.
    unfold flk_cells in FC.
    apply (munch_weaken W _ m2 m3 SUB) in MU. clear SUB.
    assert (HFACTS : hd = 0 \/ (hd <> 0 /\ hd + 232 <= lo /\ (hd + 232 <= P \/ P + 1264 <= hd) /\ (hd + 232 <= 65536 \/ 348160 <= hd))).
    { destruct OLDH as [E | (A0 & _ & A1 & A2 & A3)]; [left; exact E | right; repeat split; assumption]. }
    destruct OLDH as [HZ0 | (HNZ0 & [pvo OLDC] & F1 & F2 & F3)].
    1: replace (hd =? 0) with true in * by (symmetry; apply Z.eqb_eq; exact HZ0).
    2: replace (hd =? 0) with false in * by (symmetry; apply Z.eqb_neq; exact HNZ0).
    all: cbv iota in MU. all: cbv iota.
    all: do 5 zs; do 4 zs.
    all: zs. (* [comment removed for export] *)
    all: do 4 zs. (* [comment removed for export] *)
    all: zs; if_cases KT; zify_cond KT; [exfalso; apply KT; reflexivity|].
    all: zs; zs. (* [comment removed for export] *)
    all: zs; zs. (* [comment removed for export] *)
    all: carve_frame 16%nat ST; rename FR into FRA.
    all: zs; zs; zs; zs; zs.
    all: carve_frame 16%nat ST; rename FR into FRL.
    all: zs; zs; zs; zs; zs; zs.
    all: zs; call_sp lock_spec; [exact NL | mi |].
    all: zs; do 3 zs; release_frame FRL ST (bv_unsigned sp + -112); zs.
    all: zs. (* [comment removed for export] *)
    all: zs. (* [comment removed for export] *)
    all: zs; if_cases KH; zify_cond KH.
    - (* [comment removed for export] *)
      eapply (fopen_S7_tail fl P fd hd 104); try eassumption; try mi;
        fastfirst (first [lia | left; split; [exact HZ0| reflexivity] | intros NZ; exfalso; exact (NZ HZ0)]).
    - exfalso. subst hd. apply KH. reflexivity.
    - exfalso. rewrite ?unsigned_lit, ?Z.mod_small in KH by lia. lia.
    - (* [comment removed for export] *)
      zs.
      eapply (fopen_S7_tail fl P fd hd 112); try eassumption; try mi;
        fastfirst (first [lia | right; split; [exact HNZ0| split; [reflexivity| split; [exact F1| split; [exact F2| exact F3]]]] | intros _; assumption]).
  Qed.
  End Sz17.
  Lemma fopen_S7 : ltac:(let t := eval cbv delta [fopen_S7__stmt] in fopen_S7__stmt in exact t).
  Proof using GLO LO SP47 TPLO md slack. intros x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 sv2 j0 junk2 m2 m3 fl P fd hd canary W. ltac2:(SecDiet.SzSec.closeP 'fopen_S7__body "vvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Lemma fopen_br_r : forall (x1 spv t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (mm : mem),
    evt ssegs (fun ms' => ms' = MS (mkR x1 spv gp tp t0 t1 t2 x8 x9 (Z_to_bv 64 (Z.land 8 8)) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                                   F (Z_to_bv 64 0x1b37c) fc None mm (seg_rom ssegs))
      (MS (mkR x1 spv gp tp t0 t1 t2 x8 x9 (Z_to_bv 64 (Z.land 8 8)) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1b354) fc None mm (seg_rom ssegs)).
  Proof using Type. pin_using tt.
    intros. pose proof (munch_refl [] mm) as MU. pose proof (wmono_refl ssegs mm) as WM.
    change (Z.land 8 8) with 8. zs. if_true. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma fopen_br_w : forall (x1 t0 t1 t2 x8 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (mm : mem) (fd : Z),
    0 <= fd < 2^31 ->
    evt ssegs (fun ms' => ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 x8 (Z_to_bv 64 fd) (Z_to_bv 64 fd) (Z_to_bv 64 21523) (Z_to_bv 64 (bv_unsigned sp + -88)) a3 a4 a5 a6 (Z_to_bv 64 29) x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                                   F (Z_to_bv 64 0x1b36c) fc None mm (seg_rom ssegs))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 x8 (Z_to_bv 64 fd) (Z_to_bv 64 (Z.land 4 8)) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1b354) fc None mm (seg_rom ssegs)).
  Proof using Type. pin_using tt.
    intros until fd. intros FD. pose proof (munch_refl [] mm) as MU. pose proof (wmono_refl ssegs mm) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    change (Z.land 4 8) with 0. zs. if_false. zs. zs. zs. zs. zs.
    all: match goal with |- evt _ _ ?ms => idtac "BRW:" ms end.
    apply evt_done. cbv delta [mkR]. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma fopen_ioctl_ret : forall (x1 spv t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (mm : mem) (e : Z),
    1 <= e <= 4095 ->
    evt ssegs (fun ms' => ms' = MS (mkR x1 spv gp tp t0 t1 t2 x8 x9 (errno_ret e) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                                   F (Z_to_bv 64 0x1b37c) fc None mm (seg_rom ssegs))
      (MS (mkR x1 spv gp tp t0 t1 t2 x8 x9 (errno_ret e) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1b370) fc None mm (seg_rom ssegs)).
  Proof using MODE md slack. pin_using (fun (MODE md slack : unit) => tt).
    intros until e. intros HE. pose proof (munch_refl [] mm) as MU. pose proof (wmono_refl ssegs mm) as WM.
    pose proof (unsigned_errno_ret e HE) as U.
    zs. if_cases K; zify_cond K. 2:{ exfalso. revert K. match goal with |- ?g => idtac "KIO:" g end. rewrite ?U. lia. }
    apply evt_done. reflexivity.
  Qed.
End Fopen.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.F_memset.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_lock.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memmove__S3.F_strchr.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memmove__S3.F_fmodeflags.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition FOPEN : Z := 0x1b84c.
Definition FDOPEN : Z := 0x1b9dc.
Definition OFL_ADD : Z := 0x1c164.
Definition STR_RWA : Z := 0x10e6a.

Local Ltac mi := match goal with H : mem_inv usegs _ |- _ => exact H end.

(* [comment removed for export] *)
Lemma rwa_bytes : forall m, mem_inv usegs m ->
  bytes_at usegs m STR_RWA ([Z_to_bv 8 114; Z_to_bv 8 119; Z_to_bv 8 97] ++ Z_to_bv 8 0 :: [Z_to_bv 8 47; Z_to_bv 8 100]).
Proof.
  intros m MI. unfold STR_RWA. apply ro_bytes_at; [exact MI | lia | cbn; lia |]. apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Lemma rwa_has : forall c, c = 114 \/ c = 119 -> has_byte c [Z_to_bv 8 114; Z_to_bv 8 119; Z_to_bv 8 97] = true.
Proof. intros c [-> | ->]; reflexivity. Qed.

(* [comment removed for export] *)
Definition flk_cells (flags : word)
    (rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd : Z)
    (mode lock lbf : word) (tail : list byte) : list cell :=
  [C4 flags; C4 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 rpos); C8 (Z_to_bv 64 rend); C8 (Z_to_bv 64 closefn);
   C8 (Z_to_bv 64 wend); C8 (Z_to_bv 64 wpos); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 wbase);
   C8 (Z_to_bv 64 readfn); C8 (Z_to_bv 64 writefn); C8 (Z_to_bv 64 seekfn);
   C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 bufsize);
   C8 (Z_to_bv 64 prev); C8 (Z_to_bv 64 next);
   C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C4 mode; C4 lock; C4 lbf; C4 (Z_to_bv 64 0);
   CB 80 tail].

Lemma bytes_eq_of_unsigned' : forall bs bs' : list byte, map bv_unsigned bs = map bv_unsigned bs' -> bs = bs'.
Proof.
  induction bs as [|b bs IH]; intros [|b' bs'] E; cbn in E; try discriminate E; [reflexivity|].
  injection E as E1 E2. f_equal; [apply bv_eq; exact E1 | apply IH; exact E2].
Qed.

Lemma zero_file_cells : forall m P,
  rw_cells usegs m P [CB (Z.to_nat 232) (repeat (Z_to_bv 8 (0 mod 256)) (Z.to_nat 232))] ->
  rw_cells usegs m P (flk_cells (Z_to_bv 64 0) 0 0 0 0 0 0 0 0 0 0 0 0 0 0 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (repeat (Z_to_bv 8 0) 80)).
Proof.
  intros m P H. eapply rw_cells_recast; [exact H | | |].
  - vm_compute. repeat split; exact I.
  - apply bytes_eq_of_unsigned'. vm_compute. reflexivity.
  - reflexivity.
Qed.

Definition memset_postv (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Dst V N : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(Dst, Dst + N)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ rw_cells usegs m' Dst [CB (Z.to_nat N) (repeat (Z_to_bv 8 (V mod 256)) (Z.to_nat N))].
Definition memset_callw__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (Dst V N : Z) (junk : list byte),
  rw_cells usegs m Dst [CB (Z.to_nat N) junk] ->
  (0 <= N) -> (0 <= Dst) -> (Dst + N < 2^64) -> (0 <= V < 2^64) -> mem_inv usegs m ->
  evt usegs (memset_postv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Dst V N m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) (Z_to_bv 64 V) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x21520) fc None m (seg_rom usegs)).
Section Sz5.
Variables ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Dst V N junk : ltac2:(SecDiet.SzSec.tyM 'memset_callw__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
#[using="Type"] Lemma memset_callw__body : ltac2:(SecDiet.SzSec.bodyP 'memset_callw__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
 intros DST HN HD HDN HV MI.
  assert (ED : bv_unsigned (Z_to_bv 64 Dst : word) = Dst) by (apply unsigned_lit; lia).
  assert (EV : bv_unsigned (Z_to_bv 64 V : word) = V) by (apply unsigned_lit; lia).
  assert (EN : bv_unsigned (Z_to_bv 64 N : word) = N) by (apply unsigned_lit; lia).
  eapply evt_mono. { eapply memset_spec with (junk := junk); rewrite ?ED, ?EN; [exact DST | exact MI]. }
  intros ms' PO. unfold memset_post, memset_postv in *. rewrite ED, EV, EN in PO. exact PO.
Qed.
End Sz5.
Lemma memset_callw : ltac:(let t := eval cbv delta [memset_callw__stmt] in memset_callw__stmt in exact t).
Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Dst V N junk. ltac2:(SecDiet.SzSec.closeP 'memset_callw__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

Lemma le4_m1 : le4 (Z_to_bv 64 (-1)) = le4 (Z_to_bv 64 4294967295).
Proof. apply bytes_eq_of_unsigned'. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma fdopen_cells_recast : forall m P flags closefn readfn writefn seekfn buf bufsize prev next fd mode tail,
  rw_cells usegs m P (flk_cells flags 0 0 closefn 0 0 0 readfn writefn seekfn buf bufsize prev next fd mode (Z_to_bv 64 (-1)) (Z_to_bv 64 (-1)) tail) ->
  rw_cells usegs m P (file_cells flags 0 0 closefn 0 0 0 readfn writefn seekfn buf bufsize prev next fd mode 4294967295 tail).
Proof.
  intros. eapply rw_cells_recast; [exact H | | |].
  - destruct H as [[W _] _]. unfold flk_cells, file_cells in *. cbn in W |- *. exact W.
  - unfold flk_cells, file_cells. cbn [cells_bytes cbytes app]. rewrite !le4_m1. reflexivity.
  - reflexivity.
Qed.

Lemma strchr_res_notfound : forall A c str, c <> 0 -> has_byte c str = false -> strchr_res A c str = 0.
Proof.
  intros A c str Hc H. unfold strchr_res, has_byte in *. replace (c =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hc).
  destruct (find_byte c str); [discriminate H| reflexivity].
Qed.

Section Fopen.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (NAME MODE lo : Z) (md slack : list byte) (m : mem).

  Hypothesis LO : lo <= bv_unsigned sp - 512.
  Hypothesis GLO : 0x56000 <= lo.
  Hypothesis SP47 : bv_unsigned sp <= 2^47.
  Hypothesis MDR : 0x10000 <= MODE /\ MODE + Z.of_nat (length md) + 1 + Z.of_nat (length slack) <= 0x13000.
  Hypothesis NONUL : ~ In (Z_to_bv 8 0) md.
  Hypothesis PAD : (- (MODE + Z.of_nat (length md) + 1)) mod 8 <= Z.of_nat (length slack).
  Hypothesis M0 : mode_m0 md = 114 \/ mode_m0 md = 119.
  Hypothesis NAMER : 0 <= NAME < 2^64.
  (* [comment removed for export] *)
  Hypothesis TPR : bv_unsigned tp + -200 = 0x34190.
  Hypothesis TPLO : bv_unsigned tp + -160 <= lo.
  Hypothesis TP200 : 200 <= bv_unsigned tp.

  (* [comment removed for export] *)
  Definition fopen_S1_post : machine_state -> Prop :=
    fun ms' => exists (x1 t0 t1 t2 a4 a5 a6 t3 t4 t5 t6 : word) (m1 : mem),
      ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 MODE) (Z_to_bv 64 NAME)
                   (Z_to_bv 64 (-100)) (Z_to_bv 64 NAME) (Z_to_bv 64 (Z.lor (fmodeflags md mod 18446744073709551616) 32768)) (Z_to_bv 64 438) a4 a5 a6 (Z_to_bv 64 56)
                   (Z_to_bv 64 (fmodeflags md)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x1b8a0) fc None m1 (seg_rom usegs)
      /\ rw_cells usegs m1 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra]
      /\ munch [(lo, bv_unsigned sp)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
      /\ stk usegs m1 lo (bv_unsigned sp + -32).

  Lemma md_bytes : ro_bytes usegs MODE (md ++ Z_to_bv 8 0 :: slack) ->
    forall m', mem_inv usegs m' -> bytes_at usegs m' (bv_unsigned (Z_to_bv 64 MODE : word)) (md ++ Z_to_bv 8 0 :: slack).
  Proof using MDR. pin_using (fun (MDR : unit) => tt).
    intros ROMD m' MI. rewrite unsigned_lit by lia. apply ro_bytes_at; [exact MI | lia | rewrite length_app; cbn [length]; lia | exact ROMD].
  Qed.

  Definition fopen_S1__stmt : Prop := forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    ro_bytes usegs MODE (md ++ Z_to_bv 8 0 :: slack) ->
    stk usegs m lo (bv_unsigned sp) -> mem_inv usegs m ->
    evt usegs fopen_S1_post
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 NAME) (Z_to_bv 64 MODE) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FOPEN) fc None m (seg_rom usegs)).
  Section Sz10.
  Variables t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : ltac2:(SecDiet.SzSec.tyM 'fopen_S1__stmt "vvvvvvvvvvvvv" @t0).
  Lemma fopen_S1__body : ltac2:(SecDiet.SzSec.bodyP 'fopen_S1__stmt "vvvvvvvvvvvvv").
  Proof using GLO LO M0 MDR NAMER NONUL PAD SP47 TPLO TPR. pin_using (fun (GLO LO M0 MDR NAMER NONUL PAD SP47 TPLO TPR : unit) => tt).
 intros ROMD ST MI.
    pose proof (md_bytes ROMD) as MDB.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold FOPEN, fopen_S1_post.
    destruct md as [|b0 mdt]. { exfalso. cbn in M0. lia. }
    pose proof (byte_range b0) as Rb0.
    assert (E0 : mode_m0 (b0 :: mdt) = bv_unsigned b0) by reflexivity. rewrite E0 in M0.
    carve_frame 32%nat ST.
    do 5 zs.
    zs. (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u8ro_read usegs mm (bv_unsigned (Z_to_bv 64 MODE : word)) _ 0 _ (Z_to_bv 64 MODE) (MDB mm ltac:(mi)) ltac:(reflexivity) ltac:(lia)
                  ltac:(rewrite Z.add_0_r; symmetry; apply Z_to_bv_bv_unsigned)) as RD end.
    zs. (* [comment removed for export] *)
    clear RD.
    zs. zs. zs.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (rwa_bytes mm ltac:(mi)) as RWA end. rewrite <- (unsigned_lit STR_RWA) in RWA by (unfold STR_RWA; lia).
    zs. call_sp strchr_spec; [exact ST | exact RWA | cbn; clear; intuition discriminate | unfold STR_RWA; rewrite unsigned_lit by lia; cbn; lia | mi | lia | unfold STR_RWA; rewrite unsigned_lit by lia; cbn [length]; lia | ].
    rename PC into ST; try clear RWA; try clear POST.
    zs. if_cases K; zify_cond K.
    { exfalso. revert K. rewrite (Z.mod_small (bv_unsigned b0) 256) by lia.
      pose proof (strchr_res_found STR_RWA (bv_unsigned b0) [Z_to_bv 8 114; Z_to_bv 8 119; Z_to_bv 8 97] ltac:(unfold STR_RWA; lia) ltac:(lia) ltac:(unfold STR_RWA; cbn; lia)) as HF.
      rewrite (rwa_has (bv_unsigned b0)) in HF by lia. unfold STR_RWA in HF. intros K. rewrite K in HF. discriminate HF. }
    zs. zs.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (MDB mm ltac:(mi)) as STR end.
    call_sp fmodeflags_spec; [exact ST | exact STR | exact NONUL | rewrite unsigned_lit by lia; exact PAD | mi | lia | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia | ].
    rename PC into ST; try clear POST.
    do 7 zs.
    apply evt_done.
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact FR|]. split; [exact MU|]. split; [exact WM|]. split; [mi| exact ST].
  Qed.
  End Sz10.
  Lemma fopen_S1 : ltac:(let t := eval cbv delta [fopen_S1__stmt] in fopen_S1__stmt in exact t).
  Proof using GLO LO M0 MDR NAMER NONUL PAD SP47 TPLO TPR. intros t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6. ltac2:(SecDiet.SzSec.closeP 'fopen_S1__body "vvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition fopen_S5__stmt : Prop := forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x20 x21 x22 t3 t4 t5 t6 : word) (m1 : mem) W,
    rw_cells usegs m1 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk usegs m1 lo (bv_unsigned sp + -32) -> mem_inv usegs m1 -> munch W m m1 -> wmono usegs m m1 ->
    evt usegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
        ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (ret_pc ra) fc None m1 (seg_rom usegs)
        /\ munch W m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1 /\ stk usegs m1 lo (bv_unsigned sp))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 x20 x21 a0 a1 a2 a3 a4 a5 a6 a7 x22 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1b8f4) fc None m1 (seg_rom usegs)).
  Section Sz11.
  Variables x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x20 x21 x22 t3 t4 t5 t6 m1 W : ltac2:(SecDiet.SzSec.tyM 'fopen_S5__stmt "vvvvvvvvvvvvvvvvvvvvv" @x1).
  Lemma fopen_S5__body : ltac2:(SecDiet.SzSec.bodyP 'fopen_S5__stmt "vvvvvvvvvvvvvvvvvvvvv").
  Proof using LO MODE md slack. pin_using (fun (LO MODE md slack : unit) => tt).
 intros FR ST MI MU WM.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    zs. zs. do 6 zs.
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
  Qed.
  End Sz11.
  Lemma fopen_S5 : ltac:(let t := eval cbv delta [fopen_S5__stmt] in fopen_S5__stmt in exact t).
  Proof using LO MODE md slack. intros x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x20 x21 x22 t3 t4 t5 t6 m1 W. ltac2:(SecDiet.SzSec.closeP 'fopen_S5__body "vvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition fopen_S2_fail__stmt : Prop := forall (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x22 t3 t4 t5 t6 : word) (m1 : mem) (e : Z) (errv : word),
    rw_cells usegs m1 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells usegs m1 (bv_unsigned tp + -164) [C4 errv] ->
    1 <= e <= 4095 ->
    stk usegs m1 lo (bv_unsigned sp + -32) -> mem_inv usegs m1 -> munch [(lo, bv_unsigned sp)] m m1 -> wmono usegs m m1 ->
    evt usegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
        ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (ret_pc ra) fc None m' (seg_rom usegs)
        /\ munch [(lo, bv_unsigned sp); (bv_unsigned tp + -164, bv_unsigned tp + -160)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
        /\ stk usegs m' lo (bv_unsigned sp)
        /\ rw_cells usegs m' (bv_unsigned tp + -164) [C4 (Z_to_bv 64 e)])
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 MODE) (Z_to_bv 64 NAME) (errno_ret e) a1 a2 a3 a4 a5 a6 a7 x22 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1b8a4) fc None m1 (seg_rom usegs)).
  Section Sz12.
  Variables x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x22 t3 t4 t5 t6 m1 e errv : ltac2:(SecDiet.SzSec.tyM 'fopen_S2_fail__stmt "vvvvvvvvvvvvvvvvvvv" @x1).
  Lemma fopen_S2_fail__body : ltac2:(SecDiet.SzSec.bodyP 'fopen_S2_fail__stmt "vvvvvvvvvvvvvvvvvvv").
  Proof using GLO LO SP47 TP200 TPLO md slack. pin_using (fun (GLO LO SP47 TP200 TPLO md slack : unit) => tt).
 intros FR ERR HE ST MI MU WM.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    apply (munch_weaken [(lo, bv_unsigned sp)] [(lo, bv_unsigned sp); (bv_unsigned tp + -164, bv_unsigned tp + -160)]) in MU.
    2:{ unfold sub_fp. cbn [outside]. intros x Hx. lia. }
    zs. call_sp sysret_spec; [exact ST | exact ERR | mi | lia | lia | lia |].
    rename PC into ST.
    unfold sysret_val, sysret_errno in *. rewrite (errno_of_errno_ret e) in * by lia.
    zs. zs. if_cases K; zify_cond K.
    2:{ exfalso. lia. }
    eapply evt_mono; [eapply (fopen_S5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); [exact FR| exact ST| mi| exact MU| exact WM]|].
    cbv beta. intros ms' PO. destruct_exs PO. destruct PO as (-> & MU' & WM' & MI' & ST').
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|]. split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'|]. split; [exact ST'|]. assumption.
  Qed.
  End Sz12.
  Lemma fopen_S2_fail : ltac:(let t := eval cbv delta [fopen_S2_fail__stmt] in fopen_S2_fail__stmt in exact t).
  Proof using GLO LO SP47 TP200 TPLO md slack. intros x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x22 t3 t4 t5 t6 m1 e errv. ltac2:(SecDiet.SzSec.closeP 'fopen_S2_fail__body "vvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition fopen_S2_post (fd : Z) (canary errv : word) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 sv2 : word) (j0 : list byte) (m2 : mem),
      ms' = MS (mkR (Z_to_bv 64 0x1ba28) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 MODE) (Z_to_bv 64 fd)
                   (Z_to_bv 64 1264) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 MODE) (Z_to_bv 64 ssp_guard) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x1908c) fc None m2 (seg_rom usegs)
      /\ rw_cells usegs m2 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra]
      /\ rw_cells usegs m2 (bv_unsigned sp + -96) [CB 16 j0; C8 canary; C8 s3; C8 sv2; C8 (Z_to_bv 64 fd); C8 (Z_to_bv 64 MODE); C8 (Z_to_bv 64 0x1b8e0)]
      /\ rw_cells usegs m2 (bv_unsigned tp + -164) [C4 errv]
      /\ ssp_cells m2 canary
      /\ munch [(lo, bv_unsigned sp); (bv_unsigned tp + -164, bv_unsigned tp + -160)] m m2 /\ wmono usegs m m2 /\ mem_inv usegs m2
      /\ stk usegs m2 lo (bv_unsigned sp + -96).

  Definition fopen_S2_ok__stmt : Prop := forall (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m1 : mem) (fd : Z) (canary errv : word),
    ro_bytes usegs MODE (md ++ Z_to_bv 8 0 :: slack) ->
    rw_cells usegs m1 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells usegs m1 (bv_unsigned tp + -164) [C4 errv] -> ssp_cells m1 canary ->
    3 <= fd <= 4096 ->
    (fmodeflags md = 0 \/ fmodeflags md = 577) ->
    stk usegs m1 lo (bv_unsigned sp + -32) -> mem_inv usegs m1 -> munch [(lo, bv_unsigned sp)] m m1 -> wmono usegs m m1 ->
    evt usegs (fopen_S2_post fd canary errv)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 MODE) (Z_to_bv 64 NAME) (Z_to_bv 64 fd) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (fmodeflags md)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1b8a4) fc None m1 (seg_rom usegs)).
  Section Sz13.
  Variables x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m1 fd canary errv : ltac2:(SecDiet.SzSec.tyM 'fopen_S2_ok__stmt "vvvvvvvvvvvvvvvvvvv" @x1).
  Lemma fopen_S2_ok__body : ltac2:(SecDiet.SzSec.bodyP 'fopen_S2_ok__stmt "vvvvvvvvvvvvvvvvvvv").
  Proof using GLO LO M0 MDR NAMER NONUL PAD SP47 TP200 TPLO TPR. pin_using (fun (GLO LO M0 MDR NAMER NONUL PAD SP47 TP200 TPLO TPR : unit) => tt).
 intros ROMD FR ERR SSP FD FLV ST MI MU WM.
    pose proof (md_bytes ROMD) as MDB.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in *. unfold fopen_S2_post, ssp_cells, got_ssp, ssp_guard.
    destruct md as [|b0 mdt]. { exfalso. cbn in M0. lia. }
    pose proof (byte_range b0) as Rb0.
    assert (E0 : mode_m0 (b0 :: mdt) = bv_unsigned b0) by reflexivity. rewrite E0 in M0.
    apply (munch_weaken [(lo, bv_unsigned sp)] [(lo, bv_unsigned sp); (bv_unsigned tp + -164, bv_unsigned tp + -160)]) in MU.
    2:{ unfold sub_fp. cbn [outside]. intros x Hx. lia. }
    zs. call_sp sysret_spec; [exact ST | exact ERR | mi | lia | lia | lia |].
    rename PC into ST. rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite (errno_of_lit fd) in * by lia.
    zs. rewrite ?(sextw_small fd), ?(sx32_small fd) by lia.
    zs. if_cases K; zify_cond K. 1:{ exfalso. revert K. rewrite Z.add_0_r, (swrap32_small fd) by lia. rewrite Z.mod_small by lia. lia. }
    rewrite Z.add_0_r, (swrap32_small fd) by lia.
    zs. zs. zs. if_cases K2; zify_cond K2.
    2:{ exfalso. revert K2. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mod_small by (destruct FLV as [E|E]; rewrite E; lia). destruct FLV as [E|E]; rewrite E; lia. }
    zs. zs. zs.
    (* [comment removed for export] *)
    carve_frame 64%nat ST.
    do 6 zs. zs. zs. zs. zs. zs.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u8ro_read usegs mm (bv_unsigned (Z_to_bv 64 MODE : word)) _ 0 _ (Z_to_bv 64 MODE) (MDB mm ltac:(mi)) ltac:(reflexivity) ltac:(lia)
                  ltac:(rewrite Z.add_0_r; symmetry; apply Z_to_bv_bv_unsigned)) as RD end.
    zs. clear RD. zs. zs. zs.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (rwa_bytes mm ltac:(mi)) as RWA end. rewrite <- (unsigned_lit STR_RWA) in RWA by (unfold STR_RWA; lia).
    zs. call_sp strchr_spec; [exact ST | exact RWA | cbn; clear; intuition discriminate | unfold STR_RWA; rewrite unsigned_lit by lia; cbn; lia | mi | lia | unfold STR_RWA; rewrite unsigned_lit by lia; cbn [length]; lia | ].
    rename PC into ST; try clear RWA; try clear POST.
    zs. if_cases K3; zify_cond K3.
    { exfalso. revert K3. rewrite (Z.mod_small (bv_unsigned b0) 256) by lia.
      pose proof (strchr_res_found STR_RWA (bv_unsigned b0) [Z_to_bv 8 114; Z_to_bv 8 119; Z_to_bv 8 97] ltac:(unfold STR_RWA; lia) ltac:(lia) ltac:(unfold STR_RWA; cbn; lia)) as HF.
      rewrite (rwa_has (bv_unsigned b0)) in HF by lia. unfold STR_RWA in HF. intros K3. rewrite K3 in HF. discriminate HF. }
    zs. zs.
    apply evt_done.
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split; [assumption|]. split; [eassumption|].
    split; [assumption|]. split; [split; assumption|].
    split; [assumption|]. split; [assumption|]. split; [mi| assumption].
  Qed.
  End Sz13.
  Lemma fopen_S2_ok : ltac:(let t := eval cbv delta [fopen_S2_ok__stmt] in fopen_S2_ok__stmt in exact t).
  Proof using GLO LO M0 MDR NAMER NONUL PAD SP47 TP200 TPLO TPR. intros x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m1 fd canary errv. ltac2:(SecDiet.SzSec.closeP 'fopen_S2_ok__body "vvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition fopen_S4__stmt : Prop := forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 sv2 : word) (j0 : list byte) (m2 : mem) (fd : Z) (canary : word),
    rw_cells usegs m2 (bv_unsigned sp + -96) [CB 16 j0; C8 canary; C8 s3; C8 sv2; C8 (Z_to_bv 64 fd); C8 (Z_to_bv 64 MODE); C8 (Z_to_bv 64 0x1b8e0)] ->
    ssp_cells m2 canary -> 3 <= fd <= 4096 -> mem_inv usegs m2 ->
    evt usegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' t3' t4' t5' t6' : word),
        ms' = MS (mkR (Z_to_bv 64 0x1b8e0) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0' t1' t2' (Z_to_bv 64 MODE) (Z_to_bv 64 fd)
                     (Z_to_bv 64 fd) a1' a2' a3' a4' a5' a6' (Z_to_bv 64 57) sv2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (Z_to_bv 64 0x1b8f0) fc None m2 (seg_rom usegs))
      (MS (mkR (Z_to_bv 64 0x1ba28) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 MODE) (Z_to_bv 64 fd)
               (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 MODE) (Z_to_bv 64 ssp_guard) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1ba28) fc None m2 (seg_rom usegs)).
  Section Sz14.
  Variables t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 sv2 j0 m2 fd canary : ltac2:(SecDiet.SzSec.tyM 'fopen_S4__stmt "vvvvvvvvvvvvvvvvvvv" @t0).
  Lemma fopen_S4__body : ltac2:(SecDiet.SzSec.bodyP 'fopen_S4__stmt "vvvvvvvvvvvvvvvvvvv").
  Proof using md slack. pin_using (fun (md slack : unit) => tt).
 intros FRI SSP FD MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in *.
    pose proof (munch_refl [] m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    zs. if_true.
    zs. zs. zs. if_cases K; zify_cond K. 1:{ exfalso. apply K. reflexivity. }
    do 7 zs.
    replace (ret_pc (Z_to_bv 64 0x1b8e0)) with (Z_to_bv 64 0x1b8e0 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    zs. if_cases K2; zify_cond K2. 1:{ exfalso. rewrite ?Z.mod_small in K2 by lia. lia. }
    zs. zs. zs. rewrite (Z.mod_small fd 2147483648) by lia.
    apply evt_done. repeat (lazymatch goal with |- ex _ => eexists end). cbv delta [mkR]. reflexivity.
  Qed.
  End Sz14.
  Lemma fopen_S4 : ltac:(let t := eval cbv delta [fopen_S4__stmt] in fopen_S4__stmt in exact t).
  Proof using md slack. intros t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 sv2 j0 m2 fd canary. ltac2:(SecDiet.SzSec.closeP 'fopen_S4__body "vvvvvvvvvvvvvvvvvvv"). Qed.

  Hypothesis NOPLUS : has_byte 43 md = false.
  Hypothesis NOE : has_byte 101 md = false.

  (* [comment removed for export] *)
  Definition fopen_S6_post (fl P fd : Z) (canary : word) (junk2 : list byte) (m2 : mem) : machine_state -> Prop :=
    fun ms' => exists (x1 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m3 : mem),
      ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 P) (Z_to_bv 64 fd)
                   (Z_to_bv 64 (Z.land fl 8)) (Z_to_bv 64 (P + 240)) (Z_to_bv 64 1024) (Z_to_bv 64 (-1)) a4 a5 a6 a7
                   (Z_to_bv 64 MODE) (Z_to_bv 64 ssp_guard) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x1bb14) fc None m3 (seg_rom usegs)
      /\ rw_cells usegs m3 P (flk_cells (Z_to_bv 64 fl) 0 0 0 0 0 0 0 0 0 (P + 240) 1024 0 0 fd
                               (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (-1)) (repeat (Z_to_bv 8 0) 80))
      /\ rw_cells usegs m3 (P + 232) [CB 1032 junk2]
      /\ rw_cells usegs m3 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra]
      /\ (exists sv2 j0, rw_cells usegs m3 (bv_unsigned sp + -96) [CB 16 j0; C8 canary; C8 s3; C8 sv2; C8 (Z_to_bv 64 fd); C8 (Z_to_bv 64 MODE); C8 (Z_to_bv 64 0x1b8e0)])
      /\ ssp_cells m3 canary
      /\ munch [(lo, bv_unsigned sp); (P, P + 232)] m2 m3 /\ wmono usegs m2 m3 /\ mem_inv usegs m3
      /\ stk usegs m3 lo (bv_unsigned sp + -96).

  Definition fopen_S6__stmt : Prop := forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 sv2 : word) (j0 junk : list byte) (m2 : mem) (P fd : Z) (canary : word),
    ro_bytes usegs MODE (md ++ Z_to_bv 8 0 :: slack) ->
    rw_cells usegs m2 P [CB (Z.to_nat 1264) junk] -> 0 < P -> (P + 1264 <= 0x10000 \/ 0x56000 <= P) -> P + 1264 <= lo ->
    rw_cells usegs m2 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells usegs m2 (bv_unsigned sp + -96) [CB 16 j0; C8 canary; C8 s3; C8 sv2; C8 (Z_to_bv 64 fd); C8 (Z_to_bv 64 MODE); C8 (Z_to_bv 64 0x1b8e0)] ->
    ssp_cells m2 canary -> 3 <= fd <= 4096 ->
    stk usegs m2 lo (bv_unsigned sp + -96) -> mem_inv usegs m2 ->
    evt usegs (fopen_S6_post (if mode_m0 md =? 114 then 8 else 4) P fd canary (skipn 232 junk) m2)
      (MS (mkR (Z_to_bv 64 0x1ba28) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 MODE) (Z_to_bv 64 fd)
               (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 MODE) (Z_to_bv 64 ssp_guard) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1ba28) fc None m2 (seg_rom usegs)).
  Section Sz15.
  Variables t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 sv2 j0 junk m2 P fd canary : ltac2:(SecDiet.SzSec.tyM 'fopen_S6__stmt "vvvvvvvvvvvvvvvvvvvvv" @t0).
  Lemma fopen_S6__body : ltac2:(SecDiet.SzSec.bodyP 'fopen_S6__stmt "vvvvvvvvvvvvvvvvvvvvv").
  Proof using GLO LO M0 MDR NOE NONUL NOPLUS PAD SP47 TPLO. pin_using (fun (GLO LO M0 MDR NOE NONUL NOPLUS PAD SP47 TPLO : unit) => tt).
 intros ROMD BLK P0 PST PLO FRO FRI SSP FD ST MI.
    pose proof (md_bytes ROMD) as MDB.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in *. unfold ssp_cells, got_ssp, ssp_guard.
    destruct md as [|b0 mdt]. { exfalso. cbn in M0. lia. }
    pose proof (byte_range b0) as Rb0.
    assert (E0 : mode_m0 (b0 :: mdt) = bv_unsigned b0) by reflexivity. rewrite E0 in M0 |- *.
    set (fl := if bv_unsigned b0 =? 114 then 8 else 4).
    assert (FLR : (bv_unsigned b0 = 114 /\ fl = 8) \/ (bv_unsigned b0 = 119 /\ fl = 4)).
    { subst fl. destruct (Z.eqb_spec (bv_unsigned b0) 114) as [E|E]; [left | right]; lia. }
    clearbody fl.
    pose proof (munch_refl [(lo, bv_unsigned sp); (P, P + 232)] m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    assert (LJ : length junk = 1264%nat) by (destruct BLK as [[WF _] _]; cbn in WF; exact (proj1 WF)).
    apply (rw_cells_split_CB usegs _ _ [] (Z.to_nat 1264) junk [] [232; 1032]%nat) in BLK; [| cbn; lia].
    cbn [mk_CB_cells app] in BLK. apply (proj1 (rw_cells_app usegs _ _ [_] _)) in BLK. destruct BLK as [BLK1 BLK2].
    cbn [cells_size csize Nat.add] in BLK2. rewrite firstn_all2 in BLK2 by (rewrite length_skipn; lia).
    zs. if_cases K; zify_cond K. 1:{ exfalso. rewrite ?Z.mod_small in K by lia. lia. }
    zs. zs. zs. zs.
    call_sp memset_callw; [exact BLK1 | lia | lia | lia | lia | mi |].
    lazymatch goal with H : rw_cells usegs _ P [CB (Z.to_nat 232) (repeat _ _)] |- _ => apply zero_file_cells in H; rename H into FC end.
    unfold flk_cells in FC.
    (* [comment removed for export] *)
    zs. zs.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (MDB mm ltac:(mi)) as STR end.
    zs. call_sp strchr_spec; [exact ST | exact STR | exact NONUL | rewrite unsigned_lit by lia; exact PAD | mi | lia | rewrite unsigned_lit by lia; lia | ].
    rename PC into ST; try clear POST; try clear STR.
    rewrite !unsigned_lit by lia. change (43 mod 256) with 43.
    rewrite (strchr_res_notfound MODE 43 (b0 :: mdt) ltac:(lia) NOPLUS).
    zs. if_cases K2; zify_cond K2. 1:{ exfalso. apply K2. reflexivity. }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u8ro_read usegs mm (bv_unsigned (Z_to_bv 64 MODE : word)) _ 0 _ (Z_to_bv 64 MODE) (MDB mm ltac:(mi)) ltac:(reflexivity) ltac:(lia)
                  ltac:(rewrite Z.add_0_r; symmetry; apply Z_to_bv_bv_unsigned)) as RD end.
    zs. clear RD. zs.
    (* [comment removed for export] *)
    assert (JOIN : forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) mm,
      mem_inv usegs mm -> munch [(lo, bv_unsigned sp); (P, P + 232)] m2 mm -> wmono usegs m2 mm ->
      stk usegs mm lo (bv_unsigned sp + -96) ->
      rw_cells usegs mm P (flk_cells (Z_to_bv 64 fl) 0 0 0 0 0 0 0 0 0 0 0 0 0 0 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (repeat (Z_to_bv 8 0) 80)) ->
      rw_cells usegs mm (P + 232) [CB 1032 (skipn 232 junk)] ->
      rw_cells usegs mm (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells usegs mm (bv_unsigned sp + -96) [CB 16 j0; C8 canary; C8 s3; C8 sv2; C8 (Z_to_bv 64 fd); C8 (Z_to_bv 64 MODE); C8 (Z_to_bv 64 0x1b8e0)] ->
      rw_cells usegs mm 142816 [C8 (Z_to_bv 64 345288)] -> rw_cells usegs mm 345288 [C8 canary] ->
      evt usegs (fopen_S6_post fl P fd canary (skipn 232 junk) m2)
        (MS (mkR (Z_to_bv 64 0x1ba48) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0' t1' t2' (Z_to_bv 64 P) (Z_to_bv 64 fd)
                 (Z_to_bv 64 fl) a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 MODE) (Z_to_bv 64 345288) s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
            F (Z_to_bv 64 0x1ba80) fc None mm (seg_rom usegs))).
    { intros until mm. intros MIj MUj WMj STj FCj BLKj FROj FRIj GOTj GUARDj. unfold flk_cells in FCj.
      zs. zs.
      pose proof (MDB mm MIj) as STR.
      zs. call_sp strchr_spec; [exact STj | exact STR | exact NONUL | rewrite unsigned_lit by lia; exact PAD | mi | lia | rewrite unsigned_lit by lia; lia | ].
      rename PC into STj; try clear POST; try clear STR.
      rewrite !unsigned_lit by lia. change (101 mod 256) with 101.
      rewrite (strchr_res_notfound MODE 101 (b0 :: mdt) ltac:(lia) NOE).
      zs. if_true.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm2 _) =>
        pose proof (u8ro_read usegs mm2 (bv_unsigned (Z_to_bv 64 MODE : word)) _ 0 _ (Z_to_bv 64 MODE) (MDB mm2 ltac:(mi)) ltac:(reflexivity) ltac:(lia)
                    ltac:(rewrite Z.add_0_r; symmetry; apply Z_to_bv_bv_unsigned)) as RD end.
      zs. clear RD. zs. zs. if_cases K3; zify_cond K3. 2:{ exfalso. rewrite ?unsigned_lit, ?Z.mod_small in K3 by lia. lia. }
      zs. rewrite (sx32_small fl) by lia. zs. zs. zs. zs. rewrite ?(unsigned_lit fl) by lia. zs. zs. zs. zs.
      apply evt_done. unfold fopen_S6_post, flk_cells.
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|].
      split; [match goal with H : rw_cells usegs _ P _ |- _ => exact H end|].
      split; [assumption|]. split; [assumption|]. split; [do 2 eexists; eassumption|]. split; [split; assumption|].
      split; [assumption|]. split; [assumption|]. split; [mi| assumption]. }
    zs. if_cases K4; zify_cond K4.
    - (* [comment removed for export] *) zs. zs.
      assert (EF : fl = 8) by (rewrite ?unsigned_lit, ?Z.mod_small in K4 by lia; lia). rewrite <- EF in FC |- *.
      eapply JOIN; try eassumption; mi.
    - (* [comment removed for export] *) zs. zs. zs.
      assert (EF : fl = 4) by (rewrite ?unsigned_lit, ?Z.mod_small in K4 by lia; lia). rewrite <- EF in FC |- *.
      eapply JOIN; try eassumption; mi.
  Qed.
  End Sz15.
  Lemma fopen_S6 : ltac:(let t := eval cbv delta [fopen_S6__stmt] in fopen_S6__stmt in exact t).
  Proof using GLO LO M0 MDR NOE NONUL NOPLUS PAD SP47 TPLO. intros t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 sv2 j0 junk m2 P fd canary. ltac2:(SecDiet.SzSec.closeP 'fopen_S6__body "vvvvvvvvvvvvvvvvvvvvv"). Qed.

  Definition fopen_S7_post (fl P fd hd : Z) (canary : word) (junk2 : list byte) (m2 : mem) (W : list (Z * Z)) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ rw_cells usegs m' P (file_cells (Z_to_bv 64 fl) 0 0 F_STDIO_CLOSE 0 0 0 F_STDIO_READ F_STDIO_WRITE F_STDIO_SEEK (P + 240) 1024 0 hd fd
                               (Z_to_bv 64 0) 4294967295 (repeat (Z_to_bv 8 0) 80))
      /\ rw_cells usegs m' (P + 232) [CB 1032 junk2]
      /\ rw_cells usegs m' A_OFL_LOCK [C4 (Z_to_bv 64 0)] /\ rw_cells usegs m' A_OFL_HEAD [C8 (Z_to_bv 64 P)]
      /\ (hd <> 0 -> rw_cells usegs m' (hd + 104) [C8 (Z_to_bv 64 P)])
      /\ ssp_cells m' canary
      /\ munch W m2 m' /\ wmono usegs m2 m' /\ mem_inv usegs m'
      /\ stk usegs m' lo (bv_unsigned sp).

  (* [comment removed for export] *)
  Definition fopen_S7_tail__stmt : Prop := forall (fl P fd hd wt : Z) (canary sv2 : word) (j0 junk2 : list byte) (m2 : mem),
    0 < P -> (P + 1264 <= 0x10000 \/ 0x56000 <= P) -> P + 1264 <= lo -> 3 <= fd <= 4096 -> 0 <= hd -> hd + 232 < 2^63 ->
    ((hd = 0 /\ wt = 104) \/ (hd <> 0 /\ wt = 112 /\ hd + 232 <= lo /\ (hd + 232 <= P \/ P + 1264 <= hd) /\ (hd + 232 <= 65536 \/ 352256 <= hd))) ->
    forall (x1' t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) mm,
      mem_inv usegs mm -> munch [(lo, bv_unsigned sp); (P, P + 232); (346384, 346384 + 8); (hd + 104, hd + wt)] m2 mm -> wmono usegs m2 mm ->
      stk usegs mm lo (bv_unsigned sp + -112) ->
      rw_cells usegs mm (bv_unsigned sp + -112) [C8 (Z_to_bv 64 P); C8 (Z_to_bv 64 0x1bb88)] ->
      rw_cells usegs mm P [C4 (Z_to_bv 64 fl); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 F_STDIO_CLOSE);
                           C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                           C8 (Z_to_bv 64 F_STDIO_READ); C8 (Z_to_bv 64 F_STDIO_WRITE); C8 (Z_to_bv 64 F_STDIO_SEEK);
                           C8 (Z_to_bv 64 (P + 240)); C8 (Z_to_bv 64 1024); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 hd);
                           C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                           C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 0); CB 80 (repeat (Z_to_bv 8 0) 80)] ->
      rw_cells usegs mm (P + 232) [CB 1032 junk2] ->
      rw_cells usegs mm (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells usegs mm (bv_unsigned sp + -96) [CB 16 j0; C8 canary; C8 s3; C8 sv2; C8 (Z_to_bv 64 fd); C8 (Z_to_bv 64 MODE); C8 (Z_to_bv 64 0x1b8e0)] ->
      rw_cells usegs mm 142816 [C8 (Z_to_bv 64 345288)] -> rw_cells usegs mm 345288 [C8 canary] ->
      rw_cells usegs mm 346376 [C4 (Z_to_bv 64 0)] -> rw_cells usegs mm 346384 [C8 (Z_to_bv 64 hd)] ->
      (hd <> 0 -> rw_cells usegs mm (hd + 104) [C8 (Z_to_bv 64 P)]) ->
      evt usegs (fopen_S7_post fl P fd hd canary junk2 m2 [(lo, bv_unsigned sp); (P, P + 232); (346384, 346384 + 8); (hd + 104, hd + wt)])
        (MS (mkR x1' (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0' t1' t2' (Z_to_bv 64 P) (Z_to_bv 64 fd)
                 (Z_to_bv 64 346384) (Z_to_bv 64 hd) a2' a3' a4' a5' a6' a7' (Z_to_bv 64 MODE) (Z_to_bv 64 345288) s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
            F (Z_to_bv 64 0x1c188) fc None mm (seg_rom usegs)).
  Section Sz16.
  Variables fl P fd hd wt canary sv2 j0 junk2 m2 : ltac2:(SecDiet.SzSec.tyM 'fopen_S7_tail__stmt "vvvvvvvvvv" @fl).
  Lemma fopen_S7_tail__body : ltac2:(SecDiet.SzSec.bodyP 'fopen_S7_tail__stmt "vvvvvvvvvv").
  Proof using GLO LO SP47 TPLO md slack. pin_using (fun (GLO LO SP47 TPLO md slack : unit) => tt).
    intros P0 PST PLO FD HD0 HDHI HFACTS.
    (* [comment removed for export] *)
    try change (213400 + 8)%Z with 213408%Z. try change (346384 + 8)%Z with 346392%Z.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
      intros until mm. intros MIj MUj WMj STj FRAj FCj BLKj FROj FRIj GOTj GUARDj OLj OHj OLDHj.
      destruct HFACTS as [[HZ ->] | (HNZ & -> & HL1 & HL2 & HL3)]; [| specialize (OLDHj HNZ)].
      all: zs. (* [comment removed for export] *)
      all: zs; zs; zs; zs.
      all: call_sp unlock_spec0; [rewrite unsigned_lit by lia; exact OLj | mi |].
      all: zs; zs; zs; zs; release_frame FRAj STj (bv_unsigned sp + -96); zs.
      (* [comment removed for export] *)
      all: zs; zs; zs; if_cases KC; zify_cond KC; [exfalso; apply KC; reflexivity|].
      all: do 6 zs; release_frame FRIj STj (bv_unsigned sp + -32); zs.
      all: replace (ret_pc (Z_to_bv 64 0x1b8e0)) with (Z_to_bv 64 0x1b8e0 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      all: zs; if_cases KP; zify_cond KP; [| exfalso; rewrite ?Z.mod_small in KP by lia; lia].
      all: do 5 zs; release_frame FROj STj (bv_unsigned sp); zs.
      all: apply evt_done; unfold fopen_S7_post.
      all: repeat (lazymatch goal with |- ex _ => eexists end).
      all: split; [cbv delta [mkR]; reflexivity|].
      all: split; [apply fdopen_cells_recast; unfold flk_cells; exact FCj|].
      all: split; [assumption|]; split; [assumption|]; split; [assumption|].
      all: split; [intros NZ; first [assumption | exfalso; exact (NZ HZ)]|].
      all: split; [split; assumption|]; split; [assumption|]; split; [assumption|]; split; [mi| assumption].
  Qed.
  End Sz16.
  Lemma fopen_S7_tail : ltac:(let t := eval cbv delta [fopen_S7_tail__stmt] in fopen_S7_tail__stmt in exact t).
  Proof using GLO LO SP47 TPLO md slack. intros fl P fd hd wt canary sv2 j0 junk2 m2. ltac2:(SecDiet.SzSec.closeP 'fopen_S7_tail__body "vvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition fopen_S7__stmt : Prop := forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 sv2 : word) (j0 junk2 : list byte) (m2 m3 : mem) (fl P fd hd : Z) (canary : word) W,
    rw_cells usegs m3 P (flk_cells (Z_to_bv 64 fl) 0 0 0 0 0 0 0 0 0 (P + 240) 1024 0 0 fd (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (-1)) (repeat (Z_to_bv 8 0) 80)) ->
    rw_cells usegs m3 (P + 232) [CB 1032 junk2] -> 0 < P -> (P + 1264 <= 0x10000 \/ 0x56000 <= P) -> P + 1264 <= lo -> 3 <= fd <= 4096 ->
    rw_cells usegs m3 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells usegs m3 (bv_unsigned sp + -96) [CB 16 j0; C8 canary; C8 s3; C8 sv2; C8 (Z_to_bv 64 fd); C8 (Z_to_bv 64 MODE); C8 (Z_to_bv 64 0x1b8e0)] ->
    ssp_cells m3 canary ->
    rw_cells usegs m3 0x544e9 [C1 (Z_to_bv 8 0)] -> rw_cells usegs m3 NEED_LOCKS [C1 (Z_to_bv 8 0)] ->
    rw_cells usegs m3 A_OFL_LOCK [C4 (Z_to_bv 64 0)] -> rw_cells usegs m3 A_OFL_HEAD [C8 (Z_to_bv 64 hd)] ->
    0 <= hd -> hd + 232 < 2^63 ->
    (hd = 0 \/ (hd <> 0 /\ (exists pvo : word, rw_cells usegs m3 (hd + 104) [C8 pvo]) /\ hd + 232 <= lo /\ (hd + 232 <= P \/ P + 1264 <= hd) /\ (hd + 232 <= 0x10000 \/ 0x56000 <= hd))) ->
    munch W m2 m3 -> wmono usegs m2 m3 ->
    sub_fp W [(lo, bv_unsigned sp); (P, P + 232); (A_OFL_HEAD, A_OFL_HEAD + 8); (hd + 104, hd + (if hd =? 0 then 104 else 112))] ->
    stk usegs m3 lo (bv_unsigned sp + -96) -> mem_inv usegs m3 ->
    evt usegs (fopen_S7_post fl P fd hd canary junk2 m2 [(lo, bv_unsigned sp); (P, P + 232); (A_OFL_HEAD, A_OFL_HEAD + 8); (hd + 104, hd + (if hd =? 0 then 104 else 112))])
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 P) (Z_to_bv 64 fd)
               a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 MODE) (Z_to_bv 64 ssp_guard) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1bb3c) fc None m3 (seg_rom usegs)).
  Section Sz17.
  Variables x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 sv2 j0 junk2 m2 m3 fl P fd hd canary W : ltac2:(SecDiet.SzSec.tyM 'fopen_S7__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvv" @x1).
  Lemma fopen_S7__body : ltac2:(SecDiet.SzSec.bodyP 'fopen_S7__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GLO LO SP47 TPLO md slack. pin_using (fun (GLO LO SP47 TPLO md slack : unit) => tt).
 intros FC BLK2 P0 PST PLO FD FRO FRI SSP THR NL OL OH HD0 HDHI OLDH MU WM SUB ST MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard, A_OFL_LOCK, A_OFL_HEAD, NEED_LOCKS in *. unfold fopen_S7_post, ssp_cells, got_ssp, ssp_guard, A_OFL_LOCK, A_OFL_HEAD.
    unfold flk_cells in FC.
    apply (munch_weaken W _ m2 m3 SUB) in MU. clear SUB.
    assert (HFACTS : hd = 0 \/ (hd <> 0 /\ hd + 232 <= lo /\ (hd + 232 <= P \/ P + 1264 <= hd) /\ (hd + 232 <= 65536 \/ 352256 <= hd))).
    { destruct OLDH as [E | (A0 & _ & A1 & A2 & A3)]; [left; exact E | right; repeat split; assumption]. }
    destruct OLDH as [HZ0 | (HNZ0 & [pvo OLDC] & F1 & F2 & F3)].
    1: replace (hd =? 0) with true in * by (symmetry; apply Z.eqb_eq; exact HZ0).
    2: replace (hd =? 0) with false in * by (symmetry; apply Z.eqb_neq; exact HNZ0).
    all: cbv iota in MU. all: cbv iota.
    all: do 5 zs; do 4 zs.
    all: zs. (* [comment removed for export] *)
    all: do 4 zs. (* [comment removed for export] *)
    all: zs; if_cases KT; zify_cond KT; [exfalso; apply KT; reflexivity|].
    all: zs; zs. (* [comment removed for export] *)
    all: zs; zs. (* [comment removed for export] *)
    all: carve_frame 16%nat ST; rename FR into FRA.
    all: zs; zs; zs; zs; zs.
    all: carve_frame 16%nat ST; rename FR into FRL.
    all: zs; zs; zs; zs; zs; zs.
    all: zs; call_sp lock_spec; [exact NL | mi |].
    all: zs; do 3 zs; release_frame FRL ST (bv_unsigned sp + -112); zs.
    all: zs. (* [comment removed for export] *)
    all: zs. (* [comment removed for export] *)
    all: zs; if_cases KH; zify_cond KH.
    - (* [comment removed for export] *)
      eapply (fopen_S7_tail fl P fd hd 104); try eassumption; try mi;
        fastfirst (first [lia | left; split; [exact HZ0| reflexivity] | intros NZ; exfalso; exact (NZ HZ0)]).
    - exfalso. subst hd. apply KH. reflexivity.
    - exfalso. rewrite ?unsigned_lit, ?Z.mod_small in KH by lia. lia.
    - (* [comment removed for export] *)
      zs.
      eapply (fopen_S7_tail fl P fd hd 112); try eassumption; try mi;
        fastfirst (first [lia | right; split; [exact HNZ0| split; [reflexivity| split; [exact F1| split; [exact F2| exact F3]]]] | intros _; assumption]).
  Qed.
  End Sz17.
  Lemma fopen_S7 : ltac:(let t := eval cbv delta [fopen_S7__stmt] in fopen_S7__stmt in exact t).
  Proof using GLO LO SP47 TPLO md slack. intros x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 sv2 j0 junk2 m2 m3 fl P fd hd canary W. ltac2:(SecDiet.SzSec.closeP 'fopen_S7__body "vvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Lemma fopen_br_r : forall (x1 spv t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (mm : mem),
    evt usegs (fun ms' => ms' = MS (mkR x1 spv gp tp t0 t1 t2 x8 x9 (Z_to_bv 64 (Z.land 8 8)) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                                   F (Z_to_bv 64 0x1bb3c) fc None mm (seg_rom usegs))
      (MS (mkR x1 spv gp tp t0 t1 t2 x8 x9 (Z_to_bv 64 (Z.land 8 8)) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1bb14) fc None mm (seg_rom usegs)).
  Proof using Type. pin_using tt.
    intros. pose proof (munch_refl [] mm) as MU. pose proof (wmono_refl usegs mm) as WM.
    change (Z.land 8 8) with 8. zs. if_true. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma fopen_br_w : forall (x1 t0 t1 t2 x8 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (mm : mem) (fd : Z),
    0 <= fd < 2^31 ->
    evt usegs (fun ms' => ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 x8 (Z_to_bv 64 fd) (Z_to_bv 64 fd) (Z_to_bv 64 21523) (Z_to_bv 64 (bv_unsigned sp + -88)) a3 a4 a5 a6 (Z_to_bv 64 29) x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                                   F (Z_to_bv 64 0x1bb2c) fc None mm (seg_rom usegs))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 x8 (Z_to_bv 64 fd) (Z_to_bv 64 (Z.land 4 8)) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1bb14) fc None mm (seg_rom usegs)).
  Proof using Type. pin_using tt.
    intros until fd. intros FD. pose proof (munch_refl [] mm) as MU. pose proof (wmono_refl usegs mm) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    change (Z.land 4 8) with 0. zs. if_false. zs. zs. zs. zs. zs.
    all: match goal with |- evt _ _ ?ms => idtac "BRW:" ms end.
    apply evt_done. cbv delta [mkR]. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma fopen_ioctl_ret : forall (x1 spv t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (mm : mem) (e : Z),
    1 <= e <= 4095 ->
    evt usegs (fun ms' => ms' = MS (mkR x1 spv gp tp t0 t1 t2 x8 x9 (errno_ret e) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                                   F (Z_to_bv 64 0x1bb3c) fc None mm (seg_rom usegs))
      (MS (mkR x1 spv gp tp t0 t1 t2 x8 x9 (errno_ret e) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1bb30) fc None mm (seg_rom usegs)).
  Proof using MODE md slack. pin_using (fun (MODE md slack : unit) => tt).
    intros until e. intros HE. pose proof (munch_refl [] mm) as MU. pose proof (wmono_refl usegs mm) as WM.
    pose proof (unsigned_errno_ret e HE) as U.
    zs. if_cases K; zify_cond K. 2:{ exfalso. revert K. match goal with |- ?g => idtac "KIO:" g end. rewrite ?U. lia. }
    apply evt_done. reflexivity.
  Qed.
End Fopen.
End TwB.
End F_fopen.
