(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Ceiling Agree.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import InitStack EntrySecret.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim STree Monad Stdio Driver Prog.
From OSSVerify.pupnp.FuzzHttp.images Require Import AsanUbsan.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import AsanAcct.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import DriverSim.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.T7 Require Import RealizeS SeamA0.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation rph := AsanUbsan_phdrs.
Notation mem := (word -> option byte).

Definition RSVA : Z := 0x5d6b90.

Definition djM {St A} (c : Monad.M St A) (s : St) (Q : A -> St -> machine_state -> gst -> Prop) (msr : machine_state) (g : gst) : Prop :=
  implSr (c s) (fun r msr' g' => match r with Ok p => Q (fst p) (snd p) msr' g' | Unr => True end) msr g.

Lemma djM_ret {St A} : forall (x : A) (s : St) Q msr g, Q x s msr g -> djM (mret x) s Q msr g.
Proof. intros. unfold djM, mret. apply dj_ret. cbn. assumption. Qed.

Lemma djM_unr {St A} : forall (s : St) (Q : A -> St -> machine_state -> gst -> Prop) msr g, djM munr s Q msr g.
Proof. intros. unfold djM, munr. apply dj_ret. exact I. Qed.

Lemma djM_bind {St A B} : forall (m : Monad.M St A) (f : A -> Monad.M St B) s Q1 Q msr g,
  djM m s Q1 msr g -> (forall x s' msr' g', Q1 x s' msr' g' -> djM (f x) s' Q msr' g') -> djM (mbind m f) s Q msr g.
Proof.
  intros m f s Q1 Q msr g H HF. unfold djM, mbind, ebind in *. eapply dj_bind; [exact H|].
  intros [|[x s']] msr' g' HQ; cbn in HQ |- *; [apply dj_ret; exact I| exact (HF x s' msr' g' HQ)].
Qed.

Lemma djM_mono {St A} : forall (m : Monad.M St A) s (Q Q' : A -> St -> machine_state -> gst -> Prop) msr g,
  djM m s Q msr g -> (forall x s' msr' g', Q x s' msr' g' -> Q' x s' msr' g') -> djM m s Q' msr g.
Proof.
  intros m s Q Q' msr g H HQ. unfold djM in *. eapply dj_mono; [exact H|]. intros [|[x s']] msr' g'; cbn; auto.
Qed.

Lemma djM_evt {St A} : forall (m : Monad.M St A) s Q (P : machine_state -> Prop) msr g,
  evt asegs P msr -> (forall msr', P msr' -> djM m s Q msr' g) -> djM m s Q msr g.
Proof. intros m s Q P msr g HE HK. unfold djM in *. eapply dj_evt; [exact HE| exact HK]. Qed.

Lemma djM_seam {St A} : forall (m : Monad.M St A) s Q (P : machine_state -> gst -> Prop) msr g,
  SEAMr P msr g -> (forall msr' g', P msr' g' -> djM m s Q msr' g') -> djM m s Q msr g.
Proof. intros m s Q P msr g HS HK. unfold djM in *. eapply dj_seam; [exact HS| exact HK]. Qed.

Lemma djM_msys {St A} : forall (n : node) (pl : resp -> option A) (s : St) (Q : A -> St -> machine_state -> gst -> Prop) msr g,
  fdn n -> at_node asegs n msr ->
  (forall rsp a, GOODA n rsp -> pl rsp = Some a -> Q a s (nret msr rsp) g) ->
  djM (msys n pl) s Q msr g.
Proof.
  intros n pl s Q msr g Hn HAT HK. unfold djM, msys. cbn.
  apply dj_node; [exact Hn | exact HAT |]. intros rsp HG _.
  destruct (pl rsp) as [a|] eqn:E; cbn; apply dj_ret; cbn; [exact (HK rsp a HG E) | exact I].
Qed.

Lemma djM_of_implM {St A} : forall (c : Monad.M St A) (s : St) (Q : A -> St -> machine_state -> Prop) msr g,
  implM asegs c s Q msr -> fdtree (c s) -> djM c s (fun x s' msr' g' => Q x s' msr' /\ g' = g) msr g.
Proof.
  intros c s Q msr g HI HT. unfold djM, implM in *.
  eapply dj_mono; [exact (dj_of_impl _ _ msr g HT HI)|]. intros [|[x s']] msr' g'; cbn; [tauto| intros [HQ ->]; auto].
Qed.

Lemma zbytes_map_unsigned' : forall bs : list byte, map (Z_to_bv 8) (map bv_unsigned bs) = bs.
Proof. intros bs. rewrite map_map. induction bs as [|b bs IH]; cbn; [reflexivity|]. rewrite IH. f_equal. apply (@definitions.Z_to_bv_bv_unsigned 8). Qed.
Lemma map_unsigned_range : forall bs : list byte, Forall (fun c => 0 <= c < 256) (map bv_unsigned bs).
Proof.
  induction bs as [|b bs IH]; cbn; constructor; [| exact IH].
  pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia.
Qed.

Lemma map_unsigned_pos : forall bs : list byte, ~ In (Z_to_bv 8 0) bs -> Forall (fun c => 0 < c < 256) (map bv_unsigned bs).
Proof.
  induction bs as [|b bs IH]; cbn; intros H; constructor.
  - pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R.
    assert (bv_unsigned b <> 0); [| lia]. intros E. apply H. left. apply bv_eq. rewrite Z_to_bv_unsigned. cbn. rewrite E. reflexivity.
  - apply IH. intros X. apply H. right. exact X.
Qed.

Lemma ceil8_le : forall e E, E mod 8 = 0 -> e <= E -> e + (- e) mod 8 <= E.
Proof. intros e E H1 H2. Z.div_mod_to_equations. lia. Qed.

Section Pieces.
  Variables (sp : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw).
  Notation usp := (bv_unsigned sp).
  Notation IMGB := (build_stack_bytes rph sp argv envp uid hw rnd).

  Definition imgk_off (i : Z) : Prop := 8 <= i < 24 \/ struct_size argv envp <= i < Z.of_nat (length IMGB) - 16.
  Definition IMGK (m : mem) : Prop :=
    0 <= usp /\ usp + Z.of_nat (length IMGB) <= 2^64 /\
    forall i : nat, imgk_off (Z.of_nat i) -> mrd asegs m (wa (usp + Z.of_nat i)) = nth_error IMGB i.

  #[using="Type"] Lemma IMGK_of_bytes_at : forall m, bytes_at asegs m usp IMGB -> IMGK m.
  Proof.
    intros m (H0 & H1 & HB). split; [exact H0|]. split; [exact H1|]. intros i Hi. apply HB.
    pose proof (build_stack_bytes_length rph sp argv envp uid hw rnd) as BL.
    pose proof (raw_len_nonneg rph sp argv envp uid hw rnd) as RN.
    unfold imgk_off in Hi. unfold raw_len, struct_size in *.
    assert (0 <= pad_len argv envp) by (unfold pad_len; apply Z.mod_pos_bound; lia).
    pose proof (total_arg_bytes_nonneg argv). pose proof (total_arg_bytes_nonneg envp).
    unfold argc, envc in *. lia.
  Qed.

  #[using="Type"] Lemma IMGK_agree : forall (P : Z -> Prop) m m', gagree_on P m m' -> IMGK m ->
    (forall a, usp <= a < usp + Z.of_nat (length IMGB) -> P a) -> IMGK m'.
  Proof.
    intros P m m' AG (H0 & H1 & HB) HP. split; [exact H0|]. split; [exact H1|]. intros i Hi.
    pose proof (HB i Hi) as HBi.
    assert (R : usp <= usp + Z.of_nat i < usp + Z.of_nat (length IMGB)).
    { unfold imgk_off in Hi. pose proof (build_stack_bytes_length rph sp argv envp uid hw rnd) as BL.
      assert (0 <= pad_len argv envp) by (unfold pad_len; apply Z.mod_pos_bound; lia).
      pose proof (total_arg_bytes_nonneg argv). pose proof (total_arg_bytes_nonneg envp).
      unfold raw_len, struct_size, argc, envc in *. lia. }

    destruct (nth_error IMGB i) as [b|] eqn:EN.
    - exact (gkeep_mrd _ _ _ b (proj1 (AG (usp + Z.of_nat i) ltac:(lia) (HP _ R))) HBi).
    - exfalso. apply nth_error_None in EN. lia.
  Qed.
  Definition mcan : mem := fun a =>
    if (usp <=? bv_unsigned a) && (bv_unsigned a <? usp + Z.of_nat (length IMGB))
    then nth_error IMGB (Z.to_nat (bv_unsigned a - usp)) else None.
  #[using="Type"] Lemma mcan_img : usp + Z.of_nat (length IMGB) <= 2^64 -> bytes_at asegs mcan usp IMGB.
  Proof.
    intros H. pose proof (bv_unsigned_in_range 64 sp) as R. unfold bv_modulus in R. split; [lia|]. split; [exact H|].
    intros i Hi. unfold mrd, mcan. rewrite wa_unsigned by lia.
    replace ((usp <=? usp + Z.of_nat i) && (usp + Z.of_nat i <? usp + Z.of_nat (length IMGB)))%bool with true
      by (symmetry; apply andb_true_intro; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
    replace (Z.to_nat (usp + Z.of_nat i - usp)) with i by lia.
    destruct (nth_error IMGB i) as [b|] eqn:E; [reflexivity|]. apply nth_error_None in E. lia.
  Qed.
  #[using="Type"] Lemma IMGK_transfer : forall m A bs, IMGK m -> bytes_at asegs mcan A bs ->
    (forall a, A <= a < A + Z.of_nat (length bs) -> imgk_off (a - usp)) -> bytes_at asegs m A bs.
  Proof.
    intros m A bs (H0 & H1 & HB) (B0 & B1 & BB) HR. split; [exact B0|]. split; [exact B1|].
    intros i Hi. rewrite <- (BB i Hi).
    pose proof (HR (A + Z.of_nat i) ltac:(lia)) as K.
    assert (KR : usp <= A + Z.of_nat i < usp + Z.of_nat (length IMGB)).
    { unfold imgk_off in K. pose proof (build_stack_bytes_length rph sp argv envp uid hw rnd) as BL.
      assert (0 <= pad_len argv envp) by (unfold pad_len; apply Z.mod_pos_bound; lia).
      pose proof (total_arg_bytes_nonneg argv). pose proof (total_arg_bytes_nonneg envp).
      unfold raw_len, struct_size, argc, envc in *. lia. }
    pose proof (HB (Z.to_nat (A + Z.of_nat i - usp)) ltac:(rewrite Z2Nat.id by lia; exact K)) as E.
    rewrite Z2Nat.id in E by lia. replace (usp + (A + Z.of_nat i - usp)) with (A + Z.of_nat i) in E by lia.
    rewrite E. pose proof (mcan_img H1) as (_ & _ & MB).
    pose proof (MB (Z.to_nat (A + Z.of_nat i - usp)) ltac:(lia)) as E2.
    rewrite Z2Nat.id in E2 by lia. replace (usp + (A + Z.of_nat i - usp)) with (A + Z.of_nat i) in E2 by lia.
    symmetry. exact E2.
  Qed.
  Section Full.
  Variable m : mem.
  Hypothesis IMG : bytes_at asegs m usp (build_stack_bytes rph sp argv envp uid hw rnd).

  #[using="IMG"] Lemma stack_pieces_full :
    bytes_at asegs m usp (le8 (Z_to_bv 64 (argc argv))) /\
    bytes_at asegs m (usp + 8) (u64s (argv_ptrs sp argv envp ++ [Z_to_bv 64 0])) /\
    bytes_at asegs m (usp + 8 * (argc argv + 2)) (u64s (envp_ptrs sp argv envp ++ [Z_to_bv 64 0])) /\
    bytes_at asegs m (usp + 8 * (argc argv + envc envp + 3)) (u64s (auxv_words rph sp argv envp uid hw)) /\
    bytes_at asegs m (str_base sp argv envp) (flatten_strings argv) /\
    bytes_at asegs m (env_base sp argv envp) (flatten_strings envp) /\
    bytes_at asegs m (rnd_addr sp argv envp) (at_random_bytes (ed_random rnd)).
  Proof.
    pose proof IMG as B. rewrite build_stack_bytes_eq in B.
    unfold raw_bytes in B. remember (auxv_words rph sp argv envp uid hw) as AW eqn:EAW. cbn [u64s app] in B.
    rewrite u64s_app in B. cbn [u64s app] in B. rewrite u64s_app in B. cbn [u64s app] in B.
    repeat rewrite <- app_assoc in B. cbn [app] in B.
    pose proof (raw_len_nonneg rph sp argv envp uid hw rnd) as RN.
    pose proof (flatten_strings_length argv) as L1. pose proof (flatten_strings_length envp) as L2.
    apply bytes_at_app in B. destruct B as [B0 B]. rewrite length_le8 in B.
    apply bytes_at_app in B. destruct B as [B1 B]. rewrite u64s_length in B. unfold argv_ptrs in B. rewrite map_length, str_ptrs_length in B.
    apply bytes_at_app in B. destruct B as [B2 B]. rewrite length_le8 in B.
    apply bytes_at_app in B. destruct B as [B3 B]. rewrite u64s_length in B. unfold envp_ptrs in B. rewrite map_length, str_ptrs_length in B.
    apply bytes_at_app in B. destruct B as [B4 B]. rewrite length_le8 in B.
    apply bytes_at_app in B. destruct B as [B5 B]. rewrite u64s_length in B. replace (length AW) with 20%nat in B by (subst AW; reflexivity).
    apply bytes_at_app in B. destruct B as [B6 B].
    apply bytes_at_app in B. destruct B as [B7 B].
    apply bytes_at_app in B. destruct B as [B8 B]. rewrite repeat_length in B.
    repeat match goal with |- _ /\ _ => split end.
    - exact B0.
    - rewrite u64s_app. cbn [u64s]. rewrite app_nil_r. apply (proj2 (bytes_at_app asegs m _ _ _)). split; [exact B1|].
      rewrite u64s_length. unfold argv_ptrs at 1. rewrite map_length, str_ptrs_length.
      replace (usp + 8 + Z.of_nat (8 * length argv))%Z with (usp + Z.of_nat 8 + Z.of_nat (8 * length argv))%Z by lia. exact B2.
    - rewrite u64s_app. cbn [u64s]. rewrite app_nil_r. apply (proj2 (bytes_at_app asegs m _ _ _)). split.
      + replace (usp + 8 * (argc argv + 2))%Z with (usp + Z.of_nat 8 + Z.of_nat (8 * length argv) + Z.of_nat 8)%Z by (unfold argc; lia). exact B3.
      + rewrite u64s_length. unfold envp_ptrs at 1. rewrite map_length, str_ptrs_length.
        replace (usp + 8 * (argc argv + 2) + Z.of_nat (8 * length envp))%Z
          with (usp + Z.of_nat 8 + Z.of_nat (8 * length argv) + Z.of_nat 8 + Z.of_nat (8 * length envp))%Z by (unfold argc; lia). exact B4.
    - replace (usp + 8 * (argc argv + envc envp + 3))%Z
        with (usp + Z.of_nat 8 + Z.of_nat (8 * length argv) + Z.of_nat 8 + Z.of_nat (8 * length envp) + Z.of_nat 8)%Z by (unfold argc, envc; lia). exact B5.
    - replace (str_base sp argv envp) with (usp + Z.of_nat 8 + Z.of_nat (8 * length argv) + Z.of_nat 8 + Z.of_nat (8 * length envp) + Z.of_nat 8 + Z.of_nat (8 * 20))%Z
        by (unfold str_base, struct_size, argc, envc; lia). exact B6.
    - replace (env_base sp argv envp) with (usp + Z.of_nat 8 + Z.of_nat (8 * length argv) + Z.of_nat 8 + Z.of_nat (8 * length envp) + Z.of_nat 8 + Z.of_nat (8 * 20) + Z.of_nat (length (flatten_strings argv)))%Z
        by (unfold env_base, str_base, struct_size, argc, envc; lia). exact B7.
    - replace (rnd_addr sp argv envp) with (usp + Z.of_nat 8 + Z.of_nat (8 * length argv) + Z.of_nat 8 + Z.of_nat (8 * length envp) + Z.of_nat 8 + Z.of_nat (8 * 20)
                             + Z.of_nat (length (flatten_strings argv)) + Z.of_nat (length (flatten_strings envp)) + Z.of_nat (Z.to_nat (pad_len argv envp)))%Z
        by (unfold rnd_addr, raw_len, struct_size, argc, envc; lia). exact B.
  Qed.

  #[using="IMG"] Lemma argv_cstring_full : forall i s, nth_error argv i = Some s -> usp mod 8 = 0 ->
    exists p slack, nth_error (argv_ptrs sp argv envp) i = Some (Z_to_bv 64 p) /\ str_base sp argv envp <= p /\
      p + Z.of_nat (length s) + 1 + Z.of_nat (length slack) <= usp + Z.of_nat (length (build_stack_bytes rph sp argv envp uid hw rnd)) - 16 /\
      bytes_at asegs m p (s ++ Z_to_bv 8 0 :: slack) /\
      (- (p + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack).
  Proof.
    intros i s Hn AL. destruct (str_ptrs_nth argv (str_base sp argv envp) i s Hn) as (off & Hp & Ho & Ht & Hf).
    pose proof (raw_len_nonneg rph sp argv envp uid hw rnd) as RN. pose proof (build_stack_bytes_length rph sp argv envp uid hw rnd) as BL.
    pose proof (flatten_strings_length argv) as L1. pose proof (flatten_strings_length envp) as L2.
    set (p := str_base sp argv envp + off).
    set (e := p + Z.of_nat (length s) + 1).
    set (k := (- e) mod 8).
    assert (HK : 0 <= k < 8) by (subst k; apply Z.mod_pos_bound; lia).
    assert (OFF : usp <= p /\ e + k <= usp + Z.of_nat (length (build_stack_bytes rph sp argv envp uid hw rnd)) - 16).
    { subst p e k. unfold str_base, struct_size, raw_len in *. split; [lia|].
      rewrite BL. replace (usp + (8 * (argc argv + envc envp) + 184 + total_arg_bytes argv + total_arg_bytes envp + pad_len argv envp + 16) - 16)
        with (usp + (8 * (argc argv + envc envp) + 184 + total_arg_bytes argv + total_arg_bytes envp + pad_len argv envp)) by lia.
      apply ceil8_le.
      - unfold pad_len, raw_len, struct_size. Z.div_mod_to_equations. lia.
      - assert (0 <= pad_len argv envp) by (unfold pad_len; apply Z.mod_pos_bound; lia).
        pose proof (total_arg_bytes_nonneg envp). unfold struct_size. lia. }
    exists p, (firstn (Z.to_nat k) (skipn (Z.to_nat (e - usp)) (build_stack_bytes rph sp argv envp uid hw rnd))).
    split; [unfold argv_ptrs; rewrite nth_error_map, Hp; reflexivity|]. split; [subst p; lia|].
    assert (LS : length (firstn (Z.to_nat k) (skipn (Z.to_nat (e - usp)) (build_stack_bytes rph sp argv envp uid hw rnd))) = Z.to_nat k).
    { rewrite length_firstn, length_skipn. lia. }
    rewrite LS. split; [subst e k; lia|]. split; [| subst e k; lia].
    destruct stack_pieces_full as (_ & _ & _ & _ & B6 & _).
    pose proof (bytes_at_slice asegs rph sp argv envp uid hw rnd m (str_base sp argv envp) (flatten_strings argv) (Z.to_nat off) (length s + 1) B6 ltac:(lia)) as BS.
    rewrite Hf in BS. replace (str_base sp argv envp + Z.of_nat (Z.to_nat off)) with p in BS by (subst p; lia).
    pose proof (bytes_at_slice asegs rph sp argv envp uid hw rnd m usp (build_stack_bytes rph sp argv envp uid hw rnd) (Z.to_nat (e - usp)) (Z.to_nat k) IMG ltac:(lia)) as BK.
    replace (usp + Z.of_nat (Z.to_nat (e - usp))) with (p + Z.of_nat (length (s ++ [Z_to_bv 8 0]))) in BK by (rewrite length_app; cbn [length]; subst e; lia).
    pose proof (proj2 (bytes_at_app asegs m p _ _) (conj BS BK)) as BB. rewrite <- app_assoc in BB. cbn [app] in BB. exact BB.
  Qed.
  End Full.
  #[using="Type"] Lemma u64s_firstn2 : forall (l : list word), firstn 16 (u64s l) = u64s (firstn 2 l).
  Proof.
    intros [|a [|b l]]; [reflexivity| |].
    - cbn [u64s firstn]. rewrite app_nil_r. apply firstn_all2. rewrite length_le8. lia.
    - cbn [u64s firstn]. rewrite app_nil_r, app_assoc.
      rewrite firstn_app. rewrite firstn_all2 by (rewrite app_length, !length_le8; lia).
      rewrite app_length, !length_le8. cbn [Nat.sub Nat.add firstn]. rewrite app_nil_r. reflexivity.
  Qed.
  #[using="Type"] Lemma nth_error_firstn2 : forall {A} (l : list A) i x, (i < 2)%nat -> nth_error l i = Some x -> nth_error (firstn 2 l) i = Some x.
  Proof. intros A [|a [|b l]] [|[|i]] x Hi H; cbn in *; try discriminate; try lia; exact H. Qed.

  #[using="Type"] Lemma stack_argv2 : forall m, IMGK m -> (1 <= length argv)%nat ->
    bytes_at asegs m (usp + 8) (u64s (firstn 2 (argv_ptrs sp argv envp ++ [Z_to_bv 64 0]))).
  Proof.
    intros m K NE. pose proof K as (H0 & H1 & _).
    destruct (stack_pieces_full mcan (mcan_img H1)) as (_ & B & _).
    pose proof (bytes_at_slice asegs rph sp argv envp uid hw rnd mcan (usp + 8) _ 0 16 B) as S.
    rewrite u64s_length, length_app in S. unfold argv_ptrs in S. rewrite map_length, str_ptrs_length in S.
    cbn [length] in S. specialize (S ltac:(lia)).
    rewrite skipn_O in S. fold (argv_ptrs sp argv envp) in S. rewrite u64s_firstn2 in S. rewrite Z.add_0_r in S.
    apply (IMGK_transfer m _ _ K S). intros a Ha. left.
    rewrite u64s_length in Ha.
    assert (length (firstn 2 (argv_ptrs sp argv envp ++ [Z_to_bv 64 0])) <= 2)%nat by apply firstn_le_length.
    lia.
  Qed.

  #[using="Type"] Lemma argv_cstring : forall m, IMGK m -> forall i s, nth_error argv i = Some s -> usp mod 8 = 0 ->
    exists p slack, nth_error (argv_ptrs sp argv envp) i = Some (Z_to_bv 64 p) /\ str_base sp argv envp <= p /\
      p + Z.of_nat (length s) + 1 + Z.of_nat (length slack) <= usp + Z.of_nat (length (build_stack_bytes rph sp argv envp uid hw rnd)) - 16 /\
      bytes_at asegs m p (s ++ Z_to_bv 8 0 :: slack) /\
      (- (p + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack).
  Proof.
    intros m K i s Hn AL. pose proof K as (H0 & H1 & _).
    destruct (argv_cstring_full mcan (mcan_img H1) i s Hn AL) as (p & slack & E1 & E2 & E3 & E4 & E5).
    exists p, slack. split; [exact E1|]. split; [exact E2|]. split; [lia|]. split; [| exact E5].
    apply (IMGK_transfer m _ _ K E4). intros a Ha. right.
    rewrite app_length in Ha. cbn [length] in Ha. unfold str_base in E2. lia.
  Qed.
End Pieces.
