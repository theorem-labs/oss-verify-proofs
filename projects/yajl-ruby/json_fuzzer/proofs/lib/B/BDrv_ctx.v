(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Image ZBridge ITree Nodes NodesCfg Decode Arr FP InitMem Frame Mem Cells.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA AImages AImageFacts ExecA LazyModel NodesA ImplRzA CompatE2.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim StdioBase Stdio Driver.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top Require Import TrzStdio.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import B_iface.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BX_atexit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation aph := b_phdrs.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition dfds_std : list (word * FdEntry) :=
  [(Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1)); (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2))].

Lemma dfds_alloc : alloc_fd dfds_std = Z_to_bv 64 3. Proof. reflexivity. Qed.
Lemma dfds_free : fd_lookup dfds_std (alloc_fd dfds_std) = None. Proof. reflexivity. Qed.
Lemma dfds_range : (3 <= bv_unsigned (alloc_fd dfds_std) <= 4096)%Z. Proof. rewrite dfds_alloc. change (bv_unsigned (Z_to_bv 64 3)) with 3%Z. lia. Qed.

Definition agree_on (P : Z -> Prop) (m m' : mem) : Prop :=
  forall a, 0 <= a < 2^64 -> P a ->
    m' (wa a) = m (wa a) /\ (wview bsegs m (wa a) <> None -> wview bsegs m' (wa a) <> None).

Lemma agree_on_refl : forall P m, agree_on P m m.
Proof. aceil. intros P m a _ _. auto. Qed.
Lemma agree_on_trans : forall P m1 m2 m3, agree_on P m1 m2 -> agree_on P m2 m3 -> agree_on P m1 m3.
Proof. aceil. intros P m1 m2 m3 H1 H2 a Ha HP. destruct (H1 a Ha HP) as [E1 W1]. destruct (H2 a Ha HP) as [E2 W2]. split; [congruence|auto]. Qed.
Lemma agree_on_mono : forall (P P' : Z -> Prop) m m', agree_on P m m' -> (forall a, P' a -> P a) -> agree_on P' m m'.
Proof. aceil. intros P P' m m' H HP a Ha Hp. apply H; auto. Qed.

Lemma bytes_at_agree : forall P m m' A bs,
  agree_on P m m' -> bytes_at bsegs m A bs -> (forall a, A <= a < A + Z.of_nat (length bs) -> P a) ->
  bytes_at bsegs m' A bs.
Proof. aceil.
  intros P m m' A bs HP (H0 & H1 & HB) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (HB i Hi). unfold mrd.
  destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(apply HR; lia)) as [E _]. rewrite E. reflexivity.
Qed.

Lemma wr_at_agree : forall P m m' A n,
  agree_on P m m' -> wr_at bsegs m A n -> (forall a, A <= a < A + n -> P a) -> wr_at bsegs m' A n.
Proof. aceil.
  intros P m m' A n HP (H0 & H1 & HW) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(apply HR; lia)) as [_ W]. apply W. apply HW. exact Hi.
Qed.

Lemma rw_cells_agree : forall P m m' A cs,
  agree_on P m m' -> rw_cells bsegs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> P a) ->
  rw_cells bsegs m' A cs.
Proof. aceil.
  intros P m m' A cs HP [[Hwf HB] HW] HR. split; [split; [exact Hwf|]|].
  - eapply bytes_at_agree; eauto. rewrite cells_bytes_length by assumption. exact HR.
  - eapply wr_at_agree; eauto.
Qed.

Lemma stk_agree : forall P m m' lo hi,
  agree_on P m m' -> stk bsegs m lo hi -> (forall a, lo <= a < hi -> P a) -> stk bsegs m' lo hi.
Proof. aceil.
  intros P m m' lo hi HP (H0 & H1 & HS) HR. split; [exact H0|]. split; [exact H1|].
  intros a Ha. destruct (HS a Ha) as [W [b Hb]]. destruct (HP a ltac:(lia) (HR a Ha)) as [E W'].
  split; [apply W'; exact W|]. exists b. unfold mrd in *. rewrite E. exact Hb.
Qed.

(* [comment removed for export] *)
Lemma adi_uanchorC : forall segs C FM D, a_drv_iface segs C FM D -> forall m SP ra s0,
  In (bv_unsigned ra) (c_uras C) -> bv_unsigned s0 < alloc_ceiling -> p_uanchor D m SP ra s0.
Proof. aceil. intros segs C FM D DI m SP ra s0 Hin Hs0. apply (adi_uanchor _ _ _ _ DI); [exact Hs0| apply (adi_uras _ _ _ _ DI); exact Hin]. Qed.
End RC__1.
Ltac in_lits := rewrite ?unsigned_lit by (cbv; lia); cbn; repeat first [left; reflexivity | right].

(* [comment removed for export] *)
Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma nbig_le : forall LB, nbig LB <= Z.of_nat (length LB).
Proof. aceil.
  unfold nbig. induction LB as [|b LB IH]; [cbn; lia|]. cbn [List.filter length].
  destruct (64512 <? ab_size b); cbn [length]; rewrite ?Nat2Z.inj_succ; lia.
Qed.
Lemma nbig_small : forall LB, Z.of_nat (length LB) <= 8000 -> nbig LB <= 8000.
Proof. aceil. intros LB H. pose proof (nbig_le LB). lia. Qed.

(* [comment removed for export] *)
Lemma wr_at_heap_cells : forall m a n, wr_at bsegs m a n -> 0x603000 <= a -> 0 <= n ->
  exists junk, rw_cells bsegs m a [CB (Z.to_nat n) junk].
Proof. aceil.
  intros m a n (H0 & H1 & HW) Ha Hn.
  assert (SK : stk bsegs m a (a + n)).
  { split; [lia|]. split; [lia|]. intros x Hx. specialize (HW (x - a) ltac:(lia)). replace (a + (x - a)) with x in HW by lia.
    split; [exact HW|]. rewrite both_wview_overlay in HW by (rewrite wa_unsigned by lia; lia).
    unfold mrd. destruct (m (wa x)) as [b|]; [exists b; reflexivity| congruence]. }
  destruct (stk_carve bsegs m a (a + n) (Z.to_nat n) SK ltac:(lia)) as [_ [junk J]]. exists junk.
  replace (a + n - Z.of_nat (Z.to_nat n)) with a in J by lia. exact J.
Qed.

(* [comment removed for export] *)
Lemma aheap_pres_agree : forall C LB LF SP m m', aheap_pres bsegs C LB LF SP m m' -> agree_on (aclient_addr C LB LF SP) m m'.
Proof. aceil. intros C LB LF SP m m' H a Ha Hc. exact (H a Ha Hc). Qed.

Lemma agree_on_of_munch : forall W m m', munch W m m' -> wmono bsegs m m' -> agree_on (fun a => outside W a) m m'.
Proof. aceil.
  intros W m m' MU WM a Ha Ho. split; [| apply WM]. apply MU. rewrite wa_unsigned by exact Ha. exact Ho.
Qed.

Lemma zbytes_map_unsigned' : forall bs : list byte, map (Z_to_bv 8) (map bv_unsigned bs) = bs.
Proof. aceil. intros bs. rewrite map_map. induction bs as [|b bs IH]; cbn; [reflexivity|]. rewrite IH. f_equal. apply (@definitions.Z_to_bv_bv_unsigned 8). Qed.

Lemma map_unsigned_range : forall bs : list byte, Forall (fun c => 0 <= c < 256) (map bv_unsigned bs).
Proof. aceil.
  induction bs as [|b bs IH]; cbn; constructor; [| exact IH].
  pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia.
Qed.

Lemma map_unsigned_pos : forall bs : list byte, ~ In (Z_to_bv 8 0) bs -> Forall (fun c => 0 < c < 256) (map bv_unsigned bs).
Proof. aceil.
  induction bs as [|b bs IH]; cbn; intros H; constructor.
  - pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R.
    assert (bv_unsigned b <> 0); [| lia]. intros E. apply H. left. apply bv_eq. rewrite Z_to_bv_unsigned. cbn. rewrite E. reflexivity.
  - apply IH. intros X. apply H. right. exact X.
Qed.

Lemma zb_map_unsigned : forall bs : list byte, zb (map bv_unsigned bs) = bs.
Proof. aceil. intros bs. unfold zb. induction bs as [|b bs IH]; cbn; [reflexivity|]. rewrite IH. f_equal. apply (@definitions.Z_to_bv_bv_unsigned 8). Qed.

Lemma ceil8_le : forall e E, E mod 8 = 0 -> e <= E -> e + (- e) mod 8 <= E.
Proof. aceil. intros e E H1 H2. Z.div_mod_to_equations. lia. Qed.

Lemma byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. aceil. intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia. Qed.

(* [comment removed for export] *)
Lemma rodata_bytes : forall m A (s : list Z),
  mem_inv bsegs m -> ro_bytes_b bsegs A (zb s) = true -> 0x10000 <= A -> A + zlength s <= 0x23990 ->
  bytes_at bsegs m A (zb s).
Proof. aceil.
  intros m A s MI RO LO HI. apply ro_bytes_at; [exact MI| lia| unfold zb; rewrite length_map; unfold zlength in HI; lia| apply (ro_bytes_b_sound bsegs); exact RO].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Pieces.
  Variables (sp : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw) (m : mem).
  Notation usp := (bv_unsigned sp).
  Hypothesis IMG : bytes_at bsegs m usp (build_stack_bytes aph sp argv envp uid hw rnd).

  Lemma stack_pieces :
    bytes_at bsegs m usp (le8 (Z_to_bv 64 (argc argv))) /\
    bytes_at bsegs m (usp + 8) (u64s (argv_ptrs sp argv envp ++ [Z_to_bv 64 0])) /\
    bytes_at bsegs m (usp + 8 * (argc argv + 2)) (u64s (envp_ptrs sp argv envp ++ [Z_to_bv 64 0])) /\
    bytes_at bsegs m (usp + 8 * (argc argv + envc envp + 3)) (u64s (auxv_words aph sp argv envp uid hw)) /\
    bytes_at bsegs m (str_base sp argv envp) (flatten_strings argv) /\
    bytes_at bsegs m (env_base sp argv envp) (flatten_strings envp) /\
    bytes_at bsegs m (rnd_addr sp argv envp) (at_random_bytes (ed_random rnd)).
  Proof. aceil.
    pose proof IMG as B. rewrite build_stack_bytes_eq in B.
    unfold raw_bytes in B. remember (auxv_words aph sp argv envp uid hw) as AW eqn:EAW. cbn [u64s app] in B.
    rewrite u64s_app in B. cbn [u64s app] in B. rewrite u64s_app in B. cbn [u64s app] in B.
    repeat rewrite <- app_assoc in B. cbn [app] in B.
    pose proof (raw_len_nonneg aph sp argv envp uid hw rnd) as RN.
    pose proof (flatten_strings_length argv) as L1. pose proof (flatten_strings_length envp) as L2.
    apply bytes_at_app in B. destruct B as [B0 B]. rewrite length_le8 in B.
    apply bytes_at_app in B. destruct B as [B1 B]. rewrite u64s_length in B. unfold argv_ptrs in B. rewrite length_map, str_ptrs_length in B.
    apply bytes_at_app in B. destruct B as [B2 B]. rewrite length_le8 in B.
    apply bytes_at_app in B. destruct B as [B3 B]. rewrite u64s_length in B. unfold envp_ptrs in B. rewrite length_map, str_ptrs_length in B.
    apply bytes_at_app in B. destruct B as [B4 B]. rewrite length_le8 in B.
    apply bytes_at_app in B. destruct B as [B5 B]. rewrite u64s_length in B. replace (length AW) with 20%nat in B by (subst AW; reflexivity).
    apply bytes_at_app in B. destruct B as [B6 B].
    apply bytes_at_app in B. destruct B as [B7 B].
    apply bytes_at_app in B. destruct B as [B8 B]. rewrite repeat_length in B.
    repeat match goal with |- _ /\ _ => split end.
    - exact B0.
    - rewrite u64s_app. cbn [u64s]. rewrite app_nil_r. apply (proj2 (bytes_at_app bsegs m _ _ _)). split; [exact B1|].
      rewrite u64s_length. unfold argv_ptrs at 1. rewrite length_map, str_ptrs_length.
      replace (usp + 8 + Z.of_nat (8 * length argv))%Z with (usp + Z.of_nat 8 + Z.of_nat (8 * length argv))%Z by lia. exact B2.
    - rewrite u64s_app. cbn [u64s]. rewrite app_nil_r. apply (proj2 (bytes_at_app bsegs m _ _ _)). split.
      + replace (usp + 8 * (argc argv + 2))%Z with (usp + Z.of_nat 8 + Z.of_nat (8 * length argv) + Z.of_nat 8)%Z by (unfold argc; lia). exact B3.
      + rewrite u64s_length. unfold envp_ptrs at 1. rewrite length_map, str_ptrs_length.
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

  (* [comment removed for export] *)
  Lemma argv_cstring : forall i s, nth_error argv i = Some s -> usp mod 8 = 0 ->
    exists p slack, nth_error (argv_ptrs sp argv envp) i = Some (Z_to_bv 64 p) /\ str_base sp argv envp <= p /\
      p + Z.of_nat (length s) + 1 + Z.of_nat (length slack) <= usp + Z.of_nat (length (build_stack_bytes aph sp argv envp uid hw rnd)) /\
      bytes_at bsegs m p (s ++ Z_to_bv 8 0 :: slack) /\
      (- (p + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack) /\
      p + Z.of_nat (length s) + 1 + 16 <= usp + Z.of_nat (length (build_stack_bytes aph sp argv envp uid hw rnd)).   (* [comment removed for export] *)
  Proof. aceil.
    intros i s Hn AL. destruct (str_ptrs_nth argv (str_base sp argv envp) i s Hn) as (off & Hp & Ho & Ht & Hf).
    pose proof (raw_len_nonneg aph sp argv envp uid hw rnd) as RN. pose proof (build_stack_bytes_length aph sp argv envp uid hw rnd) as BL.
    pose proof (flatten_strings_length argv) as L1. pose proof (flatten_strings_length envp) as L2.
    set (p := str_base sp argv envp + off).
    set (e := p + Z.of_nat (length s) + 1).
    set (k := (- e) mod 8).
    assert (HK : 0 <= k < 8) by (subst k; apply Z.mod_pos_bound; lia).
    assert (OFF : usp <= p /\ e + k <= usp + Z.of_nat (length (build_stack_bytes aph sp argv envp uid hw rnd))).
    { subst p e k. unfold str_base, struct_size, raw_len in *. split; [lia|].
      rewrite BL. apply ceil8_le.
      - unfold pad_len, raw_len, struct_size. Z.div_mod_to_equations. lia.
      - unfold raw_len, struct_size. lia. }
    exists p, (firstn (Z.to_nat k) (skipn (Z.to_nat (e - usp)) (build_stack_bytes aph sp argv envp uid hw rnd))).
    split; [unfold argv_ptrs; rewrite nth_error_map, Hp; reflexivity|]. split; [subst p; lia|].
    assert (LS : length (firstn (Z.to_nat k) (skipn (Z.to_nat (e - usp)) (build_stack_bytes aph sp argv envp uid hw rnd))) = Z.to_nat k).
    { rewrite length_firstn, length_skipn. lia. }
    rewrite LS. split; [lia|]. split; [| split; [lia | subst p e; rewrite BL; unfold raw_len, str_base in *; lia]].
    destruct stack_pieces as (_ & _ & _ & _ & B6 & _).
    pose proof (bytes_at_slice bsegs aph sp argv envp uid hw rnd m (str_base sp argv envp) (flatten_strings argv) (Z.to_nat off) (length s + 1) B6 ltac:(lia)) as BS.
    rewrite Hf in BS. replace (str_base sp argv envp + Z.of_nat (Z.to_nat off)) with p in BS by (subst p; lia).
    pose proof (bytes_at_slice bsegs aph sp argv envp uid hw rnd m usp (build_stack_bytes aph sp argv envp uid hw rnd) (Z.to_nat (e - usp)) (Z.to_nat k) IMG ltac:(lia)) as BK.
    replace (usp + Z.of_nat (Z.to_nat (e - usp))) with (p + Z.of_nat (length (s ++ [Z_to_bv 8 0]))) in BK by (rewrite length_app; cbn [length]; subst e; lia).
    pose proof (proj2 (bytes_at_app bsegs m p _ _) (conj BS BK)) as BB. rewrite <- app_assoc in BB. cbn [app] in BB. exact BB.
  Qed.
End Pieces.

(* [comment removed for export] *)
Section AImg.
  Variables (sp : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw).
  Notation usp := (bv_unsigned sp).
  Definition AIMG (m : mem) : Prop :=
    bytes_at bsegs m (usp + 8) (u64s (firstn 2 (argv_ptrs sp argv envp)))
    /\ forall i s, (i < 2)%nat -> nth_error argv i = Some s ->
         exists p slack, nth_error (argv_ptrs sp argv envp) i = Some (Z_to_bv 64 p) /\ str_base sp argv envp <= p /\
           p + Z.of_nat (length s) + 1 + Z.of_nat (length slack) <= usp + Z.of_nat (length (build_stack_bytes aph sp argv envp uid hw rnd)) /\
           bytes_at bsegs m p (s ++ Z_to_bv 8 0 :: slack) /\
           (- (p + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack) /\
           p + Z.of_nat (length s) + 1 + 16 <= 0x800000000000.   (* [comment removed for export] *)

  Lemma AIMG_of_image : forall m, usp mod 8 = 0 -> usp + Z.of_nat (length (build_stack_bytes aph sp argv envp uid hw rnd)) <= 0x800000000000 ->
    bytes_at bsegs m usp (build_stack_bytes aph sp argv envp uid hw rnd) -> AIMG m.
  Proof. aceil.
    intros m AL TOP IMG. split.
    - destruct (stack_pieces sp argv envp uid hw rnd m IMG) as (_ & ARGVP & _).
      rewrite <- (firstn_skipn 2 (argv_ptrs sp argv envp)) in ARGVP. rewrite <- app_assoc, u64s_app in ARGVP.
      apply bytes_at_app in ARGVP. destruct ARGVP as [X _]. exact X.
    - intros i s0 Hi Hn. destruct (argv_cstring sp argv envp uid hw rnd m IMG i s0 Hn AL) as (p & slack & H1 & H2 & H3 & H4 & H5 & H6). exists p, slack.
      split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5| lia].
  Qed.

  Lemma AIMG_agree : forall (P : Z -> Prop) m m', agree_on P m m' ->
    (forall a, usp <= a < usp + Z.of_nat (length (build_stack_bytes aph sp argv envp uid hw rnd)) -> P a) -> AIMG m -> AIMG m'.
  Proof. aceil.
    intros P m m' AG HP [AP CS].
    pose proof (build_stack_bytes_length aph sp argv envp uid hw rnd) as BL. pose proof (raw_len_nonneg aph sp argv envp uid hw rnd) as RN.
    pose proof (flatten_strings_length argv) as L1. pose proof (flatten_strings_length envp) as L2.
    split.
    - eapply bytes_at_agree; [exact AG| exact AP|]. intros a Ha. apply HP.
      rewrite u64s_length, length_firstn in Ha. unfold raw_len, struct_size, argc, envc in *. lia.
    - intros i s0 Hi Hn. destruct (CS i s0 Hi Hn) as (p & slack & H1 & H2 & H3 & H4 & H5 & H6). exists p, slack.
      repeat (split; [assumption|]). split; [| exact (conj H5 H6)].
      eapply bytes_at_agree; [exact AG| exact H4|]. intros a Ha. apply HP. rewrite length_app in Ha. cbn [length] in Ha.
      unfold str_base, struct_size, argc, envc in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma AIMG_ptr_read : forall m i w a, AIMG m -> nth_error (argv_ptrs sp argv envp) i = Some w -> (i < 2)%nat ->
    a = wa (usp + 8 + 8 * Z.of_nat i) -> ov_read_bytes bsegs m a 8 = Some (le8 w).
  Proof. aceil.
    intros m i w a [AP _] Hn Hi ->.
    assert (Hn' : nth_error (firstn 2 (argv_ptrs sp argv envp)) i = Some w).
    { assert (HL : (i < length (argv_ptrs sp argv envp))%nat) by (apply nth_error_Some; rewrite Hn; discriminate).
      rewrite <- (firstn_skipn 2 (argv_ptrs sp argv envp)) in Hn. rewrite nth_error_app1 in Hn; [exact Hn|].
      rewrite length_firstn. lia. }
    destruct (u64s_split _ _ _ Hn') as (pre & post & E & Hlen & Eu & Hlu).
    replace (8 * Z.of_nat i)%Z with (Z.of_nat (8 * i))%Z by lia.
    rewrite (bytes_at_ov_read bsegs m (usp + 8) (u64s (firstn 2 (argv_ptrs sp argv envp))) (8 * i) 8 AP).
    2:{ rewrite Eu, !length_app, length_le8, Hlu. lia. }
    rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
    rewrite firstn_app, firstn_all2 by (rewrite length_le8; lia).
    rewrite length_le8, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
  Qed.
End AImg.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition envp_addr (sp0 : word) (argv : list (list byte)) : Z := (bv_unsigned sp0 + 8 * (argc argv + 2))%Z.

Section CTX.
  Variables (sp0 : word) (argv envp : list (list byte)).
  Notation usp0 := (bv_unsigned sp0).

  Definition LO : Z := usp0 - 8388608.

  (* [comment removed for export] *)
  Definition MFRAME (mm : mem) (pad : list byte) (s7v s6v s5v s4v : word) : Prop :=
    rw_cells bsegs mm (usp0 + -128)
      [CB 8 pad; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 (Z_to_bv 64 (envp_addr sp0 argv)); C8 (Z_to_bv 64 0x818b0);
       C8 (Z_to_bv 64 (argc argv)); C8 (Z_to_bv 64 (usp0 + 8)); C8 (Z_to_bv 64 0x92200)].
End CTX.

(* [comment removed for export] *)
Definition ASTAT (mm : mem) : Prop :=
  rw_cells bsegs mm 0xa6200 [C8 (Z_to_bv 64 0xa5498); C8 (Z_to_bv 64 0)]
  /\ rw_cells bsegs mm 0xa5498 [C8 (Z_to_bv 64 0xa9c68)]
  /\ atx_ok_on bsegs mm.
Definition astat_addr (a : Z) : Prop :=
  (0xa6200 <= a < 0xa6218) \/ (0xa5498 <= a < 0xa54a8) \/ (0x5e0c10 <= a < 0x5e0c15) \/ (0x6015a0 <= a < 0x6017c0).

Lemma atx_ok_agree : forall (P : Z -> Prop) m m', agree_on P m m' ->
  (forall a, (0x5e0c10 <= a < 0x5e0c15) \/ (0x6015a0 <= a < 0x6017c0) -> P a) -> atx_ok_on bsegs m -> atx_ok_on bsegs m'.
Proof. aceil.
  intros P m m' AG HP (reg & p3 & p4 & FJ & AJ & B1 & B2 & B3). exists reg, p3, p4, FJ, AJ.
  split; [eapply rw_cells_agree; [exact AG| exact B1| intros a Ha; apply HP; unfold atx_cells in Ha; cbn in Ha; lia]|].
  split; (eapply rw_cells_agree; [exact AG| eassumption| intros a Ha; apply HP; cbn in Ha; lia]).
Qed.

Lemma ASTAT_agree : forall (P : Z -> Prop) m m', agree_on P m m' -> (forall a, astat_addr a -> P a) -> ASTAT m -> ASTAT m'.
Proof. aceil.
  intros P m m' AG HP (G & E & AX). unfold astat_addr in HP.
  split; [| split]; [eapply rw_cells_agree; [exact AG| exact G| intros a Ha; apply HP; cbn in Ha; lia]
                    | eapply rw_cells_agree; [exact AG| exact E| intros a Ha; apply HP; cbn in Ha; lia]
                    | eapply atx_ok_agree; [exact AG| | exact AX]; intros a Ha; apply HP; lia].
Qed.

(* [comment removed for export] *)
Lemma ASTAT_reflag : forall (P : Z -> Prop) m m', agree_on P m m' -> (forall a, astat_addr a -> a <> 0x5e0c14 -> P a) ->
  rw_cells bsegs m' 0x5e0c14 [C1 (Z_to_bv 8 0)] -> ASTAT m -> ASTAT m'.
Proof. aceil.
  intros P m m' AG HP FL (G & E & (reg & p3 & p4 & FJ & AJ & B1 & B2 & B3)). unfold astat_addr in HP.
  split; [eapply rw_cells_agree; [exact AG| exact G| intros a Ha; apply HP; cbn in Ha; lia]|].
  split; [eapply rw_cells_agree; [exact AG| exact E| intros a Ha; apply HP; cbn in Ha; lia]|].
  exists reg, p3, p4, FJ, AJ.
  split; [eapply rw_cells_agree; [exact AG| exact B1| intros a Ha; apply HP; unfold atx_cells in Ha; cbn in Ha; lia]|].
  split; [eapply rw_cells_agree; [exact AG| exact B2| intros a Ha; apply HP; cbn in Ha; lia]| exact FL].
Qed.

(* [comment removed for export] *)
Lemma ASTAT_flag : forall m, ASTAT m -> rw_cells bsegs m 0x5e0c14 [C1 (Z_to_bv 8 0)].
Proof. intros m (_ & _ & (reg & p3 & p4 & FJ & AJ & _ & _ & B3)). exact B3. Qed.

Section BASE.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw).
  Hypothesis VSP : valid_sp sp0.
  Hypothesis RCSP : rc_sp = bv_unsigned sp0.          (* [comment removed for export] *)
  Hypothesis EFIT : entry_stack_fits sp0 argv envp.   (* [comment removed for export] *)
  Hypothesis VARGV : valid_argv argv.
  Hypothesis VENVP : valid_envp envp.
  Notation usp0 := (bv_unsigned sp0).
  Notation IMGB := (build_stack_bytes aph sp0 argv envp uid hw rnd).
  Notation LO' := (LO sp0).

  Lemma sp_facts : 0x7fff80000000 <= usp0 <= 0x800000000000 /\ usp0 mod 16 = 0 /\ alloc_ceiling <= LO sp0 /\ LO sp0 + 8388608 = usp0 /\ 0x605000 <= LO sp0.
  Proof.
    destruct VSP as (A & B & C). unfold LO, alloc_ceiling, sp_window_lo, sp_window_hi, stack_max_size in *. rewrite RCSP. repeat split; lia.
  Qed.

  Lemma IMGB_len : usp0 + Z.of_nat (length IMGB) <= 2^64 - 2^16.
  Proof.
    destruct VSP as (A & B & C). unfold sp_window_hi in *.
    pose proof (build_stack_bytes_length aph sp0 argv envp uid hw rnd). pose proof (raw_len_nonneg aph sp0 argv envp uid hw rnd).
    destruct VARGV as (A1 & A2 & _). destruct VENVP as (E1 & E2 & _). unfold raw_len, struct_size, argc, envc in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma IMGB_ts : usp0 + Z.of_nat (length IMGB) <= 0x800000000000.
  Proof.
    pose proof (build_stack_bytes_within_span aph sp0 argv envp uid hw rnd) as L.
    unfold entry_stack_fits, sp_window_hi in EFIT. lia.
  Qed.

  (* [comment removed for export] *)
  Definition ABASE (mm : mem) : Prop :=
    stk bsegs mm LO' (usp0 + -128) /\ mem_inv bsegs mm /\ AIMG sp0 argv envp uid hw rnd mm /\ ASTAT mm.

  (* [comment removed for export] *)
  Lemma ABASE_heap_pres : forall C LB LF SP m m', ABASE m -> aheap_pres bsegs C LB LF SP m m' -> SP <= usp0 + -128 ->
    c_seg3_lo C = 0xa5008 -> c_seg3_hi C = 0xa7000 -> c_initialized C = 0x5e0c10 ->
    mem_inv bsegs m' -> stk bsegs m' LO' (usp0 + -128) -> ABASE m'.
  Proof. aceil.
    intros C LB LF SP m m' (ST & MI & IMG & AS) HP HSP C1 C2 C3 MI' ST'. pose proof sp_facts as SF. unfold LO in SF.
    pose proof (aheap_pres_agree _ _ _ _ _ _ HP) as AG.
    split; [exact ST'|]. split; [exact MI'|]. split.
    - eapply AIMG_agree; [exact AG| intros a Ha; left; lia| exact IMG].
    - eapply ASTAT_agree; [exact AG| | exact AS]. intros a Ha. right; right; right. unfold adrv_static, astat_addr in *. rewrite C1, C2, C3. lia.
  Qed.

  (* [comment removed for export] *)
  Definition AWOK (iv : Z * Z) : Prop :=
    (LO' <= fst iv /\ snd iv <= usp0 + -128)
    \/ (snd iv <= alloc_ceiling /\ (snd iv <= 0x10000 \/ 0x603000 <= fst iv))
    \/ (fst iv = 0x5e14ac /\ snd iv = 0x5e14ac + 4)                           (* [comment removed for export] *)
    \/ (0x5d0c10 <= fst iv /\ snd iv <= 0x5d0c10 + 65536).                     (* [comment removed for export] *)

  Lemma AWOK_outside : forall W a, Forall AWOK W ->
    (usp0 + -128 <= a \/ (0x10000 <= a < 0x603000 /\ (a < 0x5e14ac \/ 0x5e14b0 <= a) /\ (a < 0x5d0c10 \/ 0x5d0c10 + 65536 <= a))) -> outside W a.
  Proof. aceil.
    pose proof sp_facts as SF. unfold LO in *.
    induction W as [|[lo1 hi1] W IH]; intros a HW Ha; cbn; [exact I|].
    inversion HW as [|x l H1 H2]; subst. split; [| apply IH; assumption].
    unfold AWOK, LO in H1, SF; aceil. cbn [fst snd] in H1. lia.
  Qed.

  Lemma ABASE_munch : forall W m m', ABASE m -> Forall AWOK W -> munch W m m' -> wmono bsegs m m' ->
    mem_inv bsegs m' -> stk bsegs m' LO' (usp0 + -128) -> ABASE m'.
  Proof. aceil.
    intros W m m' (ST & MI & IMG & AS) HW MU WM MI' ST'. pose proof sp_facts as SF. pose proof IMGB_len as IL. unfold LO in *.
    pose proof (agree_on_of_munch _ _ _ MU WM) as AG.
    split; [exact ST'|]. split; [exact MI'|]. split.
    - eapply AIMG_agree; [exact AG| | exact IMG]. intros a Ha. cbn. apply AWOK_outside; [exact HW| left; lia].
    - eapply ASTAT_agree; [exact AG| | exact AS]. intros a Ha. cbn. apply AWOK_outside; [exact HW| unfold astat_addr in Ha; right; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma ABASE_reflag : forall (P : Z -> Prop) m m', ABASE m -> agree_on P m m' ->
    (forall a, (usp0 <= a \/ 0x10000 <= a < 0x603000) -> a <> 0x5e0c14 -> P a) ->
    mem_inv bsegs m' -> stk bsegs m' LO' (usp0 + -128) -> rw_cells bsegs m' 0x5e0c14 [C1 (Z_to_bv 8 0)] -> ABASE m'.
  Proof. aceil.
    intros P m m' (ST & MI & IMG & AS) AG HP MI' ST' FL. pose proof sp_facts as SF. pose proof IMGB_len as IL. unfold LO in *.
    split; [exact ST'|]. split; [exact MI'|]. split.
    - eapply AIMG_agree; [exact AG| | exact IMG]. intros a Ha. apply HP; [left; lia| lia].
    - eapply ASTAT_reflag; [exact AG| | exact FL| exact AS]. intros a Ha NE. apply HP; [right; unfold astat_addr in Ha; lia| exact NE].
  Qed.
End BASE.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section KIT.
  Variable D : adrv_params.
  Hypothesis DI : a_drv_iface bsegs ACONSTS AFMTS D.
  Notation AHK := (p_AHK D).

  (* [comment removed for export] *)
  Lemma pol_stack : forall LB a n, alloc_ceiling <= a -> a + Z.of_nat n <= 2^64 -> a < 2^64 -> adrv_acc ACONSTS LB (Z_to_bv 64 a, n).
  Proof. aceil. intros LB a n H1 H2 H3. unfold adrv_acc. cbn [fst snd]. aceil. rewrite unsigned_lit by lia. left. lia. Qed.
  Lemma pol_img : forall LB a n, 0x10000 <= a -> a + Z.of_nat n <= 0x603000 -> adrv_acc ACONSTS LB (Z_to_bv 64 a, n).
  Proof. aceil. intros LB a n H1 H2. unfold adrv_acc. cbn [fst snd c_img_lo c_img_hi ACONSTS]. rewrite unsigned_lit by lia. right; left. lia. Qed.
  Lemma pol_blk : forall LB b a n, In b LB -> ablock_range ACONSTS (ab_addr b) (ab_size b) ->
    ab_addr b <= a -> a + Z.of_nat n <= ab_addr b + ab_size b -> adrv_acc ACONSTS LB (Z_to_bv 64 a, n).
  Proof. aceil.
    intros LB b a n IN (R1 & R2 & R3 & R4 & R5) H1 H2. unfold adrv_acc. cbn [fst snd]. aceil.
    rewrite unsigned_lit by lia. right; right. exists b. auto.
  Qed.

  (* [comment removed for export] *)
  Lemma adrv_seg : forall s LB LF m mo ms (Q : machine_state -> Prop) T,
    AHK s LB LF m mo -> evtA bsegs (adrv_acc ACONSTS LB) Q ms ->
    (forall ms' mo', Q ms' -> magree mo mo' -> AHK s LB LF m mo' -> m_fs mo' = m_fs mo -> m_fds mo' = m_fds mo ->
                     m_halted mo' = None -> realizes_cfg acfg bsegs (mkCfg ms' mo') T) ->
    realizes_cfg acfg bsegs (mkCfg ms mo) T.
  Proof. aceil.
    intros s LB LF m mo ms Q T HKx EV CONT.
    destruct (adi_kip _ _ _ _ DI _ _ _ _ _ HKx) as (Hh & Hmi & HLI & POL & BACK).
    eapply (srzA_seg bsegs (p_aS D s) (p_aN D s) (p_aEB D s) (adrv_acc ACONSTS LB) Q ms mo T EV).
    - split; [| exact POL]. split; [exact HLI|]. split; [exact Hmi| exact Hh].
    - intros ms' mo' HQ Hag [[HLI' [Hmi' Hh']] _].
      pose proof (magree_frame _ _ Hag) as (Efds & _ & _ & Efs & _).
      apply CONT; [exact HQ| exact Hag| exact (BACK mo' Hag HLI')| exact Efs| exact Efds| exact Hh'].
  Qed.

  (* [comment removed for export] *)
  Lemma AHK_after : forall s LB LF m m' mo W,
    AHK s LB LF m mo -> munch W m m' -> wmono bsegs m m' -> Forall (aclient_write_ok ACONSTS LB) W -> AHK s LB LF m' mo.
  Proof. aceil. intros. eapply (adi_frame _ _ _ _ DI); eauto. Qed.

  Lemma wok_stack : forall LB lo hi, alloc_ceiling <= lo -> aclient_write_ok ACONSTS LB (lo, hi).
  Proof. aceil. intros. left. cbn [fst]. assumption. Qed.
  Lemma wok_init : forall LB, aclient_write_ok ACONSTS LB (0x5e0c10, 0x5e0c11).
  Proof. aceil. intros. right; right; left. cbn [fst snd c_initialized ACONSTS]. lia. Qed.
  Lemma wok_flag : forall LB, aclient_write_ok ACONSTS LB (0x5e0c14, 0x5e0c15).
  Proof. aceil. intros. right; right; left. cbn [fst snd c_initialized ACONSTS]. lia. Qed.
  Lemma wok_atx : forall LB, aclient_write_ok ACONSTS LB (0x6015a0, 0x6015a0 + 544).
  Proof. aceil. intros. right; right; right. cbn [fst snd c_initialized ACONSTS]. lia. Qed.
  Lemma wok_blk : forall LB b lo hi, In b LB -> ab_addr b <= lo -> hi <= ab_addr b + ab_size b -> aclient_write_ok ACONSTS LB (lo, hi).
  Proof. aceil. intros. right; left. exists b. cbn [fst snd]. auto. Qed.
End KIT.


(* [comment removed for export] *)
End RC__2.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section RC__3.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition RSTAGE : Z := 0x5d0c10.
Definition STAGE : Z := 65536.
Lemma STAGE_val : STAGE = 65536. Proof. reflexivity. Qed.
End RC__3.
Global Opaque STAGE.
Arguments STAGE : simpl never.
Section RC__4.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition RSTG (mm : mem) (junk : list byte) : Prop := rw_cells bsegs mm RSTAGE [CB (Z.to_nat STAGE) junk].
Lemma RSTG_agree : forall (P : Z -> Prop) m m' junk, agree_on P m m' -> (forall a, RSTAGE <= a < RSTAGE + STAGE -> P a) -> RSTG m junk -> RSTG m' junk.
Proof.
  intros P m m' junk AG HP R. unfold RSTG in *. eapply rw_cells_agree; [exact AG| exact R|].
  intros a Ha. apply HP. pose proof STAGE_val. cbn [cells_size csize Nat.add] in Ha. lia.
Qed.

(* [comment removed for export] *)
Lemma rw_bytes_b_rom : forall bs A, rw_bytes_b bsegs A bs = true ->
  forall i b, nth_error bs i = Some b ->
    seg_rom bsegs (wa (A + Z.of_nat i)) = Some b /\ wview bsegs (fun _ => None) (wa (A + Z.of_nat i)) <> None.
Proof.
  induction bs as [|b0 bs IH]; intros A Hb i b Hn; [destruct i; discriminate|].
  cbn [rw_bytes_b] in Hb.
  destruct (seg_rom bsegs (wa A)) as [b'|] eqn:Er; [|discriminate].
  destruct (wview bsegs (fun _ => None) (wa A)) as [bw|] eqn:Ew; [|discriminate].
  apply andb_prop in Hb. destruct Hb as [Hbe Hb]. unfold bv_eqb in Hbe. apply Z.eqb_eq in Hbe. apply bv_eq in Hbe. subst b'.
  destruct i as [|i].
  - cbn in Hn. injection Hn as ->. rewrite Z.add_0_r. split; [exact Er| rewrite Ew; discriminate].
  - cbn in Hn. replace (A + Z.of_nat (S i))%Z with ((A + 1) + Z.of_nat i)%Z by lia. exact (IH (A + 1)%Z Hb i b Hn).
Qed.

Lemma rw_cells_any : forall (m : mem) A (bs : list byte),
  rw_bytes_b bsegs A bs = true -> 0 <= A -> A + Z.of_nat (length bs) <= 2^64 ->
  exists junk, rw_cells bsegs m A [CB (length bs) junk].
Proof.
  intros m A bs Hb HA HL.
  exists (map (fun i => match m (wa (A + Z.of_nat i)) with Some b => b | None => nth i bs (Z_to_bv 8 0) end) (seq 0 (length bs))).
  assert (G : forall i, (i < length bs)%nat ->
    mrd bsegs m (wa (A + Z.of_nat i)) = Some (match m (wa (A + Z.of_nat i)) with Some b => b | None => nth i bs (Z_to_bv 8 0) end)
    /\ wview bsegs m (wa (A + Z.of_nat i)) <> None).
  { intros i Hi. destruct (nth_error bs i) as [b|] eqn:E; [| apply nth_error_None in E; lia].
    destruct (rw_bytes_b_rom bs A Hb i b E) as [R W].
    unfold mrd. unfold wview in *. destruct (m (wa (A + Z.of_nat i))) as [b1|] eqn:Em.
    - split; [reflexivity| discriminate].
    - split; [rewrite R; f_equal; symmetry; apply nth_error_nth; exact E| exact W]. }
  set (junk := map _ _).
  assert (LJ : length junk = length bs) by (subst junk; rewrite length_map, length_seq; reflexivity).
  assert (NJ : forall i, (i < length bs)%nat -> nth_error junk i = Some (match m (wa (A + Z.of_nat i)) with Some b => b | None => nth i bs (Z_to_bv 8 0) end)).
  { intros i Hi. subst junk. rewrite (nth_error_map _ _ (seq 0 (length bs))). rewrite nth_error_seq. cbn [Nat.add].
    destruct (Nat.ltb_spec i (length bs)); [reflexivity| exfalso; lia]. }
  clearbody junk.
  split; [split|].
  - cbn. split; [exact LJ| exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. unfold bytes_at. rewrite LJ. split; [lia|]. split; [lia|].
    intros i Hi. rewrite (NJ i ltac:(lia)). exact (proj1 (G i ltac:(lia))).
  - cbn [cells_size csize]. rewrite Nat.add_0_r. split; [lia|]. split; [lia|].
    intros i Hi. replace i with (Z.of_nat (Z.to_nat i)) by lia. exact (proj2 (G (Z.to_nat i) ltac:(lia))).
Qed.

Lemma RSTAGE_rw : rw_bytes_b bsegs RSTAGE (repeat (Z_to_bv 8 0) (Z.to_nat STAGE)) = true.
Proof. rewrite STAGE_val. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma RSTG_any : forall m, exists junk, RSTG m junk.
Proof.
  intros m. unfold RSTG. destruct (rw_cells_any m RSTAGE _ RSTAGE_rw ltac:(unfold RSTAGE; lia) ltac:(rewrite repeat_length; pose proof STAGE_val; unfold RSTAGE; lia)) as [junk R].
  rewrite repeat_length in R. exists junk. exact R.
Qed.
End RC__4.

Ltac adrv_open DI HKx :=
  lazymatch goal with
  | |- realizes_cfg _ ?segs (mkCfg _ ?mo) ?K =>
      eapply (adrv_seg _ DI _ _ _ _ _ _ _ K HKx); [ | ]
  end.
