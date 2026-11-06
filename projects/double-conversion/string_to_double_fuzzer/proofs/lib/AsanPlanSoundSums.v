(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg AgentLib SpinAlg Hoare.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AsanAcct AsanAcctShape.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AsanPopFree.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

Module APSX.
Import AX2. Import AX2S. Import AP. Import APS.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section FPW_1. Context {fx : PropExec.FPState}.

Definition kept_ok (regs regs' : bvmap 5 word) : Prop :=
  forall r : bv 5, r <> 0%bv -> ~ In (ridx r) caller_saved -> getr regs' r = getr regs r.

Section Specs.
Variable SEGS : list Segment.

(* [comment removed for export] *)
Definition fill_spec (entry cmax : Z) : Prop :=
  forall mem0 (s c : word) (n : Z) (regs : bvmap 5 word) (ret : word),
    0 <= n -> bv_unsigned s + n < 2 ^ 64 ->
    store_ok SEGS mem0 s (Z.to_nat n) = true ->
    bv_unsigned c < cmax ->
    ret_ok ret -> getr regs 1%bv = ret ->
    getr regs 10%bv = s -> getr regs 11%bv = c -> getr regs 12%bv = Z_to_bv 64 n ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 entry) mem0 (seg_rom SEGS))
                  (mkst regs' ret (wbytes mem0 s (repeat (Z_to_bv 8 (bv_unsigned c)) (Z.to_nat n))) (seg_rom SEGS))
      /\ kept_ok regs regs' /\ getr regs' 10%bv = s.

(* [comment removed for export] *)
Definition copy_spec (entry : Z) : Prop :=
  forall mem0 (dst src : word) (n : Z) (bs : list byte) (regs : bvmap 5 word) (ret : word),
    0 <= n -> length bs = Z.to_nat n ->
    rdn SEGS mem0 src (length bs) = Some bs ->
    store_ok SEGS mem0 dst (length bs) = true ->
    (bv_unsigned dst + n <= bv_unsigned src \/ bv_unsigned src + n <= bv_unsigned dst) ->
    bv_unsigned src + n < 2 ^ 64 -> bv_unsigned dst + n < 2 ^ 64 ->
    ret_ok ret -> getr regs 1%bv = ret ->
    getr regs 10%bv = dst -> getr regs 11%bv = src -> getr regs 12%bv = Z_to_bv 64 n ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 entry) mem0 (seg_rom SEGS))
                  (mkst regs' ret (wbytes mem0 dst bs) (seg_rom SEGS))
      /\ kept_ok regs regs' /\ getr regs' 10%bv = dst.

(* [comment removed for export] *)
Definition miz_spec (entry : Z) : Prop :=
  forall mem (beg sp : word) (N : Z) (regs : bvmap 5 word) (ret : word),
    0 <= N <= 2 ^ 40 -> bv_unsigned beg + N + 8 <= 2 ^ 64 -> 16 <= bv_unsigned sp ->
    store_ok SEGS mem (Z_to_bv 64 (bv_unsigned sp - 8)) 8 = true ->
    (bv_unsigned beg + N <= bv_unsigned sp - 8 \/ bv_unsigned sp <= bv_unsigned beg) ->
    (forall a : word, bv_unsigned beg <= bv_unsigned a < bv_unsigned beg + N ->
       rdn SEGS mem a 1 = Some [Z_to_bv 8 0]) ->
    ret_ok ret -> getr regs 1%bv = ret -> getr regs 2%bv = sp ->
    getr regs 10%bv = beg -> getr regs 11%bv = Z_to_bv 64 N ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 entry) mem (seg_rom SEGS))
                  (mkst regs' ret (wbytes mem (Z_to_bv 64 (bv_unsigned sp - 8)) (word_to_le_bytes 8 ret)) (seg_rom SEGS))
      /\ kept_ok regs regs' /\ getr regs' 10%bv = Z_to_bv 64 1.

(* [comment removed for export] *)
Definition SEALED_BYTES : list byte :=
  [Z_to_bv 8 0x3c; Z_to_bv 8 0x73; Z_to_bv 8 0x65; Z_to_bv 8 0x61; Z_to_bv 8 0x6c; Z_to_bv 8 0x65; Z_to_bv 8 0x64; Z_to_bv 8 0x3e]
  ++ repeat (Z_to_bv 8 0) 4087.

(* [comment removed for export] *)
Definition istrncpy_spec (entry src : Z) : Prop :=
  forall mem0 (dst : word) (regs : bvmap 5 word) (ret : word),
    (forall i, src <= i < src + 9 -> mem0 (Z_to_bv 64 i) = None) ->
    store_ok SEGS mem0 dst 4095%nat = true ->
    bv_unsigned dst + 4095 < 2 ^ 64 ->
    (bv_unsigned dst + 4095 <= src \/ src + 9 <= bv_unsigned dst) ->
    ret_ok ret -> getr regs 1%bv = ret ->
    getr regs 10%bv = dst -> getr regs 11%bv = Z_to_bv 64 src -> getr regs 12%bv = Z_to_bv 64 4095 ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 entry) mem0 (seg_rom SEGS))
                  (mkst regs' ret (wbytes mem0 dst SEALED_BYTES) (seg_rom SEGS))
      /\ kept_ok regs regs' /\ getr regs' 10%bv = dst.

(* [comment removed for export] *)
End Specs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma reg_of_ridx : forall (r : bv 5) n, ridx r = n -> r = Z_to_bv 5 (Z.of_nat n).
Proof.
  intros r n H. unfold ridx in H. apply bv_eq. rewrite Z_to_bv_unsigned.
  pose proof (bv_unsigned_in_range _ r) as Hr. change (bv_modulus 5) with 32%Z in Hr.
  unfold bv_wrap. change (bv_modulus 5) with 32%Z. rewrite Z.mod_small by lia. lia.
Qed.

Lemma regs_ok_pointwise : forall E sr R,
  (forall r : bv 5, r <> 0%bv -> getr R r = edenot E (nth (ridx r) sr (ELit 0))) -> regs_ok E sr R.
Proof.
  intros E sr R H r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
  - assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; apply Z.eqb_eq in Hr0; exact Hr0). subst r.
    cbn [edenot]. apply getr_zero.
  - apply H. intros X. subst r. unfold bv_eqb in Hr0. rewrite Z.eqb_refl in Hr0. discriminate.
Qed.

Lemma caller_saved_nodup : List.NoDup caller_saved.
Proof.
  unfold caller_saved.
  repeat (apply List.NoDup_cons; [cbn; intros H; repeat (destruct H as [H|H]; [lia|]); exact H|]). apply List.NoDup_nil.
Qed.

Lemma nth_sr_fresh_out : forall cs0 nx sr i,
  ~ In i cs0 -> nth i (sr_fresh sr cs0 nx) (ELit 0) = nth i sr (ELit 0).
Proof.
  intros cs0. induction cs0 as [|c t IH]; intros nx sr i Hn; cbn [sr_fresh]; [reflexivity|].
  rewrite IH by (intros X; apply Hn; right; exact X). rewrite nth_sr_upd.
  destruct (Nat.eqb_spec i c) as [->|]; [exfalso; apply Hn; left; reflexivity | reflexivity].
Qed.

Lemma nth_sr_fresh_in : forall cs0 nx sr j,
  List.NoDup cs0 -> (j < length cs0)%nat -> nth (nth j cs0 0%nat) (sr_fresh sr cs0 nx) (ELit 0) = EVar (nx + j).
Proof.
  intros cs0. induction cs0 as [|c t IH]; intros nx sr j Hnd Hj; cbn [length] in Hj; [lia|].
  inversion Hnd as [|c' t' Hnotin Hnd']; subst.
  cbn [sr_fresh]. destruct j as [|j].
  - cbn [nth]. rewrite nth_sr_fresh_out by exact Hnotin. rewrite nth_sr_upd, Nat.eqb_refl. f_equal. lia.
  - cbn [nth]. rewrite IH by (assumption || lia). f_equal. lia.
Qed.

(* [comment removed for export] *)
Definition ext_call (E : env) (nx : nat) (R' : bvmap 5 word) : env :=
  Env (fun n => if (Nat.leb nx n && Nat.ltb n (nx + NCS))%bool
                then getr R' (Z_to_bv 5 (Z.of_nat (nth (n - nx) caller_saved 0%nat)))
                else ev E n) (eb E).

Lemma ext_call_agree : forall E nx R', env_agree nx E (ext_call E nx R').
Proof.
  intros E nx R'. split; [|reflexivity]. intros n Hn. cbn [ext_call ev].
  destruct (Nat.leb_spec nx n); [lia|]. reflexivity.
Qed.

Lemma ext_call_var : forall E nx R' j, (j < NCS)%nat ->
  ev (ext_call E nx R') (nx + j) = getr R' (Z_to_bv 5 (Z.of_nat (nth j caller_saved 0%nat))).
Proof.
  intros E nx R' j Hj. cbn [ext_call ev].
  replace (Nat.leb nx (nx + j) && Nat.ltb (nx + j) (nx + NCS))%bool with true.
  2:{ symmetry. apply andb_true_intro. split; [apply Nat.leb_le; lia | apply Nat.ltb_lt; lia]. }
  f_equal. f_equal. f_equal. f_equal. lia.
Qed.

Lemma nth_sr_vars_lt' : forall b sr r, AP.sr_vars_lt b sr = true -> (r < 32)%nat -> AP.expr_vars_lt b (nth r sr (ELit 0)) = true.
Proof.
  intros b sr. induction sr as [|x t IH]; intros r H Hr; [destruct r; reflexivity|].
  cbn [AP.sr_vars_lt] in H. apply andb_prop in H as [H1 H2]. destruct r as [|r]; [exact H1|]. cbn [nth]. apply IH; [exact H2 | lia].
Qed.

(* [comment removed for export] *)
Lemma regs_after_call : forall E sr R R' nx rv,
  regs_ok E sr R -> AP.sr_vars_lt nx sr = true -> kept_ok R R' ->
  match rv with Some e => AP.expr_vars_lt nx e = true /\ getr R' (Z_to_bv 5 10) = edenot E e | None => True end ->
  regs_ok (ext_call E nx R')
          (match rv with Some e => sr_upd (sr_fresh sr caller_saved nx) 10 e | None => sr_fresh sr caller_saved nx end) R'.
Proof.
  intros E sr R R' nx rv HR Hsv Hkept Hrv.
  pose proof (ext_call_agree E nx R') as Hag.
  assert (OLD : forall i, (i < 32)%nat -> edenot (ext_call E nx R') (nth i sr (ELit 0)) = edenot E (nth i sr (ELit 0))).
  { intros i Hi. symmetry. apply (edenot_agree' nx); [exact Hag|]. apply nth_sr_vars_lt'; assumption. }
  apply regs_ok_pointwise. intros r Hr0.
  assert (CASES : forall i, (i < 32)%nat -> In i caller_saved \/ ~ In i caller_saved).
  { intros i _. destruct (in_dec Nat.eq_dec i caller_saved); auto. }
  pose proof (ridx_range r) as Hrr.
  assert (GEN : getr R' r = edenot (ext_call E nx R') (nth (ridx r) (sr_fresh sr caller_saved nx) (ELit 0))).
  { destruct (CASES (ridx r) Hrr) as [Hin|Hnin].
    - destruct (In_nth caller_saved (ridx r) 0%nat Hin) as (j & Hj & Hnth).
      rewrite <- Hnth at 1. rewrite nth_sr_fresh_in by (apply caller_saved_nodup || exact Hj).
      cbn [edenot]. rewrite ext_call_var by exact Hj. rewrite Hnth. rewrite <- (reg_of_ridx r _ eq_refl). reflexivity.
    - rewrite nth_sr_fresh_out by exact Hnin. rewrite OLD by exact Hrr.
      rewrite (Hkept r Hr0 Hnin). pose proof (HR r) as X. unfold sr_get in X.
      destruct (bv_eqb r 0) eqn:Hb; [exfalso; apply Hr0; apply bv_eq; unfold bv_eqb in Hb; apply Z.eqb_eq in Hb; exact Hb|].
      exact X. }
  destruct rv as [e|]; [|exact GEN].
  destruct Hrv as [Hev Ha0]. rewrite nth_sr_upd.
  destruct (Nat.eqb_spec (ridx r) 10) as [H10|H10]; [|exact GEN].
  rewrite (reg_of_ridx r 10 H10). change (Z.of_nat 10) with 10%Z.
  rewrite Ha0. apply (edenot_agree' nx); [exact Hag | exact Hev].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma wbytes_same : forall bs m (a : word),
  bv_unsigned a + Z.of_nat (length bs) <= 2 ^ 64 ->
  (forall j, (j < length bs)%nat -> m (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) = Some (nth j bs (Z_to_bv 8 0))) ->
  wbytes m a bs = m.
Proof.
  intros bs m a Hnw Hall. apply functional_extensionality. intros x.
  pose proof (u64_range x) as Hx.
  destruct (Z_lt_dec (bv_unsigned x) (bv_unsigned a)) as [Hlt|Hge].
  { apply wbytes_out; [exact Hnw | lia]. }
  destruct (Z_lt_dec (bv_unsigned x) (bv_unsigned a + Z.of_nat (length bs))) as [Hin|Hout].
  2: { apply wbytes_out; [exact Hnw | lia]. }
  set (j := Z.to_nat (bv_unsigned x - bv_unsigned a)).
  assert (Hxj : x = Z_to_bv 64 (bv_unsigned a + Z.of_nat j)).
  { subst j. rewrite Z2Nat.id by lia. replace (bv_unsigned a + (bv_unsigned x - bv_unsigned a)) with (bv_unsigned x) by lia.
    symmetry. apply Z_to_bv_bv_unsigned. }
  rewrite Hxj at 1. rewrite wbytes_nth by lia. rewrite Hxj. symmetry. apply Hall. lia.
Qed.

(* [comment removed for export] *)
Lemma wbytes_defined : forall bs m (a : word) j,
  bv_unsigned a + Z.of_nat (length bs) <= 2 ^ 64 -> (j < length bs)%nat ->
  wbytes m a bs (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) <> None.
Proof. intros bs m a j Hnw Hj. rewrite wbytes_nth by assumption. discriminate. Qed.

(* [comment removed for export] *)
Lemma rdn_overlay_all : forall segs m n (a : word) b,
  bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat n -> m (Z_to_bv 64 (bv_unsigned a + i)) = Some b) ->
  rdn segs m a n = Some (repeat b n).
Proof.
  intros segs m n; induction n as [|n IH]; intros a b Hnw Hall; [reflexivity|].
  cbn [rdn repeat].
  pose proof (Hall 0 ltac:(lia)) as H0. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in H0. rewrite H0.
  destruct n as [|n'].
  - reflexivity.
  - assert (Hu1 : bv_unsigned (a + 1)%bv = bv_unsigned a + 1) by (apply u_add1; lia).
    rewrite (IH (a + 1)%bv b); [reflexivity | rewrite Hu1; lia |].
    intros i Hi. rewrite Hu1. replace (bv_unsigned a + 1 + i) with (bv_unsigned a + (1 + i)) by lia. apply Hall. lia.
Qed.

(* [comment removed for export] *)
Lemma rdn1_overlay : forall segs m (a : word) b, m a = Some b -> rdn segs m a 1 = Some [b].
Proof. intros segs m a b H. cbn [rdn]. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Lemma rdn_nth : forall segs m n (a : word) bs j,
  bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  rdn segs m a n = Some bs -> (j < n)%nat ->
  rdn segs m (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) 1 = Some [nth j bs (Z_to_bv 8 0)].
Proof.
  intros segs m n; induction n as [|n IH]; intros a bs j Hnw H Hj; [lia|].
  cbn [rdn] in H.
  destruct (match m a with Some b0 => Some b0 | None => seg_rom segs a end) as [b0|] eqn:Hb0; [|discriminate].
  destruct (rdn segs m (a + 1)%bv n) as [rest|] eqn:Hrest; [|discriminate]. injection H as <-.
  destruct j as [|j'].
  - cbn [nth]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. cbn [rdn]. rewrite Hb0. reflexivity.
  - cbn [nth]. destruct n as [|n'']; [lia|].
    assert (Hu1 : bv_unsigned (a + 1)%bv = bv_unsigned a + 1) by (apply u_add1; lia).
    replace (bv_unsigned a + Z.of_nat (S j')) with (bv_unsigned (a + 1)%bv + Z.of_nat j') by lia.
    apply (IH (a + 1)%bv rest j'); [lia | exact Hrest | lia].
Qed.

(* [comment removed for export] *)
Lemma rdn_of_nth : forall segs m n (a : word) (f : nat -> byte),
  bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  (forall j, (j < n)%nat -> rdn segs m (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) 1 = Some [f j]) ->
  rdn segs m a n = Some (map f (seq 0 n)).
Proof.
  intros segs m n; induction n as [|n IH]; intros a f Hnw Hall; [reflexivity|].
  cbn [rdn seq map].
  pose proof (Hall 0%nat ltac:(lia)) as H0. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in H0. cbn [rdn] in H0.
  destruct (match m a with Some b0 => Some b0 | None => seg_rom segs a end) as [b0|]; [|discriminate].
  injection H0 as ->.
  destruct n as [|n'].
  - reflexivity.
  - assert (Hu1 : bv_unsigned (a + 1)%bv = bv_unsigned a + 1) by (apply u_add1; lia).
    rewrite (IH (a + 1)%bv (fun j => f (S j))); [rewrite <- seq_shift, map_map; reflexivity | lia |].
    intros j Hj. rewrite Hu1. replace (bv_unsigned a + 1 + Z.of_nat j) with (bv_unsigned a + Z.of_nat (S j)) by lia.
    apply Hall. lia.
Qed.

(* [comment removed for export] *)
Lemma land_shl_disjoint : forall a b k, (0 <= a)%Z -> (0 <= k)%Z -> (0 <= b < 2 ^ k)%Z ->
  Z.land (a * 2 ^ k) b = 0%Z.
Proof.
  intros a b k Ha Hk Hb. apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i k) as [Hl|Hh].
  - rewrite Z.mul_pow2_bits_low by lia. reflexivity.
  - rewrite (Z_testbit_high k b i) by lia. apply Bool.andb_false_r.
Qed.

Lemma lor_shl_disjoint : forall a b k, (0 <= a)%Z -> (0 <= k)%Z -> (0 <= b < 2 ^ k)%Z ->
  Z.lor (a * 2 ^ k) b = (a * 2 ^ k + b)%Z.
Proof.
  intros a b k Ha Hk Hb.
  rewrite <- Z.lxor_lor by (apply land_shl_disjoint; lia).
  symmetry. apply Z.add_nocarry_lxor. apply land_shl_disjoint; lia.
Qed.

Lemma Z_to_le_bytes_of_bytes : forall bs,
  Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b rest IH]; [reflexivity|].
  cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bv_unsigned_in_range _ b) as Hb. change (bv_modulus 8) with 256%Z in Hb.
  pose proof (bytes_le_to_Z_nonneg rest) as Hr.
  assert (Hlor : Z.lor (bv_unsigned b) (Z.shiftl (bytes_le_to_Z rest) 8) = bv_unsigned b + 2 ^ 8 * bytes_le_to_Z rest).
  { rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.lor_comm. rewrite lor_shl_disjoint by lia. lia. }
  rewrite Hlor. f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with (2 ^ 8).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    change (2 ^ 8) with 256 in *. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256 in *.
    replace ((bv_unsigned b + 256 * bytes_le_to_Z rest) / 256) with (bytes_le_to_Z rest) by lia. exact IH.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma word_to_le_bytes_of_bytes : forall bs,
  (length bs <= 8)%nat ->
  word_to_le_bytes (length bs) (Z_to_bv 64 (bytes_le_to_Z bs)) = bs.
Proof.
  intros bs Hlen. unfold word_to_le_bytes.
  pose proof (AX2S.bytes_le_to_Z_bound bs) as Hb.
  assert (Hlt : bytes_le_to_Z bs < 2 ^ 64).
  { eapply Z.lt_le_trans; [exact (proj2 Hb)|]. apply Z.pow_le_mono_r; lia. }
  rewrite u64_lit by lia. apply Z_to_le_bytes_of_bytes.
Qed.

Lemma word_to_le_bytes_of_bytes_n : forall n bs,
  length bs = n -> (n <= 8)%nat ->
  word_to_le_bytes n (Z_to_bv 64 (bytes_le_to_Z bs)) = bs.
Proof. intros n bs <- Hn. apply word_to_le_bytes_of_bytes. exact Hn. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section KnowTests.
Variable segs : list Segment.
Variable A : atable.   (* [comment removed for export] *)

Lemma adenot_SA : forall E b off, adenot E (SA b off) = Z_to_bv 64 (estart E (SA b off)).
Proof. intros. unfold adenot, v_addi, estart. reflexivity. Qed.

(* [comment removed for export] *)
Lemma kwritable0_sound : forall E M allkn k b off n,
  know_ok segs E M allkn ->
  know_ok segs E M k -> kwritable0 allkn k b off n = true -> 0 <= n ->
  store_ok segs M (Z_to_bv 64 (estart E (SA b off))) (Z.to_nat n) = true
  /\ 0 <= estart E (SA b off) /\ estart E (SA b off) + n <= 2 ^ 64.
Proof.
  intros E M allkn k b off n Hall HK H Hn. induction k as [|K rest IH]; [discriminate|].
  apply Forall_cons_iff in HK as [HKK Hrest].
  destruct K; try exact (IH Hrest H).
  lazymatch type of H with context [KWr ?wa ?wl :: rest] => destruct wa as [wb wk]; rename wl into wn end.
  cbn [kwritable0] in H.
  cbn [kentry_ok] in HKK. destruct HKK as [Hfl Hs]. pose proof Hfl as Hfl'. destruct Hfl' as (F1 & F2 & F3 & F4).
  unfold estart in Hs, F1, F2, F4 |- *. cbn [a_base a_off] in Hs, F1, F2, F4 |- *.
  assert (CORE : bv_unsigned (edenot E wb) + wk <= bv_unsigned (edenot E b) + off ->
                 bv_unsigned (edenot E b) + off + n <= bv_unsigned (edenot E wb) + wk + elenZ E wn ->
                 store_ok segs M (Z_to_bv 64 (bv_unsigned (edenot E b) + off)) (Z.to_nat n) = true
                 /\ 0 <= bv_unsigned (edenot E b) + off /\ bv_unsigned (edenot E b) + off + n <= 2 ^ 64).
  { intros HA0 HB0. split; [|lia].
    replace (bv_unsigned (edenot E b) + off) with (bv_unsigned (edenot E wb) + wk + (bv_unsigned (edenot E b) + off - (bv_unsigned (edenot E wb) + wk))) by lia.
    apply Hs; [lia|]. rewrite Z2Nat.id by lia. lia. }
  lazymatch type of H with (if ?c0 then _ else _) = _ => destruct c0 eqn:Hc0 end.
  - destruct (expr_eqb b wb && Z.leb wk off)%bool eqn:H01; [|discriminate]. apply andb_prop in H01 as [H0 H1].
    apply expr_eqb_eq in H0. apply Z.leb_le in H1. subst wb.
    destruct (xlo allkn wn) as [wl|] eqn:Hx; [|discriminate]. apply Z.leb_le in Hc0.
    pose proof (xlo_sound segs E M allkn wn wl Hall Hx) as Hwl. unfold elenZ in *. apply CORE; lia.
  - lazymatch type of H with (if ?c1 then _ else _) = _ => destruct c1 eqn:Hc1; [|exact (IH Hrest H)] end.
    apply andb_prop in Hc1 as [Hnn Hxi]. apply andb_prop in Hnn as [Hn0 Hn1].
    apply Z.leb_le in Hn0. apply Z.ltb_lt in Hn1. unfold two64 in Hn1.
    destruct (xinsideL_sound segs E M allkn b off (ELit n) wb wk wn Hall Hxi) as [I1 I2].
    unfold elenZ in I2 at 1. cbn [edenot] in I2. rewrite u64_lit in I2 by lia.
    unfold estart in I1, I2. cbn [a_base a_off] in I1, I2. apply CORE; lia.
Qed.

(* [comment removed for export] *)
Lemma kwritable0_x_sound : forall E M allkn k b off n,
  know_ok segs E M allkn ->
  know_ok segs E M k -> kwritable0_x allkn k b off n = true ->
  (forall m, Z.of_nat m <= elenZ E n ->
     store_ok segs M (Z_to_bv 64 (estart E (SA b off))) m = true)
  /\ 0 <= estart E (SA b off) /\ estart E (SA b off) + elenZ E n <= 2 ^ 64.
Proof.
  intros E M allkn k b off n Hall HK H. induction k as [|K rest IH]; [discriminate|].
  apply Forall_cons_iff in HK as [HKK Hrest].
  destruct K; try exact (IH Hrest H).
  lazymatch type of H with context [KWr ?wa ?wl :: rest] => destruct wa as [wb wk]; rename wl into wn end.
  cbn [kwritable0_x] in H.
  assert (H2w : forall c1 c2 : bool, (if c1 then true else if c2 then true else kwritable0_x allkn rest b off n) = true ->
                 (c1 || c2)%bool = true \/ kwritable0_x allkn rest b off n = true)
    by (intros [|] [|]; cbn; auto).
  apply H2w in H. destruct H as [H|H]; [|exact (IH Hrest H)].
  cbn [kentry_ok] in HKK. destruct HKK as [Hfl Hs]. pose proof Hfl as Hfl'. destruct Hfl' as (F1 & F2 & F3 & F4).
  unfold estart in Hs, F1, F2, F4 |- *. cbn [a_base a_off] in Hs, F1, F2, F4 |- *.
  pose proof (u64_range (edenot E n)) as Hnr.
  assert (CORE : bv_unsigned (edenot E wb) + wk <= bv_unsigned (edenot E b) + off ->
                 bv_unsigned (edenot E b) + off + elenZ E n <= bv_unsigned (edenot E wb) + wk + elenZ E wn ->
                 (forall m, Z.of_nat m <= elenZ E n -> store_ok segs M (Z_to_bv 64 (bv_unsigned (edenot E b) + off)) m = true)
                 /\ 0 <= bv_unsigned (edenot E b) + off /\ bv_unsigned (edenot E b) + off + elenZ E n <= 2 ^ 64).
  { intros HA0 HB0. split; [|unfold elenZ in *; lia]. intros m Hm.
    replace (bv_unsigned (edenot E b) + off) with (bv_unsigned (edenot E wb) + wk + (bv_unsigned (edenot E b) + off - (bv_unsigned (edenot E wb) + wk))) by lia.
    apply Hs; lia. }
  apply orb_prop in H as [H|H].
  - destruct (expr_eqb b wb && Z.leb wk off)%bool eqn:H01; [|discriminate]. apply andb_prop in H01 as [H0 H1].
    apply expr_eqb_eq in H0. apply Z.leb_le in H1. subst wb.
    destruct (xhi allkn n) as [nh|] eqn:Hxh; [|discriminate].
    destruct (xlo allkn wn) as [wl|] eqn:Hxl; [|discriminate]. apply Z.leb_le in H.
    pose proof (xhi_sound segs E M allkn n nh Hall Hxh). pose proof (xlo_sound segs E M allkn wn wl Hall Hxl).
    apply CORE; unfold elenZ in *; lia.
  - pose proof (xinsideL_sound segs E M allkn b off n wb wk wn Hall H) as [HA0 HB0].
    unfold estart in HA0, HB0. cbn [a_base a_off] in HA0, HB0. apply CORE; lia.
Qed.

(* [comment removed for export] *)
Lemma kwritable_sound : forall E M allkn k b off n,
  know_ok segs E M allkn ->
  know_ok segs E M k -> kwritable A allkn k b off n = true -> 0 <= n ->
  store_ok segs M (Z_to_bv 64 (estart E (SA b off))) (Z.to_nat n) = true
  /\ 0 <= estart E (SA b off) /\ estart E (SA b off) + n <= 2 ^ 64.
Proof.
  intros E M allkn k b off n Hall HK H Hn. unfold kwritable in H. apply andb_prop in H as [H _].
  exact (kwritable0_sound E M allkn k b off n Hall HK H Hn).
Qed.
Lemma kwritable_lfp : forall E M allkn k b off n,
  know_ok segs E M allkn -> kwritable A allkn k b off n = true ->
  forall z, in_lfp A z = true -> z < estart E (SA b off) \/ estart E (SA b off) + n <= z.
Proof.
  intros E M allkn k b off n Hall H z Hz. unfold kwritable in H. apply andb_prop in H as [_ H].
  unfold estart; cbn [a_base a_off]. exact (APS.lfp_apartz_sound segs A E M allkn b off n Hall H z Hz).
Qed.
Lemma kwritable_x_sound : forall E M allkn k b off n,
  know_ok segs E M allkn ->
  know_ok segs E M k -> kwritable_x A allkn k b off n = true ->
  (forall m, Z.of_nat m <= elenZ E n ->
     store_ok segs M (Z_to_bv 64 (estart E (SA b off))) m = true)
  /\ 0 <= estart E (SA b off) /\ estart E (SA b off) + elenZ E n <= 2 ^ 64.
Proof.
  intros E M allkn k b off n Hall HK H. unfold kwritable_x in H. apply andb_prop in H as [H _].
  exact (kwritable0_x_sound E M allkn k b off n Hall HK H).
Qed.
Lemma kwritable_x_lfp : forall E M allkn k b off n,
  know_ok segs E M allkn -> kwritable_x A allkn k b off n = true ->
  forall z, in_lfp A z = true -> z < estart E (SA b off) \/ estart E (SA b off) + elenZ E n <= z.
Proof.
  intros E M allkn k b off n Hall H z Hz. unfold kwritable_x in H. apply andb_prop in H as [_ H].
  unfold estart, elenZ; cbn [a_base a_off]. exact (APS.lfp_apart_x_sound segs A E M allkn b off n Hall H z Hz).
Qed.

(* [comment removed for export] *)
Lemma kzero_x_sound : forall E M allkn k b off n,
  know_ok segs E M allkn ->
  know_ok segs E M k -> kzero_x allkn k b off n = true ->
  (forall i, 0 <= i < elenZ E n -> M (Z_to_bv 64 (estart E (SA b off) + i)) = Some (Z_to_bv 8 0))
  /\ 0 <= estart E (SA b off) /\ estart E (SA b off) + elenZ E n <= 2 ^ 64.
Proof.
  intros E M allkn k b off n Hall HK H. induction k as [|K rest IH]; [discriminate|].
  apply Forall_cons_iff in HK as [HKK Hrest].
  destruct K; try exact (IH Hrest H).
  lazymatch type of H with context [KZero ?za ?zl :: rest] => destruct za as [zb zk]; rename zl into zn end.
  cbn [kzero_x] in H.
  assert (H2w : forall c1 c2 : bool, (if c1 then true else if c2 then true else kzero_x allkn rest b off n) = true ->
                 (c1 || c2)%bool = true \/ kzero_x allkn rest b off n = true)
    by (intros [|] [|]; cbn; auto).
  apply H2w in H. destruct H as [H|H]; [|exact (IH Hrest H)].
  cbn [kentry_ok] in HKK. destruct HKK as [Hfl Hz]. pose proof Hfl as Hfl'. destruct Hfl' as (F1 & F2 & F3 & F4).
  unfold estart in Hz, F1, F2, F4 |- *. cbn [a_base a_off] in Hz, F1, F2, F4 |- *.
  pose proof (u64_range (edenot E n)) as Hnr.
  assert (CORE : bv_unsigned (edenot E zb) + zk <= bv_unsigned (edenot E b) + off ->
                 bv_unsigned (edenot E b) + off + elenZ E n <= bv_unsigned (edenot E zb) + zk + elenZ E zn ->
                 (forall i, 0 <= i < elenZ E n -> M (Z_to_bv 64 (bv_unsigned (edenot E b) + off + i)) = Some (Z_to_bv 8 0))
                 /\ 0 <= bv_unsigned (edenot E b) + off /\ bv_unsigned (edenot E b) + off + elenZ E n <= 2 ^ 64).
  { intros HA0 HB0. split; [|unfold elenZ in *; lia]. intros i Hi.
    replace (bv_unsigned (edenot E b) + off + i) with (bv_unsigned (edenot E zb) + zk + (bv_unsigned (edenot E b) + off - (bv_unsigned (edenot E zb) + zk) + i)) by lia.
    apply Hz. lia. }
  apply orb_prop in H as [H|H].
  - destruct (expr_eqb b zb && Z.leb zk off)%bool eqn:H01; [|discriminate]. apply andb_prop in H01 as [H0 H1].
    apply expr_eqb_eq in H0. apply Z.leb_le in H1. subst zb.
    destruct (xhi allkn n) as [nh|] eqn:Hxh; [|discriminate].
    destruct (xlo allkn zn) as [zl|] eqn:Hxl; [|discriminate]. apply Z.leb_le in H.
    pose proof (xhi_sound segs E M allkn n nh Hall Hxh). pose proof (xlo_sound segs E M allkn zn zl Hall Hxl).
    apply CORE; unfold elenZ in *; lia.
  - pose proof (xinsideL_sound segs E M allkn b off n zb zk zn Hall H) as [HA0 HB0].
    unfold estart in HA0, HB0. cbn [a_base a_off] in HA0, HB0. apply CORE; lia.
Qed.

(* [comment removed for export] *)
Lemma kimg_cut_sound : forall E M k a n,
  know_ok segs E M k -> know_ok segs E M (kimg_cut k a n).
Proof.
  intros E M k a n HK. unfold kimg_cut, know_ok. apply Forall_flat_map. apply Forall_forall. intros K Hin.
  pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
  unfold kimg_cut1. destruct K; try (apply Forall_one; exact HKK).
  lazymatch goal with |- context [KImg ?l ?h] => rename l into lo; rename h into hi end.
  destruct (Z.leb hi a || Z.leb (a + n) lo)%bool eqn:Hc; [apply Forall_one; exact HKK|].
  apply orb_false_iff in Hc as [Hc1 Hc2]. apply Z.leb_gt in Hc1. apply Z.leb_gt in Hc2.
  cbn [kentry_ok] in HKK. destruct HKK as (H0 & Hhi & Hnone).
  apply Forall_app. split.
  - destruct (Z.ltb lo a) eqn:Hl; [|constructor]. apply Z.ltb_lt in Hl. apply Forall_one. cbn [kentry_ok].
    split; [lia|]. split; [lia|]. intros i Hi. apply Hnone. lia.
  - destruct (Z.ltb (a + n) hi) eqn:Hh; [|constructor]. apply Z.ltb_lt in Hh. apply Forall_one. cbn [kentry_ok].
    split; [lia|]. split; [lia|]. intros i Hi. apply Hnone. lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition piece_ok (E : env) (M : word -> option byte) (b : expr) (off : Z) (w : nat) (v : expr) : Prop :=
  exists bs, rdn segs M (Z_to_bv 64 (estart E (SA b off))) w = Some bs /\ length bs = w
             /\ word_to_le_bytes w (edenot E v) = bs.

Lemma lookup_piece : forall E M k b off w v hs,
  know_ok segs E M k -> (1 <= w <= 8)%nat ->
  know_lookup segs k b off w false [] [] = LHit v [] hs ->
  flat E (SA b off) (Z.of_nat w) ->
  piece_ok E M b off w v.
Proof.
  intros E M k b off w v hs HK Hw HL Hfl.
  pose proof (know_lookup_sound segs E M k b off w false [] [] HK ltac:(lia) ltac:(lia)) as X.
  rewrite HL in X. destruct (X ltac:(constructor) Hfl) as (bs & Hrd & Hlen & Hv).
  exists bs. rewrite <- adenot_SA. split; [exact Hrd|]. split; [exact Hlen|].
  unfold extz in Hv. rewrite <- Hv, <- Hlen. apply word_to_le_bytes_of_bytes. lia.
Qed.

Lemma kread8e_piece : forall E M k b off v,
  know_ok segs E M k -> kread8e segs k b off = Some v -> flat E (SA b off) 8 ->
  piece_ok E M b off 8 v.
Proof.
  intros E M k b off v HK H Hfl. unfold kread8e in H.
  destruct (know_lookup segs k b off 8 false [] []) as [v' scs hs|scs hs|] eqn:HL; try discriminate.
  destruct scs; [|discriminate]. injection H as ->.
  eapply lookup_piece; [exact HK | lia | exact HL | exact Hfl].
Qed.

Lemma kreadZ1_byte : forall E M k b off z,
  know_ok segs E M k -> kreadZ segs k b off 1 = Some z -> flat E (SA b off) 1 ->
  rdn segs M (Z_to_bv 64 (estart E (SA b off))) 1 = Some [Z_to_bv 8 z] /\ 0 <= z < 256.
Proof.
  intros E M k b off z HK H Hfl. unfold kreadZ in H.
  destruct (know_lookup segs k b off 1 false [] []) as [v' scs hs|scs hs|] eqn:HL; try discriminate.
  destruct v' as [z0| | | | | | |]; try discriminate. destruct scs; [|discriminate]. injection H as <-.
  pose proof (know_lookup_sound segs E M k b off 1 false [] [] HK ltac:(lia) ltac:(lia)) as X.
  rewrite HL in X. destruct (X ltac:(constructor) Hfl) as (bs & Hrd & Hlen & Hv).
  destruct bs as [|b0 [|]]; try discriminate.
  cbn [edenot] in Hv. unfold extz in Hv. rewrite bytes_le_single in Hv.
  apply (f_equal bv_unsigned) in Hv. rewrite !u_lit64 in Hv.
  pose proof (bv_unsigned_in_range _ b0) as Hr. change (bv_modulus 8) with 256 in Hr.
  rewrite (Z.mod_small (bv_unsigned b0)) in Hv by (unfold two64; lia).
  split; [|rewrite <- Hv; lia]. rewrite <- adenot_SA, Hrd. f_equal. f_equal. apply bv_eq.
  rewrite Z_to_bv_unsigned, <- Hv. symmetry. apply bv_wrap_small. change (bv_modulus 8) with 256. lia.
Qed.

Lemma kread_bytes_sound : forall E M k len b off zs,
  know_ok segs E M k -> kread_bytes segs len k b off = Some zs ->
  0 <= estart E (SA b off) -> estart E (SA b off) + Z.of_nat len <= 2 ^ 64 ->
  rdn segs M (Z_to_bv 64 (estart E (SA b off))) len = Some (map (fun z => Z_to_bv 8 z) zs)
  /\ length zs = len /\ Forall (fun z => 0 <= z < 256) zs.
Proof.
  intros E M k len. induction len as [|len IH]; intros b off zs HK H Hlo Hhi.
  - cbn in H. injection H as <-. split; [reflexivity|]. split; [reflexivity | constructor].
  - cbn [kread_bytes] in H.
    destruct (kreadZ segs k b off 1) as [z|] eqn:Hz; [|discriminate].
    destruct (kread_bytes segs len k b (off + 1)) as [rest|] eqn:Hrest; [|discriminate].
    injection H as <-.
    assert (Hfl : flat E (SA b off) 1) by (unfold flat; lia).
    destruct (kreadZ1_byte E M k b off z HK Hz Hfl) as [Hrd Hzr].
    destruct (IH b (off + 1) rest HK Hrest ltac:(unfold estart in *; cbn [a_base a_off] in *; lia)
                 ltac:(unfold estart in *; cbn [a_base a_off] in *; lia)) as (Hrd2 & Hlen & Hall).
    split; [| split; [cbn; lia | constructor; assumption]].
    change (S len) with (1 + len)%nat. cbn [map].
    change (Z_to_bv 8 z :: map (fun z0 : Z => Z_to_bv 8 z0) rest) with ([Z_to_bv 8 z] ++ map (fun z0 : Z => Z_to_bv 8 z0) rest).
    eapply rdn_app; [exact Hrd|].
    replace (Z_to_bv 64 (estart E (SA b off)) + nat_to_word 1)%bv with (Z_to_bv 64 (estart E (SA b (off + 1)))); [exact Hrd2|].
    apply bv_eq. unfold nat_to_word, estart. cbn [a_base a_off]. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
    change (Z.of_nat 1) with 1. rewrite (Z.mod_small 1) by lia.
    rewrite Z.add_mod_idemp_l by lia. f_equal. lia.
Qed.

Lemma zbytes_of_small : forall zs, Forall (fun z => 0 <= z < 256) zs ->
  zbytes_le_to_Z zs = bytes_le_to_Z (map (fun z => Z_to_bv 8 z) zs).
Proof.
  intros zs Hall. rewrite <- zbytes_map. rewrite map_map. f_equal.
  induction Hall as [|z rest Hz Hrest IH]; [reflexivity|]. cbn [map]. f_equal; [|exact IH].
  symmetry. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. lia.
Qed.

(* [comment removed for export] *)
Lemma copy_facts_sound : forall E M k sb db fuel sk dk n kc,
  know_ok segs E M k ->
  copy_facts segs fuel k sb sk db dk n = Some kc -> 0 <= n -> (Z.to_nat n <= fuel)%nat ->
  0 <= estart E (SA sb sk) -> estart E (SA sb sk) + n <= 2 ^ 64 ->
  0 <= estart E (SA db dk) -> estart E (SA db dk) + n <= 2 ^ 64 ->
  exists bs, length bs = Z.to_nat n
    /\ rdn segs M (Z_to_bv 64 (estart E (SA sb sk))) (Z.to_nat n) = Some bs
    /\ forall M', rdn segs M' (Z_to_bv 64 (estart E (SA db dk))) (Z.to_nat n) = Some bs -> know_ok segs E M' kc.
Proof.
  intros E M k sb db fuel. induction fuel as [|f IH]; intros sk dk n kc HK H Hn Hfuel Slo Shi Dlo Dhi.
  - cbn [copy_facts] in H. injection H as <-. assert (n = 0) by lia. subst n.
    exists []. split; [reflexivity|]. split; [reflexivity|]. intros M' _. constructor.
  - cbn [copy_facts] in H.
    (* [comment removed for export] *)
    assert (STEP : forall (w : nat) v kr,
      (1 <= w <= 8)%nat -> Z.of_nat w <= n ->
      piece_ok E M sb sk w v ->
      copy_facts segs f k sb (sk + Z.of_nat w) db (dk + Z.of_nat w) (n - Z.of_nat w) = Some kr ->
      kc = KWord (SA db dk) w v :: kr ->
      exists bs, length bs = Z.to_nat n
        /\ rdn segs M (Z_to_bv 64 (estart E (SA sb sk))) (Z.to_nat n) = Some bs
        /\ forall M', rdn segs M' (Z_to_bv 64 (estart E (SA db dk))) (Z.to_nat n) = Some bs -> know_ok segs E M' kc).
    { intros w v kr Hw Hwn (bsP & HrdP & HlenP & HvP) Hr ->.
      assert (ES : estart E (SA sb (sk + Z.of_nat w)) = estart E (SA sb sk) + Z.of_nat w) by (unfold estart; cbn [a_base a_off]; lia).
      assert (ED : estart E (SA db (dk + Z.of_nat w)) = estart E (SA db dk) + Z.of_nat w) by (unfold estart; cbn [a_base a_off]; lia).
      destruct (IH (sk + Z.of_nat w) (dk + Z.of_nat w) (n - Z.of_nat w) kr HK Hr ltac:(lia) ltac:(lia)
                   ltac:(rewrite ES; lia) ltac:(rewrite ES; lia) ltac:(rewrite ED; lia) ltac:(rewrite ED; lia))
        as (bsR & HlenR & HrdR & HKR).
      exists (bsP ++ bsR). split; [rewrite length_app; lia|]. split.
      - replace (Z.to_nat n) with (w + Z.to_nat (n - Z.of_nat w))%nat by lia.
        apply rdn_app; [rewrite <- HlenP at 1; rewrite HlenP; exact HrdP|].
        rewrite ES in HrdR.
        replace (Z_to_bv 64 (estart E (SA sb sk)) + nat_to_word w)%bv with (Z_to_bv 64 (estart E (SA sb sk) + Z.of_nat w)); [exact HrdR|].
        apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
        rewrite (Z.mod_small (Z.of_nat w)) by lia. rewrite Z.add_mod_idemp_l by lia. reflexivity.
      - intros M' HM'. constructor.
        + cbn [kentry_ok]. split; [lia|]. split; [unfold flat; lia|].
          rewrite adenot_SA, HvP.
          pose proof (rdn_firstn segs M' (Z.to_nat n) _ _ w HM' ltac:(lia)) as F.
          rewrite F. f_equal. rewrite firstn_app, HlenP, Nat.sub_diag. cbn [firstn]. rewrite firstn_all2 by lia. apply app_nil_r.
        + apply HKR. rewrite ED.
          pose proof (rdn_skipn segs M' (Z.to_nat n) _ _ w HM' ltac:(lia)) as Sk.
          replace (Z.to_nat (n - Z.of_nat w)) with (Z.to_nat n - w)%nat by lia.
          replace (Z_to_bv 64 (estart E (SA db dk) + Z.of_nat w)) with (Z_to_bv 64 (estart E (SA db dk)) + nat_to_word w)%bv.
          2:{ apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
              rewrite (Z.mod_small (Z.of_nat w)) by lia. rewrite Z.add_mod_idemp_l by lia. reflexivity. }
          rewrite Sk. f_equal. rewrite skipn_app, HlenP, Nat.sub_diag. cbn [skipn]. rewrite skipn_all2 by lia. reflexivity. }
    match type of H with (if ?c then _ else _) = _ => destruct c eqn:H8 end.
    + apply andb_prop in H8 as [H8 Hknown]. apply Z.leb_le in H8.
      destruct (copy_facts segs f k sb (sk + 8) db (dk + 8) (n - 8)) as [kr|] eqn:Hr;
        [|destruct (kread8e segs k sb sk); [discriminate|]; destruct (kread_bytes segs 8 k sb sk); discriminate].
      assert (Hfl8 : flat E (SA sb sk) 8) by (unfold flat; lia).
      destruct (kread8e segs k sb sk) as [v|] eqn:Hv.
      * injection H as <-. apply (STEP 8%nat v kr); [lia | lia | | exact Hr | reflexivity].
        eapply kread8e_piece; [exact HK | exact Hv | exact Hfl8].
      * destruct (kread_bytes segs 8 k sb sk) as [zs|] eqn:Hzs; [|discriminate]. injection H as <-.
        apply (STEP 8%nat (ELit (zbytes_le_to_Z zs)) kr); [lia | lia | | exact Hr | reflexivity].
        destruct (kread_bytes_sound E M k 8 sb sk zs HK Hzs ltac:(lia) ltac:(lia)) as (Hrd & Hlen & Hsmall).
        exists (map (fun z => Z_to_bv 8 z) zs). split; [exact Hrd|]. split; [rewrite length_map; exact Hlen|].
        cbn [edenot]. rewrite (zbytes_of_small zs Hsmall).
        replace 8%nat with (length (map (fun z : Z => Z_to_bv 8 z) zs)) at 1 by (rewrite length_map; exact Hlen).
        apply word_to_le_bytes_of_bytes. rewrite length_map. lia.
    + clear H8. destruct (Z.leb 1 n) eqn:H1.
      * apply Z.leb_le in H1.
        destruct (know_lookup segs k sb sk 1 false [] []) as [v scs hs|scs hs|] eqn:HL; try discriminate.
        destruct scs; [|discriminate].
        destruct (copy_facts segs f k sb (sk + 1) db (dk + 1) (n - 1)) as [kr|] eqn:Hr; [|discriminate].
        injection H as <-. apply (STEP 1%nat v kr); [lia | lia | | exact Hr | reflexivity].
        eapply lookup_piece; [exact HK | lia | exact HL | unfold flat; lia].
      * injection H as <-. apply Z.leb_gt in H1. assert (n = 0) by lia. subst n.
        exists []. split; [reflexivity|]. split; [reflexivity|]. intros M' _. constructor.
Qed.

End KnowTests.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Sound.
Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
(* [comment removed for export] *)
Definition res_len_okP : Prop := length (segments_reserved SEGS) = n_res A.
Definition hull_okP : Prop := 0 <= img_lo A /\ img_lo A mod 4096 = 0 /\ img_hi A mod 4096 = 0 /\ img_hi A <= KHI.
Hypothesis RES_len : res_len_okP.
Hypothesis HULL_ok : hull_okP.
Hypothesis SHADOW_ok : shadow_ok A.   (* [comment removed for export] *)
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable LINV : (word -> option byte) -> Prop.   (* [comment removed for export] *)
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis argH_top : forall E M (a : word), SINV E M -> argH E a = true -> bv_unsigned (edenot E e_sp0) <= bv_unsigned a.   (* [comment removed for export] *)
Hypothesis nx0_ge : APS.nx0_ok nx0.                                                                       (* [comment removed for export] *)
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Hypothesis LINV_frame : forall M M' : word -> option byte, (forall a : word, in_lfp A (bv_unsigned a) = true -> M' a = M a) -> LINV M -> LINV M'.
(* [comment removed for export] *)
Variable FS0 : Fs.Fs.
(* [comment removed for export] *)
Definition segs_wr_ok : Prop := forall seg, In seg SEGS -> seg_writable seg = true -> seg_readable seg = true.
Hypothesis SEGS_wr : segs_wr_ok.

#[local] Notation cfg := (cfg_of SEGS) (only parsing).
#[local] Notation CSOK := (cs_ok SEGS A LIMIT SINV argH LINV FS0) (only parsing).
#[local] Notation HID := (hid A argH) (only parsing).
#[local] Notation MR := (Mr A argH) (only parsing).

(* [comment removed for export] *)
#[local] Ltac aps_fill :=
  first [eassumption | exact (fun _ : nat => @None acs) | exact (fun _ _ _ => None) | exact (fun _ _ => None) | exact (fun _ => None)
        | exact 0%nat | exact 0%Z | exact nx0 | exact LIMIT].

Lemma w_reg_sound : forall E cs R FULL model n,
  CSOK E cs R FULL model -> (0 < n < 32)%nat -> getr R (Z_to_bv 5 (Z.of_nat n)) = edenot E (reg cs n).
Proof. intros. eapply reg_sound; try eassumption. Unshelve. all: aps_fill. Qed.

Lemma w_reg_lit_sound : forall E cs R FULL model n z,
  CSOK E cs R FULL model -> (0 < n < 32)%nat -> reg_lit cs n = Some z ->
  getr R (Z_to_bv 5 (Z.of_nat n)) = Z_to_bv 64 z /\ 0 <= z < two64.
Proof. intros. eapply reg_lit_sound; try eassumption. Unshelve. all: aps_fill. Qed.

Lemma w_split_lit_denot : forall E e b k, split_lit e = (b, k) ->
  edenot E e = Z_to_bv 64 (bv_unsigned (edenot E b) + k).
Proof. intros. eapply split_lit_denot; try eassumption. Unshelve. all: aps_fill. Qed.

Lemma w_know_ok_havoc : forall E M M' k b o n,
  know_ok SEGS E M k ->
  (forall x : word, bv_unsigned x < estart E (SA b o) \/ estart E (SA b o) + elenZ E n <= bv_unsigned x -> M' x = M x) ->
  mem_grows M M' ->
  know_ok SEGS E M' (kn_havoc k b o n).
Proof. intros. eapply know_ok_havoc; try eassumption. Unshelve. all: aps_fill. Qed.
Lemma w_know_ok_havoc_z : forall E M M' k b o n,
  know_ok SEGS E M k ->
  (forall x : word, bv_unsigned x < estart E (SA b o) \/ estart E (SA b o) + elenZ E n <= bv_unsigned x -> M' x = M x) ->
  mem_grows M M' ->
  (forall x : word, estart E (SA b o) <= bv_unsigned x < estart E (SA b o) + elenZ E n -> M x <> None -> M' x = Some (Z_to_bv 8 0)) ->
  know_ok SEGS E M' (kn_havoc_z k b o n).
Proof. intros. eapply know_ok_havoc_z; try eassumption. Unshelve. all: aps_fill. Qed.

Lemma w_flat_x_sound : forall E M k b off n,
  know_ok SEGS E M k -> flat_x k b off n = true ->
  0 <= estart E (SA b off) /\ estart E (SA b off) + bv_unsigned (edenot E n) <= 2 ^ 64 /\ 0 < bv_unsigned (edenot E n).
Proof. intros. eapply flat_x_sound; try eassumption. Unshelve. all: aps_fill. Qed.

Lemma w_env_agree_le : forall b b' E E', env_agree b' E E' -> (b <= b')%nat -> env_agree b E E'.
Proof. intros b b' E E' [Hv Hb] Hle. split; [|exact Hb]. intros n Hn. apply Hv. lia. Qed.

Lemma w_cs_ok_agree : forall E E' cs R FULL model,
  env_agree (nxt cs) E E' -> fresh_ok nx0 cs = true -> CSOK E cs R FULL model -> CSOK E' cs R FULL model.
Proof. intros. eapply cs_ok_agree; try eassumption. Unshelve. all: aps_fill. Qed.

Lemma w_hid_agree : forall b E E' cs model,
  env_agree b E E' -> (nx0 <= b)%nat -> pairs_vars_lt b (a_vis cs ++ a_ghost cs) = true ->
  HID E' cs model = HID E cs model.
Proof. intros. eapply hid_agree; try eassumption. Unshelve. all: aps_fill. Qed.

Lemma w_cs_ok_frame : forall E cs R FULL model ss' R' FULL' model',
  CSOK E cs R FULL model -> same_but_materialized model model' -> MInv (allowA A E cs) model' ->
  regs_ok E (s_regs ss') R' -> s_log ss' = [] ->
  know_ok SEGS E (MR E cs model FULL') (s_know ss') ->
  (forall a, HID E cs model a = true -> FULL' a = FULL a) ->
  (forall a, in_lfp A (bv_unsigned a) = true -> FULL' a = FULL a) ->      (* [comment removed for export] *)
  CSOK E (with_ss cs ss') R' FULL' model'.
Proof. intros. eapply cs_ok_frame; try eassumption. Unshelve. all: aps_fill. Qed.

Lemma w_lazy_cover_cs : forall E cs R FULL model,
  CSOK E cs R FULL model -> lazy_cover (HID E cs model) (m_vm_lazy model) (allowA A E cs).
Proof. intros. eapply lazy_cover_cs; try eassumption. Unshelve. all: aps_fill. Qed.

Lemma w_A_wf_allowA : forall E cs, A_wf (allowA A E cs).
Proof. intros. eapply A_wf_allowA; try eassumption. Unshelve. all: aps_fill. Qed.

Lemma w_H_off_segments_cs : forall E cs model, H_off_segments SEGS (HID E cs model).
Proof. intros. eapply H_off_segments_cs; try eassumption. Unshelve. all: aps_fill. Qed.

Lemma w_fresh_ok_parts : forall cs, fresh_ok nx0 cs = true ->
  AP.sr_vars_lt (nxt cs) (s_regs (a_ss cs)) = true /\ AP.kn_vars_lt (nxt cs) (kn cs) = true
  /\ maps_vars_lt (nxt cs) (a_maps cs) = true /\ pairs_vars_lt (nxt cs) (a_vis cs ++ a_ghost cs) = true
  /\ AP.expr_vars_lt (nxt cs) (a_brk cs) = true /\ fd_vars_lt (nxt cs) (a_fd cs) = true /\ (nx0 <= nxt cs)%nat.
Proof. intros. eapply fresh_ok_parts; try eassumption. Unshelve. all: aps_fill. Qed.

(* [comment removed for export] *)

Lemma find_segment_In : forall segs a n seg, find_segment segs a n = Some seg -> In seg segs.
Proof.
  intros segs a n seg. induction segs as [|s0 rest IH]; cbn [find_segment]; intros H; [discriminate|].
  destruct (Z.leb (Z.of_N (seg_base s0)) a && Z.leb (a + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0)))%bool.
  - injection H as <-. left. reflexivity.
  - right. apply IH. exact H.
Qed.

(* [comment removed for export] *)
Lemma wview_rd1 : forall M (a : word) b,
  wview SEGS M a = Some b ->
  (match M a with Some b0 => Some b0 | None => seg_rom SEGS a end) = Some b.
Proof.
  intros M a b H. unfold wview in H. destruct (M a) as [b0|]; [exact H|].
  unfold seg_rom, memory_read. change (Z.of_N 1) with 1.
  destruct (find_segment SEGS (bv_unsigned a) 1) as [seg|] eqn:Hf; [|discriminate].
  destruct (seg_writable seg) eqn:Hw; [|discriminate].
  rewrite (SEGS_wr seg (find_segment_In _ _ _ _ Hf) Hw).
  change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes]. rewrite H. reflexivity.
Qed.

Lemma store_ok_rdn : forall n M (a : word),
  bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  store_ok SEGS M a n = true ->
  exists bs, rdn SEGS M a n = Some bs /\ length bs = n.
Proof.
  induction n as [|n IH]; intros M a Hnw Hst.
  - exists []. split; reflexivity.
  - cbn [store_ok] in Hst. destruct (wview SEGS M a) as [b|] eqn:Hv; [|discriminate].
    cbn [rdn]. rewrite (wview_rd1 M a b Hv).
    destruct n as [|n'].
    + exists [b]. split; reflexivity.
    + assert (Hu1 : bv_unsigned (a + 1)%bv = bv_unsigned a + 1) by (apply u_add1; lia).
      destruct (IH M (a + 1)%bv ltac:(rewrite Hu1; lia) Hst) as (bs & Hrd & Hlen).
      rewrite Hrd. exists (b :: bs). split; [reflexivity | cbn; lia].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma call_core : forall cs E E' R FULL model T (ret : Z) sr2 k' nx2 regs' MR',
  CSOK E cs R FULL model ->
  fresh_ok nx0 cs = true ->
  env_agree (nxt cs) E E' ->
  msteps SEGS (mkst R (Z_to_bv 64 (pc cs)) (MR E cs model FULL) (seg_rom SEGS))
              (mkst regs' (Z_to_bv 64 ret) MR' (seg_rom SEGS)) ->
  regs_ok E' sr2 regs' ->
  know_ok SEGS E' MR' k' ->
  (forall a : word, in_lfp A (bv_unsigned a) = true -> MR' a = MR E cs model FULL a) ->     (* [comment removed for export] *)
  (forall R' FULL' model',
      CSOK E' (with_ss cs (mk_ss ret sr2 k' nx2)) R' FULL' model' -> m_fs model' = m_fs model ->
      srealizes SEGS (cfg R' ret FULL' model') T) ->
  srealizes SEGS (cfg R (pc cs) FULL model) T.
Proof.
  intros cs E E' R FULL model T ret sr2 k' nx2 regs' MR' HC Hfresh Hag Hms HR' HK' Hlfp Hk.
  destruct (w_fresh_ok_parts cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  set (H := HID E cs model).
  unfold cfg_of.
  apply (srz_msteps_restricted_T SEGS H
           (w_H_off_segments_cs E cs model) SEGS_wx (allowA A E cs)
           (mkst R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS)) (mkst regs' (Z_to_bv 64 ret) MR' (seg_rom SEGS)) model T
           (w_lazy_cover_cs E cs R FULL model HC)
           (w_A_wf_allowA E cs)
           (co_minv _ _ _ _ _ _ _ _ _ _ _ _ HC) (co_halt _ _ _ _ _ _ _ _ _ _ _ _ HC)).
  - rewrite restrict_mkst. exact Hms.
  - intros model' Hinv' Hsame Hclean.
    set (FULL' := munrestrict H FULL MR').
    change (unrestrict H (ms_mem (mkst R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS))) (mkst regs' (Z_to_bv 64 ret) MR' (seg_rom SEGS)))
      with (mkst regs' (Z_to_bv 64 ret) FULL' (seg_rom SEGS)).
    apply (Hk regs' FULL' model').
    + pose proof (w_cs_ok_agree E E' cs R FULL model Hag Hfresh HC) as HC1.
      pose proof (w_hid_agree (nxt cs) E E' cs model Hag Fle Fallow) as HH.
      eapply (w_cs_ok_frame E' cs R FULL model _ regs' FULL' model' HC1 Hsame).
      * rewrite (allowA_agree A (nxt cs) E E' cs Hag Fallow). exact Hinv'.
      * exact HR'.
      * reflexivity.
      * cbn [s_know mk_ss]. unfold Mr. rewrite HH.
        fold H. unfold FULL'. rewrite (mrestrict_munrestrict_clean H FULL MR') by (intros a Ha; exact (Hclean a Ha)).
        exact HK'.
      * intros a Ha. rewrite HH in Ha.
        unfold FULL', munrestrict. fold H in Ha. rewrite Ha. reflexivity.
      * (* [comment removed for export] *)
        intros a Ha. unfold FULL', munrestrict. destruct (H a) eqn:EHa; [reflexivity|].
        rewrite (Hlfp a Ha). unfold Mr, mrestrict. fold H. rewrite EHa. reflexivity.
    + apply (same_but_materialized_frame _ _ Hsame).
Qed.

Lemma sr_vars_lt_fresh : forall rs sr nx b,
  AP.sr_vars_lt b sr = true -> (nx + length rs <= b)%nat -> AP.sr_vars_lt b (sr_fresh sr rs nx) = true.
Proof.
  induction rs as [|r rest IH]; intros sr nx b Hsr Hb; cbn [sr_fresh length] in *; [exact Hsr|].
  apply IH; [|lia]. apply sr_vars_lt_upd; [exact Hsr|]. cbn [AP.expr_vars_lt]. apply Nat.ltb_lt. lia.
Qed.

(* [comment removed for export] *)
Lemma call_node_sound : forall cs cs' E R FULL model T (ret : Z) rv k' regs' MR',
  CSOK E cs R FULL model ->
  after_call nx0 cs ret rv k' = Some cs' ->
  msteps SEGS (mkst R (Z_to_bv 64 (pc cs)) (MR E cs model FULL) (seg_rom SEGS))
              (mkst regs' (Z_to_bv 64 ret) MR' (seg_rom SEGS)) ->
  kept_ok R regs' ->
  match rv with Some e => getr regs' (Z_to_bv 5 10) = edenot E e | None => True end ->
  know_ok SEGS E MR' k' ->
  (forall a : word, in_lfp A (bv_unsigned a) = true -> MR' a = MR E cs model FULL a) ->     (* [comment removed for export] *)
  (forall E' R' FULL' model',
      env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
      srealizes SEGS (cfg R' (pc cs') FULL' model') T) ->
  srealizes SEGS (cfg R (pc cs) FULL model) T.
Proof.
  intros cs cs' E R FULL model T ret rv k' regs' MR' HC Hac Hms Hkept Hrv HK' Hlfp Hk.
  unfold after_call in Hac.
  match type of Hac with context [if ?c then _ else _] => destruct c eqn:Hc; [|discriminate] end.
  apply andb_prop in Hc as [Hc Hrvv]. apply andb_prop in Hc as [Hfresh Hkv].
  injection Hac as <-.
  destruct (w_fresh_ok_parts cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  set (E' := ext_call E (nxt cs) regs').
  pose proof (ext_call_agree E (nxt cs) regs') as Hag. fold E' in Hag.
  eapply (call_core cs E E' R FULL model T ret _ k' _ regs' MR' HC Hfresh Hag Hms).
  - apply (regs_after_call E _ R regs' (nxt cs) rv (co_regs _ _ _ _ _ _ _ _ _ _ _ _ HC) Fsr Hkept).
    destruct rv as [e|]; [split; [exact Hrvv | exact Hrv] | exact I].
  - eapply know_ok_agree'; [exact Hag | exact Hkv | exact HK'].
  - exact Hlfp.
  - intros R' FULL' model' HC' Hfs. apply (Hk E' R' FULL' model'); [| exact HC' | exact Hfs].
    split; [eapply w_env_agree_le; [exact Hag | exact Fle] | exact Hag].
Qed.

(* [comment removed for export] *)
Lemma call_core_H : forall cs E E' R FULL model T (ret : Z) sr2 k' nx2 regs' (H2 : word -> bool) MR',
  CSOK E cs R FULL model ->
  fresh_ok nx0 cs = true ->
  env_agree (nxt cs) E E' ->
  (forall a, H2 a = true -> HID E cs model a = true) ->
  lazy_cover H2 (m_vm_lazy model) (allowA A E cs) ->
  msteps SEGS (mkst R (Z_to_bv 64 (pc cs)) (mrestrict H2 FULL) (seg_rom SEGS))
              (mkst regs' (Z_to_bv 64 ret) MR' (seg_rom SEGS)) ->
  regs_ok E' sr2 regs' ->
  know_ok SEGS E' (mrestrict (HID E cs model) MR') k' ->
  (forall a, HID E cs model a = true -> H2 a = false -> MR' a = FULL a) ->
  (forall a : word, in_lfp A (bv_unsigned a) = true -> H2 a = false -> MR' a = FULL a) ->
  (forall R' FULL' model',
      CSOK E' (with_ss cs (mk_ss ret sr2 k' nx2)) R' FULL' model' -> m_fs model' = m_fs model ->
      srealizes SEGS (cfg R' ret FULL' model') T) ->
  srealizes SEGS (cfg R (pc cs) FULL model) T.
Proof.
  intros cs E E' R FULL model T ret sr2 k' nx2 regs' H2 MR' HC Hfresh Hag Hsub Hlc Hms HR' HK' Hkeep Hlfp Hk.
  destruct (w_fresh_ok_parts cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  assert (HH2 : H_off_segments SEGS H2).
  { intros a Ha. apply (w_H_off_segments_cs E cs model). apply Hsub. exact Ha. }
  unfold cfg_of.
  apply (srz_msteps_restricted_T SEGS H2 HH2 SEGS_wx (allowA A E cs)
           (mkst R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS)) (mkst regs' (Z_to_bv 64 ret) MR' (seg_rom SEGS)) model T
           Hlc (w_A_wf_allowA E cs) (co_minv _ _ _ _ _ _ _ _ _ _ _ _ HC) (co_halt _ _ _ _ _ _ _ _ _ _ _ _ HC)).
  - rewrite restrict_mkst. exact Hms.
  - intros model' Hinv' Hsame Hclean.
    set (FULL' := munrestrict H2 FULL MR').
    change (unrestrict H2 (ms_mem (mkst R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS))) (mkst regs' (Z_to_bv 64 ret) MR' (seg_rom SEGS)))
      with (mkst regs' (Z_to_bv 64 ret) FULL' (seg_rom SEGS)).
    apply (Hk regs' FULL' model').
    + pose proof (w_cs_ok_agree E E' cs R FULL model Hag Hfresh HC) as HC1.
      pose proof (w_hid_agree (nxt cs) E E' cs model Hag Fle Fallow) as HH.
      eapply (w_cs_ok_frame E' cs R FULL model _ regs' FULL' model' HC1 Hsame).
      * rewrite (allowA_agree A (nxt cs) E E' cs Hag Fallow). exact Hinv'.
      * exact HR'.
      * reflexivity.
      * cbn [s_know mk_ss]. unfold Mr. rewrite HH.
        replace (mrestrict (HID E cs model) FULL') with (mrestrict (HID E cs model) MR'); [exact HK'|].
        apply functional_extensionality. intros a. unfold mrestrict, FULL', munrestrict.
        destruct (HID E cs model a) eqn:Hh; [reflexivity|]. destruct (H2 a) eqn:H2a; [|reflexivity].
        pose proof (Hsub a H2a). congruence.
      * intros a Ha. rewrite HH in Ha. unfold FULL', munrestrict. destruct (H2 a) eqn:H2a; [reflexivity|]. exact (Hkeep a Ha H2a).
      * intros a Ha. unfold FULL', munrestrict. destruct (H2 a) eqn:H2a; [reflexivity|]. exact (Hlfp a Ha H2a).
    + apply (same_but_materialized_frame _ _ Hsame).
Qed.

Lemma call_node_sound_H : forall cs cs' E R FULL model T (ret : Z) rv k' regs' (H2 : word -> bool) MR',
  CSOK E cs R FULL model ->
  after_call nx0 cs ret rv k' = Some cs' ->
  (forall a, H2 a = true -> HID E cs model a = true) ->
  lazy_cover H2 (m_vm_lazy model) (allowA A E cs) ->
  msteps SEGS (mkst R (Z_to_bv 64 (pc cs)) (mrestrict H2 FULL) (seg_rom SEGS))
              (mkst regs' (Z_to_bv 64 ret) MR' (seg_rom SEGS)) ->
  kept_ok R regs' ->
  match rv with Some e => getr regs' (Z_to_bv 5 10) = edenot E e | None => True end ->
  know_ok SEGS E (mrestrict (HID E cs model) MR') k' ->
  (forall a, HID E cs model a = true -> H2 a = false -> MR' a = FULL a) ->
  (forall a : word, in_lfp A (bv_unsigned a) = true -> H2 a = false -> MR' a = FULL a) ->
  (forall E' R' FULL' model',
      env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
      srealizes SEGS (cfg R' (pc cs') FULL' model') T) ->
  srealizes SEGS (cfg R (pc cs) FULL model) T.
Proof.
  intros cs cs' E R FULL model T ret rv k' regs' H2 MR' HC Hac Hsub Hlc Hms Hkept Hrv HK' Hkeep Hlfp Hk.
  unfold after_call in Hac.
  match type of Hac with context [if ?c then _ else _] => destruct c eqn:Hc; [|discriminate] end.
  apply andb_prop in Hc as [Hc Hrvv]. apply andb_prop in Hc as [Hfresh Hkv].
  injection Hac as <-.
  destruct (w_fresh_ok_parts cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  set (E' := ext_call E (nxt cs) regs').
  pose proof (ext_call_agree E (nxt cs) regs') as Hag. fold E' in Hag.
  eapply (call_core_H cs E E' R FULL model T ret _ k' _ regs' H2 MR' HC Hfresh Hag Hsub Hlc Hms).
  - apply (regs_after_call E _ R regs' (nxt cs) rv (co_regs _ _ _ _ _ _ _ _ _ _ _ _ HC) Fsr Hkept).
    destruct rv as [e|]; [split; [exact Hrvv | exact Hrv] | exact I].
  - eapply know_ok_agree'; [exact Hag | exact Hkv | exact HK'].
  - exact Hkeep.
  - exact Hlfp.
  - intros R' FULL' model' HC' Hfs. apply (Hk E' R' FULL' model'); [| exact HC' | exact Hfs].
    split; [eapply w_env_agree_le; [exact Hag | exact Fle] | exact Hag].
Qed.

(* [comment removed for export] *)
Definition ext_call2 (E : env) (nx : nat) (R' : bvmap 5 word) (vals : list word) : env :=
  ext_list (ext_call E nx R') (nx + NCS) vals.

Lemma ext_call2_agree : forall E nx R' vals, env_agree nx E (ext_call2 E nx R' vals).
Proof.
  intros E nx R' vals. unfold ext_call2.
  destruct (ext_call_agree E nx R') as [H1 H2]. destruct (ext_list_agree (ext_call E nx R') (nx + NCS) vals) as [H3 H4].
  split; [|rewrite H2; exact H4]. intros n Hn. rewrite H1 by exact Hn. apply H3. lia.
Qed.

Lemma ext_call2_agree16 : forall E nx R' vals, env_agree (nx + NCS) (ext_call E nx R') (ext_call2 E nx R' vals).
Proof. intros. unfold ext_call2. apply ext_list_agree. Qed.

Lemma ext_call2_at : forall E nx R' vals i, (i < length vals)%nat ->
  ev (ext_call2 E nx R' vals) (nx + NCS + i) = nth i vals (Z_to_bv 64 0).
Proof. intros. unfold ext_call2. apply ext_list_at. assumption. Qed.

Lemma call_node_sound2 : forall cs cs' E R FULL model T (ret : Z) rv k' extra vals regs' MR',
  CSOK E cs R FULL model ->
  after_call2 nx0 cs ret rv k' extra = Some cs' ->
  msteps SEGS (mkst R (Z_to_bv 64 (pc cs)) (MR E cs model FULL) (seg_rom SEGS))
              (mkst regs' (Z_to_bv 64 ret) MR' (seg_rom SEGS)) ->
  kept_ok R regs' ->
  match rv with Some e => getr regs' (Z_to_bv 5 10) = edenot E e | None => True end ->
  know_ok SEGS (ext_call2 E (nxt cs) regs' vals) MR' k' ->
  (forall a : word, in_lfp A (bv_unsigned a) = true -> MR' a = MR E cs model FULL a) ->     (* [comment removed for export] *)
  (forall E' R' FULL' model',
      env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
      srealizes SEGS (cfg R' (pc cs') FULL' model') T) ->
  srealizes SEGS (cfg R (pc cs) FULL model) T.
Proof.
  intros cs cs' E R FULL model T ret rv k' extra vals regs' MR' HC Hac Hms Hkept Hrv HK' Hlfp Hk.
  unfold after_call2 in Hac.
  match type of Hac with context [if ?c then _ else _] => destruct c eqn:Hc; [|discriminate] end.
  apply andb_prop in Hc as [Hc Hrvv]. apply andb_prop in Hc as [Hfresh Hkv].
  injection Hac as <-.
  destruct (w_fresh_ok_parts cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  set (E' := ext_call2 E (nxt cs) regs' vals).
  pose proof (ext_call2_agree E (nxt cs) regs' vals) as Hag. fold E' in Hag.
  set (sr1 := sr_fresh (s_regs (a_ss cs)) caller_saved (nxt cs)).
  assert (Hsf : AP.sr_vars_lt (nxt cs + NCS) sr1 = true).
  { subst sr1. apply sr_vars_lt_fresh; [eapply sr_vars_lt_mono; [exact Fsr | lia] | ].
    unfold caller_saved, NCS. cbn [length]. lia. }
  assert (HR2 : regs_ok E' (match rv with Some e => sr_upd sr1 10 e | None => sr1 end) regs').
  { eapply (regs_ok_agree' (nxt cs + NCS)); [apply ext_call2_agree16 | |].
    - destruct rv as [e|]; [|exact Hsf]. apply sr_vars_lt_upd; [exact Hsf|]. eapply expr_vars_lt_mono; [exact Hrvv | unfold nxt, NCS; lia].
    - subst sr1. apply (regs_after_call E _ R regs' (nxt cs) rv (co_regs _ _ _ _ _ _ _ _ _ _ _ _ HC) Fsr Hkept).
      destruct rv as [e|]; [split; [exact Hrvv | exact Hrv] | exact I]. }
  eapply (call_core cs E E' R FULL model T ret _ k' _ regs' MR' HC Hfresh Hag Hms HR2 HK' Hlfp).
  intros R' FULL' model' HC' Hfs. apply (Hk E' R' FULL' model'); [| exact HC' | exact Hfs].
  split; [eapply w_env_agree_le; [exact Hag | exact Fle] | exact Hag].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ret_lit_sound : forall E cs R FULL model r,
  CSOK E cs R FULL model -> ret_lit cs = Some r ->
  getr R (Z_to_bv 5 1) = Z_to_bv 64 r /\ ret_ok (Z_to_bv 64 r) /\ 0 <= r < two64.
Proof.
  intros E cs R FULL model r HC H. unfold ret_lit in H.
  destruct (reg cs 1) as [z| | | | | | |] eqn:Hr; try discriminate.
  destruct (Z.eqb (z mod 2) 0 && Z.ltb z two64 && Z.leb 0 z)%bool eqn:Hc; [|discriminate]. injection H as <-.
  apply andb_prop in Hc as [Hc H0]. apply andb_prop in Hc as [He Hlt].
  apply Z.eqb_eq in He. apply Z.ltb_lt in Hlt. apply Z.leb_le in H0.
  pose proof (w_reg_sound E cs R FULL model 1 HC ltac:(lia)) as R1.
  rewrite Hr in R1. cbn [edenot] in R1.
  split; [exact R1|]. split; [| lia]. apply ret_ok_even. rewrite u64_lit by (unfold two64 in Hlt; lia). exact He.
Qed.


Lemma split_lit_vars : forall e b k m, split_lit e = (b, k) -> AP.expr_vars_lt m e = true -> AP.expr_vars_lt m b = true.
Proof.
  intros e b k m H Hv. unfold split_lit in H.
  destruct e; try (injection H as <- <-; first [exact Hv | reflexivity]).
  lazymatch type of H with (match ?o with _ => _ end) = _ => destruct o end; try (injection H as <- <-; exact Hv).
  lazymatch type of H with (match ?y with _ => _ end) = _ => destruct y end; try (injection H as <- <-; exact Hv).
  injection H as <- <-. cbn [AP.expr_vars_lt] in Hv. apply andb_prop in Hv as [Hv _]. exact Hv.
Qed.

Lemma nth_map_seq : forall {T} (f : nat -> T) W i d, (i < W)%nat -> nth i (map f (seq 0 W)) d = f i.
Proof.
  intros T f W i d Hi. rewrite (nth_indep _ d (f 0%nat)) by (rewrite length_map, length_seq; exact Hi).
  rewrite map_nth. rewrite seq_nth by exact Hi. reflexivity.
Qed.

Lemma nth_repeat_lt : forall {T} (a d : T) m j, (j < m)%nat -> nth j (repeat a m) d = a.
Proof. intros T a d m. induction m as [|m IH]; intros j Hj; [lia|]. destruct j; [reflexivity|]. cbn. apply IH. lia. Qed.

(* [comment removed for export] *)
Lemma k0_sound : forall E M k db dk ne dst k0,
  know_ok SEGS E M k ->
  (if off_image_x A k db dk ne then Some k
   else match dst, ne with ELit d, ELit n => Some (kimg_cut k (d mod two64) n) | _, _ => None end) = Some k0 ->
  know_ok SEGS E M k0.
Proof.
  intros E M k db dk ne dst k0 HK H.
  destruct (off_image_x A k db dk ne); [injection H as <-; exact HK|].
  destruct dst; try discriminate. destruct ne; try discriminate. injection H as <-.
  apply kimg_cut_sound. exact HK.
Qed.

(* [comment removed for export] *)
Lemma wbytes_fill_at : forall M (s : word) b n i,
  bv_unsigned s + n <= 2 ^ 64 -> 0 <= i < n ->
  wbytes M s (repeat b (Z.to_nat n)) (Z_to_bv 64 (bv_unsigned s + i)) = Some b.
Proof.
  intros M s b n i Hnw Hi.
  replace i with (Z.of_nat (Z.to_nat i)) by lia.
  rewrite wbytes_nth by (rewrite repeat_length; lia). f_equal. apply nth_repeat_lt. lia.
Qed.

Lemma Z_to_bv8_mod : forall c, Z_to_bv 8 (c mod 256) = Z_to_bv 8 c.
Proof.
  intros c. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  apply Z.mod_mod. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma wbytes_lfp : forall E M k db dk ne bs (s : word),
  know_ok SEGS E M k -> kwritable_x A k k db dk ne = true ->
  bv_unsigned s = estart E (SA db dk) -> Z.of_nat (length bs) <= elenZ E ne ->
  forall a : word, in_lfp A (bv_unsigned a) = true -> wbytes M s bs a = M a.
Proof.
  intros E M k db dk ne bs s HK Hwr Hs Hlen a Ha.
  destruct (kwritable_x_sound SEGS A E M k k db dk ne HK HK Hwr) as (_ & Wlo & Whi).
  destruct (kwritable_x_lfp SEGS A E M k k db dk ne HK Hwr (bv_unsigned a) Ha) as [X|X]; apply wbytes_out; lia.
Qed.
Lemma wbytes_lfp_lit : forall E M k db dk n bs (s : word),
  know_ok SEGS E M k -> kwritable A k k db dk n = true -> 0 <= n ->
  estart E (SA db dk) <= bv_unsigned s -> bv_unsigned s + Z.of_nat (length bs) <= estart E (SA db dk) + n ->
  forall a : word, in_lfp A (bv_unsigned a) = true -> wbytes M s bs a = M a.
Proof.
  intros E M k db dk n bs s HK Hwr Hn Hs Hlen a Ha.
  destruct (kwritable_sound SEGS A E M k k db dk n HK HK Hwr Hn) as (_ & Wlo & Whi).
  destruct (kwritable_lfp SEGS A E M k k db dk n HK Hwr (bv_unsigned a) Ha) as [X|X]; apply wbytes_out; lia.
Qed.

Lemma summary_fill_sound : forall entry cmax,
  fill_spec SEGS entry cmax ->
  node1_stmt SEGS A nx0 LIMIT SINV argH LINV FS0 always (fun cs => summary_fill A nx0 cs entry cmax).
Proof.
  intros entry cmax SUM cs cs' E R FULL model T HC _ Hn Hk.
  pose proof HC as HKN. apply co_know in HKN.
  set (M := MR E cs model FULL) in *.
  rewrite summary_fill_eq in Hn. (* [comment removed for export] *) unfold summary_fill_ref in Hn.
  destruct (Z.eqb (pc cs) entry) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
  destruct (ret_lit cs) as [ret|] eqn:Hret; [|discriminate].
  destruct (reg_lit cs 11) as [c|] eqn:H11; [|discriminate].
  destruct (Z.ltb c cmax) eqn:Hcm; [|discriminate]. cbn [negb] in Hn. apply Z.ltb_lt in Hcm.
  destruct (split_lit (reg cs 10)) as [db dk] eqn:Hspl.
  destruct (xlo (kn cs) (reg cs 12)) as [nlo|] eqn:Hnlo; [|discriminate].
  destruct (xhi (kn cs) (reg cs 12)) as [nhi|] eqn:Hnhi; [|discriminate].
  destruct (xhi (kn cs) (reg cs 10)) as [dhi|] eqn:Hdhi; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  apply andb_prop in Hcond as [Hcond Hb]. apply andb_prop in Hcond as [Hn0 Hn40].
  apply Z.leb_le in Hn0. apply Z.leb_le in Hn40. apply Z.ltb_lt in Hb. unfold two64 in Hb.
  (* [comment removed for export] *)
  destruct (ret_lit_sound E cs R FULL model ret HC Hret) as (R1 & Hrok & Hretr).
  destruct (w_reg_lit_sound E cs R FULL model 11 c HC ltac:(lia) H11) as [R11 Hc].
  pose proof (w_reg_sound E cs R FULL model 10 HC ltac:(lia)) as R10.
  pose proof (w_reg_sound E cs R FULL model 12 HC ltac:(lia)) as R12.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hnlo) as Hnlo'.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hnhi) as Hnhi'.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hdhi) as Hdhi'.
  set (s := edenot E (reg cs 10)) in *. set (nw := edenot E (reg cs 12)) in *. set (n := bv_unsigned nw) in *.
  pose proof (u64_range nw) as Hnr. fold n in Hnr.
  assert (Hnwn : Z_to_bv 64 n = nw) by (apply Z_to_bv_bv_unsigned).
  pose proof (w_split_lit_denot E (reg cs 10) db dk Hspl) as Hsd. fold s in Hsd.
  assert (Hse : Z_to_bv 64 (estart E (SA db dk)) = s) by (rewrite Hsd; reflexivity).
  assert (Hlen : elenZ E (reg cs 12) = n) by reflexivity.
  (* [comment removed for export] *)
  assert (FIN : forall k',
     store_ok SEGS M s (Z.to_nat n) = true ->
     know_ok SEGS E (wbytes M s (repeat (Z_to_bv 8 c) (Z.to_nat n))) k' ->
     after_call nx0 cs ret (Some (reg cs 10)) k' = Some cs' ->
     (forall a : word, in_lfp A (bv_unsigned a) = true -> wbytes M s (repeat (Z_to_bv 8 c) (Z.to_nat n)) a = M a) ->
     srealizes SEGS (cfg R (pc cs) FULL model) T).
  { intros k' Hst HK' Hac HLF.
    destruct (SUM M s (Z_to_bv 64 c) n R (Z_to_bv 64 ret) ltac:(lia) ltac:(lia) Hst
                 ltac:(rewrite u64_lit by (unfold two64 in Hc; lia); lia) Hrok R1 R10 R11 ltac:(rewrite Hnwn; exact R12))
      as (regs' & Hms & Hkept & Ha0).
    rewrite (u64_lit c) in Hms by (unfold two64 in Hc; lia).
    eapply (call_node_sound cs cs' E R FULL model T ret (Some (reg cs 10)) k' regs' _ HC Hac).
    - rewrite Hpc. exact Hms.
    - exact Hkept.
    - exact Ha0.
    - exact HK'.
    - exact HLF.
    - exact Hk. }
  assert (ST0 : n = 0 -> store_ok SEGS M s (Z.to_nat n) = true) by (intros ->; reflexivity).
  assert (WB0 : n = 0 -> wbytes M s (repeat (Z_to_bv 8 c) (Z.to_nat n)) = M) by (intros ->; reflexivity).
  (* [comment removed for export] *)
  destruct (Z.eqb nhi 0) eqn:Hnhi0.
  { apply Z.eqb_eq in Hnhi0. assert (Hz : n = 0) by lia.
    apply (FIN (kn cs)); [exact (ST0 Hz) | rewrite (WB0 Hz); exact HKN | exact Hn | intros a _; rewrite (WB0 Hz); reflexivity]. }
  (* [comment removed for export] *)
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hzb end.
  { apply andb_prop in Hzb as [Hzb Hwr]. apply andb_prop in Hzb as [Hc8 Hkz]. apply Z.eqb_eq in Hc8.
    destruct (kwritable_x_sound SEGS A E M (kn cs) (kn cs) db dk (reg cs 12) HKN HKN Hwr) as (Wst & Wlo & Whi).
    destruct (kzero_x_sound SEGS E M (kn cs) (kn cs) db dk (reg cs 12) HKN HKN Hkz) as (Zb & _ & _).
    rewrite Hse, Hlen in *.
    apply (FIN (kn cs)); [apply Wst; lia | | exact Hn |].
    2:{ destruct (Z.eq_dec n 0) as [Hz|Hnz]; [intros a _; rewrite (WB0 Hz); reflexivity|].
        eapply (wbytes_lfp E M (kn cs) db dk (reg cs 12)); [exact HKN | exact Hwr | rewrite <- Hse; apply u64_lit; lia | rewrite repeat_length, Hlen; lia]. }
    destruct (Z.eq_dec n 0) as [Hz|Hnz]; [rewrite (WB0 Hz); exact HKN|].
    assert (Hus : bv_unsigned s = estart E (SA db dk)) by (rewrite <- Hse; apply u64_lit; lia).
    rewrite wbytes_same; [exact HKN | rewrite repeat_length; lia |].
    intros j Hj. rewrite repeat_length in Hj. rewrite nth_repeat_lt by exact Hj.
    rewrite Hus. rewrite Zb by lia. rewrite <- (Z_to_bv8_mod c), Hc8. reflexivity. }
  clear Hzb.
  (* [comment removed for export] *)
  match type of Hn with (match ?o with _ => _ end) = _ => destruct o as [k0|] eqn:Hk0; [|discriminate] end.
  pose proof (k0_sound E M (kn cs) db dk (reg cs 12) (reg cs 10) k0 HKN Hk0) as HK0.
  destruct (kwritable_x A (kn cs) (kn cs) db dk (reg cs 12)) eqn:Hwr; [|discriminate].
  destruct (kwritable_x_sound SEGS A E M (kn cs) (kn cs) db dk (reg cs 12) HKN HKN Hwr) as (Wst & Wlo & Whi).
  rewrite Hse, Hlen in *.
  eapply FIN; [apply Wst; lia | | exact Hn |].
  2:{ destruct (Z.eq_dec n 0) as [Hz|Hnz]; [intros a _; rewrite (WB0 Hz); reflexivity|].
      eapply (wbytes_lfp E M (kn cs) db dk (reg cs 12)); [exact HKN | exact Hwr | rewrite <- Hse; apply u64_lit; lia | rewrite repeat_length, Hlen; lia]. }
  set (M' := wbytes M s (repeat (Z_to_bv 8 c) (Z.to_nat n))).
  assert (HK1 : know_ok SEGS E M' (kn_havoc k0 db dk (reg cs 12))).
  { eapply w_know_ok_havoc; [exact HK0 | | apply wbytes_grows].
    intros x Hx. rewrite Hlen in Hx. destruct (Z.eq_dec n 0) as [Hz|Hnz]; [subst M'; rewrite (WB0 Hz); reflexivity|].
    assert (Hus : bv_unsigned s = estart E (SA db dk)) by (rewrite <- Hse; apply u64_lit; lia).
    subst M'. apply wbytes_out; rewrite repeat_length; lia. }
  destruct (Z.ltb 0 nlo) eqn:Hpos; [|exact HK1]. apply Z.ltb_lt in Hpos.
  assert (Hus : bv_unsigned s = estart E (SA db dk)) by (rewrite <- Hse; apply u64_lit; lia).
  assert (FILL : forall i, 0 <= i < n -> M' (Z_to_bv 64 (estart E (SA db dk) + i)) = Some (Z_to_bv 8 c)).
  { intros i Hi. subst M'. rewrite <- Hus. apply wbytes_fill_at; lia. }
  constructor; [|exact HK1].
  destruct (Z.eqb (c mod 256) 0) eqn:Hc8; cbn [kentry_ok]; rewrite Hlen.
  - apply Z.eqb_eq in Hc8. split; [unfold flat; lia|]. intros i Hi. rewrite (FILL i Hi). rewrite <- (Z_to_bv8_mod c), Hc8. reflexivity.
  - split; [unfold flat; lia|]. intros i Hi. rewrite (FILL i Hi). rewrite Z_to_bv8_mod. reflexivity.
Qed.

(* [comment removed for export] *)

Lemma store_ok_sub : forall M (a : word) n (b : word) m,
  bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  store_ok SEGS M a n = true ->
  bv_unsigned a <= bv_unsigned b -> bv_unsigned b + Z.of_nat m <= bv_unsigned a + Z.of_nat n ->
  store_ok SEGS M b m = true.
Proof.
  intros M a n b m Hnw Hst Hlo Hhi. apply store_ok_of_all; [lia|].
  intros x Hx. eapply (store_ok_all SEGS M n a Hnw Hst). lia.
Qed.

Lemma summary_miz_sound :
  miz_spec SEGS (x_memiszero A) ->
  node1_stmt SEGS A nx0 LIMIT SINV argH LINV FS0 always (fun cs => summary_miz A nx0 cs).
Proof.
  intros SUM cs cs' E R FULL model T HC _ Hn Hk.
  pose proof HC as HKN. apply co_know in HKN.
  set (M := MR E cs model FULL) in *.
  rewrite summary_miz_eq in Hn. (* [comment removed for export] *) unfold summary_miz_ref in Hn.
  destruct (Z.eqb (pc cs) (x_memiszero A)) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
  destruct (ret_lit cs) as [ret|] eqn:Hret; [|discriminate].
  destruct (split_lit (reg cs 10)) as [bb bk] eqn:Hsb.
  destruct (split_lit (eaddz (reg cs 2) (-16))) as [qb qk] eqn:Hsq.
  destruct (xlo (kn cs) (reg cs 11)) as [nlo|] eqn:Hnlo; [|discriminate].
  destruct (xhi (kn cs) (reg cs 11)) as [nhi|] eqn:Hnhi; [|discriminate].
  destruct (xhi (kn cs) (reg cs 10)) as [bhi|] eqn:Hbhi; [|discriminate].
  destruct (xlo (kn cs) (reg cs 2)) as [splo|] eqn:Hsplo; [|discriminate].
  destruct (xhi (kn cs) (reg cs 2)) as [sphi|] eqn:Hsphi; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  apply andb_prop in Hcond as [Hcond Hkz]. apply andb_prop in Hcond as [Hcond Hap].
  apply andb_prop in Hcond as [Hcond Hwr]. apply andb_prop in Hcond as [Hcond Hsphi'].
  apply andb_prop in Hcond as [Hcond Hsplo']. apply andb_prop in Hcond as [Hcond Hb8].
  apply andb_prop in Hcond as [Hn0 Hn40].
  apply Z.leb_le in Hn0. apply Z.leb_le in Hn40. apply Z.leb_le in Hb8. apply Z.leb_le in Hsplo'. apply Z.ltb_lt in Hsphi'.
  unfold two64 in Hb8, Hsphi'.
  (* [comment removed for export] *)
  destruct (ret_lit_sound E cs R FULL model ret HC Hret) as (R1 & Hrok & Hretr).
  pose proof (w_reg_sound E cs R FULL model 2 HC ltac:(lia)) as R2.
  pose proof (w_reg_sound E cs R FULL model 10 HC ltac:(lia)) as R10.
  pose proof (w_reg_sound E cs R FULL model 11 HC ltac:(lia)) as R11.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hnlo) as Hnlo2.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hnhi) as Hnhi2.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hbhi) as Hbhi2.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hsplo) as Hsplo2.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hsphi) as Hsphi2.
  set (beg := edenot E (reg cs 10)) in *. set (spw := edenot E (reg cs 2)) in *.
  set (nw := edenot E (reg cs 11)) in *. set (N := bv_unsigned nw) in *.
  pose proof (u64_range nw) as Hnr. fold N in Hnr. pose proof (u64_range beg) as Hbr. pose proof (u64_range spw) as Hsr.
  assert (HnwN : Z_to_bv 64 N = nw) by (apply Z_to_bv_bv_unsigned).
  assert (HlenN : elenZ E (reg cs 11) = N) by reflexivity.
  (* [comment removed for export] *)
  pose proof (w_split_lit_denot E _ qb qk Hsq) as Hq.
  unfold eaddz in Hq. rewrite mkAlu_denot, alu_add in Hq. cbn [edenot] in Hq. fold spw in Hq. unfold v_add in Hq.
  destruct (kwritable_sound SEGS A E M (kn cs) (kn cs) qb qk 16 HKN HKN Hwr ltac:(lia)) as (Qst & Qlo & Qhi).
  set (Q := estart E (SA qb qk)) in *.
  assert (HQ : Q = bv_unsigned spw - 16).
  { apply (f_equal bv_unsigned) in Hq. rewrite !u_lit64 in Hq. unfold two64 in Hq.
    change (estart E (SA qb qk)) with Q in Hq.
    rewrite (Z.mod_small Q) in Hq by lia.
    rewrite <- Hq.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
  assert (Hstk : store_ok SEGS M (Z_to_bv 64 (bv_unsigned spw - 8)) 8 = true).
  { apply (store_ok_sub M (Z_to_bv 64 Q) 16); rewrite ?u64_lit by lia; try lia. exact Qst. }
  (* [comment removed for export] *)
  pose proof (w_split_lit_denot E (reg cs 10) bb bk Hsb) as Hbeg. fold beg in Hbeg.
  destruct (kzero_x_sound SEGS E M (kn cs) (kn cs) bb bk (reg cs 11) HKN HKN Hkz) as (Zb & Blo & Bhi).
  rewrite HlenN in Zb, Bhi.
  pose proof (ranges_apart_x_sound SEGS E M (kn cs) qb qk (ELit 16) bb bk (reg cs 11) HKN Hap) as Hapart.
  rewrite HlenN in Hapart. change (estart E (SA qb qk)) with Q in Hapart.
  replace (elenZ E (ELit 16)) with 16 in Hapart by (unfold elenZ; cbn [edenot]; rewrite u64_lit by lia; reflexivity).
  set (B := estart E (SA bb bk)) in *.
  assert (HuB : bv_unsigned beg = B \/ (B = 2 ^ 64 /\ bv_unsigned beg = 0)).
  { destruct (Z.eq_dec B (2 ^ 64)) as [HB|HB].
    - right. split; [exact HB|]. rewrite Hbeg. change (bv_unsigned (edenot E bb) + bk) with B. rewrite HB. reflexivity.
    - left. rewrite Hbeg. apply u64_lit. lia. }
  assert (Hdisj : bv_unsigned beg + N <= bv_unsigned spw - 8 \/ bv_unsigned spw <= bv_unsigned beg) by lia.
  assert (Hz : forall a : word, bv_unsigned beg <= bv_unsigned a < bv_unsigned beg + N ->
                 rdn SEGS M a 1 = Some [Z_to_bv 8 0]).
  { intros a Ha. apply rdn1_overlay.
    destruct HuB as [HuB|[HB Hu0]]; [|lia].
    replace a with (Z_to_bv 64 (B + (bv_unsigned a - B))) by (rewrite <- (Z_to_bv_bv_unsigned 64 a) at 2; f_equal; lia).
    apply Zb. lia. }
  destruct (SUM M beg spw N R (Z_to_bv 64 ret) ltac:(lia) ltac:(lia) ltac:(lia) Hstk Hdisj Hz Hrok R1 R2 R10
               ltac:(rewrite HnwN; exact R11)) as (regs' & Hms & Hkept & Ha0).
  eapply (call_node_sound cs cs' E R FULL model T ret (Some (ELit 1)) _ regs' _ HC Hn).
  - rewrite Hpc. exact Hms.
  - exact Hkept.
  - exact Ha0.
  - eapply w_know_ok_havoc; [exact HKN | | apply wbytes_grows].
    intros x Hx. change (estart E (SA qb qk)) with Q in Hx.
    replace (elenZ E (ELit 16)) with 16 in Hx by (unfold elenZ; cbn [edenot]; rewrite u64_lit by lia; reflexivity).
    apply wbytes_out; rewrite length_N_to_le_bytes, u64_lit by lia; lia.
  - (* [comment removed for export] *)
    eapply (wbytes_lfp_lit E M (kn cs) qb qk 16); [exact HKN | exact Hwr | lia | |];
      change (estart E (SA qb qk)) with Q; rewrite ?length_N_to_le_bytes, u64_lit by lia; lia.
  - exact Hk.
Qed.

(* [comment removed for export] *)

Lemma summary_copy_sound : forall entry,
  copy_spec SEGS entry ->
  node1_stmt SEGS A nx0 LIMIT SINV argH LINV FS0 always (fun cs => summary_copy SEGS A nx0 cs entry).
Proof.
  intros entry SUM cs cs' E R FULL model T HC _ Hn Hk.
  pose proof HC as HKN. apply co_know in HKN.
  set (M := MR E cs model FULL) in *.
  rewrite summary_copy_eq in Hn. (* [comment removed for export] *) unfold summary_copy_ref in Hn.
  destruct (Z.eqb (pc cs) entry) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
  destruct (ret_lit cs) as [ret|] eqn:Hret; [|discriminate].
  pose proof (w_reg_sound E cs R FULL model 12 HC ltac:(lia)) as R12.
  remember (reg cs 12) as ne eqn:Hne.
  destruct (split_lit (reg cs 10)) as [db dk] eqn:Hspd.
  destruct (split_lit (reg cs 11)) as [sb sk] eqn:Hsps.
  destruct (xlo (kn cs) ne) as [nlo|] eqn:Hnlo; [|discriminate].
  destruct (xhi (kn cs) ne) as [nhi|] eqn:Hnhi; [|discriminate].
  destruct (xhi (kn cs) (reg cs 10)) as [dhi|] eqn:Hdhi; [|discriminate].
  destruct (xhi (kn cs) (reg cs 11)) as [shi|] eqn:Hshi; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  apply andb_prop in Hcond as [Hcond Hb2]. apply andb_prop in Hcond as [Hcond Hb1]. apply andb_prop in Hcond as [Hn0 Hn40].
  apply Z.leb_le in Hn0. apply Z.leb_le in Hn40. apply Z.ltb_lt in Hb1. apply Z.ltb_lt in Hb2. unfold two64 in Hb1, Hb2.
  (* [comment removed for export] *)
  destruct (ret_lit_sound E cs R FULL model ret HC Hret) as (R1 & Hrok & Hretr).
  pose proof (w_reg_sound E cs R FULL model 10 HC ltac:(lia)) as R10.
  pose proof (w_reg_sound E cs R FULL model 11 HC ltac:(lia)) as R11.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hnlo) as Hnlo2.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hnhi) as Hnhi2.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hdhi) as Hdhi2.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hshi) as Hshi2.
  set (s := edenot E (reg cs 10)) in *. set (sr := edenot E (reg cs 11)) in *.
  set (nw := edenot E ne) in *. set (n := bv_unsigned nw) in *.
  pose proof (u64_range nw) as Hnr. fold n in Hnr. pose proof (u64_range s) as Hsr0. pose proof (u64_range sr) as Hsr1.
  assert (Hnwn : Z_to_bv 64 n = nw) by (apply Z_to_bv_bv_unsigned).
  pose proof (w_split_lit_denot E (reg cs 10) db dk Hspd) as Hsd. fold s in Hsd.
  pose proof (w_split_lit_denot E (reg cs 11) sb sk Hsps) as Hss. fold sr in Hss.
  assert (Hse : Z_to_bv 64 (estart E (SA db dk)) = s) by (rewrite Hsd; reflexivity).
  assert (Hsre : Z_to_bv 64 (estart E (SA sb sk)) = sr) by (rewrite Hss; reflexivity).
  assert (Hlen : elenZ E ne = n) by reflexivity.
  (* [comment removed for export] *)
  assert (FIN : forall k' bs,
     length bs = Z.to_nat n ->
     rdn SEGS M sr (length bs) = Some bs ->
     store_ok SEGS M s (length bs) = true ->
     (bv_unsigned s + n <= bv_unsigned sr \/ bv_unsigned sr + n <= bv_unsigned s) ->
     know_ok SEGS E (wbytes M s bs) k' ->
     after_call nx0 cs ret (Some (reg cs 10)) k' = Some cs' ->
     (forall a : word, in_lfp A (bv_unsigned a) = true -> wbytes M s bs a = M a) ->
     srealizes SEGS (cfg R (pc cs) FULL model) T).
  { intros k' bs Hlbs Hrd Hst Hdisj HK' Hac HLF.
    destruct (SUM M s sr n bs R (Z_to_bv 64 ret) ltac:(lia) Hlbs Hrd Hst Hdisj ltac:(lia) ltac:(lia) Hrok R1 R10 R11
                 ltac:(rewrite Hnwn; exact R12)) as (regs' & Hms & Hkept & Ha0).
    eapply (call_node_sound cs cs' E R FULL model T ret (Some (reg cs 10)) k' regs' _ HC Hac).
    - rewrite Hpc. exact Hms.
    - exact Hkept.
    - exact Ha0.
    - exact HK'.
    - exact HLF.
    - exact Hk. }
  (* [comment removed for export] *)
  destruct (Z.eqb nhi 0) eqn:Hnhi0.
  { apply Z.eqb_eq in Hnhi0. assert (Hz : n = 0) by lia.
    apply (FIN (kn cs) []); [rewrite Hz; reflexivity | reflexivity | reflexivity | lia | cbn [wbytes]; exact HKN | exact Hn | intros a _; reflexivity]. }
  match type of Hn with (match ?o with _ => _ end) = _ => destruct o as [k0|] eqn:Hk0; [|discriminate] end.
  pose proof (k0_sound E M (kn cs) db dk ne (reg cs 10) k0 HKN Hk0) as HK0.
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hwa; [|discriminate] end.
  apply andb_prop in Hwa as [Hwr Hap].
  destruct (kwritable_x_sound SEGS A E M (kn cs) (kn cs) db dk ne HKN HKN Hwr) as (Wst & Wlo & Whi).
  pose proof (ranges_apart_x_sound SEGS E M (kn cs) db dk ne sb sk ne HKN Hap) as Hapart.
  rewrite Hlen in *.
  set (D := estart E (SA db dk)) in *. set (S := estart E (SA sb sk)) in *.
  rewrite Hse in Wst.
  (* [comment removed for export] *)
  assert (HAVOC : forall bs, length bs = Z.to_nat n -> 0 < n ->
            know_ok SEGS E (wbytes M s bs) (kn_havoc k0 db dk ne)).
  { intros bs Hlbs Hpos.
    assert (Hus : bv_unsigned s = D) by (rewrite <- Hse; apply u64_lit; lia).
    eapply w_know_ok_havoc; [exact HK0 | | apply wbytes_grows].
    intros x Hx. rewrite Hlen in Hx. change (estart E (SA db dk)) with D in Hx.
    apply wbytes_out; rewrite Hlbs; lia. }
  (* [comment removed for export] *)
  assert (HusD : 0 < n -> 0 <= S -> S + n <= 2 ^ 64 -> bv_unsigned s = D /\ bv_unsigned sr = S).
  { intros Hpos Slo Shi. split; [rewrite <- Hse | rewrite <- Hsre]; apply u64_lit; lia. }
  (* [comment removed for export] *)
  assert (VARS : fresh_ok nx0 cs = true ->
            AP.kn_vars_lt (nxt cs) (kn cs) = true /\ AP.expr_vars_lt (nxt cs) db = true /\ AP.expr_vars_lt (nxt cs) ne = true
            /\ AP.sr_vars_lt (nxt cs) (s_regs (a_ss cs)) = true).
  { intros Hfresh. destruct (w_fresh_ok_parts cs Hfresh) as (Fsr & Fkn & _).
    split; [exact Fkn|]. split; [| split; [rewrite Hne; unfold reg; apply nth_sr_vars_lt'; [exact Fsr | lia] | exact Fsr]].
    eapply split_lit_vars; [exact Hspd|]. unfold reg. apply nth_sr_vars_lt'; [exact Fsr | lia]. }
  (* [comment removed for export] *)
  assert (GEN : kwritable_x A (kn cs) (kn cs) sb sk ne = true -> flat_x (kn cs) sb sk ne = true ->
    forall (W : nat) (u : bool), 8 * Z.of_nat W <= n -> (u = true -> 0 < n) ->
    after_call2 nx0 cs ret (Some (reg cs 10))
      (map (fun i : nat => KWord (SA db (dk + 8 * Z.of_nat i)) 8 (EVar (nxt cs + NCS + i))) (seq 0 W)
       ++ kblob_prefix (kn cs) sb sk db dk nlo ne ++ (if u then KUnk (SA db dk) ne :: kn_havoc k0 db dk ne else kn_havoc k0 db dk ne)) W
      = Some cs' ->
    srealizes SEGS (cfg R (pc cs) FULL model) T).
  { intros Hswr Hsfl W u HW Hu Hac.
    destruct (kwritable_x_sound SEGS A E M (kn cs) (kn cs) sb sk ne HKN HKN Hswr) as (SWst & Slo & Shi).
    destruct (w_flat_x_sound E M (kn cs) sb sk ne HKN Hsfl) as (_ & _ & Spos).
    rewrite Hlen in SWst, Shi. change (bv_unsigned (edenot E ne)) with n in Spos.
    change (estart E (SA sb sk)) with S in SWst, Slo, Shi. rewrite Hsre in SWst.
    destruct (HusD Spos Slo Shi) as [Hus Husr].
    destruct (store_ok_rdn (Z.to_nat n) M sr ltac:(lia) (SWst (Z.to_nat n) ltac:(lia))) as (bs & Hrd & Hlbs).
    assert (Hfresh : fresh_ok nx0 cs = true).
    { unfold after_call2 in Hac. destruct (fresh_ok nx0 cs); [reflexivity | cbn [andb] in Hac; discriminate]. }
    destruct (VARS Hfresh) as (Fkn & Fdb & Fne & Fsr).
    destruct (SUM M s sr n bs R (Z_to_bv 64 ret) ltac:(lia) Hlbs ltac:(rewrite Hlbs; exact Hrd)
                 ltac:(rewrite Hlbs; apply Wst; lia) ltac:(lia) ltac:(lia) ltac:(lia) Hrok R1 R10 R11
                 ltac:(rewrite Hnwn; exact R12)) as (regs' & Hms & Hkept & Ha0).
    set (vals := map (fun i : nat => Z_to_bv 64 (bytes_le_to_Z (firstn 8 (skipn (8 * i) bs)))) (seq 0 W)).
    eapply (call_node_sound2 cs cs' E R FULL model T ret (Some (reg cs 10)) _ W vals regs' (wbytes M s bs) HC Hac).
    - rewrite Hpc. exact Hms.
    - exact Hkept.
    - exact Ha0.
    - set (E2 := ext_call2 E (nxt cs) regs' vals).
      pose proof (ext_call2_agree E (nxt cs) regs' vals) as Hag2. fold E2 in Hag2.
      assert (Edb : edenot E2 db = edenot E db) by (symmetry; eapply edenot_agree'; [exact Hag2 | exact Fdb]).
      assert (Ene : edenot E2 ne = edenot E ne) by (symmetry; eapply edenot_agree'; [exact Hag2 | exact Fne]).
      assert (ED2 : estart E2 (SA db dk) = D) by (unfold estart; cbn [a_base a_off]; rewrite Edb; reflexivity).
      assert (EL2 : elenZ E2 ne = n) by (unfold elenZ; rewrite Ene; reflexivity).
      pose proof (rdn_wbytes_hit SEGS bs M s ltac:(rewrite Hlbs; lia)) as Hhit.
      apply Forall_app. split.
      + (* [comment removed for export] *)
        apply Forall_forall. intros K HinK. apply in_map_iff in HinK as (i & <- & Hini). apply in_seq in Hini.
        assert (EDi : estart E2 (SA db (dk + 8 * Z.of_nat i)) = D + 8 * Z.of_nat i).
        { unfold estart. cbn [a_base a_off]. rewrite Edb. change (estart E (SA db dk)) with (bv_unsigned (edenot E db) + dk) in *. unfold D. unfold estart. cbn [a_base a_off]. lia. }
        cbn [kentry_ok]. split; [lia|]. split; [unfold flat; rewrite EDi; lia|].
        rewrite adenot_SA, EDi. cbn [edenot]. unfold E2. rewrite ext_call2_at by (subst vals; rewrite length_map, length_seq; lia).
        subst vals. rewrite (nth_map_seq _ W i (Z_to_bv 64 0)) by lia.
        assert (Hpiece : length (firstn 8 (skipn (8 * i) bs)) = 8%nat) by (rewrite length_firstn, length_skipn; lia).
        rewrite (word_to_le_bytes_of_bytes_n 8 _ Hpiece) by lia.
        pose proof (rdn_skipn SEGS (wbytes M s bs) (length bs) s bs (8 * i) Hhit ltac:(lia)) as Sk.
        pose proof (rdn_firstn SEGS (wbytes M s bs) (length bs - 8 * i) _ _ 8 Sk ltac:(lia)) as Fi.
        replace (Z_to_bv 64 (D + 8 * Z.of_nat i)) with (s + nat_to_word (8 * i))%bv; [exact Fi|].
        apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod, Hus.
        rewrite (Z.mod_small (Z.of_nat (8 * i))) by lia. f_equal. lia.
      + apply Forall_app. split.
        { (* [comment removed for export] *)
          unfold kblob_prefix.
          destruct (List.find _ (kn cs)) as [K|] eqn:HF; [|constructor].
          apply find_some in HF as [HinK HKt].
          destruct K as [| |[kb ko] nb j| | | | | | |]; try (now constructor).
          apply andb_prop in HKt as [HKt Hnb]. apply andb_prop in HKt as [Hkb Hko].
          apply expr_eqb_eq in Hkb. apply Z.eqb_eq in Hko. subst kb ko.
          pose proof (proj1 (Forall_forall _ _) HKN _ HinK) as HKB. cbn [kentry_ok] in HKB.
          set (m := elenZ E nb).
          (* [comment removed for export] *)
          assert (Hm : 0 <= m <= n).
          { unfold kblob_len_ok in Hnb. apply Bool.orb_prop in Hnb as [Hlit | Heq].
            - destruct nb as [n0| | | | | | |]; try discriminate Hlit.
              apply andb_prop in Hlit as [Hn0pos Hn0le]. apply Z.ltb_lt in Hn0pos. apply Z.leb_le in Hn0le.
              subst m. unfold elenZ. rewrite edenot_lit, u64_lit by lia. lia.
            - apply expr_eqb_eq in Heq. subst nb. subst m. rewrite Hlen. lia. }
          (* [comment removed for export] *)
          assert (Fnb : AP.expr_vars_lt (nxt cs) nb = true).
          { assert (GEN : forall kk, AP.kn_vars_lt (nxt cs) kk = true -> In (KBlob (SA sb sk) nb j) kk -> AP.expr_vars_lt (nxt cs) nb = true).
            { induction kk as [|K0 kk IH]; [intros _ []|]. cbn [AP.kn_vars_lt]. intros Hkk [->|Hin].
              - apply andb_prop in Hkk as [HKfirst _]. cbn [AP.kentry_vars_lt] in HKfirst. apply andb_prop in HKfirst as [_ Hx]. exact Hx.
              - apply andb_prop in Hkk as [_ Hkk']. exact (IH Hkk' Hin). }
            exact (GEN (kn cs) Fkn HinK). }
          assert (Enb : edenot E2 nb = edenot E nb) by (symmetry; eapply edenot_agree'; [exact Hag2 | exact Fnb]).
          assert (Em2 : elenZ E2 nb = m) by (subst m; unfold elenZ; rewrite Enb; reflexivity).
          destruct HKB as (Bflat & Blen & Bbytes).
          change (estart E (SA sb sk)) with S in Bflat, Bbytes.
          destruct Hag2 as [Hag2a Heb2].
          assert (HB : kentry_ok SEGS E2 (wbytes M s bs) (KBlob (SA db dk) nb j));
            [| exact (Forall_cons _ _ _ HB (Forall_nil _)) ].
          cbn [kentry_ok]. rewrite Em2, ED2, <- Heb2.
          refine (conj _ (conj Blen _)).
          - unfold flat. rewrite ED2. unfold flat in Bflat. pose proof (Wlo) as Wlo'. pose proof (Whi) as Whi'.
            change (estart E (SA db dk)) with D in Wlo', Whi'. lia.
          - intros i Hi. rewrite <- Hus.
            replace i with (Z.of_nat (Z.to_nat i)) by lia.
            rewrite (wbytes_nth bs M s (Z.to_nat i)) by (rewrite ?Hlbs; lia).
            f_equal.
            pose proof (rdn_nth SEGS M (Z.to_nat n) sr bs (Z.to_nat i) ltac:(lia) Hrd ltac:(lia)) as RB1.
            rewrite Husr in RB1. specialize (Bbytes (Z.of_nat (Z.to_nat i)) ltac:(lia)).
            cbn [rdn] in RB1. rewrite Bbytes in RB1. injection RB1 as RB1. rewrite ?Nat2Z.id in RB1 |- *. symmetry. exact RB1.
          }
      (* [comment removed for export] *)
        assert (HKN2 : know_ok SEGS E2 M (kn cs)) by (eapply know_ok_agree'; [exact Hag2 | exact Fkn | exact HKN]).
        pose proof (k0_sound E2 M (kn cs) db dk ne (reg cs 10) k0 HKN2 Hk0) as HK02.
        assert (HAV2 : know_ok SEGS E2 (wbytes M s bs) (kn_havoc k0 db dk ne)).
        { eapply w_know_ok_havoc; [exact HK02 | | apply wbytes_grows].
          intros x Hx. rewrite ED2, EL2 in Hx. apply wbytes_out; rewrite Hlbs; lia. }
        destruct u; [|exact HAV2].
        constructor; [|exact HAV2].
        (* [comment removed for export] *)
        apply know_ok_unk_intro_pt.
        * unfold flat. rewrite ED2, EL2. specialize (Hu eq_refl). lia.
        * intros i Hi. rewrite ED2. rewrite EL2 in Hi. rewrite <- Hus.
          replace i with (Z.of_nat (Z.to_nat i)) by lia.
          apply wbytes_defined; rewrite Hlbs; lia.
    - (* [comment removed for export] *) eapply (wbytes_lfp E M (kn cs) db dk ne); [exact HKN | exact Hwr | exact Hus | rewrite Hlbs, Hlen; lia].
    - exact Hk. }
  (* [comment removed for export] *)
  assert (HSRC :
    (if (kwritable_x A (kn cs) (kn cs) sb sk ne && flat_x (kn cs) sb sk ne)%bool
     then after_call2 nx0 cs ret (Some (reg cs 10))
            (map (fun i : nat => KWord (SA db (dk + 8 * Z.of_nat i)) 8 (EVar (nxt cs + NCS + i)))
                 (seq 0 (if (Z.eqb nlo nhi && Z.eqb (nhi mod 8) 0 && Z.leb nhi 256 && Z.ltb 0 nhi)%bool then Z.to_nat (nhi / 8) else 0%nat))
             ++ kblob_prefix (kn cs) sb sk db dk nlo ne ++ (if Z.ltb 0 nlo then KUnk (SA db dk) ne :: kn_havoc k0 db dk ne else kn_havoc k0 db dk ne))
            (if (Z.eqb nlo nhi && Z.eqb (nhi mod 8) 0 && Z.leb nhi 256 && Z.ltb 0 nhi)%bool then Z.to_nat (nhi / 8) else 0%nat)
     else None) = Some cs' ->
    srealizes SEGS (cfg R (pc cs) FULL model) T).
  { destruct (kwritable_x A (kn cs) (kn cs) sb sk ne && flat_x (kn cs) sb sk ne)%bool eqn:Hsw; [|discriminate].
    apply andb_prop in Hsw as [Hswr Hsfl].
    assert (Hu : Z.ltb 0 nlo = true -> 0 < n) by (intros Hnlo0; apply Z.ltb_lt in Hnlo0; lia).
    destruct (Z.eqb nlo nhi && Z.eqb (nhi mod 8) 0 && Z.leb nhi 256 && Z.ltb 0 nhi)%bool eqn:HW.
    - apply andb_prop in HW as [HW Hp]. apply andb_prop in HW as [HW H256]. apply andb_prop in HW as [Heq Hm8].
      apply Z.eqb_eq in Heq. apply Z.eqb_eq in Hm8. apply Z.leb_le in H256. apply Z.ltb_lt in Hp.
      apply (GEN Hswr Hsfl); [|exact Hu].
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    - apply (GEN Hswr Hsfl); [lia | exact Hu]. }
  (* [comment removed for export] *)
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hzs end.
  { apply andb_prop in Hzs as [Hpos Hkz]. apply Z.ltb_lt in Hpos.
    destruct (kzero_x_sound SEGS E M (kn cs) (kn cs) sb sk ne HKN HKN Hkz) as (Zb & Slo & Shi).
    rewrite Hlen in Zb, Shi. change (estart E (SA sb sk)) with S in Zb, Shi, Slo.
    destruct (HusD ltac:(lia) Slo Shi) as [Hus Husr].
    apply (FIN (KZero (SA db dk) ne :: kn_havoc k0 db dk ne) (repeat (Z_to_bv 8 0) (Z.to_nat n)));
      [apply repeat_length | | | lia | | exact Hn | eapply (wbytes_lfp E M (kn cs) db dk ne); [exact HKN | exact Hwr | exact Hus | rewrite repeat_length, Hlen; lia]].
    - rewrite repeat_length. apply rdn_overlay_all; [lia|]. intros i Hi. rewrite Husr. apply Zb. lia.
    - rewrite repeat_length. apply Wst. lia.
    - constructor; [| apply HAVOC; [apply repeat_length | lia]].
      cbn [kentry_ok]. rewrite Hlen. change (estart E (SA db dk)) with D. split; [unfold flat; lia|].
      intros i Hi. rewrite <- Hus. apply wbytes_fill_at; lia. }
  clear Hzs.
  (* [comment removed for export] *)
  destruct ne as [z| | | | | | |]; try exact (HSRC Hn).
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc3; [|exact (HSRC Hn)] end.
  apply andb_prop in Hc3 as [H2048 Hfl]. apply Z.leb_le in H2048.
  destruct (copy_facts SEGS (Z.to_nat nhi) (kn cs) sb sk db dk nhi) as [kc|] eqn:Hcf; [|exact (HSRC Hn)].
  assert (Hnn : n = nhi).
  { cbn [xhi] in Hnhi. injection Hnhi as <-. rewrite zlit64_eq. subst n nw. cbn [edenot]. apply u_lit64. }
  destruct (w_flat_x_sound E M (kn cs) sb sk (ELit z) HKN Hfl) as (Slo & Shi & Spos).
  change (estart E (SA sb sk)) with S in Slo, Shi. change (bv_unsigned (edenot E (ELit z))) with n in Shi, Spos.
  destruct (HusD Spos Slo Shi) as [Hus Husr].
  destruct (copy_facts_sound SEGS E M (kn cs) sb db (Z.to_nat nhi) sk dk nhi kc HKN Hcf ltac:(lia) ltac:(lia)
              ltac:(change (estart E (SA sb sk)) with S; lia) ltac:(change (estart E (SA sb sk)) with S; lia)
              ltac:(change (estart E (SA db dk)) with D; lia) ltac:(change (estart E (SA db dk)) with D; lia))
    as (bs & Hlbs & Hrd & HKC).
  change (estart E (SA sb sk)) with S in Hrd. change (estart E (SA db dk)) with D in HKC.
  rewrite <- Hnn in Hlbs, Hrd, HKC.
  apply (FIN (kc ++ kn_havoc k0 db dk (ELit z)) bs); [exact Hlbs | | | lia | | exact Hn | eapply (wbytes_lfp E M (kn cs) db dk (ELit z)); [exact HKN | exact Hwr | exact Hus | rewrite Hlbs, Hlen; lia]].
  - rewrite Hlbs, <- Hsre. exact Hrd.
  - rewrite Hlbs. apply Wst. lia.
  - apply Forall_app. split.
    + apply HKC. rewrite <- Hus, Z_to_bv_bv_unsigned, <- Hlbs. apply rdn_wbytes_hit. rewrite Hlbs. lia.
    + apply HAVOC; [exact Hlbs | lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma img_cov_sound : forall E M k a b,
  know_ok SEGS E M k -> img_cov k a b = true -> forall i, a <= i < b -> M (Z_to_bv 64 i) = None.
Proof.
  intros E M k a b HK H i Hi. unfold img_cov in H. apply existsb_exists in H as [K [HinK HKb]].
  destruct K as [| | |lo hi| | | | | |]; try discriminate.
  apply andb_prop in HKb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  pose proof (proj1 (Forall_forall _ _) HK _ HinK) as HK1. cbn [kentry_ok] in HK1. destruct HK1 as (_ & _ & HK1).
  apply HK1. lia.
Qed.

Lemma SEALED_BYTES_length : length SEALED_BYTES = 4095%nat.
Proof. reflexivity. Qed.

Lemma SEALED_W_bytes : word_to_le_bytes 8 (Z_to_bv 64 SEALED_W) = firstn 8 SEALED_BYTES.
Proof.
  replace SEALED_W with (bytes_le_to_Z (firstn 8 SEALED_BYTES)) by (vm_compute; reflexivity).
  apply word_to_le_bytes_of_bytes_n; reflexivity.
Qed.

Lemma SEALED_BYTES_nth_hi : forall j, (8 <= j < 4095)%nat -> nth j SEALED_BYTES (Z_to_bv 8 0) = Z_to_bv 8 0.
Proof.
  intros j Hj. unfold SEALED_BYTES. rewrite app_nth2 by (cbn; lia). cbn [length]. apply nth_repeat_lt. lia.
Qed.

Lemma summary_istrncpy_sound :
  istrncpy_spec SEGS (x_istrncpy A) (x_sealed A) ->
  node1_stmt SEGS A nx0 LIMIT SINV argH LINV FS0 always (fun cs => summary_istrncpy A nx0 cs).
Proof.
  intros SUM cs cs' E R FULL model T HC _ Hn Hk.
  pose proof HC as HKN. apply co_know in HKN.
  set (M := MR E cs model FULL) in *.
  rewrite summary_istrncpy_eq in Hn. (* [comment removed for export] *) unfold summary_istrncpy_ref in Hn.
  destruct (Z.eqb (pc cs) (x_istrncpy A)) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
  destruct (ret_lit cs) as [ret|] eqn:Hret; [|discriminate].
  destruct (reg_lit cs 11) as [src|] eqn:H11; [|discriminate].
  destruct (reg_lit cs 12) as [n|] eqn:H12; [|discriminate].
  destruct (Z.eqb src (x_sealed A) && Z.eqb n 4095)%bool eqn:Hsn; [|discriminate]. cbn [negb] in Hn.
  apply andb_prop in Hsn as [Hsrc Hn95]. apply Z.eqb_eq in Hsrc. apply Z.eqb_eq in Hn95. subst src n.
  destruct (split_lit (reg cs 10)) as [db dk] eqn:Hspl.
  destruct (xhi (kn cs) (reg cs 10)) as [dhi|] eqn:Hdhi; [|discriminate].
  match type of Hn with (match ?o with _ => _ end) = _ => destruct o as [k0|] eqn:Hk0; [|discriminate] end.
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  repeat match type of Hcond with (_ && _)%bool = true => apply andb_prop in Hcond as [Hcond ?X] end.
  rename Hcond into Hb. apply Z.ltb_lt in Hb. unfold two64 in Hb.
  match goal with Hl : Z.leb 0 (x_sealed A) = true |- _ => apply Z.leb_le in Hl; rename Hl into Hs0 end.
  match goal with Hl : Z.ltb (x_sealed A + 9) two64 = true |- _ => apply Z.ltb_lt in Hl; unfold two64 in Hl; rename Hl into Hs9 end.
  match goal with Hl : kwritable_x _ _ _ db dk (ELit 4095) = true |- _ => rename Hl into Hwr end.
  match goal with Hl : img_cov k0 _ _ = true |- _ => rename Hl into Hcov end.
  match goal with Hl : ranges_apart_x _ db dk (ELit 4095) (ELit 0) _ (ELit 9) = true |- _ => rename Hl into Hap end.
  (* [comment removed for export] *)
  destruct (ret_lit_sound E cs R FULL model ret HC Hret) as (R1 & Hrok & Hretr).
  destruct (w_reg_lit_sound E cs R FULL model 11 _ HC ltac:(lia) H11) as [R11 _].
  destruct (w_reg_lit_sound E cs R FULL model 12 _ HC ltac:(lia) H12) as [R12 _].
  pose proof (w_reg_sound E cs R FULL model 10 HC ltac:(lia)) as R10.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hdhi) as Hdhi'.
  set (s := edenot E (reg cs 10)) in *.
  pose proof (w_split_lit_denot E (reg cs 10) db dk Hspl) as Hsd. fold s in Hsd.
  assert (Hse : Z_to_bv 64 (estart E (SA db dk)) = s) by (rewrite Hsd; reflexivity).
  pose proof (k0_sound E M (kn cs) db dk (ELit 4095) (reg cs 10) k0 HKN
                ltac:(destruct (off_image_x A (kn cs) db dk (ELit 4095)); [exact Hk0 | destruct (reg cs 10); try discriminate; exact Hk0])) as HK0.
  destruct (kwritable_x_sound SEGS A E M (kn cs) (kn cs) db dk (ELit 4095) HKN HKN Hwr) as (Wst & Wlo & Whi).
  pose proof (ranges_apart_x_sound SEGS E M (kn cs) db dk (ELit 4095) (ELit 0) (x_sealed A) (ELit 9) HKN Hap) as Hapart.
  rewrite !elenZ_lit in * by lia.
  unfold estart in Hapart at 2 3; cbn [a_base a_off edenot] in Hapart. rewrite u_lit0 in Hapart.
  set (D := estart E (SA db dk)) in *.
  assert (Hus : bv_unsigned s = D) by (rewrite <- Hse; apply u64_lit; lia).
  pose proof (img_cov_sound E M k0 _ _ HK0 Hcov) as Hnone.
  destruct (SUM M s R (Z_to_bv 64 ret) Hnone ltac:(rewrite <- Hse; apply Wst; lia) ltac:(lia) ltac:(lia)
               Hrok R1 R10 R11 R12) as (regs' & Hms & Hkept & Ha0).
  eapply (call_node_sound cs cs' E R FULL model T ret (Some (reg cs 10)) _ regs' _ HC Hn).
  - rewrite Hpc. exact Hms.
  - exact Hkept.
  - exact Ha0.
  - set (M' := wbytes M s SEALED_BYTES).
    assert (Hlen : bv_unsigned s + Z.of_nat (length SEALED_BYTES) <= 2 ^ 64) by (rewrite SEALED_BYTES_length; lia).
    assert (BY : forall j, (j < 4095)%nat -> M' (Z_to_bv 64 (D + Z.of_nat j)) = Some (nth j SEALED_BYTES (Z_to_bv 8 0))).
    { intros j Hj. subst M'. rewrite <- Hus. apply wbytes_nth; [exact Hlen | rewrite SEALED_BYTES_length; exact Hj]. }
    constructor; [|constructor].
    + (* [comment removed for export] *)
      cbn [kentry_ok]. split; [lia|]. split; [unfold flat; cbn [Z.of_nat]; fold D; lia|].
      rewrite adenot_SA. fold D. rewrite <- Hus, Z_to_bv_bv_unsigned.
      cbn [edenot]. rewrite SEALED_W_bytes.
      replace (firstn 8 SEALED_BYTES) with (map (fun j => nth j SEALED_BYTES (Z_to_bv 8 0)) (seq 0 8)) by reflexivity.
      apply rdn_of_nth; [lia|]. intros j Hj. apply rdn1_overlay. rewrite Hus. apply BY. lia.
    + (* [comment removed for export] *)
      cbn [kentry_ok]. rewrite elenZ_lit by lia.
      assert (HD8 : estart E (SA db (dk + 8)) = D + 8) by (unfold D, estart; cbn [a_base a_off]; lia).
      rewrite HD8. split; [unfold flat; lia|].
      intros i Hi. replace (D + 8 + i) with (D + Z.of_nat (Z.to_nat (8 + i))) by lia.
      rewrite BY by lia. f_equal. apply SEALED_BYTES_nth_hi. lia.
    + (* [comment removed for export] *)
      eapply w_know_ok_havoc; [exact HK0 | | apply wbytes_grows].
      intros x Hx. rewrite elenZ_lit in Hx by lia. fold D in Hx. subst M'. apply wbytes_out; rewrite ?SEALED_BYTES_length; lia.
  - (* [comment removed for export] *)
    eapply (wbytes_lfp E M (kn cs) db dk (ELit 4095)); [exact HKN | exact Hwr | exact Hus | rewrite SEALED_BYTES_length, elenZ_lit by lia; lia].
  - exact Hk.
Qed.

(* [comment removed for export] *)

Lemma firstn_skipn_map_nth : forall {T} (d : T) k (l : list T) m, (m + k <= length l)%nat ->
  firstn k (skipn m l) = map (fun q => nth (m + q)%nat l d) (seq 0 k).
Proof.
  intros T d k. induction k as [|k IH]; intros l m Hm; [reflexivity|].
  cbn [seq map]. rewrite <- seq_shift, map_map.
  destruct (skipn m l) as [|x rest] eqn:Hs.
  - exfalso. pose proof (f_equal (@length _) Hs) as HL. rewrite length_skipn in HL. cbn in HL. lia.
  - cbn [firstn]. f_equal.
    + rewrite <- nth_skipn, Hs. reflexivity.
    + replace rest with (skipn (S m) l).
      2: { replace (S m) with (1 + m)%nat by lia. rewrite <- skipn_skipn, Hs. reflexivity. }
      rewrite (IH l (S m)) by lia. apply map_ext. intros q. f_equal. lia.
Qed.

Lemma popfree_facts_sound : forall E M lb lk cnt c s K (base : word),
  bv_unsigned base = estart E (SA lb lk) ->
  (K <= Z.to_nat cnt)%nat -> 0 < cnt -> estart E (SA lb lk) + 4 * cnt <= 2 ^ 64 -> 0 <= estart E (SA lb lk) ->
  know_ok SEGS E (wbytes M base (pf_bytes c s (Z.to_nat cnt))) (popfree_facts lb lk cnt c s K).
Proof.
  intros E M lb lk cnt c s K base Hbase HK Hcnt Hhi Hlo. unfold popfree_facts. apply Forall_forall. intros Kx Hin.
  apply in_map_iff in Hin as [t [<- Hint]]. apply in_seq in Hint.
  set (D := estart E (SA lb lk)) in *. set (j := cnt - 1 - Z.of_nat t).
  assert (Hj : 0 <= j < cnt) by lia.
  cbn [kentry_ok]. split; [lia|].
  assert (HDj : estart E (SA lb (lk + 4 * j)) = D + 4 * j) by (unfold D, estart; cbn [a_base a_off]; lia).
  split; [unfold flat; rewrite HDj; cbn [Z.of_nat]; lia|].
  rewrite adenot_SA, HDj. cbn [edenot].
  rewrite word_to_le_bytes4_Z.
  replace ((c + Z.of_nat t * s) / 16) with ((c + (Z.of_nat (Z.to_nat cnt) - 1 - j) * s) / 16) by (f_equal; f_equal; lia).
  rewrite <- (pf_bytes_cell c s (Z.to_nat cnt) j) by lia.
  assert (Hlen : length (pf_bytes c s (Z.to_nat cnt)) = (4 * Z.to_nat cnt)%nat) by apply pf_bytes_length.
  rewrite (firstn_skipn_map_nth (Z_to_bv 8 0) 4) by (rewrite Hlen; lia).
  assert (Hu : bv_unsigned (Z_to_bv 64 (D + 4 * j)) = D + 4 * j) by (apply u64_lit; lia).
  apply rdn_of_nth; [rewrite Hu; lia|]. intros q Hq. apply rdn1_overlay. rewrite Hu.
  replace (D + 4 * j + Z.of_nat q) with (bv_unsigned base + Z.of_nat (Z.to_nat (4 * j) + q)) by lia.
  apply wbytes_nth; rewrite Hlen; lia.
Qed.

Lemma summary_popfree_sound :
  popfree_spec SEGS (x_popfree A) ->
  forall args, node1_stmt SEGS A nx0 LIMIT SINV argH LINV FS0 always (fun cs => summary_popfree A nx0 cs args).
Proof.
  intros SUM args cs cs' E R FULL model T HC _ Hn Hk.
  pose proof HC as HKN. apply co_know in HKN.
  set (M := MR E cs model FULL) in *.
  rewrite summary_popfree_eq in Hn. unfold summary_popfree_ref in Hn. rewrite kn_havocM_eq in Hn.
  destruct (Z.eqb (pc cs) (x_popfree A)) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
  destruct args as [|[K| | | | | | |] [|]]; try discriminate.
  destruct (reg_lit cs 10) as [i|] eqn:H10; [|discriminate].
  destruct (reg_lit cs 12) as [c|] eqn:H12; [|discriminate].
  destruct (reg_lit cs 21) as [s|] eqn:H21; [|discriminate].
  destruct (reg_lit cs 19) as [n|] eqn:H19; [|discriminate].
  destruct (split_lit (eaddz (reg cs 11) (- (4 * n)))) as [lb lk] eqn:Hspl.
  destruct (xlo (kn cs) (reg cs 11)) as [el|] eqn:Hel; [|discriminate].
  destruct (xhi (kn cs) (reg cs 11)) as [eh|] eqn:Heh; [|discriminate].
  match type of Hn with (if ?cnd then _ else _) = _ => destruct cnd eqn:Hcond; [|discriminate] end.
  repeat match type of Hcond with (_ && _)%bool = true => apply andb_prop in Hcond as [Hcond ?X] end.
  apply Z.leb_le in Hcond.
  repeat match goal with
         | Hl : Z.leb _ _ = true |- _ => apply Z.leb_le in Hl
         | Hl : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in Hl end.
  repeat match goal with Hl : context [two64] |- _ => change two64 with (2 ^ 64)%Z in Hl end.
  match goal with Hl : fresh_ok nx0 cs = true |- _ => rename Hl into Hfresh end.
  match goal with Hl : kwritable_x _ _ _ lb lk _ = true |- _ => rename Hl into Hwr end.
  match type of Hn with Some ?x = Some _ => assert (Hcs : cs' = x) by congruence end. subst cs'. clear Hn.
  (* [comment removed for export] *)
  destruct (w_reg_lit_sound E cs R FULL model 10 _ HC ltac:(lia) H10) as [R10 Hi].
  destruct (w_reg_lit_sound E cs R FULL model 12 _ HC ltac:(lia) H12) as [R12 Hc].
  destruct (w_reg_lit_sound E cs R FULL model 21 _ HC ltac:(lia) H21) as [R21 Hs].
  destruct (w_reg_lit_sound E cs R FULL model 19 _ HC ltac:(lia) H19) as [R19 Hnn].
  pose proof (w_reg_sound E cs R FULL model 11 HC ltac:(lia)) as R11.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hel) as Hel'.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Heh) as Heh'.
  repeat match goal with Hl : context [two64] |- _ => change two64 with (2 ^ 64)%Z in Hl end.
  set (ew := edenot E (reg cs 11)) in *. set (e := bv_unsigned ew) in *.
  pose proof (u64_range ew) as Her. fold e in Her.
  set (cnt := n - i) in *.
  destruct (kwritable_x_sound SEGS A E M (kn cs) (kn cs) lb lk (ELit (4 * cnt)) HKN HKN Hwr) as (Wst & Wlo & Whi).
  rewrite elenZ_lit in Wst, Whi by lia.
  set (D := estart E (SA lb lk)) in *.
  pose proof (w_split_lit_denot E _ lb lk Hspl) as Hsd.
  assert (HloD : edenot E (eaddz (reg cs 11) (- (4 * n))) = Z_to_bv 64 (e - 4 * n)).
  { unfold eaddz. rewrite mkAlu_denot. cbn [edenot]. apply bv_eq. rewrite u_add64. fold ew. rewrite u_lit64. unfold two64.
    rewrite u64_lit by lia. fold e.
    replace (e + - (4 * n) mod 2 ^ 64) with ((e - 4 * n) + 1 * 2 ^ 64).
    2: { rewrite <- (Z.mod_add (- (4 * n)) 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia. }
    rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  assert (HD : D = e - 4 * n).
  { assert (HDdef : D = bv_unsigned (edenot E lb) + lk) by reflexivity.
    rewrite HloD, <- HDdef in Hsd. apply (f_equal bv_unsigned) in Hsd. rewrite !u64_lit in Hsd by lia. lia. }
  destruct (SUM R M i e c s n R10 ltac:(unfold e; rewrite Z_to_bv_bv_unsigned; exact R11) R12 R21 R19
               ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
               ltac:(rewrite <- HD; apply Wst; lia)) as (regs' & Hms & G10 & G12 & G14 & G15 & Gkeep).
  set (M' := wbytes M (Z_to_bv 64 (e - 4 * n)) (pf_bytes c s (Z.to_nat (n - i)))) in *.
  eapply (call_core cs E E R FULL model T (pc cs + 32) _ _ (nxt cs) regs' M' HC Hfresh (env_agree_refl _ _)).
  (* [comment removed for export] *)
  5: { intros R' FULL' model' HC' Hfs. apply (Hk E R' FULL' model' (conj (env_agree_refl _ _) (env_agree_refl _ _)) HC' Hfs). }
  4: { (* [comment removed for export] *)
       subst M'. eapply (wbytes_lfp E M (kn cs) lb lk (ELit (4 * cnt))); [exact HKN | exact Hwr | change (estart E (SA lb lk)) with D; rewrite HD; apply u64_lit; lia |].
       rewrite elenZ_lit by lia. unfold cnt. rewrite pf_bytes_length. lia. }
  - rewrite Hpc. exact Hms.
  - (* [comment removed for export] *)
    apply regs_ok_pointwise. intros r Hr0. rewrite !nth_sr_upd.
    pose proof (co_regs _ _ _ _ _ _ _ _ _ _ _ _ HC r) as HR. unfold sr_get in HR.
    assert (Hrz : bv_eqb r 0%bv = false).
    { unfold bv_eqb. apply Z.eqb_neq. intros Hc0. apply Hr0. apply bv_eq. exact Hc0. }
    rewrite Hrz in HR.
    destruct (Nat.eqb (ridx r) 15) eqn:E15.
    { apply Nat.eqb_eq in E15. rewrite (reg_of_ridx r 15 E15). refine (eq_trans G15 _). rewrite HloD. reflexivity. }
    destruct (Nat.eqb (ridx r) 14) eqn:E14.
    { apply Nat.eqb_eq in E14. rewrite (reg_of_ridx r 14 E14). refine (eq_trans G14 _). cbn [edenot]. f_equal; f_equal; lia. }
    destruct (Nat.eqb (ridx r) 12) eqn:E12.
    { apply Nat.eqb_eq in E12. rewrite (reg_of_ridx r 12 E12). refine (eq_trans G12 _). cbn [edenot]. f_equal; lia. }
    destruct (Nat.eqb (ridx r) 10) eqn:E10.
    { apply Nat.eqb_eq in E10. rewrite (reg_of_ridx r 10 E10). refine (eq_trans G10 _). reflexivity. }
    apply Nat.eqb_neq in E15. apply Nat.eqb_neq in E14. apply Nat.eqb_neq in E12. apply Nat.eqb_neq in E10.
    rewrite Gkeep; [exact HR| | | |]; intros Hrr; [apply E10 | apply E12 | apply E14 | apply E15]; rewrite Hrr; reflexivity.
  - (* [comment removed for export] *)
    assert (Hlen : length (pf_bytes c s (Z.to_nat (n - i))) = (4 * Z.to_nat cnt)%nat) by (unfold cnt; apply pf_bytes_length).
    assert (Hbase : bv_unsigned (Z_to_bv 64 (e - 4 * n)) = D) by (rewrite HD; apply u64_lit; lia).
    unfold know_ok. apply Forall_app_intro; [|apply Forall_app_intro].
    + fold cnt. apply (popfree_facts_sound E M lb lk cnt c s (Z.to_nat K) (Z_to_bv 64 (e - 4 * n)) Hbase); lia.
    + destruct (Z.ltb K cnt) eqn:HKc; [|constructor]. apply Z.ltb_lt in HKc.
      constructor; [|constructor]. cbn [kentry_ok]. rewrite elenZ_lit by lia. split; [unfold flat; lia|].
      intros q Hq. fold D. replace (D + q) with (bv_unsigned (Z_to_bv 64 (e - 4 * n)) + Z.of_nat (Z.to_nat q)) by lia.
      subst M'. apply wbytes_defined; rewrite Hlen; lia.
    + eapply w_know_ok_havoc; [exact HKN | | apply wbytes_grows].
      intros x Hx. rewrite elenZ_lit in Hx by lia. fold D in Hx. subst M'. apply wbytes_out; rewrite Hlen; lia.
Qed.

Theorem node_x_sound_XIMemset :
  fill_spec SEGS (x_imemset A) 256 -> x_stmt SEGS A nx0 LIMIT SINV argH LINV FS0 XIMemset.
Proof. intros SUM args. exact (summary_fill_sound _ _ SUM). Qed.

(* [comment removed for export] *)
Lemma find_containing_sound0 : forall E M k ms kinds b off ne m,
  know_ok SEGS E M k -> find_containing k ms kinds b off ne = Some m ->
  In m ms /\ (In (am_kind m) kinds /\ is_fog m = false)
  /\ bv_unsigned (edenot E (am_base m)) <= estart E (SA b off)
  /\ estart E (SA b off) + elenZ E ne <= bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m)).
Proof.
  intros E M k ms kinds b off ne m HK Hf. unfold find_containing in Hf. apply find_some in Hf as [Hin Hb].
  apply andb_prop in Hb as [Hk Hins]. apply andb_prop in Hk as [Hnf Hk]. apply negb_true_iff in Hnf.
  apply existsb_exists in Hk as (kd & Hkd & Heq). apply mkind_eqb_eq in Heq. subst kd.
  pose proof (xinsideL_sound SEGS E M k b off ne (am_base m) 0 (am_len m) HK Hins) as [I1 I2].
  unfold estart in I1, I2 |- *. cbn [a_base a_off] in *. unfold elenZ in *. repeat split; try assumption; lia.
Qed.

Lemma pb_le : forall a : word,
  bv_unsigned (page_base a) <= bv_unsigned a /\ bv_unsigned a < bv_unsigned (page_base a) + 4096 /\ bv_unsigned (page_base a) mod 4096 = 0.
Proof.
  intros a. unfold page_base, page_base_of, page_size. pose proof (u64_range a) as Ha.
  assert (H : 0 <= bv_unsigned a / 4096 * 4096 <= bv_unsigned a).
  { pose proof (Z.mul_div_le (bv_unsigned a) 4096 ltac:(lia)). pose proof (Z.div_pos (bv_unsigned a) 4096 ltac:(lia) ltac:(lia)). lia. }
  pose proof (Z.div_mod (bv_unsigned a) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (bv_unsigned a) 4096 ltac:(lia)).
  rewrite u64_lit by lia. split; [lia|]. split; [lia|]. rewrite Z.mod_mul by lia. reflexivity.
Qed.

Lemma u_esub : forall E a b, bv_unsigned (edenot E (esub a b)) = (bv_unsigned (edenot E a) - bv_unsigned (edenot E b)) mod 2 ^ 64.
Proof. intros. unfold esub. rewrite mkAlu_denot. apply u_sub64. Qed.
Lemma u_eadd' : forall E a b, bv_unsigned (edenot E (eadd a b)) = (bv_unsigned (edenot E a) + bv_unsigned (edenot E b)) mod 2 ^ 64.
Proof. intros. unfold eadd. rewrite mkAlu_denot, alu_add. unfold v_add. apply u_lit64a. Qed.

Lemma summary_fill0_sound : forall entry cmax p q,
  fill_spec SEGS entry cmax ->
  node1_stmt SEGS A nx0 LIMIT SINV argH LINV FS0 always (fun cs => summary_fill0 A nx0 cs entry cmax p q).
Proof.
  intros entry cmax p q SUM cs cs' E R FULL model T HC _ Hn Hk.
  pose proof HC as HKN. apply co_know in HKN.
  set (M := MR E cs model FULL) in *.
  rewrite summary_fill0_eq in Hn. unfold summary_fill0_ref in Hn.
  destruct (Z.eqb (pc cs) entry) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
  destruct (ret_lit cs) as [ret|] eqn:Hret; [|discriminate].
  destruct (reg_lit cs 11) as [c|] eqn:H11; [|discriminate].
  destruct (Z.ltb c cmax) eqn:Hcm; [|discriminate]. cbn [negb] in Hn. apply Z.ltb_lt in Hcm.
  destruct (split_lit (reg cs 10)) as [db dk] eqn:Hspl.
  destruct (split_lit p) as [pb pk] eqn:Hspp.
  destruct (xlo (kn cs) (reg cs 12)) as [nlo|] eqn:Hnlo; [|discriminate].
  destruct (xhi (kn cs) (reg cs 12)) as [nhi|] eqn:Hnhi; [|discriminate].
  destruct (xhi (kn cs) (reg cs 10)) as [dhi|] eqn:Hdhi; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  repeat match type of Hcond with (_ && _)%bool = true => apply andb_prop in Hcond as [Hcond ?X] end.
  rename Hcond into Hc8. apply Z.eqb_eq in Hc8.
  match goal with Hl : Z.ltb 0 nlo = true |- _ => apply Z.ltb_lt in Hl; rename Hl into Hnlo0 end.
  match goal with Hl : Z.leb nhi (2 ^ 40) = true |- _ => apply Z.leb_le in Hl; rename Hl into Hn40 end.
  match goal with Hl : Z.ltb (dhi + nhi) two64 = true |- _ => apply Z.ltb_lt in Hl; rename Hl into Hb; unfold two64 in Hb end.
  match goal with Hl : lin_ge0 (kn cs) [(p, 0)] [(reg cs 10, 0)] = true |- _ => rename Hl into Lp1 end.
  match goal with Hl : lin_ge0 (kn cs) [(reg cs 10, 0); (reg cs 12, 0)] [(p, 0)] = true |- _ => rename Hl into Lp2 end.
  match goal with Hl : Z.leb 12 (ealign (kn cs) q) = true |- _ => apply Z.leb_le in Hl; rename Hl into Hqal end.
  match goal with Hl : lin_ge0 (kn cs) [(reg cs 10, 0)] [(q, 0)] = true |- _ => rename Hl into Lq1 end.
  match goal with Hl : lin_ge0 (kn cs) [(q, 4095)] [(p, 0)] = true |- _ => rename Hl into Lq2 end.
  match goal with Hl : flat_x (kn cs) db dk (esub p (reg cs 10)) = true |- _ => rename Hl into Hflp end.
  match goal with Hl : flat_x (kn cs) pb pk (esub (eadd (reg cs 10) (reg cs 12)) p) = true |- _ => rename Hl into Hflt end.
  match goal with Hl : match find_containing _ _ _ _ _ _ with Some _ => true | None => false end = true |- _ => rename Hl into Hfc end.
  match goal with Hl : forallb _ (a_ghost cs) = true |- _ => rename Hl into Hgh end.
  match goal with Hl : forallb _ (a_vis cs) = true |- _ => rename Hl into Hvs end.
  match goal with Hl : off_image_x A (kn cs) db dk (reg cs 12) = true |- _ => rename Hl into Hoff end.
  match goal with Hl : lfp_apart_x A (kn cs) db dk (reg cs 12) = true |- _ => rename Hl into Hlfp end.
  match goal with Hl : kwritable_x A (kn cs) (kn cs) pb pk _ = true |- _ => rename Hl into Hwr end.
  (* [comment removed for export] *)
  destruct (ret_lit_sound E cs R FULL model ret HC Hret) as (R1 & Hrok & Hretr).
  destruct (w_reg_lit_sound E cs R FULL model 11 c HC ltac:(lia) H11) as [R11 Hc].
  pose proof (w_reg_sound E cs R FULL model 10 HC ltac:(lia)) as R10.
  pose proof (w_reg_sound E cs R FULL model 12 HC ltac:(lia)) as R12.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hnlo) as Hnlo'.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hnhi) as Hnhi'.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hdhi) as Hdhi'.
  set (s := edenot E (reg cs 10)) in *. set (nw := edenot E (reg cs 12)) in *. set (n := bv_unsigned nw) in *.
  pose proof (u64_range nw) as Hnr. fold n in Hnr. pose proof (u64_range s) as Hsr.
  assert (Hnwn : Z_to_bv 64 n = nw) by (apply Z_to_bv_bv_unsigned).
  set (D := bv_unsigned s) in *. set (Pz := bv_unsigned (edenot E p)) in *. set (Qz := bv_unsigned (edenot E q)) in *.
  pose proof (u64_range (edenot E p)) as Hpr. fold Pz in Hpr.
  (* [comment removed for export] *)
  pose proof (lin_ge0_sound SEGS E M (kn cs) _ _ HKN Lp1) as G1. pose proof (lin_ge0_sound SEGS E M (kn cs) _ _ HKN Lp2) as G2.
  pose proof (lin_ge0_sound SEGS E M (kn cs) _ _ HKN Lq1) as G3. pose proof (lin_ge0_sound SEGS E M (kn cs) _ _ HKN Lq2) as G4.
  cbn [xt_den] in G1, G2, G3, G4. fold s nw D Pz Qz n in G1, G2, G3, G4.
  change (bv_unsigned s) with D in G1, G2, G3. change (bv_unsigned (edenot E p)) with Pz in G1, G2, G4.
  change (bv_unsigned (edenot E q)) with Qz in G3, G4. change (bv_unsigned nw) with n in G2.
  (* [comment removed for export] *)
  destruct (w_flat_x_sound E M (kn cs) db dk (esub p (reg cs 10)) HKN Hflp) as (Fp1 & Fp2 & Fp3).
  destruct (w_flat_x_sound E M (kn cs) pb pk (esub (eadd (reg cs 10) (reg cs 12)) p) HKN Hflt) as (Ft1 & Ft2 & Ft3).
  rewrite u_esub in Fp2, Fp3. change (bv_unsigned (edenot E p)) with Pz in Fp2, Fp3. change (bv_unsigned (edenot E (reg cs 10))) with D in Fp2, Fp3.
  rewrite u_esub, u_eadd' in Ft2, Ft3. change (bv_unsigned (edenot E p)) with Pz in Ft2, Ft3.
  change (bv_unsigned (edenot E (reg cs 10))) with D in Ft2, Ft3. change (bv_unsigned (edenot E (reg cs 12))) with n in Ft2, Ft3.
  pose proof (w_split_lit_denot E (reg cs 10) db dk Hspl) as Hsd. fold s in Hsd.
  pose proof (w_split_lit_denot E p pb pk Hspp) as Hpd.
  assert (HeD : estart E (SA db dk) = D).
  { unfold D. rewrite Hsd. unfold estart. cbn [a_base a_off]. rewrite u64_lit; [reflexivity|]. unfold estart in Fp1, Fp2; cbn [a_base a_off] in Fp1, Fp2. unfold two64. lia. }
  assert (HeP : estart E (SA pb pk) = Pz).
  { unfold Pz. rewrite Hpd. unfold estart. cbn [a_base a_off]. rewrite u64_lit; [reflexivity|]. unfold estart in Ft1, Ft2; cbn [a_base a_off] in Ft1, Ft2. unfold two64. lia. }
  rewrite HeD in *. rewrite HeP in *.
  assert (NP : (Pz - D) mod 2 ^ 64 = Pz - D) by (apply Z.mod_small; lia). rewrite NP in Fp2, Fp3.
  assert (NT : (((D + n) mod 2 ^ 64) - Pz) mod 2 ^ 64 = D + n - Pz) by (rewrite (Z.mod_small (D + n)) by lia; apply Z.mod_small; lia). rewrite NT in Ft2, Ft3.
  assert (Hse : Z_to_bv 64 D = s) by (apply Z_to_bv_bv_unsigned).
  pose proof (APS.cs_alloc_top SEGS A LIMIT SINV argH LINV FS0 E cs R FULL model HC) as (AT1 & AT2 & AT3).
  pose proof HULL_ok as HU; unfold hull_okP, hull_ok in HU; destruct HU as (U0 & U1 & U2 & U3).
  (* [comment removed for export] *)
  destruct (find_containing (kn cs) (a_maps cs) [KRWLAZY] db dk (reg cs 12)) as [m0|] eqn:Hfc0; [|discriminate]. clear Hfc.
  destruct (find_containing_sound0 E M (kn cs) (a_maps cs) [KRWLAZY] db dk (reg cs 12) m0 HKN Hfc0) as (Hm0 & [Hk0 Hnf0] & C1 & C2).
  rewrite HeD in C1, C2. unfold elenZ in C2. change (bv_unsigned (edenot E (reg cs 12))) with n in C2.
  assert (Hkind : am_kind m0 = KRWLAZY) by (destruct Hk0 as [Hk0|[]]; symmetry; exact Hk0).
  pose proof (proj1 (Forall_forall _ _) (co_kinds _ _ _ _ _ _ _ _ _ _ _ _ HC) m0 Hm0 Hkind) as KIND.
  pose proof (APS.maps_match_In E (a_maps cs) (vm_maps (m_vmmaps model)) m0 (co_maps _ _ _ _ _ _ _ _ _ _ _ _ HC) Hm0 Hnf0) as HIN.
  pose proof (proj1 (Forall_forall _ _) (co_bounds _ _ _ _ _ _ _ _ _ _ _ _ HC) (amap_den E m0) HIN) as (B1 & B2 & B3 & B4 & B5).
  unfold amap_den in B1, B2, B3, B4, B5, HIN. cbn [fst snd] in B1, B2, B3, B4, B5.
  set (mb := bv_unsigned (edenot E (am_base m0))) in *. set (ml := bv_unsigned (edenot E (am_len m0))) in *.
  assert (INR : forall a : word, D <= bv_unsigned a < D + n ->
            in_ivs (bv_unsigned a) (vm_maps (m_vmmaps model)) = true /\ in_ivs (bv_unsigned a) (vm_noaccess (m_vmmaps model)) = false
            /\ page_in_ranges (page_base a) (m_vm_lazy model) = true /\ in_hull A (bv_unsigned a) = false
            /\ bv_unsigned a < alloc_top (m_vmmaps model) /\ argH E a = false).
  { intros a Ha. destruct (KIND a ltac:(unfold mb, ml in *; lia)) as [K1 K2].
    split; [apply in_ivs_true; exists (edenot E (am_base m0), edenot E (am_len m0)); split; [exact HIN | cbn [fst snd]; unfold mb, ml in *; lia]|].
    split; [exact K1|]. split; [exact K2|].
    split; [unfold in_hull; apply andb_false_iff; destruct B4 as [B4|B4]; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia|].
    split; [lia|].
    destruct (argH E a) eqn:Ha2; [|reflexivity]. exfalso.
    pose proof (argH_top E FULL a (co_sinv _ _ _ _ _ _ _ _ _ _ _ _ HC) Ha2). unfold STK in AT1. lia. }
  (* [comment removed for export] *)
  assert (GH : forall a : word, D <= bv_unsigned a < Pz -> in_ghost E cs (bv_unsigned a) = false).
  { intros a Ha. unfold in_ghost. apply existsb_false_forall. intros g Hg.
    pose proof (proj1 (forallb_forall _ _) Hgh g Hg) as Hg1. cbv beta in Hg1.
    destruct (split_lit (fst g)) as [gb gk] eqn:Hgs. apply andb_prop in Hg1 as [Hgf Hga].
    destruct (w_flat_x_sound E M (kn cs) gb gk (snd g) HKN Hgf) as (Gf1 & Gf2 & Gf3).
    pose proof (ranges_apart_x_sound SEGS E M (kn cs) db dk (esub p (reg cs 10)) gb gk (snd g) HKN Hga) as D1.
    rewrite HeD in D1. unfold elenZ in D1 at 1. rewrite u_esub in D1. change (bv_unsigned (edenot E p)) with Pz in D1.
    change (bv_unsigned (edenot E (reg cs 10))) with D in D1. rewrite NP in D1.
    pose proof (w_split_lit_denot E (fst g) gb gk Hgs) as Hgd.
    assert (Ug : uE E (fst g) = estart E (SA gb gk)).
    { unfold uE. rewrite Hgd. unfold estart. cbn [a_base a_off]. apply u64_lit. unfold estart in Gf1, Gf2; cbn [a_base a_off] in Gf1, Gf2. unfold two64. lia. }
    rewrite Ug. unfold uE. fold (elenZ E (snd g)). apply andb_false_iff.
    destruct D1 as [D1|D1]; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; unfold elenZ in *; lia. }
  (* [comment removed for export] *)
  assert (PREF0 : forall a : word, D <= bv_unsigned a < Pz -> HID E cs model a = true -> FULL a = Some (Z_to_bv 8 0)).
  { intros a Ha Hh. destruct (INR a ltac:(lia)) as (I1 & I2 & I3 & _ & _ & _).
    exact (co_zero _ _ _ _ _ _ _ _ _ _ _ _ HC a Hh I1 I2 I3 (GH a Ha)). }
  (* [comment removed for export] *)
  assert (OFFSEG : forall a : word, D <= bv_unsigned a < D + n -> find_segment SEGS (bv_unsigned a) 1 = None).
  { intros a Ha. apply SEGS_in_hull. destruct (INR a Ha) as (_ & _ & _ & I4 & _). exact I4. }
  assert (PREF1 : forall a : word, D <= bv_unsigned a < Pz -> HID E cs model a = false -> FULL a <> None).
  { intros a Ha Hh. destruct (INR a ltac:(lia)) as (I1 & I2 & I3 & I4 & I5 & I6).
    unfold hid in Hh. apply orb_false_iff in Hh as [_ Hv]. apply negb_false_iff in Hv. unfold vis in Hv.
    rewrite I4 in Hv. rewrite (proj2 (Z.leb_gt _ _)) in Hv by lia. rewrite I1, I2, I3 in Hv. cbn [orb andb negb] in Hv.
    unfold in_allow in Hv. apply orb_prop in Hv as [Hv|Hv].
    - (* [comment removed for export] *)
      exfalso. unfold in_vis in Hv. apply existsb_exists in Hv as (v & Hv & Hin).
      pose proof (proj1 (forallb_forall _ _) Hvs v Hv) as Hv1. cbv beta in Hv1.
      destruct (split_lit (fst v)) as [vb vk] eqn:Hvsp. destruct (shadow_of A (kn cs) (fst v) (snd v)) as [[sb sk] sn] eqn:Hsh.
      repeat match type of Hv1 with (_ && _)%bool = true => apply andb_prop in Hv1 as [Hv1 ?X] end.
      match goal with Hl : ranges_apart_x (kn cs) db dk _ vb vk (snd v) = true |- _ => rename Hl into Hva end.
      destruct (w_flat_x_sound E M (kn cs) vb vk (snd v) HKN Hv1) as (Vf1 & Vf2 & Vf3).
      pose proof (ranges_apart_x_sound SEGS E M (kn cs) db dk (esub p (reg cs 10)) vb vk (snd v) HKN Hva) as D1.
      rewrite HeD in D1. unfold elenZ in D1 at 1. rewrite u_esub in D1. change (bv_unsigned (edenot E p)) with Pz in D1.
      change (bv_unsigned (edenot E (reg cs 10))) with D in D1. rewrite NP in D1.
      pose proof (w_split_lit_denot E (fst v) vb vk Hvsp) as Hvd.
      assert (Uv : uE E (fst v) = estart E (SA vb vk)).
      { unfold uE. rewrite Hvd. unfold estart. cbn [a_base a_off]. apply u64_lit. unfold estart in Vf1, Vf2; cbn [a_base a_off] in Vf1, Vf2. unfold two64. lia. }
      rewrite Uv in Hin. apply andb_prop in Hin as [Z1 Z2]. apply Z.leb_le in Z1. apply Z.ltb_lt in Z2. unfold uE, elenZ in *. lia.
    - (* [comment removed for export] *)
      unfold in_sh in Hv. apply existsb_exists in Hv as (v & Hv & Hin).
      pose proof (proj1 (forallb_forall _ _) Hvs v Hv) as Hv1. cbv beta in Hv1.
      destruct (split_lit (fst v)) as [vb vk] eqn:Hvsp. destruct (shadow_of A (kn cs) (fst v) (snd v)) as [[sb sk] sn] eqn:Hsh.
      cbv zeta in Hv1.
      set (al8 := (Z.leb 3 (ealign (kn cs) (fst v)) && Z.leb 3 (ealign (kn cs) (snd v)))%bool) in Hv1.
      set (snx := if al8 then sn else eadd sn (ELit 1)) in Hv1.
      apply andb_prop in Hv1 as [Hv1 Halt]. apply andb_prop in Hv1 as [Hv1 Hva]. apply andb_prop in Hv1 as [Hv1 Hsflx].
      apply andb_prop in Hv1 as [Hvfl Hsfl].
      destruct (APS.shadow_of_val SEGS A SHADOW_ok E M (kn cs) (fst v) (snd v) sb sk sn HKN Hsh Hsfl) as [S1 S2].
      destruct (w_flat_x_sound E M (kn cs) sb sk sn HKN Hsfl) as (Sf1 & Sf2 & Sf3).
      destruct (w_flat_x_sound E M (kn cs) sb sk snx HKN Hsflx) as (Sg1 & Sg2 & Sg3).
      destruct (w_flat_x_sound E M (kn cs) vb vk (snd v) HKN Hvfl) as (Vf1 & Vf2 & Vf3).
      pose proof (u64_range (edenot E (fst v))) as Rv1. pose proof (u64_range (edenot E (snd v))) as Rv2.
      pose proof SHADOW_ok as So; unfold shadow_ok in So.
      assert (Hb8 : 0 <= bv_unsigned (edenot E (fst v)) / 8 < 2 ^ 61) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
      assert (Hn8 : 0 <= bv_unsigned (edenot E (snd v)) / 8 < 2 ^ 61) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
      rewrite Z.mod_small in S1 by lia.
      pose proof (Z.div_mod (bv_unsigned (edenot E (fst v))) 8 ltac:(lia)) as Dm1. pose proof (Z.mod_pos_bound (bv_unsigned (edenot E (fst v))) 8 ltac:(lia)) as Mb1.
      pose proof (Z.div_mod (bv_unsigned (edenot E (snd v))) 8 ltac:(lia)) as Dm2. pose proof (Z.mod_pos_bound (bv_unsigned (edenot E (snd v))) 8 ltac:(lia)) as Mb2.
      (* [comment removed for export] *)
      assert (Hshlo : sh_lo A E v = estart E (SA sb sk)) by (unfold sh_lo, uE; rewrite S1; lia).
      assert (Hshhi : sh_hi A E v <= estart E (SA sb sk) + elenZ E snx).
      { unfold sh_hi, uE. rewrite S1. subst snx. destruct al8 eqn:Hal8.
        - (* [comment removed for export] *)
          rewrite S2. subst al8. apply andb_prop in Hal8 as [Hab Han]. apply Z.leb_le in Hab. apply Z.leb_le in Han.
          destruct (ealign_sound SEGS E M (kn cs) (fst v) HKN) as [_ Hdb]. destruct (ealign_sound SEGS E M (kn cs) (snd v) HKN) as [_ Hdn].
          assert (D8b : (8 | bv_unsigned (edenot E (fst v)))).
          { eapply Z.divide_trans; [|exact Hdb]. exists (2 ^ (ealign (kn cs) (fst v) - 3)). change 8 with (2 ^ 3). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
          assert (D8n : (8 | bv_unsigned (edenot E (snd v)))).
          { eapply Z.divide_trans; [|exact Hdn]. exists (2 ^ (ealign (kn cs) (snd v) - 3)). change 8 with (2 ^ 3). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
          destruct D8b as [qb Hqb]. destruct D8n as [qn Hqn]. rewrite Hqb, Hqn.
          rewrite Z.div_mul, <- Z.mul_add_distr_r, !Z.div_mul by lia. lia.
        - (* [comment removed for export] *)
          assert (L1 : elenZ E (eadd sn (ELit 1)) = elenZ E sn + 1).
          { unfold elenZ. rewrite u_eadd'. cbn [edenot]. rewrite (u64_lit 1) by (unfold two64; lia). apply Z.mod_small. unfold elenZ in S2. rewrite S2. lia. }
          rewrite L1, S2.
          assert (LT : (bv_unsigned (edenot E (fst v)) + bv_unsigned (edenot E (snd v))) / 8 < bv_unsigned (edenot E (fst v)) / 8 + bv_unsigned (edenot E (snd v)) / 8 + 2)
            by (apply Z.div_lt_upper_bound; lia).
          lia. }
      assert (Lx1 : 1 <= elenZ E snx) by (unfold elenZ in *; lia).
      rewrite Hshlo in Hin. apply andb_prop in Hin as [Z1 Z2]. apply Z.leb_le in Z1. apply Z.ltb_lt in Z2.
      apply orb_prop in Halt as [Halt|Hpg]; [apply orb_prop in Halt as [Hsa|Hsw]|].
      + exfalso. pose proof (ranges_apart_x_sound SEGS E M (kn cs) db dk (esub p (reg cs 10)) sb sk snx HKN Hsa) as D1.
        rewrite HeD in D1. unfold elenZ in D1 at 1. rewrite u_esub in D1. change (bv_unsigned (edenot E p)) with Pz in D1.
        change (bv_unsigned (edenot E (reg cs 10))) with D in D1. rewrite NP in D1. lia.
      + destruct (kwritable_x_sound SEGS A E M (kn cs) (kn cs) sb sk snx HKN HKN Hsw) as (Wst & Wlo & Whi).
        pose proof (store_ok_all SEGS M (Z.to_nat (elenZ E snx)) (Z_to_bv 64 (estart E (SA sb sk))) ltac:(rewrite u64_lit by (unfold two64; lia); lia) (Wst (Z.to_nat (elenZ E snx)) ltac:(lia)) a
                      ltac:(rewrite u64_lit by (unfold two64; lia); lia)) as Hw.
        unfold wview in Hw. unfold M, Mr, mrestrict in Hw. unfold hid in Hw. rewrite I6 in Hw. cbn [orb] in Hw.
        assert (Hvz : vis A E cs model a = true).
        { unfold vis. rewrite I4, I1, I2, I3. rewrite (proj2 (Z.leb_gt _ _)) by lia. cbn [orb andb negb].
          unfold in_allow. apply orb_true_iff. right. unfold in_sh. apply existsb_exists. exists v. split; [exact Hv|].
          rewrite Hshlo. apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
        rewrite Hvz in Hw. cbn [negb] in Hw. destruct (FULL a); [discriminate|]. rewrite (OFFSEG a ltac:(lia)) in Hw. exfalso. apply Hw. reflexivity.
      + (* [comment removed for export] *)
        exfalso. unfold vis_below_pg in Hpg.
        apply andb_prop in Hpg as [Hpg G6]. apply andb_prop in Hpg as [Hpg G5]. apply andb_prop in Hpg as [Hpg Hph].
        apply andb_prop in Hpg as [Hpg Had]. apply andb_prop in Hpg as [Hpg Han]. apply andb_prop in Hpg as [Hoff512 Hab].
        apply Z.eqb_eq in Hoff512. apply Z.leb_le in Hab. apply Z.leb_le in Han. apply Z.leb_le in Had.
        destruct (xhi (kn cs) p) as [ph|] eqn:Hxp; [|discriminate]. apply Z.ltb_lt in Hph. unfold two64 in Hph.
        pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hxp) as Hph'. change (bv_unsigned (edenot E p)) with Pz in Hph'.
        pose proof (lin_ge0_sound SEGS E M (kn cs) _ _ HKN G5) as G5'. pose proof (lin_ge0_sound SEGS E M (kn cs) _ _ HKN G6) as G6'.
        cbn [xt_den] in G5', G6'. change (bv_unsigned (edenot E p)) with Pz in G5'. change (bv_unsigned (edenot E (reg cs 10))) with D in G5'.
        assert (U8 : bv_unsigned (edenot E (escale 8 p)) = 8 * Pz).
        { unfold escale. rewrite mkMd_denot. cbn [edenot]. rewrite u_mul64. rewrite (u64_lit 8) by (unfold two64; lia).
          change (bv_unsigned (edenot E p)) with Pz. apply Z.mod_small. lia. }
        rewrite U8 in G6'.
        destruct (ealign_sound SEGS E M (kn cs) (fst v) HKN) as [_ Hdb]. destruct (ealign_sound SEGS E M (kn cs) (snd v) HKN) as [_ Hdn].
        destruct (ealign_sound SEGS E M (kn cs) (reg cs 10) HKN) as [_ Hdd]. change (bv_unsigned (edenot E (reg cs 10))) with D in Hdd.
        assert (Pb : (4096 | bv_unsigned (edenot E (fst v)))).
        { eapply Z.divide_trans; [|exact Hdb]. exists (2 ^ (ealign (kn cs) (fst v) - 12)). change 4096 with (2 ^ 12). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
        assert (Pn : (4096 | bv_unsigned (edenot E (snd v)))).
        { eapply Z.divide_trans; [|exact Hdn]. exists (2 ^ (ealign (kn cs) (snd v) - 12)). change 4096 with (2 ^ 12). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
        assert (Pd : (512 | D)).
        { eapply Z.divide_trans; [|exact Hdd]. exists (2 ^ (ealign (kn cs) (reg cs 10) - 9)). change 512 with (2 ^ 9). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
        destruct Pb as [tb Htb]. destruct Pn as [tn Htn]. destruct Pd as [td Htd].
        pose proof (Z.div_mod (shadow_off A) 512 ltac:(lia)) as Ho. rewrite Hoff512, Z.add_0_r in Ho.
        (* [comment removed for export] *)
        unfold sh_hi, uE in Z2. rewrite Htb, Htn in Z2. rewrite <- Z.mul_add_distr_r in Z2.
        replace ((tb + tn) * 4096 / 8) with ((tb + tn) * 512) in Z2 by (rewrite <- (Z.div_mul ((tb + tn) * 512) 8) by lia; f_equal; lia).
        nia. }
  (* [comment removed for export] *)
  destruct (kwritable_x_sound SEGS A E M (kn cs) (kn cs) pb pk (esub (eadd (reg cs 10) (reg cs 12)) p) HKN HKN Hwr) as (Tst & _ & _).
  rewrite HeP in Tst. unfold elenZ in Tst. rewrite u_esub, u_eadd' in Tst. change (bv_unsigned (edenot E p)) with Pz in Tst.
  change (bv_unsigned (edenot E (reg cs 10))) with D in Tst. change (bv_unsigned (edenot E (reg cs 12))) with n in Tst. rewrite NT in Tst.
  assert (TAIL : forall a : word, Pz <= bv_unsigned a < D + n -> HID E cs model a = false /\ FULL a <> None).
  { intros a Ha.
    pose proof (store_ok_all SEGS M (Z.to_nat (D + n - Pz)) (Z_to_bv 64 Pz) ltac:(rewrite u64_lit by (unfold two64; lia); lia) (Tst (Z.to_nat (D + n - Pz)) ltac:(lia)) a
                  ltac:(rewrite u64_lit by (unfold two64; lia); lia)) as Hw.
    unfold wview in Hw. unfold M, Mr, mrestrict in Hw. rewrite (OFFSEG a ltac:(lia)) in Hw.
    destruct (HID E cs model a); [exfalso; apply Hw; reflexivity|]. split; [reflexivity|]. destruct (FULL a); [discriminate|]. exfalso; apply Hw; reflexivity. }
  (* [comment removed for export] *)
  set (H2 := fun a : word => (HID E cs model a && negb ((D <=? bv_unsigned a) && (bv_unsigned a <? Pz)))%bool).
  set (M2 := mrestrict H2 FULL).
  assert (M2def : forall a : word, D <= bv_unsigned a < D + n -> M2 a = FULL a /\ FULL a <> None).
  { intros a Ha. unfold M2, mrestrict, H2.
    destruct (Z_lt_le_dec (bv_unsigned a) Pz) as [Hlt|Hge].
    - replace ((D <=? bv_unsigned a) && (bv_unsigned a <? Pz))%bool with true
        by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
      rewrite andb_false_r. split; [reflexivity|].
      destruct (HID E cs model a) eqn:Hh; [rewrite (PREF0 a ltac:(lia) Hh); discriminate | exact (PREF1 a ltac:(lia) Hh)].
    - destruct (TAIL a ltac:(lia)) as [Hh Hd]. rewrite Hh. cbn [andb]. split; [reflexivity | exact Hd]. }
  assert (Hst : store_ok SEGS M2 s (Z.to_nat n) = true).
  { apply store_ok_of_all; [lia|]. intros x Hx. destruct (M2def x ltac:(lia)) as [E1 E2]. unfold wview. rewrite E1. destruct (FULL x); [discriminate | exfalso; apply E2; reflexivity]. }
  (* [comment removed for export] *)
  destruct (SUM M2 s (Z_to_bv 64 c) n R (Z_to_bv 64 ret) ltac:(lia) ltac:(lia) Hst
               ltac:(rewrite u64_lit by (unfold two64 in Hc; lia); lia) Hrok R1 R10 R11 ltac:(rewrite Hnwn; exact R12))
    as (regs' & Hms & Hkept & Ha0).
  rewrite (u64_lit c) in Hms by (unfold two64 in Hc; lia).
  assert (Hc0 : Z_to_bv 8 c = Z_to_bv 8 0) by (rewrite <- (Z_to_bv8_mod c), Hc8; reflexivity). rewrite Hc0 in Hms.
  set (MR' := wbytes M2 s (repeat (Z_to_bv 8 0) (Z.to_nat n))) in *.
  assert (WIN : forall a : word, D <= bv_unsigned a < D + n -> MR' a = Some (Z_to_bv 8 0)).
  { intros a Ha. unfold MR'. replace a with (Z_to_bv 64 (bv_unsigned s + (bv_unsigned a - D))) by (apply bv_eq; rewrite u64_lit by (unfold two64; lia); lia).
    apply wbytes_fill_at; lia. }
  assert (WOUT : forall a : word, bv_unsigned a < D \/ D + n <= bv_unsigned a -> MR' a = M2 a).
  { intros a Ha. unfold MR'. apply wbytes_out; rewrite repeat_length; lia. }
  eapply (call_node_sound_H cs cs' E R FULL model T ret (Some (reg cs 10)) _ regs' H2 MR' HC Hn).
  - (* [comment removed for export] *) intros a Ha. unfold H2 in Ha. apply andb_prop in Ha as [Ha _]. exact Ha.
  - (* [comment removed for export] *)
    intros w Hlz Hw. unfold H2 in Hw. apply andb_false_iff in Hw as [Hw|Hw]; [exact (w_lazy_cover_cs E cs R FULL model HC w Hlz Hw)|].
    apply negb_false_iff in Hw. apply andb_prop in Hw as [W1 W2]. apply Z.leb_le in W1. apply Z.ltb_lt in W2.
    set (t := Z_to_bv 64 Pz). assert (Ut : bv_unsigned t = Pz) by (unfold t; apply u64_lit; unfold two64; lia).
    destruct (TAIL t ltac:(rewrite Ut; lia)) as [Th _]. destruct (INR t ltac:(rewrite Ut; lia)) as (_ & _ & Tlz & _ & _ & _).
    pose proof (w_lazy_cover_cs E cs R FULL model HC t Tlz Th) as Hcov.
    (* [comment removed for export] *)
    destruct (ealign_sound SEGS E M (kn cs) q HKN) as [_ Hdq]. change (bv_unsigned (edenot E q)) with Qz in Hdq.
    assert (D4096 : (4096 | Qz)).
    { eapply Z.divide_trans; [|exact Hdq]. exists (2 ^ (ealign (kn cs) q - 12)). change 4096 with (2 ^ 12). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
    destruct D4096 as [qq Hqq].
    pose proof (pb_le w) as (P1 & P2 & P3). pose proof (pb_le t) as (Q1 & Q2 & Q3). rewrite Ut in Q1, Q2.
    assert (EQ : page_base w = page_base t).
    { apply bv_eq. pose proof (Z.div_mod (bv_unsigned (page_base w)) 4096 ltac:(lia)). pose proof (Z.div_mod (bv_unsigned (page_base t)) 4096 ltac:(lia)). nia. }
    rewrite EQ. exact Hcov.
  - rewrite Hpc. exact Hms.
  - exact Hkept.
  - exact Ha0.
  - (* [comment removed for export] *)
    set (Mv := mrestrict (HID E cs model) MR').
    assert (MvOUT : forall x : word, bv_unsigned x < D \/ D + n <= bv_unsigned x -> Mv x = M x).
    { intros x Hx. unfold Mv, M, Mr, mrestrict. destruct (HID E cs model x) eqn:Hh; [reflexivity|].
      rewrite (WOUT x Hx). unfold M2, mrestrict, H2. rewrite Hh. reflexivity. }
    assert (MvGROW : mem_grows M Mv).
    { intros x Hx. unfold Mv, mrestrict. unfold M, Mr, mrestrict in Hx. destruct (HID E cs model x) eqn:Hh; [exact Hx|].
      destruct (Z_lt_le_dec (bv_unsigned x) D); [rewrite WOUT by lia|]; [unfold M2, mrestrict, H2; rewrite Hh; exact Hx|].
      destruct (Z_lt_le_dec (bv_unsigned x) (D + n)); [rewrite WIN by lia; discriminate|].
      rewrite WOUT by lia. unfold M2, mrestrict, H2. rewrite Hh. exact Hx. }
    constructor.
    + (* [comment removed for export] *) cbn [kentry_ok]. rewrite HeP. unfold elenZ. rewrite u_esub, u_eadd'.
      change (bv_unsigned (edenot E p)) with Pz. change (bv_unsigned (edenot E (reg cs 10))) with D. change (bv_unsigned (edenot E (reg cs 12))) with n. rewrite NT.
      split; [unfold flat; rewrite HeP; lia|].
      intros i Hi. unfold Mv, mrestrict.
      destruct (TAIL (Z_to_bv 64 (Pz + i)) ltac:(rewrite u64_lit by (unfold two64; lia); lia)) as [Th _]. rewrite Th.
      apply WIN. rewrite u64_lit by (unfold two64; lia). lia.
    + eapply w_know_ok_havoc_z; [exact HKN | | exact MvGROW |].
      * rewrite HeD. unfold elenZ. change (bv_unsigned (edenot E (reg cs 12))) with n. exact MvOUT.
      * (* [comment removed for export] *)
        intros x Hx Hdef. rewrite HeD in Hx. unfold elenZ in Hx. change (bv_unsigned (edenot E (reg cs 12))) with n in Hx.
        unfold Mv, mrestrict. unfold M, Mr, mrestrict in Hdef.
        destruct (HID E cs model x) eqn:Hh; [exfalso; apply Hdef; reflexivity|]. apply WIN. lia.
  - (* [comment removed for export] *)
    intros a Hh H2a. unfold H2 in H2a. rewrite Hh in H2a. cbn [andb] in H2a. apply negb_false_iff in H2a.
    apply andb_prop in H2a as [W1 W2]. apply Z.leb_le in W1. apply Z.ltb_lt in W2.
    rewrite (WIN a ltac:(lia)). symmetry. exact (PREF0 a ltac:(lia) Hh).
  - (* [comment removed for export] *)
    intros a Ha H2a.
    pose proof (APS.lfp_apart_x_sound SEGS A E M (kn cs) db dk (reg cs 12) HKN Hlfp (bv_unsigned a) Ha) as X.
    unfold uE in X. change (bv_unsigned (edenot E (reg cs 12))) with n in X.
    pose proof HeD as HeD'. unfold estart in HeD'. cbn [a_base a_off] in HeD'.
    assert (Hout : bv_unsigned a < D \/ D + n <= bv_unsigned a) by lia.
    rewrite (WOUT a Hout). unfold M2, mrestrict. rewrite H2a. reflexivity.
  - exact Hk.
Qed.

Theorem node_x_sound_XMemset :
  fill_spec SEGS (x_memset A) two64 -> x_stmt SEGS A nx0 LIMIT SINV argH LINV FS0 XMemset.
Proof.
  intros SUM args. destruct args as [|p [|q [|? ?]]].
  - exact (summary_fill_sound _ _ SUM).
  - intros cs cs' E R FULL model T HC _ Hn Hk. discriminate.
  - exact (summary_fill0_sound _ _ p q SUM).
  - intros cs cs' E R FULL model T HC _ Hn Hk. discriminate.
Qed.

Theorem node_x_sound_XIMemcpy :
  copy_spec SEGS (x_imemcpy A) -> x_stmt SEGS A nx0 LIMIT SINV argH LINV FS0 XIMemcpy.
Proof. intros SUM args. exact (summary_copy_sound _ SUM). Qed.

Theorem node_x_sound_XMemcpy :
  copy_spec SEGS (x_memcpy A) -> x_stmt SEGS A nx0 LIMIT SINV argH LINV FS0 XMemcpy.
Proof. intros SUM args. exact (summary_copy_sound _ SUM). Qed.

Theorem node_x_sound_XMemIsZero :
  miz_spec SEGS (x_memiszero A) -> x_stmt SEGS A nx0 LIMIT SINV argH LINV FS0 XMemIsZero.
Proof. intros SUM args. exact (summary_miz_sound SUM). Qed.

Theorem node_x_sound_XIStrncpy :
  istrncpy_spec SEGS (x_istrncpy A) (x_sealed A) -> x_stmt SEGS A nx0 LIMIT SINV argH LINV FS0 XIStrncpy.
Proof. intros SUM args. exact (summary_istrncpy_sound SUM). Qed.

Theorem node_x_sound_XPopFree :
  popfree_spec SEGS (x_popfree A) -> x_stmt SEGS A nx0 LIMIT SINV argH LINV FS0 XPopFree.
Proof. intros SUM args. exact (summary_popfree_sound SUM args). Qed.

End Sound.
End FPW_1.


End APSX.
