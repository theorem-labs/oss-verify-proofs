(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YA0f.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/Reusable/YA0f.v at origin/ossv/recipes 6ebe35ba632 (fuzz_knock's released ASan tree); module paths changed to reac-pw/fuzz_headamp. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK15 YK00 YK04 YK05 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK0c YK0e YK0f YK09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YA0c YA0e.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK0a.
Local Instance asanreflect_fx : YK11.FPState := YK11.fx0.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Open Scope Z_scope.
Module APSXG.
Import AX2. Import AX2S. Import APG. Import APSG.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Definition kept_ok (regs regs' : bvmap 5 word) : Prop :=
forall r : bv 5, r <> 0%bv -> ~ In (ridx r) caller_saved -> getr regs' r = getr regs r.
Section g.
Variable SEGS : list Segment.
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
Definition SEALED_BYTES : list byte :=
[Z_to_bv 8 0x3c; Z_to_bv 8 0x73; Z_to_bv 8 0x65; Z_to_bv 8 0x61; Z_to_bv 8 0x6c; Z_to_bv 8 0x65; Z_to_bv 8 0x64; Z_to_bv 8 0x3e]
++ repeat (Z_to_bv 8 0) 4087.
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
End g.
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
Lemma nth_sr_vars_lt' : forall b sr r, APG.sr_vars_lt b sr = true -> (r < 32)%nat -> APG.expr_vars_lt b (nth r sr (ELit 0)) = true.
Proof.
intros b sr. induction sr as [|x t IH]; intros r H Hr; [destruct r; reflexivity|].
cbn [APG.sr_vars_lt] in H. apply andb_prop in H as [H1 H2]. destruct r as [|r]; [exact H1|]. cbn [nth]. apply IH; [exact H2 | lia].
Qed.
Lemma regs_after_call : forall E sr R R' nx rv,
regs_ok E sr R -> APG.sr_vars_lt nx sr = true -> kept_ok R R' ->
match rv with Some e => APG.expr_vars_lt nx e = true /\ getr R' (Z_to_bv 5 10) = edenot E e | None => True end ->
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
Lemma wbytes_defined : forall bs m (a : word) j,
bv_unsigned a + Z.of_nat (length bs) <= 2 ^ 64 -> (j < length bs)%nat ->
wbytes m a bs (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) <> None.
Proof. intros bs m a j Hnw Hj. rewrite wbytes_nth by assumption. discriminate. Qed.
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
Lemma rdn1_overlay : forall segs m (a : word) b, m a = Some b -> rdn segs m a 1 = Some [b].
Proof. intros segs m a b H. cbn [rdn]. rewrite H. reflexivity. Qed.
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
Section a0.
Variable segs : list Segment.
Lemma adenot_SA : forall E b off, adenot E (SA b off) = Z_to_bv 64 (estart E (SA b off)).
Proof. intros. unfold adenot, v_addi, estart. reflexivity. Qed.
Lemma kwritable_sound : forall E M allkn k b off n,
know_ok segs E M allkn ->
know_ok segs E M k -> kwritable allkn k b off n = true -> 0 <= n ->
store_ok segs M (Z_to_bv 64 (estart E (SA b off))) (Z.to_nat n) = true
/\ 0 <= estart E (SA b off) /\ estart E (SA b off) + n <= 2 ^ 64.
Proof.
intros E M allkn k b off n Hall HK H Hn. induction k as [|K rest IH]; [discriminate|].
apply Forall_cons_iff in HK as [HKK Hrest].
destruct K; try exact (IH Hrest H).
lazymatch type of H with context [KWr ?wa ?wl :: rest] => destruct wa as [wb wk]; rename wl into wn end.
cbn [kwritable] in H.
cbn [kentry_ok] in HKK. destruct HKK as [Hfl Hs]. pose proof Hfl as Hfl'. destruct Hfl' as (F1 & F2 & F3 & F4).
unfold estart in Hs, F1, F2, F4 |- *. cbn [a_base a_off] in Hs, F1, F2, F4 |- *.
assert (CORE : bv_unsigned (edenot E wb) + wk <= bv_unsigned (edenot E b) + off ->
bv_unsigned (edenot E b) + off + n <= bv_unsigned (edenot E wb) + wk + elenZ E wn ->
store_ok segs M (Z_to_bv 64 (bv_unsigned (edenot E b) + off)) (Z.to_nat n) = true
/\ 0 <= bv_unsigned (edenot E b) + off /\ bv_unsigned (edenot E b) + off + n <= 2 ^ 64).
{ intros A B. split; [|lia].
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
destruct (xinside_sound segs E M allkn b off (ELit n) wb wk wn Hall Hxi) as [I1 I2].
unfold elenZ in I2 at 1. cbn [edenot] in I2. rewrite u64_lit in I2 by lia.
unfold estart in I1, I2. cbn [a_base a_off] in I1, I2. apply CORE; lia.
Qed.
Lemma kwritable_x_sound : forall E M allkn k b off n,
know_ok segs E M allkn ->
know_ok segs E M k -> kwritable_x allkn k b off n = true ->
(forall m, Z.of_nat m <= elenZ E n ->
store_ok segs M (Z_to_bv 64 (estart E (SA b off))) m = true)
/\ 0 <= estart E (SA b off) /\ estart E (SA b off) + elenZ E n <= 2 ^ 64.
Proof.
intros E M allkn k b off n Hall HK H. induction k as [|K rest IH]; [discriminate|].
apply Forall_cons_iff in HK as [HKK Hrest].
destruct K; try exact (IH Hrest H).
lazymatch type of H with context [KWr ?wa ?wl :: rest] => destruct wa as [wb wk]; rename wl into wn end.
cbn [kwritable_x] in H.
assert (H2w : forall c1 c2 : bool, (if c1 then true else if c2 then true else kwritable_x allkn rest b off n) = true ->
(c1 || c2)%bool = true \/ kwritable_x allkn rest b off n = true)
by (intros [|] [|]; cbn; auto).
apply H2w in H. destruct H as [H|H]; [|exact (IH Hrest H)].
cbn [kentry_ok] in HKK. destruct HKK as [Hfl Hs]. pose proof Hfl as Hfl'. destruct Hfl' as (F1 & F2 & F3 & F4).
unfold estart in Hs, F1, F2, F4 |- *. cbn [a_base a_off] in Hs, F1, F2, F4 |- *.
pose proof (u64_range (edenot E n)) as Hnr.
assert (CORE : bv_unsigned (edenot E wb) + wk <= bv_unsigned (edenot E b) + off ->
bv_unsigned (edenot E b) + off + elenZ E n <= bv_unsigned (edenot E wb) + wk + elenZ E wn ->
(forall m, Z.of_nat m <= elenZ E n -> store_ok segs M (Z_to_bv 64 (bv_unsigned (edenot E b) + off)) m = true)
/\ 0 <= bv_unsigned (edenot E b) + off /\ bv_unsigned (edenot E b) + off + elenZ E n <= 2 ^ 64).
{ intros A B. split; [|unfold elenZ in *; lia]. intros m Hm.
replace (bv_unsigned (edenot E b) + off) with (bv_unsigned (edenot E wb) + wk + (bv_unsigned (edenot E b) + off - (bv_unsigned (edenot E wb) + wk))) by lia.
apply Hs; lia. }
apply orb_prop in H as [H|H].
- destruct (expr_eqb b wb && Z.leb wk off)%bool eqn:H01; [|discriminate]. apply andb_prop in H01 as [H0 H1].
apply expr_eqb_eq in H0. apply Z.leb_le in H1. subst wb.
destruct (xhi allkn n) as [nh|] eqn:Hxh; [|discriminate].
destruct (xlo allkn wn) as [wl|] eqn:Hxl; [|discriminate]. apply Z.leb_le in H.
pose proof (xhi_sound segs E M allkn n nh Hall Hxh). pose proof (xlo_sound segs E M allkn wn wl Hall Hxl).
apply CORE; unfold elenZ in *; lia.
- pose proof (xinside_sound segs E M allkn b off n wb wk wn Hall H) as [A B].
unfold estart in A, B. cbn [a_base a_off] in A, B. apply CORE; lia.
Qed.
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
{ intros A B. split; [|unfold elenZ in *; lia]. intros i Hi.
replace (bv_unsigned (edenot E b) + off + i) with (bv_unsigned (edenot E zb) + zk + (bv_unsigned (edenot E b) + off - (bv_unsigned (edenot E zb) + zk) + i)) by lia.
apply Hz. lia. }
apply orb_prop in H as [H|H].
- destruct (expr_eqb b zb && Z.leb zk off)%bool eqn:H01; [|discriminate]. apply andb_prop in H01 as [H0 H1].
apply expr_eqb_eq in H0. apply Z.leb_le in H1. subst zb.
destruct (xhi allkn n) as [nh|] eqn:Hxh; [|discriminate].
destruct (xlo allkn zn) as [zl|] eqn:Hxl; [|discriminate]. apply Z.leb_le in H.
pose proof (xhi_sound segs E M allkn n nh Hall Hxh). pose proof (xlo_sound segs E M allkn zn zl Hall Hxl).
apply CORE; unfold elenZ in *; lia.
- pose proof (xinside_sound segs E M allkn b off n zb zk zn Hall H) as [A B].
unfold estart in A, B. cbn [a_base a_off] in A, B. apply CORE; lia.
Qed.
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
End a0.
Section d0.
Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable TOP : Z.
Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Definition res_len_okP : Prop := length (segments_reserved SEGS) = n_res A.
Definition hull_okP : Prop := 0 <= img_lo A /\ img_lo A mod 4096 = 0 /\ img_hi A mod 4096 = 0 /\ img_hi A <= KHI.
Hypothesis RES_len : res_len_okP.
Hypothesis HULL_ok : hull_okP.
Hypothesis TOP_ok' : top_ok TOP.   Hypothesis RES_cover : res_cover_ok SEGS A.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Hypothesis argH_high : forall E (a : word), argH E a = true -> TOP <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Hypothesis SINV_s1 : forall E M, SINV E M ->
uE E e_sp0 = TOP + 8388608 /\ uE E (EVar V_S1) = (TOP + 8388608) / 32768 /\ (TOP + 8388608) mod 16 = 0.
Hypothesis SHADOW_ok : shadow_ok A.
Variable FS0 : Fs.Fs.
Definition segs_wr_ok : Prop := forall seg, In seg SEGS -> seg_writable seg = true -> seg_readable seg = true.
Hypothesis SEGS_wr : segs_wr_ok.
#[local] Notation cfg := (cfg_of SEGS) (only parsing).
#[local] Notation CSOK := (cs_ok SEGS A LIMIT TOP SINV argH FS0) (only parsing).
#[local] Notation HID := (hid A TOP argH) (only parsing).
#[local] Notation MR := (Mr A TOP argH) (only parsing).
#[local] Ltac aps_fill :=
first [eassumption | exact (fun _ : nat => @None acs) | exact (fun _ _ _ => None) | exact (fun _ _ => None) | exact (fun _ => None)
| exact 0%nat | exact 0%Z | exact nx0 | exact LIMIT | exact TOP_ok' | exact RES_cover].
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
CSOK E (with_ss cs ss') R' FULL' model'.
Proof. intros. eapply cs_ok_frame; try eassumption. Unshelve. all: aps_fill. Qed.
Lemma w_lazy_cover_cs : forall E cs R FULL model,
CSOK E cs R FULL model -> lazy_cover (HID E cs model) (m_vm_lazy model) (allowA A E cs).
Proof. intros. eapply lazy_cover_cs; try eassumption. Unshelve. all: aps_fill. Qed.
Lemma w_page_base_le : forall a : word,
bv_unsigned (page_base a) <= bv_unsigned a /\ bv_unsigned a < bv_unsigned (page_base a) + 4096 /\ bv_unsigned (page_base a) mod 4096 = 0.
Proof. intros. eapply page_base_le; try eassumption. Unshelve. all: aps_fill. Qed.
Lemma w_A_wf_allowA : forall E cs, A_wf (allowA A E cs).
Proof. intros. eapply A_wf_allowA; try eassumption. Unshelve. all: aps_fill. Qed.
Lemma w_H_off_segments_cs : forall E cs model, H_off_segments SEGS (HID E cs model).
Proof. intros. eapply H_off_segments_cs; try eassumption. Unshelve. all: aps_fill. Qed.
Lemma w_fresh_ok_parts : forall cs, fresh_ok nx0 cs = true ->
APG.sr_vars_lt (nxt cs) (s_regs (a_ss cs)) = true /\ APG.kn_vars_lt (nxt cs) (kn cs) = true
/\ maps_vars_lt (nxt cs) (a_maps cs) = true /\ pairs_vars_lt (nxt cs) (a_vis cs ++ a_ghost cs) = true
/\ APG.expr_vars_lt (nxt cs) (a_brk cs) = true /\ fd_vars_lt (nxt cs) (a_fd cs) = true /\ (nx0 <= nxt cs)%nat.
Proof. intros. eapply fresh_ok_parts; try eassumption. Unshelve. all: aps_fill. Qed.
Lemma find_segment_In : forall segs a n seg, find_segment segs a n = Some seg -> In seg segs.
Proof.
intros segs a n seg. induction segs as [|s0 rest IH]; cbn [find_segment]; intros H; [discriminate|].
destruct (Z.leb (Z.of_N (seg_base s0)) a && Z.leb (a + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0)))%bool.
- injection H as <-. left. reflexivity.
- right. apply IH. exact H.
Qed.
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
Lemma call_core : forall cs E E' R FULL model T (ret : Z) sr2 k' nx2 regs' MR',
CSOK E cs R FULL model ->
fresh_ok nx0 cs = true ->
env_agree (nxt cs) E E' ->
msteps SEGS (mkst R (Z_to_bv 64 (pc cs)) (MR E cs model FULL) (seg_rom SEGS))
(mkst regs' (Z_to_bv 64 ret) MR' (seg_rom SEGS)) ->
regs_ok E' sr2 regs' ->
know_ok SEGS E' MR' k' ->
(forall R' FULL' model',
CSOK E' (with_ss cs (mk_ss ret sr2 k' nx2)) R' FULL' model' -> m_fs model' = m_fs model ->
srealizes SEGS (cfg R' ret FULL' model') T) ->
srealizes SEGS (cfg R (pc cs) FULL model) T.
Proof.
intros cs E E' R FULL model T ret sr2 k' nx2 regs' MR' HC Hfresh Hag Hms HR' HK' Hk.
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
+ apply (same_but_materialized_frame _ _ Hsame).
Qed.
Lemma call_core_H : forall (Hh : word -> bool) cs E E' R FULL model T (ret : Z) sr2 k' nx2 regs' MR',
CSOK E cs R FULL model ->
fresh_ok nx0 cs = true ->
env_agree (nxt cs) E E' ->
H_off_segments SEGS Hh ->
lazy_cover Hh (m_vm_lazy model) (allowA A E cs) ->
msteps SEGS (mkst R (Z_to_bv 64 (pc cs)) (mrestrict Hh FULL) (seg_rom SEGS))
(mkst regs' (Z_to_bv 64 ret) MR' (seg_rom SEGS)) ->
(forall a, Hh a = false -> HID E cs model a = true -> MR' a = FULL a) ->
regs_ok E' sr2 regs' ->
know_ok SEGS E' (mrestrict (HID E cs model) (munrestrict Hh FULL MR')) k' ->
(forall R' FULL' model',
CSOK E' (with_ss cs (mk_ss ret sr2 k' nx2)) R' FULL' model' -> m_fs model' = m_fs model ->
srealizes SEGS (cfg R' ret FULL' model') T) ->
srealizes SEGS (cfg R (pc cs) FULL model) T.
Proof.
intros Hh cs E E' R FULL model T ret sr2 k' nx2 regs' MR' HC Hfresh Hag HHoff HLC Hms HKEEP HR' HK' Hk.
destruct (w_fresh_ok_parts cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
unfold cfg_of.
apply (srz_msteps_restricted_T SEGS Hh HHoff SEGS_wx (allowA A E cs)
(mkst R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS)) (mkst regs' (Z_to_bv 64 ret) MR' (seg_rom SEGS)) model T
HLC (w_A_wf_allowA E cs) (co_minv _ _ _ _ _ _ _ _ _ _ _ _ HC) (co_halt _ _ _ _ _ _ _ _ _ _ _ _ HC)).
- rewrite restrict_mkst. exact Hms.
- intros model' Hinv' Hsame Hclean.
set (FULL' := munrestrict Hh FULL MR').
change (unrestrict Hh (ms_mem (mkst R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS))) (mkst regs' (Z_to_bv 64 ret) MR' (seg_rom SEGS)))
with (mkst regs' (Z_to_bv 64 ret) FULL' (seg_rom SEGS)).
apply (Hk regs' FULL' model').
+ pose proof (w_cs_ok_agree E E' cs R FULL model Hag Hfresh HC) as HC1.
pose proof (w_hid_agree (nxt cs) E E' cs model Hag Fle Fallow) as HH.
eapply (w_cs_ok_frame E' cs R FULL model _ regs' FULL' model' HC1 Hsame).
* rewrite (allowA_agree A (nxt cs) E E' cs Hag Fallow). exact Hinv'.
* exact HR'.
* reflexivity.
* cbn [s_know mk_ss]. unfold Mr. rewrite HH. exact HK'.
* intros a Ha. rewrite HH in Ha. unfold FULL', munrestrict.
destruct (Hh a) eqn:Hha; [reflexivity | exact (HKEEP a Hha Ha)].
+ apply (same_but_materialized_frame _ _ Hsame).
Qed.
Lemma sr_vars_lt_fresh : forall rs sr nx b,
APG.sr_vars_lt b sr = true -> (nx + length rs <= b)%nat -> APG.sr_vars_lt b (sr_fresh sr rs nx) = true.
Proof.
induction rs as [|r rest IH]; intros sr nx b Hsr Hb; cbn [sr_fresh length] in *; [exact Hsr|].
apply IH; [|lia]. apply sr_vars_lt_upd; [exact Hsr|]. cbn [APG.expr_vars_lt]. apply Nat.ltb_lt. lia.
Qed.
Lemma call_node_sound : forall cs cs' E R FULL model T (ret : Z) rv k' regs' MR',
CSOK E cs R FULL model ->
after_call nx0 cs ret rv k' = Some cs' ->
msteps SEGS (mkst R (Z_to_bv 64 (pc cs)) (MR E cs model FULL) (seg_rom SEGS))
(mkst regs' (Z_to_bv 64 ret) MR' (seg_rom SEGS)) ->
kept_ok R regs' ->
match rv with Some e => getr regs' (Z_to_bv 5 10) = edenot E e | None => True end ->
know_ok SEGS E MR' k' ->
(forall E' R' FULL' model',
env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
srealizes SEGS (cfg R' (pc cs') FULL' model') T) ->
srealizes SEGS (cfg R (pc cs) FULL model) T.
Proof.
intros cs cs' E R FULL model T ret rv k' regs' MR' HC Hac Hms Hkept Hrv HK' Hk.
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
- intros R' FULL' model' HC' Hfs. apply (Hk E' R' FULL' model'); [| exact HC' | exact Hfs].
split; [eapply w_env_agree_le; [exact Hag | exact Fle] | exact Hag].
Qed.
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
(forall E' R' FULL' model',
env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
srealizes SEGS (cfg R' (pc cs') FULL' model') T) ->
srealizes SEGS (cfg R (pc cs) FULL model) T.
Proof.
intros cs cs' E R FULL model T ret rv k' extra vals regs' MR' HC Hac Hms Hkept Hrv HK' Hk.
unfold after_call2 in Hac.
match type of Hac with context [if ?c then _ else _] => destruct c eqn:Hc; [|discriminate] end.
apply andb_prop in Hc as [Hc Hrvv]. apply andb_prop in Hc as [Hfresh Hkv].
injection Hac as <-.
destruct (w_fresh_ok_parts cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
set (E' := ext_call2 E (nxt cs) regs' vals).
pose proof (ext_call2_agree E (nxt cs) regs' vals) as Hag. fold E' in Hag.
set (sr1 := sr_fresh (s_regs (a_ss cs)) caller_saved (nxt cs)).
assert (Hsf : APG.sr_vars_lt (nxt cs + NCS) sr1 = true).
{ subst sr1. apply sr_vars_lt_fresh; [eapply sr_vars_lt_mono; [exact Fsr | lia] | ].
unfold caller_saved, NCS. cbn [length]. lia. }
assert (HR2 : regs_ok E' (match rv with Some e => sr_upd sr1 10 e | None => sr1 end) regs').
{ eapply (regs_ok_agree' (nxt cs + NCS)); [apply ext_call2_agree16 | |].
- destruct rv as [e|]; [|exact Hsf]. apply sr_vars_lt_upd; [exact Hsf|]. eapply expr_vars_lt_mono; [exact Hrvv | unfold nxt, NCS; lia].
- subst sr1. apply (regs_after_call E _ R regs' (nxt cs) rv (co_regs _ _ _ _ _ _ _ _ _ _ _ _ HC) Fsr Hkept).
destruct rv as [e|]; [split; [exact Hrvv | exact Hrv] | exact I]. }
eapply (call_core cs E E' R FULL model T ret _ k' _ regs' MR' HC Hfresh Hag Hms HR2 HK').
intros R' FULL' model' HC' Hfs. apply (Hk E' R' FULL' model'); [| exact HC' | exact Hfs].
split; [eapply w_env_agree_le; [exact Hag | exact Fle] | exact Hag].
Qed.
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
Lemma split_lit_vars : forall e b k m, split_lit e = (b, k) -> APG.expr_vars_lt m e = true -> APG.expr_vars_lt m b = true.
Proof.
intros e b k m H Hv. unfold split_lit in H.
destruct e; try (injection H as <- <-; first [exact Hv | reflexivity]).
lazymatch type of H with (match ?o with _ => _ end) = _ => destruct o end; try (injection H as <- <-; exact Hv).
lazymatch type of H with (match ?y with _ => _ end) = _ => destruct y end; try (injection H as <- <-; exact Hv).
injection H as <- <-. cbn [APG.expr_vars_lt] in Hv. apply andb_prop in Hv as [Hv _]. exact Hv.
Qed.
Lemma nth_map_seq : forall {T} (f : nat -> T) W i d, (i < W)%nat -> nth i (map f (seq 0 W)) d = f i.
Proof.
intros T f W i d Hi. rewrite (nth_indep _ d (f 0%nat)) by (rewrite length_map, length_seq; exact Hi).
rewrite map_nth. rewrite seq_nth by exact Hi. reflexivity.
Qed.
Lemma nth_repeat_lt : forall {T} (a d : T) m j, (j < m)%nat -> nth j (repeat a m) d = a.
Proof. intros T a d m. induction m as [|m IH]; intros j Hj; [lia|]. destruct j; [reflexivity|]. cbn. apply IH. lia. Qed.
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
Lemma summary_fill_sound : forall entry cmax,
fill_spec SEGS entry cmax ->
node1_stmt SEGS A nx0 LIMIT TOP SINV argH FS0 always (fun cs => summary_fill A nx0 cs entry cmax).
Proof.
intros entry cmax SUM cs cs' E R FULL model T HC _ Hn Hk.
pose proof HC as HKN. apply co_know in HKN.
set (M := MR E cs model FULL) in *.
rewrite summary_fill_eq in Hn.   unfold summary_fill_ref in Hn.
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
assert (FIN : forall k',
store_ok SEGS M s (Z.to_nat n) = true ->
know_ok SEGS E (wbytes M s (repeat (Z_to_bv 8 c) (Z.to_nat n))) k' ->
after_call nx0 cs ret (Some (reg cs 10)) k' = Some cs' ->
srealizes SEGS (cfg R (pc cs) FULL model) T).
{ intros k' Hst HK' Hac.
destruct (SUM M s (Z_to_bv 64 c) n R (Z_to_bv 64 ret) ltac:(lia) ltac:(lia) Hst
ltac:(rewrite u64_lit by (unfold two64 in Hc; lia); lia) Hrok R1 R10 R11 ltac:(rewrite Hnwn; exact R12))
as (regs' & Hms & Hkept & Ha0).
rewrite (u64_lit c) in Hms by (unfold two64 in Hc; lia).
eapply (call_node_sound cs cs' E R FULL model T ret (Some (reg cs 10)) k' regs' _ HC Hac).
- rewrite Hpc. exact Hms.
- exact Hkept.
- exact Ha0.
- exact HK'.
- exact Hk. }
assert (ST0 : n = 0 -> store_ok SEGS M s (Z.to_nat n) = true) by (intros ->; reflexivity).
assert (WB0 : n = 0 -> wbytes M s (repeat (Z_to_bv 8 c) (Z.to_nat n)) = M) by (intros ->; reflexivity).
destruct (Z.eqb nhi 0) eqn:Hnhi0.
{ apply Z.eqb_eq in Hnhi0. assert (Hz : n = 0) by lia.
apply (FIN (kn cs)); [exact (ST0 Hz) | rewrite (WB0 Hz); exact HKN | exact Hn]. }
match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hzb end.
{ apply andb_prop in Hzb as [Hzb Hwr]. apply andb_prop in Hzb as [Hc8 Hkz]. apply Z.eqb_eq in Hc8.
destruct (kwritable_x_sound SEGS E M (kn cs) (kn cs) db dk (reg cs 12) HKN HKN Hwr) as (Wst & Wlo & Whi).
destruct (kzero_x_sound SEGS E M (kn cs) (kn cs) db dk (reg cs 12) HKN HKN Hkz) as (Zb & _ & _).
rewrite Hse, Hlen in *.
apply (FIN (kn cs)); [apply Wst; lia | | exact Hn].
destruct (Z.eq_dec n 0) as [Hz|Hnz]; [rewrite (WB0 Hz); exact HKN|].
assert (Hus : bv_unsigned s = estart E (SA db dk)) by (rewrite <- Hse; apply u64_lit; lia).
rewrite wbytes_same; [exact HKN | rewrite repeat_length; lia |].
intros j Hj. rewrite repeat_length in Hj. rewrite nth_repeat_lt by exact Hj.
rewrite Hus. rewrite Zb by lia. rewrite <- (Z_to_bv8_mod c), Hc8. reflexivity. }
clear Hzb.
match type of Hn with (match ?o with _ => _ end) = _ => destruct o as [k0|] eqn:Hk0; [|discriminate] end.
pose proof (k0_sound E M (kn cs) db dk (reg cs 12) (reg cs 10) k0 HKN Hk0) as HK0.
destruct (kwritable_x (kn cs) (kn cs) db dk (reg cs 12)) eqn:Hwr; [|discriminate].
destruct (kwritable_x_sound SEGS E M (kn cs) (kn cs) db dk (reg cs 12) HKN HKN Hwr) as (Wst & Wlo & Whi).
rewrite Hse, Hlen in *.
eapply FIN; [apply Wst; lia | | exact Hn].
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
node1_stmt SEGS A nx0 LIMIT TOP SINV argH FS0 always (fun cs => summary_miz A nx0 cs).
Proof.
intros SUM cs cs' E R FULL model T HC _ Hn Hk.
pose proof HC as HKN. apply co_know in HKN.
set (M := MR E cs model FULL) in *.
rewrite summary_miz_eq in Hn.   unfold summary_miz_ref in Hn.
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
pose proof (w_split_lit_denot E _ qb qk Hsq) as Hq.
unfold eaddz in Hq. rewrite mkAlu_denot, alu_add in Hq. cbn [edenot] in Hq. fold spw in Hq. unfold v_add in Hq.
destruct (kwritable_sound SEGS E M (kn cs) (kn cs) qb qk 16 HKN HKN Hwr ltac:(lia)) as (Qst & Qlo & Qhi).
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
- exact Hk.
Qed.
Lemma summary_copy_sound : forall entry,
copy_spec SEGS entry ->
node1_stmt SEGS A nx0 LIMIT TOP SINV argH FS0 always (fun cs => summary_copy SEGS A nx0 cs entry).
Proof.
intros entry SUM cs cs' E R FULL model T HC _ Hn Hk.
pose proof HC as HKN. apply co_know in HKN.
set (M := MR E cs model FULL) in *.
rewrite summary_copy_eq in Hn.   unfold summary_copy_ref in Hn.
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
assert (FIN : forall k' bs,
length bs = Z.to_nat n ->
rdn SEGS M sr (length bs) = Some bs ->
store_ok SEGS M s (length bs) = true ->
(bv_unsigned s + n <= bv_unsigned sr \/ bv_unsigned sr + n <= bv_unsigned s) ->
know_ok SEGS E (wbytes M s bs) k' ->
after_call nx0 cs ret (Some (reg cs 10)) k' = Some cs' ->
srealizes SEGS (cfg R (pc cs) FULL model) T).
{ intros k' bs Hlbs Hrd Hst Hdisj HK' Hac.
destruct (SUM M s sr n bs R (Z_to_bv 64 ret) ltac:(lia) Hlbs Hrd Hst Hdisj ltac:(lia) ltac:(lia) Hrok R1 R10 R11
ltac:(rewrite Hnwn; exact R12)) as (regs' & Hms & Hkept & Ha0).
eapply (call_node_sound cs cs' E R FULL model T ret (Some (reg cs 10)) k' regs' _ HC Hac).
- rewrite Hpc. exact Hms.
- exact Hkept.
- exact Ha0.
- exact HK'.
- exact Hk. }
destruct (Z.eqb nhi 0) eqn:Hnhi0.
{ apply Z.eqb_eq in Hnhi0. assert (Hz : n = 0) by lia.
apply (FIN (kn cs) []); [rewrite Hz; reflexivity | reflexivity | reflexivity | lia | cbn [wbytes]; exact HKN | exact Hn]. }
match type of Hn with (match ?o with _ => _ end) = _ => destruct o as [k0|] eqn:Hk0; [|discriminate] end.
pose proof (k0_sound E M (kn cs) db dk ne (reg cs 10) k0 HKN Hk0) as HK0.
match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hwa; [|discriminate] end.
apply andb_prop in Hwa as [Hwr Hap].
destruct (kwritable_x_sound SEGS E M (kn cs) (kn cs) db dk ne HKN HKN Hwr) as (Wst & Wlo & Whi).
pose proof (ranges_apart_x_sound SEGS E M (kn cs) db dk ne sb sk ne HKN Hap) as Hapart.
rewrite Hlen in *.
set (D := estart E (SA db dk)) in *. set (S := estart E (SA sb sk)) in *.
rewrite Hse in Wst.
assert (HAVOC : forall bs, length bs = Z.to_nat n -> 0 < n ->
know_ok SEGS E (wbytes M s bs) (kn_havoc k0 db dk ne)).
{ intros bs Hlbs Hpos.
assert (Hus : bv_unsigned s = D) by (rewrite <- Hse; apply u64_lit; lia).
eapply w_know_ok_havoc; [exact HK0 | | apply wbytes_grows].
intros x Hx. rewrite Hlen in Hx. change (estart E (SA db dk)) with D in Hx.
apply wbytes_out; rewrite Hlbs; lia. }
assert (HusD : 0 < n -> 0 <= S -> S + n <= 2 ^ 64 -> bv_unsigned s = D /\ bv_unsigned sr = S).
{ intros Hpos Slo Shi. split; [rewrite <- Hse | rewrite <- Hsre]; apply u64_lit; lia. }
assert (VARS : fresh_ok nx0 cs = true ->
APG.kn_vars_lt (nxt cs) (kn cs) = true /\ APG.expr_vars_lt (nxt cs) db = true /\ APG.expr_vars_lt (nxt cs) ne = true
/\ APG.sr_vars_lt (nxt cs) (s_regs (a_ss cs)) = true).
{ intros Hfresh. destruct (w_fresh_ok_parts cs Hfresh) as (Fsr & Fkn & _).
split; [exact Fkn|]. split; [| split; [rewrite Hne; unfold reg; apply nth_sr_vars_lt'; [exact Fsr | lia] | exact Fsr]].
eapply split_lit_vars; [exact Hspd|]. unfold reg. apply nth_sr_vars_lt'; [exact Fsr | lia]. }
assert (GEN : kwritable_x (kn cs) (kn cs) sb sk ne = true -> flat_x (kn cs) sb sk ne = true ->
forall (W : nat) (u : bool), 8 * Z.of_nat W <= n -> (u = true -> 0 < n) ->
after_call2 nx0 cs ret (Some (reg cs 10))
(map (fun i : nat => KWord (SA db (dk + 8 * Z.of_nat i)) 8 (EVar (nxt cs + NCS + i))) (seq 0 W)
++ kblob_prefix (kn cs) sb sk db dk nlo ++ (if u then KUnk (SA db dk) ne :: kn_havoc k0 db dk ne else kn_havoc k0 db dk ne)) W
= Some cs' ->
srealizes SEGS (cfg R (pc cs) FULL model) T).
{ intros Hswr Hsfl W u HW Hu Hac.
destruct (kwritable_x_sound SEGS E M (kn cs) (kn cs) sb sk ne HKN HKN Hswr) as (SWst & Slo & Shi).
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
+
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
{
unfold kblob_prefix.
destruct (List.find _ (kn cs)) as [K|] eqn:HF; [|constructor].
apply find_some in HF as [HinK HKt].
destruct K as [| |[kb ko] [n0| | | | | | |] j| | | | | | |]; try (now constructor).
apply andb_prop in HKt as [HKt Hn0le]. apply andb_prop in HKt as [HKt Hn0pos]. apply andb_prop in HKt as [Hkb Hko].
apply expr_eqb_eq in Hkb. apply Z.eqb_eq in Hko. apply Z.ltb_lt in Hn0pos. apply Z.leb_le in Hn0le. subst kb ko.
pose proof (proj1 (Forall_forall _ _) HKN _ HinK) as HKB. cbn [kentry_ok] in HKB.
assert (En0 : elenZ E (ELit n0) = n0) by (unfold elenZ; rewrite edenot_lit, u64_lit; lia).
assert (En0' : elenZ E2 (ELit n0) = n0) by (unfold elenZ; rewrite edenot_lit, u64_lit; lia).
rewrite En0 in HKB. destruct HKB as (Bflat & Blen & Bbytes).
change (estart E (SA sb sk)) with S in Bflat, Bbytes.
destruct Hag2 as [Hag2a Heb2].
assert (HB : kentry_ok SEGS E2 (wbytes M s bs) (KBlob (SA db dk) (ELit n0) j));
[| exact (Forall_cons _ _ _ HB (Forall_nil _)) ].
cbn [kentry_ok]. rewrite En0', ED2, <- Heb2.
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
assert (HKN2 : know_ok SEGS E2 M (kn cs)) by (eapply know_ok_agree'; [exact Hag2 | exact Fkn | exact HKN]).
pose proof (k0_sound E2 M (kn cs) db dk ne (reg cs 10) k0 HKN2 Hk0) as HK02.
assert (HAV2 : know_ok SEGS E2 (wbytes M s bs) (kn_havoc k0 db dk ne)).
{ eapply w_know_ok_havoc; [exact HK02 | | apply wbytes_grows].
intros x Hx. rewrite ED2, EL2 in Hx. apply wbytes_out; rewrite Hlbs; lia. }
destruct u; [|exact HAV2].
constructor; [|exact HAV2].
apply know_ok_unk_intro_pt.
* unfold flat. rewrite ED2, EL2. specialize (Hu eq_refl). lia.
* intros i Hi. rewrite ED2. rewrite EL2 in Hi. rewrite <- Hus.
replace i with (Z.of_nat (Z.to_nat i)) by lia.
apply wbytes_defined; rewrite Hlbs; lia.
- exact Hk. }
assert (HSRC :
(if (kwritable_x (kn cs) (kn cs) sb sk ne && flat_x (kn cs) sb sk ne)%bool
then after_call2 nx0 cs ret (Some (reg cs 10))
(map (fun i : nat => KWord (SA db (dk + 8 * Z.of_nat i)) 8 (EVar (nxt cs + NCS + i)))
(seq 0 (if (Z.eqb nlo nhi && Z.eqb (nhi mod 8) 0 && Z.leb nhi 256 && Z.ltb 0 nhi)%bool then Z.to_nat (nhi / 8) else 0%nat))
++ kblob_prefix (kn cs) sb sk db dk nlo ++ (if Z.ltb 0 nlo then KUnk (SA db dk) ne :: kn_havoc k0 db dk ne else kn_havoc k0 db dk ne))
(if (Z.eqb nlo nhi && Z.eqb (nhi mod 8) 0 && Z.leb nhi 256 && Z.ltb 0 nhi)%bool then Z.to_nat (nhi / 8) else 0%nat)
else None) = Some cs' ->
srealizes SEGS (cfg R (pc cs) FULL model) T).
{ destruct (kwritable_x (kn cs) (kn cs) sb sk ne && flat_x (kn cs) sb sk ne)%bool eqn:Hsw; [|discriminate].
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
match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hzs end.
{ apply andb_prop in Hzs as [Hpos Hkz]. apply Z.ltb_lt in Hpos.
destruct (kzero_x_sound SEGS E M (kn cs) (kn cs) sb sk ne HKN HKN Hkz) as (Zb & Slo & Shi).
rewrite Hlen in Zb, Shi. change (estart E (SA sb sk)) with S in Zb, Shi, Slo.
destruct (HusD ltac:(lia) Slo Shi) as [Hus Husr].
apply (FIN (KZero (SA db dk) ne :: kn_havoc k0 db dk ne) (repeat (Z_to_bv 8 0) (Z.to_nat n)));
[apply repeat_length | | | lia | | exact Hn].
- rewrite repeat_length. apply rdn_overlay_all; [lia|]. intros i Hi. rewrite Husr. apply Zb. lia.
- rewrite repeat_length. apply Wst. lia.
- constructor; [| apply HAVOC; [apply repeat_length | lia]].
cbn [kentry_ok]. rewrite Hlen. change (estart E (SA db dk)) with D. split; [unfold flat; lia|].
intros i Hi. rewrite <- Hus. apply wbytes_fill_at; lia. }
clear Hzs.
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
apply (FIN (kc ++ kn_havoc k0 db dk (ELit z)) bs); [exact Hlbs | | | lia | | exact Hn].
- rewrite Hlbs, <- Hsre. exact Hrd.
- rewrite Hlbs. apply Wst. lia.
- apply Forall_app. split.
+ apply HKC. rewrite <- Hus, Z_to_bv_bv_unsigned, <- Hlbs. apply rdn_wbytes_hit. rewrite Hlbs. lia.
+ apply HAVOC; [exact Hlbs | lia].
Qed.
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
node1_stmt SEGS A nx0 LIMIT TOP SINV argH FS0 always (fun cs => summary_istrncpy A nx0 cs).
Proof.
intros SUM cs cs' E R FULL model T HC _ Hn Hk.
pose proof HC as HKN. apply co_know in HKN.
set (M := MR E cs model FULL) in *.
rewrite summary_istrncpy_eq in Hn.   unfold summary_istrncpy_ref in Hn.
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
match goal with Hl : kwritable_x _ _ db dk (ELit 4095) = true |- _ => rename Hl into Hwr end.
match goal with Hl : img_cov k0 _ _ = true |- _ => rename Hl into Hcov end.
match goal with Hl : ranges_apart_x _ db dk (ELit 4095) (ELit 0) _ (ELit 9) = true |- _ => rename Hl into Hap end.
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
destruct (kwritable_x_sound SEGS E M (kn cs) (kn cs) db dk (ELit 4095) HKN HKN Hwr) as (Wst & Wlo & Whi).
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
+
cbn [kentry_ok]. split; [lia|]. split; [unfold flat; cbn [Z.of_nat]; fold D; lia|].
rewrite adenot_SA. fold D. rewrite <- Hus, Z_to_bv_bv_unsigned.
cbn [edenot]. rewrite SEALED_W_bytes.
replace (firstn 8 SEALED_BYTES) with (map (fun j => nth j SEALED_BYTES (Z_to_bv 8 0)) (seq 0 8)) by reflexivity.
apply rdn_of_nth; [lia|]. intros j Hj. apply rdn1_overlay. rewrite Hus. apply BY. lia.
+
cbn [kentry_ok]. rewrite elenZ_lit by lia.
assert (HD8 : estart E (SA db (dk + 8)) = D + 8) by (unfold D, estart; cbn [a_base a_off]; lia).
rewrite HD8. split; [unfold flat; lia|].
intros i Hi. replace (D + 8 + i) with (D + Z.of_nat (Z.to_nat (8 + i))) by lia.
rewrite BY by lia. f_equal. apply SEALED_BYTES_nth_hi. lia.
+
eapply w_know_ok_havoc; [exact HK0 | | apply wbytes_grows].
intros x Hx. rewrite elenZ_lit in Hx by lia. fold D in Hx. subst M'. apply wbytes_out; rewrite ?SEALED_BYTES_length; lia.
- exact Hk.
Qed.
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
forall args, node1_stmt SEGS A nx0 LIMIT TOP SINV argH FS0 always (fun cs => summary_popfree A nx0 cs args).
Proof.
intros SUM args cs cs' E R FULL model T HC _ Hn Hk.
pose proof HC as HKN. apply co_know in HKN.
set (M := MR E cs model FULL) in *.
unfold summary_popfree in Hn.
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
match goal with Hl : kwritable_x _ _ lb lk _ = true |- _ => rename Hl into Hwr end.
match type of Hn with Some ?x = Some _ => assert (Hcs : cs' = x) by congruence end. subst cs'. clear Hn.
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
destruct (kwritable_x_sound SEGS E M (kn cs) (kn cs) lb lk (ELit (4 * cnt)) HKN HKN Hwr) as (Wst & Wlo & Whi).
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
4: { intros R' FULL' model' HC' Hfs. apply (Hk E R' FULL' model' (conj (env_agree_refl _ _) (env_agree_refl _ _)) HC' Hfs). }
- rewrite Hpc. exact Hms.
-
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
-
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
Lemma shadow_of_den_s : forall E M k b n sb sk sn l,
know_ok SEGS E M k -> shadow_of A k b n = (sb, sk, sn) -> flat_x k sb sk l = true ->
estart E (SA sb sk) = shadow_off A + bv_unsigned (edenot E b) / 8
/\ elenZ E sn = bv_unsigned (edenot E n) / 8.
Proof.
intros E M k b n sb sk sn l HK Hsh Hfl. pose proof SHADOW_ok as SO. unfold shadow_ok in SO.
destruct (w_flat_x_sound E M k sb sk l HK Hfl) as (F1 & F2 & F3). pose proof (u64_range (edenot E l)) as Rl.
unfold shadow_of in Hsh.
destruct (split_lit (eadd (mkSrl k b 3) (ELit (shadow_off A)))) as [sb' sk'] eqn:Hss. injection Hsh as -> -> <-.
pose proof (u64_range (edenot E b)) as Rb. pose proof (u64_range (edenot E n)) as Rn. pose proof (u64_range (edenot E sb)) as Rsb.
assert (Usn : bv_unsigned (edenot E (mkSrl k n 3)) = bv_unsigned (edenot E n) / 8).
{ rewrite (mkSrl_denot SEGS E _ k n 3 (Z_to_bv 64 3) HK) by (rewrite u64_lit by lia; reflexivity).
rewrite u_srl64. rewrite u64_lit by lia. reflexivity. }
split; [|unfold elenZ; exact Usn].
pose proof (w_split_lit_denot E _ sb sk Hss) as D. unfold eadd in D. rewrite mkAlu_denot in D. cbn [edenot] in D.
apply (f_equal bv_unsigned) in D. rewrite u_add64 in D.
rewrite (mkSrl_denot SEGS E _ k b 3 (Z_to_bv 64 3) HK) in D by (rewrite u64_lit by lia; reflexivity).
rewrite u_srl64 in D.
unfold estart in *. cbn [a_base a_off] in *. unfold elenZ in F2.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
rewrite (u64_lit 3) in D by lia. rewrite (u64_lit (shadow_off A)) in D by lia.
change (2 ^ (3 mod 64)) with 8 in D.
rewrite (Z.mod_small (bv_unsigned (edenot E b) / 8 + shadow_off A)) in D by lia.
rewrite u64_lit in D by lia. lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.
Lemma stack_side_den_s : forall E, uE E e_sp0 = TOP + 8388608 ->
bv_unsigned (edenot E (fst stack_side)) = TOP /\ bv_unsigned (edenot E (snd stack_side)) = STACK_END - TOP.
Proof.
intros E Hsp. pose proof TOP_ok' as HT; unfold top_ok, CEIL in HT. unfold uE in Hsp. pose proof (u64_range (edenot E e_sp0)) as R.
unfold stack_side. cbn [fst snd]. unfold eadd, esub. rewrite !mkAlu_denot. cbn [alu64 alu edenot].
rewrite bv_add_unsigned, bv_sub_unsigned, Hsp. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64)%Z. unfold STACK_LO, STACK_END.
rewrite (Z_to_bv_unsigned 64 (-8388608)). unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64)%Z.
rewrite u64_lit by lia. split; [|rewrite Z.mod_small by lia; lia].
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.
Lemma spad_parse_sound : forall ms hb hl mL mG mH,
spad_parse A ms = Some (hb, hl, mL, mG, mH) ->
find_band A ms = Some (mL, mG, mH) /\ am_base mH = ELit hb /\ am_len mH = ELit hl.
Proof.
intros ms hb hl mL mG mH H. unfold spad_parse in H.
destruct (find_band A ms) as [[[mL' mG'] mH']|]; [|discriminate].
destruct (am_base mH') as [z| | | | | | |] eqn:E1; try discriminate.
destruct (am_len mH') as [w| | | | | | |] eqn:E2; try discriminate.
injection H as <- <- <- <- <-. auto.
Qed.
Lemma spad_fill0_sound : forall entry cmax,
fill_spec SEGS entry cmax ->
node1_stmt SEGS A nx0 LIMIT TOP SINV argH FS0 always (fun cs => spad_fill0 A nx0 cs entry cmax).
Proof.
intros entry cmax SUM cs cs' E R FULL model T HC _ Hn Hk.
pose proof HC as HKN. apply co_know in HKN.
set (M := MR E cs model FULL) in *.
pose proof TOP_ok' as HT; unfold top_ok, CEIL in HT. pose proof SHADOW_ok as SO; unfold shadow_ok in SO.
pose proof HULL_ok as HU; unfold hull_okP in HU; destruct HU as (HU0 & HU1 & HU2 & HU3).
unfold spad_fill0 in Hn.
destruct (Z.eqb (pc cs) entry) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
destruct (ret_lit cs) as [ret|] eqn:Hret; [|discriminate].
destruct (reg_lit cs 11) as [c|] eqn:H11; [|discriminate].
destruct (spad_parse A (a_maps cs)) as [[[[[hb hl] mL] mG] mH]|] eqn:Hparse; [|discriminate].
destruct (spad_parse_sound (a_maps cs) hb hl mL mG mH Hparse) as (Hband & HhB & HhL).
destruct (split_lit (reg cs 10)) as [db dk] eqn:Hspl.
match type of Hn with (if negb ?cnd then _ else _) = _ => destruct cnd eqn:Hc1; [|discriminate] end. cbn [negb] in Hn.
destruct (shadow_of A (kn cs) (fst stack_side) (snd stack_side)) as [[cb ck] cn] eqn:Hshc.
destruct (base_range (kn cs) P0b) as [[plo phi]|] eqn:Hbr; [|discriminate].
destruct (xhi (kn cs) (reg cs 12)) as [nhi|] eqn:Hnhi; [|discriminate].
destruct (xlo (kn cs) (reg cs 12)) as [nlo|] eqn:Hnlo; [|discriminate].
destruct (spad_cond A cs db dk (reg cs 12) cb ck mL mG mH hb hl plo phi nhi nlo) eqn:Hc2; [|discriminate].
unfold spad_cond in Hc2.
apply andb_prop in Hc1 as [Hc1 Hins]. apply andb_prop in Hc1 as [Hc1 Hc0]. apply andb_prop in Hc1 as [Hc8 Hcm].
apply Z.eqb_eq in Hc8. apply Z.ltb_lt in Hcm. apply Z.leb_le in Hc0.
apply andb_prop in Hc2 as [Hc2 Hgh]. apply andb_prop in Hc2 as [Hc2 Hvis]. apply andb_prop in Hc2 as [Hc2 Hwrc].
apply andb_prop in Hc2 as [Hc2 Hflc]. apply andb_prop in Hc2 as [Hc2 Hstk]. apply andb_prop in Hc2 as [Hc2 Hlin].
apply andb_prop in Hc2 as [Hc2 Hal]. apply andb_prop in Hc2 as [Hc2 Hfl]. apply andb_prop in Hc2 as [Hc2 Hn4096].
apply andb_prop in Hc2 as [Hc2 Hnlo0]. apply andb_prop in Hc2 as [Hc2 Hoffal]. apply andb_prop in Hc2 as [Hc2 Hp0nn].
apply andb_prop in Hc2 as [Hc2 Hcont2]. apply andb_prop in Hc2 as [Hc2 Hcont1]. apply andb_prop in Hc2 as [Hc2 Hhl64].
apply andb_prop in Hc2 as [Hc2 Hhb0]. apply andb_prop in Hc2 as [Hnfog Hkind].
apply negb_true_iff in Hnfog. apply mkind_eqb_eq in Hkind.
apply Z.leb_le in Hhb0. apply Z.ltb_lt in Hhl64. apply Z.leb_le in Hcont1. apply Z.leb_le in Hcont2. apply Z.leb_le in Hp0nn.
apply Z.eqb_eq in Hoffal. apply Z.ltb_lt in Hnlo0. apply Z.leb_le in Hn4096. apply Z.leb_le in Hal. unfold two64 in Hhl64.
unfold P0k, STACK_LO in Hcont1, Hcont2, Hp0nn. change ((-8388608) / 8) with (-1048576) in Hcont1, Hcont2, Hp0nn.
destruct (ret_lit_sound E cs R FULL model ret HC Hret) as (R1 & Hrok & Hretr).
destruct (w_reg_lit_sound E cs R FULL model 11 c HC ltac:(lia) H11) as [R11 Hc].
pose proof (w_reg_sound E cs R FULL model 10 HC ltac:(lia)) as R10.
pose proof (w_reg_sound E cs R FULL model 12 HC ltac:(lia)) as R12.
pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hnlo) as Hnlo'.
pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hnhi) as Hnhi'.
set (s := edenot E (reg cs 10)) in *. set (nw := edenot E (reg cs 12)) in *. set (n := bv_unsigned nw) in *.
pose proof (u64_range nw) as Hnr. fold n in Hnr.
assert (Hnwn : Z_to_bv 64 n = nw) by (apply Z_to_bv_bv_unsigned).
set (s0 := estart E (SA db dk)).
destruct (w_flat_x_sound E M (kn cs) db dk (reg cs 12) HKN Hfl) as (F1 & F2 & F3). fold nw n s0 in F2, F3. fold s0 in F1.
assert (Hus : bv_unsigned s = s0) by (unfold s; rewrite (w_split_lit_denot E (reg cs 10) db dk Hspl); apply u64_lit; unfold s0, estart in *; cbn [a_base a_off] in *; lia).
assert (Hse : Z_to_bv 64 s0 = s) by (rewrite <- Hus; apply Z_to_bv_bv_unsigned).
assert (Hlen : elenZ E (reg cs 12) = n) by reflexivity.
pose proof (xinside_sound SEGS E M (kn cs) db dk (reg cs 12) P0b (P0k A) (ELit 4096) HKN Hins) as [I1 I2].
fold s0 in I1, I2. rewrite Hlen in I2. rewrite (APSG.elenZ_lit E 4096) in I2 by lia.
set (p0 := estart E (SA P0b (P0k A))) in *.
pose proof (base_range_sound SEGS E M (kn cs) P0b plo phi HKN Hbr) as [P1 P2].
destruct (SINV_s1 E FULL (co_sinv _ _ _ _ _ _ _ _ _ _ _ _ HC)) as (Usp & Us1 & Ual).
set (q1 := (TOP + 8388608) / 32768) in *.
assert (Q1 : 4294901760 <= q1 <= 4294967296).
{ unfold q1. clear - HT. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
assert (UP0b : bv_unsigned (edenot E P0b) = 4096 * q1).
{ unfold P0b, escale. rewrite mkMd_denot. rewrite u_mul64. unfold uE in Us1. rewrite Us1. cbn [edenot]. rewrite u64_lit by lia.
apply Z.mod_small. unfold q1.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
assert (Ep0 : p0 = 4096 * q1 + shadow_off A - 1048576).
{ unfold p0, estart. cbn [a_base a_off]. rewrite UP0b. unfold P0k, STACK_LO. change ((-8388608) / 8) with (-1048576). lia. }
set (st := shadow_off A + TOP / 8).
assert (ST : p0 <= st <= p0 + 4094 /\ p0 mod 4096 = 0 /\ TOP mod 8 = 0).
{ unfold st. rewrite Ep0. unfold q1.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). clear - Ual HT Hoffal SO. lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
destruct ST as (ST & P0al & TOP8).
rewrite UP0b in P1, P2.
assert (Hp0hi : p0 + 4096 <= shadow_off A + 17592186044416).
{ rewrite Ep0. unfold q1. clear - HT. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
assert (HinStk : In stack_side (a_vis cs)).
{ apply existsb_exists in Hstk as [p [Hp Heq]]. unfold pair_eqb in Heq. apply andb_prop in Heq as [E1 E2].
apply expr_eqb_eq in E1. apply expr_eqb_eq in E2. destruct p as [p1 p2]. cbn [fst snd] in E1, E2. subst p1 p2. exact Hp. }
destruct (stack_side_den_s E Usp) as [D1 D2].
destruct (shadow_of_den_s E M (kn cs) _ _ cb ck cn (ELit 4096) HKN Hshc Hflc) as [C1 _]. rewrite D1 in C1.
assert (C1' : estart E (SA cb ck) = st) by (unfold st; exact C1).
destruct (kwritable_x_sound SEGS E M (kn cs) (kn cs) cb ck (ELit 4096) HKN HKN Hwrc) as (Wst & Wlo & Whi).
rewrite (APSG.elenZ_lit E 4096) in Wst, Whi by lia. rewrite C1' in Wst, Wlo, Whi.
assert (WV : forall x : word, st <= bv_unsigned x < st + 4096 -> wview SEGS M x <> None).
{ intros x Hx. apply (store_ok_all SEGS M 4096%nat (Z_to_bv 64 st)); rewrite ?u64_lit by lia; [lia | apply (Wst 4096%nat); lia | lia]. }
destruct (APSG.find_band_sound A (a_maps cs) mL mG mH Hband) as (_ & _ & _ & (HHin & HHnf & _ & _ & _)).
assert (HmH : In (amap_den E mH) (vm_maps (m_vmmaps model))).
{ eapply maps_match_In; [exact (co_maps _ _ _ _ _ _ _ _ _ _ _ _ HC) | exact HHin | exact HHnf]. }
assert (UmH : bv_unsigned (edenot E (am_base mH)) = hb /\ bv_unsigned (edenot E (am_len mH)) = hl).
{ rewrite HhB, HhL. cbn [edenot]. rewrite !u64_lit by lia. split; reflexivity. }
destruct UmH as [UmH1 UmH2].
pose proof (proj1 (Forall_forall _ _) (co_bounds _ _ _ _ _ _ _ _ _ _ _ _ HC) _ HmH) as (B1 & B2 & B3 & B4 & B5).
cbn [amap_den fst snd] in B1, B2, B3, B4, B5. rewrite ?UmH1, ?UmH2 in B1. rewrite ?UmH1, ?UmH2 in B2. rewrite ?UmH1, ?UmH2 in B3.
rewrite ?UmH1, ?UmH2 in B4. rewrite ?UmH1, ?UmH2 in B5.
assert (BAND : forall x : word, p0 <= bv_unsigned x < p0 + 4096 ->
in_ivs (bv_unsigned x) (vm_maps (m_vmmaps model)) = true
/\ in_ivs (bv_unsigned x) (vm_noaccess (m_vmmaps model)) = false
/\ page_in_ranges (page_base x) (m_vm_lazy model) = true
/\ in_hull A (bv_unsigned x) = false /\ bv_unsigned x < TOP).
{ intros x Hx.
assert (Hxm : bv_unsigned (edenot E (am_base mH)) <= bv_unsigned x < bv_unsigned (edenot E (am_base mH)) + bv_unsigned (edenot E (am_len mH))) by (rewrite UmH1, UmH2; lia).
split; [eapply in_ivs_maps_match; [exact (co_maps _ _ _ _ _ _ _ _ _ _ _ _ HC) | exact HHin | exact HHnf | exact Hxm]|].
destruct (proj1 (Forall_forall _ _) (co_kinds _ _ _ _ _ _ _ _ _ _ _ _ HC) mH HHin Hkind x Hxm) as [N1 N2].
split; [exact N1|]. split; [exact N2|]. split; [|lia].
unfold in_hull. apply andb_false_iff. destruct B4 as [B4|B4]; [left; apply Z.leb_gt; lia | right; apply Z.ltb_ge; lia]. }
assert (U8 : bv_unsigned (edenot E (escale 8 (eaddz db (dk - shadow_off A)))) = 8 * (s0 - shadow_off A)).
{ unfold escale, eaddz. rewrite mkMd_denot, u_mul64, mkAlu_denot. cbn [edenot alu64 alu]. rewrite bv_add_unsigned.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite (u64_lit 8) by lia.
rewrite (Z_to_bv_unsigned 64 (dk - shadow_off A)). unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
unfold s0, estart. cbn [a_base a_off]. pose proof (u64_range (edenot E db)) as Rdb. unfold s0, estart in I1, I2. cbn [a_base a_off] in I1, I2.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
clear - Rdb I1 I2 Ep0 Q1 SO Hp0hi Hnr. rewrite Ep0 in I1, I2, Hp0hi. clearbody n p0 q1.
rewrite Z.add_mod_idemp_r by lia. rewrite (Z.mod_small (bv_unsigned (edenot E db) + (dk - shadow_off A))) by lia.
rewrite Z.mod_small by lia. lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
pose proof (lin_ge0_sound SEGS E M (kn cs) _ _ HKN Hlin) as LIN. cbn [xt_den] in LIN. rewrite U8 in LIN. unfold uE in Usp. rewrite Usp in LIN.
unfold STACK_LO in LIN.
set (bottom := 8 * (s0 - shadow_off A)) in *.
assert (BAL : bottom mod 4096 = 0).
{ pose proof (ealign_sound SEGS E M (kn cs) (escale 8 (eaddz db (dk - shadow_off A))) HKN) as [AR AL]. rewrite U8 in AL.
destruct AL as [m Hm]. rewrite Hm.
replace (ealign (kn cs) (escale 8 (eaddz db (dk - shadow_off A)))) with (12 + (ealign (kn cs) (escale 8 (eaddz db (dk - shadow_off A))) - 12)) by lia.
rewrite Z.pow_add_r by lia. change (2 ^ 12) with 4096. rewrite (Z.mul_comm 4096), Z.mul_assoc. apply Z_mod_mult. }
assert (KEY : forall e, e <= TOP -> e mod 4096 = 0 -> e <= bottom).
{ intros e He Hem. clear - He Hem LIN BAL.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
assert (Hbs : shadow_off A + bottom / 8 = s0).
{ unfold bottom. rewrite Z.mul_comm, Z.div_mul by lia. lia. }
assert (HID_core : forall x : word, st <= bv_unsigned x < p0 + 4096 -> HID E cs model x = false).
{ intros x Hx. destruct (BAND x ltac:(lia)) as (N1 & N2 & N3 & N4 & N5).
unfold hid. replace (argH E x) with false by (symmetry; destruct (argH E x) eqn:Ha; [pose proof (argH_high _ _ Ha); lia | reflexivity]).
cbn [orb]. apply negb_false_iff. unfold vis. rewrite N1, N2, N3. cbn [negb andb].
assert (Hsh : in_sh A E cs (bv_unsigned x) = true).
{ unfold in_sh. apply existsb_exists. exists stack_side. split; [exact HinStk|]. unfold sh_lo, sh_hi, uE. rewrite D1, D2. unfold STACK_END.
apply andb_true_intro. split; [apply Z.leb_le; unfold st in *; lia | apply Z.ltb_lt].
replace (TOP + (140737488355328 - TOP)) with 140737488355328 by lia. change (140737488355328 / 8) with 17592186044416. lia. }
unfold in_allow. rewrite Hsh. rewrite !orb_true_r. reflexivity. }
assert (HID_pad : forall x : word, s0 <= bv_unsigned x < s0 + n -> bv_unsigned x < st -> HID E cs model x = true).
{ intros x Hx Hxst. destruct (BAND x ltac:(lia)) as (N1 & N2 & N3 & N4 & N5).
unfold hid. apply orb_true_iff. right. apply negb_true_iff. unfold vis. rewrite N4, N1, N2, N3.
replace (TOP <=? bv_unsigned x) with false by (symmetry; apply Z.leb_gt; lia). cbn [orb negb andb].
unfold in_allow. apply orb_false_iff. split.
-
unfold in_vis. apply existsb_false_forall. intros p Hp.
pose proof (proj1 (forallb_forall _ _) Hvis p Hp) as Hpp. cbv beta in Hpp. apply orb_prop in Hpp as [Heq|Hpp].
+ unfold pair_eqb in Heq. apply andb_prop in Heq as [E1 E2]. apply expr_eqb_eq in E1. apply expr_eqb_eq in E2.
destruct p as [p1 p2]. cbn [fst snd] in E1, E2 |- *. subst p1 p2. unfold uE. rewrite D1.
apply andb_false_iff. left. apply Z.leb_gt. lia.
+ destruct (split_lit (fst p)) as [pb pk] eqn:Hps. apply andb_prop in Hpp as [Hpp _]. apply andb_prop in Hpp as [Hpf Hap].
destruct (w_flat_x_sound E M (kn cs) pb pk (snd p) HKN Hpf) as (Fp1 & Fp2 & Fp3).
pose proof (u_of_split E (fst p) pb pk Hps ltac:(lia)) as Up.
pose proof (ranges_apart_x_sound SEGS E M (kn cs) _ _ _ _ _ _ HKN Hap) as AP. fold s0 in AP. rewrite Hlen in AP. unfold elenZ in AP.
unfold uE. rewrite Up. apply andb_false_iff. destruct AP as [AP|AP]; [right; apply Z.ltb_ge; lia | left; apply Z.leb_gt; lia].
-
unfold in_sh. apply existsb_false_forall. intros p Hp.
pose proof (proj1 (forallb_forall _ _) Hvis p Hp) as Hpp. cbv beta in Hpp. apply orb_prop in Hpp as [Heq|Hpp].
+ unfold pair_eqb in Heq. apply andb_prop in Heq as [E1 E2]. apply expr_eqb_eq in E1. apply expr_eqb_eq in E2.
destruct p as [p1 p2]. cbn [fst snd] in E1, E2 |- *. subst p1 p2. unfold sh_lo, uE. cbn [fst snd]. rewrite D1.
apply andb_false_iff. left. apply Z.leb_gt. unfold st in Hxst. lia.
+ destruct (split_lit (fst p)) as [pb pk] eqn:Hps. apply andb_prop in Hpp as [Hpp Hin3]. apply andb_prop in Hpp as [Hpf Hap].
destruct (w_flat_x_sound E M (kn cs) pb pk (snd p) HKN Hpf) as (Fp1 & Fp2 & Fp3).
pose proof (u_of_split E (fst p) pb pk Hps ltac:(lia)) as Up.
apply andb_false_iff. right. apply Z.ltb_ge. unfold sh_hi, uE. rewrite Up.
apply orb_prop in Hin3 as [Hin3|Hin3].
*
unfold inside_nonband in Hin3. apply existsb_exists in Hin3 as [m [Hm Hmm]].
apply andb_prop in Hmm as [Hmm Hxi]. apply andb_prop in Hmm as [Hmm _]. apply andb_prop in Hmm as [Hmm _]. apply andb_prop in Hmm as [Hmf _].
apply negb_true_iff in Hmf.
pose proof (xinside_sound SEGS E M (kn cs) pb pk (snd p) (am_base m) 0 (am_len m) HKN Hxi) as [X1 X2].
unfold estart in X1 at 1. unfold estart in X2 at 2. cbn [a_base a_off] in X1, X2. rewrite Z.add_0_r in X1, X2. unfold elenZ in X2.
assert (Hmv : In (amap_den E m) (vm_maps (m_vmmaps model))) by (eapply maps_match_In; [exact (co_maps _ _ _ _ _ _ _ _ _ _ _ _ HC) | exact Hm | exact Hmf]).
pose proof (proj1 (Forall_forall _ _) (co_bounds _ _ _ _ _ _ _ _ _ _ _ _ HC) _ Hmv) as (M1 & M2 & M3 & M4 & M5). cbn [amap_den fst snd] in M1, M2, M3, M4, M5.
assert (ME : bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m)) <= bottom).
{ apply KEY; [exact M5|]. clear - M2 M3. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
clear - ME X1 X2 Hbs Hx Fp1. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
*
unfold sh_below in Hin3. destruct (xhi (kn cs) (fst p)) as [ph|] eqn:Hph; [|discriminate].
destruct (xhi (kn cs) (snd p)) as [lh|] eqn:Hlh; [|discriminate]. destruct (base_range (kn cs) db) as [[dlo dhi]|] eqn:Hdb; [|discriminate].
apply andb_prop in Hin3 as [Hin3 Hbl]. apply andb_prop in Hin3 as [Hph0 Hlh0]. apply Z.leb_le in Hbl. apply Z.leb_le in Hph0. apply Z.leb_le in Hlh0.
pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hph) as Xp. pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hlh) as Xl.
pose proof (base_range_sound SEGS E M (kn cs) db dlo dhi HKN Hdb) as [Db _]. rewrite <- Up.
unfold s0, estart in Hx. cbn [a_base a_off] in Hx. pose proof (u64_range (edenot E (fst p))). pose proof (u64_range (edenot E (snd p))).
clear - Xp Xl Db Hbl Hx H H0. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
assert (GH_pad : forall x : word, s0 <= bv_unsigned x < s0 + n -> in_ghost E cs (bv_unsigned x) = false).
{ intros x Hx. unfold in_ghost. apply existsb_false_forall. intros q Hq.
pose proof (proj1 (forallb_forall _ _) Hgh q Hq) as Hqq. cbv beta in Hqq. destruct (split_lit (fst q)) as [qb qk] eqn:Hqs.
apply andb_prop in Hqq as [Hqf Hap]. destruct (w_flat_x_sound E M (kn cs) qb qk (snd q) HKN Hqf) as (Fq1 & Fq2 & Fq3).
pose proof (u_of_split E (fst q) qb qk Hqs ltac:(lia)) as Uq.
pose proof (ranges_apart_x_sound SEGS E M (kn cs) _ _ _ _ _ _ HKN Hap) as AP. fold s0 in AP. rewrite Hlen in AP. unfold elenZ in AP.
unfold uE. rewrite Uq. apply andb_false_iff. destruct AP as [AP|AP]; [right; apply Z.ltb_ge; lia | left; apply Z.leb_gt; lia]. }
assert (ZERO_pad : forall x : word, s0 <= bv_unsigned x < s0 + n -> bv_unsigned x < st -> FULL x = Some (Z_to_bv 8 0)).
{ intros x Hx Hxst. destruct (BAND x ltac:(lia)) as (N1 & N2 & N3 & _).
exact (co_zero _ _ _ _ _ _ _ _ _ _ _ _ HC x (HID_pad x Hx Hxst) N1 N2 N3 (GH_pad x Hx)). }
set (Hh := fun a : word => (HID E cs model a && negb ((p0 <=? bv_unsigned a) && (bv_unsigned a <? st)))%bool).
set (Mp := mrestrict Hh FULL).
assert (HSUB : forall a, Hh a = true -> HID E cs model a = true) by (intros a Ha; unfold Hh in Ha; apply andb_prop in Ha as [Ha _]; exact Ha).
assert (HhOFF : H_off_segments SEGS Hh) by (intros a Ha; exact (w_H_off_segments_cs E cs model a (HSUB a Ha))).
assert (HLC : lazy_cover Hh (m_vm_lazy model) (allowA A E cs)).
{ intros w Hlz Hw. unfold Hh in Hw. apply andb_false_iff in Hw as [Hw|Hw]; [exact (w_lazy_cover_cs E cs R FULL model HC w Hlz Hw)|].
apply negb_false_iff in Hw. apply andb_prop in Hw as [W1 W2]. apply Z.leb_le in W1. apply Z.ltb_lt in W2.
pose proof (w_page_base_le w) as (PB1 & PB2 & PB3).
unfold page_allowedb, allowA. apply existsb_exists. exists (pagedown (sh_lo A E stack_side), pageup (sh_hi A E stack_side)). split.
- apply in_flat_map. exists stack_side. split; [apply in_or_app; left; exact HinStk|]. right. left. reflexivity.
- cbn [fst snd]. unfold sh_lo, sh_hi, uE, page_size. rewrite D1, D2. unfold STACK_END.
replace (TOP + (140737488355328 - TOP)) with 140737488355328 by lia. change (140737488355328 / 8) with 17592186044416.
apply andb_true_intro. unfold pagedown, pageup. unfold st in *. split; apply Z.leb_le.
+ clear - W1 W2 PB1 PB2 PB3 ST P0al. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
+ clear - W1 W2 PB1 PB2 PB3 ST P0al Hp0hi. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
assert (STP : store_ok SEGS Mp s (Z.to_nat n) = true).
{ apply store_ok_of_all; [rewrite Hus, Z2Nat.id by lia; lia|]. intros x Hx. rewrite Hus, Z2Nat.id in Hx by lia.
unfold wview, Mp, mrestrict, Hh. cbn beta. destruct (Z_lt_dec (bv_unsigned x) st) as [Hlt|Hge].
- rewrite (HID_pad x Hx Hlt). rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. cbn [andb negb].
rewrite (ZERO_pad x Hx Hlt). discriminate.
- rewrite (HID_core x) by lia. cbn [andb].
pose proof (WV x ltac:(lia)) as WVx. unfold wview, M, Mr, mrestrict in WVx. rewrite (HID_core x) in WVx by lia. exact WVx. }
destruct (SUM Mp s (Z_to_bv 64 c) n R (Z_to_bv 64 ret) ltac:(lia) ltac:(rewrite Hus; lia) STP
ltac:(rewrite u64_lit by (unfold two64 in Hc; lia); lia) Hrok R1 R10 R11 ltac:(rewrite Hnwn; exact R12))
as (regs' & Hms & Hkept & Ha0).
rewrite (u64_lit c) in Hms by (unfold two64 in Hc; lia).
assert (Zc : Z_to_bv 8 c = Z_to_bv 8 0) by (rewrite <- (Z_to_bv8_mod c), Hc8; reflexivity).
rewrite Zc in Hms.
set (MR' := wbytes Mp s (repeat (Z_to_bv 8 0) (Z.to_nat n))) in Hms.
assert (MR'_in : forall a : word, s0 <= bv_unsigned a < s0 + n -> MR' a = Some (Z_to_bv 8 0)).
{ intros a Ha. unfold MR'. replace a with (Z_to_bv 64 (bv_unsigned s + (bv_unsigned a - s0))) by (apply bv_eq; rewrite u64_lit; pose proof (u64_range a); lia).
apply wbytes_fill_at; rewrite ?Hus; lia. }
assert (MR'_out : forall a : word, bv_unsigned a < s0 \/ s0 + n <= bv_unsigned a -> MR' a = Mp a).
{ intros a Ha. unfold MR'. apply wbytes_out; rewrite repeat_length, Z2Nat.id, Hus by lia; lia. }
unfold after_call in Hn.
match type of Hn with context [if ?c then _ else _] => destruct c eqn:Hac; [|discriminate] end.
apply andb_prop in Hac as [Hac Hrvv]. apply andb_prop in Hac as [Hfresh Hkv]. injection Hn as <-.
destruct (w_fresh_ok_parts cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
set (E' := ext_call E (nxt cs) regs'). pose proof (ext_call_agree E (nxt cs) regs') as Hag. fold E' in Hag.
eapply (call_core_H Hh cs E E' R FULL model T ret _ (spad_keep (kn cs) cb ck cn ++ kn_havoc (kn cs) db dk (reg cs 12)) _ regs' MR' HC Hfresh Hag HhOFF HLC).
- rewrite Hpc. exact Hms.
-
intros a Hha Hhid. unfold Hh in Hha. rewrite Hhid in Hha. cbn [andb] in Hha. apply negb_false_iff in Hha.
apply andb_prop in Hha as [A1 A2]. apply Z.leb_le in A1. apply Z.ltb_lt in A2.
destruct (Z_lt_dec (bv_unsigned a) s0) as [Hl|Hr]; [|destruct (Z_lt_dec (bv_unsigned a) (s0 + n)) as [Hi|Ho]].
+ rewrite MR'_out by lia. unfold Mp, mrestrict, Hh. rewrite Hhid. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
+ rewrite (MR'_in a) by lia. symmetry. apply ZERO_pad; lia.
+ rewrite MR'_out by lia. unfold Mp, mrestrict, Hh. rewrite Hhid. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
- apply (regs_after_call E _ R regs' (nxt cs) (Some (reg cs 10)) (co_regs _ _ _ _ _ _ _ _ _ _ _ _ HC) Fsr Hkept).
split; [exact Hrvv | exact Ha0].
- eapply know_ok_agree'; [exact Hag | exact Hkv |].
apply Forall_app. split.
{
unfold spad_keep. destruct (existsb (kentry_eqb (KZero (SA cb ck) cn)) (kn cs)) eqn:Hcore; [|constructor].
apply existsb_exists in Hcore as (K0 & HK0 & HKe). apply kentry_eqb_eq in HKe. subst K0.
pose proof (proj1 (Forall_forall _ _) HKN _ HK0) as [CF CZ]. constructor; [|constructor]. split; [exact CF|].
intros i Hi. pose proof (CZ i Hi) as Zi. unfold M, Mr, mrestrict in Zi. unfold mrestrict, munrestrict.
set (x := Z_to_bv 64 (estart E (SA cb ck) + i)) in *.
destruct (HID E cs model x) eqn:Hhx; [discriminate Zi|].
replace (Hh x) with false by (unfold Hh; rewrite Hhx; reflexivity).
destruct (Z_lt_dec (bv_unsigned x) s0) as [Hl|Hr]; [|destruct (Z_lt_dec (bv_unsigned x) (s0 + n)) as [Hi2|Ho]].
* rewrite MR'_out by lia. unfold Mp, mrestrict. replace (Hh x) with false by (unfold Hh; rewrite Hhx; reflexivity). exact Zi.
* rewrite (MR'_in x) by lia. reflexivity.
* rewrite MR'_out by lia. unfold Mp, mrestrict. replace (Hh x) with false by (unfold Hh; rewrite Hhx; reflexivity). exact Zi. }
eapply w_know_ok_havoc; [exact HKN | |].
+ intros x Hx. fold s0 in Hx. rewrite Hlen in Hx. unfold M, Mr, mrestrict, munrestrict.
destruct (HID E cs model x) eqn:Hhx; [reflexivity|].
replace (Hh x) with false by (unfold Hh; rewrite Hhx; reflexivity).
rewrite MR'_out by lia. unfold Mp, mrestrict. replace (Hh x) with false by (unfold Hh; rewrite Hhx; reflexivity). reflexivity.
+ intros x Hx. unfold M, Mr, mrestrict in Hx. unfold mrestrict, munrestrict.
destruct (HID E cs model x) eqn:Hhx; [exact Hx|].
replace (Hh x) with false by (unfold Hh; rewrite Hhx; reflexivity).
destruct (Z_lt_dec (bv_unsigned x) s0) as [Hl|Hr]; [|destruct (Z_lt_dec (bv_unsigned x) (s0 + n)) as [Hi|Ho]].
* rewrite MR'_out by lia. unfold Mp, mrestrict. replace (Hh x) with false by (unfold Hh; rewrite Hhx; reflexivity). exact Hx.
* rewrite (MR'_in x) by lia. discriminate.
* rewrite MR'_out by lia. unfold Mp, mrestrict. replace (Hh x) with false by (unfold Hh; rewrite Hhx; reflexivity). exact Hx.
- intros R' FULL' model' HC' Hfs. apply (Hk E' R' FULL' model'); [| exact HC' | exact Hfs].
split; [eapply w_env_agree_le; [exact Hag | exact Fle] | exact Hag].
Qed.
Lemma spad_fillz_sound : forall entry cmax,
fill_spec SEGS entry cmax ->
node1_stmt SEGS A nx0 LIMIT TOP SINV argH FS0 always (fun cs => spad_fillz A nx0 cs entry cmax).
Proof.
intros entry cmax SUM cs cs' E R FULL model T HC _ Hn Hk.
pose proof HC as HKN. apply co_know in HKN.
set (M := MR E cs model FULL) in *.
pose proof TOP_ok' as HT; unfold top_ok, CEIL in HT. pose proof SHADOW_ok as SO; unfold shadow_ok in SO.
pose proof HULL_ok as HU; unfold hull_okP in HU; destruct HU as (HU0 & HU1 & HU2 & HU3).
unfold spad_fillz in Hn.
destruct (Z.eqb (pc cs) entry) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
destruct (ret_lit cs) as [ret|] eqn:Hret; [|discriminate].
destruct (reg_lit cs 11) as [c|] eqn:H11; [|discriminate].
destruct (spad_parse A (a_maps cs)) as [[[[[hb hl] mL] mG] mH]|] eqn:Hparse; [|discriminate].
destruct (spad_parse_sound (a_maps cs) hb hl mL mG mH Hparse) as (Hband & HhB & HhL).
destruct (split_lit (reg cs 10)) as [db dk] eqn:Hspl.
match type of Hn with (if negb ?cnd then _ else _) = _ => destruct cnd eqn:Hc1; [|discriminate] end. cbn [negb] in Hn.
destruct (shadow_of A (kn cs) (fst stack_side) (snd stack_side)) as [[cb ck] cn] eqn:Hshc.
destruct (base_range (kn cs) P0b) as [[plo phi]|] eqn:Hbr; [|discriminate].
destruct (xhi (kn cs) (reg cs 12)) as [nhi|] eqn:Hnhi; [|discriminate].
destruct (xlo (kn cs) (reg cs 12)) as [nlo|] eqn:Hnlo; [|discriminate].
destruct (spad_condz A cs db dk (reg cs 12) cb ck cn mL mG mH hb hl plo phi nhi nlo) eqn:Hc2; [|discriminate].
unfold spad_condz in Hc2.
apply andb_prop in Hc1 as [Hc1 Hc0]. apply andb_prop in Hc1 as [Hc8 Hcm].
apply Z.eqb_eq in Hc8. apply Z.ltb_lt in Hcm. apply Z.leb_le in Hc0.
apply andb_prop in Hc2 as [Hc2 Hgh]. apply andb_prop in Hc2 as [Hc2 Hvis]. apply andb_prop in Hc2 as [Hc2 Hcore]. apply andb_prop in Hc2 as [Hc2 Hwrc].
apply andb_prop in Hc2 as [Hc2 Hflc]. apply andb_prop in Hc2 as [Hc2 Hstk]. apply andb_prop in Hc2 as [Hc2 HlinE]. apply andb_prop in Hc2 as [Hc2 HlinP].
apply andb_prop in Hc2 as [Hc2 Hlin].
apply andb_prop in Hc2 as [Hc2 Hal]. apply andb_prop in Hc2 as [Hc2 Hfl]. apply andb_prop in Hc2 as [Hc2 Hn4096].
apply andb_prop in Hc2 as [Hc2 Hnlo0]. apply andb_prop in Hc2 as [Hc2 Hoffal]. apply andb_prop in Hc2 as [Hc2 Hp0nn].
apply andb_prop in Hc2 as [Hc2 Hcont2]. apply andb_prop in Hc2 as [Hc2 Hcont1]. apply andb_prop in Hc2 as [Hc2 Hhl64].
apply andb_prop in Hc2 as [Hc2 Hhb0]. apply andb_prop in Hc2 as [Hnfog Hkind].
apply negb_true_iff in Hnfog. apply mkind_eqb_eq in Hkind.
apply Z.leb_le in Hhb0. apply Z.ltb_lt in Hhl64. apply Z.leb_le in Hcont1. apply Z.leb_le in Hcont2. apply Z.leb_le in Hp0nn.
apply Z.eqb_eq in Hoffal. apply Z.ltb_lt in Hnlo0. apply Z.leb_le in Hn4096. apply Z.leb_le in Hal. unfold two64 in Hhl64.
unfold P0k, STACK_LO in Hcont1, Hp0nn. change ((-8388608) / 8) with (-1048576) in Hcont1, Hp0nn.
destruct (ret_lit_sound E cs R FULL model ret HC Hret) as (R1 & Hrok & Hretr).
destruct (w_reg_lit_sound E cs R FULL model 11 c HC ltac:(lia) H11) as [R11 Hc].
pose proof (w_reg_sound E cs R FULL model 10 HC ltac:(lia)) as R10.
pose proof (w_reg_sound E cs R FULL model 12 HC ltac:(lia)) as R12.
pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hnlo) as Hnlo'.
pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hnhi) as Hnhi'.
set (s := edenot E (reg cs 10)) in *. set (nw := edenot E (reg cs 12)) in *. set (n := bv_unsigned nw) in *.
pose proof (u64_range nw) as Hnr. fold n in Hnr.
assert (Hnwn : Z_to_bv 64 n = nw) by (apply Z_to_bv_bv_unsigned).
set (s0 := estart E (SA db dk)).
destruct (w_flat_x_sound E M (kn cs) db dk (reg cs 12) HKN Hfl) as (F1 & F2 & F3). fold nw n s0 in F2, F3. fold s0 in F1.
assert (Hus : bv_unsigned s = s0) by (unfold s; rewrite (w_split_lit_denot E (reg cs 10) db dk Hspl); apply u64_lit; unfold s0, estart in *; cbn [a_base a_off] in *; lia).
assert (Hse : Z_to_bv 64 s0 = s) by (rewrite <- Hus; apply Z_to_bv_bv_unsigned).
assert (Hlen : elenZ E (reg cs 12) = n) by reflexivity.
pose proof (lin_ge0_sound SEGS E M (kn cs) _ _ HKN HlinP) as I1. cbn [xt_den] in I1.
pose proof (lin_ge0_sound SEGS E M (kn cs) _ _ HKN HlinE) as IE. cbn [xt_den] in IE.
set (p0 := estart E (SA P0b (P0k A))) in *.
assert (I1' : p0 <= s0) by (unfold p0, s0, estart; cbn [a_base a_off]; lia).
pose proof (base_range_sound SEGS E M (kn cs) P0b plo phi HKN Hbr) as [P1 P2].
destruct (SINV_s1 E FULL (co_sinv _ _ _ _ _ _ _ _ _ _ _ _ HC)) as (Usp & Us1 & Ual).
set (q1 := (TOP + 8388608) / 32768) in *.
assert (Q1 : 4294901760 <= q1 <= 4294967296).
{ unfold q1. clear - HT. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
assert (UP0b : bv_unsigned (edenot E P0b) = 4096 * q1).
{ unfold P0b, escale. rewrite mkMd_denot. rewrite u_mul64. unfold uE in Us1. rewrite Us1. cbn [edenot]. rewrite u64_lit by lia.
apply Z.mod_small. unfold q1.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
assert (Ep0 : p0 = 4096 * q1 + shadow_off A - 1048576).
{ unfold p0, estart. cbn [a_base a_off]. rewrite UP0b. unfold P0k, STACK_LO. change ((-8388608) / 8) with (-1048576). lia. }
set (st := shadow_off A + TOP / 8).
assert (ST : p0 <= st <= p0 + 4094 /\ p0 mod 4096 = 0 /\ TOP mod 8 = 0).
{ unfold st. rewrite Ep0. unfold q1.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). clear - Ual HT Hoffal SO. lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
destruct ST as (ST & P0al & TOP8).
rewrite UP0b in P1, P2.
assert (Hp0hi : p0 + 4096 <= shadow_off A + 17592186044416).
{ rewrite Ep0. unfold q1. clear - HT. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
assert (HinStk : In stack_side (a_vis cs)).
{ apply existsb_exists in Hstk as [p [Hp Heq]]. unfold pair_eqb in Heq. apply andb_prop in Heq as [E1 E2].
apply expr_eqb_eq in E1. apply expr_eqb_eq in E2. destruct p as [p1 p2]. cbn [fst snd] in E1, E2. subst p1 p2. exact Hp. }
destruct (stack_side_den_s E Usp) as [D1 D2].
destruct (shadow_of_den_s E M (kn cs) _ _ cb ck cn cn HKN Hshc Hflc) as [C1 C2]. rewrite D1 in C1. rewrite D2 in C2.
assert (C1' : estart E (SA cb ck) = st) by (unfold st; exact C1).
set (cend := shadow_off A + 17592186044416).
assert (CL : elenZ E cn = cend - st).
{ rewrite C2. unfold cend, st, STACK_END. clear - TOP8 HT. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
assert (I2 : s0 + n <= cend).
{ unfold elenZ in CL. unfold estart in C1'. cbn [a_base a_off] in C1'. unfold s0, estart, n, nw. cbn [a_base a_off]. lia. }
destruct (kwritable_x_sound SEGS E M (kn cs) (kn cs) cb ck cn HKN HKN Hwrc) as (Wst & Wlo & Whi).
rewrite CL in Wst, Whi. rewrite C1' in Wst, Wlo, Whi.
assert (WV : forall x : word, st <= bv_unsigned x < cend -> wview SEGS M x <> None).
{ intros x Hx. apply (store_ok_all SEGS M (Z.to_nat (cend - st)) (Z_to_bv 64 st)); rewrite ?u64_lit by lia; [rewrite Z2Nat.id by lia; lia | apply (Wst (Z.to_nat (cend - st))); rewrite Z2Nat.id by lia; lia | rewrite Z2Nat.id by lia; lia]. }
destruct (APSG.find_band_sound A (a_maps cs) mL mG mH Hband) as (_ & _ & _ & (HHin & HHnf & _ & _ & _)).
assert (HmH : In (amap_den E mH) (vm_maps (m_vmmaps model))).
{ eapply maps_match_In; [exact (co_maps _ _ _ _ _ _ _ _ _ _ _ _ HC) | exact HHin | exact HHnf]. }
assert (UmH : bv_unsigned (edenot E (am_base mH)) = hb /\ bv_unsigned (edenot E (am_len mH)) = hl).
{ rewrite HhB, HhL. cbn [edenot]. rewrite !u64_lit by lia. split; reflexivity. }
destruct UmH as [UmH1 UmH2].
pose proof (proj1 (Forall_forall _ _) (co_bounds _ _ _ _ _ _ _ _ _ _ _ _ HC) _ HmH) as (B1 & B2 & B3 & B4 & B5).
cbn [amap_den fst snd] in B1, B2, B3, B4, B5. rewrite ?UmH1, ?UmH2 in B1. rewrite ?UmH1, ?UmH2 in B2. rewrite ?UmH1, ?UmH2 in B3.
rewrite ?UmH1, ?UmH2 in B4. rewrite ?UmH1, ?UmH2 in B5.
assert (BAND : forall x : word, p0 <= bv_unsigned x < cend ->
in_ivs (bv_unsigned x) (vm_maps (m_vmmaps model)) = true
/\ in_ivs (bv_unsigned x) (vm_noaccess (m_vmmaps model)) = false
/\ page_in_ranges (page_base x) (m_vm_lazy model) = true
/\ in_hull A (bv_unsigned x) = false /\ bv_unsigned x < TOP).
{ intros x Hx.
assert (Hxm : bv_unsigned (edenot E (am_base mH)) <= bv_unsigned x < bv_unsigned (edenot E (am_base mH)) + bv_unsigned (edenot E (am_len mH))) by (rewrite UmH1, UmH2; lia).
split; [eapply in_ivs_maps_match; [exact (co_maps _ _ _ _ _ _ _ _ _ _ _ _ HC) | exact HHin | exact HHnf | exact Hxm]|].
destruct (proj1 (Forall_forall _ _) (co_kinds _ _ _ _ _ _ _ _ _ _ _ _ HC) mH HHin Hkind x Hxm) as [N1 N2].
split; [exact N1|]. split; [exact N2|]. split; [|lia].
unfold in_hull. apply andb_false_iff. destruct B4 as [B4|B4]; [left; apply Z.leb_gt; lia | right; apply Z.ltb_ge; lia]. }
assert (U8 : bv_unsigned (edenot E (escale 8 (eaddz db (dk - shadow_off A)))) = 8 * (s0 - shadow_off A)).
{ unfold escale, eaddz. rewrite mkMd_denot, u_mul64, mkAlu_denot. cbn [edenot alu64 alu]. rewrite bv_add_unsigned.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite (u64_lit 8) by lia.
rewrite (Z_to_bv_unsigned 64 (dk - shadow_off A)). unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
unfold s0, estart. cbn [a_base a_off]. pose proof (u64_range (edenot E db)) as Rdb.
pose proof I1' as J1. pose proof I2 as J2. unfold s0, estart, cend in J1, J2. cbn [a_base a_off] in J1, J2.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
clear - Rdb J1 J2 Ep0 Q1 SO Hnr. rewrite Ep0 in J1. clearbody n p0 q1.
rewrite Z.add_mod_idemp_r by lia. rewrite (Z.mod_small (bv_unsigned (edenot E db) + (dk - shadow_off A))) by lia.
rewrite Z.mod_small by lia. lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
pose proof (lin_ge0_sound SEGS E M (kn cs) _ _ HKN Hlin) as LIN. cbn [xt_den] in LIN. rewrite U8 in LIN. unfold uE in Usp. rewrite Usp in LIN.
unfold STACK_LO in LIN.
set (bottom := 8 * (s0 - shadow_off A)) in *.
assert (BAL : bottom mod 4096 = 0).
{ pose proof (ealign_sound SEGS E M (kn cs) (escale 8 (eaddz db (dk - shadow_off A))) HKN) as [AR AL]. rewrite U8 in AL.
destruct AL as [m Hm]. rewrite Hm.
replace (ealign (kn cs) (escale 8 (eaddz db (dk - shadow_off A)))) with (12 + (ealign (kn cs) (escale 8 (eaddz db (dk - shadow_off A))) - 12)) by lia.
rewrite Z.pow_add_r by lia. change (2 ^ 12) with 4096. rewrite (Z.mul_comm 4096), Z.mul_assoc. apply Z_mod_mult. }
assert (KEY : forall e, e <= TOP -> e mod 4096 = 0 -> e <= bottom).
{ intros e He Hem. clear - He Hem LIN BAL.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
assert (Hbs : shadow_off A + bottom / 8 = s0).
{ unfold bottom. rewrite Z.mul_comm, Z.div_mul by lia. lia. }
assert (HID_core : forall x : word, st <= bv_unsigned x < cend -> HID E cs model x = false).
{ intros x Hx. destruct (BAND x ltac:(lia)) as (N1 & N2 & N3 & N4 & N5).
unfold hid. replace (argH E x) with false by (symmetry; destruct (argH E x) eqn:Ha; [pose proof (argH_high _ _ Ha); lia | reflexivity]).
cbn [orb]. apply negb_false_iff. unfold vis. rewrite N1, N2, N3. cbn [negb andb].
assert (Hsh : in_sh A E cs (bv_unsigned x) = true).
{ unfold in_sh. apply existsb_exists. exists stack_side. split; [exact HinStk|]. unfold sh_lo, sh_hi, uE. rewrite D1, D2. unfold STACK_END.
apply andb_true_intro. split; [apply Z.leb_le; unfold st in *; lia | apply Z.ltb_lt].
replace (TOP + (140737488355328 - TOP)) with 140737488355328 by lia. change (140737488355328 / 8) with 17592186044416. lia. }
unfold in_allow. rewrite Hsh. rewrite !orb_true_r. reflexivity. }
assert (HID_pad : forall x : word, s0 <= bv_unsigned x < s0 + n -> bv_unsigned x < st -> HID E cs model x = true).
{ intros x Hx Hxst. destruct (BAND x ltac:(lia)) as (N1 & N2 & N3 & N4 & N5).
unfold hid. apply orb_true_iff. right. apply negb_true_iff. unfold vis. rewrite N4, N1, N2, N3.
replace (TOP <=? bv_unsigned x) with false by (symmetry; apply Z.leb_gt; lia). cbn [orb negb andb].
unfold in_allow. apply orb_false_iff. split.
-
unfold in_vis. apply existsb_false_forall. intros p Hp.
pose proof (proj1 (forallb_forall _ _) Hvis p Hp) as Hpp. cbv beta in Hpp. apply orb_prop in Hpp as [Heq|Hpp].
+ unfold pair_eqb in Heq. apply andb_prop in Heq as [E1 E2]. apply expr_eqb_eq in E1. apply expr_eqb_eq in E2.
destruct p as [p1 p2]. cbn [fst snd] in E1, E2 |- *. subst p1 p2. unfold uE. rewrite D1.
apply andb_false_iff. left. apply Z.leb_gt. lia.
+ destruct (split_lit (fst p)) as [pb pk] eqn:Hps. apply andb_prop in Hpp as [Hpp _]. apply andb_prop in Hpp as [Hpf Hap].
destruct (w_flat_x_sound E M (kn cs) pb pk (snd p) HKN Hpf) as (Fp1 & Fp2 & Fp3).
pose proof (u_of_split E (fst p) pb pk Hps ltac:(lia)) as Up.
pose proof (ranges_apart_x_sound SEGS E M (kn cs) _ _ _ _ _ _ HKN Hap) as AP. fold s0 in AP. rewrite Hlen in AP. unfold elenZ in AP.
unfold uE. rewrite Up. apply andb_false_iff. destruct AP as [AP|AP]; [right; apply Z.ltb_ge; lia | left; apply Z.leb_gt; lia].
-
unfold in_sh. apply existsb_false_forall. intros p Hp.
pose proof (proj1 (forallb_forall _ _) Hvis p Hp) as Hpp. cbv beta in Hpp. apply orb_prop in Hpp as [Heq|Hpp].
+ unfold pair_eqb in Heq. apply andb_prop in Heq as [E1 E2]. apply expr_eqb_eq in E1. apply expr_eqb_eq in E2.
destruct p as [p1 p2]. cbn [fst snd] in E1, E2 |- *. subst p1 p2. unfold sh_lo, uE. cbn [fst snd]. rewrite D1.
apply andb_false_iff. left. apply Z.leb_gt. unfold st in Hxst. lia.
+ destruct (split_lit (fst p)) as [pb pk] eqn:Hps. apply andb_prop in Hpp as [Hpp Hin3]. apply andb_prop in Hpp as [Hpf Hap].
destruct (w_flat_x_sound E M (kn cs) pb pk (snd p) HKN Hpf) as (Fp1 & Fp2 & Fp3).
pose proof (u_of_split E (fst p) pb pk Hps ltac:(lia)) as Up.
apply andb_false_iff. right. apply Z.ltb_ge. unfold sh_hi, uE. rewrite Up.
apply orb_prop in Hin3 as [Hin3|Hin3].
*
unfold inside_nonband in Hin3. apply existsb_exists in Hin3 as [m [Hm Hmm]].
apply andb_prop in Hmm as [Hmm Hxi]. apply andb_prop in Hmm as [Hmm _]. apply andb_prop in Hmm as [Hmm _]. apply andb_prop in Hmm as [Hmf _].
apply negb_true_iff in Hmf.
pose proof (xinside_sound SEGS E M (kn cs) pb pk (snd p) (am_base m) 0 (am_len m) HKN Hxi) as [X1 X2].
unfold estart in X1 at 1. unfold estart in X2 at 2. cbn [a_base a_off] in X1, X2. rewrite Z.add_0_r in X1, X2. unfold elenZ in X2.
assert (Hmv : In (amap_den E m) (vm_maps (m_vmmaps model))) by (eapply maps_match_In; [exact (co_maps _ _ _ _ _ _ _ _ _ _ _ _ HC) | exact Hm | exact Hmf]).
pose proof (proj1 (Forall_forall _ _) (co_bounds _ _ _ _ _ _ _ _ _ _ _ _ HC) _ Hmv) as (M1 & M2 & M3 & M4 & M5). cbn [amap_den fst snd] in M1, M2, M3, M4, M5.
assert (ME : bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m)) <= bottom).
{ apply KEY; [exact M5|]. clear - M2 M3. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
clear - ME X1 X2 Hbs Hx Fp1. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
*
unfold sh_below in Hin3. destruct (xhi (kn cs) (fst p)) as [ph|] eqn:Hph; [|discriminate].
destruct (xhi (kn cs) (snd p)) as [lh|] eqn:Hlh; [|discriminate]. destruct (base_range (kn cs) db) as [[dlo dhi]|] eqn:Hdb; [|discriminate].
apply andb_prop in Hin3 as [Hin3 Hbl]. apply andb_prop in Hin3 as [Hph0 Hlh0]. apply Z.leb_le in Hbl. apply Z.leb_le in Hph0. apply Z.leb_le in Hlh0.
pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hph) as Xp. pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hlh) as Xl.
pose proof (base_range_sound SEGS E M (kn cs) db dlo dhi HKN Hdb) as [Db _]. rewrite <- Up.
unfold s0, estart in Hx. cbn [a_base a_off] in Hx. pose proof (u64_range (edenot E (fst p))). pose proof (u64_range (edenot E (snd p))).
clear - Xp Xl Db Hbl Hx H H0. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
assert (GH_pad : forall x : word, s0 <= bv_unsigned x < s0 + n -> in_ghost E cs (bv_unsigned x) = false).
{ intros x Hx. unfold in_ghost. apply existsb_false_forall. intros q Hq.
pose proof (proj1 (forallb_forall _ _) Hgh q Hq) as Hqq. cbv beta in Hqq. destruct (split_lit (fst q)) as [qb qk] eqn:Hqs.
apply andb_prop in Hqq as [Hqf Hap]. destruct (w_flat_x_sound E M (kn cs) qb qk (snd q) HKN Hqf) as (Fq1 & Fq2 & Fq3).
pose proof (u_of_split E (fst q) qb qk Hqs ltac:(lia)) as Uq.
pose proof (ranges_apart_x_sound SEGS E M (kn cs) _ _ _ _ _ _ HKN Hap) as AP. fold s0 in AP. rewrite Hlen in AP. unfold elenZ in AP.
unfold uE. rewrite Uq. apply andb_false_iff. destruct AP as [AP|AP]; [right; apply Z.ltb_ge; lia | left; apply Z.leb_gt; lia]. }
assert (ZERO_pad : forall x : word, s0 <= bv_unsigned x < s0 + n -> bv_unsigned x < st -> FULL x = Some (Z_to_bv 8 0)).
{ intros x Hx Hxst. destruct (BAND x ltac:(lia)) as (N1 & N2 & N3 & _).
exact (co_zero _ _ _ _ _ _ _ _ _ _ _ _ HC x (HID_pad x Hx Hxst) N1 N2 N3 (GH_pad x Hx)). }
set (Hh := fun a : word => (HID E cs model a && negb ((p0 <=? bv_unsigned a) && (bv_unsigned a <? st)))%bool).
set (Mp := mrestrict Hh FULL).
assert (HSUB : forall a, Hh a = true -> HID E cs model a = true) by (intros a Ha; unfold Hh in Ha; apply andb_prop in Ha as [Ha _]; exact Ha).
assert (HhOFF : H_off_segments SEGS Hh) by (intros a Ha; exact (w_H_off_segments_cs E cs model a (HSUB a Ha))).
assert (HLC : lazy_cover Hh (m_vm_lazy model) (allowA A E cs)).
{ intros w Hlz Hw. unfold Hh in Hw. apply andb_false_iff in Hw as [Hw|Hw]; [exact (w_lazy_cover_cs E cs R FULL model HC w Hlz Hw)|].
apply negb_false_iff in Hw. apply andb_prop in Hw as [W1 W2]. apply Z.leb_le in W1. apply Z.ltb_lt in W2.
pose proof (w_page_base_le w) as (PB1 & PB2 & PB3).
unfold page_allowedb, allowA. apply existsb_exists. exists (pagedown (sh_lo A E stack_side), pageup (sh_hi A E stack_side)). split.
- apply in_flat_map. exists stack_side. split; [apply in_or_app; left; exact HinStk|]. right. left. reflexivity.
- cbn [fst snd]. unfold sh_lo, sh_hi, uE, page_size. rewrite D1, D2. unfold STACK_END.
replace (TOP + (140737488355328 - TOP)) with 140737488355328 by lia. change (140737488355328 / 8) with 17592186044416.
apply andb_true_intro. unfold pagedown, pageup. unfold st in *. split; apply Z.leb_le.
+ clear - W1 W2 PB1 PB2 PB3 ST P0al. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
+ clear - W1 W2 PB1 PB2 PB3 ST P0al Hp0hi. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
assert (STP : store_ok SEGS Mp s (Z.to_nat n) = true).
{ apply store_ok_of_all; [rewrite Hus, Z2Nat.id by lia; lia|]. intros x Hx. rewrite Hus, Z2Nat.id in Hx by lia.
unfold wview, Mp, mrestrict, Hh. cbn beta. destruct (Z_lt_dec (bv_unsigned x) st) as [Hlt|Hge].
- rewrite (HID_pad x Hx Hlt). rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. cbn [andb negb].
rewrite (ZERO_pad x Hx Hlt). discriminate.
- rewrite (HID_core x) by lia. cbn [andb].
pose proof (WV x ltac:(lia)) as WVx. unfold wview, M, Mr, mrestrict in WVx. rewrite (HID_core x) in WVx by lia. exact WVx. }
destruct (SUM Mp s (Z_to_bv 64 c) n R (Z_to_bv 64 ret) ltac:(lia) ltac:(rewrite Hus; lia) STP
ltac:(rewrite u64_lit by (unfold two64 in Hc; lia); lia) Hrok R1 R10 R11 ltac:(rewrite Hnwn; exact R12))
as (regs' & Hms & Hkept & Ha0).
rewrite (u64_lit c) in Hms by (unfold two64 in Hc; lia).
assert (Zc : Z_to_bv 8 c = Z_to_bv 8 0) by (rewrite <- (Z_to_bv8_mod c), Hc8; reflexivity).
rewrite Zc in Hms.
set (MR' := wbytes Mp s (repeat (Z_to_bv 8 0) (Z.to_nat n))) in Hms.
assert (MR'_in : forall a : word, s0 <= bv_unsigned a < s0 + n -> MR' a = Some (Z_to_bv 8 0)).
{ intros a Ha. unfold MR'. replace a with (Z_to_bv 64 (bv_unsigned s + (bv_unsigned a - s0))) by (apply bv_eq; rewrite u64_lit; pose proof (u64_range a); lia).
apply wbytes_fill_at; rewrite ?Hus; lia. }
assert (MR'_out : forall a : word, bv_unsigned a < s0 \/ s0 + n <= bv_unsigned a -> MR' a = Mp a).
{ intros a Ha. unfold MR'. apply wbytes_out; rewrite repeat_length, Z2Nat.id, Hus by lia; lia. }
unfold after_call in Hn.
match type of Hn with context [if ?c then _ else _] => destruct c eqn:Hac; [|discriminate] end.
apply andb_prop in Hac as [Hac Hrvv]. apply andb_prop in Hac as [Hfresh Hkv]. injection Hn as <-.
destruct (w_fresh_ok_parts cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
set (E' := ext_call E (nxt cs) regs'). pose proof (ext_call_agree E (nxt cs) regs') as Hag. fold E' in Hag.
eapply (call_core_H Hh cs E E' R FULL model T ret _ (kn cs) _ regs' MR' HC Hfresh Hag HhOFF HLC).
- rewrite Hpc. exact Hms.
-
intros a Hha Hhid. unfold Hh in Hha. rewrite Hhid in Hha. cbn [andb] in Hha. apply negb_false_iff in Hha.
apply andb_prop in Hha as [A1 A2]. apply Z.leb_le in A1. apply Z.ltb_lt in A2.
destruct (Z_lt_dec (bv_unsigned a) s0) as [Hl|Hr]; [|destruct (Z_lt_dec (bv_unsigned a) (s0 + n)) as [Hi|Ho]].
+ rewrite MR'_out by lia. unfold Mp, mrestrict, Hh. rewrite Hhid. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
+ rewrite (MR'_in a) by lia. symmetry. apply ZERO_pad; lia.
+ rewrite MR'_out by lia. unfold Mp, mrestrict, Hh. rewrite Hhid. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
- apply (regs_after_call E _ R regs' (nxt cs) (Some (reg cs 10)) (co_regs _ _ _ _ _ _ _ _ _ _ _ _ HC) Fsr Hkept).
split; [exact Hrvv | exact Ha0].
- eapply know_ok_agree'; [exact Hag | exact Hkv |].
replace (mrestrict (HID E cs model) (munrestrict Hh FULL MR')) with M; [exact HKN|].
apply functional_extensionality. intros x. unfold M, Mr, mrestrict, munrestrict.
destruct (HID E cs model x) eqn:Hhx; [reflexivity|].
replace (Hh x) with false by (unfold Hh; rewrite Hhx; reflexivity).
destruct (Z_lt_dec (bv_unsigned x) s0) as [Hl|Hr]; [|destruct (Z_lt_dec (bv_unsigned x) (s0 + n)) as [Hi2|Ho]].
+ rewrite MR'_out by lia. unfold Mp, mrestrict. replace (Hh x) with false by (unfold Hh; rewrite Hhx; reflexivity). reflexivity.
+ rewrite (MR'_in x) by lia.
destruct (Z_lt_dec (bv_unsigned x) st) as [Hlt|Hge]; [rewrite (HID_pad x ltac:(lia) Hlt) in Hhx; discriminate|].
apply existsb_exists in Hcore as (K0 & HK0 & HKe). apply kentry_eqb_eq in HKe. subst K0.
pose proof (proj1 (Forall_forall _ _) HKN _ HK0) as [CF CZ].
pose proof (CZ (bv_unsigned x - st) ltac:(rewrite CL; lia)) as Zi. rewrite C1' in Zi.
replace (st + (bv_unsigned x - st)) with (bv_unsigned x) in Zi by lia. rewrite Z_to_bv_bv_unsigned in Zi.
unfold M, Mr, mrestrict in Zi. rewrite Hhx in Zi. exact Zi.
+ rewrite MR'_out by lia. unfold Mp, mrestrict. replace (Hh x) with false by (unfold Hh; rewrite Hhx; reflexivity). reflexivity.
- intros R' FULL' model' HC' Hfs. apply (Hk E' R' FULL' model'); [| exact HC' | exact Hfs].
split; [eapply w_env_agree_le; [exact Hag | exact Fle] | exact Hag].
Qed.
Theorem node_x_sound_XIMemset :
fill_spec SEGS (x_imemset A) 256 -> x_stmt SEGS A nx0 LIMIT TOP SINV argH FS0 XIMemset.
Proof.
intros SUM args cs cs' E R FULL model T HC Hal Hn Hk. cbn [node_x] in Hn.
destruct (spad_fillz A nx0 cs (x_imemset A) 256) as [cs0|] eqn:Hsz.
{ injection Hn as <-. exact (spad_fillz_sound _ _ SUM cs cs0 E R FULL model T HC Hal Hsz Hk). }
destruct (spad_fill0 A nx0 cs (x_imemset A) 256) as [cs1|] eqn:Hsp.
- injection Hn as <-. exact (spad_fill0_sound _ _ SUM cs cs1 E R FULL model T HC Hal Hsp Hk).
- exact (summary_fill_sound _ _ SUM cs cs' E R FULL model T HC Hal Hn Hk).
Qed.
Theorem node_x_sound_XMemset :
fill_spec SEGS (x_memset A) two64 -> x_stmt SEGS A nx0 LIMIT TOP SINV argH FS0 XMemset.
Proof.
intros SUM args cs cs' E R FULL model T HC Hal Hn Hk. cbn [node_x] in Hn.
destruct (spad_fillz A nx0 cs (x_memset A) two64) as [cs0|] eqn:Hsz.
{ injection Hn as <-. exact (spad_fillz_sound _ _ SUM cs cs0 E R FULL model T HC Hal Hsz Hk). }
destruct (spad_fill0 A nx0 cs (x_memset A) two64) as [cs1|] eqn:Hsp.
- injection Hn as <-. exact (spad_fill0_sound _ _ SUM cs cs1 E R FULL model T HC Hal Hsp Hk).
- exact (summary_fill_sound _ _ SUM cs cs' E R FULL model T HC Hal Hn Hk).
Qed.
Theorem node_x_sound_XIMemcpy :
copy_spec SEGS (x_imemcpy A) -> x_stmt SEGS A nx0 LIMIT TOP SINV argH FS0 XIMemcpy.
Proof. intros SUM args. exact (summary_copy_sound _ SUM). Qed.
Theorem node_x_sound_XMemcpy :
copy_spec SEGS (x_memcpy A) -> x_stmt SEGS A nx0 LIMIT TOP SINV argH FS0 XMemcpy.
Proof. intros SUM args. exact (summary_copy_sound _ SUM). Qed.
Theorem node_x_sound_XMemIsZero :
miz_spec SEGS (x_memiszero A) -> x_stmt SEGS A nx0 LIMIT TOP SINV argH FS0 XMemIsZero.
Proof. intros SUM args. exact (summary_miz_sound SUM). Qed.
Theorem node_x_sound_XIStrncpy :
istrncpy_spec SEGS (x_istrncpy A) (x_sealed A) -> x_stmt SEGS A nx0 LIMIT TOP SINV argH FS0 XIStrncpy.
Proof. intros SUM args. exact (summary_istrncpy_sound SUM). Qed.
Theorem node_x_sound_XPopFree :
popfree_spec SEGS (x_popfree A) -> x_stmt SEGS A nx0 LIMIT TOP SINV argH FS0 XPopFree.
Proof. intros SUM args. exact (summary_popfree_sound SUM args). Qed.
Lemma w_cover_x_rd1 : forall fuel E M k b i stop,
know_ok SEGS E M k -> cover_x fuel k b i stop = true ->
forall j, (i <= j < stop)%Z -> (0 <= uE E b + j < 2 ^ 64)%Z /\ rd1 SEGS M (Z_to_bv 64 (uE E b + j)) <> None.
Proof. intros. eapply cover_x_rd1; try eassumption. Unshelve. all: aps_fill. Qed.
Lemma w_know_ok_cutout : forall E M M' k b o n,
know_ok SEGS E M k ->
(forall x : word, (bv_unsigned x < estart E (SA b o) \/ estart E (SA b o) + elenZ E n <= bv_unsigned x)%Z -> M' x = M x) ->
know_ok SEGS E M' (kn_cutout k b o n).
Proof. intros. eapply know_ok_cutout; try eassumption. Unshelve. all: aps_fill. Qed.
Lemma img_cell_readable_rd1 : forall M a n,
img_cell_readable SEGS a n = true ->
forall j, (j < n)%nat -> rd1 SEGS M (Z_to_bv 64 (a + Z.of_nat j)) <> None.
Proof.
intros M a n. revert a. induction n as [|n IH]; intros a H j Hj; [lia|].
cbn [img_cell_readable] in H. destruct (seg_rom SEGS (Z_to_bv 64 a)) as [b|] eqn:Hr; [|discriminate].
destruct j as [|j'].
- cbn [Z.of_nat]. rewrite Z.add_0_r. unfold rd1. destruct (M (Z_to_bv 64 a)); [discriminate|]. rewrite Hr. discriminate.
- replace (a + Z.of_nat (S j'))%Z with (a + 1 + Z.of_nat j')%Z by lia. apply IH; [exact H | lia].
Qed.
Theorem xn_havoccell_sound : forall args, node1_stmt SEGS A nx0 LIMIT TOP SINV argH FS0 always (xn_havoccell nx0 SEGS args).
Proof.
intros args cs cs' E R FULL model T HC _ Hn HK.
unfold xn_havoccell in Hn.
destruct args as [|b [|e2 rest]]; try discriminate Hn. destruct e2 as [n| | | | | | |]; try discriminate Hn.
destruct rest; [|discriminate Hn].
destruct (split_lit b) as [bb bo] eqn:Hsp.
match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
injection Hn as <-.
apply andb_prop in Hc as [Hc Hcov]. apply andb_prop in Hc as [Hfresh Hvb].
assert (COMMON : (0 < n)%Z /\ (n <= 8)%Z /\ flat_x (kn cs) bb bo (ELit n) = true
/\ (cover_x (S (length (kn cs))) (kn cs) bb bo (bo + n) = true
\/ (bb = ELit 0 /\ img_cell_readable SEGS bo (Z.to_nat n) = true))).
{ unfold havoc_readable, havoc_covered in Hcov. apply orb_prop in Hcov as [Hcov|Hcov].
- apply andb_prop in Hcov as [Hcov Hcx]. apply andb_prop in Hcov as [Hcov Hfl]. apply andb_prop in Hcov as [Hn0 Hn8].
apply Z.ltb_lt in Hn0. apply Z.leb_le in Hn8. repeat split; try assumption. left; exact Hcx.
- apply andb_prop in Hcov as [Hcov Himg]. apply andb_prop in Hcov as [Hcov Hfl]. apply andb_prop in Hcov as [Hn0 Hn8].
apply Z.ltb_lt in Hn0. apply Z.leb_le in Hn8. destruct bb as [z| | | | | | |]; try discriminate Himg. destruct z; try discriminate Himg.
repeat split; try assumption. right. split; [reflexivity | exact Himg]. }
destruct COMMON as (Hn0 & Hn8 & Hfl & ROUTE).
destruct (w_fresh_ok_parts cs Hfresh) as (Fsr & Fkn & Fmaps & Fvis & Fbrk & Ffd & Fle).
pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK0.
set (M := MR E cs model FULL) in *.
destruct (w_flat_x_sound E M (kn cs) bb bo (ELit n) HK0 Hfl) as (F1 & F2 & F3). rewrite edenot_lit, u64_lit in F2, F3 by (unfold two64 in *; lia).
set (lo := estart E (SA bb bo)) in *.
assert (Hub : uE E bb + bo = lo) by reflexivity.
assert (RD : forall j, (j < Z.to_nat n)%nat -> rd1 SEGS M (Z_to_bv 64 (lo + Z.of_nat j)) <> None).
{ intros j Hj. destruct ROUTE as [Hcx|[-> Himg]].
- destruct (w_cover_x_rd1 _ E M (kn cs) bb bo (bo + n) HK0 Hcx (bo + Z.of_nat j) ltac:(lia)) as [_ R1].
replace (lo + Z.of_nat j)%Z with (uE E bb + (bo + Z.of_nat j))%Z by (unfold lo, estart, uE; cbn [a_base a_off]; lia). exact R1.
- replace lo with bo by (unfold lo, estart; cbn [a_base a_off edenot]; rewrite u64_lit by lia; lia).
exact (img_cell_readable_rd1 M bo (Z.to_nat n) Himg j Hj). }
destruct (rdn_defined SEGS M (Z.to_nat n) (Z_to_bv 64 lo) ltac:(rewrite u64_lit by lia; lia)) as (bs & Hbs & Hlen).
{ intros j Hj. rewrite u64_lit by lia. exact (RD j Hj). }
set (w := Z_to_bv 64 (bytes_le_to_Z bs)).
set (E' := ext1 E (nxt cs) w).
pose proof (ext1_agree E (nxt cs) w) as Hag. fold E' in Hag.
assert (Hag0 : env_agree nx0 E E') by (eapply w_env_agree_le; [exact Hag | exact Fle]).
assert (HC' : CSOK E' cs R FULL model) by (eapply w_cs_ok_agree; [exact Hag | exact Hfresh | exact HC]).
assert (Hbb : APG.expr_vars_lt (nxt cs) bb = true) by (eapply split_lit_vars; [exact Hsp | exact Hvb]).
assert (Elo : estart E' (SA bb bo) = lo).
{ unfold lo, estart. cbn [a_base a_off]. rewrite <- (edenot_agree' (nxt cs) E E' bb Hag Hbb). reflexivity. }
assert (HM : MR E' cs model FULL = M).
{ unfold M, Mr. rewrite (w_hid_agree (nxt cs) E E' cs model Hag Fle Fvis). reflexivity. }
apply (HK E' R FULL model); [split; [exact Hag0 | exact Hag] | | reflexivity].
eapply w_cs_ok_frame; [exact HC' | apply same_but_materialized_refl | exact (co_minv _ _ _ _ _ _ _ _ _ _ _ _ HC') | exact (co_regs _ _ _ _ _ _ _ _ _ _ _ _ HC') | reflexivity | | intros; reflexivity].
cbn [s_know mk_ss]. rewrite HM. apply Forall_cons.
-   cbn [kentry_ok].
assert (Hfl' : flat E' (SA bb bo) (Z.of_nat (Z.to_nat n))) by (unfold flat; rewrite Elo; unfold lo in *; lia).
split; [lia|]. split; [exact Hfl'|].
replace (adenot E' (SA bb bo)) with (Z_to_bv 64 lo) by (apply bv_eq; rewrite (flat_u E' _ _ Hfl'), Elo, u64_lit by (unfold lo in *; lia); reflexivity).
rewrite Hbs. cbn [edenot]. unfold E'. rewrite ext1_at. f_equal. symmetry. unfold w. apply word_to_le_bytes_of_bytes_n; [exact Hlen | lia].
-
eapply w_know_ok_cutout; [| intros; reflexivity].
pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC') as HK1. rewrite HM in HK1. exact HK1.
Qed.
End d0.
End APSXG.
