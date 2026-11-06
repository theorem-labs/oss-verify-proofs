(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan HeapIface HeapIfaceA L5Defs L5Core L5LazyA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA PmShadowW.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutAuto CutLib CutHeap CutHeap2 CutL5 CutCertA CutHeapA.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module CL5A.
Definition mem := (word -> option byte).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Vis.
Variable segs : list Segment.
Variable H : word -> bool.

Lemma vis_some : forall (M : mem) a b, mrestrict H M a = Some b -> M a = Some b.
Proof. intros M a b. unfold mrestrict. destruct (H a); [discriminate | auto]. Qed.
Lemma vis_eq : forall (M : mem) a, H a = false -> mrestrict H M a = M a.
Proof. intros M a Ha. unfold mrestrict. rewrite Ha. reflexivity. Qed.
Lemma vis_def : forall (M : mem) a, mrestrict H M a <> None -> M a <> None.
Proof. intros M a. unfold mrestrict. destruct (H a); [congruence | auto]. Qed.

(* [comment removed for export] *)
Lemma rdn_full : H_off_segments segs H -> forall (M : mem) n (a : word) bs, rdn segs (mrestrict H M) a n = Some bs -> rdn segs M a n = Some bs.
Proof.
  intros HH M n. induction n as [|n IH]; intros a bs Hr; [exact Hr|]. cbn [rdn] in *.
  unfold mrestrict in Hr at 1. destruct (H a) eqn:EH.
  - exfalso. unfold seg_rom, memory_read in Hr. change (Z.of_N 1) with 1 in Hr. rewrite (HH a EH) in Hr. discriminate.
  - destruct (M a) as [b|].
    + destruct (rdn segs (mrestrict H M) (a + 1)%bv n) as [r|] eqn:E2; [|discriminate]. rewrite (IH _ _ E2). exact Hr.
    + destruct (seg_rom segs a) as [b|]; [|discriminate].
      destruct (rdn segs (mrestrict H M) (a + 1)%bv n) as [r|] eqn:E2; [|discriminate]. rewrite (IH _ _ E2). exact Hr.
Qed.
(* [comment removed for export] *)
Lemma rdn_vis : forall (M : mem) a (n : nat), 0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> (forall i, 0 <= i < Z.of_nat n -> H (Z_to_bv 64 (a + i)) = false) ->
  rdn segs (mrestrict H M) (Z_to_bv 64 a) n = rdn segs M (Z_to_bv 64 a) n.
Proof. intros M a n H0 H1 HV. apply rdn_mrestrict_eq. intros k Hk. unfold woff. rewrite L5.unsigned_lit by lia. apply HV. lia. Qed.

Lemma u64_full : H_off_segments segs H -> forall (M : mem) a v, L5.u64_at segs (mrestrict H M) a v -> L5.u64_at segs M a v.
Proof. intros HH M a v. unfold L5.u64_at. apply rdn_full. exact HH. Qed.
Lemma u32_full : H_off_segments segs H -> forall (M : mem) a v, L5.u32_at segs (mrestrict H M) a v -> L5.u32_at segs M a v.
Proof. intros HH M a v. unfold L5.u32_at. apply rdn_full. exact HH. Qed.
Lemma u8_full : H_off_segments segs H -> forall (M : mem) a v, L5.u8_at segs (mrestrict H M) a v -> L5.u8_at segs M a v.
Proof. intros HH M a v. unfold L5.u8_at. apply rdn_full. exact HH. Qed.
Lemma bytes_full : H_off_segments segs H -> forall (M : mem) p bs, L5.bytes_at segs (mrestrict H M) p bs -> L5.bytes_at segs M p bs.
Proof. intros HH M p bs HB i Hi. exact (u8_full HH M _ _ (HB i Hi)). Qed.
Lemma defined_full : forall (M : mem) a n, L5.defined (mrestrict H M) a n -> L5.defined M a n.
Proof. intros M a n Hd i Hi. exact (vis_def M _ (Hd i Hi)). Qed.
Lemma byte_full : forall (M : mem) a v, byte_at (mrestrict H M) a v -> byte_at M a v.
Proof. intros M a v. unfold byte_at. apply vis_some. Qed.

Definition visr (a n : Z) : Prop := forall i, 0 <= i < n -> H (Z_to_bv 64 (a + i)) = false.
Lemma visr_sub : forall a n a' n', visr a n -> a <= a' -> a' + n' <= a + n -> visr a' n'.
Proof. intros a n a' n' HV H1 H2 i Hi. replace (a' + i) with (a + (a' - a + i)) by lia. apply HV. lia. Qed.
Lemma u64_vis : forall (M : mem) a v, 0 <= a -> a + 8 <= 2 ^ 64 -> visr a 8 -> L5.u64_at segs M a v -> L5.u64_at segs (mrestrict H M) a v.
Proof. intros M a v H0 H1 HV Hu. unfold L5.u64_at. rewrite (rdn_vis M a 8 H0 H1 HV). exact Hu. Qed.
Lemma u32_vis : forall (M : mem) a v, 0 <= a -> a + 4 <= 2 ^ 64 -> visr a 4 -> L5.u32_at segs M a v -> L5.u32_at segs (mrestrict H M) a v.
Proof. intros M a v H0 H1 HV Hu. unfold L5.u32_at. rewrite (rdn_vis M a 4 H0 H1 HV). exact Hu. Qed.
Lemma u8_vis : forall (M : mem) a v, 0 <= a -> a + 1 <= 2 ^ 64 -> visr a 1 -> L5.u8_at segs M a v -> L5.u8_at segs (mrestrict H M) a v.
Proof. intros M a v H0 H1 HV Hu. unfold L5.u8_at. rewrite (rdn_vis M a 1 H0 H1 HV). exact Hu. Qed.
Lemma bytes_vis : forall (M : mem) p bs, 0 <= p -> p + Z.of_nat (length bs) <= 2 ^ 64 -> visr p (Z.of_nat (length bs)) ->
  L5.bytes_at segs M p bs -> L5.bytes_at segs (mrestrict H M) p bs.
Proof.
  intros M p bs H0 H1 HV HB i Hi. apply u8_vis; [lia | lia | | exact (HB i Hi)].
  apply (visr_sub p (Z.of_nat (length bs))); [exact HV | lia | lia].
Qed.
Lemma defined_vis : forall (M : mem) a n, visr a n -> L5.defined M a n -> L5.defined (mrestrict H M) a n.
Proof. intros M a n HV Hd i Hi. rewrite (vis_eq M _ (HV i Hi)). exact (Hd i Hi). Qed.
Lemma byte_vis : forall (M : mem) a v, H (Z_to_bv 64 a) = false -> byte_at M a v -> byte_at (mrestrict H M) a v.
Proof. intros M a v HV Hb. unfold byte_at. rewrite (vis_eq M _ HV). exact Hb. Qed.

(* [comment removed for export] *)
Lemma rdn_same : forall (M M' : mem) n a, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> (forall i, a <= i < a + Z.of_nat n -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
  rdn segs M' (Z_to_bv 64 a) n = rdn segs M (Z_to_bv 64 a) n.
Proof.
  intros M M'. induction n as [|n IH]; intros a Ha Hn Heq; [reflexivity|]. cbn [rdn]. rewrite (Heq a ltac:(lia)).
  replace (Z_to_bv 64 a + 1)%bv with (Z_to_bv 64 (a + 1)).
  2: { apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_unsigned (1%bv : bv 64)) with 1. rewrite <- Zplus_mod_idemp_l. reflexivity. }
  rewrite (IH (a + 1)); [reflexivity | lia | lia | intros i Hi; apply Heq; lia].
Qed.
Lemma u64_same : forall (M M' : mem) a v, 0 <= a -> a + 8 <= 2 ^ 64 -> (forall i, a <= i < a + 8 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> L5.u64_at segs M a v -> L5.u64_at segs M' a v.
Proof. intros M M' a v H0 H1 Heq Hu. unfold L5.u64_at. rewrite (rdn_same M M' 8 a H0 H1 Heq). exact Hu. Qed.
Lemma u8_same : forall (M M' : mem) a v, 0 <= a -> a + 1 <= 2 ^ 64 -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a) -> L5.u8_at segs M a v -> L5.u8_at segs M' a v.
Proof. intros M M' a v H0 H1 Heq Hu. unfold L5.u8_at. rewrite (rdn_same M M' 1 a H0 H1); [exact Hu|]. intros i Hi. replace i with a by lia. exact Heq. Qed.
Lemma bytes_same : forall (M M' : mem) p bs, 0 <= p -> p + Z.of_nat (length bs) <= 2 ^ 64 ->
  (forall i, p <= i < p + Z.of_nat (length bs) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> L5.bytes_at segs M p bs -> L5.bytes_at segs M' p bs.
Proof. intros M M' p bs H0 H1 Heq HB i Hi. apply (u8_same M M'); [lia | lia | apply Heq; lia | exact (HB i Hi)]. Qed.
Lemma defined_same : forall (M M' : mem) a n, (forall i, a <= i < a + n -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> L5.defined M a n -> L5.defined M' a n.
Proof. intros M M' a n Heq Hd i Hi. rewrite (Heq (a + i) ltac:(lia)). exact (Hd i Hi). Qed.
End Vis.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition uv (E : env) (e : expr) : Z := bv_unsigned (edenot E e).
Lemma uv_range : forall E e, 0 <= uv E e < 2 ^ 64.
Proof. intros. unfold uv. pose proof (u64_range (edenot E e)) as X. unfold two64 in X. exact X. Qed.
(* [comment removed for export] *)
Lemma lin_val : forall E e, exists q, uv E e = lden E (lin_of e) + q * 2 ^ 64.
Proof. intros E e. destruct (lin_of_sound E e) as [q Hq]. unfold uE in Hq. exists (- q). unfold uv. lia. Qed.
Lemma uv_agree : forall b E E' e, env_agree b E E' -> APC.expr_vars_lt b e = true -> uv E' e = uv E e.
Proof. intros b E E' e Hag Hv. unfold uv. rewrite (SR.edenot_agree_AP b E E' e Hag Hv). reflexivity. Qed.
Lemma uv_var : forall b E E' n, env_agree b E E' -> (n < b)%nat -> uv E' (EVar n) = uv E (EVar n).
Proof. intros b E E' n [Hag _] Hn. unfold uv. cbn [edenot]. rewrite (Hag n Hn). reflexivity. Qed.
Lemma estart_srl3 : forall E e k, estart E (SA (CHA.SRL3 e) k) = uv E e / 8 + k.
Proof. intros E e k. unfold estart. cbn [a_base a_off]. rewrite CHA.u_srl3. reflexivity. Qed.
Lemma estart_srl3' : forall E e k, estart E (SA (EAlu Instr.ALU_SRL e (ELit 3)) k) = uv E e / 8 + k.
Proof. exact estart_srl3. Qed.
Lemma u_and7 : forall E e, bv_unsigned (edenot E (EAlu Instr.ALU_AND e (ELit 7))) = bv_unsigned (edenot E e) mod 8.
Proof. intros E e. exact (u_and_mask E e 7 3 ltac:(lia) eq_refl). Qed.
Lemma estart_agree : forall b E E' e k, env_agree b E E' -> APC.expr_vars_lt b e = true -> estart E' (SA e k) = estart E (SA e k).
Proof. intros b E E' e k Hag Hv. unfold estart. cbn [a_base a_off]. rewrite (SR.edenot_agree_AP b E E' e Hag Hv). reflexivity. Qed.

Section Tmpl.
Variable segs : list Segment.
Lemma bytes1 : forall z, 0 <= z < 2 ^ 64 -> word_to_le_bytes 1 (Z_to_bv 64 z) = [Z_to_bv 8 z].
Proof.
  intros z Hz. unfold word_to_le_bytes. cbn. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 8) with 256. change (bv_modulus 64) with (2^64). rewrite (Z.mod_small z (2^64)) by lia. reflexivity.
Qed.
Lemma kword8_intro : forall E (M : mem) a v A z, estart E a = A -> 0 <= A -> A + 1 <= 2 ^ 64 -> edenot E v = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 ->
  L5.u8_at segs M A z -> kentry_ok segs E M (KWord a 1 v).
Proof.
  intros E M a v A z Ha H0 H1 Hv Hz Hu. cbn [kentry_ok]. assert (Hfl : flat E a (Z.of_nat 1)) by (unfold flat; rewrite Ha; lia).
  split; [lia|]. split; [exact Hfl|]. rewrite (CL5.adenot_start E a _ Hfl), Ha, Hv. rewrite (bytes1 z Hz). exact Hu.
Qed.
Lemma kword8_elim : forall E (M : mem) a v A, kentry_ok segs E M (KWord a 1 v) -> estart E a = A -> L5.u8_at segs M A (uv E v).
Proof.
  intros E M a v A (_ & Hfl & Hr) Ha. unfold L5.u8_at. rewrite <- Ha, <- (CL5.adenot_start E a _ Hfl), Hr.
  unfold uv, word_to_le_bytes. cbn [Z_to_le_bytes]. reflexivity.
Qed.
Lemma kword32_elim : forall E (M : mem) a v A, kentry_ok segs E M (KWord a 4 v) -> estart E a = A -> L5.u32_at segs M A (uv E v).
Proof. intros E M a v A (_ & Hfl & Hr) Ha. unfold L5.u32_at. rewrite <- Ha, <- (CL5.adenot_start E a _ Hfl), Hr. unfold uv. rewrite Z_to_bv_bv_unsigned. reflexivity. Qed.
Lemma kword64_elim : forall E (M : mem) a v A, kentry_ok segs E M (KWord a 8 v) -> estart E a = A -> L5.u64_at segs M A (uv E v).
Proof. intros E M a v A HK Ha. exact (CL5.kword64_elim segs E M a v A (uv E v) HK Ha eq_refl). Qed.
(* [comment removed for export] *)
Lemma u8_byte_at : forall (M : mem) a v, M (Z_to_bv 64 a) <> None -> L5.u8_at segs M a v -> byte_at M a v.
Proof. intros M a v Hd Hu. unfold byte_at. exact (CL5.overlay_byte segs M _ _ Hu Hd). Qed.
Lemma byte_at_u8 : forall (M : mem) a v, byte_at M a v -> L5.u8_at segs M a v.
Proof. intros M a v Hb. unfold L5.u8_at, byte_at in *. cbn [rdn]. rewrite Hb. reflexivity. Qed.

Lemma kzero_intro : forall E (M : mem) a n A N, estart E a = A -> elenZ E n = N -> 0 <= A -> A + N <= 2 ^ 64 -> A < 2 ^ 64 ->
  (forall j, 0 <= j < N -> byte_at M (A + j) 0) -> kentry_ok segs E M (KZero a n).
Proof.
  intros E M a n A N Ha Hn H0 H1 H2 HZ. cbn [kentry_ok]. rewrite Ha, Hn.
  split; [unfold flat; rewrite Ha; pose proof (u64_range (edenot E n)); unfold elenZ in Hn; lia|]. intros i Hi. exact (HZ i Hi).
Qed.
Lemma kzero_elim : forall E (M : mem) a n A N, kentry_ok segs E M (KZero a n) -> estart E a = A -> elenZ E n = N -> forall j, 0 <= j < N -> byte_at M (A + j) 0.
Proof. intros E M a n A N [_ HZ] <- <- j Hj. exact (HZ j Hj). Qed.
(* [comment removed for export] *)
Lemma shz_intro : forall E (M : mem) pe g p, uv E pe = p -> 0 <= g < 2 ^ 40 -> 0 <= p < 2 ^ 47 -> shadow_zero M p g -> kentry_ok segs E M (KZero (SA (CHA.SRL3 pe) SB) (ELit g)).
Proof.
  intros E M pe g p Hp Hg Hr HZ. assert (Hd : 0 <= p / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  apply (kzero_intro E M _ _ (p / 8 + SB) g); [rewrite estart_srl3, Hp; reflexivity | unfold elenZ; cbn [edenot]; apply u64_of_Z; lia | unfold SB; lia | unfold SB; lia | unfold SB; lia |].
  intros j Hj. replace (p / 8 + SB + j) with (S p + j) by (unfold S; lia). exact (HZ j Hj).
Qed.
Lemma shz_elim : forall E (M : mem) pe g p, kentry_ok segs E M (KZero (SA (CHA.SRL3 pe) SB) (ELit g)) -> uv E pe = p -> 0 <= g < 2 ^ 64 -> shadow_zero M p g.
Proof.
  intros E M pe g p HK Hp Hg j Hj. replace (S p + j) with (p / 8 + SB + j) by (unfold S; lia).
  apply (kzero_elim E M _ _ (p / 8 + SB) g HK); [rewrite estart_srl3, Hp; reflexivity | unfold elenZ; cbn [edenot]; apply u64_of_Z; lia | exact Hj].
Qed.
Lemma shbyte_intro : forall E (M : mem) pe ve p v, uv E pe = p -> edenot E ve = Z_to_bv 64 v -> 0 <= v < 256 -> 0 <= p < 2 ^ 47 -> byte_at M (S p) v ->
  kentry_ok segs E M (KWord (SA (CHA.SRL3 pe) SB) 1 ve).
Proof.
  intros E M pe ve p v Hp Hv Hr Hpr Hb. assert (Hd : 0 <= p / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  apply (kword8_intro E M _ _ (S p) v); [rewrite estart_srl3, Hp; reflexivity | unfold S, SB; lia | unfold S, SB; lia | exact Hv | lia | exact (byte_at_u8 M _ _ Hb)].
Qed.
End Tmpl.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ainfr (FF : list fframe) (a n : Z) : Prop :=
  exists f, In f FF /\ ff_addr f + 32 <= a /\ a + n <= ff_addr f + ff_bytes (ff_class f) - 8.

Lemma S_add_al : forall b n, b mod 8 = 0 -> S (b + n) = S b + n / 8.
Proof. intros b n Hb. unfold S. apply Z.mod_divide in Hb; [|lia]. destruct Hb as [q ->]. rewrite Z.div_add_l, Z.div_mul by lia. lia. Qed.
(* [comment removed for export] *)
Lemma blk_shadow_in : forall b n a, b mod 8 = 0 -> 0 < n -> S b <= a < S b + (n + 7) / 8 -> in_shadow_of b n a.
Proof.
  intros b n a Hb Hn Ha. unfold in_shadow_of. split; [lia|]. replace (b + n - 1) with (b + (n - 1)) by lia. rewrite (S_add_al b (n - 1) Hb).
  pose proof (Z.div_mod (n + 7) 8 ltac:(lia)) as D7. pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)) as R7.
  assert (E1 : (n - 1) / 8 = (n + 7) / 8 - 1) by (symmetry; apply (Zdiv_unique _ 8 _ ((n + 7) mod 8)); lia). lia.
Qed.
(* [comment removed for export] *)
Lemma gran_le : forall p g X, X mod 8 = 0 -> p + 8 * g - 7 <= X -> p / 8 + g <= X / 8.
Proof.
  intros p g X HX H. replace (p / 8 + g) with ((p + g * 8) / 8) by (rewrite Z.div_add by lia; reflexivity).
  apply Z.mod_divide in HX; [|lia]. destruct HX as [q ->]. rewrite Z.div_mul by lia.
  assert (G : (p + g * 8) / 8 < q + 1) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.
Lemma gran_blk : forall n, 0 <= n -> 8 * ((n + 7) / 8) <= n + 7.
Proof. intros n Hn. pose proof (Z.div_mod (n + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)). lia. Qed.
Lemma shreg_bounds : forall b n, 0 <= b -> 0 <= n -> b + n <= 2 ^ 47 -> b mod 8 = 0 -> SB <= b / 8 + SB /\ b / 8 + SB + (n + 7) / 8 <= 0x10007fff8000.
Proof.
  intros b n Hb Hn H Hal. pose proof (Z.div_pos b 8 Hb ltac:(lia)). split; [lia|].
  pose proof (gran_le b ((n + 7) / 8) (2 ^ 47) eq_refl ltac:(pose proof (gran_blk n Hn); lia)) as G. change (2 ^ 47 / 8) with (2 ^ 44) in G. unfold SB. lia.
Qed.
Lemma al64_add8 : forall x y, x mod 64 = 0 -> y mod 64 = 0 -> (x + y) mod 8 = 0.
Proof.
  intros x y Hx Hy. apply Z.mod_divide in Hx; [|lia]. apply Z.mod_divide in Hy; [|lia]. destruct Hx as [p ->]. destruct Hy as [q ->].
  replace (p * 64 + q * 64) with ((8 * (p + q)) * 8) by lia. apply Z_mod_mult.
Qed.
Lemma elen_srl3' : forall E e, elenZ E (EAlu Instr.ALU_SRL e (ELit 3)) = uv E e / 8.
Proof. intros E e. unfold elenZ. exact (CHA.u_srl3 E e). Qed.
(* [comment removed for export] *)
Lemma sh_apart2 : forall p n q m a, 0 <= p -> 0 <= q -> 0 < n -> 0 < m -> p mod 8 = 0 -> q mod 8 = 0 -> (p + n <= q \/ q + m <= p) ->
  in_shadow_of p n a -> in_shadow_of q m a -> False.
Proof.
  intros p n q m a Hp Hq Hn Hm Ap Aq [H|H] X Y; [exact (CHA.shadow_apart p n q m a Hp Hn Hm H Aq X Y) | exact (CHA.shadow_apart q m p n a Hq Hm Hn H Ap Y X)].
Qed.
Lemma forallb_filter_self : forall {T} (f : T -> bool) l, forallb f (List.filter f l) = true.
Proof. intros T f l. apply forallb_forall. intros x Hx. apply filter_In in Hx. exact (proj2 Hx). Qed.
Lemma ainfr_sub : forall FF a n a' n', ainfr FF a n -> a <= a' -> a' + n' <= a + n -> ainfr FF a' n'.
Proof. intros FF a n a' n' (f & Hf & F1 & F2) H1 H2. exists f. split; [exact Hf|]. lia. Qed.
Lemma div8_le : forall x y, x <= y -> x / 8 <= y / 8.
Proof. intros. apply Z.div_le_mono; lia. Qed.
(* [comment removed for export] *)
Lemma shreg_in_shadow : forall p g a, p mod 8 = 0 -> 0 < g -> p / 8 + SB <= a < p / 8 + SB + g -> in_shadow_of p (8 * g) a.
Proof.
  intros p g a Hp Hg Ha. unfold in_shadow_of, S. apply Z.mod_divide in Hp; [|lia]. destruct Hp as [q ->].
  rewrite Z.div_mul in Ha by lia. rewrite Z.div_mul by lia.
  assert (E1 : (q * 8 + 8 * g - 1) / 8 = q + g - 1) by (symmetry; apply (Zdiv_unique _ 8 (q + g - 1) 7); lia). rewrite E1. lia.
Qed.
Lemma shreg1_in_shadow : forall p a, a = p / 8 + SB -> in_shadow_of p 1 a.
Proof. intros p a ->. unfold in_shadow_of, S. replace (p + 1 - 1) with p by lia. lia. Qed.
Lemma in_shadow_mono : forall p n q m a, q <= p -> p + n <= q + m -> 0 < n -> in_shadow_of p n a -> in_shadow_of q m a.
Proof. intros p n q m a H1 H2 Hn [X1 X2]. unfold in_shadow_of, S in *. pose proof (div8_le q p H1). pose proof (div8_le (p + n - 1) (q + m - 1) ltac:(lia)). lia. Qed.

(* [comment removed for export] *)
Lemma shadow_cont_same : forall (M M' : mem) u n mid, 0 <= mid <= n -> u mod 8 = 0 ->
  (forall a, in_shadow_of u n a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> shadow_cont M u n mid -> shadow_cont M' u n mid.
Proof.
  intros M M' u n mid Hm Hu Heq. apply shadow_cont_tr; [exact Hm|]. intros j v Hj Hidx Hb. unfold byte_at. rewrite Heq; [exact Hb|].
  apply sbw_idx_iff in Hidx; [|lia]. unfold in_shadow_of, S. apply Z.mod_divide in Hu; [|lia]. destruct Hu as [q ->].
  pose proof (Z.div_mod (n + 7) 8 ltac:(lia)) as D7. pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)) as R7.
  assert (E1 : (q * 8 + n - 1) / 8 = q + (n + 7) / 8 - 1) by (symmetry; apply (Zdiv_unique _ 8 _ ((n + 7) mod 8)); lia).
  rewrite E1, Z.div_mul by lia. lia.
Qed.
Lemma shadow_zero_same : forall (M M' : mem) p g, (forall j, 0 <= j < g -> M' (Z_to_bv 64 (S p + j)) = M (Z_to_bv 64 (S p + j))) -> shadow_zero M p g -> shadow_zero M' p g.
Proof. intros M M' p g Heq HZ j Hj. unfold byte_at. rewrite (Heq j Hj). exact (HZ j Hj). Qed.

Section Frames.
Variable L : asan_layout.
Variable ar : asan_run.
Hypothesis LY_img : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO.

Lemma infr_rng : forall LB FF a n, CHA.rng_facts L ar LB FF -> ainfr FF a n -> 0 < n ->
  ar_fs ar + 32 <= a /\ a + n + 8 <= ar_fs ar + FS_BYTES /\ 0 <= a /\ a + n <= ahl_ceil ar /\ (a + n <= BIGSHADOW_LO \/ BIGSHADOW_HI <= a) /\ a + n <= 2 ^ 47
  /\ (a + n <= hl_img_lo L \/ hl_img_hi L <= a).
Proof.
  intros LB FF a n RFx (f & Hf & F1 & F2) Hn. destruct (CHA.rf_frm _ _ _ _ RFx f Hf) as (G1 & G2 & _). destruct (CHA.rf_fs _ _ _ _ RFx) as ((A0 & A1 & A2) & A3 & A4).
  unfold FS_BYTES in *. repeat split; try lia.
Qed.
(* [comment removed for export] *)
Lemma not_stk_shadow_app : forall LB FF a, CHA.rng_facts L ar LB FF -> (a < BIGSHADOW_LO \/ BIGSHADOW_HI <= a) ->
  in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar).
Proof.
  intros LB FF a RFx Ha X. destruct (CHA.rf_ceil _ _ _ _ RFx) as (CL & _). destruct (CHA.rf_sptop _ _ _ _ RFx) as (SP1 & _).
  pose proof (CHA.shadow_range (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a ltac:(lia) ltac:(lia) ltac:(lia) X). unfold BIGSHADOW_LO, BIGSHADOW_HI in *. lia.
Qed.
(* [comment removed for export] *)
Lemma not_stk_shadow_sh : forall LB FF p n a, CHA.rng_facts L ar LB FF -> 0 <= p -> 0 < n -> p + n <= ahl_ceil ar -> in_shadow_of p n a ->
  in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar).
Proof.
  intros LB FF p n a RFx Hp Hn Hc X Y. exfalso. destruct (CHA.rf_ceil _ _ _ _ RFx) as (CL & C8). destruct (CHA.rf_sptop _ _ _ _ RFx) as (SP1 & _).
  exact (CHA.shadow_apart p n (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a Hp Hn ltac:(lia) Hc C8 X Y).
Qed.

Lemma infr_clientw : forall LB FF sp scr o n a, ainfr FF o n -> o <= a < o + n -> aclientw L ar LB FF sp scr a.
Proof.
  intros LB FF sp scr o n a (f & Hf & F1 & F2) Ha. right; right; right; left. exists f. split; [exact Hf|]. split; lia.
Qed.
Lemma infr_sh_clientw : forall LB FF sp scr o n a, ainfr FF o n -> 0 < n -> in_shadow_of o n a -> aclientw L ar LB FF sp scr a.
Proof.
  intros LB FF sp scr o n a (f & Hf & F1 & F2) Hn Ha. right; right; right; right; right; left. exists f. split; [exact Hf|].
  apply (in_shadow_mono o n); [lia | lia | exact Hn | exact Ha].
Qed.
(* [comment removed for export] *)
Lemma infr_wok : forall LB FF sp scr o n a, CHA.rng_facts L ar LB FF -> ainfr FF o n -> o <= a < o + n ->
  0 <= a < 2 ^ 64 /\ aclientw L ar LB FF sp scr a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)).
Proof.
  intros LB FF sp scr o n a RFx HI Ha. destruct (infr_rng LB FF o n RFx HI ltac:(lia)) as (R1 & R2 & R3 & R4 & R5 & R6 & R7).
  split; [lia|]. split; [exact (infr_clientw LB FF sp scr o n a HI Ha)|]. apply (not_stk_shadow_app LB FF a RFx). lia.
Qed.
Lemma infr_sh_wok : forall LB FF sp scr o n a, CHA.rng_facts L ar LB FF -> ainfr FF o n -> 0 < n -> in_shadow_of o n a ->
  0 <= a < 2 ^ 64 /\ aclientw L ar LB FF sp scr a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)).
Proof.
  intros LB FF sp scr o n a RFx HI Hn Ha. destruct (infr_rng LB FF o n RFx HI Hn) as (R1 & R2 & R3 & R4 & R5 & R6 & R7).
  pose proof (CHA.shadow_range o n a R3 Hn R6 Ha) as SR.
  split; [lia|]. split; [exact (infr_sh_clientw LB FF sp scr o n a HI Hn Ha)|]. exact (not_stk_shadow_sh LB FF o n a RFx R3 Hn R4 Ha).
Qed.
(* [comment removed for export] *)
Definition acobj (FF : list fframe) (sp a n : Z) : Prop := ainfr FF a n \/ (sp <= a /\ a + n <= ar_sptop ar).
Lemma acobj_rng : forall LB FF sp a n, CHA.rng_facts L ar LB FF -> ahl_ceil ar <= sp -> acobj FF sp a n -> 0 < n ->
  0 <= a /\ a + n <= 2 ^ 47 /\ (a + n <= BIGSHADOW_LO \/ BIGSHADOW_HI <= a) /\ (ar_fs ar + 32 <= a \/ ahl_ceil ar <= a) /\ (a + n <= ahl_ceil ar \/ sp <= a).
Proof.
  intros LB FF sp a n RFx Hsp [HI|[H1 H2]] Hn.
  - destruct (infr_rng LB FF a n RFx HI Hn) as (R1 & R2 & R3 & R4 & R5 & R6 & R7). repeat split; try lia.
  - destruct (CHA.rf_ceil _ _ _ _ RFx) as (CL & _). destruct (CHA.rf_sptop _ _ _ _ RFx) as (SP1 & _). unfold BIGSHADOW_HI. repeat split; lia.
Qed.
Lemma acobj_wok : forall LB FF sp scr o n a, CHA.rng_facts L ar LB FF -> ahl_ceil ar <= sp -> acobj FF sp o n -> o <= a < o + n ->
  0 <= a < 2 ^ 64 /\ aclientw L ar LB FF sp scr a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)).
Proof.
  intros LB FF sp scr o n a RFx Hsp [HI|[H1 H2]] Ha; [exact (infr_wok LB FF sp scr o n a RFx HI Ha)|].
  destruct (CHA.rf_ceil _ _ _ _ RFx) as (CL & _). destruct (CHA.rf_sptop _ _ _ _ RFx) as (SP1 & _).
  split; [lia|]. split; [right; left; split; lia|]. apply (not_stk_shadow_app LB FF a RFx). unfold BIGSHADOW_HI. lia.
Qed.
Lemma acobj_sh_wok : forall LB FF sp scr o n a, CHA.rng_facts L ar LB FF -> ahl_ceil ar <= sp -> acobj FF sp o n -> 0 < n -> in_shadow_of o n a ->
  0 <= a < 2 ^ 64 /\ aclientw L ar LB FF sp scr a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)).
Proof.
  intros LB FF sp scr o n a RFx Hsp [HI|[H1 H2]] Hn Ha; [exact (infr_sh_wok LB FF sp scr o n a RFx HI Hn Ha)|].
  destruct (CHA.rf_ceil _ _ _ _ RFx) as (CL & _). destruct (CHA.rf_sptop _ _ _ _ RFx) as (SP1 & SP16).
  pose proof (CHA.shadow_range o n a ltac:(lia) Hn ltac:(lia) Ha) as SR.
  split; [lia|]. split; [right; right; right; right; left; apply (in_shadow_mono o n); [lia | lia | exact Hn | exact Ha]|].
  intros _. destruct Ha as [_ A2]. unfold S in *. apply Z.mod_divide in SP16; [|lia]. destruct SP16 as [q Hq].
  assert (E1 : ar_sptop ar / 8 = 2 * q) by (rewrite Hq; replace (q * 16) with ((2 * q) * 8) by lia; apply Z.div_mul; lia).
  assert (E2 : (o + n - 1) / 8 < 2 * q) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.
End Frames.
End CL5A.
