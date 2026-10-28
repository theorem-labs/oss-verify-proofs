(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From LinuxProcessSemantics.Riscv Require Import Sem.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore AsanPlanSoundSums
  HeapIface LibIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5 PmEncSpecs_u5 PmLibSpecsX_u5.
From Stdlib Require Import Classical.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutL5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmTop Require Import TopKit_u5 TopKit2_u5 ReadKit_u5 ChunkKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncKit_u5.
Import ListNotations. Import AX2. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module TKX.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma agree_of_samem : forall (K : Z -> Prop) M M' a n, TK.samem K M M' -> 0 <= a -> a + n <= 2 ^ 64 -> TK2.cov K a n -> L5C.agree_on M M' a n.
Proof. intros K M M' a n AG Ha Hn HC i Hi. apply AG; [lia | apply HC; exact Hi]. Qed.

(* [comment removed for export] *)
Lemma enc_inv_x : forall (K : Z -> Prop) M M' V S2 g, TK.samem K M M' -> 0 <= V -> V + PMES.ENC_SIZE <= 2 ^ 62 -> 0 <= S2 -> S2 + 24 <= 2 ^ 62 ->
  TK2.cov K V PMES.ENC_SIZE -> TK2.cov K S2 24 ->
  (forall b, In b (PMES.g_lbv g) -> 0 <= fst b /\ fst b + snd b <= 2 ^ 64 /\ TK2.cov K (fst b) (snd b)) ->
  PMES.enc_inv M V S2 g -> PMES.enc_inv M' V S2 g.
Proof.
  intros K M M' V S2 g AG HV HV2 HS HS2 CV CS CB H. unfold PMES.ENC_SIZE in *.
  pose proof H as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hcol & _) & _).
  apply (EK.enc_inv_agree M M' V S2 g); [lia | unfold PMES.ENC_SIZE; lia | lia | lia | | | | | | exact H].
  - apply (agree_of_samem K M M' _ _ AG); [lia | unfold PMES.O_COLUMN; lia | eapply TK2.cov_sub; [exact CV | unfold PMES.O_COLUMN; lia | unfold PMES.O_COLUMN; lia]].
  - apply (agree_of_samem K M M' _ _ AG); [unfold PMES.O_COLON; lia | unfold PMES.ENC_SIZE, PMES.O_COLON; lia | eapply TK2.cov_sub; [exact CV | unfold PMES.O_COLON; lia | unfold PMES.ENC_SIZE, PMES.O_COLON; lia]].
  - apply (TK.defined_samem K M M' _ _ AG); [unfold PMES.O_COLUMN; lia | unfold PMES.O_COLUMN; lia | eapply TK2.cov_sub; [exact CV | unfold PMES.O_COLUMN; lia | unfold PMES.O_COLUMN; lia] | exact Hcol].
  - apply (agree_of_samem K M M' _ _ AG); [lia | lia | exact CS].
  - intros b Hb. destruct (CB b Hb) as (B1 & B2 & B3). split; [exact B1|]. split; [exact B2|]. apply (agree_of_samem K M M' _ _ AG); [lia | lia | exact B3].
Qed.

(* [comment removed for export] *)
Lemma opts_idle_x : forall (K : Z -> Prop) M M' V, TK.samem K M M' -> 0 <= V -> V + PMES.ENC_SIZE <= 2 ^ 62 -> TK2.cov K (V + 96) 144 ->
  PMES.opts_idle M V -> PMES.opts_idle M' V.
Proof.
  intros K M M' V AG HV HV2 HC (A & B & C & D & E & F). unfold PMES.ENC_SIZE in HV2. unfold PMES.opts_idle.
  repeat split; (apply (TK2.u64_x K M M' AG); [lia | eapply TK2.cov_sub; [exact HC | lia | lia] | assumption]).
Qed.

(* [comment removed for export] *)
Definition lits_cov (K : Z -> Prop) : Prop := forall a, PML.LIT_LO <= a < PML.LIT_HI -> K a.
Lemma lits_ok_x : forall (K : Z -> Prop) M M', TK.samem K M M' -> lits_cov K -> PML.lits_ok M -> PML.lits_ok M'.
Proof. intros K M M' AG HK H. apply (PML.lits_ok_agree M M'); [|exact H]. intros a Ha. apply AG; [unfold PML.LIT_LO, PML.LIT_HI in Ha; lia | apply HK; exact Ha]. Qed.
Lemma lits_pristine_x : forall (K : Z -> Prop) M M', TK.samem K M M' -> lits_cov K -> PML.lits_pristine M -> PML.lits_pristine M'.
Proof. intros K M M' AG HK H a Ha. rewrite (AG a) by (first [unfold PML.LIT_LO, PML.LIT_HI in Ha; lia | apply HK; exact Ha]). apply H. exact Ha. Qed.
(* [comment removed for export] *)
Lemma lits_cov_keepH : forall L LBk W sp scr, (forall a, PML.LIT_LO <= a < PML.LIT_HI -> L5.outside W a) -> lits_cov (TK2.keepH L LBk W sp scr).
Proof. intros L LBk W sp scr HW a Ha. split; [apply HW; exact Ha|]. right; right; right. unfold PML.LIT_LO, PML.LIT_HI in Ha. lia. Qed.
Lemma lits_cov_out : forall F, (forall w, In w F -> PML.LIT_HI <= fst w \/ fst w + snd w <= PML.LIT_LO) -> lits_cov (L5.outside F).
Proof. intros F HF a Ha w Hw Hin. unfold L5.in_rng in Hin. destruct (HF w Hw); lia. Qed.

(* [comment removed for export] *)
Lemma rdn_img : forall (M : mem) (a : Z) (n : nat),
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> (forall i, a <= i < a + Z.of_nat n -> M (Z_to_bv 64 i) = None) ->
  rdn RSEGS M (Z_to_bv 64 a) n = rdn RSEGS (fun _ => None) (Z_to_bv 64 a) n.
Proof. intros M a n Ha Hn H. symmetry. apply (L5C.rdn_agree RSEGS M (fun _ => None) n a Ha Hn). intros i Hi. rewrite H; [reflexivity | exact Hi]. Qed.
Lemma lits_pristine_ok : forall M, PML.lits_pristine M -> PML.lits_ok M.
Proof.
  intros M H. unfold PML.lits_pristine, PML.LIT_LO, PML.LIT_HI in H.
  unfold PML.lits_ok, PML.lit_ok, PML.LIT_NULL_S, PML.LIT_NULL_G, PML.LIT_TRUE_S, PML.LIT_TRUE_G, PML.LIT_FALSE_S, PML.LIT_FALSE_G, PML.u8, PML.u64, L5.u8_at, L5.u64_at.
  repeat split; left; rewrite !(rdn_img M) by (first [cbn; lia | intros i Hi; apply H; cbn in Hi; lia]); repeat split; vm_compute; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rdn_S : forall (M : mem) (x : word) n,
  rdn RSEGS M x (S n) = match (match M x with Some b => Some b | None => seg_rom RSEGS x end) with
                        | Some b => match rdn RSEGS M (x + 1)%bv n with Some rest => Some (b :: rest) | None => None end | None => None end.
Proof. reflexivity. Qed.
Lemma u64_zero_bytes01 : forall (M : mem) a, 0 <= a -> a + 8 <= 2 ^ 64 -> PML.u64 M a 0 -> PML.u8 M a 0 /\ PML.u8 M (a + 1) 0.
Proof.
  intros M a Ha Ha8 H. unfold PML.u64, PML.u8, L5.u64_at, L5.u8_at in *.
  rewrite (rdn_S M _ 7) in H.
  destruct (match M (Z_to_bv 64 a) with Some b => Some b | None => seg_rom RSEGS (Z_to_bv 64 a) end) as [b0|] eqn:E0; [|discriminate].
  rewrite (rdn_S M _ 6) in H.
  assert (EA : (Z_to_bv 64 a + 1)%bv = Z_to_bv 64 (a + 1)).
  { apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    replace (bv_unsigned (1%bv : bv 64)) with 1 by reflexivity. rewrite (Z.mod_small a) by lia. reflexivity. }
  rewrite EA in H.
  destruct (match M (Z_to_bv 64 (a + 1)) with Some b => Some b | None => seg_rom RSEGS (Z_to_bv 64 (a + 1)) end) as [b1|] eqn:E1; [|discriminate].
  destruct (rdn RSEGS M (Z_to_bv 64 (a + 1) + 1)%bv 6) as [rest|] eqn:ER; [|discriminate].
  unfold word_to_le_bytes in H. cbn [Z_to_le_bytes] in H. injection H as H0 H1 H2.
  split; [rewrite (rdn_S M _ 0), E0; cbn [rdn]; rewrite H0; reflexivity | rewrite (rdn_S M _ 0), E1; cbn [rdn]; rewrite H1; reflexivity].
Qed.
Lemma sink0 : forall (M : mem) o, 0 <= o -> o + 24 <= 2 ^ 64 -> PML.u64 M o 0 -> L5.defined M o 24 -> PMES.sink_at M o (PML.SShort []).
Proof.
  intros M o Ho Ho24 H0 Hd. destruct (u64_zero_bytes01 M o Ho ltac:(lia) H0) as [B0 B1].
  split; [|split; [exact Hd | exact I]]. cbn [PML.str_at]. split; [cbn; lia|]. split; [exact B0|]. split; [intros i Hi; cbn in Hi; lia|].
  cbn [length Z.of_nat]. rewrite Z.add_0_r. exact B1.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma nodup_last : forall (A : list (Z * Z)) (x : Z * Z), base.NoDup (map fst (A ++ [x])) -> forall b, In b A -> fst b <> fst x.
Proof.
  induction A as [|a A IH]; intros x ND b Hb; [destruct Hb|].
  cbn [app map] in ND. inversion ND as [|y l N1 N2]; subst. destruct Hb as [<-|Hb].
  - intros X. apply N1. apply stdpp.base.list_elem_of_In. rewrite X. rewrite map_app. apply in_or_app. right. left. reflexivity.
  - exact (IH x N2 b Hb).
Qed.
Lemma lb_remove_last : forall (A : list (Z * Z)) p cap, (forall b, In b A -> fst b <> p) -> lb_remove p (A ++ [(p, cap)]) = A.
Proof.
  induction A as [|a A IH]; intros p cap H; cbn [app lb_remove fst].
  - rewrite Z.eqb_refl. reflexivity.
  - destruct (Z.eqb_spec (fst a) p) as [E|E]; [exfalso; exact (H a (or_introl eq_refl) E)|]. f_equal. apply IH. intros b Hb. apply H. right. exact Hb.
Qed.
(* [comment removed for export] *)
Lemma g_lbv_g0 : PMES.g_lbv PMES.g0 = [].
Proof. reflexivity. Qed.
Lemma kenc_g0 : forall L, PMX.kenc L PMES.g0 = 54 * hl_k_per_malloc L.
Proof. intros L. reflexivity. Qed.
Lemma kenc_nonneg : forall L g, 0 <= hl_k_per_malloc L -> 0 <= PMX.kenc L g.
Proof. intros L g H. unfold PMX.kenc. pose proof (EK.kv_s2_pos (PMES.g_rep g)). pose proof (EK.kv_st_nonneg (PMES.g_scap g)). nia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition hv_slotX (off : Z) (exc : list (nat * expr)) (q : nat) : expr :=
  if Nat.eqb q 2 then (if Z.eqb off 0 then EVar 2 else EAlu ALU_ADD (EVar 2) (ELit off))
  else match List.find (fun p => Nat.eqb (fst p) q) exc with Some p => snd p | None => EVar (32 + q) end.
Definition hv_shapeX (sr : list expr) (off : Z) (exc : list (nat * expr)) : bool :=
  forallb (fun q => expr_eqb (nth q sr (ELit 0)) (hv_slotX off exc q)) (seq 1 31).
Lemma regs_ok_hvX : forall sr off exc sp0 R gl bl,
  hv_shapeX sr off exc = true -> 0 <= sp0 < 2 ^ 64 -> 0 <= sp0 + off < 2 ^ 64 ->
  getr R 2%bv = Z_to_bv 64 (sp0 + off) ->
  (forall q e, In (q, e) exc -> getr R (Z_to_bv 5 (Z.of_nat q)) = edenot (CK.hvB sp0 R gl bl) e) ->
  regs_ok (CK.hvB sp0 R gl bl) sr R.
Proof.
  intros sr off exc sp0 R gl bl Hsh Hsp Hspo H2 Hexc. apply APSX.regs_ok_pointwise. intros r Hr0.
  assert (Hq : In (ridx r) (seq 1 31)).
  { apply in_seq. pose proof (ridx_range r). assert (ridx r <> 0%nat).
    { intros X. apply Hr0. rewrite <- (ridx_roundtrip r), X. apply bv_eq. reflexivity. } lia. }
  unfold hv_shapeX in Hsh. rewrite forallb_forall in Hsh. specialize (Hsh _ Hq). apply expr_eqb_eq in Hsh. rewrite Hsh.
  unfold hv_slotX. destruct (Nat.eqb (ridx r) 2) eqn:E2.
  - apply Nat.eqb_eq in E2. assert (r = 2%bv) by (rewrite <- (ridx_roundtrip r), E2; apply bv_eq; reflexivity). subst r.
    destruct (Z.eqb_spec off 0) as [->|Hne].
    + cbn [edenot ev CK.hvB]. unfold TK.hvV. cbn [Nat.ltb Nat.leb Nat.eqb]. rewrite H2. f_equal. lia.
    + cbn [edenot ev CK.hvB]. unfold TK.hvV. cbn [Nat.ltb Nat.leb Nat.eqb]. rewrite TK.add_lit by lia. exact H2.
  - destruct (find (fun p => Nat.eqb (fst p) (ridx r)) exc) as [[q e]|] eqn:Hf.
    + apply find_some in Hf as [Hin Hq2]. cbn [fst] in Hq2. apply Nat.eqb_eq in Hq2. subst q. cbn [snd].
      rewrite <- (Hexc _ _ Hin), ridx_roundtrip. reflexivity.
    + cbn [edenot]. symmetry. apply CK.hvB_reg.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma u64_zero : forall (M : mem) A, (forall i, 0 <= i < 8 -> M (Z_to_bv 64 (A + i)) = Some (Z_to_bv 8 0)) -> L5.u64_at RSEGS M A 0.
Proof.
  intros M A H. unfold L5.u64_at. cbn [rdn]. rewrite !L5C.add1_lit.
  pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
  replace (A + 1 + 1) with (A + 2) by lia. replace (A + 2 + 1) with (A + 3) by lia. replace (A + 3 + 1) with (A + 4) by lia. replace (A + 4 + 1) with (A + 5) by lia.
  replace (A + 5 + 1) with (A + 6) by lia. replace (A + 6 + 1) with (A + 7) by lia.
  rewrite H0, (H 1 ltac:(lia)), (H 2 ltac:(lia)), (H 3 ltac:(lia)), (H 4 ltac:(lia)), (H 5 ltac:(lia)), (H 6 ltac:(lia)), (H 7 ltac:(lia)). reflexivity.
Qed.
Lemma u32_zero : forall (M : mem) A, (forall i, 0 <= i < 4 -> M (Z_to_bv 64 (A + i)) = Some (Z_to_bv 8 0)) -> L5.u32_at RSEGS M A 0.
Proof.
  intros M A H. unfold L5.u32_at. cbn [rdn]. rewrite !L5C.add1_lit.
  pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
  replace (A + 1 + 1) with (A + 2) by lia. replace (A + 2 + 1) with (A + 3) by lia.
  rewrite H0, (H 1 ltac:(lia)), (H 2 ltac:(lia)), (H 3 ltac:(lia)). reflexivity.
Qed.
Lemma kword16_low : forall E (M : mem) a v A, kentry_ok RSEGS E M (KWord a 2 v) -> estart E a = A -> L5.u8_at RSEGS M A ((bv_unsigned (edenot E v)) mod 256).
Proof.
  intros E M a v A (_ & Hfl & Hr) Ha. unfold L5.u8_at. rewrite <- Ha, <- (CL5.adenot_start E a _ Hfl).
  set (x := adenot E a) in *. set (w := edenot E v) in *. clearbody x w.
  assert (EQ : forall n, rdn RSEGS M x (S n) = match (match M x with Some b => Some b | None => seg_rom RSEGS x end) with
                 | Some b => match rdn RSEGS M (x + 1)%bv n with Some rest => Some (b :: rest) | None => None end | None => None end) by reflexivity.
  rewrite (EQ 1%nat) in Hr. rewrite (EQ 0%nat). cbn [rdn].
  destruct (match M x with Some b => Some b | None => seg_rom RSEGS x end) as [b0|] eqn:E0; [|discriminate].
  destruct (rdn RSEGS M (x + 1)%bv 1) as [rest|] eqn:ER; [|discriminate].
  unfold word_to_le_bytes in Hr. cbn [Z_to_le_bytes] in Hr. injection Hr as H1 H2. f_equal. f_equal. rewrite H1. apply bv_eq.
  rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma mod256_of_mul : forall a k, (a * (256 * k)) mod 256 = 0.
Proof. intros a k. replace (a * (256 * k)) with ((a * k) * 256) by lia. apply Z.mod_mul. lia. Qed.
Lemma mod256_mod : forall x k, 0 < k -> (x mod (256 * k)) mod 256 = x mod 256.
Proof. intros x k Hk. rewrite (Z.rem_mul_r x 256 k) by lia. rewrite (Z.mul_comm 256), Z.mod_add by lia. apply Z.mod_mod. lia. Qed.
Lemma en_low_byte : forall (w : word), (bv_unsigned (ext_val true 0 2 (mul_div M_MUL (Z_to_bv 64 512) w))) mod 256 = 0.
Proof.
  intros w. unfold ext_val, ext_Z. cbn [Z.of_nat Z.mul Nat.mul]. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  cbn [mul_div]. rewrite bv_mul_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite (Z.mod_small 512) by lia. rewrite Z.div_1_r.
  set (u := bv_unsigned w). clearbody u.
  unfold bv_swrap, bv_wrap. change (bv_modulus (8 * N.of_nat 2)) with 65536. change (bv_half_modulus (8 * N.of_nat 2)) with 32768. change (2 ^ (8 * Z.of_nat 2)) with 65536.
  set (y := (512 * u) mod 2 ^ 64). assert (Y : y mod 256 = 0).
  { unfold y. change (2 ^ 64) with (256 * 2 ^ 56). rewrite mod256_mod by lia. replace (512 * u) with (u * (256 * 2)) by lia. apply mod256_of_mul. }
  clearbody y.
  set (t := y mod 65536). assert (T1 : t mod 256 = 0) by (unfold t; change 65536 with (256 * 256); rewrite mod256_mod by lia; exact Y).
  assert (T : 0 <= t < 65536) by (unfold t; apply Z.mod_pos_bound; lia). clearbody t.
  set (s := (t + 32768) mod 65536 - 32768).
  assert (S1 : s mod 256 = 0).
  { unfold s. destruct (Z_lt_le_dec t 32768).
    - rewrite (Z.mod_small (t + 32768) 65536) by lia. replace (t + 32768 - 32768) with t by lia. exact T1.
    - replace ((t + 32768) mod 65536) with (t + 32768 - 65536) by (apply (Z.mod_unique_pos (t + 32768) 65536 1); lia).
      replace (t + 32768 - 65536 - 32768) with (t + (-256) * 256) by lia. rewrite Z.mod_add by lia. exact T1. }
  clearbody s. change (2 ^ 64) with (256 * 2 ^ 56). rewrite mod256_mod by lia. exact S1.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rdn_lit_byte : forall (M : mem) n a z k, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> 0 <= z ->
  rdn RSEGS M (Z_to_bv 64 a) n = Some (Z_to_le_bytes n z) -> (k < n)%nat ->
  L5.u8_at RSEGS M (a + Z.of_nat k) ((z / 2 ^ (8 * Z.of_nat k)) mod 256).
Proof.
  intros M n. induction n as [|n IH]; intros a z k Ha Hn Hz H Hk; [lia|].
  rewrite rdn_S in H. destruct (match M (Z_to_bv 64 a) with Some b => Some b | None => seg_rom RSEGS (Z_to_bv 64 a) end) as [b0|] eqn:E0; [|discriminate].
  rewrite L5C.add1_lit in H by lia.
  destruct (rdn RSEGS M (Z_to_bv 64 (a + 1)) n) as [rest|] eqn:ER; [|discriminate].
  cbn [Z_to_le_bytes] in H. injection H as H0 H1.
  destruct k as [|k].
  - cbn [Z.of_nat Z.mul]. rewrite Z.add_0_r, Z.pow_0_r, Z.div_1_r. unfold L5.u8_at. rewrite rdn_S, E0, H0. cbn [rdn].
    unfold word_to_le_bytes. cbn [Z_to_le_bytes]. f_equal. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. change (bv_modulus 64) with (2 ^ 64).
    rewrite Z.mod_mod by lia. reflexivity.
  - replace (a + Z.of_nat (S k)) with (a + 1 + Z.of_nat k) by lia.
    replace (z / 2 ^ (8 * Z.of_nat (S k))) with ((Z.shiftr z 8) / 2 ^ (8 * Z.of_nat k)).
    2:{ rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_div by lia. f_equal. rewrite <- Z.pow_add_r by lia. f_equal. lia. }
    apply (IH (a + 1) (Z.shiftr z 8) k); [lia | lia | rewrite Z.shiftr_div_pow2 by lia; apply Z.div_pos; lia | | lia].
    rewrite ER, H1. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma wordn_lit_byte : forall (M : mem) n a z k, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> 0 <= z < 2 ^ 64 ->
  rdn RSEGS M (Z_to_bv 64 a) n = Some (word_to_le_bytes n (Z_to_bv 64 z)) -> (k < n)%nat ->
  L5.u8_at RSEGS M (a + Z.of_nat k) ((z / 2 ^ (8 * Z.of_nat k)) mod 256).
Proof.
  intros M n a z k Ha Hn Hz H Hk. apply (rdn_lit_byte M n a z k Ha Hn ltac:(lia)); [|exact Hk].
  rewrite H. unfold word_to_le_bytes. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma u64_byte : forall (M : mem) a z k, 0 <= a -> a + 8 <= 2 ^ 64 -> 0 <= z < 2 ^ 64 -> L5.u64_at RSEGS M a z -> (k < 8)%nat ->
  L5.u8_at RSEGS M (a + Z.of_nat k) ((z / 2 ^ (8 * Z.of_nat k)) mod 256).
Proof. intros M a z k Ha H8 Hz H Hk. apply (wordn_lit_byte M 8 a z k Ha ltac:(cbn; lia) Hz H Hk). Qed.
End TKX.
