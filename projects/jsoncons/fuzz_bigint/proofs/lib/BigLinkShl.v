(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Src0PlanKit AsanPlanCore AsanPlanSoundSums BigLinkBase BigLinkGlue BigLinkInlBase.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module BSHL.
Abbreviation RSEGS := Plain.M.loaded_segments.

Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).

Lemma In_of_existsb (i : nat) (l : list nat) : existsb (Nat.eqb i) l = true -> In i l.
Proof. intros H. apply existsb_exists in H as (x & Hx & E). apply Nat.eqb_eq in E. subst. exact Hx. Qed.

Ltac inK := apply In_of_existsb; vm_compute; reflexivity.

Lemma nth_error_single {A} (x y : A) i : nth_error [x] i = Some y -> y = x.
Proof. destruct i; simpl. congruence. destruct i; discriminate. Qed.

Lemma unsigned_of_lit (w : word) z : w = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> bv_unsigned w = z.
Proof. intros -> Hz. apply BG.unsigned_lit. exact Hz. Qed.

Lemma kentry_KUnk_z E M j off (a : Z) ne t n :
  bv_unsigned (ev E j) = a -> BL.zcomp ne = Some t -> BL.zden (BL.uv E) t = n ->
  0 <= a + off -> 0 < n < 2 ^ 64 -> a + off + n <= 2 ^ 64 ->
  BG.defined M (a + off) n -> kentry_ok RSEGS E M (KUnk (SA (EVar j) off) ne).
Proof.
  intros Ha Ht Hn H1 H2 H3 Hd. cbn [kentry_ok]. unfold flat, elenZ. rewrite BG.estart_var, Ha.
  rewrite (BL.zcomp_sound E ne t Ht), Hn. split. lia. intros i Hi. apply Hd. lia.
Qed.

Definition fb_chk : bool :=
  forallb (fun x : Z => if x mod 4 =? 1 then ((Z.land x 1 =? 1) && (Z.land x 2 =? 0) && (Z.land x 253 =? x))%bool else true) (map Z.of_nat (seq 0 256)).

Lemma fb_chk_ok : fb_chk = true. Proof. vm_compute. reflexivity. Qed.

Lemma fb_bits fb : 0 <= fb < 256 -> fb mod 4 = 1 -> Z.land fb 1 = 1 /\ Z.land fb 2 = 0 /\ Z.land fb 253 = fb.
Proof.
  intros Hr Hm. pose proof fb_chk_ok as C. unfold fb_chk in C. rewrite forallb_forall in C.
  specialize (C fb). assert (IN : In fb (map Z.of_nat (seq 0 256))). { apply in_map_iff. exists (Z.to_nat fb). split. lia. apply in_seq. lia. }
  specialize (C IN). rewrite (proj2 (Z.eqb_eq _ _) Hm) in C. apply andb_prop in C as [C C3]. apply andb_prop in C as [C1 C2].
  apply Z.eqb_eq in C1. apply Z.eqb_eq in C2. apply Z.eqb_eq in C3. auto.
Qed.

Lemma and_lit_val (x : word) m : 0 <= m < 2 ^ 64 -> bv_unsigned (alu64 ALU_AND x (Z_to_bv 64 m)) = Z.land (bv_unsigned x) m.
Proof.
  intros Hm. rewrite (BL.zalu_sound ALU_AND x (Z_to_bv 64 m) (Z.land (bv_unsigned x) m)). reflexivity.
  cbn [BL.zalu]. rewrite BG.unsigned_lit by lia. reflexivity.
Qed.

Lemma kentry_flagfacts E M i fb : bv_unsigned (ev E i) = fb -> 0 <= fb < 256 -> fb mod 4 = 1 ->
  Forall (kentry_ok RSEGS E M) [KRange (EAlu ALU_AND (EVar i) (ELit 1)) 1 1; KRange (EAlu ALU_AND (EVar i) (ELit 2)) 0 0; KRange (EVar i) 0 255].
Proof.
  intros U Hr Hm. destruct (fb_bits fb Hr Hm) as (B1 & B2 & _).
  apply Forall_cons. { cbn [kentry_ok edenot]. rewrite and_lit_val by lia. rewrite U, B1. lia. }
  apply Forall_cons. { cbn [kentry_ok edenot]. rewrite and_lit_val by lia. rewrite U, B2. lia. }
  apply Forall_cons. { cbn [kentry_ok edenot]. rewrite U. lia. }
  apply Forall_nil.
Qed.

Lemma kentry_KWord1_var E M j off i (a b : Z) :
  bv_unsigned (ev E j) = a -> bv_unsigned (ev E i) = b -> 0 <= a + off -> a + off + 1 <= 2 ^ 64 -> 0 <= b < 256 ->
  BG.u8_at M (a + off) b -> kentry_ok RSEGS E M (KWord (SA (EVar j) off) 1 (EVar i)).
Proof.
  intros Ha Hb H1 H2 Hr Hu. cbn [kentry_ok]. split. lia. split.
  - unfold flat. rewrite BG.estart_var, Ha. lia.
  - rewrite BG.adenot_var, Ha. cbn [edenot]. rewrite <- (Z_to_bv_bv_unsigned 64 (ev E i)), Hb. rewrite BG.word_to_le_bytes_1 by auto. exact Hu.
Qed.

Lemma u8_of_KWord1_var E M j off i (a b : Z) :
  kentry_ok RSEGS E M (KWord (SA (EVar j) off) 1 (EVar i)) -> bv_unsigned (ev E j) = a -> bv_unsigned (ev E i) = b -> 0 <= b < 256 -> BG.u8_at M (a + off) b.
Proof.
  intros K Ha Hb Hr. cbn [kentry_ok] in K. destruct K as (_ & F & Rd). unfold BG.u8_at.
  rewrite BG.adenot_var, Ha in Rd. cbn [edenot] in Rd. rewrite <- (Z_to_bv_bv_unsigned 64 (ev E i)), Hb in Rd. rewrite BG.word_to_le_bytes_1 in Rd by auto. exact Rd.
Qed.

Lemma u8_of_KWord1_and253 E M j off i (a b : Z) :
  kentry_ok RSEGS E M (KWord (SA (EVar j) off) 1 (EAlu ALU_AND (EVar i) (ELit 253))) -> bv_unsigned (ev E j) = a -> bv_unsigned (ev E i) = b ->
  0 <= b < 256 -> b mod 4 = 1 -> BG.u8_at M (a + off) b.
Proof.
  intros K Ha Hb Hr Hm. cbn [kentry_ok] in K. destruct K as (_ & F & Rd). unfold BG.u8_at.
  rewrite BG.adenot_var, Ha in Rd. cbn [edenot] in Rd.
  replace (alu64 ALU_AND (ev E i) (Z_to_bv 64 253)) with (Z_to_bv 64 b) in Rd. rewrite BG.word_to_le_bytes_1 in Rd by auto. exact Rd.
  apply bv_eq. rewrite and_lit_val by lia. rewrite Hb. destruct (fb_bits b Hr Hm) as (_ & _ & B3). rewrite B3. apply BG.unsigned_lit. lia.
Qed.

Lemma land_m2_even r : 0 <= r -> r mod 2 = 0 -> Z.land r (-2) = r.
Proof.
  intros Hr He. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
  change (-2) with (Z.lnot 1). rewrite Z.lnot_spec by lia.
  destruct (Z.eq_dec i 0) as [->|NZ].
  - rewrite Z.bit0_eqb. change (Z.testbit 1 0) with true. cbn [negb]. rewrite Bool.andb_false_r. symmetry. apply Z.eqb_neq. lia.
  - replace (Z.testbit 1 i) with false. rewrite Bool.andb_true_r. reflexivity. symmetry. rewrite <- (Z.pow_0_r 2). rewrite Z.pow2_bits_eqb by lia. apply Z.eqb_neq. lia.
Qed.

Lemma defined_word M a : BG.defined M a 8 -> 0 <= a -> a + 8 <= 2 ^ 64 -> exists w, 0 <= w < 2 ^ 64 /\ BG.u64_at M a w.
Proof.
  intros D Ha Hb.
  set (f := fun x : Z => match M (Z_to_bv 64 x) with Some b => b | None => Z_to_bv 8 0 end).
  set (bs := map (fun k => f (a + Z.of_nat k)) (seq 0 8)).
  exists (bytes_le_to_Z bs).
  assert (L: length bs = 8%nat) by reflexivity.
  pose proof (bytes_le_to_Z_bound bs) as B. rewrite L in B. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in B. split. exact B.
  unfold BG.u64_at. rewrite (APSX.word_to_le_bytes_of_bytes_n 8 bs L ltac:(lia)).
  unfold bs. apply (BG.rdn_of_bytes M f 8 a Ha Hb). intros i Hi. unfold f.
  destruct (M (Z_to_bv 64 (a + i))) eqn:E. reflexivity. exfalso. apply (D i). simpl in Hi; lia. exact E.
Qed.

Lemma rl1 : (1%bv : bv 5) = reg 1. Proof. apply bv_eq. reflexivity. Qed.
Lemma rl2 : (2%bv : bv 5) = reg 2. Proof. apply bv_eq. reflexivity. Qed.
Lemma rl3 : (3%bv : bv 5) = reg 3. Proof. apply bv_eq. reflexivity. Qed.
Lemma rl4 : (4%bv : bv 5) = reg 4. Proof. apply bv_eq. reflexivity. Qed.
Lemma rl10 : (10%bv : bv 5) = reg 10. Proof. apply bv_eq. reflexivity. Qed.
Lemma rl11 : (11%bv : bv 5) = reg 11. Proof. apply bv_eq. reflexivity. Qed.

End BSHL.
