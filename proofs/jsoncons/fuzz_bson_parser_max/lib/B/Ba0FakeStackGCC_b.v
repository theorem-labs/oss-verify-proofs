(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib MemSplit As0StepLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0MemIsZero_b Ba0RegionPoisoned_b
  Ba0AsanMemset_b Ba0AsanMemcpy_b Ba0StrlenIcpt_b Ba0TlsGetAddr_b Ba0FakeStackGC_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0_code_r48448_48dd8_b Ba0_code_r69818_698c8_b Ba0_code_r69654_69674_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition gc_fl (fs c i : Z) : Z := (fs + 4096 + 32768 - 2 * 2 ^ (14 - c) + i)%Z.          (* [comment removed for export] *)
Definition gc_fr (fs c i : Z) : Z := (fs + 4096 + 32768 + c * 2 ^ 20 + i * 2 ^ (6 + c))%Z.  (* [comment removed for export] *)
Definition gc_sh (fs c i : Z) : Z := (SB + gc_fr fs c i / 8)%Z.                             (* [comment removed for export] *)
Definition gc_valid (c i : Z) : Prop := (0 <= c <= 10)%Z /\ (0 <= i < 2 ^ (14 - c))%Z.
Definition gc_insh (fs c i a : Z) : Prop := (gc_sh fs c i <= a < gc_sh fs c i + 2 ^ (3 + c))%Z.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition gc_col (sparg bot : Z) (flag rs : Z -> Z -> Z) (c i : Z) : Prop := flag c i <> 0%Z /\ (bot < rs c i < sparg)%Z.
Definition gc_shz_lo (fs : Z) : Z := (SB + (fs + 4096 + 32768) / 8)%Z.                        (* [comment removed for export] *)
Definition gc_shz_hi (fs : Z) : Z := (SB + (fs + 4096 + 32768 + 11 * 2 ^ 20) / 8)%Z.

(* [comment removed for export] *)
Definition gc_outz (lo hi fs a : Z) : Prop :=
  (a < lo \/ hi <= a)%Z /\ ~ (fs + 4096 <= a < fs + 4096 + 32768)%Z /\ ~ (gc_shz_lo fs <= a < gc_shz_hi fs)%Z.
Definition gc_done_lt (c i c' i' : Z) : Prop := (c' < c \/ (c' = c /\ i' < i))%Z.                (* [comment removed for export] *)

(* [comment removed for export] *)
Definition gc_postb (gb : Z) (mem0 Mf : word -> option byte) (lo hi fs : Z) (col : Z -> Z -> Prop) : Prop :=
  mem_grows mem0 Mf
  /\ (forall x : word, (bv_unsigned x < lo \/ hi <= bv_unsigned x)%Z -> bv_unsigned x <> (fs + 96)%Z ->
        (forall c i, gc_valid c i -> col c i -> bv_unsigned x <> gc_fl fs c i /\ ~ gc_insh fs c i (bv_unsigned x)) -> Mf x = mem0 x)
  /\ (forall c i, gc_valid c i -> col c i -> Mf (Z_to_bv 64 (gc_fl fs c i)) = Some (Z_to_bv 8 0))
  /\ rdn ASEGS Mf (Z_to_bv 64 (fs + 96)) 1%nat = Some [Z_to_bv 8 gb].         (* [comment removed for export] *)

(* [comment removed for export] *)
Definition gc_post := gc_postb 0.

Lemma gc_pow_facts : forall c, (0 <= c <= 10)%Z ->
  (16 <= 2 ^ (14 - c) <= 16384)%Z /\ (64 <= 2 ^ (6 + c) <= 65536)%Z /\ (8 <= 2 ^ (3 + c) <= 8192)%Z
  /\ (2 ^ (14 - c) * 2 ^ (6 + c) = 2 ^ 20)%Z /\ (2 ^ (6 + c) = 2 ^ (3 + c) * 8)%Z.
Proof.
  intros c Hc.
  assert (E : (c = 0 \/ c = 1 \/ c = 2 \/ c = 3 \/ c = 4 \/ c = 5 \/ c = 6 \/ c = 7 \/ c = 8 \/ c = 9 \/ c = 10)%Z) by lia.
  destruct E as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]; vm_compute; intuition discriminate.
Qed.

Lemma gc_fl_range : forall fs c i, gc_valid c i -> (fs + 4096 <= gc_fl fs c i < fs + 4096 + 32768)%Z.
Proof. intros fs c i [Hc Hi]. pose proof (gc_pow_facts c Hc) as (P1 & _). unfold gc_fl. lia. Qed.

Lemma gc_fl_lt : forall fs c i c' i', gc_valid c i -> gc_valid c' i' -> (c < c')%Z -> (gc_fl fs c i < gc_fl fs c' i')%Z.
Proof.
  intros fs c i c' i' [Hc Hi] [Hc' Hi'] L. unfold gc_fl.
  assert (P : (2 * 2 ^ (14 - c') <= 2 ^ (14 - c))%Z).
  { replace (2 * 2 ^ (14 - c'))%Z with (2 ^ (15 - c'))%Z by (replace (15 - c')%Z with (Z.succ (14 - c')) by lia; rewrite Z.pow_succ_r by lia; reflexivity).
    apply Z.pow_le_mono_r; lia. }
  lia.
Qed.
Lemma gc_fl_inj : forall fs c i c' i', gc_valid c i -> gc_valid c' i' -> gc_fl fs c i = gc_fl fs c' i' -> c = c' /\ i = i'.
Proof.
  intros fs c i c' i' V V' E.
  destruct (Z.lt_trichotomy c c') as [L|[->|L]].
  - pose proof (gc_fl_lt fs c i c' i' V V' L). lia.
  - split; [reflexivity|]. unfold gc_fl in E. lia.
  - pose proof (gc_fl_lt fs c' i' c i V' V L). lia.
Qed.

Lemma gc_fr_range : forall fs c i, gc_valid c i ->
  (fs + 4096 + 32768 <= gc_fr fs c i)%Z /\ (gc_fr fs c i + 2 ^ (6 + c) <= fs + 4096 + 32768 + 11 * 2 ^ 20)%Z.
Proof.
  intros fs c i [Hc Hi]. pose proof (gc_pow_facts c Hc) as (P1 & P2 & P3 & P4 & P5). unfold gc_fr.
  assert (A : (0 <= i * 2 ^ (6 + c))%Z) by (apply Z.mul_nonneg_nonneg; lia).
  assert (B : (i * 2 ^ (6 + c) + 2 ^ (6 + c) <= 2 ^ 20)%Z).
  { rewrite <- P4. replace (i * 2 ^ (6 + c) + 2 ^ (6 + c))%Z with ((i + 1) * 2 ^ (6 + c))%Z by ring. apply Z.mul_le_mono_nonneg_r; lia. }
  assert (C : (0 <= c * 2 ^ 20 <= 10 * 2 ^ 20)%Z) by lia.
  lia.
Qed.

Lemma gc_sh_range : forall fs c i, gc_valid c i -> (gc_shz_lo fs <= gc_sh fs c i)%Z /\ (gc_sh fs c i + 2 ^ (3 + c) <= gc_shz_hi fs)%Z.
Proof.
  intros fs c i V. pose proof (gc_fr_range fs c i V) as [R1 R2]. destruct V as [Hc Hi].
  pose proof (gc_pow_facts c Hc) as (P1 & P2 & P3 & P4 & P5). unfold gc_sh, gc_shz_lo, gc_shz_hi.
  split.
  - apply Z.add_le_mono_l. apply Z.div_le_mono; lia.
  - assert (E : ((gc_fr fs c i + 2 ^ (6 + c)) / 8 = gc_fr fs c i / 8 + 2 ^ (3 + c))%Z) by (rewrite P5; apply Z.div_add; lia).
    assert (L : ((gc_fr fs c i + 2 ^ (6 + c)) / 8 <= (fs + 4096 + 32768 + 11 * 2 ^ 20) / 8)%Z) by (apply Z.div_le_mono; lia).
    lia.
Qed.

(* [comment removed for export] *)
Lemma gc_shz_facts : forall fs, (0x696000 <= fs)%Z -> (fs + 4096 + 32768 + 11 * 2 ^ 20 < 2 ^ 47)%Z ->
  (fs + 4096 + 32768 + 11 * 2 ^ 20 <= 0x7fff7000 \/ 0x10007fff8000 <= fs)%Z ->
  (gc_shz_hi fs <= fs \/ fs + 4096 + 32768 + 11 * 2 ^ 20 <= gc_shz_lo fs)%Z /\ (0x7fff8000 <= gc_shz_lo fs)%Z /\ (gc_shz_lo fs <= gc_shz_hi fs)%Z /\ (gc_shz_hi fs < 2 ^ 45)%Z.
Proof.
  intros fs F1 F2 A. unfold gc_shz_lo, gc_shz_hi, SB.
  assert (D1 : (0 <= (fs + 4096 + 32768) / 8)%Z) by (apply Z.div_pos; lia).
  assert (D2 : ((fs + 4096 + 32768) / 8 <= (fs + 4096 + 32768 + 11 * 2 ^ 20) / 8)%Z) by (apply Z.div_le_mono; lia).
  assert (D3 : ((fs + 4096 + 32768 + 11 * 2 ^ 20) / 8 <= 2 ^ 47 / 8)%Z) by (apply Z.div_le_mono; lia).
  change (2 ^ 47 / 8)%Z with 17592186044416%Z in D3.
  repeat split; try lia.
Qed.
Lemma gc_fr_in_app : forall fs c i, (0x696000 <= fs)%Z -> (fs + 4096 + 32768 + 11 * 2 ^ 20 < 2 ^ 47)%Z ->
  (fs + 4096 + 32768 + 11 * 2 ^ 20 <= 0x7fff7000 \/ 0x10007fff8000 <= fs)%Z -> gc_valid c i -> in_app (gc_fr fs c i).
Proof.
  intros fs c i F1 F2 A V. pose proof (gc_fr_range fs c i V) as [R1 R2]. destruct V as [Hc Hi]. pose proof (gc_pow_facts c Hc) as (_ & P2 & _).
  unfold in_app, LOWEND, HIGHBEG, HIGHEND. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma u64_lit : forall a, (0 <= a < 2 ^ 64)%Z -> bv_unsigned (Z_to_bv 64 a) = a.
Proof. intros a Ha. apply u_Z2bv; lia. Qed.
Lemma word_of_u : forall (x : word) a, bv_unsigned x = a -> x = Z_to_bv 64 a.
Proof. intros x a <-. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma len_concat_le8 : forall (w : word) n, Z.of_nat (length (concat (repeat (word_to_le_bytes 8 w) n))) = (8 * Z.of_nat n)%Z.
Proof.
  intros w n. induction n as [|n IH]; [reflexivity|]. cbn [repeat concat]. rewrite length_app, Nat2Z.inj_add, IH, length_N_to_le_bytes. lia.
Qed.

Section GCM.
  Variable mem0 : word -> option byte.
  Variables lo hi fs : Z.                          (* [comment removed for export] *)
  Variable col : Z -> Z -> Prop.
  Hypothesis Hfsb : (0 <= fs)%Z /\ (fs + 4096 + 32768 + 11 * 2 ^ 20 < 2 ^ 64)%Z.
  Hypothesis Hzb : (0 <= gc_shz_lo fs)%Z /\ (gc_shz_hi fs < 2 ^ 64)%Z.
  Hypothesis Hdj_fl_sh : (gc_shz_hi fs <= fs \/ fs + 4096 + 32768 + 11 * 2 ^ 20 <= gc_shz_lo fs)%Z.     (* [comment removed for export] *)
  Hypothesis Hdj_fr_fs : (hi <= fs \/ fs + 4096 + 32768 + 11 * 2 ^ 20 <= lo)%Z.                          (* [comment removed for export] *)
  Hypothesis Hdj_fr_sh : (gc_shz_hi fs <= lo \/ hi <= gc_shz_lo fs)%Z.                                  (* [comment removed for export] *)

  Definition gcm (done : Z -> Z -> Prop) (M : word -> option byte) : Prop :=
    mem_grows mem0 M
    /\ (forall x : word, (bv_unsigned x < lo \/ hi <= bv_unsigned x)%Z ->
          (forall c i, gc_valid c i -> done c i -> col c i -> bv_unsigned x <> gc_fl fs c i /\ ~ gc_insh fs c i (bv_unsigned x)) -> M x = mem0 x)
    /\ (forall c i, gc_valid c i -> done c i -> col c i -> M (Z_to_bv 64 (gc_fl fs c i)) = Some (Z_to_bv 8 0)).

  #[using="Type"] Lemma gcm_init : forall M, mem_grows mem0 M -> (forall x : word, (bv_unsigned x < lo \/ hi <= bv_unsigned x)%Z -> M x = mem0 x) -> gcm (fun _ _ => False) M.
  Proof. intros M G O. split; [exact G|]. split; [intros x Hx _; apply O; exact Hx | intros c i _ []]. Qed.

  #[using="Type"] Lemma gcm_equiv : forall (d d' : Z -> Z -> Prop) M, (forall c i, gc_valid c i -> (d' c i <-> d c i)) -> gcm d M -> gcm d' M.
  Proof.
    intros d d' M E (G & O & P). split; [exact G|]. split.
    - intros x Hx Hn. apply O; [exact Hx|]. intros c i V D C. apply Hn; [exact V | apply E; assumption | exact C].
    - intros c i V D C. apply P; [exact V | apply E; assumption | exact C].
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma gcm_skip : forall (d d' : Z -> Z -> Prop) M c0 i0, ~ col c0 i0 ->
    (forall c i, gc_valid c i -> (d' c i <-> d c i \/ (c = c0 /\ i = i0))) -> gcm d M -> gcm d' M.
  Proof.
    intros d d' M c0 i0 NC E (G & O & P). split; [exact G|]. split.
    - intros x Hx Hn. apply O; [exact Hx|]. intros c i V D C. apply Hn; [exact V | apply E; [exact V | left; exact D] | exact C].
    - intros c i V D C. apply E in D; [|exact V]. destruct D as [D|[-> ->]]; [apply P; assumption | contradiction].
  Qed.

  (* [comment removed for export] *)
  #[using="Hfsb Hdj_fr_fs"] Lemma gcm_frame : forall d M M', gcm d M -> mem_grows M M' -> (forall x : word, (bv_unsigned x < lo \/ hi <= bv_unsigned x)%Z -> M' x = M x) -> gcm d M'.
  Proof.
    intros d M M' (G & O & P) G' O'. split; [eapply mem_grows_trans; eassumption|]. split.
    - intros x Hx Hn. rewrite (O' x Hx). apply O; assumption.
    - intros c i V D C. pose proof (P c i V D C) as P1. pose proof (gc_fl_range fs c i V) as FR.
      rewrite O'; [exact P1 | rewrite u64_lit by lia; lia].
  Qed.

  (* [comment removed for export] *)
  #[using="Hdj_fl_sh"] Lemma gcm_out : forall d M, gcm d M -> forall x : word, (bv_unsigned x < lo \/ hi <= bv_unsigned x)%Z ->
    ~ (fs + 4096 <= bv_unsigned x < fs + 4096 + 32768)%Z -> ~ (gc_shz_lo fs <= bv_unsigned x < gc_shz_hi fs)%Z -> M x = mem0 x.
  Proof.
    intros d M (G & O & P) x Hx Nf Ns. apply O; [exact Hx|]. intros c i V _ _.
    pose proof (gc_fl_range fs c i V) as FR. pose proof (gc_sh_range fs c i V) as [S1 S2]. unfold gc_insh. lia.
  Qed.
  #[using="Hfsb Hdj_fl_sh Hdj_fr_fs"] Lemma gcm_flag : forall d M c i, gcm d M -> gc_valid c i -> ~ d c i -> M (Z_to_bv 64 (gc_fl fs c i)) = mem0 (Z_to_bv 64 (gc_fl fs c i)).
  Proof.
    intros d M c i (G & O & P) V ND. pose proof (gc_fl_range fs c i V) as FR.
    apply O; [rewrite u64_lit by lia; lia|]. rewrite u64_lit by lia. intros c' i' V' D' C'. split.
    - intros E. apply (gc_fl_inj fs c i c' i' V V') in E. destruct E as [-> ->]. contradiction.
    - pose proof (gc_sh_range fs c' i' V') as [S1 S2]. unfold gc_insh. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Hfsb Hzb Hdj_fl_sh"] Lemma gcm_collect : forall (d d' : Z -> Z -> Prop) M c0 i0 bs, gc_valid c0 i0 -> col c0 i0 -> Z.of_nat (length bs) = (2 ^ (3 + c0))%Z ->
    (forall c i, gc_valid c i -> (d' c i <-> d c i \/ (c = c0 /\ i = i0))) -> gcm d M ->
    gcm d' (wbytes (wbytes M (Z_to_bv 64 (gc_fl fs c0 i0)) [Z_to_bv 8 0]) (Z_to_bv 64 (gc_sh fs c0 i0)) bs).
  Proof.
    intros d d' M c0 i0 bs V0 C0 Ln E (G & O & P).
    pose proof (gc_fl_range fs c0 i0 V0) as FR0. pose proof (gc_sh_range fs c0 i0 V0) as [S01 S02].
    pose proof (gc_pow_facts c0 (proj1 V0)) as (_ & _ & P3 & _).
    set (M1 := wbytes M (Z_to_bv 64 (gc_fl fs c0 i0)) [Z_to_bv 8 0]).
    assert (OUT2 : forall x : word, ~ gc_insh fs c0 i0 (bv_unsigned x) -> wbytes M1 (Z_to_bv 64 (gc_sh fs c0 i0)) bs x = M1 x).
    { intros x Hx. unfold gc_insh in Hx. apply wbytes_outside; rewrite Ln, u64_lit by lia; lia. }
    assert (OUT1 : forall x : word, bv_unsigned x <> gc_fl fs c0 i0 -> M1 x = M x).
    { intros x Hx. unfold M1. apply wbytes_outside; cbn [length Z.of_nat Pos.to_nat]; rewrite u64_lit by lia; lia. }
    assert (IN1 : M1 (Z_to_bv 64 (gc_fl fs c0 i0)) = Some (Z_to_bv 8 0)).
    { unfold M1. rewrite wbytes_inside by (cbn [length Z.of_nat Pos.to_nat]; rewrite ?u64_lit by lia; lia). rewrite Z.sub_diag. reflexivity. }
    split; [eapply mem_grows_trans; [exact G|]; eapply mem_grows_trans; apply wbytes_grows|]. split.
    - intros x Hx Hn.
      destruct (Hn c0 i0 V0 ltac:(apply E; [exact V0 | right; split; reflexivity]) C0) as [N1 N2].
      rewrite OUT2 by exact N2. rewrite OUT1 by exact N1. apply O; [exact Hx|].
      intros c i Vv D C. apply Hn; [exact Vv | apply E; [exact Vv | left; exact D] | exact C].
    - intros c i V D C. pose proof (gc_fl_range fs c i V) as FR. pose proof (gc_sh_range fs c0 i0 V0) as [S1 S2].
      rewrite OUT2 by (unfold gc_insh; rewrite u64_lit by lia; lia).
      destruct (Z.eq_dec (gc_fl fs c i) (gc_fl fs c0 i0)) as [Ef|Nf]; [rewrite Ef; exact IN1|].
      rewrite OUT1 by (rewrite u64_lit by lia; exact Nf).
      apply E in D; [|exact V]. destruct D as [D|[-> ->]]; [apply (P c i V D C) | contradiction Nf; reflexivity].
  Qed.
End GCM.

(* [comment removed for export] *)
Lemma gc_post_widen : forall gb (mem0 M2 Mf : word -> option byte) lo hi lo' hi' fs col,
  gc_postb gb M2 Mf lo' hi' fs col -> (lo <= lo')%Z -> (hi' <= hi)%Z -> mem_grows mem0 M2 ->
  (forall x : word, (bv_unsigned x < lo \/ hi <= bv_unsigned x)%Z -> M2 x = mem0 x) -> gc_postb gb mem0 Mf lo hi fs col.
Proof.
  intros gb mem0 M2 Mf lo hi lo' hi' fs col (G & O & P & Q) L1 L2 G2 O2. split; [eapply mem_grows_trans; eassumption|]. split; [|split; [exact P | exact Q]].
  intros x Hx N96 Hn. rewrite (O x) by (first [lia | assumption]). apply O2. exact Hx.
Qed.
Lemma gc_post_ext : forall gb (mem0 Mf : word -> option byte) lo hi fs (col col' : Z -> Z -> Prop),
  (forall c i, gc_valid c i -> (col' c i <-> col c i)) -> gc_postb gb mem0 Mf lo hi fs col -> gc_postb gb mem0 Mf lo hi fs col'.
Proof.
  intros gb mem0 Mf lo hi fs col col' E (G & O & P & Q). split; [exact G|]. split; [|split; [|exact Q]].
  - intros x Hx N96 Hn. apply O; [exact Hx | exact N96 |]. intros c i V C. apply Hn; [exact V | apply E; assumption].
  - intros c i V C. apply P; [exact V | apply E; assumption].
Qed.
Lemma gc_post_rdn : forall gb (mem0 Mf : word -> option byte) lo hi fs col a (n : nat), gc_postb gb mem0 Mf lo hi fs col ->
  (0 <= a)%Z -> (a + Z.of_nat n <= 2 ^ 64)%Z ->
  (a + Z.of_nat n <= lo \/ hi <= a)%Z -> (a + Z.of_nat n <= fs + 96 \/ fs + 97 <= a)%Z ->
  (a + Z.of_nat n <= fs + 4096 \/ fs + 4096 + 32768 <= a)%Z -> (a + Z.of_nat n <= gc_shz_lo fs \/ gc_shz_hi fs <= a)%Z ->
  rdn ASEGS Mf (Z_to_bv 64 a) n = rdn ASEGS mem0 (Z_to_bv 64 a) n.
Proof.
  intros gb mem0 Mf lo hi fs col a n (G & O & P & Q) A1 A2 D1 D2 D3 D4.
  destruct n as [|n]; [reflexivity|].
  apply rdn_ext; [rewrite u64_lit by lia; lia|]. intros x Hx. rewrite u64_lit in Hx by lia.
  apply O; [lia | lia |]. intros c i V _. pose proof (gc_fl_range fs c i V) as FR. pose proof (gc_sh_range fs c i V) as [S1 S2]. unfold gc_insh. lia.
Qed.
Lemma gc_post_flag_keep : forall gb (mem0 Mf : word -> option byte) lo hi fs col c i, gc_postb gb mem0 Mf lo hi fs col ->
  (0 <= fs)%Z -> (fs + 4096 + 32768 + 11 * 2 ^ 20 < 2 ^ 64)%Z -> (gc_shz_hi fs <= fs \/ fs + 4096 + 32768 + 11 * 2 ^ 20 <= gc_shz_lo fs)%Z ->
  (hi <= fs \/ fs + 4096 + 32768 + 11 * 2 ^ 20 <= lo)%Z -> gc_valid c i -> ~ col c i ->
  rdn ASEGS Mf (Z_to_bv 64 (gc_fl fs c i)) 1%nat = rdn ASEGS mem0 (Z_to_bv 64 (gc_fl fs c i)) 1%nat.
Proof.
  intros gb mem0 Mf lo hi fs col c i (G & O & P & Q) F1 F2 K3 K4 V NC. pose proof (gc_fl_range fs c i V) as FR.
  apply rdn_ext; [rewrite u64_lit by lia; cbn [Z.of_nat Pos.to_nat]; lia|]. intros x Hx. rewrite u64_lit in Hx by lia. cbn [Z.of_nat Pos.to_nat] in Hx.
  apply O; [lia | lia |]. intros c' i' V' C'. split.
  - intros E. replace (bv_unsigned x) with (gc_fl fs c i) in E by lia. apply (gc_fl_inj fs c i c' i' V V') in E. destruct E as [-> ->]. contradiction.
  - pose proof (gc_sh_range fs c' i' V') as [S1 S2]. unfold gc_insh. lia.
Qed.
Lemma gc_post_flag_col : forall gb (mem0 Mf : word -> option byte) lo hi fs col c i, gc_postb gb mem0 Mf lo hi fs col ->
  (0 <= fs)%Z -> (fs + 4096 + 32768 + 11 * 2 ^ 20 < 2 ^ 64)%Z -> gc_valid c i -> col c i ->
  rdn ASEGS Mf (Z_to_bv 64 (gc_fl fs c i)) 1%nat = Some [Z_to_bv 8 0].
Proof.
  intros gb mem0 Mf lo hi fs col c i (G & O & P & Q) F1 F2 V C. pose proof (gc_fl_range fs c i V) as FR. pose proof (P c i V C) as P1.
  change [Z_to_bv 8 0] with (repeat (Z_to_bv 8 0) 1). apply MemSplit.rdn_const; [rewrite u64_lit by lia; cbn [Z.of_nat Pos.to_nat]; lia|].
  intros x Hx. rewrite u64_lit in Hx by lia. cbn [Z.of_nat Pos.to_nat] in Hx. rewrite (word_of_u x (gc_fl fs c i)) by lia. exact P1.
Qed.

Section FPX_1. Context {fx : PropExec.FPState}.

#[local] Ltac rwH :=
  repeat match goal with
         | H : getr ?rg ?i = _ |- context [getr ?rg ?i] => rewrite !H
         end.
#[local] Ltac unorm :=
  repeat match goal with
         | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
             lazymatch z with context [Z_to_bv 64 _] => fail | _ => rewrite (u_Z2bv z) by lia end
         end.
#[local] Ltac cond :=
  rwH; unfold at_, v_addi, v_add, c_eq, c_ltu, bv_eqb, bv_ltu; imm_norm; unorm;
  first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge]; lia.
#[local] Ltac wval :=
  gres; rwH; unfold at_, v_addi, v_add, v_sub, v_srli; imm_norm; unorm; rewrite ?Z.shiftr_div_pow2 by lia;
  try change (2 ^ 3)%Z with 8%Z; first [reflexivity | f_equal; lia].
#[local] Ltac maddr z := match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 z) by (symmetry; wval) end.
#[local] Ltac mldq F D z R :=
  chain_step; [reflexivity
    | eapply step_ld with (bs := word_to_le_bytes 8 (Z_to_bv 64 _)); [exact F | reflexivity | exact D | maddr z; exact R | exact (bytes_le_to_Z_8 _)]
    | step_simpl; vnorm].
#[local] Ltac post := repeat split; gres; rwH; try reflexivity; try (f_equal; lia); try solve_keeps_but.
#[local] Ltac mlbq F D z R :=
  chain_step; [reflexivity
    | eapply step_lb; [exact F | reflexivity | exact D | maddr z; exact R]
    | step_simpl; vnorm].
(* [comment removed for export] *)
#[local] Ltac kbt := first [ solve [repeat first [left; reflexivity | right]]
                           | let HIn := fresh "HIn" in let E := fresh "E" in intros HIn; repeat (destruct HIn as [E|HIn]; [discriminate E|]); exact HIn ].
#[local] Ltac stepsdq F D aa vv oktac :=
  chain_step; [reflexivity
    | eapply step_sd_at with (a := aa) (v := vv); [exact F | reflexivity | exact D | wval | gres; rwH; first [reflexivity | f_equal; lia] | oktac]
    | step_simpl].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section SETSH.
  Variable M : word -> option byte.
  Variable rom : word -> option byte.
  Variables c sh g35 : Z.                      (* [comment removed for export] *)
  Hypothesis Hc : (0 <= c <= 6)%Z.
  Hypothesis Hsh : (0 <= sh)%Z /\ (sh + 8 * 2 ^ c < 2 ^ 64)%Z.
  Hypothesis Hok : store_ok ASEGS M (Z_to_bv 64 sh) (Z.to_nat (8 * 2 ^ c)) = true.

  Definition ssm (k : Z) : word -> option byte := wbytes M (Z_to_bv 64 sh) (concat (repeat (word_to_le_bytes 8 (Z_to_bv 64 g35)) (Z.to_nat k))).
  Definition ss_inv (rg : bvmap 5 word) (k : Z) : Prop :=
    getr rg 10 = Z_to_bv 64 (k + 1) /\ getr rg 11 = Z_to_bv 64 (sh + 8 * k) /\ getr rg 23 = Z_to_bv 64 g35 /\ getr rg 20 = Z_to_bv 64 c.
  Definition ss_keeps (regs regs' : bvmap 5 word) : Prop := forall r : reg, r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> getr regs' r = getr regs r.
  #[local] Ltac kp3 := intros r N10 N11 N12; repeat (rewrite getr_other; [| intros ->; match goal with Hn : ?a <> ?a |- _ => exact (Hn eq_refl) end]); reflexivity.

  #[using="Hc"] Lemma pow_c_bounds : (1 <= 2 ^ c <= 64)%Z.
  Proof.
    split; [change 1%Z with (2 ^ 0)%Z | change 64%Z with (2 ^ 6)%Z]; apply Z.pow_le_mono_r; lia.
  Qed.

  #[using="Hc Hsh"] Lemma ssm_step : forall k, (0 <= k)%Z -> (k < 2 ^ c)%Z ->
    wbytes (ssm k) (Z_to_bv 64 (sh + 8 * k)) (word_to_le_bytes 8 (Z_to_bv 64 g35)) = ssm (k + 1).
  Proof.
    intros k Hk Hk2. unfold ssm.
    replace (Z.to_nat (k + 1)) with (Z.to_nat k + 1)%nat by lia.
    rewrite repeat_app, concat_app. cbn [repeat concat]. rewrite app_nil_r, wbytes_app. f_equal. unfold at_. rewrite len_concat_le8. f_equal.
    destruct Hsh as [S1 S2]. rewrite u_Z2bv by lia. lia.
  Qed.

  #[using="Hc Hsh Hok"] Lemma gc_setshadow_loop : forall (q : nat) regs k,
    ss_inv regs k -> (0 <= k)%Z -> (k + Z.of_nat q + 1 = 2 ^ c)%Z ->
    exists regs', msteps ASEGS (mkst regs (0x5d9ac : word) (ssm k) rom) (mkst regs' (0x5d908 : word) (ssm (2 ^ c)) rom) /\ ss_keeps regs regs'.
  Proof.
    induction q as [|q IH]; intros regs k (H10 & H11 & H23 & H20) Hk Hq; pose proof pow_c_bounds as Pc; destruct Hsh as [S1 S2].
    - assert (Hdiv : ((k + 1) / 2 ^ c = 1)%Z) by (replace (k + 1)%Z with (2 ^ c)%Z by lia; apply Z.div_same; lia).
      eexists. split.
      + stepsdq F_5d594 D_5d594 (Z_to_bv 64 (sh + 8 * k)) (Z_to_bv 64 g35)
          ltac:(apply (store_ok_mono _ _ M); [apply wbytes_grows|];
                apply (store_ok_sub ASEGS M (Z_to_bv 64 sh) _ (Z.to_nat (8 * 2 ^ c))); [unorm; lia | exact Hok | unorm; lia | unorm; cbn [Z.of_nat Pos.to_nat]; lia]).   (* [comment removed for export] *)
        rewrite (ssm_step k Hk ltac:(lia)).
        stepsv F_5d598 D_5d598 (Z_to_bv 64 1) ltac:(gres; rwH; rewrite v_srl_lit by lia; rewrite Hdiv; reflexivity).   (* [comment removed for export] *)
        stepiv F_5d59c D_5d59c (Z_to_bv 64 (sh + 8 * (k + 1))) ltac:(wval).                              (* [comment removed for export] *)
        stepiv F_5d5a0 D_5d5a0 (Z_to_bv 64 (k + 1 + 1)) ltac:(wval).                                     (* [comment removed for export] *)
        stepb_ft F_5d5a4 D_5d5a4 ltac:(cond).                                                             (* [comment removed for export] *)
        stepn F_5d5a8 D_5d5a8.                                                                            (* [comment removed for export] *)
        replace (k + 1)%Z with (2 ^ c)%Z by lia.
        apply mst_refl.
      + kp3.
    - assert (Hdiv : ((k + 1) / 2 ^ c = 0)%Z) by (apply Z.div_small; lia).
      assert (STEP : exists r1, msteps ASEGS (mkst regs (0x5d9ac : word) (ssm k) rom) (mkst r1 (0x5d9ac : word) (ssm (k + 1)) rom) /\ ss_inv r1 (k + 1) /\ ss_keeps regs r1).
      { eexists. split.
        - stepsdq F_5d594 D_5d594 (Z_to_bv 64 (sh + 8 * k)) (Z_to_bv 64 g35)
            ltac:(apply (store_ok_mono _ _ M); [apply wbytes_grows|];
                  apply (store_ok_sub ASEGS M (Z_to_bv 64 sh) _ (Z.to_nat (8 * 2 ^ c))); [unorm; lia | exact Hok | unorm; lia | unorm; cbn [Z.of_nat Pos.to_nat]; lia]).
          rewrite (ssm_step k Hk ltac:(lia)).
          stepsv F_5d598 D_5d598 (Z_to_bv 64 0) ltac:(gres; rwH; rewrite v_srl_lit by lia; rewrite Hdiv; reflexivity).
          stepiv F_5d59c D_5d59c (Z_to_bv 64 (sh + 8 * (k + 1))) ltac:(wval).
          stepiv F_5d5a0 D_5d5a0 (Z_to_bv 64 (k + 1 + 1)) ltac:(wval).
          stepb_tk F_5d5a4 D_5d5a4 ltac:(cond).                                                           (* [comment removed for export] *)
          apply mst_refl.
        - split; [unfold ss_inv; post | kp3]. }
      destruct STEP as (r1 & RUN1 & INV1 & KP1).
      destruct (IH r1 (k + 1)%Z INV1 ltac:(lia) ltac:(lia)) as (r2 & RUN2 & KP2).
      exists r2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2]|].
      intros r N10 N11 N12. rewrite (KP2 r N10 N11 N12). apply KP1; assumption.
  Qed.
End SETSH.

#[using="Type"] Lemma gc_kit : forall t fs,
  (0x696000 <= fs)%Z /\ (fs + 4096 + 32768 + 11 * 2 ^ 20 < 2 ^ 47)%Z /\ (fs + 4096 + 32768 + 11 * 2 ^ 20 <= t - 160 \/ t <= fs)%Z ->
  (fs + 4096 + 32768 + 11 * 2 ^ 20 <= 0x7fff7000 \/ 0x10007fff8000 <= fs)%Z ->
  ((0 <= fs)%Z /\ (fs + 4096 + 32768 + 11 * 2 ^ 20 < 2 ^ 64)%Z) /\ ((0 <= gc_shz_lo fs)%Z /\ (gc_shz_hi fs < 2 ^ 64)%Z)
  /\ (gc_shz_hi fs <= fs \/ fs + 4096 + 32768 + 11 * 2 ^ 20 <= gc_shz_lo fs)%Z /\ (t <= fs \/ fs + 4096 + 32768 + 11 * 2 ^ 20 <= t - 160)%Z.
Proof.
  intros t fs (F1 & F2 & F3) A. pose proof (gc_shz_facts fs F1 F2 A) as (Z1 & Z2 & Z3 & Z4). repeat split; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section SLOT.
  Variables mem0 Mfr : word -> option byte.      (* [comment removed for export] *)
  Variable rom : word -> option byte.
  Variables t fs c nfr nlog frsz flb sparg bot g35 : Z.
  Variables flag rs : Z -> Z -> Z.
  Hypothesis Hc : (0 <= c <= 10)%Z.
  Hypothesis Hnlog : nlog = (14 - c)%Z.
  Hypothesis Hnfr : nfr = (2 ^ nlog)%Z.
  Hypothesis Hfrsz : frsz = (2 ^ (6 + c))%Z.
  Hypothesis Hflb : flb = (fs + 4096 + 32768 - 2 * nfr)%Z.
  Hypothesis Ht : (0x1000000 <= t - 160)%Z /\ (t < 2 ^ 64)%Z.
  Hypothesis Hfs : (0x696000 <= fs)%Z /\ (fs + 4096 + 32768 + 11 * 2 ^ 20 < 2 ^ 47)%Z /\ (fs + 4096 + 32768 + 11 * 2 ^ 20 <= t - 160 \/ t <= fs)%Z.
  Hypothesis Happ : (fs + 4096 + 32768 + 11 * 2 ^ 20 <= 0x7fff7000 \/ 0x10007fff8000 <= fs)%Z.
  Hypothesis Hshz : (gc_shz_hi fs <= t - 160 \/ t <= gc_shz_lo fs)%Z.
  Hypothesis Hsp : (0 <= sparg < 2 ^ 64)%Z /\ (0 <= bot < 2 ^ 64)%Z.
  Hypothesis Hwfs : store_ok ASEGS mem0 (Z_to_bv 64 fs) (Z.to_nat (4096 + 32768 + 11 * 2 ^ 20)) = true.
  Hypothesis HF0 : forall c i, gc_valid c i ->
    rdn ASEGS mem0 (Z_to_bv 64 (gc_fl fs c i)) 1%nat = Some [Z_to_bv 8 (flag c i)] /\ (0 <= flag c i < 256)%Z.
  Hypothesis HCL : forall M', (forall x : word, gc_outz (t - 160) t fs (bv_unsigned x) -> M' x = mem0 x) ->
    rdn ASEGS M' (Z_to_bv 64 (fs + 88)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 20))
    /\ rt_layout_globs M'
    /\ (forall c i, gc_valid c i -> flag c i <> 0%Z ->
          rdn ASEGS M' (Z_to_bv 64 (gc_fr fs c i + 24)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (rs c i))) /\ (0 <= rs c i < 2 ^ 64)%Z).
  Hypothesis HFR : rdn ASEGS Mfr (Z_to_bv 64 (t - 120)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x140928))
                /\ rdn ASEGS Mfr (Z_to_bv 64 (t - 128)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x140930))
                /\ rdn ASEGS Mfr (Z_to_bv 64 (t - 136)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x140920)).
  Hypothesis Hcol6 : forall c i, gc_valid c i -> gc_col sparg bot flag rs c i -> (c <= 6)%Z.
  Hypothesis Hshok : forall c i, gc_valid c i -> gc_col sparg bot flag rs c i ->
    store_ok ASEGS mem0 (Z_to_bv 64 (gc_sh fs c i)) (Z.to_nat (2 ^ (3 + c))) = true.

  #[local] Abbreviation col := (gc_col sparg bot flag rs).
  #[local] Abbreviation GCM := (gcm mem0 (t - 160) t fs col).


  (* [comment removed for export] *)
  Definition frm (M : word -> option byte) : Prop :=
    forall x : word, (t - 160 <= bv_unsigned x < t)%Z -> ~ (t - 112 <= bv_unsigned x < t - 104)%Z -> M x = Mfr x.

  Definition gi2_inv (rg : bvmap 5 word) (i : Z) : Prop :=
    getr rg 27 = Z_to_bv 64 i /\ getr rg 24 = Z_to_bv 64 flb /\ getr rg 25 = Z_to_bv 64 fs /\ getr rg 20 = Z_to_bv 64 c
    /\ getr rg 7 = Z_to_bv 64 1 /\ getr rg 8 = Z_to_bv 64 (fs + 4096) /\ getr rg 21 = Z_to_bv 64 (6 + c) /\ getr rg 18 = Z_to_bv 64 bot
    /\ getr rg 9 = Z_to_bv 64 sparg /\ getr rg 19 = Z_to_bv 64 nlog
    /\ getr rg 26 = Z_to_bv 64 0 /\ getr rg 22 = Z_to_bv 64 0x13fc38 /\ getr rg 23 = Z_to_bv 64 g35 /\ getr rg 28 = Z_to_bv 64 6
    /\ getr rg 2 = Z_to_bv 64 (t - 144).
  (* [comment removed for export] *)
  Definition gs_keeps (regs regs' : bvmap 5 word) : Prop :=
    forall r : reg, r <> 5%bv -> r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv -> r <> 15%bv -> r <> 16%bv -> r <> 17%bv -> getr regs' r = getr regs r.
  #[using="Type"] Lemma gi2_keeps : forall regs regs' i, gi2_inv regs i -> gs_keeps regs regs' -> gi2_inv regs' i.
  Proof.
    intros regs regs' i (H27 & H24 & H25 & H20 & H7 & H8 & H21 & H18 & H9 & H19 & H26 & H22 & H23 & H28 & H2) K. unfold gi2_inv.
    rewrite !K by (intros E; discriminate E). repeat split; assumption.
  Qed.
  #[using="Type"] Lemma gs_keeps_trans : forall r1 r2 r3, gs_keeps r1 r2 -> gs_keeps r2 r3 -> gs_keeps r1 r3.
  Proof. intros r1 r2 r3 K1 K2 r; intros. rewrite K2 by assumption. apply K1; assumption. Qed.

  #[local] Ltac kp9 := intros r; intros; repeat (rewrite getr_other; [| intros ->; match goal with Hn : ?a <> ?a |- _ => exact (Hn eq_refl) end]); reflexivity.

  #[using="frsz Hc Hnlog Hnfr Hfrsz Hflb Ht Hfs Happ Hshz Hsp Hwfs HF0 HCL HFR Hcol6 Hshok"] Lemma gcc_slot_run : forall regs M i,
    gi2_inv regs i -> (0 <= i < nfr)%Z -> GCM (gc_done_lt c i) M -> frm M ->
    exists regs' M',
      msteps ASEGS (mkst regs (0x5d914 : word) M rom) (mkst regs' (0x5d908 : word) M' rom)
      /\ gs_keeps regs regs' /\ GCM (gc_done_lt c (i + 1)) M' /\ frm M'.
  Proof.
    intros regs M i INV Hi GM FRM.
    pose proof INV as (H27 & H24 & H25 & H20 & H7 & H8 & H21 & H18 & H9 & H19 & H26 & H22 & H23 & H28 & H2).
    pose proof (gc_kit t fs Hfs Happ) as (K1 & K2 & K3 & K4).
    destruct Hfs as (Fs1 & Fs2 & Fs3). destruct Hsp as [Sp1 Sp2]. destruct Ht as [Ta Tb].
    pose proof (gc_pow_facts c Hc) as (P1 & P2 & P3 & P4 & P5).
    assert (V : gc_valid c i) by (split; [exact Hc | rewrite <- Hnlog, <- Hnfr; exact Hi]).
    assert (Efl : (flb + i)%Z = gc_fl fs c i) by (unfold gc_fl; rewrite Hflb, Hnfr, Hnlog; reflexivity).
    assert (Eff : (fs + 4096 + 32768 + c * 2 ^ 20 + i * frsz)%Z = gc_fr fs c i) by (unfold gc_fr; rewrite Hfrsz; reflexivity).
    pose proof (gc_fl_range fs c i V) as FLR. pose proof (gc_fr_range fs c i V) as [FRR1 FRR2]. pose proof (gc_sh_range fs c i V) as [SHR1 SHR2].
    assert (Nfr : (16 <= nfr <= 16384)%Z) by (rewrite Hnfr, Hnlog; exact P1).
    assert (Fb : (64 <= frsz <= 65536)%Z) by (rewrite Hfrsz; exact P2).
    assert (Nl : (0 <= nlog <= 14)%Z) by lia.
    destruct (HF0 c i V) as [Fi0 Bi].
    (* [comment removed for export] *)
    assert (Fi : rdn ASEGS M (Z_to_bv 64 (flb + i)) 1%nat = Some [Z_to_bv 8 (flag c i)]).
    { rewrite Efl, <- Fi0. apply rdn_ext; [rewrite u64_lit by lia; cbn [Z.of_nat Pos.to_nat]; lia|].
      intros x Hx. rewrite u64_lit in Hx by lia. cbn [Z.of_nat Pos.to_nat] in Hx.
      rewrite (word_of_u x (gc_fl fs c i)) by lia.
      eapply (gcm_flag mem0 (t - 160) t fs col K1 K3 K4); [exact GM | exact V | unfold gc_done_lt; lia]. }
    assert (OUTZ : forall x : word, gc_outz (t - 160) t fs (bv_unsigned x) -> M x = mem0 x).
    { intros x (O1 & O2 & O3). exact (gcm_out mem0 (t - 160) t fs col K3 _ M GM x O1 O2 O3). }
    destruct (HCL M OUTZ) as (HL & HGL & HRS).
    assert (EDONE : forall c' i', gc_valid c' i' -> (gc_done_lt c (i + 1) c' i' <-> gc_done_lt c i c' i' \/ (c' = c /\ i' = i))).
    { intros c' i' _. unfold gc_done_lt. lia. }
    destruct (Z.eq_dec (flag c i) 0) as [F0|F1].
    { (* [comment removed for export] *)
      exists (regupd (regupd regs 11 (Z_to_bv 64 (flb + i))) 10 (Z_to_bv 64 0)), M. split; [|split; [kp9 | split; [|exact FRM]]].
      - stepiv F_5d4fc D_5d4fc (Z_to_bv 64 (flb + i)) ltac:(wval).                                   (* [comment removed for export] *)
        chain_step; [reflexivity | eapply step_lbu; [exact F_5d500 | reflexivity | exact D_5d500 | maddr (flb + i)%Z; exact Fi] | step_simpl; vnorm].   (* [comment removed for export] *)
        stepb_tk F_5d504 D_5d504 ltac:(rewrite (u_Z2bv8 (flag c i)) by lia; cond).                    (* [comment removed for export] *)
        rewrite F0. apply mst_refl.
      - apply (gcm_skip mem0 (t - 160) t fs col (gc_done_lt c i) _ M c i); [|exact EDONE | exact GM].
        intros (NZ & _). contradiction. }
    destruct (HRS c i V F1) as (Ri0 & Bri).
    assert (Ri : rdn ASEGS M (Z_to_bv 64 (fs + 4096 + 32768 + c * 2 ^ 20 + i * frsz + 24)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (rs c i))))
      by (rewrite Eff; exact Ri0).
    (* [comment removed for export] *)
    #[local] Ltac runB Fi HL Ri flb i fs c frsz Hfrsz flagci :=
      stepiv F_5d4fc D_5d4fc (Z_to_bv 64 (flb + i)) ltac:(wval);
      (chain_step; [reflexivity | eapply step_lbu; [exact F_5d500 | reflexivity | exact D_5d500 | maddr (flb + i)%Z; exact Fi] | step_simpl; vnorm]);
      stepb_ft F_5d504 D_5d504 ltac:(rewrite (u_Z2bv8 flagci) by lia; cond);
      mldq F_5d508 D_5d508 (fs + 88)%Z HL;
      stepn F_5d50c D_5d50c;
      stepsv F_5d510 D_5d510 (Z_to_bv 64 (c * 2 ^ 20)) ltac:(gres; rwH; apply v_sll_lit; lia);
      stepn F_5d514 D_5d514;
      stepiv F_5d518 D_5d518 (Z_to_bv 64 (fs + 4096 + c * 2 ^ 20)) ltac:(wval);
      stepiv F_5d51c D_5d51c (Z_to_bv 64 (fs + 4096 + c * 2 ^ 20 + 32768)) ltac:(wval);
      stepsv F_5d520 D_5d520 (Z_to_bv 64 (i * frsz)) ltac:(gres; rwH; rewrite v_sll_lit by lia; rewrite <- Hfrsz; reflexivity);
      stepiv F_5d524 D_5d524 (Z_to_bv 64 (fs + 4096 + 32768 + c * 2 ^ 20 + i * frsz)) ltac:(gres; rwH; unfold v_add; unorm; f_equal; nia);
      mldq F_5d528 D_5d528 (fs + 4096 + 32768 + c * 2 ^ 20 + i * frsz + 24)%Z Ri.
    destruct (Z.le_gt_cases (rs c i) bot) as [LE|GT].
    { (* [comment removed for export] *)
      eexists. exists M. split; [|split; [|split; [|exact FRM]]].
      - runB Fi HL Ri flb i fs c frsz Hfrsz (flag c i).
        stepb_tk F_5d52c D_5d52c ltac:(cond).                                                         (* [comment removed for export] *)
        apply mst_refl.
      - kp9.
      - apply (gcm_skip mem0 (t - 160) t fs col (gc_done_lt c i) _ M c i); [|exact EDONE | exact GM].
        intros (_ & NC). lia. }
    destruct (Z.le_gt_cases sparg (rs c i)) as [GE|LT].
    { (* [comment removed for export] *)
      eexists. exists M. split; [|split; [|split; [|exact FRM]]].
      - runB Fi HL Ri flb i fs c frsz Hfrsz (flag c i).
        stepb_ft F_5d52c D_5d52c ltac:(cond).                                                         (* [comment removed for export] *)
        stepb_tk F_5d530 D_5d530 ltac:(cond).                                                         (* [comment removed for export] *)
        apply mst_refl.
      - kp9.
      - apply (gcm_skip mem0 (t - 160) t fs col (gc_done_lt c i) _ M c i); [|exact EDONE | exact GM].
        intros (_ & NC). lia. }
    (* [comment removed for export] *)
    assert (COL : col c i) by (split; [exact F1 | lia]).
    pose proof (Hcol6 c i V COL) as C6. pose proof (Hshok c i V COL) as SHOK.
    destruct GM as (GMG & GMO & GMP).
    set (M1 := wbytes M (Z_to_bv 64 (gc_fl fs c i)) [Z_to_bv 8 0]).
    assert (G1 : mem_grows mem0 M1) by (unfold M1; eapply mem_grows_trans; [exact GMG | apply wbytes_grows]).
    assert (OUTZ1 : forall x : word, gc_outz (t - 160) t fs (bv_unsigned x) -> M1 x = mem0 x).
    { intros x OZ. pose proof OZ as (O1 & O2 & O3). unfold M1. rewrite wbytes_outside; [apply OUTZ; exact OZ | |]; cbn [length Z.of_nat Pos.to_nat]; rewrite u64_lit by (clear - Bi F1 FLR Fb Fs1 Fs2 Fs3 Happ Hc Hfrsz Hfs Hshz K3 K4 Nl O1 O3 P5 SHR1 SHR2 Ta c flag frsz fs i nlog t x; lia); lia. }
    destruct (HCL M1 OUTZ1) as (_ & (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8) & _). unfold SB in Y2. unfold HIGHEND in Y8.
    assert (FR1 : forall a, (t - 160 <= a)%Z -> (a + 8 <= t)%Z -> (a + 8 <= t - 112 \/ t - 104 <= a)%Z ->
              rdn ASEGS M1 (Z_to_bv 64 a) 8%nat = rdn ASEGS Mfr (Z_to_bv 64 a) 8%nat).
    { intros a A1 A2 A3. apply rdn_ext; [rewrite u64_lit by lia; cbn [Z.of_nat Pos.to_nat]; lia|].
      intros x Hx. rewrite u64_lit in Hx by lia. cbn [Z.of_nat Pos.to_nat] in Hx.
      unfold M1. rewrite wbytes_outside; [apply FRM; lia | |]; cbn [length Z.of_nat Pos.to_nat]; rewrite u64_lit by lia; lia. }
    destruct HFR as (HFR1 & HFR2 & HFR3).
    rewrite <- (FR1 (t - 120)%Z) in HFR1 by lia. rewrite <- (FR1 (t - 128)%Z) in HFR2 by lia. rewrite <- (FR1 (t - 136)%Z) in HFR3 by lia.
    assert (WFL : store_ok ASEGS M (Z_to_bv 64 (flb + i)) 1%nat = true).
    { apply (store_ok_mono _ _ mem0 M _ GMG).
      apply (store_ok_sub ASEGS mem0 (Z_to_bv 64 fs) _ (Z.to_nat (4096 + 32768 + 11 * 2 ^ 20))); [rewrite u64_lit by lia; lia | exact Hwfs | rewrite !u64_lit by lia; lia | rewrite !u64_lit by lia; cbn [Z.of_nat Pos.to_nat]; lia]. }
    assert (Esh : gc_sh fs c i = (2147450880 + gc_fr fs c i / 8)%Z) by reflexivity.
    assert (E8 : (8 * 2 ^ c = 2 ^ (3 + c))%Z) by (rewrite Z.pow_add_r by lia; reflexivity).
    assert (INAPP : in_app (gc_fr fs c i)) by (apply gc_fr_in_app; assumption).
    assert (PRE : exists r1, msteps ASEGS (mkst regs (0x5d914 : word) M rom) (mkst r1 (0x5d9ac : word) M1 rom)
              /\ ss_inv c (gc_sh fs c i) g35 r1 0 /\ gs_keeps regs r1).
    { unfold in_app, LOWEND, HIGHBEG, HIGHEND in INAPP. destruct INAPP as [LOW|HIGH].
      - eexists. split; [|split].
        + runB Fi HL Ri flb i fs c frsz Hfrsz (flag c i).
          stepb_ft F_5d52c D_5d52c ltac:(cond).
          stepb_ft F_5d530 D_5d530 ltac:(cond).                                                       (* [comment removed for export] *)
          chain_step; [reflexivity | eapply (step_sb_at ASEGS) with (a := Z_to_bv 64 (flb + i)) (b := Z_to_bv 8 0);
              [exact F_5d534 | reflexivity | exact D_5d534 | wval | gres; rwH; reflexivity | apply bv_eq; vm_compute; reflexivity | exact WFL ] | step_simpl; vnorm].   (* [comment removed for export] *)
          rewrite Efl. change (wbytes M (Z_to_bv 64 (gc_fl fs c i)) [Z_to_bv 8 0]) with M1.
          mld F_5d538 D_5d538 (0x13fc38 : word) Y2.                                                     (* [comment removed for export] *)
          stepn F_5d53c D_5d53c.                                                                      (* [comment removed for export] *)
          stepn F_5d540 D_5d540.                                                                      (* [comment removed for export] *)
          stepn F_5d544 D_5d544.                                                                      (* [comment removed for export] *)
          stepn F_5d548 D_5d548.                                                                      (* [comment removed for export] *)
          stepb_tk F_5d54c D_5d54c ltac:(rewrite Eff; cond).                                          (* [comment removed for export] *)
          stepb_ft F_5d584 D_5d584 ltac:(cond).                                                       (* [comment removed for export] *)
          stepiv F_5d588 D_5d588 (Z_to_bv 64 (gc_fr fs c i / 8)) ltac:(rewrite Eff; wval).            (* [comment removed for export] *)
          stepiv F_5d58c D_5d58c (Z_to_bv 64 (gc_sh fs c i + 8 * 0)) ltac:(rewrite Esh; wval).        (* [comment removed for export] *)
          stepn F_5d590 D_5d590.                                                                      (* [comment removed for export] *)
          apply mst_refl.
        + unfold ss_inv. post.
        + kp9.
      - eexists. split; [|split].
        + runB Fi HL Ri flb i fs c frsz Hfrsz (flag c i).
          stepb_ft F_5d52c D_5d52c ltac:(cond).
          stepb_ft F_5d530 D_5d530 ltac:(cond).                                                       (* [comment removed for export] *)
          chain_step; [reflexivity | eapply (step_sb_at ASEGS) with (a := Z_to_bv 64 (flb + i)) (b := Z_to_bv 8 0);
              [exact F_5d534 | reflexivity | exact D_5d534 | wval | gres; rwH; reflexivity | apply bv_eq; vm_compute; reflexivity | exact WFL ] | step_simpl; vnorm].   (* [comment removed for export] *)
          rewrite Efl. change (wbytes M (Z_to_bv 64 (gc_fl fs c i)) [Z_to_bv 8 0]) with M1.
          mld F_5d538 D_5d538 (0x13fc38 : word) Y2.                                                     (* [comment removed for export] *)
          stepn F_5d53c D_5d53c.
          stepn F_5d540 D_5d540.
          stepn F_5d544 D_5d544.
          stepn F_5d548 D_5d548.
          stepb_ft F_5d54c D_5d54c ltac:(rewrite Eff; cond).                                          (* [comment removed for export] *)
          mldq F_5d550 D_5d550 (t - 120)%Z HFR1.                                                       (* [comment removed for export] *)
          mld F_5d554 D_5d554 (0x140928 : word) Y4.                                                     (* [comment removed for export] *)
          mldq F_5d558 D_5d558 (t - 128)%Z HFR2.                                                       (* [comment removed for export] *)
          mld F_5d55c D_5d55c (0x140930 : word) Y6.                                                     (* [comment removed for export] *)
          stepn F_5d560 D_5d560.                                                                      (* [comment removed for export] *)
          stepb_tk F_5d564 D_5d564 ltac:(rewrite Eff; cond).                                          (* [comment removed for export] *)
          mldq F_5d56c D_5d56c (t - 136)%Z HFR3.                                                       (* [comment removed for export] *)
          mld F_5d570 D_5d570 (0x140920 : word) Y8.                                                     (* [comment removed for export] *)
          stepn F_5d574 D_5d574.                                                                      (* [comment removed for export] *)
          stepn F_5d578 D_5d578.                                                                      (* [comment removed for export] *)
          stepb_ft F_5d57c D_5d57c ltac:(rewrite Eff; cond).                                          (* [comment removed for export] *)
          stepb_ft F_5d580 D_5d580 ltac:(rewrite Eff; cond).                                          (* [comment removed for export] *)
          stepb_ft F_5d584 D_5d584 ltac:(cond).                                                       (* [comment removed for export] *)
          stepiv F_5d588 D_5d588 (Z_to_bv 64 (gc_fr fs c i / 8)) ltac:(rewrite Eff; wval).            (* [comment removed for export] *)
          stepiv F_5d58c D_5d58c (Z_to_bv 64 (gc_sh fs c i + 8 * 0)) ltac:(rewrite Esh; wval).        (* [comment removed for export] *)
          stepn F_5d590 D_5d590.                                                                      (* [comment removed for export] *)
          apply mst_refl.
        + unfold ss_inv. post.
        + kp9. }
    destruct PRE as (r1 & RUN1 & SI & KP1).
    destruct K2 as [K2a K2b].
    assert (SHOK1 : store_ok ASEGS M1 (Z_to_bv 64 (gc_sh fs c i)) (Z.to_nat (8 * 2 ^ c)) = true)
      by (rewrite E8; apply (store_ok_mono _ _ mem0 M1 _ G1); exact SHOK).
    assert (Pc : (1 <= 2 ^ c)%Z) by (change 1%Z with (2 ^ 0)%Z; apply Z.pow_le_mono_r; lia).
    destruct (gc_setshadow_loop M1 rom c (gc_sh fs c i) g35 ltac:(lia) ltac:(split; lia) SHOK1 (Z.to_nat (2 ^ c - 1)) r1 0%Z SI ltac:(lia) ltac:(lia))
      as (r2 & RUN2 & KP2).
    change (ssm M1 (gc_sh fs c i) g35 0) with M1 in RUN2.
    exists r2, (ssm M1 (gc_sh fs c i) g35 (2 ^ c)). split; [eapply msteps_trans; [exact RUN1 | exact RUN2]|]. split; [|split].
    - intros r; intros. rewrite KP2 by assumption. apply KP1; assumption.
    - assert (LN : Z.of_nat (length (concat (repeat (word_to_le_bytes 8 (Z_to_bv 64 g35)) (Z.to_nat (2 ^ c))))) = (2 ^ (3 + c))%Z)
        by (rewrite len_concat_le8, Z2Nat.id by lia; exact E8).
      unfold ssm, M1.
      apply (gcm_collect mem0 (t - 160) t fs col K1 (conj K2a K2b) K3 (gc_done_lt c i) _ M c i _ V COL LN EDONE). split; [exact GMG | split; [exact GMO | exact GMP]].
    - assert (LN : Z.of_nat (length (concat (repeat (word_to_le_bytes 8 (Z_to_bv 64 g35)) (Z.to_nat (2 ^ c))))) = (2 ^ (3 + c))%Z)
        by (rewrite len_concat_le8, Z2Nat.id by lia; exact E8).
      intros x Hx1 Hx2. unfold ssm, M1.
      rewrite wbytes_outside; [rewrite wbytes_outside; [apply FRM; assumption | |] | |];
        rewrite ?LN; cbn [length Z.of_nat Pos.to_nat]; rewrite u64_lit by lia; lia.
  Qed.

  (* [comment removed for export] *)
  Definition gi_keeps2 (regs regs' : bvmap 5 word) : Prop :=
    forall r : reg, r <> 5%bv -> r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv -> r <> 15%bv -> r <> 16%bv -> r <> 17%bv -> r <> 27%bv ->
      getr regs' r = getr regs r.
  #[local] Ltac kp10 := intros r; intros; repeat (rewrite getr_other; [| intros ->; match goal with Hn : ?a <> ?a |- _ => exact (Hn eq_refl) end]); reflexivity.

  #[using="frsz Hc Hnlog Hnfr Hfrsz Hflb Ht Hfs Happ Hshz Hsp Hwfs HF0 HCL HFR Hcol6 Hshok"] Lemma gcc_inner_run : forall (q : nat) regs M i,
    gi2_inv regs i -> (0 <= i)%Z -> (i + Z.of_nat q + 1 = nfr)%Z -> GCM (gc_done_lt c i) M -> frm M ->
    exists regs' M',
      msteps ASEGS (mkst regs (0x5d914 : word) M rom) (mkst regs' (0x5d8a4 : word) M' rom)
      /\ gi2_inv regs' nfr /\ gi_keeps2 regs regs' /\ GCM (gc_done_lt c nfr) M' /\ frm M'.
  Proof.
    induction q as [|q IH]; intros regs M i INV Hi Hq GM FRM;
      pose proof (gc_pow_facts c Hc) as (P1 & _);
      assert (Nfr : (16 <= nfr <= 16384)%Z) by (rewrite Hnfr, Hnlog; exact P1);
      assert (Nl : (0 <= nlog <= 14)%Z) by lia;
      destruct (gcc_slot_run regs M i INV ltac:(lia) GM FRM) as (r1 & M1 & RUN1 & KP1 & GM1 & FRM1);
      pose proof (gi2_keeps regs r1 i INV KP1) as (H27 & H24 & H25 & H20 & H7 & H8 & H21 & H18 & H9 & H19 & H26 & H22 & H23 & H28 & H2).
    - (* [comment removed for export] *)
      assert (Hdiv : ((i + 1) / 2 ^ nlog = 1)%Z) by (rewrite <- Hnfr; replace (i + 1)%Z with nfr by lia; apply Z.div_same; lia).
      assert (TAIL : exists r2, msteps ASEGS (mkst r1 (0x5d908 : word) M1 rom) (mkst r2 (0x5d8a4 : word) M1 rom) /\ gi2_inv r2 nfr /\ gi_keeps2 r1 r2).
      { eexists. split; [|split].
        - stepiv F_5d4f0 D_5d4f0 (Z_to_bv 64 (i + 1)) ltac:(wval).                                    (* [comment removed for export] *)
          stepsv F_5d4f4 D_5d4f4 (Z_to_bv 64 1) ltac:(gres; rwH; rewrite v_srl_lit by lia; rewrite Hdiv; reflexivity).   (* [comment removed for export] *)
          stepb_tk F_5d4f8 D_5d4f8 ltac:(cond).                                                        (* [comment removed for export] *)
          apply mst_refl.
        - unfold gi2_inv. post.
        - kp10. }
      destruct TAIL as (r2 & RUN2 & INV2 & KP2).
      exists r2, M1. split; [eapply msteps_trans; [exact RUN1 | exact RUN2]|]. split; [exact INV2|]. split; [|split; [|exact FRM1]].
      + intros r; intros. rewrite KP2 by assumption. apply KP1; assumption.
      + replace nfr with (i + 1)%Z by lia. exact GM1.
    - assert (Hdiv : ((i + 1) / 2 ^ nlog = 0)%Z) by (apply Z.div_small; rewrite <- Hnfr; lia).
      assert (TAIL : exists r2, msteps ASEGS (mkst r1 (0x5d908 : word) M1 rom) (mkst r2 (0x5d914 : word) M1 rom) /\ gi2_inv r2 (i + 1) /\ gi_keeps2 r1 r2).
      { eexists. split; [|split].
        - stepiv F_5d4f0 D_5d4f0 (Z_to_bv 64 (i + 1)) ltac:(wval).
          stepsv F_5d4f4 D_5d4f4 (Z_to_bv 64 0) ltac:(gres; rwH; rewrite v_srl_lit by lia; rewrite Hdiv; reflexivity).
          stepb_ft F_5d4f8 D_5d4f8 ltac:(cond).                                                        (* [comment removed for export] *)
          apply mst_refl.
        - unfold gi2_inv. post.
        - kp10. }
      destruct TAIL as (r2 & RUN2 & INV2 & KP2).
      destruct (IH r2 M1 (i + 1)%Z INV2 ltac:(lia) ltac:(lia) GM1 FRM1) as (r3 & M3 & RUN3 & INV3 & KP3 & GM3 & FRM3).
      exists r3, M3. split; [eapply msteps_trans; [exact RUN1|]; eapply msteps_trans; [exact RUN2 | exact RUN3]|].
      split; [exact INV3|]. split; [|split; [exact GM3 | exact FRM3]].
      intros r; intros. rewrite KP3 by assumption. rewrite KP2 by assumption. apply KP1; assumption.
  Qed.
End SLOT.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CLASS.
  Variables mem0 Mfr : word -> option byte.
  Variable rom : word -> option byte.
  Variables t fs sparg bot g35 : Z.
  Variables flag rs : Z -> Z -> Z.
  Hypothesis Ht : (0x1000000 <= t - 160)%Z /\ (t < 2 ^ 64)%Z.
  Hypothesis Hfs : (0x696000 <= fs)%Z /\ (fs + 4096 + 32768 + 11 * 2 ^ 20 < 2 ^ 47)%Z /\ (fs + 4096 + 32768 + 11 * 2 ^ 20 <= t - 160 \/ t <= fs)%Z.
  Hypothesis Happ : (fs + 4096 + 32768 + 11 * 2 ^ 20 <= 0x7fff7000 \/ 0x10007fff8000 <= fs)%Z.
  Hypothesis Hshz : (gc_shz_hi fs <= t - 160 \/ t <= gc_shz_lo fs)%Z.
  Hypothesis Hsp : (0 <= sparg < 2 ^ 64)%Z /\ (0 <= bot < 2 ^ 64)%Z.
  Hypothesis Hok : store_ok ASEGS mem0 (Z_to_bv 64 (t - 160)) 160%nat = true.
  Hypothesis Hwfs : store_ok ASEGS mem0 (Z_to_bv 64 fs) (Z.to_nat (4096 + 32768 + 11 * 2 ^ 20)) = true.
  Hypothesis HF0 : forall c i, gc_valid c i ->
    rdn ASEGS mem0 (Z_to_bv 64 (gc_fl fs c i)) 1%nat = Some [Z_to_bv 8 (flag c i)] /\ (0 <= flag c i < 256)%Z.
  Hypothesis HCL : forall M', (forall x : word, gc_outz (t - 160) t fs (bv_unsigned x) -> M' x = mem0 x) ->
    rdn ASEGS M' (Z_to_bv 64 (fs + 88)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 20))
    /\ rt_layout_globs M'
    /\ (forall c i, gc_valid c i -> flag c i <> 0%Z ->
          rdn ASEGS M' (Z_to_bv 64 (gc_fr fs c i + 24)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (rs c i))) /\ (0 <= rs c i < 2 ^ 64)%Z).
  Hypothesis HFR : rdn ASEGS Mfr (Z_to_bv 64 (t - 120)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x140928))
                /\ rdn ASEGS Mfr (Z_to_bv 64 (t - 128)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x140930))
                /\ rdn ASEGS Mfr (Z_to_bv 64 (t - 136)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x140920)).
  Hypothesis Hcol6 : forall c i, gc_valid c i -> gc_col sparg bot flag rs c i -> (c <= 6)%Z.
  Hypothesis Hshok : forall c i, gc_valid c i -> gc_col sparg bot flag rs c i ->
    store_ok ASEGS mem0 (Z_to_bv 64 (gc_sh fs c i)) (Z.to_nat (2 ^ (3 + c))) = true.

  #[local] Abbreviation col := (gc_col sparg bot flag rs).
  #[local] Abbreviation GCM := (gcm mem0 (t - 160) t fs col).
  #[local] Abbreviation FRM := (frm Mfr t).

  Definition gcl2_inv (rg : bvmap 5 word) (c : Z) : Prop :=
    getr rg 20 = Z_to_bv 64 c /\ getr rg 25 = Z_to_bv 64 fs /\ getr rg 7 = Z_to_bv 64 1 /\ getr rg 8 = Z_to_bv 64 (fs + 4096)
    /\ getr rg 18 = Z_to_bv 64 bot /\ getr rg 9 = Z_to_bv 64 sparg /\ getr rg 2 = Z_to_bv 64 (t - 144)
    /\ getr rg 26 = Z_to_bv 64 0 /\ getr rg 22 = Z_to_bv 64 0x13fc38 /\ getr rg 23 = Z_to_bv 64 g35 /\ getr rg 28 = Z_to_bv 64 6.
  Definition gcl_keeps2 (regs regs' : bvmap 5 word) : Prop :=
    forall r : reg, r <> 5%bv -> r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv -> r <> 15%bv -> r <> 16%bv -> r <> 17%bv -> r <> 27%bv ->
      r <> 21%bv -> r <> 24%bv -> r <> 19%bv -> r <> 20%bv -> getr regs' r = getr regs r.

  #[local] Ltac kp14 := intros r; intros; repeat (rewrite getr_other; [| intros ->; match goal with Hn : ?a <> ?a |- _ => exact (Hn eq_refl) end]); reflexivity.

  #[using="Ht Hfs Happ Hshz Hsp Hok Hwfs HF0 HCL HFR Hcol6 Hshok"] Lemma gcc_class_run : forall regs M c,
    gcl2_inv regs c -> (0 <= c <= 10)%Z -> GCM (gc_done_lt c 0) M -> FRM M ->
    exists regs' M',
      msteps ASEGS (mkst regs (0x5d8b0 : word) M rom) (mkst regs' (0x5d8a4 : word) M' rom)
      /\ gcl2_inv regs' c /\ gcl_keeps2 regs regs' /\ GCM (gc_done_lt (c + 1) 0) M' /\ FRM M'.
  Proof.
    intros regs M c (H20 & H25 & H7 & H8 & H18 & H9 & H2 & H26 & H22 & H23 & H28) Hc GM FR.
    destruct (gc_facts_all c Hc) as (nfr & frsz & k1 & (Fn & Ff & Ff2 & Fk & Fk1 & Fand)).
    pose proof (gc_pow_facts c Hc) as (P1 & P2 & _).
    assert (Nb : (16 <= nfr <= 16384)%Z) by (rewrite Fn; exact P1).
    assert (Fb : (64 <= frsz <= 65536)%Z) by (rewrite Ff; exact P2).
    pose proof (gc_kit t fs Hfs Happ) as (K1 & K2 & K3 & K4).
    destruct Hfs as (Fs1 & Fs2 & Fs3). destruct Ht as [Ta Tb]. destruct Hsp as [Sp1 Sp2].
    assert (OUTZ : forall x : word, gc_outz (t - 160) t fs (bv_unsigned x) -> M x = mem0 x).
    { intros x (O1 & O2 & O3). exact (gcm_out mem0 (t - 160) t fs col K3 _ M GM x O1 O2 O3). }
    destruct (HCL M OUTZ) as (CL & _).
    pose proof GM as (GMG & _).
    set (M' := wbytes M (Z_to_bv 64 (t - 112)) (word_to_le_bytes 8 (Z_to_bv 64 frsz))).
    assert (OM' : forall x : word, ~ (t - 112 <= bv_unsigned x < t - 104)%Z -> M' x = M x).
    { intros x Hx. unfold M'. apply wbytes_outside; rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; rewrite u64_lit by lia; lia. }
    assert (GM' : GCM (gc_done_lt c 0) M').
    { apply (gcm_frame mem0 (t - 160) t fs col K1 K4 _ M M' GM); [unfold M'; apply wbytes_grows|]. intros x Hx. apply OM'. lia. }
    assert (FR' : FRM M') by (intros x Hx1 Hx2; rewrite OM' by exact Hx2; apply FR; assumption).
    assert (exists flb, flb = fs + 4096 + 32768 - 2 * nfr)%Z as (flb & Hflb) by (eexists; reflexivity).
    (* [comment removed for export] *)
    assert (S1 : exists r1, msteps ASEGS (mkst regs (0x5d8b0 : word) M rom) (mkst r1 (0x5d914 : word) M' rom)
              /\ gi2_inv t fs c (14 - c) flb sparg bot g35 r1 0 /\ gcl_keeps2 regs r1).
    { eexists. split; [|split].
      - stepn F_5d498 D_5d498.                                                                            (* [comment removed for export] *)
        mldq F_5d49c D_5d49c (fs + 88)%Z CL.                                                               (* [comment removed for export] *)
        stepn F_5d4a0 D_5d4a0.                                                                            (* [comment removed for export] *)
        stepsv F_5d4a4 D_5d4a4 (Z_to_bv 64 (10 - c)) ltac:(gres; rwH; unfold v_subw; unorm; rewrite swrap32_small by lia; reflexivity).   (* [comment removed for export] *)
        stepiv F_5d4a8 D_5d4a8 (Z_to_bv 64 (6 + c)) ltac:(wval).                                         (* [comment removed for export] *)
        stepiv F_5d4ac D_5d4ac (Z_to_bv 64 18446744073709551615) ltac:(gres; apply bv_eq; vm_compute; reflexivity).   (* [comment removed for export] *)
        stepsv F_5d4b0 D_5d4b0 (Z_to_bv 64 (18446744073709551615 * 2 ^ (10 - c))) ltac:(gres; rwH; apply v_sll_lit; lia).   (* [comment removed for export] *)
        stepiv F_5d4b4 D_5d4b4 (Z_to_bv 64 k1) ltac:(gres; rwH; unfold v_andi; change (bv_wrap 64 1023) with 1023%Z; exact Fand).   (* [comment removed for export] *)
        stepn F_5d4b8 D_5d4b8.                                                                            (* [comment removed for export] *)
        stepiv F_5d4bc D_5d4bc (Z_to_bv 64 (20 - c)) ltac:(wval).                                        (* [comment removed for export] *)
        stepsv F_5d4c0 D_5d4c0 (Z_to_bv 64 (32 * k1)) ltac:(gres; rwH; rewrite v_sll_lit by lia; change (2 ^ 5)%Z with 32%Z; f_equal; lia).   (* [comment removed for export] *)
        stepiv F_5d4c4 D_5d4c4 (Z_to_bv 64 (14 - c)) ltac:(wval).                                        (* [comment removed for export] *)
        stepiv F_5d4c8 D_5d4c8 (Z_to_bv 64 flb) ltac:(wval).                                             (* [comment removed for export] *)
        stepn F_5d4cc D_5d4cc.                                                                            (* [comment removed for export] *)
        stepsv F_5d4d0 D_5d4d0 (Z_to_bv 64 frsz) ltac:(gres; rwH; rewrite v_sll_lit by lia; rewrite Ff2; reflexivity).   (* [comment removed for export] *)
        stepsdq F_5d4d4 D_5d4d4 (Z_to_bv 64 (t - 112)) (Z_to_bv 64 frsz)
          ltac:(apply (store_ok_mono _ _ mem0); [exact GMG|];
                apply (store_ok_sub ASEGS mem0 (Z_to_bv 64 (t - 160)) _ 160%nat); [unorm; cbn; lia | exact Hok | unorm; lia | unorm; cbn; lia]).   (* [comment removed for export] *)
        change (wbytes M (Z_to_bv 64 (t - 112)) (word_to_le_bytes 8 (Z_to_bv 64 frsz))) with M'.
        stepn F_5d4d8 D_5d4d8.                                                                            (* [comment removed for export] *)
        apply mst_refl.
      - unfold gi2_inv. post.
      - kp14. }
    destruct S1 as (r1 & RUN1 & I1 & KS1).
    (* [comment removed for export] *)
    destruct (gcc_inner_run mem0 Mfr rom t fs c nfr (14 - c) frsz flb sparg bot g35 flag rs Hc eq_refl Fn Ff Hflb (conj Ta Tb) (conj Fs1 (conj Fs2 Fs3)) Happ Hshz
                (conj Sp1 Sp2) Hwfs HF0 HCL HFR Hcol6 Hshok (Z.to_nat (nfr - 1)) r1 M' 0%Z I1 ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia) GM' FR')
      as (r2 & M2 & RUN2 & I2 & KS2 & GM2 & FR2).
    exists r2, M2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2]|]. split; [|split; [|split; [|exact FR2]]].
    - destruct I2 as (J27 & J24 & J25 & J20 & J7 & J8 & J21 & J18 & J9 & J19 & J26 & J22 & J23 & J28 & J2). unfold gcl2_inv. repeat split; assumption.
    - intros r; intros. rewrite KS2 by assumption. apply KS1; assumption.
    - apply (gcm_equiv mem0 (t - 160) t fs col (gc_done_lt c nfr) _ M2); [|exact GM2].
      intros c' i' [Vc Vi]. unfold gc_done_lt. rewrite Fn.
      assert (c' = c -> (i' < 2 ^ (14 - c))%Z) by (intros ->; lia). lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Ht Hfs Happ Hshz Hsp Hok Hwfs HF0 HCL HFR Hcol6 Hshok"] Lemma gcc_classes_run : forall (q : nat) regs M c,
    gcl2_inv regs c -> (0 <= c)%Z -> (c + Z.of_nat q = 10)%Z -> GCM (gc_done_lt c 0) M -> FRM M ->
    exists regs' M',
      msteps ASEGS (mkst regs (0x5d8b0 : word) M rom) (mkst regs' (0x5da88 : word) M' rom)
      /\ getr regs' 25 = Z_to_bv 64 fs /\ getr regs' 2 = Z_to_bv 64 (t - 144) /\ gcl_keeps2 regs regs' /\ GCM (gc_done_lt 11 0) M' /\ FRM M'.
  Proof.
    induction q as [|q IH]; intros regs M c HI Hc Hq GM FR;
      destruct (gcc_class_run regs M c HI ltac:(lia) GM FR) as (r1 & M1 & RUN1 & I1 & KC1 & GM1 & FR1);
      pose proof I1 as (H20 & H25 & H7 & H8 & H18 & H9 & H2 & H26 & H22 & H23 & H28).
    - eexists. exists M1. split; [|split; [|split; [|split; [|split; [|exact FR1]]]]].
      + eapply msteps_trans; [exact RUN1|].
        stepiv F_5d48c D_5d48c (Z_to_bv 64 11) ltac:(wval).                                            (* [comment removed for export] *)
        stepn F_5d490 D_5d490.                                                                          (* [comment removed for export] *)
        stepb_tk F_5d494 D_5d494 ltac:(cond).                                                           (* [comment removed for export] *)
        apply mst_refl.
      + gres. exact H25.
      + gres. exact H2.
      + unfold gcl_keeps2. intros r; intros. repeat (rewrite getr_other; [| intros ->; match goal with Hn : ?a <> ?a |- _ => exact (Hn eq_refl) end]).
        apply KC1; assumption.
      + replace 11%Z with (c + 1)%Z by lia. exact GM1.
    - assert (S2 : exists r2, msteps ASEGS (mkst r1 (0x5d8a4 : word) M1 rom) (mkst r2 (0x5d8b0 : word) M1 rom)
                /\ gcl2_inv r2 (c + 1) /\ gcl_keeps2 r1 r2).
      { eexists. split; [|split].
        - stepiv F_5d48c D_5d48c (Z_to_bv 64 (c + 1)) ltac:(wval).                                       (* [comment removed for export] *)
          stepn F_5d490 D_5d490.                                                                          (* [comment removed for export] *)
          stepb_ft F_5d494 D_5d494 ltac:(cond).                                                           (* [comment removed for export] *)
          apply mst_refl.
        - unfold gcl2_inv. post.
        - kp14. }
      destruct S2 as (r2 & RUN2 & I2 & KC2).
      destruct (IH r2 M1 (c + 1)%Z I2 ltac:(lia) ltac:(lia) GM1 FR1) as (r3 & M3 & RUN3 & J25 & J2 & KC3 & GM3 & FR3).
      exists r3, M3. split; [|split; [exact J25 | split; [exact J2 | split; [|split; [exact GM3 | exact FR3]]]]].
      + eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2 | exact RUN3].
      + intros r; intros. rewrite KC3 by assumption. rewrite KC2 by assumption. apply KC1; assumption.
  Qed.
End CLASS.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WHOLE.
  Variable mem0 : word -> option byte.
  Variable rom : word -> option byte.
  Variables sp ra : word.
  Variables t fs sparg tpv key tsd ctx th top botth g40 g35 : Z.    (* [comment removed for export] *)
  Variables flag rs : Z -> Z -> Z.           (* [comment removed for export] *)
  Hypothesis Hs_def : bv_unsigned sp = t.
  Hypothesis Hret : ret_ok ra.
  Hypothesis Ht : (0x1000000 <= t - 160)%Z /\ (t < 2 ^ 64)%Z.
  Hypothesis Hok : store_ok ASEGS mem0 (Z_to_bv 64 (t - 160)) 160%nat = true.
  Hypothesis Htp : (96 <= tpv < 2 ^ 64)%Z.
  Hypothesis Hkey : (0 <= key < 2 ^ 28)%Z.
  Hypothesis Htsd : (0 <= tsd /\ tsd + 8 * key + 8 <= 2 ^ 64)%Z.
  Hypothesis Hctx : (0 < ctx /\ ctx + 160 <= 2 ^ 64)%Z.
  Hypothesis Hth : (0 < th /\ th + 80 <= 2 ^ 64)%Z.
  Hypothesis Htop : (botth < top)%Z /\ (0 <= botth)%Z /\ (top < 2 ^ 64)%Z /\ (botth <= sparg <= top)%Z.   (* [comment removed for export] *)
  Hypothesis Hfs : (0x696000 <= fs)%Z /\ (fs + 4096 + 32768 + 11 * 2 ^ 20 < 2 ^ 47)%Z /\ (fs + 4096 + 32768 + 11 * 2 ^ 20 <= t - 160 \/ t <= fs)%Z.
  Hypothesis Happ : (fs + 4096 + 32768 + 11 * 2 ^ 20 <= 0x7fff7000 \/ 0x10007fff8000 <= fs)%Z.          (* [comment removed for export] *)
  Hypothesis Hshz : (gc_shz_hi fs <= t - 160 \/ t <= gc_shz_lo fs)%Z.                                     (* [comment removed for export] *)
  Hypothesis Hwfs : store_ok ASEGS mem0 (Z_to_bv 64 fs) (Z.to_nat (4096 + 32768 + 11 * 2 ^ 20)) = true.  (* [comment removed for export] *)
  Hypothesis Hg : (0 <= g40 < 2 ^ 64)%Z.
  (* [comment removed for export] *)
  Hypothesis HF0 : forall c i, gc_valid c i ->
    rdn ASEGS mem0 (Z_to_bv 64 (gc_fl fs c i)) 1%nat = Some [Z_to_bv 8 (flag c i)] /\ (0 <= flag c i < 256)%Z.
  (* [comment removed for export] *)
  Hypothesis HCT : forall M', (forall x : word, (bv_unsigned x < t - 160 \/ t <= bv_unsigned x)%Z -> M' x = mem0 x) ->
     rdn ASEGS M' (0x13f4a0 : word) 1%nat = Some [Z_to_bv 8 1] /\                                       (* [comment removed for export] *)
     rdn ASEGS M' (0x13f4a4 : word) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 key)) /\
     rdn ASEGS M' (Z_to_bv 64 (tpv - 88)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 tsd)) /\
     rdn ASEGS M' (Z_to_bv 64 (tsd + 8 * key)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 ctx)) /\
     rdn ASEGS M' (Z_to_bv 64 (ctx + 152)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 th)) /\
     rdn ASEGS M' (Z_to_bv 64 (th + 40)) 1%nat = Some [Z_to_bv 8 0] /\                                  (* [comment removed for export] *)
     rdn ASEGS M' (Z_to_bv 64 (th + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 top)) /\        (* [comment removed for export] *)
     rdn ASEGS M' (Z_to_bv 64 (th + 16)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 botth)) /\     (* [comment removed for export] *)
     rdn ASEGS M' (0x1374b8 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 g40)) /\              (* [comment removed for export] *)
     rdn ASEGS M' (0x10380 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 g35)).    (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis HCL : forall M', (forall x : word, gc_outz (t - 160) t fs (bv_unsigned x) -> M' x = mem0 x) ->
     rdn ASEGS M' (Z_to_bv 64 (fs + 88)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 20))          (* [comment removed for export] *)
     /\ rt_layout_globs M'                                                                            (* [comment removed for export] *)
     /\ (forall c i, gc_valid c i -> flag c i <> 0%Z ->
          rdn ASEGS M' (Z_to_bv 64 (gc_fr fs c i + 24)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (rs c i))) /\ (0 <= rs c i < 2 ^ 64)%Z).
  (* [comment removed for export] *)
  Hypothesis Hcol6 : forall c i, gc_valid c i -> gc_col sparg botth flag rs c i -> (c <= 6)%Z.
  Hypothesis Hshok : forall c i, gc_valid c i -> gc_col sparg botth flag rs c i ->
    store_ok ASEGS mem0 (Z_to_bv 64 (gc_sh fs c i)) (Z.to_nat (2 ^ (3 + c))) = true.

  #[local] Ltac hide_dj := try hide Hfs.
  #[using="Hs_def"] Lemma sp_sgc : sp = Z_to_bv 64 t.  Proof. rewrite <- Hs_def. symmetry. apply Z_to_bv_bv_unsigned. Qed.

  (* [comment removed for export] *)
  Definition F13 (rg : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem0
      (Z_to_bv 64 (t - 8)) (word_to_le_bytes 8 ra))
      (Z_to_bv 64 (t - 16)) (word_to_le_bytes 8 (getr rg 8)))
      (Z_to_bv 64 (t - 24)) (word_to_le_bytes 8 (getr rg 9)))
      (Z_to_bv 64 (t - 32)) (word_to_le_bytes 8 (getr rg 18)))
      (Z_to_bv 64 (t - 40)) (word_to_le_bytes 8 (getr rg 19)))
      (Z_to_bv 64 (t - 48)) (word_to_le_bytes 8 (getr rg 20)))
      (Z_to_bv 64 (t - 56)) (word_to_le_bytes 8 (getr rg 21)))
      (Z_to_bv 64 (t - 64)) (word_to_le_bytes 8 (getr rg 22)))
      (Z_to_bv 64 (t - 72)) (word_to_le_bytes 8 (getr rg 23)))
      (Z_to_bv 64 (t - 80)) (word_to_le_bytes 8 (getr rg 24)))
      (Z_to_bv 64 (t - 88)) (word_to_le_bytes 8 (getr rg 25)))
      (Z_to_bv 64 (t - 96)) (word_to_le_bytes 8 (getr rg 26)))
      (Z_to_bv 64 (t - 104)) (word_to_le_bytes 8 (getr rg 27)).

  #[using="key tsd ctx th top g40 g35 Hs_def Hret Ht Hok Htp Hkey Htsd Hctx Hth Htop Hfs Happ Hshz Hwfs HF0 HCT HCL Hcol6 Hshok"] Theorem gc_collect_run : forall regs,
    getr regs 10 = Z_to_bv 64 fs -> getr regs 11 = Z_to_bv 64 sparg -> getr regs 4 = Z_to_bv 64 tpv -> getr regs 2 = sp -> getr regs 1 = ra ->
    exists regs' Mf,
      msteps ASEGS (mkst regs (0x5d7e0 : word) mem0 rom) (mkst regs' ra Mf rom)
      /\ getr regs' 2 = sp /\ getr regs' 1 = ra /\ keeps_cs regs regs'
      /\ gc_post mem0 Mf (t - 160) t fs (gc_col sparg botth flag rs).
  Proof.
    assert (HCo : forall M', (forall x : word, (bv_unsigned x < t - 160 \/ t <= bv_unsigned x)%Z -> M' x = mem0 x) ->
       rdn ASEGS M' (0x13f4a0 : word) 1%nat = Some [Z_to_bv 8 1] /\
       rdn ASEGS M' (0x13f4a4 : word) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 key)) /\
       rdn ASEGS M' (Z_to_bv 64 (tpv - 88)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 tsd)) /\
       rdn ASEGS M' (Z_to_bv 64 (tsd + 8 * key)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 ctx)) /\
       rdn ASEGS M' (Z_to_bv 64 (ctx + 152)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 th)) /\
       rdn ASEGS M' (Z_to_bv 64 (th + 40)) 1%nat = Some [Z_to_bv 8 0] /\
       rdn ASEGS M' (Z_to_bv 64 (th + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 top)) /\
       rdn ASEGS M' (Z_to_bv 64 (th + 16)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 botth)) /\
       rt_layout_globs M' /\
       rdn ASEGS M' (0x1374b8 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 g40)) /\
       rdn ASEGS M' (0x10380 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 g35))).
    { intros M' O. destruct (HCT M' O) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10).
      destruct (HCL M') as (_ & LAY & _); [intros x (O1 & _); apply O; exact O1|].
      exact (conj C1 (conj C2 (conj C3 (conj C4 (conj C5 (conj C6 (conj C7 (conj C8 (conj LAY (conj C9 C10)))))))))). }
    hide_dj.
    intros regs H10 H11 H4 H2 H1. rewrite sp_sgc in H2.
    destruct Ht as [Ta Tb]. destruct Hth as [Th1 Th2]. destruct Htop as (Tp1 & Tp2 & Tp3 & Tp4).
    unhide Hfs. destruct Hfs as (Fs1 & Fs2 & Fs3). hide Fs3.
    assert (Hra : ret_ok (0x5d824 : word)) by (unfold ret_ok; apply bv_eq; vm_compute; reflexivity).
    #[local] Ltac oout := intros x Hx; pose proof (u64_range x);
       destruct Hx as [Hx|Hx]; [rewrite !wbytes_below; first [reflexivity | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; imm_norm; unorm; lia | unorm; lia]
                              | rewrite !wbytes_above; first [reflexivity | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; imm_norm; unorm; lia]].
    #[local] Ltac sok := apply (store_ok_mono _ _ mem0); [repeat (eapply mem_grows_trans; [|apply wbytes_grows]); first [apply mem_grows_refl | assumption] |];
                        apply (store_ok_sub ASEGS mem0 (Z_to_bv 64 (t - 160)) _ 160%nat); [unorm; cbn; lia | exact Hok | unorm; lia | unorm; cbn; lia].
    assert (O13 : forall x : word, (bv_unsigned x < t - 160 \/ t <= bv_unsigned x)%Z -> F13 regs x = mem0 x) by (unfold F13; oout).
    assert (G13 : mem_grows mem0 (F13 regs)) by (unfold F13; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
    (* [comment removed for export] *)
    assert (S1 : exists r1, msteps ASEGS (mkst regs (0x5d7e0 : word) mem0 rom) (mkst r1 (0x838e4 : word) (F13 regs) rom)
              /\ (getr r1 9 = Z_to_bv 64 sparg /\ getr r1 25 = Z_to_bv 64 fs /\ getr r1 4 = Z_to_bv 64 tpv /\ getr r1 2 = Z_to_bv 64 (t - 144)
                  /\ getr r1 1 = (0x5d824 : word) /\ keeps_but [1; 2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv regs r1)).
    { unfold F13. eexists. split.
      - stepiv F_5d3c8 D_5d3c8 (Z_to_bv 64 (t - 144)) ltac:(wval).                                       (* [comment removed for export] *)
        stepsd F_5d3cc D_5d3cc (Z_to_bv 64 (t - 8)) ra ltac:(sok).                                          (* [comment removed for export] *)
        stepsd F_5d3d0 D_5d3d0 (Z_to_bv 64 (t - 16)) (getr regs 8) ltac:(sok).
        stepsd F_5d3d4 D_5d3d4 (Z_to_bv 64 (t - 24)) (getr regs 9) ltac:(sok).
        stepsd F_5d3d8 D_5d3d8 (Z_to_bv 64 (t - 32)) (getr regs 18) ltac:(sok).
        stepsd F_5d3dc D_5d3dc (Z_to_bv 64 (t - 40)) (getr regs 19) ltac:(sok).
        stepsd F_5d3e0 D_5d3e0 (Z_to_bv 64 (t - 48)) (getr regs 20) ltac:(sok).
        stepsd F_5d3e4 D_5d3e4 (Z_to_bv 64 (t - 56)) (getr regs 21) ltac:(sok).
        stepsd F_5d3e8 D_5d3e8 (Z_to_bv 64 (t - 64)) (getr regs 22) ltac:(sok).
        stepsd F_5d3ec D_5d3ec (Z_to_bv 64 (t - 72)) (getr regs 23) ltac:(sok).
        stepsd F_5d3f0 D_5d3f0 (Z_to_bv 64 (t - 80)) (getr regs 24) ltac:(sok).
        stepsd F_5d3f4 D_5d3f4 (Z_to_bv 64 (t - 88)) (getr regs 25) ltac:(sok).
        stepsd F_5d3f8 D_5d3f8 (Z_to_bv 64 (t - 96)) (getr regs 26) ltac:(sok).
        stepsd F_5d3fc D_5d3fc (Z_to_bv 64 (t - 104)) (getr regs 27) ltac:(sok).                           (* [comment removed for export] *)
        stepiv F_5d400 D_5d400 (Z_to_bv 64 sparg) ltac:(wval).                                           (* [comment removed for export] *)
        stepiv F_5d404 D_5d404 (Z_to_bv 64 fs) ltac:(wval).                                              (* [comment removed for export] *)
        stepn F_5d408 D_5d408.                                                                             (* [comment removed for export] *)
        apply mst_refl.
      - repeat split; gres; rwH; try reflexivity; try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
    destruct S1 as (r1 & RUN1 & Q9 & Q25 & Q4 & Q2 & Q1 & K1).
    (* [comment removed for export] *)
    destruct (get_current_thread_run r1 (F13 regs) rom (0x5d824 : word) (t - 144) tpv key tsd ctx th Q2 Q4 Q1 Hra ltac:(lia) ltac:(lia) Htp Hkey Htsd Hctx ltac:(lia)
                ltac:(replace (t - 144 - 16)%Z with (t - 160)%Z by lia; unfold F13; sok)) as (r2 & RUN2 & T10 & T2 & T1 & K2).
    { intros M' HM'. assert (O' : forall x : word, (bv_unsigned x < t - 160 \/ t <= bv_unsigned x)%Z -> M' x = mem0 x).
      { intros x Hx. rewrite (HM' x) by lia. apply O13. exact Hx. }
      destruct (HCo M' O') as (C1 & C2 & C3 & C4 & C5 & _). repeat split; assumption. }
    set (M14 := wbytes (F13 regs) (Z_to_bv 64 (t - 144 - 8)) (word_to_le_bytes 8 (0x5d824 : word))) in RUN2.
    assert (O14 : forall x : word, (bv_unsigned x < t - 160 \/ t <= bv_unsigned x)%Z -> M14 x = mem0 x).
    { intros x Hx. rewrite <- (O13 x Hx). unfold M14. revert x Hx. oout. }
    assert (G14 : mem_grows mem0 M14) by (unfold M14; eapply mem_grows_trans; [exact G13 | apply wbytes_grows]).
    assert (T9 : getr r2 9 = Z_to_bv 64 sparg) by (rewrite (K2 9%bv) by kbt; exact Q9).
    assert (T25 : getr r2 25 = Z_to_bv 64 fs) by (rewrite (K2 25%bv) by kbt; exact Q25).
    assert (T4 : getr r2 4 = Z_to_bv 64 tpv) by (rewrite (K2 4%bv) by kbt; exact Q4).
    destruct (HCo M14 O14) as (_ & _ & _ & _ & _ & D40 & D8 & D16 & (E48 & _ & E50 & _) & _).
    set (M15 := wbytes M14 (Z_to_bv 64 (t - 120)) (word_to_le_bytes 8 (Z_to_bv 64 0x140928))).
    set (M16 := wbytes M15 (Z_to_bv 64 (t - 128)) (word_to_le_bytes 8 (Z_to_bv 64 0x140930))).
    set (M17 := wbytes M16 (Z_to_bv 64 (t - 136)) (word_to_le_bytes 8 (Z_to_bv 64 0x140920))).
    set (M18 := wbytes M17 (Z_to_bv 64 (t - 144)) (word_to_le_bytes 8 (Z_to_bv 64 g40))).
    assert (O15 : forall x : word, (bv_unsigned x < t - 160 \/ t <= bv_unsigned x)%Z -> M15 x = mem0 x) by (intros x Hx; rewrite <- (O14 x Hx); unfold M15; revert x Hx; oout).
    assert (O16 : forall x : word, (bv_unsigned x < t - 160 \/ t <= bv_unsigned x)%Z -> M16 x = mem0 x) by (intros x Hx; rewrite <- (O15 x Hx); unfold M16; revert x Hx; oout).
    assert (O17 : forall x : word, (bv_unsigned x < t - 160 \/ t <= bv_unsigned x)%Z -> M17 x = mem0 x) by (intros x Hx; rewrite <- (O16 x Hx); unfold M17; revert x Hx; oout).
    assert (O18 : forall x : word, (bv_unsigned x < t - 160 \/ t <= bv_unsigned x)%Z -> M18 x = mem0 x) by (intros x Hx; rewrite <- (O17 x Hx); unfold M18; revert x Hx; oout).
    assert (G18 : mem_grows mem0 M18) by (unfold M18, M17, M16, M15; do 4 (eapply mem_grows_trans; [|apply wbytes_grows]); exact G14).
    destruct (HCo M15 O15) as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & E58 & _) & _).
    destruct (HCo M16 O16) as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & E60 & _) & _).
    destruct (HCo M17 O17) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & E40 & _).
    destruct (HCo M18 O18) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E35).
    (* [comment removed for export] *)
    assert (S3 : exists r3, msteps ASEGS (mkst r2 (0x5d824 : word) M14 rom) (mkst r3 (0x5d8b0 : word) M18 rom)
              /\ (gcl2_inv t fs sparg botth g35 r3 0 /\ keeps_but [1; 2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv r2 r3)).
    { eexists. split.
      - stepb_ft F_5d40c D_5d40c ltac:(cond).                                                              (* [comment removed for export] *)
        stepiv F_5d410 D_5d410 (Z_to_bv 64 th) ltac:(wval).                                               (* [comment removed for export] *)
        stepn F_5d414 D_5d414.                                                                             (* [comment removed for export] *)
        mlbq F_83690 D_83690 (th + 40)%Z D40.                                                               (* [comment removed for export] *)
        stepfence F_83694 D_83694.
        stepb_tk F_83698 D_83698 ltac:(rwH; cbn; cond).                                                    (* [comment removed for export] *)
        mldq F_836d0 D_836d0 (th + 8)%Z D8.                                                                 (* [comment removed for export] *)
        mldq F_836d4 D_836d4 (th + 16)%Z D16.                                                               (* [comment removed for export] *)
        stepov F_836d8 D_836d8 (Z_to_bv 64 1) ltac:(gres; rwH; unfold v_sltu, c_ltu, bv_ltu; unorm; replace (botth <? top)%Z with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).  (* [comment removed for export] *)
        stepn F_836dc D_836dc.                                                                             (* [comment removed for export] *)
        stepov F_836e0 D_836e0 (Z_to_bv 64 top) ltac:(gres; rwH; unfold v_and; imm_norm; unorm; rewrite Z.land_comm; change 18446744073709551615%Z with (Z.ones 64); rewrite Z.land_ones by lia; f_equal; apply Z.mod_small; lia).  (* [comment removed for export] *)
        stepret F_836e4 D_836e4 (0x5d830 : word) ltac:(rwH; first [reflexivity | apply bv_eq; vm_compute; reflexivity]).
        stepiv F_5d418 D_5d418 (Z_to_bv 64 top) ltac:(wval).                                              (* [comment removed for export] *)
        stepiv F_5d41c D_5d41c (Z_to_bv 64 th) ltac:(wval).                                               (* [comment removed for export] *)
        stepn F_5d420 D_5d420.                                                                             (* [comment removed for export] *)
        mlbq F_836e8 D_836e8 (th + 40)%Z D40.                                                               (* [comment removed for export] *)
        stepfence F_836ec D_836ec.
        stepb_tk F_836f0 D_836f0 ltac:(rwH; cbn; cond).                                                    (* [comment removed for export] *)
        mldq F_83728 D_83728 (th + 8)%Z D8.                                                                 (* [comment removed for export] *)
        mldq F_8372c D_8372c (th + 16)%Z D16.                                                               (* [comment removed for export] *)
        stepov F_83730 D_83730 (Z_to_bv 64 1) ltac:(gres; rwH; unfold v_sltu, c_ltu, bv_ltu; unorm; replace (botth <? top)%Z with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).  (* [comment removed for export] *)
        stepn F_83734 D_83734.                                                                             (* [comment removed for export] *)
        stepov F_83738 D_83738 (Z_to_bv 64 botth) ltac:(gres; rwH; unfold v_and; imm_norm; unorm; change 18446744073709551615%Z with (Z.ones 64); rewrite Z.land_comm; rewrite Z.land_ones by lia; f_equal; apply Z.mod_small; lia).  (* [comment removed for export] *)
        stepret F_8373c D_8373c (0x5d83c : word) ltac:(rwH; first [reflexivity | apply bv_eq; vm_compute; reflexivity]).
        stepb_ft F_5d424 D_5d424 ltac:(cond).                                                              (* [comment removed for export] *)
        stepiv F_5d428 D_5d428 (Z_to_bv 64 botth) ltac:(wval).                                            (* [comment removed for export] *)
        stepb_ft F_5d42c D_5d42c ltac:(cond).                                                              (* [comment removed for export] *)
        stepn F_5d430 D_5d430.                                                                             (* [comment removed for export] *)
        stepn F_5d434 D_5d434.                                                                             (* [comment removed for export] *)
        stepn F_5d438 D_5d438.                                                                             (* [comment removed for export] *)
        stepn F_5d43c D_5d43c.
        stepn F_5d440 D_5d440.
        stepn F_5d444 D_5d444.
        stepn F_5d448 D_5d448.
        stepn F_5d44c D_5d44c.
        stepiv F_5d450 D_5d450 (Z_to_bv 64 (fs + 4096)) ltac:(wval).                                      (* [comment removed for export] *)
        mld F_5d454 D_5d454 (0x1374c0 : word) E48.                                                          (* [comment removed for export] *)
        mld F_5d458 D_5d458 (0x1374c8 : word) E50.                                                          (* [comment removed for export] *)
        stepsdq F_5d45c D_5d45c (Z_to_bv 64 (t - 120)) (Z_to_bv 64 0x140928) ltac:(unfold M14, F13; sok).       (* [comment removed for export] *)
        change (wbytes M14 (Z_to_bv 64 (t - 120)) (word_to_le_bytes 8 (Z_to_bv 64 0x140928))) with M15.
        mld F_5d460 D_5d460 (0x1374d0 : word) E58.                                                          (* [comment removed for export] *)
        stepsdq F_5d464 D_5d464 (Z_to_bv 64 (t - 128)) (Z_to_bv 64 0x140930) ltac:(unfold M15, M14, F13; sok).  (* [comment removed for export] *)
        change (wbytes M15 (Z_to_bv 64 (t - 128)) (word_to_le_bytes 8 (Z_to_bv 64 0x140930))) with M16.
        mld F_5d468 D_5d468 (0x1374d8 : word) E60.                                                          (* [comment removed for export] *)
        stepsdq F_5d46c D_5d46c (Z_to_bv 64 (t - 136)) (Z_to_bv 64 0x140920) ltac:(unfold M16, M15, M14, F13; sok).   (* [comment removed for export] *)
        change (wbytes M16 (Z_to_bv 64 (t - 136)) (word_to_le_bytes 8 (Z_to_bv 64 0x140920))) with M17.
        mld F_5d470 D_5d470 (0x1374b8 : word) E40.                                                          (* [comment removed for export] *)
        stepsdq F_5d474 D_5d474 (Z_to_bv 64 (t - 144)) (Z_to_bv 64 g40) ltac:(unfold M17, M16, M15, M14, F13; sok).   (* [comment removed for export] *)
        change (wbytes M17 (Z_to_bv 64 (t - 144)) (word_to_le_bytes 8 (Z_to_bv 64 g40))) with M18.
        mld F_5d478 D_5d478 (0x10380 : word) E35.                                                          (* [comment removed for export] *)
        stepn F_5d47c D_5d47c.                                                                             (* [comment removed for export] *)
        stepn F_5d480 D_5d480.                                                                             (* [comment removed for export] *)
        stepn F_5d484 D_5d484.                                                                             (* [comment removed for export] *)
        stepn F_5d488 D_5d488.                                                                             (* [comment removed for export] *)
        apply mst_refl.
      - split; [unfold gcl2_inv; post | solve_keeps_but]. }
    destruct S3 as (r3 & RUN3 & I3 & K3).
    (* [comment removed for export] *)
    assert (HFR' : rdn ASEGS M18 (Z_to_bv 64 (t - 120)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x140928))
                /\ rdn ASEGS M18 (Z_to_bv 64 (t - 128)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x140930))
                /\ rdn ASEGS M18 (Z_to_bv 64 (t - 136)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x140920))).
    { unfold M18, M17, M16, M15. repeat split;
        repeat (rewrite rdn_wbytes_out; [ | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia | cbn [Z.of_nat Pos.to_nat]; unorm; lia | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia ]);
        apply rdn_wbytes_hit8; unorm; lia. }
    unhide Fs3.
    pose proof (gc_kit t fs (conj Fs1 (conj Fs2 Fs3)) Happ) as (KK1 & KK2 & KK3 & KK4).
    assert (GM18 : gcm mem0 (t - 160) t fs (gc_col sparg botth flag rs) (gc_done_lt 0 0) M18).
    { apply (gcm_equiv mem0 (t - 160) t fs _ (fun _ _ => False)); [|apply gcm_init; [exact G18 | exact O18]].
      intros c i [Vc Vi]. unfold gc_done_lt. lia. }
    assert (FR18 : frm M18 t M18) by (intros x _ _; reflexivity).
    assert (Hsp' : (0 <= sparg < 2 ^ 64)%Z /\ (0 <= botth < 2 ^ 64)%Z) by lia.
    destruct (gcc_classes_run mem0 M18 rom t fs sparg botth g35 flag rs (conj Ta Tb) (conj Fs1 (conj Fs2 Fs3)) Happ Hshz Hsp' Hok Hwfs HF0 HCL HFR' Hcol6 Hshok
                10%nat r3 M18 0%Z I3 ltac:(lia) eq_refl GM18 FR18) as (r4 & M4 & RUN4 & J25 & J2 & K4 & GM4 & FR4).
    hide Fs3.
    assert (Hwf96 : store_ok ASEGS mem0 (Z_to_bv 64 (fs + 96)) 1%nat = true).
    { apply (store_ok_sub ASEGS mem0 (Z_to_bv 64 fs) _ (Z.to_nat (4096 + 32768 + 11 * 2 ^ 20))); [unorm; lia | exact Hwfs | unorm; lia | unorm; cbn [Z.of_nat Pos.to_nat]; lia]. }
    assert (G4' : mem_grows mem0 M4) by (destruct GM4 as (X & _); exact X).
    set (M5 := wbytes M4 (Z_to_bv 64 (fs + 96)) [Z_to_bv 8 0]).
    (* [comment removed for export] *)
    assert (SL : forall k v, (k = 8 /\ v = ra \/ k = 16 /\ v = getr regs 8 \/ k = 24 /\ v = getr regs 9 \/ k = 32 /\ v = getr regs 18 \/ k = 40 /\ v = getr regs 19 \/ k = 48 /\ v = getr regs 20 \/ k = 56 /\ v = getr regs 21 \/ k = 64 /\ v = getr regs 22 \/ k = 72 /\ v = getr regs 23 \/ k = 80 /\ v = getr regs 24 \/ k = 88 /\ v = getr regs 25 \/ k = 96 /\ v = getr regs 26 \/ k = 104 /\ v = getr regs 27)%Z ->
                 rdn ASEGS M5 (Z_to_bv 64 (t - k)) 8%nat = Some (word_to_le_bytes 8 v)).
    { intros k v Hk. assert (Hk' : (8 <= k <= 104)%Z) by lia.
      rewrite (rdn_ext ASEGS 8 M5 (F13 regs)); [| unorm; cbn; lia |].
      - unfold F13. destruct Hk as [[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]]]]]]]]]]];
          repeat (rewrite rdn_wbytes_out; [ | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; (clear - t; lia) | cbn [Z.of_nat Pos.to_nat]; unorm; (clear - Ht t; lia) | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; (clear - Ht t; lia) ]);
          apply rdn_wbytes_hit8; unorm; (clear - Ht t; lia).
      - intros x Hx. rewrite u_Z2bv in Hx by lia. cbn [Z.of_nat Pos.to_nat] in Hx. pose proof (u64_range x).
        unfold M5. rewrite wbytes_out_any_gc; [| cbn [length Z.of_nat Pos.to_nat]; unorm; lia | cbn [length Z.of_nat Pos.to_nat]; unorm; lia].
        rewrite (FR4 x) by lia.
        unfold M18, M17, M16, M15, M14. rewrite !wbytes_above; first [reflexivity | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; imm_norm; unorm; lia]. }
    #[local] Ltac slv := first [split; reflexivity | left; split; reflexivity | right; slv].
    eexists. exists M5. split.
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|]. eapply msteps_trans; [exact RUN4|].
      chain_step; [reflexivity | eapply (step_sb_at ASEGS) with (a := Z_to_bv 64 (fs + 96)) (b := Z_to_bv 8 0);
          [exact F_5d670 | reflexivity | exact D_5d670 | wval | gres; reflexivity | apply bv_eq; vm_compute; reflexivity
          | apply (store_ok_mono _ _ mem0 M4 _ G4'); exact Hwf96 ] | step_simpl; vnorm].                     (* [comment removed for export] *)
      change (wbytes M4 (Z_to_bv 64 (fs + 96)) [Z_to_bv 8 0]) with M5.
      stepld F_5d674 D_5d674 (ra) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (t - 8)) by (symmetry; wval) end; apply SL; slv).
      stepld F_5d678 D_5d678 (getr regs 8) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (t - 16)) by (symmetry; wval) end; apply SL; slv).
      stepld F_5d67c D_5d67c (getr regs 9) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (t - 24)) by (symmetry; wval) end; apply SL; slv).
      stepld F_5d680 D_5d680 (getr regs 18) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (t - 32)) by (symmetry; wval) end; apply SL; slv).
      stepld F_5d684 D_5d684 (getr regs 19) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (t - 40)) by (symmetry; wval) end; apply SL; slv).
      stepld F_5d688 D_5d688 (getr regs 20) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (t - 48)) by (symmetry; wval) end; apply SL; slv).
      stepld F_5d68c D_5d68c (getr regs 21) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (t - 56)) by (symmetry; wval) end; apply SL; slv).
      stepld F_5d690 D_5d690 (getr regs 22) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (t - 64)) by (symmetry; wval) end; apply SL; slv).
      stepld F_5d694 D_5d694 (getr regs 23) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (t - 72)) by (symmetry; wval) end; apply SL; slv).
      stepld F_5d698 D_5d698 (getr regs 24) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (t - 80)) by (symmetry; wval) end; apply SL; slv).
      stepld F_5d69c D_5d69c (getr regs 25) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (t - 88)) by (symmetry; wval) end; apply SL; slv).
      stepld F_5d6a0 D_5d6a0 (getr regs 26) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (t - 96)) by (symmetry; wval) end; apply SL; slv).
      stepld F_5d6a4 D_5d6a4 (getr regs 27) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (t - 104)) by (symmetry; wval) end; apply SL; slv).
      stepiv F_5d6a8 D_5d6a8 (Z_to_bv 64 t) ltac:(wval).                                                  (* [comment removed for export] *)
      stepret F_5d6ac D_5d6ac ra ltac:(rwH; reflexivity).
      apply mst_refl.
    - split; [gres; symmetry; apply sp_sgc|]. split; [gres; reflexivity|]. split.
      { intros r Hcs. cbv in Hcs.
        destruct Hcs as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]]]; gres;
          first [ reflexivity | rewrite H1; reflexivity | rewrite H2; reflexivity
                | rewrite (K4 _) by (intros E; discriminate E); rewrite (K3 _) by kbt;
                  rewrite (K2 _) by kbt; rewrite (K1 _) by kbt; reflexivity ]. }
      destruct GM4 as (G4 & O4 & P4).
      assert (OUT5 : forall x : word, bv_unsigned x <> (fs + 96)%Z -> M5 x = M4 x).
      { intros x Hx. unfold M5. apply wbytes_outside; cbn [length Z.of_nat Pos.to_nat]; rewrite u64_lit by lia; lia. }
      assert (DALL : forall c i, gc_valid c i -> gc_done_lt 11 0 c i) by (intros c i [Vc _]; unfold gc_done_lt; lia).
      split; [eapply mem_grows_trans; [exact G4 | apply wbytes_grows]|]. split; [|split].
      + intros x Hx N96 Hn. rewrite OUT5 by exact N96. apply O4; [exact Hx|]. intros c i V _ C. apply Hn; assumption.
      + intros c i V C. pose proof (P4 c i V (DALL c i V) C) as QQ1. pose proof (gc_fl_range fs c i V) as FLR.
        rewrite OUT5 by (rewrite u64_lit by lia; lia). exact QQ1.
      + unfold M5. apply (rdn_wbytes_hit ASEGS [Z_to_bv 8 0]). cbn [length Z.of_nat Pos.to_nat]. rewrite u64_lit by lia. lia.
  Qed.
End WHOLE.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section EARLY.
  Variable mem0 : word -> option byte.
  Variable rom : word -> option byte.
  Variables sp ra : word.
  Variables t fs sparg tpv key tsd ctx th top botth : Z.
  Hypothesis Hs_def : bv_unsigned sp = t.
  Hypothesis Hret : ret_ok ra.
  Hypothesis Ht : (0x1000000 <= t - 160)%Z /\ (t < 2 ^ 64)%Z.
  Hypothesis Hok : store_ok ASEGS mem0 (Z_to_bv 64 (t - 160)) 160%nat = true.
  Hypothesis Htp : (96 <= tpv < 2 ^ 64)%Z.
  Hypothesis Hkey : (0 <= key < 2 ^ 28)%Z.
  Hypothesis Htsd : (0 <= tsd /\ tsd + 8 * key + 8 <= 2 ^ 64)%Z.
  Hypothesis Hctx : (0 < ctx /\ ctx + 160 <= 2 ^ 64)%Z.
  Hypothesis Hth : (0 < th /\ th + 80 <= 2 ^ 64)%Z.
  Hypothesis Htop : (botth < top)%Z /\ (0 <= botth)%Z /\ (top < 2 ^ 64)%Z /\ (top < sparg)%Z /\ (sparg < 2 ^ 64)%Z.   (* [comment removed for export] *)
  Hypothesis Hfsb : (0 <= fs < 2 ^ 64)%Z.
  Hypothesis HCE : forall M', (forall x : word, (bv_unsigned x < t - 160 \/ t <= bv_unsigned x)%Z -> M' x = mem0 x) ->
     rdn ASEGS M' (0x13f4a0 : word) 1%nat = Some [Z_to_bv 8 1] /\
     rdn ASEGS M' (0x13f4a4 : word) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 key)) /\
     rdn ASEGS M' (Z_to_bv 64 (tpv - 88)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 tsd)) /\
     rdn ASEGS M' (Z_to_bv 64 (tsd + 8 * key)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 ctx)) /\
     rdn ASEGS M' (Z_to_bv 64 (ctx + 152)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 th)) /\
     rdn ASEGS M' (Z_to_bv 64 (th + 40)) 1%nat = Some [Z_to_bv 8 0] /\
     rdn ASEGS M' (Z_to_bv 64 (th + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 top)) /\
     rdn ASEGS M' (Z_to_bv 64 (th + 16)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 botth)).

  #[using="Hs_def"] Lemma sp_sge : sp = Z_to_bv 64 t.  Proof. rewrite <- Hs_def. symmetry. apply Z_to_bv_bv_unsigned. Qed.

  (* [comment removed for export] *)
  Definition F13e (rg : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem0
      (Z_to_bv 64 (t - 8)) (word_to_le_bytes 8 ra))
      (Z_to_bv 64 (t - 16)) (word_to_le_bytes 8 (getr rg 8)))
      (Z_to_bv 64 (t - 24)) (word_to_le_bytes 8 (getr rg 9)))
      (Z_to_bv 64 (t - 32)) (word_to_le_bytes 8 (getr rg 18)))
      (Z_to_bv 64 (t - 40)) (word_to_le_bytes 8 (getr rg 19)))
      (Z_to_bv 64 (t - 48)) (word_to_le_bytes 8 (getr rg 20)))
      (Z_to_bv 64 (t - 56)) (word_to_le_bytes 8 (getr rg 21)))
      (Z_to_bv 64 (t - 64)) (word_to_le_bytes 8 (getr rg 22)))
      (Z_to_bv 64 (t - 72)) (word_to_le_bytes 8 (getr rg 23)))
      (Z_to_bv 64 (t - 80)) (word_to_le_bytes 8 (getr rg 24)))
      (Z_to_bv 64 (t - 88)) (word_to_le_bytes 8 (getr rg 25)))
      (Z_to_bv 64 (t - 96)) (word_to_le_bytes 8 (getr rg 26)))
      (Z_to_bv 64 (t - 104)) (word_to_le_bytes 8 (getr rg 27)).


  #[using="key tsd ctx th top botth Hs_def Hret Ht Hok Htp Hkey Htsd Hctx Hth Htop Hfsb HCE"] Theorem gc_early_run : forall regs,
    getr regs 10 = Z_to_bv 64 fs -> getr regs 11 = Z_to_bv 64 sparg -> getr regs 4 = Z_to_bv 64 tpv -> getr regs 2 = sp -> getr regs 1 = ra ->
    exists regs' Mj,
      msteps ASEGS (mkst regs (0x5d7e0 : word) mem0 rom) (mkst regs' ra Mj rom)
      /\ getr regs' 2 = sp /\ getr regs' 1 = ra /\ keeps_cs regs regs'
      /\ (forall x : word, (bv_unsigned x < t - 160 \/ t <= bv_unsigned x)%Z -> Mj x = mem0 x) /\ mem_grows mem0 Mj.
  Proof.
    intros regs H10 H11 H4 H2 H1. rewrite sp_sge in H2.
    destruct Ht as [Ta Tb]. destruct Hth as [Th1 Th2]. destruct Htop as (Tp1 & Tp2 & Tp3 & Tp4 & Tp5).
    assert (Hra : ret_ok (0x5d824 : word)) by (unfold ret_ok; apply bv_eq; vm_compute; reflexivity).
    #[local] Ltac oout := intros x Hx; pose proof (u64_range x);
       destruct Hx as [Hx|Hx]; [rewrite !wbytes_below; first [reflexivity | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; imm_norm; unorm; lia | unorm; lia]
                              | rewrite !wbytes_above; first [reflexivity | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; imm_norm; unorm; lia]].
    #[local] Ltac sok := apply (store_ok_mono _ _ mem0); [repeat (eapply mem_grows_trans; [|apply wbytes_grows]); first [apply mem_grows_refl | assumption] |];
                        apply (store_ok_sub ASEGS mem0 (Z_to_bv 64 (t - 160)) _ 160%nat); [unorm; cbn; lia | exact Hok | unorm; lia | unorm; cbn; lia].
    assert (O13 : forall x : word, (bv_unsigned x < t - 160 \/ t <= bv_unsigned x)%Z -> F13e regs x = mem0 x) by (unfold F13e; oout).
    assert (G13 : mem_grows mem0 (F13e regs)) by (unfold F13e; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
    (* [comment removed for export] *)
    assert (S1 : exists r1, msteps ASEGS (mkst regs (0x5d7e0 : word) mem0 rom) (mkst r1 (0x838e4 : word) (F13e regs) rom)
              /\ (getr r1 9 = Z_to_bv 64 sparg /\ getr r1 25 = Z_to_bv 64 fs /\ getr r1 4 = Z_to_bv 64 tpv /\ getr r1 2 = Z_to_bv 64 (t - 144)
                  /\ getr r1 1 = (0x5d824 : word) /\ keeps_but [1; 2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv regs r1)).
    { unfold F13e. eexists. split.
      - stepiv F_5d3c8 D_5d3c8 (Z_to_bv 64 (t - 144)) ltac:(wval).                                       (* [comment removed for export] *)
        stepsd F_5d3cc D_5d3cc (Z_to_bv 64 (t - 8)) ra ltac:(sok).                                          (* [comment removed for export] *)
        stepsd F_5d3d0 D_5d3d0 (Z_to_bv 64 (t - 16)) (getr regs 8) ltac:(sok).
        stepsd F_5d3d4 D_5d3d4 (Z_to_bv 64 (t - 24)) (getr regs 9) ltac:(sok).
        stepsd F_5d3d8 D_5d3d8 (Z_to_bv 64 (t - 32)) (getr regs 18) ltac:(sok).
        stepsd F_5d3dc D_5d3dc (Z_to_bv 64 (t - 40)) (getr regs 19) ltac:(sok).
        stepsd F_5d3e0 D_5d3e0 (Z_to_bv 64 (t - 48)) (getr regs 20) ltac:(sok).
        stepsd F_5d3e4 D_5d3e4 (Z_to_bv 64 (t - 56)) (getr regs 21) ltac:(sok).
        stepsd F_5d3e8 D_5d3e8 (Z_to_bv 64 (t - 64)) (getr regs 22) ltac:(sok).
        stepsd F_5d3ec D_5d3ec (Z_to_bv 64 (t - 72)) (getr regs 23) ltac:(sok).
        stepsd F_5d3f0 D_5d3f0 (Z_to_bv 64 (t - 80)) (getr regs 24) ltac:(sok).
        stepsd F_5d3f4 D_5d3f4 (Z_to_bv 64 (t - 88)) (getr regs 25) ltac:(sok).
        stepsd F_5d3f8 D_5d3f8 (Z_to_bv 64 (t - 96)) (getr regs 26) ltac:(sok).
        stepsd F_5d3fc D_5d3fc (Z_to_bv 64 (t - 104)) (getr regs 27) ltac:(sok).                           (* [comment removed for export] *)
        stepiv F_5d400 D_5d400 (Z_to_bv 64 sparg) ltac:(wval).                                           (* [comment removed for export] *)
        stepiv F_5d404 D_5d404 (Z_to_bv 64 fs) ltac:(wval).                                              (* [comment removed for export] *)
        stepn F_5d408 D_5d408.                                                                             (* [comment removed for export] *)
        apply mst_refl.
      - repeat split; gres; rwH; try reflexivity; try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
    destruct S1 as (r1 & RUN1 & Q9 & Q25 & Q4 & Q2 & Q1 & K1).
    (* [comment removed for export] *)
    destruct (get_current_thread_run r1 (F13e regs) rom (0x5d824 : word) (t - 144) tpv key tsd ctx th Q2 Q4 Q1 Hra ltac:(lia) ltac:(lia) Htp Hkey Htsd Hctx ltac:(lia)
                ltac:(replace (t - 144 - 16)%Z with (t - 160)%Z by lia; unfold F13e; sok)) as (r2 & RUN2 & T10 & T2 & T1 & K2).
    { intros M' HM'. assert (O' : forall x : word, (bv_unsigned x < t - 160 \/ t <= bv_unsigned x)%Z -> M' x = mem0 x).
      { intros x Hx. rewrite (HM' x) by lia. apply O13. exact Hx. }
      destruct (HCE M' O') as (C1 & C2 & C3 & C4 & C5 & _). repeat split; assumption. }
    set (M14 := wbytes (F13e regs) (Z_to_bv 64 (t - 144 - 8)) (word_to_le_bytes 8 (0x5d824 : word))) in RUN2.
    assert (O14 : forall x : word, (bv_unsigned x < t - 160 \/ t <= bv_unsigned x)%Z -> M14 x = mem0 x).
    { intros x Hx. rewrite <- (O13 x Hx). unfold M14. revert x Hx. oout. }
    assert (G14 : mem_grows mem0 M14) by (unfold M14; eapply mem_grows_trans; [exact G13 | apply wbytes_grows]).
    assert (T9 : getr r2 9 = Z_to_bv 64 sparg) by (rewrite (K2 9%bv) by kbt; exact Q9).
    assert (T25 : getr r2 25 = Z_to_bv 64 fs) by (rewrite (K2 25%bv) by kbt; exact Q25).
    assert (T4 : getr r2 4 = Z_to_bv 64 tpv) by (rewrite (K2 4%bv) by kbt; exact Q4).
    destruct (HCE M14 O14) as (_ & _ & _ & _ & _ & D40 & D8 & D16).
    assert (S3 : exists r3, msteps ASEGS (mkst r2 (0x5d824 : word) M14 rom) (mkst r3 (0x5da8c : word) M14 rom)
              /\ (getr r3 2 = Z_to_bv 64 (t - 144) /\ keeps_but [1; 2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv r2 r3)).
    { eexists. split.
      - stepb_ft F_5d40c D_5d40c ltac:(cond).                                                              (* [comment removed for export] *)
        stepiv F_5d410 D_5d410 (Z_to_bv 64 th) ltac:(wval).                                               (* [comment removed for export] *)
        stepn F_5d414 D_5d414.                                                                             (* [comment removed for export] *)
        mlbq F_83690 D_83690 (th + 40)%Z D40.                                                               (* [comment removed for export] *)
        stepfence F_83694 D_83694.
        stepb_tk F_83698 D_83698 ltac:(rwH; cbn; cond).                                                    (* [comment removed for export] *)
        mldq F_836d0 D_836d0 (th + 8)%Z D8.                                                                 (* [comment removed for export] *)
        mldq F_836d4 D_836d4 (th + 16)%Z D16.                                                               (* [comment removed for export] *)
        stepov F_836d8 D_836d8 (Z_to_bv 64 1) ltac:(gres; rwH; unfold v_sltu, c_ltu, bv_ltu; unorm; replace (botth <? top)%Z with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).  (* [comment removed for export] *)
        stepn F_836dc D_836dc.                                                                             (* [comment removed for export] *)
        stepov F_836e0 D_836e0 (Z_to_bv 64 top) ltac:(gres; rwH; unfold v_and; imm_norm; unorm; rewrite Z.land_comm; change 18446744073709551615%Z with (Z.ones 64); rewrite Z.land_ones by lia; f_equal; apply Z.mod_small; lia).  (* [comment removed for export] *)
        stepret F_836e4 D_836e4 (0x5d830 : word) ltac:(rwH; first [reflexivity | apply bv_eq; vm_compute; reflexivity]).
        stepiv F_5d418 D_5d418 (Z_to_bv 64 top) ltac:(wval).                                              (* [comment removed for export] *)
        stepiv F_5d41c D_5d41c (Z_to_bv 64 th) ltac:(wval).                                               (* [comment removed for export] *)
        stepn F_5d420 D_5d420.                                                                             (* [comment removed for export] *)
        mlbq F_836e8 D_836e8 (th + 40)%Z D40.                                                               (* [comment removed for export] *)
        stepfence F_836ec D_836ec.
        stepb_tk F_836f0 D_836f0 ltac:(rwH; cbn; cond).                                                    (* [comment removed for export] *)
        mldq F_83728 D_83728 (th + 8)%Z D8.                                                                 (* [comment removed for export] *)
        mldq F_8372c D_8372c (th + 16)%Z D16.                                                               (* [comment removed for export] *)
        stepov F_83730 D_83730 (Z_to_bv 64 1) ltac:(gres; rwH; unfold v_sltu, c_ltu, bv_ltu; unorm; replace (botth <? top)%Z with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).  (* [comment removed for export] *)
        stepn F_83734 D_83734.                                                                             (* [comment removed for export] *)
        stepov F_83738 D_83738 (Z_to_bv 64 botth) ltac:(gres; rwH; unfold v_and; imm_norm; unorm; change 18446744073709551615%Z with (Z.ones 64); rewrite Z.land_comm; rewrite Z.land_ones by lia; f_equal; apply Z.mod_small; lia).  (* [comment removed for export] *)
        stepret F_8373c D_8373c (0x5d83c : word) ltac:(rwH; first [reflexivity | apply bv_eq; vm_compute; reflexivity]).
        stepb_tk F_5d424 D_5d424 ltac:(cond).                                                              (* [comment removed for export] *)
        apply mst_refl.
      - split; [gres; rwH; reflexivity | solve_keeps_but]. }
    destruct S3 as (r3 & RUN3 & J2 & K3).
    assert (SL : forall k v, (k = 8 /\ v = ra \/ k = 16 /\ v = getr regs 8 \/ k = 24 /\ v = getr regs 9 \/ k = 32 /\ v = getr regs 18 \/ k = 40 /\ v = getr regs 19 \/ k = 48 /\ v = getr regs 20 \/ k = 56 /\ v = getr regs 21 \/ k = 64 /\ v = getr regs 22 \/ k = 72 /\ v = getr regs 23 \/ k = 80 /\ v = getr regs 24 \/ k = 88 /\ v = getr regs 25 \/ k = 96 /\ v = getr regs 26 \/ k = 104 /\ v = getr regs 27)%Z ->
                 rdn ASEGS M14 (Z_to_bv 64 (t - k)) 8%nat = Some (word_to_le_bytes 8 v)).
    { intros k v Hk. assert (Hk' : (8 <= k <= 104)%Z) by lia.
      unfold M14, F13e. destruct Hk as [[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]]]]]]]]]]];
          repeat (rewrite rdn_wbytes_out; [ | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; (clear - t; lia) | cbn [Z.of_nat Pos.to_nat]; unorm; (clear - Ht t; lia) | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; (clear - Ht t; lia) ]);
          apply rdn_wbytes_hit8; unorm; (clear - Ht t; lia). }
    #[local] Ltac slv := first [split; reflexivity | left; split; reflexivity | right; slv].
    eexists. exists M14. split.
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|].
      stepld F_5d674 D_5d674 (ra) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (t - 8)) by (symmetry; wval) end; apply SL; slv).
      stepld F_5d678 D_5d678 (getr regs 8) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (t - 16)) by (symmetry; wval) end; apply SL; slv).
      stepld F_5d67c D_5d67c (getr regs 9) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (t - 24)) by (symmetry; wval) end; apply SL; slv).
      stepld F_5d680 D_5d680 (getr regs 18) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (t - 32)) by (symmetry; wval) end; apply SL; slv).
      stepld F_5d684 D_5d684 (getr regs 19) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (t - 40)) by (symmetry; wval) end; apply SL; slv).
      stepld F_5d688 D_5d688 (getr regs 20) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (t - 48)) by (symmetry; wval) end; apply SL; slv).
      stepld F_5d68c D_5d68c (getr regs 21) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (t - 56)) by (symmetry; wval) end; apply SL; slv).
      stepld F_5d690 D_5d690 (getr regs 22) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (t - 64)) by (symmetry; wval) end; apply SL; slv).
      stepld F_5d694 D_5d694 (getr regs 23) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (t - 72)) by (symmetry; wval) end; apply SL; slv).
      stepld F_5d698 D_5d698 (getr regs 24) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (t - 80)) by (symmetry; wval) end; apply SL; slv).
      stepld F_5d69c D_5d69c (getr regs 25) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (t - 88)) by (symmetry; wval) end; apply SL; slv).
      stepld F_5d6a0 D_5d6a0 (getr regs 26) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (t - 96)) by (symmetry; wval) end; apply SL; slv).
      stepld F_5d6a4 D_5d6a4 (getr regs 27) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (t - 104)) by (symmetry; wval) end; apply SL; slv).
      stepiv F_5d6a8 D_5d6a8 (Z_to_bv 64 t) ltac:(wval).                                                  (* [comment removed for export] *)
      stepret F_5d6ac D_5d6ac ra ltac:(rwH; reflexivity).
      apply mst_refl.
    - split; [gres; symmetry; apply sp_sge|]. split; [gres; reflexivity|]. split; [|split; [exact O14 | exact G14]].
      intros r Hcs. cbv in Hcs.
      destruct Hcs as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]]]; gres;
        first [ reflexivity | rewrite H1; reflexivity | rewrite H2; reflexivity
              | rewrite (K3 _) by kbt; rewrite (K2 _) by kbt; rewrite (K1 _) by kbt; reflexivity ].
  Qed.
End EARLY.
End FPX_1.
