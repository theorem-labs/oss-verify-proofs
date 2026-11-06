From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import Contract.
Import ListNotations.
Local Open Scope Z_scope.

Definition G_LIVE : Z := 0x2f620.
Definition G_PEAK : Z := 0x2f628.
Definition G_COUNT : Z := 0x2f630.
Definition G_FAIL : Z := 0x1f3a8.

Fixpoint lsum (Lam : list (Z * Z)) : Z :=
  match Lam with
  | [] => 0
  | (_, k) :: r => k + lsum r
  end.

Definition alloc_statics (a : Z) : Prop :=
  G_LIVE <= a < G_LIVE + 8 \/ G_PEAK <= a < G_PEAK + 8 \/ G_COUNT <= a < G_COUNT + 8 \/ G_FAIL <= a < G_FAIL + 8.

Section Ledger.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Let segs := ms_segs B.

Definition alloc_words (mem : word -> option byte) (live peak cnt fail : Z) : Prop :=
  word_mem segs mem G_LIVE live /\ word_mem segs mem G_PEAK peak /\
  word_mem segs mem G_COUNT cnt /\ word_mem segs mem G_FAIL fail.

Definition lblock (L : layout) (A : astate) (mem : word -> option byte) (a k : Z) : Prop :=
  0 <= k /\ In (a - 16, k + 16) (blocks L A) /\ word_mem segs mem (a - 16) k /\
  (forall i, 0 <= i < k + 16 -> ~ in_img B (a - 16 + i)).

Definition ledger (L : layout) (A : astate) (mem : word -> option byte) (Lam : list (Z * Z))
    (peak cnt fail : Z) : Prop :=
  alloc_words mem (lsum Lam) peak cnt fail /\
  lsum Lam <= peak < 2 ^ 64 /\ 0 <= cnt < 2 ^ 64 /\ 0 <= fail < 2 ^ 64 /\
  NoDup (map fst Lam) /\
  Forall (fun ak => lblock L A mem (fst ak) (snd ak)) Lam.

Definition ublocks_kept (L : layout) (A A' : astate) (gone : Z * Z) : Prop :=
  forall q k, In (q, k) (user_blocks A) -> (ptr_addr L q, k) <> gone -> In (q, k) (user_blocks A').

Definition writes_only (W : Z -> Prop) (mem mem' : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ W a -> mbyte segs mem' a = mbyte segs mem a.

Definition keeps (L : layout) (A : astate) (mem mem' : word -> option byte) (gone : Z) : Prop :=
  forall a k i, In (a, k) (blocks L A) -> a <> gone -> 0 <= i < k -> mbyte segs mem' (a + i) = mbyte segs mem (a + i).

Definition omx_GI (j : nat) (mem : word -> option byte) : Prop :=
  exists peak cnt, alloc_words mem 0 peak cnt (2 ^ 64 - 1) /\ 0 <= peak < 2 ^ 64 /\ 0 <= cnt <= Z.of_nat j * 2 ^ 60 /\ cnt <= 2 ^ 62.

Lemma omx_GI_ledger : forall j mem L A, omx_GI j mem ->
  exists peak cnt, ledger L A mem [] peak cnt (2 ^ 64 - 1) /\ 0 <= cnt <= Z.of_nat j * 2 ^ 60.
Proof.
  intros j mem L A (peak & cnt & HW & HP & HC & HC2).
  exists peak, cnt. split; [|exact HC].
  unfold ledger. cbn [lsum map]. split; [exact HW|].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [constructor|constructor].
Qed.

End Ledger.

Section LedgerFacts.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.

Lemma lblock_user : forall L A mem a k, lblock B L A mem a k ->
  exists q, In (q, k + 16) (user_blocks A) /\ ptr_addr L q = a - 16.
Proof.
  intros L A mem a k (_ & Hin & _). unfold blocks in Hin. apply in_map_iff in Hin.
  destruct Hin as ([q n] & E & Hq). cbn [fst snd] in E. injection E as E1 E2.
  exists q. subst n. split; [exact Hq | exact E1].
Qed.

Lemma ledger_block_range : forall L A mem md Lam peak cnt fail a k,
  aa_MR API L A mem md -> ledger B L A mem Lam peak cnt fail -> In (a, k) Lam ->
  4112 <= a /\ a + k <= alloc_ceiling /\ a + k < 2 ^ 47.
Proof.
  intros L A mem md Lam peak cnt fail a k HM HL Hin.
  destruct HL as (_ & _ & _ & _ & _ & HF). rewrite Forall_forall in HF. specialize (HF _ Hin). cbn [fst snd] in HF.
  destruct (lblock_user _ _ _ _ _ HF) as (q & Hq & Ep).
  pose proof (mr_blocks_range _ _ (aa_laws API) _ _ _ _ q (k + 16) HM Hq) as R. rewrite Ep in R.
  pose proof alloc_ceiling_lt. lia.
Qed.

Lemma ledger_block_present : forall L A mem md Lam peak cnt fail a k i,
  aa_MR API L A mem md -> ledger B L A mem Lam peak cnt fail -> In (a, k) Lam -> 0 <= i < k ->
  present mem (a + i).
Proof.
  intros L A mem md Lam peak cnt fail a k i HM HL Hin Hi.
  destruct HL as (_ & _ & _ & _ & _ & HF). rewrite Forall_forall in HF. specialize (HF _ Hin). cbn [fst snd] in HF.
  destruct (lblock_user _ _ _ _ _ HF) as (q & Hq & Ep).
  destruct (mr_blocks _ _ (aa_laws API) _ _ _ _ q (k + 16) (i + 16) HM Hq ltac:(lia)) as (P & _).
  rewrite Ep in P. replace (a - 16 + (i + 16)) with (a + i) in P by lia. exact P.
Qed.

Lemma present_writable : forall mem a, present mem a -> writable_at (ms_segs B) mem a.
Proof.
  intros mem a (b & Hb). unfold writable_at, wview. rewrite Hb. discriminate.
Qed.

Lemma ledger_block_not_img : forall L A mem Lam peak cnt fail a k i,
  ledger B L A mem Lam peak cnt fail -> In (a, k) Lam -> -16 <= i < k -> ~ in_img B (a + i).
Proof.
  intros L A mem Lam peak cnt fail a k i HL Hin Hi.
  destruct HL as (_ & _ & _ & _ & _ & HF). rewrite Forall_forall in HF. specialize (HF _ Hin). cbn [fst snd] in HF.
  destruct HF as (_ & _ & _ & HI). replace (a + i) with (a - 16 + (i + 16)) by lia. apply HI. lia.
Qed.

Lemma ledger_block_aligned : forall L A mem md Lam peak cnt fail a k,
  aa_MR API L A mem md -> ledger B L A mem Lam peak cnt fail -> In (a, k) Lam -> a mod 16 = 0.
Proof.
  intros L A mem md Lam peak cnt fail a k HM HL Hin.
  destruct HL as (_ & _ & _ & _ & _ & HF). rewrite Forall_forall in HF. specialize (HF _ Hin). cbn [fst snd] in HF.
  destruct (lblock_user _ _ _ _ _ HF) as (q & Hq & Ep).
  pose proof (mr_blocks_aligned _ _ (aa_laws API) _ _ _ _ q (k + 16) HM Hq) as R. rewrite Ep in R.
  replace a with (a - 16 + 1 * 16) by lia. rewrite Z_mod_plus_full. exact R.
Qed.

Lemma ledger_frame : forall L A L' A' mem mem' Lam peak cnt fail,
  ledger B L A mem Lam peak cnt fail ->
  (forall a k, In (a, k) Lam -> In (a - 16, k + 16) (blocks L' A')) ->
  (forall x, alloc_statics x \/ (exists a k, In (a, k) Lam /\ a - 16 <= x < a - 8) ->
     mbyte (ms_segs B) mem' x = mbyte (ms_segs B) mem x) ->
  ledger B L' A' mem' Lam peak cnt fail.
Proof.
  intros L A L' A' mem mem' Lam peak cnt fail HL Hbl Hm.
  destruct HL as ((W1 & W2 & W3 & W4) & HP & HC & HFl & HN & HF).
  assert (WF : forall g v, word_mem (ms_segs B) mem g v ->
    (forall k, (k < 8)%nat -> alloc_statics (g + Z.of_nat k) \/
       (exists a kk, In (a, kk) Lam /\ a - 16 <= g + Z.of_nat k < a - 8)) ->
    word_mem (ms_segs B) mem' g v).
  { intros g v Hw Hin k Hk. rewrite Hm by (apply Hin; exact Hk). exact (Hw k Hk). }
  split; [|split; [exact HP|split; [exact HC|split; [exact HFl|split; [exact HN|]]]]].
  - unfold alloc_words.
    repeat split; apply WF; try assumption; intros k Hk; left;
      unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL; lia.
  - rewrite Forall_forall in HF |- *. intros [a k] Hin. specialize (HF _ Hin). cbn [fst snd] in HF |- *.
    destruct HF as (Hk & Hb & Hw & Hi). split; [exact Hk|]. split; [exact (Hbl a k Hin)|]. split; [|exact Hi].
    apply WF; [exact Hw|]. intros j Hj. right. exists a, k. split; [exact Hin|]. lia.
Qed.

End LedgerFacts.
