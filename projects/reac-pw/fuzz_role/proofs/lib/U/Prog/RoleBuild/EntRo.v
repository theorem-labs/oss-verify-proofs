(** The UBSan ent_build walk's .rodata sources: a string of the image and the frame's locals lie apart (memcpy's
    disjointness premise), from the image bytes on one side and the stack region outside the image on the other. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require Import Tac Image.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Tables Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Prog.RoleBuild Require Import EntCut EntFacts.
Import ListNotations.
Open Scope Z_scope.

(** Two runs of addresses, one outside the image and one inside it, do not overlap. *)
Lemma rom_disj : forall a n p k, 0 < n -> 0 < k ->
  (forall i, 0 <= i < n -> seg_rom rsegs (wa (a + i)) = None) ->
  (forall j, 0 <= j < k -> seg_rom rsegs (wa (p + j)) <> None) ->
  a + n <= p \/ p + k <= a.
Proof.
  intros a n p k Hn Hk HA HP.
  destruct (Z.le_gt_cases (a + n) p) as [H|H]; [left; exact H|].
  destruct (Z.le_gt_cases (p + k) a) as [H'|H']; [right; exact H'|].
  exfalso. destruct (Z.le_gt_cases a p) as [Hap|Hap].
  - apply (HP 0 ltac:(lia)). rewrite Z.add_0_r. replace p with (a + (p - a)) by lia. apply HA. lia.
  - apply (HP (a - p) ltac:(lia)). replace (p + (a - p)) with (a + 0) by lia. apply HA. lia.
Qed.

(** The bytes ro_bytes_b checks are in the image. *)
Lemma ro_bytes_b_rom : forall bs A j, ro_bytes_b rsegs A bs = true -> 0 <= j < Z.of_nat (length bs) ->
  seg_rom rsegs (wa (A + j)) <> None.
Proof.
  induction bs as [|x bs IH]; intros A j H Hj; cbn [length] in Hj; [lia|].
  cbn [ro_bytes_b] in H. destruct (seg_rom rsegs (wa A)) as [y|] eqn:E; [|discriminate].
  apply andb_prop in H as [_ H]. destruct (Z.eq_dec j 0) as [->|Hj0].
  - rewrite Z.add_0_r, E. discriminate.
  - replace (A + j) with (A + 1 + (j - 1)) by lia. apply IH; [exact H | lia].
Qed.

Lemma rostr_rom : forall p s j, rostr_ok p s = true -> 0 <= j < Z.of_nat (length s) + 1 ->
  seg_rom rsegs (wa (p + j)) <> None.
Proof.
  intros p s j H Hj. unfold rostr_ok in H. repeat rewrite andb_true_iff in H.
  destruct H as (((((_ & H2) & _) & _) & _) & _).
  apply (ro_bytes_b_rom _ p j H2). rewrite length_app. cbn [length]. lia.
Qed.

Section Apart.
Variables (sp : word) (m : word -> option byte) (r : list byte) (src pp lo : Z).
Hypothesis HE : ent_pre sp m r src pp lo.

(** A run of n <= |s| + 1 bytes of the frame's locals and the first n bytes of the .rodata string s at p. *)
Lemma ro_apart : forall p s a (n : Z), rostr_ok p s = true -> 0 < n -> n <= Z.of_nat (length s) + 1 ->
  bv_unsigned sp + 0xb8 <= a -> a + n <= bv_unsigned sp + FRAME_LOCALS ->
  p + n <= a \/ a + n <= p.
Proof.
  intros p s a n Hok Hn Hl H1 H2. pose proof (ep_range sp m r src pp lo HE) as R.
  destruct (rom_disj a n p n Hn Hn) as [X|X]; [ | | right; exact X | left; exact X ].
  - intros i Hi. apply (ep_rom sp m r src pp lo HE). unfold FRAME_LOCALS in *. lia.
  - intros j Hj. apply (rostr_rom p s j Hok). lia.
Qed.

End Apart.
