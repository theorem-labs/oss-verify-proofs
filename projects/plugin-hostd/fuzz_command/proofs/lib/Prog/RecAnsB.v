From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0o YK0s YK14 YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Mem Cells Step.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import MState.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0 Contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv RecInvP RecKindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require snprintf_c.
Import ListNotations.
Local Open Scope Z_scope.

Lemma eqv_mkst_fx : forall R F pc fc m ro ms, Regs6ss.ms_eqv (MS R F pc fc None m ro) ms ->
  exists R', ms = @mkst (mkFP F fc) R' pc m ro /\ Regs6ss.xregs_eqv R R'.
Proof.
  intros R F pc fc m ro [r f p sv rv c mm o] (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
  cbn in *. subst. exists r. split; [reflexivity | exact H1].
Qed.

Lemma guard_wview : forall (m : word -> option byte) i, 0 <= i < 8 ->
  wview rsegs m (Mem.wa (snprintf_c.GOT_GUARD + i)) <> None /\ wview rsegs m (Mem.wa (snprintf_c.GUARD + i)) <> None.
Proof.
  intros m i Hi. unfold snprintf_c.GOT_GUARD, snprintf_c.GUARD.
  assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
  repeat (destruct C as [C|C]; [subst i; unfold wview;
    split; (match goal with |- context [m ?x] => destruct (m x) end; [discriminate | vm_compute; discriminate])|]).
  subst i. unfold wview.
  split; (match goal with |- context [m ?x] => destruct (m x) end; [discriminate | vm_compute; discriminate]).
Qed.

Lemma Z_to_le_bytes_nth : forall n z k, (k < n)%nat ->
  nth_error (Z_to_le_bytes n z) k = Some (Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k))).
Proof.
  induction n as [|n IH]; intros z k Hk; [lia|]. destruct k as [|k]; cbn [Z_to_le_bytes nth_error].
  - replace (8 * Z.of_nat 0) with 0 by lia. rewrite Z.shiftr_0_r. reflexivity.
  - rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. do 3 f_equal. lia.
Qed.

Lemma word_mem_le8 : forall segs m a g, 0 <= a -> a + 8 <= 2 ^ 64 -> 0 <= g < 2 ^ 64 ->
  word_mem segs m a g -> Mem.bytes_at segs m a (Mem.le8 (Z_to_bv 64 g)).
Proof.
  intros segs m a g Ha Hb Hg W. split; [lia|]. split; [rewrite Mem.length_le8; lia|].
  intros i Hi. rewrite Mem.length_le8 in Hi. pose proof (W i Hi) as E.
  change (Mem.mrd segs m (Mem.wa (a + Z.of_nat i))) with (mbyte segs m (a + Z.of_nat i)). rewrite E.
  unfold Mem.le8, word_to_le_bytes. rewrite unsigned_lit by lia. rewrite Z_to_le_bytes_nth by lia.
  f_equal. apply Mem.Z_to_bv8_mod. unfold le_byte.
  replace (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) by reflexivity. rewrite (Z.mod_small g) by lia.
  change (2 ^ 8) with 256. apply Z.mod_mod. lia.
Qed.

Lemma f18_words_after : forall (m m' : word -> option byte) g,
  f18_words rsegs m ->
  (forall i, 0 <= i < 8 -> mbyte rsegs m' (snprintf_c.GOT_GUARD + i) = mbyte rsegs m (snprintf_c.GOT_GUARD + i)) ->
  0 <= g < 2 ^ 64 -> word_mem rsegs m' snprintf_c.GUARD g ->
  f18_words rsegs m'.
Proof.
  intros m m' g [[[_ HB] _] _] HK Hg HW. unfold f18_words. split.
  - split; [split; [cbn; split; exact I|]|].
    + cbn [Cells.cells_bytes Cells.cbytes] in HB |- *. rewrite app_nil_r in HB |- *.
      apply (bytes_at_transfer rsegs m); [exact HB|]. intros i Hi. rewrite Mem.length_le8 in Hi. apply HK. lia.
    + split; [unfold snprintf_c.GOT_GUARD; lia|]. split; [cbn; unfold snprintf_c.GOT_GUARD; lia|].
      intros i Hi. cbn in Hi. exact (proj1 (guard_wview m' i Hi)).
  - exists (Z_to_bv 64 g). split; [split; [cbn; split; exact I|]|].
    + cbn [Cells.cells_bytes Cells.cbytes]. rewrite app_nil_r.
      apply word_mem_le8; [unfold snprintf_c.GUARD; lia | unfold snprintf_c.GUARD; lia | exact Hg | exact HW].
    + split; [unfold snprintf_c.GUARD; lia|]. split; [cbn; unfold snprintf_c.GUARD; lia|].
      intros i Hi. cbn in Hi. exact (proj2 (guard_wview m' i Hi)).
Qed.

Lemma call_at_blocks : forall segs bl mem a c P pn, call_at segs bl mem a c P -> In pn P -> In pn bl.
Proof.
  intros segs bl mem a c P pn (_ & _ & HL & _ & _ & _ & HK) Hin.
  apply In_nth_error in Hin as (k & Ek).
  assert (Hk : (k < length (snd c))%nat) by (rewrite <- HL; apply nth_error_Some; rewrite Ek; discriminate).
  destruct (nth_error (snd c) k) as [s|] eqn:Es; [|apply nth_error_None in Es; lia].
  exact (proj1 (proj2 (proj2 (HK k s pn Es Ek)))).
Qed.

Lemma rec_rep_O_blocks : forall segs gr sc L A mem R O pn,
  rec_rep segs gr sc L A mem R O -> In pn O -> In pn (blocks L A).
Proof.
  intros segs gr sc L A mem R O pn (Q & HR & HO) Hin. apply HO in Hin.
  destruct HR as (HS & HC & HA & HP & HX & HW).
  destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
  unfold lay_blocks in Hin. apply in_app_or in Hin as [Hin|Hin].
  - apply in_concat in Hin as (P & HP' & Hpn). apply In_nth_error in HP' as (i & EP).
    destruct (nth_error (r_calls R) i) as [c|] eqn:Ec.
    + exact (call_at_blocks _ _ _ _ _ _ _ (proj1 (C4 i c P Ec EP)) Hpn).
    + exfalso. apply nth_error_None in Ec.
      assert (i < length (l_calls Q))%nat by (apply nth_error_Some; rewrite EP; discriminate). lia.
  - apply in_app_or in Hin as [Hin|Hin]; [exact (call_at_blocks _ _ _ _ _ _ _ C5 Hin)|].
    apply in_app_or in Hin as [Hin|Hin].
    + unfold answer_at in HA. destruct (l_answer Q) as [pn'|]; cbn in Hin; [|contradiction].
      destruct Hin as [<-|[]]. destruct (r_answer R); [exact (proj1 (proj2 (proj2 HA)))|contradiction].
    + unfold reply_at in HP. destruct (l_reply Q) as [pn'|]; cbn in Hin; [|contradiction].
      destruct Hin as [<-|[]]. destruct (r_reply R); [exact (proj1 (proj2 (proj2 (proj2 (proj2 HP)))))|contradiction].
Qed.

Lemma free_users_incl : forall {T : Type} (U2 U3 : list (T * Z)) (f2 f3 : T -> Z) p n b1 b2,
  List.NoDup (map fst U2) -> In (p, n) U2 ->
  map (fun e => (f2 (fst e), snd e)) U2 = b1 ++ (f2 p, n) :: b2 ->
  map (fun e => (f3 (fst e), snd e)) U3 = b1 ++ b2 ->
  (forall q k, In (q, k) U2 -> q <> p -> In (q, k) U3) ->
  incl U3 U2.
Proof.
  intros T U2 U3 f2 f3 p n b1 b2 ND Hin E2 E3 K.
  apply in_split in Hin as (l1 & l2 & ->).
  assert (ND2 : List.NoDup (l1 ++ (p, n) :: l2)) by (eapply NoDup_map_inv; exact ND).
  assert (NP : ~ In p (map fst (l1 ++ l2))).
  { rewrite map_app in ND |- *. cbn [map fst] in ND. apply NoDup_remove_2 in ND. exact ND. }
  assert (LL : length U3 = length (l1 ++ l2)).
  { assert (H2 := f_equal (@length _) E2). assert (H3 := f_equal (@length _) E3).
    rewrite length_map in H2, H3. rewrite length_app in H2. rewrite length_app in H2. rewrite length_app in H3.
    rewrite length_app. cbn [length] in H2. lia. }
  assert (INC : incl (l1 ++ l2) U3).
  { intros [q k] Hqk. apply K.
    - apply in_app_or in Hqk. apply in_or_app. destruct Hqk as [H|H]; [left; exact H | right; right; exact H].
    - intros ->. apply NP. apply in_map_iff. exists (p, k). split; [reflexivity | exact Hqk]. }
  intros e He.
  assert (LE : (length U3 <= length (l1 ++ l2))%nat) by (rewrite LL; apply le_n).
  pose proof (@NoDup_length_incl (T * Z) (l1 ++ l2) U3 (NoDup_remove_1 _ _ _ ND2) LE INC e He) as H.
  apply in_app_or in H. apply in_or_app. destruct H as [H|H]; [left; exact H | right; right; exact H].
Qed.

Lemma in_mid_other : forall {X : Type} (b1 b2 : list X) x y, In y (b1 ++ x :: b2) -> y <> x -> In y (b1 ++ b2).
Proof.
  intros X b1 b2 x y H N. apply in_app_or in H. apply in_or_app.
  destruct H as [H|[H|H]]; [left; exact H | congruence | right; exact H].
Qed.

Lemma in_mid_inv : forall {X : Type} (b1 b2 : list X) x y, In y (b1 ++ b2) -> In y (b1 ++ x :: b2).
Proof.
  intros X b1 b2 x y H. apply in_app_or in H. apply in_or_app.
  destruct H as [H|H]; [left; exact H | right; right; exact H].
Qed.

Lemma with_vmmaps_twice' : forall v1 v2 md, with_vmmaps v2 (with_vmmaps v1 md) = with_vmmaps v2 md.
Proof. intros v1 v2 md. destruct md as [f [mp lz mt] io fs pr li ti]. reflexivity. Qed.

Section Own.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable MR : MR_t.
Hypothesis LAWS : MR_laws B MR.
Hypothesis AXM : AllocExtra B MR.
Hypothesis CTXM : forall L A mem md a, MR L A mem md -> ms_ctx B <= a < ms_ctx B + CTX_SIZE -> owned B L A a.

Lemma not_owned_mid : forall L A mem md L2 A2 mem2 md2 a, MR L A mem md -> MR L2 A2 mem2 md2 ->
  (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) -> ~ owned B L A a -> ~ owned B L2 A2 a.
Proof using LAWS AXM CTXM.
  intros L A mem md L2 A2 mem2 md2 a H1 H2 Hd N1 [Ha|Hs]; [|apply N1; right; exact Hs].
  destruct Hd as [Hd|Hd].
  - pose proof (mr_owned_low B MR LAWS L2 A2 mem2 md2 a H2 (or_introl Ha)). lia.
  - apply N1. apply (CTXM L A mem md a H1). exact (ax_img AXM L2 A2 mem2 md2 a H2 Hd Ha).
Qed.

End Own.
