(* reac-pw/fuzz_link, image A: wrapper_strcmp (0x4304c) as a step of the caller's program-global journal
   `ajournal_gx G XO OUT` (lib/A/W_journalG.v), over the stop-index contract of lib/Reusable/AStrcmpDef.v
   (`astrcmp_realizes`: the wrapper compares byte by byte up to the first index k where the bytes differ or the
   first string's byte is 0, reads [x, x + k + 1) and [y, y + k + 1) only, and answers CharCmpX of the two bytes
   at k). lib/A/Prog/LinkWalk.v's `aj_gx_strcmp_at` lifts the OTHER strcmp form (lib/A/Rt/RtString.v, over whole
   C strings), whose `atail_vis` premises the own-function contracts do not give; this file lifts the form the
   contracts were written against.

   Section s: `aj_gx_astrcmp_at`, the lift itself, over lib/A/Prog/link_ajkit.v `aj_gx_call_at` with the wrapper's
   window w := 2 * ESTACK and no cells (Eb := fun _ => False). Its ecall-pre premises come from the caller's
   journal through `aj_gx_ecall_pre`, exactly as LinkWalk.v's aj_gx_strcmp_at derives them; the remaining premises
   (the stop index, the two reads, the two strings outside the window, the addressability of the read ranges) are
   the contract's own and the caller's walk supplies them.

   Sections l and c: `astrcmp_cstr_meet`, the shape every caller of the wrapper in link has: two C strings
   (`acstr_at`), compared whole. It produces the stop index k and the two bytes at it, bounds k by the length of
   either string (so the caller's premises over [p, p + |s| + 1) contain the range the wrapper reads), and says
   that the answer word is 0 exactly when the two byte lists are equal. The walks of fuzz_if_nametoindex /
   index_of, model_decide, check_read, check_marks, remember and reac_served_decide all use this pair.

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import AStrcmpDef.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_amem link_ajkit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ==========================================================================
   Section l: the stop index of two C strings, on byte lists alone
   ========================================================================== *)

(* the first index at which two byte lists differ, by byte value *)
Fixpoint lws_meet (l1 l2 : list byte) : nat :=
  match l1, l2 with
  | b1 :: t1, b2 :: t2 => if bv_unsigned b1 =? bv_unsigned b2 then S (lws_meet t1 t2) else 0%nat
  | _, _ => 0%nat
  end.

Lemma lws_meet_le1 : forall l1 l2, (lws_meet l1 l2 <= length l1)%nat.
Proof.
  induction l1 as [|b1 t1 IH]; intros [|b2 t2]; cbn [lws_meet length]; try lia.
  destruct (bv_unsigned b1 =? bv_unsigned b2); [pose proof (IH t2); lia | lia].
Qed.

Lemma lws_meet_le2 : forall l1 l2, (lws_meet l1 l2 <= length l2)%nat.
Proof.
  induction l1 as [|b1 t1 IH]; intros [|b2 t2]; cbn [lws_meet length]; try lia.
  destruct (bv_unsigned b1 =? bv_unsigned b2); [pose proof (IH t2); lia | lia].
Qed.

Lemma lws_meet_pre : forall l1 l2 i, (i < lws_meet l1 l2)%nat ->
  exists b1 b2, nth_error l1 i = Some b1 /\ nth_error l2 i = Some b2 /\ bv_unsigned b1 = bv_unsigned b2.
Proof.
  induction l1 as [|c1 t1 IH]; intros [|c2 t2] i Hi; cbn [lws_meet] in Hi; try lia.
  destruct (Z.eqb_spec (bv_unsigned c1) (bv_unsigned c2)) as [He|Hne]; [|lia].
  destruct i as [|i]; [exists c1, c2; cbn [nth_error]; auto|].
  cbn [nth_error]. apply IH. lia.
Qed.

Lemma lws_meet_at : forall l1 l2 b1 b2,
  nth_error l1 (lws_meet l1 l2) = Some b1 -> nth_error l2 (lws_meet l1 l2) = Some b2 ->
  bv_unsigned b1 <> bv_unsigned b2.
Proof.
  induction l1 as [|c1 t1 IH]; intros [|c2 t2] b1 b2 H1 H2; cbn [lws_meet] in H1, H2; try discriminate.
  destruct (Z.eqb_spec (bv_unsigned c1) (bv_unsigned c2)) as [He|Hne].
  - cbn [nth_error] in H1, H2. exact (IH t2 b1 b2 H1 H2).
  - cbn [nth_error] in H1, H2. injection H1 as <-. injection H2 as <-. exact Hne.
Qed.

Lemma lws_meet_eq : forall l1 l2,
  (lws_meet l1 l2 = length l1)%nat -> (lws_meet l1 l2 = length l2)%nat -> l1 = l2.
Proof.
  induction l1 as [|b1 t1 IH]; intros [|b2 t2] H1 H2; cbn [lws_meet length] in H1, H2;
    try (exfalso; lia); [reflexivity|].
  destruct (Z.eqb_spec (bv_unsigned b1) (bv_unsigned b2)) as [He|Hne]; [|lia].
  f_equal; [apply bv_eq; exact He | apply IH; lia].
Qed.

Lemma lws_zb0 : bv_unsigned (zb 0) = 0.
Proof. unfold zb. rewrite Z_to_bv_unsigned. reflexivity. Qed.

Lemma lws_nth_nul : forall (s : list byte), nth_error (s ++ [zb 0]) (length s) = Some (zb 0).
Proof. intros s. rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity. Qed.

(* the index at which the wrapper stops on two C strings: the first difference, or the NUL of the first *)
Definition lws_stop (sx sy : list byte) : nat :=
  Nat.min (lws_meet (sx ++ [zb 0]) (sy ++ [zb 0])) (length sx).

Lemma lws_stop_sx : forall sx sy, (lws_stop sx sy <= length sx)%nat.
Proof. intros sx sy. unfold lws_stop. lia. Qed.

Lemma lws_stop_pre : forall sx sy i, ~ In (zb 0) sx -> (i < lws_stop sx sy)%nat ->
  exists b, nth_error (sx ++ [zb 0]) i = Some b /\ nth_error (sy ++ [zb 0]) i = Some b /\ bv_unsigned b <> 0.
Proof.
  intros sx sy i HNx Hi. unfold lws_stop in Hi.
  destruct (lws_meet_pre (sx ++ [zb 0]) (sy ++ [zb 0]) i ltac:(lia)) as (b1 & b2 & H1 & H2 & He).
  exists b1. split; [exact H1|].
  split; [rewrite H2; f_equal; apply bv_eq; symmetry; exact He|].
  intros Hz. apply HNx.
  assert (Hlt : (i < length sx)%nat) by lia.
  rewrite nth_error_app1 in H1 by lia.
  replace (zb 0) with b1; [exact (nth_error_In _ _ H1)|].
  apply bv_eq. rewrite Hz, lws_zb0. reflexivity.
Qed.

Lemma lws_stop_at : forall sx sy, ~ In (zb 0) sx -> ~ In (zb 0) sy ->
  (lws_stop sx sy <= length sy)%nat /\
  exists b1 b2, nth_error (sx ++ [zb 0]) (lws_stop sx sy) = Some b1 /\
                nth_error (sy ++ [zb 0]) (lws_stop sx sy) = Some b2 /\
                (bv_unsigned b1 <> bv_unsigned b2 \/ bv_unsigned b1 = 0) /\
                (bv_unsigned b1 = bv_unsigned b2 <-> sx = sy).
Proof.
  intros sx sy HNx HNy.
  assert (Hl1 : length (sx ++ [zb 0]) = S (length sx)) by (rewrite length_app; cbn [length]; lia).
  assert (Hl2 : length (sy ++ [zb 0]) = S (length sy)) by (rewrite length_app; cbn [length]; lia).
  pose proof (lws_meet_le1 (sx ++ [zb 0]) (sy ++ [zb 0])) as Hm1.
  pose proof (lws_meet_le2 (sx ++ [zb 0]) (sy ++ [zb 0])) as Hm2.
  destruct (Nat.le_gt_cases (lws_meet (sx ++ [zb 0]) (sy ++ [zb 0])) (length sx)) as [Hmx|Hmx].
  - (* the compare stopped at or before the NUL of sx: the stop index is the first difference *)
    assert (Hst : lws_stop sx sy = lws_meet (sx ++ [zb 0]) (sy ++ [zb 0])) by (unfold lws_stop; lia).
    assert (Hmy : (lws_meet (sx ++ [zb 0]) (sy ++ [zb 0]) <= length sy)%nat).
    { destruct (Nat.le_gt_cases (lws_meet (sx ++ [zb 0]) (sy ++ [zb 0])) (length sy)) as [H|H]; [exact H|].
      exfalso.
      destruct (lws_meet_pre (sx ++ [zb 0]) (sy ++ [zb 0]) (length sy) ltac:(lia)) as (b1 & b2 & H1 & H2 & He).
      rewrite lws_nth_nul in H2. injection H2 as <-. rewrite lws_zb0 in He.
      rewrite nth_error_app1 in H1 by lia.
      apply HNx. replace (zb 0) with b1; [exact (nth_error_In _ _ H1)|].
      apply bv_eq. rewrite He, lws_zb0. reflexivity. }
    split; [lia|].
    assert (E1 : exists b1, nth_error (sx ++ [zb 0]) (lws_meet (sx ++ [zb 0]) (sy ++ [zb 0])) = Some b1).
    { destruct (nth_error (sx ++ [zb 0]) (lws_meet (sx ++ [zb 0]) (sy ++ [zb 0]))) as [b|] eqn:E;
        [exists b; reflexivity|]. exfalso. apply nth_error_None in E. lia. }
    assert (E2 : exists b2, nth_error (sy ++ [zb 0]) (lws_meet (sx ++ [zb 0]) (sy ++ [zb 0])) = Some b2).
    { destruct (nth_error (sy ++ [zb 0]) (lws_meet (sx ++ [zb 0]) (sy ++ [zb 0]))) as [b|] eqn:E;
        [exists b; reflexivity|]. exfalso. apply nth_error_None in E. lia. }
    destruct E1 as (b1 & E1). destruct E2 as (b2 & E2).
    pose proof (lws_meet_at _ _ b1 b2 E1 E2) as Hdiff.
    exists b1, b2. rewrite Hst.
    split; [exact E1|]. split; [exact E2|]. split; [left; exact Hdiff|].
    split; [intros He; exfalso; exact (Hdiff He)|].
    intros Heq. exfalso. apply Hdiff. subst sy. rewrite E1 in E2. injection E2 as <-. reflexivity.
  - (* the compare ran past the NUL of sx: the two strings are equal and the stop index is |sx| *)
    assert (Hst : lws_stop sx sy = length sx) by (unfold lws_stop; lia).
    destruct (lws_meet_pre (sx ++ [zb 0]) (sy ++ [zb 0]) (length sx) ltac:(lia)) as (b1 & b2 & H1 & H2 & He).
    rewrite lws_nth_nul in H1. injection H1 as <-. rewrite lws_zb0 in He.
    assert (Hylen : (length sy <= length sx)%nat).
    { destruct (Nat.le_gt_cases (length sy) (length sx)) as [H|H]; [exact H|].
      exfalso. rewrite nth_error_app1 in H2 by lia.
      apply HNy. replace (zb 0) with b2; [exact (nth_error_In _ _ H2)|].
      apply bv_eq. rewrite <- He, lws_zb0. reflexivity. }
    assert (Heqlen : (length sy = length sx)%nat) by lia.
    assert (Hll : sx ++ [zb 0] = sy ++ [zb 0]) by (apply lws_meet_eq; lia).
    assert (Hsxy : sx = sy) by exact (app_inv_tail _ _ _ Hll).
    split; [lia|].
    exists (zb 0), b2. rewrite Hst.
    split; [exact (lws_nth_nul sx)|]. split; [exact H2|].
    split; [right; exact lws_zb0|].
    split; [intros _; exact Hsxy | intros _; rewrite lws_zb0; exact He].
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* The sink head is an explicit argument, as in link_amem.v, link_ajkit.v and LinkWalk.v. *)
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.

Section s.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.

(* wrapper_strcmp on the caller's journal: the window is [sp - 2 * ESTACK, sp) and nothing else changes. *)
Lemma aj_gx_astrcmp_at : forall pc, AStrcmpDef.astrcmp_realizes segs B pc ->
  forall G XO OUT W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc kj x y kk c1 c2 raw,
  gx_ok segs B G ->
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc kj ->
  spZ regsT mod 16 = 0 -> sp0 - STK <= spZ regsT - 2 * ESTACK -> spZ regsT <= sp0 ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  getr regsT 1 = raw -> YK0s.ret_ok raw ->
  getr regsT 10 = w64 x -> getr regsT 11 = w64 y -> 0 < x -> 0 < y ->
  kk + 1 < 2 ^ 32 -> x + kk + 1 <= 2 ^ 63 -> y + kk + 1 <= 2 ^ 63 ->
  AStrcmpDef.str_meet segs W memT x y kk c1 c2 ->
  src_ok segs W regsT memT x (kk + 1) -> src_ok segs W regsT memT y (kk + 1) ->
  (forall a, x <= a <= x + kk -> ~ (spZ regsT - 2 * ESTACK <= a < spZ regsT)) ->
  (forall a, y <= a <= y + kk -> ~ (spZ regsT - 2 * ESTACK <= a < spZ regsT)) ->
  amem_range x (kk + 1) -> amem_range y (kk + 1) ->
  range_addressable (aview segs (w_H W) memT) SHADOW_OFF x (kk + 1) ->
  shadow_hull_vis (aview segs (w_H W) memT) x (kk + 1) ->
  range_addressable (aview segs (w_H W) memT) SHADOW_OFF y (kk + 1) ->
  shadow_hull_vis (aview segs (w_H W) memT) y (kk + 1) ->
  SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
    (fun W2 cf => W2 = W /\ exists regs2 mem2 md2,
       cf = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
       ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 kj /\
       same_but_materialized mdc md2 /\
       aregs_preserved regsT regs2 /\
       getr regs2 10 = w64 (AStrcmpDef.strcmp_res c1 c2) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - 2 * ESTACK <= a < spZ regsT) ->
          aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
       (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros pc HC G XO OUT W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc kj x y kk c1 c2 raw
  HG HJX H16 Hlo Hhi Hgp Htp Hra Hraw Hx Hy Hx0 Hy0 Hk32 Hxk Hyk Hmeet Hsx Hsy Hax Hay
  Hmx Hmy HRx HHx HRy HHy.
assert (Hes : ESTACK = 4096) by reflexivity.
destruct (aj_gx_ecall_pre SK segs B (2 * ESTACK) G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc kj regsT
  HJX ltac:(lia) H16 Hlo Hhi ltac:(rewrite Hra; exact Hraw) Hgp Htp) as (HPRE & HSLO & HWIN).
eapply SRr_mono.
{ apply (aj_gx_call_at SK segs B LAWS segs_low (2 * ESTACK) (fun _ => False) pc G XO OUT W regsT memT
    STK sp0 FP ly S W0 mem md own lyc Sc mdc kj raw
    (fun regs' mem' md' =>
       AR segs B lyc Sc W mem' md' /\ same_but_materialized mdc md' /\
       aregs_preserved regsT regs' /\ getr regs' 10 = w64 (AStrcmpDef.strcmp_res c1 c2) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - 2 * ESTACK <= a < spZ regsT) ->
          aview segs (w_H W) mem' a = aview segs (w_H W) memT a) /\
       (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem' a))).
  - exact HG.
  - exact HJX.
  - lia.
  - exact Hlo.
  - exact Hhi.
  - exact Hra.
  - intros a [].
  - intros regs' mem' md' (HAR' & Hsame & _ & _ & Hfr & Hpres').
    split; [exact HAR'|]. split; [exact Hsame|].
    split; [intros a Ha Hw _; exact (Hfr a Ha Hw) | exact Hpres'].
  - eapply SRr_mono.
    { exact (HC lyc Sc W regsT memT mdc x y kk c1 c2 HPRE HSLO HWIN Hx Hy Hx0 Hy0 Hk32 Hxk Hyk
        Hmeet Hsx Hsy Hax Hay Hmx Hmy HRx HHx HRy HHy). }
    cbv beta. intros W1 c3 _ (-> & regs' & mem' & md' & -> & HAR' & HP' & Hsame & Hres & Hfr & Hpres').
    split; [reflexivity|]. exists regs', mem', md'. split; [reflexivity|].
    split; [exact HAR'|]. split; [exact Hsame|]. split; [exact HP'|]. split; [exact Hres|].
    split; [exact Hfr | exact Hpres']. }
cbv beta. intros W2 cf _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HAR2 & Hsame2 & HP2 & Hres2 & Hfr2 & Hpres2).
split; [reflexivity|]. exists regs2, mem2, md2.
split; [reflexivity|]. split; [exact HJ2|]. split; [exact Hsame2|]. split; [exact HP2|].
split; [exact Hres2|]. split; [exact Hfr2 | exact Hpres2].
Qed.
End s.

(* ==========================================================================
   Section c: the stop index at the memory the walk sees
   ========================================================================== *)
Section c.
Variable segs : list Segment.
Variable W : world segs.

(* A byte of a C string, as the view the wrapper's contract reads. *)
Lemma lws_view_of : forall (memT : word -> option byte) p s i b,
  abytes segs (mrestrict (w_H W) memT) p (s ++ [zb 0]) ->
  nth_error (s ++ [zb 0]) i = Some b ->
  aview segs (w_H W) memT (p + Z.of_nat i) = Some (bv_unsigned b).
Proof.
  intros memT p s i b (_ & _ & Hnth) Hi.
  assert (Hlt : (i < length (s ++ [zb 0]))%nat)
    by (apply nth_error_Some; intros HN; rewrite HN in Hi; discriminate).
  unfold aview. rewrite (Hnth i Hlt), Hi. reflexivity.
Qed.

(* THE SHAPE every link caller of wrapper_strcmp has: two whole C strings. *)
Lemma astrcmp_cstr_meet : forall (memT : word -> option byte) x y sx sy,
  acstr_at segs (mrestrict (w_H W) memT) x sx ->
  acstr_at segs (mrestrict (w_H W) memT) y sy ->
  exists kk c1 c2,
    0 <= kk /\ kk <= Z.of_nat (length sx) /\ kk <= Z.of_nat (length sy) /\
    AStrcmpDef.str_meet segs W memT x y kk c1 c2 /\
    (AStrcmpDef.strcmp_res c1 c2 = 0 <-> sx = sy).
Proof.
  intros memT x y sx sy (HAx & HNx) (HAy & HNy).
  pose proof (lws_stop_sx sx sy) as Hkx.
  destruct (lws_stop_at sx sy HNx HNy) as (Hky & b1 & b2 & E1 & E2 & Hstop & Hiff).
  exists (Z.of_nat (lws_stop sx sy)), (bv_unsigned b1), (bv_unsigned b2).
  split; [lia|]. split; [lia|]. split; [lia|].
  split.
  { unfold AStrcmpDef.str_meet. split; [lia|]. split.
    - intros i Hi.
      destruct (lws_stop_pre sx sy (Z.to_nat i) HNx ltac:(lia)) as (b & Hb1 & Hb2 & Hbz).
      exists (bv_unsigned b).
      split; [replace i with (Z.of_nat (Z.to_nat i)) by lia;
              exact (lws_view_of memT x sx (Z.to_nat i) b HAx Hb1)|].
      split; [replace i with (Z.of_nat (Z.to_nat i)) by lia;
              exact (lws_view_of memT y sy (Z.to_nat i) b HAy Hb2) | exact Hbz].
    - split; [exact (lws_view_of memT x sx _ b1 HAx E1)|].
      split; [exact (lws_view_of memT y sy _ b2 HAy E2) | exact Hstop]. }
  unfold AStrcmpDef.strcmp_res.
  destruct (Z.eqb_spec (bv_unsigned b1) (bv_unsigned b2)) as [He|Hne].
  - split; [intros _; exact (proj1 Hiff He) | intros _; reflexivity].
  - split.
    + destruct (Z.ltb_spec (bv_unsigned b1) (bv_unsigned b2)); intros HH; lia.
    + intros Heq. exfalso. exact (Hne (proj2 Hiff Heq)).
Qed.
End c.
End a.
