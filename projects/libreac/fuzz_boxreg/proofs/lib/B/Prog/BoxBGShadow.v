(* libreac/fuzz_boxreg, ASan+UBSan build (fuzz_boxreg.asan-ubsan): the two shadow facts of lib/B/Prog/BoxBClose.v's
   row 8 (boxb_gshadow_B), proved at the asyms instance TfibB (lib/B/AD2l.v) from AR alone; the B twin of
   lib/A/Prog/BoxGShadow.v. No function is proved here (kind: start-up facts of the image).
   - img_shadow_vis_boxb (gsB_isv): in every AR state, every shadow byte of [IMG_LO, IMG_TOP) is readable. The image's
     shadow is tiled by the four ranges of Tfib_zero_shadow (lib/B/AF0m.v), whose shadow AR's zero-shadow law keeps
     zero (lib/A/Prog/BoxRo.v zs_zero over YG0q.AR_laws_ok), and the 60 one-byte cells of Tfib_const_shadow, which AR's
     am_const keeps at their values: the shadow of the five registered globals with their guard granules (0x7fffc198,
     12 bytes; 0x7fffc1a8, 8 bytes) and that of the asan_globals records 0x9db90 .. 0x9dcd0 (0x8000bb72, 40 bytes).
   - globs_marked_boxb (gsB_glob): the shadow byte of each registered global (BoxBClose.v's BOXB_GLOBS, stated here by
     its value) is a constant shadow cell holding the global's size, which is block_shadow for a global of under 8
     bytes.
   Image A differs only in where its asan_globals records lie (0x9d770 .. 0x9d8b0, shadow cells from 0x8000baee): the
   statements are the same (60 shadow cells in both images, the same five globals at the same addresses and sizes).
   Both are stated at the types of boxb_gshadow_B's fields at BB := TfibB, so Build_boxb_gshadow_B TfibB
   img_shadow_vis_boxb globs_marked_boxb discharges row 8 without the start-up certificate: AR's laws over TfibB's
   tables give both facts in every state. That the stated cell values hold in the hand-off states is the start-up
   certificate's job (lib/B/AF0mCheck.v's header), not this file's.
   Source: the premise audit of boxreg's frozen lib/B statements at TfibB (a Theorem Labs lane, 2026-10-29, scratch
   boxpa/premaudit-b/ZzPremAuditB.v, globs_marked_TfibB and img_shadow_vis_TfibB_closed), moved here unchanged except
   for names and the statements' binders. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK11 YK04 YA0i YA0n YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YG0q.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B Require Import AF0m AF0mCheck AD2l.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import BoxRo.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBImg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* A constant shadow cell holds its value in every reader that satisfies the const table. *)
Lemma shadow_cell_holds : forall B ly (rd : reader) s v,
  Forall (cell_holds B ly rd) (as_const B ly) -> (forall ly, as_const B ly = Tfib_const ly) ->
  In (z1 (ANum s) v) Tfib_const_shadow -> rd s = Some (le_byte v 1 0).
Proof.
  intros B ly rd s v HF HC Hs.
  assert (Hs' : In (z1 (ANum s) v) (as_const B ly))
    by (rewrite HC; unfold Tfib_const; apply in_app_iff; right; apply in_app_iff; right; exact Hs).
  pose proof (proj1 (Forall_forall _ _) HF _ Hs') as H. unfold cell_holds in H. cbn [c_at c_val c_w z1 c1] in H.
  specialize (H O ltac:(lia)). cbn [aeval Z.of_nat] in H. rewrite Z.add_0_r in H. exact H.
Qed.
(* block_shadow of a global of under 8 bytes is its one shadow byte *)
Lemma bs1 : forall (rd : reader) q sz s,
  q mod 8 = 0 -> (sz + 7) / 8 = 1 -> shadow_of_addr SHADOW_OFF q = s -> 0 <= sz ->
  rd s = Some (if 0 <? sz / 8 then 0 else sz mod 8) -> block_shadow rd SHADOW_OFF q sz.
Proof.
  intros rd q sz s Hq Hd Hs Hz Hr. split; [exact Hq|]. split; [exact Hz|].
  intros i Hi. rewrite Hd in Hi. assert (i = 0) by lia. subst i. rewrite Z.add_0_r, Hs. exact Hr.
Qed.
(* s is the address of a one-byte constant shadow cell *)
Definition pt_b (s : Z) : bool :=
  existsb (fun c => match c with ACell (ANum a') (S O) (AV (ANum _)) => Z.eqb a' s | _ => false end)
    Tfib_const_shadow.
Lemma pt_b_sound : forall s, pt_b s = true -> exists v, In (z1 (ANum s) v) Tfib_const_shadow.
Proof.
  intros s H. apply existsb_exists in H as (c & Hc & Hb). destruct c as [e w av].
  destruct e; cbn in Hb; try discriminate.
  destruct w as [|[|w]]; cbn in Hb; try discriminate.
  destruct av as [e'|]; cbn in Hb; try discriminate.
  destruct e'; cbn in Hb; try discriminate.
  apply Z.eqb_eq in Hb. subst. eexists. exact Hc.
Qed.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma globs_marked_syms : forall B, (forall ly, as_const B ly = Tfib_const ly) ->
  globs_marked boxb_segs B [(0x20cc0, 6); (0x20ce0, 1); (0x20d00, 5); (0x20d40, 3); (0x20d60, 1)].
Proof.
  intros B HC ly S W mem md q sz Hin HAR.
  destruct HAR as [HM _]. pose proof (am_const _ _ _ _ HM) as HF.
  pose proof (fun s v => shadow_cell_holds B ly (aview boxb_segs (w_H W) mem) s v HF HC) as P.
  destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- <-.
  - apply (bs1 _ _ _ 0x7fffc198); [reflexivity | reflexivity | reflexivity | lia |].
    rewrite (P 0x7fffc198 6) by (repeat (first [left; reflexivity | right])). reflexivity.
  - apply (bs1 _ _ _ 0x7fffc19c); [reflexivity | reflexivity | reflexivity | lia |].
    rewrite (P 0x7fffc19c 1) by (repeat (first [left; reflexivity | right])). reflexivity.
  - apply (bs1 _ _ _ 0x7fffc1a0); [reflexivity | reflexivity | reflexivity | lia |].
    rewrite (P 0x7fffc1a0 5) by (repeat (first [left; reflexivity | right])). reflexivity.
  - apply (bs1 _ _ _ 0x7fffc1a8); [reflexivity | reflexivity | reflexivity | lia |].
    rewrite (P 0x7fffc1a8 3) by (repeat (first [left; reflexivity | right])). reflexivity.
  - apply (bs1 _ _ _ 0x7fffc1ac); [reflexivity | reflexivity | reflexivity | lia |].
    rewrite (P 0x7fffc1ac 1) by (repeat (first [left; reflexivity | right])). reflexivity.
Qed.
Lemma img_shadow_vis_syms : forall B, AR_laws boxb_segs B -> as_zero_shadow B = Tfib_zero_shadow ->
  (forall ly, as_const B ly = Tfib_const ly) -> img_shadow_vis boxb_segs B.
Proof.
  intros B LAWS HZ HC ly S W mem md a HAR Ha. unfold IMG_HI in Ha.
  pose proof (Z.div_mod a 8 ltac:(lia)) as Da. pose proof (Z.mod_pos_bound a 8 ltac:(lia)) as Ba.
  pose proof HAR as HAR'. destruct HAR' as [HM _]. pose proof (am_const _ _ _ _ HM) as HF.
  assert (HZr : forall q m, In (q, m) (as_zero_shadow B) -> q mod 8 = 0 -> m mod 8 = 0 -> q <= a < q + m ->
            aview boxb_segs (w_H W) mem (shadow_addr a) <> None).
  { intros q m Hin Hq8 Hm8 Hr.
    pose proof (zs_zero boxb_segs B LAWS q m Hin ly S W mem md HAR) as Hz.
    pose proof (Z.div_mod q 8 ltac:(lia)) as Dq. pose proof (Z.div_mod m 8 ltac:(lia)) as Dm.
    assert (R : 0 <= a / 8 - q / 8 < m / 8) by lia.
    specialize (Hz (a / 8 - q / 8) R). unfold shadow_of_addr in Hz. unfold shadow_addr.
    replace (SHADOW_OFF + a / 8) with (SHADOW_OFF + q / 8 + (a / 8 - q / 8)) by lia. rewrite Hz. discriminate. }
  assert (HPt : forall lo n, forallb pt_b (zbytes lo n) = true -> lo <= shadow_addr a < lo + n ->
            aview boxb_segs (w_H W) mem (shadow_addr a) <> None).
  { intros lo n Hb Hr.
    pose proof (proj1 (forallb_forall _ _) Hb (shadow_addr a) (in_zbytes lo n (shadow_addr a) Hr)) as H1.
    destruct (pt_b_sound _ H1) as (v & Hv).
    rewrite (shadow_cell_holds B ly _ _ v HF HC Hv). discriminate. }
  destruct (Z_lt_le_dec a 0x20cc0) as [h1|h1].
  { apply (HZr 0x10000 (0x20cc0 - 0x10000)); [rewrite HZ; left; reflexivity | reflexivity | reflexivity | lia]. }
  destruct (Z_lt_le_dec a 0x20d20) as [h2|h2].
  { apply (HPt 0x7fffc198 12); [vm_compute; reflexivity | unfold shadow_addr, SHADOW_OFF; lia]. }
  destruct (Z_lt_le_dec a 0x20d40) as [h3|h3].
  { apply (HZr 0x20d20 (0x20d40 - 0x20d20)); [rewrite HZ; right; left; reflexivity | reflexivity | reflexivity | lia]. }
  destruct (Z_lt_le_dec a 0x20d80) as [h4|h4].
  { apply (HPt 0x7fffc1a8 8); [vm_compute; reflexivity | unfold shadow_addr, SHADOW_OFF; lia]. }
  destruct (Z_lt_le_dec a 0x9db90) as [h5|h5].
  { apply (HZr 0x20d80 (0x9db90 - 0x20d80)); [rewrite HZ; right; right; left; reflexivity | reflexivity | reflexivity | lia]. }
  destruct (Z_lt_le_dec a 0x9dcd0) as [h6|h6].
  { apply (HPt 0x8000bb72 40); [vm_compute; reflexivity | unfold shadow_addr, SHADOW_OFF; lia]. }
  apply (HZr 0x9dcd0 (0x5f6000 - 0x9dcd0)); [rewrite HZ; right; right; right; left; reflexivity | reflexivity | reflexivity | lia].
Qed.
End s.

(* gsB_isv at TfibB: AR_laws holds for every segs and B (lib/Reusable/YG0q.v AR_laws_ok) *)
Lemma img_shadow_vis_boxb : forall (rc : YM05.RunCeil) (fx : YK11.FPState), img_shadow_vis boxb_segs TfibB.
Proof.
  intros rc fx. apply img_shadow_vis_syms; [apply YG0q.AR_laws_ok | reflexivity | intros ly; reflexivity].
Qed.
(* gsB_glob at TfibB; the list is BoxBClose.v's BOXB_GLOBS *)
Lemma globs_marked_boxb : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  globs_marked boxb_segs TfibB [(0x20cc0, 6); (0x20ce0, 1); (0x20d00, 5); (0x20d40, 3); (0x20d60, 1)].
Proof. intros rc fx. apply globs_marked_syms. intros ly. reflexivity. Qed.
