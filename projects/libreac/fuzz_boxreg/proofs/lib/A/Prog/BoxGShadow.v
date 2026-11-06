(* libreac/fuzz_boxreg, ASan build (fuzz_boxreg.asan): the two shadow facts of lib/A/Prog/BoxClose.v's row 8
   (box_gshadow_A), proved at the asyms instance TfibB (lib/A/AD2l.v) from AR alone. No function is proved here (kind:
   start-up facts of the image).
   - img_shadow_vis_box (gsA_isv): in every AR state, every shadow byte of [IMG_LO, IMG_TOP) is readable. The image's
     shadow is tiled by the four ranges of Tfib_zero_shadow (lib/A/AF0m.v), whose shadow AR's am_zshadow keeps zero,
     and the 60 one-byte cells of Tfib_const_shadow, which AR's am_const keeps at their values: the shadow of the five
     registered globals with their guard granules (0x7fffc198, 12 bytes; 0x7fffc1a8, 8 bytes) and that of the
     asan_globals records 0x9d770 .. 0x9d8b0 (0x8000baee, 40 bytes).
   - globs_marked_box (gsA_glob): the shadow byte of each registered global (BoxClose.v's BOX_GLOBS, stated here by its
     value) is a constant shadow cell holding the global's size, which is block_shadow for a global of under 8 bytes.
   Both are stated at the types of box_gshadow_A's fields at BA := TfibB, so Build_box_gshadow_A TfibB
   img_shadow_vis_box globs_marked_box discharges row 8 without the start-up certificate: AR's laws over TfibB's tables
   give both facts in every state. That the stated cell values hold in the hand-off states is the start-up
   certificate's job (lib/A/AF0mCheck.v's header), not this file's.
   Source: the premise audit of boxreg's frozen lib/A statements at TfibB (a Theorem Labs lane, 2026-10-29, scratch
   boxpa/premaudit-a/ZzPremAuditA.v section 3), moved here unchanged except for names and the statements' binders. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK11 YK04 YA0i YA0n YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A Require Import AF0m AF0mCheck AD2l.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import BoxImg BoxRo.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* s is the address of a one-byte constant shadow cell *)
Definition shadow_cell1_b (s : Z) : bool :=
  existsb (fun c => match c with ACell (ANum a') (S O) (AV (ANum _)) => a' =? s | _ => false end) Tfib_const_shadow.
Lemma shadow_cell1_b_ok : forall s, shadow_cell1_b s = true -> exists v, In (ACell (ANum s) 1 (AV (ANum v))) Tfib_const_shadow.
Proof.
intros s H. apply existsb_exists in H as (c & Hc & Hb). destruct c as [e w av].
destruct e; try discriminate. destruct w as [|[|w]]; try discriminate.
destruct av as [e'|]; try discriminate. destruct e'; try discriminate.
apply Z.eqb_eq in Hb. subst. eexists. exact Hc.
Qed.
Lemma shadow_cells_ok : forall lo n s, forallb shadow_cell1_b (zbytes lo n) = true -> lo <= s < lo + n ->
  exists v, In (ACell (ANum s) 1 (AV (ANum v))) Tfib_const_shadow.
Proof.
intros lo n s H Hs. apply shadow_cell1_b_ok. exact (proj1 (forallb_forall _ _) H s (in_zbytes lo n s Hs)).
Qed.
(* the three runs of constant shadow cells *)
Lemma shadow_runs : forallb shadow_cell1_b (zbytes 0x7fffc198 12) = true /\
  forallb shadow_cell1_b (zbytes 0x7fffc1a8 8) = true /\ forallb shadow_cell1_b (zbytes 0x8000baee 40) = true.
Proof. vm_compute. repeat split; reflexivity. Qed.

Section v. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* In every AR state a constant shadow cell holds its value. *)
Lemma shadow_cell_view : forall ly S (W : world box_segs) mem md a v,
  AR box_segs TfibB ly S W mem md -> In (ACell (ANum a) 1 (AV (ANum v))) Tfib_const_shadow ->
  aview box_segs (w_H W) mem a = Some (le_byte v 1 0).
Proof.
intros ly S W mem md a v [HM _] Ha. apply am_const in HM.
assert (Hc : In (ACell (ANum a) 1 (AV (ANum v))) (as_const TfibB ly)).
{ cbn [as_const TfibB]. unfold Tfib_const. apply in_app_iff. right. apply in_app_iff. right. exact Ha. }
pose proof (proj1 (Forall_forall _ _) HM _ Hc) as H. unfold cell_holds in H. cbv zeta in H.
cbn [c_val c_at c_w aeval] in H. specialize (H 0%nat ltac:(lia)). cbn [Z.of_nat] in H. rewrite Z.add_0_r in H.
exact H.
Qed.
End v.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* gsA_isv at TfibB *)
Lemma img_shadow_vis_box : forall (rc : YM05.RunCeil) (fx : YK11.FPState), img_shadow_vis box_segs TfibB.
Proof.
intros rc fx ly S W mem md a HAR Ha.
pose proof HAR as [HM _]. apply am_zshadow in HM. unfold zshadow_ok in HM.
assert (Zr : forall q m, In (q, m) Tfib_zero_shadow -> q mod 8 = 0 -> m mod 8 = 0 -> q <= a < q + m ->
  aview box_segs (w_H W) mem (shadow_addr a) = Some 0).
{ intros q m Hq H8 Hm8 Hr.
  assert (Hin : In (q, m) (zero_shadow_ranges TfibB ly)) by (unfold zero_shadow_ranges; right; exact Hq).
  pose proof (proj1 (Forall_forall _ _) HM _ Hin) as Z0. cbn [fst snd] in Z0. unfold zero_shadow in Z0.
  replace (shadow_addr a) with (shadow_of_addr SHADOW_OFF q + (a / 8 - q / 8)) by (unfold shadow_addr, shadow_of_addr; lia).
  apply Z0. lia. }
destruct shadow_runs as (G1 & G2 & G3).
assert (Hcell : forall lo n, forallb shadow_cell1_b (zbytes lo n) = true -> lo <= shadow_addr a < lo + n ->
  aview box_segs (w_H W) mem (shadow_addr a) <> None).
{ intros lo n G Hs. destruct (shadow_cells_ok lo n _ G Hs) as (v & Hv).
  rewrite (shadow_cell_view ly S W mem md _ v HAR Hv). discriminate. }
unfold shadow_addr in Hcell |- *. unfold IMG_HI in Ha.
destruct (Z_lt_le_dec a 0x20cc0) as [H1|H1].
{ fold (shadow_addr a). rewrite (Zr 0x10000 (0x20cc0 - 0x10000)); [discriminate | cbn [In Tfib_zero_shadow]; repeat (first [left; reflexivity | right]) | reflexivity | reflexivity | lia]. }
destruct (Z_lt_le_dec a 0x20d20) as [H2|H2]; [apply (Hcell _ _ G1); unfold SHADOW_OFF; lia|].
destruct (Z_lt_le_dec a 0x20d40) as [H3|H3].
{ fold (shadow_addr a). rewrite (Zr 0x20d20 (0x20d40 - 0x20d20)); [discriminate | cbn [In Tfib_zero_shadow]; repeat (first [left; reflexivity | right]) | reflexivity | reflexivity | lia]. }
destruct (Z_lt_le_dec a 0x20d80) as [H4|H4]; [apply (Hcell _ _ G2); unfold SHADOW_OFF; lia|].
destruct (Z_lt_le_dec a 0x9d770) as [H5|H5].
{ fold (shadow_addr a). rewrite (Zr 0x20d80 (0x9d770 - 0x20d80)); [discriminate | cbn [In Tfib_zero_shadow]; repeat (first [left; reflexivity | right]) | reflexivity | reflexivity | lia]. }
destruct (Z_lt_le_dec a 0x9d8b0) as [H6|H6]; [apply (Hcell _ _ G3); unfold SHADOW_OFF; lia|].
fold (shadow_addr a). rewrite (Zr 0x9d8b0 (0x5f6000 - 0x9d8b0)); [discriminate | cbn [In Tfib_zero_shadow]; repeat (first [left; reflexivity | right]) | reflexivity | reflexivity | lia].
Qed.

(* gsA_glob at TfibB; the list is BoxClose.v's BOX_GLOBS *)
Lemma globs_marked_box : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  globs_marked box_segs TfibB [(0x20cc0, 6); (0x20ce0, 1); (0x20d00, 5); (0x20d40, 3); (0x20d60, 1)].
Proof.
intros rc fx ly S W mem md q sz Hin HAR.
destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- <-;
(split; [reflexivity|]); (split; [lia|]); intros i Hi;
(match type of Hi with context [?x / 8] => let v := eval vm_compute in (x / 8) in change (x / 8) with v in Hi end);
assert (Ei : i = 0) by lia; subst i;
(match goal with |- ?rd (?e + 0) = Some ?r =>
  let e' := eval vm_compute in (e + 0) in let r' := eval vm_compute in r in
  change (rd (e + 0) = Some r) with (rd e' = Some r');
  rewrite (shadow_cell_view ly S W mem md e' r' HAR);
  [vm_compute; reflexivity | apply zcell_in; vm_compute; reflexivity] end).
Qed.
