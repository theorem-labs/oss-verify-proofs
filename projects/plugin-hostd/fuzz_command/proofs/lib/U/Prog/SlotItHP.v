From Stdlib Require Import ZArith List Bool Lia String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require check_reply_c check_arity_c rec_shape_of_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import CommandModel rec_shape_of_c
  check_reply_c check_arity_c.
Import ListNotations.
Local Open Scope Z_scope.

(* HarnessProps states the reply and arity facts of a message with the plain build's check_reply_c and
   check_arity_c, whose strings are read from the plain image. The shape and verb tables sit at the same
   addresses in both builds and their strings are equal, so the facts carry over to this build's statements. *)

Definition hp_addrs : list Z :=
  SHAPE_LIT :: 0x1067c :: 0x104e2 :: map (fun r => match r with (_, _, a) => a end) shape_rows ++
  concat (map (fun r => match r with (na, sy, _) => [na; sy] end) parsed_rows).

Lemma hp_img_all : map (fun a => map bv_unsigned (lib.Prog.check_reply_c.img_str a)) hp_addrs =
                   map (fun a => map bv_unsigned (img_str a)) hp_addrs.
Proof. vm_compute. reflexivity. Qed.

Lemma hp_map_bv_inj : forall (x y : list byte), map bv_unsigned x = map bv_unsigned y -> x = y.
Proof.
  induction x as [|a x IH]; intros [|b y] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | exact (IH y H2)].
Qed.

Lemma hp_map_in : forall {X Y : Type} (f g : X -> Y) (l : list X) x, map f l = map g l -> In x l -> f x = g x.
Proof.
  intros X Y f g l x. induction l as [|y l IH]; intros El Hl; [destruct Hl|]. cbn [map] in El. injection El as E1 E2.
  destruct Hl as [<-|Hl]; [exact E1 | exact (IH E2 Hl)].
Qed.

Lemma hp_img : forall a, In a hp_addrs -> lib.Prog.check_reply_c.img_str a = img_str a.
Proof.
  intros a Ha. apply hp_map_bv_inj.
  exact (hp_map_in (fun a => map bv_unsigned (lib.Prog.check_reply_c.img_str a)) (fun a => map bv_unsigned (img_str a))
    hp_addrs a hp_img_all Ha).
Qed.

Lemma hp_shape_find_in : forall rows v, In (shape_find rows v) (SHAPE_LIT :: map (fun r => match r with (_, _, a) => a end) rows).
Proof.
  induction rows as [|[[x nm] a] rows IH]; intros v; cbn [shape_find map]; [left; reflexivity|].
  destruct (bytes_eqb (str_bytes nm) v); [right; left; reflexivity|].
  destruct (IH v) as [E|E]; [left; exact E | right; right; exact E].
Qed.

Lemma hp_shape_addr : forall n w0, lib.Prog.check_reply_c.img_str (lib.Prog.check_reply_c.shape_addr n w0) = img_str (shape_addr n w0).
Proof.
  intros n w0.
  change (lib.Prog.check_reply_c.shape_addr n w0) with (shape_addr n w0).
  apply hp_img. unfold shape_addr, hp_addrs. destruct (n =? 0); [left; reflexivity|].
  destruct (hp_shape_find_in shape_rows w0) as [E|E]; [left; exact E|].
  right. right. right. apply in_or_app. left. exact E.
Qed.

Lemma hp_reply_ok : forall n w0 xr, lib.Prog.check_reply_c.reply_ok n w0 xr -> reply_ok n w0 xr.
Proof.
  intros n w0 xr (H1 & H2). split; [exact H1|].
  intros H. destruct (H2 H) as [E|E].
  - left. rewrite <- hp_shape_addr. exact E.
  - right. rewrite <- (hp_img SHAPE_LIT) by (left; reflexivity). exact E.
Qed.

Lemma hp_row_find : forall v rows,
  (forall na sy fm, In (na, sy, fm) rows -> lib.Prog.check_reply_c.img_str na = img_str na /\ lib.Prog.check_reply_c.img_str sy = img_str sy) ->
  lib.Prog.check_arity_c.row_find v rows = row_find v rows.
Proof.
  intros v. induction rows as [|[[na sy] fm] rows IH]; intros H; [reflexivity|].
  cbn [lib.Prog.check_arity_c.row_find row_find].
  destruct (H na sy fm (or_introl eq_refl)) as [E1 E2]. rewrite E1, E2.
  rewrite IH by (intros na' sy' fm' Hin; exact (H na' sy' fm' (or_intror Hin))).
  reflexivity.
Qed.

Lemma hp_passed_on : forall v, lib.Prog.check_arity_c.passed_on_m v = passed_on_m v.
Proof.
  intros v. unfold lib.Prog.check_arity_c.passed_on_m, passed_on_m.
  rewrite (hp_img 0x1067c) by (right; left; reflexivity).
  rewrite (hp_img 0x104e2) by (right; right; left; reflexivity).
  reflexivity.
Qed.

Lemma hp_arity_ok : forall t v q nc fn0, lib.Prog.check_arity_c.arity_ok t v q nc fn0 -> arity_ok t v q nc fn0.
Proof.
  intros t v q nc fn0 H. unfold lib.Prog.check_arity_c.arity_ok in H. unfold arity_ok.
  rewrite hp_passed_on in H.
  assert (E : lib.Prog.check_arity_c.row_find v lib.Prog.check_arity_c.parsed_rows = row_find v parsed_rows).
  { change lib.Prog.check_arity_c.parsed_rows with parsed_rows. apply hp_row_find.
    intros na sy fm Hin. split; apply hp_img; unfold hp_addrs; right; right; right; apply in_or_app; right;
      apply in_concat; exists [na; sy]; (split; [apply in_map_iff; exists (na, sy, fm); split; [reflexivity | exact Hin]|]);
      cbn; tauto. }
  rewrite E in H. exact H.
Qed.
