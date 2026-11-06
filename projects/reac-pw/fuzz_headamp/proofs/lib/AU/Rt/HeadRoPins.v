(* The comments in this file are reac-pw/fuzz_pin's lib/A/Rt/PinRoPins.v, unchanged apart from names and this unit's files, image and values. reac-pw/fuzz_headamp, image B (fuzz_headamp.asan-ubsan 53edda9bdeeb): lib/AU/Rt/StrncmpView.v's `ro_owned_pinned` for every
   symbol record B of the TfibSyms class: every runtime-owned byte (Tfib_owned_static) that lies in a loaded
   segment without write permission is held by a constant cell of Tfib_const_abs at a constant address, whose
   constant value is the image's little-endian word there. The fact is decided by ro_pins_ok, a boolean check over
   image B's own tables and segments (vm_compute), and ro_pins_sound reads it as the proposition.
   rule 24 (reuse): no function is proved here. The shape is libreac/fuzz_boxreg's lib/A/Rt/StrncmpViewInst.v
   box_ro_owned_pinned (origin/ossv/recipes f26f9fbd8777), which takes the same fact from boxreg's AF0mCheck.v
   gate; this unit has no such gate file, so the check is written here over StrncmpView.v's own ro_img_word. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI04 YI00 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import YB1v YF0m.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU.Rt Require Import StrncmpView.
Import ListNotations.
Local Open Scope Z_scope.

(* a constant cell at a constant address: its address and value *)
Definition cell_av (c : acell) : option (Z * Z) :=
  match c_at c, c_val c with
  | ANum a', AV (ANum v) => Some (a', v)
  | _, _ => None
  end.

Lemma cell_av_spec : forall c a' v, cell_av c = Some (a', v) -> c_at c = ANum a' /\ c_val c = AV (ANum v).
Proof.
  intros c a' v H. unfold cell_av in H.
  destruct (c_at c); try discriminate H.
  destruct (c_val c) as [e|]; try discriminate H.
  destruct e; try discriminate H.
  injection H as <- <-. split; reflexivity.
Qed.

(* such a cell covering a whose image word is its value *)
Definition cell_pins (a : Z) (c : acell) : bool :=
  match cell_av c with
  | Some (a', v) =>
      if (a' <=? a) && (a <? a' + Z.of_nat (c_w c)) then
        match ro_img_word tfibsegs a' (c_w c) with Some v' => v' =? v | None => false end
      else false
  | None => false
  end.

(* the bytes of an owned range r that lie in a segment s without write permission *)
Definition seg_ro_bytes (r : Z * Z) (s : Segment) : list Z :=
  if seg_writable s then []
  else
    let lo := Z.max (fst r) (Z.of_N (seg_base s)) in
    let hi := Z.min (fst r + snd r) (Z.of_N (seg_base s) + Z.of_N (seg_size s)) in
    map (fun i => lo + Z.of_nat i) (seq 0 (Z.to_nat (hi - lo))).

Definition ro_pins_ok (owned : list (Z * Z)) (cells : list acell) : bool :=
  forallb (fun r => forallb (fun s => forallb (fun a => existsb (cell_pins a) cells) (seg_ro_bytes r s))
    tfibsegs) owned.

Lemma ro_pins_sound : forall owned cells, ro_pins_ok owned cells = true ->
  forall a, in_rom tfibsegs a -> Exists (in_zr a) owned ->
  Exists (fun c => exists a' v, c_at c = ANum a' /\ c_val c = AV (ANum v) /\ a' <= a < a' + Z.of_nat (c_w c) /\
    ro_img_word tfibsegs a' (c_w c) = Some v) cells.
Proof.
  intros owned cells H a (s & Hs & Hw & Hlo & Hhi) Ho.
  apply Exists_exists in Ho as (r & Hr & Hz). unfold in_zr in Hz.
  pose proof (proj1 (forallb_forall _ _) H r Hr) as H1.
  pose proof (proj1 (forallb_forall _ _) H1 s Hs) as H2.
  assert (Ha : In a (seg_ro_bytes r s)).
  { unfold seg_ro_bytes. rewrite Hw. apply in_map_iff.
    exists (Z.to_nat (a - Z.max (fst r) (Z.of_N (seg_base s)))). split; [lia|].
    apply in_seq. lia. }
  pose proof (proj1 (forallb_forall _ _) H2 a Ha) as H3.
  apply existsb_exists in H3 as (c & Hc & Hp).
  apply Exists_exists. exists c. split; [exact Hc|].
  unfold cell_pins in Hp. revert Hp.
  destruct (cell_av c) as [[a' v]|] eqn:Ec; [|intros Hf; discriminate Hf].
  apply cell_av_spec in Ec as [E1 E2].
  destruct ((a' <=? a) && (a <? a' + Z.of_nat (c_w c))) eqn:Hp0; [|intros Hf; discriminate Hf].
  apply andb_prop in Hp0 as [P1 P2]. apply Z.leb_le in P1. apply Z.ltb_lt in P2.
  destruct (ro_img_word tfibsegs a' (c_w c)) as [v'|] eqn:Ei; [|intros Hf; discriminate Hf].
  intros Hw'. apply Z.eqb_eq in Hw'. subst v'.
  exists a', v. split; [exact E1|]. split; [exact E2|]. split; [lia | exact Ei].
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* every TfibSyms record pins the owned read-only bytes, once the check holds of image B's tables *)
Lemma hd_ro_owned_pinned_of : ro_pins_ok Tfib_owned_static Tfib_const_abs = true ->
  forall B, TfibSyms B -> ro_owned_pinned tfibsegs B.
Proof.
  intros HC B TB ly a Hrom Ho.
  rewrite (ts_owned B TB) in Ho. rewrite (ts_const B TB ly). unfold Tfib_const.
  pose proof (ro_pins_sound _ _ HC a Hrom Ho) as HE.
  apply Exists_app. right. apply Exists_app. left. exact HE.
Qed.
End b.

(* the check over image B's own tables (lib/AU/YF0m.v) and image *)
Lemma hd_ro_pins_ok : ro_pins_ok Tfib_owned_static Tfib_const_abs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma hd_ro_owned_pinned {fx : YK11.FPState} {rc : YM05.RunCeil} : forall B, TfibSyms B -> ro_owned_pinned tfibsegs B.
Proof. exact (hd_ro_owned_pinned_of hd_ro_pins_ok). Qed.
