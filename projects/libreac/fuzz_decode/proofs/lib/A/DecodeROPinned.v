(* libreac/fuzz_decode, build asan: ro_owned_pinned at image A's generated start-up record GrantB (lib/A/AD2l.v).
   Rule 24: no function is proved here. Kind: start-up facts; a fact about the image and its asyms record, proved by
   computation.
   - ro_img_word / ro_owned_pinned: verbatim from libreac/fuzz_boxreg lib/A/Rt/StrncmpView.v:33-49 and :101 (blob
     1071839c23a3, a working branch df8841114cce), module paths changed only. They are image-generic (segs, B
     are parameters). Its outer Section b (the FPState / RunCeil context) is left out: neither definition uses it.
     Every runtime-owned byte of a segment without write permission lies in a cell of as_const B ly at a constant
     address whose constant value is the image's little-endian word there.
   - img_word, pinb, zbytes, ro_pinned_chk, their soundness lemmas and the gate: from boxreg lib/A/AF0mCheck.v:36-46,
     :76-114, :135-140 (blob 4c631199f27d), with box_segs -> tfibsegs (lib/A/AB1v.v:13), box_ro_ranges ->
     dec_ro_ranges, box_ro_pinned -> dec_ro_pinned, box_ro_gate -> dec_ro_gate.
   - dec_ro_ranges: the two non-writable PT_LOADs of fuzz_decode.asan (sha256 5973b76807d8...) by p_filesz,
     [0x10000, 0x2f008) and [0x30008, 0x977a8) (a Theorem Labs lane's decode/OWNED-CELLS.md section 7). No step trusts them:
     owned_ro_ok checks against the loaded segments that every owned range meeting a non-writable segment lies
     inside one of them, and dec_ro_pinned checks every owned byte inside them against the image.
   - The instance (ro_img_word_dec, seg_ov, owned_ro_ok, owned_in_rom_ro_ranges, dec_ro_owned_pinned): from boxreg
     lib/A/Rt/StrncmpViewInst.v:25-73 (blob 14e08ec9e37a), with TfibB -> GrantB. as_const GrantB ly = Tfib_const ly
     = Tfib_const_sym ++ Tfib_const_abs ++ Tfib_const_shadow (lib/A/AF0m.v:380) and as_owned_static GrantB =
     Tfib_owned_static (AF0m.v:383); the gate runs over Tfib_const_abs. *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YI04 YI00 YM05 YF0p.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import AF0l AF0m ACej AD2l AB1v.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* The definition: boxreg lib/A/Rt/StrncmpView.v:33-49, :101. *)
Section c.
Variable segs : list Segment.
Variable B : asyms.
(* The bytes the image carries at a, little-endian, as a value; None when it carries none (AF0mCheck.v img_word). *)
Fixpoint ro_img_word (a : Z) (w : nat) : option Z :=
match w with
| O => Some 0
| S w' =>
  match seg_rom segs (Z_to_bv 64 a), ro_img_word (a + 1) w' with
  | Some b, Some v => Some (bv_unsigned b + 256 * v)
  | _, _ => None
  end
end.
(* Every runtime-owned byte of a segment without write permission is pinned to its image byte by a constant cell. *)
Definition ro_owned_pinned : Prop :=
forall ly a, in_rom segs a -> Exists (in_zr a) (as_owned_static B) ->
Exists (fun c => exists a' v, c_at c = ANum a' /\ c_val c = AV (ANum v) /\ a' <= a < a' + Z.of_nat (c_w c) /\
  ro_img_word a' (c_w c) = Some v) (as_const B ly).
End c.

(* The gate: boxreg lib/A/AF0mCheck.v:36-46, :76-114, :135-140, over tfibsegs. *)
(* The bytes the image carries at a, little-endian, as a value; None when it carries none. *)
Fixpoint img_word (a : Z) (w : nat) : option Z :=
match w with
| O => Some 0
| S w' =>
  match seg_rom tfibsegs (Z_to_bv 64 a), img_word (a + 1) w' with
  | Some b, Some v => Some (bv_unsigned b + 256 * v)
  | _, _ => None
  end
end.
(* The two non-writable PT_LOADs of fuzz_decode.asan, (p_vaddr, p_filesz). *)
Definition dec_ro_ranges : list (Z * Z) := [(0x10000, 0x1f008); (0x30008, 0x677a0)].
Definition pinb (c : acell) (a : Z) : bool :=
match c_at c, c_val c with
| ANum a', AV (ANum v) => (a' <=? a) && (a <? a' + Z.of_nat (c_w c)) && match img_word a' (c_w c) with Some x => Z.eqb x v | None => false end
| _, _ => false
end.
Lemma pinb_sound : forall c a, pinb c a = true ->
exists a' v, c_at c = ANum a' /\ c_val c = AV (ANum v) /\ a' <= a < a' + Z.of_nat (c_w c) /\ img_word a' (c_w c) = Some v.
Proof.
intros [e w av] a H. unfold pinb in H. cbn [c_at c_val c_w] in H |- *.
destruct e as [a'| | | | | | | | | | | | | | | | | |]; try (cbn in H; discriminate).
destruct av as [e'|]; [|cbn in H; discriminate]. destruct e' as [v| | | | | | | | | | | | | | | | | |]; try (cbn in H; discriminate).
destruct (img_word a' w) as [x|] eqn:Ei; [|rewrite Bool.andb_false_r in H; discriminate].
apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.eqb_eq in H3. subst x.
exists a', v. split; [reflexivity|]. split; [reflexivity|]. split; [lia | exact Ei].
Qed.
Definition zbytes (lo n : Z) : list Z := map (fun k => lo + Z.of_nat k) (seq 0 (Z.to_nat n)).
Lemma in_zbytes : forall lo n a, lo <= a < lo + n -> In a (zbytes lo n).
Proof.
intros lo n a H. unfold zbytes. apply in_map_iff. exists (Z.to_nat (a - lo)). split; [lia|]. apply in_seq. lia.
Qed.
Definition ro_pinned_chk (owned : list (Z * Z)) (l : list acell) : bool :=
forallb (fun r => forallb (fun s =>
  let lo := Z.max (fst r) (fst s) in let hi := Z.min (fst r + snd r) (fst s + snd s) in
  forallb (fun a => existsb (fun c => pinb c a) l) (zbytes lo (hi - lo))) dec_ro_ranges) owned.
Lemma ro_pinned_chk_sound : forall owned l, ro_pinned_chk owned l = true ->
forall a, Exists (fun s => fst s <= a < fst s + snd s) dec_ro_ranges -> Exists (fun r => fst r <= a < fst r + snd r) owned ->
Exists (fun c => exists a' v, c_at c = ANum a' /\ c_val c = AV (ANum v) /\ a' <= a < a' + Z.of_nat (c_w c) /\
  img_word a' (c_w c) = Some v) l.
Proof.
intros owned l H a Hs Hr. unfold ro_pinned_chk in H.
apply Exists_exists in Hs as (s & Hs & Ls). apply Exists_exists in Hr as (r & Hr & Lr).
pose proof (proj1 (forallb_forall _ _) H r Hr) as H1. cbv beta in H1.
pose proof (proj1 (forallb_forall _ _) H1 s Hs) as H2. cbv beta zeta in H2.
assert (Ha : In a (zbytes (Z.max (fst r) (fst s)) (Z.min (fst r + snd r) (fst s + snd s) - Z.max (fst r) (fst s))))
by (apply in_zbytes; lia).
pose proof (proj1 (forallb_forall _ _) H2 a Ha) as H3. cbv beta in H3.
apply existsb_exists in H3 as (c & Hc & Hp). apply Exists_exists. exists c. split; [exact Hc | exact (pinb_sound c a Hp)].
Qed.
(* Every owned byte inside a non-writable PT_LOAD is pinned to its image word by a row of Tfib_const_abs. *)
Theorem dec_ro_pinned : ro_pinned_chk Tfib_owned_static Tfib_const_abs = true.
Proof. vm_compute. reflexivity. Qed.
Definition dec_ro_gate : Prop :=
forall a, Exists (fun s => fst s <= a < fst s + snd s) dec_ro_ranges -> Exists (fun r => fst r <= a < fst r + snd r) Tfib_owned_static ->
Exists (fun c => exists a' v, c_at c = ANum a' /\ c_val c = AV (ANum v) /\ a' <= a < a' + Z.of_nat (c_w c) /\
  img_word a' (c_w c) = Some v) Tfib_const_abs.
Lemma dec_ro_gate_holds : dec_ro_gate.
Proof. exact (ro_pinned_chk_sound Tfib_owned_static Tfib_const_abs dec_ro_pinned). Qed.

(* The instance: boxreg lib/A/Rt/StrncmpViewInst.v:25-73, for tfibsegs and GrantB. *)
(* ro_img_word at tfibsegs is img_word: the same recursion. *)
Lemma ro_img_word_dec : forall w a, ro_img_word tfibsegs a w = img_word a w.
Proof.
  induction w as [|w IH]; intro a; cbn [ro_img_word img_word]; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

(* A byte that is both owned (Tfib_owned_static) and in_rom is inside dec_ro_ranges: every owned range that meets a
   non-writable loaded segment lies within a dec_ro_range. owned_ro_ok is that, by vm_compute. *)
Definition seg_ov (r : Z * Z) (sg : Segment) : bool :=
  andb (negb (seg_writable sg))
    (andb (Z.of_N (seg_base sg) <? fst r + snd r) (fst r <? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))).
Definition owned_ro_ok : bool :=
  forallb (fun r => implb (existsb (seg_ov r) tfibsegs)
    (existsb (fun q => (fst q <=? fst r) && (fst r + snd r <=? fst q + snd q)) dec_ro_ranges)) Tfib_owned_static.
Lemma owned_ro_ok_true : owned_ro_ok = true.
Proof. vm_compute. reflexivity. Qed.

Lemma owned_in_rom_ro_ranges : forall a, in_rom tfibsegs a ->
  Exists (fun r => fst r <= a < fst r + snd r) Tfib_owned_static ->
  Exists (fun r => fst r <= a < fst r + snd r) dec_ro_ranges.
Proof.
  intros a (sg & Hin & Hnw & Hlo & Hhi) Ho.
  apply Exists_exists in Ho as (r & Hr & Hro).
  pose proof (proj1 (forallb_forall _ _) owned_ro_ok_true r Hr) as H. cbv beta in H.
  assert (Hov : existsb (seg_ov r) tfibsegs = true).
  { apply existsb_exists. exists sg. split; [exact Hin|].
    unfold seg_ov. rewrite Hnw. cbn [negb andb]. apply andb_true_intro. split; apply Z.ltb_lt; lia. }
  rewrite Hov in H. cbn [implb] in H.
  apply existsb_exists in H as (q & Hq & Hb).
  apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  apply Exists_exists. exists q. split; [exact Hq|]. lia.
Qed.

(* The discharge. *)
Theorem dec_ro_owned_pinned : ro_owned_pinned tfibsegs GrantB.
Proof.
  intros ly a Hrom Ho.
  (* as_owned_static GrantB = Tfib_owned_static; in_zr a r = fst r <= a < fst r + snd r. *)
  assert (Ho' : Exists (fun r => fst r <= a < fst r + snd r) Tfib_owned_static).
  { revert Ho. cbn [as_owned_static GrantB]. apply Exists_impl. intros r Hr. exact Hr. }
  pose proof (dec_ro_gate_holds a (owned_in_rom_ro_ranges a Hrom Ho') Ho') as HG.
  apply Exists_exists in HG as (c & Hc & a' & v & Ha & Hv & Hrg & Hw).
  apply Exists_exists. exists c. split.
  - cbn [as_const GrantB]. unfold Tfib_const. apply in_app_iff. right. apply in_app_iff. left. exact Hc.
  - exists a', v. rewrite ro_img_word_dec. split; [exact Ha | split; [exact Hv | split; [exact Hrg | exact Hw]]].
Qed.
