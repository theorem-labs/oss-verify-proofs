(* libreac/fuzz_decode, build asan-ubsan: ro_owned_pinned at image B's generated start-up record TfibB (lib/B/YD2l.v).
   Rule 24: no function is proved here. Kind: start-up facts; a fact about the image and its asyms record, proved by
   computation.
   - ro_owned_pinned / ro_img_word: the image-generic definitions of lib/A/DecodeROPinned.v:33-52 (blob 7e20ccff6520,
     a working branch 2f6c3143ebd; segs and B are parameters), taken by Require, not Import. This file
     names nothing else of lib/A.
   - img_word, pinb, zbytes, ro_pinned_chk, their soundness lemmas, the gate and the instance: lib/A/DecodeROPinned.v
     :54-163 restated over image B: tfibsegs (lib/B/YB1v.v:11), Tfib_const_abs and Tfib_owned_static (lib/B/YF0m.v),
     TfibB; dec_ro_ranges -> decB_ro_ranges, dec_ro_pinned -> decB_ro_pinned, dec_ro_gate -> decB_ro_gate.
   - decB_ro_ranges: the two non-writable PT_LOADs of fuzz_decode.asan-ubsan (sha256 5d05689fd5b1..., the bytes
     projects/libreac/fuzz_decode/harness.yaml pins for asan-ubsan) by (p_vaddr, p_filesz), [0x10000, 0x2f054) (R) and
     [0x30054, 0x97d50) (R E) (pyelftools readelf.py -l). No step trusts them: owned_ro_ok checks against the loaded
     segments that every owned range meeting a non-writable segment lies inside one of them, and decB_ro_pinned checks
     every owned byte inside them against the image.
   - as_const TfibB ly = Tfib_const ly = Tfib_const_sym ++ Tfib_const_abs ++ Tfib_const_shadow (lib/B/YF0m.v:302) and
     as_owned_static TfibB = Tfib_owned_static (lib/B/YD2l.v:33); the gate runs over Tfib_const_abs. *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YI04 YI00 YM05 YF0p.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require DecodeROPinned.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import YF0l YF0m YCej YD2l YB1v.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* The gate, over image B's tfibsegs. *)
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
(* The two non-writable PT_LOADs of fuzz_decode.asan-ubsan, (p_vaddr, p_filesz). *)
Definition decB_ro_ranges : list (Z * Z) := [(0x10000, 0x1f054); (0x30054, 0x67cfc)].
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
  forallb (fun a => existsb (fun c => pinb c a) l) (zbytes lo (hi - lo))) decB_ro_ranges) owned.
Lemma ro_pinned_chk_sound : forall owned l, ro_pinned_chk owned l = true ->
forall a, Exists (fun s => fst s <= a < fst s + snd s) decB_ro_ranges -> Exists (fun r => fst r <= a < fst r + snd r) owned ->
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
Theorem decB_ro_pinned : ro_pinned_chk Tfib_owned_static Tfib_const_abs = true.
Proof. vm_compute. reflexivity. Qed.
Definition decB_ro_gate : Prop :=
forall a, Exists (fun s => fst s <= a < fst s + snd s) decB_ro_ranges -> Exists (fun r => fst r <= a < fst r + snd r) Tfib_owned_static ->
Exists (fun c => exists a' v, c_at c = ANum a' /\ c_val c = AV (ANum v) /\ a' <= a < a' + Z.of_nat (c_w c) /\
  img_word a' (c_w c) = Some v) Tfib_const_abs.
Lemma decB_ro_gate_holds : decB_ro_gate.
Proof. exact (ro_pinned_chk_sound Tfib_owned_static Tfib_const_abs decB_ro_pinned). Qed.

(* The instance, for tfibsegs and TfibB. *)
(* ro_img_word at tfibsegs is img_word: the same recursion. *)
Lemma ro_img_word_dec : forall w a, DecodeROPinned.ro_img_word tfibsegs a w = img_word a w.
Proof.
  induction w as [|w IH]; intro a; cbn [DecodeROPinned.ro_img_word img_word]; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

(* A byte that is both owned (Tfib_owned_static) and in_rom is inside decB_ro_ranges: every owned range that meets a
   non-writable loaded segment lies within a decB_ro_range. owned_ro_ok is that, by vm_compute. *)
Definition seg_ov (r : Z * Z) (sg : Segment) : bool :=
  andb (negb (seg_writable sg))
    (andb (Z.of_N (seg_base sg) <? fst r + snd r) (fst r <? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))).
Definition owned_ro_ok : bool :=
  forallb (fun r => implb (existsb (seg_ov r) tfibsegs)
    (existsb (fun q => (fst q <=? fst r) && (fst r + snd r <=? fst q + snd q)) decB_ro_ranges)) Tfib_owned_static.
Lemma owned_ro_ok_true : owned_ro_ok = true.
Proof. vm_compute. reflexivity. Qed.

Lemma owned_in_rom_ro_ranges : forall a, in_rom tfibsegs a ->
  Exists (fun r => fst r <= a < fst r + snd r) Tfib_owned_static ->
  Exists (fun r => fst r <= a < fst r + snd r) decB_ro_ranges.
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
Theorem dec_ro_owned_pinned : DecodeROPinned.ro_owned_pinned tfibsegs TfibB.
Proof.
  intros ly a Hrom Ho.
  (* as_owned_static TfibB = Tfib_owned_static; in_zr a r = fst r <= a < fst r + snd r. *)
  assert (Ho' : Exists (fun r => fst r <= a < fst r + snd r) Tfib_owned_static).
  { revert Ho. cbn [as_owned_static TfibB]. apply Exists_impl. intros r Hr. exact Hr. }
  pose proof (decB_ro_gate_holds a (owned_in_rom_ro_ranges a Hrom Ho') Ho') as HG.
  apply Exists_exists in HG as (c & Hc & a' & v & Ha & Hv & Hrg & Hw).
  apply Exists_exists. exists c. split.
  - cbn [as_const TfibB]. unfold Tfib_const. apply in_app_iff. right. apply in_app_iff. left. exact Hc.
  - exists a', v. rewrite ro_img_word_dec. split; [exact Ha | split; [exact Hv | split; [exact Hrg | exact Hw]]].
Qed.
