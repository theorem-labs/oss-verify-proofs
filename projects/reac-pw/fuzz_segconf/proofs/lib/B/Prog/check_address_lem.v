(* the image-B port of lib/A/Prog/check_address_lem.v (commit 254b4716bf4f): helper facts of
   the walk of check_address on fuzz_segconf image B (lib/B/Prog/check_address.v). A text of SegModel read through a
   state's reader as the byte list the string wrappers' contracts take, and the strncmp wrapper's model value on two
   C strings as SegModel's strncmp. No image number appears here; only the Require lines differ from image A's
   file: the kit copies YG0f YG0n and SegABase come from lib.B (commit 694f3575dda2). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegABase.
Import ListNotations.
Open Scope Z_scope.

Lemma ca_unsigned8 : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof.
intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. exact Hz.
Qed.

Lemma ca_zs_zb : forall l, Forall (fun z => 0 <= z < 256) l -> seg_spec.zs (seg_spec.zb l) = l.
Proof.
induction l as [|z l IH]; intros H; [reflexivity|].
inversion H as [|? ? Hz Hl]; subst. cbn [seg_spec.zs seg_spec.zb map].
unfold seg_spec.zs, seg_spec.zb in IH. rewrite (ca_unsigned8 z Hz), (IH Hl). reflexivity.
Qed.

Lemma ca_zb_length : forall l, length (seg_spec.zb l) = length l.
Proof. intros l. unfold seg_spec.zb. apply length_map. Qed.

Lemma ca_zs_length : forall bs, length (seg_spec.zs bs) = length bs.
Proof. intros bs. unfold seg_spec.zs. apply length_map. Qed.

(* no byte of a list is NUL exactly when no value of it is 0 *)
Lemma ca_nul_free_bytes : forall bs : list byte, ~ In 0 (seg_spec.zs bs) -> ~ In ZB0 bs.
Proof. intros bs H Hin. apply H. unfold seg_spec.zs. apply (in_map bv_unsigned) in Hin. exact Hin. Qed.

Lemma ca_nul_free_zs : forall bs : list byte, ~ In ZB0 bs -> ~ In 0 (seg_spec.zs bs).
Proof.
intros bs H Hin. apply H. unfold seg_spec.zs in Hin. apply in_map_iff in Hin as (b & Hb & Hin).
replace ZB0 with b; [exact Hin|]. apply bv_eq. rewrite Hb. reflexivity.
Qed.

Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* a reader built from a memory gives byte values *)
Lemma ca_view_byte : forall segs H mem a z, aview segs H mem a = Some z -> 0 <= z < 256.
Proof.
intros segs H mem a z Hv. unfold aview in Hv.
match type of Hv with option_map _ ?o = _ => destruct o as [b|] end; cbn in Hv; [|discriminate Hv].
injection Hv as <-. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R. exact R.
Qed.

Lemma ca_zs_range : forall segs H mem p l, sa_zs (aview segs H mem) p l -> Forall (fun z => 0 <= z < 256) l.
Proof.
intros segs H mem p l Hz. apply Forall_forall. intros z Hin.
apply (In_nth l z 0) in Hin as (i & Hi & Hn). specialize (Hz i Hi). rewrite Hn in Hz.
exact (ca_view_byte _ _ _ _ _ Hz).
Qed.

(* the C string s at p, as the bytes, terminator and NUL-freedom the wrappers' contracts state of a byte list *)
Lemma ca_strz_bytes : forall segs H mem p s, sa_strz (aview segs H mem) p s ->
  sa_bytes (aview segs H mem) p (seg_spec.zb s ++ [ZB0]) /\ ~ In ZB0 (seg_spec.zb s) /\
  seg_spec.zs (seg_spec.zb s) = s /\ length (seg_spec.zb s) = length s.
Proof.
intros segs H mem p s [Hz Hn].
pose proof (ca_zs_range segs H mem p _ Hz) as R. apply Forall_app in R as [Rs R0].
assert (Ezs : seg_spec.zs (seg_spec.zb s) = s) by exact (ca_zs_zb s Rs).
split; [|split; [|split; [exact Ezs | apply ca_zb_length]]].
- intros i Hi. replace (seg_spec.zb s ++ [ZB0]) with (seg_spec.zb (s ++ [0])) in *
    by (unfold seg_spec.zb; rewrite map_app; reflexivity).
  rewrite ca_zb_length in Hi. rewrite (Hz i Hi). f_equal.
  unfold seg_spec.zb. change ZB0 with (Z_to_bv 8 0). rewrite map_nth. symmetry. apply ca_unsigned8.
  apply (Forall_nth (fun z => 0 <= z < 256) (s ++ [0])); [apply Forall_app; split; [exact Rs | exact R0] | exact Hi].
- apply ca_nul_free_bytes. rewrite Ezs. exact Hn.
Qed.

End r.

(* the strncmp wrapper's model walk on two C strings (got's bytes and NUL; want's bytes, NUL and any following bytes)
   is SegModel's strncmp_go on their values, for every count: each NUL stops the walk before a list runs out *)
Lemma ca_walk_bridge : forall (bg bw sl : list byte) (k : nat),
  ~ In 0 (seg_spec.zs bg) -> ~ In 0 (seg_spec.zs bw) ->
  StrFun.strncmp_walk (bg ++ [ZB0]) (bw ++ ZB0 :: sl) k =
  Some (SegModel.strncmp_go (seg_spec.zs bg) (seg_spec.zs bw) k).
Proof.
unfold seg_spec.zs.
induction bg as [|x bg IH]; intros bw sl k NG NW.
- destruct bw as [|y bw]; destruct k; reflexivity.
- cbn [map In] in NG. assert (Hx : bv_unsigned x <> 0) by tauto.
  assert (NG' : ~ In 0 (map bv_unsigned bg)) by tauto.
  destruct bw as [|y bw].
  + cbn [app map StrFun.strncmp_walk]. rewrite (proj2 (Z.eqb_neq _ _) Hx). destruct k; reflexivity.
  + cbn [map In] in NW. assert (Hy : bv_unsigned y <> 0) by tauto.
    assert (NW' : ~ In 0 (map bv_unsigned bw)) by tauto.
    destruct k as [|k].
    * cbn [app map StrFun.strncmp_walk SegModel.strncmp_go SegModel.hd0].
      rewrite (proj2 (Z.eqb_neq _ _) Hx), (proj2 (Z.eqb_neq _ _) Hy). reflexivity.
    * cbn [app map StrFun.strncmp_walk SegModel.strncmp_go].
      rewrite !(proj2 (Z.eqb_neq _ _) Hx), !(proj2 (Z.eqb_neq _ _) Hy).
      destruct (Z.eqb_spec (bv_unsigned x) (bv_unsigned y)) as [E|E]; cbn [negb orb andb Nat.eqb].
      -- apply IH; assumption.
      -- reflexivity.
Qed.

(* the value the strncmp wrapper's contract states, at n = the length of want *)
Lemma ca_strncmp_model : forall (bg bw : list byte),
  ~ In 0 (seg_spec.zs bg) -> ~ In 0 (seg_spec.zs bw) ->
  StrFun.strncmp_model (bg ++ [ZB0]) (bw ++ [ZB0]) (Z.of_nat (length bw)) =
  Some (SegModel.strncmp (seg_spec.zs bg) (seg_spec.zs bw) (length bw)).
Proof.
intros bg bw NG NW. unfold StrFun.strncmp_model.
destruct (length bw) as [|n] eqn:L.
- reflexivity.
- replace (Z.to_nat (Z.of_nat (S n) - 1)) with n by lia.
  change (Z.of_nat (S n) =? 0) with false. unfold SegModel.strncmp. cbv iota beta.
  apply (ca_walk_bridge bg bw []); assumption.
Qed.

(* SegModel's strlen of a NUL-free text is its length *)
Lemma ca_strlen_id : forall s, ~ In 0 s -> SegModel.strlen s = length s.
Proof. intros s H. apply SegModel.strlen_id. exact H. Qed.

(* the abort arm's premise, on the byte lists the strncmp wrapper sees: the model value is 0 *)
Lemma ca_cmp_zero : forall gs ws,
  Forall (fun z => 0 <= z < 256) gs -> Forall (fun z => 0 <= z < 256) ws -> ~ In 0 gs -> ~ In 0 ws ->
  SegModel.strncmp gs ws (SegModel.strlen ws) = 0 ->
  StrFun.strncmp_model (seg_spec.zb gs ++ [ZB0]) (seg_spec.zb ws ++ [ZB0]) (Z.of_nat (length (seg_spec.zb ws))) = Some 0.
Proof.
intros gs ws Rg Rw Ng Nw H.
rewrite ca_strncmp_model by (rewrite ca_zs_zb; assumption).
rewrite !ca_zs_zb by assumption. rewrite ca_zb_length. rewrite <- (ca_strlen_id ws Nw), H. reflexivity.
Qed.
