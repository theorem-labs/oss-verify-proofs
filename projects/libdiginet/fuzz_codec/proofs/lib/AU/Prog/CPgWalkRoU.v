(* Modified by Theorem Labs, 2026-10: copied from lib/A/Prog/CPgWalkRo.v and moved to image B (the ASan-UBSan build):
   the image-A core modules are image B's (lib/AU), YImgTop is YImgTopU, the CA_ constants are CB_ ones with
   image B's values; lemma and tactic names unchanged. *)
(* The string literals of image B as data a walk reads or hands to a callee.
   The A-level contracts give the image's read-only bytes through cimg_rd's arodata_okP, which holds only for a byte
   that is in no owned static of the runtime and not errno. lib/A/YCeh.v's TfibLib names those two facts for the
   tables of lib_const_addr only, not for the 33 string literals of CB_ROSTRS. cpw_rows_free is that fact for a list
   of rows; a walk that needs a literal's VALUE (the strcmp wrapper's str_meet, a callee's cstr_rd) takes
   `cpw_rows_free B CB_ROSTRS` as a hypothesis, and the closing discharges it from the runtime's symbol record
   (cpw_rows_free_syms: TfibSyms B, by computation over Tfib_owned_static).
   - cpw_row_view / cpw_row_mbyte: a byte of such a row reads as the image's byte;
   - cpw_img_list / cpw_row_garr8: the row's bytes as the list of Z a cstr_rd / garr8 premise names;
   - cpw_row_crd: the row's crd_ok in any state of the journal, from the start-up facts. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import YImgTopU.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCef YF0l YF0m YCej YCeh YCem YCep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CodecRo CodecGlobs CPgWalkU CPgWalkImgU.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* every byte of every row is in no owned static of the runtime and not errno *)
Definition cpw_rows_free (B : asyms) (l : list (Z * Z)) : Prop :=
Forall (fun r => forall i, 0 <= i < snd r ->
  ~ Exists (in_zr (fst r + i)) (as_owned_static B) /\ ~ (as_errno B <= fst r + i < as_errno B + 4)) l.

(* the check by computation: each row lies off each owned static and below errno *)
Definition cpw_rows_off (l : list (Z * Z)) : bool :=
forallb (fun r => forallb (fun o => (fst o + snd o <=? fst r) || (fst r + snd r <=? fst o)) Tfib_owned_static
                  && (fst r + snd r <=? TFIB_ERRNO)) l.
Lemma cpw_rows_free_of_off : forall B l, TfibSyms B -> cpw_rows_off l = true -> cpw_rows_free B l.
Proof.
intros B l TB Hc. unfold cpw_rows_free. apply Forall_forall. intros r Hr i Hi.
pose proof (proj1 (forallb_forall _ _) Hc r Hr) as Hb. cbv beta in Hb.
apply andb_prop in Hb as [Ho He]. apply Z.leb_le in He.
split.
- rewrite (ts_owned B TB). intros HE. apply Exists_exists in HE as (o & Hin & [H1 H2]).
  pose proof (proj1 (forallb_forall _ _) Ho o Hin) as Hb. cbv beta in Hb.
  apply Bool.orb_prop in Hb as [Hb|Hb]; apply Z.leb_le in Hb; lia.
- rewrite (ts_errno B TB). lia.
Qed.
Lemma cpw_rows_free_syms : forall B, TfibSyms B -> cpw_rows_free B CB_ROSTRS.
Proof. intros B TB. apply (cpw_rows_free_of_off B CB_ROSTRS TB). vm_compute. reflexivity. Qed.
Lemma cpw_rows_free_In : forall B l q n i, cpw_rows_free B l -> In (q, n) l -> 0 <= i < n ->
~ Exists (in_zr (q + i)) (as_owned_static B) /\ ~ (as_errno B <= q + i < as_errno B + 4).
Proof. intros B l q n i H Hin Hi. exact (proj1 (Forall_forall _ _) H (q, n) Hin i Hi). Qed.

(* the bytes of [q, q + n) of the image file, as Z (0 where the file holds none) *)
Definition cpw_img_list (q n : Z) : list Z :=
map (fun k => match img_byte tfibsegs (q + Z.of_nat k) with Some b => bv_unsigned b | None => 0 end)
    (seq 0 (Z.to_nat n)).
Lemma cpw_img_list_length : forall q n, 0 <= n -> Z.of_nat (length (cpw_img_list q n)) = n.
Proof. intros q n Hn. unfold cpw_img_list. rewrite length_map, length_seq. lia. Qed.
Lemma cpw_nth_map_seq : forall (f : nat -> Z) k n d, (k < n)%nat -> nth k (map f (seq 0 n)) d = f k.
Proof.
intros f k n d Hk. rewrite (nth_indep _ d (f 0%nat)) by (rewrite length_map, length_seq; lia).
rewrite map_nth, seq_nth by lia. reflexivity.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variables rlo rhi : Z.
(* a byte of a free row of the read-only data reads as the image's byte *)
Lemma cpw_row_mbyte : forall (W : world tfibsegs) memc l q n i,
arodata_okP tfibsegs rlo rhi B (aview tfibsegs (w_H W) memc) -> cpw_rows_free B l -> In (q, n) l ->
(forall j, 0 <= j < n -> in_roP tfibsegs rlo rhi (q + j)) -> 0 <= i < n ->
mbyte tfibsegs (mrestrict (w_H W) memc) (q + i) = img_byte tfibsegs (q + i).
Proof.
intros W memc l q n i HRO HF Hin Hro Hi.
destruct (cpw_rows_free_In B l q n i HF Hin Hi) as (Ho & He).
apply (cpg_img_rd B rlo rhi W memc (q + i) 1 HRO); [intros a Ha; replace a with (q + i) by lia; exact (Hro i Hi)
| intros a Ha; replace a with (q + i) by lia; exact Ho | intros a Ha; replace a with (q + i) by lia; exact He | lia].
Qed.
Lemma cpw_row_view : forall (W : world tfibsegs) memc l q n i,
arodata_okP tfibsegs rlo rhi B (aview tfibsegs (w_H W) memc) -> cpw_rows_free B l -> In (q, n) l ->
(forall j, 0 <= j < n -> in_roP tfibsegs rlo rhi (q + j)) -> 0 <= i < n ->
aview tfibsegs (w_H W) memc (q + i) = option_map (fun b : byte => bv_unsigned b) (img_byte tfibsegs (q + i)).
Proof.
intros W memc l q n i HRO HF Hin Hro Hi. unfold aview.
rewrite (cpw_row_mbyte W memc l q n i HRO HF Hin Hro Hi). reflexivity.
Qed.
(* the row's bytes as a garr8 *)
Lemma cpw_row_garr8 : forall (W : world tfibsegs) memc l q n,
arodata_okP tfibsegs rlo rhi B (aview tfibsegs (w_H W) memc) -> cpw_rows_free B l -> In (q, n) l ->
(forall j, 0 <= j < n -> in_roP tfibsegs rlo rhi (q + j)) -> cpg_img_some q n = true -> 0 <= n ->
garr8 tfibsegs (mrestrict (w_H W) memc) q (cpw_img_list q n).
Proof.
intros W memc l q n HRO HF Hin Hro Hs Hn j Hj.
assert (Hl : length (cpw_img_list q n) = Z.to_nat n) by (unfold cpw_img_list; rewrite length_map, length_seq; reflexivity).
rewrite Hl in Hj.
assert (Hk : In j (seq 0 (Z.to_nat n))) by (apply in_seq; lia).
pose proof (proj1 (forallb_forall _ _) Hs j Hk) as Hb. cbv beta in Hb.
assert (Hnth : nth j (cpw_img_list q n) 0 =
  match img_byte tfibsegs (q + Z.of_nat j) with Some b => bv_unsigned b | None => 0 end)
  by (unfold cpw_img_list; apply (cpw_nth_map_seq
       (fun k => match img_byte tfibsegs (q + Z.of_nat k) with Some b => bv_unsigned b | None => 0 end)); exact Hj).
rewrite Hnth.
destruct (img_byte tfibsegs (q + Z.of_nat j)) as [b|] eqn:Eb; [|discriminate].
pose proof (bv_unsigned_in_range 8 b) as Rb. change (bv_modulus 8) with 256 in Rb.
split; [|exact Rb].
apply cpg_val_mem1; [exact Rb|].
rewrite (cpw_row_mbyte W memc l q n (Z.of_nat j) HRO HF Hin Hro ltac:(lia)), Eb.
f_equal. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
(* the row's crd_ok, in any state AR holds of whose read-only data is the image's *)
Lemma cpw_row_crd : forall G l ly S (W : world tfibsegs) memc md sp T q n,
AR tfibsegs B ly S W memc md -> globs_marked tfibsegs B G -> In (q, n) G -> img_shadow_vis tfibsegs B ->
arodata_okP tfibsegs rlo rhi B (aview tfibsegs (w_H W) memc) -> cpw_rows_free B l -> In (q, n) l ->
(forall j, 0 <= j < n -> in_roP tfibsegs rlo rhi (q + j)) -> cpg_img_some q n = true ->
0 < n -> 0 <= q -> IMG_LO + 64 <= q -> q + n + 64 <= IMG_HI -> q + n <= 2 ^ 63 ->
amem_range q n -> q + n <= sp - T ->
crd_ok tfibsegs W memc sp T q n.
Proof.
intros G l ly S W memc md sp T q n HAR HG HinG HV HRO HF Hin Hro Hs Hn Hq Hlo Hhi H63 Ham Hwin.
split; [exact Hq|]. split; [exact H63|].
split.
{ intros a Ha. replace a with (q + (a - q)) by lia.
  rewrite (cpw_row_view W memc l q n (a - q) HRO HF Hin Hro ltac:(lia)).
  assert (Hk : In (Z.to_nat (a - q)) (seq 0 (Z.to_nat n))) by (apply in_seq; lia).
  pose proof (proj1 (forallb_forall _ _) Hs _ Hk) as Hb. cbv beta in Hb.
  rewrite Z2Nat.id in Hb by lia.
  destruct (img_byte tfibsegs (q + (a - q))); [discriminate | discriminate Hb]. }
split; [exact (ro_usable_glob tfibsegs B G ly S W memc md q n q n HG HinG HAR ltac:(lia) ltac:(lia))|].
split; [intros _; exact (ro_hull tfibsegs B ly S W memc md q n HV HAR Hn Hlo Hhi)|].
split; [exact Ham|]. left. exact Hwin.
Qed.
End b.
