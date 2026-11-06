(* Modified by Theorem Labs, 2026-10: copied from lib/A/Prog/CPgWalkImg.v and moved to image B (the ASan-UBSan build):
   the image-A core modules are image B's (lib/AU), YImgTop is YImgTopU, the CA_ constants are CB_ ones with
   image B's values; lemma and tactic names unchanged. *)
(* The two region facts an image-B walk of codec's own code needs when it reads a table of the image.
   - cpg_img_region_ok: the table's bytes, as a region holding the image's own bytes. Its premises are the
     walk's read-only-data fact (lib/A/Prog/CPgBase.v arodata_okP) over a range the image holds.
   - cpg_shadow_region_ok: the table's shadow bytes, as a region based at the shadow-offset atom 32.
   Why the second one is there: an instrumented check of an address the code holds as a constant folds to
   `SOff 32 off`, the shadow-offset atom plus a literal, and not to `(x >> 3) + Bx`, so the token layer of
   lib/Reusable/YCbn.v (match_x) never sees it and the run stops with SR_load (Some 32) off. The walk
   carries those shadow bytes as an ordinary region instead. Their values are the start-up certificate's
   (lib/A/Prog/CodecRo.v globs_marked, lib/Reusable/YG0v.v block_shadow): 0 for a whole granule of the
   registered global, the size modulo 8 for its partial last granule.
   Both are stated over an abstract segment list's symbol record B; the ranges are the caller's. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CodecRo CodecGlobs CPgWalkU.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ================================ the table's own bytes ================================ *)
(* the region: [q, q + n), read-only, holding the image's bytes *)
Definition cpg_img_region (q n : Z) : YP09.region :=
YP09.mkRegion None q (q + n) 0 0 [YP09.mkChunk q (CImg n)].
(* the image file holds every byte of [q, q + n) (checked by computation at the walk's own range) *)
Definition cpg_img_some (q n : Z) : bool :=
forallb (fun k => match img_byte tfibsegs (q + Z.of_nat k) with Some _ => true | None => false end)
        (seq 0 (Z.to_nat n)).

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c.
Variable B : asyms.
Variables rlo rhi : Z.
(* on a range of the read-only data the bytes of memory are the image's *)
Lemma cpg_img_rd : forall (W : world tfibsegs) memc q n,
arodata_okP tfibsegs rlo rhi B (aview tfibsegs (w_H W) memc) ->
(forall a, q <= a < q + n -> in_roP tfibsegs rlo rhi a) ->
(forall a, q <= a < q + n -> ~ Exists (in_zr a) (as_owned_static B)) ->
(forall a, q <= a < q + n -> ~ (as_errno B <= a < as_errno B + 4)) ->
forall a, q <= a < q + n -> mbyte tfibsegs (mrestrict (w_H W) memc) a = img_byte tfibsegs a.
Proof.
intros W memc q n HRO Hin Hown Herr a Ha.
pose proof (HRO a (Hin a Ha) (Hown a Ha) (Herr a Ha)) as H. unfold aview in H. unfold img_byte.
destruct (mbyte tfibsegs (mrestrict (w_H W) memc) a) as [b|];
destruct (seg_rom tfibsegs (Z_to_bv 64 a)) as [b'|]; cbn in H;
[f_equal; apply bv_eq; injection H as H; exact H | discriminate | discriminate | reflexivity].
Qed.
Lemma cpg_img_region_ok : forall E (W : world tfibsegs) memc q n,
arodata_okP tfibsegs rlo rhi B (aview tfibsegs (w_H W) memc) ->
(forall a, q <= a < q + n -> in_roP tfibsegs rlo rhi a) ->
(forall a, q <= a < q + n -> ~ Exists (in_zr a) (as_owned_static B)) ->
(forall a, q <= a < q + n -> ~ (as_errno B <= a < as_errno B + 4)) ->
cpg_img_some q n = true -> 0 <= q -> 0 <= n -> q + n <= 2 ^ 64 ->
region_ok tfibsegs E (mrestrict (w_H W) memc) (cpg_img_region q n).
Proof.
intros E W memc q n HRO Hin Hown Herr Hsome Hq Hn Hqn.
pose proof (cpg_img_rd W memc q n HRO Hin Hown Herr) as HRD.
unfold cpg_img_region, region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
intros i Hi. cbn [YP09.c_off YP09.c_val c_len cv_len cbyte] in Hi |- *. rewrite !Z.add_0_l.
assert (Hk : In (Z.to_nat i) (seq 0 (Z.to_nat n))) by (apply in_seq; lia).
pose proof (proj1 (forallb_forall _ _) Hsome (Z.to_nat i) Hk) as Hb. cbn beta in Hb.
rewrite Z2Nat.id in Hb by lia.
destruct (img_byte tfibsegs (q + i)) as [b|] eqn:Eb; [|discriminate].
exists b. split; [reflexivity|]. rewrite (HRD (q + i) ltac:(lia)). exact Eb.
Qed.
End c.

(* ================================ the table's shadow bytes ================================ *)
(* the shadow bytes of a registered global (q, sz): one chunk per granule, 0 for a whole granule and
   sz mod 8 for the partial last one (lib/Reusable/YG0v.v block_shadow) *)
Fixpoint cpg_sh_chunks (c0 sz : Z) (k : nat) (i : Z) : list YP09.chunk :=
match k with
| O => []
| S k' => YP09.mkChunk (c0 + i) (CVal 1 (SLit (if i <? sz / 8 then 0 else sz mod 8)))
          :: cpg_sh_chunks c0 sz k' (i + 1)
end.
Definition cpg_shadow_region (q sz : Z) : YP09.region :=
YP09.mkRegion (Some 32%nat) (q / 8) (q / 8 + (sz + 7) / 8) 0 0
(cpg_sh_chunks (q / 8) sz (Z.to_nat ((sz + 7) / 8)) 0).

Section d.
Lemma cpg_le_byte1 : forall v, 0 <= v < 256 -> le_byte v 1 0 = v.
Proof.
intros v Hv. unfold le_byte. change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r, (Z.mod_small v 256) by lia. apply Z.mod_small. lia.
Qed.
Lemma cpg_val_mem1 : forall m a v, 0 <= v < 256 -> mbyte tfibsegs m a = Some (Z_to_bv 8 v) ->
val_mem tfibsegs m a 1 v.
Proof.
intros m a v Hv Hm k Hk. assert (Ek : k = 0%nat) by lia. subst k.
change (Z.of_nat 0) with 0. rewrite Z.add_0_r, Hm. f_equal. f_equal. symmetry.
apply cpg_le_byte1. exact Hv.
Qed.
Lemma cpg_sh_chunks_ok : forall E m sz base c0 k i,
0 <= sz ->
(forall j, 0 <= j < Z.of_nat k ->
 mbyte tfibsegs m (base + (c0 + (i + j))) = Some (Z_to_bv 8 (if i + j <? sz / 8 then 0 else sz mod 8))) ->
Forall (YP09.chunk_ok tfibsegs E m base) (cpg_sh_chunks c0 sz k i).
Proof.
intros E m sz base c0 k. induction k as [|k IH]; intros i Hsz H; cbn [cpg_sh_chunks]; [apply Forall_nil|].
pose proof (Z.mod_pos_bound sz 8 ltac:(lia)) as Hmod.
set (v := if i <? sz / 8 then 0 else sz mod 8).
assert (Hv : 0 <= v < 256) by (unfold v; destruct (i <? sz / 8); lia).
constructor.
- apply (chunk_ok_val tfibsegs E m base (c0 + i) 1 (SLit v) v);
  [reflexivity | change (2 ^ (8 * Z.of_N 1)) with 256; lia | cbn; lia |].
  apply cpg_val_mem1; [exact Hv|].
  pose proof (H 0 ltac:(cbn; lia)) as Hb. rewrite Z.add_0_r in Hb. exact Hb.
- apply IH; [exact Hsz|]. intros j Hj.
  replace (i + 1 + j) with (i + (1 + j)) by lia.
  apply H. rewrite Nat2Z.inj_succ in *. lia.
Qed.
End d.

Section e.
Variable B : asyms.
Lemma cpg_shadow_region_ok : forall E (W : world tfibsegs) memc ly S md G q sz,
globs_marked tfibsegs B G -> In (q, sz) G -> AR tfibsegs B ly S W memc md ->
ew E 32 = Z_to_bv 64 SB -> 0 <= q -> q + sz <= 2 ^ 63 ->
region_ok tfibsegs E (mrestrict (w_H W) memc) (cpg_shadow_region q sz).
Proof.
intros E W memc ly S md G q sz HG Hin HAR E32 Hq Hqsz.
pose proof (HG ly S W memc md q sz Hin HAR) as (Hq8 & Hsz & HB).
assert (Hbase : base_val E (Some 32%nat) = SB)
  by (cbn [base_val]; rewrite E32; apply unsigned_lit_small; unfold SB; lia).
assert (Hd1 : 0 <= q / 8) by (apply Z.div_pos; lia).
assert (Hd2 : q / 8 <= q) by (apply Z.div_le_upper_bound; lia).
assert (Hd3 : 0 <= (sz + 7) / 8) by (apply Z.div_pos; lia).
assert (Hd4 : (sz + 7) / 8 <= sz + 7) by (apply Z.div_le_upper_bound; lia).
unfold cpg_shadow_region, region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
rewrite Hbase.
split; [unfold SB; lia|]. split; [unfold SB; lia|]. split; [intros o Ho; lia|].
apply (cpg_sh_chunks_ok E (mrestrict (w_H W) memc) sz SB (q / 8) _ 0 Hsz).
intros j Hj. rewrite Z2Nat.id in Hj by lia. rewrite Z.add_0_l.
pose proof (HB j ltac:(lia)) as Hv.
unfold shadow_of_addr in Hv. rewrite <- SB_SHADOW_OFF in Hv.
replace (SB + (q / 8 + j)) with (SB + q / 8 + j) by lia.
unfold aview in Hv.
destruct (mbyte tfibsegs (mrestrict (w_H W) memc) (SB + q / 8 + j)) as [b|] eqn:Eb; cbn in Hv; [|discriminate].
injection Hv as Hv. rewrite <- Hv, Z_to_bv_bv_unsigned. reflexivity.
Qed.
End e.
End b.
