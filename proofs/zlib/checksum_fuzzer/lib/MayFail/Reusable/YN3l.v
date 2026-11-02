(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN3l.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0l.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP08.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP04.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO00.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN3v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section g.
Variable segs : list Segment.
Fixpoint find_lit2 (cs : list chunk) (img : bool) (a : Z) : option Z :=
match cs with
| [] => None
| c :: cs' =>
if (c_off c <=? a) && (a <? c_off c + c_len c) then
match c_val c with
| CZero _ => Some 0
| CVal _ (SLit z) => Some ((Z.shiftr (zcanon z) (8 * (a - c_off c))) mod 256)
| CImg _ => if img then match img_byte segs a with Some b => Some (bv_unsigned b) | None => None end
else find_lit2 cs' img a
| _ => find_lit2 cs' img a
end
else find_lit2 cs' img a
end.
Lemma find_lit2_sound : forall E m base cs img a z,
Forall (chunk_ok segs E m base) cs -> (img = true -> base = 0) ->
find_lit2 cs img a = Some z -> mbyte segs m (base + a) = Some (Z_to_bv 8 z).
Proof.
intros E m base cs img a z Hcs Himg. induction Hcs as [|c cs Hc Hcs IH]; cbn; intros H; [discriminate|].
destruct ((c_off c <=? a) && (a <? c_off c + c_len c)) eqn:Hin; [|apply IH; exact H].
apply andb_prop in Hin as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
destruct (Hc (a - c_off c) ltac:(lia)) as (b & Hb1 & Hb2).
replace (base + c_off c + (a - c_off c)) with (base + a) in Hb2 by lia.
destruct (c_val c) as [w v|len|len|d s len] eqn:Hcv.
- destruct v; try (apply IH; exact H). injection H as <-.
cbn [cbyte sv_denot] in Hb1. injection Hb1 as <-. rewrite Hb2. f_equal.
unfold byte_of_word. rewrite unsigned_lit, Z_to_bv8_mod. reflexivity.
- injection H as <-. cbn [cbyte] in Hb1. injection Hb1 as <-. exact Hb2.
- destruct img.
+ specialize (Himg eq_refl). subst base. cbn [cbyte] in Hb1.
replace (0 + c_off c + (a - c_off c)) with a in Hb1 by lia.
rewrite Hb1 in H. injection H as <-. rewrite Z_to_bv_bv_unsigned. exact Hb2.
+ apply IH. exact H.
- apply IH. exact H.
Qed.
Fixpoint read_lits2 (cs : list chunk) (img : bool) (off : Z) (n : nat) : option (list Z) :=
match n with
| O => Some []
| S n' => match find_lit2 cs img off, read_lits2 cs img (off + 1) n' with
| Some z, Some zs => Some (z :: zs)
| _, _ => None
end
end.
Lemma read_lits2_length : forall cs img n off zs, read_lits2 cs img off n = Some zs -> length zs = n.
Proof.
intros cs img n. induction n as [|n IH]; intros off zs H; cbn in H.
- injection H as <-. reflexivity.
- destruct (find_lit2 cs img off) as [z|]; [|discriminate].
destruct (read_lits2 cs img (off + 1) n) as [zs'|] eqn:Hr; [|discriminate].
injection H as <-. cbn. f_equal. eapply IH. exact Hr.
Qed.
Lemma read_lits2_sound : forall E m base cs img n off zs,
Forall (chunk_ok segs E m base) cs -> (img = true -> base = 0) ->
read_lits2 cs img off n = Some zs ->
mbytes_at segs m (base + off) (map (Z_to_bv 8) zs).
Proof.
intros E m base cs img n. induction n as [|n IH]; intros off zs Hcs Himg H; cbn in H.
- injection H as <-. apply mbytes_at_nil.
- destruct (find_lit2 cs img off) as [z|] eqn:Hz; [|discriminate].
destruct (read_lits2 cs img (off + 1) n) as [zs'|] eqn:Hr; [|discriminate].
injection H as <-. cbn [map].
change (Z_to_bv 8 z :: ?l) with ([Z_to_bv 8 z] ++ l). apply mbytes_at_app.
+ intros j Hj. cbn in Hj. destruct j; [|lia]. cbn [nth_error]. rewrite Z.add_0_r.
exact (find_lit2_sound E m base cs img off z Hcs Himg Hz).
+ cbn [length]. replace (base + off + Z.of_nat 1) with (base + (off + 1)) by lia.
apply IH; assumption.
Qed.
Definition lit_buf (rs : smem) (vb : sv) (n : nat) : option (list Z) :=
match n with
| O => Some []
| _ =>
match match vb with SOff b o => Some (Some b, o) | SLit a => Some (None, zcanon a) | _ => None end with
| Some (b, o) =>
match find_region rs b o (Z.of_nat n) with
| Some r => read_lits2 (r_chunks r) (match b with None => true | Some _ => false end) o n
| None => None
end
| None => None
end
end.
Lemma lit_buf_sound : forall E m rs vb n zs,
mem_ok segs E m rs -> lit_buf rs vb n = Some zs ->
rdn segs m (sv_denot E vb) n = Some (map (Z_to_bv 8) zs).
Proof.
intros E m rs vb n zs HM H. unfold lit_buf in H.
destruct n as [|n'].
{ injection H as <-. reflexivity. }
set (n := S n') in *.
destruct vb as [a|b o| | | | | | | | |]; try discriminate.
- destruct (find_region rs None (zcanon a) (Z.of_nat n)) as [r|] eqn:Hr; [|discriminate].
apply find_region_sound in Hr as (Hin & Hb & Hlo & Hhi).
pose proof (mem_ok_region segs E m rs r HM Hin) as (_ & _ & _ & Hcs). rewrite Hb in Hcs. cbn [base_val] in Hcs.
pose proof (read_lits2_sound E m 0 (r_chunks r) true n (zcanon a) zs Hcs ltac:(reflexivity) H) as Hmb.
pose proof (mbytes_at_rdn segs m _ _ Hmb) as Hrd.
rewrite length_map, (read_lits2_length _ _ _ _ _ H), Z.add_0_l in Hrd.
cbn [sv_denot]. rewrite <- Z_to_bv64_canon. exact Hrd.
- destruct (find_region rs (Some b) o (Z.of_nat n)) as [r|] eqn:Hr; [|discriminate].
apply find_region_sound in Hr as (Hin & Hb & Hlo & Hhi).
pose proof (mem_ok_region segs E m rs r HM Hin) as (_ & _ & _ & Hcs). rewrite Hb in Hcs. cbn [base_val] in Hcs.
pose proof (read_lits2_sound E m (bv_unsigned (ew E b)) (r_chunks r) false n o zs Hcs ltac:(discriminate) H) as Hmb.
pose proof (mbytes_at_rdn segs m _ _ Hmb) as Hrd.
rewrite length_map, (read_lits2_length _ _ _ _ _ H) in Hrd.
cbn [sv_denot]. exact Hrd.
Qed.
Fixpoint zlist_eqb (l1 l2 : list Z) : bool :=
match l1, l2 with
| [], [] => true
| x :: l1', y :: l2' => Z.eqb x y && zlist_eqb l1' l2'
| _, _ => false
end.
Lemma zlist_eqb_eq : forall l1 l2, zlist_eqb l1 l2 = true -> l1 = l2.
Proof.
induction l1 as [|x l1 IH]; intros [|y l2] H; cbn in H; try discriminate; [reflexivity|].
apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. subst. f_equal. apply IH. exact H2.
Qed.
End g.
End e.