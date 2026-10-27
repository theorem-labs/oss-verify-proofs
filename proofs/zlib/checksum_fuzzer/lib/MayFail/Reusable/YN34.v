(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN34.v, with its module paths changed. *)
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
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH00.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN35.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN3f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN3g.
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
Definition lit_sv (v : sv) : option Z := match v with SLit z => Some (zcanon z) | _ => None end.
Lemma lit_sv_sound : forall E v z, lit_sv v = Some z -> sv_denot E v = Z_to_bv 64 z /\ 0 <= z < M64.
Proof.
intros E v z H. destruct v; cbn in H; try discriminate. injection H as <-.
split; [cbn; symmetry; apply Z_to_bv64_canon| apply zcanon_range].
Qed.
Lemma lit_sv_U : forall E v z, lit_sv v = Some z -> U E v = z.
Proof.
intros E v z H. destruct (lit_sv_sound E v z H) as [Hd Hr]. unfold U. rewrite Hd.
apply unsigned_lit_small. unfold M64 in Hr. lia.
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
Lemma lit_buf_length : forall rs vb n zs, lit_buf rs vb n = Some zs -> length zs = n.
Proof.
intros rs vb n zs H. unfold lit_buf in H. destruct n as [|n'].
{ injection H as <-. reflexivity. }
destruct (match vb with SOff b o => Some (Some b, o) | SLit a => Some (None, zcanon a) | _ => None end) as [[b o]|]; [|discriminate].
destruct (find_region rs b o (Z.of_nat (S n'))) as [r|]; [|discriminate].
eapply read_lits2_length. exact H.
Qed.
Definition iovcnt_of (G : facts) (v : sv) : option Z :=
match v with
| SLit z => Some (zcanon z)
| SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_SLTU (SLit 0) (SAlu ALU_XOR (SOff b x) (SOff b' y))) (SLit 1)) (SLit 0) =>
if Nat.eqb b b' then
match atom_lookup (f_atoms G) b with
| Some f => if (0 <=? af_lo f + Z.min x y) && (af_hi f + Z.max x y <? M64)
then Some (if x =? y then 1 else 2) else None
| None => None
end
else None
| SAlu ALU_ADD (SAlu ALU_SLTU (SLit 0) (SAlu ALU_XOR (SOff b x) (SOff b' y))) (SLit 1) =>
if Nat.eqb b b' then
match atom_lookup (f_atoms G) b with
| Some f => if (0 <=? af_lo f + Z.min x y) && (af_hi f + Z.max x y <? M64)
then Some (if x =? y then 1 else 2) else None
| None => None
end
else None
| _ => None
end.
Lemma iovcnt_val' : forall E a b,
sv_denot E (SAlu ALU_ADD (SAlu ALU_SLTU (SLit 0) (SAlu ALU_XOR a b)) (SLit 1))
= Z_to_bv 64 (if U E a =? U E b then 1 else 2).
Proof.
intros E a b. rewrite denot_lit_U. f_equal.
rewrite !U_SAlu, !U_SLit. cbn [zalu_raw].
pose proof (U_range E a). pose proof (U_range E b).
pose proof (Z_lxor_range (U E a) (U E b) ltac:(unfold M64 in *; lia) ltac:(unfold M64 in *; lia)).
rewrite (zcanon_id (Z.lxor _ _)) by (unfold M64; lia). rewrite (zcanon_id 0) by (unfold M64; lia).
destruct (Z.eqb_spec (U E a) (U E b)) as [Heq|Hne].
- rewrite Heq, Z.lxor_nilpotent. vm_compute. reflexivity.
- assert (Hnz : Z.lxor (U E a) (U E b) <> 0) by (intros Hz; apply Hne; apply Z.lxor_eq; exact Hz).
replace (0 <? Z.lxor (U E a) (U E b)) with true by (symmetry; apply Z.ltb_lt; lia).
vm_compute. reflexivity.
Qed.
Lemma iovcnt_core : forall E G b x y f,
facts_ok E G -> atom_lookup (f_atoms G) b = Some f ->
0 <= af_lo f + Z.min x y -> af_hi f + Z.max x y < M64 ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_SLTU (SLit 0) (SAlu ALU_XOR (SOff b x) (SOff b y))) (SLit 1))
= Z_to_bv 64 (if x =? y then 1 else 2).
Proof.
intros E G b x y f HG Hf C1 C2.
pose proof (atom_lookup_ok E _ _ _ (proj1 HG) Hf) as (Hb & _).
rewrite iovcnt_val'. rewrite !U_off by (unfold M64 in *; lia).
destruct (Z.eqb_spec x y) as [->|Hne].
- rewrite Z.eqb_refl. reflexivity.
- rewrite (proj2 (Z.eqb_neq _ _)) by lia. reflexivity.
Qed.
Lemma iovcnt_of_sound : forall E G v c,
facts_ok E G -> iovcnt_of G v = Some c -> sv_denot E v = Z_to_bv 64 c.
Proof.
intros E G v c HG H.
destruct v as [z| |op a b| | | | | | | |]; cbn in H; try discriminate.
{ injection H as <-. cbn. symmetry. apply Z_to_bv64_canon. }
destruct op; try discriminate.
destruct a as [| |op2 a2 b2| | | | | | | |]; try discriminate. destruct op2; try discriminate.
-
destruct a2 as [| |op3 a3 b3| | | | | | | |]; try discriminate. destruct op3; try discriminate.
destruct a3 as [z3| | | | | | | | | |]; try discriminate. destruct z3; try discriminate.
destruct b3 as [| |op4 a4 b4| | | | | | | |]; try discriminate. destruct op4; try discriminate.
destruct a4 as [|bx x| | | | | | | | |]; try discriminate.
destruct b4 as [|by_ y| | | | | | | | |]; try discriminate.
destruct b2 as [z2| | | | | | | | | |]; try discriminate.
destruct z2 as [|p|]; try discriminate. destruct p; try discriminate.
destruct b as [z1| | | | | | | | | |]; try discriminate. destruct z1; try discriminate.
destruct (Nat.eqb_spec bx by_); [|discriminate]. subst by_.
destruct (atom_lookup (f_atoms G) bx) as [f|] eqn:Hf; [|discriminate].
destruct ((0 <=? af_lo f + Z.min x y) && (af_hi f + Z.max x y <? M64)) eqn:Hck; [|discriminate].
injection H as <-.
apply andb_prop in Hck as [C1 C2]. apply Z.leb_le in C1. apply Z.ltb_lt in C2.
pose proof (atom_lookup_ok E _ _ _ (proj1 HG) Hf) as (Hb & _).
rewrite iovcnt_val. rewrite !U_off by (unfold M64 in *; lia).
destruct (Z.eqb_spec x y) as [->|Hne].
+ rewrite Z.eqb_refl. reflexivity.
+ rewrite (proj2 (Z.eqb_neq _ _)) by lia. reflexivity.
-
destruct a2 as [z3| | | | | | | | | |]; try discriminate. destruct z3; try discriminate.
destruct b2 as [| |op4 a4 b4| | | | | | | |]; try discriminate. destruct op4; try discriminate.
destruct a4 as [|bx x| | | | | | | | |]; try discriminate.
destruct b4 as [|by_ y| | | | | | | | |]; try discriminate.
destruct b as [z1| | | | | | | | | |]; try discriminate.
destruct z1 as [|p|]; try discriminate. destruct p; try discriminate.
destruct (Nat.eqb_spec bx by_); [|discriminate]. subst by_.
destruct (atom_lookup (f_atoms G) bx) as [f|] eqn:Hf; [|discriminate].
destruct ((0 <=? af_lo f + Z.min x y) && (af_hi f + Z.max x y <? M64)) eqn:Hck; [|discriminate].
injection H as <-.
apply andb_prop in Hck as [C1 C2]. apply Z.leb_le in C1. apply Z.ltb_lt in C2.
exact (iovcnt_core E G bx x y f HG Hf C1 C2).
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
Lemma map_Z_to_bv8_unsigned : forall msg : list byte, map (Z_to_bv 8) (map bv_unsigned msg) = msg.
Proof. induction msg as [|b msg IH]; cbn; [reflexivity|]. rewrite Z_to_bv_bv_unsigned, IH. reflexivity. Qed.
Fixpoint find_wregion (rs : smem) (b : nat) (lo hi : Z) : option nat :=
match rs with
| [] => None
| r :: rs' =>
if obase_eqb (r_base r) (Some b) && (r_lo r <=? lo) && (hi <=? r_hi r) && (r_wlo r <=? lo) && (hi <=? r_whi r)
then Some O
else option_map S (find_wregion rs' b lo hi)
end.
Lemma find_wregion_sound : forall rs b lo hi i,
find_wregion rs b lo hi = Some i ->
exists r, nth_error rs i = Some r /\ r_base r = Some b /\ r_lo r <= lo /\ hi <= r_hi r /\ r_wlo r <= lo /\ hi <= r_whi r.
Proof.
induction rs as [|r rs IH]; intros b lo hi i H; cbn in H; [discriminate|].
destruct (obase_eqb (r_base r) (Some b) && (r_lo r <=? lo) && (hi <=? r_hi r) && (r_wlo r <=? lo) && (hi <=? r_whi r)) eqn:C.
- injection H as <-. exists r. cbn.
apply andb_prop in C as [C C5]. apply andb_prop in C as [C C4]. apply andb_prop in C as [C C3]. apply andb_prop in C as [C1 C2].
apply Z.leb_le in C2. apply Z.leb_le in C3. apply Z.leb_le in C4. apply Z.leb_le in C5.
apply obase_eqb_eq in C1. repeat split; auto.
- destruct (find_wregion rs b lo hi) as [j|] eqn:Hj; [|discriminate]. cbn in H. injection H as <-.
cbn. apply IH. exact Hj.
Qed.
End g.
Definition wchk (G : facts) (b : nat) (K : Z) (vb : sv) (n : Z) : bool :=
match vb with
| SLit a => match atom_lookup (f_atoms G) b with
| Some f => (0 <=? zcanon a) && (zcanon a + n <=? af_lo f + K + 8) && (0 <=? n) && (zcanon a + n <=? 2^47)
| None => false
end
| SOff b' o => Nat.eqb b' b &&
match atom_lookup (f_atoms G) b with
| Some f => (0 <=? af_lo f + o) && (af_hi f + o + n <=? 2^47) && (0 <=? n)
&& ((o + n <=? K + 8) || (K + 40 <=? o))
| None => false
end
| _ => false
end.
Lemma wchk_sound : forall E G b K vb n,
facts_ok E G -> wchk G b K vb n = true ->
U E vb + n <= 2^47 /\ (U E vb + n <= bv_unsigned (ew E b) + K + 8 \/ bv_unsigned (ew E b) + K + 40 <= U E vb).
Proof.
intros E G b K vb n HG H. unfold wchk in H.
destruct vb as [a|b' o| | | | | | | | |]; try discriminate.
- destruct (atom_lookup (f_atoms G) b) as [f|] eqn:Hf; [|discriminate].
apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. apply Z.leb_le in H4.
pose proof (atom_lookup_ok E _ _ _ (proj1 HG) Hf) as (Hb & _).
pose proof (u64_range (ew E b)). rewrite U_SLit. unfold M64 in *. lia.
- apply andb_prop in H as [Hbb H]. apply Nat.eqb_eq in Hbb. subst b'.
destruct (atom_lookup (f_atoms G) b) as [f|] eqn:Hf; [|discriminate].
apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
pose proof (atom_lookup_ok E _ _ _ (proj1 HG) Hf) as (Hb & _).
rewrite U_off by (unfold M64 in *; lia). unfold M64 in *.
apply orb_prop in H4. destruct H4 as [H4|H4]; apply Z.leb_le in H4; lia.
Qed.
Definition wx_one (s1 : sstate) (b : nat) (K o : Z) : option (sv * sv * list Z * Z) :=
match iov_read1 (ss_mem s1) (Some b) o with
| Some (vb, vl) =>
match lit_sv vl with
| Some n => match lit_buf src0segs (ss_mem s1) vb (Z.to_nat n) with
| Some zs => if wchk (ss_facts s1) b K vb n then Some (vb, vl, zs, n) else None
| None => None
end
| None => None
end
| None => None
end.
Lemma wx_one_sound : forall E s1 m b K o vb vl zs n,
mem_ok src0segs E m (ss_mem s1) -> facts_ok E (ss_facts s1) ->
wx_one s1 b K o = Some (vb, vl, zs, n) ->
iov_read1 (ss_mem s1) (Some b) o = Some (vb, vl)
/\ rdn src0segs m (sv_denot E vb) (word_to_nat (sv_denot E vl)) = Some (map (Z_to_bv 8) zs)
/\ U E vl = n /\ Z.of_nat (length zs) = n /\ 0 <= n
/\ U E vb + n <= 2^47 /\ (U E vb + n <= bv_unsigned (ew E b) + K + 8 \/ bv_unsigned (ew E b) + K + 40 <= U E vb).
Proof.
intros E s1 m b K o vb vl zs n HM HG H. unfold wx_one in H.
destruct (iov_read1 (ss_mem s1) (Some b) o) as [[vb' vl']|] eqn:Hiov; [|discriminate].
destruct (lit_sv vl') as [n'|] eqn:Hvl; [|discriminate].
destruct (lit_buf src0segs (ss_mem s1) vb' (Z.to_nat n')) as [zs'|] eqn:Hbuf; [|discriminate].
destruct (wchk (ss_facts s1) b K vb' n') eqn:Hw; [|discriminate].
injection H as -> -> -> ->.
pose proof (lit_sv_U E vl n Hvl) as HU. pose proof (proj2 (lit_sv_sound E vl n Hvl)) as Hr.
pose proof (lit_buf_length _ _ _ _ _ Hbuf) as Hl.
destruct (wchk_sound E _ b K vb n HG Hw) as [W1 W2].
split; [first [exact Hiov | reflexivity]|]. split.
{ unfold word_to_nat. change (bv_unsigned (sv_denot E vl)) with (U E vl). rewrite HU.
eapply lit_buf_sound; eauto. }
split; [exact HU|]. split; [unfold M64 in Hr; lia|]. split; [lia|]. split; [exact W1| exact W2].
Qed.
Definition wx_step (k : nat) (ss : sstate) : option (sstate * sstate * list Z * Z) :=
match sym_runN src0segs src0tbl FUEL ss with
| (s1, RS_ecall) =>
if negb (ss_pc s1 =? WL_ECALL1) then None else
match sr_get (ss_regs s1) 17, lit_sv (sr_get (ss_regs s1) 10),
iovcnt_of (ss_facts s1) (sr_get (ss_regs s1) 12), iovcnt_of (ss_facts s1) (sr_get (ss_regs s1) 18),
sr_get (ss_regs s1) 2, sr_get (ss_regs s1) 9, ss_resv s1 with
| SLit 66, Some fd, Some cnt, Some cnt', SOff b K, SLit F, None =>
if negb ((fd =? 1) || (fd =? 2)) then None else
if negb (cnt =? cnt') then None else
if negb (zcanon F =? F) then None else
if negb (ss_atoms_lt k s1) then None else
match find_wregion (ss_mem s1) b (K + 8) (K + 40), atom_lookup (f_atoms (ss_facts s1)) b,
lit_buf src0segs (ss_mem s1) (SLit (F + 120)) 4 with
| Some i, Some f, Some fdz =>
if negb ((0 <=? af_lo f + K) && (af_hi f + K + 40 <=? 2^47) && (0 <=? F) && (F + 124 <=? af_lo f + K + 8)
&& zlist_eqb fdz [fd; 0; 0; 0]) then None else
let iovp := sr_get (ss_regs s1) 19 in
if negb (sv_eqb iovp (sr_get (ss_regs s1) 11)) then None else
if cnt =? 2 then
if negb (sv_eqb iovp (SOff b (K + 8))) then None else
match wx_one s1 b K (K + 8), wx_one s1 b K (K + 24), lit_sv (sr_get (ss_regs s1) 22) with
| Some (vb0, vl0, zs0, n0), Some (vb1, vl1, zs1, n1), Some rem =>
if (rem =? n0 + n1) && (1 <=? rem) && (rem <=? 2^25)
then Some (s1, wl_after s1 i K k, zs0 ++ zs1, fd) else None
| _, _, _ => None
end
else if cnt =? 1 then
if negb (sv_eqb iovp (SOff b (K + 24))) then None else
match wx_one s1 b K (K + 24), lit_sv (sr_get (ss_regs s1) 22) with
| Some (vb1, vl1, zs1, n1), Some rem =>
if (rem =? n1) && (1 <=? rem) && (rem <=? 2^25)
then Some (s1, wl_after s1 i K k, zs1, fd) else None
| _, _ => None
end
else None
| _, _, _ => None
end
| _, _, _, _, _, _, _ => None
end
| _ => None
end.
Theorem realizes_stdio_writev_by_run : forall E ss ms model ch k s1 s2 zs fd T,
st_ok src0segs E ss ms -> m_halted model = None -> m_vm_lazy model = [] ->
wx_step k ss = Some (s1, s2, zs, fd) ->
fdchan (Z_to_bv 64 fd) ch model ->
(forall ms' ws, st_ok src0segs (havoc E k ws) s2 ms' ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
skeleton (ss_mem s2) = skeleton (ss_mem ss) -> mem_atoms_lt k (ss_mem s2) = true ->
realizes src0segs (mkCfg ms' model) T) ->
realizes src0segs (mkCfg ms model) (t_emit (map (WriteEv ch) (map (Z_to_bv 8) zs)) T).
Proof.
intros E ss ms model ch k s1 s2 zs fd T HS Hh Hlz Hck Hch Hk. unfold wx_step in Hck.
destruct (sym_runN src0segs src0tbl FUEL ss) as [s1' st] eqn:Hrun. destruct st; try discriminate.
destruct (ss_pc s1' =? WL_ECALL1) eqn:Hpc; [|discriminate]. apply Z.eqb_eq in Hpc. cbn [negb] in Hck.
destruct (sr_get (ss_regs s1') 17) as [no| | | | | | | | | |] eqn:H17; try discriminate.
destruct no as [|p17|]; try discriminate. do 7 (destruct p17 as [p17|p17|]; try discriminate).
destruct (lit_sv (sr_get (ss_regs s1') 10)) as [fd'|] eqn:H10; [|discriminate].
destruct (iovcnt_of (ss_facts s1') (sr_get (ss_regs s1') 12)) as [cnt|] eqn:H12; [|discriminate].
destruct (iovcnt_of (ss_facts s1') (sr_get (ss_regs s1') 18)) as [cnt'|] eqn:H18; [|discriminate].
destruct (sr_get (ss_regs s1') 2) as [|b K| | | | | | | | |] eqn:H2; try discriminate.
destruct (sr_get (ss_regs s1') 9) as [F| | | | | | | | | |] eqn:H9; try discriminate.
destruct (ss_resv s1') eqn:Hrv; try discriminate.
destruct (negb ((fd' =? 1) || (fd' =? 2))) eqn:Hfd; [discriminate|].
assert (Hfd12 : fd' = 1 \/ fd' = 2).
{ apply negb_false_iff in Hfd. apply orb_prop in Hfd as [Hf|Hf]; apply Z.eqb_eq in Hf; lia. }
destruct (negb (cnt =? cnt')) eqn:Hcc; [discriminate|]. apply negb_false_iff in Hcc. apply Z.eqb_eq in Hcc. subst cnt'.
destruct (negb (zcanon F =? F)) eqn:HFc; [discriminate|]. apply negb_false_iff in HFc. apply Z.eqb_eq in HFc.
destruct (ss_atoms_lt k s1') eqn:Hat; [|discriminate]. cbn [negb] in Hck.
destruct (find_wregion (ss_mem s1') b (K + 8) (K + 40)) as [i|] eqn:Hwr; [|discriminate].
destruct (atom_lookup (f_atoms (ss_facts s1')) b) as [f|] eqn:Hf; [|discriminate].
destruct (lit_buf src0segs (ss_mem s1') (SLit (F + 120)) 4) as [fdz|] eqn:Hfdz; [|discriminate].
destruct ((0 <=? af_lo f + K) && (af_hi f + K + 40 <=? 2^47) && (0 <=? F) && (F + 124 <=? af_lo f + K + 8)
&& zlist_eqb fdz [fd'; 0; 0; 0]) eqn:Hbnd; [|discriminate]. cbn [negb] in Hck.
apply andb_prop in Hbnd as [Hbnd Hfdz4]. apply andb_prop in Hbnd as [Hbnd B4]. apply andb_prop in Hbnd as [Hbnd B3].
apply andb_prop in Hbnd as [B1 B2].
apply Z.leb_le in B1. apply Z.leb_le in B2. apply Z.leb_le in B3. apply Z.leb_le in B4. apply zlist_eqb_eq in Hfdz4. subst fdz.
destruct (sv_eqb (sr_get (ss_regs s1') 19) (sr_get (ss_regs s1') 11)) eqn:H1911; [|discriminate]. cbn [negb] in Hck.
apply sv_eqb_eq in H1911.
destruct (find_wregion_sound _ _ _ _ _ Hwr) as (r & Hi & Hrb & Hrlo & Hrhi & Hwlo & Hwhi).
destruct (sym_run_sound src0segs src0tbl src0tbl_ok _ E ss s1' RS_ecall ms HS Hrun) as (_ & _ & _ & Hsk' & _).
pose proof (eq_sym Hsk') as Hsk. clear Hsk'.
assert (Hma : forall i K, mem_atoms_lt k (ss_mem (wl_after s1' i K k)) = true).
{ intros i0 K0. unfold wl_after; cbn [ss_mem].
apply (mem_atoms_lt_submem k _ (ss_mem s1')); [apply submem_forget_win|].
unfold ss_atoms_lt in Hat. apply andb_prop in Hat as [Hat' _]. apply andb_prop in Hat' as [Hat' _].
apply andb_prop in Hat' as [_ Hm]. exact Hm. }
assert (Hskafter : forall i K, skeleton (ss_mem (wl_after s1' i K k)) = skeleton (ss_mem ss)).
{ intros i0 K0. unfold wl_after; cbn [ss_mem]. rewrite skeleton_forget_win. symmetry. exact Hsk. }
eapply (rz_run_ecall src0segs src0tbl src0tbl_ok FUEL E ss s1' ms model _ Hh Hlz HS Hrun).
intros ms1 HS1 HF1.
pose proof HS1 as HS1copy.
destruct HS1copy as (_ & _ & _ & _ & _ & _ & Hregs1 & Hmem1 & HG1).
pose proof (lit_sv_sound E _ _ H10) as [D10 R10].
pose proof (iovcnt_of_sound E _ _ _ HG1 H12) as D12.
pose proof (iovcnt_of_sound E _ _ _ HG1 H18) as D18.
assert (H32 : fd32 (Z_to_bv 64 fd') = Z_to_bv 64 fd') by (destruct Hfd12 as [-> | ->]; reflexivity).
assert (Hfd31 : bv_unsigned (Z_to_bv 64 fd') < 2^31) by (rewrite u_Z2bv by lia; lia).
pose proof (atom_lookup_ok E _ _ _ (proj1 HG1) Hf) as (Hbf & _).
pose proof (lit_buf_sound src0segs E (ms_mem ms1) _ _ _ _ Hmem1 Hfdz) as Hfdrd. cbn [sv_denot] in Hfdrd.
assert (HfdB : bytes_le_to_Z (map (Z_to_bv 8) [fd'; 0; 0; 0]) = bv_unsigned (Z_to_bv 64 fd')).
{ clear -Hfd12. destruct Hfd12 as [-> | ->]; vm_compute; reflexivity. }
destruct (cnt =? 2) eqn:Hc2.
- apply Z.eqb_eq in Hc2. subst cnt.
destruct (sv_eqb (sr_get (ss_regs s1') 19) (SOff b (K + 8))) eqn:H19; [|discriminate]. cbn [negb] in Hck.
apply sv_eqb_eq in H19.
destruct (wx_one s1' b K (K + 8)) as [[[[vb0 vl0] zs0] n0]|] eqn:Ho0; [|discriminate].
destruct (wx_one s1' b K (K + 24)) as [[[[vb1 vl1] zs1] n1]|] eqn:Ho1; [|discriminate].
destruct (lit_sv (sr_get (ss_regs s1') 22)) as [rem|] eqn:H22; [|discriminate].
destruct ((rem =? n0 + n1) && (1 <=? rem) && (rem <=? 2 ^ 25)) eqn:Hrem; [|discriminate].
injection Hck as <- <- <- <-.
apply andb_prop in Hrem as [Hrem Q3]. apply andb_prop in Hrem as [Q1 Q2].
apply Z.eqb_eq in Q1. apply Z.leb_le in Q2. apply Z.leb_le in Q3. subst rem.
destruct (wx_one_sound E s1' (ms_mem ms1) b K _ _ _ _ _ Hmem1 HG1 Ho0) as (Hiov0 & Hrd0 & HU0 & Hlz0 & Hn0 & Hnw0 & Hd0).
destruct (wx_one_sound E s1' (ms_mem ms1) b K _ _ _ _ _ Hmem1 HG1 Ho1) as (Hiov1 & Hrd1 & HU1 & Hlz1 & Hn1 & Hnw1 & Hd1).
rewrite map_app.
eapply (rz_sym_stdio_writev2 E s1' ms1 model (Z_to_bv 64 fd') ch i b K F r vb0 vl0 vb1 vl1 _ _ _ k T Hh Hlz HS1 Hrv Hpc);
[ exact H17 | exact D10 | exact Hch | exact H32 | exact Hfd31 | exact D12 | exact D18 | exact H2
| exact H19 | rewrite <- H1911; exact H19 | rewrite (lit_sv_U E _ _ H22), HU0, HU1; reflexivity
| rewrite H9, U_SLit; exact HFc
| exact Hi | exact Hrb | exact Hrlo | exact Hrhi | exact Hwlo | exact Hwhi
| unfold iov_read2; rewrite Hiov0; replace (K + 8 + 16) with (K + 24) by lia; rewrite Hiov1; reflexivity
| exact Hrd0 | exact Hrd1 | rewrite HU0, HU1; lia
| rewrite HU0; exact Hnw0 | rewrite HU0; exact Hd0 | rewrite HU1; exact Hnw1 | rewrite HU1; exact Hd1
| exact Hfdrd | exact HfdB | lia | unfold M64 in *; lia | lia | lia | unfold M64 in *; lia | exact Hat | ].
intros ms' ws HS' HF'. apply (Hk ms' ws HS'); [eapply frame_of_trans; [exact Hsk | exact HF1 | exact HF'] | apply Hskafter | apply Hma].
- destruct (cnt =? 1) eqn:Hc1; [|discriminate]. apply Z.eqb_eq in Hc1. subst cnt.
destruct (sv_eqb (sr_get (ss_regs s1') 19) (SOff b (K + 24))) eqn:H19; [|discriminate]. cbn [negb] in Hck.
apply sv_eqb_eq in H19.
destruct (wx_one s1' b K (K + 24)) as [[[[vb1 vl1] zs1] n1]|] eqn:Ho1; [|discriminate].
destruct (lit_sv (sr_get (ss_regs s1') 22)) as [rem|] eqn:H22; [|discriminate].
destruct ((rem =? n1) && (1 <=? rem) && (rem <=? 2 ^ 25)) eqn:Hrem; [|discriminate].
injection Hck as <- <- <- <-.
apply andb_prop in Hrem as [Hrem Q3]. apply andb_prop in Hrem as [Q1 Q2].
apply Z.eqb_eq in Q1. apply Z.leb_le in Q2. apply Z.leb_le in Q3. subst rem.
destruct (wx_one_sound E s1' (ms_mem ms1) b K _ _ _ _ _ Hmem1 HG1 Ho1) as (Hiov1 & Hrd1 & HU1 & Hlz1 & Hn1 & Hnw1 & Hd1).
eapply (rz_sym_stdio_writev1 E s1' ms1 model (Z_to_bv 64 fd') ch i b K F r vb1 vl1 _ _ k T Hh Hlz HS1 Hrv Hpc);
[ exact H17 | exact D10 | exact Hch | exact H32 | exact Hfd31 | exact D12 | exact D18 | exact H2
| exact H19 | rewrite <- H1911; exact H19 | rewrite (lit_sv_U E _ _ H22), HU1; reflexivity
| rewrite H9, U_SLit; exact HFc
| exact Hi | exact Hrb | exact Hrlo | exact Hrhi | exact Hwlo | exact Hwhi
| exact Hiov1
| exact Hrd1 | rewrite HU1; lia
| rewrite HU1; exact Hnw1 | rewrite HU1; exact Hd1
| exact Hfdrd | exact HfdB | lia | unfold M64 in *; lia | lia | lia | unfold M64 in *; lia | exact Hat | ].
intros ms' ws HS' HF'. apply (Hk ms' ws HS'); [eapply frame_of_trans; [exact Hsk | exact HF1 | exact HF'] | apply Hskafter | apply Hma].
Qed.
Definition skel_eqb (a b : option nat * Z * Z * Z * Z) : bool :=
match a, b with
| (b1, l1, h1, w1, x1), (b2, l2, h2, w2, x2) =>
obase_eqb b1 b2 && (l1 =? l2) && (h1 =? h2) && (w1 =? w2) && (x1 =? x2)
end.
Fixpoint skeleton_eqb (l1 l2 : list (option nat * Z * Z * Z * Z)) : bool :=
match l1, l2 with
| [], [] => true
| x :: l1', y :: l2' => skel_eqb x y && skeleton_eqb l1' l2'
| _, _ => false
end.
Lemma skeleton_eqb_eq : forall l1 l2, skeleton_eqb l1 l2 = true -> l1 = l2.
Proof.
induction l1 as [|x l1 IH]; intros [|y l2] H; cbn in H; try discriminate; [reflexivity|].
apply andb_prop in H as [H1 H2]. f_equal; [|apply IH; exact H2].
destruct x as [[[[b1 lo1] hi1] w1] x1]. destruct y as [[[[b2 lo2] hi2] w2] x2]. cbn in H1.
apply andb_prop in H1 as [H1 E4]. apply andb_prop in H1 as [H1 E3]. apply andb_prop in H1 as [H1 E2].
apply andb_prop in H1 as [E0 E1].
apply obase_eqb_eq in E0. apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. apply Z.eqb_eq in E3. apply Z.eqb_eq in E4.
subst. reflexivity.
Qed.
Definition wx_msg_check (k : nat) (ss : sstate) (msg : list byte) : option (sstate * Z) :=
match wx_step k ss with
| Some (s1, s2, zs, fd) =>
if zlist_eqb zs (map bv_unsigned msg) then Some (s2, fd) else None
| None => None
end.
Theorem realizes_writev_msg_by_run : forall E ss ms model ch k msg s2 fd T,
st_ok src0segs E ss ms -> m_halted model = None -> m_vm_lazy model = [] ->
wx_msg_check k ss msg = Some (s2, fd) ->
fdchan (Z_to_bv 64 fd) ch model ->
(forall ms' ws, st_ok src0segs (havoc E k ws) s2 ms' -> frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
skeleton (ss_mem s2) = skeleton (ss_mem ss) -> mem_atoms_lt k (ss_mem s2) = true ->
realizes src0segs (mkCfg ms' model) T) ->
realizes src0segs (mkCfg ms model) (t_emit (map (WriteEv ch) msg) T).
Proof.
intros E ss ms model ch k msg s2 fd T HS Hh Hlz Hck Hch Hk. unfold wx_msg_check in Hck.
destruct (wx_step k ss) as [[[[s1 s2'] zs] fd']|] eqn:Hwx; [|discriminate].
destruct (zlist_eqb zs (map bv_unsigned msg)) eqn:Heq; [|discriminate].
injection Hck as <- <-. apply zlist_eqb_eq in Heq. subst zs.
rewrite <- (map_Z_to_bv8_unsigned msg).
eapply realizes_stdio_writev_by_run; eauto.
Qed.
Definition diag_exit_check (k : nat) (ss : sstate) (msg : list byte) (code : Z) : option Z :=
match wx_msg_check k ss msg with
| Some (s2, fd) => if exit_run_check src0segs src0tbl s2 code then Some fd else None
| None => None
end.
Theorem realizes_diag_exit_by_run : forall E ss ms model ch k msg code fd,
st_ok src0segs E ss ms -> m_halted model = None -> m_vm_lazy model = [] -> 0 <= code < 256 ->
diag_exit_check k ss msg code = Some fd ->
fdchan (Z_to_bv 64 fd) ch model ->
realizes src0segs (mkCfg ms model) (t_emit (map (WriteEv ch) msg) (t_exit (Z_to_bv 64 code) (m_fs model))).
Proof.
intros E ss ms model ch k msg code fd HS Hh Hlz Hcode Hck Hch. unfold diag_exit_check in Hck.
destruct (wx_msg_check k ss msg) as [[s2 fd']|] eqn:Hwx; [|discriminate].
destruct (exit_run_check src0segs src0tbl s2 code) eqn:Hex; [|discriminate]. injection Hck as <-.
eapply realizes_writev_msg_by_run; eauto.
intros ms' ws HS' _ _ _. eapply (src0_exit (havoc E k ws)); eauto.
Qed.
End e.
Ltac src0_diag_exit_tac HS Hch k :=
lazymatch type of HS with st_ok _ ?E ?ss ?ms =>
lazymatch type of Hch with fdchan (Z_to_bv 64 ?fd) ?ch ?model =>
lazymatch goal with |- realizes _ _ (t_emit (map _ ?msg) (t_exit (Z_to_bv 64 ?code) _)) =>
let r := eval vm_compute in (diag_exit_check k ss msg code) in
lazymatch r with
| Some _ =>
apply (realizes_diag_exit_by_run E ss ms model ch k msg code fd HS);
[ assumption | assumption | lia | vm_compute; reflexivity | exact Hch ]
| None => fail "src0_diag_exit_tac: diag_exit_check failed (inspect wx_step / exit_run_check on this state)"
end
end end end.
Ltac src0_fwrite_tac HS Hch k :=
lazymatch type of HS with st_ok _ ?E ?ss ?ms =>
lazymatch type of Hch with fdchan (Z_to_bv 64 ?fd) ?ch ?model =>
lazymatch goal with |- realizes _ _ (t_emit (map _ ?msg) _) =>
let r := eval vm_compute in (wx_msg_check k ss msg) in
lazymatch r with
| Some (?s2, _) =>
let Hck := fresh "Hck" in
assert (Hck : wx_msg_check k ss msg = Some (s2, fd)) by (vm_compute; reflexivity);
apply (realizes_writev_msg_by_run E ss ms model ch k msg s2 fd _ HS ltac:(assumption) ltac:(assumption) Hck Hch);
clear Hck HS;
let ms' := fresh "ms" in let ws := fresh "ws" in let HF := fresh "HF" in
let Hsk := fresh "Hsk" in let Hma := fresh "Hma" in
intros ms' ws HS HF Hsk Hma;
sym_transport src0segs E ss s2 ms' HS HF; try clear Hsk Hma
| None => fail "src0_fwrite_tac: wx_msg_check failed on this state"
end
end end end.
