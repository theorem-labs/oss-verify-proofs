(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK0o YQ0k.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ0a YQ04 YQ0d YQ05.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP00 YO3v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8v YE1o YE1p YF8r.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK18 YK05 YA0i YA0l YA0m YA0n.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section e. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section g. Context {imgk : img}.
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
intros E m base cs img a z Hcs Himg. induction Hcs as [|c cs Hc Hcs IH]; cbn; intros H; [img_try (discriminate)|].
destruct ((c_off c <=? a) && (a <? c_off c + c_len c)) eqn:Hin; [|img_try (img_apply IH; img_exact H)].
apply andb_prop in Hin as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
destruct (Hc (a - c_off c) ltac:(img_lia)) as (b & Hb1 & Hb2).
replace (base + c_off c + (a - c_off c)) with (base + a) in Hb2 by img_lia.
destruct (c_val c) as [w v|len|len|d s len] eqn:Hcv.
- destruct v; try (img_apply IH; img_exact H). injection H as <-.
cbn [cbyte sv_denot] in Hb1. injection Hb1 as <-. rewrite Hb2. f_equal.
unfold byte_of_word. rewrite unsigned_lit, Z_to_bv8_mod. img_refl.
- injection H as <-. cbn [cbyte] in Hb1. injection Hb1 as <-. img_exact Hb2.
- destruct img.
+ specialize (Himg eq_refl). (subst base; cbv beta). cbn [cbyte] in Hb1.
replace (0 + c_off c + (a - c_off c)) with a in Hb1 by img_lia.
rewrite Hb1 in H. injection H as <-. rewrite Z_to_bv_bv_unsigned. img_exact Hb2.
+ img_apply IH. img_exact H.
- img_apply IH. img_exact H.
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
- injection H as <-. img_refl.
- destruct (find_lit2 cs img off) as [z|]; [|img_try (discriminate)].
destruct (read_lits2 cs img (off + 1) n) as [zs'|] eqn:Hr; [|img_try (discriminate)].
injection H as <-. cbn. f_equal. eapply IH. img_exact Hr.
Qed.
Lemma read_lits2_sound : forall E m base cs img n off zs,
Forall (chunk_ok segs E m base) cs -> (img = true -> base = 0) ->
read_lits2 cs img off n = Some zs ->
mbytes_at segs m (base + off) (map (Z_to_bv 8) zs).
Proof.
intros E m base cs img n. induction n as [|n IH]; intros off zs Hcs Himg H; cbn in H.
- injection H as <-. img_apply mbytes_at_nil.
- destruct (find_lit2 cs img off) as [z|] eqn:Hz; [|img_try (discriminate)].
destruct (read_lits2 cs img (off + 1) n) as [zs'|] eqn:Hr; [|img_try (discriminate)].
injection H as <-. cbn [map].
change (Z_to_bv 8 z :: ?l) with ([Z_to_bv 8 z] ++ l). img_apply mbytes_at_app.
+ intros j Hj. cbn in Hj. destruct j; [|img_lia]. cbn [nth_error]. rewrite Z.add_0_r.
img_exact (find_lit2_sound E m base cs img off z Hcs Himg Hz).
+ cbn [length]. replace (base + off + Z.of_nat 1) with (base + (off + 1)) by img_lia.
img_apply IH; assumption.
Qed.
Definition lit_sv (v : sv) : option Z := match v with SLit z => Some (zcanon z) | _ => None end.
Lemma lit_sv_sound : forall E v z, lit_sv v = Some z -> sv_denot E v = Z_to_bv 64 z /\ 0 <= z < M64.
Proof.
intros E v z H. destruct v; cbn in H; try discriminate. injection H as <-.
split; [img_try (cbn; symmetry; img_apply Z_to_bv64_canon)| img_try (img_apply zcanon_range)].
Qed.
Lemma lit_sv_U : forall E v z, lit_sv v = Some z -> U E v = z.
Proof.
intros E v z H. destruct (lit_sv_sound E v z H) as [Hd Hr]. unfold U. rewrite Hd.
img_apply unsigned_lit_small. unfold M64 in Hr. img_lia.
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
{ injection H as <-. img_refl. }
set (n := S n') in *.
destruct vb as [a|b o| | | | | | | | |]; try discriminate.
- destruct (find_region rs None (zcanon a) (Z.of_nat n)) as [r|] eqn:Hr; [|img_try (discriminate)].
apply find_region_sound in Hr as (Hin & Hb & Hlo & Hhi).
pose proof (mem_ok_region segs E m rs r HM Hin) as (_ & _ & _ & Hcs). rewrite Hb in Hcs. cbn [base_val] in Hcs.
pose proof (read_lits2_sound E m 0 (r_chunks r) true n (zcanon a) zs Hcs ltac:(img_refl) H) as Hmb.
pose proof (mbytes_at_rdn segs m _ _ Hmb) as Hrd.
rewrite length_map, (read_lits2_length _ _ _ _ _ H), Z.add_0_l in Hrd.
cbn [sv_denot]. rewrite <- Z_to_bv64_canon. img_exact Hrd.
- destruct (find_region rs (Some b) o (Z.of_nat n)) as [r|] eqn:Hr; [|img_try (discriminate)].
apply find_region_sound in Hr as (Hin & Hb & Hlo & Hhi).
pose proof (mem_ok_region segs E m rs r HM Hin) as (_ & _ & _ & Hcs). rewrite Hb in Hcs. cbn [base_val] in Hcs.
pose proof (read_lits2_sound E m (bv_unsigned (ew E b)) (r_chunks r) false n o zs Hcs ltac:(img_try (discriminate)) H) as Hmb.
pose proof (mbytes_at_rdn segs m _ _ Hmb) as Hrd.
rewrite length_map, (read_lits2_length _ _ _ _ _ H) in Hrd.
cbn [sv_denot]. img_exact Hrd.
Qed.
Lemma lit_buf_length : forall rs vb n zs, lit_buf rs vb n = Some zs -> length zs = n.
Proof.
intros rs vb n zs H. unfold lit_buf in H. destruct n as [|n'].
{ injection H as <-. img_refl. }
destruct (match vb with SOff b o => Some (Some b, o) | SLit a => Some (None, zcanon a) | _ => None end) as [[b o]|]; [|img_try (discriminate)].
destruct (find_region rs b o (Z.of_nat (S n'))) as [r|]; [|img_try (discriminate)].
eapply read_lits2_length. img_exact H.
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
pose proof (Z_lxor_range (U E a) (U E b) ltac:(img_try (unfold M64 in *; img_lia)) ltac:(img_try (unfold M64 in *; img_lia))).
rewrite (zcanon_id (Z.lxor _ _)) by (img_try (unfold M64; img_lia)). rewrite (zcanon_id 0) by (img_try (unfold M64; img_lia)).
destruct (Z.eqb_spec (U E a) (U E b)) as [Heq|Hne].
- rewrite Heq, Z.lxor_nilpotent. img_case; vm_compute. all: img_refl.
- assert (Hnz : Z.lxor (U E a) (U E b) <> 0) by (img_try (intros Hz; img_apply Hne; img_apply Z.lxor_eq; img_exact Hz)).
replace (0 <? Z.lxor (U E a) (U E b)) with true by (img_try (symmetry; img_apply Z.ltb_lt; img_lia)).
img_case; vm_compute. all: img_refl.
Qed.
Lemma iovcnt_core : forall E G b x y f,
facts_ok E G -> atom_lookup (f_atoms G) b = Some f ->
0 <= af_lo f + Z.min x y -> af_hi f + Z.max x y < M64 ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_SLTU (SLit 0) (SAlu ALU_XOR (SOff b x) (SOff b y))) (SLit 1))
= Z_to_bv 64 (if x =? y then 1 else 2).
Proof.
intros E G b x y f HG Hf C1 C2.
pose proof (atom_lookup_ok E _ _ _ (proj1 HG) Hf) as (Hb & _).
rewrite iovcnt_val'. rewrite !U_off by (img_try (unfold M64 in *; img_lia)).
destruct (Z.eqb_spec x y) as [->|Hne].
- rewrite Z.eqb_refl. img_refl.
- rewrite (proj2 (Z.eqb_neq _ _)) by img_lia. img_refl.
Qed.
Lemma iovcnt_of_sound : forall E G v c,
facts_ok E G -> iovcnt_of G v = Some c -> sv_denot E v = Z_to_bv 64 c.
Proof.
intros E G v c HG H.
destruct v as [z| |op a b| | | | | | | |]; cbn in H; try discriminate.
{ injection H as <-. cbn. symmetry. img_apply Z_to_bv64_canon. }
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
destruct (Nat.eqb_spec bx by_); [|img_try (discriminate)]. (subst by_; cbv beta).
destruct (atom_lookup (f_atoms G) bx) as [f|] eqn:Hf; [|img_try (discriminate)].
destruct ((0 <=? af_lo f + Z.min x y) && (af_hi f + Z.max x y <? M64)) eqn:Hck; [|img_try (discriminate)].
injection H as <-.
apply andb_prop in Hck as [C1 C2]. apply Z.leb_le in C1. apply Z.ltb_lt in C2.
pose proof (atom_lookup_ok E _ _ _ (proj1 HG) Hf) as (Hb & _).
rewrite iovcnt_val. rewrite !U_off by (img_try (unfold M64 in *; img_lia)).
destruct (Z.eqb_spec x y) as [->|Hne].
+ rewrite Z.eqb_refl. img_refl.
+ rewrite (proj2 (Z.eqb_neq _ _)) by img_lia. img_refl.
-
destruct a2 as [z3| | | | | | | | | |]; try discriminate. destruct z3; try discriminate.
destruct b2 as [| |op4 a4 b4| | | | | | | |]; try discriminate. destruct op4; try discriminate.
destruct a4 as [|bx x| | | | | | | | |]; try discriminate.
destruct b4 as [|by_ y| | | | | | | | |]; try discriminate.
destruct b as [z1| | | | | | | | | |]; try discriminate.
destruct z1 as [|p|]; try discriminate. destruct p; try discriminate.
destruct (Nat.eqb_spec bx by_); [|img_try (discriminate)]. (subst by_; cbv beta).
destruct (atom_lookup (f_atoms G) bx) as [f|] eqn:Hf; [|img_try (discriminate)].
destruct ((0 <=? af_lo f + Z.min x y) && (af_hi f + Z.max x y <? M64)) eqn:Hck; [|img_try (discriminate)].
injection H as <-.
apply andb_prop in Hck as [C1 C2]. apply Z.leb_le in C1. apply Z.ltb_lt in C2.
img_exact (iovcnt_core E G bx x y f HG Hf C1 C2).
Qed.
Fixpoint zlist_eqb (l1 l2 : list Z) : bool :=
match l1, l2 with
| [], [] => true
| x :: l1', y :: l2' => Z.eqb x y && zlist_eqb l1' l2'
| _, _ => false
end.
Lemma zlist_eqb_eq : forall l1 l2, zlist_eqb l1 l2 = true -> l1 = l2.
Proof.
induction l1 as [|x l1 IH]; intros [|y l2] H; cbn in H; try discriminate; [img_refl|].
apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. (subst; cbv beta). f_equal. img_apply IH. img_exact H2.
Qed.
Lemma map_Z_to_bv8_unsigned : forall msg : list byte, map (Z_to_bv 8) (map bv_unsigned msg) = msg.
Proof. induction msg as [|b msg IH]; cbn; [img_refl|]. rewrite Z_to_bv_bv_unsigned, IH. img_refl. Qed.
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
induction rs as [|r rs IH]; intros b lo hi i H; cbn in H; [img_try (discriminate)|].
destruct (obase_eqb (r_base r) (Some b) && (r_lo r <=? lo) && (hi <=? r_hi r) && (r_wlo r <=? lo) && (hi <=? r_whi r)) eqn:C.
- injection H as <-. exists r. cbn.
apply andb_prop in C as [C C5]. apply andb_prop in C as [C C4]. apply andb_prop in C as [C C3]. apply andb_prop in C as [C1 C2].
apply Z.leb_le in C2. apply Z.leb_le in C3. apply Z.leb_le in C4. apply Z.leb_le in C5.
apply obase_eqb_eq in C1. repeat split; auto.
- destruct (find_wregion rs b lo hi) as [j|] eqn:Hj; [|img_try (discriminate)]. cbn in H. injection H as <-.
cbn. img_apply IH. img_exact Hj.
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
- destruct (atom_lookup (f_atoms G) b) as [f|] eqn:Hf; [|img_try (discriminate)].
apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. apply Z.leb_le in H4.
pose proof (atom_lookup_ok E _ _ _ (proj1 HG) Hf) as (Hb & _).
pose proof (u64_range (ew E b)). rewrite U_SLit. unfold M64 in *. img_lia.
- apply andb_prop in H as [Hbb H]. apply Nat.eqb_eq in Hbb. (subst b'; cbv beta).
destruct (atom_lookup (f_atoms G) b) as [f|] eqn:Hf; [|img_try (discriminate)].
apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
pose proof (atom_lookup_ok E _ _ _ (proj1 HG) Hf) as (Hb & _).
rewrite U_off by (img_try (unfold M64 in *; img_lia)). unfold M64 in *.
apply orb_prop in H4. destruct H4 as [H4|H4]; apply Z.leb_le in H4; img_lia.
Qed.
Definition wx_one {imgk : img} (s1 : sstate) (b : nat) (K o : Z) : option (sv * sv * list Z * Z) :=
match iov_read1 (ss_mem s1) (Some b) o with
| Some (vb, vl) =>
match lit_sv vl with
| Some n => match lit_buf tfxsegs (ss_mem s1) vb (Z.to_nat n) with
| Some zs => if wchk (ss_facts s1) b K vb n then Some (vb, vl, zs, n) else None
| None => None
end
| None => None
end
| None => None
end.
Lemma wx_one_sound {imgk : img} : forall E s1 m b K o vb vl zs n,
mem_ok tfxsegs E m (ss_mem s1) -> facts_ok E (ss_facts s1) ->
wx_one s1 b K o = Some (vb, vl, zs, n) ->
iov_read1 (ss_mem s1) (Some b) o = Some (vb, vl)
/\ rdn tfxsegs m (sv_denot E vb) (word_to_nat (sv_denot E vl)) = Some (map (Z_to_bv 8) zs)
/\ U E vl = n /\ Z.of_nat (length zs) = n /\ 0 <= n
/\ U E vb + n <= 2^47 /\ (U E vb + n <= bv_unsigned (ew E b) + K + 8 \/ bv_unsigned (ew E b) + K + 40 <= U E vb).
Proof.
intros E s1 m b K o vb vl zs n HM HG H. unfold wx_one in H.
destruct (iov_read1 (ss_mem s1) (Some b) o) as [[vb' vl']|] eqn:Hiov; [|img_try (discriminate)].
destruct (lit_sv vl') as [n'|] eqn:Hvl; [|img_try (discriminate)].
destruct (lit_buf tfxsegs (ss_mem s1) vb' (Z.to_nat n')) as [zs'|] eqn:Hbuf; [|img_try (discriminate)].
destruct (wchk (ss_facts s1) b K vb' n') eqn:Hw; [|img_try (discriminate)].
injection H as -> -> -> ->.
pose proof (lit_sv_U E vl n Hvl) as HU. pose proof (proj2 (lit_sv_sound E vl n Hvl)) as Hr.
pose proof (lit_buf_length _ _ _ _ _ Hbuf) as Hl.
destruct (wchk_sound E _ b K vb n HG Hw) as [W1 W2].
split; [img_try (first [img_exact Hiov | img_refl])|]. split.
{ unfold word_to_nat. img_change (bv_unsigned (sv_denot E vl)) with (U E vl). rewrite HU.
eapply lit_buf_sound; eauto. }
split; [img_try (img_exact HU)|]. split; [img_try (unfold M64 in Hr; img_lia)|]. split; [img_lia|]. split; [img_try (img_exact W1)| img_try (img_exact W2)].
Qed.
Definition wx_step {imgk : img} (tbl : ctable) (k : nat) (ss : sstate) : option (sstate * sstate * list Z * Z) :=
match sym_runN tfxsegs tbl FUEL ss with
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
lit_buf tfxsegs (ss_mem s1) (SLit (F + 120)) 4 with
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
Lemma srz_run_ecall_r {imgk : img} : forall (tbl : ctable) (W : world tfxsegs) n E ss s1 ms model T,
table_ok tfxsegs tbl ->
st_ok tfxsegs E ss (restrict (w_H W) ms) -> AI tfxsegs (w_H W) (w_A W) model ->
sym_runN tfxsegs tbl n ss = (s1, RS_ecall) ->
(forall ms1 mat1, st_ok_ecall tfxsegs E s1 (restrict (w_H W) ms1) ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) ->
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1)) ->
AI tfxsegs (w_H W) (w_A W) (with_vm_backing (m_vm_lazy model) mat1 model) ->
srealizes tfxsegs (mkCfg ms1 (with_vm_backing (m_vm_lazy model) mat1 model)) T) ->
srealizes tfxsegs (mkCfg ms model) T.
Proof.
intros tbl W n E ss s1 ms model T Htbl HS HAI Hrun Hk.
apply (SRr_srealizes tfxsegs W (mkCfg ms model)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy model) mat1 model) /\
st_ok_ecall tfxsegs E s1 (restrict (w_H W) ms1) /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))) T).
- eapply (SRr_run_gen tfxsegs tbl Htbl Hwx_tfa W n E ss s1 RS_ecall ms model _ HS Hrun).
intros ms1 mat1 HS1 HF HFr. img_apply SRr_ret. split; [img_refl|]. exists ms1, mat1. auto.
- img_exact HAI.
- intros W' c' _ HAI' (-> & ms1 & mat1 & -> & HS1 & HF & HFr). cbn [cfg_model] in HAI'. img_exact (Hk ms1 mat1 HS1 HF HFr HAI').
Qed.
Theorem srz_stdio_writev_by_run {imgk : img} : forall (tbl : ctable) (W : world tfxsegs) E ss ms model ch k s1 s2 zs fd T,
table_ok tfxsegs tbl ->
st_ok tfxsegs E ss (restrict (w_H W) ms) -> AI tfxsegs (w_H W) (w_A W) model ->
wx_step tbl k ss = Some (s1, s2, zs, fd) ->
fdchan (Z_to_bv 64 fd) ch model ->
(forall ms' ws mat', st_ok tfxsegs (havoc E k ws) s2 (restrict (w_H W) ms') ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
skeleton (ss_mem s2) = skeleton (ss_mem ss) -> mem_atoms_lt k (ss_mem s2) = true ->
AI tfxsegs (w_H W) (w_A W) (with_vm_backing (m_vm_lazy model) mat' model) ->
srealizes tfxsegs (mkCfg ms' (with_vm_backing (m_vm_lazy model) mat' model)) T) ->
srealizes tfxsegs (mkCfg ms model) (t_emit (map (WriteEv ch) (map (Z_to_bv 8) zs)) T).
Proof.
intros tbl W E ss ms model ch k s1 s2 zs fd T Htbl HS HAI Hck Hch Hk. unfold wx_step in Hck.
destruct (sym_runN tfxsegs tbl FUEL ss) as [s1' st] eqn:Hrun. destruct st; try discriminate.
destruct (ss_pc s1' =? WL_ECALL1) eqn:Hpc; [|img_try (discriminate)]. apply Z.eqb_eq in Hpc. cbn [negb] in Hck.
destruct (sr_get (ss_regs s1') 17) as [no| | | | | | | | | |] eqn:H17; try discriminate.
destruct no as [|p17|]; try discriminate. do 7 (destruct p17 as [p17|p17|]; try discriminate).
destruct (lit_sv (sr_get (ss_regs s1') 10)) as [fd'|] eqn:H10; [|img_try (discriminate)].
destruct (iovcnt_of (ss_facts s1') (sr_get (ss_regs s1') 12)) as [cnt|] eqn:H12; [|img_try (discriminate)].
destruct (iovcnt_of (ss_facts s1') (sr_get (ss_regs s1') 18)) as [cnt'|] eqn:H18; [|img_try (discriminate)].
destruct (sr_get (ss_regs s1') 2) as [|b K| | | | | | | | |] eqn:H2; try discriminate.
destruct (sr_get (ss_regs s1') 9) as [F| | | | | | | | | |] eqn:H9; try discriminate.
destruct (ss_resv s1') eqn:Hrv; try discriminate.
destruct (negb ((fd' =? 1) || (fd' =? 2))) eqn:Hfd; [img_try (discriminate)|].
assert (Hfd12 : fd' = 1 \/ fd' = 2).
{ apply negb_false_iff in Hfd. apply orb_prop in Hfd as [Hf|Hf]; apply Z.eqb_eq in Hf; img_lia. }
destruct (negb (cnt =? cnt')) eqn:Hcc; [img_try (discriminate)|]. apply negb_false_iff in Hcc. apply Z.eqb_eq in Hcc. (subst cnt'; cbv beta).
destruct (negb (zcanon F =? F)) eqn:HFc; [img_try (discriminate)|]. apply negb_false_iff in HFc. apply Z.eqb_eq in HFc.
destruct (ss_atoms_lt k s1') eqn:Hat; [|img_try (discriminate)]. cbn [negb] in Hck.
destruct (find_wregion (ss_mem s1') b (K + 8) (K + 40)) as [i|] eqn:Hwr; [|img_try (discriminate)].
destruct (atom_lookup (f_atoms (ss_facts s1')) b) as [f|] eqn:Hf; [|img_try (discriminate)].
destruct (lit_buf tfxsegs (ss_mem s1') (SLit (F + 120)) 4) as [fdz|] eqn:Hfdz; [|img_try (discriminate)].
destruct ((0 <=? af_lo f + K) && (af_hi f + K + 40 <=? 2^47) && (0 <=? F) && (F + 124 <=? af_lo f + K + 8)
&& zlist_eqb fdz [fd'; 0; 0; 0]) eqn:Hbnd; [|img_try (discriminate)]. cbn [negb] in Hck.
apply andb_prop in Hbnd as [Hbnd Hfdz4]. apply andb_prop in Hbnd as [Hbnd B4]. apply andb_prop in Hbnd as [Hbnd B3].
apply andb_prop in Hbnd as [B1 B2].
apply Z.leb_le in B1. apply Z.leb_le in B2. apply Z.leb_le in B3. apply Z.leb_le in B4. apply zlist_eqb_eq in Hfdz4. (subst fdz; cbv beta).
destruct (sv_eqb (sr_get (ss_regs s1') 19) (sr_get (ss_regs s1') 11)) eqn:H1911; [|img_try (discriminate)]. cbn [negb] in Hck.
apply sv_eqb_eq in H1911.
destruct (find_wregion_sound _ _ _ _ _ Hwr) as (r & Hi & Hrb & Hrlo & Hrhi & Hwlo & Hwhi).
destruct (sym_run_sound tfxsegs tbl Htbl _ E ss s1' RS_ecall _ HS Hrun) as (_ & _ & _ & Hsk' & _).
pose proof (eq_sym Hsk') as Hsk. clear Hsk'.
assert (Hma : forall i K, mem_atoms_lt k (ss_mem (wl_after s1' i K k)) = true).
{ intros i0 K0. unfold wl_after; cbn [ss_mem].
img_apply (mem_atoms_lt_submem k _ (ss_mem s1')); [img_try (img_apply submem_forget_win)|].
unfold ss_atoms_lt in Hat. apply andb_prop in Hat as [Hat' _]. apply andb_prop in Hat' as [Hat' _].
apply andb_prop in Hat' as [_ Hm]. img_exact Hm. }
assert (Hskafter : forall i K, skeleton (ss_mem (wl_after s1' i K k)) = skeleton (ss_mem ss)).
{ intros i0 K0. unfold wl_after; cbn [ss_mem]. rewrite skeleton_forget_win. symmetry. img_exact Hsk. }
eapply (srz_run_ecall_r tbl W FUEL E ss s1' ms model _ Htbl HS HAI Hrun).
intros ms1 mat1 HS1 HF1 HFr1 HAI1.
pose proof HS1 as HS1copy.
destruct HS1copy as (_ & _ & _ & _ & _ & _ & Hregs1 & Hmem1 & HG1).
pose proof (lit_sv_sound E _ _ H10) as [D10 R10].
pose proof (iovcnt_of_sound E _ _ _ HG1 H12) as D12.
pose proof (iovcnt_of_sound E _ _ _ HG1 H18) as D18.
assert (H32 : fd32 (Z_to_bv 64 fd') = Z_to_bv 64 fd') by (img_try (destruct Hfd12 as [-> | ->]; img_refl)).
assert (Hfd31 : bv_unsigned (Z_to_bv 64 fd') < 2^31) by (img_try (rewrite u_Z2bv by img_lia; img_lia)).
pose proof (atom_lookup_ok E _ _ _ (proj1 HG1) Hf) as (Hbf & _).
pose proof (lit_buf_sound tfxsegs E (mrestrict (w_H W) (ms_mem ms1)) _ _ _ _ Hmem1 Hfdz) as Hfdrd. cbn [sv_denot] in Hfdrd.
assert (HfdB : bytes_le_to_Z (map (Z_to_bv 8) [fd'; 0; 0; 0]) = bv_unsigned (Z_to_bv 64 fd')).
{ clear -Hfd12. destruct Hfd12 as [-> | ->]; (img_case; vm_compute); img_refl. }
destruct (cnt =? 2) eqn:Hc2.
- apply Z.eqb_eq in Hc2. (subst cnt; cbv beta).
destruct (sv_eqb (sr_get (ss_regs s1') 19) (SOff b (K + 8))) eqn:H19; [|img_try (discriminate)]. cbn [negb] in Hck.
apply sv_eqb_eq in H19.
destruct (wx_one s1' b K (K + 8)) as [[[[vb0 vl0] zs0] n0]|] eqn:Ho0; [|img_try (discriminate)].
destruct (wx_one s1' b K (K + 24)) as [[[[vb1 vl1] zs1] n1]|] eqn:Ho1; [|img_try (discriminate)].
destruct (lit_sv (sr_get (ss_regs s1') 22)) as [rem|] eqn:H22; [|img_try (discriminate)].
destruct ((rem =? n0 + n1) && (1 <=? rem) && (rem <=? 2 ^ 25)) eqn:Hrem; [|img_try (discriminate)].
injection Hck as <- <- <- <-.
apply andb_prop in Hrem as [Hrem Q3]. apply andb_prop in Hrem as [Q1 Q2].
apply Z.eqb_eq in Q1. apply Z.leb_le in Q2. apply Z.leb_le in Q3. (subst rem; cbv beta).
destruct (wx_one_sound E s1' (mrestrict (w_H W) (ms_mem ms1)) b K _ _ _ _ _ Hmem1 HG1 Ho0) as (Hiov0 & Hrd0 & HU0 & Hlz0 & Hn0 & Hnw0 & Hd0).
destruct (wx_one_sound E s1' (mrestrict (w_H W) (ms_mem ms1)) b K _ _ _ _ _ Hmem1 HG1 Ho1) as (Hiov1 & Hrd1 & HU1 & Hlz1 & Hn1 & Hnw1 & Hd1).
rewrite map_app.
eapply (srz_sym_stdio_writev2 W E s1' ms1 _ (Z_to_bv 64 fd') ch i b K F r vb0 vl0 vb1 vl1 _ _ _ k T HAI1 HS1 Hrv Hpc);
[ img_try (img_exact H17) | img_try (img_exact D10) | img_try (img_exact Hch) | img_try (img_exact H32) | img_try (img_exact Hfd31) | img_try (img_exact D12) | img_try (img_exact D18) | img_try (img_exact H2)
| img_try (img_exact H19) | img_try (rewrite <- H1911; img_exact H19) | img_try (rewrite (lit_sv_U E _ _ H22), HU0, HU1; img_refl)
| img_try (rewrite H9, U_SLit; img_exact HFc)
| img_try (img_exact Hi) | img_try (img_exact Hrb) | img_try (img_exact Hrlo) | img_try (img_exact Hrhi) | img_try (img_exact Hwlo) | img_try (img_exact Hwhi)
| img_try (unfold iov_read2; rewrite Hiov0; replace (K + 8 + 16) with (K + 24) by img_lia; rewrite Hiov1; img_refl)
| img_try (img_exact Hrd0) | img_try (img_exact Hrd1) | img_try (rewrite HU0, HU1; img_lia)
| img_try (rewrite HU0; img_exact Hnw0) | img_try (rewrite HU0; img_exact Hd0) | img_try (rewrite HU1; img_exact Hnw1) | img_try (rewrite HU1; img_exact Hd1)
| img_try (img_exact Hfdrd) | img_try (img_exact HfdB) | img_lia | img_try (unfold M64 in *; img_lia) | img_lia | img_lia | img_try (unfold M64 in *; img_lia) | img_try (img_exact Hat) | ].
intros ms' ws mat' HS' HF' HFr' HAI'. rewrite wvb_wvb in HAI' |- *.
img_apply (Hk ms' ws _ HS'); [img_try (eapply frame_of_trans; [img_exact Hsk | img_exact HF1 | img_exact HF']) | img_try (eapply frame_of_trans; [img_exact Hsk | img_exact HFr1 | img_exact HFr']) | img_try (img_apply Hskafter) | img_try (img_apply Hma) | img_try (img_exact HAI')].
- destruct (cnt =? 1) eqn:Hc1; [|img_try (discriminate)]. apply Z.eqb_eq in Hc1. (subst cnt; cbv beta).
destruct (sv_eqb (sr_get (ss_regs s1') 19) (SOff b (K + 24))) eqn:H19; [|img_try (discriminate)]. cbn [negb] in Hck.
apply sv_eqb_eq in H19.
destruct (wx_one s1' b K (K + 24)) as [[[[vb1 vl1] zs1] n1]|] eqn:Ho1; [|img_try (discriminate)].
destruct (lit_sv (sr_get (ss_regs s1') 22)) as [rem|] eqn:H22; [|img_try (discriminate)].
destruct ((rem =? n1) && (1 <=? rem) && (rem <=? 2 ^ 25)) eqn:Hrem; [|img_try (discriminate)].
injection Hck as <- <- <- <-.
apply andb_prop in Hrem as [Hrem Q3]. apply andb_prop in Hrem as [Q1 Q2].
apply Z.eqb_eq in Q1. apply Z.leb_le in Q2. apply Z.leb_le in Q3. (subst rem; cbv beta).
destruct (wx_one_sound E s1' (mrestrict (w_H W) (ms_mem ms1)) b K _ _ _ _ _ Hmem1 HG1 Ho1) as (Hiov1 & Hrd1 & HU1 & Hlz1 & Hn1 & Hnw1 & Hd1).
eapply (srz_sym_stdio_writev1 W E s1' ms1 _ (Z_to_bv 64 fd') ch i b K F r vb1 vl1 _ _ k T HAI1 HS1 Hrv Hpc);
[ img_try (img_exact H17) | img_try (img_exact D10) | img_try (img_exact Hch) | img_try (img_exact H32) | img_try (img_exact Hfd31) | img_try (img_exact D12) | img_try (img_exact D18) | img_try (img_exact H2)
| img_try (img_exact H19) | img_try (rewrite <- H1911; img_exact H19) | img_try (rewrite (lit_sv_U E _ _ H22), HU1; img_refl)
| img_try (rewrite H9, U_SLit; img_exact HFc)
| img_try (img_exact Hi) | img_try (img_exact Hrb) | img_try (img_exact Hrlo) | img_try (img_exact Hrhi) | img_try (img_exact Hwlo) | img_try (img_exact Hwhi)
| img_try (img_exact Hiov1)
| img_try (img_exact Hrd1) | img_try (rewrite HU1; img_lia)
| img_try (rewrite HU1; img_exact Hnw1) | img_try (rewrite HU1; img_exact Hd1)
| img_try (img_exact Hfdrd) | img_try (img_exact HfdB) | img_lia | img_try (unfold M64 in *; img_lia) | img_lia | img_lia | img_try (unfold M64 in *; img_lia) | img_try (img_exact Hat) | ].
intros ms' ws mat' HS' HF' HFr' HAI'. rewrite wvb_wvb in HAI' |- *.
img_apply (Hk ms' ws _ HS'); [img_try (eapply frame_of_trans; [img_exact Hsk | img_exact HF1 | img_exact HF']) | img_try (eapply frame_of_trans; [img_exact Hsk | img_exact HFr1 | img_exact HFr']) | img_try (img_apply Hskafter) | img_try (img_apply Hma) | img_try (img_exact HAI')].
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
induction l1 as [|x l1 IH]; intros [|y l2] H; cbn in H; try discriminate; [img_refl|].
apply andb_prop in H as [H1 H2]. f_equal; [|img_try (img_apply IH; img_exact H2)].
destruct x as [[[[b1 lo1] hi1] w1] x1]. destruct y as [[[[b2 lo2] hi2] w2] x2]. cbn in H1.
apply andb_prop in H1 as [H1 E4]. apply andb_prop in H1 as [H1 E3]. apply andb_prop in H1 as [H1 E2].
apply andb_prop in H1 as [E0 E1].
apply obase_eqb_eq in E0. apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. apply Z.eqb_eq in E3. apply Z.eqb_eq in E4.
(subst; cbv beta). img_refl.
Qed.
Definition wx_msg_check {imgk : img} (tbl : ctable) (k : nat) (ss : sstate) (msg : list byte) : option (sstate * Z) :=
match wx_step tbl k ss with
| Some (s1, s2, zs, fd) =>
if zlist_eqb zs (map bv_unsigned msg) then Some (s2, fd) else None
| None => None
end.

End e.
