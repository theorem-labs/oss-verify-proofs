(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN0h.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK0v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0c.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN01.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2j.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0l.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP04.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP01.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH00.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0j.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition E0 (regs : bvmap 5 word) (cx : nat -> Z) : env :=
mkEnv (fun n => match n with
| 1%nat => getr regs 1%bv
| 2%nat => getr regs 2%bv
| 3%nat => getr regs 3%bv
| 4%nat => getr regs 4%bv
| 5%nat => getr regs 5%bv
| 6%nat => getr regs 6%bv
| 7%nat => getr regs 7%bv
| 8%nat => getr regs 8%bv
| 9%nat => getr regs 9%bv
| 10%nat => getr regs 10%bv
| 11%nat => getr regs 11%bv
| 12%nat => getr regs 12%bv
| 13%nat => getr regs 13%bv
| 14%nat => getr regs 14%bv
| 15%nat => getr regs 15%bv
| 16%nat => getr regs 16%bv
| 17%nat => getr regs 17%bv
| 18%nat => getr regs 18%bv
| 19%nat => getr regs 19%bv
| 20%nat => getr regs 20%bv
| 21%nat => getr regs 21%bv
| 22%nat => getr regs 22%bv
| 23%nat => getr regs 23%bv
| 24%nat => getr regs 24%bv
| 25%nat => getr regs 25%bv
| 26%nat => getr regs 26%bv
| 27%nat => getr regs 27%bv
| 28%nat => getr regs 28%bv
| 29%nat => getr regs 29%bv
| 30%nat => getr regs 30%bv
| 31%nat => getr regs 31%bv
| n => Z_to_bv 64 (cx n)
end)
(fun _ => []).
Definition cx_set (cx : nat -> Z) (n : nat) (v : Z) : nat -> Z := fun k => if Nat.eqb k n then v else cx k.
Lemma E0_cx : forall regs cx n, (32 <= n)%nat -> ew (E0 regs cx) n = Z_to_bv 64 (cx n).
Proof. intros regs cx n Hn. cbn [ew E0]. do 32 (destruct n as [|n]; [lia|]). reflexivity. Qed.
Lemma E0_reg : forall regs cx n, (1 <= n <= 31)%nat -> ew (E0 regs cx) n = getr regs (Z_to_bv 5 (Z.of_nat n)).
Proof.
intros regs cx n Hn. destruct n as [|n]; [lia|].
do 31 (destruct n as [|n]; [reflexivity|]). lia.
Qed.
Section d.
Variable segs : list Segment.
Lemma chunk_ok_word : forall E m base off v (val : Z),
sv_denot E v = Z_to_bv 64 val -> word_mem segs m (base + off) val ->
chunk_ok segs E m base (mkChunk off (CVal 8 v)).
Proof.
intros E m base off v val Hv Hw i Hi. cbn [c_off c_val c_len cv_len cbyte] in Hi |- *.
exists (byte_of_word (sv_denot E v) i). split; [reflexivity|].
replace i with (Z.of_nat (Z.to_nat i)) by lia. rewrite (Hw (Z.to_nat i)) by lia.
f_equal. unfold byte_of_word. rewrite Hv.
rewrite (YN01.le_byte_bv val 8 (Z.to_nat i)) by lia.
rewrite Z_to_bv_unsigned. change (bv_wrap 64 val) with (val mod 2 ^ (8 * Z.of_nat 8)). reflexivity.
Qed.
Lemma chunk_ok_w4 : forall E m base off v (val : Z),
sv_denot E v = Z_to_bv 64 val -> 0 <= val < 2 ^ 32 ->
(forall k, (k < 4)%nat -> mbyte segs m (base + off + Z.of_nat k) = Some (Z_to_bv 8 (le_byte val 4 k))) ->
chunk_ok segs E m base (mkChunk off (CVal 4 v)).
Proof.
intros E m base off v val Hv Hval Hw. apply (chunk_ok_cval segs E m base off 4 v val Hv); [lia | exact Hw].
Qed.
Lemma word_mem_of_chunk : forall E m base off v val,
chunk_ok segs E m base (mkChunk off (CVal 8 v)) -> sv_denot E v = Z_to_bv 64 val ->
word_mem segs m (base + off) val.
Proof.
intros E m base off v val Hc Hv k Hk.
apply (chunk_bytes_cval segs E m base off 8 v val Hc); [| exact Hk].
rewrite Hv, Z_to_bv_unsigned. change (bv_wrap 64 val) with (val mod 2 ^ 64).
change (8 * Z.of_N 8) with 64. rewrite Z.mod_mod by lia. reflexivity.
Qed.
Definition wskel (rs : smem) : list (option nat * Z * Z) := map (fun r => (r_base r, r_wlo r, r_whi r)) rs.
Lemma in_wrange_wskel : forall E rs x,
in_wrange E rs x -> exists b lo hi, In (b, lo, hi) (wskel rs) /\ base_val E b + lo <= x < base_val E b + hi.
Proof.
intros E rs x (r & Hin & Hx). exists (r_base r), (r_wlo r), (r_whi r). split; [|exact Hx].
unfold wskel. apply in_map_iff. exists r. auto.
Qed.
Lemma frame_of_at : forall E rs m m' x,
frame_of E rs m m' -> 0 <= x < 2 ^ 64 -> ~ in_wrange E rs x -> m' (Z_to_bv 64 x) = m (Z_to_bv 64 x).
Proof. intros E rs m m' x HF Hx Hn. apply (HF (Z_to_bv 64 x)). rewrite u64_of_Z by exact Hx. exact Hn. Qed.
Lemma lupd_nth_spec {T} : forall (l : list T) i f k,
nth_error (lupd_nth l i f) k = if Nat.eqb k i then option_map f (nth_error l k) else nth_error l k.
Proof.
induction l as [|x l IH]; intros i f k.
- cbn. destruct (Nat.eqb k i); destruct k; reflexivity.
- destruct i as [|i]; destruct k as [|k]; cbn; try reflexivity. rewrite IH. reflexivity.
Qed.
Lemma lupd_nth_length {T} : forall (l : list T) i f, length (lupd_nth l i f) = length l.
Proof. induction l as [|x l IH]; intros [|i] f; cbn; try reflexivity. rewrite IH. reflexivity. Qed.
Lemma In_lupd_nth {T} : forall (l : list T) i f y,
In y (lupd_nth l i f) -> In y l \/ exists x, nth_error l i = Some x /\ y = f x.
Proof.
induction l as [|x l IH]; intros [|i] f y Hy; cbn in Hy.
- destruct Hy.
- destruct Hy.
- destruct Hy as [<-|Hy]; [right; exists x; auto | left; right; exact Hy].
- destruct Hy as [<-|Hy]; [left; left; reflexivity|].
destruct (IH i f y Hy) as [H|(x' & H1 & H2)]; [left; right; exact H | right; exists x'; auto].
Qed.
Lemma upd_chunk_extents : forall rs i off cv,
map (fun r => (r_base r, r_lo r, r_hi r))
(lupd_nth rs i (fun r => mkRegion (r_base r) (r_lo r) (r_hi r) (r_wlo r) (r_whi r)
(map (fun c => if (c_off c =? off) then mkChunk off cv else c) (r_chunks r))))
= map (fun r => (r_base r, r_lo r, r_hi r)) rs.
Proof. induction rs as [|r rs IH]; intros [|i] off cv; cbn; try reflexivity; rewrite ?IH; reflexivity. Qed.
Lemma pairwise_disjoint_ext : forall E rs rs',
map (fun r => (r_base r, r_lo r, r_hi r)) rs' = map (fun r => (r_base r, r_lo r, r_hi r)) rs ->
pairwise_disjoint E rs -> pairwise_disjoint E rs'.
Proof.
intros E rs. induction rs as [|r rs IH]; intros [|r' rs'] Hm Hpd; cbn in *; try discriminate; [exact I|].
injection Hm as Hb Hlo Hhi Hm'. destruct Hpd as [Ha Hp]. split; [|apply IH; assumption].
clear IH Hp. revert rs' Hm'. induction rs as [|x rs IH]; intros [|x' rs'] Hm'; cbn in *; try discriminate; [exact I|].
injection Hm' as Xb Xlo Xhi Hm''. destruct Ha as [D Ha']. split; [| apply IH; [exact Ha' | exact Hm'']].
unfold extent_disjoint in *. rewrite Hb, Hlo, Hhi, Xb, Xlo, Xhi. exact D.
Qed.
Lemma st_ok_upd_chunk : forall E ss ms i off (w : N) v v',
st_ok segs E ss ms ->
(forall r c, nth_error (ss_mem ss) i = Some r -> In c (r_chunks r) -> c_off c = off -> c_val c = CVal w v) ->
sv_denot E v' = sv_denot E v ->
regions_wf (ss_mem (upd_chunk i off (CVal w v') ss)) = true ->
st_ok segs E (upd_chunk i off (CVal w v') ss) ms.
Proof.
intros E ss ms i off w v v' HS Hc Hv Hwf.
destruct HS as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & (Wf & Ok & Pd) & S9).
unfold st_ok, upd_chunk, setmem; cbn. repeat (split; [assumption|]). split; [|exact S9].
split; [exact Hwf|]. split.
- rewrite Forall_forall in Ok |- *. intros r' Hin.
destruct (In_lupd_nth _ _ _ _ Hin) as [H|(r & Hr & ->)]; [apply Ok; exact H|].
pose proof (Ok r (nth_error_In _ _ Hr)) as (R1 & R2 & R3 & R4).
split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. cbn.
rewrite Forall_forall in R4 |- *. intros c' Hc'. apply in_map_iff in Hc' as (c & Ec & Hcin). subst c'.
destruct (Z.eqb_spec (c_off c) off) as [Eo|Ne]; [|apply R4; exact Hcin].
pose proof (Hc r c Hr Hcin Eo) as Ecv. specialize (R4 c Hcin).
destruct c as [co cvv]. cbn in Eo, Ecv. subst co cvv.
intros j Hj. destruct (R4 j Hj) as (b & Hb1 & Hb2). exists b. cbn [c_off c_val cbyte] in *. rewrite Hv. auto.
- eapply pairwise_disjoint_ext; [apply upd_chunk_extents | exact Pd].
Qed.
Lemma st_ok_drop_chunk : forall E ss ms i off,
st_ok segs E ss ms -> regions_wf (ss_mem (drop_chunk i off ss)) = true -> st_ok segs E (drop_chunk i off ss) ms.
Proof.
intros E ss ms i off HS Hwf.
destruct HS as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & (Wf & Ok & Pd) & S9).
unfold st_ok, drop_chunk, setmem; cbn. repeat (split; [assumption|]). split; [|exact S9].
split; [exact Hwf|]. split.
- rewrite Forall_forall in Ok |- *. intros r' Hin.
destruct (In_lupd_nth _ _ _ _ Hin) as [H|(r & Hr & ->)]; [apply Ok; exact H|].
pose proof (Ok r (nth_error_In _ _ Hr)) as (R1 & R2 & R3 & R4).
split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. cbn.
rewrite Forall_forall in R4 |- *. intros c Hc. apply filter_In in Hc as [Hc _]. apply R4. exact Hc.
- eapply pairwise_disjoint_ext; [| exact Pd]. clear.
generalize (ss_mem ss) as rs. intros rs. revert i. induction rs as [|r rs IH]; intros [|i]; cbn; try reflexivity; rewrite ?IH; reflexivity.
Qed.
Lemma st_ok_regs_ext : forall E ss regs regs' pc m rom,
st_ok segs E ss (mkst regs pc m rom) -> (forall r, getr regs' r = getr regs r) -> st_ok segs E ss (mkst regs' pc m rom).
Proof.
intros E ss regs regs' pc m rom (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9) Hext.
unfold st_ok, mkst; cbn in *. repeat (split; [assumption|]). split; [|exact (conj S8 S9)].
intros r. rewrite Hext. apply S7.
Qed.
Lemma st_ok_set_reg : forall n E ss regs pc m rom r v,
st_ok segs E ss (mkst regs pc m rom) -> ss_atoms_lt n ss = true -> bv_eqb r 0 = false ->
st_ok segs (ewset E n v)
(mkSS (ss_pc ss) (sr_set (ss_regs ss) r (SOff n 0)) (ss_mem ss) (ss_resv ss) (ss_facts ss))
(mkst (regupd regs r v) pc m rom).
Proof.
intros n E ss regs pc m rom r v HS Hat Hr.
pose proof (st_ok_agree segs n E (ewset E n v) ss _ HS (env_agree_ewset _ _ _) Hat) as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9).
unfold st_ok, mkst; cbn in *. repeat (split; [assumption|]). split; [|exact (conj S8 S9)].
generalize (regs_ok_set (ewset E n v) (ss_regs ss) regs r v (SOff n 0) S7). rewrite Hr. intros H. apply H.
cbn. rewrite Nat.eqb_refl. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned.
Qed.
Lemma ss_atoms_lt_set_reg : forall n ss r,
ss_atoms_lt n ss = true ->
ss_atoms_lt (S n) (mkSS (ss_pc ss) (sr_set (ss_regs ss) r (SOff n 0)) (ss_mem ss) (ss_resv ss) (ss_facts ss)) = true.
Proof.
intros n ss r Hat. unfold ss_atoms_lt in Hat |- *. cbn [ss_regs ss_mem ss_facts ss_resv].
apply andb_prop in Hat as [Hat H4]. apply andb_prop in Hat as [Hat H3]. apply andb_prop in Hat as [H1 H2].
rewrite (mem_atoms_lt_mono n (S n) _ ltac:(lia) H2). rewrite (facts_atoms_lt_mono n (S n) _ ltac:(lia) H3).
rewrite regs_atoms_lt_set; [| apply (regs_atoms_lt_mono n (S n)); [lia | assumption] | cbn; apply Nat.leb_refl].
destruct (ss_resv ss); [rewrite (sv_atoms_lt_mono n (S n) _ ltac:(lia) H4)|]; reflexivity.
Qed.
Lemma st_ok_clobber : forall rs n E ss regs regs' pc m rom,
st_ok segs E ss (mkst regs pc m rom) -> ss_atoms_lt n ss = true ->
forallb (fun r : reg => negb (bv_eqb r 0)) rs = true ->
(forall r, ~ In r rs -> getr regs' r = getr regs r) ->
exists E', env_agree n E E' /\ st_ok segs E' (junk_regs rs n ss) (mkst regs' pc m rom).
Proof.
induction rs as [|r rs IH]; intros n E ss regs regs' pc m rom HS Hat Hrs Hext; cbn.
- exists E. split; [apply env_agree_refl|]. eapply st_ok_regs_ext; [exact HS|]. intros r. apply Hext. intros [].
- cbn in Hrs. apply andb_prop in Hrs as [Hr Hrs]. apply negb_true_iff in Hr.
pose proof (st_ok_set_reg n E ss regs pc m rom r (getr regs' r) HS Hat Hr) as HS1.
destruct (IH (S n) _ _ _ regs' pc m rom HS1 (ss_atoms_lt_set_reg n ss r Hat) Hrs) as (E' & HA & HS').
+ intros r' Hn'. destruct (decide (r' = r)) as [->|Hne].
* unfold getr, regupd. rewrite Hr. unfold reg_get. rewrite bvmap_get_set_same. reflexivity.
* transitivity (getr regs r'); [apply Hext; intros [H|H]; [exact (Hne (eq_sym H)) | exact (Hn' H)] |].
unfold getr, regupd. rewrite Hr. destruct (bv_eqb r' 0); [reflexivity|]. unfold reg_get.
rewrite bvmap_get_set_other; [reflexivity|]. intros Heq. apply Hne. symmetry. exact Heq.
+ exists E'. split; [|exact HS'].
eapply env_agree_trans; [apply env_agree_ewset | eapply env_agree_le; [| exact HA]; lia].
Qed.
Definition chunk_is (ss : sstate) (i : nat) (off : Z) (cv : cval) : bool :=
match nth_error (ss_mem ss) i with
| Some r => forallb (fun c => negb (Z.eqb (c_off c) off) || cval_eqb (c_val c) cv) (r_chunks r)
| None => true
end.
Lemma chunk_is_sound : forall ss i off cv, chunk_is ss i off cv = true ->
forall r c, nth_error (ss_mem ss) i = Some r -> In c (r_chunks r) -> c_off c = off -> c_val c = cv.
Proof.
intros ss i off cv H r c Hr Hc Ho. unfold chunk_is in H. rewrite Hr in H.
pose proof (proj1 (forallb_forall _ _) H c Hc) as Hx. cbn beta in Hx. rewrite Ho, Z.eqb_refl in Hx. cbn in Hx.
apply cval_eqb_eq. exact Hx.
Qed.
Lemma st_ok_abs_chunk : forall n E ss ms i off (w : N) v,
st_ok segs E ss ms -> ss_atoms_lt n ss = true -> chunk_is ss i off (CVal w v) = true -> sv_atoms_lt n v = true ->
regions_wf (ss_mem (upd_chunk i off (CVal w (SOff n 0)) ss)) = true ->
st_ok segs (ewset E n (sv_denot E v)) (upd_chunk i off (CVal w (SOff n 0)) ss) ms /\ env_agree n E (ewset E n (sv_denot E v)).
Proof.
intros n E ss ms i off w v HS Hat Hc Hv Hwf.
pose proof (env_agree_ewset E n (sv_denot E v)) as HA.
split; [| exact HA].
apply (st_ok_upd_chunk (ewset E n (sv_denot E v)) ss ms i off w v (SOff n 0)).
- exact (st_ok_agree segs n E _ ss ms HS HA Hat).
- exact (chunk_is_sound ss i off (CVal w v) Hc).
- cbn [sv_denot ew ewset]. rewrite Nat.eqb_refl, Z.add_0_r, Z_to_bv_bv_unsigned. symmetry. apply (sv_denot_agree n); [exact HA | exact Hv].
- exact Hwf.
Qed.
Lemma st_ok_setfacts : forall E ss ms G, st_ok segs E ss ms -> facts_ok E G -> st_ok segs E (setfacts G ss) ms.
Proof. intros. apply st_ok_facts; assumption. Qed.
End d.
Section e.
Variables (regs : bvmap 5 word) (mem : word -> option byte) (cx : nat -> Z).
Let E := E0 regs cx.
Let sp := bv_unsigned (getr regs 2).
Hypothesis Hsp : alloc_ceiling + AMS <= sp /\ sp < 2 ^ 63 /\ sp mod 16 = 0.
Hypothesis Hstk : forall x, sp - AMS <= x < sp -> writable_at src0segs mem x.
Hypothesis Htp : getr regs 4 = Z_to_bv 64 TP.
Hypothesis Herr : forall x, ERRNO <= x < ERRNO + 4 -> writable_at src0segs mem x.
Hypothesis Hgot : word_mem src0segs mem GOT GUARD.
Hypothesis Hguard : word_mem src0segs mem GUARD (cx 32%nat).
Hypothesis Hpgsz : word_mem src0segs mem (LIBC + 48) 4096.
Hypothesis Hctxw : forall x, CTX <= x < CTX + 928 -> writable_at src0segs mem x.
Hypothesis Hc16 : word_mem src0segs mem (CTX + 16) (cx 33%nat).
Hypothesis Hc24 : word_mem src0segs mem (CTX + 24) (cx 36%nat).
Hypothesis Hc32 : word_mem src0segs mem (CTX + 32) (cx 37%nat).
Hypothesis Hc40 : word_mem src0segs mem (CTX + 40) (cx 38%nat).
Hypothesis Hc48 : word_mem src0segs mem (CTX + 48) (cx 39%nat).
Hypothesis Hc56 : word_mem src0segs mem (CTX + 56) (cx 40%nat).
Hypothesis Hc64 : word_mem src0segs mem (CTX + 64) (cx 41%nat).
Hypothesis Hc72 : word_mem src0segs mem (CTX + 72) (cx 42%nat).
Hypothesis Hc920 : word_mem src0segs mem (CTX + 920) (cx 43%nat).
Hypothesis Hsh : 0 <= cx 39%nat <= 40.
Lemma regs_ok_am : regs_ok E regs_am regs.
Proof.
subst E. regs_ok_cases; first [ exact Htp | symmetry; exact Htp | apply getr_zero | symmetry; apply getr_zero ].
Qed.
Ltac lits := unfold LOCK, CTX, LIBC, ERRNO, TP, GOT, GUARD, AMS, src0_D_malloc_lock, src0_D_malloc_context, src0_D_libc, src0_tp,
src0_D_got_stack_chk_guard, src0_D_stack_chk_guard in *.
Lemma E_cx : forall n, (32 <= n)%nat -> sv_denot E (SOff n 0) = Z_to_bv 64 (cx n).
Proof.
intros n Hn. cbn [sv_denot]. subst E. rewrite (E0_cx regs cx n Hn). rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma region_ok_statics : forall (i : bool),
(forall k, (k < 4)%nat -> mbyte src0segs mem (CTX + 8 + Z.of_nat k) = Some (Z_to_bv 8 (le_byte (if i then 1 else 0) 4 k))) ->
word_mem src0segs mem CTX (if i then cx 0%nat else 0)   ->
Forall (region_ok src0segs E mem) [R_got; R_guard; R_pgsz; R_ctxA i; R_ctxB; R_ctxC; R_errno].
Proof.
intros i Hinit Hsec. pose proof (proj1 alloc_ceiling_val) as AC.
repeat apply Forall_cons; try apply Forall_nil;
apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val R_got R_guard R_pgsz R_ctxA R_ctxB R_ctxC R_errno]; lits; try lia;
try (intros o Ho; rewrite Z.add_0_l; first [apply Hctxw; lia | apply Herr; lia]);
repeat apply Forall_cons; try apply Forall_nil.
- apply (chunk_ok_word src0segs E mem 0 _ _ GUARD); [reflexivity | exact Hgot].
- apply (chunk_ok_word src0segs E mem 0 _ _ (cx 32%nat)); [apply E_cx; lia | exact Hguard].
- apply (chunk_ok_word src0segs E mem 0 _ _ 4096); [reflexivity | exact Hpgsz].
- apply (chunk_ok_word src0segs E mem 0 _ _ (if i then cx 0%nat else 0));
[destruct i; [subst E; cbn [sv_denot ew E0]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | reflexivity] | exact Hsec].
- apply (chunk_ok_w4 src0segs E mem 0 _ _ (if i then 1 else 0)); [destruct i; reflexivity | destruct i; lia | intros k Hk; rewrite Z.add_0_l; apply Hinit; exact Hk].
- apply (chunk_ok_word src0segs E mem 0 _ _ (cx 33%nat)); [apply E_cx; lia | exact Hc16].
- apply (chunk_ok_word src0segs E mem 0 _ _ (cx 36%nat)); [apply E_cx; lia | exact Hc24].
- apply (chunk_ok_word src0segs E mem 0 _ _ (cx 37%nat)); [apply E_cx; lia | exact Hc32].
- apply (chunk_ok_word src0segs E mem 0 _ _ (cx 38%nat)); [apply E_cx; lia | exact Hc40].
- apply (chunk_ok_word src0segs E mem 0 _ _ (cx 39%nat)); [apply E_cx; lia | exact Hc48].
- apply (chunk_ok_word src0segs E mem 0 _ _ (cx 40%nat)); [apply E_cx; lia | exact Hc56].
- apply (chunk_ok_word src0segs E mem 0 _ _ (cx 41%nat)); [apply E_cx; lia | exact Hc64].
- apply (chunk_ok_word src0segs E mem 0 _ _ (cx 42%nat)); [apply E_cx; lia | exact Hc72].
- apply (chunk_ok_word src0segs E mem 0 _ _ (cx 43%nat)); [apply E_cx; lia | exact Hc920].
Qed.
Lemma region_ok_stack : region_ok src0segs E mem R_stack.
Proof.
subst E sp. pose proof (proj1 alloc_ceiling_val) as AC.
apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val ew E0 R_stack]; lits; try lia.
- intros o Ho. apply Hstk. lia.
- apply Forall_nil.
Qed.
Lemma facts_ok_am1 : facts_ok E facts_am1.
Proof.
pose proof (proj1 alloc_ceiling_val) as ACV_p9.
subst E sp. pose proof (proj1 alloc_ceiling_val) as AC.
unfold facts_am1, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
unfold afact_ok, F_sp, F_sh; cbn [af_lo af_hi af_al2 ew E0]. lits.
rewrite !u64_of_Z by lia. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. change (2 ^ 4) with 16.
repeat split; lia.
Qed.
Theorem st_ok_am1 :
(forall k, (k < 4)%nat -> mbyte src0segs mem (CTX + 8 + Z.of_nat k) = Some (Z_to_bv 8 (le_byte 1 4 k))) ->
word_mem src0segs mem CTX (cx 0%nat)   ->
st_ok src0segs E ss_am1 (mkst regs (Z_to_bv 64 src0_A_alloc_meta) mem (seg_rom src0segs)).
Proof.
intros Hinit Hsec. pose proof (proj1 alloc_ceiling_val) as AC.
unfold st_ok, ss_am1, mkst; cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem ss_pc ss_regs ss_mem ss_resv ss_facts resv_denot].
repeat (split; [reflexivity|]).
split; [apply regs_ok_am|]. split; [| apply facts_ok_am1].
apply mem_ok_intro; [vm_compute; reflexivity | |].
- unfold mem_am1. apply Forall_cons; [apply region_ok_stack | apply (region_ok_statics true Hinit Hsec)].
- subst E sp. cbn [pairwise_disjoint all_disjoint mem_am1].
repeat split; unfold extent_disjoint; cbn [base_val r_base r_lo r_hi ew E0 R_stack R_got R_guard R_pgsz R_ctxA R_ctxB R_ctxC R_errno]; lits; lia.
Qed.
Hypothesis Hauxp : word_mem src0segs mem (LIBC + 8) (cx 44%nat).
Hypothesis Hauxv : forall k, (k < 10)%nat -> word_mem src0segs mem (cx 44%nat + 16 * Z.of_nat k) (nth k AUXV_TYPES 0).
Hypothesis Har : word_mem src0segs mem (cx 44%nat + 16 * 8 + 8) (cx 45%nat).
Hypothesis Hav_range : 4096 <= cx 44%nat /\ cx 44%nat + 160 <= 2 ^ 63 /\ 4096 <= cx 45%nat /\ cx 45%nat + 16 <= 2 ^ 63 /\ sp <= cx 44%nat.
Lemma facts_ok_am0 : facts_ok E facts_am0.
Proof.
pose proof (proj1 alloc_ceiling_val) as ACV_p9.
subst E sp. pose proof (proj1 alloc_ceiling_val) as AC.
unfold facts_am0, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
unfold afact_ok, F_sp, F_sh, F_av, F_ar; cbn [af_lo af_hi af_al2 ew E0]. lits.
rewrite !u64_of_Z by lia. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. change (2 ^ 4) with 16.
repeat split; lia.
Qed.
Theorem st_ok_am0 :
(forall k, (k < 4)%nat -> mbyte src0segs mem (CTX + 8 + Z.of_nat k) = Some (Z_to_bv 8 (le_byte 0 4 k))) ->
word_mem src0segs mem CTX 0   ->
st_ok src0segs E ss_am0 (mkst regs (Z_to_bv 64 src0_A_alloc_meta) mem (seg_rom src0segs)).
Proof.
intros Hinit Hsec. pose proof (proj1 alloc_ceiling_val) as AC.
assert (E44 : base_val E (Some 44%nat) = cx 44%nat).
{ subst E. cbn [base_val ew E0]. apply u64_of_Z. lia. }
unfold st_ok, ss_am0, mkst; cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem ss_pc ss_regs ss_mem ss_resv ss_facts resv_denot].
repeat (split; [reflexivity|]).
split; [apply regs_ok_am|]. split; [| apply facts_ok_am0].
apply mem_ok_intro; [vm_compute; reflexivity | |].
- change mem_am0 with ((R_stack :: [R_got; R_guard; R_pgsz; R_ctxA false; R_ctxB; R_ctxC; R_errno]) ++ [R_auxp; R_auxv]).
apply Forall_app. split; [apply Forall_cons; [apply region_ok_stack | apply (region_ok_statics false Hinit Hsec)] |].
apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]].
+ apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val R_auxp]; lits; try lia.
apply Forall_cons; [|apply Forall_nil]. apply (chunk_ok_word src0segs E mem 0 _ _ (cx 44%nat)); [apply E_cx; lia | exact Hauxp].
+ apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks R_auxv]; rewrite E44; [lia | lia | intros o Ho; lia |].
assert (TY : forall k off ty, (k < 10)%nat -> off = 16 * Z.of_nat k -> ty = nth k AUXV_TYPES 0 ->
chunk_ok src0segs E mem (cx 44%nat) (mkChunk off (CVal 8 (SLit ty)))).
{ intros k off ty Hk -> ->. apply (chunk_ok_word src0segs E mem _ _ _ (nth k AUXV_TYPES 0)); [reflexivity | apply Hauxv; exact Hk]. }
repeat apply Forall_cons; try apply Forall_nil;
first [ apply (TY 0%nat); [lia | reflexivity | reflexivity]
| apply (TY 1%nat); [lia | reflexivity | reflexivity]
| apply (TY 2%nat); [lia | reflexivity | reflexivity]
| apply (TY 3%nat); [lia | reflexivity | reflexivity]
| apply (TY 4%nat); [lia | reflexivity | reflexivity]
| apply (TY 5%nat); [lia | reflexivity | reflexivity]
| apply (TY 6%nat); [lia | reflexivity | reflexivity]
| apply (TY 7%nat); [lia | reflexivity | reflexivity]
| apply (TY 8%nat); [lia | reflexivity | reflexivity]
| apply (TY 9%nat); [lia | reflexivity | reflexivity]
| apply (chunk_ok_word src0segs E mem _ _ _ (cx 45%nat)); [apply E_cx; lia | replace (cx 44%nat + 136) with (cx 44%nat + 16 * 8 + 8) by lia; exact Har] ].
- subst sp. cbn [pairwise_disjoint all_disjoint app].
repeat split; unfold extent_disjoint; subst E; cbn [base_val r_base r_lo r_hi ew E0 R_stack R_got R_guard R_pgsz R_ctxA R_ctxB R_ctxC R_errno R_auxp R_auxv];
rewrite ?(u64_of_Z (cx 44%nat)) by lia; lits; lia.
Qed.
End e.
End a.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
