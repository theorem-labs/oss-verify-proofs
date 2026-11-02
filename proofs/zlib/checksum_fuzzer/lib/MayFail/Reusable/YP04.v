(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YP04.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0l.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP03.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section e.
Variable segs : list Segment.
Variable tbl : ctable.
Hypothesis tbl_ok : table_ok segs tbl.
Context {fx : FPState}.
Lemma rz_run_to_stop : forall n stop E ss ss' why ms model T,
m_halted model = None -> m_vm_lazy model = [] ->
st_ok segs E ss ms ->
sym_run_toN segs tbl n stop ss = (ss', RS_stopped why) ->
(forall ms', st_ok segs E ss' ms' ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
realizes segs (mkCfg ms' model) T) ->
realizes segs (mkCfg ms model) T.
Proof. intros n stop E ss ss' why. exact (rz_run_to_gen segs tbl tbl_ok n stop E ss ss' (RS_stopped why)). Qed.
Lemma rz_run_to_running : forall n stop E ss ss' ms model T,
m_halted model = None -> m_vm_lazy model = [] ->
st_ok segs E ss ms ->
sym_run_toN segs tbl n stop ss = (ss', RS_running) ->
(forall ms', st_ok segs E ss' ms' ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
realizes segs (mkCfg ms' model) T) ->
realizes segs (mkCfg ms model) T.
Proof. intros n stop E ss ss'. exact (rz_run_to_gen segs tbl tbl_ok n stop E ss ss' RS_running). Qed.
Lemma rz_run_to_ecall : forall n stop E ss ss' ms model T,
m_halted model = None -> m_vm_lazy model = [] ->
st_ok segs E ss ms ->
sym_run_toN segs tbl n stop ss = (ss', RS_ecall) ->
(forall ms', st_ok_ecall segs E ss' ms' ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
realizes segs (mkCfg ms' model) T) ->
realizes segs (mkCfg ms model) T.
Proof. intros n stop E ss ss'. exact (rz_run_to_gen segs tbl tbl_ok n stop E ss ss' RS_ecall). Qed.
Definition lit_zbyte (cv : cval) (i : Z) : option Z :=
match cv with
| CZero _ => Some 0
| CVal _ (SLit z) => Some ((Z.shiftr (zcanon z) (8 * i)) mod 256)
| _ => None
end.
Lemma Z_to_bv8_mod : forall x, Z_to_bv 8 (x mod 256) = Z_to_bv 8 x.
Proof.
intros x. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with 256. apply Z.mod_mod. lia.
Qed.
Lemma lit_zbyte_sound : forall E a cv i z,
lit_zbyte cv i = Some z -> cbyte segs E a cv i = Some (Z_to_bv 8 z).
Proof.
intros E a cv i z H. destruct cv as [w v|len|len|d s len]; cbn in H; try discriminate.
- destruct v; try discriminate. injection H as <-. cbn [cbyte sv_denot].
unfold byte_of_word. rewrite unsigned_lit, Z_to_bv8_mod. reflexivity.
- injection H as <-. reflexivity.
Qed.
Fixpoint find_lit (cs : list chunk) (a : Z) : option Z :=
match cs with
| [] => None
| c :: cs' =>
if (c_off c <=? a) && (a <? c_off c + c_len c)
then match lit_zbyte (c_val c) (a - c_off c) with
| Some z => Some z
| None => find_lit cs' a
end
else find_lit cs' a
end.
Lemma find_lit_sound : forall E m base cs a z,
Forall (chunk_ok segs E m base) cs -> find_lit cs a = Some z ->
mbyte segs m (base + a) = Some (Z_to_bv 8 z).
Proof.
intros E m base cs a z Hcs. induction Hcs as [|c cs Hc Hcs IH]; cbn; intros H; [discriminate|].
destruct ((c_off c <=? a) && (a <? c_off c + c_len c)) eqn:Hin; [|apply IH; exact H].
apply andb_prop in Hin as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
destruct (lit_zbyte (c_val c) (a - c_off c)) as [z'|] eqn:Hz; [|apply IH; exact H].
injection H as <-.
destruct (Hc (a - c_off c) ltac:(lia)) as (b & Hb1 & Hb2).
rewrite (lit_zbyte_sound E _ _ _ _ Hz) in Hb1. injection Hb1 as <-.
replace (base + a) with (base + c_off c + (a - c_off c)) by lia. exact Hb2.
Qed.
Fixpoint cover_lit (cs : list chunk) (cv : cval) (off : Z) (i : Z) (n : nat) : bool :=
match n with
| O => true
| S n' => match lit_zbyte cv i, find_lit cs (off + i) with
| Some z, Some z' => Z.eqb z z' && cover_lit cs cv off (i + 1) n'
| _, _ => false
end
end.
Lemma cover_lit_sound : forall E m base cs cv off n i,
Forall (chunk_ok segs E m base) cs -> cover_lit cs cv off i n = true ->
forall j, i <= j < i + Z.of_nat n ->
exists b, cbyte segs E (base + off) cv j = Some b /\ mbyte segs m (base + off + j) = Some b.
Proof.
intros E m base cs cv off n. induction n as [|n IH]; intros i Hcs H j Hj; [lia|].
cbn [cover_lit] in H.
destruct (lit_zbyte cv i) as [z|] eqn:Hz; [|discriminate].
destruct (find_lit cs (off + i)) as [z'|] eqn:Hf; [|discriminate].
apply andb_prop in H as [Heq H]. apply Z.eqb_eq in Heq. subst z'.
destruct (Z.eq_dec j i) as [->|Hne].
- exists (Z_to_bv 8 z). split; [apply lit_zbyte_sound; exact Hz|].
replace (base + off + i) with (base + (off + i)) by lia.
eapply find_lit_sound; eauto.
- apply (IH (i + 1)); [exact Hcs| exact H| lia].
Qed.
Definition add_lit_region (r : region) (c : chunk) : option region :=
if chunk_inside r c && cover_lit (r_chunks r) (c_val c) (c_off c) 0 (Z.to_nat (c_len c))
then Some (mkRegion (r_base r) (r_lo r) (r_hi r) (r_wlo r) (r_whi r) (c :: r_chunks r))
else None.
Fixpoint add_lit_chunk (rs : smem) (b : option nat) (c : chunk) : option smem :=
match rs with
| [] => None
| r :: rs' =>
if obase_eqb (r_base r) b && (r_lo r <=? c_off c) && (c_off c <? r_hi r)
then match add_lit_region r c with Some r' => Some (r' :: rs') | None => None end
else match add_lit_chunk rs' b c with Some rs'' => Some (r :: rs'') | None => None end
end.
Lemma add_lit_region_facts : forall E m r c r',
add_lit_region r c = Some r' ->
region_wf r = true -> region_ok segs E m r ->
region_wf r' = true /\ region_ok segs E m r' /\ extent_of r' = extent_of r
/\ r_wlo r' = r_wlo r /\ r_whi r' = r_whi r.
Proof.
intros E m r c r' H Hwf Hok. unfold add_lit_region in H.
destruct (chunk_inside r c && cover_lit (r_chunks r) (c_val c) (c_off c) 0 (Z.to_nat (c_len c))) eqn:Hck;
[|discriminate]. injection H as <-.
apply andb_prop in Hck as [Hci Hcov].
pose proof (chunk_inside_facts r c Hci) as (C1 & C2 & C3).
destruct Hok as (H0 & H1 & Hw & Hcs).
split; [|split; [|split; [reflexivity| split; reflexivity]]].
- unfold region_wf in Hwf |- *; cbn [r_lo r_hi r_wlo r_whi r_chunks forallb].
apply andb_prop in Hwf as [Hwf1 Hwf2]. rewrite Hwf1. cbn [andb].
apply andb_true_intro. split; [|exact Hwf2].
unfold chunk_inside in Hci |- *. cbn [r_lo r_hi]. exact Hci.
- unfold region_ok; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks].
split; [exact H0|]. split; [exact H1|]. split; [exact Hw|].
constructor; [|exact Hcs].
intros i Hi. apply (cover_lit_sound E m _ (r_chunks r) (c_val c) (c_off c) (Z.to_nat (c_len c)) 0 Hcs Hcov).
unfold c_len in Hi |- *. lia.
Qed.
Lemma add_lit_chunk_facts : forall E m rs b c rs',
add_lit_chunk rs b c = Some rs' ->
regions_wf rs = true -> Forall (region_ok segs E m) rs ->
regions_wf rs' = true /\ Forall (region_ok segs E m) rs' /\ map extent_of rs' = map extent_of rs
/\ map (fun r => (r_wlo r, r_whi r)) rs' = map (fun r => (r_wlo r, r_whi r)) rs.
Proof.
intros E m rs b c. induction rs as [|r rs IH]; intros rs' H Hwf Hok; cbn in H; [discriminate|].
cbn in Hwf. apply andb_prop in Hwf as [Hwfr Hwf]. inversion Hok as [|r0 rs0 Hokr Hokrs]; subst.
destruct (obase_eqb (r_base r) b && (r_lo r <=? c_off c) && (c_off c <? r_hi r)).
- destruct (add_lit_region r c) as [r'|] eqn:Hr; [|discriminate]. injection H as <-.
destruct (add_lit_region_facts E m r c r' Hr Hwfr Hokr) as (W & O & X & WL & WH).
cbn. rewrite W, Hwf, X, WL, WH. repeat split; try reflexivity. constructor; assumption.
- destruct (add_lit_chunk rs b c) as [rs''|] eqn:Hrs; [|discriminate]. injection H as <-.
destruct (IH rs'' eq_refl Hwf Hokrs) as (W & O & X & WW).
cbn. rewrite Hwfr, W, X, WW. repeat split; try reflexivity. constructor; assumption.
Qed.
Lemma mem_ok_add_lit_chunk : forall E m rs b c rs',
mem_ok segs E m rs -> add_lit_chunk rs b c = Some rs' -> mem_ok segs E m rs'.
Proof.
intros E m rs b c rs' (Hwf & Hok & Hpd) H.
destruct (add_lit_chunk_facts E m rs b c rs' H Hwf Hok) as (W & O & X & _).
split; [exact W|]. split; [exact O|].
eapply pairwise_disjoint_extents; [symmetry; exact X| exact Hpd].
Qed.
Lemma st_ok_add_lit_chunk : forall E ss ms b c rs',
st_ok segs E ss ms -> add_lit_chunk (ss_mem ss) b c = Some rs' ->
st_ok segs E (mkSS (ss_pc ss) (ss_regs ss) rs' (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms b c rs' (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) H.
unfold st_ok; cbn. repeat (split; [assumption|]). split; [|exact H9].
eapply mem_ok_add_lit_chunk; eauto.
Qed.
Lemma add_lit_chunk_skeleton : forall rs b c rs',
add_lit_chunk rs b c = Some rs' -> skeleton rs' = skeleton rs.
Proof.
intros rs b c. induction rs as [|r rs IH]; intros rs' H; cbn in H; [discriminate|].
destruct (obase_eqb (r_base r) b && (r_lo r <=? c_off c) && (c_off c <? r_hi r)).
- destruct (add_lit_region r c) as [r'|] eqn:Hr; [|discriminate]. injection H as <-.
unfold add_lit_region in Hr.
destruct (chunk_inside r c && cover_lit (r_chunks r) (c_val c) (c_off c) 0 (Z.to_nat (c_len c)));
[|discriminate]. injection Hr as <-. reflexivity.
- destruct (add_lit_chunk rs b c) as [rs''|] eqn:Hrs; [|discriminate]. injection H as <-.
cbn. unfold skeleton in IH. rewrite (IH rs'' eq_refl). reflexivity.
Qed.
Definition keep_chunks (f : chunk -> bool) (r : region) : region :=
mkRegion (r_base r) (r_lo r) (r_hi r) (r_wlo r) (r_whi r) (List.filter f (r_chunks r)).
Definition clean_head (f : chunk -> bool) (rs : smem) : smem :=
match rs with [] => [] | r :: rs' => keep_chunks f r :: rs' end.
Lemma subregion_refl : forall r, subregion r r.
Proof. intros r. unfold subregion. repeat split; try lia. auto. Qed.
Lemma submem_refl : forall rs, submem rs rs.
Proof. induction rs; [constructor| apply submem_keep; [apply subregion_refl| assumption]]. Qed.
Lemma subregion_keep_chunks : forall f r, subregion (keep_chunks f r) r.
Proof.
intros f r. unfold subregion, keep_chunks; cbn. repeat split; try lia.
intros c Hc. apply List.filter_In in Hc. tauto.
Qed.
Lemma submem_clean_head : forall f rs, submem (clean_head f rs) rs.
Proof.
intros f [|r rs]; cbn; [constructor|].
apply submem_keep; [apply subregion_keep_chunks| apply submem_refl].
Qed.
Lemma regions_wf_clean_head : forall f rs, regions_wf rs = true -> regions_wf (clean_head f rs) = true.
Proof.
intros f [|r rs]; cbn; [reflexivity|]. intros H. apply andb_prop in H as [Hr Hrs].
rewrite Hrs, andb_true_r. unfold region_wf, keep_chunks in Hr |- *; cbn.
apply andb_prop in Hr as [H1 H2]. rewrite H1. cbn.
apply forallb_forall. intros c Hc. apply List.filter_In in Hc as [Hc _].
unfold chunk_inside in *; cbn. exact (proj1 (forallb_forall _ _) H2 c Hc).
Qed.
Lemma st_ok_clean_head : forall E ss ms f,
st_ok segs E ss ms ->
st_ok segs E (mkSS (ss_pc ss) (ss_regs ss) (clean_head f (ss_mem ss)) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms f HS. apply (st_ok_submem segs E ss ms); [exact HS| apply submem_clean_head|].
apply regions_wf_clean_head. destruct HS as (_ & _ & _ & _ & _ & _ & _ & HM & _). exact (proj1 HM).
Qed.
Definition clean_all (f : chunk -> bool) (rs : smem) : smem := map (keep_chunks f) rs.
Lemma region_wf_keep_chunks : forall f r, region_wf r = true -> region_wf (keep_chunks f r) = true.
Proof.
intros f r Hr. unfold region_wf, keep_chunks in Hr |- *; cbn.
apply andb_prop in Hr as [H1 H2]. rewrite H1. cbn.
apply forallb_forall. intros c Hc. apply List.filter_In in Hc as [Hc _].
unfold chunk_inside in *; cbn. exact (proj1 (forallb_forall _ _) H2 c Hc).
Qed.
Lemma submem_clean_all : forall f rs, submem (clean_all f rs) rs.
Proof.
intros f rs. unfold clean_all. induction rs as [|r rs IH]; cbn [map]; [constructor|].
apply submem_keep; [apply subregion_keep_chunks| exact IH].
Qed.
Lemma regions_wf_clean_all : forall f rs, regions_wf rs = true -> regions_wf (clean_all f rs) = true.
Proof.
intros f rs. unfold clean_all. induction rs as [|r rs IH]; cbn [map regions_wf]; [reflexivity|].
intros H. apply andb_prop in H as [Hr Hrs].
rewrite (region_wf_keep_chunks f r Hr), (IH Hrs). reflexivity.
Qed.
Lemma st_ok_clean_all : forall E ss ms f,
st_ok segs E ss ms ->
st_ok segs E (mkSS (ss_pc ss) (ss_regs ss) (clean_all f (ss_mem ss)) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms f HS. apply (st_ok_submem segs E ss ms); [exact HS| apply submem_clean_all|].
apply regions_wf_clean_all. destruct HS as (_ & _ & _ & _ & _ & _ & _ & HM & _). exact (proj1 HM).
Qed.
Definition not_cdata (d : nat) (c : chunk) : bool :=
match c_val c with CData d' _ _ => negb (Nat.eqb d' d) | _ => true end.
End e.
Ltac sym_run_to_with tblok HS stop :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss ?ms =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let r := eval vm_compute in (sym_run_toN segs tbl FUEL stop ss) in
lazymatch r with
| (?ss', ?st) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_run_toN segs tbl FUEL stop ss = (ss', st)) by (vm_compute; reflexivity);
let ms' := fresh "ms" in let HF := fresh "HF" in
lazymatch st with
| RS_ecall =>
eapply (rz_run_to_ecall segs tbl tblok FUEL stop E ss ss' ms);
[ | | exact HS | exact Hrun | clear Hrun HS; intros ms' HS HF ]; [assumption|assumption|];
sym_transport_ecall segs E ss ss' ms' HS HF
| RS_stopped ?why =>
eapply (rz_run_to_stop segs tbl tblok FUEL stop E ss ss' why ms);
[ | | exact HS | exact Hrun | clear Hrun HS; intros ms' HS HF ]; [assumption|assumption|];
sym_transport segs E ss ss' ms' HS HF
| RS_running =>
eapply (rz_run_to_running segs tbl tblok FUEL stop E ss ss' ms);
[ | | exact HS | exact Hrun | clear Hrun HS; intros ms' HS HF ]; [assumption|assumption|];
sym_transport segs E ss ss' ms' HS HF
end
end
end
end.
Ltac sym_add_chunk HS b c :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss ?ms =>
let r := eval vm_compute in (add_lit_chunk (ss_mem ss) b c) in
lazymatch r with
| Some ?rs' =>
let H := fresh in
assert (H : add_lit_chunk (ss_mem ss) b c = Some rs') by (vm_compute; reflexivity);
apply (st_ok_add_lit_chunk segs E ss ms b c rs' HS) in H;
clear HS; rename H into HS; sym_norm HS
| None => fail "sym_add_chunk: coverage check failed"
end
end.
