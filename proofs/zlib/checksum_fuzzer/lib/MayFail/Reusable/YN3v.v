(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN3v.v, with its module paths changed. *)
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
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section h.
Variable segs : list Segment.
Variable tbl : ctable.
Hypothesis tbl_ok : table_ok segs tbl.
Definition below (b : Z) (c : chunk) : bool := c_off c + c_len c <=? b.
Definition abover (b : Z) (c : chunk) : bool := b <=? c_off c.
Definition split3 (r : region) (a b : Z) : list region :=
[ mkRegion (r_base r) (r_lo r) a (r_lo r) a (List.filter (below a) (r_chunks r));
mkRegion (r_base r) a b 0 0 [];
mkRegion (r_base r) b (r_hi r) b (r_hi r) (List.filter (abover b) (r_chunks r)) ].
Definition split3_head (rs : smem) (a b : Z) : smem :=
match rs with r :: rs' => split3 r a b ++ rs' | [] => [] end.
Definition win_ok (E : env) (m : word -> option byte) (lo hi : sv) : Prop :=
forall x, bv_unsigned (sv_denot E lo) <= x < bv_unsigned (sv_denot E hi) -> writable_at segs m x.
Lemma all_disjoint_inside : forall E r r' rs,
r_base r' = r_base r -> r_lo r <= r_lo r' -> r_hi r' <= r_hi r -> r_lo r' <= r_hi r' ->
all_disjoint E r rs -> all_disjoint E r' rs.
Proof.
intros E r r' rs Hb Hlo Hhi Hle. induction rs as [|x rs IH]; cbn; intros H; [exact I|].
destruct H as [Hd Ha]. split; [|apply IH; exact Ha].
unfold extent_disjoint in *. rewrite Hb. lia.
Qed.
Lemma mem_ok_split3_head : forall E m r rs a b,
mem_ok segs E m (r :: rs) ->
r_lo r <= a -> a <= b -> b <= r_hi r -> r_wlo r = r_lo r -> r_whi r = r_hi r ->
mem_ok segs E m (split3 r a b ++ rs)
/\ (forall x, base_val E (r_base r) + a <= x < base_val E (r_base r) + b -> writable_at segs m x).
Proof.
intros E m r rs a b (Hwf & Hok & Hpd) Ha Hab Hb Hwlo Hwhi.
cbn in Hwf. apply andb_prop in Hwf as [Hrwf Hwf].
apply region_wf_facts in Hrwf as (Hlohi & _ & Hcin).
inversion Hok as [|r0 rs0 Hr Hrs]; subst.
destruct Hr as (H0 & H1 & Hw & Hcs).
cbn in Hpd. destruct Hpd as [Hall Hpd].
split.
- split; [|split].
+
assert (W1 : region_wf (mkRegion (r_base r) (r_lo r) a (r_lo r) a (List.filter (below a) (r_chunks r))) = true).
{ unfold region_wf; cbn [r_lo r_hi r_wlo r_whi r_chunks].
apply andb_true_intro; split; [apply andb_true_intro; split|].
- apply Z.leb_le; lia.
- apply orb_true_intro. right. apply andb_true_intro. split; apply Z.leb_le; lia.
- apply forallb_forall. intros c Hc. apply filter_In in Hc as [Hc Hbl].
pose proof (proj1 (forallb_forall _ _) Hcin c Hc) as Hci. apply chunk_inside_facts in Hci.
unfold below in Hbl. apply Z.leb_le in Hbl.
unfold chunk_inside; cbn [r_lo r_hi]. rewrite !andb_true_iff, !Z.leb_le. lia. }
assert (W2 : region_wf (mkRegion (r_base r) a b 0 0 []) = true).
{ unfold region_wf; cbn [r_lo r_hi r_wlo r_whi r_chunks forallb].
rewrite andb_true_r. apply andb_true_intro; split; [apply Z.leb_le; lia|].
apply orb_true_intro. left. apply Z.leb_le. lia. }
assert (W3 : region_wf (mkRegion (r_base r) b (r_hi r) b (r_hi r) (List.filter (abover b) (r_chunks r))) = true).
{ unfold region_wf; cbn [r_lo r_hi r_wlo r_whi r_chunks].
apply andb_true_intro; split; [apply andb_true_intro; split|].
- apply Z.leb_le; lia.
- apply orb_true_intro. right. apply andb_true_intro. split; apply Z.leb_le; lia.
- apply forallb_forall. intros c Hc. apply filter_In in Hc as [Hc Hab'].
pose proof (proj1 (forallb_forall _ _) Hcin c Hc) as Hci. apply chunk_inside_facts in Hci.
unfold abover in Hab'. apply Z.leb_le in Hab'.
unfold chunk_inside; cbn [r_lo r_hi]. rewrite !andb_true_iff, !Z.leb_le. lia. }
cbn [split3 app regions_wf]. rewrite W1, W2, W3, Hwf. reflexivity.
+
cbn [split3 app]. constructor; [|constructor; [|constructor; [|exact Hrs]]].
* unfold region_ok; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks].
split; [lia|]. split; [lia|]. split.
-- intros o Ho. apply Hw. lia.
-- rewrite Forall_forall in Hcs |- *. intros c Hc. apply filter_In in Hc as [Hc _]. auto.
* unfold region_ok; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks].
split; [lia|]. split; [lia|]. split; [intros o Ho; lia| constructor].
* unfold region_ok; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks].
split; [lia|]. split; [lia|]. split.
-- intros o Ho. apply Hw. lia.
-- rewrite Forall_forall in Hcs |- *. intros c Hc. apply filter_In in Hc as [Hc _]. auto.
+
cbn [split3 app pairwise_disjoint all_disjoint]. split; [|split; [|split; [|exact Hpd]]].
* split; [unfold extent_disjoint; cbn; lia|]. split; [unfold extent_disjoint; cbn; lia|].
eapply (all_disjoint_inside E r); cbn; try reflexivity; try lia. exact Hall.
* split; [unfold extent_disjoint; cbn; lia|].
eapply (all_disjoint_inside E r); cbn; try reflexivity; try lia. exact Hall.
* eapply (all_disjoint_inside E r); cbn; try reflexivity; try lia. exact Hall.
- intros x Hx. replace x with (base_val E (r_base r) + (x - base_val E (r_base r))) by lia.
apply Hw. lia.
Qed.
Lemma st_ok_split3_head : forall E ss ms r rs a b lo hi,
st_ok segs E ss ms -> ss_mem ss = r :: rs ->
r_lo r <= a -> a <= b -> b <= r_hi r -> r_wlo r = r_lo r -> r_whi r = r_hi r ->
bv_unsigned (sv_denot E lo) = base_val E (r_base r) + a ->
bv_unsigned (sv_denot E hi) = base_val E (r_base r) + b ->
st_ok segs E (mkSS (ss_pc ss) (ss_regs ss) (split3 r a b ++ rs) (ss_resv ss) (ss_facts ss)) ms
/\ win_ok E (ms_mem ms) lo hi.
Proof.
intros E ss ms r rs a b lo hi (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9) Hm Ha Hab Hb Hwlo Hwhi Hlo Hhi.
rewrite Hm in S8.
destruct (mem_ok_split3_head E (ms_mem ms) r rs a b S8 Ha Hab Hb Hwlo Hwhi) as [HM HW].
split.
- unfold st_ok; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts]. repeat (split; [assumption|]). exact S9.
- intros x Hx. apply HW. lia.
Qed.
Lemma mem_ok_wbytes_inside : forall E m l1 r l2 a bs,
mem_ok segs E m (l1 ++ r :: l2) -> r_chunks r = [] ->
base_val E (r_base r) + r_lo r <= a ->
a + Z.of_nat (length bs) <= base_val E (r_base r) + r_hi r ->
mem_ok segs E (wbytes m (Z_to_bv 64 a) bs) (l1 ++ r :: l2).
Proof.
intros E m l1 r l2 a bs (Hwf & Hok & Hpd) Hnil Hlo Hhi.
split; [exact Hwf|]. split; [|exact Hpd].
assert (Hrin : In r (l1 ++ r :: l2)) by (apply in_app_iff; right; left; reflexivity).
pose proof (proj1 (Forall_forall _ _) Hok r Hrin) as (Hb0 & Hb1 & _ & _).
pose proof (pairwise_disjoint_split E l1 r l2 Hpd) as Hdis.
assert (Hgrow : mem_grows m (wbytes m (Z_to_bv 64 a) bs)) by apply wbytes_grows.
rewrite Forall_forall in Hok |- *. intros r' Hin'.
specialize (Hok r' Hin'). destruct Hok as (Hc0 & Hc1 & Hw' & Hcs').
split; [exact Hc0|]. split; [exact Hc1|]. split.
- intros o Ho. eapply writable_at_grows; [exact Hgrow|]. apply Hw'. exact Ho.
- destruct (Nat.eq_dec (length bs) 0) as [Hz|Hz].
{ destruct bs; [cbn [wbytes]; exact Hcs'| cbn in Hz; lia]. }
apply in_app_iff in Hin'. destruct Hin' as [Hin'|[<-|Hin']].
2:{ rewrite Hnil. constructor. }
all: assert (Hd : extent_disjoint E r r')
by (apply (proj1 (Forall_forall _ _) Hdis r'); apply in_app_iff; auto).
all: assert (Hwf' : region_wf r' = true)
by (apply (regions_wf_In (l1 ++ r :: l2)); [exact Hwf| apply in_app_iff; cbn; auto]).
all: apply region_wf_facts in Hwf' as (Hlohi' & _ & Hcin').
all: rewrite Forall_forall in Hcs' |- *; intros c Hc;
pose proof (proj1 (forallb_forall _ _) Hcin' c Hc) as Hci; apply chunk_inside_facts in Hci;
apply chunk_ok_wbytes_out; try lia; [|apply Hcs'; exact Hc];
unfold extent_disjoint in Hd; lia.
Qed.
Lemma st_ok_mem_wbytes_inside : forall E ss regs pc m l1 r l2 a bs,
st_ok segs E ss (mkst regs pc m (seg_rom segs)) -> ss_mem ss = l1 ++ r :: l2 -> r_chunks r = [] ->
base_val E (r_base r) + r_lo r <= a ->
a + Z.of_nat (length bs) <= base_val E (r_base r) + r_hi r ->
mem_ok segs E (wbytes m (Z_to_bv 64 a) bs) (ss_mem ss).
Proof.
intros E ss regs pc m l1 r l2 a bs HS Hm Hnil Hlo Hhi.
pose proof (st_ok_mem_ok segs E ss _ HS) as HM. cbn [ms_mem mkst] in HM.
rewrite Hm in HM |- *. eapply mem_ok_wbytes_inside; eauto.
Qed.
Definition sep_check2 (G : facts) (lo hi : sv) (r : region) : bool :=
sep_check G lo hi r ||
match lo, hi, r_base r with
| SOff b x, SOff b' y, Some rb =>
Nat.eqb b b' && Nat.eqb b rb &&
match atom_lookup (f_atoms G) b with
| Some f => (0 <=? af_lo f + x) && (x <=? y) && (af_hi f + y <? M64) && (af_hi f + r_whi r <? M64)
&& (0 <=? af_lo f + r_wlo r)
&& ((y <=? r_wlo r) || (r_whi r <=? x))
| None => false
end
| _, _, _ => false
end.
Definition kept_check2 (G : facts) (rs : smem) (lo hi : sv) : bool :=
forallb (sep_check2 G lo hi) rs.
Lemma sep_check2_sound : forall E G lo hi r a bs x,
facts_ok E G -> region_wf r = true ->
run_loc E lo hi a bs ->
sep_check2 G lo hi r = true ->
a <= x < a + Z.of_nat (length bs) ->
~ (base_val E (r_base r) + r_wlo r <= x < base_val E (r_base r) + r_whi r).
Proof.
intros E G lo hi r a bs x HG Hwf Hloc H Hx.
unfold sep_check2 in H. apply orb_prop in H as [H|H].
{ eapply sep_check_sound; eauto. }
destruct Hloc as [Hlo Hhi]. intros Hin.
destruct lo as [|b xo| | | | | | | | |]; try discriminate.
destruct hi as [|b' yo| | | | | | | | |]; try discriminate.
destruct (r_base r) as [rb|] eqn:Hrb; try discriminate. cbn [base_val] in Hin.
apply andb_prop in H as [H Hm]. apply andb_prop in H as [B1 B2].
apply Nat.eqb_eq in B1. apply Nat.eqb_eq in B2. subst b' rb.
destruct (atom_lookup (f_atoms G) b) as [f|] eqn:Hf; [|discriminate].
apply andb_prop in Hm as [Hm C6]. apply andb_prop in Hm as [Hm C5]. apply andb_prop in Hm as [Hm C4].
apply andb_prop in Hm as [Hm C3]. apply andb_prop in Hm as [C1 C2].
apply Z.leb_le in C1. apply Z.leb_le in C2. apply Z.ltb_lt in C3. apply Z.ltb_lt in C4. apply Z.leb_le in C5.
pose proof (atom_lookup_ok E _ _ _ (proj1 HG) Hf) as (Hb & _).
pose proof (u64_range (ew E b)) as Hbr.
rewrite denot_SOff in Hlo, Hhi. unfold M64 in *.
rewrite zcanon_id in Hlo by (unfold M64 in *; lia). rewrite zcanon_id in Hhi by (unfold M64 in *; lia).
apply orb_prop in C6 as [C6|C6]; apply Z.leb_le in C6; lia.
Qed.
Lemma kept_check2_sound : forall E G rs lo hi a bs x,
facts_ok E G -> regions_wf rs = true ->
run_loc E lo hi a bs -> kept_check2 G rs lo hi = true ->
a <= x < a + Z.of_nat (length bs) -> ~ in_wrange E rs x.
Proof.
intros E G rs lo hi a bs x HG Hwf Hloc H Hx (r & Hin & Hr).
unfold kept_check2 in H. pose proof (proj1 (forallb_forall _ _) H r Hin) as Hs.
eapply (sep_check2_sound E G lo hi r a bs x HG); eauto.
eapply regions_wf_In; eauto.
Qed.
Definition runs_kept_check2 (G : facts) (rs : smem) (l : list (sv * sv)) : bool :=
forallb (fun p => kept_check2 G rs (fst p) (snd p)) l.
Lemma runs_ok_frame2 : forall E G rs m m' l,
facts_ok E G -> regions_wf rs = true ->
frame_of E rs m m' ->
runs_kept_check2 G rs (map (fun e => match e with (lo, hi, _, _) => (lo, hi) end) l) = true ->
runs_ok E m l -> runs_ok E m' l.
Proof.
intros E G rs m m' l HG Hwf Hfr Hk H. unfold runs_ok, runs_kept_check2 in *.
rewrite Forall_forall in *. intros [[[lo hi] a] bs] Hin. specialize (H _ Hin). cbn in H.
destruct H as (Hlo & Hhi & Hb). split; [exact Hlo|]. split; [exact Hhi|].
assert (Hkc : kept_check2 G rs lo hi = true).
{ apply (proj1 (forallb_forall _ _) Hk (lo, hi)). apply in_map_iff. exists (lo, hi, a, bs). auto. }
pose proof (u64_range (sv_denot E lo)). pose proof (u64_range (sv_denot E hi)).
apply (bytes_at_frame m m' a bs); [| lia | lia | exact Hb].
intros x Hx. apply Hfr. eapply kept_check2_sound; eauto. split; assumption.
Qed.
Lemma runs_ok_after2 : forall E ss ss' ms' m l,
st_ok segs E ss' ms' ->
regions_wf (ss_mem ss) = true ->
runs_kept_check2 (ss_facts ss') (ss_mem ss) (map (fun e => match e with (lo, hi, _, _) => (lo, hi) end) l) = true ->
frame_of E (ss_mem ss) m (ms_mem ms') ->
runs_ok E m l -> runs_ok E (ms_mem ms') l.
Proof.
intros E ss ss' ms' m l HS Hwf Hk Hfr H.
eapply runs_ok_frame2; [apply (st_ok_facts_ok segs E ss' ms' HS) | exact Hwf | exact Hfr | exact Hk | exact H].
Qed.
Lemma runs_ok_after2_ecall : forall E ss ss' ms' m l,
st_ok_ecall segs E ss' ms' ->
regions_wf (ss_mem ss) = true ->
runs_kept_check2 (ss_facts ss') (ss_mem ss) (map (fun e => match e with (lo, hi, _, _) => (lo, hi) end) l) = true ->
frame_of E (ss_mem ss) m (ms_mem ms') ->
runs_ok E m l -> runs_ok E (ms_mem ms') l.
Proof.
intros E ss ss' ms' m l HS Hwf Hk Hfr H.
destruct HS as (_ & _ & _ & _ & _ & _ & _ & _ & HG).
eapply runs_ok_frame2; [exact HG | exact Hwf | exact Hfr | exact Hk | exact H].
Qed.
Lemma writable_at_eq : forall m m' x,
m' (Z_to_bv 64 x) = m (Z_to_bv 64 x) -> writable_at segs m x -> writable_at segs m' x.
Proof. intros m m' x Heq Hw. unfold writable_at, wview in *. rewrite Heq. exact Hw. Qed.
Lemma win_ok_frame : forall E G rs m m' lo hi,
facts_ok E G -> regions_wf rs = true -> frame_of E rs m m' ->
kept_check2 G rs lo hi = true ->
win_ok E m lo hi -> win_ok E m' lo hi.
Proof.
intros E G rs m m' lo hi HG Hwf Hfr Hk H x Hx.
pose proof (u64_range (sv_denot E lo)). pose proof (u64_range (sv_denot E hi)).
eapply writable_at_eq; [|apply H; exact Hx].
apply Hfr. rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2^64); lia).
set (n := Z.to_nat (bv_unsigned (sv_denot E hi) - bv_unsigned (sv_denot E lo))).
apply (kept_check2_sound E G rs lo hi (bv_unsigned (sv_denot E lo)) (repeat (Z_to_bv 8 0) n) x HG Hwf);
[| exact Hk | rewrite repeat_length; lia].
split; [lia|]. rewrite repeat_length. lia.
Qed.
Lemma win_ok_after : forall E ss ss' ms' m lo hi,
st_ok segs E ss' ms' -> regions_wf (ss_mem ss) = true ->
kept_check2 (ss_facts ss') (ss_mem ss) lo hi = true ->
frame_of E (ss_mem ss) m (ms_mem ms') ->
win_ok E m lo hi -> win_ok E (ms_mem ms') lo hi.
Proof.
intros E ss ss' ms' m lo hi HS Hwf Hk Hfr H.
eapply win_ok_frame; [apply (st_ok_facts_ok segs E ss' ms' HS) | exact Hwf | exact Hfr | exact Hk | exact H].
Qed.
Lemma win_ok_after_ecall : forall E ss ss' ms' m lo hi,
st_ok_ecall segs E ss' ms' -> regions_wf (ss_mem ss) = true ->
kept_check2 (ss_facts ss') (ss_mem ss) lo hi = true ->
frame_of E (ss_mem ss) m (ms_mem ms') ->
win_ok E m lo hi -> win_ok E (ms_mem ms') lo hi.
Proof.
intros E ss ss' ms' m lo hi HS Hwf Hk Hfr H.
destruct HS as (_ & _ & _ & _ & _ & _ & _ & _ & HG).
eapply win_ok_frame; [exact HG | exact Hwf | exact Hfr | exact Hk | exact H].
Qed.
Lemma win_ok_wbytes : forall E m lo hi a bs,
win_ok E m lo hi -> win_ok E (wbytes m a bs) lo hi.
Proof. intros E m lo hi a bs H x Hx. eapply writable_at_grows; [apply wbytes_grows| apply H; exact Hx]. Qed.
Lemma win_ok_agree : forall k E E' m lo hi,
env_agree k E E' -> sv_atoms_lt k lo = true -> sv_atoms_lt k hi = true ->
win_ok E m lo hi -> win_ok E' m lo hi.
Proof.
intros k E E' m lo hi HA Hlo Hhi H x Hx.
rewrite (sv_denot_agree k E E' lo HA Hlo), (sv_denot_agree k E E' hi HA Hhi) in Hx.
apply H. exact Hx.
Qed.
Lemma win_ok_eqmem : forall E m m' lo hi, m' = m -> win_ok E m lo hi -> win_ok E m' lo hi.
Proof. intros; subst; assumption. Qed.
Lemma store_ok_of_win : forall E m lo hi (d : word) n,
win_ok E m lo hi ->
bv_unsigned (sv_denot E lo) <= bv_unsigned d ->
bv_unsigned d + Z.of_nat n <= bv_unsigned (sv_denot E hi) ->
store_ok segs m d n = true.
Proof.
intros E m lo hi d n H Hlo Hhi. pose proof (u64_range (sv_denot E hi)).
apply store_ok_of_all; [lia|].
intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply H. lia.
Qed.
Lemma bytes_at_wbytes_same : forall m a bs,
0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
bytes_at (wbytes m (Z_to_bv 64 a) bs) a bs.
Proof.
intros m a bs. revert m a. induction bs as [|b bs IH]; intros m a Ha Hnw j Hj; cbn [length] in *; [lia|].
cbn [wbytes]. rewrite Z_to_bv64_add1.
destruct j as [|j].
- cbn [nth_error]. rewrite Z.add_0_r.
destruct bs as [|b' bs'].
+ cbn [wbytes]. rewrite bv_eqb_refl. reflexivity.
+ cbn [length] in *. rewrite wbytes_below.
* rewrite bv_eqb_refl. reflexivity.
* cbn [length]. rewrite !Z_to_bv_unsigned, !bv_wrap_small by (change (bv_modulus 64) with (2^64); lia). lia.
* rewrite !Z_to_bv_unsigned, !bv_wrap_small by (change (bv_modulus 64) with (2^64); lia). lia.
- cbn [nth_error]. replace (a + Z.of_nat (S j)) with (a + 1 + Z.of_nat j) by lia.
apply (IH _ (a + 1)); lia.
Qed.
Lemma bytes_at_wbytes_out : forall m a bs a' bs',
0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
0 <= a' -> a' + Z.of_nat (length bs') <= 2^64 ->
(a' + Z.of_nat (length bs') <= a \/ a + Z.of_nat (length bs) <= a') ->
bytes_at m a' bs' -> bytes_at (wbytes m (Z_to_bv 64 a) bs) a' bs'.
Proof.
intros m a bs a' bs' Ha Hnw Ha' Hnw' Hd H j Hj.
destruct bs as [|b0 bs0]; [cbn [wbytes]; apply H; exact Hj|].
assert (Hlt : a < 2^64) by (cbn [length] in Hnw; lia).
destruct Hd as [Hd|Hd].
- rewrite wbytes_below; [apply H; exact Hj| |];
rewrite !Z_to_bv_unsigned, !bv_wrap_small by (change (bv_modulus 64) with (2^64); lia); lia.
- rewrite wbytes_above; [apply H; exact Hj|].
rewrite !Z_to_bv_unsigned, !bv_wrap_small by (change (bv_modulus 64) with (2^64); lia). lia.
Qed.
Lemma bytes_at_app : forall m a l1 l2,
bytes_at m a l1 -> bytes_at m (a + Z.of_nat (length l1)) l2 -> bytes_at m a (l1 ++ l2).
Proof.
intros m a l1 l2 H1 H2 j Hj. rewrite length_app in Hj.
destruct (Nat.lt_ge_cases j (length l1)) as [Hl|Hg].
- rewrite nth_error_app1 by exact Hl. apply H1. exact Hl.
- rewrite nth_error_app2 by exact Hg.
replace (a + Z.of_nat j) with (a + Z.of_nat (length l1) + Z.of_nat (j - length l1)) by lia.
apply H2. lia.
Qed.
Lemma bytes_at_nil : forall m a, bytes_at m a [].
Proof. intros m a j Hj. cbn in Hj. lia. Qed.
Lemma bytes_at_firstn : forall m a l n, bytes_at m a l -> bytes_at m a (firstn n l).
Proof. intros m a l n H. rewrite <- (firstn_skipn n l) in H. exact (bytes_at_app_l _ _ _ _ H). Qed.
Lemma runs_ok_single : forall E m lo hi a bs,
bv_unsigned (sv_denot E lo) <= a -> a + Z.of_nat (length bs) <= bv_unsigned (sv_denot E hi) ->
bytes_at m a bs -> runs_ok E m [(lo, hi, a, bs)].
Proof. intros. constructor; [|constructor]. cbv beta iota. repeat split; assumption. Qed.
Lemma runs_ok_single_inv : forall E m lo hi a bs,
runs_ok E m [(lo, hi, a, bs)] ->
bv_unsigned (sv_denot E lo) <= a /\ a + Z.of_nat (length bs) <= bv_unsigned (sv_denot E hi) /\ bytes_at m a bs.
Proof. intros E m lo hi a bs H. inversion H as [|x l Hx _]; subst. exact Hx. Qed.
Lemma runs_ok_eqmem : forall E m m' l, m' = m -> runs_ok E m l -> runs_ok E m' l.
Proof. intros; subst; assumption. Qed.
Definition mbytes_at (m : word -> option byte) (a : Z) (bs : list byte) : Prop :=
forall j, (j < length bs)%nat -> mbyte segs m (a + Z.of_nat j) = nth_error bs j.
Lemma mbytes_at_rdn : forall m a bs, mbytes_at m a bs -> rdn segs m (Z_to_bv 64 a) (length bs) = Some bs.
Proof. intros m a bs H. apply (proj2 (rdn_mbytes segs m (length bs) a bs)). split; [reflexivity| exact H]. Qed.
Lemma bytes_at_mbytes : forall m a bs, bytes_at m a bs -> mbytes_at m a bs.
Proof. intros m a bs H j Hj. apply (bytes_at_mbyte segs). exact H. exact Hj. Qed.
Lemma mbytes_at_app : forall m a l1 l2,
mbytes_at m a l1 -> mbytes_at m (a + Z.of_nat (length l1)) l2 -> mbytes_at m a (l1 ++ l2).
Proof.
intros m a l1 l2 H1 H2 j Hj. rewrite length_app in Hj.
destruct (Nat.lt_ge_cases j (length l1)) as [Hl|Hg].
- rewrite nth_error_app1 by exact Hl. apply H1. exact Hl.
- rewrite nth_error_app2 by exact Hg.
replace (a + Z.of_nat j) with (a + Z.of_nat (length l1) + Z.of_nat (j - length l1)) by lia.
apply H2. lia.
Qed.
Lemma mbytes_at_nil : forall m a, mbytes_at m a [].
Proof. intros m a j Hj. cbn in Hj. lia. Qed.
Fixpoint read_lits (cs : list chunk) (off : Z) (n : nat) : option (list Z) :=
match n with
| O => Some []
| S n' => match find_lit cs off, read_lits cs (off + 1) n' with
| Some z, Some zs => Some (z :: zs)
| _, _ => None
end
end.
Lemma read_lits_length : forall cs n off zs, read_lits cs off n = Some zs -> length zs = n.
Proof.
intros cs n. induction n as [|n IH]; intros off zs H; cbn in H.
- injection H as <-. reflexivity.
- destruct (find_lit cs off) as [z|]; [|discriminate].
destruct (read_lits cs (off + 1) n) as [zs'|] eqn:Hr; [|discriminate].
injection H as <-. cbn. f_equal. eapply IH. exact Hr.
Qed.
Lemma read_lits_sound : forall E m base cs n off zs,
Forall (chunk_ok segs E m base) cs -> read_lits cs off n = Some zs ->
mbytes_at m (base + off) (map (Z_to_bv 8) zs).
Proof.
intros E m base cs n. induction n as [|n IH]; intros off zs Hcs H; cbn in H.
- injection H as <-. apply mbytes_at_nil.
- destruct (find_lit cs off) as [z|] eqn:Hz; [|discriminate].
destruct (read_lits cs (off + 1) n) as [zs'|] eqn:Hr; [|discriminate].
injection H as <-. cbn [map].
change (Z_to_bv 8 z :: ?l) with ([Z_to_bv 8 z] ++ l). apply mbytes_at_app.
+ intros j Hj. cbn in Hj. destruct j; [|lia]. cbn [nth_error]. rewrite Z.add_0_r.
exact (find_lit_sound segs E m base cs off z Hcs Hz).
+ cbn [length]. replace (base + off + Z.of_nat 1) with (base + (off + 1)) by lia.
apply IH; [exact Hcs | exact Hr].
Qed.
Lemma read_lits_region : forall E m rs i r off n zs,
mem_ok segs E m rs -> nth_error rs i = Some r ->
read_lits (r_chunks r) off n = Some zs ->
mbytes_at m (base_val E (r_base r) + off) (map (Z_to_bv 8) zs).
Proof.
intros E m rs i r off n zs HM Hn H.
pose proof (mem_ok_region segs E m rs r HM (nth_error_In _ _ Hn)) as (_ & _ & _ & Hcs).
eapply read_lits_sound; eauto.
Qed.
Lemma chunk_bytes_word : forall E abs v,
chunk_bytes segs E abs (CVal 8 v) 0 8 = word_le8 (sv_denot E v).
Proof. intros. cbn [chunk_bytes]. rewrite word_le8_st_bytes. reflexivity. Qed.
Lemma le_bytes_word_le8 : forall w : word, le_bytes_to_word (word_le8 w) = w.
Proof. intros w. rewrite le_bytes_to_word_Z, bytes_le_n_to_le_8. apply Z_to_bv_bv_unsigned. Qed.
Lemma rdn_chunk_word : forall E m rs b off r v,
mem_ok segs E m rs ->
find_region rs b off 8 = Some r ->
find_chunk (r_chunks r) off 8 = Some (mkChunk off (CVal 8 v)) ->
rdn segs m (Z_to_bv 64 (base_val E b + off)) 8 = Some (word_le8 (sv_denot E v)).
Proof.
intros E m rs b off r v HM Hr Hc.
rewrite (mem_ok_read segs E m rs b off 8 r (mkChunk off (CVal 8 v)) HM Hr Hc I).
cbn [c_off c_val]. rewrite Z.sub_diag, chunk_bytes_word. reflexivity.
Qed.
Lemma ms_read_u64_of_rdn : forall regs pc mem a w,
rdn segs mem a 8 = Some (word_le8 w) ->
ms_read_u64 (pend_at regs pc mem (seg_rom segs)) a = Some w.
Proof.
intros regs pc mem a w H. unfold ms_read_u64.
rewrite (ms_read_bytes_rdn segs) by reflexivity. cbn [ms_mem pend_at].
change (word_to_nat (Z_to_bv 64 8)) with 8%nat. rewrite H. f_equal. apply le_bytes_word_le8.
Qed.
Lemma ms_read_bytes_of_rdn : forall regs pc mem a (l : word) bs,
rdn segs mem a (word_to_nat l) = Some bs ->
ms_read_bytes (pend_at regs pc mem (seg_rom segs)) a l = Some bs.
Proof.
intros regs pc mem a l bs H. rewrite (ms_read_bytes_rdn segs) by reflexivity.
cbn [ms_mem pend_at]. exact H.
Qed.
Lemma ms_read_bytes_zero : forall regs pc mem a,
ms_read_bytes (pend_at regs pc mem (seg_rom segs)) a (Z_to_bv 64 0) = Some [].
Proof. intros. rewrite (ms_read_bytes_rdn segs) by reflexivity. reflexivity. Qed.
Definition havoc (E : env) (k : nat) (ws : list word) : env :=
mkEnv (fun i => if (i <? k)%nat then ew E i else nth (i - k) ws (ew E i)) (ed E).
Lemma ew_havoc_old : forall E k ws i, (i < k)%nat -> ew (havoc E k ws) i = ew E i.
Proof.
intros E k ws i Hi. unfold havoc. cbn [ew].
destruct (i <? k)%nat eqn:Hlt; [reflexivity|]. apply Nat.ltb_ge in Hlt. lia.
Qed.
Lemma env_agree_havoc : forall E k ws, env_agree k E (havoc E k ws).
Proof.
intros E k ws. split; [|reflexivity]. intros n Hn. symmetry. symmetry. rewrite ew_havoc_old by exact Hn. reflexivity.
Qed.
Lemma ew_havoc_new : forall E k ws j d, (j < length ws)%nat -> ew (havoc E k ws) (k + j) = nth j ws d.
Proof.
intros E k ws j d Hj. unfold havoc. cbn [ew].
destruct (k + j <? k)%nat eqn:Hlt; [apply Nat.ltb_lt in Hlt; lia|].
replace (k + j - k)%nat with j by lia. apply nth_indep. exact Hj.
Qed.
Lemma ed_havoc : forall E k ws, ed (havoc E k ws) = ed E.
Proof. reflexivity. Qed.
Fixpoint junk_upd (k : nat) (rl : list reg) : list (reg * sv) :=
match rl with [] => [] | r :: rl' => (r, SOff k 0) :: junk_upd (S k) rl' end.
Lemma junk_upd_fst : forall k rl, map fst (junk_upd k rl) = rl.
Proof. intros k rl. revert k. induction rl; intros k; cbn; [reflexivity| f_equal; apply IHrl]. Qed.
Lemma junk_upd_ok : forall E k ws rl regs' j,
(length rl + j <= length ws)%nat ->
forallb (fun r : reg => negb (bv_eqb r 0)) rl = true ->
(forall i, (i < length rl)%nat -> nth (j + i) ws (Z_to_bv 64 0) = getr regs' (nth i rl 0%bv)) ->
Forall (fun p => bv_eqb (fst p) 0 = false /\ getr regs' (fst p) = sv_denot (havoc E k ws) (snd p))
(junk_upd (k + j) rl).
Proof.
intros E k ws rl regs'. induction rl as [|r rl IH]; intros j Hlen Hnz Hval; cbn; [constructor|].
cbn in Hnz. apply andb_prop in Hnz as [Hr Hnz].
constructor.
- cbn [fst snd]. split; [destruct (bv_eqb r 0); [discriminate| reflexivity]|].
cbn [sv_denot]. rewrite Z.add_0_r, (ew_havoc_new E k ws j (Z_to_bv 64 0)) by (cbn in Hlen; lia).
rewrite Z_to_bv_bv_unsigned. symmetry. specialize (Hval 0%nat ltac:(cbn; lia)). cbn in Hval.
rewrite Nat.add_0_r in Hval. exact Hval.
- replace (S (k + j)) with (k + S j)%nat by lia. apply IH.
+ cbn in Hlen. lia.
+ exact Hnz.
+ intros i Hi. replace (S j + i)%nat with (j + S i)%nat by lia. exact (Hval (S i) ltac:(cbn; lia)).
Qed.
Lemma junk_upd_ok0 : forall E k rl regs',
forallb (fun r : reg => negb (bv_eqb r 0)) rl = true ->
Forall (fun p => bv_eqb (fst p) 0 = false /\ getr regs' (fst p) = sv_denot (havoc E k (map (getr regs') rl)) (snd p))
(junk_upd k rl).
Proof.
intros E k rl regs' Hnz.
pose proof (junk_upd_ok E k (map (getr regs') rl) rl regs' 0 ltac:(rewrite length_map; lia) Hnz) as H.
rewrite Nat.add_0_r in H. apply H.
intros i Hi. cbn [Nat.add]. rewrite (nth_indep _ _ (getr regs' 0%bv)) by (rewrite length_map; exact Hi).
change (getr regs' 0%bv) with ((fun r => getr regs' r) 0%bv). rewrite map_nth. reflexivity.
Qed.
Lemma st_ok_splice_havoc : forall k E ss regs regs' pc pc' mem mem' rs' upd rl,
st_ok segs E ss (mkst regs pc mem (seg_rom segs)) ->
ss_atoms_lt k ss = true ->
reg_nodup (map fst upd ++ rl) = true ->
forallb (fun r : reg => negb (bv_eqb r 0)) rl = true ->
forallb (fun p => sv_atoms_lt k (snd p)) upd = true ->
mem_atoms_lt k rs' = true ->
(forall r, reg_in r (map fst upd ++ rl) = false -> getr regs' r = getr regs r) ->
Forall (fun p => bv_eqb (fst p) 0 = false /\ getr regs' (fst p) = sv_denot E (snd p)) upd ->
mem_ok segs E mem' rs' ->
st_ok segs (havoc E k (map (getr regs') rl))
(mkSS pc' (sr_sets (ss_regs ss) (upd ++ junk_upd k rl)) rs' None (ss_facts ss))
(mkst regs' (Z_to_bv 64 pc') mem' (seg_rom segs)).
Proof.
intros k E ss regs regs' pc pc' mem mem' rs' upd rl HS Hat Hnd Hnz Hupd_at Hrs_at Hsame Hupd HM.
set (E' := havoc E k (map (getr regs') rl)).
assert (HA : env_agree k E E') by apply env_agree_havoc.
eapply (st_ok_set_regs_mem segs k E E' ss regs regs' pc pc' mem mem' rs' (upd ++ junk_upd k rl) HS HA Hat).
- rewrite map_app, junk_upd_fst. exact Hnd.
- rewrite map_app, junk_upd_fst. exact Hsame.
- apply Forall_app. split.
+ rewrite Forall_forall in Hupd |- *. intros p Hp. specialize (Hupd p Hp). destruct Hupd as [H1 H2].
split; [exact H1|]. rewrite H2. symmetry. apply (sv_denot_agree k E E'); [exact HA|].
apply (proj1 (forallb_forall _ _) Hupd_at p Hp).
+ subst E'. apply junk_upd_ok0. exact Hnz.
- eapply mem_ok_agree; eauto.
Qed.
Lemma iovcnt_val : forall E a b,
sv_denot E (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_SLTU (SLit 0) (SAlu ALU_XOR a b)) (SLit 1)) (SLit 0))
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
Lemma U_neg_off : forall E n c,
0 <= - (bv_unsigned (ew E n) + c) < M64 ->
U E (SAlu ALU_SUB (SLit 0) (SOff n c)) = - (bv_unsigned (ew E n) + c).
Proof.
intros E n c H. rewrite U_SAlu, U_SLit, U_SOff. cbn [zalu_raw].
rewrite (zcanon_id 0) by (unfold M64; lia).
unfold zcanon. rewrite Zminus_mod_idemp_r.
replace (0 - (bv_unsigned (ew E n) + c)) with (- (bv_unsigned (ew E n) + c)) by lia.
apply Z.mod_small. lia.
Qed.
Lemma U_add_off_atom : forall E n a k c,
0 <= bv_unsigned (ew E n) + a + (bv_unsigned (ew E k) + c) < M64 ->
0 <= bv_unsigned (ew E k) + c < M64 ->
U E (SAlu ALU_ADD (SOff n a) (SOff k c)) = bv_unsigned (ew E n) + a + (bv_unsigned (ew E k) + c).
Proof.
intros E n a k c H Hk. rewrite U_SAlu, !U_SOff. cbn [zalu_raw].
rewrite (zcanon_id (bv_unsigned (ew E k) + c)) by exact Hk.
unfold zcanon. rewrite Zplus_mod_idemp_l. apply Z.mod_small. exact H.
Qed.
Lemma U_off : forall E n c, 0 <= bv_unsigned (ew E n) + c < M64 -> U E (SOff n c) = bv_unsigned (ew E n) + c.
Proof. intros E n c H. rewrite U_SOff. apply zcanon_id. exact H. Qed.
Lemma branch_geu_U : forall E a b, branch_taken BC_GEU (sv_denot E a) (sv_denot E b) = negb (U E a <? U E b).
Proof. intros. reflexivity. Qed.
Lemma branch_ltu_U : forall E a b, branch_taken BC_LTU (sv_denot E a) (sv_denot E b) = (U E a <? U E b).
Proof. intros. reflexivity. Qed.
Lemma branch_eq_U : forall E a b, branch_taken BC_EQ (sv_denot E a) (sv_denot E b) = (U E a =? U E b).
Proof. intros. cbn [branch_taken]. unfold bv_eqb. reflexivity. Qed.
Lemma branch_ne_U : forall E a b, branch_taken BC_NE (sv_denot E a) (sv_denot E b) = negb (U E a =? U E b).
Proof. intros. cbn [branch_taken]. unfold bv_eqb. reflexivity. Qed.
Definition chunk_word_at (rs : smem) (b : option nat) (o : Z) : option sv :=
match find_region rs b o 8 with
| Some r => match find_chunk (r_chunks r) o 8 with
| Some (mkChunk o' (CVal 8 v)) => if o' =? o then Some v else None
| _ => None
end
| None => None
end.
Lemma chunk_word_at_sound : forall E m rs b o v,
mem_ok segs E m rs -> chunk_word_at rs b o = Some v ->
rdn segs m (Z_to_bv 64 (base_val E b + o)) 8 = Some (word_le8 (sv_denot E v)).
Proof.
intros E m rs b o v HM H. unfold chunk_word_at in H.
destruct (find_region rs b o 8) as [r|] eqn:Hr; [|discriminate].
destruct (find_chunk (r_chunks r) o 8) as [[o' [w v'| | |]]|] eqn:Hc; try discriminate.
destruct w as [|p]; try discriminate.
repeat (destruct p; try discriminate).
destruct (Z.eqb_spec o' o); [|discriminate]. injection H as <-. subst o'.
eapply rdn_chunk_word; eauto.
Qed.
Definition iov_read1 (rs : smem) (b : option nat) (o : Z) : option (sv * sv) :=
match chunk_word_at rs b o, chunk_word_at rs b (o + 8) with
| Some vb, Some vl => Some (vb, vl)
| _, _ => None
end.
Definition iov_read2 (rs : smem) (b : option nat) (o : Z) : option (sv * sv * sv * sv) :=
match iov_read1 rs b o, iov_read1 rs b (o + 16) with
| Some (vb0, vl0), Some (vb1, vl1) => Some (vb0, vl0, vb1, vl1)
| _, _ => None
end.
Lemma iov_read1_sound : forall E m rs b o vb vl,
mem_ok segs E m rs -> iov_read1 rs b o = Some (vb, vl) ->
rdn segs m (Z_to_bv 64 (base_val E b + o)) 8 = Some (word_le8 (sv_denot E vb))
/\ rdn segs m (Z_to_bv 64 (base_val E b + o + 8)) 8 = Some (word_le8 (sv_denot E vl)).
Proof.
intros E m rs b o vb vl HM H. unfold iov_read1 in H.
destruct (chunk_word_at rs b o) as [x|] eqn:H1; [|discriminate].
destruct (chunk_word_at rs b (o + 8)) as [y|] eqn:H2; [|discriminate]. injection H as <- <-.
split; [eapply chunk_word_at_sound; eauto|].
rewrite <- Z.add_assoc. eapply chunk_word_at_sound; eauto.
Qed.
Lemma U_sextw_high : forall E a, M64 - 2^31 <= U E a -> U E (SAluw ALU_ADD a (SLit 0)) = U E a.
Proof.
intros E a H. pose proof (U_range E a) as Hr.
rewrite U_of_S, S_SAluw. cbn [zalu_raw]. rewrite U_SLit. change (zcanon 0 mod 2 ^ 32) with 0. rewrite Z.add_0_r.
unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
change (bv_modulus 64) with (2^64). unfold M64 in *.
replace (U E a mod 2^32) with (U E a - (2^32 - 1) * 2^32).
2:{ symmetry. rewrite <- (Z.mod_add _ (-(2^32 - 1))) by lia.
replace (U E a + - (2^32-1) * 2^32) with (U E a - (2^32-1)*2^32) by lia. apply Z.mod_small. lia. }
replace ((U E a - (2 ^ 32 - 1) * 2 ^ 32 + 2 ^ 31) mod 2 ^ 32) with (U E a - (2 ^ 32 - 1) * 2 ^ 32 + 2 ^ 31 - 2^32).
2:{ symmetry. rewrite <- (Z.mod_add _ (-1)) by lia.
replace (U E a - (2 ^ 32 - 1) * 2 ^ 32 + 2 ^ 31 + - (1) * 2^32) with (U E a - (2 ^ 32 - 1) * 2 ^ 32 + 2 ^ 31 - 2^32) by lia.
apply Z.mod_small. lia. }
rewrite <- (Z.mod_add _ 1) by lia.
replace (U E a - (2 ^ 32 - 1) * 2 ^ 32 + 2 ^ 31 - 2 ^ 32 - 2 ^ 31 + 1 * 2 ^ 64) with (U E a) by lia.
apply Z.mod_small. lia.
Qed.
Lemma byte_list_eq : forall l1 l2 : list byte, map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
induction l1 as [|b l1 IH]; intros [|b' l2] H; cbn in H; try discriminate; [reflexivity|].
injection H as Hb Hl. f_equal; [apply bv_eq; exact Hb| apply IH; exact Hl].
Qed.
End h.
End g.
Ltac reg_of HS r H :=
lazymatch type of HS with st_ok ?segs ?E ?ss ?ms =>
pose proof (st_ok_reg segs E ss ms r HS) as H;
eval_sr_get_in H; cbn [sv_denot] in H; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in H
end.
Ltac env_transport E' Hagree :=
repeat match goal with
| HK : runs_ok ?E ?m ?l |- _ =>
lazymatch E with
| E' => fail
| _ => apply (runs_ok_agree _ E E' m l Hagree) in HK; [|vm_compute; reflexivity]
end
| HW : win_ok ?segs ?E ?m ?lo ?hi |- _ =>
lazymatch E with
| E' => fail
| _ => apply (win_ok_agree segs _ E E' m lo hi Hagree) in HW; [|vm_compute; reflexivity|vm_compute; reflexivity]
end
end.
Ltac sym_new_atom HS k v :=
lazymatch type of HS with st_ok ?segs ?E ?ss ?ms =>
let H := fresh "HS'" in
pose proof (st_ok_agree segs k E (ewset E k v) ss ms HS (env_agree_ewset E k v)
ltac:(vm_compute; reflexivity)) as H;
env_transport (ewset E k v) (env_agree_ewset E k v);
clear HS; rename H into HS
end.
Ltac sym_splice_havoc HS Hms k upd rl :=
lazymatch type of HS with st_ok ?segs ?E ?ss ?ms =>
lazymatch type of Hms with msteps _ _ (mkst ?regs' (Z_to_bv 64 ?pc') ?mem' _) =>
let Hshape := fresh "Hshape" in
pose proof (st_ok_mkst segs E ss ms HS eq_refl) as Hshape;
rewrite Hshape; eapply rz_msteps; [assumption | assumption | exact Hms | ];
rewrite Hshape in HS; clear Hshape;
let H := fresh "HS'" in
unshelve epose proof (st_ok_splice_havoc segs k E ss (ms_regs ms) regs' _ pc' (ms_mem ms) mem' (ss_mem ss) upd rl
HS _ _ _ _ _ _ _ _) as H;
[ vm_compute; reflexivity
| vm_compute; reflexivity
| vm_compute; reflexivity
| vm_compute; reflexivity
| vm_compute; reflexivity
| | |
| env_transport (havoc E k (map (getr regs') rl)) (env_agree_havoc E k (map (getr regs') rl));
clear HS Hms; rename H into HS; sym_norm HS ]
end end.
Ltac sym_step_manual HS Hstep upd :=
lazymatch type of HS with st_ok ?segs ?E ?ss ?ms =>
lazymatch type of Hstep with _ = MachineOk (mkst ?regs' (Z_to_bv 64 ?pc') _ _) =>
let Hshape := fresh "Hshape" in
pose proof (st_ok_mkst segs E ss ms HS eq_refl) as Hshape;
rewrite Hshape; eapply rz_msteps; [assumption | assumption | eapply msteps_one; [reflexivity | exact Hstep] | ];
rewrite Hshape in HS; clear Hshape;
let H := fresh "HS'" in
unshelve epose proof (st_ok_set_regs segs 1000%nat E E ss (ms_regs ms) regs' _ pc' (ms_mem ms) upd
HS (env_agree_refl 1000%nat E) _ _ _ _ _) as H;
[ vm_compute; reflexivity
| reflexivity
| vm_compute; reflexivity
| |
| clear HS Hstep; rename H into HS; sym_norm HS ]
end end.
Ltac win_transport segs E ss ss' ms' HS HF :=
repeat match goal with
| HW : win_ok _ ?E0 ?m ?lo ?hi |- _ =>
lazymatch m with
| ms_mem ms' => fail
| _ => first
[ apply (win_ok_after segs E ss ss' ms' m lo hi HS
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HF) in HW
| fail 1 ]
end
end.
Ltac win_transport_ecall segs E ss ss' ms' HS HF :=
repeat match goal with
| HW : win_ok _ ?E0 ?m ?lo ?hi |- _ =>
lazymatch m with
| ms_mem ms' => fail
| _ => first
[ apply (win_ok_after_ecall segs E ss ss' ms' m lo hi HS
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HF) in HW
| fail 1 ]
end
end.
Ltac runs2_transport segs E ss ss' ms' HS HF :=
repeat match goal with
| HK : runs_ok ?E0 ?m ?l |- _ =>
lazymatch m with
| ms_mem ms' => fail
| _ => first
[ apply (runs_ok_after2 segs E ss ss' ms' m l HS
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HF) in HK
| fail 1 ]
end
end.
Ltac runs2_transport_ecall segs E ss ss' ms' HS HF :=
repeat match goal with
| HK : runs_ok ?E0 ?m ?l |- _ =>
lazymatch m with
| ms_mem ms' => fail
| _ => first
[ apply (runs_ok_after2_ecall segs E ss ss' ms' m l HS
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HF) in HK
| fail 1 ]
end
end.
Ltac check_transported ms' :=
try match goal with
| H : runs_ok _ ?m _ |- _ => lazymatch m with ms_mem ms' => fail | _ => fail 2 "runs_ok hypothesis not transported:" H end
| H : win_ok _ _ ?m _ _ |- _ => lazymatch m with ms_mem ms' => fail | _ => fail 2 "win_ok hypothesis not transported:" H end
| H : runs_at _ ?m _ |- _ => lazymatch m with ms_mem ms' => fail | _ => fail 2 "runs_at hypothesis not transported:" H end
end.
Ltac sym_transport3 segs E ss ss' ms' HS HF :=
cbn [ms_mem mkst pend_at] in HF;
win_transport segs E ss ss' ms' HS HF;
runs2_transport segs E ss ss' ms' HS HF;
sym_transport segs E ss ss' ms' HS HF;
check_transported ms'.
Ltac sym_transport3_ecall segs E ss ss' ms' HS HF :=
cbn [ms_mem mkst pend_at] in HF;
win_transport_ecall segs E ss ss' ms' HS HF;
runs2_transport_ecall segs E ss ss' ms' HS HF;
sym_transport_ecall segs E ss ss' ms' HS HF;
check_transported ms'.
Ltac sym_run3_with tblok HS :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss ?ms =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let r := eval vm_compute in (sym_runN segs tbl FUEL ss) in
lazymatch r with
| (?ss', ?st) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_runN segs tbl FUEL ss = (ss', st)) by (vm_compute; reflexivity);
let ms' := fresh "ms" in let HF := fresh "HF" in
lazymatch st with
| RS_ecall =>
eapply (rz_run_ecall segs tbl tblok FUEL E ss ss' ms);
[ | | exact HS | exact Hrun | clear Hrun HS; intros ms' HS HF ]; [assumption|assumption|];
sym_transport3_ecall segs E ss ss' ms' HS HF
| RS_stopped ?why =>
eapply (rz_run_stop segs tbl tblok FUEL E ss ss' why ms);
[ | | exact HS | exact Hrun | clear Hrun HS; intros ms' HS HF ]; [assumption|assumption|];
sym_transport3 segs E ss ss' ms' HS HF
| RS_running =>
eapply (rz_run_running segs tbl tblok FUEL E ss ss' ms);
[ | | exact HS | exact Hrun | clear Hrun HS; intros ms' HS HF ]; [assumption|assumption|];
sym_transport3 segs E ss ss' ms' HS HF
end
end
end
end.
Ltac sym_run3_to_with tblok HS stop :=
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
eapply (rz_run_to_gen segs tbl tblok FUEL stop E ss ss' st ms);
[ | | exact HS | exact Hrun | clear Hrun HS; intros ms' HS HF ]; [assumption|assumption|];
lazymatch st with
| RS_ecall => change (st_ok_ecall segs E ss' ms') in HS; sym_transport3_ecall segs E ss ss' ms' HS HF
| _ => change (st_ok segs E ss' ms') in HS; sym_transport3 segs E ss ss' ms' HS HF
end
end
end
end.
Ltac sym_assume_with3 tblok HS dir :=
sym_assume_with tblok HS dir;
[ rewrite ?branch_geu_U, ?branch_ltu_U, ?branch_eq_U, ?branch_ne_U | sym_norm HS ].
Ltac rdn_lits HS i :=
lazymatch goal with |- rdn ?segs ?m (sv_denot ?E (SOff ?n ?off)) (word_to_nat (sv_denot _ (SLit ?k))) = Some _ =>
lazymatch type of HS with
| context [st_ok_ecall _ _ ?ss _] => rdn_lits_core HS segs E ss m i n off k
| context [st_ok _ _ ?ss _] => rdn_lits_core HS segs E ss m i n off k
end end
with rdn_lits_core HS segs E ss m i n off k :=
let kn := eval vm_compute in (Z.to_nat k) in
let ro := eval vm_compute in (nth_error (ss_mem ss) i) in
lazymatch ro with Some ?r =>
let zs := eval vm_compute in (read_lits (r_chunks r) off kn) in
lazymatch zs with
| Some ?zs' =>
let Hm := st_mem_ok HS in
let Hb := fresh "Hb" in
pose proof (mbytes_at_rdn segs m _ _ (read_lits_region segs E m (ss_mem ss) i r off kn zs' Hm
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))) as Hb;
cbn [length map base_val r_base] in Hb;
cbn [sv_denot]; rewrite word_to_nat_lit by lia;
change (Z.to_nat k) with kn; rewrite Hb; clear Hb;
f_equal; apply byte_list_eq; try (vm_compute; reflexivity)
| None => fail "rdn_lits: bytes not literal at" off k
end end.
Ltac pose_lits HS i off n Hb :=
let go segs E ss m :=
let ro := eval vm_compute in (nth_error (ss_mem ss) i) in
lazymatch ro with Some ?r =>
let zs := eval vm_compute in (read_lits (r_chunks r) off n) in
lazymatch zs with
| Some ?zs' =>
let Hm := st_mem_ok HS in
pose proof (read_lits_region segs E m (ss_mem ss) i r off n zs' Hm
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as Hb;
cbn [map base_val r_base] in Hb
| None => fail "pose_lits: bytes not literal at" off n
end end in
lazymatch type of HS with
| st_ok_ecall ?segs ?E ?ss ?ms => go segs E ss (ms_mem ms)
| st_ok ?segs ?E ?ss ?ms => go segs E ss (ms_mem ms)
end.
Ltac evalE :=
rewrite ?ew_havoc_old by lia; rewrite ?ew_ewset_same; rewrite ?ew_ewset_other by lia; rewrite ?ew_ewset_same;
rewrite ?ew_havoc_old by lia; rewrite ?ew_ewset_same; rewrite ?ew_ewset_other by lia;
repeat match goal with
| H : bv_unsigned (ew ?E ?n) = ?v |- context [bv_unsigned (ew ?E ?n)] => rewrite !H
end;
rewrite ?(unsigned_lit_small (Z.of_nat _)) by lia;
rewrite ?Z.add_0_r;
rewrite ?unsigned_lit_small by lia.
Ltac rdn_run HR i :=
cbn [sv_denot]; rewrite !Z.add_0_r; evalE;
rewrite word_to_nat_lit by lia; rewrite Nat2Z.id;
apply bytes_at_rdn; eapply bytes_at_app_l;
lazymatch goal with |- bytes_at ?m _ _ =>
let Hb := fresh "Hb" in
pose proof (runs_at_nth _ m _ i _ _ HR eq_refl) as Hb; cbn [nth_error app] in Hb; exact Hb end.
Ltac rdn_buf HS HK :=
lazymatch goal with |- rdn ?segs ?m _ _ = Some (?U ++ ?REST) =>
let Hb := fresh "Hb" in let Hrun := fresh "Hrun" in
cbn [sv_denot]; evalE; rewrite word_to_nat_lit by lia;
pose proof (runs_ok_single_inv _ _ _ _ _ _ HK) as (_ & _ & Hrun);
replace (Z.to_nat _) with (length (U ++ REST))
by (rewrite !length_app;
repeat match goal with |- context [length (strB ?str)] =>
let v := eval compute in (length (strB str)) in change (length (strB str)) with v end;
change (length nl) with 1%nat; lia);
apply (mbytes_at_rdn segs); apply mbytes_at_app;
[ let n := eval compute in (length U) in
pose_lits HS 0%nat (-544) n Hb; revert Hb; evalE; intros Hb;
lazymatch type of Hb with mbytes_at _ _ _ ?zs =>
replace U with zs by (apply byte_list_eq; vm_compute; reflexivity) end;
exact Hb
| let v := eval compute in (Z.of_nat (length U)) in change (Z.of_nat (length U)) with v;
lazymatch type of Hrun with bytes_at _ ?a _ => replace (_ + v) with a by lia end;
apply bytes_at_mbytes; exact Hrun ]
end.
Ltac rdn_rodata HS lem :=
lazymatch goal with |- rdn ?sg ?m ?a ?n = Some _ =>
let Hb := fresh "Hb" in
eassert (Hb : rdn sg m a n = Some _) by (rdn_of_chunk HS);
rewrite Hb; f_equal; apply lem end.
Ltac atom_fact_lit := evalE; rewrite ?Z.mod_1_r; lia.
