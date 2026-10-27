(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YP0f.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0e.
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
Section d.
Variable segs : list Segment.
Context {fx : FPState}.
Definition run_ok (E : env) (m : word -> option byte) (lo hi : sv) (a : Z) (bs : list byte) : Prop :=
bv_unsigned (sv_denot E lo) <= a
/\ a + Z.of_nat (length bs) <= bv_unsigned (sv_denot E hi)
/\ bytes_at m a bs.
Definition runs_ok (E : env) (m : word -> option byte) (l : list (sv * sv * Z * list byte)) : Prop :=
Forall (fun e => match e with (lo, hi, a, bs) => run_ok E m lo hi a bs end) l.
Definition itv_lo (i : itv) : option Z := match i with Some (l, _) => Some l | None => None end.
Definition itv_hi (i : itv) : option Z := match i with Some (_, h) => Some h | None => None end.
Definition wr_bounds (G : facts) (r : region) : option (Z * Z) :=
match r_base r with
| None => Some (r_wlo r, r_whi r)
| Some b => match atom_lookup (f_atoms G) b with
| Some f => Some (af_lo f + r_wlo r, af_hi f + r_whi r)
| None => None
end
end.
Fixpoint cond_excludes (cs : list acond) (t : nat) (wlo whi : Z) : bool :=
match cs with
| [] => false
| mkAC BC_GEU (SOff t' c) (SLit w) :: r =>
(Nat.eqb t' t && (0 <=? - c) && (0 <=? w) && (w <? M64) && (- c <=? wlo) && (whi <=? - c + w) && (- c + w <=? M64))
|| cond_excludes r t wlo whi
| _ :: r => cond_excludes r t wlo whi
end.
Definition sep_check (G : facts) (lo hi : sv) (r : region) : bool :=
(r_whi r <=? r_wlo r) ||
match lo, hi, r_base r with
| SOff b x, SOff b' y, Some rb =>
Nat.eqb b b' && Nat.eqb b rb &&
match atom_lookup (f_atoms G) b with
| Some f => (0 <=? x) && (x <=? y) && (af_hi f + y <? M64) && (af_hi f + r_whi r <? M64)
&& (0 <=? af_lo f + r_wlo r)
&& ((y <=? r_wlo r) || (r_whi r <=? x))
| None => false
end
| _, _, _ => false
end ||
match itv_hi (sv_urange G hi), itv_lo (sv_urange G lo), wr_bounds G r with
| Some hh, Some ll, Some (wl, wh) => (hh <=? wl) || (wh <=? ll)
| _, _, _ => false
end ||
match lo, hi, r_base r with
| SOff t x, SOff t' y, None =>
Nat.eqb t t' && (0 <=? x) && (x <=? y) &&
match atom_lookup (f_atoms G) t with
| Some f => (af_hi f + y <? M64) && cond_excludes (f_conds G) t (r_wlo r - y + 1) (r_whi r - x)
| None => false
end
| _, _, _ => false
end.
Definition kept_check (G : facts) (rs : smem) (lo hi : sv) : bool :=
forallb (sep_check G lo hi) rs.
Definition runs_kept_check (G : facts) (rs : smem) (l : list (sv * sv)) : bool :=
forallb (fun p => kept_check G rs (fst p) (snd p)) l.
Lemma cond_excludes_sound : forall E cs t wlo whi,
conds_ok E cs -> cond_excludes cs t wlo whi = true ->
forall z, wlo <= z < whi -> bv_unsigned (ew E t) <> z.
Proof.
intros E cs t wlo whi Hcs H. induction cs as [|[c a b] r IH]; cbn in H; [discriminate|].
destruct Hcs as [Hc Hr].
assert (IH' : cond_excludes r t wlo whi = true -> forall z, wlo <= z < whi -> bv_unsigned (ew E t) <> z)
by (intros; apply IH; assumption).
destruct c; try (apply IH'; exact H).
destruct a as [|t' c0| | | | | | | | |]; try (apply IH'; exact H).
destruct b as [w| | | | | | | | | |]; try (apply IH'; exact H).
apply orb_prop in H as [H|H]; [|apply IH'; exact H].
apply andb_prop in H as [H A6]. apply andb_prop in H as [H A5]. apply andb_prop in H as [H A4].
apply andb_prop in H as [H A3]. apply andb_prop in H as [H A2]. apply andb_prop in H as [A0 A1].
apply Nat.eqb_eq in A0. subst t'.
apply Z.leb_le in A1. apply Z.leb_le in A2. apply Z.ltb_lt in A3. apply Z.leb_le in A4.
apply Z.leb_le in A5. apply Z.leb_le in A6.
intros z Hz Heq.
unfold acond_ok in Hc. cbn [ac_c ac_a ac_b branch_taken sv_denot] in Hc.
unfold bv_ltu in Hc. rewrite !Z_to_bv_unsigned in Hc.
pose proof (u64_range (ew E t)) as Ht. rewrite Heq in Hc.
unfold bv_wrap in Hc. change (bv_modulus 64) with M64 in Hc. unfold M64 in *.
rewrite (Z.mod_small w) in Hc by lia.
rewrite (Z.mod_small (z + c0)) in Hc by lia.
destruct (z + c0 <? w) eqn:Hlt; [discriminate|]. apply Z.ltb_ge in Hlt. lia.
Qed.
Definition run_loc (E : env) (lo hi : sv) (a : Z) (bs : list byte) : Prop :=
bv_unsigned (sv_denot E lo) <= a /\ a + Z.of_nat (length bs) <= bv_unsigned (sv_denot E hi).
Lemma sep_check_sound : forall E G lo hi r a bs x,
facts_ok E G -> region_wf r = true ->
run_loc E lo hi a bs ->
sep_check G lo hi r = true ->
a <= x < a + Z.of_nat (length bs) ->
~ (base_val E (r_base r) + r_wlo r <= x < base_val E (r_base r) + r_whi r).
Proof.
intros E G lo hi r a bs x HG Hwf [Hlo Hhi] H Hx Hin.
pose proof (u64_range (sv_denot E lo)) as Rlo. pose proof (u64_range (sv_denot E hi)) as Rhi.
unfold sep_check in H.
apply orb_prop in H as [H|H].
2:{
destruct lo as [|t xo| | | | | | | | |]; try discriminate.
destruct hi as [|t' yo| | | | | | | | |]; try discriminate.
destruct (r_base r) as [rb|] eqn:Hrb; try discriminate. cbn [base_val] in Hin.
repeat (apply andb_prop in H as [H ?]).
apply Nat.eqb_eq in H. subst t'. apply Z.leb_le in H2. apply Z.leb_le in H1.
destruct (atom_lookup (f_atoms G) t) as [f|] eqn:Hf; [|discriminate].
apply andb_prop in H0 as [Hnw Hce]. apply Z.ltb_lt in Hnw.
pose proof (atom_lookup_ok E _ _ _ (proj1 HG) Hf) as (Hb & _).
rewrite denot_SOff in Hlo, Hhi. unfold M64 in Hnw.
pose proof (u64_range (ew E t)) as Ht.
rewrite zcanon_id in Hlo by (unfold M64 in *; lia). rewrite zcanon_id in Hhi by (unfold M64 in *; lia).
apply (cond_excludes_sound E (f_conds G) t _ _ (proj1 (proj2 HG)) Hce (bv_unsigned (ew E t))); [|reflexivity].
lia. }
apply orb_prop in H as [H|H].
2:{
destruct (itv_hi (sv_urange G hi)) as [hh|] eqn:Hhh; [|discriminate].
destruct (itv_lo (sv_urange G lo)) as [ll|] eqn:Hll; [|discriminate].
destruct (wr_bounds G r) as [[wl wh]|] eqn:Hwb; [|discriminate].
assert (Hhh' : bv_unsigned (sv_denot E hi) <= hh).
{ unfold itv_hi in Hhh. destruct (sv_urange G hi) as [[l0 h0]|] eqn:Hu; [|discriminate].
injection Hhh as <-. apply (sv_urange_sound E G hi l0 h0 HG Hu). }
assert (Hll' : ll <= bv_unsigned (sv_denot E lo)).
{ unfold itv_lo in Hll. destruct (sv_urange G lo) as [[l0 h0]|] eqn:Hu; [|discriminate].
injection Hll as <-. apply (sv_urange_sound E G lo l0 h0 HG Hu). }
assert (Hw : wl <= base_val E (r_base r) + r_wlo r /\ base_val E (r_base r) + r_whi r <= wh).
{ unfold wr_bounds in Hwb. destruct (r_base r) as [b|]; cbn [base_val].
- destruct (atom_lookup (f_atoms G) b) as [f|] eqn:Hf; [|discriminate]. injection Hwb as <- <-.
pose proof (atom_lookup_ok E _ _ _ (proj1 HG) Hf) as (Hb & _). lia.
- injection Hwb as <- <-. lia. }
apply orb_prop in H as [H|H]; apply Z.leb_le in H; lia. }
apply orb_prop in H as [H|H].
{ apply Z.leb_le in H. lia. }
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
Lemma kept_check_sound : forall E G rs lo hi a bs x,
facts_ok E G -> regions_wf rs = true ->
run_loc E lo hi a bs -> kept_check G rs lo hi = true ->
a <= x < a + Z.of_nat (length bs) -> ~ in_wrange E rs x.
Proof.
intros E G rs lo hi a bs x HG Hwf Hloc H Hx (r & Hin & Hr).
unfold kept_check in H. pose proof (proj1 (forallb_forall _ _) H r Hin) as Hs.
eapply (sep_check_sound E G lo hi r a bs x HG); eauto.
eapply regions_wf_In; eauto.
Qed.
Lemma runs_ok_frame : forall E G rs m m' l,
facts_ok E G -> regions_wf rs = true ->
frame_of E rs m m' ->
runs_kept_check G rs (map (fun e => match e with (lo, hi, _, _) => (lo, hi) end) l) = true ->
runs_ok E m l -> runs_ok E m' l.
Proof.
intros E G rs m m' l HG Hwf Hfr Hk H. unfold runs_ok, runs_kept_check in *.
rewrite Forall_forall in *. intros [[[lo hi] a] bs] Hin. specialize (H _ Hin). cbn in H.
destruct H as (Hlo & Hhi & Hb). split; [exact Hlo|]. split; [exact Hhi|].
assert (Hkc : kept_check G rs lo hi = true).
{ apply (proj1 (forallb_forall _ _) Hk (lo, hi)). apply in_map_iff. exists (lo, hi, a, bs). auto. }
pose proof (u64_range (sv_denot E lo)). pose proof (u64_range (sv_denot E hi)).
apply (bytes_at_frame m m' a bs); [| lia | lia | exact Hb].
intros x Hx. apply Hfr. eapply kept_check_sound; eauto. split; assumption.
Qed.
Lemma st_ok_regions_wf : forall E ss ms, st_ok segs E ss ms -> regions_wf (ss_mem ss) = true.
Proof. intros E ss ms HS. apply (proj1 (st_ok_mem_ok segs E ss ms HS)). Qed.
Lemma runs_ok_after : forall E ss ss' ms' m l,
st_ok segs E ss' ms' -> skeleton (ss_mem ss') = skeleton (ss_mem ss) \/ True ->
regions_wf (ss_mem ss) = true ->
runs_kept_check (ss_facts ss') (ss_mem ss) (map (fun e => match e with (lo, hi, _, _) => (lo, hi) end) l) = true ->
frame_of E (ss_mem ss) m (ms_mem ms') ->
runs_ok E m l -> runs_ok E (ms_mem ms') l.
Proof.
intros E ss ss' ms' m l HS _ Hwf Hk Hfr H.
eapply runs_ok_frame; [apply (st_ok_facts_ok segs E ss' ms' HS) | exact Hwf | exact Hfr | exact Hk | exact H].
Qed.
Lemma runs_ok_after_ecall : forall E ss ss' ms' m l,
st_ok_ecall segs E ss' ms' ->
regions_wf (ss_mem ss) = true ->
runs_kept_check (ss_facts ss') (ss_mem ss) (map (fun e => match e with (lo, hi, _, _) => (lo, hi) end) l) = true ->
frame_of E (ss_mem ss) m (ms_mem ms') ->
runs_ok E m l -> runs_ok E (ms_mem ms') l.
Proof.
intros E ss ss' ms' m l HS Hwf Hk Hfr H.
destruct HS as (_ & _ & _ & _ & _ & _ & _ & _ & HG).
eapply runs_ok_frame; [exact HG | exact Hwf | exact Hfr | exact Hk | exact H].
Qed.
Lemma runs_ok_agree : forall k E E' m l,
env_agree k E E' ->
forallb (fun e => match e with (lo, hi, _, _) => sv_atoms_lt k lo && sv_atoms_lt k hi end) l = true ->
runs_ok E m l -> runs_ok E' m l.
Proof.
intros k E E' m l HA Hat H. unfold runs_ok in *. rewrite Forall_forall in *.
intros [[[lo hi] a] bs] Hin. specialize (H _ Hin). cbn in H.
pose proof (proj1 (forallb_forall _ _) Hat _ Hin) as Hlh. cbn in Hlh. apply andb_prop in Hlh as [H1 H2].
destruct H as (Hlo & Hhi & Hb).
rewrite <- (sv_denot_agree k E E' lo HA H1) in Hlo. rewrite <- (sv_denot_agree k E E' hi HA H2) in Hhi.
repeat split; assumption.
Qed.
Lemma runs_ok_nth : forall E m l i lo hi a bs,
runs_ok E m l -> nth_error l i = Some (lo, hi, a, bs) -> bytes_at m a bs.
Proof.
intros E m l i lo hi a bs H Hn. unfold runs_ok in H. rewrite Forall_forall in H.
apply nth_error_In in Hn. specialize (H _ Hn). cbv beta iota in H. destruct H as (H1 & H2 & H3). exact H3.
Qed.
Lemma runs_ok_nth_loc : forall E m l i lo hi a bs,
runs_ok E m l -> nth_error l i = Some (lo, hi, a, bs) ->
bv_unsigned (sv_denot E lo) <= a /\ a + Z.of_nat (length bs) <= bv_unsigned (sv_denot E hi).
Proof.
intros E m l i lo hi a bs H Hn. unfold runs_ok in H. rewrite Forall_forall in H.
apply nth_error_In in Hn. specialize (H _ Hn). cbv beta iota in H. destruct H as (H1 & H2 & H3). split; assumption.
Qed.
End d.
Ltac sym_transport2 segs E ss ss' ms' HS HF :=
cbn [ms_mem mkst pend_at] in HF;
repeat match goal with
| HR : runs_at ?spv ?m ?l |- _ =>
lazymatch m with
| ms_mem ms' => fail
| _ => first
[ apply (runs_at_after segs E ss' ms' (ss_mem ss) m spv l HS
ltac:(vm_compute; reflexivity) HF ltac:(cbn; lia)) in HR
| fail 1 ]
end
| HK : runs_ok ?E0 ?m ?l |- _ =>
lazymatch m with
| ms_mem ms' => fail
| _ => first
[ apply (runs_ok_after segs E ss ss' ms' m l HS (or_intror I)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HF) in HK
| fail 1 ]
end
end;
try clear HF;
try match type of HS with st_ok _ _ _ ?ms' =>
repeat match goal with
| old : machine_state |- _ => lazymatch old with ms' => fail | _ => clear old end
end
end.
Ltac sym_transport2_ecall segs E ss ss' ms' HS HF :=
cbn [ms_mem mkst pend_at] in HF;
repeat match goal with
| HR : runs_at ?spv ?m ?l |- _ =>
lazymatch m with
| ms_mem ms' => fail
| _ => first
[ apply (runs_at_after_ecall segs E ss' ms' (ss_mem ss) m spv l HS
ltac:(vm_compute; reflexivity) HF ltac:(cbn; lia)) in HR
| fail 1 ]
end
| HK : runs_ok ?E0 ?m ?l |- _ =>
lazymatch m with
| ms_mem ms' => fail
| _ => first
[ apply (runs_ok_after_ecall segs E ss ss' ms' m l HS
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HF) in HK
| fail 1 ]
end
end;
try clear HF;
repeat match goal with
| old : machine_state |- _ => lazymatch old with ms' => fail | _ => clear old end
end.
Ltac sym_run2_with tblok HS :=
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
sym_transport2_ecall segs E ss ss' ms' HS HF
| RS_stopped ?why =>
eapply (rz_run_stop segs tbl tblok FUEL E ss ss' why ms);
[ | | exact HS | exact Hrun | clear Hrun HS; intros ms' HS HF ]; [assumption|assumption|];
sym_transport2 segs E ss ss' ms' HS HF
| RS_running =>
eapply (rz_run_running segs tbl tblok FUEL E ss ss' ms);
[ | | exact HS | exact Hrun | clear Hrun HS; intros ms' HS HF ]; [assumption|assumption|];
sym_transport2 segs E ss ss' ms' HS HF
end
end
end
end.
Ltac sym_run2_to_with tblok HS stop :=
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
| RS_ecall => sym_transport2_ecall segs E ss ss' ms' HS HF
| _ => sym_transport2 segs E ss ss' ms' HS HF
end
end
end
end.
