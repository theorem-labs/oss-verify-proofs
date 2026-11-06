(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: a symbolic-state lemma for fuzz_reply's ASan walks, over the region form of
   Reusable/YP09.v and the pi state of Reusable/YP0d.v.  IMAGE B copy, byte for byte below this comment, of
   lib/A/W_rebase.v at a working branch 9367674296a (7aaf61c32d4): that file is not on the B integration
   base (a working branch), and it requires only lib/Reusable, so B's send_line walk
   (lib/B/W_send_line_*.v) carries it under its own name. *)
(* Rebasing a region.  The symbolic engine finds a region by its base atom syntactically (Reusable/YP09.v
   find_region / obase_eqb; Reusable/YP0l.v addr_of (SOff n z) = (Some n, z)).  A program that reads a global with a
   PLdHi slot addresses it through the object atom, (Some (A_OBJ i), off) (Reusable/YP0a.v sym_step_pi), and stores
   to it through the kept auipc register, (Some (A_HI j), imm).  Regions are pairwise disjoint, so one region
   serves both only if its base atom is switched between the two.  `st_ok_pi_rebase` switches it: region i's base a
   becomes b and every offset of the region (lo, hi, the writable window, the chunks) moves by d, where
   base a = base b + d.  Nothing else of the state changes, so the region covers the same bytes with the same
   contents.  The equation between the two image atoms is not derivable from the listing's certificate (a PLdHi
   slot's immediate is the fetched word's, which the abstract placement does not fix), so a walk takes it as a
   Section hypothesis `VAL (A_HI j) + imm = VAL (A_OBJ i)`, which the pinned placement (W_img.v PB_fr) discharges
   by vm_compute.  `prebase` applies the lemma and normalises the new state. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK0o YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP00 YP0k YP0b.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0a YP0d.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section a. Context {fx : FPState}.
Variable segs : list Segment.
Variable val : nat -> Z.
Definition shift_chunk (d : Z) (c : YP09.chunk) : YP09.chunk := YP09.mkChunk (YP09.c_off c + d) (YP09.c_val c).
Definition rebase_region (b : nat) (d : Z) (r : region) : region :=
YP09.mkRegion (Some b) (YP09.r_lo r + d) (YP09.r_hi r + d) (YP09.r_wlo r + d) (YP09.r_whi r + d)
(map (shift_chunk d) (YP09.r_chunks r)).
Fixpoint map_nth {X : Type} (f : X -> X) (i : nat) (l : list X) : list X :=
match l, i with
| [], _ => []
| x :: l', O => f x :: l'
| x :: l', S i' => x :: map_nth f i' l'
end.
Definition ss_rebase (i b : nat) (d : Z) (ss : sstate) : sstate :=
mkSST (ss_pc ss) (ss_regs ss) (ss_fregs ss) (map_nth (rebase_region b d) i (ss_mem ss)) (ss_resv ss) (ss_facts ss).
Definition same_extent (E : env) (r r' : region) : Prop :=
base_val E (YP09.r_base r') + YP09.r_lo r' = base_val E (YP09.r_base r) + YP09.r_lo r /\
base_val E (YP09.r_base r') + YP09.r_hi r' = base_val E (YP09.r_base r) + YP09.r_hi r.
Lemma same_extent_rebase : forall E r b d,
base_val E (YP09.r_base r) = base_val E (Some b) + d -> same_extent E r (rebase_region b d r).
Proof. intros E r b d H. unfold same_extent, rebase_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi]. lia. Qed.
Lemma extent_disjoint_same_l : forall E r r' r2, same_extent E r r' ->
extent_disjoint E r r2 -> extent_disjoint E r' r2.
Proof. intros E r r' r2 [H1 H2] H. unfold extent_disjoint in *. lia. Qed.
Lemma extent_disjoint_same_r : forall E r r' r2, same_extent E r r' ->
extent_disjoint E r2 r -> extent_disjoint E r2 r'.
Proof. intros E r r' r2 [H1 H2] H. unfold extent_disjoint in *. lia. Qed.
Lemma all_disjoint_same_l : forall E r r' rs, same_extent E r r' -> all_disjoint E r rs -> all_disjoint E r' rs.
Proof.
intros E r r' rs Hs. induction rs as [|r2 rs IH]; cbn; [auto|].
intros [H1 H2]. split; [exact (extent_disjoint_same_l E r r' r2 Hs H1) | exact (IH H2)].
Qed.
Lemma all_disjoint_map_nth : forall E (f : region -> region) x i rs r,
nth_error rs i = Some r -> same_extent E r (f r) -> all_disjoint E x rs -> all_disjoint E x (map_nth f i rs).
Proof.
intros E f x i rs. revert i. induction rs as [|r0 rs IH]; intros i r Hn Hs H; [destruct i; exact H|].
destruct H as [H1 H2]. destruct i as [|i]; cbn in Hn |- *.
- injection Hn as <-. split; [exact (extent_disjoint_same_r E r0 (f r0) x Hs H1) | exact H2].
- split; [exact H1|]. exact (IH i r Hn Hs H2).
Qed.
Lemma pairwise_disjoint_map_nth : forall E (f : region -> region) i rs r,
nth_error rs i = Some r -> same_extent E r (f r) -> pairwise_disjoint E rs -> pairwise_disjoint E (map_nth f i rs).
Proof.
intros E f i rs. revert i. induction rs as [|r0 rs IH]; intros i r Hn Hs H; [destruct i; exact H|].
destruct H as [H1 H2]. destruct i as [|i]; cbn in Hn |- *.
- injection Hn as <-. split; [exact (all_disjoint_same_l E r0 (f r0) rs Hs H1) | exact H2].
- split; [exact (all_disjoint_map_nth E f r0 i rs r Hn Hs H1) | exact (IH i r Hn Hs H2)].
Qed.
Lemma Forall_map_nth : forall {X : Type} (P : X -> Prop) (f : X -> X) i l x0,
nth_error l i = Some x0 -> (P x0 -> P (f x0)) -> Forall P l -> Forall P (map_nth f i l).
Proof.
intros X P f i l. revert i. induction l as [|x l IH]; intros i x0 Hn Hf H; [destruct i; exact H|].
inversion H as [|? ? Hx Hl]; subst. destruct i as [|i]; cbn in Hn |- *.
- injection Hn as <-. constructor; [exact (Hf Hx) | exact Hl].
- constructor; [exact Hx | exact (IH i x0 Hn Hf Hl)].
Qed.
Lemma region_ok_rebase : forall E m r b d,
base_val E (YP09.r_base r) = base_val E (Some b) + d -> region_ok segs E m r -> region_ok segs E m (rebase_region b d r).
Proof.
intros E m r b d Hb (H1 & H2 & H3 & H4). unfold region_ok, rebase_region.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
split; [lia|]. split; [lia|]. split.
- intros o Ho. replace (base_val E (Some b) + o) with (base_val E (YP09.r_base r) + (o - d)) by lia. apply H3. lia.
- apply Forall_map. eapply Forall_impl; [|exact H4]. intros c Hc i Hi.
  unfold shift_chunk, YP09.c_len in *. cbn [YP09.c_off YP09.c_val] in *.
  replace (base_val E (Some b) + (YP09.c_off c + d)) with (base_val E (YP09.r_base r) + YP09.c_off c) by lia.
  exact (Hc i Hi).
Qed.
Lemma st_ok_rebase : forall E ss ms i r b d,
st_ok segs E ss ms -> nth_error (ss_mem ss) i = Some r ->
base_val E (YP09.r_base r) = base_val E (Some b) + d ->
regions_wf (map_nth (rebase_region b d) i (ss_mem ss)) = true ->
st_ok segs E (mkSST (ss_pc ss) (ss_regs ss) (ss_fregs ss) (map_nth (rebase_region b d) i (ss_mem ss)) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms i r b d (S1 & S2 & S3 & S4 & S5 & S6 & S7 & (M1 & M2 & M3) & S9) Hn Hb Hwf.
unfold st_ok. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
do 7 (split; [assumption|]). split; [|exact S9].
split; [exact Hwf|]. split.
- exact (Forall_map_nth _ (rebase_region b d) i (ss_mem ss) r Hn (region_ok_rebase E (ms_mem ms) r b d Hb) M2).
- exact (pairwise_disjoint_map_nth E (rebase_region b d) i (ss_mem ss) r Hn (same_extent_rebase E r b d Hb) M3).
Qed.
Lemma st_ok_pi_rebase : forall E ss ms i r b d,
st_ok_pi segs val E ss ms -> nth_error (ss_mem ss) i = Some r ->
base_val E (YP09.r_base r) = base_val E (Some b) + d ->
regions_wf (map_nth (rebase_region b d) i (ss_mem ss)) = true ->
st_ok_pi segs val E (ss_rebase i b d ss) ms.
Proof.
intros E ss ms i r b d HS Hn Hb Hwf. unfold st_ok_pi, abs_ss, setpc, ss_rebase in *.
cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts] in *.
exact (st_ok_rebase E (mkSST (val A_TEXT + ss_pc ss) (ss_regs ss) (ss_fregs ss) (ss_mem ss) (ss_resv ss) (ss_facts ss))
ms i r b d HS Hn Hb Hwf).
Qed.
(* The equation between two image atoms, from the placement's values. *)
Lemma base_val_img : forall A_LIM E a b d, img_env val A_LIM E ->
(A_TEXT <= a < A_LIM)%nat -> (A_TEXT <= b < A_LIM)%nat -> val a = val b + d ->
base_val E (Some a) = base_val E (Some b) + d.
Proof. intros A_LIM E a b d HE Ha Hb H. cbn [base_val]. rewrite (HE a Ha), (HE b Hb). exact H. Qed.
End a.
(* prebase HS i b d HREL: in  HS : st_ok_pi segs val E ss ms, move region i (whose base is an image atom a) to base
   atom b, given  HREL : val a = val b + d  (or  val b + d = val a); the new state is normalised by vm_compute. *)
Ltac prebase HS i b d HREL :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss ?ms =>
let HEI := lazymatch goal with H : img_env val _ E |- _ => H | _ => fail "prebase: no img_env hypothesis for" E end in
let r := eval vm_compute in (nth i (ss_mem ss) (YP09.mkRegion None 0 0 0 0 [])) in
let HS' := fresh "HSr" in
pose proof (st_ok_pi_rebase segs val E ss ms i r b d HS ltac:(vm_compute; reflexivity)
  ltac:(cbn [YP09.r_base]; apply (base_val_img val _ E _ b d HEI); [cbv; lia | cbv; lia | first [exact HREL | symmetry; exact HREL | lia]])
  ltac:(vm_compute; reflexivity)) as HS';
clear HS; rename HS' into HS;
let ss2 := eval vm_compute in (ss_rebase i b d ss) in change (ss_rebase i b d ss) with ss2 in HS
end.
