(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YQ0j YQ0b YQ0i YQ09 YQ04 YO3v YI00.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section S.
Context {fx : YK11.FPState}.
Variable segs : list Segment.
Definition region_kept_ck (E : env) (mem mem' : word -> option byte) (r : YQ0b.region) : Prop :=
(forall c, In c (r_chunks r) -> forall i, 0 <= i < c_len c ->
mbyte segs mem' (base_val E (r_base r) + c_off c + i) = mbyte segs mem (base_val E (r_base r) + c_off c + i)) /\
(forall a, base_val E (r_base r) + r_wlo r <= a < base_val E (r_base r) + r_whi r ->
writable_at segs mem a -> writable_at segs mem' a).
Lemma region_kept_ck_of_kept : forall E mem mem' r,
forallb (chunk_inside r) (r_chunks r) = true -> region_kept segs E mem mem' r -> region_kept_ck E mem mem' r.
Proof.
intros E mem mem' r Hin [K1 K2]. split; [|exact K2].
intros c Hc i Hi. pose proof (proj1 (forallb_forall _ _) Hin c Hc) as Hci. unfold chunk_inside in Hci.
apply andb_prop in Hci as [Hci _]. apply andb_prop in Hci as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
apply K1. lia.
Qed.
Lemma region_ok_kept_ck : forall E mem mem' r,
region_ok segs E mem r -> region_kept_ck E mem mem' r -> region_ok segs E mem' r.
Proof.
intros E mem mem' r (Hlo & Hhi & Hw & Hcs) [K1 K2]. unfold region_ok. cbv zeta.
split; [exact Hlo|]. split; [exact Hhi|]. split.
- intros o Ho. apply K2; [lia|]. apply Hw. exact Ho.
- apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) Hcs c Hc) as Hck.
intros i Hi. destruct (Hck i Hi) as (b & Hb1 & Hb2). exists b. split; [exact Hb1|].
rewrite (K1 c Hc i Hi). exact Hb2.
Qed.
Lemma mem_ok_kept_ck : forall E mem mem' rs,
mem_ok segs E mem rs -> Forall (region_kept_ck E mem mem') rs -> mem_ok segs E mem' rs.
Proof.
intros E mem mem' rs (Hwf & Hok & Hpd) Hk. split; [exact Hwf|]. split; [|exact Hpd].
apply Forall_forall. intros r Hr.
exact (region_ok_kept_ck E mem mem' r (proj1 (Forall_forall _ _) Hok r Hr) (proj1 (Forall_forall _ _) Hk r Hr)).
Qed.
Theorem st_ok_after_stretch_ck : forall k E ss ms regs' mem' rs pc (clob : list reg),
st_ok segs E ss ms ->
ss_resv ss = None ->
ss_atoms_lt k ss = true ->
regions_wf rs = true -> mem_atoms_lt k rs = true ->
submem rs (ss_mem ss) ->
reg_nodup clob = true -> forallb (fun r : reg => negb (bv_eqb r 0)) clob = true ->
(forall r, reg_in r clob = false -> getr regs' r = getr (ms_regs ms) r) ->
Forall (region_kept_ck E (ms_mem ms) mem') rs ->
st_ok segs (havoc E k (map (getr regs') clob)) (ss_after_stretch ss rs k clob pc)
(mkst regs' (Z_to_bv 64 pc) mem' (seg_rom segs)).
Proof.
intros k E ss ms regs' mem' rs pc clob HS Hrv Hat Hwf Hmat Hsub Hnd Hnz Hsame Hk.
pose proof (st_ok_mkst segs E ss ms HS Hrv) as Hshape. rewrite Hshape in HS.
pose proof (st_ok_splice_havoc segs k E ss (ms_regs ms) regs' (Z_to_bv 64 (ss_pc ss)) pc
(ms_mem ms) mem' rs [] clob HS Hat) as H.
cbn [map app] in H. apply H.
- exact Hnd.
- exact Hnz.
- reflexivity.
- exact Hmat.
- exact Hsame.
- constructor.
- apply (mem_ok_kept_ck E (ms_mem ms) mem' rs); [|exact Hk].
eapply mem_ok_sub; [exact Hsub | exact Hwf | exact (st_ok_mem_ok segs E ss _ HS)].
Qed.
End S.
Ltac jafter_stretch_ck HS k regs2 mem2 clob newpc idxs HS2 :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss ?ms =>
let rs := eval vm_compute in (pick (ss_mem ss) idxs) in
pose proof (st_ok_after_stretch_ck segs k E ss ms regs2 mem2 rs newpc clob HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(submem_tac) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as HS2;
let ss2 := eval vm_compute in (ss_after_stretch ss rs k clob newpc) in
change (ss_after_stretch ss rs k clob newpc) with ss2 in HS2
end.
