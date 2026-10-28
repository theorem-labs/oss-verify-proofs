(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0n YI0s YCbw.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0y YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACbk AC8a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8h AC8j ACbc ACbf ACab ACam ACai ACan.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Definition gen_chunk (off : Z) (v' : sv) (c : YP09.chunk) : YP09.chunk :=
match YP09.c_val c with
| CVal w _ => if Z.eqb (YP09.c_off c) off then YP09.mkChunk (YP09.c_off c) (CVal w v') else c
| _ => c
end.
Definition gen_region (b : option nat) (lo off : Z) (v' : sv) (r : YP09.region) : YP09.region :=
if (YP09.obase_eqb (YP09.r_base r) b && Z.eqb (YP09.r_lo r) lo)%bool
then YP09.mkRegion (YP09.r_base r) (YP09.r_lo r) (YP09.r_hi r) (YP09.r_wlo r) (YP09.r_whi r) (map (gen_chunk off v') (YP09.r_chunks r))
else r.
Definition ss_gen_slot (ss : sstate) (b : option nat) (lo off : Z) (v' : sv) : sstate :=
mkSS (ss_pc ss) (ss_regs ss) (map (gen_region b lo off v') (ss_mem ss)) (ss_resv ss) (ss_facts ss).
Definition slot_vals (b : option nat) (lo off : Z) (rs : smem) : list sv :=
flat_map (fun r => if (YP09.obase_eqb (YP09.r_base r) b && Z.eqb (YP09.r_lo r) lo)%bool
then flat_map (fun c => match YP09.c_val c with CVal _ v => if Z.eqb (YP09.c_off c) off then [v] else [] | _ => [] end) (YP09.r_chunks r)
else []) rs.
Section a. Context {fx : YK11.FPState}.
Context {SK : YI16.sink_head}.
Lemma gen_region_extent : forall b lo off v' r, YP09.extent_of (gen_region b lo off v' r) = YP09.extent_of r.
Proof. intros b lo off v' r. unfold gen_region. destruct (_ && _)%bool; reflexivity. Qed.
Lemma st_ok_gen_slot : forall segs E ss ms b lo off v',
st_ok segs E ss ms ->
Forall (fun v => sv_denot E v' = sv_denot E v) (slot_vals b lo off (ss_mem ss)) ->
YP09.regions_wf (map (gen_region b lo off v') (ss_mem ss)) = true ->
st_ok segs E (ss_gen_slot ss b lo off v') ms.
Proof.
intros segs E ss ms b lo off v' (H1 & H2 & H3 & H4 & H5 & H6 & H7 & (Hwf & Hro & Hpd) & H9) Hv Hwf'.
unfold st_ok, ss_gen_slot; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts]. repeat (split; [assumption|]). split; [|exact H9].
split; [exact Hwf'|]. split.
- clear Hwf Hpd Hwf'. revert Hv. induction Hro as [|r rs Hr Hrs IH]; intros Hv; [constructor|].
cbn [map]. cbn [slot_vals flat_map] in Hv. apply Forall_app in Hv as [Hv1 Hv2]. constructor; [|exact (IH Hv2)].
unfold gen_region. destruct (YP09.obase_eqb (YP09.r_base r) b && (YP09.r_lo r =? lo))%bool; [|exact Hr].
destruct Hr as (Hb0 & Hb1 & Hw & Hcs). unfold YP09.region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
split; [exact Hb0|]. split; [exact Hb1|]. split; [exact Hw|].
clear Hb0 Hb1 Hw Hv2 IH. revert Hv1. induction Hcs as [|c cs Hc Hcs IHc]; intros Hv1; [constructor|].
cbn [map]. cbn [flat_map] in Hv1. apply Forall_app in Hv1 as [Hc1 Hc2]. constructor; [|exact (IHc Hc2)].
unfold gen_chunk. destruct (YP09.c_val c) as [w v| | |] eqn:Ecv; try exact Hc.
destruct (YP09.c_off c =? off) eqn:Eo; [|exact Hc].
inversion Hc1 as [|? ? Hvv _]; subst.
unfold YP09.chunk_ok in *. cbn [YP09.c_off YP09.c_val YP09.c_len YP09.cv_len]. unfold YP09.c_len in Hc. rewrite Ecv in Hc. cbn [YP09.cv_len] in Hc.
intros i Hi. destruct (Hc i Hi) as (bb & Hb & Hm). exists bb. split; [|exact Hm].
cbn [YP09.cbyte] in Hb |- *. rewrite Hvv. exact Hb.
- apply (YP09.pairwise_disjoint_extents E (ss_mem ss)); [|exact Hpd].
rewrite map_map. apply map_ext. intros r. symmetry. apply gen_region_extent.
Qed.
Section d. Context {rc : YM05.RunCeil} {PI : PAImg lib_asan3_1_listing}.
Lemma st_ok_pi_gen_slot : forall E ss ms b lo off v',
st_ok_pi (@pa_segs _ lib_asan3_1_listing PI) (@pa_val _ lib_asan3_1_listing PI) E ss ms ->
Forall (fun v => sv_denot E v' = sv_denot E v) (slot_vals b lo off (ss_mem ss)) ->
YP09.regions_wf (map (gen_region b lo off v') (ss_mem ss)) = true ->
st_ok_pi (@pa_segs _ lib_asan3_1_listing PI) (@pa_val _ lib_asan3_1_listing PI) E (ss_gen_slot ss b lo off v') ms.
Proof. intros E ss ms b lo off v' HS; destruct ss as [p0 r0 f0 m0 q0 g0]; intros; eapply (st_ok_gen_slot _ E _ ms b lo off v' HS); eassumption. Qed.
End d.
End a.
Ltac ra_join_slot HS target N deads b lo off hook :=
norm_ss HS;
let tg := eval red in target in
pi_park_deads HS N deads;
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let dl := eval cbv in deads in
let sv0 := eval vm_compute in (hd (SLit 0) (slot_vals b lo off (ss_mem ssx))) in
let vals := constr:(map (fun r : bv 5 => getr (ms_regs msx) r) dl ++ [sv_denot Ex sv0]) in
let vals' := eval cbn [map app ms_regs restrict] in vals in
pose proof (st_ok_pi_havoc_hi N Ex ssx msx vals' HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS;
set_regs_rec HS N vals' 0%nat dl;
norm_ss HS;
lazymatch type of HS with st_ok_pi _ _ ?Ey ?ssy ?msy =>
let HS4 := fresh "HS4" in
let n := eval vm_compute in (N + length dl)%nat in
let i := eval vm_compute in (length dl) in
pose proof (st_ok_pi_gen_slot Ey ssy msy b lo off (SOff n 0) HS
ltac:(let l := eval vm_compute in (slot_vals b lo off (ss_mem ssy)) in change (slot_vals b lo off (ss_mem ssy)) with l;
constructor; [|constructor];
rewrite (sv_denot_agree N Ex Ey sv0 (env_agree_havoc_ge N N Ex Ex vals' ltac:(lia) (env_agree_refl N Ex)) ltac:(vm_compute; reflexivity));
cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; change n with (N + i)%nat;
rewrite (ew_havoc_new _ N vals' i (Z_to_bv 64 0)) by (cbn [length]; lia); cbn [nth]; reflexivity)
ltac:(vm_compute; reflexivity)) as HS4;
clear HS; rename HS4 into HS end | st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let dl := eval cbv in deads in
let sv0 := eval vm_compute in (hd (SLit 0) (slot_vals b lo off (ss_mem ssx))) in
let vals := constr:(map (fun r : bv 5 => getr (ms_regs msx) r) dl ++ [sv_denot Ex sv0]) in
let vals' := eval cbn [map app ms_regs restrict] in vals in
pose proof (st_ok_havoc _ N Ex ssx msx vals' HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS;
set_regs_rec HS N vals' 0%nat dl;
norm_ss HS;
lazymatch type of HS with st_ok _ ?Ey ?ssy ?msy =>
let HS4 := fresh "HS4" in
let n := eval vm_compute in (N + length dl)%nat in
let i := eval vm_compute in (length dl) in
pose proof (st_ok_gen_slot _ Ey ssy msy b lo off (SOff n 0) HS
ltac:(let l := eval vm_compute in (slot_vals b lo off (ss_mem ssy)) in change (slot_vals b lo off (ss_mem ssy)) with l;
constructor; [|constructor];
rewrite (sv_denot_agree N Ex Ey sv0 (env_agree_havoc_ge N N Ex Ex vals' ltac:(lia) (env_agree_refl N Ex)) ltac:(vm_compute; reflexivity));
cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; change n with (N + i)%nat;
rewrite (ew_havoc_new _ N vals' i (Z_to_bv 64 0)) by (cbn [length]; lia); cbn [nth]; reflexivity)
ltac:(vm_compute; reflexivity)) as HS4;
clear HS; rename HS4 into HS end  end;
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let v := eval vm_compute in ssx in change ssx with v in HS | st_ok _ ?Ex ?ssx ?msx =>
let v := eval vm_compute in ssx in change ssx with v in HS  end;
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let rs := eval cbn [ss_mem] in (ss_mem tg) in
pose proof (st_ok_pi_submem Ex ssx msx rs HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let rs := eval cbn [ss_mem] in (ss_mem tg) in
pose proof (st_ok_submem _ Ex ssx msx rs HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS  end;
norm_ss HS;
hook;
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let fa := eval cbn [ss_facts f_atoms] in (f_atoms (ss_facts tg)) in
let cs := eval cbn [ss_facts f_conds] in (f_conds (ss_facts tg)) in
let al := eval cbn [ss_facts f_alias] in (f_alias (ss_facts tg)) in
pose proof (st_ok_pi_facts_incl3 Ex ssx msx fa cs al HS ltac:(incl_lit_tac) ltac:(incl_lit_tac) ltac:(incl_lit_tac)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let fa := eval cbn [ss_facts f_atoms] in (f_atoms (ss_facts tg)) in
let cs := eval cbn [ss_facts f_conds] in (f_conds (ss_facts tg)) in
let al := eval cbn [ss_facts f_alias] in (f_alias (ss_facts tg)) in
pose proof (st_ok_facts_incl3 _ Ex ssx msx fa cs al HS ltac:(incl_lit_tac) ltac:(incl_lit_tac) ltac:(incl_lit_tac)) as HS3;
clear HS; rename HS3 into HS  end;
norm_ss HS;
lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ => first [change ssx with target in HS | idtac "JOIN-MISMATCH" ssx tg] | st_ok _ _ ?ssx _ => first [change ssx with target in HS | idtac "JOIN-MISMATCH" ssx tg]  end.
Ltac slot_val HS b lo off v tac H :=
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx _ =>
let sv0 := eval vm_compute in (hd (SLit 0) (slot_vals b lo off (ss_mem ssx))) in
assert (H : sv_denot Ev sv0 = v) by tac | st_ok _ ?Ev ?ssx _ =>
let sv0 := eval vm_compute in (hd (SLit 0) (slot_vals b lo off (ss_mem ssx))) in
assert (H : sv_denot Ev sv0 = v) by tac  end.
Ltac slot_words Ex ssx slots :=
lazymatch slots with
| [] => constr:(@nil word)
| (?b, ?lo, ?off) :: ?tl =>
let sv0 := eval vm_compute in (hd (SLit 0) (slot_vals b lo off (ss_mem ssx))) in
let rest := slot_words Ex ssx tl in
constr:(sv_denot Ex sv0 :: rest)
end.
Ltac gen_slots_rec HS N Ex vals i slots :=
lazymatch slots with
| [] => idtac
| (?b, ?lo, ?off) :: ?tl =>
lazymatch type of HS with st_ok_pi _ _ ?Ey ?ssy ?msy =>
let HS4 := fresh "HS4" in
let n := eval vm_compute in (N + i)%nat in
let l := eval vm_compute in (slot_vals b lo off (ss_mem ssy)) in
lazymatch l with
| [?sv0] =>
pose proof (st_ok_pi_gen_slot Ey ssy msy b lo off (SOff n 0) HS
ltac:(change (slot_vals b lo off (ss_mem ssy)) with l;
constructor; [|constructor];
rewrite (sv_denot_agree N Ex Ey sv0 (env_agree_havoc_ge N N Ex Ex vals ltac:(lia) (env_agree_refl N Ex)) ltac:(vm_compute; reflexivity));
cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; change n with (N + i)%nat;
rewrite (ew_havoc_new _ N vals i (Z_to_bv 64 0)) by (cbn [length]; lia); cbn [nth]; reflexivity)
ltac:(vm_compute; reflexivity)) as HS4;
clear HS; rename HS4 into HS;
lazymatch type of HS with st_ok_pi _ _ _ ?ssz _ => let v := eval vm_compute in ssz in change ssz with v in HS end;
gen_slots_rec HS N Ex vals (S i) tl
end | st_ok _ ?Ey ?ssy ?msy =>
let HS4 := fresh "HS4" in
let n := eval vm_compute in (N + i)%nat in
let l := eval vm_compute in (slot_vals b lo off (ss_mem ssy)) in
lazymatch l with
| [?sv0] =>
pose proof (st_ok_gen_slot _ Ey ssy msy b lo off (SOff n 0) HS
ltac:(change (slot_vals b lo off (ss_mem ssy)) with l;
constructor; [|constructor];
rewrite (sv_denot_agree N Ex Ey sv0 (env_agree_havoc_ge N N Ex Ex vals ltac:(lia) (env_agree_refl N Ex)) ltac:(vm_compute; reflexivity));
cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; change n with (N + i)%nat;
rewrite (ew_havoc_new _ N vals i (Z_to_bv 64 0)) by (cbn [length]; lia); cbn [nth]; reflexivity)
ltac:(vm_compute; reflexivity)) as HS4;
clear HS; rename HS4 into HS;
lazymatch type of HS with st_ok _ _ ?ssz _ => let v := eval vm_compute in ssz in change ssz with v in HS end;
gen_slots_rec HS N Ex vals (S i) tl
end  end
end.
Ltac ra_join_slots HS target N deads slots hook :=
norm_ss HS;
let tg := eval red in target in
pi_park_deads HS N deads;
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let dl := eval cbv in deads in
let sw := slot_words Ex ssx slots in
let vals := constr:(map (fun r : bv 5 => getr (ms_regs msx) r) dl ++ sw) in
let vals' := eval cbn [map app ms_regs restrict] in vals in
pose proof (st_ok_pi_havoc_hi N Ex ssx msx vals' HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS;
set_regs_rec HS N vals' 0%nat dl;
norm_ss HS;
let i0 := eval vm_compute in (length dl) in
gen_slots_rec HS N Ex vals' i0 slots | st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let dl := eval cbv in deads in
let sw := slot_words Ex ssx slots in
let vals := constr:(map (fun r : bv 5 => getr (ms_regs msx) r) dl ++ sw) in
let vals' := eval cbn [map app ms_regs restrict] in vals in
pose proof (st_ok_havoc _ N Ex ssx msx vals' HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS;
set_regs_rec HS N vals' 0%nat dl;
norm_ss HS;
let i0 := eval vm_compute in (length dl) in
gen_slots_rec HS N Ex vals' i0 slots  end;
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let rs := eval cbn [ss_mem] in (ss_mem tg) in
pose proof (st_ok_pi_submem Ex ssx msx rs HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let rs := eval cbn [ss_mem] in (ss_mem tg) in
pose proof (st_ok_submem _ Ex ssx msx rs HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS  end;
norm_ss HS;
hook;
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let fa := eval cbn [ss_facts f_atoms] in (f_atoms (ss_facts tg)) in
let cs := eval cbn [ss_facts f_conds] in (f_conds (ss_facts tg)) in
let al := eval cbn [ss_facts f_alias] in (f_alias (ss_facts tg)) in
pose proof (st_ok_pi_facts_incl3 Ex ssx msx fa cs al HS ltac:(incl_lit_tac) ltac:(incl_lit_tac) ltac:(incl_lit_tac)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let fa := eval cbn [ss_facts f_atoms] in (f_atoms (ss_facts tg)) in
let cs := eval cbn [ss_facts f_conds] in (f_conds (ss_facts tg)) in
let al := eval cbn [ss_facts f_alias] in (f_alias (ss_facts tg)) in
pose proof (st_ok_facts_incl3 _ Ex ssx msx fa cs al HS ltac:(incl_lit_tac) ltac:(incl_lit_tac) ltac:(incl_lit_tac)) as HS3;
clear HS; rename HS3 into HS  end;
norm_ss HS;
lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ => first [change ssx with target in HS | idtac "JOIN-MISMATCH" ssx tg] | st_ok _ _ ?ssx _ => first [change ssx with target in HS | idtac "JOIN-MISMATCH" ssx tg]  end.
