(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI01 YI04 YI06 YC2v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YF8z YC1d YC1a YC2o YC10 YC2p YC0x YC1b YC3g YC2u YC4o YC4q YC46 YC4g YC4c YC4h.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Definition gen_chunk (off : Z) (v' : sv) (c : YQ0b.chunk) : YQ0b.chunk :=
match YQ0b.c_val c with
| CVal w _ => if Z.eqb (YQ0b.c_off c) off then YQ0b.mkChunk (YQ0b.c_off c) (CVal w v') else c
| _ => c
end.
Definition gen_region (b : option nat) (lo off : Z) (v' : sv) (r : YQ0b.region) : YQ0b.region :=
if (YQ0b.obase_eqb (YQ0b.r_base r) b && Z.eqb (YQ0b.r_lo r) lo)%bool
then YQ0b.mkRegion (YQ0b.r_base r) (YQ0b.r_lo r) (YQ0b.r_hi r) (YQ0b.r_wlo r) (YQ0b.r_whi r) (map (gen_chunk off v') (YQ0b.r_chunks r))
else r.
Definition ss_gen_slot (ss : sstate) (b : option nat) (lo off : Z) (v' : sv) : sstate :=
mkSS (ss_pc ss) (ss_regs ss) (map (gen_region b lo off v') (ss_mem ss)) (ss_resv ss) (ss_facts ss).
Definition slot_vals (b : option nat) (lo off : Z) (rs : smem) : list sv :=
flat_map (fun r => if (YQ0b.obase_eqb (YQ0b.r_base r) b && Z.eqb (YQ0b.r_lo r) lo)%bool
then flat_map (fun c => match YQ0b.c_val c with CVal _ v => if Z.eqb (YQ0b.c_off c) off then [v] else [] | _ => [] end) (YQ0b.r_chunks r)
else []) rs.
Section a. Context {fx : YK11.FPState}.
Lemma gen_region_extent : forall b lo off v' r, YQ0b.extent_of (gen_region b lo off v' r) = YQ0b.extent_of r.
Proof. intros b lo off v' r. unfold gen_region. destruct (_ && _)%bool; reflexivity. Qed.
Lemma st_ok_gen_slot : forall segs E ss ms b lo off v',
st_ok segs E ss ms ->
Forall (fun v => sv_denot E v' = sv_denot E v) (slot_vals b lo off (ss_mem ss)) ->
YQ0b.regions_wf (map (gen_region b lo off v') (ss_mem ss)) = true ->
st_ok segs E (ss_gen_slot ss b lo off v') ms.
Proof.
intros segs E ss ms b lo off v' (H1 & H2 & H3 & H4 & H5 & H6 & H7 & (Hwf & Hro & Hpd) & H9) Hv Hwf'.
unfold st_ok, ss_gen_slot; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts]. repeat (split; [assumption|]). split; [|exact H9].
split; [exact Hwf'|]. split.
- clear Hwf Hpd Hwf'. revert Hv. induction Hro as [|r rs Hr Hrs IH]; intros Hv; [constructor|].
cbn [map]. cbn [slot_vals flat_map] in Hv. apply Forall_app in Hv as [Hv1 Hv2]. constructor; [|exact (IH Hv2)].
unfold gen_region. destruct (YQ0b.obase_eqb (YQ0b.r_base r) b && (YQ0b.r_lo r =? lo))%bool; [|exact Hr].
destruct Hr as (Hb0 & Hb1 & Hw & Hcs). unfold YQ0b.region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks].
split; [exact Hb0|]. split; [exact Hb1|]. split; [exact Hw|].
clear Hb0 Hb1 Hw Hv2 IH. revert Hv1. induction Hcs as [|c cs Hc Hcs IHc]; intros Hv1; [constructor|].
cbn [map]. cbn [flat_map] in Hv1. apply Forall_app in Hv1 as [Hc1 Hc2]. constructor; [|exact (IHc Hc2)].
unfold gen_chunk. destruct (YQ0b.c_val c) as [w v| | |] eqn:Ecv; try exact Hc.
destruct (YQ0b.c_off c =? off) eqn:Eo; [|exact Hc].
inversion Hc1 as [|? ? Hvv _]; subst.
unfold YQ0b.chunk_ok in *. cbn [YQ0b.c_off YQ0b.c_val YQ0b.c_len YQ0b.cv_len]. unfold YQ0b.c_len in Hc. rewrite Ecv in Hc. cbn [YQ0b.cv_len] in Hc.
intros i Hi. destruct (Hc i Hi) as (bb & Hb & Hm). exists bb. split; [|exact Hm].
cbn [YQ0b.cbyte] in Hb |- *. rewrite Hvv. exact Hb.
- apply (YQ0b.pairwise_disjoint_extents E (ss_mem ss)); [|exact Hpd].
rewrite map_map. apply map_ext. intros r. symmetry. apply gen_region_extent.
Qed.
End a.
Ltac ra_join_slot HS target N deads b lo off hook :=
norm_ss HS;
let tg := eval red in target in
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let dl := eval cbv in deads in
let sv0 := eval vm_compute in (hd (SLit 0) (slot_vals b lo off (ss_mem ssx))) in
let vals := constr:(map (fun r : bv 5 => getr (ms_regs msx) r) dl ++ [sv_denot Ex sv0]) in
let vals' := eval cbn [map app ms_regs restrict] in vals in
pose proof (st_ok_havoc trasegs N Ex ssx msx vals' HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS;
set_regs_rec HS N vals' 0%nat dl;
norm_ss HS;
lazymatch type of HS with st_ok _ ?Ey ?ssy ?msy =>
let HS4 := fresh "HS4" in
let n := eval vm_compute in (N + length dl)%nat in
let i := eval vm_compute in (length dl) in
pose proof (st_ok_gen_slot trasegs Ey ssy msy b lo off (SOff n 0) HS
ltac:(let l := eval vm_compute in (slot_vals b lo off (ss_mem ssy)) in change (slot_vals b lo off (ss_mem ssy)) with l;
constructor; [|constructor];
rewrite (sv_denot_agree N Ex Ey sv0 (env_agree_havoc_ge N N Ex Ex vals' ltac:(lia) (env_agree_refl N Ex)) ltac:(vm_compute; reflexivity));
cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; change n with (N + i)%nat;
rewrite (ew_havoc_new _ N vals' i (Z_to_bv 64 0)) by (cbn [length]; lia); cbn [nth]; reflexivity)
ltac:(vm_compute; reflexivity)) as HS4;
clear HS; rename HS4 into HS end end;
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let v := eval vm_compute in ssx in change ssx with v in HS end;
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let rs := eval cbn [ss_mem] in (ss_mem tg) in
pose proof (st_ok_submem trasegs Ex ssx msx rs HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS end;
norm_ss HS;
hook;
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let fa := eval cbn [ss_facts f_atoms] in (f_atoms (ss_facts tg)) in
let cs := eval cbn [ss_facts f_conds] in (f_conds (ss_facts tg)) in
let al := eval cbn [ss_facts f_alias] in (f_alias (ss_facts tg)) in
pose proof (st_ok_facts_incl3 trasegs Ex ssx msx fa cs al HS ltac:(incl_lit_tac) ltac:(incl_lit_tac) ltac:(incl_lit_tac)) as HS3;
clear HS; rename HS3 into HS end;
norm_ss HS;
lazymatch type of HS with st_ok _ _ ?ssx _ => first [change ssx with target in HS | idtac "JOIN-MISMATCH" ssx tg] end.
Ltac slot_val HS b lo off v tac H :=
lazymatch type of HS with st_ok _ ?Ev ?ssx _ =>
let sv0 := eval vm_compute in (hd (SLit 0) (slot_vals b lo off (ss_mem ssx))) in
assert (H : sv_denot Ev sv0 = v) by tac end.
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
lazymatch type of HS with st_ok _ ?Ey ?ssy ?msy =>
let HS4 := fresh "HS4" in
let n := eval vm_compute in (N + i)%nat in
let l := eval vm_compute in (slot_vals b lo off (ss_mem ssy)) in
lazymatch l with
| [?sv0] =>
pose proof (st_ok_gen_slot trasegs Ey ssy msy b lo off (SOff n 0) HS
ltac:(change (slot_vals b lo off (ss_mem ssy)) with l;
constructor; [|constructor];
rewrite (sv_denot_agree N Ex Ey sv0 (env_agree_havoc_ge N N Ex Ex vals ltac:(lia) (env_agree_refl N Ex)) ltac:(vm_compute; reflexivity));
cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; change n with (N + i)%nat;
rewrite (ew_havoc_new _ N vals i (Z_to_bv 64 0)) by (cbn [length]; lia); cbn [nth]; reflexivity)
ltac:(vm_compute; reflexivity)) as HS4;
clear HS; rename HS4 into HS;
lazymatch type of HS with st_ok _ _ ?ssz _ => let v := eval vm_compute in ssz in change ssz with v in HS end;
gen_slots_rec HS N Ex vals (S i) tl
end end
end.
Ltac ra_join_slots HS target N deads slots hook :=
norm_ss HS;
let tg := eval red in target in
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let dl := eval cbv in deads in
let sw := slot_words Ex ssx slots in
let vals := constr:(map (fun r : bv 5 => getr (ms_regs msx) r) dl ++ sw) in
let vals' := eval cbn [map app ms_regs restrict] in vals in
pose proof (st_ok_havoc trasegs N Ex ssx msx vals' HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS;
set_regs_rec HS N vals' 0%nat dl;
norm_ss HS;
let i0 := eval vm_compute in (length dl) in
gen_slots_rec HS N Ex vals' i0 slots end;
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let rs := eval cbn [ss_mem] in (ss_mem tg) in
pose proof (st_ok_submem trasegs Ex ssx msx rs HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS end;
norm_ss HS;
hook;
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let fa := eval cbn [ss_facts f_atoms] in (f_atoms (ss_facts tg)) in
let cs := eval cbn [ss_facts f_conds] in (f_conds (ss_facts tg)) in
let al := eval cbn [ss_facts f_alias] in (f_alias (ss_facts tg)) in
pose proof (st_ok_facts_incl3 trasegs Ex ssx msx fa cs al HS ltac:(incl_lit_tac) ltac:(incl_lit_tac) ltac:(incl_lit_tac)) as HS3;
clear HS; rename HS3 into HS end;
norm_ss HS;
lazymatch type of HS with st_ok _ _ ?ssx _ => first [change ssx with target in HS | idtac "JOIN-MISMATCH" ssx tg] end.
