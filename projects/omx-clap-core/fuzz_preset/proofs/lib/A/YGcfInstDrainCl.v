(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/YGcfInstDrainCl.v (commit 67deba317dfb, blob 650c6dc7d370) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb); module paths changed; 0 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0s YK0i YP09 YO0d YK08 YP03.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YI04 YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YGcfTok YG03cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfXs ImgBase YG0h YG08cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfInstDrainR.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YK0g.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require YGcfInstDrainCg.
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section U. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {IM : AImg}.
Variable B : asyms.

Lemma sec_extents_sizes_R : forall U pp cc bb ly s, WfR_cf U pp cc bb s ->
Forall (fun e => 4096 <= snd e < 2 ^ 64) (sec_extents ly s).
Proof.
intros U pp cc bb ly s W. pose proof (wfr_chunks _ _ _ _ _ W) as CK. unfold sec_extents. apply Forall_forall. intros e He.
apply in_flat_map in He as (k & Hk & He). pose proof (proj1 (Forall_forall _ _) CK k Hk) as [Hn _].
destruct (ck_beg k) as [|o|r o|c p]; try destruct He as [<-|[]]; try destruct He. cbn [snd].
pose proof (sec_map_size_page (ck_req k) ltac:(lia)). pose proof (cf_sizes_ok (ck_req k) Hn). pose proof cf_nob_ok.
unfold kPage in *. lia.
Qed.

Lemma nohole_R : forall U pp cc bb ly s a, WfR_cf U pp cc bb s -> ~ prim_hole_at ly s a.
Proof.
intros U pp cc bb ly s a W (c' & h & Hc' & Hh & Ha). pose proof (wfr_classes _ _ _ _ _ W c' Hc') as CL.
pose proof (wrc_holes _ _ _ _ _ _ CL) as [HH _]. rewrite (proj1 (Forall_forall _ _) HH h Hh) in Ha.
unfold in_zr in Ha. cbn [fst snd] in Ha. lia.
Qed.

Lemma ALedger_cf_grant : forall ly X c md md2,
layout_ok ly -> WfR_cf (as_universe B) 0 0 0 X -> 1 <= c <= 30 ->
rg_mapped_fa (reg X c) + kFreeArrayMapSize <= kFreeArrayMax ->
(Z.to_nat c < length (st_regions X))%nat ->
ALedger_cf im_segs ly X md ->
vm_maps (m_vmmaps md2) = vm_maps (m_vmmaps md) -> vm_reserved (m_vmmaps md2) = vm_reserved (m_vmmaps md) ->
vm_limit (m_vmmaps md2) = vm_limit (m_vmmaps md) -> alloc_top (m_vmmaps md2) = alloc_top (m_vmmaps md) ->
(forall lo n, region_free (vm_noaccess (m_vmmaps md)) lo n = true -> region_free (vm_noaccess (m_vmmaps md2)) lo n = true) ->
sec_placed ly X -> xs_placed_cf ly X ->
(forall x, ~ (fa_base ly c + rg_mapped_fa (reg X c) <= x < fa_base ly c + rg_mapped_fa (reg X c) + kUserMapSize) ->
  YK0g.covered (vm_noaccess (m_vmmaps md2) ++ m_vm_lazy md2) x = YK0g.covered (vm_noaccess (m_vmmaps md) ++ m_vm_lazy md) x) ->
eager_used md2 <= eager_used md + kUserMapSize ->
ALedger_cf im_segs ly (YGcfInstDrainCg.cgX X c) md2.
Proof.
intros ly X c md md2 LO W Hc Hmax Hlenr L VM RES LIM TOP NAF PL XP COV EG.
set (X' := YGcfInstDrainCg.cgX X c).
assert (SE : sec_extents ly X' = sec_extents ly X) by reflexivity.
assert (EZ : errb_zone ly X' = errb_zone ly X) by reflexivity.
assert (EC : errb_cap_cf X' = errb_cap_cf X) by reflexivity.
assert (SR : st_sec_reserved X' = st_sec_reserved X) by reflexivity.
assert (PC : prim_committed X' = prim_committed X + kFreeArrayMapSize) by (apply YGcfInstDrainCg.cg_prim_committed; assumption).
assert (MONO1 : forall c', 1 <= c' <= 31 -> rg_mapped_user (reg X c') <= rg_mapped_user (reg X' c') /\
  rg_mapped_fa (reg X c') <= rg_mapped_fa (reg X' c')).
{ intros c' Hc'. destruct (Z.eq_dec c' c) as [->|Hne].
  - unfold X'. rewrite YGcfInstDrainCg.cg_reg_c by assumption. unfold YGcfInstDrainCg.cgr. cbn [rg_mapped_user rg_mapped_fa].
    unfold kFreeArrayMapSize. lia.
  - unfold X'. rewrite YGcfInstDrainCg.cg_reg_other by (assumption || lia). lia. }
assert (NOH : forall a, ~ prim_hole_at ly X' a).
{ intros a (c' & h & Hc' & Hh & Ha).
  assert (Hh0 : In h (rg_holes (reg X c'))).
  { destruct (Z.eq_dec c' c) as [->|Hne].
    - unfold X' in Hh. rewrite YGcfInstDrainCg.cg_reg_c in Hh by assumption. unfold YGcfInstDrainCg.cgr, del_hole in Hh.
      cbn [rg_holes] in Hh. apply filter_In in Hh. exact (proj1 Hh).
    - unfold X' in Hh. rewrite YGcfInstDrainCg.cg_reg_other in Hh by (assumption || lia). exact Hh. }
  apply (nohole_R _ _ _ _ ly X a W). exists c', h. split; [exact Hc'|]. split; [exact Hh0 | exact Ha]. }

assert (SLOT : ly_prim ly <= fa_base ly c + rg_mapped_fa (reg X c) /\
  fa_base ly c + rg_mapped_fa (reg X c) + kUserMapSize <= ly_prim ly + kPrimResvSize).
{ pose proof (wfr_classes _ _ _ _ _ W c ltac:(lia)) as CL.
  pose proof (wrc_fa _ _ _ _ _ _ CL) as [F1 F2]. pose proof (wrc_fa_bound _ _ _ _ _ _ CL) as F3.
  pose proof (region_in_prim ly c LO ltac:(lia)) as (R1 & R2 & _ & R4 & _).
  unfold fa_base, region_base in *. unfold kFreeArrayOffset, kFreeArrayMax, kUserMapSize, kFreeArrayMapSize in *. lia. }

assert (XSA : forall z, In z (errb_zone ly X) -> zdisjoint z (ly_prim ly, kPrimResvSize) /\ 0 <= fst z /\
  fst z + snd z <= alloc_ceiling /\ 0 <= snd z).
{ intros z Hz. unfold errb_zone in Hz. pose proof (proj1 (Forall_forall _ _) XP z Hz) as (P1 & [P2a P2b] & P3 & P4).
  assert (SZ0 : 0 <= snd z).
  { unfold xs_cf in Hz. destruct (last_cap_idx (st_secs X) 0 None); [|destruct Hz].
    destruct Hz as [<-|[]]. cbn [snd]. apply errb_cap_cf_nonneg. }
  split; [|lia]. apply (proj1 (Forall_forall _ _) P4). apply in_app_iff. right. apply in_app_iff. left.
  unfold static_extents, owned_extents. cbn. tauto. }
assert (ESX : esec (vm_noaccess (m_vmmaps md2)) (m_vm_lazy md2) (sec_extents ly X ++ errb_zone ly X) =
  esec (vm_noaccess (m_vmmaps md)) (m_vm_lazy md) (sec_extents ly X ++ errb_zone ly X)).
{ destruct PL as [PF PD]. pose proof (sec_extents_sizes_R _ _ _ _ ly X W) as SZ. apply esec_ext.
  - apply Forall_forall. intros e He. pose proof alloc_ceiling_lt as AC. change (2 ^ 47) with 140737488355328 in AC.
    apply in_app_iff in He as [He|He].
    + pose proof (proj1 (Forall_forall _ _) PF e He) as (_ & [H1 H2] & H3).
      pose proof (proj1 (Forall_forall _ _) SZ e He) as H4. cbn beta in H4. lia.
    + destruct (XSA e He) as (_ & Z1 & Z2 & Z3). lia.
  - intros e x He Hx. apply COV. apply in_app_iff in He as [He|He].
    + pose proof (pairwise_In zdisjoint _ e (ly_prim ly, kPrimResvSize) (sec_extents ly X) (static_extents ly) eq_refl PD He
        ltac:(unfold static_extents, owned_extents; cbn; tauto)) as D.
      unfold zdisjoint in D. cbn [fst snd] in D. lia.
    + destruct (XSA e He) as (D & _). unfold zdisjoint in D. cbn [fst snd] in D. lia. }
assert (U64 : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (YG0n.w64 z) = z).
{ intros z Hz. unfold YG0n.w64. rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity|]. unfold bv_modulus. lia. }
destruct L as [L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12 L13 L14 L15 L16 L17].
unfold eager_cf in L9.
constructor; try unfold eager_cf; rewrite ?VM, ?RES, ?LIM, ?TOP, ?SE, ?EZ, ?EC, ?SR, ?PC, ?ESX; try assumption.
- destruct L4 as (pieces & (P1 & P2 & P3) & P4). exists pieces. split; [split; [|split; [exact P2|]]|].
  + eapply Forall_impl; [|exact P1]. intros p (A & B0 & C0). split; [exact A|].
    split; apply (YG0h.cut_ok_mono ly X X' MONO1); assumption.
  + intros a Ha. rewrite (P3 a Ha). split; intros _; [apply NOH | apply (nohole_R _ _ _ _ ly X a W)].
  + exact P4.
- unfold kFreeArrayMapSize, kUserMapSize in *. lia.
- destruct L15 as [N1 N2]. split; apply NAF; assumption.
-
  intros x Hx. assert (DEC : (fa_base ly c + rg_mapped_fa (reg X c) <= x < fa_base ly c + rg_mapped_fa (reg X c) + kUserMapSize) \/
    ~ (fa_base ly c + rg_mapped_fa (reg X c) <= x < fa_base ly c + rg_mapped_fa (reg X c) + kUserMapSize)) by lia.
  destruct DEC as [Hin|Hout].
  + destruct L4 as (pieces & (P1 & P2 & P3) & P4).
    pose proof (proj2 (P3 x ltac:(lia)) (nohole_R _ _ _ _ ly X x W)) as EX.
    apply Exists_exists in EX as (p & Hpp & Hzr). unfold in_zr in Hzr.
    destruct (proj1 (P4 p) Hpp) as (Hm & Hpos & B1 & B2).
    pose proof (lo_high _ LO) as IP. unfold in_high in IP. cbn [fst snd] in IP. pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR.
    unfold YK0g.covered. apply existsb_exists. exists (wiv p). split; [exact Hm|].
    unfold YK0g.in_iv, YK0g.in_rng, YK0g.B, YK0g.S, wiv. cbn [fst snd].
    rewrite !U64 by (unfold ASAN_CEIL, kHighMemBeg in *; lia).
    apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
  + rewrite (COV x Hout) in Hx. exact (L16 x Hx).
Qed.
End U.
