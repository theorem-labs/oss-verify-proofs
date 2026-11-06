(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk pcs are fuzz_state.asan's: the __asan_memset pcs move with the function by +0x744 (cgif 0x51a78 -> 0x521bc), and the return into __asan_region_is_poisoned after its mem_is_zero call is 0x54d58 (cgif 0x542cc). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/AE6t.v; 1494 of its 2186 lines of code are new or changed and 358 lines of the source are left out. *)
(* fuzz_state image A: __asan_memset (0x521bc) under the ANY-USER-POISON invariant ARU (lib/A/FSupoison.v:34), for ANY
   set U of user-poisoned ranges: FSupoisonU.aintrin_realizesU tfibsegs B OSet FSH_Base.PC_memset (lib/A/FSupoisonU.v:244).
   RULE 24 LINE: proves function __asan_memset (fs image A 0x521bc, image B 0x5222c). Reuse search:
   `proof-index __asan_memset 0x521bc 0x5222c` unpiped (2026-10-29 10:39Z), last line:
   `proof-index: end; __asan_memset: 0 named, 1339 by address, 25 related, 0 released lemma(s), ...; 0x521bc: 0
   named, 0 by address, ... 0 released lemma(s) ...; 0x5222c: 0 named, 0 by address, ... 0 released lemma(s) ...`
   (the 1339 by-address hits are other units' images; the unreleased fs hits are S0's own U = [] AR walks, the
   templates below). Second-agent check a Theorem Labs lane (a Theorem Labs lane's r24/1029/asanmc-check.md): Verdict: CONFIRM (no head
   proves a U-form at 0x521bc; the ARU memset at 0x51d18 is the __wrap_memset interceptor, walk AE79, not this one).

   Templates. The walk is S0's U = [] proof lib/A/AE2r.v:567 asan_memset_realizes (AE6t -> AE6u -> AE6v -> AE2r), ported
   to ARU. Primary template: a working branch 53ce9e4138c lib/A/FSupoisonAsanC.v (the sibling
   __asan_memcpy walk AE6k .. AE2q over ARU, the same AE-walk lineage; memset has ONE range, the destination); method
   as in a working branch cd7610bc4ed lib/A/FSupoisonIntrinS.v (the interceptor memset walk AE79 over ARU).
   Both are read with git show, not merged, not imported (neither is in S0). Code text unchanged except where U is
   threaded:
     AE6t.v:347-534  ms_tail  -> ms_tailU: the one step that consumes AR. Its post closes with FSupoison.ARU_frame /
                     ARU_stack (lib/A/FSupoison.v:155,168) instead of al_frame / al_stack.
     AE6t.v:555-1053 Section h -> Section h here over FSupoison.ecall_preU: POSTm states ARU; basics gives ARm of
                     aview H (unpoison U mem) and the stack window apresent on the real mem
                     (FSupoisonIntrinR.stack_present); ent_ro moves the image's read-only cells from the unpoisoned
                     reading to the real one with FSupoisonIntrinR.ro_regions_off + FSxMsetR.asan_memset_regions_off_ush
                     (the walk's region condition, a named lemma in lib/A/FSxMsetR.v, not a hidden premise); finish
                     calls ms_tailU. ent_stk / ent0 / path0 / ent1_0 .. ent1_8: text unchanged.
     AE6u.v:72-596, AE6v.v:72-491 (path1_0 .. path1_8), AE2r.v:82-552 (ent2L, ent2H, path2L, path2H) and
                     AE2r.v:555-565 (the case split): text unchanged; they take ecall_pre as a section hypothesis, so
                     they are restated over ecall_preU, never with a new step.
     AE2r.v:567-585  asan_memset_realizes -> asan_memset_realizesU (statement: AR -> ARU, ecall_pre -> ecall_preU).
   Imported and applied as they are (their statements mention no AR / ecall_pre): every symbolic run r_* and state of
   AE6t, AE6t.Env2 / Env10 / Env12, AE6t's tail_shape / chunk_is_sound, AE2r.t_cases, the musl leaf tfib_memset
   (MS_REAL 0x98e24) inside ms_tailU, and AE2y's / AE3d's step lemmas.
   R2: every report / error branch of the walk is proved untaken from the premises, as in the AR walk (the branch
   conditions br_* / rp_* / qc_flag_zero over range_addressable, shadow_hull_vis and amem_range, all on aview mem).
   The two 8-byte QuickCheck shadow words the n <= 64 path loads (the `ld`s the r_p1_t_2 runs stop at, AE6t.v:89 ff.)
   may hold a neighbouring granule's 0xf7: the walk reads them as FRESH atoms q1 / q2 from aview mem and proves both
   branches of the zero test, so it needs no fact about them and none is added (FSxMsetR.v header).

   Premises: Section variables B : asyms, LAWS : AR_laws tfibsegs B, TB : TfibSyms B (those of FSupoisonIntrin.v's
   interceptor contracts and of the __asan_memcpy twin); the theorem's own premises are aintrin_realizesU's:
   ecall_preU ly S U W regs mem md, a0 = d, a1 = x, a2 = n, 0 <= n < 2 ^ 32, 0 <= d, d + n <= 2 ^ 63, dest_ok,
   amem_range d n, range_addressable (aview mem) d n, 0 < n -> shadow_hull_vis (aview mem) d n. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AB1w AE3d AE20 AE2y AE6t.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require AE2r FSupoison FSupoisonU FSupoisonIntrinR FSxMsetR.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YI14 YI16.
Import ListNotations.
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Module FSP := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoison.
Module FSuR := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonIntrinR.
Module FSxR := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSxMsetR.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section g.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Lemma ms_tailU : forall ly S UP (W : world tfibsegs) regs mem md (regs1 : bvmap 5 word) (mem1 : word -> option byte) mat1 d x n,
FSP.ecall_preU tfibsegs B ly S UP W regs mem md ->
getr regs 11 = w64 x -> 0 <= n < 2 ^ 32 -> 0 <= d -> d + n <= 2 ^ 63 ->
dest_ok tfibsegs B ly S W regs mem d n ->
getr regs1 10 = w64 d -> getr regs1 11 = w64 x -> getr regs1 12 = w64 n ->
getr regs1 1 = w64 MS_RA -> getr regs1 2 = w64 (spZ regs - 2128) ->
getr regs1 3 = getr regs 3 -> getr regs1 4 = getr regs 4 ->
getr regs1 22 = getr regs 22 -> getr regs1 23 = getr regs 23 -> getr regs1 24 = getr regs 24 -> getr regs1 25 = getr regs 25 -> getr regs1 26 = getr regs 26 -> getr regs1 27 = getr regs 27 ->
(forall z : word, ~ (spZ regs - MS_SCR <= bv_unsigned z < spZ regs) -> mem1 z = mem z) ->
(forall a, spZ regs - MS_SCR <= a < spZ regs -> apresent (w_H W) mem1 a) ->
val_mem tfibsegs (mrestrict (w_H W) mem1) (spZ regs - 8) 8 (bv_unsigned (getr regs 1)) ->
val_mem tfibsegs (mrestrict (w_H W) mem1) (spZ regs - 16) 8 (bv_unsigned (getr regs 8)) ->
val_mem tfibsegs (mrestrict (w_H W) mem1) (spZ regs - 24) 8 (bv_unsigned (getr regs 9)) ->
val_mem tfibsegs (mrestrict (w_H W) mem1) (spZ regs - 32) 8 (bv_unsigned (getr regs 18)) ->
val_mem tfibsegs (mrestrict (w_H W) mem1) (spZ regs - 40) 8 (bv_unsigned (getr regs 19)) ->
val_mem tfibsegs (mrestrict (w_H W) mem1) (spZ regs - 48) 8 (bv_unsigned (getr regs 20)) ->
val_mem tfibsegs (mrestrict (w_H W) mem1) (spZ regs - 56) 8 (bv_unsigned (getr regs 21)) ->
SRr tfibsegs W (mkCfg (mkst regs1 (Z_to_bv 64 MS_REAL) mem1 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat1 md))
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
FSP.ARU tfibsegs B ly S UP W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 d /\
(forall i, 0 <= i < n -> aview tfibsegs (w_H W) mem' (d + i) = Some (x mod 256)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (spZ regs - ESTACK <= a < spZ regs) -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Proof.
intros ly S UP W regs mem md regs1 mem1 mat1 d x n HPRE Hx Hn Hd Hdn HDST G10 G11 G12 G1 G2 G3 G4 G22 G23 G24 G25 G26 G27
MEQ1 PRS1 V0 V1 V2 V3 V4 V5 V6.
pose proof HPRE as ((HAR & Hra & Hal16 & Hslo & Htop & HpresE & Hgp & Htp) & HOK & HPO).
assert (HARU : FSP.ARU tfibsegs B ly S UP W mem md) by (split; [exact HAR | split; [exact HOK | exact HPO]]).
pose proof AF0x.Hwx_tfa as Hwx. assert (HES : ESTACK = 4096) by reflexivity. assert (HSC : MS_SCR = 2200) by reflexivity.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (sp0 := spZ regs) in *. assert (Hsp44 : 2 ^ 44 <= sp0 <= 2 ^ 47) by (unfold kHighMemBeg in Lbeg; lia).
set (H := w_H W) in *.
assert (DW : forall a, d <= a < d + n -> writable_at tfibsegs (mrestrict H mem1) a /\ H (Z_to_bv 64 a) = false).
{ intros a Ha. destruct (HDST a Ha) as (Hw & _ & Hns).
assert (Hw1 : writable_at tfibsegs (mrestrict H mem1) a).
{ apply (writable_at_same (mrestrict H mem) (mrestrict H mem1) a); [|exact Hw].
unfold mrestrict. rewrite (MEQ1 (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by lia. unfold sp0 in *. lia. }
split; [exact Hw1|]. destruct (H (Z_to_bv 64 a)) eqn:Hh; [|reflexivity].
exfalso. exact (hidden_not_writable W mem1 a ltac:(lia) Hh Hw1). }
set (nn := Z.to_nat n). assert (Hnn : Z.of_nat nn = n) by (subst nn; lia).
assert (SOK : store_ok tfibsegs (mrestrict H mem1) (w64 d) nn = true).
{ apply store_ok_of_all; unfold w64; rewrite unsigned_lit_small by lia; [lia|].
intros z Hz. pose proof (proj1 (DW (bv_unsigned z) ltac:(lia))) as Wz. unfold writable_at in Wz. rewrite Z_to_bv_bv_unsigned in Wz. exact Wz. }
destruct (tfib_memset (w64 d) (w64 x) (w64 n) nn (mrestrict H mem1) (seg_rom tfibsegs) regs1 G10 G11 G12
ltac:(unfold w64; rewrite unsigned_lit_small by lia; lia) SOK ltac:(unfold w64; rewrite unsigned_lit_small by lia; lia))
as (regs2 & Hms & A10 & Hkeep).
rewrite G1 in Hms. replace (v_jalr (w64 MS_RA) 0) with (Z_to_bv 64 MS_RA : word) in Hms by (apply bv_eq; vm_compute; reflexivity).
change (Z_to_bv 64 tfib_A_memset) with (Z_to_bv 64 MS_REAL) in Hms.
set (cb := Z_to_bv 8 (bv_unsigned (w64 x) mod 256)) in Hms.
set (m1r := mrestrict H mem1) in *. set (m2r := wbytes m1r (w64 d) (repeat cb nn)) in Hms.
assert (KEEP : forall r : bv 5, r <> 11%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv -> r <> 15%bv -> r <> 16%bv -> getr regs2 r = getr regs1 r)
by (intros r; apply Hkeep).
set (mem2 := munrestrict H mem1 m2r).
assert (LEN : Z.of_nat (length (repeat cb nn)) = n) by (rewrite repeat_length; exact Hnn).
assert (M2out : forall z : word, ~ (d <= bv_unsigned z < d + n) -> mem2 z = mem1 z).
{ intros z Hz. subst mem2 m2r. unfold munrestrict. destruct (H z) eqn:Hh; [reflexivity|].
assert (Ew : wbytes m1r (w64 d) (repeat cb nn) z = m1r z).
{ destruct (Z_lt_le_dec (bv_unsigned z) d) as [L|L].
- apply wbytes_below; unfold w64; rewrite ?LEN, unsigned_lit_small by lia; lia.
- apply wbytes_above. unfold w64. rewrite LEN, unsigned_lit_small by lia. lia. }
rewrite Ew. subst m1r. unfold mrestrict. rewrite Hh. reflexivity. }
assert (M2in : forall i, 0 <= i < n -> mem2 (Z_to_bv 64 (d + i)) = Some cb).
{ intros i Hi. subst mem2. unfold munrestrict. rewrite (proj2 (DW (d + i) ltac:(lia))).
subst m2r. rewrite (wbytes_inside (repeat cb nn) m1r (w64 d) (Z_to_bv 64 (d + i)));
unfold w64; rewrite ?LEN, ?unsigned_lit_small by lia; [|lia|lia].
replace (Z.to_nat (d + i - d)) with (Z.to_nat i) by lia. apply nth_error_repeat. lia. }
assert (AV2 : forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (sp0 - MS_SCR <= a < sp0) -> aview tfibsegs H mem2 a = aview tfibsegs H mem a).
{ intros a Hr Ha Hs. apply aview_same. rewrite (M2out (Z_to_bv 64 a)), (MEQ1 (Z_to_bv 64 a)); [reflexivity| |];
rewrite unsigned_lit_small by lia; [exact Hs | exact Ha]. }
assert (MS2 : forall z : word, sp0 - MS_SCR <= bv_unsigned z < sp0 -> mem2 z = mem1 z).
{ intros z Hz. apply M2out. intros Hd'. destruct (HDST (bv_unsigned z) Hd') as (_ & _ & Hns). apply Hns. unfold sp0 in *. lia. }
assert (A2 : getr regs2 2 = w64 (sp0 - 2128)) by (rewrite KEEP by (intros H'; discriminate H'); exact G2).
set (E2 := Ereg regs2 [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20; getr regs 21]).
assert (E2_2 : bv_unsigned (ew E2 2) = sp0 - 2128).
{ subst E2. rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl), A2. unfold w64. apply unsigned_lit_small. lia. }
assert (VM : forall a v, val_mem tfibsegs (mrestrict H mem1) a 8 v -> sp0 - MS_SCR <= a -> a + 8 <= sp0 -> val_mem tfibsegs (mrestrict H mem2) a 8 v).
{ intros a v Hv Hlo Hhi. apply (val_mem_frame H mem1 mem2 a 8 v); [|exact Hv]. intros k Hk. apply MS2. rewrite unsigned_lit_small by lia. lia. }
assert (HSe : st_ok tfibsegs E2 ss_epi (restrict H (mkst regs2 (Z_to_bv 64 MS_RA) mem2 (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_epi. apply (entry_st_ok_full tfibsegs);
change (Ereg regs2 [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20; getr regs 21]) with E2.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil].
unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
replace (base_val E2 (Some 2%nat)) with (sp0 - 2128) by (symmetry; exact E2_2).
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
unfold epi_chunks.
assert (CK : forall (j : nat) (r : bv 5) off, nth j [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20; getr regs 21] (Z_to_bv 64 0) = getr regs r ->
off = 2120 - 8 * Z.of_nat j -> Z.of_nat j < 7 ->
val_mem tfibsegs (mrestrict H mem1) (sp0 - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs r)) ->
YP09.chunk_ok tfibsegs E2 (mrestrict H mem2) (sp0 - 2128) (YP09.mkChunk off (CVal 8 (SOff (32 + j) 0)))).
{ intros j r off Hnth Hoff Hj8 Hv. eapply (chunk_ok_val tfibsegs E2 _ (sp0 - 2128) off 8 _ (bv_unsigned (getr regs r))).
- cbn [sv_denot]. subst E2. rewrite (ew_Ereg_extra regs2 _ j), Hnth, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- pose proof (u64_range (getr regs r)). zside.
- zside.
- subst off. replace (sp0 - 2128 + (2120 - 8 * Z.of_nat j)) with (sp0 - 8 - 8 * Z.of_nat j) by lia. apply VM; [exact Hv | lia | lia]. }
repeat apply Forall_cons; try apply Forall_nil.
+ apply (CK 0%nat 1%bv); [reflexivity | reflexivity | cbn; lia | replace (sp0 - 8 - 8 * Z.of_nat 0) with (sp0 - 8) by lia; exact V0].
+ apply (CK 1%nat 8%bv); [reflexivity | reflexivity | cbn; lia | replace (sp0 - 8 - 8 * Z.of_nat 1) with (sp0 - 16) by lia; exact V1].
+ apply (CK 2%nat 9%bv); [reflexivity | reflexivity | cbn; lia | replace (sp0 - 8 - 8 * Z.of_nat 2) with (sp0 - 24) by lia; exact V2].
+ apply (CK 3%nat 18%bv); [reflexivity | reflexivity | cbn; lia | replace (sp0 - 8 - 8 * Z.of_nat 3) with (sp0 - 32) by lia; exact V3].
+ apply (CK 4%nat 19%bv); [reflexivity | reflexivity | cbn; lia | replace (sp0 - 8 - 8 * Z.of_nat 4) with (sp0 - 40) by lia; exact V4].
+ apply (CK 5%nat 20%bv); [reflexivity | reflexivity | cbn; lia | replace (sp0 - 8 - 8 * Z.of_nat 5) with (sp0 - 48) by lia; exact V5].
+ apply (CK 6%nat 21%bv); [reflexivity | reflexivity | cbn; lia | replace (sp0 - 8 - 8 * Z.of_nat 6) with (sp0 - 56) by lia; exact V6].
- apply pairwise_disjoint_of_extents. cbn. repeat split.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2_2.
change (2 ^ 4) with 16. unfold sp0 in *. repeat split; try lia.
all: replace (spZ regs - 2128) with (spZ regs + (-133) * 16) by lia; rewrite Z_mod_plus_full; exact Hal16. }
eapply (SRr_msteps tfibsegs Hwx W); [rewrite restrict_mkst_fx; exact Hms|].
intros model' Hsbm _. rewrite (same_but_materialized_wvb md model' Hsbm). cbn [ms_mem mkst].
change (unrestrict H mem1 (mkst regs2 (Z_to_bv 64 MS_RA) m2r (seg_rom tfibsegs))) with (mkst regs2 (Z_to_bv 64 MS_RA) mem2 (seg_rom tfibsegs)).
eapply SRr_bind; [apply (icpt_phase W E2 ss_epi epi_e _ _ _ HSe r_epi)|].
cbv beta. intros W1 c1 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
eapply (SRr_ret_at tfibsegs tbl_icpt tbl_icpt_ok Hwx W E2); [exact HS3 | reflexivity | vm_compute; reflexivity |].
intros mat'. rewrite wvb_wvb.
assert (MEQ3 : forall z, ms_mem ms3 z = mem2 z) by (intros z; apply HF3; intros Hin; destruct (in_wrange_windows E2 _ _ Hin) as (b & lo & hi & Ht & Hw); cbn in Ht; destruct Ht as [Hq|[]]; injection Hq as <- <- <-; cbn [base_val] in Hw; lia).
rreg HS3 (1%bv : bv 5) Q1. rreg HS3 (2%bv : bv 5) Q2. rreg HS3 (10%bv : bv 5) Q10.
rreg HS3 (8%bv : bv 5) Q8. rreg HS3 (9%bv : bv 5) Q9. rreg HS3 (18%bv : bv 5) Q18. rreg HS3 (19%bv : bv 5) Q19.
rreg HS3 (20%bv : bv 5) Q20. rreg HS3 (21%bv : bv 5) Q21. rreg HS3 (22%bv : bv 5) Q22.
rreg HS3 (3%bv : bv 5) Q3. rreg HS3 (4%bv : bv 5) Q4.
rreg HS3 (23%bv : bv 5) Q23. rreg HS3 (24%bv : bv 5) Q24. rreg HS3 (25%bv : bv 5) Q25. rreg HS3 (26%bv : bv 5) Q26. rreg HS3 (27%bv : bv 5) Q27.
assert (X32 : ew E2 32 = getr regs 1) by (subst E2; exact (ew_Ereg_extra regs2 _ 0)).
rewrite X32 in Q1.
replace (v_jalr (getr (ms_regs ms3) 1) 0) with (w64 (raZ regs)) by (rewrite Q1; unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; symmetry; exact Hra).
split; [reflexivity|]. exists (ms_regs ms3), (ms_mem ms3), (with_vm_backing (m_vm_lazy md) mat' md).
pose proof (same_but_materialized_frame md _ (with_vm_backing_same md mat')) as MF.
assert (AV3 : forall a, aview tfibsegs H (ms_mem ms3) a = aview tfibsegs H mem2 a) by (intros a; apply aview_same; apply MEQ3).
split; [reflexivity|].
split; [|split; [|split; [|split; [|split; [|split]]]]].
-   apply (FSP.ARU_frame tfibsegs B LAWS ly S UP W mem md (ms_mem ms3) _ HARU).
+ intros a Hr Hown. rewrite AV3. apply AV2; [exact Hr | intros Hd'; exact (proj1 (proj2 (HDST a Hd')) Hown) |].
intros Hs. exact (FSP.ARU_stack tfibsegs B LAWS ly S UP W mem md a HARU ltac:(unfold sp0 in *; lia) Hown).
+ intros a Hv. rewrite AV3. rewrite (AE2y.aview_mod _ mem2 a). rewrite (AE2y.aview_mod _ mem a) in Hv.
assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' d) as [L1|L1]; [| destruct (Z_lt_le_dec a' (d + n)) as [L2|L2]].
2:{ unfold aview, mbyte, mrestrict. rewrite (proj2 (DW a' ltac:(lia))). replace a' with (d + (a' - d)) by lia. rewrite (M2in (a' - d)) by lia. discriminate. }
all: destruct (Z_lt_le_dec a' (sp0 - MS_SCR)) as [L3|L3]; [rewrite AV2 by lia; exact Hv|].
all: destruct (Z_lt_le_dec a' sp0) as [L4|L4]; [| rewrite AV2 by lia; exact Hv].
all: apply aview_some_of_apresent; apply (apresent_same H mem1 mem2 a' (MS2 (Z_to_bv 64 a') ltac:(rewrite unsigned_lit_small by lia; lia))); apply PRS1; lia.
+ apply MF. + apply MF. + apply MF.
+ exact (AE2y.hs_kept_trans _ _ _ _ (AE2y.hs_kept_trans _ _ _ _ (AE2y.hs_kept_win _ _ _ _ _ _ _ _ MEQ1 HpresE ltac:(unfold ESTACK, MS_SCR; lia) ltac:(lia)) (AE2y.hs_kept_unrestrict _ _ _)) (AE2y.hs_kept_eq _ _ _ MEQ3)).
-
intros r Hr. unfold acallee_saved in Hr.
assert (X : forall j rr, nth j [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20; getr regs 21] (Z_to_bv 64 0) = getr regs rr -> ew E2 (32 + j) = getr regs rr)
by (intros jj rr Hnth; subst E2; rewrite (ew_Ereg_extra regs2 _ jj); exact Hnth).
assert (Y : forall i (rr : bv 5), Z.of_nat i = bv_unsigned rr -> ew E2 i = getr regs2 rr) by (intros ii rr Hnth; subst E2; exact (ew_Ereg_nat regs2 _ ii rr Hnth)).
destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]].
+ replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q2. apply bv_eq. rewrite Z_to_bv_unsigned, E2_2. unfold sp0, spZ, bv_wrap. change (bv_modulus 64) with (2 ^ 64).
pose proof (u64_range (getr regs 2)). rewrite Z.mod_small by lia. lia.
+ replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q3, (Y 3%nat 3%bv eq_refl), KEEP by (intros H'; discriminate H'). exact G3.
+ replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q4, (Y 4%nat 4%bv eq_refl), KEEP by (intros H'; discriminate H'). exact G4.
+ replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q8. exact (X 1%nat 8%bv eq_refl).
+ replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q9. exact (X 2%nat 9%bv eq_refl).
+ assert (Hc : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]].
* replace (Z_to_bv 5 18) with (18%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q18. exact (X 3%nat 18%bv eq_refl).
* replace (Z_to_bv 5 19) with (19%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q19. exact (X 4%nat 19%bv eq_refl).
* replace (Z_to_bv 5 20) with (20%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q20. exact (X 5%nat 20%bv eq_refl).
* replace (Z_to_bv 5 21) with (21%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q21. exact (X 6%nat 21%bv eq_refl).
* replace (Z_to_bv 5 22) with (22%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q22, (Y 22%nat 22%bv eq_refl), KEEP by (intros H'; discriminate H'). exact G22.
* replace (Z_to_bv 5 23) with (23%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q23, (Y 23%nat 23%bv eq_refl), KEEP by (intros H'; discriminate H'). exact G23.
* replace (Z_to_bv 5 24) with (24%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q24, (Y 24%nat 24%bv eq_refl), KEEP by (intros H'; discriminate H'). exact G24.
* replace (Z_to_bv 5 25) with (25%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q25, (Y 25%nat 25%bv eq_refl), KEEP by (intros H'; discriminate H'). exact G25.
* replace (Z_to_bv 5 26) with (26%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q26, (Y 26%nat 26%bv eq_refl), KEEP by (intros H'; discriminate H'). exact G26.
* replace (Z_to_bv 5 27) with (27%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q27, (Y 27%nat 27%bv eq_refl), KEEP by (intros H'; discriminate H'). exact G27.
- apply with_vm_backing_same.
- rewrite Q10. subst E2. rewrite (ew_Ereg_nat regs2 _ 10 10%bv eq_refl). exact A10.
- intros i Hi. rewrite AV3. unfold aview, mbyte, mrestrict. rewrite (proj2 (DW (d + i) ltac:(lia))), (M2in i Hi). cbn [option_map].
f_equal. subst cb. unfold w64. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (256 * 2 ^ 56). change (bv_modulus 8) with 256.
rewrite Z.mod_mod by lia. apply Z.mod_mod_divide. exists (2 ^ 56). reflexivity.
- intros a Hr Hd' Hs. rewrite AV3. apply AV2; [exact Hr | exact Hd' | unfold sp0 in *; lia].
- intros a Hp. pose proof Hp as [Hh [b Hb]].
assert (Hr : apresent H (ms_mem ms3) a <-> apresent H (ms_mem ms3) (a mod 2 ^ 64)).
{ unfold apresent. rewrite <- (AE2y.Z_to_bv64_of_mod a). tauto. }
apply (proj2 Hr). clear Hr.
assert (Hp' : apresent H mem (a mod 2 ^ 64)) by (unfold apresent; rewrite (AE2y.Z_to_bv64_of_mod a); exact Hp).
assert (Ha : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
apply (apresent_same H mem2 (ms_mem ms3) a' (MEQ3 _)).
destruct (Z_lt_le_dec a' d) as [L1|L1]; [| destruct (Z_lt_le_dec a' (d + n)) as [L2|L2]].
2:{ split; [exact (proj2 (DW a' ltac:(lia)))|]. exists cb. replace a' with (d + (a' - d)) by lia. apply M2in. lia. }
all: destruct (Z_lt_le_dec a' (sp0 - MS_SCR)) as [L3|L3];
[apply (apresent_same H mem mem2 a'); [rewrite (M2out (Z_to_bv 64 a')), (MEQ1 (Z_to_bv 64 a')) by (rewrite unsigned_lit_small by lia; lia); reflexivity | exact Hp']|].
all: destruct (Z_lt_le_dec a' sp0) as [L4|L4];
[| apply (apresent_same H mem mem2 a'); [rewrite (M2out (Z_to_bv 64 a')), (MEQ1 (Z_to_bv 64 a')) by (rewrite unsigned_lit_small by lia; lia); reflexivity | exact Hp']].
all: apply (apresent_same H mem1 mem2 a' (MS2 (Z_to_bv 64 a') ltac:(rewrite unsigned_lit_small by lia; lia))); apply PRS1; lia.
Qed.
End g.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.
Variables (ly : alayout) (S : astate) (UP : list (Z * Z)) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (d x n : Z).
Hypothesis HPRE : FSP.ecall_preU tfibsegs B ly S UP W regs mem md.
(* ARU of the real memory: ecall_preU's AR (which is of unpoison UP mem) with UP's two side conditions. *)
Lemma HARU : FSP.ARU tfibsegs B ly S UP W mem md.
Proof. destruct HPRE as ((HAR & _) & HOK & HPO). split; [exact HAR | split; [exact HOK | exact HPO]]. Qed.
Hypothesis G10 : getr regs 10 = w64 d.
Hypothesis G11 : getr regs 11 = w64 x.
Hypothesis G12 : getr regs 12 = w64 n.
Hypothesis Hn : 0 <= n < 2 ^ 32.
Hypothesis Hd : 0 <= d.
Hypothesis Hdn : d + n <= 2 ^ 63.
Hypothesis HDST : dest_ok tfibsegs B ly S W regs mem d n.
Hypothesis HRA : range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF d n.
Hypothesis HHULL : 0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) mem) d n.
Hypothesis HAM : amem_range d n.
Definition POSTm : world tfibsegs -> config -> Prop :=
fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
FSP.ARU tfibsegs B ly S UP W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 d /\
(forall i, 0 <= i < n -> aview tfibsegs (w_H W) mem' (d + i) = Some (x mod 256)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (spZ regs - ESTACK <= a < spZ regs) -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a).
Let sp0 : Z := spZ regs.
Let H := w_H W.
Let g0 : Z := d / 8.
Let g1 : Z := (d + n - 1) / 8.
Let du : Z := (d + 7) / 8 * 8.
Let de : Z := (d + n) / 8 * 8.
Let gu : Z := (d + 7) / 8.
Let ge : Z := (d + n) / 8.
Lemma basics : 2 ^ 44 <= sp0 <= 2 ^ 47 /\ kHighMemBeg + 4096 <= sp0 /\ sp0 mod 16 = 0 /\ d + n <= 2 ^ 47 - 1 /\
(forall a, sp0 - 4096 <= a < sp0 -> apresent H mem a) /\ ARm B ly S (aview tfibsegs H (FSP.unpoison UP mem)).
Proof.
pose proof HPRE as ((HAR & Hra & Hal16 & Hslo & Htop & HpresE & Hgp & Htp) & HOK & HPO).
pose proof (FSuR.stack_present B ly S UP W regs mem md HPRE) as HpresM.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (ESTACK = 4096) by reflexivity.
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. subst sp0 H.
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact HpresM | exact (proj1 HAR)].
Qed.
Lemma finish : forall E ss ms mat,
st_ok tfibsegs E ss (restrict H ms) -> ss_resv ss = None -> tail_shape ss = true ->
(forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E i = getr regs r) ->
(forall z : word, ~ (sp0 - MS_SCR <= bv_unsigned z < sp0) -> ms_mem ms z = mem z) ->
(forall a, sp0 - MS_SCR <= a < sp0 - MS_STK -> apresent H (ms_mem ms) a) ->
SRr tfibsegs W (mkCfg ms (with_vm_backing (m_vm_lazy md) mat md)) POSTm.
Proof.
intros E ss ms mat HS Hrv Hsh HE MEQ PRS.
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bpres & BM). assert (HSC : MS_SCR = 2200) by reflexivity. assert (HSK : MS_STK = 2192) by reflexivity.
unfold tail_shape in Hsh. apply andb_prop in Hsh as [Hsh C56]. apply andb_prop in Hsh as [Hsh C48]. apply andb_prop in Hsh as [Hsh C40]. apply andb_prop in Hsh as [Hsh C32]. apply andb_prop in Hsh as [Hsh C24]. apply andb_prop in Hsh as [Hsh C16]. apply andb_prop in Hsh as [Hsh C8]. apply andb_prop in Hsh as [Hsh R22]. apply andb_prop in Hsh as [Hsh R27]. apply andb_prop in Hsh as [Hsh R26]. apply andb_prop in Hsh as [Hsh R25]. apply andb_prop in Hsh as [Hsh R24]. apply andb_prop in Hsh as [Hsh R23]. apply andb_prop in Hsh as [Hsh R4]. apply andb_prop in Hsh as [Hsh R3]. apply andb_prop in Hsh as [Hsh R2]. apply andb_prop in Hsh as [Hsh R1]. apply andb_prop in Hsh as [Hsh R12]. apply andb_prop in Hsh as [Hsh R11]. apply andb_prop in Hsh as [Hsh R10]. apply andb_prop in Hsh as [Hsh Smem].
destruct (ss_mem ss) as [|r0 rest] eqn:Hmem; [discriminate|].
apply andb_prop in Smem as [Smem Hwhi]. apply andb_prop in Smem as [Hbase Hwlo].
apply obase_eqb_eq in Hbase. apply Z.eqb_eq in Hwlo. apply Z.eqb_eq in Hwhi. apply Z.eqb_eq in Hsh.
assert (E2 : bv_unsigned (ew E 2) = sp0) by (rewrite (HE 2%nat 2%bv eq_refl); reflexivity).
assert (RD : forall (r : bv 5) v, reg_is ss (bv_unsigned r) v = true -> getr (ms_regs ms) r = sv_denot E v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply (st_ok_reg_denot H E ss ms r HS). }
assert (RA : forall (r : bv 5) i, Z.of_nat i = bv_unsigned r -> reg_is ss (bv_unsigned r) (SOff i 0) = true -> getr (ms_regs ms) r = getr regs r).
{ intros r i Hi Hr. rewrite (RD r _ Hr). cbn [sv_denot]. rewrite (HE i r Hi), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (CK : forall off (r : bv 5) i, Z.of_nat i = bv_unsigned r -> has_chunk ss off (SOff i 0) = true ->
val_mem tfibsegs (mrestrict H (ms_mem ms)) (sp0 + off) 8 (bv_unsigned (getr regs r))).
{ intros off r i Hi Hc. unfold has_chunk in Hc. rewrite Hmem in Hc. apply existsb_exists in Hc as (c & Hin & Hc).
apply chunk_is_sound in Hc. subst c.
pose proof (st_ok_mem_ok tfibsegs E ss _ HS) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs. rewrite Hmem in Hrs.
pose proof (Forall_inv Hrs) as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hck. rewrite Hbase in Hck. cbn [base_val] in Hck. rewrite E2 in Hck.
apply (val_of_chunk_ok tfibsegs E _ _ off 8 (SOff i 0) (bv_unsigned (getr regs r)) Hck).
- cbn [sv_denot]. rewrite (HE i r Hi), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- pose proof (u64_range (getr regs r)). zside.
- zside. }
pose proof (st_ok_restrict_mkst tfibsegs H E _ _ HS Hrv) as Hshape. rewrite Hsh in Hshape. rewrite Hshape.
apply (ms_tailU B LAWS ly S UP W regs mem md (ms_regs ms) (ms_mem ms) mat d x n HPRE G11 Hn Hd Hdn HDST).
- rewrite (RD 10%bv (SOff 10 0) R10). cbn [sv_denot]. rewrite (HE 10%nat 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned. exact G10.
- rewrite (RD 11%bv (SOff 11 0) R11). cbn [sv_denot]. rewrite (HE 11%nat 11%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned. exact G11.
- rewrite (RD 12%bv (SOff 12 0) R12). cbn [sv_denot]. rewrite (HE 12%nat 12%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned. exact G12.
- rewrite (RD 1%bv (SLit MS_RA) R1). reflexivity.
- rewrite (RD 2%bv (SOff 2 (-2128)) R2). cbn [sv_denot]. rewrite (HE 2%nat 2%bv eq_refl). reflexivity.
- exact (RA 3%bv 3%nat eq_refl R3). - exact (RA 4%bv 4%nat eq_refl R4).
- exact (RA 22%bv 22%nat eq_refl R22). - exact (RA 23%bv 23%nat eq_refl R23). - exact (RA 24%bv 24%nat eq_refl R24). - exact (RA 25%bv 25%nat eq_refl R25).
- exact (RA 26%bv 26%nat eq_refl R26). - exact (RA 27%bv 27%nat eq_refl R27).
- exact MEQ.
- intros a Ha. destruct (Z_lt_le_dec a (sp0 - MS_STK)) as [L|L]; [apply PRS; lia|].
apply (st_ok_window_apresent H E ss ms 0 r0 a HS ltac:(rewrite Hmem; reflexivity)); [| unfold TFIB_IMG_END, kHighMemBeg in *; lia].
rewrite Hbase, Hwlo, Hwhi. cbn [base_val]. rewrite E2. lia.
- replace (sp0 - 8) with (sp0 + -8) by lia. exact (CK (-8) 1%bv 1%nat eq_refl C8).
- replace (sp0 - 16) with (sp0 + -16) by lia. exact (CK (-16) 8%bv 8%nat eq_refl C16).
- replace (sp0 - 24) with (sp0 + -24) by lia. exact (CK (-24) 9%bv 9%nat eq_refl C24).
- replace (sp0 - 32) with (sp0 + -32) by lia. exact (CK (-32) 18%bv 18%nat eq_refl C32).
- replace (sp0 - 40) with (sp0 + -40) by lia. exact (CK (-40) 19%bv 19%nat eq_refl C40).
- replace (sp0 - 48) with (sp0 + -48) by lia. exact (CK (-48) 20%bv 20%nat eq_refl C48).
- replace (sp0 - 56) with (sp0 + -56) by lia. exact (CK (-56) 21%bv 21%nat eq_refl C56).
Qed.
Local Notation Env := (AE2y.Env regs).
Local Notation Env_reg := (AE2y.Env_reg regs).
Local Notation Env_x := (AE2y.Env_x regs).
(* AE6t's Env2 / Env10 / Env12 state no AR / ecall_pre: applied as they are (AE2r.v:55-57). Env2 is read at this
   section's sp0, as the copied proofs' lia steps pair it with basics' sp0 facts (AE6t.Env2's own sp0 is discharged
   to spZ regs). *)
Lemma Env2 : forall extra, bv_unsigned (ew (Env extra) 2) = sp0.
Proof. exact (AE6t.Env2 regs). Qed.
Local Notation Env10 := (AE6t.Env10 regs d G10).
Local Notation Env12 := (AE6t.Env12 regs n G12).
Lemma ent_stk : forall extra, region_ok tfibsegs (Env extra) (mrestrict H mem) stk.
Proof.
intros extra. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bpres & BM). unfold stk, MS_STK.
apply (region_ok_stack tfibsegs (Env extra) _ 2 sp0 (- 2192)); [exact (Env2 extra) | lia | lia |].
intros a Ha. apply AF0x.apresent_writable; [unfold AF0x.TFIB_IMG_END, kHighMemBeg in *; lia|]. apply Bpres. lia.
Qed.
Lemma ent_ro : forall extra, Forall (region_ok tfibsegs (Env extra) (mrestrict H mem)) (map ro_region icpt_rodata).
Proof.
intros extra. apply (FSuR.ro_regions_off B TB ly S UP W mem md (Env extra) mem HARU).
- intros a Hro. exact (FSxR.asan_memset_regions_off_ush B ly S UP W regs mem md d n HPRE Hd HAM HRA a
    (or_intror (or_introl Hro))).
- intros a Ha. reflexivity.
Qed.
Lemma ent0 : n = 0 -> st_ok tfibsegs (Env []) ss0 (restrict H (mkst regs (Z_to_bv 64 MS_ENTRY) mem (seg_rom tfibsegs))).
Proof.
intros Hn0. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bpres & BM).
rewrite restrict_mkst_fx. unfold ss0. unfold AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [])) with (Env []).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply ent_stk | apply ent_ro].
- apply pairwise_disjoint_of_extents. unfold stk, icpt_rodata, ro_region, extent_of_region.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite (Env2 []). unfold MS_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; exact I]. cbn [f_atoms atoms_ok facts0]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite (Env2 []), (Env10 []), (Env12 []), !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; apply Z.mod_1_r.
Qed.
Lemma path0 : n = 0 -> SRr tfibsegs W (cfg_at tfibsegs MS_ENTRY regs mem md) POSTm.
Proof.
intros Hn0.
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bpres & BM). assert (HSC : MS_SCR = 2200) by reflexivity.
unfold cfg_at. change (w64 MS_ENTRY) with (Z_to_bv 64 MS_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 MS_ENTRY) mem (seg_rom tfibsegs)) z = mem z) by (intros; reflexivity).
set (EE := Env []). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply Env_reg; assumption).
pose proof (Env2 []) as EE2. pose proof (Env10 []) as EE10. pose proof (Env12 []) as EE12. fold EE in EE2, EE10, EE12.
pose proof (ent0 Hn0) as HS0. fold EE in HS0.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS0 r_p0_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG p0_e0 13) (RG p0_e0 12) HS1 (br_ovf_false EE 10 12 d n EE10 EE12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_p0_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_GEU (RG p0_e1 14) (RG p0_e1 13) HS2 (br_cls_zero EE ltac:(rewrite EE12, Hn0; reflexivity))) as HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_p0_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF3 HFr3.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_NE (RG p0_e2 12) (SLit 0) HS3 (br_n_zero EE ltac:(rewrite EE12, Hn0; reflexivity))) as HS3'.
change (neg_bc BC_NE) with BC_EQ in HS3'. clear HS3.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS3' r_p0_3)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HF4 & HFr4). rewrite ?wvb_wvb in *.
assert (MEQ4 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z).
{ intros z Hz. rewrite (HF4 z); [apply MEQ3; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF4 HFr4.
apply (finish EE p0_e3 ms4 mat4 HS4 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ4. unfold MS_SCR, MS_STK in *. lia.
- intros a Ha; unfold MS_SCR, MS_STK in *; apply (apresent_same H mem (ms_mem ms4) a); [apply MEQ4; rewrite unsigned_lit_small by lia; lia | apply Bpres; lia].
Qed.
Lemma ent1_0 : forall b1 q1 q2, 1 <= n <= 64 -> g1 - g0 = 0 -> aview tfibsegs H mem (SB + g1) = Some b1 -> saddr_ok (d + n - 1) b1 ->
st_ok tfibsegs (Env [g0; g1; b1; q1; q2]) (ss1 0) (restrict H (mkst regs (Z_to_bv 64 MS_ENTRY) mem (seg_rom tfibsegs))).
Proof.
intros b1 q1 q2 Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bpres & BM).
set (EE := Env [g0; g1; b1; q1; q2]).
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (apply (Env_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (Env_x _ 2); reflexivity).
pose proof (Env2 [g0; g1; b1; q1; q2]) as E2. pose proof (Env10 [g0; g1; b1; q1; q2]) as E10. pose proof (Env12 [g0; g1; b1; q1; q2]) as E12.
fold EE in E2, E10, E12.
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= d < 8 * g0 + 8) by (subst g0; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1 <= d + n - 1 < 8 * g1 + 8) by (subst g1; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1 < 2 ^ 44) by lia.
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
rewrite restrict_mkst_fx. unfold ss1. unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [g0; g1; b1; q1; q2])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply ent_stk | apply Forall_cons; [| apply ent_ro]].
unfold shreg1, region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app].
change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by lia.
split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: first
[ apply chunk_ok_zero; intros i Hi; rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|];
rewrite <- (ra_granule_zero (aview tfibsegs H mem) d n (g0 + i) HRA ltac:(lia) Hd); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0 _ 1 (SOff 34 0) b1); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
- apply pairwise_disjoint_of_extents. unfold stk, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2, E32, unsigned_lit_small by lia. unfold MS_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok facts1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E12, E32, E34, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; apply Z.mod_1_r.
+ cbn [f_alias aliases1 alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_srl3, (U_atom EE 10 d E10), (U_atom EE 32 g0 E32) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 10 12 d n E10 E12), (U_atom_off EE 32 g0 0 E32) by lia. subst g0 g1. lia.
Qed.
Lemma ent1_1 : forall b1 q1 q2, 1 <= n <= 64 -> g1 - g0 = 1 -> aview tfibsegs H mem (SB + g1) = Some b1 -> saddr_ok (d + n - 1) b1 ->
st_ok tfibsegs (Env [g0; g1; b1; q1; q2]) (ss1 1) (restrict H (mkst regs (Z_to_bv 64 MS_ENTRY) mem (seg_rom tfibsegs))).
Proof.
intros b1 q1 q2 Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bpres & BM).
set (EE := Env [g0; g1; b1; q1; q2]).
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (apply (Env_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (Env_x _ 2); reflexivity).
pose proof (Env2 [g0; g1; b1; q1; q2]) as E2. pose proof (Env10 [g0; g1; b1; q1; q2]) as E10. pose proof (Env12 [g0; g1; b1; q1; q2]) as E12.
fold EE in E2, E10, E12.
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= d < 8 * g0 + 8) by (subst g0; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1 <= d + n - 1 < 8 * g1 + 8) by (subst g1; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1 < 2 ^ 44) by lia.
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
rewrite restrict_mkst_fx. unfold ss1. unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [g0; g1; b1; q1; q2])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply ent_stk | apply Forall_cons; [| apply ent_ro]].
unfold shreg1, region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app].
change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by lia.
split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: first
[ apply chunk_ok_zero; intros i Hi; rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|];
rewrite <- (ra_granule_zero (aview tfibsegs H mem) d n (g0 + i) HRA ltac:(lia) Hd); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0 _ 1 (SOff 34 0) b1); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
- apply pairwise_disjoint_of_extents. unfold stk, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2, E32, unsigned_lit_small by lia. unfold MS_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok facts1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E12, E32, E34, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; apply Z.mod_1_r.
+ cbn [f_alias aliases1 alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_srl3, (U_atom EE 10 d E10), (U_atom EE 32 g0 E32) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 10 12 d n E10 E12), (U_atom_off EE 32 g0 1 E32) by lia. subst g0 g1. lia.
Qed.
Lemma ent1_2 : forall b1 q1 q2, 1 <= n <= 64 -> g1 - g0 = 2 -> aview tfibsegs H mem (SB + g1) = Some b1 -> saddr_ok (d + n - 1) b1 ->
st_ok tfibsegs (Env [g0; g1; b1; q1; q2]) (ss1 2) (restrict H (mkst regs (Z_to_bv 64 MS_ENTRY) mem (seg_rom tfibsegs))).
Proof.
intros b1 q1 q2 Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bpres & BM).
set (EE := Env [g0; g1; b1; q1; q2]).
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (apply (Env_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (Env_x _ 2); reflexivity).
pose proof (Env2 [g0; g1; b1; q1; q2]) as E2. pose proof (Env10 [g0; g1; b1; q1; q2]) as E10. pose proof (Env12 [g0; g1; b1; q1; q2]) as E12.
fold EE in E2, E10, E12.
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= d < 8 * g0 + 8) by (subst g0; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1 <= d + n - 1 < 8 * g1 + 8) by (subst g1; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1 < 2 ^ 44) by lia.
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
rewrite restrict_mkst_fx. unfold ss1. unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [g0; g1; b1; q1; q2])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply ent_stk | apply Forall_cons; [| apply ent_ro]].
unfold shreg1, region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app].
change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by lia.
split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: first
[ apply chunk_ok_zero; intros i Hi; rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|];
rewrite <- (ra_granule_zero (aview tfibsegs H mem) d n (g0 + i) HRA ltac:(lia) Hd); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0 _ 1 (SOff 34 0) b1); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
- apply pairwise_disjoint_of_extents. unfold stk, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2, E32, unsigned_lit_small by lia. unfold MS_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok facts1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E12, E32, E34, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; apply Z.mod_1_r.
+ cbn [f_alias aliases1 alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_srl3, (U_atom EE 10 d E10), (U_atom EE 32 g0 E32) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 10 12 d n E10 E12), (U_atom_off EE 32 g0 2 E32) by lia. subst g0 g1. lia.
Qed.
Lemma ent1_3 : forall b1 q1 q2, 1 <= n <= 64 -> g1 - g0 = 3 -> aview tfibsegs H mem (SB + g1) = Some b1 -> saddr_ok (d + n - 1) b1 ->
st_ok tfibsegs (Env [g0; g1; b1; q1; q2]) (ss1 3) (restrict H (mkst regs (Z_to_bv 64 MS_ENTRY) mem (seg_rom tfibsegs))).
Proof.
intros b1 q1 q2 Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bpres & BM).
set (EE := Env [g0; g1; b1; q1; q2]).
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (apply (Env_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (Env_x _ 2); reflexivity).
pose proof (Env2 [g0; g1; b1; q1; q2]) as E2. pose proof (Env10 [g0; g1; b1; q1; q2]) as E10. pose proof (Env12 [g0; g1; b1; q1; q2]) as E12.
fold EE in E2, E10, E12.
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= d < 8 * g0 + 8) by (subst g0; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1 <= d + n - 1 < 8 * g1 + 8) by (subst g1; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1 < 2 ^ 44) by lia.
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
rewrite restrict_mkst_fx. unfold ss1. unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [g0; g1; b1; q1; q2])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply ent_stk | apply Forall_cons; [| apply ent_ro]].
unfold shreg1, region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app].
change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by lia.
split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: first
[ apply chunk_ok_zero; intros i Hi; rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|];
rewrite <- (ra_granule_zero (aview tfibsegs H mem) d n (g0 + i) HRA ltac:(lia) Hd); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0 _ 1 (SOff 34 0) b1); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
- apply pairwise_disjoint_of_extents. unfold stk, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2, E32, unsigned_lit_small by lia. unfold MS_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok facts1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E12, E32, E34, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; apply Z.mod_1_r.
+ cbn [f_alias aliases1 alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_srl3, (U_atom EE 10 d E10), (U_atom EE 32 g0 E32) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 10 12 d n E10 E12), (U_atom_off EE 32 g0 3 E32) by lia. subst g0 g1. lia.
Qed.
Lemma ent1_4 : forall b1 q1 q2, 1 <= n <= 64 -> g1 - g0 = 4 -> aview tfibsegs H mem (SB + g1) = Some b1 -> saddr_ok (d + n - 1) b1 ->
st_ok tfibsegs (Env [g0; g1; b1; q1; q2]) (ss1 4) (restrict H (mkst regs (Z_to_bv 64 MS_ENTRY) mem (seg_rom tfibsegs))).
Proof.
intros b1 q1 q2 Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bpres & BM).
set (EE := Env [g0; g1; b1; q1; q2]).
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (apply (Env_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (Env_x _ 2); reflexivity).
pose proof (Env2 [g0; g1; b1; q1; q2]) as E2. pose proof (Env10 [g0; g1; b1; q1; q2]) as E10. pose proof (Env12 [g0; g1; b1; q1; q2]) as E12.
fold EE in E2, E10, E12.
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= d < 8 * g0 + 8) by (subst g0; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1 <= d + n - 1 < 8 * g1 + 8) by (subst g1; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1 < 2 ^ 44) by lia.
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
rewrite restrict_mkst_fx. unfold ss1. unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [g0; g1; b1; q1; q2])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply ent_stk | apply Forall_cons; [| apply ent_ro]].
unfold shreg1, region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app].
change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by lia.
split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: first
[ apply chunk_ok_zero; intros i Hi; rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|];
rewrite <- (ra_granule_zero (aview tfibsegs H mem) d n (g0 + i) HRA ltac:(lia) Hd); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0 _ 1 (SOff 34 0) b1); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
- apply pairwise_disjoint_of_extents. unfold stk, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2, E32, unsigned_lit_small by lia. unfold MS_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok facts1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E12, E32, E34, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; apply Z.mod_1_r.
+ cbn [f_alias aliases1 alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_srl3, (U_atom EE 10 d E10), (U_atom EE 32 g0 E32) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 10 12 d n E10 E12), (U_atom_off EE 32 g0 4 E32) by lia. subst g0 g1. lia.
Qed.
Lemma ent1_5 : forall b1 q1 q2, 1 <= n <= 64 -> g1 - g0 = 5 -> aview tfibsegs H mem (SB + g1) = Some b1 -> saddr_ok (d + n - 1) b1 ->
st_ok tfibsegs (Env [g0; g1; b1; q1; q2]) (ss1 5) (restrict H (mkst regs (Z_to_bv 64 MS_ENTRY) mem (seg_rom tfibsegs))).
Proof.
intros b1 q1 q2 Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bpres & BM).
set (EE := Env [g0; g1; b1; q1; q2]).
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (apply (Env_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (Env_x _ 2); reflexivity).
pose proof (Env2 [g0; g1; b1; q1; q2]) as E2. pose proof (Env10 [g0; g1; b1; q1; q2]) as E10. pose proof (Env12 [g0; g1; b1; q1; q2]) as E12.
fold EE in E2, E10, E12.
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= d < 8 * g0 + 8) by (subst g0; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1 <= d + n - 1 < 8 * g1 + 8) by (subst g1; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1 < 2 ^ 44) by lia.
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
rewrite restrict_mkst_fx. unfold ss1. unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [g0; g1; b1; q1; q2])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply ent_stk | apply Forall_cons; [| apply ent_ro]].
unfold shreg1, region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app].
change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by lia.
split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: first
[ apply chunk_ok_zero; intros i Hi; rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|];
rewrite <- (ra_granule_zero (aview tfibsegs H mem) d n (g0 + i) HRA ltac:(lia) Hd); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0 _ 1 (SOff 34 0) b1); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
- apply pairwise_disjoint_of_extents. unfold stk, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2, E32, unsigned_lit_small by lia. unfold MS_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok facts1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E12, E32, E34, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; apply Z.mod_1_r.
+ cbn [f_alias aliases1 alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_srl3, (U_atom EE 10 d E10), (U_atom EE 32 g0 E32) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 10 12 d n E10 E12), (U_atom_off EE 32 g0 5 E32) by lia. subst g0 g1. lia.
Qed.
Lemma ent1_6 : forall b1 q1 q2, 1 <= n <= 64 -> g1 - g0 = 6 -> aview tfibsegs H mem (SB + g1) = Some b1 -> saddr_ok (d + n - 1) b1 ->
st_ok tfibsegs (Env [g0; g1; b1; q1; q2]) (ss1 6) (restrict H (mkst regs (Z_to_bv 64 MS_ENTRY) mem (seg_rom tfibsegs))).
Proof.
intros b1 q1 q2 Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bpres & BM).
set (EE := Env [g0; g1; b1; q1; q2]).
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (apply (Env_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (Env_x _ 2); reflexivity).
pose proof (Env2 [g0; g1; b1; q1; q2]) as E2. pose proof (Env10 [g0; g1; b1; q1; q2]) as E10. pose proof (Env12 [g0; g1; b1; q1; q2]) as E12.
fold EE in E2, E10, E12.
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= d < 8 * g0 + 8) by (subst g0; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1 <= d + n - 1 < 8 * g1 + 8) by (subst g1; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1 < 2 ^ 44) by lia.
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
rewrite restrict_mkst_fx. unfold ss1. unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [g0; g1; b1; q1; q2])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply ent_stk | apply Forall_cons; [| apply ent_ro]].
unfold shreg1, region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app].
change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by lia.
split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: first
[ apply chunk_ok_zero; intros i Hi; rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|];
rewrite <- (ra_granule_zero (aview tfibsegs H mem) d n (g0 + i) HRA ltac:(lia) Hd); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0 _ 1 (SOff 34 0) b1); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
- apply pairwise_disjoint_of_extents. unfold stk, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2, E32, unsigned_lit_small by lia. unfold MS_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok facts1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E12, E32, E34, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; apply Z.mod_1_r.
+ cbn [f_alias aliases1 alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_srl3, (U_atom EE 10 d E10), (U_atom EE 32 g0 E32) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 10 12 d n E10 E12), (U_atom_off EE 32 g0 6 E32) by lia. subst g0 g1. lia.
Qed.
Lemma ent1_7 : forall b1 q1 q2, 1 <= n <= 64 -> g1 - g0 = 7 -> aview tfibsegs H mem (SB + g1) = Some b1 -> saddr_ok (d + n - 1) b1 ->
st_ok tfibsegs (Env [g0; g1; b1; q1; q2]) (ss1 7) (restrict H (mkst regs (Z_to_bv 64 MS_ENTRY) mem (seg_rom tfibsegs))).
Proof.
intros b1 q1 q2 Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bpres & BM).
set (EE := Env [g0; g1; b1; q1; q2]).
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (apply (Env_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (Env_x _ 2); reflexivity).
pose proof (Env2 [g0; g1; b1; q1; q2]) as E2. pose proof (Env10 [g0; g1; b1; q1; q2]) as E10. pose proof (Env12 [g0; g1; b1; q1; q2]) as E12.
fold EE in E2, E10, E12.
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= d < 8 * g0 + 8) by (subst g0; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1 <= d + n - 1 < 8 * g1 + 8) by (subst g1; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1 < 2 ^ 44) by lia.
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
rewrite restrict_mkst_fx. unfold ss1. unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [g0; g1; b1; q1; q2])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply ent_stk | apply Forall_cons; [| apply ent_ro]].
unfold shreg1, region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app].
change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by lia.
split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: first
[ apply chunk_ok_zero; intros i Hi; rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|];
rewrite <- (ra_granule_zero (aview tfibsegs H mem) d n (g0 + i) HRA ltac:(lia) Hd); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0 _ 1 (SOff 34 0) b1); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
- apply pairwise_disjoint_of_extents. unfold stk, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2, E32, unsigned_lit_small by lia. unfold MS_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok facts1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E12, E32, E34, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; apply Z.mod_1_r.
+ cbn [f_alias aliases1 alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_srl3, (U_atom EE 10 d E10), (U_atom EE 32 g0 E32) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 10 12 d n E10 E12), (U_atom_off EE 32 g0 7 E32) by lia. subst g0 g1. lia.
Qed.
Lemma ent1_8 : forall b1 q1 q2, 1 <= n <= 64 -> g1 - g0 = 8 -> aview tfibsegs H mem (SB + g1) = Some b1 -> saddr_ok (d + n - 1) b1 ->
st_ok tfibsegs (Env [g0; g1; b1; q1; q2]) (ss1 8) (restrict H (mkst regs (Z_to_bv 64 MS_ENTRY) mem (seg_rom tfibsegs))).
Proof.
intros b1 q1 q2 Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bpres & BM).
set (EE := Env [g0; g1; b1; q1; q2]).
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (apply (Env_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (Env_x _ 2); reflexivity).
pose proof (Env2 [g0; g1; b1; q1; q2]) as E2. pose proof (Env10 [g0; g1; b1; q1; q2]) as E10. pose proof (Env12 [g0; g1; b1; q1; q2]) as E12.
fold EE in E2, E10, E12.
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= d < 8 * g0 + 8) by (subst g0; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1 <= d + n - 1 < 8 * g1 + 8) by (subst g1; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1 < 2 ^ 44) by lia.
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
rewrite restrict_mkst_fx. unfold ss1. unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [g0; g1; b1; q1; q2])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply ent_stk | apply Forall_cons; [| apply ent_ro]].
unfold shreg1, region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app].
change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by lia.
split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: first
[ apply chunk_ok_zero; intros i Hi; rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|];
rewrite <- (ra_granule_zero (aview tfibsegs H mem) d n (g0 + i) HRA ltac:(lia) Hd); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0 _ 1 (SOff 34 0) b1); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
- apply pairwise_disjoint_of_extents. unfold stk, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2, E32, unsigned_lit_small by lia. unfold MS_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok facts1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E12, E32, E34, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; apply Z.mod_1_r.
+ cbn [f_alias aliases1 alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_srl3, (U_atom EE 10 d E10), (U_atom EE 32 g0 E32) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 10 12 d n E10 E12), (U_atom_off EE 32 g0 8 E32) by lia. subst g0 g1. lia.
Qed.
Lemma path1_0 : 1 <= n <= 64 -> g1 - g0 = 0 -> SRr tfibsegs W (cfg_at tfibsegs MS_ENTRY regs mem md) POSTm.
Proof.
intros Hn64 Ht.
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bpres & BM). assert (HSC : MS_SCR = 2200) by reflexivity.
unfold cfg_at. change (w64 MS_ENTRY) with (Z_to_bv 64 MS_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 MS_ENTRY) mem (seg_rom tfibsegs)) z = mem z) by (intros; reflexivity).
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= d < 8 * g0 + 8) by (subst g0; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1 <= d + n - 1 < 8 * g1 + 8) by (subst g1; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1 < 2 ^ 44) by lia.
destruct (ra_last (aview tfibsegs H mem) d n HRA ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
pose proof (HHULL ltac:(lia)) as HH.
set (h1 := (g0 + 2147450880) / 8 * 8). set (h2 := (g1 + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0 + 2147450880 < h1 + 8) by (subst h1; pose proof (Z.div_mod (g0 + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g0 + 2147450880) 8 ltac:(lia)); lia).
assert (Hh2 : h2 <= g1 + 2147450880 < h2 + 8) by (subst h2; pose proof (Z.div_mod (g1 + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g1 + 2147450880) 8 ltac:(lia)); lia).
assert (Hh12 : h1 <= h2) by (subst h1 h2; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
assert (Hsh1 : shadow_addr d / 8 * 8 = h1) by (subst h1; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g0; f_equal; f_equal; lia).
assert (Hsh2 : shadow_addr (d + n - 1) / 8 * 8 = h2) by (subst h2; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g1; f_equal; f_equal; lia).
destruct (hull_rdword H mem d n h1 HH ltac:(lia) ltac:(lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem d n h2 HH ltac:(lia) ltac:(lia)) as (q2 & Hq2 & Rq2).
set (EE := Env [g0; g1; b1; q1; q2]). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply Env_reg; assumption).
pose proof (Env2 [g0; g1; b1; q1; q2]) as EE2. pose proof (Env10 [g0; g1; b1; q1; q2]) as EE10. pose proof (Env12 [g0; g1; b1; q1; q2]) as EE12. fold EE in EE2, EE10, EE12.
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (apply (Env_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (Env_x _ 2); reflexivity).
assert (E35 : ew EE 35 = Z_to_bv 64 q1) by (apply (Env_x _ 3); reflexivity).
assert (E36 : ew EE 36 = Z_to_bv 64 q2) by (apply (Env_x _ 4); reflexivity).
pose proof (ent1_0 b1 q1 q2 Hn64 Ht Hb1 Hok) as HS0. fold EE in HS0.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS0 r_p1_0_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG p1_0_e0 13) (RG p1_0_e0 12) HS1 (br_ovf_false EE 10 12 d n EE10 EE12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_p1_0_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG p1_0_e1 14) (RG p1_0_e1 13) HS2 (br_cls_small EE n EE12 Hn64)) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_p1_0_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF3 HFr3.
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply MEQ3. rewrite unsigned_lit_small by lia. unfold MS_STK, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (p1_0_e2) ms3 _ 16%bv 16%bv 538627 h1 35 48 HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (U_hull_addr EE 32 g0 2147450880 E32 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4).
assert (MEQ4 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z) by (intros z Hz; rewrite HM4; apply MEQ3; exact Hz).
clear HM4 HW4 HS3.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450880) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0 2147450880 E32) by lia. f_equal. subst h2. replace (g0 + 2147450880) with (g1 + 2147450880) by lia. reflexivity. }
assert (HW5 : rdword (aview tfibsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply MEQ4. rewrite unsigned_lit_small by lia. unfold MS_STK, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (set_regs_pc p1_0_e2 [((16%bv : bv 5), SOff 35 0)] (ss_pc p1_0_e2 + 4)) ms4 _ 17%bv 17%bv 571523 h2 36 48 HS4 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (Hrs2) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW5)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HM5).
assert (MEQ5 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z) by (intros z Hz; rewrite HM5; apply MEQ4; exact Hz).
clear HM5 HW5 HS4.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS5 r_p1_0_3)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF6 HFr6.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_NE (RG p1_0_e3 16) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_p1_0z_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF7 HFr7.
apply (finish EE p1_0z_e0 ms7 mat7 HS7 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ7. unfold MS_SCR, MS_STK in *. lia.
- intros a Ha; unfold MS_SCR, MS_STK in *; apply (apresent_same H mem (ms_mem ms7) a); [apply MEQ7; rewrite unsigned_lit_small by lia; lia | apply Bpres; lia].
+
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_NE (RG p1_0_e3 16) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_p1_0n_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF7 HFr7.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG p1_0n_e0 13) (SLit 0) HS7 (qc_flag_zero EE 0%nat 10 12 34 d n b1 EE10 EE12 E34 Hd ltac:(lia) Hdn ltac:(lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS7' r_p1_0n_1)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF8 HFr8.
apply (finish EE p1_0n_e1 ms8 mat8 HS8 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ8. unfold MS_SCR, MS_STK in *. lia.
- intros a Ha; unfold MS_SCR, MS_STK in *; apply (apresent_same H mem (ms_mem ms8) a); [apply MEQ8; rewrite unsigned_lit_small by lia; lia | apply Bpres; lia].
Qed.
Lemma path1_1 : 1 <= n <= 64 -> g1 - g0 = 1 -> SRr tfibsegs W (cfg_at tfibsegs MS_ENTRY regs mem md) POSTm.
Proof.
intros Hn64 Ht.
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bpres & BM). assert (HSC : MS_SCR = 2200) by reflexivity.
unfold cfg_at. change (w64 MS_ENTRY) with (Z_to_bv 64 MS_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 MS_ENTRY) mem (seg_rom tfibsegs)) z = mem z) by (intros; reflexivity).
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= d < 8 * g0 + 8) by (subst g0; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1 <= d + n - 1 < 8 * g1 + 8) by (subst g1; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1 < 2 ^ 44) by lia.
destruct (ra_last (aview tfibsegs H mem) d n HRA ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
pose proof (HHULL ltac:(lia)) as HH.
set (h1 := (g0 + 2147450880) / 8 * 8). set (h2 := (g1 + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0 + 2147450880 < h1 + 8) by (subst h1; pose proof (Z.div_mod (g0 + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g0 + 2147450880) 8 ltac:(lia)); lia).
assert (Hh2 : h2 <= g1 + 2147450880 < h2 + 8) by (subst h2; pose proof (Z.div_mod (g1 + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g1 + 2147450880) 8 ltac:(lia)); lia).
assert (Hh12 : h1 <= h2) by (subst h1 h2; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
assert (Hsh1 : shadow_addr d / 8 * 8 = h1) by (subst h1; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g0; f_equal; f_equal; lia).
assert (Hsh2 : shadow_addr (d + n - 1) / 8 * 8 = h2) by (subst h2; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g1; f_equal; f_equal; lia).
destruct (hull_rdword H mem d n h1 HH ltac:(lia) ltac:(lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem d n h2 HH ltac:(lia) ltac:(lia)) as (q2 & Hq2 & Rq2).
set (EE := Env [g0; g1; b1; q1; q2]). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply Env_reg; assumption).
pose proof (Env2 [g0; g1; b1; q1; q2]) as EE2. pose proof (Env10 [g0; g1; b1; q1; q2]) as EE10. pose proof (Env12 [g0; g1; b1; q1; q2]) as EE12. fold EE in EE2, EE10, EE12.
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (apply (Env_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (Env_x _ 2); reflexivity).
assert (E35 : ew EE 35 = Z_to_bv 64 q1) by (apply (Env_x _ 3); reflexivity).
assert (E36 : ew EE 36 = Z_to_bv 64 q2) by (apply (Env_x _ 4); reflexivity).
pose proof (ent1_1 b1 q1 q2 Hn64 Ht Hb1 Hok) as HS0. fold EE in HS0.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS0 r_p1_1_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG p1_1_e0 13) (RG p1_1_e0 12) HS1 (br_ovf_false EE 10 12 d n EE10 EE12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_p1_1_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG p1_1_e1 14) (RG p1_1_e1 13) HS2 (br_cls_small EE n EE12 Hn64)) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_p1_1_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF3 HFr3.
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply MEQ3. rewrite unsigned_lit_small by lia. unfold MS_STK, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (p1_1_e2) ms3 _ 16%bv 16%bv 538627 h1 35 48 HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (U_hull_addr EE 32 g0 2147450880 E32 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4).
assert (MEQ4 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z) by (intros z Hz; rewrite HM4; apply MEQ3; exact Hz).
clear HM4 HW4 HS3.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450881) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0 2147450881 E32) by lia. f_equal. subst h2. replace (g0 + 2147450881) with (g1 + 2147450880) by lia. reflexivity. }
assert (HW5 : rdword (aview tfibsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply MEQ4. rewrite unsigned_lit_small by lia. unfold MS_STK, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (set_regs_pc p1_1_e2 [((16%bv : bv 5), SOff 35 0)] (ss_pc p1_1_e2 + 4)) ms4 _ 17%bv 17%bv 571523 h2 36 48 HS4 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (Hrs2) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW5)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HM5).
assert (MEQ5 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z) by (intros z Hz; rewrite HM5; apply MEQ4; exact Hz).
clear HM5 HW5 HS4.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS5 r_p1_1_3)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF6 HFr6.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_NE (RG p1_1_e3 16) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_p1_1z_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF7 HFr7.
apply (finish EE p1_1z_e0 ms7 mat7 HS7 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ7. unfold MS_SCR, MS_STK in *. lia.
- intros a Ha; unfold MS_SCR, MS_STK in *; apply (apresent_same H mem (ms_mem ms7) a); [apply MEQ7; rewrite unsigned_lit_small by lia; lia | apply Bpres; lia].
+
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_NE (RG p1_1_e3 16) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_p1_1n_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF7 HFr7.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG p1_1n_e0 13) (SLit 0) HS7 (qc_flag_zero EE 1%nat 10 12 34 d n b1 EE10 EE12 E34 Hd ltac:(lia) Hdn ltac:(lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS7' r_p1_1n_1)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF8 HFr8.
apply (finish EE p1_1n_e1 ms8 mat8 HS8 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ8. unfold MS_SCR, MS_STK in *. lia.
- intros a Ha; unfold MS_SCR, MS_STK in *; apply (apresent_same H mem (ms_mem ms8) a); [apply MEQ8; rewrite unsigned_lit_small by lia; lia | apply Bpres; lia].
Qed.
Lemma path1_2 : 1 <= n <= 64 -> g1 - g0 = 2 -> SRr tfibsegs W (cfg_at tfibsegs MS_ENTRY regs mem md) POSTm.
Proof.
intros Hn64 Ht.
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bpres & BM). assert (HSC : MS_SCR = 2200) by reflexivity.
unfold cfg_at. change (w64 MS_ENTRY) with (Z_to_bv 64 MS_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 MS_ENTRY) mem (seg_rom tfibsegs)) z = mem z) by (intros; reflexivity).
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= d < 8 * g0 + 8) by (subst g0; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1 <= d + n - 1 < 8 * g1 + 8) by (subst g1; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1 < 2 ^ 44) by lia.
destruct (ra_last (aview tfibsegs H mem) d n HRA ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
pose proof (HHULL ltac:(lia)) as HH.
set (h1 := (g0 + 2147450880) / 8 * 8). set (h2 := (g1 + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0 + 2147450880 < h1 + 8) by (subst h1; pose proof (Z.div_mod (g0 + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g0 + 2147450880) 8 ltac:(lia)); lia).
assert (Hh2 : h2 <= g1 + 2147450880 < h2 + 8) by (subst h2; pose proof (Z.div_mod (g1 + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g1 + 2147450880) 8 ltac:(lia)); lia).
assert (Hh12 : h1 <= h2) by (subst h1 h2; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
assert (Hsh1 : shadow_addr d / 8 * 8 = h1) by (subst h1; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g0; f_equal; f_equal; lia).
assert (Hsh2 : shadow_addr (d + n - 1) / 8 * 8 = h2) by (subst h2; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g1; f_equal; f_equal; lia).
destruct (hull_rdword H mem d n h1 HH ltac:(lia) ltac:(lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem d n h2 HH ltac:(lia) ltac:(lia)) as (q2 & Hq2 & Rq2).
set (EE := Env [g0; g1; b1; q1; q2]). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply Env_reg; assumption).
pose proof (Env2 [g0; g1; b1; q1; q2]) as EE2. pose proof (Env10 [g0; g1; b1; q1; q2]) as EE10. pose proof (Env12 [g0; g1; b1; q1; q2]) as EE12. fold EE in EE2, EE10, EE12.
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (apply (Env_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (Env_x _ 2); reflexivity).
assert (E35 : ew EE 35 = Z_to_bv 64 q1) by (apply (Env_x _ 3); reflexivity).
assert (E36 : ew EE 36 = Z_to_bv 64 q2) by (apply (Env_x _ 4); reflexivity).
pose proof (ent1_2 b1 q1 q2 Hn64 Ht Hb1 Hok) as HS0. fold EE in HS0.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS0 r_p1_2_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG p1_2_e0 13) (RG p1_2_e0 12) HS1 (br_ovf_false EE 10 12 d n EE10 EE12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_p1_2_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG p1_2_e1 14) (RG p1_2_e1 13) HS2 (br_cls_small EE n EE12 Hn64)) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_p1_2_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF3 HFr3.
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply MEQ3. rewrite unsigned_lit_small by lia. unfold MS_STK, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (p1_2_e2) ms3 _ 16%bv 16%bv 538627 h1 35 48 HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (U_hull_addr EE 32 g0 2147450880 E32 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4).
assert (MEQ4 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z) by (intros z Hz; rewrite HM4; apply MEQ3; exact Hz).
clear HM4 HW4 HS3.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450882) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0 2147450882 E32) by lia. f_equal. subst h2. replace (g0 + 2147450882) with (g1 + 2147450880) by lia. reflexivity. }
assert (HW5 : rdword (aview tfibsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply MEQ4. rewrite unsigned_lit_small by lia. unfold MS_STK, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (set_regs_pc p1_2_e2 [((16%bv : bv 5), SOff 35 0)] (ss_pc p1_2_e2 + 4)) ms4 _ 17%bv 17%bv 571523 h2 36 48 HS4 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (Hrs2) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW5)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HM5).
assert (MEQ5 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z) by (intros z Hz; rewrite HM5; apply MEQ4; exact Hz).
clear HM5 HW5 HS4.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS5 r_p1_2_3)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF6 HFr6.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_NE (RG p1_2_e3 16) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_p1_2z_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF7 HFr7.
apply (finish EE p1_2z_e0 ms7 mat7 HS7 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ7. unfold MS_SCR, MS_STK in *. lia.
- intros a Ha; unfold MS_SCR, MS_STK in *; apply (apresent_same H mem (ms_mem ms7) a); [apply MEQ7; rewrite unsigned_lit_small by lia; lia | apply Bpres; lia].
+
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_NE (RG p1_2_e3 16) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_p1_2n_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF7 HFr7.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG p1_2n_e0 13) (SLit 0) HS7 (qc_flag_zero EE 2%nat 10 12 34 d n b1 EE10 EE12 E34 Hd ltac:(lia) Hdn ltac:(lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS7' r_p1_2n_1)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF8 HFr8.
apply (finish EE p1_2n_e1 ms8 mat8 HS8 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ8. unfold MS_SCR, MS_STK in *. lia.
- intros a Ha; unfold MS_SCR, MS_STK in *; apply (apresent_same H mem (ms_mem ms8) a); [apply MEQ8; rewrite unsigned_lit_small by lia; lia | apply Bpres; lia].
Qed.
Lemma path1_3 : 1 <= n <= 64 -> g1 - g0 = 3 -> SRr tfibsegs W (cfg_at tfibsegs MS_ENTRY regs mem md) POSTm.
Proof.
intros Hn64 Ht.
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bpres & BM). assert (HSC : MS_SCR = 2200) by reflexivity.
unfold cfg_at. change (w64 MS_ENTRY) with (Z_to_bv 64 MS_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 MS_ENTRY) mem (seg_rom tfibsegs)) z = mem z) by (intros; reflexivity).
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= d < 8 * g0 + 8) by (subst g0; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1 <= d + n - 1 < 8 * g1 + 8) by (subst g1; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1 < 2 ^ 44) by lia.
destruct (ra_last (aview tfibsegs H mem) d n HRA ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
pose proof (HHULL ltac:(lia)) as HH.
set (h1 := (g0 + 2147450880) / 8 * 8). set (h2 := (g1 + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0 + 2147450880 < h1 + 8) by (subst h1; pose proof (Z.div_mod (g0 + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g0 + 2147450880) 8 ltac:(lia)); lia).
assert (Hh2 : h2 <= g1 + 2147450880 < h2 + 8) by (subst h2; pose proof (Z.div_mod (g1 + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g1 + 2147450880) 8 ltac:(lia)); lia).
assert (Hh12 : h1 <= h2) by (subst h1 h2; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
assert (Hsh1 : shadow_addr d / 8 * 8 = h1) by (subst h1; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g0; f_equal; f_equal; lia).
assert (Hsh2 : shadow_addr (d + n - 1) / 8 * 8 = h2) by (subst h2; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g1; f_equal; f_equal; lia).
destruct (hull_rdword H mem d n h1 HH ltac:(lia) ltac:(lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem d n h2 HH ltac:(lia) ltac:(lia)) as (q2 & Hq2 & Rq2).
set (EE := Env [g0; g1; b1; q1; q2]). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply Env_reg; assumption).
pose proof (Env2 [g0; g1; b1; q1; q2]) as EE2. pose proof (Env10 [g0; g1; b1; q1; q2]) as EE10. pose proof (Env12 [g0; g1; b1; q1; q2]) as EE12. fold EE in EE2, EE10, EE12.
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (apply (Env_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (Env_x _ 2); reflexivity).
assert (E35 : ew EE 35 = Z_to_bv 64 q1) by (apply (Env_x _ 3); reflexivity).
assert (E36 : ew EE 36 = Z_to_bv 64 q2) by (apply (Env_x _ 4); reflexivity).
pose proof (ent1_3 b1 q1 q2 Hn64 Ht Hb1 Hok) as HS0. fold EE in HS0.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS0 r_p1_3_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG p1_3_e0 13) (RG p1_3_e0 12) HS1 (br_ovf_false EE 10 12 d n EE10 EE12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_p1_3_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG p1_3_e1 14) (RG p1_3_e1 13) HS2 (br_cls_small EE n EE12 Hn64)) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_p1_3_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF3 HFr3.
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply MEQ3. rewrite unsigned_lit_small by lia. unfold MS_STK, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (p1_3_e2) ms3 _ 16%bv 16%bv 538627 h1 35 48 HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (U_hull_addr EE 32 g0 2147450880 E32 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4).
assert (MEQ4 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z) by (intros z Hz; rewrite HM4; apply MEQ3; exact Hz).
clear HM4 HW4 HS3.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450883) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0 2147450883 E32) by lia. f_equal. subst h2. replace (g0 + 2147450883) with (g1 + 2147450880) by lia. reflexivity. }
assert (HW5 : rdword (aview tfibsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply MEQ4. rewrite unsigned_lit_small by lia. unfold MS_STK, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (set_regs_pc p1_3_e2 [((16%bv : bv 5), SOff 35 0)] (ss_pc p1_3_e2 + 4)) ms4 _ 17%bv 17%bv 571523 h2 36 48 HS4 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (Hrs2) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW5)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HM5).
assert (MEQ5 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z) by (intros z Hz; rewrite HM5; apply MEQ4; exact Hz).
clear HM5 HW5 HS4.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS5 r_p1_3_3)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF6 HFr6.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_NE (RG p1_3_e3 16) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_p1_3z_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF7 HFr7.
apply (finish EE p1_3z_e0 ms7 mat7 HS7 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ7. unfold MS_SCR, MS_STK in *. lia.
- intros a Ha; unfold MS_SCR, MS_STK in *; apply (apresent_same H mem (ms_mem ms7) a); [apply MEQ7; rewrite unsigned_lit_small by lia; lia | apply Bpres; lia].
+
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_NE (RG p1_3_e3 16) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_p1_3n_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF7 HFr7.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG p1_3n_e0 13) (SLit 0) HS7 (qc_flag_zero EE 3%nat 10 12 34 d n b1 EE10 EE12 E34 Hd ltac:(lia) Hdn ltac:(lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS7' r_p1_3n_1)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF8 HFr8.
apply (finish EE p1_3n_e1 ms8 mat8 HS8 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ8. unfold MS_SCR, MS_STK in *. lia.
- intros a Ha; unfold MS_SCR, MS_STK in *; apply (apresent_same H mem (ms_mem ms8) a); [apply MEQ8; rewrite unsigned_lit_small by lia; lia | apply Bpres; lia].
Qed.
Lemma path1_4 : 1 <= n <= 64 -> g1 - g0 = 4 -> SRr tfibsegs W (cfg_at tfibsegs MS_ENTRY regs mem md) POSTm.
Proof.
intros Hn64 Ht.
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bpres & BM). assert (HSC : MS_SCR = 2200) by reflexivity.
unfold cfg_at. change (w64 MS_ENTRY) with (Z_to_bv 64 MS_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 MS_ENTRY) mem (seg_rom tfibsegs)) z = mem z) by (intros; reflexivity).
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= d < 8 * g0 + 8) by (subst g0; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1 <= d + n - 1 < 8 * g1 + 8) by (subst g1; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1 < 2 ^ 44) by lia.
destruct (ra_last (aview tfibsegs H mem) d n HRA ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
pose proof (HHULL ltac:(lia)) as HH.
set (h1 := (g0 + 2147450880) / 8 * 8). set (h2 := (g1 + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0 + 2147450880 < h1 + 8) by (subst h1; pose proof (Z.div_mod (g0 + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g0 + 2147450880) 8 ltac:(lia)); lia).
assert (Hh2 : h2 <= g1 + 2147450880 < h2 + 8) by (subst h2; pose proof (Z.div_mod (g1 + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g1 + 2147450880) 8 ltac:(lia)); lia).
assert (Hh12 : h1 <= h2) by (subst h1 h2; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
assert (Hsh1 : shadow_addr d / 8 * 8 = h1) by (subst h1; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g0; f_equal; f_equal; lia).
assert (Hsh2 : shadow_addr (d + n - 1) / 8 * 8 = h2) by (subst h2; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g1; f_equal; f_equal; lia).
destruct (hull_rdword H mem d n h1 HH ltac:(lia) ltac:(lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem d n h2 HH ltac:(lia) ltac:(lia)) as (q2 & Hq2 & Rq2).
set (EE := Env [g0; g1; b1; q1; q2]). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply Env_reg; assumption).
pose proof (Env2 [g0; g1; b1; q1; q2]) as EE2. pose proof (Env10 [g0; g1; b1; q1; q2]) as EE10. pose proof (Env12 [g0; g1; b1; q1; q2]) as EE12. fold EE in EE2, EE10, EE12.
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (apply (Env_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (Env_x _ 2); reflexivity).
assert (E35 : ew EE 35 = Z_to_bv 64 q1) by (apply (Env_x _ 3); reflexivity).
assert (E36 : ew EE 36 = Z_to_bv 64 q2) by (apply (Env_x _ 4); reflexivity).
pose proof (ent1_4 b1 q1 q2 Hn64 Ht Hb1 Hok) as HS0. fold EE in HS0.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS0 r_p1_4_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG p1_4_e0 13) (RG p1_4_e0 12) HS1 (br_ovf_false EE 10 12 d n EE10 EE12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_p1_4_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG p1_4_e1 14) (RG p1_4_e1 13) HS2 (br_cls_small EE n EE12 Hn64)) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_p1_4_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF3 HFr3.
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply MEQ3. rewrite unsigned_lit_small by lia. unfold MS_STK, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (p1_4_e2) ms3 _ 16%bv 16%bv 538627 h1 35 48 HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (U_hull_addr EE 32 g0 2147450880 E32 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4).
assert (MEQ4 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z) by (intros z Hz; rewrite HM4; apply MEQ3; exact Hz).
clear HM4 HW4 HS3.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450884) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0 2147450884 E32) by lia. f_equal. subst h2. replace (g0 + 2147450884) with (g1 + 2147450880) by lia. reflexivity. }
assert (HW5 : rdword (aview tfibsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply MEQ4. rewrite unsigned_lit_small by lia. unfold MS_STK, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (set_regs_pc p1_4_e2 [((16%bv : bv 5), SOff 35 0)] (ss_pc p1_4_e2 + 4)) ms4 _ 17%bv 17%bv 571523 h2 36 48 HS4 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (Hrs2) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW5)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HM5).
assert (MEQ5 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z) by (intros z Hz; rewrite HM5; apply MEQ4; exact Hz).
clear HM5 HW5 HS4.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS5 r_p1_4_3)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF6 HFr6.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_NE (RG p1_4_e3 16) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_p1_4z_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF7 HFr7.
apply (finish EE p1_4z_e0 ms7 mat7 HS7 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ7. unfold MS_SCR, MS_STK in *. lia.
- intros a Ha; unfold MS_SCR, MS_STK in *; apply (apresent_same H mem (ms_mem ms7) a); [apply MEQ7; rewrite unsigned_lit_small by lia; lia | apply Bpres; lia].
+
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_NE (RG p1_4_e3 16) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_p1_4n_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF7 HFr7.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG p1_4n_e0 13) (SLit 0) HS7 (qc_flag_zero EE 4%nat 10 12 34 d n b1 EE10 EE12 E34 Hd ltac:(lia) Hdn ltac:(lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS7' r_p1_4n_1)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF8 HFr8.
apply (finish EE p1_4n_e1 ms8 mat8 HS8 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ8. unfold MS_SCR, MS_STK in *. lia.
- intros a Ha; unfold MS_SCR, MS_STK in *; apply (apresent_same H mem (ms_mem ms8) a); [apply MEQ8; rewrite unsigned_lit_small by lia; lia | apply Bpres; lia].
Qed.
Lemma path1_5 : 1 <= n <= 64 -> g1 - g0 = 5 -> SRr tfibsegs W (cfg_at tfibsegs MS_ENTRY regs mem md) POSTm.
Proof.
intros Hn64 Ht.
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bpres & BM). assert (HSC : MS_SCR = 2200) by reflexivity.
unfold cfg_at. change (w64 MS_ENTRY) with (Z_to_bv 64 MS_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 MS_ENTRY) mem (seg_rom tfibsegs)) z = mem z) by (intros; reflexivity).
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= d < 8 * g0 + 8) by (subst g0; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1 <= d + n - 1 < 8 * g1 + 8) by (subst g1; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1 < 2 ^ 44) by lia.
destruct (ra_last (aview tfibsegs H mem) d n HRA ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
pose proof (HHULL ltac:(lia)) as HH.
set (h1 := (g0 + 2147450880) / 8 * 8). set (h2 := (g1 + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0 + 2147450880 < h1 + 8) by (subst h1; pose proof (Z.div_mod (g0 + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g0 + 2147450880) 8 ltac:(lia)); lia).
assert (Hh2 : h2 <= g1 + 2147450880 < h2 + 8) by (subst h2; pose proof (Z.div_mod (g1 + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g1 + 2147450880) 8 ltac:(lia)); lia).
assert (Hh12 : h1 <= h2) by (subst h1 h2; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
assert (Hsh1 : shadow_addr d / 8 * 8 = h1) by (subst h1; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g0; f_equal; f_equal; lia).
assert (Hsh2 : shadow_addr (d + n - 1) / 8 * 8 = h2) by (subst h2; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g1; f_equal; f_equal; lia).
destruct (hull_rdword H mem d n h1 HH ltac:(lia) ltac:(lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem d n h2 HH ltac:(lia) ltac:(lia)) as (q2 & Hq2 & Rq2).
set (EE := Env [g0; g1; b1; q1; q2]). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply Env_reg; assumption).
pose proof (Env2 [g0; g1; b1; q1; q2]) as EE2. pose proof (Env10 [g0; g1; b1; q1; q2]) as EE10. pose proof (Env12 [g0; g1; b1; q1; q2]) as EE12. fold EE in EE2, EE10, EE12.
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (apply (Env_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (Env_x _ 2); reflexivity).
assert (E35 : ew EE 35 = Z_to_bv 64 q1) by (apply (Env_x _ 3); reflexivity).
assert (E36 : ew EE 36 = Z_to_bv 64 q2) by (apply (Env_x _ 4); reflexivity).
pose proof (ent1_5 b1 q1 q2 Hn64 Ht Hb1 Hok) as HS0. fold EE in HS0.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS0 r_p1_5_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG p1_5_e0 13) (RG p1_5_e0 12) HS1 (br_ovf_false EE 10 12 d n EE10 EE12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_p1_5_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG p1_5_e1 14) (RG p1_5_e1 13) HS2 (br_cls_small EE n EE12 Hn64)) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_p1_5_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF3 HFr3.
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply MEQ3. rewrite unsigned_lit_small by lia. unfold MS_STK, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (p1_5_e2) ms3 _ 16%bv 16%bv 538627 h1 35 48 HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (U_hull_addr EE 32 g0 2147450880 E32 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4).
assert (MEQ4 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z) by (intros z Hz; rewrite HM4; apply MEQ3; exact Hz).
clear HM4 HW4 HS3.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450885) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0 2147450885 E32) by lia. f_equal. subst h2. replace (g0 + 2147450885) with (g1 + 2147450880) by lia. reflexivity. }
assert (HW5 : rdword (aview tfibsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply MEQ4. rewrite unsigned_lit_small by lia. unfold MS_STK, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (set_regs_pc p1_5_e2 [((16%bv : bv 5), SOff 35 0)] (ss_pc p1_5_e2 + 4)) ms4 _ 17%bv 17%bv 571523 h2 36 48 HS4 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (Hrs2) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW5)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HM5).
assert (MEQ5 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z) by (intros z Hz; rewrite HM5; apply MEQ4; exact Hz).
clear HM5 HW5 HS4.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS5 r_p1_5_3)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF6 HFr6.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_NE (RG p1_5_e3 16) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_p1_5z_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF7 HFr7.
apply (finish EE p1_5z_e0 ms7 mat7 HS7 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ7. unfold MS_SCR, MS_STK in *. lia.
- intros a Ha; unfold MS_SCR, MS_STK in *; apply (apresent_same H mem (ms_mem ms7) a); [apply MEQ7; rewrite unsigned_lit_small by lia; lia | apply Bpres; lia].
+
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_NE (RG p1_5_e3 16) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_p1_5n_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF7 HFr7.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG p1_5n_e0 13) (SLit 0) HS7 (qc_flag_zero EE 5%nat 10 12 34 d n b1 EE10 EE12 E34 Hd ltac:(lia) Hdn ltac:(lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS7' r_p1_5n_1)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF8 HFr8.
apply (finish EE p1_5n_e1 ms8 mat8 HS8 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ8. unfold MS_SCR, MS_STK in *. lia.
- intros a Ha; unfold MS_SCR, MS_STK in *; apply (apresent_same H mem (ms_mem ms8) a); [apply MEQ8; rewrite unsigned_lit_small by lia; lia | apply Bpres; lia].
Qed.
Lemma path1_6 : 1 <= n <= 64 -> g1 - g0 = 6 -> SRr tfibsegs W (cfg_at tfibsegs MS_ENTRY regs mem md) POSTm.
Proof.
intros Hn64 Ht.
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bpres & BM). assert (HSC : MS_SCR = 2200) by reflexivity.
unfold cfg_at. change (w64 MS_ENTRY) with (Z_to_bv 64 MS_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 MS_ENTRY) mem (seg_rom tfibsegs)) z = mem z) by (intros; reflexivity).
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= d < 8 * g0 + 8) by (subst g0; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1 <= d + n - 1 < 8 * g1 + 8) by (subst g1; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1 < 2 ^ 44) by lia.
destruct (ra_last (aview tfibsegs H mem) d n HRA ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
pose proof (HHULL ltac:(lia)) as HH.
set (h1 := (g0 + 2147450880) / 8 * 8). set (h2 := (g1 + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0 + 2147450880 < h1 + 8) by (subst h1; pose proof (Z.div_mod (g0 + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g0 + 2147450880) 8 ltac:(lia)); lia).
assert (Hh2 : h2 <= g1 + 2147450880 < h2 + 8) by (subst h2; pose proof (Z.div_mod (g1 + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g1 + 2147450880) 8 ltac:(lia)); lia).
assert (Hh12 : h1 <= h2) by (subst h1 h2; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
assert (Hsh1 : shadow_addr d / 8 * 8 = h1) by (subst h1; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g0; f_equal; f_equal; lia).
assert (Hsh2 : shadow_addr (d + n - 1) / 8 * 8 = h2) by (subst h2; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g1; f_equal; f_equal; lia).
destruct (hull_rdword H mem d n h1 HH ltac:(lia) ltac:(lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem d n h2 HH ltac:(lia) ltac:(lia)) as (q2 & Hq2 & Rq2).
set (EE := Env [g0; g1; b1; q1; q2]). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply Env_reg; assumption).
pose proof (Env2 [g0; g1; b1; q1; q2]) as EE2. pose proof (Env10 [g0; g1; b1; q1; q2]) as EE10. pose proof (Env12 [g0; g1; b1; q1; q2]) as EE12. fold EE in EE2, EE10, EE12.
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (apply (Env_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (Env_x _ 2); reflexivity).
assert (E35 : ew EE 35 = Z_to_bv 64 q1) by (apply (Env_x _ 3); reflexivity).
assert (E36 : ew EE 36 = Z_to_bv 64 q2) by (apply (Env_x _ 4); reflexivity).
pose proof (ent1_6 b1 q1 q2 Hn64 Ht Hb1 Hok) as HS0. fold EE in HS0.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS0 r_p1_6_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG p1_6_e0 13) (RG p1_6_e0 12) HS1 (br_ovf_false EE 10 12 d n EE10 EE12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_p1_6_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG p1_6_e1 14) (RG p1_6_e1 13) HS2 (br_cls_small EE n EE12 Hn64)) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_p1_6_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF3 HFr3.
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply MEQ3. rewrite unsigned_lit_small by lia. unfold MS_STK, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (p1_6_e2) ms3 _ 16%bv 16%bv 538627 h1 35 48 HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (U_hull_addr EE 32 g0 2147450880 E32 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4).
assert (MEQ4 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z) by (intros z Hz; rewrite HM4; apply MEQ3; exact Hz).
clear HM4 HW4 HS3.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450886) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0 2147450886 E32) by lia. f_equal. subst h2. replace (g0 + 2147450886) with (g1 + 2147450880) by lia. reflexivity. }
assert (HW5 : rdword (aview tfibsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply MEQ4. rewrite unsigned_lit_small by lia. unfold MS_STK, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (set_regs_pc p1_6_e2 [((16%bv : bv 5), SOff 35 0)] (ss_pc p1_6_e2 + 4)) ms4 _ 17%bv 17%bv 571523 h2 36 48 HS4 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (Hrs2) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW5)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HM5).
assert (MEQ5 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z) by (intros z Hz; rewrite HM5; apply MEQ4; exact Hz).
clear HM5 HW5 HS4.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS5 r_p1_6_3)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF6 HFr6.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_NE (RG p1_6_e3 16) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_p1_6z_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF7 HFr7.
apply (finish EE p1_6z_e0 ms7 mat7 HS7 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ7. unfold MS_SCR, MS_STK in *. lia.
- intros a Ha; unfold MS_SCR, MS_STK in *; apply (apresent_same H mem (ms_mem ms7) a); [apply MEQ7; rewrite unsigned_lit_small by lia; lia | apply Bpres; lia].
+
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_NE (RG p1_6_e3 16) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_p1_6n_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF7 HFr7.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG p1_6n_e0 13) (SLit 0) HS7 (qc_flag_zero EE 6%nat 10 12 34 d n b1 EE10 EE12 E34 Hd ltac:(lia) Hdn ltac:(lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS7' r_p1_6n_1)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF8 HFr8.
apply (finish EE p1_6n_e1 ms8 mat8 HS8 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ8. unfold MS_SCR, MS_STK in *. lia.
- intros a Ha; unfold MS_SCR, MS_STK in *; apply (apresent_same H mem (ms_mem ms8) a); [apply MEQ8; rewrite unsigned_lit_small by lia; lia | apply Bpres; lia].
Qed.
Lemma path1_7 : 1 <= n <= 64 -> g1 - g0 = 7 -> SRr tfibsegs W (cfg_at tfibsegs MS_ENTRY regs mem md) POSTm.
Proof.
intros Hn64 Ht.
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bpres & BM). assert (HSC : MS_SCR = 2200) by reflexivity.
unfold cfg_at. change (w64 MS_ENTRY) with (Z_to_bv 64 MS_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 MS_ENTRY) mem (seg_rom tfibsegs)) z = mem z) by (intros; reflexivity).
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= d < 8 * g0 + 8) by (subst g0; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1 <= d + n - 1 < 8 * g1 + 8) by (subst g1; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1 < 2 ^ 44) by lia.
destruct (ra_last (aview tfibsegs H mem) d n HRA ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
pose proof (HHULL ltac:(lia)) as HH.
set (h1 := (g0 + 2147450880) / 8 * 8). set (h2 := (g1 + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0 + 2147450880 < h1 + 8) by (subst h1; pose proof (Z.div_mod (g0 + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g0 + 2147450880) 8 ltac:(lia)); lia).
assert (Hh2 : h2 <= g1 + 2147450880 < h2 + 8) by (subst h2; pose proof (Z.div_mod (g1 + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g1 + 2147450880) 8 ltac:(lia)); lia).
assert (Hh12 : h1 <= h2) by (subst h1 h2; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
assert (Hsh1 : shadow_addr d / 8 * 8 = h1) by (subst h1; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g0; f_equal; f_equal; lia).
assert (Hsh2 : shadow_addr (d + n - 1) / 8 * 8 = h2) by (subst h2; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g1; f_equal; f_equal; lia).
destruct (hull_rdword H mem d n h1 HH ltac:(lia) ltac:(lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem d n h2 HH ltac:(lia) ltac:(lia)) as (q2 & Hq2 & Rq2).
set (EE := Env [g0; g1; b1; q1; q2]). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply Env_reg; assumption).
pose proof (Env2 [g0; g1; b1; q1; q2]) as EE2. pose proof (Env10 [g0; g1; b1; q1; q2]) as EE10. pose proof (Env12 [g0; g1; b1; q1; q2]) as EE12. fold EE in EE2, EE10, EE12.
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (apply (Env_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (Env_x _ 2); reflexivity).
assert (E35 : ew EE 35 = Z_to_bv 64 q1) by (apply (Env_x _ 3); reflexivity).
assert (E36 : ew EE 36 = Z_to_bv 64 q2) by (apply (Env_x _ 4); reflexivity).
pose proof (ent1_7 b1 q1 q2 Hn64 Ht Hb1 Hok) as HS0. fold EE in HS0.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS0 r_p1_7_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG p1_7_e0 13) (RG p1_7_e0 12) HS1 (br_ovf_false EE 10 12 d n EE10 EE12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_p1_7_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG p1_7_e1 14) (RG p1_7_e1 13) HS2 (br_cls_small EE n EE12 Hn64)) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_p1_7_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF3 HFr3.
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply MEQ3. rewrite unsigned_lit_small by lia. unfold MS_STK, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (p1_7_e2) ms3 _ 16%bv 16%bv 538627 h1 35 48 HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (U_hull_addr EE 32 g0 2147450880 E32 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4).
assert (MEQ4 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z) by (intros z Hz; rewrite HM4; apply MEQ3; exact Hz).
clear HM4 HW4 HS3.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450887) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0 2147450887 E32) by lia. f_equal. subst h2. replace (g0 + 2147450887) with (g1 + 2147450880) by lia. reflexivity. }
assert (HW5 : rdword (aview tfibsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply MEQ4. rewrite unsigned_lit_small by lia. unfold MS_STK, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (set_regs_pc p1_7_e2 [((16%bv : bv 5), SOff 35 0)] (ss_pc p1_7_e2 + 4)) ms4 _ 17%bv 17%bv 571523 h2 36 48 HS4 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (Hrs2) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW5)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HM5).
assert (MEQ5 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z) by (intros z Hz; rewrite HM5; apply MEQ4; exact Hz).
clear HM5 HW5 HS4.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS5 r_p1_7_3)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF6 HFr6.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_NE (RG p1_7_e3 16) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_p1_7z_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF7 HFr7.
apply (finish EE p1_7z_e0 ms7 mat7 HS7 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ7. unfold MS_SCR, MS_STK in *. lia.
- intros a Ha; unfold MS_SCR, MS_STK in *; apply (apresent_same H mem (ms_mem ms7) a); [apply MEQ7; rewrite unsigned_lit_small by lia; lia | apply Bpres; lia].
+
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_NE (RG p1_7_e3 16) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_p1_7n_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF7 HFr7.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG p1_7n_e0 13) (SLit 0) HS7 (qc_flag_zero EE 7%nat 10 12 34 d n b1 EE10 EE12 E34 Hd ltac:(lia) Hdn ltac:(lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS7' r_p1_7n_1)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF8 HFr8.
apply (finish EE p1_7n_e1 ms8 mat8 HS8 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ8. unfold MS_SCR, MS_STK in *. lia.
- intros a Ha; unfold MS_SCR, MS_STK in *; apply (apresent_same H mem (ms_mem ms8) a); [apply MEQ8; rewrite unsigned_lit_small by lia; lia | apply Bpres; lia].
Qed.
Lemma path1_8 : 1 <= n <= 64 -> g1 - g0 = 8 -> SRr tfibsegs W (cfg_at tfibsegs MS_ENTRY regs mem md) POSTm.
Proof.
intros Hn64 Ht.
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bpres & BM). assert (HSC : MS_SCR = 2200) by reflexivity.
unfold cfg_at. change (w64 MS_ENTRY) with (Z_to_bv 64 MS_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 MS_ENTRY) mem (seg_rom tfibsegs)) z = mem z) by (intros; reflexivity).
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= d < 8 * g0 + 8) by (subst g0; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1 <= d + n - 1 < 8 * g1 + 8) by (subst g1; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1 < 2 ^ 44) by lia.
destruct (ra_last (aview tfibsegs H mem) d n HRA ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
pose proof (HHULL ltac:(lia)) as HH.
set (h1 := (g0 + 2147450880) / 8 * 8). set (h2 := (g1 + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0 + 2147450880 < h1 + 8) by (subst h1; pose proof (Z.div_mod (g0 + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g0 + 2147450880) 8 ltac:(lia)); lia).
assert (Hh2 : h2 <= g1 + 2147450880 < h2 + 8) by (subst h2; pose proof (Z.div_mod (g1 + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g1 + 2147450880) 8 ltac:(lia)); lia).
assert (Hh12 : h1 <= h2) by (subst h1 h2; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
assert (Hsh1 : shadow_addr d / 8 * 8 = h1) by (subst h1; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g0; f_equal; f_equal; lia).
assert (Hsh2 : shadow_addr (d + n - 1) / 8 * 8 = h2) by (subst h2; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g1; f_equal; f_equal; lia).
destruct (hull_rdword H mem d n h1 HH ltac:(lia) ltac:(lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem d n h2 HH ltac:(lia) ltac:(lia)) as (q2 & Hq2 & Rq2).
set (EE := Env [g0; g1; b1; q1; q2]). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply Env_reg; assumption).
pose proof (Env2 [g0; g1; b1; q1; q2]) as EE2. pose proof (Env10 [g0; g1; b1; q1; q2]) as EE10. pose proof (Env12 [g0; g1; b1; q1; q2]) as EE12. fold EE in EE2, EE10, EE12.
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (apply (Env_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (Env_x _ 2); reflexivity).
assert (E35 : ew EE 35 = Z_to_bv 64 q1) by (apply (Env_x _ 3); reflexivity).
assert (E36 : ew EE 36 = Z_to_bv 64 q2) by (apply (Env_x _ 4); reflexivity).
pose proof (ent1_8 b1 q1 q2 Hn64 Ht Hb1 Hok) as HS0. fold EE in HS0.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS0 r_p1_8_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG p1_8_e0 13) (RG p1_8_e0 12) HS1 (br_ovf_false EE 10 12 d n EE10 EE12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_p1_8_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG p1_8_e1 14) (RG p1_8_e1 13) HS2 (br_cls_small EE n EE12 Hn64)) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_p1_8_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF3 HFr3.
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply MEQ3. rewrite unsigned_lit_small by lia. unfold MS_STK, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (p1_8_e2) ms3 _ 16%bv 16%bv 538627 h1 35 48 HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (U_hull_addr EE 32 g0 2147450880 E32 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4).
assert (MEQ4 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z) by (intros z Hz; rewrite HM4; apply MEQ3; exact Hz).
clear HM4 HW4 HS3.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450888) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0 2147450888 E32) by lia. f_equal. subst h2. replace (g0 + 2147450888) with (g1 + 2147450880) by lia. reflexivity. }
assert (HW5 : rdword (aview tfibsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply MEQ4. rewrite unsigned_lit_small by lia. unfold MS_STK, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (set_regs_pc p1_8_e2 [((16%bv : bv 5), SOff 35 0)] (ss_pc p1_8_e2 + 4)) ms4 _ 17%bv 17%bv 571523 h2 36 48 HS4 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (Hrs2) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW5)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HM5).
assert (MEQ5 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z) by (intros z Hz; rewrite HM5; apply MEQ4; exact Hz).
clear HM5 HW5 HS4.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS5 r_p1_8_3)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF6 HFr6.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_NE (RG p1_8_e3 16) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_p1_8z_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF7 HFr7.
apply (finish EE p1_8z_e0 ms7 mat7 HS7 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ7. unfold MS_SCR, MS_STK in *. lia.
- intros a Ha; unfold MS_SCR, MS_STK in *; apply (apresent_same H mem (ms_mem ms7) a); [apply MEQ7; rewrite unsigned_lit_small by lia; lia | apply Bpres; lia].
+
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_NE (RG p1_8_e3 16) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_p1_8n_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF7 HFr7.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG p1_8n_e0 13) (SLit 0) HS7 (qc_flag_zero EE 8%nat 10 12 34 d n b1 EE10 EE12 E34 Hd ltac:(lia) Hdn ltac:(lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS7' r_p1_8n_1)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF8 HFr8.
apply (finish EE p1_8n_e1 ms8 mat8 HS8 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ8. unfold MS_SCR, MS_STK in *. lia.
- intros a Ha; unfold MS_SCR, MS_STK in *; apply (apresent_same H mem (ms_mem ms8) a); [apply MEQ8; rewrite unsigned_lit_small by lia; lia | apply Bpres; lia].
Qed.
Lemma ent2L : forall b1, 64 < n -> d + n <= kLowMemEnd - 1 -> aview tfibsegs H mem (SB + g1) = Some b1 -> saddr_ok (d + n - 1) b1 ->
st_ok tfibsegs (Env [g0; g1; b1; 0; 0; du; de; gu; ge]) ss2L (restrict H (mkst regs (Z_to_bv 64 MS_ENTRY) mem (seg_rom tfibsegs))).
Proof.
intros b1 Hn64 Hrg Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bpres & BM). unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in Hrg.
set (EE := Env [g0; g1; b1; 0; 0; du; de; gu; ge]).
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (apply (Env_x _ 0); reflexivity).
assert (E33 : ew EE 33 = Z_to_bv 64 g1) by (apply (Env_x _ 1); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (Env_x _ 2); reflexivity).
assert (E37 : ew EE 37 = Z_to_bv 64 du) by (apply (Env_x _ 5); reflexivity).
assert (E38 : ew EE 38 = Z_to_bv 64 de) by (apply (Env_x _ 6); reflexivity).
assert (E39 : ew EE 39 = Z_to_bv 64 gu) by (apply (Env_x _ 7); reflexivity).
assert (E40 : ew EE 40 = Z_to_bv 64 ge) by (apply (Env_x _ 8); reflexivity).
pose proof (Env2 [g0; g1; b1; 0; 0; du; de; gu; ge]) as E2. pose proof (Env10 [g0; g1; b1; 0; 0; du; de; gu; ge]) as E10. pose proof (Env12 [g0; g1; b1; 0; 0; du; de; gu; ge]) as E12.
fold EE in E2, E10, E12.
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= d < 8 * g0 + 8) by (subst g0; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1 <= d + n - 1 < 8 * g1 + 8) by (subst g1; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hgu : 8 * gu <= d + 7 < 8 * gu + 8 /\ du = 8 * gu) by (subst gu du; pose proof (Z.div_mod (d + 7) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + 7) 8 ltac:(lia)); lia).
assert (Hge : 8 * ge <= d + n < 8 * ge + 8 /\ de = 8 * ge) by (subst ge de; pose proof (Z.div_mod (d + n) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n) 8 ltac:(lia)); lia).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
rewrite restrict_mkst_fx. unfold ss2L. unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [g0; g1; b1; 0; 0; du; de; gu; ge])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply ent_stk | apply Forall_cons; [| apply Forall_cons; [| apply ent_ro]]].
+ unfold region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
apply Forall_cons; [|apply Forall_nil]. apply chunk_ok_zero. intros i Hi. rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|].
rewrite <- (ra_granule_zero (aview tfibsegs H mem) d n g0 HRA ltac:(lia) Hd). unfold SB. f_equal. lia.
+ unfold region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
change (base_val EE (Some 33%nat)) with (bv_unsigned (ew EE 33)). rewrite E33, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val tfibsegs EE _ g1 _ 1 (SOff 34 0) b1); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
apply val_mem1_of_aview. rewrite <- Hb1. unfold SB. f_equal. lia.
- apply pairwise_disjoint_of_extents. unfold stk, shregs2, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2, E32, E33, !unsigned_lit_small by lia. unfold MS_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok facts2L]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E12, E32, E33, E34, E37, E38, E39, E40, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. change (2 ^ 3) with 8. repeat split; try lia; try apply Z.mod_1_r.
all: first [rewrite (proj2 Hgu) | rewrite (proj2 Hge)]; rewrite Z.mul_comm; apply Z_mod_mult.
+ cbn [f_alias aliases2 alias_ok]. split; [|split; [|split; [|split; [|split; [|split; [|exact I]]]]]].
* apply U_inj. rewrite U_srl3, (U_atom EE 10 d E10), (U_atom EE 32 g0 E32) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 10 12 d n E10 E12), (U_atom EE 33 g1 E33) by lia. reflexivity.
* apply U_inj. rewrite U_and_m8, (U_atom_off EE 10 d 7 E10), (U_atom EE 37 du E37) by lia. pose proof (Z.div_mod (d + 7) 8 ltac:(lia)). lia.
* apply U_inj. rewrite U_and_m8, (U_add2 EE 10 12 d n E10 E12), (U_atom EE 38 de E38) by lia. pose proof (Z.div_mod (d + n) 8 ltac:(lia)). lia.
* apply U_inj. rewrite U_srl3, (U_atom EE 37 du E37), (U_atom EE 39 gu E39) by lia. rewrite (proj2 Hgu), Z.mul_comm, Z.div_mul by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_atom EE 38 de E38), (U_atom EE 40 ge E40) by lia. rewrite (proj2 Hge), Z.mul_comm, Z.div_mul by lia. reflexivity.
Qed.
Lemma ent2H : forall b1, 64 < n -> kHighMemBeg <= d /\ d + n <= kHighMemEnd - 1 -> aview tfibsegs H mem (SB + g1) = Some b1 -> saddr_ok (d + n - 1) b1 ->
st_ok tfibsegs (Env [g0; g1; b1; 0; 0; du; de; gu; ge]) ss2H (restrict H (mkst regs (Z_to_bv 64 MS_ENTRY) mem (seg_rom tfibsegs))).
Proof.
intros b1 Hn64 Hrg Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bpres & BM). unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in Hrg.
set (EE := Env [g0; g1; b1; 0; 0; du; de; gu; ge]).
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (apply (Env_x _ 0); reflexivity).
assert (E33 : ew EE 33 = Z_to_bv 64 g1) by (apply (Env_x _ 1); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (Env_x _ 2); reflexivity).
assert (E37 : ew EE 37 = Z_to_bv 64 du) by (apply (Env_x _ 5); reflexivity).
assert (E38 : ew EE 38 = Z_to_bv 64 de) by (apply (Env_x _ 6); reflexivity).
assert (E39 : ew EE 39 = Z_to_bv 64 gu) by (apply (Env_x _ 7); reflexivity).
assert (E40 : ew EE 40 = Z_to_bv 64 ge) by (apply (Env_x _ 8); reflexivity).
pose proof (Env2 [g0; g1; b1; 0; 0; du; de; gu; ge]) as E2. pose proof (Env10 [g0; g1; b1; 0; 0; du; de; gu; ge]) as E10. pose proof (Env12 [g0; g1; b1; 0; 0; du; de; gu; ge]) as E12.
fold EE in E2, E10, E12.
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= d < 8 * g0 + 8) by (subst g0; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1 <= d + n - 1 < 8 * g1 + 8) by (subst g1; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hgu : 8 * gu <= d + 7 < 8 * gu + 8 /\ du = 8 * gu) by (subst gu du; pose proof (Z.div_mod (d + 7) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + 7) 8 ltac:(lia)); lia).
assert (Hge : 8 * ge <= d + n < 8 * ge + 8 /\ de = 8 * ge) by (subst ge de; pose proof (Z.div_mod (d + n) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n) 8 ltac:(lia)); lia).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
rewrite restrict_mkst_fx. unfold ss2H. unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [g0; g1; b1; 0; 0; du; de; gu; ge])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply ent_stk | apply Forall_cons; [| apply Forall_cons; [| apply ent_ro]]].
+ unfold region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
apply Forall_cons; [|apply Forall_nil]. apply chunk_ok_zero. intros i Hi. rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|].
rewrite <- (ra_granule_zero (aview tfibsegs H mem) d n g0 HRA ltac:(lia) Hd). unfold SB. f_equal. lia.
+ unfold region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
change (base_val EE (Some 33%nat)) with (bv_unsigned (ew EE 33)). rewrite E33, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val tfibsegs EE _ g1 _ 1 (SOff 34 0) b1); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
apply val_mem1_of_aview. rewrite <- Hb1. unfold SB. f_equal. lia.
- apply pairwise_disjoint_of_extents. unfold stk, shregs2, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2, E32, E33, !unsigned_lit_small by lia. unfold MS_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok facts2H]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E12, E32, E33, E34, E37, E38, E39, E40, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. change (2 ^ 3) with 8. repeat split; try lia; try apply Z.mod_1_r.
all: first [rewrite (proj2 Hgu) | rewrite (proj2 Hge)]; rewrite Z.mul_comm; apply Z_mod_mult.
+ cbn [f_alias aliases2 alias_ok]. split; [|split; [|split; [|split; [|split; [|split; [|exact I]]]]]].
* apply U_inj. rewrite U_srl3, (U_atom EE 10 d E10), (U_atom EE 32 g0 E32) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 10 12 d n E10 E12), (U_atom EE 33 g1 E33) by lia. reflexivity.
* apply U_inj. rewrite U_and_m8, (U_atom_off EE 10 d 7 E10), (U_atom EE 37 du E37) by lia. pose proof (Z.div_mod (d + 7) 8 ltac:(lia)). lia.
* apply U_inj. rewrite U_and_m8, (U_add2 EE 10 12 d n E10 E12), (U_atom EE 38 de E38) by lia. pose proof (Z.div_mod (d + n) 8 ltac:(lia)). lia.
* apply U_inj. rewrite U_srl3, (U_atom EE 37 du E37), (U_atom EE 39 gu E39) by lia. rewrite (proj2 Hgu), Z.mul_comm, Z.div_mul by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_atom EE 38 de E38), (U_atom EE 40 ge E40) by lia. rewrite (proj2 Hge), Z.mul_comm, Z.div_mul by lia. reflexivity.
Qed.
Lemma path2L : 64 < n -> d + n <= kLowMemEnd - 1 -> SRr tfibsegs W (cfg_at tfibsegs MS_ENTRY regs mem md) POSTm.
Proof.
intros Hn64 Hrg.
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bpres & BM). assert (HSC : MS_SCR = 2200) by reflexivity.
unfold cfg_at. change (w64 MS_ENTRY) with (Z_to_bv 64 MS_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 MS_ENTRY) mem (seg_rom tfibsegs)) z = mem z) by (intros; reflexivity).
pose proof Hrg as Hrg'. unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in Hrg'.
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= d < 8 * g0 + 8) by (subst g0; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1 <= d + n - 1 < 8 * g1 + 8) by (subst g1; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hgu : 8 * gu <= d + 7 < 8 * gu + 8 /\ du = 8 * gu) by (subst gu du; pose proof (Z.div_mod (d + 7) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + 7) 8 ltac:(lia)); lia).
assert (Hge : 8 * ge <= d + n < 8 * ge + 8 /\ de = 8 * ge) by (subst ge de; pose proof (Z.div_mod (d + n) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n) 8 ltac:(lia)); lia).
destruct (ra_last (aview tfibsegs H mem) d n HRA ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
set (EE := Env [g0; g1; b1; 0; 0; du; de; gu; ge]). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply Env_reg; assumption).
pose proof (Env2 [g0; g1; b1; 0; 0; du; de; gu; ge]) as EE2. pose proof (Env10 [g0; g1; b1; 0; 0; du; de; gu; ge]) as EE10. pose proof (Env12 [g0; g1; b1; 0; 0; du; de; gu; ge]) as EE12. fold EE in EE2, EE10, EE12.
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (apply (Env_x _ 0); reflexivity).
assert (E33 : ew EE 33 = Z_to_bv 64 g1) by (apply (Env_x _ 1); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (Env_x _ 2); reflexivity).
assert (E39 : ew EE 39 = Z_to_bv 64 gu) by (apply (Env_x _ 7); reflexivity).
assert (E40 : ew EE 40 = Z_to_bv 64 ge) by (apply (Env_x _ 8); reflexivity).
assert (E32u : bv_unsigned (ew EE 32) = g0) by (rewrite E32; apply unsigned_lit_small; lia).
assert (E33u : bv_unsigned (ew EE 33) = g1) by (rewrite E33; apply unsigned_lit_small; lia).
pose proof (ent2L b1 Hn64 Hrg Hb1 Hok) as HS0. fold EE in HS0.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS0 r_p2L_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG p2L_e0 13) (RG p2L_e0 12) HS1 (br_ovf_false EE 10 12 d n EE10 EE12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_p2L_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_GEU (SLit 2147450879) (RG p2L_e1 18) HS2 (br_end_low EE 10 12 d n EE10 EE12 Hd ltac:(lia) ltac:(unfold kLowMemEnd in *; lia))) as HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_p2L_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF3 HFr3.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG p2L_e2 8) (RG p2L_e2 18) HS3 (br_beg_lt_end EE 10 12 d n EE10 EE12 Hd ltac:(lia) ltac:(lia))) as HS3'.
change (neg_bc BC_GEU) with BC_LTU in HS3'. clear HS3.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS3' r_p2L_3)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HF4 & HFr4). rewrite ?wvb_wvb in *.
assert (MEQ4 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z).
{ intros z Hz. rewrite (HF4 z); [apply MEQ3; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF4 HFr4.
destruct (Z.eq_dec b1 0) as [Hbz|Hbz].
+
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG p2L_e3 11) (SLit 0) HS4 (rp_b1_zero EE 34 ltac:(rewrite E34, Hbz; reflexivity))) as HS4'. clear HS4.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS4' r_p2Lz_0)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). rewrite ?wvb_wvb in *.
assert (MEQ5 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z).
{ intros z Hz. rewrite (HF5 z); [apply MEQ4; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF5 HFr5.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG p2Lz_e0 19) (RG p2Lz_e0 10) HS5 (br_sbeg_lt_send EE 39 40 gu ge E39 E40 ltac:(lia) ltac:(unfold SB; lia))) as HS5'.
change (neg_bc BC_GEU) with BC_LTU in HS5'. clear HS5.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS5' r_p2Lz_1)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF6 HFr6.
assert (SLW : forall z, sp0 - 2192 - 8 <= z < sp0 - 2192 -> writable_at tfibsegs (mrestrict H (ms_mem ms6)) z).
{ intros z Hz. apply AF0x.apresent_writable; [unfold AF0x.TFIB_IMG_END, kHighMemBeg in *; lia|]. apply (apresent_same H mem (ms_mem ms6) z); [apply MEQ6; rewrite unsigned_lit_small by lia; unfold MS_STK; lia | apply Bpres; lia]. }
assert (SZERO : forall a, gu + SB <= a < gu + SB + (ge - gu) -> aview tfibsegs H (ms_mem ms6) a = Some 0).
{ intros a Ha. unfold SB in Ha. rewrite (aview_same H mem (ms_mem ms6) a) by (apply MEQ6; rewrite unsigned_lit_small by lia; unfold MS_STK, kHighMemBeg in *; lia).
replace a with (SB + (a - SB)) by lia. apply (ra_granule_zero (aview tfibsegs H mem) d n (a - SB) HRA); [unfold SB in *; lia | exact Hd]. }
assert (R10 : sv_denot EE (RG p2Lz_e1 10) = Z_to_bv 64 (gu + SB)).
{ change (sv_denot EE (RG p2Lz_e1 10)) with (sv_denot EE (SOff 39 SB)). cbn [sv_denot]. rewrite E39, unsigned_lit_small by lia. reflexivity. }
assert (R11 : sv_denot EE (RG p2Lz_e1 11) = Z_to_bv 64 (ge - gu)).
{ change (sv_denot EE (RG p2Lz_e1 11)) with (sv_denot EE (SAlu ALU_ADD (SMd M_MUL (SOff 39 0) (SLit (-1))) (SOff 40 0))). exact (U_mz_len EE 39 40 gu ge E39 E40 ltac:(lia) ltac:(lia)). }
assert (R2 : sv_denot EE (RG p2Lz_e1 2) = Z_to_bv 64 (sp0 - 2192)).
{ change (sv_denot EE (RG p2Lz_e1 2)) with (sv_denot EE (SOff 2 (-2192))). cbn [sv_denot]. rewrite EE2. f_equal; lia. }
assert (R1 : sv_denot EE (RG p2Lz_e1 1) = Z_to_bv 64 347480).
{ change (sv_denot EE (RG p2Lz_e1 1)) with (sv_denot EE (SLit 347480)). apply bv_eq. vm_compute. reflexivity. }
assert (HOFF : Forall (fun r => 0 <= base_val EE (YP09.r_base r) + YP09.r_lo r /\ base_val EE (YP09.r_base r) + YP09.r_hi r <= 2 ^ 64 /\
(base_val EE (YP09.r_base r) + YP09.r_hi r <= sp0 - 2192 - 8 \/ sp0 - 2192 <= base_val EE (YP09.r_base r) + YP09.r_lo r) /\
YP09.r_lo r <= YP09.r_wlo r /\ YP09.r_whi r <= YP09.r_hi r) (ss_mem p2Lz_e1)).
{ cbn [ss_mem p2Lz_e1]. repeat (apply Forall_cons); try apply Forall_nil.
all: cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?EE2, ?E32u, ?E33u; unfold MS_STK, SB, kHighMemBeg in *; repeat split; lia. }
eapply SRr_bind; [exact (icpt_memisz W EE p2Lz_e1 ms6 _ 48 (ss_mem p2Lz_e1) (gu + SB) (ge - gu) (sp0 - 2192) 347480 HS6 eq_refl eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (submem_refl _)
R10 R11 R2 R1 ltac:(lia) ltac:(unfold SB; lia) ltac:(unfold SB, kHighMemBeg in *; lia) ltac:(unfold TFIB_IMG_END, kHighMemBeg in *; lia) ltac:(lia)
(ret_ok_lit 347480 ltac:(lia) eq_refl) ltac:(left; unfold SB, kHighMemBeg in *; lia) SLW SZERO HOFF)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HM7 & HP7). rewrite ?wvb_wvb in *.
set (EE' := havoc EE 48 (map (getr (ms_regs ms7)) MZ_CLOB)) in HS7.
assert (EE'reg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE' i = getr regs r).
{ intros i r Hi. subst EE'. rewrite ew_havoc_old by (pose proof (u5_range r); lia). apply EEreg. exact Hi. }
assert (EE'2 : bv_unsigned (ew EE' 2) = sp0) by (rewrite (EE'reg 2%nat 2%bv eq_refl); reflexivity).
assert (MEQ7 : forall z : word, ~ (sp0 - MS_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HM7 z) by (unfold MS_SCR in *; lia). apply MEQ6. unfold MS_SCR, MS_STK in *. lia. }
assert (PSL7 : forall z : word, sp0 - MS_SCR <= bv_unsigned z < sp0 - MS_STK -> ms_mem ms7 z <> None).
{ intros z Hz. apply HP7. unfold MS_SCR, MS_STK in *. lia. }
clear HM7 HP7 SLW SZERO R10 R11 R2 R1 HOFF HS6.
eapply SRr_bind; [apply (icpt_phase W EE' _ _ _ _ _ HS7 r_p2Lz_2)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MS_SCR <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE' _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE'2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
assert (PSL8 : forall z : word, sp0 - MS_SCR <= bv_unsigned z < sp0 - MS_STK -> ms_mem ms8 z <> None).
{ intros z Hz. rewrite (HF8 z); [apply PSL7; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE' _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE'2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF8 HFr8.
apply (finish EE' p2Lz_e2 ms8 mat8 HS8 eq_refl ltac:(vm_compute; reflexivity) EE'reg).
- intros z Hz. apply MEQ8. unfold MS_SCR, MS_STK in *. lia.
- intros a Ha; split; [exact (proj1 (Bpres a ltac:(unfold MS_SCR, MS_STK in *; lia))) |];
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by (unfold MS_SCR, MS_STK in *; lia); exact Ha) Eb)].
+
assert (Hlt : (d + n - 1) mod 8 < b1 < 8) by (destruct Hok as [Hz0 | [Hlt Hb]]; [exfalso; exact (Hbz Hz0) | lia]).
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_EQ (RG p2L_e3 11) (SLit 0) HS4 (rp_b1_nonzero EE 34 b1 E34 ltac:(lia))) as HS4'.
change (neg_bc BC_EQ) with BC_NE in HS4'. clear HS4.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS4' r_p2Ln_0)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). rewrite ?wvb_wvb in *.
assert (MEQ5 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z).
{ intros z Hz. rewrite (HF5 z); [apply MEQ4; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF5 HFr5.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_LT (RG p2Ln_e0 12) (RG p2Ln_e0 11) HS5 (rp_blt_last EE 10 12 34 d n b1 EE10 EE12 E34 Hd ltac:(lia) Hdn Hlt)) as HS5'. clear HS5.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS5' r_p2Ln_1)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF6 HFr6.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG p2Ln_e1 19) (RG p2Ln_e1 10) HS6 (br_sbeg_lt_send EE 39 40 gu ge E39 E40 ltac:(lia) ltac:(unfold SB; lia))) as HS6'.
change (neg_bc BC_GEU) with BC_LTU in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_p2Ln_2)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF7 HFr7.
assert (SLW : forall z, sp0 - 2192 - 8 <= z < sp0 - 2192 -> writable_at tfibsegs (mrestrict H (ms_mem ms7)) z).
{ intros z Hz. apply AF0x.apresent_writable; [unfold AF0x.TFIB_IMG_END, kHighMemBeg in *; lia|]. apply (apresent_same H mem (ms_mem ms7) z); [apply MEQ7; rewrite unsigned_lit_small by lia; unfold MS_STK; lia | apply Bpres; lia]. }
assert (SZERO : forall a, gu + SB <= a < gu + SB + (ge - gu) -> aview tfibsegs H (ms_mem ms7) a = Some 0).
{ intros a Ha. unfold SB in Ha. rewrite (aview_same H mem (ms_mem ms7) a) by (apply MEQ7; rewrite unsigned_lit_small by lia; unfold MS_STK, kHighMemBeg in *; lia).
replace a with (SB + (a - SB)) by lia. apply (ra_granule_zero (aview tfibsegs H mem) d n (a - SB) HRA); [unfold SB in *; lia | exact Hd]. }
assert (R10 : sv_denot EE (RG p2Ln_e2 10) = Z_to_bv 64 (gu + SB)).
{ change (sv_denot EE (RG p2Ln_e2 10)) with (sv_denot EE (SOff 39 SB)). cbn [sv_denot]. rewrite E39, unsigned_lit_small by lia. reflexivity. }
assert (R11 : sv_denot EE (RG p2Ln_e2 11) = Z_to_bv 64 (ge - gu)).
{ change (sv_denot EE (RG p2Ln_e2 11)) with (sv_denot EE (SAlu ALU_ADD (SMd M_MUL (SOff 39 0) (SLit (-1))) (SOff 40 0))). exact (U_mz_len EE 39 40 gu ge E39 E40 ltac:(lia) ltac:(lia)). }
assert (R2 : sv_denot EE (RG p2Ln_e2 2) = Z_to_bv 64 (sp0 - 2192)).
{ change (sv_denot EE (RG p2Ln_e2 2)) with (sv_denot EE (SOff 2 (-2192))). cbn [sv_denot]. rewrite EE2. f_equal; lia. }
assert (R1 : sv_denot EE (RG p2Ln_e2 1) = Z_to_bv 64 347480).
{ change (sv_denot EE (RG p2Ln_e2 1)) with (sv_denot EE (SLit 347480)). apply bv_eq. vm_compute. reflexivity. }
assert (HOFF : Forall (fun r => 0 <= base_val EE (YP09.r_base r) + YP09.r_lo r /\ base_val EE (YP09.r_base r) + YP09.r_hi r <= 2 ^ 64 /\
(base_val EE (YP09.r_base r) + YP09.r_hi r <= sp0 - 2192 - 8 \/ sp0 - 2192 <= base_val EE (YP09.r_base r) + YP09.r_lo r) /\
YP09.r_lo r <= YP09.r_wlo r /\ YP09.r_whi r <= YP09.r_hi r) (ss_mem p2Ln_e2)).
{ cbn [ss_mem p2Ln_e2]. repeat (apply Forall_cons); try apply Forall_nil.
all: cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?EE2, ?E32u, ?E33u; unfold MS_STK, SB, kHighMemBeg in *; repeat split; lia. }
eapply SRr_bind; [exact (icpt_memisz W EE p2Ln_e2 ms7 _ 48 (ss_mem p2Ln_e2) (gu + SB) (ge - gu) (sp0 - 2192) 347480 HS7 eq_refl eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (submem_refl _)
R10 R11 R2 R1 ltac:(lia) ltac:(unfold SB; lia) ltac:(unfold SB, kHighMemBeg in *; lia) ltac:(unfold TFIB_IMG_END, kHighMemBeg in *; lia) ltac:(lia)
(ret_ok_lit 347480 ltac:(lia) eq_refl) ltac:(left; unfold SB, kHighMemBeg in *; lia) SLW SZERO HOFF)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HM8 & HP8). rewrite ?wvb_wvb in *.
set (EE' := havoc EE 48 (map (getr (ms_regs ms8)) MZ_CLOB)) in HS8.
assert (EE'reg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE' i = getr regs r).
{ intros i r Hi. subst EE'. rewrite ew_havoc_old by (pose proof (u5_range r); lia). apply EEreg. exact Hi. }
assert (EE'2 : bv_unsigned (ew EE' 2) = sp0) by (rewrite (EE'reg 2%nat 2%bv eq_refl); reflexivity).
assert (MEQ8 : forall z : word, ~ (sp0 - MS_SCR <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HM8 z) by (unfold MS_SCR in *; lia). apply MEQ7. unfold MS_SCR, MS_STK in *. lia. }
assert (PSL8 : forall z : word, sp0 - MS_SCR <= bv_unsigned z < sp0 - MS_STK -> ms_mem ms8 z <> None).
{ intros z Hz. apply HP8. unfold MS_SCR, MS_STK in *. lia. }
clear HM8 HP8 SLW SZERO R10 R11 R2 R1 HOFF HS7.
eapply SRr_bind; [apply (icpt_phase W EE' _ _ _ _ _ HS8 r_p2Ln_3)|].
cbv beta. intros W9 c9 _ (-> & ms9 & mat9 & -> & HS9 & HF9 & HFr9). rewrite ?wvb_wvb in *.
assert (MEQ9 : forall z : word, ~ (sp0 - MS_SCR <= bv_unsigned z < sp0) -> ms_mem ms9 z = mem z).
{ intros z Hz. rewrite (HF9 z); [apply MEQ8; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE' _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE'2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
assert (PSL9 : forall z : word, sp0 - MS_SCR <= bv_unsigned z < sp0 - MS_STK -> ms_mem ms9 z <> None).
{ intros z Hz. rewrite (HF9 z); [apply PSL8; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE' _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE'2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF9 HFr9.
apply (finish EE' p2Ln_e3 ms9 mat9 HS9 eq_refl ltac:(vm_compute; reflexivity) EE'reg).
- intros z Hz. apply MEQ9. unfold MS_SCR, MS_STK in *. lia.
- intros a Ha; split; [exact (proj1 (Bpres a ltac:(unfold MS_SCR, MS_STK in *; lia))) |];
destruct (ms_mem ms9 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL9 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by (unfold MS_SCR, MS_STK in *; lia); exact Ha) Eb)].
Qed.
Lemma path2H : 64 < n -> kHighMemBeg <= d /\ d + n <= kHighMemEnd - 1 -> SRr tfibsegs W (cfg_at tfibsegs MS_ENTRY regs mem md) POSTm.
Proof.
intros Hn64 Hrg.
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bpres & BM). assert (HSC : MS_SCR = 2200) by reflexivity.
unfold cfg_at. change (w64 MS_ENTRY) with (Z_to_bv 64 MS_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 MS_ENTRY) mem (seg_rom tfibsegs)) z = mem z) by (intros; reflexivity).
pose proof Hrg as Hrg'. unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in Hrg'.
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= d < 8 * g0 + 8) by (subst g0; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1 <= d + n - 1 < 8 * g1 + 8) by (subst g1; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hgu : 8 * gu <= d + 7 < 8 * gu + 8 /\ du = 8 * gu) by (subst gu du; pose proof (Z.div_mod (d + 7) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + 7) 8 ltac:(lia)); lia).
assert (Hge : 8 * ge <= d + n < 8 * ge + 8 /\ de = 8 * ge) by (subst ge de; pose proof (Z.div_mod (d + n) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n) 8 ltac:(lia)); lia).
destruct (ra_last (aview tfibsegs H mem) d n HRA ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
set (EE := Env [g0; g1; b1; 0; 0; du; de; gu; ge]). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply Env_reg; assumption).
pose proof (Env2 [g0; g1; b1; 0; 0; du; de; gu; ge]) as EE2. pose proof (Env10 [g0; g1; b1; 0; 0; du; de; gu; ge]) as EE10. pose proof (Env12 [g0; g1; b1; 0; 0; du; de; gu; ge]) as EE12. fold EE in EE2, EE10, EE12.
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (apply (Env_x _ 0); reflexivity).
assert (E33 : ew EE 33 = Z_to_bv 64 g1) by (apply (Env_x _ 1); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (Env_x _ 2); reflexivity).
assert (E39 : ew EE 39 = Z_to_bv 64 gu) by (apply (Env_x _ 7); reflexivity).
assert (E40 : ew EE 40 = Z_to_bv 64 ge) by (apply (Env_x _ 8); reflexivity).
assert (E32u : bv_unsigned (ew EE 32) = g0) by (rewrite E32; apply unsigned_lit_small; lia).
assert (E33u : bv_unsigned (ew EE 33) = g1) by (rewrite E33; apply unsigned_lit_small; lia).
pose proof (ent2H b1 Hn64 Hrg Hb1 Hok) as HS0. fold EE in HS0.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS0 r_p2H_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG p2H_e0 13) (RG p2H_e0 12) HS1 (br_ovf_false EE 10 12 d n EE10 EE12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_p2H_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (SLit 140737488355327) (RG p2H_e1 18) HS2 (br_end_high EE 10 12 d n EE10 EE12 Hd ltac:(lia) ltac:(unfold kHighMemEnd in *; lia))) as HS2'.
change (neg_bc BC_LTU) with BC_GEU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_p2H_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF3 HFr3.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG p2H_e2 8) (RG p2H_e2 18) HS3 (br_beg_lt_end EE 10 12 d n EE10 EE12 Hd ltac:(lia) ltac:(lia))) as HS3'.
change (neg_bc BC_GEU) with BC_LTU in HS3'. clear HS3.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS3' r_p2H_3)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HF4 & HFr4). rewrite ?wvb_wvb in *.
assert (MEQ4 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z).
{ intros z Hz. rewrite (HF4 z); [apply MEQ3; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF4 HFr4.
destruct (Z.eq_dec b1 0) as [Hbz|Hbz].
+
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG p2H_e3 11) (SLit 0) HS4 (rp_b1_zero EE 34 ltac:(rewrite E34, Hbz; reflexivity))) as HS4'. clear HS4.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS4' r_p2Hz_0)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). rewrite ?wvb_wvb in *.
assert (MEQ5 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z).
{ intros z Hz. rewrite (HF5 z); [apply MEQ4; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF5 HFr5.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG p2Hz_e0 19) (RG p2Hz_e0 10) HS5 (br_sbeg_lt_send EE 39 40 gu ge E39 E40 ltac:(lia) ltac:(unfold SB; lia))) as HS5'.
change (neg_bc BC_GEU) with BC_LTU in HS5'. clear HS5.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS5' r_p2Hz_1)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF6 HFr6.
assert (SLW : forall z, sp0 - 2192 - 8 <= z < sp0 - 2192 -> writable_at tfibsegs (mrestrict H (ms_mem ms6)) z).
{ intros z Hz. apply AF0x.apresent_writable; [unfold AF0x.TFIB_IMG_END, kHighMemBeg in *; lia|]. apply (apresent_same H mem (ms_mem ms6) z); [apply MEQ6; rewrite unsigned_lit_small by lia; unfold MS_STK; lia | apply Bpres; lia]. }
assert (SZERO : forall a, gu + SB <= a < gu + SB + (ge - gu) -> aview tfibsegs H (ms_mem ms6) a = Some 0).
{ intros a Ha. unfold SB in Ha. rewrite (aview_same H mem (ms_mem ms6) a) by (apply MEQ6; rewrite unsigned_lit_small by lia; unfold MS_STK, kHighMemBeg in *; lia).
replace a with (SB + (a - SB)) by lia. apply (ra_granule_zero (aview tfibsegs H mem) d n (a - SB) HRA); [unfold SB in *; lia | exact Hd]. }
assert (R10 : sv_denot EE (RG p2Hz_e1 10) = Z_to_bv 64 (gu + SB)).
{ change (sv_denot EE (RG p2Hz_e1 10)) with (sv_denot EE (SOff 39 SB)). cbn [sv_denot]. rewrite E39, unsigned_lit_small by lia. reflexivity. }
assert (R11 : sv_denot EE (RG p2Hz_e1 11) = Z_to_bv 64 (ge - gu)).
{ change (sv_denot EE (RG p2Hz_e1 11)) with (sv_denot EE (SAlu ALU_ADD (SMd M_MUL (SOff 39 0) (SLit (-1))) (SOff 40 0))). exact (U_mz_len EE 39 40 gu ge E39 E40 ltac:(lia) ltac:(lia)). }
assert (R2 : sv_denot EE (RG p2Hz_e1 2) = Z_to_bv 64 (sp0 - 2192)).
{ change (sv_denot EE (RG p2Hz_e1 2)) with (sv_denot EE (SOff 2 (-2192))). cbn [sv_denot]. rewrite EE2. f_equal; lia. }
assert (R1 : sv_denot EE (RG p2Hz_e1 1) = Z_to_bv 64 347480).
{ change (sv_denot EE (RG p2Hz_e1 1)) with (sv_denot EE (SLit 347480)). apply bv_eq. vm_compute. reflexivity. }
assert (HOFF : Forall (fun r => 0 <= base_val EE (YP09.r_base r) + YP09.r_lo r /\ base_val EE (YP09.r_base r) + YP09.r_hi r <= 2 ^ 64 /\
(base_val EE (YP09.r_base r) + YP09.r_hi r <= sp0 - 2192 - 8 \/ sp0 - 2192 <= base_val EE (YP09.r_base r) + YP09.r_lo r) /\
YP09.r_lo r <= YP09.r_wlo r /\ YP09.r_whi r <= YP09.r_hi r) (ss_mem p2Hz_e1)).
{ cbn [ss_mem p2Hz_e1]. repeat (apply Forall_cons); try apply Forall_nil.
all: cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?EE2, ?E32u, ?E33u; unfold MS_STK, SB, kHighMemBeg in *; repeat split; lia. }
eapply SRr_bind; [exact (icpt_memisz W EE p2Hz_e1 ms6 _ 48 (ss_mem p2Hz_e1) (gu + SB) (ge - gu) (sp0 - 2192) 347480 HS6 eq_refl eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (submem_refl _)
R10 R11 R2 R1 ltac:(lia) ltac:(unfold SB; lia) ltac:(unfold SB, kHighMemBeg in *; lia) ltac:(unfold TFIB_IMG_END, kHighMemBeg in *; lia) ltac:(lia)
(ret_ok_lit 347480 ltac:(lia) eq_refl) ltac:(left; unfold SB, kHighMemBeg in *; lia) SLW SZERO HOFF)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HM7 & HP7). rewrite ?wvb_wvb in *.
set (EE' := havoc EE 48 (map (getr (ms_regs ms7)) MZ_CLOB)) in HS7.
assert (EE'reg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE' i = getr regs r).
{ intros i r Hi. subst EE'. rewrite ew_havoc_old by (pose proof (u5_range r); lia). apply EEreg. exact Hi. }
assert (EE'2 : bv_unsigned (ew EE' 2) = sp0) by (rewrite (EE'reg 2%nat 2%bv eq_refl); reflexivity).
assert (MEQ7 : forall z : word, ~ (sp0 - MS_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HM7 z) by (unfold MS_SCR in *; lia). apply MEQ6. unfold MS_SCR, MS_STK in *. lia. }
assert (PSL7 : forall z : word, sp0 - MS_SCR <= bv_unsigned z < sp0 - MS_STK -> ms_mem ms7 z <> None).
{ intros z Hz. apply HP7. unfold MS_SCR, MS_STK in *. lia. }
clear HM7 HP7 SLW SZERO R10 R11 R2 R1 HOFF HS6.
eapply SRr_bind; [apply (icpt_phase W EE' _ _ _ _ _ HS7 r_p2Hz_2)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MS_SCR <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE' _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE'2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
assert (PSL8 : forall z : word, sp0 - MS_SCR <= bv_unsigned z < sp0 - MS_STK -> ms_mem ms8 z <> None).
{ intros z Hz. rewrite (HF8 z); [apply PSL7; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE' _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE'2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF8 HFr8.
apply (finish EE' p2Hz_e2 ms8 mat8 HS8 eq_refl ltac:(vm_compute; reflexivity) EE'reg).
- intros z Hz. apply MEQ8. unfold MS_SCR, MS_STK in *. lia.
- intros a Ha; split; [exact (proj1 (Bpres a ltac:(unfold MS_SCR, MS_STK in *; lia))) |];
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by (unfold MS_SCR, MS_STK in *; lia); exact Ha) Eb)].
+
assert (Hlt : (d + n - 1) mod 8 < b1 < 8) by (destruct Hok as [Hz0 | [Hlt Hb]]; [exfalso; exact (Hbz Hz0) | lia]).
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_EQ (RG p2H_e3 11) (SLit 0) HS4 (rp_b1_nonzero EE 34 b1 E34 ltac:(lia))) as HS4'.
change (neg_bc BC_EQ) with BC_NE in HS4'. clear HS4.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS4' r_p2Hn_0)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). rewrite ?wvb_wvb in *.
assert (MEQ5 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z).
{ intros z Hz. rewrite (HF5 z); [apply MEQ4; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF5 HFr5.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_LT (RG p2Hn_e0 12) (RG p2Hn_e0 11) HS5 (rp_blt_last EE 10 12 34 d n b1 EE10 EE12 E34 Hd ltac:(lia) Hdn Hlt)) as HS5'. clear HS5.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS5' r_p2Hn_1)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF6 HFr6.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG p2Hn_e1 19) (RG p2Hn_e1 10) HS6 (br_sbeg_lt_send EE 39 40 gu ge E39 E40 ltac:(lia) ltac:(unfold SB; lia))) as HS6'.
change (neg_bc BC_GEU) with BC_LTU in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_p2Hn_2)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF7 HFr7.
assert (SLW : forall z, sp0 - 2192 - 8 <= z < sp0 - 2192 -> writable_at tfibsegs (mrestrict H (ms_mem ms7)) z).
{ intros z Hz. apply AF0x.apresent_writable; [unfold AF0x.TFIB_IMG_END, kHighMemBeg in *; lia|]. apply (apresent_same H mem (ms_mem ms7) z); [apply MEQ7; rewrite unsigned_lit_small by lia; unfold MS_STK; lia | apply Bpres; lia]. }
assert (SZERO : forall a, gu + SB <= a < gu + SB + (ge - gu) -> aview tfibsegs H (ms_mem ms7) a = Some 0).
{ intros a Ha. unfold SB in Ha. rewrite (aview_same H mem (ms_mem ms7) a) by (apply MEQ7; rewrite unsigned_lit_small by lia; unfold MS_STK, kHighMemBeg in *; lia).
replace a with (SB + (a - SB)) by lia. apply (ra_granule_zero (aview tfibsegs H mem) d n (a - SB) HRA); [unfold SB in *; lia | exact Hd]. }
assert (R10 : sv_denot EE (RG p2Hn_e2 10) = Z_to_bv 64 (gu + SB)).
{ change (sv_denot EE (RG p2Hn_e2 10)) with (sv_denot EE (SOff 39 SB)). cbn [sv_denot]. rewrite E39, unsigned_lit_small by lia. reflexivity. }
assert (R11 : sv_denot EE (RG p2Hn_e2 11) = Z_to_bv 64 (ge - gu)).
{ change (sv_denot EE (RG p2Hn_e2 11)) with (sv_denot EE (SAlu ALU_ADD (SMd M_MUL (SOff 39 0) (SLit (-1))) (SOff 40 0))). exact (U_mz_len EE 39 40 gu ge E39 E40 ltac:(lia) ltac:(lia)). }
assert (R2 : sv_denot EE (RG p2Hn_e2 2) = Z_to_bv 64 (sp0 - 2192)).
{ change (sv_denot EE (RG p2Hn_e2 2)) with (sv_denot EE (SOff 2 (-2192))). cbn [sv_denot]. rewrite EE2. f_equal; lia. }
assert (R1 : sv_denot EE (RG p2Hn_e2 1) = Z_to_bv 64 347480).
{ change (sv_denot EE (RG p2Hn_e2 1)) with (sv_denot EE (SLit 347480)). apply bv_eq. vm_compute. reflexivity. }
assert (HOFF : Forall (fun r => 0 <= base_val EE (YP09.r_base r) + YP09.r_lo r /\ base_val EE (YP09.r_base r) + YP09.r_hi r <= 2 ^ 64 /\
(base_val EE (YP09.r_base r) + YP09.r_hi r <= sp0 - 2192 - 8 \/ sp0 - 2192 <= base_val EE (YP09.r_base r) + YP09.r_lo r) /\
YP09.r_lo r <= YP09.r_wlo r /\ YP09.r_whi r <= YP09.r_hi r) (ss_mem p2Hn_e2)).
{ cbn [ss_mem p2Hn_e2]. repeat (apply Forall_cons); try apply Forall_nil.
all: cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?EE2, ?E32u, ?E33u; unfold MS_STK, SB, kHighMemBeg in *; repeat split; lia. }
eapply SRr_bind; [exact (icpt_memisz W EE p2Hn_e2 ms7 _ 48 (ss_mem p2Hn_e2) (gu + SB) (ge - gu) (sp0 - 2192) 347480 HS7 eq_refl eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (submem_refl _)
R10 R11 R2 R1 ltac:(lia) ltac:(unfold SB; lia) ltac:(unfold SB, kHighMemBeg in *; lia) ltac:(unfold TFIB_IMG_END, kHighMemBeg in *; lia) ltac:(lia)
(ret_ok_lit 347480 ltac:(lia) eq_refl) ltac:(left; unfold SB, kHighMemBeg in *; lia) SLW SZERO HOFF)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HM8 & HP8). rewrite ?wvb_wvb in *.
set (EE' := havoc EE 48 (map (getr (ms_regs ms8)) MZ_CLOB)) in HS8.
assert (EE'reg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE' i = getr regs r).
{ intros i r Hi. subst EE'. rewrite ew_havoc_old by (pose proof (u5_range r); lia). apply EEreg. exact Hi. }
assert (EE'2 : bv_unsigned (ew EE' 2) = sp0) by (rewrite (EE'reg 2%nat 2%bv eq_refl); reflexivity).
assert (MEQ8 : forall z : word, ~ (sp0 - MS_SCR <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HM8 z) by (unfold MS_SCR in *; lia). apply MEQ7. unfold MS_SCR, MS_STK in *. lia. }
assert (PSL8 : forall z : word, sp0 - MS_SCR <= bv_unsigned z < sp0 - MS_STK -> ms_mem ms8 z <> None).
{ intros z Hz. apply HP8. unfold MS_SCR, MS_STK in *. lia. }
clear HM8 HP8 SLW SZERO R10 R11 R2 R1 HOFF HS7.
eapply SRr_bind; [apply (icpt_phase W EE' _ _ _ _ _ HS8 r_p2Hn_3)|].
cbv beta. intros W9 c9 _ (-> & ms9 & mat9 & -> & HS9 & HF9 & HFr9). rewrite ?wvb_wvb in *.
assert (MEQ9 : forall z : word, ~ (sp0 - MS_SCR <= bv_unsigned z < sp0) -> ms_mem ms9 z = mem z).
{ intros z Hz. rewrite (HF9 z); [apply MEQ8; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE' _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE'2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
assert (PSL9 : forall z : word, sp0 - MS_SCR <= bv_unsigned z < sp0 - MS_STK -> ms_mem ms9 z <> None).
{ intros z Hz. rewrite (HF9 z); [apply PSL8; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE' _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE'2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF9 HFr9.
apply (finish EE' p2Hn_e3 ms9 mat9 HS9 eq_refl ltac:(vm_compute; reflexivity) EE'reg).
- intros z Hz. apply MEQ9. unfold MS_SCR, MS_STK in *. lia.
- intros a Ha; split; [exact (proj1 (Bpres a ltac:(unfold MS_SCR, MS_STK in *; lia))) |];
destruct (ms_mem ms9 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL9 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by (unfold MS_SCR, MS_STK in *; lia); exact Ha) Eb)].
Qed.
Theorem asan_memset_srrU : SRr tfibsegs W (cfg_at tfibsegs MS_ENTRY regs mem md) POSTm.
Proof.
destruct (Z.eq_dec n 0) as [Hn0|Hn0]; [apply path0; exact Hn0|].
destruct (Z_le_gt_dec n 64) as [Hle|Hgt].
- assert (Hn64 : 1 <= n <= 64) by lia.
assert (Hg0 : 8 * g0 <= d < 8 * g0 + 8) by (subst g0; pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia).
assert (Hg1 : 8 * g1 <= d + n - 1 < 8 * g1 + 8) by (subst g1; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
destruct (AE2r.t_cases regs d n Hd (g1 - g0) ltac:(lia)) as [Ht|[Ht|[Ht|[Ht|[Ht|[Ht|[Ht|[Ht|Ht]]]]]]]];
[apply path1_0 | apply path1_1 | apply path1_2 | apply path1_3 | apply path1_4 | apply path1_5 | apply path1_6 | apply path1_7 | apply path1_8]; assumption.
- destruct HAM as [HL|HH]; [apply path2L; [lia | exact HL] | apply path2H; [lia | exact HH]].
Qed.
End h.
(* AE2r.v:567 asan_memset_realizes in ARU form: ecall_pre -> FSupoison.ecall_preU, AR -> FSupoison.ARU; every other
   conjunct verbatim. *)
Theorem asan_memset_realizesU : forall B, AR_laws tfibsegs B -> TfibSyms B ->
forall ly S UP (W : world tfibsegs) regs mem md d x n,
FSP.ecall_preU tfibsegs B ly S UP W regs mem md ->
getr regs 10 = w64 d -> getr regs 11 = w64 x -> getr regs 12 = w64 n -> 0 <= n < 2 ^ 32 -> 0 <= d -> d + n <= 2 ^ 63 ->
dest_ok tfibsegs B ly S W regs mem d n ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF d n -> (0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) mem) d n) ->
amem_range d n ->
SRr tfibsegs W (cfg_at tfibsegs 0x521bc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
FSP.ARU tfibsegs B ly S UP W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 d /\
(forall i, 0 <= i < n -> aview tfibsegs (w_H W) mem' (d + i) = Some (x mod 256)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (spZ regs - ESTACK <= a < spZ regs) -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Proof.
intros B LAWS TB ly S UP W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HRA HHULL HAM.
exact (asan_memset_srrU B LAWS TB ly S UP W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HRA HHULL HAM).
Qed.
(* The target: FSupoisonU.v:244 aintrin_realizesU OSet at __asan_memset (lib/A/FSH_Base.v:92 PC_memset = 0x521bc =
   AE6t.MS_ENTRY), the fr_memset / FSClose H_memset premise. Its premise order (dest_ok, amem_range, then the shadow
   facts) differs from AE2r's; its post is asan_memset_realizesU's (the match on OSet reduces to Some (x mod 256)). *)
Section t.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.
Theorem tfib_asan_memset_realizesU : FSupoisonU.aintrin_realizesU tfibsegs B OSet FSH_Base.PC_memset.
Proof.
intros ly S U W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HAM HRA HHULL _.
exact (asan_memset_realizesU B LAWS TB ly S U W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HRA HHULL HAM).
Qed.
End t.
End c.
