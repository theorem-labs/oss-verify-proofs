(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: new file for libreac/fuzz_scene. The __asan::MemToShadow copy that
   __asan_stack_malloc_8 (jal at 0x3f564) and __asan_stack_free_8 (jal at 0x3f5e0) call, at 0x3f604 in the
   image fuzz_scene.asan-ubsan (libreac/fuzz_scene), against the shared summary
   lib/Reusable/AsStackLeaf.v's mem_to_shadow_realizes. The file is the asan-ubsan copy of
   lib/A/RT_mem_to_shadow.v: the image values move and the asan-state modules are lib/AU
   YB1v YB1w YE34 YF0l YF0m YF0x YE2y YE3d in place of lib/A AB1v AB1w AE34 AF0l AF0m AF0x AE2y AE3d. *)

(*   MEASURED: the 28-instruction body 0x3f604-0x3f670 is masked-IDENTICAL to the asan copy at 0x3f5d8 and to
   the cgif_file donor range at 0x3cc00 (SHADOW.md:298, row 10: 28 instructions, raw diff 9, masked
   IDENTICAL), so the shape of the walk is the asan one with the asan-ubsan cells:
     shadow offset  GOT 0x9ba40 -> 0xa3af8 -> 0x7fff8000 = SHADOW_OFF
     kMidMemBeg     GOT 0x9ba48 -> 0xa47e8 -> 0
     kMidMemEnd     GOT 0x9ba50 -> 0xa47f0 -> 0
     kHighMemEnd    GOT 0x9ba58 -> 0xa47e0 -> 0x7fffffffffff
   and the return at 0x3f604 + 0x68 = 0x3f66c. No store, no sp operand and no call on either zone's path.

   The two zones are the two disjuncts of in_app (YG0f.v:277) for the fake stack, which AR's layout gives for
   ANY slot (F_app, YG0t.v:33), live or free: the statement asks for no (cid, pos) in frames S. Each zone is
   one symbolic run of the same table, with the entry's a0 bounded by one atom fact; every other constant the
   body reads is a start-up cell of YF0m's Tfib_const, delivered by YE2y's rodata_ok from YF0m.TfibSyms B and
   AR, so this file needs NO extra Section hypothesis for the cells.
   By section of the asan-ubsan image (a Theorem Labs lane's import check, 2026-10-29 03:10Z): the four GOT words above
   are FILE-BACKED (.got, the image's own bytes); the four cells they point to (0xa3af8, 0xa47e8, 0xa47f0,
   0xa47e0) are NOBITS (.bss) -- NOT file facts: their values are the START-UP STATE, measured by a Theorem Labs lane
   in all 50 of scene's hand-off states, and enter through the start-up certificate that supplies Tfib_const. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0s YG0t.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import YB1v YB1w YE34 YF0l YF0m YF0x YE2y YE3d.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YN32.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import AsStackLeaf.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Definition M2S_ENTRY : Z := 0x3f604.
Definition M2S_RET : Z := 0x3f66c.
Definition m2s_ranges : list (Z * nat) := [(M2S_ENTRY, 28%nat)].
Definition tbl_m2s : ctable := Eval vm_compute in build_ranges m2s_ranges TEmpty.
Lemma tbl_m2s_eq : tbl_m2s = build_ranges m2s_ranges TEmpty. Proof. vm_cast_no_check (eq_refl tbl_m2s). Qed.
Lemma tbl_m2s_ok : table_ok tfibsegs tbl_m2s.
Proof. rewrite tbl_m2s_eq. apply build_ranges_ok; [unfold m2s_ranges; repeat constructor; cbn; discriminate | exact (table_ok_empty tfibsegs)]. Qed.
Definition m2s_rodata : list (Z * Z * list (Z * BinNums.N * Z)) :=
[(0x9ba40, 32, [(0, 8%N, 0xa3af8); (8, 8%N, 0xa47e8); (16, 8%N, 0xa47f0); (24, 8%N, 0xa47e0)]);
(0xa3af8, 8, [(0, 8%N, 0x7fff8000)]);
(0xa47e0, 24, [(0, 8%N, 0x7fffffffffff); (8, 8%N, 0); (16, 8%N, 0)])].
Lemma m2s_rodata_chk : forall ly, rodata_chk ly m2s_rodata = true.
Proof. intros ly. vm_compute. reflexivity. Qed.
Definition not_ecall (st : run_status) : bool := match st with RS_ecall => false | _ => true end.
Definition keep_regs : list Z := [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Definition keep_shape (ss : sstate) : bool :=
forallb (fun r => sv_eqb (sr_get (ss_regs ss) (Z_to_bv 5 r)) (SOff (Z.to_nat r) 0)) keep_regs.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition RUN (s : sstate) := sym_runN tfibsegs tbl_m2s FUEL s.
Definition m2s_fact (hi : bool) : afact :=
if hi then mkAF kHighMemBeg 140737479966720 0 else mkAF 0 (kLowShadowBeg - 1) 0.
Lemma m2s_fact_al2 : forall hi, af_al2 (m2s_fact hi) = 0. Proof. intros [|]; reflexivity. Qed.
Definition ss_ent (hi : bool) : sstate :=
mkSS M2S_ENTRY sr_atoms (map ro_region m2s_rodata) None (mkFacts [(10%nat, m2s_fact hi)] [] []).
Definition e_lo : sstate := Eval vm_compute in fst (RUN (ss_ent false)).
Definition e_hi : sstate := Eval vm_compute in fst (RUN (ss_ent true)).
Definition st_lo : run_status := Eval vm_compute in snd (RUN (ss_ent false)).
Definition st_hi : run_status := Eval vm_compute in snd (RUN (ss_ent true)).
Lemma r_lo : RUN (ss_ent false) = (e_lo, st_lo). Proof. vm_compute. reflexivity. Qed.
Lemma r_hi : RUN (ss_ent true) = (e_hi, st_hi). Proof. vm_compute. reflexivity. Qed.
Lemma ne_lo : not_ecall st_lo = true. Proof. vm_compute. reflexivity. Qed.
Lemma ne_hi : not_ecall st_hi = true. Proof. vm_compute. reflexivity. Qed.
Definition a0_out : sv := Eval vm_compute in sr_get (ss_regs e_lo) 10%bv.
Definition m2s_shape (ss : sstate) : bool :=
(ss_pc ss =? M2S_RET) && (match ss_resv ss with None => true | _ => false end) &&
sv_eqb (sr_get (ss_regs ss) 10%bv) a0_out && keep_shape ss.
Lemma shape_lo : m2s_shape e_lo = true. Proof. vm_compute. reflexivity. Qed.
Lemma shape_hi : m2s_shape e_hi = true. Proof. vm_compute. reflexivity. Qed.
Lemma zsrl3 : forall q, 0 <= q < 2 ^ 64 -> zalu64 ALU_SRL q 3 = q / 8.
Proof.
intros q Hq. unfold zalu64. cbn [zalu_raw]. unfold zcanon, M64.
rewrite (Z.mod_small q) by lia.
replace (Z.land (3 mod 2 ^ 64) 63) with 3 by (vm_compute; reflexivity).
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
apply Z.mod_small. split; [apply Z.div_pos; lia|].
apply (Z.le_lt_trans _ q); [apply Z.div_le_upper_bound; lia | lia].
Qed.
Lemma zadd_small : forall x y, 0 <= x -> 0 <= y -> x + y < 2 ^ 64 -> zalu64 ALU_ADD x y = x + y.
Proof.
intros x y H1 H2 H3. unfold zalu64. cbn [zalu_raw]. unfold zcanon, M64.
rewrite (Z.mod_small x) by lia. rewrite (Z.mod_small y) by lia. apply Z.mod_small. lia.
Qed.
Lemma m2s_phase : forall (W : world tfibsegs) E ss ss' st ms md,
not_ecall st = true ->
st_ok tfibsegs E ss (restrict (w_H W) ms) -> sym_runN tfibsegs tbl_m2s FUEL ss = (ss', st) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
st_ok tfibsegs E ss' (restrict (w_H W) ms1) /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
intros W E ss ss' st ms md Hne HS Hrun.
eapply (SRr_run_gen tfibsegs tbl_m2s tbl_m2s_ok YF0x.Hwx_tfa W FUEL E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF HFr. apply SRr_ret. split; [reflexivity|]. exists ms1, mat1.
split; [reflexivity|]. split; [| split; [exact HF | exact HFr]].
destruct st; first [exact HS1 | discriminate Hne].
Qed.
Section d.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.
Section e.
Variables (hi : bool) (e1 : sstate) (st1 : run_status).
Hypothesis Hrun : RUN (ss_ent hi) = (e1, st1).
Hypothesis Hne : not_ecall st1 = true.
Hypothesis Hshape : m2s_shape e1 = true.
Lemma m2s_body : forall ly S W regs mem md p,
AR tfibsegs B ly S W mem md -> YK0s.ret_ok (getr regs 1) -> getr regs 10 = w64 p ->
af_lo (m2s_fact hi) <= p -> p <= af_hi (m2s_fact hi) -> 0 <= p < 2 ^ 47 ->
SRr tfibsegs W (cfg_at tfibsegs M2S_ENTRY regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
AR tfibsegs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 (shadow_addr p) /\
(forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Proof.
intros ly S W regs mem md p HAR Hra G10 Hlo Hhi Hp47.
pose proof YF0x.Hwx_tfa as Hwx.
set (H := w_H W) in *.
assert (HD8 : 0 <= p / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
set (EE := YE2y.Env regs ([] : list Z)).
assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r)
by (intros; apply YE2y.Env_reg; assumption).
assert (E10 : forall extra, bv_unsigned (ew (Ereg regs extra) 10%nat) = p).
{ intros extra. rewrite (ew_Ereg_nat regs extra 10%nat 10%bv eq_refl), G10. unfold w64.
rewrite unsigned_lit_small by lia. reflexivity. }
assert (E10E : bv_unsigned (ew EE 10%nat) = p).
{ rewrite (EEreg 10%nat 10%bv eq_refl), G10. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
assert (HS0 : st_ok tfibsegs EE (ss_ent hi) (restrict H (mkst regs (Z_to_bv 64 M2S_ENTRY) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_ent, EE, YE2y.Env. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- exact (rodata_ok B TB m2s_rodata ly S H mem _ (m2s_rodata_chk ly) (proj1 HAR)).
- apply pairwise_disjoint_of_extents. unfold m2s_rodata, ro_region, extent_of_region.
cbn [map fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val zpairwise_disjoint zall_disjoint].
unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. split; [|exact I].
unfold afact_ok. rewrite E10, (m2s_fact_al2 hi), Z.pow_0_r.
split; [split; [exact Hlo | exact Hhi]|]. split; [apply Z.mod_1_r | lia]. }
unfold cfg_at. change (w64 M2S_ENTRY) with (Z_to_bv 64 M2S_ENTRY).
eapply SRr_bind; [apply (m2s_phase W EE _ _ _ _ _ Hne HS0 Hrun)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1).
assert (MEQ1 : forall z, ms_mem ms1 z = mem z).
{ intros z. apply HF1. intros Hw. destruct (in_wrange_windows EE _ _ Hw) as (b & wlo & whi & Ht & Hb).
cbn in Ht.
repeat (destruct Ht as [Hq|Ht]; [injection Hq as <- <- <-; cbn [base_val] in Hb; lia|]). destruct Ht. }
assert (AV : forall a, aview tfibsegs H (ms_mem ms1) a = aview tfibsegs H mem a)
by (intros a; apply (YF0x.aview_same H mem (ms_mem ms1) a); apply MEQ1).
unfold m2s_shape in Hshape. apply andb_prop in Hshape as [Hshape KR].
apply andb_prop in Hshape as [Hshape S10]. apply andb_prop in Hshape as [Spc Srv].
apply Z.eqb_eq in Spc.
assert (Hrv : ss_resv e1 = None) by (destruct (ss_resv e1); [discriminate | reflexivity]).
apply sv_eqb_eq in S10. unfold keep_shape in KR. rewrite forallb_forall in KR.
assert (KEEP1 : forall r, In r keep_regs -> getr (ms_regs ms1) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hr. rewrite (st_ok_restrict_reg tfibsegs H EE e1 ms1 _ HS1).
specialize (KR r Hr). apply sv_eqb_eq in KR. rewrite KR.
cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. apply EEreg.
unfold keep_regs in Hr. cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [reflexivity|]). destruct Hr. }
assert (Q1 : getr (ms_regs ms1) 1 = getr regs 1)
by (exact (KEEP1 1 ltac:(unfold keep_regs; cbn [In]; tauto))).
assert (A10 : getr (ms_regs ms1) 10 = w64 (shadow_addr p)).
{ rewrite (st_ok_restrict_reg tfibsegs H EE e1 ms1 10%bv HS1), S10.
cbv [a0_out]. cbn [sv_denot]. rewrite !zalu64_sound. rewrite E10E. rewrite ?Z.add_0_r.
rewrite (zsrl3 p) by lia. rewrite zadd_small by lia.
unfold w64, shadow_addr, SHADOW_OFF. f_equal; lia. }
eapply (SRr_ret_at tfibsegs tbl_m2s tbl_m2s_ok Hwx W EE); [exact HS1 | exact Hrv | rewrite Spc; vm_compute; reflexivity |].
intros mat'. rewrite wvb_wvb.
replace (v_jalr (getr (ms_regs ms1) 1) 0) with (w64 (raZ regs))
by (rewrite Q1; unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; symmetry; exact Hra).
split; [reflexivity|]. exists (ms_regs ms1), (ms_mem ms1), (with_vm_backing (m_vm_lazy md) mat' md).
pose proof (same_but_materialized_frame md _ (with_vm_backing_same md mat')) as MF.
split; [reflexivity|].
split; [|split; [|split; [exact (with_vm_backing_same md mat') |split; [exact A10 | split; [|]]]]].
-
apply (al_frame _ _ LAWS ly S W mem md (ms_mem ms1) _ HAR).
+ intros a _ _. apply AV.
+ intros a Hv. rewrite AV. exact Hv.
+ apply MF. + apply MF. + apply MF.
+ intros a _ _. apply MEQ1.
-
intros r Hr. apply KEEP1. unfold acallee_saved in Hr. unfold keep_regs. cbn [In]. lia.
-
intros a _. apply AV.
-
intros a Ha. apply (YF0x.apresent_same H mem (ms_mem ms1) a (MEQ1 _) Ha).
Qed.
End e.
Theorem m2s_at : AsStackLeaf.mem_to_shadow_realizes tfibsegs B M2S_ENTRY.
Proof.
intros ly S W regs mem md cid pos p HAR Hra Hcid Hpos G10 Hp1 Hp2.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY.
destruct (F_app ly HLY) as (HF0 & HFZ & _).
pose proof (frame_off_bounds cid pos Hcid Hpos) as (FO1 & FO2 & _ & _ & _ & FO6).
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR.
change (2 ^ 20) with 1048576 in FO1, FO2, FO6.
unfold frame_addr in Hp1, Hp2.
assert (PL : ly_F ly <= p) by (unfold kFakeFramesOff in FO1; lia).
assert (PU : p < ly_F ly + kFakeStackSize) by lia.
destruct HFZ as [HZ | [HZ1 HZ2]].
-
apply (m2s_body false e_lo st_lo r_lo ne_lo shape_lo ly S W regs mem md p HAR Hra G10);
cbn [m2s_fact af_lo af_hi]; unfold kLowShadowBeg in *; change (2 ^ 47) with 140737488355328; lia.
-
apply (m2s_body true e_hi st_hi r_hi ne_hi shape_hi ly S W regs mem md p HAR Hra G10);
cbn [m2s_fact af_lo af_hi]; unfold kHighMemBeg in *; change (2 ^ 47) with 140737488355328; lia.
Qed.
End d.
Theorem scene_mem_to_shadow : forall (B : asyms),
AR_laws tfibsegs B -> YF0m.TfibSyms B -> AsStackLeaf.mem_to_shadow_realizes tfibsegs B M2S_ENTRY.
Proof. intros B LAWS TB. exact (m2s_at B LAWS TB). Qed.
End c.
