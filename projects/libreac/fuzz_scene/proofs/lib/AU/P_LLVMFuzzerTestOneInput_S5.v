(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment S5 of the ASan+UBSan walk of libreac/fuzz_scene's LLVMFuzzerTestOneInput. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00 YI16.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0s YG0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YO09 YE00.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import YE01 YCbp.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import PaRun PaShadow PaStep SceneSyms SceneList SceneAddr ScenePa SceneImg.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import PaJournal ScenePaLib SceneBase SceneRo SceneFrame YC1h YC85 YC1g YC4b YC45.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog Require Import SceneBlock SceneTM.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import SetShadowDef.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import P_LLVMFuzzerTestOneInput_ctx P_LLVMFuzzerTestOneInput_seg.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import J_StackSz J_StackSzPf U_NotTrap U_Word4.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import P_reac_ctrl_scene_build P_reac_ctrl_scene_set_mac.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require P_LLVMFuzzerTestOneInput.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YO0c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Notation scene_sink_head := P_LLVMFuzzerTestOneInput.scene_sink_head.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation SEGS := (@pa_segs _ scene_listing PI_scene).
#[local] Notation VAL := (@pa_val _ scene_listing PI_scene).
#[local] Notation SIGMA := (@pa_sigma _ scene_listing PI_scene).
#[local] Notation BASE := (@pa_val _ scene_listing PI_scene A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ scene_listing PI_scene).
#[local] Notation RHI := (@pa_relro_hi _ scene_listing PI_scene).
Section h.
Variable B : asyms.
Variables A_LLVMF RA_LLVMF EV_LIB LIVE_LIB LLVMF_STK A_EMPTY : Z.
Context {RO : ro_below_ofl (SK := scene_sink_head) SEGS RLO RHI}.
Hypothesis HEV : P_LLVMFuzzerTestOneInput.LLVMF_EV <= EV_LIB.
Hypothesis HLIVE : 2 * P_LLVMFuzzerTestOneInput.LLVMF_NMAX <= LIVE_LIB.
Hypothesis HSTK : P_LLVMFuzzerTestOneInput.LLVMF_SPDROP + ASTACK <= LLVMF_STK.
Hypothesis TL : PALib (L := scene_listing) (PI := PI_scene) B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMALLOC : amalloc_realizes SEGS B.
Hypothesis AMEMSET : aintrin_realizes SEGS B OSet (SIGMA SS___asan_memset).
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA SS___asan_memcpy).
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA SS___interceptor_trampoline_bcmp).
Hypothesis ASH00 : SetShadowDef.aset_shadow_realizes SEGS B (SIGMA SS___asan_set_shadow_00) 0.
Hypothesis ASHF8 : SetShadowDef.aset_shadow_realizes SEGS B (SIGMA SS___asan_set_shadow_f8) 0xf8.
Hypothesis SSB : treac_ctrl_scene_build_spec (SK := scene_sink_head) (PI := PI_scene) B.
Hypothesis SSM : treac_ctrl_scene_set_mac_spec (SK := scene_sink_head) (PI := PI_scene) B.
Hypothesis HTRACE : rt_trace_in_stmt SEGS RA_LLVMF (pc_malloc_ra0 (as_code B)) (pc_free_ra0 (as_code B))
P_LLVMFuzzerTestOneInput.RT_malloc1_ra P_LLVMFuzzerTestOneInput.RT_malloc2_ra P_LLVMFuzzerTestOneInput.RT_malloc3_ra
P_LLVMFuzzerTestOneInput.RT_free1_ra P_LLVMFuzzerTestOneInput.RT_free2_ra P_LLVMFuzzerTestOneInput.RT_free3_ra (as_universe B).
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let AJSS := aj_set_shadow_at (SK := scene_sink_head) SEGS B LAWS pa_segs_low.
Definition s5_walk : swalk := {| sw_sink := P_LLVMFuzzerTestOneInput.SCENE_SINK_OWNED;
sw_entry := A_LLVMF; sw_ra := RA_LLVMF; sw_ev := EV_LIB; sw_live := LIVE_LIB;
sw_stk := LLVMF_STK; sw_empty := A_EMPTY;
sw_xm := fun _ : Z => 0; sw_xn := fun _ : Z => 0;
sw_rlo := RLO; sw_rhi := RHI |}.
Let errno_low : api_env SEGS B := pal_env B TL.
Let RUNP := SRr_run_pi_AJ (SK := scene_sink_head) B LAWS.
Let RUNC := SRr_run_pi_AJ_call (SK := scene_sink_head) B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ (SK := scene_sink_head) B LAWS.
Let BR := paj_branch (PI := PI_scene).
#[local] Notation IM := scene_geom_asan_ubsan.

(* ---- the spill slots the block reloads through s1 (x9): [s1+0x10] shF+0x1c, [s1+0x18] F, [s1+0x20] n'',
   [s1+0x28] F, [s1+0x30] expect = F+224, [s1+0x38] mac = F+112.  Extra atoms: 32 = n'', 33 = F. ---- *)
Definition s5_spills : list YP09.chunk :=
[ YP09.mkChunk 0x10 (CVal 8 (SOff 19 28));
  YP09.mkChunk 0x18 (CVal 8 (SOff 33 0));
  YP09.mkChunk 0x20 (CVal 8 (SOff 32 0));
  YP09.mkChunk 0x28 (CVal 8 (SOff 33 0));
  YP09.mkChunk 0x30 (CVal 8 (SOff 33 224));
  YP09.mkChunk 0x38 (CVal 8 (SOff 33 112)) ].
Definition s5_spill_region : YP09.region := YP09.mkRegion (Some 9%nat) 0x10 0x40 0 0 s5_spills.
Definition s5_extra (nn F : Z) : list word := [Z_to_bv 64 nn; Z_to_bv 64 F].
Definition s5_spills_at (W : world SEGS) (mem : word -> option byte) (sp1 F sF nn : Z) : Prop :=
rdword (aview SEGS (w_H W) mem) (sp1 + 16) = Some (sF + 28) /\
rdword (aview SEGS (w_H W) mem) (sp1 + 24) = Some F /\
rdword (aview SEGS (w_H W) mem) (sp1 + 32) = Some nn /\
rdword (aview SEGS (w_H W) mem) (sp1 + 40) = Some F /\
rdword (aview SEGS (w_H W) mem) (sp1 + 48) = Some (F + 224) /\
rdword (aview SEGS (w_H W) mem) (sp1 + 56) = Some (F + 112).
Lemma s5_spills_kept : forall W W' mem mem' sp1 F sF nn,
(forall a, sp1 + 16 <= a < sp1 + 64 -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
s5_spills_at W mem sp1 F sF nn -> s5_spills_at W' mem' sp1 F sF nn.
Proof.
intros W W' mem mem' sp1 F sF nn Hk (H1 & H2 & H3 & H4 & H5 & H6).
repeat split; [rewrite <- H1 | rewrite <- H2 | rewrite <- H3 | rewrite <- H4 | rewrite <- H5 | rewrite <- H6];
apply rdword_ext; intros k Hk'; apply Hk; lia.
Qed.
Lemma s5_entry : forall (W : world SEGS) regs mem pc sp1 F sF nn,
getr regs 9 = Z_to_bv 64 sp1 -> getr regs 19 = Z_to_bv 64 sF ->
0 <= sp1 -> sp1 + 64 <= 2 ^ 64 -> 0 <= F -> F + 224 < 2 ^ 64 -> 0 <= sF -> sF + 28 < 2 ^ 64 ->
0 <= nn < 2 ^ 64 ->
s5_spills_at W mem sp1 F sF nn ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (s5_extra nn F)))
(mkSS pc sr_atoms [s5_spill_region] None (mkFacts [] [] []))
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
intros W regs mem pc sp1 F sF nn R9 R19 H1 H2 H3 H4 H5 H6 Hn (V1 & V2 & V3 & V4 & V5 & V6).
set (E := Eimg (Ereg regs (s5_extra nn F))).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
by (intros n r Hr; apply ew_Eimg_Ereg_nat; exact Hr).
assert (U9 : bv_unsigned (ew E 9) = sp1) by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E 19) = sF) by (rewrite (EE 19%nat 19%bv eq_refl), R19; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = nn)
by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_extra regs _ 0); apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = F)
by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_extra regs _ 1); apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor]. unfold region_ok, s5_spill_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst].
  rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  unfold s5_spills. repeat apply Forall_cons; try apply Forall_nil.
  + apply (chunk_ok_val SEGS E _ sp1 16 8 (SOff 19 28) (sF + 28));
    [cbn [sv_denot]; rewrite U19; reflexivity | change (8 * Z.of_N 8) with 64; lia | zside |].
    exact (val_mem_of_rdword SEGS _ _ _ _ V1).
  + apply (chunk_ok_val SEGS E _ sp1 24 8 (SOff 33 0) F);
    [cbn [sv_denot]; rewrite U33, Z.add_0_r; reflexivity | change (8 * Z.of_N 8) with 64; lia | zside |].
    exact (val_mem_of_rdword SEGS _ _ _ _ V2).
  + apply (chunk_ok_val SEGS E _ sp1 32 8 (SOff 32 0) nn);
    [cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity | change (8 * Z.of_N 8) with 64; lia | zside |].
    exact (val_mem_of_rdword SEGS _ _ _ _ V3).
  + apply (chunk_ok_val SEGS E _ sp1 40 8 (SOff 33 0) F);
    [cbn [sv_denot]; rewrite U33, Z.add_0_r; reflexivity | change (8 * Z.of_N 8) with 64; lia | zside |].
    exact (val_mem_of_rdword SEGS _ _ _ _ V4).
  + apply (chunk_ok_val SEGS E _ sp1 48 8 (SOff 33 224) (F + 224));
    [cbn [sv_denot]; rewrite U33; reflexivity | change (8 * Z.of_N 8) with 64; lia | zside |].
    exact (val_mem_of_rdword SEGS _ _ _ _ V5).
  + apply (chunk_ok_val SEGS E _ sp1 56 8 (SOff 33 112) (F + 112));
    [cbn [sv_denot]; rewrite U33; reflexivity | change (8 * Z.of_N 8) with 64; lia | zside |].
    exact (val_mem_of_rdword SEGS _ _ _ _ V6).
- cbn. tauto.
- unfold facts_ok; cbn; tauto.
Qed.
(* The entry state of the three `sw` tag stores (0x830e4, 0x830fc, 0x83114): the spill region and one 4-byte writable
   region per store, at expect + 0 (based on s2 = x18), expect + 0x368 and expect + 0x37c (based on atom 33 = F). *)
Definition s5_tag_regions : list YP09.region :=
[ YP09.mkRegion (Some 18%nat) 0 4 0 4 [];
  YP09.mkRegion (Some 33%nat) 1096 1100 1096 1100 [];
  YP09.mkRegion (Some 33%nat) 1116 1120 1116 1120 [] ].
Lemma s5_entry_t : forall (W : world SEGS) regs mem pc sp1 F sF nn,
getr regs 9 = Z_to_bv 64 sp1 -> getr regs 19 = Z_to_bv 64 sF -> getr regs 18 = Z_to_bv 64 (F + 224) ->
0 <= sp1 -> sp1 + 64 <= 2 ^ 64 -> 0 <= F -> F + 9128 <= sp1 + 16 -> 0 <= sF -> sF + 28 < 2 ^ 64 ->
0 <= nn < 2 ^ 64 ->
(forall a, F + 224 <= a < F + 228 \/ F + 1096 <= a < F + 1100 \/ F + 1116 <= a < F + 1120 -> apresent (w_H W) mem a) ->
s5_spills_at W mem sp1 F sF nn ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (s5_extra nn F)))
(mkSS pc sr_atoms (s5_spill_region :: s5_tag_regions) None (mkFacts [] [] []))
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
intros W regs mem pc sp1 F sF nn R9 R19 R18 H1 H2 H3 H4 H5 H6 Hn HPR (V1 & V2 & V3 & V4 & V5 & V6).
set (E := Eimg (Ereg regs (s5_extra nn F))).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
by (intros n r Hr; apply ew_Eimg_Ereg_nat; exact Hr).
assert (U9 : bv_unsigned (ew E 9) = sp1) by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
assert (U18 : bv_unsigned (ew E 18) = F + 224) by (rewrite (EE 18%nat 18%bv eq_refl), R18; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E 19) = sF) by (rewrite (EE 19%nat 19%bv eq_refl), R19; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = nn)
by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_extra regs _ 0); apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = F)
by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_extra regs _ 1); apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor.
  { unfold region_ok, s5_spill_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst].
    rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    unfold s5_spills. repeat apply Forall_cons; try apply Forall_nil.
    + apply (chunk_ok_val SEGS E _ sp1 16 8 (SOff 19 28) (sF + 28));
      [cbn [sv_denot]; rewrite U19; reflexivity | change (8 * Z.of_N 8) with 64; lia | zside |].
      exact (val_mem_of_rdword SEGS _ _ _ _ V1).
    + apply (chunk_ok_val SEGS E _ sp1 24 8 (SOff 33 0) F);
      [cbn [sv_denot]; rewrite U33, Z.add_0_r; reflexivity | change (8 * Z.of_N 8) with 64; lia | zside |].
      exact (val_mem_of_rdword SEGS _ _ _ _ V2).
    + apply (chunk_ok_val SEGS E _ sp1 32 8 (SOff 32 0) nn);
      [cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity | change (8 * Z.of_N 8) with 64; lia | zside |].
      exact (val_mem_of_rdword SEGS _ _ _ _ V3).
    + apply (chunk_ok_val SEGS E _ sp1 40 8 (SOff 33 0) F);
      [cbn [sv_denot]; rewrite U33, Z.add_0_r; reflexivity | change (8 * Z.of_N 8) with 64; lia | zside |].
      exact (val_mem_of_rdword SEGS _ _ _ _ V4).
    + apply (chunk_ok_val SEGS E _ sp1 48 8 (SOff 33 224) (F + 224));
      [cbn [sv_denot]; rewrite U33; reflexivity | change (8 * Z.of_N 8) with 64; lia | zside |].
      exact (val_mem_of_rdword SEGS _ _ _ _ V5).
    + apply (chunk_ok_val SEGS E _ sp1 56 8 (SOff 33 112) (F + 112));
      [cbn [sv_denot]; rewrite U33; reflexivity | change (8 * Z.of_N 8) with 64; lia | zside |].
      exact (val_mem_of_rdword SEGS _ _ _ _ V6). }
  unfold s5_tag_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
  first [rewrite U18 | rewrite U33];
  (split; [lia|]); (split; [lia|]); (split; [intros o Ho; apply (apresent_writable SEGS); apply HPR; lia | apply Forall_nil]).
- unfold s5_tag_regions, s5_spill_region.
  cbn [YP09.pairwise_disjoint YP09.all_disjoint YP09.extent_disjoint YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val].
  unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val base_val].
  rewrite U9, U18, U33. repeat split; lia.
- unfold facts_ok; cbn; tauto.
Qed.
(* scene_tag outside the twelve tag offsets (a Theorem Labs lane's P_reac_ctrl_scene_build.v scene_tags) *)
Lemma s5_tag0 : forall i, ~ In i [0; 1; 2; 3; 872; 873; 874; 875; 892; 893; 894; 895] -> scene_tag i = 0.
Proof.
intros i Hn. unfold scene_tag, scene_tags. cbn [find fst].
repeat match goal with
| |- context [?k =? i] => destruct (Z.eqb_spec k i) as [?Hq | ?Hq];
    [exfalso; apply Hn; subst i; cbn [In]; lia | cbn [find fst snd] ]
end.
reflexivity.
Qed.
(* The caller chain at a call of the walk (cgif_file_fuzzer A/ACf5.v:172-186 rt_chain; a Theorem Labs lane's S5 kit s5_chain). *)
Lemma s5_chain : forall ly (rd rd' : reader) (regs : bvmap 5 word) sp',
achain ly rd (spZ regs) (s0Z regs) [] -> ly_top ly <= 2 ^ 64 ->
(forall a, spZ regs <= a < 2 ^ 64 -> rd' a = rd a) ->
rdword rd' (spZ regs - 8) = Some (raZ regs) -> rdword rd' (spZ regs - 16) = Some (s0Z regs) -> 4096 <= raZ regs ->
alloc_ceiling <= spZ regs -> spZ regs mod 8 = 0 -> sp' + 16 <= spZ regs ->
achain ly rd' sp' (spZ regs) (if spZ regs + 16 <? ly_top ly then [(spZ regs, raZ regs, s0Z regs)] else []).
Proof.
intros ly rd rd' regs sp' Hch Htop64 Hk H8 H16 Hra Hceil Hal Hsp'.
destruct (Z.ltb_spec (spZ regs + 16) (ly_top ly)) as [Hlt | Hge].
- apply (achain_push ly rd rd' (spZ regs) (s0Z regs) (raZ regs) [] sp' Hch Htop64 Hk);
  [exact H8 | exact H16 | exact Hra | exact Hceil | exact Hal | lia | exact Hsp'].
- left. split; [right; left; lia | reflexivity].
Qed.
(* The callee-saved registers the block relies on: sp = s1 = sp1, s0 = sp0, gp, tp, s3 = shF, s4 = body, s8 = n'. *)
Definition s5_rk (sp0 sp1 sF body np : Z) (regs : bvmap 5 word) : Prop :=
getr regs 2 = Z_to_bv 64 sp1 /\ getr regs 3 = YG0d.w64 (as_gp B) /\ getr regs 4 = YG0d.w64 (as_tp B) /\
getr regs 8 = Z_to_bv 64 sp0 /\ getr regs 9 = Z_to_bv 64 sp1 /\ getr regs 19 = Z_to_bv 64 sF /\
getr regs 20 = Z_to_bv 64 body /\ getr regs 24 = Z_to_bv 64 np.
Lemma s5_rk_pres : forall sp0 sp1 sF body np regs regs',
aregs_preserved regs regs' -> s5_rk sp0 sp1 sF body np regs -> s5_rk sp0 sp1 sF body np regs'.
Proof.
intros sp0 sp1 sF body np regs regs' HP (R2 & R3 & R4 & R8 & R9 & R19 & R20 & R24).
repeat split;
[ rewrite <- R2 | rewrite <- R3 | rewrite <- R4 | rewrite <- R8 | rewrite <- R9 | rewrite <- R19 | rewrite <- R20 | rewrite <- R24 ];
first [ exact (HP 2 ltac:(unfold acallee_saved; lia)) | exact (HP 3 ltac:(unfold acallee_saved; lia))
| exact (HP 4 ltac:(unfold acallee_saved; lia)) | exact (HP 8 ltac:(unfold acallee_saved; lia))
| exact (HP 9 ltac:(unfold acallee_saved; lia)) | exact (HP 19 ltac:(unfold acallee_saved; lia))
| exact (HP 20 ltac:(unfold acallee_saved; lia)) | exact (HP 24 ltac:(unfold acallee_saved; lia)) ].
Qed.
Lemma s5_rk_kept : forall sp0 sp1 sF body np regs regs',
(forall r, In r [2; 3; 4; 8; 9; 19; 20; 24]%bv -> getr regs' r = getr regs r) ->
s5_rk sp0 sp1 sF body np regs -> s5_rk sp0 sp1 sF body np regs'.
Proof.
intros sp0 sp1 sF body np regs regs' HK (R2 & R3 & R4 & R8 & R9 & R19 & R20 & R24).
repeat split; rewrite HK by (cbn; tauto); assumption.
Qed.
(* The bytes S5 hands back unchanged at C6: the six spill words [sp1+16, sp1+64), the 13 saved words
   [sp0-104, sp0), the frame's flag word, mac, and the frame shadow outside the expect row; the expect row
   shF+[28, 1141) is what the set_shadow_00 / set_shadow_f8 pair works on. *)
Definition s5_prot (sp0 sp1 F sF a : Z) : Prop :=
(sp1 + 16 <= a < sp1 + 64) \/ (sp0 - 104 <= a < sp0) \/ (F + 16376 <= a < F + 16384) \/ (F + 112 <= a < F + 118) \/
(sF <= a < sF + 28) \/ (sF + 1141 <= a < sF + 1176).
Definition s5_row (sF a : Z) : Prop := sF + 28 <= a < sF + 1141.
(* `seqz s2, (s8 xor 8904)` (0x82fbc-0x82fc0). *)
Lemma s5_seqz_xor : forall x : word,
bv_unsigned (alu64 ALU_SLTU (alu64 ALU_XOR x (Z_to_bv 64 8904)) (Z_to_bv 64 1)) = (if bv_unsigned x =? 8904 then 1 else 0).
Proof.
intros x. rewrite YO0c.seqz_unsigned, YO0c.alu64_xor. change (bv_unsigned (Z_to_bv 64 8904)) with 8904.
destruct (Z.eqb_spec (Z.lxor (bv_unsigned x) 8904) 0) as [H|H]; destruct (Z.eqb_spec (bv_unsigned x) 8904) as [H'|H']; try reflexivity.
- exfalso. apply H'. apply Z.lxor_eq_0_iff. exact H.
- exfalso. apply H. rewrite H'. reflexivity.
Qed.
(* pin a register of the symbolic state to a literal (a Theorem Labs lane's P_check_step_S2.v `pin`) and add an atom fact *)
Local Ltac pin HS r e Hr :=
  let H := fresh "HSp" in
  pose proof (ast_ok_pi_set_reg_fp _ _ _ r e HS eq_refl
    ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite Hr; reflexivity)) as H;
  clear HS; rename H into HS; cbn [add_atom ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
Local Ltac addf HS n f Hf :=
  let H := fresh "HSf" in
  pose proof (st_ok_pi_add_fact _ _ _ n f HS Hf) as H; clear HS; rename H into HS.

Lemma seg_S5_au : seg_S5_stmt (SK := scene_sink_head) SEGS B ameter_triv s5_walk IM.
Proof.
unfold seg_S5_stmt, sc_from_C5.
intros cx POST HB HC6 ly3 S3 W3 regs3 mem3 md3 bs body bb ev HC5.
unfold cut_C5 in HC5. cbn [sg_cid sg_off_mac sg_off_blk sg_off_expect sg_mac_n sg_blk_n sg_scene_n sg_sh_blki_lo sg_sh_blki_hi
sg5_sp0 sg5_sp1 sg5_F sg5_Fsp sg5_shF sg5_expect sg5_mac sg5_shexp sg5_body sg5_nn sg5_nprime sg_pc_c5 scene_geom_asan_ubsan] in HC5.
destruct HC5 as (Hevr & HJ0 & HPerm & HBB & HBLK & Hlenbb & Hbody8 & HFRM & HSAV & HSHBG & HSHBI & HOPBLK & HOPMAC & HIMG & HIN & Hnn1 & HMACB
& V_sp0 & V_sp1 & V_F & V_Fsp & V_shF & V_expect & V_mac & V_shexp & V_body & V_nn & V_nprime).
unfold RV_s0, RV_s1, RV_s3, RV_s4, RV_s8 in *.
cbn [vat] in V_sp0, V_sp1, V_F, V_Fsp, V_shF, V_expect, V_mac, V_shexp, V_body, V_nn, V_nprime.
destruct HB as (HB0 & Hsp1eq).
destruct HB0 as (HAFN & Hra0 & Hp0 & Hn0 & Hpn & Hfrs0 & Hev0 & Hlive0 & HROD0 & HSNK0 & HFD0 & HSORT0 & HMOK0).
destruct HJ0 as (HJ & Hfrs3 & HMLE).
cbn [sg_cid scene_geom_asan_ubsan] in HJ, Hfrs3.
destruct HIMG as (Hsp3 & Hgp3 & Htp3 & HROD3).
cbn [sw_stk sw_ev sw_live sw_ra sw_rlo sw_rhi s5_walk] in *.
pose proof HAFN as (HAR0 & Hra4' & Hra4 & Hgp0 & Htp0 & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hstklo & Hstkhi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR3 & Hly3 & Hsecs3 & Hwle3 & Hio3 & _ & Hnev3 & Hk3 & _).
pose proof pa_base_lo as HBLO. pose proof pa_B_ok as HBOK.
assert (Hes : ESTACK = 4096) by reflexivity. assert (Has : ASTACK = 16384) by reflexivity.
unfold P_LLVMFuzzerTestOneInput.LLVMF_SPDROP in HSTK. unfold P_LLVMFuzzerTestOneInput.LLVMF_EV in HEV.
unfold P_LLVMFuzzerTestOneInput.LLVMF_NMAX in HLIVE.
set (sp0 := spZ (c_regs cx)) in *.
set (F := sc_F SEGS IM cx) in *.
assert (Hfin3 : In (8, c_fpos cx) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly3 HAR0 Hly3) as (_ & EFA & EFL).
assert (EFA3 : frame_addr ly3 8 (c_fpos cx) = F) by (rewrite EFA; reflexivity).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 mem3 md3 8 (c_fpos cx) HAR3 Hfin3) as (HF4096 & HFceil & HFapp).
destruct (al_frames _ _ LAWS ly3 S3 W3 mem3 md3 8 (c_fpos cx) HAR3 Hfin3) as (HF32 & HFin_app & HFpres & HFSpres).
pose proof (frm_off_imgP B ly3 S3 W3 mem3 md3 8 (c_fpos cx) HAR3 Hfin3) as HFimg.
rewrite EFA3 in HF4096, HFceil, HFapp, HF32, HFin_app, HFpres, HFSpres, HFimg.
change (fs_frame_bytes 8) with 16384 in *.
set (sp1 := c_sp1 cx) in *.
set (sF := shadow_addr F) in *.
set (nn := sc_nn IM bs) in *.
set (np := sc_nprime IM bs) in *.
change (224 / 8) with 28 in V_shexp.
assert (Hsp1rng : sp0 - 256 < sp1 <= sp0 - 224)
by (pose proof (Z.div_mod (sp0 - 224) 32 ltac:(lia)); pose proof (Z.mod_pos_bound (sp0 - 224) 32 ltac:(lia)); lia).
assert (Hsp1al16 : sp1 mod 16 = 0).
{ replace sp1 with (32 * ((sp0 - 224) / 32)) by (symmetry; exact Hsp1eq).
  replace (32 * ((sp0 - 224) / 32)) with (((sp0 - 224) / 32 * 2) * 16) by lia. apply Z_mod_mult. }
assert (Hsp1lo : alloc_ceiling + 16000 <= sp1) by lia.
assert (Hsp1hi : sp1 <= 2 ^ 47) by lia.
assert (Hom : (sp1 - sp0) mod 16 = 0) by (rewrite Zminus_mod, Hsp1al16, Hal16; reflexivity).
assert (Hoff : -240 <= sp1 - sp0 <= -224)
by (destruct (proj1 (Z.mod_divide (sp1 - sp0) 16 ltac:(lia)) Hom) as [q Hq]; lia).
assert (HsFlt : 2147450880 + 512 <= sF < 17592186044416 + 2147450880)
by (unfold sF, shadow_addr, SHADOW_OFF;
    pose proof (Z.div_le_lower_bound F 8 512 ltac:(lia) ltac:(lia));
    pose proof (Z.div_lt_upper_bound F 8 17592186044416 ltac:(lia) ltac:(lia)); lia).
assert (Hnnb : 1 <= nn <= 65535) by exact Hnn1.
assert (Hbody4096 : 4096 <= body) by (destruct HBLK as (H & _); exact H).
assert (Hbodyceil : body + req_size nn <= alloc_ceiling) by (destruct HBLK as (_ & _ & H & _); exact H).
assert (Ereq : req_size nn = nn) by (unfold req_size; destruct (Z.eqb_spec nn 0); lia).
assert (HAF : AF_LLVMFuzzerTestOneInput = 0) by reflexivity.
assert (HF8g : forall k, 0 <= k -> (F + 8 * k) / 8 = F / 8 + k).
{ intros k Hk. destruct (proj1 (Z.mod_divide F 32 ltac:(lia)) HF32) as [q Hq]. rewrite Hq.
  replace (q * 32 + 8 * k) with ((4 * q + k) * 8) by lia. replace (q * 32) with ((4 * q) * 8) by lia.
  rewrite !Z.div_mul by lia. reflexivity. }
assert (HcidF : frame_addr (c_ly cx) 8 (c_fpos cx) = F) by reflexivity.
assert (Hbody_new : ~ In (body, nn) (ablocks B (c_ly cx) (c_S cx))).
{ intros Hc. destruct HBLK as (_ & _ & _ & _ & _ & Haftb). destruct (Haftb Hc 0 ltac:(cbn [snd]; rewrite Ereq; lia)) as (r & [] & _). }
unfold cfg_at, YG0d.w64. cbn [sg_pc_c5 scene_geom_asan_ubsan].
rewrite <- (Z.add_assoc BASE AF_LLVMFuzzerTestOneInput SEG_C5_off).
assert (SP3 : s5_spills_at W3 mem3 sp1 F sF nn) by (repeat split; assumption).
pose proof (s5_entry W3 regs3 mem3 (AF_LLVMFuzzerTestOneInput + SEG_C5_off) sp1 F sF nn V_sp1 V_shF
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) SP3) as HS.
remember (Eimg (Ereg regs3 (s5_extra nn F))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs3 r)
by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HAG : env_agree 32 (Ereg regs3 (s5_extra nn F)) E)
by (subst E; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E32 : ew E 32 = Z_to_bv 64 nn)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 0)).
(* ---- run 1: 0x82fa4 `ld a0,0x20(s1)`, then the call of __wrap_malloc at 0x82fa8 ---- *)
paj_run_shc RUNP RUNC HS HJ.
{ intros a (r & Hin & Ha).
  lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
  cbn [In] in Hin. destruct Hin as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. lia. }
rename ms into msA, HJ into HJA, HFr into HFrA. clear HF HG.
assert (KA : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem msA) a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. eapply (aview_kept_frame _ _ _ _ _ 0 HFrA); [lia | | exact Ha].
  intros b Hb (r & Hin & Hrb).
  lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
  cbn [In] in Hin. destruct Hin as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb. lia. }
clear HFrA.
prreg HS (10%bv : bv 5) Ra0. prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp.
assert (RKAl : forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr (ms_regs msA) r = getr regs3 r).
{ intros x Hx. exact (regs_kept_of_st_ok SEGS E _ (restrict (w_H W3) msA) regs3 (s5_extra nn F)
  [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HS HAG eq_refl x Hx). }
pmkst HS.
pose proof HJA as (_ & _ & _ & _ & _ & _ & _ & _ & HJup & _).
assert (Rsp' : spZ (ms_regs msA) = sp1) by (unfold spZ at 1; rewrite Rsp, (EE 2%nat 2%bv eq_refl); exact Hsp3).
assert (Rs0' : s0Z (ms_regs msA) = sp0)
by (unfold s0Z; rewrite (RKAl 8%bv ltac:(cbn; tauto)), V_sp0; unfold YG0d.w64; apply unsigned_lit_small; lia).
assert (Rra' : raZ (ms_regs msA) = P_LLVMFuzzerTestOneInput.RT_malloc3_ra)
by (unfold raZ, P_LLVMFuzzerTestOneInput.RT_malloc3_ra, P_LLVMFuzzerTestOneInput.RT_malloc3_off;
    rewrite Rra, HAF; apply unsigned_lit_small; lia).
assert (Hsave : forall j, 0 <= j < 13 -> rdword (aview SEGS (w_H W3) (ms_mem msA)) (sp0 - 8 - 8 * j)
= Some (bv_unsigned (getr (c_regs cx) (nth (Z.to_nat j) sc_saved_regs 0%bv)))).
{ intros j Hj. rewrite <- (HSAV j Hj). apply rdword_ext. intros k Hk. apply KA. lia. }
assert (Hach : achain ly3 (aview SEGS (w_H W3) (ms_mem msA)) sp1 sp0 (rt_ch cx)).
{ unfold rt_ch. apply (achain_ly_top (c_ly cx)).
  - pose proof Hly3 as LY. destruct LY as (_ & _ & _ & _ & _ & _ & _ & _ & LT & _). exact LT.
  - apply (s5_chain (c_ly cx) (aview SEGS (w_H (c_W cx)) (c_mem cx)) _ (c_regs cx) sp1 Hch0); [lia | | | | exact Hra4 | lia | | lia].
    + intros a Ha. apply HJup; lia.
    + replace (spZ (c_regs cx) - 8) with (sp0 - 8 - 8 * 0) by (unfold sp0; lia). exact (Hsave 0 ltac:(lia)).
    + replace (spZ (c_regs cx) - 16) with (sp0 - 8 - 8 * 1) by (unfold sp0; lia). exact (Hsave 1 ltac:(lia)).
    + fold sp0. destruct (proj1 (Z.mod_divide sp0 16 ltac:(lia)) Hal16) as [q Hq]. rewrite Hq.
      replace (q * 16) with ((2 * q) * 8) by lia. apply Z_mod_mult. }
rewrite (pal_malloc B TL).
eapply SRr_bind.
{ eapply (amalloc04_rule_triv (SK := scene_sink_head) SEGS B pa_segs_low errno_low LAWS ML AMALLOC W3 (ms_regs msA) (ms_mem msA) LLVMF_STK sp0 []
  (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(8, c_fpos cx)] ly3 S3 _ ev nn (sp1 - sp0)
  (Z_to_bv 64 (BASE + 1800)) (rt_ch cx) HJA).
  - rewrite Ra0, E32. reflexivity.
  - unfold MALLOC_MAX. lia.
  - unfold LIVE_MAX in *. rewrite Ereq in HBB. lia.
  - rewrite Rsp'. lia.
  - exact Hom.
  - lia.
  - lia.
  - rewrite (RKAl 3%bv ltac:(cbn; tauto)). exact Hgp3.
  - rewrite (RKAl 4%bv ltac:(cbn; tauto)). exact Htp3.
  - exact Rra.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold EV_MAX in *. lia.
  - apply (achain_chain_pre ly3 _ sp1 sp0 (rt_ch cx) (ms_regs msA) Hach); [rewrite Rsp'; lia | exact Rs0' |].
    rewrite Rra'. unfold P_LLVMFuzzerTestOneInput.RT_malloc3_ra, P_LLVMFuzzerTestOneInput.RT_malloc3_off. rewrite HAF. lia.
  - apply (HTRACE (pc_malloc_ra0 (as_code B)) P_LLVMFuzzerTestOneInput.RT_malloc3_ra (ms_regs msA) cx Hra0 Rra').
    left. split; [reflexivity | right; right; reflexivity].
  - exact I. }
cbv beta. intros W4 c4 _ (ly4 & S4 & regs4 & mem4 & md4 & res & -> & HJ4 & HP4 & Ha04 & Hfrs4 & Hres & Eab4 & HK4 & _).
assert (RK3 : s5_rk sp0 sp1 sF body np regs3).
{ unfold s5_rk. split; [rewrite <- Hsp3; unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity|].
  split; [exact Hgp3|]. split; [exact Htp3|]. split; [exact V_sp0|]. split; [exact V_sp1|].
  split; [exact V_shF|]. split; [exact V_body | exact V_nprime]. }
assert (RKA : s5_rk sp0 sp1 sF body np (ms_regs msA))
by (apply (s5_rk_kept _ _ _ _ _ regs3); [intros r Hr; apply RKAl; cbn in Hr |- *; tauto | exact RK3]).
pose proof (s5_rk_pres _ _ _ _ _ _ _ HP4 RKA) as RK4.
assert (SPA : s5_spills_at W3 (ms_mem msA) sp1 F sF nn)
by (apply (s5_spills_kept W3 W3 mem3); [intros a Ha; apply KA; lia | exact SP3]).
pose proof HK4 as (HK4up & HK4blk & HK4img & HK4frm & HK4pres & HK4win).
assert (SP4 : s5_spills_at W4 mem4 sp1 F sF nn)
by (apply (s5_spills_kept W3 W4 (ms_mem msA)); [intros a Ha; apply HK4up; lia | exact SPA]).
pose proof RK4 as (R4_2 & R4_3 & R4_4 & R4_8 & R4_9 & R4_19 & R4_20 & R4_24).
clear HS HE HEI EE HAG E32 Ra0 Rra Rsp E.
(* ---- block B: 0x82fac `beqz a0` (refuted), then up to the call of __asan_memcpy at 0x82fd0 ---- *)
pose proof (s5_entry W4 regs4 mem4 1800 sp1 F sF nn R4_9 R4_19 ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) SP4) as HS.
remember (Eimg (Ereg regs4 (s5_extra nn F))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (Hin4 : In (res, nn) (ablocks B ly4 S4)) by (rewrite Eab4; apply in_or_app; right; left; reflexivity).
pose proof (proj1 HJ4) as HAR4.
destruct (al_blocks _ _ LAWS _ _ _ _ _ res nn HAR4 Hin4) as (Hres16 & Hres4096' & Hresceil & Hresapp & Hrespres & _).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs4 r)
by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
(* ---- the cut C6, from what each arm gives back: the journal, the protected bytes, the registers ---- *)
assert (Hftok : aftok [] (ablocks B (c_ly cx) (c_S cx)) (res, nn))
by (eapply (aftok_new_block (SK := scene_sink_head) SEGS B LAWS); [exact HJA | exact HAR4 | exact Eab4 | lia]).
assert (Hfresh : ~ In (res, nn) (ablocks B (c_ly cx) (c_S cx))).
{ intros Hc. destruct (Hftok Hc 0 ltac:(cbn [snd]; lia)) as (r & [] & _). }
unfold sc_from_C6 in HC6.
assert (EXIT : forall regs6 mem6 md6,
ajournal (SK := scene_sink_head) SEGS B LLVMF_STK sp0 [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(8, c_fpos cx)] ly4 S4 W4 mem6 md6 (ev + 1) ->
(forall a, s5_prot sp0 sp1 F sF a -> aview SEGS (w_H W4) mem6 a = aview SEGS (w_H W3) mem3 a) ->
(forall a, s5_row sF a -> aview SEGS (w_H W4) mem6 a = aview SEGS (w_H W3) mem3 a) ->
s5_rk sp0 sp1 sF body np regs6 -> getr regs6 22 = Z_to_bv 64 res ->
SRr SEGS W4 (mkCfg (mkst regs6 (Z_to_bv 64 (BASE + 2228)) mem6 (seg_rom SEGS)) md6) POST).
{ intros regs6 mem6 md6 HJ6 KP6 KR6 RK6 R6_22.
  pose proof RK6 as (R6_2 & R6_3 & R6_4 & R6_8 & R6_9 & R6_19 & R6_20 & R6_24).
  pose proof HJ6 as (HAR6 & Hly6 & _ & _ & _ & Hfrs6 & Hnev6 & _).
  replace (Z_to_bv 64 (BASE + 2228)) with (YG0d.w64 (sg_pc_c6 IM))
  by (cbn [sg_pc_c6 scene_geom_asan_ubsan]; unfold YG0d.w64, SEG_C6_off; rewrite HAF; f_equal).
  change (mkCfg (mkst regs6 (YG0d.w64 (sg_pc_c6 IM)) mem6 (seg_rom SEGS)) md6) with (cfg_at SEGS (sg_pc_c6 IM) regs6 mem6 md6).
  apply (HC6 ly4 S4 W4 regs6 mem6 md6 bs body res (ev + 1)).
  destruct (al_layout _ _ LAWS _ _ _ _ _ ly4 HAR0 Hly6) as (_ & EFA6 & _).
  assert (Hfin4 : In (8, c_fpos cx) (frames S4)) by (rewrite Hfrs6; left; reflexivity).
  destruct (al_frames _ _ LAWS ly4 S4 W4 mem6 md6 8 (c_fpos cx) HAR6 Hfin4) as (_ & _ & HFp6 & HFSp6).
  assert (EF6 : frame_addr ly4 8 (c_fpos cx) = F) by (rewrite EFA6; reflexivity).
  rewrite EF6 in HFp6, HFSp6. change (fs_frame_bytes 8) with 16384 in HFp6, HFSp6.
  change (16384 / 8) with 2048 in HFSp6.
  assert (KSH : forall o, 0 <= o < 1176 -> aview SEGS (w_H W4) mem6 (sF + o) = aview SEGS (w_H W3) mem3 (sF + o)).
  { intros o Ho. destruct (Z_lt_dec o 28); [|destruct (Z_lt_dec o 1141)].
    - apply KP6. unfold s5_prot. right; right; right; right; left. lia.
    - apply KR6. unfold s5_row. lia.
    - apply KP6. unfold s5_prot. right; right; right; right; right. lia. }
  assert (HF8 : forall k, 0 <= k -> (F + 8 * k) / 8 = F / 8 + k).
  { intros k Hk. destruct (proj1 (Z.mod_divide F 32 ltac:(lia)) HF32) as [q Hq]. rewrite Hq.
    replace (q * 32 + 8 * k) with ((4 * q + k) * 8) by lia. replace (q * 32) with ((4 * q) * 8) by lia.
    rewrite !Z.div_mul by lia. reflexivity. }
  destruct HFRM as (HFLAG & _ & _).
  cbn [sg_cid scene_geom_asan_ubsan] in HFLAG. change (fs_frame_bytes 8) with 16384 in HFLAG.
  cbn [sc_open sg_off_blk sg_blk_n sg_off_mac sg_mac_n scene_geom_asan_ubsan] in HOPBLK, HOPMAC.
  unfold cut_C6.
  cbn [sg_cid sg_sh_blki_lo sg_sh_blki_hi sg_off_blk sg_blk_n sg_off_mac sg_mac_n sg6_sp0 sg6_sp1 sg6_F sg6_Fsp
  sg6_shF sg6_body sg6_before scene_geom_asan_ubsan vat].
  unfold RV_s0, RV_s1, RV_s3, RV_s4, RV_s6.
  fold sp0 sp1 F nn. fold sF.
  split; [lia|].
  split; [split; [exact HJ6|]; split; [rewrite Hfrs6, Hfrs0; reflexivity | exact I]|].
  split; [rewrite Eab4; apply Permutation_app_tail; exact HPerm|].
  split.
  { rewrite (blocks_bytes_bsum B ly4 S4), Eab4, bsum_app, <- (blocks_bytes_bsum B ly3 S3).
    change (bsum [(res, nn)]) with (nn + 0). rewrite Ereq in HBB |- *. lia. }
  split; [exact HBLK|].
  split.
  { unfold sc_blk_ok. split; [lia|]. split.
    { apply zone2_of_app; [exact Hresapp | exact (blk_off_imgP B ly4 S4 W4 mem4 md4 res nn HAR4 Hin4)]. }
    split; [exact Hresceil|]. split; [exact Hres16|]. split; [|exact Hftok].
    intros blc lyq ownq i Hb Hi. right; right; left. exists res, nn. split; [exact Hb|]. split; [exact Hfresh | lia]. }
  split.
  { unfold sc_frame. cbn [sg_cid scene_geom_asan_ubsan]. change (fs_frame_bytes 8) with 16384. fold F. fold sF.
    split; [rewrite <- HFLAG; apply rdword_ext; intros k Hk; apply KP6; unfold s5_prot; right; right; left; lia|].
    split; [intros a Ha; exact (proj1 (HFp6 a Ha))|].
    change (16384 / 8) with 2048. intros a Ha. replace a with (shadow_addr F + (a - shadow_addr F)) by lia.
    exact (proj1 (HFSp6 (a - shadow_addr F) ltac:(fold sF; lia))). }
  split; [intros j Hj; rewrite <- (HSAV j Hj); apply rdword_ext; intros k Hk; apply KP6; unfold s5_prot; right; left; lia|].
  split.
  { unfold sc_shbg in *. cbn [sg_sh_bg scene_geom_asan_ubsan] in *. rewrite Forall_forall in *. intros t Ht.
    specialize (HSHBG t Ht). cbn [In] in Ht.
    destruct Ht as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]; cbn [fst snd] in *; unfold sc_shr in *;
    intros o Ho; fold F; fold sF; rewrite KSH by lia; apply HSHBG; exact Ho. }
  split; [unfold sc_shr in *; intros o Ho; fold F; fold sF; rewrite KSH by lia; apply HSHBI; exact Ho|].
  split.
  { unfold sc_open in *. destruct HOPBLK as (Hm & Hn & Hc). split; [exact Hm|]. split; [exact Hn|].
    intros i Hi. change ((34 + 7) / 8) with 5 in Hi.
    assert (Ea : shadow_of_addr SHADOW_OFF (F + 144) + i = sF + (18 + i))
    by (unfold shadow_of_addr, sF, shadow_addr; replace (F + 144) with (F + 8 * 18) by lia; rewrite HF8 by lia; lia).
    fold F. rewrite Ea, KSH by lia. rewrite <- Ea. exact (Hc i Hi). }
  split.
  { unfold sc_open in *. destruct HOPMAC as (Hm & Hn & Hc). split; [exact Hm|]. split; [exact Hn|].
    intros i Hi. change ((6 + 7) / 8) with 1 in Hi.
    assert (Ea : shadow_of_addr SHADOW_OFF (F + 112) + i = sF + (14 + i))
    by (unfold shadow_of_addr, sF, shadow_addr; replace (F + 112) with (F + 8 * 14) by lia; rewrite HF8 by lia; lia).
    fold F. rewrite Ea, KSH by lia. rewrite <- Ea. exact (Hc i Hi). }
  split.
  { unfold sc_img. split; [unfold spZ; rewrite R6_2; apply unsigned_lit_small; lia|].
    split; [exact R6_3|]. split; [exact R6_4|].
    assert (HRODP : arodata_okP SEGS RLO RHI B (aview SEGS (w_H (c_W cx)) (c_mem cx)))
    by (unfold arodata_okP, in_roP; exact HROD0).
    pose proof (arodata_ok_journalP (SK := scene_sink_head) SEGS RLO RHI (@pa_relro_img _ scene_listing PI_scene) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ6 HRODP) as HROD6.
    unfold arodata_okP, in_roP in HROD6. exact HROD6. }
  split; [exact HIN|]. split; [exact Hnn1|].
  split; [exact R6_8|]. split; [exact R6_9|].
  split; [rewrite <- V_F; apply rdword_ext; intros k Hk; apply KP6; unfold s5_prot; left; lia|].
  split; [rewrite <- V_Fsp; apply rdword_ext; intros k Hk; apply KP6; unfold s5_prot; left; lia|].
  split; [exact R6_19|]. split; [exact R6_20 | exact R6_22]. }
(* the bytes the cut keeps are outside every heap block, every callee window and the expect bytes *)
assert (HsFhi : sF + 2048 <= 17594332497920).
{ unfold sF, shadow_addr, SHADOW_OFF.
  pose proof (Z.div_lt_upper_bound F 8 17592185044992 ltac:(lia) ltac:(lia)). lia. }
assert (HFapp' : F + 16384 <= 2147446784 \/ 17594333495296 <= F)
by (unfold in_app, kLowShadowBeg, kHighMemBeg in HFapp; lia).
assert (PCLS : forall a, s5_prot sp0 sp1 F sF a \/ s5_row sF a ->
  (sp1 <= a < 2 ^ 64) \/ (F + 112 <= a < F + 118) \/ (F + 16376 <= a < F + 16384) \/ (sF <= a < sF + 1176)).
{ intros a [Ha | Ha]; unfold s5_prot, s5_row in Ha; lia. }
assert (PH : forall a b m, In (b, m) (ablocks B ly4 S4) -> s5_prot sp0 sp1 F sF a \/ s5_row sF a ->
  ~ (b <= a < b + req_size m)).
{ intros a b m Hbm Ha Hab.
  assert (Hfin4 : In (8, c_fpos cx) (frames S4)) by (rewrite Hfrs4; exact Hfin3).
  pose proof (sep_block_frame SEGS B LAWS ly4 S4 W4 mem4 md4 b m 8 (c_fpos cx) HAR4 Hbm Hfin4) as Hd.
  destruct (al_layout _ _ LAWS _ _ _ _ _ ly4 HAR0 (proj1 (proj2 HJ4))) as (_ & EFA4 & _).
  rewrite EFA4 in Hd. fold F in Hd. change (fs_frame_bytes 8) with 16384 in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR4 Hbm) as (_ & Hb4096 & Hbc & Hbapp & _).
  unfold in_app, kLowShadowBeg, kHighMemBeg in Hbapp.
  pose proof (PCLS a Ha) as HC. clear - Hab Hd Hb4096 Hbc Hbapp HC HsFhi HsFlt C1 Hsp1lo.
  assert (HcidF : frame_addr (c_ly cx) 8 (c_fpos cx) = F) by reflexivity. rewrite HcidF in Hd.
  clear HcidF. destruct HC as [H | [H | [H | H]]]; destruct Hbapp as [_ [Hb1 | [Hb1 Hb2]]]; lia. }
assert (PW : forall a, s5_prot sp0 sp1 F sF a \/ s5_row sF a -> ~ (sp1 - ASTACK <= a < sp1)).
{ intros a Ha Hw. destruct (PCLS a Ha) as [H | [H | [H | H]]]; lia. }
assert (PE : forall a, s5_prot sp0 sp1 F sF a \/ s5_row sF a -> ~ (F + 224 <= a < F + 9128)).
{ intros a [Ha | Ha] He; unfold s5_prot, s5_row in Ha; clear - Ha He HsFhi HsFlt HFapp' HFceil Hsp1lo Hsp1rng C1; lia. }
(* ---- facts on n', body and before ---- *)
assert (Enn : nn = if np =? 0 then 1 else np) by reflexivity.
assert (Hnp0 : 0 <= np).
{ unfold np, sc_nprime, sc_u16. cbn [sg_scene_n scene_geom_asan_ubsan].
  destruct (HIN 1 ltac:(lia)) as ((? & ?) & _). destruct (HIN 2 ltac:(lia)) as ((? & ?) & _).
  destruct (Z.land (bs 0) 1 =? 0); lia. }
assert (Hnp : 0 <= np <= nn) by (rewrite Enn; destruct (Z.eqb_spec np 0); lia).
assert (Hbody3 : In (body, nn) (ablocks B ly3 S3))
by (eapply Permutation_in; [apply Permutation_sym; exact HPerm | apply in_or_app; right; left; reflexivity]).
assert (Hbody4 : In (body, nn) (ablocks B ly4 S4)) by (rewrite Eab4; apply in_or_app; left; exact Hbody3).
assert (HdisjBR : res + nn <= body \/ body + nn <= res).
{ apply in_split in Hbody3 as (l1 & l2 & E1).
  pose proof (sep_blocks_pos SEGS B LAWS ly4 S4 W4 mem4 md4 (body, nn) (res, nn) l1 l2 [] HAR4) as Hd.
  rewrite Eab4, E1, <- app_assoc in Hd. cbn [app] in Hd. specialize (Hd eq_refl).
  unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. rewrite Ereq in Hd. lia. }
(* ---- what malloc kept: the protected bytes and the expect row (frame, frame shadow, the stack above sp1), and body ---- *)
assert (K34 : forall a, s5_prot sp0 sp1 F sF a \/ s5_row sF a -> aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. pose proof (PCLS a Ha) as HC.
  rewrite <- (KA a ltac:(destruct HC as [H|[H|[H|H]]]; lia)).
  assert (HnE : ~ (res <= a < res + req_size nn)) by exact (PH a res nn Hin4 Ha).
  destruct HC as [H | [H | [H | H]]].
  - apply HK4up; lia.
  - apply (HK4frm 8 (c_fpos cx) a Hfin3); [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite EFA3; change (fs_frame_bytes 8) with 16384; lia | exact HnE].
  - apply (HK4frm 8 (c_fpos cx) a Hfin3); [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite EFA3; change (fs_frame_bytes 8) with 16384; lia | exact HnE].
  - apply (HK4frm 8 (c_fpos cx) a Hfin3); [right; unfold in_zr; cbn [fst snd]; rewrite EFA3; fold sF; change (fs_frame_bytes 8 / 8) with 2048; lia | exact HnE]. }
assert (BODY4 : forall i, 0 <= i < nn -> aview SEGS (w_H W4) mem4 (body + i) = aview SEGS (w_H W3) mem3 (body + i)).
{ intros i Hi. rewrite <- (KA (body + i) ltac:(lia)). apply (HK4blk body nn i Hbody3); [rewrite Ereq; lia | lia]. }
(* the beqz a0 at 0x82fac: a0 = res >= 4096 *)
psrr_branch_pi RUNP BR HS.
{ exfalso. cbn [sv_denot] in Hc. rewrite (EE 10%nat 10%bv eq_refl), Ha04 in Hc.
  cbn [branch_taken] in Hc. unfold bv_eqb, YG0d.w64 in Hc.
  rewrite Z.add_0_r, Z_to_bv_bv_unsigned in Hc. rewrite !unsigned_lit_small in Hc by lia.
  apply Z.eqb_eq in Hc. lia. }
paj_run_shc RUNP RUNC HS HJ4.
{ intros a (r & Hin & Ha).
  lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
  cbn [In] in Hin. destruct Hin as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. lia. }
rename ms into msB, HJ4 into HJB, HFr into HFrB. clear HF HG.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
prreg HS (22%bv : bv 5) Rs6. prreg HS (18%bv : bv 5) Rs2.
assert (HAG4 : env_agree 32 (Ereg regs4 (s5_extra nn F)) E)
by (subst E; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (RKB : s5_rk sp0 sp1 sF body np (ms_regs msB)).
{ apply (s5_rk_kept _ _ _ _ _ regs4); [|exact RK4]. intros x Hx.
  exact (regs_kept_of_st_ok SEGS E _ (restrict (w_H W4) msB) regs4 (s5_extra nn F) [2; 3; 4; 8; 9; 19; 20; 24]%bv HS HAG4 eq_refl x Hx). }
pose proof RKB as (RB2 & RB3 & RB4 & RB8 & RB9 & RB19 & RB20 & RB24).
assert (KB : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W4) (ms_mem msB) a = aview SEGS (w_H W4) mem4 a).
{ intros a Ha. eapply (aview_kept_frame _ _ _ _ _ 0 HFrB); [lia | | exact Ha].
  intros b Hb (r & Hin & Hrb).
  lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
  cbn [In] in Hin. destruct Hin as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb. lia. }
clear HFrB.
pmkst HS.
pose proof (proj1 HJB) as HARB.
destruct (al_blocks _ _ LAWS _ _ _ _ _ body nn HARB Hbody4) as (_ & _ & Hbceil & _ & HbpresB & _).
(* ---- __asan_memcpy(before, body, n') at 0x82fd0 ---- *)
eapply SRr_bind.
{ eapply (aj_intrin_at (SK := scene_sink_head) SEGS B LAWS pa_segs_low OCpy (SIGMA SS___asan_memcpy) AMEMCPY W4 (ms_regs msB) (ms_mem msB)
  LLVMF_STK sp0 [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(8, c_fpos cx)] ly4 S4 _ (ev + 1)
  res body np (sp1 - sp0) (Z_to_bv 64 (BASE + 1840)) HJB).
  - rewrite Ra0, (EE 10%nat 10%bv eq_refl). exact Ha04.
  - rewrite Ra1, (EE 20%nat 20%bv eq_refl). exact R4_20.
  - rewrite Ra2, (EE 24%nat 24%bv eq_refl). exact R4_24.
  - lia.
  - lia.
  - lia.
  - unfold spZ at 1. rewrite RB2, unsigned_lit_small by lia. lia.
  - exact Hom.
  - lia.
  - rewrite Hes. lia.
  - exact RB3.
  - exact RB4.
  - exact Rra.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a Ha. split; [| rewrite Hes; lia].
    replace a with (res + (a - res)) by lia.
    eapply (awr_new_block (SK := scene_sink_head) SEGS B LAWS); [exact HJA | exact HAR4 | exact Eab4 | lia | exact Hin4 | lia].
  - eapply (amem_range_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ HARB Hin4); lia.
  - eapply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ HARB Hin4); lia.
  - intros Hnz. eapply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ HARB Hin4); lia.
  - cbv iota. split; [lia|]. split; [lia|]. split.
    { intros a Ha. split; [apply (aview_some_of_apresent SEGS); apply (proj1 (HbpresB a ltac:(lia))) |].
      unfold spZ at 1. rewrite RB2, unsigned_lit_small by lia. rewrite Hes. lia. }
    split; [lia|]. split; [eapply (amem_range_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ HARB Hbody4); lia|].
    split; [eapply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ HARB Hbody4); lia|].
    intros Hnz. eapply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ HARB Hbody4); lia. }
cbv beta. intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & HJ5 & HP5 & Ha05 & Heff5 & Hfr5 & Hpres5).
pose proof (s5_rk_pres _ _ _ _ _ _ _ HP5 RKB) as RK5.
pose proof RK5 as (R5_2 & R5_3 & R5_4 & R5_8 & R5_9 & R5_19 & R5_20 & R5_24).
assert (R5_22 : getr regs5 22 = Z_to_bv 64 res).
{ transitivity (getr (ms_regs msB) 22%bv); [exact (HP5 22 ltac:(unfold acallee_saved; lia))|].
  rewrite Rs6. cbn [sv_denot]. rewrite (EE 10%nat 10%bv eq_refl), Ha04. unfold YG0d.w64.
  rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; first [reflexivity | rewrite unsigned_lit_small by lia; reflexivity]. }
assert (R5_18v : getr regs5 18 = getr (ms_regs msB) 18%bv)
by exact (HP5 18 ltac:(unfold acallee_saved; lia)).
(* memcpy kept every byte outside [res, res + np) and its stack window *)
assert (K45 : forall a, s5_prot sp0 sp1 F sF a \/ s5_row sF a -> aview SEGS (w_H W4) mem5 a = aview SEGS (w_H W4) mem4 a).
{ intros a Ha. pose proof (PCLS a Ha) as HC. rewrite <- (KB a ltac:(destruct HC as [H|[H|[H|H]]]; lia)).
  apply Hfr5; [destruct HC as [H|[H|[H|H]]]; lia | | ].
  - intros Hr. apply (PH a res nn Hin4 Ha). rewrite Ereq. lia.
  - intros Hw. apply (PW a Ha). rewrite Has. rewrite Hes in Hw. lia. }
assert (BODY5 : forall i, 0 <= i < nn -> aview SEGS (w_H W4) mem5 (body + i) = aview SEGS (w_H W3) mem3 (body + i)).
{ intros i Hi. rewrite <- (BODY4 i Hi). rewrite <- (KB (body + i) ltac:(lia)).
  apply Hfr5; [lia | lia | rewrite Hes; lia]. }
assert (BEF5 : forall i, 0 <= i < np -> aview SEGS (w_H W4) mem5 (res + i) = aview SEGS (w_H W3) mem3 (body + i)).
{ intros i Hi. rewrite (Heff5 i Hi). rewrite (KB (body + i) ltac:(lia)). apply BODY4. lia. }
assert (SP5 : s5_spills_at W4 mem5 sp1 F sF nn).
{ apply (s5_spills_kept W3 W4 mem3); [|exact SP3]. intros a Ha.
  assert (Hp : s5_prot sp0 sp1 F sF a \/ s5_row sF a) by (left; unfold s5_prot; lia).
  rewrite (K45 a Hp). exact (K34 a Hp). }
assert (R5_18 : getr regs5 18 = Z_to_bv 64 (if np =? 8904 then 1 else 0)).
{ rewrite R5_18v, Rs2. cbn [sv_denot]. rewrite (EE 24%nat 24%bv eq_refl), R4_24.
  apply bv_eq. rewrite s5_seqz_xor. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned.
  rewrite (unsigned_lit_small np) by lia.
  destruct (np =? 8904); symmetry; apply unsigned_lit_small; lia. }
clear HS HE HEI EE HAG4 Ra0 Ra1 Ra2 Rra Rs6 Rs2 Hc E.
(* the caller chain at any call of the block: the entry's chain pushed with LLVMF's own record (s5_chain) *)
assert (ACH : forall m md k, ajournal (SK := scene_sink_head) SEGS B LLVMF_STK sp0 [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
  [(8, c_fpos cx)] ly4 S4 W4 m md k ->
  (forall a, s5_prot sp0 sp1 F sF a -> aview SEGS (w_H W4) m a = aview SEGS (w_H W3) mem3 a) ->
  achain ly4 (aview SEGS (w_H W4) m) sp1 sp0 (rt_ch cx)).
{ intros m md k HJm KPm.
  pose proof HJm as (_ & HLYm & _ & _ & _ & _ & _ & _ & HJupm & _).
  unfold rt_ch. apply (achain_ly_top (c_ly cx)).
  - destruct HLYm as (_ & _ & _ & _ & _ & _ & _ & _ & LT & _). exact LT.
  - apply (s5_chain (c_ly cx) (aview SEGS (w_H (c_W cx)) (c_mem cx)) _ (c_regs cx) sp1 Hch0); [lia | | | | exact Hra4 | lia | | lia].
    + intros a Ha. apply HJupm; lia.
    + replace (spZ (c_regs cx) - 8) with (sp0 - 8 - 8 * 0) by (unfold sp0; lia).
      transitivity (rdword (aview SEGS (w_H W3) mem3) (sp0 - 8 - 8 * 0)); [|exact (HSAV 0 ltac:(lia))].
      apply rdword_ext. intros kk Hkk. apply KPm. unfold s5_prot. right; left; lia.
    + replace (spZ (c_regs cx) - 16) with (sp0 - 8 - 8 * 1) by (unfold sp0; lia).
      transitivity (rdword (aview SEGS (w_H W3) mem3) (sp0 - 8 - 8 * 1)); [|exact (HSAV 1 ltac:(lia))].
      apply rdword_ext. intros kk Hkk. apply KPm. unfold s5_prot. right; left; lia.
    + fold sp0. destruct (proj1 (Z.mod_divide sp0 16 ltac:(lia)) Hal16) as [q Hq]. rewrite Hq.
      replace (q * 16) with ((2 * q) * 8) by lia. apply Z_mod_mult. }
assert (KP5 : forall a, s5_prot sp0 sp1 F sF a -> aview SEGS (w_H W4) mem5 a = aview SEGS (w_H W3) mem3 a)
by (intros a Ha; rewrite (K45 a (or_introl Ha)); exact (K34 a (or_introl Ha))).
assert (KR5 : forall a, s5_row sF a -> aview SEGS (w_H W4) mem5 a = aview SEGS (w_H W3) mem3 a)
by (intros a Ha; rewrite (K45 a (or_intror Ha)); exact (K34 a (or_intror Ha))).
(* one call of the bcmp wrapper from the block (sp = sp1): aj_bcmp_at with the block's constants discharged *)
assert (BCMP : forall (regsT : bvmap 5 word) m mdT (x y n : Z) (raw : word),
  ajournal (SK := scene_sink_head) SEGS B LLVMF_STK sp0 [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(8, c_fpos cx)] ly4 S4 W4 m mdT (ev + 1) ->
  getr regsT 10 = YG0d.w64 x -> getr regsT 11 = YG0d.w64 y -> getr regsT 12 = YG0d.w64 n -> 0 <= n < 2 ^ 32 ->
  4096 <= x -> x + n <= alloc_ceiling -> 4096 <= y -> y + n <= alloc_ceiling ->
  spZ regsT = sp1 -> getr regsT 3 = YG0d.w64 (as_gp B) -> getr regsT 4 = YG0d.w64 (as_tp B) ->
  getr regsT 1 = raw -> YK0s.ret_ok raw ->
  (forall i, 0 <= i < n -> aview SEGS (w_H W4) m (x + i) <> None) ->
  (forall i, 0 <= i < n -> aview SEGS (w_H W4) m (y + i) <> None) ->
  amem_range x n -> amem_range y n ->
  range_addressable (aview SEGS (w_H W4) m) SHADOW_OFF x n -> (0 < n -> shadow_hull_vis (aview SEGS (w_H W4) m) x n) ->
  range_addressable (aview SEGS (w_H W4) m) SHADOW_OFF y n -> (0 < n -> shadow_hull_vis (aview SEGS (w_H W4) m) y n) ->
  SRr SEGS W4 (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA SS___interceptor_trampoline_bcmp)) m (seg_rom SEGS)) mdT)
  (fun W2 c2 => W2 = W4 /\ exists regs2 mem2 md2 (v : word),
    c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
    ajournal (SK := scene_sink_head) SEGS B LLVMF_STK sp0 [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
      [(8, c_fpos cx)] ly4 S4 W4 mem2 md2 (ev + 1) /\
    aregs_preserved regsT regs2 /\ getr regs2 10 = v /\
    (v = YG0d.w64 0 <-> forall i, 0 <= i < n -> aview SEGS (w_H W4) m (x + i) = aview SEGS (w_H W4) m (y + i)) /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - 2 * ESTACK <= a < sp1) -> aview SEGS (w_H W4) mem2 a = aview SEGS (w_H W4) m a))).
{ intros regsT m mdT x y n raw HJm Q10 Q11 Q12 Hn Hx0 Hxn Hy0 Hyn Hspm Qgp Qtp Qra Hraw HSX HSY HMX HMY HRX HHX HRY HHY.
  eapply SRr_mono.
  { eapply (aj_bcmp_at (SK := scene_sink_head) SEGS B LAWS pa_segs_low (SIGMA SS___interceptor_trampoline_bcmp) ABCMP W4 regsT m
      LLVMF_STK sp0 [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(8, c_fpos cx)] ly4 S4 mdT (ev + 1) x y n (sp1 - sp0) raw HJm).
    - exact Q10. - exact Q11. - exact Q12. - exact Hn.
    - lia. - lia. - lia. - lia.
    - rewrite Hspm. lia.
    - exact Hom.
    - lia.
    - rewrite Hes. lia.
    - exact Qgp. - exact Qtp. - exact Qra. - exact Hraw.
    - intros a Ha. split; [replace a with (x + (a - x)) by lia; apply HSX; lia | rewrite Hspm, Hes; lia].
    - intros a Ha. split; [replace a with (y + (a - y)) by lia; apply HSY; lia | rewrite Hspm, Hes; lia].
    - intros a Ha. rewrite Hes. lia.
    - intros a Ha. rewrite Hes. lia.
    - exact HMX. - exact HMY. - exact HRX. - exact HHX. - exact HRY. - exact HHY. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hcmp & Hfr & _).
  split; [reflexivity|]. exists regs2, mem2, md2, v.
  split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|]. split; [exact Hv|]. split; [exact Hcmp|].
  intros a Ha Hout. apply Hfr; [exact Ha | rewrite Hes in *; lia]. }
(* ---- run C: 0x82fd4 .. jal reac_ctrl_scene_set_mac 0x82fe0 ---- *)
pose proof (s5_entry W4 regs5 mem5 1840 sp1 F sF nn R5_9 R5_19 ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) SP5) as HS.
remember (Eimg (Ereg regs5 (s5_extra nn F))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs5 r)
by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HAG5 : env_agree 32 (Ereg regs5 (s5_extra nn F)) E)
by (subst E; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
replace (Z_to_bv 64 (BASE + 1840)) with (Z_to_bv 64 (BASE + 1840)) by reflexivity.
paj_run_shc RUNP RUNC HS HJ5.
{ intros a (r & Hin & Ha).
  lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
  cbn [In] in Hin. destruct Hin as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. lia. }
rename ms into msC, HJ5 into HJC, HFr into HFrC. clear HF HG.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
assert (RKCl : forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 22; 24]%bv -> getr (ms_regs msC) r = getr regs5 r).
{ intros x Hx. exact (regs_kept_of_st_ok SEGS E _ (restrict (w_H W4) msC) regs5 (s5_extra nn F)
  [2; 3; 4; 8; 9; 18; 19; 20; 22; 24]%bv HS HAG5 eq_refl x Hx). }
assert (RKC : s5_rk sp0 sp1 sF body np (ms_regs msC))
by (apply (s5_rk_kept _ _ _ _ _ regs5); [intros r Hr; apply RKCl; cbn in Hr |- *; tauto | exact RK5]).
pose proof RKC as (RC2 & RC3 & RC4 & RC8 & RC9 & RC19 & RC20 & RC24).
assert (KC : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W4) (ms_mem msC) a = aview SEGS (w_H W4) mem5 a).
{ intros a Ha. eapply (aview_kept_frame _ _ _ _ _ 0 HFrC); [lia | | exact Ha].
  intros b Hb (r & Hin & Hrb).
  lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
  cbn [In] in Hin. destruct Hin as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb. lia. }
clear HFrC.
assert (E33 : ew E 33 = Z_to_bv 64 F)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs5 _ 1)).
assert (Ra0' : getr (ms_regs msC) 10%bv = YG0d.w64 body)
by (rewrite Ra0; cbn [sv_denot]; rewrite (EE 20%nat 20%bv eq_refl), R5_20; unfold YG0d.w64;
    rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; first [reflexivity | rewrite unsigned_lit_small by lia; reflexivity]).
assert (Ra1' : getr (ms_regs msC) 11%bv = YG0d.w64 np)
by (rewrite Ra1; cbn [sv_denot]; rewrite (EE 24%nat 24%bv eq_refl), R5_24; unfold YG0d.w64;
    rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; first [reflexivity | rewrite unsigned_lit_small by lia; reflexivity]).
assert (Ra2' : getr (ms_regs msC) 12%bv = YG0d.w64 (F + 112))
by (rewrite Ra2; cbn [sv_denot]; rewrite E33; unfold YG0d.w64; rewrite unsigned_lit_small by lia; reflexivity).
pmkst HS.
assert (HSIG : SIGMA SS_reac_ctrl_scene_set_mac = BASE + AF_reac_ctrl_scene_set_mac) by reflexivity.
rewrite HSIG.
assert (HJCk : forall a, s5_prot sp0 sp1 F sF a -> aview SEGS (w_H W4) (ms_mem msC) a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. rewrite KC by (destruct (PCLS a (or_introl Ha)) as [H|[H|[H|H]]]; lia). exact (KP5 a Ha). }
eapply SRr_bind.
{ eapply (cl_callS (SK := scene_sink_head) B LAWS W4 (ms_regs msC) (ms_mem msC) (Z_to_bv 64 (BASE + AF_reac_ctrl_scene_set_mac))
    LLVMF_STK sp0 [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(8, c_fpos cx)] ly4 S4 _ (ev + 1)
    SET_MAC_STK (setmac_fp body np (F + 112)) 0 (sp1 - sp0) (getr (ms_regs msC) 1) (rt_ch cx) _ HJC).
  - unfold spZ at 1. rewrite RC2, unsigned_lit_small by lia. lia.
  - exact Hom.
  - lia.
  - unfold SET_MAC_STK, SET_MAC_FRAME. rewrite Hes. lia.
  - unfold SET_MAC_STK, SET_MAC_FRAME. rewrite Hes. lia.
  - exact RC3.
  - exact RC4.
  - reflexivity.
  - rewrite Rra. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite Rra, unsigned_lit_small by lia. lia.
  - replace (sp0 + (sp1 - sp0)) with sp1 by lia.
    replace (s0Z (ms_regs msC)) with sp0 by (unfold s0Z; rewrite RC8; symmetry; apply unsigned_lit_small; lia).
    exact (ACH (ms_mem msC) _ (ev + 1) HJC HJCk).
  - intros HPRE1.
    assert (HGO : scene_go body np (F + 112) = true ->
      (exists b m, In (b, m) (ablocks B ly4 S4) /\ b <= body + MAC_OFF /\ body + MAC_OFF + MAC_LEN <= b + req_size m) /\
      ((exists b m, In (b, m) (ablocks B ly4 S4) /\ b <= F + 112 /\ F + 112 + MAC_LEN <= b + req_size m) \/
       afobj SEGS B ly4 S4 W4 (ms_mem msC) (F + 112) MAC_LEN) /\
      (body + MAC_OFF + MAC_LEN <= F + 112 \/ F + 112 + MAC_LEN <= body + MAC_OFF)).
    { intros Hgo. unfold scene_go, SCENE_BYTES in Hgo. apply andb_prop in Hgo as [Hgo _]. apply andb_prop in Hgo as [Hgo _].
      apply Z.eqb_eq in Hgo.
      assert (Hnn8904 : nn = 8904) by (rewrite Enn, Hgo; reflexivity).
      assert (Hfin4 : In (8, c_fpos cx) (frames S4)) by (rewrite Hfrs4; exact Hfin3).
      destruct (al_layout _ _ LAWS _ _ _ _ _ ly4 HAR0 (proj1 (proj2 HJB))) as (_ & EFA4 & _).
      pose proof (sep_block_frame SEGS B LAWS ly4 S4 W4 mem4 md4 body nn 8 (c_fpos cx) HAR4 Hbody4 Hfin4) as Hd.
      rewrite EFA4, HcidF in Hd. change (fs_frame_bytes 8) with 16384 in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
      unfold MAC_OFF, MAC_LEN.
      split; [exists body, nn; split; [exact Hbody4 | rewrite Ereq; lia]|].
      split; [right | lia].
      unfold afobj. split.
      { exists 8, (c_fpos cx). split; [exact Hfin4|]. rewrite EFA4, HcidF. change (fs_frame_bytes 8) with 16384.
        split; [lia|]. split; [|lia].
        destruct (proj1 (Z.mod_divide F 32 ltac:(lia)) HF32) as [q Hq]. rewrite Hq.
        replace (q * 32) with ((4 * q) * 8) by lia. apply Z_mod_mult. }
      split.
      { destruct (proj1 (Z.mod_divide F 32 ltac:(lia)) HF32) as [q Hq]. rewrite Hq.
        replace (q * 32 + 112) with ((4 * q + 14) * 8) by lia. apply Z_mod_mult. }
      apply (block_shadow_range _ SHADOW_OFF (F + 112) 6 (F + 112) 6); [|lia|lia].
      unfold sc_open in HOPMAC. cbn [sg_off_mac sg_mac_n scene_geom_asan_ubsan] in HOPMAC.
      destruct HOPMAC as (Hm & Hn & Hcm). split; [exact Hm|]. split; [exact Hn|].
      intros i Hi. change ((6 + 7) / 8) with 1 in Hi.
      assert (Ea : shadow_of_addr SHADOW_OFF (F + 112) + i = sF + (14 + i))
      by (unfold shadow_of_addr, sF, shadow_addr; replace (F + 112) with (F + 8 * 14) by lia; rewrite HF8g by lia; lia).
      rewrite Ea, HJCk by (unfold s5_prot; lia). rewrite <- Ea. exact (Hcm i Hi). }
    pose proof (SSM ly4 S4 W4 (ms_regs msC) (ms_mem msC) _ (rt_ch cx) body np (F + 112) HPRE1 Ra0' Ra1' Ra2'
      ltac:(lia) ltac:(lia) ltac:(lia) HGO) as CALL.
    unfold cfg_at, treac_ctrl_scene_set_mac_post, apost_base, A_reac_ctrl_scene_set_macP in CALL. exact CALL.
  - intros a Ha. right. unfold setmac_fp in Ha.
    destruct (scene_go body np (F + 112)) eqn:Hgo; [|destruct (inFP_nil a Ha)].
    unfold scene_go, SCENE_BYTES in Hgo. apply andb_prop in Hgo as [Hgo _]. apply andb_prop in Hgo as [Hgo _].
    apply Z.eqb_eq in Hgo.
    destruct Ha as (r & [<- | []] & Hr). cbn [fst snd] in Hr. unfold MAC_OFF, MAC_LEN in Hr.
    exists body, nn. split; [exact Hbody4|]. split; [exact Hbody_new | rewrite Ereq, Enn, Hgo; cbn; lia]. }
cbv beta. intros W6 c6 _ (ly6 & S6 & regs6 & mem6 & md6 & -> & HJ6 & HJ6i & HP6 & (-> & -> & -> & HPerm6 & R6_10 & HSM)).
rewrite Z.add_0_r in HJ6.
pose proof (s5_rk_pres _ _ _ _ _ _ _ HP6 RKC) as RK6.
pose proof RK6 as (R6_2 & R6_3 & R6_4 & R6_8 & R6_9 & R6_19 & R6_20 & R6_24).
assert (R6_22 : getr regs6 22 = Z_to_bv 64 res).
{ transitivity (getr (ms_regs msC) 22%bv); [exact (HP6 22 ltac:(unfold acallee_saved; lia))|].
  rewrite (RKCl 22%bv ltac:(cbn; tauto)). exact R5_22. }
assert (R6_18 : getr regs6 18 = Z_to_bv 64 (if np =? 8904 then 1 else 0)).
{ transitivity (getr (ms_regs msC) 18%bv); [exact (HP6 18 ltac:(unfold acallee_saved; lia))|].
  rewrite (RKCl 18%bv ltac:(cbn; tauto)). exact R5_18. }
assert (Hgo_eq : scene_go body np (F + 112) = (np =? 8904)).
{ unfold scene_go, SCENE_BYTES. destruct (Z.eqb_spec body 0); [lia|]. destruct (Z.eqb_spec (F + 112) 0); [lia|].
  cbn [negb]. rewrite !andb_true_r. reflexivity. }
rewrite Hgo_eq in R6_10, HSM.
rewrite Rra.
assert (Hsp6 : spZ (ms_regs msC) = sp1) by (unfold spZ; rewrite RC2; apply unsigned_lit_small; lia).
rewrite Hsp6 in HSM.
clear HS HE HEI EE HAG5 Ra0 Ra1 Ra2 Rra Ra0' Ra1' Ra2' E33 E.
(* the blocks' bytes are present and addressable at any state of the journal *)
assert (BLK : forall m md k, ajournal (SK := scene_sink_head) SEGS B LLVMF_STK sp0 [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(8, c_fpos cx)] ly4 S4 W4 m md k -> forall b, In (b, nn) (ablocks B ly4 S4) -> forall x n, b <= x -> x + n <= b + nn -> 0 <= n ->
  (forall i, 0 <= i < n -> aview SEGS (w_H W4) m (x + i) <> None) /\ amem_range x n /\
  range_addressable (aview SEGS (w_H W4) m) SHADOW_OFF x n /\ (0 < n -> shadow_hull_vis (aview SEGS (w_H W4) m) x n)).
{ intros m md k HJm b Hb x n Hx Hxn Hn. pose proof (proj1 HJm) as HARm.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b nn HARm Hb) as (_ & _ & _ & _ & Hbp & _).
  split; [intros i Hi; apply (aview_some_of_apresent SEGS); apply (proj1 (Hbp (x + i) ltac:(rewrite Ereq; lia)))|].
  split; [eapply (amem_range_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ HARm Hb); rewrite ?Ereq; lia|].
  split; [eapply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ HARm Hb); rewrite ?Ereq; lia|].
  intros Hnz. eapply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ HARm Hb); rewrite ?Ereq; lia. }
(* body and before lie outside the fake frame *)
assert (Hfin4 : In (8, c_fpos cx) (frames S4)) by (rewrite Hfrs4; exact Hfin3).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly4 HAR0 (proj1 (proj2 HJB))) as (_ & EFA4 & _).
assert (HBF : body + nn <= F \/ F + 16384 <= body).
{ pose proof (sep_block_frame SEGS B LAWS ly4 S4 W4 mem4 md4 body nn 8 (c_fpos cx) HAR4 Hbody4 Hfin4) as Hd.
  rewrite EFA4, HcidF in Hd. change (fs_frame_bytes 8) with 16384 in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
  rewrite Ereq in Hd. exact Hd. }
assert (HRF : res + nn <= F \/ F + 16384 <= res).
{ pose proof (sep_block_frame SEGS B LAWS ly4 S4 W4 mem4 md4 res nn 8 (c_fpos cx) HAR4 Hin4 Hfin4) as Hd.
  rewrite EFA4, HcidF in Hd. change (fs_frame_bytes 8) with 16384 in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
  rewrite Ereq in Hd. exact Hd. }
(* the spill words follow from the protected bytes *)
assert (SPOK : forall m, (forall a, s5_prot sp0 sp1 F sF a -> aview SEGS (w_H W4) m a = aview SEGS (w_H W3) mem3 a) ->
  s5_spills_at W4 m sp1 F sF nn)
by (intros m Hm; apply (s5_spills_kept W3 W4 mem3); [intros a Ha; apply Hm; unfold s5_prot; lia | exact SP3]).
destruct (Z.eq_dec np 8904) as [Hgo | Hngo].
2:{
(* ==== the r <> 0 arm (n' <> 8904): set_mac refused and wrote only its own frame ==== *)
assert (Hnpb : (np =? 8904) = false) by (apply Z.eqb_neq; exact Hngo).
rewrite Hnpb in R6_10, R6_18, HSM.
assert (K6 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - 16 <= a < sp1) ->
  aview SEGS (w_H W4) mem6 a = aview SEGS (w_H W4) (ms_mem msC) a).
{ intros a Ha Hn. apply (aview_eq_of SEGS). unfold mrestrict. rewrite (HSM (Z_to_bv 64 a)); [reflexivity|].
  rewrite unsigned_lit_small by lia. unfold SET_MAC_FRAME. exact Hn. }
assert (KP6 : forall a, s5_prot sp0 sp1 F sF a -> aview SEGS (w_H W4) mem6 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. pose proof (PCLS a (or_introl Ha)) as HC.
  rewrite K6 by (destruct HC as [H|[H|[H|H]]]; lia). exact (HJCk a Ha). }
assert (KR6 : forall a, s5_row sF a -> aview SEGS (w_H W4) mem6 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. pose proof (PCLS a (or_intror Ha)) as HC.
  rewrite K6 by (destruct HC as [H|[H|[H|H]]]; lia). rewrite KC by (destruct HC as [H|[H|[H|H]]]; lia). exact (KR5 a Ha). }
assert (BODY6 : forall i, 0 <= i < nn -> aview SEGS (w_H W4) mem6 (body + i) = aview SEGS (w_H W3) mem3 (body + i)).
{ intros i Hi. rewrite K6 by lia. rewrite KC by lia. exact (BODY5 i Hi). }
assert (BEF6 : forall i, 0 <= i < np -> aview SEGS (w_H W4) mem6 (res + i) = aview SEGS (w_H W3) mem3 (body + i)).
{ intros i Hi. rewrite K6 by lia. rewrite KC by lia. exact (BEF5 i Hi). }
assert (SP6 : s5_spills_at W4 mem6 sp1 F sF nn).
{ apply (s5_spills_kept W3 W4 mem3); [|exact SP3]. intros a Ha. apply KP6. unfold s5_prot. lia. }
pose proof (s5_entry W4 regs6 mem6 1856 sp1 F sF nn R6_9 R6_19 ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) SP6) as HS.
remember (Eimg (Ereg regs6 (s5_extra nn F))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs6 r)
by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HAG6 : env_agree 32 (Ereg regs6 (s5_extra nn F)) E)
by (subst E; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
pin HS (18%bv : bv 5) (SLit 0) R6_18. pin HS (10%bv : bv 5) (SLit (-1)) R6_10.
paj_run_shc RUNP RUNC HS HJ6.
{ intros a (r & Hin & Ha).
  lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
  cbn [In] in Hin. destruct Hin as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. lia. }
rename ms into msD, HJ6 into HJD, HFr into HFrD. clear HF HG.
prreg HS (10%bv : bv 5) Da0. prreg HS (11%bv : bv 5) Da1. prreg HS (12%bv : bv 5) Da2. prreg HS (1%bv : bv 5) Dra.
prreg HS (23%bv : bv 5) Ds7.
assert (RKDl : forall r, In r [2; 3; 4; 8; 9; 19; 20; 22; 24]%bv -> getr (ms_regs msD) r = getr regs6 r).
{ intros x Hx. exact (regs_kept_of_st_ok SEGS E _ (restrict (w_H W4) msD) regs6 (s5_extra nn F)
  [2; 3; 4; 8; 9; 19; 20; 22; 24]%bv HS HAG6 eq_refl x Hx). }
assert (RKD : s5_rk sp0 sp1 sF body np (ms_regs msD))
by (apply (s5_rk_kept _ _ _ _ _ regs6); [intros r Hr; apply RKDl; cbn in Hr |- *; tauto | exact RK6]).
pose proof RKD as (RD2 & RD3 & RD4 & RD8 & RD9 & RD19 & RD20 & RD24).
assert (RD22 : getr (ms_regs msD) 22%bv = Z_to_bv 64 res) by (rewrite (RKDl 22%bv ltac:(cbn; tauto)); exact R6_22).
assert (KD : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W4) (ms_mem msD) a = aview SEGS (w_H W4) mem6 a).
{ intros a Ha. eapply (aview_kept_frame _ _ _ _ _ 0 HFrD); [lia | | exact Ha].
  intros b Hb (r & Hin & Hrb).
  lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
  cbn [In] in Hin. destruct Hin as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb. lia. }
clear HFrD.
assert (Da0' : getr (ms_regs msD) 10%bv = YG0d.w64 body)
by (rewrite Da0; cbn [sv_denot]; rewrite (EE 20%nat 20%bv eq_refl), R6_20; unfold YG0d.w64;
    rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; first [reflexivity | rewrite unsigned_lit_small by lia; reflexivity]).
assert (Da1' : getr (ms_regs msD) 11%bv = YG0d.w64 res)
by (rewrite Da1; cbn [sv_denot]; rewrite (EE 22%nat 22%bv eq_refl), R6_22; unfold YG0d.w64;
    rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; first [reflexivity | rewrite unsigned_lit_small by lia; reflexivity]).
assert (Da2' : getr (ms_regs msD) 12%bv = YG0d.w64 np)
by (rewrite Da2; cbn [sv_denot]; rewrite (EE 24%nat 24%bv eq_refl), R6_24; unfold YG0d.w64;
    rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; first [reflexivity | rewrite unsigned_lit_small by lia; reflexivity]).
assert (Ds7' : getr (ms_regs msD) 23%bv = Z_to_bv 64 18446744073709551615) by (rewrite Ds7; reflexivity).
pmkst HS.
clear HS HE HEI EE HAG6 Da0 Da1 Da2 Ds7 E.
eapply SRr_bind.
{ destruct (BLK _ _ _ HJD body Hbody4 body np ltac:(lia) ltac:(lia) ltac:(lia)) as (BX1 & BX2 & BX3 & BX4).
  destruct (BLK _ _ _ HJD res Hin4 res np ltac:(lia) ltac:(lia) ltac:(lia)) as (BY1 & BY2 & BY3 & BY4).
  eapply (BCMP (ms_regs msD) (ms_mem msD) _ body res np (Z_to_bv 64 (BASE + 1888)) HJD Da0' Da1' Da2');
  [lia | lia | lia | lia | lia | unfold spZ; rewrite RD2; apply unsigned_lit_small; lia | exact RD3 | exact RD4 | exact Dra
  | apply ret_ok_codeptr_v; [lia | reflexivity] | exact BX1 | exact BY1 | exact BX2 | exact BY2 | exact BX3 | exact BX4
  | exact BY3 | exact BY4]. }
cbv beta. intros W7 c7 _ (-> & regs7 & mem7 & md7 & v7 & -> & HJ7 & HP7 & R7_10 & Hcmp7 & K7).
assert (Hv7 : v7 = YG0d.w64 0).
{ apply (proj2 Hcmp7). intros i Hi. rewrite !KD by lia. rewrite (BODY6 i ltac:(lia)), (BEF6 i Hi). reflexivity. }
rewrite Hv7 in R7_10. clear Hv7 Hcmp7.
pose proof (s5_rk_pres _ _ _ _ _ _ _ HP7 RKD) as RK7.
pose proof RK7 as (R7_2 & R7_3 & R7_4 & R7_8 & R7_9 & R7_19 & R7_20 & R7_24).
assert (R7_22 : getr regs7 22 = Z_to_bv 64 res)
by (transitivity (getr (ms_regs msD) 22%bv); [exact (HP7 22 ltac:(unfold acallee_saved; lia)) | exact RD22]).
assert (R7_23 : getr regs7 23 = Z_to_bv 64 18446744073709551615)
by (transitivity (getr (ms_regs msD) 23%bv); [exact (HP7 23 ltac:(unfold acallee_saved; lia)) | exact Ds7']).
assert (KM7 : forall a, s5_prot sp0 sp1 F sF a \/ s5_row sF a -> aview SEGS (w_H W4) mem7 a = aview SEGS (w_H W4) mem6 a).
{ intros a Ha. pose proof (PCLS a Ha) as HC. pose proof (PW a Ha) as HW.
  rewrite K7 by (try (destruct HC as [H|[H|[H|H]]]; lia); rewrite Hes, <- Has; exact HW). apply KD.
  destruct HC as [H|[H|[H|H]]]; lia. }
assert (BODY7 : forall i, 0 <= i < nn -> aview SEGS (w_H W4) mem7 (body + i) = aview SEGS (w_H W3) mem3 (body + i)).
{ intros i Hi. rewrite K7 by (rewrite ?Hes; lia). rewrite KD by lia. exact (BODY6 i Hi). }
assert (BEF7 : forall i, 0 <= i < np -> aview SEGS (w_H W4) mem7 (res + i) = aview SEGS (w_H W3) mem3 (body + i)).
{ intros i Hi. rewrite K7 by (rewrite ?Hes; lia). rewrite KD by lia. exact (BEF6 i Hi). }
assert (KP7 : forall a, s5_prot sp0 sp1 F sF a -> aview SEGS (w_H W4) mem7 a = aview SEGS (w_H W3) mem3 a)
by (intros a Ha; rewrite (KM7 a (or_introl Ha)); exact (KP6 a Ha)).
assert (KR7 : forall a, s5_row sF a -> aview SEGS (w_H W4) mem7 a = aview SEGS (w_H W3) mem3 a)
by (intros a Ha; rewrite (KM7 a (or_intror Ha)); exact (KR6 a Ha)).
assert (SP7 : s5_spills_at W4 mem7 sp1 F sF nn).
{ apply (s5_spills_kept W3 W4 mem3); [|exact SP3]. intros a Ha. apply KP7. unfold s5_prot. lia. }
(* ---- 0x83004 `bnez a0` (a0 = 0), the arguments, jal reac_ctrl_scene_build 0x83014 ---- *)
pose proof (s5_entry W4 regs7 mem7 1888 sp1 F sF nn R7_9 R7_19 ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) SP7) as HS.
remember (Eimg (Ereg regs7 (s5_extra nn F))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs7 r)
by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HAG7 : env_agree 32 (Ereg regs7 (s5_extra nn F)) E)
by (subst E; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (R7_10' : getr regs7 10%bv = Z_to_bv 64 0) by (rewrite R7_10; reflexivity).
pin HS (10%bv : bv 5) (SLit 0) R7_10'.
paj_run_shc RUNP RUNC HS HJ7.
{ intros a (r & Hin & Ha).
  lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
  cbn [In] in Hin. destruct Hin as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. lia. }
rename ms into msE, HJ7 into HJE, HFr into HFrE. clear HF HG.
prreg HS (10%bv : bv 5) Ea0. prreg HS (11%bv : bv 5) Ea1. prreg HS (12%bv : bv 5) Ea2. prreg HS (1%bv : bv 5) Era.
assert (RKEl : forall r, In r [2; 3; 4; 8; 9; 19; 20; 22; 23; 24]%bv -> getr (ms_regs msE) r = getr regs7 r).
{ intros x Hx. exact (regs_kept_of_st_ok SEGS E _ (restrict (w_H W4) msE) regs7 (s5_extra nn F)
  [2; 3; 4; 8; 9; 19; 20; 22; 23; 24]%bv HS HAG7 eq_refl x Hx). }
assert (RKE : s5_rk sp0 sp1 sF body np (ms_regs msE))
by (apply (s5_rk_kept _ _ _ _ _ regs7); [intros r Hr; apply RKEl; cbn in Hr |- *; tauto | exact RK7]).
pose proof RKE as (RE2 & RE3 & RE4 & RE8 & RE9 & RE19 & RE20 & RE24).
assert (KE : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W4) (ms_mem msE) a = aview SEGS (w_H W4) mem7 a).
{ intros a Ha. eapply (aview_kept_frame _ _ _ _ _ 0 HFrE); [lia | | exact Ha].
  intros b0 Hb0 (r & Hin & Hrb).
  lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
  cbn [In] in Hin. destruct Hin as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb. lia. }
clear HFrE.
assert (E33 : ew E 33 = Z_to_bv 64 F)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs7 _ 1)).
assert (Ea0' : getr (ms_regs msE) 10%bv = YG0d.w64 body)
by (rewrite Ea0; cbn [sv_denot]; rewrite (EE 20%nat 20%bv eq_refl), R7_20; unfold YG0d.w64;
    rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; first [reflexivity | rewrite unsigned_lit_small by lia; reflexivity]).
assert (Ea1' : getr (ms_regs msE) 11%bv = YG0d.w64 np)
by (rewrite Ea1; cbn [sv_denot]; rewrite (EE 24%nat 24%bv eq_refl), R7_24; unfold YG0d.w64;
    rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; first [reflexivity | rewrite unsigned_lit_small by lia; reflexivity]).
assert (Ea2' : getr (ms_regs msE) 12%bv = YG0d.w64 (F + 112))
by (rewrite Ea2; cbn [sv_denot]; rewrite E33; unfold YG0d.w64; rewrite unsigned_lit_small by lia; reflexivity).
assert (RE22 : getr (ms_regs msE) 22%bv = Z_to_bv 64 res) by (rewrite (RKEl 22%bv ltac:(cbn; tauto)); exact R7_22).
assert (RE23 : getr (ms_regs msE) 23%bv = Z_to_bv 64 18446744073709551615) by (rewrite (RKEl 23%bv ltac:(cbn; tauto)); exact R7_23).
pmkst HS.
clear HS HE HEI EE HAG7 Ea0 Ea1 Ea2 E33 E.
assert (HSIGB : SIGMA SS_reac_ctrl_scene_build = BASE + AF_reac_ctrl_scene_build) by reflexivity.
rewrite HSIGB.
assert (KPE : forall a, s5_prot sp0 sp1 F sF a -> aview SEGS (w_H W4) (ms_mem msE) a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. rewrite KE by (destruct (PCLS a (or_introl Ha)) as [H|[H|[H|H]]]; lia). exact (KP7 a Ha). }
assert (Hokb : scene_okb body np (F + 112) = false).
{ unfold scene_okb. replace (np =? P_reac_ctrl_scene_build.SCENE_BYTES) with false
  by (symmetry; apply Z.eqb_neq; unfold P_reac_ctrl_scene_build.SCENE_BYTES; exact Hngo). reflexivity. }
eapply SRr_bind.
{ eapply (cl_callS (SK := scene_sink_head) B LAWS W4 (ms_regs msE) (ms_mem msE) (Z_to_bv 64 (BASE + AF_reac_ctrl_scene_build))
    LLVMF_STK sp0 [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(8, c_fpos cx)] ly4 S4 _ (ev + 1)
    REAC_CTRL_SCENE_BUILD_STK (scene_fp body np (F + 112)) 0 (sp1 - sp0) (getr (ms_regs msE) 1) (rt_ch cx) _ HJE).
  - unfold spZ at 1. rewrite RE2, unsigned_lit_small by lia. lia.
  - exact Hom.
  - lia.
  - unfold REAC_CTRL_SCENE_BUILD_STK. rewrite Hes. lia.
  - unfold REAC_CTRL_SCENE_BUILD_STK. rewrite Hes. lia.
  - exact RE3.
  - exact RE4.
  - reflexivity.
  - rewrite Era. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite Era, unsigned_lit_small by lia. lia.
  - replace (sp0 + (sp1 - sp0)) with sp1 by lia.
    replace (s0Z (ms_regs msE)) with sp0 by (unfold s0Z; rewrite RE8; symmetry; apply unsigned_lit_small; lia).
    exact (ACH (ms_mem msE) _ (ev + 1) HJE KPE).
  - intros HPRE1.
    assert (HOK : scene_okb body np (F + 112) = true ->
      In (body, SCENE_BYTES) (ablocks B ly4 S4) /\ afobj SEGS B ly4 S4 W4 (ms_mem msE) (F + 112) SCENE_MAC_LEN)
    by (rewrite Hokb; discriminate).
    pose proof (SSB ly4 S4 W4 (ms_regs msE) (ms_mem msE) _ (rt_ch cx) body np (F + 112) HPRE1 Ea0' Ea1' Ea2'
      ltac:(lia) ltac:(lia) ltac:(lia) HOK) as CALL.
    unfold cfg_at, treac_ctrl_scene_build_post, apost_base, A_reac_ctrl_scene_buildP in CALL. exact CALL.
  - intros a Ha. unfold scene_fp in Ha. rewrite Hokb in Ha. destruct (inFP_nil a Ha). }
cbv beta. intros W8 c8 _ (ly8 & S8 & regs8 & mem8 & md8 & -> & HJ8 & HJ8i & HP8 & (-> & -> & -> & HSC)).
rewrite Hokb in HSC. destruct HSC as (R8_10 & K8). rewrite Z.add_0_r in HJ8. rewrite Era.
pose proof (s5_rk_pres _ _ _ _ _ _ _ HP8 RKE) as RK8.
pose proof RK8 as (R8_2 & R8_3 & R8_4 & R8_8 & R8_9 & R8_19 & R8_20 & R8_24).
assert (R8_22 : getr regs8 22 = Z_to_bv 64 res)
by (transitivity (getr (ms_regs msE) 22%bv); [exact (HP8 22 ltac:(unfold acallee_saved; lia)) | exact RE22]).
assert (R8_23 : getr regs8 23 = Z_to_bv 64 18446744073709551615)
by (transitivity (getr (ms_regs msE) 23%bv); [exact (HP8 23 ltac:(unfold acallee_saved; lia)) | exact RE23]).
assert (Hspe : spZ (ms_regs msE) = sp1) by (unfold spZ; rewrite RE2; apply unsigned_lit_small; lia).
rewrite Hspe in K8.
assert (KM8 : forall a, s5_prot sp0 sp1 F sF a \/ s5_row sF a -> aview SEGS (w_H W4) mem8 a = aview SEGS (w_H W4) mem7 a).
{ intros a Ha. pose proof (PCLS a Ha) as HC. pose proof (PW a Ha) as HW.
  rewrite K8 by (try (destruct HC as [H|[H|[H|H]]]; lia); rewrite Has in HW; lia). apply KE.
  destruct HC as [H|[H|[H|H]]]; lia. }
assert (BODY8 : forall i, 0 <= i < nn -> aview SEGS (w_H W4) mem8 (body + i) = aview SEGS (w_H W3) mem3 (body + i)).
{ intros i Hi. rewrite K8 by lia. rewrite KE by lia. exact (BODY7 i Hi). }
assert (BEF8 : forall i, 0 <= i < np -> aview SEGS (w_H W4) mem8 (res + i) = aview SEGS (w_H W3) mem3 (body + i)).
{ intros i Hi. rewrite K8 by lia. rewrite KE by lia. exact (BEF7 i Hi). }
assert (KP8 : forall a, s5_prot sp0 sp1 F sF a -> aview SEGS (w_H W4) mem8 a = aview SEGS (w_H W3) mem3 a)
by (intros a Ha; rewrite (KM8 a (or_introl Ha)); exact (KP7 a Ha)).
assert (KR8 : forall a, s5_row sF a -> aview SEGS (w_H W4) mem8 a = aview SEGS (w_H W3) mem3 a)
by (intros a Ha; rewrite (KM8 a (or_intror Ha)); exact (KR7 a Ha)).
assert (SP8 : s5_spills_at W4 mem8 sp1 F sF nn).
{ apply (s5_spills_kept W3 W4 mem3); [|exact SP3]. intros a Ha. apply KP8. unfold s5_prot. lia. }
(* ---- 0x83018 `bne a0,s7` (both -1), then jal __wrap_bcmp 0x83028 ---- *)
pose proof (s5_entry W4 regs8 mem8 1908 sp1 F sF nn R8_9 R8_19 ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) SP8) as HS.
remember (Eimg (Ereg regs8 (s5_extra nn F))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs8 r)
by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HAG8 : env_agree 32 (Ereg regs8 (s5_extra nn F)) E)
by (subst E; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (R8_10' : getr regs8 10%bv = Z_to_bv 64 18446744073709551615)
by (rewrite R8_10; unfold YG0d.w64; apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity).
pin HS (10%bv : bv 5) (SLit 18446744073709551615) R8_10'.
pin HS (23%bv : bv 5) (SLit 18446744073709551615) R8_23.
paj_run_shc RUNP RUNC HS HJ8.
{ intros a (r & Hin & Ha).
  lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
  cbn [In] in Hin. destruct Hin as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. lia. }
rename ms into msF, HJ8 into HJF, HFr into HFrF. clear HF HG.
prreg HS (10%bv : bv 5) Fa0. prreg HS (11%bv : bv 5) Fa1. prreg HS (12%bv : bv 5) Fa2. prreg HS (1%bv : bv 5) Fra.
assert (RKFl : forall r, In r [2; 3; 4; 8; 9; 19; 20; 22; 24]%bv -> getr (ms_regs msF) r = getr regs8 r).
{ intros x Hx. exact (regs_kept_of_st_ok SEGS E _ (restrict (w_H W4) msF) regs8 (s5_extra nn F)
  [2; 3; 4; 8; 9; 19; 20; 22; 24]%bv HS HAG8 eq_refl x Hx). }
assert (RKF : s5_rk sp0 sp1 sF body np (ms_regs msF))
by (apply (s5_rk_kept _ _ _ _ _ regs8); [intros r Hr; apply RKFl; cbn in Hr |- *; tauto | exact RK8]).
pose proof RKF as (RF2 & RF3 & RF4 & RF8 & RF9 & RF19 & RF20 & RF24).
assert (RF22 : getr (ms_regs msF) 22%bv = Z_to_bv 64 res) by (rewrite (RKFl 22%bv ltac:(cbn; tauto)); exact R8_22).
assert (KF : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W4) (ms_mem msF) a = aview SEGS (w_H W4) mem8 a).
{ intros a Ha. eapply (aview_kept_frame _ _ _ _ _ 0 HFrF); [lia | | exact Ha].
  intros b0 Hb0 (r & Hin & Hrb).
  lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
  cbn [In] in Hin. destruct Hin as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb. lia. }
clear HFrF.
assert (Fa0' : getr (ms_regs msF) 10%bv = YG0d.w64 body)
by (rewrite Fa0; cbn [sv_denot]; rewrite (EE 20%nat 20%bv eq_refl), R8_20; unfold YG0d.w64;
    rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; first [reflexivity | rewrite unsigned_lit_small by lia; reflexivity]).
assert (Fa1' : getr (ms_regs msF) 11%bv = YG0d.w64 res)
by (rewrite Fa1; cbn [sv_denot]; rewrite (EE 22%nat 22%bv eq_refl), R8_22; unfold YG0d.w64;
    rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; first [reflexivity | rewrite unsigned_lit_small by lia; reflexivity]).
assert (Fa2' : getr (ms_regs msF) 12%bv = YG0d.w64 np)
by (rewrite Fa2; cbn [sv_denot]; rewrite (EE 24%nat 24%bv eq_refl), R8_24; unfold YG0d.w64;
    rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; first [reflexivity | rewrite unsigned_lit_small by lia; reflexivity]).
pmkst HS.
clear HS HE HEI EE HAG8 Fa0 Fa1 Fa2 E.
eapply SRr_bind.
{ destruct (BLK _ _ _ HJF body Hbody4 body np ltac:(lia) ltac:(lia) ltac:(lia)) as (CX1 & CX2 & CX3 & CX4).
  destruct (BLK _ _ _ HJF res Hin4 res np ltac:(lia) ltac:(lia) ltac:(lia)) as (CY1 & CY2 & CY3 & CY4).
  eapply (BCMP (ms_regs msF) (ms_mem msF) _ body res np (Z_to_bv 64 (BASE + 1928)) HJF Fa0' Fa1' Fa2');
  [lia | lia | lia | lia | lia | unfold spZ; rewrite RF2; apply unsigned_lit_small; lia | exact RF3 | exact RF4 | exact Fra
  | apply ret_ok_codeptr_v; [lia | reflexivity] | exact CX1 | exact CY1 | exact CX2 | exact CY2 | exact CX3 | exact CX4
  | exact CY3 | exact CY4]. }
cbv beta. intros W9 c9 _ (-> & regs9 & mem9 & md9 & v9 & -> & HJ9 & HP9 & R9_10 & Hcmp9 & K9).
assert (Hv9 : v9 = YG0d.w64 0).
{ apply (proj2 Hcmp9). intros i Hi. rewrite !KF by lia. rewrite (BODY8 i ltac:(lia)), (BEF8 i Hi). reflexivity. }
rewrite Hv9 in R9_10. clear Hv9 Hcmp9.
pose proof (s5_rk_pres _ _ _ _ _ _ _ HP9 RKF) as RK9.
pose proof RK9 as (R9_2 & R9_3 & R9_4 & R9_8 & R9_9 & R9_19 & R9_20 & R9_24).
assert (R9_22 : getr regs9 22 = Z_to_bv 64 res)
by (transitivity (getr (ms_regs msF) 22%bv); [exact (HP9 22 ltac:(unfold acallee_saved; lia)) | exact RF22]).
assert (KM9 : forall a, s5_prot sp0 sp1 F sF a \/ s5_row sF a -> aview SEGS (w_H W4) mem9 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. pose proof (PCLS a Ha) as HC. pose proof (PW a Ha) as HW.
  rewrite K9 by (try (destruct HC as [H|[H|[H|H]]]; lia); rewrite Hes, <- Has; exact HW).
  rewrite KF by (destruct HC as [H|[H|[H|H]]]; lia).
  destruct Ha as [Ha | Ha]; [exact (KP8 a Ha) | exact (KR8 a Ha)]. }
(* ---- 0x8302c `beqz a0` (a0 = 0) -> C6 ---- *)
remember (Eimg (Ereg regs9 [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAG9 : env_agree 32 (Ereg regs9 []) E)
by (subst E; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (R9_10' : getr regs9 10%bv = Z_to_bv 64 0) by (rewrite R9_10; reflexivity).
assert (HS : st_ok_pi SEGS VAL E (mkSS 1928 (sr_set sr_atoms 10%bv (SLit 0)) [] None (mkFacts [] [] []))
  (restrict (w_H W4) (mkst regs9 (Z_to_bv 64 (BASE + 1928)) mem9 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx.
  apply (ast_ok_pi_set_reg_fp E (mkSS 1928 sr_atoms [] None (mkFacts [] [] [])) _ 10%bv (SLit 0));
    [| reflexivity | cbn [sv_denot ms_regs mkst]; rewrite R9_10'; reflexivity].
  apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - reflexivity.
  - constructor.
  - exact I.
  - split; [exact I | split; exact I]. }
paj_run_to_shc RUNTOP HS HJ9 (AF_LLVMFuzzerTestOneInput + SEG_C6_off). { apply awr_ok_nil. }
lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?msx) |- _ => rename msx into msG end.
assert (KG : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W4) (ms_mem msG) a = aview SEGS (w_H W4) mem9 a).
{ intros a Ha. lazymatch goal with HFx : frame_of _ _ (mrestrict _ mem9) (mrestrict _ (ms_mem msG)) |- _ =>
    eapply (aview_kept_frame _ _ _ _ _ 0 HFx); [lia | | exact Ha] end.
  intros b0 Hb0 (r & Hin & Hrb). destruct Hin. }
assert (RKG : s5_rk sp0 sp1 sF body np (ms_regs msG)).
{ apply (s5_rk_kept _ _ _ _ _ regs9); [|exact RK9]. intros x Hx.
  exact (regs_kept_of_st_ok SEGS E _ (restrict (w_H W4) msG) regs9 [] [2; 3; 4; 8; 9; 19; 20; 24]%bv HS HAG9 eq_refl x Hx). }
assert (RG22 : getr (ms_regs msG) 22%bv = Z_to_bv 64 res).
{ transitivity (getr regs9 22%bv); [|exact R9_22].
  exact (regs_kept_of_st_ok SEGS E _ (restrict (w_H W4) msG) regs9 [] [22]%bv HS HAG9 eq_refl 22%bv ltac:(cbn; tauto)). }
pmkst HS.
lazymatch goal with HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem msG) ?mdx _ |- _ =>
  apply (EXIT (ms_regs msG) (ms_mem msG) mdx HJx) end.
- intros a Ha. rewrite KG by (destruct (PCLS a (or_introl Ha)) as [H|[H|[H|H]]]; lia). exact (KM9 a (or_introl Ha)).
- intros a Ha. rewrite KG by (destruct (PCLS a (or_intror Ha)) as [H|[H|[H|H]]]; lia). exact (KM9 a (or_intror Ha)).
- exact RKG.
- exact RG22. }
(* ==== the r = 0 arm (n' = 8904): set_mac wrote the 6 mac bytes at body + 832 ==== *)
assert (Hnpt : (np =? 8904) = true) by (apply Z.eqb_eq; exact Hgo).
rewrite Hnpt in R6_10, R6_18, HSM.
unfold MAC_OFF, MAC_LEN in HSM.
destruct HSM as (MAC6 & K6g).
assert (Hnn8904 : nn = 8904) by (rewrite Enn, Hgo; reflexivity).
(* one transport of the r = 0 arm's four memory facts across a step that keeps every byte outside the `expect`
   object and the callee stack window *)
assert (TP : forall (m m' : word -> option byte),
  (forall a, 0 <= a < 2 ^ 64 -> ~ (F + 224 <= a < F + 9128) -> ~ (sp1 - ASTACK <= a < sp1) ->
     aview SEGS (w_H W4) m' a = aview SEGS (w_H W4) m a) ->
  ((forall a, s5_prot sp0 sp1 F sF a -> aview SEGS (w_H W4) m a = aview SEGS (w_H W3) mem3 a) /\
   (forall i, 0 <= i < nn -> ~ (832 <= i < 838) -> aview SEGS (w_H W4) m (body + i) = aview SEGS (w_H W3) mem3 (body + i)) /\
   (forall j, 0 <= j < 6 -> aview SEGS (w_H W4) m (body + 832 + j) = aview SEGS (w_H W3) mem3 (F + 112 + j)) /\
   (forall i, 0 <= i < np -> aview SEGS (w_H W4) m (res + i) = aview SEGS (w_H W3) mem3 (body + i))) ->
  ((forall a, s5_prot sp0 sp1 F sF a -> aview SEGS (w_H W4) m' a = aview SEGS (w_H W3) mem3 a) /\
   (forall i, 0 <= i < nn -> ~ (832 <= i < 838) -> aview SEGS (w_H W4) m' (body + i) = aview SEGS (w_H W3) mem3 (body + i)) /\
   (forall j, 0 <= j < 6 -> aview SEGS (w_H W4) m' (body + 832 + j) = aview SEGS (w_H W3) mem3 (F + 112 + j)) /\
   (forall i, 0 <= i < np -> aview SEGS (w_H W4) m' (res + i) = aview SEGS (w_H W3) mem3 (body + i)))).
{ intros m m' Hk (H1 & H2 & H3 & H4).
  split.
  { intros a Ha. rewrite Hk; [exact (H1 a Ha) | | | ].
    - destruct (PCLS a (or_introl Ha)) as [H|[H|[H|H]]]; lia.
    - exact (PE a (or_introl Ha)).
    - intros Hw. apply (PW a (or_introl Ha)). rewrite Has. lia. }
  split; [intros i Hi Hni; rewrite Hk by lia; exact (H2 i Hi Hni)|].
  split; [intros j Hj; rewrite Hk by lia; exact (H3 j Hj) | intros i Hi; rewrite Hk by lia; exact (H4 i Hi)]. }
assert (K6 : forall a, s5_prot sp0 sp1 F sF a \/ s5_row sF a -> aview SEGS (w_H W4) mem6 a = aview SEGS (w_H W4) (ms_mem msC) a).
{ intros a Ha. pose proof (PCLS a Ha) as HC. apply K6g.
  - destruct HC as [H|[H|[H|H]]]; lia.
  - intros Hr. apply (PH a body nn Hbody4 Ha). rewrite Ereq. lia.
  - intros Hw. apply (PW a Ha). unfold SET_MAC_STK, SET_MAC_FRAME in Hw. rewrite Has. rewrite Hes in Hw. lia. }
assert (KP6 : forall a, s5_prot sp0 sp1 F sF a -> aview SEGS (w_H W4) mem6 a = aview SEGS (w_H W3) mem3 a)
by (intros a Ha; rewrite (K6 a (or_introl Ha)); exact (HJCk a Ha)).
assert (KR6 : forall a, s5_row sF a -> aview SEGS (w_H W4) mem6 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. rewrite (K6 a (or_intror Ha)).
  rewrite KC by (destruct (PCLS a (or_intror Ha)) as [H|[H|[H|H]]]; lia). exact (KR5 a Ha). }
assert (BODY6 : forall i, 0 <= i < nn -> ~ (832 <= i < 838) ->
  aview SEGS (w_H W4) mem6 (body + i) = aview SEGS (w_H W3) mem3 (body + i)).
{ intros i Hi Hni. rewrite K6g by (unfold SET_MAC_STK, SET_MAC_FRAME; rewrite ?Hes; lia).
  rewrite KC by lia. exact (BODY5 i Hi). }
assert (MACB6 : forall j, 0 <= j < 6 -> aview SEGS (w_H W4) mem6 (body + 832 + j) = aview SEGS (w_H W3) mem3 (F + 112 + j)).
{ intros j Hj. rewrite (MAC6 j Hj). apply HJCk. unfold s5_prot. lia. }
assert (BEF6 : forall i, 0 <= i < np -> aview SEGS (w_H W4) mem6 (res + i) = aview SEGS (w_H W3) mem3 (body + i)).
{ intros i Hi. rewrite K6g by (unfold SET_MAC_STK, SET_MAC_FRAME; rewrite ?Hes; lia).
  rewrite KC by lia. exact (BEF5 i Hi). }
assert (SP6 : s5_spills_at W4 mem6 sp1 F sF nn).
{ apply (s5_spills_kept W3 W4 mem3); [|exact SP3]. intros a Ha. apply KP6. unfold s5_prot. lia. }
(* ---- 0x82fe4 .. the UBSan guard 0x83038 and jal __wrap_bcmp 0x8304c ---- *)
pose proof (s5_entry W4 regs6 mem6 1856 sp1 F sF nn R6_9 R6_19 ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) SP6) as HS.
remember (Eimg (Ereg regs6 (s5_extra nn F))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs6 r)
by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HAG6 : env_agree 32 (Ereg regs6 (s5_extra nn F)) E)
by (subst E; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E20 : ew E 20 = Z_to_bv 64 body) by (rewrite (EE 20%nat 20%bv eq_refl); exact R6_20).
assert (E22 : ew E 22 = Z_to_bv 64 res) by (rewrite (EE 22%nat 22%bv eq_refl); exact R6_22).
assert (F20 : afact_ok E 20 (mkAF 4096 (2 ^ 47) 0))
by (unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E20, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia).
assert (F22 : afact_ok E 22 (mkAF 4096 (2 ^ 47) 0))
by (unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E22, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia).
addf HS 20%nat (mkAF 4096 (2 ^ 47) 0) F20. addf HS 22%nat (mkAF 4096 (2 ^ 47) 0) F22.
assert (R6_18' : getr regs6 18%bv = Z_to_bv 64 1) by (rewrite R6_18; reflexivity).
assert (R6_10' : getr regs6 10%bv = Z_to_bv 64 0) by (rewrite R6_10; reflexivity).
pin HS (18%bv : bv 5) (SLit 1) R6_18'.
pin HS (10%bv : bv 5) (SLit 0) R6_10'.
paj_run_shc RUNP RUNC HS HJ6.
{ intros a (r & Hin & Ha).
  lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
  cbn [In] in Hin. destruct Hin as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. lia. }
(* the mac object at F + 112: present, in the app range, addressable and hull-visible at any journal state whose
   protected bytes still read as the cut's *)
assert (MACOK : forall m md k, ajournal (SK := scene_sink_head) SEGS B LLVMF_STK sp0 [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(8, c_fpos cx)] ly4 S4 W4 m md k ->
  (forall a, s5_prot sp0 sp1 F sF a -> aview SEGS (w_H W4) m a = aview SEGS (w_H W3) mem3 a) ->
  (forall j, 0 <= j < 6 -> aview SEGS (w_H W4) m (F + 112 + j) <> None) /\ amem_range (F + 112) 6 /\
  range_addressable (aview SEGS (w_H W4) m) SHADOW_OFF (F + 112) 6 /\ shadow_hull_vis (aview SEGS (w_H W4) m) (F + 112) 6).
{ intros m md k HJm KPm. pose proof (proj1 HJm) as HARm.
  pose proof HJm as (_ & HLYm & _ & _ & _ & Hfrsm & _).
  assert (Hfinm : In (8, c_fpos cx) (frames S4)) by (rewrite Hfrsm; left; reflexivity).
  destruct (al_layout _ _ LAWS _ _ _ _ _ ly4 HAR0 HLYm) as (_ & EFAm & _).
  destruct (al_frames _ _ LAWS ly4 S4 W4 m md 8 (c_fpos cx) HARm Hfinm) as (_ & _ & HFp & _).
  rewrite EFAm, HcidF in HFp. change (fs_frame_bytes 8) with 16384 in HFp.
  split; [intros j Hj; apply (aview_some_of_apresent SEGS); exact (proj1 (HFp (F + 112 + j) ltac:(lia)))|].
  split; [apply (amem_range_sub_app F 16384 (F + 112) 6 HFapp HFceil); lia|].
  split.
  { apply (block_shadow_range _ SHADOW_OFF (F + 112) 6 (F + 112) 6); [|lia|lia].
    unfold sc_open in HOPMAC. cbn [sg_off_mac sg_mac_n scene_geom_asan_ubsan] in HOPMAC.
    destruct HOPMAC as (Hm & Hn & Hcm). split; [exact Hm|]. split; [exact Hn|].
    intros i Hi. change ((6 + 7) / 8) with 1 in Hi.
    assert (Ea : shadow_of_addr SHADOW_OFF (F + 112) + i = sF + (14 + i))
    by (unfold shadow_of_addr, sF, shadow_addr; replace (F + 112) with (F + 8 * 14) by lia; rewrite HF8g by lia; lia).
    rewrite Ea, KPm by (unfold s5_prot; lia). rewrite <- Ea. exact (Hcm i Hi). }
  eapply (shadow_hull_vis_of_frame SEGS B LAWS ly4 S4 W4 m md 8 (c_fpos cx) (F + 112) 6 HARm Hfinm);
  [rewrite EFAm, HcidF; lia | rewrite EFAm, HcidF; change (fs_frame_bytes 8) with 16384; lia | lia]. }
rename ms into msP, HJ6 into HJP, HFr into HFrP. clear HF HG.
prreg HS (10%bv : bv 5) Pa0. prreg HS (11%bv : bv 5) Pa1. prreg HS (12%bv : bv 5) Pa2. prreg HS (1%bv : bv 5) Pra.
prreg HS (23%bv : bv 5) Ps7. prreg HS (25%bv : bv 5) Ps9.
assert (RKPl : forall r, In r [2; 3; 4; 8; 9; 19; 20; 22; 24]%bv -> getr (ms_regs msP) r = getr regs6 r).
{ intros x Hx. exact (regs_kept_of_st_ok SEGS E _ (restrict (w_H W4) msP) regs6 (s5_extra nn F)
  [2; 3; 4; 8; 9; 19; 20; 22; 24]%bv HS HAG6 eq_refl x Hx). }
assert (RKP : s5_rk sp0 sp1 sF body np (ms_regs msP))
by (apply (s5_rk_kept _ _ _ _ _ regs6); [intros r Hr; apply RKPl; cbn in Hr |- *; tauto | exact RK6]).
pose proof RKP as (RP2 & RP3 & RP4 & RP8 & RP9 & RP19 & RP20 & RP24).
assert (RP22 : getr (ms_regs msP) 22%bv = Z_to_bv 64 res) by (rewrite (RKPl 22%bv ltac:(cbn; tauto)); exact R6_22).
assert (RP23 : getr (ms_regs msP) 23%bv = Z_to_bv 64 0) by (rewrite Ps7; reflexivity).
assert (RP25 : getr (ms_regs msP) 25%bv = Z_to_bv 64 (body + 832))
by (rewrite Ps9; cbn [sv_denot]; rewrite (EE 20%nat 20%bv eq_refl), R6_20; unfold YG0d.w64;
    rewrite unsigned_lit_small by lia; reflexivity).
assert (KPm : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W4) (ms_mem msP) a = aview SEGS (w_H W4) mem6 a).
{ intros a Ha. eapply (aview_kept_frame _ _ _ _ _ 0 HFrP); [lia | | exact Ha].
  intros b0 Hb0 (r & Hin & Hrb).
  lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
  cbn [In] in Hin. destruct Hin as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb. lia. }
clear HFrP.
assert (KPP : forall a, s5_prot sp0 sp1 F sF a -> aview SEGS (w_H W4) (ms_mem msP) a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. rewrite KPm by (destruct (PCLS a (or_introl Ha)) as [H|[H|[H|H]]]; lia). exact (KP6 a Ha). }
assert (Pa0' : getr (ms_regs msP) 10%bv = YG0d.w64 (body + 832))
by (rewrite Pa0; cbn [sv_denot]; rewrite (EE 20%nat 20%bv eq_refl), R6_20; unfold YG0d.w64;
    rewrite unsigned_lit_small by lia; reflexivity).
assert (E33b : ew E 33 = Z_to_bv 64 F)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs6 _ 1)).
assert (Pa1' : getr (ms_regs msP) 11%bv = YG0d.w64 (F + 112))
by (rewrite Pa1; cbn [sv_denot]; rewrite E33b; unfold YG0d.w64; rewrite unsigned_lit_small by lia; reflexivity).
assert (Pa2' : getr (ms_regs msP) 12%bv = YG0d.w64 6) by (rewrite Pa2; reflexivity).
pmkst HS.
eapply SRr_bind.
{ destruct (BLK _ _ _ HJP body Hbody4 (body + 832) 6 ltac:(lia) ltac:(lia) ltac:(lia)) as (MX1 & MX2 & MX3 & MX4).
  destruct (MACOK _ _ _ HJP KPP) as (MY1 & MY2 & MY3 & MY4).
  eapply (BCMP (ms_regs msP) (ms_mem msP) _ (body + 832) (F + 112) 6 (Z_to_bv 64 (BASE + 1964)) HJP Pa0' Pa1' Pa2');
  [lia | lia | lia | lia | lia | unfold spZ; rewrite RP2; apply unsigned_lit_small; lia | exact RP3 | exact RP4 | exact Pra
  | apply ret_ok_codeptr_v; [lia | reflexivity] | exact MX1 | exact MY1 | exact MX2 | exact MY2 | exact MX3 | exact MX4
  | exact MY3 | intros _; exact MY4]. }
cbv beta. intros Wm cm _ (-> & regsm & memm & mdm & vm & -> & HJm & HPm & Rm10 & Hcmpm & Km).
assert (Hvm : vm = YG0d.w64 0).
{ apply (proj2 Hcmpm). intros i Hi. rewrite !KPm by lia.
  replace (body + 832 + i) with (body + 832 + i) by lia. rewrite (MACB6 i Hi).
  symmetry. apply KP6. unfold s5_prot. lia. }
rewrite Hvm in Rm10. clear Hvm Hcmpm.
pose proof (conj KP6 (conj BODY6 (conj MACB6 BEF6))) as MOK6.
pose proof (TP mem6 (ms_mem msP) ltac:(intros a Ha _ _; apply KPm; exact Ha) MOK6) as MOKP.
pose proof (TP (ms_mem msP) memm ltac:(intros a Ha _ Hw; apply Km; [exact Ha | rewrite Hes; lia]) MOKP) as MOKm.
clear MOK6 MOKP. clear HS HE HEI EE HAG6 Pa0 Pa1 Pa2 Ps7 Ps9 Pa0' Pa1' Pa2' E33b E20 E22 F20 F22 E.
pose proof MOKm as (MP & MB & MM & MR).
pose proof (s5_rk_pres _ _ _ _ _ _ _ HPm RKP) as RKm.
pose proof RKm as (Rm2 & Rm3 & Rm4 & Rm8 & Rm9 & Rm19 & Rm20 & Rm24).
assert (Rm22 : getr regsm 22 = Z_to_bv 64 res)
by (transitivity (getr (ms_regs msP) 22%bv); [exact (HPm 22 ltac:(unfold acallee_saved; lia)) | exact RP22]).
assert (Rm23 : getr regsm 23 = Z_to_bv 64 0)
by (transitivity (getr (ms_regs msP) 23%bv); [exact (HPm 23 ltac:(unfold acallee_saved; lia)) | exact RP23]).
assert (Rm25 : getr regsm 25 = Z_to_bv 64 (body + 832))
by (transitivity (getr (ms_regs msP) 25%bv); [exact (HPm 25 ltac:(unfold acallee_saved; lia)) | exact RP25]).
assert (Rm10' : getr regsm 10%bv = Z_to_bv 64 0) by (rewrite Rm10; reflexivity).
(* ---- 0x83050 .. jal __wrap_bcmp 0x83060 (body vs before, 832 bytes) ---- *)
pose proof (s5_entry W4 regsm memm 1964 sp1 F sF nn Rm9 Rm19 ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) (SPOK memm MP)) as HS.
remember (Eimg (Ereg regsm (s5_extra nn F))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsm r)
by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HAGm : env_agree 32 (Ereg regsm (s5_extra nn F)) E)
by (subst E; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (Fm20 : afact_ok E 20 (mkAF 4096 (2 ^ 47) 0))
by (unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite (EE 20%nat 20%bv eq_refl), Rm20, unsigned_lit_small by lia;
    rewrite Z.pow_0_r, Z.mod_1_r; lia).
assert (Fm22 : afact_ok E 22 (mkAF 4096 (2 ^ 47) 0))
by (unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite (EE 22%nat 22%bv eq_refl), Rm22, unsigned_lit_small by lia;
    rewrite Z.pow_0_r, Z.mod_1_r; lia).
assert (Fm25 : afact_ok E 25 (mkAF 4096 (2 ^ 47) 0))
by (unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite (EE 25%nat 25%bv eq_refl), Rm25, unsigned_lit_small by lia;
    rewrite Z.pow_0_r, Z.mod_1_r; lia).
addf HS 20%nat (mkAF 4096 (2 ^ 47) 0) Fm20. addf HS 22%nat (mkAF 4096 (2 ^ 47) 0) Fm22.
addf HS 25%nat (mkAF 4096 (2 ^ 47) 0) Fm25.
pin HS (10%bv : bv 5) (SLit 0) Rm10'.
paj_run_shc RUNP RUNC HS HJm.
{ intros a (r & Hin & Ha).
  lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
  cbn [In] in Hin. destruct Hin as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. lia. }
rename ms into msQ, HJm into HJQ, HFr into HFrQ. clear HF HG.
prreg HS (10%bv : bv 5) Qa0. prreg HS (11%bv : bv 5) Qa1. prreg HS (12%bv : bv 5) Qa2. prreg HS (1%bv : bv 5) Qra.
assert (RKQl : forall r, In r [2; 3; 4; 8; 9; 19; 20; 22; 23; 24; 25]%bv -> getr (ms_regs msQ) r = getr regsm r).
{ intros x Hx. exact (regs_kept_of_st_ok SEGS E _ (restrict (w_H W4) msQ) regsm (s5_extra nn F)
  [2; 3; 4; 8; 9; 19; 20; 22; 23; 24; 25]%bv HS HAGm eq_refl x Hx). }
assert (RKQ : s5_rk sp0 sp1 sF body np (ms_regs msQ))
by (apply (s5_rk_kept _ _ _ _ _ regsm); [intros r Hr; apply RKQl; cbn in Hr |- *; tauto | exact RKm]).
pose proof RKQ as (RQ2 & RQ3 & RQ4 & RQ8 & RQ9 & RQ19 & RQ20 & RQ24).
assert (RQ22 : getr (ms_regs msQ) 22%bv = Z_to_bv 64 res) by (rewrite (RKQl 22%bv ltac:(cbn; tauto)); exact Rm22).
assert (RQ23 : getr (ms_regs msQ) 23%bv = Z_to_bv 64 0) by (rewrite (RKQl 23%bv ltac:(cbn; tauto)); exact Rm23).
assert (RQ25 : getr (ms_regs msQ) 25%bv = Z_to_bv 64 (body + 832)) by (rewrite (RKQl 25%bv ltac:(cbn; tauto)); exact Rm25).
assert (KQ : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W4) (ms_mem msQ) a = aview SEGS (w_H W4) memm a).
{ intros a Ha. eapply (aview_kept_frame _ _ _ _ _ 0 HFrQ); [lia | | exact Ha].
  intros b0 Hb0 (r & Hin & Hrb).
  lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
  cbn [In] in Hin. destruct Hin as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb. lia. }
clear HFrQ.
pose proof (TP memm (ms_mem msQ) ltac:(intros a Ha _ _; apply KQ; exact Ha) MOKm) as MOKQ.
pose proof MOKQ as (QP & QB & QM & QR).
assert (Qa0' : getr (ms_regs msQ) 10%bv = YG0d.w64 body)
by (rewrite Qa0; cbn [sv_denot]; rewrite (EE 20%nat 20%bv eq_refl), Rm20; unfold YG0d.w64;
    rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; first [reflexivity | rewrite unsigned_lit_small by lia; reflexivity]).
assert (Qa1' : getr (ms_regs msQ) 11%bv = YG0d.w64 res)
by (rewrite Qa1; cbn [sv_denot]; rewrite (EE 22%nat 22%bv eq_refl), Rm22; unfold YG0d.w64;
    rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; first [reflexivity | rewrite unsigned_lit_small by lia; reflexivity]).
assert (Qa2' : getr (ms_regs msQ) 12%bv = YG0d.w64 832) by (rewrite Qa2; reflexivity).
pmkst HS.
clear HS HE HEI EE HAGm Qa0 Qa1 Qa2 Fm20 Fm22 Fm25 E.
eapply SRr_bind.
{ destruct (BLK _ _ _ HJQ body Hbody4 body 832 ltac:(lia) ltac:(lia) ltac:(lia)) as (PX1 & PX2 & PX3 & PX4).
  destruct (BLK _ _ _ HJQ res Hin4 res 832 ltac:(lia) ltac:(lia) ltac:(lia)) as (PY1 & PY2 & PY3 & PY4).
  eapply (BCMP (ms_regs msQ) (ms_mem msQ) _ body res 832 (Z_to_bv 64 (BASE + 1984)) HJQ Qa0' Qa1' Qa2');
  [lia | lia | lia | lia | lia | unfold spZ; rewrite RQ2; apply unsigned_lit_small; lia | exact RQ3 | exact RQ4 | exact Qra
  | apply ret_ok_codeptr_v; [lia | reflexivity] | exact PX1 | exact PY1 | exact PX2 | exact PY2 | exact PX3 | exact PX4
  | exact PY3 | exact PY4]. }
cbv beta. intros Wp cp _ (-> & regsp & memp & mdp & vp & -> & HJp & HPp & Rp10 & Hcmpp & Kp).
assert (Hvp : vp = YG0d.w64 0).
{ apply (proj2 Hcmpp). intros i Hi. rewrite (QB i ltac:(lia) ltac:(lia)), (QR i ltac:(lia)). reflexivity. }
rewrite Hvp in Rp10. clear Hvp Hcmpp.
pose proof (TP (ms_mem msQ) memp ltac:(intros a Ha _ Hw; apply Kp; [exact Ha | rewrite Hes; lia]) MOKQ) as MOKp.
pose proof MOKp as (PP & PB & PM & PR).
pose proof (s5_rk_pres _ _ _ _ _ _ _ HPp RKQ) as RKp.
pose proof RKp as (Rp2 & Rp3 & Rp4 & Rp8 & Rp9 & Rp19 & Rp20 & Rp24).
assert (Rp22 : getr regsp 22 = Z_to_bv 64 res)
by (transitivity (getr (ms_regs msQ) 22%bv); [exact (HPp 22 ltac:(unfold acallee_saved; lia)) | exact RQ22]).
assert (Rp23 : getr regsp 23 = Z_to_bv 64 0)
by (transitivity (getr (ms_regs msQ) 23%bv); [exact (HPp 23 ltac:(unfold acallee_saved; lia)) | exact RQ23]).
assert (Rp25 : getr regsp 25 = Z_to_bv 64 (body + 832))
by (transitivity (getr (ms_regs msQ) 25%bv); [exact (HPp 25 ltac:(unfold acallee_saved; lia)) | exact RQ25]).
assert (Rp10' : getr regsp 10%bv = Z_to_bv 64 0) by (rewrite Rp10; reflexivity).
assert (Rp24' : getr regsp 24%bv = Z_to_bv 64 8904) by (rewrite Rp24, Hgo; reflexivity).
(* ---- 0x83064 .. the four UBSan guards and jal __wrap_bcmp 0x83098 (body + 0x346 vs before + 0x346) ---- *)
pose proof (s5_entry W4 regsp memp 1984 sp1 F sF nn Rp9 Rp19 ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) (SPOK memp PP)) as HS.
remember (Eimg (Ereg regsp (s5_extra nn F))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsp r)
by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HAGp : env_agree 32 (Ereg regsp (s5_extra nn F)) E)
by (subst E; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (Fp20 : afact_ok E 20 (mkAF 4096 (2 ^ 47) 0))
by (unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite (EE 20%nat 20%bv eq_refl), Rp20, unsigned_lit_small by lia;
    rewrite Z.pow_0_r, Z.mod_1_r; lia).
assert (Fp22 : afact_ok E 22 (mkAF 4096 (2 ^ 47) 0))
by (unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite (EE 22%nat 22%bv eq_refl), Rp22, unsigned_lit_small by lia;
    rewrite Z.pow_0_r, Z.mod_1_r; lia).
assert (Fp25 : afact_ok E 25 (mkAF 4096 (2 ^ 47) 0))
by (unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite (EE 25%nat 25%bv eq_refl), Rp25, unsigned_lit_small by lia;
    rewrite Z.pow_0_r, Z.mod_1_r; lia).
addf HS 20%nat (mkAF 4096 (2 ^ 47) 0) Fp20. addf HS 22%nat (mkAF 4096 (2 ^ 47) 0) Fp22.
addf HS 25%nat (mkAF 4096 (2 ^ 47) 0) Fp25.
pin HS (10%bv : bv 5) (SLit 0) Rp10'. pin HS (24%bv : bv 5) (SLit 8904) Rp24'.
paj_run_shc RUNP RUNC HS HJp.
{ intros a (r & Hin & Ha).
  lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
  cbn [In] in Hin. destruct Hin as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. lia. }
rename ms into msR, HJp into HJR, HFr into HFrR. clear HF HG.
prreg HS (10%bv : bv 5) Ra0b. prreg HS (11%bv : bv 5) Ra1b. prreg HS (12%bv : bv 5) Ra2b. prreg HS (1%bv : bv 5) Rrab.
prreg HS (24%bv : bv 5) Rs8b.
assert (RKRl : forall r, In r [2; 3; 4; 8; 9; 19; 20; 22; 23; 25]%bv -> getr (ms_regs msR) r = getr regsp r).
{ intros x Hx. exact (regs_kept_of_st_ok SEGS E _ (restrict (w_H W4) msR) regsp (s5_extra nn F)
  [2; 3; 4; 8; 9; 19; 20; 22; 23; 25]%bv HS HAGp eq_refl x Hx). }
assert (RR24 : getr (ms_regs msR) 24%bv = Z_to_bv 64 np) by (rewrite Rs8b, Hgo; reflexivity).
assert (RKR : s5_rk sp0 sp1 sF body np (ms_regs msR)).
{ unfold s5_rk.
  split; [rewrite (RKRl 2%bv ltac:(cbn; tauto)); exact Rp2|].
  split; [rewrite (RKRl 3%bv ltac:(cbn; tauto)); exact Rp3|].
  split; [rewrite (RKRl 4%bv ltac:(cbn; tauto)); exact Rp4|].
  split; [rewrite (RKRl 8%bv ltac:(cbn; tauto)); exact Rp8|].
  split; [rewrite (RKRl 9%bv ltac:(cbn; tauto)); exact Rp9|].
  split; [rewrite (RKRl 19%bv ltac:(cbn; tauto)); exact Rp19|].
  split; [rewrite (RKRl 20%bv ltac:(cbn; tauto)); exact Rp20 | exact RR24]. }
pose proof RKR as (RR2 & RR3 & RR4 & RR8 & RR9 & RR19 & RR20 & _).
assert (RR22 : getr (ms_regs msR) 22%bv = Z_to_bv 64 res) by (rewrite (RKRl 22%bv ltac:(cbn; tauto)); exact Rp22).
assert (RR23 : getr (ms_regs msR) 23%bv = Z_to_bv 64 0) by (rewrite (RKRl 23%bv ltac:(cbn; tauto)); exact Rp23).
assert (KR : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W4) (ms_mem msR) a = aview SEGS (w_H W4) memp a).
{ intros a Ha. eapply (aview_kept_frame _ _ _ _ _ 0 HFrR); [lia | | exact Ha].
  intros b0 Hb0 (r & Hin & Hrb).
  lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
  cbn [In] in Hin. destruct Hin as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb. lia. }
clear HFrR.
pose proof (TP memp (ms_mem msR) ltac:(intros a Ha _ _; apply KR; exact Ha) MOKp) as MOKR.
pose proof MOKR as (RP & RB & RM & RR).
assert (Ra0b' : getr (ms_regs msR) 10%bv = YG0d.w64 (body + 838))
by (rewrite Ra0b; cbn [sv_denot]; rewrite (EE 20%nat 20%bv eq_refl), Rp20; unfold YG0d.w64;
    rewrite unsigned_lit_small by lia; reflexivity).
assert (Ra1b' : getr (ms_regs msR) 11%bv = YG0d.w64 (res + 838))
by (rewrite Ra1b; cbn [sv_denot]; rewrite (EE 22%nat 22%bv eq_refl), Rp22; unfold YG0d.w64;
    rewrite unsigned_lit_small by lia; reflexivity).
assert (Ra2b' : getr (ms_regs msR) 12%bv = YG0d.w64 8066) by (rewrite Ra2b; reflexivity).
pmkst HS.
clear HS HE HEI EE HAGp Ra0b Ra1b Ra2b Fp20 Fp22 Fp25 E.
eapply SRr_bind.
{ destruct (BLK _ _ _ HJR body Hbody4 (body + 838) 8066 ltac:(lia) ltac:(lia) ltac:(lia)) as (RX1 & RX2 & RX3 & RX4).
  destruct (BLK _ _ _ HJR res Hin4 (res + 838) 8066 ltac:(lia) ltac:(lia) ltac:(lia)) as (RY1 & RY2 & RY3 & RY4).
  eapply (BCMP (ms_regs msR) (ms_mem msR) _ (body + 838) (res + 838) 8066 (Z_to_bv 64 (BASE + 2040)) HJR Ra0b' Ra1b' Ra2b');
  [lia | lia | lia | lia | lia | unfold spZ; rewrite RR2; apply unsigned_lit_small; lia | exact RR3 | exact RR4 | exact Rrab
  | apply ret_ok_codeptr_v; [lia | reflexivity] | exact RX1 | exact RY1 | exact RX2 | exact RY2 | exact RX3 | exact RX4
  | exact RY3 | exact RY4]. }
cbv beta. intros Wr cr _ (-> & regsr & memr & mdr & vr & -> & HJr & HPr & Rr10 & Hcmpr & Kr).
assert (Hvr : vr = YG0d.w64 0).
{ apply (proj2 Hcmpr). intros i Hi.
  replace (body + 838 + i) with (body + (838 + i)) by lia. replace (res + 838 + i) with (res + (838 + i)) by lia.
  rewrite (RB (838 + i) ltac:(lia) ltac:(lia)), (RR (838 + i) ltac:(lia)). reflexivity. }
rewrite Hvr in Rr10. clear Hvr Hcmpr.
pose proof (TP (ms_mem msR) memr ltac:(intros a Ha _ Hw; apply Kr; [exact Ha | rewrite Hes; lia]) MOKR) as MOKr.
pose proof MOKr as (rP & rB & rM & rR).
pose proof (s5_rk_pres _ _ _ _ _ _ _ HPr RKR) as RKr.
pose proof RKr as (Rr2 & Rr3 & Rr4 & Rr8 & Rr9 & Rr19 & Rr20 & Rr24).
assert (Rr23 : getr regsr 23 = Z_to_bv 64 0)
by (transitivity (getr (ms_regs msR) 23%bv); [exact (HPr 23 ltac:(unfold acallee_saved; lia)) | exact RR23]).
assert (Rr10' : getr regsr 10%bv = Z_to_bv 64 0) by (rewrite Rr10; reflexivity).
assert (Rr24' : getr regsr 24%bv = Z_to_bv 64 8904) by (rewrite Rr24, Hgo; reflexivity).
(* the bytes a callee journal at sp1 keeps when its footprint lies in body: the protected bytes, the expect row and
   the before block *)
destruct (al_blocks _ _ LAWS _ _ _ _ _ body nn HAR4 Hbody4) as (_ & _ & _ & Hbapp & _).
rewrite Ereq in Hbapp. unfold in_app, kLowShadowBeg, kHighMemBeg in Hbapp.
assert (KEEPJ : forall STK1 FP1 m md m' md' k,
  ajournal (SK := scene_sink_head) SEGS B STK1 sp1 FP1 ly4 S4 W4 m md [] ly4 S4 W4 m' md' k ->
  (forall a, inFP FP1 a -> body <= a < body + nn) ->
  forall a, (s5_prot sp0 sp1 F sF a \/ s5_row sF a \/ (exists i, 0 <= i < np /\ a = res + i)) ->
  aview SEGS (w_H W4) m' a = aview SEGS (w_H W4) m a).
{ intros STK1 FP1 m md m' md' k HJk HFP a Ha.
  pose proof HJk as (_ & _ & _ & _ & _ & _ & _ & _ & J1 & J2 & _ & J4 & _).
  destruct Ha as [Ha | [Ha | (i & Hi & ->)]].
  - destruct (PCLS a (or_introl Ha)) as [H | [H | [H | H]]].
    + apply J1; lia.
    + apply (J4 8 (c_fpos cx) a Hfin4); [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite EFA4, HcidF;
        change (fs_frame_bytes 8) with 16384; lia | intros Hin; pose proof (HFP a Hin); lia].
    + apply (J4 8 (c_fpos cx) a Hfin4); [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite EFA4, HcidF;
        change (fs_frame_bytes 8) with 16384; lia | intros Hin; pose proof (HFP a Hin); lia].
    + apply (J4 8 (c_fpos cx) a Hfin4); [right; unfold in_zr; cbn [fst snd]; rewrite EFA4, HcidF; fold sF;
        change (fs_frame_bytes 8 / 8) with 2048; lia | intros Hin; pose proof (HFP a Hin); lia].
  - apply (J4 8 (c_fpos cx) a Hfin4); [right; unfold in_zr, s5_row in *; cbn [fst snd]; rewrite EFA4, HcidF; fold sF;
      change (fs_frame_bytes 8 / 8) with 2048; lia | intros Hin; pose proof (HFP a Hin); unfold s5_row in Ha; lia].
  - apply (J2 res nn i Hin4 Hin4); [rewrite Ereq; lia | intros Hin; pose proof (HFP _ Hin); lia]. }
(* ---- 0x8309c .. jal reac_ctrl_scene_build 0x830ac (the ok path: n' = 8904) ---- *)
pose proof (s5_entry W4 regsr memr 2040 sp1 F sF nn Rr9 Rr19 ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) (SPOK memr rP)) as HS.
remember (Eimg (Ereg regsr (s5_extra nn F))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsr r)
by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HAGr : env_agree 32 (Ereg regsr (s5_extra nn F)) E)
by (subst E; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
pin HS (10%bv : bv 5) (SLit 0) Rr10'. pin HS (24%bv : bv 5) (SLit 8904) Rr24'.
paj_run_shc RUNP RUNC HS HJr.
{ intros a (r & Hin & Ha).
  lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
  cbn [In] in Hin. destruct Hin as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. lia. }
rename ms into msS, HJr into HJS, HFr into HFrS. clear HF HG.
prreg HS (10%bv : bv 5) Sa0. prreg HS (11%bv : bv 5) Sa1. prreg HS (12%bv : bv 5) Sa2. prreg HS (1%bv : bv 5) Sra.
prreg HS (24%bv : bv 5) Ss8.
assert (RKSl : forall r, In r [2; 3; 4; 8; 9; 19; 20; 22; 23]%bv -> getr (ms_regs msS) r = getr regsr r).
{ intros x Hx. exact (regs_kept_of_st_ok SEGS E _ (restrict (w_H W4) msS) regsr (s5_extra nn F)
  [2; 3; 4; 8; 9; 19; 20; 22; 23]%bv HS HAGr eq_refl x Hx). }
assert (RS24 : getr (ms_regs msS) 24%bv = Z_to_bv 64 np) by (rewrite Ss8, Hgo; reflexivity).
assert (RKS : s5_rk sp0 sp1 sF body np (ms_regs msS)).
{ unfold s5_rk.
  split; [rewrite (RKSl 2%bv ltac:(cbn; tauto)); exact Rr2|].
  split; [rewrite (RKSl 3%bv ltac:(cbn; tauto)); exact Rr3|].
  split; [rewrite (RKSl 4%bv ltac:(cbn; tauto)); exact Rr4|].
  split; [rewrite (RKSl 8%bv ltac:(cbn; tauto)); exact Rr8|].
  split; [rewrite (RKSl 9%bv ltac:(cbn; tauto)); exact Rr9|].
  split; [rewrite (RKSl 19%bv ltac:(cbn; tauto)); exact Rr19|].
  split; [rewrite (RKSl 20%bv ltac:(cbn; tauto)); exact Rr20 | exact RS24]. }
pose proof RKS as (RS2 & RS3 & RS4 & RS8 & RS9 & RS19 & RS20 & _).
assert (RS23 : getr (ms_regs msS) 23%bv = Z_to_bv 64 0) by (rewrite (RKSl 23%bv ltac:(cbn; tauto)); exact Rr23).
assert (KS : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W4) (ms_mem msS) a = aview SEGS (w_H W4) memr a).
{ intros a Ha. eapply (aview_kept_frame _ _ _ _ _ 0 HFrS); [lia | | exact Ha].
  intros b0 Hb0 (r & Hin & Hrb).
  lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
  cbn [In] in Hin. destruct Hin as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb. lia. }
clear HFrS.
pose proof (TP memr (ms_mem msS) ltac:(intros a Ha _ _; apply KS; exact Ha) MOKr) as MOKS.
pose proof MOKS as (SP & SB & SM & SR).
assert (E33c : ew E 33 = Z_to_bv 64 F)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsr _ 1)).
assert (Sa0' : getr (ms_regs msS) 10%bv = YG0d.w64 body)
by (rewrite Sa0; cbn [sv_denot]; rewrite (EE 20%nat 20%bv eq_refl), Rr20; unfold YG0d.w64;
    rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; first [reflexivity | rewrite unsigned_lit_small by lia; reflexivity]).
assert (Sa1' : getr (ms_regs msS) 11%bv = YG0d.w64 np) by (rewrite Sa1, Hgo; reflexivity).
assert (Sa2' : getr (ms_regs msS) 12%bv = YG0d.w64 (F + 112))
by (rewrite Sa2; cbn [sv_denot]; rewrite E33c; unfold YG0d.w64; rewrite unsigned_lit_small by lia; reflexivity).
pmkst HS.
clear HS HE HEI EE HAGr Sa0 Sa1 Sa2 Ss8 E33c E.
assert (HSIGB2 : SIGMA SS_reac_ctrl_scene_build = BASE + AF_reac_ctrl_scene_build) by reflexivity.
rewrite HSIGB2.
assert (Hokt : scene_okb body np (F + 112) = true).
{ unfold scene_okb. replace (np =? P_reac_ctrl_scene_build.SCENE_BYTES) with true
  by (symmetry; apply Z.eqb_eq; unfold P_reac_ctrl_scene_build.SCENE_BYTES; exact Hgo).
  destruct (Z.eqb_spec body 0); [lia|]. destruct (Z.eqb_spec (F + 112) 0); [lia|]. reflexivity. }
eapply SRr_bind.
{ eapply (cl_callS (SK := scene_sink_head) B LAWS W4 (ms_regs msS) (ms_mem msS) (Z_to_bv 64 (BASE + AF_reac_ctrl_scene_build))
    LLVMF_STK sp0 [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(8, c_fpos cx)] ly4 S4 _ (ev + 1)
    REAC_CTRL_SCENE_BUILD_STK (scene_fp body np (F + 112)) 0 (sp1 - sp0) (getr (ms_regs msS) 1) (rt_ch cx) _ HJS).
  - unfold spZ at 1. rewrite RS2, unsigned_lit_small by lia. lia.
  - exact Hom.
  - lia.
  - unfold REAC_CTRL_SCENE_BUILD_STK. rewrite Hes. lia.
  - unfold REAC_CTRL_SCENE_BUILD_STK. rewrite Hes. lia.
  - exact RS3.
  - exact RS4.
  - reflexivity.
  - rewrite Sra. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite Sra, unsigned_lit_small by lia. lia.
  - replace (sp0 + (sp1 - sp0)) with sp1 by lia.
    replace (s0Z (ms_regs msS)) with sp0 by (unfold s0Z; rewrite RS8; symmetry; apply unsigned_lit_small; lia).
    exact (ACH (ms_mem msS) _ (ev + 1) HJS SP).
  - intros HPRE1.
    assert (HOK : scene_okb body np (F + 112) = true ->
      In (body, P_reac_ctrl_scene_build.SCENE_BYTES) (ablocks B ly4 S4) /\
      afobj SEGS B ly4 S4 W4 (ms_mem msS) (F + 112) P_reac_ctrl_scene_build.SCENE_MAC_LEN).
    { intros _. unfold P_reac_ctrl_scene_build.SCENE_BYTES, P_reac_ctrl_scene_build.SCENE_MAC_LEN.
      split; [rewrite <- Hnn8904; exact Hbody4|].
      destruct (MACOK _ _ _ HJS SP) as (_ & _ & MRA & _).
      unfold afobj. split.
      { exists 8, (c_fpos cx). split; [exact Hfin4|]. rewrite EFA4, HcidF. change (fs_frame_bytes 8) with 16384.
        split; [lia|]. split; [|lia].
        destruct (proj1 (Z.mod_divide F 32 ltac:(lia)) HF32) as [q Hq]. rewrite Hq.
        replace (q * 32) with ((4 * q) * 8) by lia. apply Z_mod_mult. }
      split; [|exact MRA].
      destruct (proj1 (Z.mod_divide F 32 ltac:(lia)) HF32) as [q Hq]. rewrite Hq.
      replace (q * 32 + 112) with ((4 * q + 14) * 8) by lia. apply Z_mod_mult. }
    pose proof (SSB ly4 S4 W4 (ms_regs msS) (ms_mem msS) _ (rt_ch cx) body np (F + 112) HPRE1 Sa0' Sa1' Sa2'
      ltac:(lia) ltac:(lia) ltac:(lia) HOK) as CALL.
    unfold cfg_at, treac_ctrl_scene_build_post, apost_base, A_reac_ctrl_scene_buildP in CALL. exact CALL.
  - intros a Ha. right. unfold scene_fp in Ha. rewrite Hokt in Ha.
    destruct Ha as (r & [<- | []] & Hr). cbn [fst snd] in Hr. unfold P_reac_ctrl_scene_build.SCENE_BYTES in Hr.
    exists body, nn. split; [exact Hbody4|]. split; [exact Hbody_new | rewrite Ereq; lia]. }
cbv beta. intros W10 c10 _ (ly10 & S10 & regs10 & mem10 & md10 & -> & HJ10 & HJ10i & HP10 & (-> & -> & -> & HSC2)).
rewrite Hokt in HSC2. destruct HSC2 as (R10_10 & SCBF). rewrite Z.add_0_r in HJ10. rewrite Sra.
unfold P_reac_ctrl_scene_build.SCENE_BYTES, P_reac_ctrl_scene_build.SCENE_MAC_OFF, P_reac_ctrl_scene_build.SCENE_MAC_LEN in SCBF.
replace (sp0 + (sp1 - sp0)) with sp1 in HJ10i by lia.
assert (HFPsb : forall a, inFP (scene_fp body np (F + 112)) a -> body <= a < body + nn).
{ unfold scene_fp. rewrite Hokt. intros a (r & [<- | []] & Hr). cbn [fst snd] in Hr.
  unfold P_reac_ctrl_scene_build.SCENE_BYTES in Hr. lia. }
assert (KP10 : forall a, s5_prot sp0 sp1 F sF a -> aview SEGS (w_H W4) mem10 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. rewrite (KEEPJ _ _ _ _ _ _ _ HJ10i HFPsb a (or_introl Ha)). exact (SP a Ha). }
assert (BF10 : forall i, 0 <= i < 8904 -> aview SEGS (w_H W4) mem10 (body + i) =
  if (832 <=? i) && (i <? 832 + 6) then aview SEGS (w_H W3) mem3 (F + 112 + (i - 832)) else Some (scene_tag i)).
{ intros i Hi. rewrite (SCBF i Hi). destruct ((832 <=? i) && (i <? 832 + 6)) eqn:Hm; [|reflexivity].
  apply andb_prop in Hm as [Hm1 Hm2]. apply Z.leb_le in Hm1. apply Z.ltb_lt in Hm2.
  apply SP. unfold s5_prot. lia. }
pose proof (s5_rk_pres _ _ _ _ _ _ _ HP10 RKS) as RK10.
pose proof RK10 as (R10_2 & R10_3 & R10_4 & R10_8 & R10_9 & R10_19 & R10_20 & R10_24).
assert (R10_23 : getr regs10 23 = Z_to_bv 64 0)
by (transitivity (getr (ms_regs msS) 23%bv); [exact (HP10 23 ltac:(unfold acallee_saved; lia)) | exact RS23]).
assert (R10_10' : getr regs10 10%bv = Z_to_bv 64 0) by (rewrite R10_10; reflexivity).
(* the earlier steps' facts are no longer needed: drop them, so that lia sees a small context *)
repeat match goal with
| H : forall a, s5_prot _ _ _ _ a -> aview _ _ ?m a = _ |- _ =>
    lazymatch m with mem10 => fail | _ => clear H end
| H : forall a, 0 <= a < 2 ^ 64 -> aview _ _ _ a = aview _ _ _ a |- _ => clear H
end.
try clear MOKS SB SM SR SCBF MOKr rB rM rR HJ10i SPOK.
(* ---- 0x830b0 `bne a0,s7` (0 / 0) .. jal __asan_set_shadow_00 0x830bc (shF + 0x1c, 1113) ---- *)
assert (SPOK10 : s5_spills_at W4 mem10 sp1 F sF nn)
by (apply (s5_spills_kept W3 W4 mem3); [intros a Ha; apply KP10; unfold s5_prot; lia | exact SP3]).
pose proof (s5_entry W4 regs10 mem10 2060 sp1 F sF nn R10_9 R10_19 ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) SPOK10) as HS.
remember (Eimg (Ereg regs10 (s5_extra nn F))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs10 r)
by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HAG10 : env_agree 32 (Ereg regs10 (s5_extra nn F)) E)
by (subst E; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
pin HS (10%bv : bv 5) (SLit 0) R10_10'. pin HS (23%bv : bv 5) (SLit 0) R10_23.
paj_run_shc RUNP RUNC HS HJ10.
{ intros a (r & Hin & Ha).
  lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
  cbn [In] in Hin. destruct Hin as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. lia. }
rename ms into msT, HJ10 into HJT, HFr into HFrT. clear HF HG.
prreg HS (10%bv : bv 5) Ta0. prreg HS (11%bv : bv 5) Ta1. prreg HS (1%bv : bv 5) Tra.
assert (RKTl : forall r, In r [2; 3; 4; 8; 9; 19; 20; 22; 24]%bv -> getr (ms_regs msT) r = getr regs10 r).
{ intros x Hx. exact (regs_kept_of_st_ok SEGS E _ (restrict (w_H W4) msT) regs10 (s5_extra nn F)
  [2; 3; 4; 8; 9; 19; 20; 22; 24]%bv HS HAG10 eq_refl x Hx). }
assert (RKT : s5_rk sp0 sp1 sF body np (ms_regs msT))
by (apply (s5_rk_kept _ _ _ _ _ regs10); [intros r Hr; apply RKTl; cbn in Hr |- *; tauto | exact RK10]).
pose proof RKT as (RT2 & RT3 & RT4 & RT8 & RT9 & RT19 & RT20 & RT24).
assert (RT22 : getr (ms_regs msT) 22%bv = Z_to_bv 64 res).
{ rewrite (RKTl 22%bv ltac:(cbn; tauto)). transitivity (getr (ms_regs msS) 22%bv);
  [exact (HP10 22 ltac:(unfold acallee_saved; lia)) | rewrite (RKSl 22%bv ltac:(cbn; tauto))].
  transitivity (getr (ms_regs msR) 22%bv); [exact (HPr 22 ltac:(unfold acallee_saved; lia)) | exact RR22]. }
assert (KT : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W4) (ms_mem msT) a = aview SEGS (w_H W4) mem10 a).
{ intros a Ha. eapply (aview_kept_frame _ _ _ _ _ 0 HFrT); [lia | | exact Ha].
  intros b0 Hb0 (r & Hin & Hrb).
  lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
  cbn [In] in Hin. destruct Hin as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb. lia. }
clear HFrT.
assert (Ta0' : getr (ms_regs msT) 10%bv = YG0d.w64 (sF + 28))
by (rewrite Ta0; cbn [sv_denot]; rewrite (EE 19%nat 19%bv eq_refl), R10_19; unfold YG0d.w64;
    rewrite unsigned_lit_small by lia; reflexivity).
assert (Ta1' : getr (ms_regs msT) 11%bv = YG0d.w64 1113) by (rewrite Ta1; reflexivity).
pmkst HS.
clear HS HE HEI EE HAG10 Ta0 Ta1 E.
eapply SRr_bind.
{ eapply (AJSS (SIGMA SS___asan_set_shadow_00) 0 ASH00 W4 (ms_regs msT) (ms_mem msT) LLVMF_STK sp0 []
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(8, c_fpos cx)] ly4 S4 _ (ev + 1) 8 (c_fpos cx) (sF + 28) 1113
    (sp1 - sp0) (Z_to_bv 64 (BASE + 2076)) HJT).
  - left; reflexivity.
  - exact Ta0'.
  - exact Ta1'.
  - lia.
  - rewrite EFA4, HcidF. fold sF. lia.
  - rewrite EFA4, HcidF. fold sF. change (fs_frame_bytes 8 / 8) with 2048. lia.
  - unfold spZ at 1. rewrite RT2, unsigned_lit_small by lia. lia.
  - exact Hom.
  - lia.
  - rewrite Hes. lia.
  - exact RT3.
  - exact RT4.
  - exact Tra.
  - apply ret_ok_codeptr_v; [lia | reflexivity]. }
cbv beta. intros W11 c11 _ (-> & regs11 & mem11 & md11 & -> & HJ11 & HP11 & ROW0 & K11 & _).
assert (KP11 : forall a, s5_prot sp0 sp1 F sF a -> aview SEGS (w_H W4) mem11 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. rewrite K11.
  - rewrite KT by (destruct (PCLS a (or_introl Ha)) as [H|[H|[H|H]]]; lia). exact (KP10 a Ha).
  - destruct (PCLS a (or_introl Ha)) as [H|[H|[H|H]]]; lia.
  - unfold s5_prot in Ha. clear - Ha HFapp' HsFlt HsFhi Hsp1lo Hsp1rng C1. lia. }
assert (BF11 : forall i, 0 <= i < 8904 -> aview SEGS (w_H W4) mem11 (body + i) =
  if (832 <=? i) && (i <? 832 + 6) then aview SEGS (w_H W3) mem3 (F + 112 + (i - 832)) else Some (scene_tag i)).
{ intros i Hi. rewrite K11; [rewrite KT by lia; exact (BF10 i Hi) | lia | ].
  clear - Hi Hbapp HsFlt HsFhi Hnn8904. lia. }
pose proof (s5_rk_pres _ _ _ _ _ _ _ HP11 RKT) as RK11.
pose proof RK11 as (R11_2 & R11_3 & R11_4 & R11_8 & R11_9 & R11_19 & R11_20 & R11_24).
assert (R11_22 : getr regs11 22 = Z_to_bv 64 res)
by (transitivity (getr (ms_regs msT) 22%bv); [exact (HP11 22 ltac:(unfold acallee_saved; lia)) | exact RT22]).
clear KP10 BF10 KT.
(* ---- 0x830c0 .. jal __asan_memset 0x830d4 (expect + 4, 0, 8900) ---- *)
assert (SPOK11 : s5_spills_at W4 mem11 sp1 F sF nn)
by (apply (s5_spills_kept W3 W4 mem3); [intros a Ha; apply KP11; unfold s5_prot; lia | exact SP3]).
pose proof (s5_entry W4 regs11 mem11 2076 sp1 F sF nn R11_9 R11_19 ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) SPOK11) as HS.
remember (Eimg (Ereg regs11 (s5_extra nn F))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs11 r)
by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HAG11 : env_agree 32 (Ereg regs11 (s5_extra nn F)) E)
by (subst E; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E33u : ew E 33 = Z_to_bv 64 F)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs11 _ 1)).
paj_run_shc RUNP RUNC HS HJ11.
{ intros a (r & Hin & Ha).
  lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
  cbn [In] in Hin. destruct Hin as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. lia. }
rename ms into msU, HJ11 into HJU, HFr into HFrU. clear HF HG.
prreg HS (10%bv : bv 5) Ua0. prreg HS (11%bv : bv 5) Ua1. prreg HS (12%bv : bv 5) Ua2. prreg HS (1%bv : bv 5) Ura.
prreg HS (18%bv : bv 5) Us2.
assert (RKUl : forall r, In r [2; 3; 4; 8; 9; 19; 20; 22; 24]%bv -> getr (ms_regs msU) r = getr regs11 r).
{ intros x Hx. exact (regs_kept_of_st_ok SEGS E _ (restrict (w_H W4) msU) regs11 (s5_extra nn F)
  [2; 3; 4; 8; 9; 19; 20; 22; 24]%bv HS HAG11 eq_refl x Hx). }
assert (RKU : s5_rk sp0 sp1 sF body np (ms_regs msU))
by (apply (s5_rk_kept _ _ _ _ _ regs11); [intros r Hr; apply RKUl; cbn in Hr |- *; tauto | exact RK11]).
pose proof RKU as (RU2 & RU3 & RU4 & RU8 & RU9 & RU19 & RU20 & RU24).
assert (RU22 : getr (ms_regs msU) 22%bv = Z_to_bv 64 res) by (rewrite (RKUl 22%bv ltac:(cbn; tauto)); exact R11_22).
assert (RU18 : getr (ms_regs msU) 18%bv = Z_to_bv 64 (F + 224))
by (rewrite Us2; cbn [sv_denot]; rewrite E33u; rewrite ?unsigned_lit_small by lia; reflexivity).
assert (KU : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W4) (ms_mem msU) a = aview SEGS (w_H W4) mem11 a).
{ intros a Ha. eapply (aview_kept_frame _ _ _ _ _ 0 HFrU); [lia | | exact Ha].
  intros b0 Hb0 (r & Hin & Hrb).
  lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
  cbn [In] in Hin. destruct Hin as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb. lia. }
clear HFrU.
assert (Ua0' : getr (ms_regs msU) 10%bv = YG0d.w64 (F + 228))
by (rewrite Ua0; cbn [sv_denot]; rewrite E33u; unfold YG0d.w64; rewrite unsigned_lit_small by lia; reflexivity).
assert (Ua1' : getr (ms_regs msU) 11%bv = YG0d.w64 0) by (rewrite Ua1; reflexivity).
assert (Ua2' : getr (ms_regs msU) 12%bv = YG0d.w64 8900) by (rewrite Ua2; reflexivity).
pmkst HS.
clear HS HE HEI EE HAG11 Ua0 Ua1 Ua2 Us2 E33u E.
assert (HF8d : F mod 8 = 0).
{ destruct (proj1 (Z.mod_divide F 32 ltac:(lia)) HF32) as [q Hq]. rewrite Hq.
  replace (q * 32) with ((4 * q) * 8) by lia. apply Z_mod_mult. }
(* the shadow byte of an address of the expect object lies in the row set_shadow_00 zeroed *)
assert (SHE : forall x, F + 224 <= x < F + 9128 -> SHADOW_OFF + x / 8 = sF + 28 + ((x - F) / 8 - 28) /\ 0 <= (x - F) / 8 - 28 < 1113).
{ intros x Hx.
  assert (Ex : x / 8 = F / 8 + (x - F) / 8).
  { replace x with ((F / 8) * 8 + (x - F)) at 1 by (pose proof (Z.div_mod F 8 ltac:(lia)); lia).
    rewrite Z.div_add_l by lia. reflexivity. }
  split; [unfold sF, shadow_addr; rewrite Ex; lia|].
  split; [apply Z.le_0_sub; apply Z.div_le_lower_bound; lia | ].
  assert ((x - F) / 8 < 1141) by (apply Z.div_lt_upper_bound; lia). lia. }
eapply SRr_bind.
{ eapply (aj_intrin_at (SK := scene_sink_head) SEGS B LAWS pa_segs_low OSet (SIGMA SS___asan_memset) AMEMSET W4 (ms_regs msU) (ms_mem msU)
    LLVMF_STK sp0 [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(8, c_fpos cx)] ly4 S4 _ (ev + 1)
    (F + 228) 0 8900 (sp1 - sp0) (Z_to_bv 64 (BASE + 2100)) HJU).
  - exact Ua0'.
  - exact Ua1'.
  - exact Ua2'.
  - lia.
  - lia.
  - lia.
  - unfold spZ at 1. rewrite RU2, unsigned_lit_small by lia. lia.
  - exact Hom.
  - lia.
  - rewrite Hes. lia.
  - exact RU3.
  - exact RU4.
  - exact Ura.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a Ha. split; [| rewrite Hes; lia].
    right. right. right. exists 8, (c_fpos cx). split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
    rewrite EFA4, HcidF. change (fs_frame_bytes 8) with 16384. lia.
  - apply (amem_range_sub_app F 16384 (F + 228) 8900 HFapp HFceil); lia.
  - intros x Hx. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr.
    destruct (SHE x ltac:(lia)) as (Es & Hk). rewrite Es. rewrite KU by lia. exact (ROW0 _ Hk).
  - intros _. eapply (shadow_hull_vis_of_frame SEGS B LAWS ly4 S4 W4 (ms_mem msU) _ 8 (c_fpos cx) (F + 228) 8900 (proj1 HJU) Hfin4);
    [rewrite EFA4, HcidF; lia | rewrite EFA4, HcidF; change (fs_frame_bytes 8) with 16384; lia | lia].
  - exact I. }
cbv beta. intros W12 c12 _ (-> & regs12 & mem12 & md12 & -> & HJ12 & HP12 & Ha012 & ZERO & K12 & _).
pose proof (s5_rk_pres _ _ _ _ _ _ _ HP12 RKU) as RK12.
pose proof RK12 as (R12_2 & R12_3 & R12_4 & R12_8 & R12_9 & R12_19 & R12_20 & R12_24).
assert (R12_18 : getr regs12 18 = Z_to_bv 64 (F + 224))
by (transitivity (getr (ms_regs msU) 18%bv); [exact (HP12 18 ltac:(unfold acallee_saved; lia)) | exact RU18]).
assert (R12_22 : getr regs12 22 = Z_to_bv 64 res)
by (transitivity (getr (ms_regs msU) 22%bv); [exact (HP12 22 ltac:(unfold acallee_saved; lia)) | exact RU22]).
assert (KP12 : forall a, s5_prot sp0 sp1 F sF a -> aview SEGS (w_H W4) mem12 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. pose proof (PCLS a (or_introl Ha)) as HC. pose proof (PE a (or_introl Ha)) as HE'. pose proof (PW a (or_introl Ha)) as HW.
  rewrite K12; [| destruct HC as [H|[H|[H|H]]]; lia | lia | rewrite Hes; rewrite Has in HW; lia].
  rewrite KU by (destruct HC as [H|[H|[H|H]]]; lia). exact (KP11 a Ha). }
assert (KR12 : forall a, s5_row sF a -> aview SEGS (w_H W4) mem12 a = aview SEGS (w_H W4) mem11 a).
{ intros a Ha. pose proof (PCLS a (or_intror Ha)) as HC. pose proof (PE a (or_intror Ha)) as HE'. pose proof (PW a (or_intror Ha)) as HW.
  rewrite K12; [| destruct HC as [H|[H|[H|H]]]; lia | lia | rewrite Hes; rewrite Has in HW; lia].
  apply KU. destruct HC as [H|[H|[H|H]]]; lia. }
assert (BF12 : forall i, 0 <= i < 8904 -> aview SEGS (w_H W4) mem12 (body + i) =
  if (832 <=? i) && (i <? 832 + 6) then aview SEGS (w_H W3) mem3 (F + 112 + (i - 832)) else Some (scene_tag i)).
{ intros i Hi. rewrite K12; [| lia | lia | rewrite Hes; lia]. rewrite KU by lia. exact (BF11 i Hi). }
assert (EXP12 : forall i, 4 <= i < 8904 -> aview SEGS (w_H W4) mem12 (F + 224 + i) = Some 0).
{ intros i Hi. replace (F + 224 + i) with (F + 228 + (i - 4)) by lia. rewrite (ZERO (i - 4) ltac:(lia)). reflexivity. }
pose proof (proj1 HJ12) as HAR12.
destruct (al_frames _ _ LAWS ly4 S4 W4 mem12 md12 8 (c_fpos cx) HAR12 Hfin4) as (_ & _ & HFp12 & _).
rewrite EFA4, HcidF in HFp12. change (fs_frame_bytes 8) with 16384 in HFp12.
assert (SPOK12 : s5_spills_at W4 mem12 sp1 F sF nn)
by (apply (s5_spills_kept W3 W4 mem3); [intros a Ha; apply KP12; unfold s5_prot; lia | exact SP3]).
clear ZERO K12 KP11 BF11 KU.
(* ---- 0x830d8 .. the three `sw` tags with their UBSan guards, then jal __asan_memcpy 0x83130 ---- *)
pose proof (s5_entry_t W4 regs12 mem12 2100 sp1 F sF nn R12_9 R12_19 R12_18 ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros a Ha; exact (proj1 (HFp12 a ltac:(lia)))) SPOK12) as HS.
remember (Eimg (Ereg regs12 (s5_extra nn F))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs12 r)
by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HAG12 : env_agree 32 (Ereg regs12 (s5_extra nn F)) E)
by (subst E; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E33t : ew E 33 = Z_to_bv 64 F)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs12 _ 1)).
assert (U18t : bv_unsigned (ew E 18) = F + 224)
by (rewrite (EE 18%nat 18%bv eq_refl), R12_18; apply unsigned_lit_small; lia).
assert (U33t : bv_unsigned (ew E 33) = F) by (rewrite E33t; apply unsigned_lit_small; lia).
assert (F18 : afact_ok E 18 (mkAF 4096 (2 ^ 47) 0))
by (unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U18t; rewrite Z.pow_0_r, Z.mod_1_r; lia).
assert (F33 : afact_ok E 33 (mkAF 4096 (2 ^ 47) 0))
by (unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U33t; rewrite Z.pow_0_r, Z.mod_1_r; lia).
addf HS 18%nat (mkAF 4096 (2 ^ 47) 0) F18. addf HS 33%nat (mkAF 4096 (2 ^ 47) 0) F33.
paj_run_shc RUNP RUNC HS HJ12.
{ intros a (r & Hin & Ha).
  lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
  cbn [In] in Hin. destruct Hin as [<- | [<- | [<- | [<- | []]]]];
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; [lia | rewrite U18t in Ha | rewrite U33t in Ha | rewrite U33t in Ha];
  right; right; right; exists 8, (c_fpos cx); (split; [left; reflexivity|]); left; unfold in_zr; cbn [fst snd];
  rewrite EFA4, HcidF; change (fs_frame_bytes 8) with 16384; lia. }
rename ms into msV, HJ12 into HJV, HFr into HFrV. clear HF HG.
(* the twelve tag bytes, read out of the three store regions of the post state *)
pose proof (st_ok_region_nth _ _ _ 1 _ HS eq_refl) as RG1.
pose proof (st_ok_region_nth _ _ _ 2 _ HS eq_refl) as RG2.
pose proof (st_ok_region_nth _ _ _ 3 _ HS eq_refl) as RG3.
cbn [ms_mem restrict] in RG1, RG2, RG3.
pose proof (field_of_region_any E _ 18 (F + 224) _ _ _ _ _ 0 4%N _ RG1 U18t (or_introl eq_refl) ltac:(lia)) as VT1.
pose proof (field_of_region_any E _ 33 F _ _ _ _ _ 1096 4%N _ RG2 U33t (or_introl eq_refl) ltac:(lia)) as VT2.
pose proof (field_of_region_any E _ 33 F _ _ _ _ _ 1116 4%N _ RG3 U33t (or_introl eq_refl) ltac:(lia)) as VT3.
change (N.to_nat 4) with 4%nat in VT1, VT2, VT3.
rewrite (ltac:(vm_compute; reflexivity) : bv_unsigned (sv_denot E (SLit 875770417)) mod 2 ^ (8 * Z.of_N 4) = 875770417) in VT1.
rewrite (ltac:(vm_compute; reflexivity) : bv_unsigned (sv_denot E (SLit 1347639635)) mod 2 ^ (8 * Z.of_N 4) = 1347639635) in VT2.
rewrite (ltac:(vm_compute; reflexivity) : bv_unsigned (sv_denot E (SLit 1313162067)) mod 2 ^ (8 * Z.of_N 4) = 1313162067) in VT3.
rewrite Z.add_0_r in VT1.
assert (T1 : forall k, 0 <= k < 4 -> aview SEGS (w_H W4) (ms_mem msV) (F + 224 + k) = Some (scene_tag k)).
{ intros k Hk. rewrite (val_mem_aview_byte4 SEGS (w_H W4) (ms_mem msV) (F + 224) 875770417 k VT1 ltac:(lia) Hk).
  assert (Hk' : k = 0 \/ k = 1 \/ k = 2 \/ k = 3) by lia.
  destruct Hk' as [-> | [-> | [-> | ->]]]; vm_compute; reflexivity. }
assert (T2 : forall k, 0 <= k < 4 -> aview SEGS (w_H W4) (ms_mem msV) (F + 224 + (872 + k)) = Some (scene_tag (872 + k))).
{ intros k Hk. replace (F + 224 + (872 + k)) with (F + 1096 + k) by lia.
  rewrite (val_mem_aview_byte4 SEGS (w_H W4) (ms_mem msV) (F + 1096) 1347639635 k VT2 ltac:(lia) Hk).
  assert (Hk' : k = 0 \/ k = 1 \/ k = 2 \/ k = 3) by lia.
  destruct Hk' as [-> | [-> | [-> | ->]]]; vm_compute; reflexivity. }
assert (T3 : forall k, 0 <= k < 4 -> aview SEGS (w_H W4) (ms_mem msV) (F + 224 + (892 + k)) = Some (scene_tag (892 + k))).
{ intros k Hk. replace (F + 224 + (892 + k)) with (F + 1116 + k) by lia.
  rewrite (val_mem_aview_byte4 SEGS (w_H W4) (ms_mem msV) (F + 1116) 1313162067 k VT3 ltac:(lia) Hk).
  assert (Hk' : k = 0 \/ k = 1 \/ k = 2 \/ k = 3) by lia.
  destruct Hk' as [-> | [-> | [-> | ->]]]; vm_compute; reflexivity. }
clear RG1 RG2 RG3 VT1 VT2 VT3.
assert (KV : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 224 <= a < F + 228) -> ~ (F + 1096 <= a < F + 1100) -> ~ (F + 1116 <= a < F + 1120) ->
  aview SEGS (w_H W4) (ms_mem msV) a = aview SEGS (w_H W4) mem12 a).
{ intros a Ha N1 N2 N3. apply (aview_eq_of SEGS). apply HFrV. rewrite unsigned_lit_small by lia.
  intros (r & Hin & Hrb).
  lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
  cbn [In] in Hin. destruct Hin as [<- | [<- | [<- | [<- | []]]]];
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb; [lia | rewrite U18t in Hrb; lia | rewrite U33t in Hrb; lia | rewrite U33t in Hrb; lia]. }
clear HFrV.
prreg HS (10%bv : bv 5) Va0. prreg HS (11%bv : bv 5) Va1. prreg HS (12%bv : bv 5) Va2. prreg HS (1%bv : bv 5) Vra.
prreg HS (18%bv : bv 5) Vs2. prreg HS (21%bv : bv 5) Vs5.
assert (RKVl : forall r, In r [2; 3; 4; 8; 9; 19; 20; 22; 24]%bv -> getr (ms_regs msV) r = getr regs12 r).
{ intros x Hx. exact (regs_kept_of_st_ok SEGS E _ (restrict (w_H W4) msV) regs12 (s5_extra nn F)
  [2; 3; 4; 8; 9; 19; 20; 22; 24]%bv HS HAG12 eq_refl x Hx). }
assert (RKV : s5_rk sp0 sp1 sF body np (ms_regs msV))
by (apply (s5_rk_kept _ _ _ _ _ regs12); [intros r Hr; apply RKVl; cbn in Hr |- *; tauto | exact RK12]).
pose proof RKV as (RV2 & RV3 & RV4 & RV8 & RV9 & RV19 & RV20 & RV24).
assert (RV22 : getr (ms_regs msV) 22%bv = Z_to_bv 64 res) by (rewrite (RKVl 22%bv ltac:(cbn; tauto)); exact R12_22).
assert (RV18 : getr (ms_regs msV) 18%bv = Z_to_bv 64 (F + 224))
by (rewrite Vs2; cbn [sv_denot]; rewrite E33t; rewrite ?unsigned_lit_small by lia; reflexivity).
assert (RV21 : getr (ms_regs msV) 21%bv = Z_to_bv 64 body)
by (rewrite Vs5; cbn [sv_denot]; rewrite (EE 20%nat 20%bv eq_refl), R12_20; unfold YG0d.w64;
    rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; first [reflexivity | rewrite unsigned_lit_small by lia; reflexivity]).
assert (Va0' : getr (ms_regs msV) 10%bv = YG0d.w64 (F + 1056))
by (rewrite Va0; cbn [sv_denot]; rewrite E33t; unfold YG0d.w64; rewrite unsigned_lit_small by lia; reflexivity).
assert (Va1' : getr (ms_regs msV) 11%bv = YG0d.w64 (F + 112))
by (rewrite Va1; cbn [sv_denot]; rewrite E33t; unfold YG0d.w64; rewrite unsigned_lit_small by lia; reflexivity).
assert (Va2' : getr (ms_regs msV) 12%bv = YG0d.w64 6) by (rewrite Va2; reflexivity).
pmkst HS.
clear HS HE HEI EE HAG12 Va0 Va1 Va2 Vs2 Vs5 F18 F33 E33t U18t U33t E.
assert (KPV : forall a, s5_prot sp0 sp1 F sF a -> aview SEGS (w_H W4) (ms_mem msV) a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. pose proof (PE a (or_introl Ha)) as HE'. pose proof (PCLS a (or_introl Ha)) as HC.
  rewrite KV by (destruct HC as [H|[H|[H|H]]]; lia). exact (KP12 a Ha). }
assert (KRV : forall a, s5_row sF a -> aview SEGS (w_H W4) (ms_mem msV) a = aview SEGS (w_H W4) mem11 a).
{ intros a Ha. pose proof (PE a (or_intror Ha)) as HE'. pose proof (PCLS a (or_intror Ha)) as HC.
  rewrite KV by (destruct HC as [H|[H|[H|H]]]; lia). exact (KR12 a Ha). }
assert (BFV : forall i, 0 <= i < 8904 -> aview SEGS (w_H W4) (ms_mem msV) (body + i) =
  if (832 <=? i) && (i <? 832 + 6) then aview SEGS (w_H W3) mem3 (F + 112 + (i - 832)) else Some (scene_tag i)).
{ intros i Hi. rewrite KV by lia. exact (BF12 i Hi). }
(* ---- __asan_memcpy(expect + 0x340, mac, 6) at 0x83130 ---- *)
destruct (MACOK _ _ _ HJV KPV) as (MV1 & MV2 & MV3 & MV4).
eapply SRr_bind.
{ eapply (aj_intrin_at (SK := scene_sink_head) SEGS B LAWS pa_segs_low OCpy (SIGMA SS___asan_memcpy) AMEMCPY W4 (ms_regs msV) (ms_mem msV)
    LLVMF_STK sp0 [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(8, c_fpos cx)] ly4 S4 _ (ev + 1)
    (F + 1056) (F + 112) 6 (sp1 - sp0) (Z_to_bv 64 (BASE + 2192)) HJV).
  - exact Va0'.
  - exact Va1'.
  - exact Va2'.
  - lia.
  - lia.
  - lia.
  - unfold spZ at 1. rewrite RV2, unsigned_lit_small by lia. lia.
  - exact Hom.
  - lia.
  - rewrite Hes. lia.
  - exact RV3.
  - exact RV4.
  - exact Vra.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a Ha. split; [| rewrite Hes; lia].
    right. right. right. exists 8, (c_fpos cx). split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
    rewrite EFA4, HcidF. change (fs_frame_bytes 8) with 16384. lia.
  - apply (amem_range_sub_app F 16384 (F + 1056) 6 HFapp HFceil); lia.
  - intros x Hx. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr.
    destruct (SHE x ltac:(lia)) as (Es & Hk). rewrite Es. rewrite KRV by (unfold s5_row; lia). exact (ROW0 _ Hk).
  - intros _. eapply (shadow_hull_vis_of_frame SEGS B LAWS ly4 S4 W4 (ms_mem msV) _ 8 (c_fpos cx) (F + 1056) 6 (proj1 HJV) Hfin4);
    [rewrite EFA4, HcidF; lia | rewrite EFA4, HcidF; change (fs_frame_bytes 8) with 16384; lia | lia].
  - cbv iota. split; [lia|]. split; [lia|]. split.
    { intros a Ha. split; [replace a with (F + 112 + (a - (F + 112))) by lia; apply MV1; lia |].
      unfold spZ at 1. rewrite RV2, unsigned_lit_small by lia. rewrite Hes. lia. }
    split; [lia|]. split; [exact MV2|]. split; [exact MV3 | intros _; exact MV4]. }
cbv beta. intros W13 c13 _ (-> & regs13 & mem13 & md13 & -> & HJ13 & HP13 & Ha013 & CPY & K13 & _).
pose proof (s5_rk_pres _ _ _ _ _ _ _ HP13 RKV) as RK13.
pose proof RK13 as (R13_2 & R13_3 & R13_4 & R13_8 & R13_9 & R13_19 & R13_20 & R13_24).
assert (R13_22 : getr regs13 22 = Z_to_bv 64 res)
by (transitivity (getr (ms_regs msV) 22%bv); [exact (HP13 22 ltac:(unfold acallee_saved; lia)) | exact RV22]).
assert (R13_21 : getr regs13 21 = Z_to_bv 64 body)
by (transitivity (getr (ms_regs msV) 21%bv); [exact (HP13 21 ltac:(unfold acallee_saved; lia)) | exact RV21]).
assert (R13_18 : getr regs13 18 = Z_to_bv 64 (F + 224))
by (transitivity (getr (ms_regs msV) 18%bv); [exact (HP13 18 ltac:(unfold acallee_saved; lia)) | exact RV18]).
(* the expect object after the last write: the scene image, mac at 832 *)
assert (EXPF : forall i, 0 <= i < 8904 -> aview SEGS (w_H W4) mem13 (F + 224 + i) =
  if (832 <=? i) && (i <? 832 + 6) then aview SEGS (w_H W3) mem3 (F + 112 + (i - 832)) else Some (scene_tag i)).
{ intros i Hi. destruct ((832 <=? i) && (i <? 832 + 6)) eqn:Hm.
  - apply andb_prop in Hm as [Hm1 Hm2]. apply Z.leb_le in Hm1. apply Z.ltb_lt in Hm2.
    replace (F + 224 + i) with (F + 1056 + (i - 832)) by lia. rewrite (CPY (i - 832) ltac:(lia)).
    apply KPV. unfold s5_prot. lia.
  - assert (Hni : i < 832 \/ 838 <= i)
    by (apply andb_false_iff in Hm as [Hx | Hx]; [apply Z.leb_gt in Hx | apply Z.ltb_ge in Hx]; lia).
    rewrite K13 by (rewrite ?Hes; lia).
    destruct (Z_lt_dec i 4) as [H4 | H4]; [exact (T1 i ltac:(lia))|].
    destruct (Z_lt_dec i 872) as [H5 | H5].
    { rewrite KV by lia. rewrite (EXP12 i ltac:(lia)). rewrite s5_tag0; [reflexivity | cbn [In]; lia]. }
    destruct (Z_lt_dec i 876) as [H6 | H6].
    { pose proof (T2 (i - 872) ltac:(lia)) as Ht. replace (872 + (i - 872)) with i in Ht by lia. exact Ht. }
    destruct (Z_lt_dec i 892) as [H7 | H7].
    { rewrite KV by lia. rewrite (EXP12 i ltac:(lia)). rewrite s5_tag0; [reflexivity | cbn [In]; lia]. }
    destruct (Z_lt_dec i 896) as [H8 | H8].
    { pose proof (T3 (i - 892) ltac:(lia)) as Ht. replace (892 + (i - 892)) with i in Ht by lia. exact Ht. }
    rewrite KV by lia. rewrite (EXP12 i ltac:(lia)). rewrite s5_tag0; [reflexivity | cbn [In]; lia]. }
assert (BF13 : forall i, 0 <= i < 8904 -> aview SEGS (w_H W4) mem13 (body + i) =
  if (832 <=? i) && (i <? 832 + 6) then aview SEGS (w_H W3) mem3 (F + 112 + (i - 832)) else Some (scene_tag i)).
{ intros i Hi. rewrite K13 by (rewrite ?Hes; lia). exact (BFV i Hi). }
assert (KP13 : forall a, s5_prot sp0 sp1 F sF a -> aview SEGS (w_H W4) mem13 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. pose proof (PE a (or_introl Ha)) as HE'. pose proof (PCLS a (or_introl Ha)) as HC. pose proof (PW a (or_introl Ha)) as HW.
  rewrite K13; [exact (KPV a Ha) | destruct HC as [H|[H|[H|H]]]; lia | lia | rewrite Hes; rewrite Has in HW; lia]. }
assert (KR13 : forall a, s5_row sF a -> aview SEGS (w_H W4) mem13 a = aview SEGS (w_H W4) mem11 a).
{ intros a Ha. pose proof (PE a (or_intror Ha)) as HE'. pose proof (PCLS a (or_intror Ha)) as HC. pose proof (PW a (or_intror Ha)) as HW.
  rewrite K13; [exact (KRV a Ha) | destruct HC as [H|[H|[H|H]]]; lia | lia | rewrite Hes; rewrite Has in HW; lia]. }
assert (SP13 : s5_spills_at W4 mem13 sp1 F sF nn)
by (apply (s5_spills_kept W3 W4 mem3); [intros a Ha; apply KP13; unfold s5_prot; lia | exact SP3]).
clear T1 T2 T3 KV KPV KRV BFV CPY K13 EXP12 BF12 KP12 KR12 MV1 MV2 MV3 MV4.
(* ---- 0x83134 .. jal __wrap_bcmp 0x83144 (body vs expect, 8904 bytes) ---- *)
pose proof (s5_entry W4 regs13 mem13 2192 sp1 F sF nn R13_9 R13_19 ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) SP13) as HS.
remember (Eimg (Ereg regs13 (s5_extra nn F))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs13 r)
by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HAG13 : env_agree 32 (Ereg regs13 (s5_extra nn F)) E)
by (subst E; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
paj_run_shc RUNP RUNC HS HJ13.
{ intros a (r & Hin & Ha).
  lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
  cbn [In] in Hin. destruct Hin as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. lia. }
rename ms into msX, HJ13 into HJX, HFr into HFrX. clear HF HG.
prreg HS (10%bv : bv 5) Xa0. prreg HS (11%bv : bv 5) Xa1. prreg HS (12%bv : bv 5) Xa2. prreg HS (1%bv : bv 5) Xra.
assert (RKXl : forall r, In r [2; 3; 4; 8; 9; 19; 20; 22; 24]%bv -> getr (ms_regs msX) r = getr regs13 r).
{ intros x Hx. exact (regs_kept_of_st_ok SEGS E _ (restrict (w_H W4) msX) regs13 (s5_extra nn F)
  [2; 3; 4; 8; 9; 19; 20; 22; 24]%bv HS HAG13 eq_refl x Hx). }
assert (RKX : s5_rk sp0 sp1 sF body np (ms_regs msX))
by (apply (s5_rk_kept _ _ _ _ _ regs13); [intros r Hr; apply RKXl; cbn in Hr |- *; tauto | exact RK13]).
pose proof RKX as (RX2 & RX3 & RX4 & RX8 & RX9 & RX19 & RX20 & RX24).
assert (RX22 : getr (ms_regs msX) 22%bv = Z_to_bv 64 res) by (rewrite (RKXl 22%bv ltac:(cbn; tauto)); exact R13_22).
assert (KX : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W4) (ms_mem msX) a = aview SEGS (w_H W4) mem13 a).
{ intros a Ha. eapply (aview_kept_frame _ _ _ _ _ 0 HFrX); [lia | | exact Ha].
  intros b0 Hb0 (r & Hin & Hrb).
  lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
  cbn [In] in Hin. destruct Hin as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb. lia. }
clear HFrX.
assert (Xa0' : getr (ms_regs msX) 10%bv = YG0d.w64 body)
by (rewrite Xa0; cbn [sv_denot]; rewrite (EE 21%nat 21%bv eq_refl), R13_21; unfold YG0d.w64;
    rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; first [reflexivity | rewrite unsigned_lit_small by lia; reflexivity]).
assert (Xa1' : getr (ms_regs msX) 11%bv = YG0d.w64 (F + 224))
by (rewrite Xa1; cbn [sv_denot]; rewrite (EE 18%nat 18%bv eq_refl), R13_18; unfold YG0d.w64;
    rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; first [reflexivity | rewrite unsigned_lit_small by lia; reflexivity]).
assert (Xa2' : getr (ms_regs msX) 12%bv = YG0d.w64 8904) by (rewrite Xa2; reflexivity).
pmkst HS.
clear HS HE HEI EE HAG13 Xa0 Xa1 Xa2 E.
pose proof (proj1 HJX) as HARX.
destruct (al_frames _ _ LAWS ly4 S4 W4 (ms_mem msX) _ 8 (c_fpos cx) HARX Hfin4) as (_ & _ & HFpX & _).
rewrite EFA4, HcidF in HFpX. change (fs_frame_bytes 8) with 16384 in HFpX.
eapply SRr_bind.
{ destruct (BLK _ _ _ HJX body Hbody4 body 8904 ltac:(lia) ltac:(lia) ltac:(lia)) as (FX1 & FX2 & FX3 & FX4).
  assert (FY1 : forall i, 0 <= i < 8904 -> aview SEGS (w_H W4) (ms_mem msX) (F + 224 + i) <> None)
  by (intros i Hi; apply (aview_some_of_apresent SEGS); exact (proj1 (HFpX (F + 224 + i) ltac:(lia)))).
  assert (FY3 : range_addressable (aview SEGS (w_H W4) (ms_mem msX)) SHADOW_OFF (F + 224) 8904).
  { intros x Hx. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr.
    destruct (SHE x ltac:(lia)) as (Es & Hk). rewrite Es. rewrite KX by lia. rewrite KR13 by (unfold s5_row; lia).
    exact (ROW0 _ Hk). }
  assert (FY4 : shadow_hull_vis (aview SEGS (w_H W4) (ms_mem msX)) (F + 224) 8904)
  by (eapply (shadow_hull_vis_of_frame SEGS B LAWS ly4 S4 W4 (ms_mem msX) _ 8 (c_fpos cx) (F + 224) 8904 HARX Hfin4);
      [rewrite EFA4, HcidF; lia | rewrite EFA4, HcidF; change (fs_frame_bytes 8) with 16384; lia | lia]).
  eapply (BCMP (ms_regs msX) (ms_mem msX) _ body (F + 224) 8904 (Z_to_bv 64 (BASE + 2212)) HJX Xa0' Xa1' Xa2');
  [lia | lia | lia | lia | lia | unfold spZ; rewrite RX2; apply unsigned_lit_small; lia | exact RX3 | exact RX4 | exact Xra
  | apply ret_ok_codeptr_v; [lia | reflexivity] | exact FX1 | exact FY1 | exact FX2
  | apply (amem_range_sub_app F 16384 (F + 224) 8904 HFapp HFceil); lia
  | exact FX3 | exact FX4 | exact FY3 | intros _; exact FY4]. }
cbv beta. intros W14 c14 _ (-> & regs14 & mem14 & md14 & v14 & -> & HJ14 & HP14 & R14_10 & Hcmp14 & K14).
assert (Hv14 : v14 = YG0d.w64 0).
{ apply (proj2 Hcmp14). intros i Hi. rewrite !KX by lia. rewrite (BF13 i Hi), (EXPF i Hi). reflexivity. }
rewrite Hv14 in R14_10. clear Hv14 Hcmp14.
pose proof (s5_rk_pres _ _ _ _ _ _ _ HP14 RKX) as RK14.
pose proof RK14 as (R14_2 & R14_3 & R14_4 & R14_8 & R14_9 & R14_19 & R14_20 & R14_24).
assert (R14_22 : getr regs14 22 = Z_to_bv 64 res)
by (transitivity (getr (ms_regs msX) 22%bv); [exact (HP14 22 ltac:(unfold acallee_saved; lia)) | exact RX22]).
assert (KP14 : forall a, s5_prot sp0 sp1 F sF a -> aview SEGS (w_H W4) mem14 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. pose proof (PCLS a (or_introl Ha)) as HC. pose proof (PW a (or_introl Ha)) as HW.
  rewrite K14; [| destruct HC as [H|[H|[H|H]]]; lia | rewrite Hes; rewrite Has in HW; lia].
  rewrite KX by (destruct HC as [H|[H|[H|H]]]; lia). exact (KP13 a Ha). }
assert (KR14 : forall a, s5_row sF a -> aview SEGS (w_H W4) mem14 a = aview SEGS (w_H W4) mem11 a).
{ intros a Ha. pose proof (PCLS a (or_intror Ha)) as HC. pose proof (PW a (or_intror Ha)) as HW.
  rewrite K14; [| destruct HC as [H|[H|[H|H]]]; lia | rewrite Hes; rewrite Has in HW; lia].
  rewrite KX by (destruct HC as [H|[H|[H|H]]]; lia). exact (KR13 a Ha). }
assert (SP14 : s5_spills_at W4 mem14 sp1 F sF nn)
by (apply (s5_spills_kept W3 W4 mem3); [intros a Ha; apply KP14; unfold s5_prot; lia | exact SP3]).
clear KX K14 KP13 KR13 BF13 EXPF.
(* ---- 0x83148 `bnez a0` (a0 = 0) .. jal __asan_set_shadow_f8 0x83154 (shF + 0x1c, 1113) ---- *)
pose proof (s5_entry W4 regs14 mem14 2212 sp1 F sF nn R14_9 R14_19 ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) SP14) as HS.
remember (Eimg (Ereg regs14 (s5_extra nn F))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs14 r)
by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HAG14 : env_agree 32 (Ereg regs14 (s5_extra nn F)) E)
by (subst E; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (R14_10' : getr regs14 10%bv = Z_to_bv 64 0) by (rewrite R14_10; reflexivity).
pin HS (10%bv : bv 5) (SLit 0) R14_10'.
paj_run_shc RUNP RUNC HS HJ14.
{ intros a (r & Hin & Ha).
  lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
  cbn [In] in Hin. destruct Hin as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. lia. }
rename ms into msY, HJ14 into HJY, HFr into HFrY. clear HF HG.
prreg HS (10%bv : bv 5) Ya0. prreg HS (11%bv : bv 5) Ya1. prreg HS (1%bv : bv 5) Yra.
assert (RKYl : forall r, In r [2; 3; 4; 8; 9; 19; 20; 22; 24]%bv -> getr (ms_regs msY) r = getr regs14 r).
{ intros x Hx. exact (regs_kept_of_st_ok SEGS E _ (restrict (w_H W4) msY) regs14 (s5_extra nn F)
  [2; 3; 4; 8; 9; 19; 20; 22; 24]%bv HS HAG14 eq_refl x Hx). }
assert (RKY : s5_rk sp0 sp1 sF body np (ms_regs msY))
by (apply (s5_rk_kept _ _ _ _ _ regs14); [intros r Hr; apply RKYl; cbn in Hr |- *; tauto | exact RK14]).
pose proof RKY as (RY2 & RY3 & RY4 & RY8 & RY9 & RY19 & RY20 & RY24).
assert (RY22 : getr (ms_regs msY) 22%bv = Z_to_bv 64 res) by (rewrite (RKYl 22%bv ltac:(cbn; tauto)); exact R14_22).
assert (KY : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W4) (ms_mem msY) a = aview SEGS (w_H W4) mem14 a).
{ intros a Ha. eapply (aview_kept_frame _ _ _ _ _ 0 HFrY); [lia | | exact Ha].
  intros b0 Hb0 (r & Hin & Hrb).
  lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
  cbn [In] in Hin. destruct Hin as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb. lia. }
clear HFrY.
assert (Ya0' : getr (ms_regs msY) 10%bv = YG0d.w64 (sF + 28))
by (rewrite Ya0; cbn [sv_denot]; rewrite (EE 19%nat 19%bv eq_refl), R14_19; unfold YG0d.w64;
    rewrite unsigned_lit_small by lia; reflexivity).
assert (Ya1' : getr (ms_regs msY) 11%bv = YG0d.w64 1113) by (rewrite Ya1; reflexivity).
pmkst HS.
clear HS HE HEI EE HAG14 Ya0 Ya1 E.
eapply SRr_bind.
{ eapply (AJSS (SIGMA SS___asan_set_shadow_f8) 0xf8 ASHF8 W4 (ms_regs msY) (ms_mem msY) LLVMF_STK sp0 []
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(8, c_fpos cx)] ly4 S4 _ (ev + 1) 8 (c_fpos cx) (sF + 28) 1113
    (sp1 - sp0) (Z_to_bv 64 (BASE + 2228)) HJY).
  - left; reflexivity.
  - exact Ya0'.
  - exact Ya1'.
  - lia.
  - rewrite EFA4, HcidF. fold sF. lia.
  - rewrite EFA4, HcidF. fold sF. change (fs_frame_bytes 8 / 8) with 2048. lia.
  - unfold spZ at 1. rewrite RY2, unsigned_lit_small by lia. lia.
  - exact Hom.
  - lia.
  - rewrite Hes. lia.
  - exact RY3.
  - exact RY4.
  - exact Yra.
  - apply ret_ok_codeptr_v; [lia | reflexivity]. }
cbv beta. intros W15 c15 _ (-> & regs15 & mem15 & md15 & -> & HJ15 & HP15 & ROWF & K15 & _).
pose proof (s5_rk_pres _ _ _ _ _ _ _ HP15 RKY) as RK15.
assert (R15_22 : getr regs15 22 = Z_to_bv 64 res)
by (transitivity (getr (ms_regs msY) 22%bv); [exact (HP15 22 ltac:(unfold acallee_saved; lia)) | exact RY22]).
assert (KP15 : forall a, s5_prot sp0 sp1 F sF a -> aview SEGS (w_H W4) mem15 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. pose proof (PCLS a (or_introl Ha)) as HC.
  rewrite K15; [| destruct HC as [H|[H|[H|H]]]; lia | unfold s5_prot in Ha; clear - Ha HFapp' HsFlt HsFhi Hsp1lo Hsp1rng C1; lia].
  rewrite KY by (destruct HC as [H|[H|[H|H]]]; lia). exact (KP14 a Ha). }
assert (Hbg : forall o, 28 <= o < 1141 -> aview SEGS (w_H W3) mem3 (sF + o) = Some 0xf8).
{ unfold sc_shbg in HSHBG. cbn [sg_sh_bg scene_geom_asan_ubsan] in HSHBG.
  pose proof (proj1 (Forall_forall _ _) HSHBG (0x1c, 0x475, 0xf8)
    ltac:(cbn [In]; right; right; right; right; left; reflexivity)) as Hb.
  cbn [fst snd] in Hb. unfold sc_shr in Hb. exact Hb. }
assert (KR15 : forall a, s5_row sF a -> aview SEGS (w_H W4) mem15 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. unfold s5_row in Ha. replace a with (sF + 28 + (a - sF - 28)) by lia.
  rewrite (ROWF (a - sF - 28) ltac:(lia)). replace (sF + 28 + (a - sF - 28)) with (sF + (a - sF)) by lia.
  rewrite (Hbg (a - sF) ltac:(lia)). reflexivity. }
exact (EXIT regs15 mem15 md15 HJ15 KP15 KR15 RK15 R15_22).
Qed.
End h.
End d.
Print Assumptions seg_S5_au.
