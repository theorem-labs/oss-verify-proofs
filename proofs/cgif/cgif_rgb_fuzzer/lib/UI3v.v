(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s YK0p.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ00 YQ07 YQ08.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 YI00 YI0f YI02 YI01 YI03 YI04
UI1e UI39 UI1i UI57 UI1h YI0x UI26 UO3n UO0e
YI07 YP14 YI08 YI0c YI0g UI3h UI3d UI4v UIZm UI3x.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Ltac jafter_stretch_keep HS k regs2 mem2 clob newpc idxs HS2 :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss ?ms =>
let rs := eval vm_compute in (pick (ss_mem ss) idxs) in
pose proof (st_ok_after_stretch segs k E ss ms regs2 mem2 rs newpc clob HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity) ltac:(submem_tac) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as HS2;
let ss2 := eval vm_compute in (ss_after_stretch ss rs k clob newpc) in
change (ss_after_stretch ss rs k clob newpc) with ss2 in HS2
end.
Definition E1_RETM : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0x64).
Definition E1_DRET : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0x13b0).
Lemma fp_of_eta : forall f : YK11.FPState, mkFP (@fp_regs f) (@fp_csr f) = f.
Proof. intros []. reflexivity. Qed.
Lemma fsd_step_keep : forall E ss ss' (ms : machine_state) fmt rs1 rs2 imm wz,
st_okF ubs2segs E ss ms ->
clookup ubs2tbl (ss_pc ss) = Some wz -> is_ecall (Z_to_bv 32 wz) = false ->
decode_any (Z_to_bv 32 wz) = Some (FStore fmt rs1 rs2 imm, 4) ->
sym_stepF ubs2segs ubs2tbl ss = SRun ss' ->
exists ms', RiscvSemantics.step ubs2segs ms = MachineOk ms' /\ st_okF ubs2segs E ss' ms' /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') /\ ms_fregs ms' = ms_fregs ms /\ ms_fcsr ms' = ms_fcsr ms.
Proof.
intros E ss ss' ms fmt rs1 rs2 imm wz HS Hlk Hec Hd H.
unfold sym_stepF in H. rewrite Hlk in H. cbv zeta in H. rewrite Hec, Hd in H. cbn [negb Z.eqb Pos.eqb] in H.
destruct (fp_exec ubs2segs ss (FStore fmt rs1 rs2 imm)) as [o|] eqn:Hx; [|cbn [fp_exec] in Hx; discriminate Hx].
destruct ms as [regs fregs pcv pend resv fcsr mem rom].
destruct HS as (Hfr & Hpc & Hpend & Hresv & Hfcsr & Hrom & Hregs & Hmem & HG); cbn in *.
subst pcv pend rom.
pose proof (ubs2tbl_ok (ss_pc ss) wz Hlk) as Hf.
rewrite (step_on_fetch ubs2segs _ (Z_to_bv 32 wz)) by exact Hf.
rewrite (decode_exec_compat ubs2segs). rewrite Hec, Hd.
assert (HR : forall r, rget (Core regs fregs (Z_to_bv 64 (ss_pc ss)) fcsr resv) r = sv_denot E (sr_get (ss_regs ss) r)).
{ intros r. rewrite rget_regs. apply Hregs. }
assert (HFg : forall r, fget (Core regs fregs (Z_to_bv 64 (ss_pc ss)) fcsr resv) r = sv_denot E (sfr_get (ss_fregs ss) r)).
{ intros r. apply (fget_fregs E). exact Hfr. }
cbn [fp_exec] in Hx.
cbv beta iota zeta delta
[interp_eff0 RiscvSemantics.width_bytes RiscvSemantics.width_bytesZ
Sem.exec Sem.load_val Sem.store_val
Sem.with_regs Sem.with_pc Sem.with_resv Sem.with_fregs Sem.with_fcsr Sem.fset Sem.fwrite Sem.accrue
Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv
ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom ms_fregs ms_fcsr].
rewrite ?rset_core; cbv beta iota zeta delta [Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv].
rewrite ?HR, ?HFg.
destruct (ss_resv ss) as [rv0|] eqn:Hrv; [injection Hx as <-; discriminate H|]. cbn in Hresv. subst resv.
remember (s_alu2 (ss_facts ss) ALU_ADD (sr_get (ss_regs ss) rs1) (SLit (bv_signed imm))) as a eqn:Ha.
destruct (addr_of a) as [[b off]|] eqn:Hao; [|injection Hx as <-; discriminate H].
remember (match fmt with FMT_S => SZ4 | FMT_D => SZ8 end) as sz eqn:Hszf.
destruct (sstore (ss_mem ss) b off sz (sfr_get (ss_fregs ss) rs2)) as [m'|] eqn:Hst;
injection Hx as <-; [|discriminate H]. injection H as <-.
pose proof (sstore_sound ubs2segs E mem _ _ _ _ _ m' Hmem Hst) as [Hok Hmem'].
assert (Haddr : (sv_denot E (sr_get (ss_regs ss) rs1) + sext 64 imm)%bv = Z_to_bv 64 (base_val E b + off)).
{ rewrite <- (addr_of_sound E (ss_facts ss) a b off HG Hao). subst a.
rewrite s_alu2_sound by exact HG. cbn [sv_denot]. rewrite sext64_lit. reflexivity. }
rewrite Haddr.
destruct fmt; subst sz; cbn [nbytes nbits] in Hok, Hmem';
cbv beta iota zeta delta [interp_eff0 RiscvSemantics.width_bytes];
rewrite Hok; unfold inval_resv;
cbv beta iota zeta delta [Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv];
rewrite ?st_bytes_32, ?st_bytes_64, write_to_mem_wbytes;
eexists; (split; [reflexivity|]);
(split; [apply st_okF_mach; cbn; auto; apply pc_plus4
| split; [cbn [ms_mem]; eapply store_region_frame; [exact Hmem| | cbn; lia] | split; reflexivity] ]).
all: unfold sstore in Hst; unfold st_bytes; rewrite length_zbytes; exact Hst.
Qed.
Definition E1_FSD : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0x38).
Definition E1_FLD : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0x13f0).
Definition E1_FLD3 : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0x13fc).
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition ss_E1 : sstate :=
mkSS PC_E1 sr_atoms
[ YQ0b.mkRegion (Some 2%nat) (-128) 0 (-128) 0 [] ;
YQ0b.mkRegion (Some 2%nat) (-5168) (-5002) (-5168) (-5002) [] ;
YQ0b.mkRegion (Some 10%nat) 0 RGB_SIZE 0 0 (obj_chunks_from LAY_Rgb 32) ]
None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + RGBA_STK) (2^63) 4); (10%nat, mkAF 4096 (CEIL_MAX - RGB_SIZE) 4);
(11%nat, mkAF (CEIL_MIN + RGBA_STK) (2^63 - 24) 3);
(39%nat, mkAF 0 65535 0); (40%nat, mkAF 0 65535 0); (43%nat, mkAF 0 (2^32 - 1) 0) ] [] []).
Section d.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Variables (L : layout) (A : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (r cfp g wfn ctx path attr gen loops W H bef beffmt cur : Z) (s : cgif_st) (N : Z).
Variables (img fmt fattr fgen delay : Z) (rest : list (Z * Z)).
Lemma SR_fsd : forall E ss ss' ms STK sp0 FP L0 A0 mem md Lc Ac mdc Q fm rs1 rs2 imm wz,
st_okF ubs2segs E ss ms ->
clookup ubs2tbl (ss_pc ss) = Some wz -> is_ecall (Z_to_bv 32 wz) = false ->
decode_any (Z_to_bv 32 wz) = Some (FStore fm rs1 rs2 imm, 4) ->
sym_stepF ubs2segs ubs2tbl ss = SRun ss' ->
journal ubs2_msyms MR STK sp0 FP L0 A0 mem md Lc Ac (ms_mem ms) mdc ->
wr_ok E (ss_mem ss) STK sp0 FP (blocks L0 A0) (blocks Lc Ac) ->
(forall ms', st_okF ubs2segs E ss' ms' -> journal ubs2_msyms MR STK sp0 FP L0 A0 mem md Lc Ac (ms_mem ms') mdc ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') -> ms_fregs ms' = ms_fregs ms -> ms_fcsr ms' = ms_fcsr ms ->
SR ubs2segs (mkCfg ms' mdc) Q) ->
SR ubs2segs (mkCfg ms mdc) Q.
Proof.
intros E ss ss' ms STK sp0 FP L0 A0 mem md Lc Ac mdc Q fm rs1 rs2 imm wz HS Hlk Hec Hd Hst HJ Hwr Hk.
destruct (fsd_step_keep E ss ss' ms fm rs1 rs2 imm wz HS Hlk Hec Hd Hst) as (ms' & Hstep & HS' & Hfr & Hf1 & Hf2).
assert (Hms : msteps ubs2segs ms ms') by (apply msteps_one; [destruct HS as (_ & _ & Hp & _); exact Hp | exact Hstep]).
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hl & _).
apply (SR_msteps ubs2segs ms ms' mdc Q Hh Hl Hms). apply Hk; [exact HS' | | exact Hfr | exact Hf1 | exact Hf2].
eapply (journal_exec ubs2_msyms MR LAWS IMG); [exact HJ | exact Hfr | apply (msteps_mem_grows ubs2segs); exact Hms | exact Hwr].
Qed.
Ltac fsd_go HS HJ wrtac :=
lazymatch type of HS with st_okF _ ?Ex ?ssx ?msx =>
let r := eval vm_compute in (sym_stepF ubs2segs ubs2tbl ssx) in
lazymatch r with SRun ?ss' =>
let w := eval vm_compute in (clookup ubs2tbl (ss_pc ssx)) in
lazymatch w with Some ?wz =>
let d := eval vm_compute in (decode_any (Z_to_bv 32 wz)) in
lazymatch d with Some (FStore ?fm ?a1 ?a2 ?im, _) =>
eapply (SR_fsd Ex ssx ss' msx _ _ _ _ _ _ _ _ _ _ _ fm a1 a2 im wz HS
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HJ); [wrtac |]
end end end end.
Definition SAVE_CHUNKS : list YQ0b.chunk :=
[ mkChunk (-128) (CVal 8 (SOff 62 0)); mkChunk (-120) (CVal 8 (SOff 53 0)); mkChunk (-112) (CVal 8 (SOff 52 0));
mkChunk (-104) (CVal 8 (SOff 27 0)); mkChunk (-96) (CVal 8 (SOff 26 0)); mkChunk (-88) (CVal 8 (SOff 25 0));
mkChunk (-80) (CVal 8 (SOff 24 0)); mkChunk (-72) (CVal 8 (SOff 23 0)); mkChunk (-64) (CVal 8 (SOff 22 0));
mkChunk (-56) (CVal 8 (SOff 21 0)); mkChunk (-48) (CVal 8 (SOff 20 0)); mkChunk (-40) (CVal 8 (SOff 19 0));
mkChunk (-32) (CVal 8 (SOff 18 0)); mkChunk (-24) (CVal 8 (SOff 9 0)); mkChunk (-16) (CVal 8 (SOff 8 0));
mkChunk (-8) (CVal 8 (SOff 1 0)) ].
Lemma ra_saved_of_chunks : forall E (m : word -> option byte),
Forall (chunk_ok ubs2segs E m (spZ regs0)) SAVE_CHUNKS ->
(forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs0 rr) ->
ra_saved_ok regs0 m.
Proof.
intros E m HC HE.
assert (X : forall off n (rr : reg), In (mkChunk off (CVal 8 (SOff n 0))) SAVE_CHUNKS -> Z.of_nat n = bv_unsigned rr ->
word_mem ubs2segs m (spZ regs0 + off) (bv_unsigned (getr regs0 rr))).
{ intros off n rr Hin Hn. apply val_mem_word_mem.
apply (val_of_chunk_ok ubs2segs E m (spZ regs0) off 8%N (SOff n 0) (bv_unsigned (getr regs0 rr)));
[exact (proj1 (Forall_forall _ _) HC _ Hin) | cbn [sv_denot]; rewrite Z.add_0_r, (HE n rr Hn), Z_to_bv_bv_unsigned; reflexivity | apply u64_range8 | cbn; lia]. }
intros j rr Hj. unfold UI4v.sp0.
destruct j as [|[|[|[|[|[|[|[|[|[|[|[|[|j]]]]]]]]]]]]];
[ cbn in Hj; injection Hj as <-; replace (spZ regs0 - 8 * (Z.of_nat 0 + 1)) with (spZ regs0 + -8) by lia; apply (X (-8) 1%nat); [cbv; tauto | reflexivity]
| cbn in Hj; injection Hj as <-; replace (spZ regs0 - 8 * (Z.of_nat 1 + 1)) with (spZ regs0 + -16) by lia; apply (X (-16) 8%nat); [cbv; tauto | reflexivity]
| cbn in Hj; injection Hj as <-; replace (spZ regs0 - 8 * (Z.of_nat 2 + 1)) with (spZ regs0 + -24) by lia; apply (X (-24) 9%nat); [cbv; tauto | reflexivity]
| cbn in Hj; injection Hj as <-; replace (spZ regs0 - 8 * (Z.of_nat 3 + 1)) with (spZ regs0 + -32) by lia; apply (X (-32) 18%nat); [cbv; tauto | reflexivity]
| cbn in Hj; injection Hj as <-; replace (spZ regs0 - 8 * (Z.of_nat 4 + 1)) with (spZ regs0 + -40) by lia; apply (X (-40) 19%nat); [cbv; tauto | reflexivity]
| cbn in Hj; injection Hj as <-; replace (spZ regs0 - 8 * (Z.of_nat 5 + 1)) with (spZ regs0 + -48) by lia; apply (X (-48) 20%nat); [cbv; tauto | reflexivity]
| cbn in Hj; injection Hj as <-; replace (spZ regs0 - 8 * (Z.of_nat 6 + 1)) with (spZ regs0 + -56) by lia; apply (X (-56) 21%nat); [cbv; tauto | reflexivity]
| cbn in Hj; injection Hj as <-; replace (spZ regs0 - 8 * (Z.of_nat 7 + 1)) with (spZ regs0 + -64) by lia; apply (X (-64) 22%nat); [cbv; tauto | reflexivity]
| cbn in Hj; injection Hj as <-; replace (spZ regs0 - 8 * (Z.of_nat 8 + 1)) with (spZ regs0 + -72) by lia; apply (X (-72) 23%nat); [cbv; tauto | reflexivity]
| cbn in Hj; injection Hj as <-; replace (spZ regs0 - 8 * (Z.of_nat 9 + 1)) with (spZ regs0 + -80) by lia; apply (X (-80) 24%nat); [cbv; tauto | reflexivity]
| cbn in Hj; injection Hj as <-; replace (spZ regs0 - 8 * (Z.of_nat 10 + 1)) with (spZ regs0 + -88) by lia; apply (X (-88) 25%nat); [cbv; tauto | reflexivity]
| cbn in Hj; injection Hj as <-; replace (spZ regs0 - 8 * (Z.of_nat 11 + 1)) with (spZ regs0 + -96) by lia; apply (X (-96) 26%nat); [cbv; tauto | reflexivity]
| cbn in Hj; injection Hj as <-; replace (spZ regs0 - 8 * (Z.of_nat 12 + 1)) with (spZ regs0 + -104) by lia; apply (X (-104) 27%nat); [cbv; tauto | reflexivity]
| destruct j; discriminate Hj ].
Qed.
Lemma ubs2_rgbadd_E1a :
K_M1 API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest ->
rgba_pre API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest ->
SR ubs2segs (cfg_at regs0 PC_E1 mem0 md0) (rgba_post API L A regs0 mem0 md0 r g wfn ctx path attr gen loops W H bef beffmt s N img fmt rest).
Proof.
intros KM1 PRE. unfold K_M1, cfg_at in KM1.
destruct PRE as (HPRE & Hinit & Hfrm & G10 & G11 & Hc8 & Hclo & Hchi & Hcfp & Hobj & Hcg & Hwf & HW & HHt & HNmax & Hbef & Hro & HBent).
pose proof HPRE as (HH & Hra & Hst & Htp & Herr).
destruct Hst as (Hal16 & Hstk0 & Hceil & H63 & Hstw).
pose proof (proj1 alloc_ceiling_val) as Hac.
assert (HRv : RGBA_STK = 24576) by reflexivity. assert (HFv : RGBA_FRAME = 5168) by reflexivity.
assert (HSZ : RGB_SIZE = 64) by reflexivity. assert (HAPv : OFF_apal = 166) by reflexivity.
assert (HN1 : 1 <= N).
{ destruct Hwf as (_ & HW1 & HH1 & HNdef & _). rewrite HNdef. clear - HW1 HH1. nia. }
assert (Hrin : In (r, RGB_SIZE) (blocks L A)) by (eapply blocks_perm_in; [exact HBent | left; reflexivity]).
destruct (heap_blocks_range ubs2_msyms MR LAWS L A mem0 md0 r RGB_SIZE HH Hrin ltac:(lia)) as (Rr0 & Rr1 & Rr16).
pose proof (obj_at_range _ _ _ _ _ Hobj) as Rrgb.
pose proof (Rrgb 7%nat W eq_refl) as RW. pose proof (Rrgb 8%nat H eq_refl) as RH. pose proof (Rrgb 11%nat cur eq_refl) as Rcur.
cbn in RW, RH, Rcur.
set (rgbv := [g; wfn; ctx; path; attr; gen; loops; W; H; bef; beffmt; cur]) in *.
set (E := Ereg regs0 (map (Z_to_bv 64) rgbv ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs0 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall j v, nth_error rgbv j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HE39 : ew E 39 = Z_to_bv 64 W) by (apply (HV 7%nat); reflexivity).
assert (HE40 : ew E 40 = Z_to_bv 64 H) by (apply (HV 8%nat); reflexivity).
assert (HE43 : ew E 43 = Z_to_bv 64 cur) by (apply (HV 11%nat); reflexivity).
set (sp0 := spZ regs0) in *. assert (Hsp0 : sp0 = spZ regs0) by reflexivity.
assert (HRFCv : RGBFC_SIZE = 24) by reflexivity.
assert (HU2 : bv_unsigned (ew E 2) = sp0) by (rewrite (HE 2%nat 2%bv eq_refl); reflexivity).
assert (HU10 : bv_unsigned (ew E 10) = r) by (rewrite (HE 10%nat 10%bv eq_refl), G10; apply unsigned_lit_small; lia).
pose proof Hclo as Hclo1. unfold UI4v.sp0 in Hclo1.
assert (HU11 : bv_unsigned (ew E 11) = cfp) by (rewrite (HE 11%nat 11%bv eq_refl), G11; apply unsigned_lit_small; unfold RGBFC_SIZE in *; lia).
assert (HS : st_ok ubs2segs E ss_E1 (mkst regs0 (Z_to_bv 64 PC_E1) mem0 (seg_rom ubs2segs))).
{ unfold ss_E1. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor]]].
+ apply (region_ok_stack ubs2segs _ mem0 2 sp0); [exact HU2 | lia | lia | intros a Ha; apply Hstw; lia].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2. split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hstw; lia | constructor].
+ eapply (region_ok_obj ubs2segs _ mem0 10 r); [exact HU10 | lia | lia | exact Hobj | reflexivity | | intros i Hi; lia].
intros j v Hj. apply Ereg_vals. exact Hj.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU2, HU10. unfold RGBA_FRAME, OFF_apal, RGB_SIZE in *. repeat split; lia.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, HU10, HU11, HE39, HE40, HE43, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. unfold RGB_SIZE, RGBFC_SIZE in *. repeat split; lia. }
pose proof (journal_init ubs2_msyms MR RGBA_STK (FPfoot r g bef beffmt s N) L A regs0 mem0 md0 HPRE) as HJ.
change mem0 with (ms_mem (mkst regs0 (Z_to_bv 64 PC_E1) mem0 (seg_rom ubs2segs))) in HJ. fold sp0 in HJ.
unfold cfg_at. change (mkst regs0 (Z_to_bv 64 PC_E1) mem0 (seg_rom ubs2segs)) with (mkst regs0 (Z_to_bv 64 PC_E1) mem0 (seg_rom ubs2segs)).
jrun_to LAWS ubs2tbl_ok HS HJ E1_FSD.
{ eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF, HG.
assert (K1a : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 5168 <= a < sp0) -> mbyte ubs2segs (ms_mem ms) a = mbyte ubs2segs mem0 a).
{ intros a Ha Hna. mb_frame_g HF; [reflexivity | rewrite HU2; lia | rewrite HU2; lia | rewrite HU10; lia]. }
clear HF HG.
pose proof HS as (Hfr1 & _ & _ & _ & Hfc1 & _).
pose proof (st_ok_enterF ubs2segs fx 44 E _ ms HS ltac:(vm_compute; reflexivity) Hfrm) as HSF. clear HS.
set (E' := ew_fregs E 44 (@fp_regs fx)) in HSF.
assert (EA : forall k, (k < 44)%nat -> ew E' k = ew E k) by (intros k Hk; subst E'; apply ew_fregs_low; exact Hk).
assert (HU2' : bv_unsigned (ew E' 2) = sp0) by (rewrite EA by lia; exact HU2).
assert (HU10' : bv_unsigned (ew E' 10) = r) by (rewrite EA by lia; exact HU10).
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSF.
Ltac wrF HU := (eapply wr_ok_cons_win; [reflexivity | exact HU | cbn [r_wlo r_whi]; intros _; lia |]);
(eapply wr_ok_cons_win; [reflexivity | exact HU | cbn [r_wlo r_whi]; intros _; lia |]); apply wr_ok_cons_ro; [cbn; lia|]; apply wr_ok_nil.
fsd_go HSF HJ ltac:(wrF HU2'). intros ms1 HSF1 HJ1 HF1 Hfa1 Hfb1. clear HSF HJ.
fsd_go HSF1 HJ1 ltac:(wrF HU2'). intros ms2 HSF2 HJ2 HF2 Hfa2 Hfb2. clear HSF1 HJ1.
fsd_go HSF2 HJ2 ltac:(wrF HU2'). intros ms3 HSF3 HJ3 HF3 Hfa3 Hfb3. clear HSF2 HJ2.
cbn [ms_mem] in HF1, HF2, HF3.
assert (Hfx : fp_of ms3 = fx) by (unfold fp_of; rewrite Hfa3, Hfb3, Hfa2, Hfb2, Hfa1, Hfb1, Hfr1, Hfc1; apply fp_of_eta).
pose proof (st_okF_to_legacy ubs2segs E' _ ms3 HSF3) as HS. rewrite Hfx in HS. clear HSF3.
assert (K1b : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 5168 <= a < sp0) -> mbyte ubs2segs (ms_mem ms3) a = mbyte ubs2segs mem0 a).
{ intros a Ha Hna. rewrite <- (K1a a Ha Hna).
mb_frame_g HF3; [| rewrite HU2'; lia | rewrite HU2'; lia | rewrite HU10'; lia].
mb_frame_g HF2; [| rewrite HU2'; lia | rewrite HU2'; lia | rewrite HU10'; lia].
mb_frame_g HF1; [reflexivity | rewrite HU2'; lia | rewrite HU2'; lia | rewrite HU10'; lia]. }
assert (HEb : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E' n = getr regs0 rr).
{ intros n rr Hn. pose proof (u5_range rr). rewrite EA by lia. apply HE. exact Hn. }
assert (HE39b : ew E' 39 = Z_to_bv 64 W) by (rewrite EA by lia; exact HE39).
assert (HE40b : ew E' 40 = Z_to_bv 64 H) by (rewrite EA by lia; exact HE40).
assert (HE43b : ew E' 43 = Z_to_bv 64 cur) by (rewrite EA by lia; exact HE43).
clear HF1 HF2 HF3 Hfa1 Hfb1 Hfa2 Hfb2 Hfa3 Hfb3 Hfx Hfr1 Hfc1 K1a EA HE HE39 HE40 HE43 HU2 HU10 HU11 HV ms ms1 ms2.
clearbody E'. clear E. rename E' into E. rename HEb into HE. rename HE39b into HE39. rename HE40b into HE40. rename HE43b into HE43.
rename HU2' into HU2. rename HU10' into HU10. rename HJ3 into HJ.
pose proof HJ as (_ & _ & _ & _ & _ & HstkJ & _). destruct HstkJ as (_ & _ & _ & _ & Hstw3).
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_memset.
{ eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
jreg HS (10%bv:reg) as Ma0. rewrite HU2 in Ma0.
jreg HS (11%bv:reg) as Ma1. jreg HS (12%bv:reg) as Ma2. jreg HS (1%bv:reg) as Mra.
cbn [ms_mem mkst] in HF, HG, HJ.
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 5168 <= a < sp0) -> mbyte ubs2segs (ms_mem ms) a = mbyte ubs2segs mem0 a).
{ intros a Ha Hna. rewrite <- (K1b a Ha Hna). mb_frame_g HF; [reflexivity | rewrite HU2; lia | rewrite HU2; lia | rewrite HU10; lia]. }
clear K1b.
eapply SR_bind.
{ eapply (jmemset ubs2_msyms MR LAWS IMG ubs2_A_memset ubs2_memset_spec E _ _ RGBA_STK sp0 (FPfoot r g bef beffmt s N) L A mem0 md0 L A _ (sp0 - 5002) 0 768);
[ exact HS | reflexivity | reflexivity | exact HJ | replace (sp0 - 5002) with (sp0 + -5002) by lia; exact Ma0 | exact Ma1 | exact Ma2 | exact Mra
| apply ret_ok_even; vm_compute; reflexivity | lia | lia | lia | lia | | ].
- intros i Hi. eapply (present_grows _ _ _ HG).
apply writable_off_img_present; [lia | unfold in_img1; lia | apply Hstw3; lia].
- intros a Ha. left. lia. }
cbv beta. intros c' (regs2 & mem2 & -> & HJ2 & Hd10 & Hfr2 & Hout2 & Hgr2 & Hzero2). clear HJ.
jafter_stretch_keep HS 76%nat regs2 mem2 MEMSET_CLOB E1_RETM [0%nat; 1%nat; 2%nat] HS2.
match type of HS2 with ?P -> ?Q -> _ => assert (HKr : P); [| assert (HKm : Q); [| specialize (HS2 HKr HKm); clear HKr HKm]] end.
{ intros rr Hrr. apply Hfr2. exact Hrr. }
{ constructor; [|constructor; [|constructor; [|constructor]]].
- eapply region_kept_out; [exact Hout2 | exact Hgr2 | cbn [r_base r_lo base_val]; rewrite HU2; lia | cbn [r_base r_hi base_val]; rewrite HU2; lia | cbn [r_base r_lo r_hi base_val]; rewrite HU2; intros a Ha; lia | cbn; lia | cbn; lia].
- eapply region_kept_out; [exact Hout2 | exact Hgr2 | cbn [r_base r_lo base_val]; rewrite HU2; lia | cbn [r_base r_hi base_val]; rewrite HU2; lia | cbn [r_base r_lo r_hi base_val]; rewrite HU2; intros a Ha; lia | cbn; lia | cbn; lia].
- eapply region_kept_out; [exact Hout2 | exact Hgr2 | cbn [r_base r_lo base_val]; rewrite HU10; lia | cbn [r_base r_hi base_val]; rewrite HU10; lia | cbn [r_base r_lo r_hi base_val]; rewrite HU10; intros a Ha; lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 5002 <= a < sp0 - 4234) -> mbyte ubs2segs mem2 a = mbyte ubs2segs (ms_mem ms) a).
{ intros a Ha Hna. unfold mbyte. rewrite (Hout2 (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by lia; lia). reflexivity. }
clear HF HG.
jrun LAWS ubs2tbl_ok HS HJ2.
{ eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF, HG.
assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 5168 <= a < sp0) -> mbyte ubs2segs (ms_mem ms0) a = mbyte ubs2segs mem0 a).
{ intros a Ha Hna. rewrite <- (K1 a Ha Hna), <- (K2 a Ha ltac:(lia)). mb_frame_g HF; [reflexivity | rewrite HU2; lia | rewrite HU2; lia | rewrite HU10; lia]. }
clear HF HG K1 K2.
assert (HE' : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew (havoc E 76 (map (getr regs2) MEMSET_CLOB)) n = getr regs0 rr).
{ intros n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
rewrite ew_havoc_old by lia. apply HE. exact Hn. }
jbranch ubs2tbl HS.
{
jrun_to LAWS ubs2tbl_ok HS HJ2 PC_M1.
{ eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF, HG |- *.
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc]. lazymatch goal with |- SR _ (mkCfg (mkst _ ?pcv _ _) _) _ => change pcv with (Z_to_bv 64 PC_M1) end.
lazymatch goal with |- SR _ (mkCfg (mkst _ _ (ms_mem ?msx) _) _) _ =>
assert (K4 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 5168 <= a < sp0) -> mbyte ubs2segs (ms_mem msx) a = mbyte ubs2segs mem0 a)
by (intros a Ha Hna; rewrite <- (K3 a Ha Hna); mb_frame_g HF; [reflexivity | rewrite HU2; lia | rewrite HU2; lia | rewrite HU10; lia]);
pose proof (st_region_chunks ubs2segs _ _ _ 0%nat _ 2%nat sp0 HS eq_refl eq_refl ltac:(ew_havoc; exact HU2)) as HC0;
pose proof (st_region_chunks ubs2segs _ _ _ 1%nat _ 2%nat sp0 HS eq_refl eq_refl ltac:(ew_havoc; exact HU2)) as HC1
end.
cbn [r_chunks] in HC0, HC1.
apply (KM1 _ L A). split.
{
split; [exact HJ2|]. split; [exact Hinit|]. split; [exact Hfrm|]. split; [exact Hra|]. split; [exact Hal16|]. split; [exact Htp|].
split; [exact (ra_saved_of_chunks _ _ HC0 HE')|].
split; [exact Hc8|]. split; [exact Hclo|]. split; [exact Hchi|].
split. { eapply (obj_at_transport_range ubs2segs _ _ _ _ _ RGBFC_SIZE); [exact Hcfp | reflexivity |].
intros i Hi. unfold RGBFC_SIZE in Hi. unfold UI4v.sp0 in Hclo. apply K4; lia. }
split; [exact Hro|]. split; [exact Hwf|]. split; [exact HW|]. split; [exact HHt|]. split; [exact HNmax|]. split; [exact Hbef | exact HBent]. }
split. { split; [jreg HS (2%bv:reg) as Hq; rewrite Hq, HU2; unfold sp, UI4v.sp0, RGBA_FRAME; f_equal; unfold sp0; lia |].
split; [jreg HS (3%bv:reg) as Hq; rewrite Hq; exact (HE 3%nat 3%bv eq_refl) |].
jreg HS (4%bv:reg) as Hq; rewrite Hq; exact (HE 4%nat 4%bv eq_refl). }
split; [jreg HS (26%bv:reg) as Hq; rewrite Hq, (HE 11%nat 11%bv eq_refl); exact G11|].
split; [jreg HS (8%bv:reg) as Hq; rewrite Hq, (HE 10%nat 10%bv eq_refl); exact G10|].
split; [jreg HS (10%bv:reg) as Hq; rewrite Hq; exact HE39|].
split; [jreg HS (11%bv:reg) as Hq; rewrite Hq; exact HE40|].
split. { unfold slot. apply (proj1 (val_mem_word_mem ubs2segs _ _ _)). replace (sp regs0 + 144) with (sp0 + -5024) by (unfold sp, UI4v.sp0, RGBA_FRAME; unfold sp0; lia).
lazymatch goal with |- val_mem _ ?m _ _ _ =>
eapply (val_of_chunk_ok ubs2segs _ m sp0 (-5024) 8%N (SLit 0) 0); [exact (proj1 (Forall_forall _ _) HC1 (mkChunk (-5024) (CVal 8 (SLit 0))) ltac:(cbv; tauto)) | reflexivity | cbn; lia | cbn; lia] end. }
split. { unfold slot. apply (proj1 (val_mem_word_mem ubs2segs _ _ _)). replace (sp regs0 + 152) with (sp0 + -5016) by (unfold sp, UI4v.sp0, RGBA_FRAME; unfold sp0; lia).
lazymatch goal with |- val_mem _ ?m _ _ _ =>
eapply (val_of_chunk_ok ubs2segs _ m sp0 (-5016) 8%N (SLit 0) 0); [exact (proj1 (Forall_forall _ _) HC1 (mkChunk (-5016) (CVal 8 (SLit 0))) ltac:(cbv; tauto)) | reflexivity | cbn; lia | cbn; lia] end. }
split. { eapply (obj_at_transport_range ubs2segs _ _ _ _ _ RGB_SIZE); [exact Hobj | reflexivity |]. intros i Hi. apply K4; lia. }
split. { eapply (cgif_at_kept _ _ g s N (blocks L A)); [| exact Hcg |].
- eapply Permutation_trans; [exact HBent|]. unfold BASE. apply Permutation_middle.
- intros b n i Hbn Hi. destruct (blocks_range _ _ LAWS L A mem0 md0 b n HH Hbn) as [Hb0 Hb1]. apply K4; lia. }
exact HBent. }
jrun LAWS ubs2tbl_ok HS HJ2.
{ eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
jbranch ubs2tbl HS.
{
jrun_to LAWS ubs2tbl_ok HS HJ2 PC_M1.
{ eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF, HG, HF0, HG0 |- *.
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc]. lazymatch goal with |- SR _ (mkCfg (mkst _ ?pcv _ _) _) _ => change pcv with (Z_to_bv 64 PC_M1) end.
lazymatch goal with |- SR _ (mkCfg (mkst _ _ (ms_mem ?msx) _) _) _ =>
assert (K4 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 5168 <= a < sp0) -> mbyte ubs2segs (ms_mem msx) a = mbyte ubs2segs mem0 a)
by (intros a Ha Hna; rewrite <- (K3 a Ha Hna); mb_frame_g HF0; [mb_frame_g HF; [reflexivity | rewrite HU2; lia | rewrite HU2; lia | rewrite HU10; lia] | rewrite HU2; lia | rewrite HU2; lia | rewrite HU10; lia]);
pose proof (st_region_chunks ubs2segs _ _ _ 0%nat _ 2%nat sp0 HS eq_refl eq_refl ltac:(ew_havoc; exact HU2)) as HC0;
pose proof (st_region_chunks ubs2segs _ _ _ 1%nat _ 2%nat sp0 HS eq_refl eq_refl ltac:(ew_havoc; exact HU2)) as HC1
end.
cbn [r_chunks] in HC0, HC1.
apply (KM1 _ L A). split.
{
split; [exact HJ2|]. split; [exact Hinit|]. split; [exact Hfrm|]. split; [exact Hra|]. split; [exact Hal16|]. split; [exact Htp|].
split; [exact (ra_saved_of_chunks _ _ HC0 HE')|].
split; [exact Hc8|]. split; [exact Hclo|]. split; [exact Hchi|].
split. { eapply (obj_at_transport_range ubs2segs _ _ _ _ _ RGBFC_SIZE); [exact Hcfp | reflexivity |].
intros i Hi. unfold RGBFC_SIZE in Hi. unfold UI4v.sp0 in Hclo. apply K4; lia. }
split; [exact Hro|]. split; [exact Hwf|]. split; [exact HW|]. split; [exact HHt|]. split; [exact HNmax|]. split; [exact Hbef | exact HBent]. }
split. { split; [jreg HS (2%bv:reg) as Hq; rewrite Hq, HU2; unfold sp, UI4v.sp0, RGBA_FRAME; f_equal; unfold sp0; lia |].
split; [jreg HS (3%bv:reg) as Hq; rewrite Hq; exact (HE 3%nat 3%bv eq_refl) |].
jreg HS (4%bv:reg) as Hq; rewrite Hq; exact (HE 4%nat 4%bv eq_refl). }
split; [jreg HS (26%bv:reg) as Hq; rewrite Hq, (HE 11%nat 11%bv eq_refl); exact G11|].
split; [jreg HS (8%bv:reg) as Hq; rewrite Hq, (HE 10%nat 10%bv eq_refl); exact G10|].
split; [jreg HS (10%bv:reg) as Hq; rewrite Hq; exact HE39|].
split; [jreg HS (11%bv:reg) as Hq; rewrite Hq; exact HE40|].
split. { unfold slot. apply (proj1 (val_mem_word_mem ubs2segs _ _ _)). replace (sp regs0 + 144) with (sp0 + -5024) by (unfold sp, UI4v.sp0, RGBA_FRAME; unfold sp0; lia).
lazymatch goal with |- val_mem _ ?m _ _ _ =>
eapply (val_of_chunk_ok ubs2segs _ m sp0 (-5024) 8%N (SLit 0) 0); [exact (proj1 (Forall_forall _ _) HC1 (mkChunk (-5024) (CVal 8 (SLit 0))) ltac:(cbv; tauto)) | reflexivity | cbn; lia | cbn; lia] end. }
split. { unfold slot. apply (proj1 (val_mem_word_mem ubs2segs _ _ _)). replace (sp regs0 + 152) with (sp0 + -5016) by (unfold sp, UI4v.sp0, RGBA_FRAME; unfold sp0; lia).
lazymatch goal with |- val_mem _ ?m _ _ _ =>
eapply (val_of_chunk_ok ubs2segs _ m sp0 (-5016) 8%N (SLit 0) 0); [exact (proj1 (Forall_forall _ _) HC1 (mkChunk (-5016) (CVal 8 (SLit 0))) ltac:(cbv; tauto)) | reflexivity | cbn; lia | cbn; lia] end. }
split. { eapply (obj_at_transport_range ubs2segs _ _ _ _ _ RGB_SIZE); [exact Hobj | reflexivity |]. intros i Hi. apply K4; lia. }
split. { eapply (cgif_at_kept _ _ g s N (blocks L A)); [| exact Hcg |].
- eapply Permutation_trans; [exact HBent|]. unfold BASE. apply Permutation_middle.
- intros b n i Hbn Hi. destruct (blocks_range _ _ LAWS L A mem0 md0 b n HH Hbn) as [Hb0 Hb1]. apply K4; lia. }
exact HBent. }
pose proof (st_ok_enterF ubs2segs fx 128 _ _ _ HS ltac:(vm_compute; reflexivity) Hfrm) as HSF. clear HS.
lazymatch type of HSF with st_okF _ (ew_fregs ?Eb _ _) _ _ =>
set (E2 := ew_fregs Eb 128 (@fp_regs fx)) in HSF;
assert (EA2 : forall k, (k < 128)%nat -> ew E2 k = ew Eb k) by (intros k Hk; subst E2; apply ew_fregs_low; exact Hk) end.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSF.
assert (HU2x : bv_unsigned (ew E2 2) = sp0) by (rewrite EA2 by lia; ew_havoc; exact HU2).
assert (HU10x : bv_unsigned (ew E2 10) = r) by (rewrite EA2 by lia; ew_havoc; exact HU10).
assert (HEx : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E2 n = getr regs0 rr).
{ intros n rr Hn. pose proof (u5_range rr). rewrite EA2 by lia. rewrite ew_havoc_old by lia. apply HE. exact Hn. }
jrunF LAWS ubs2tbl_ok HSF HJ2.
{ eapply wr_ok_cons_win; [reflexivity | exact HU2x | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | exact HU2x | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF, HG, HF0, HG0 |- *.
pose proof (st_okF_frm ubs2segs _ _ _ HSF) as HfrmF.
pose proof (st_okF_to_legacy ubs2segs _ _ _ HSF) as HS. clear HSF.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (K4 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 5168 <= a < sp0) -> mbyte ubs2segs (ms_mem msx) a = mbyte ubs2segs mem0 a)
by (intros a Ha Hna; rewrite <- (K3 a Ha Hna); mb_frame_g HF0; [mb_frame_g HF; [reflexivity | rewrite HU2; lia | rewrite HU2; lia | rewrite HU10; lia] | rewrite HU2x; lia | rewrite HU2x; lia | rewrite HU10x; lia])
end.
clear HE. rename HEx into HE.
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ2)) as (Hh & Hl & _).
lazymatch type of HS with @st_ok _ ?fxq _ _ _ =>
eapply (SR_ret_at (fx := fxq) ubs2segs ubs2tbl); [exact ubs2tbl_ok | exact Hh | exact Hl | exact HS | reflexivity | vm_compute; reflexivity |] end.
unfold rgba_post.
lazymatch type of HS with @st_ok _ ?fxq _ _ ?msf => exists fxq, L, A, (ms_regs msf), (ms_mem msf), md0, s, bef, beffmt, cur end.
split. { jreg HS (1%bv:reg) as Hq. rewrite Hq, (HE 1%nat 1%bv eq_refl), Hra. reflexivity. }
split; [exact HfrmF|]. split; [exact HJ2|].
split. { apply regs_preserved_intro_g.
- jreg HS (2%bv:reg) as Hq. rewrite Hq. exact (HE 2%nat 2%bv eq_refl).
- jreg HS (3%bv:reg) as Hq. rewrite Hq. exact (HE 3%nat 3%bv eq_refl).
- jreg HS (4%bv:reg) as Hq. rewrite Hq. exact (HE 4%nat 4%bv eq_refl).
- jreg HS (8%bv:reg) as Hq. rewrite Hq. exact (HE 8%nat 8%bv eq_refl).
- jreg HS (9%bv:reg) as Hq. rewrite Hq. exact (HE 9%nat 9%bv eq_refl).
- jreg HS (18%bv:reg) as Hq. rewrite Hq. exact (HE 18%nat 18%bv eq_refl).
- jreg HS (19%bv:reg) as Hq. rewrite Hq. exact (HE 19%nat 19%bv eq_refl).
- jreg HS (20%bv:reg) as Hq. rewrite Hq. exact (HE 20%nat 20%bv eq_refl).
- jreg HS (21%bv:reg) as Hq. rewrite Hq. exact (HE 21%nat 21%bv eq_refl).
- jreg HS (22%bv:reg) as Hq. rewrite Hq. exact (HE 22%nat 22%bv eq_refl).
- jreg HS (23%bv:reg) as Hq. rewrite Hq. exact (HE 23%nat 23%bv eq_refl).
- jreg HS (24%bv:reg) as Hq. rewrite Hq. exact (HE 24%nat 24%bv eq_refl).
- jreg HS (25%bv:reg) as Hq. rewrite Hq. exact (HE 25%nat 25%bv eq_refl).
- jreg HS (26%bv:reg) as Hq. rewrite Hq. exact (HE 26%nat 26%bv eq_refl).
- jreg HS (27%bv:reg) as Hq. rewrite Hq. exact (HE 27%nat 27%bv eq_refl). }
split; [exact Hinit|].
split. { eapply (obj_at_transport_range ubs2segs _ _ _ _ _ RGB_SIZE); [exact Hobj | reflexivity |]. intros i Hi. apply K4; lia. }
split. { eapply (cgif_at_kept _ _ g s N (blocks L A)); [| exact Hcg |].
- eapply Permutation_trans; [exact HBent|]. unfold BASE. apply Permutation_middle.
- intros b n i Hbn Hi. destruct (blocks_range _ _ LAWS L A mem0 md0 b n HH Hbn) as [Hb0 Hb1]. apply K4; lia. }
split; [exact Hwf|]. split; [exact HW|]. split; [exact HHt|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact Hbef|]. exact HBent.
Qed.
End d.
End c.
