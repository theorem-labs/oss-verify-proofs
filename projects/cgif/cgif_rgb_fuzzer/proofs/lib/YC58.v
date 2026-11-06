(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation Reals.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YK0p.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02 YQ07 YQ08 YC03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04 YC06.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2u YC1b YC4u YC4z YC59 YC5c YC54 YC55 YC56.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC5a YC57.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC5b.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YP14 YI08 YI0c YI0g YM00 YM07 YM05 YM04 YM01 YM02 YM06 YI0d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN07.
Import ListNotations.
Ltac2 sat_vars () := [@rc; @B; @STK; @sp0; @FP; @ly; @S; @W0; @mem0; @md0; @own; @k1; @ly2; @S2; @W2; @memM; @regs0; @palp; @frp; @nln; @imin; @imax; @cidx; @res; @pal; @fr; @pb; @pm; @fb; @fm; @mn0; @mn1; @mn2; @n0].
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Local Abbreviation D := fmt_double.
Section S.
Context {rc : YN05.RunCeil}.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMALLOC : forall fx : FPState, @amalloc_realizes fx rc trasegs B.
Hypothesis AMEMSET : forall fx : FPState, @aintrin_realizes fx rc trasegs B OSet A_asan_memset.
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL. Let errno_low := tl_env B TL.
Lemma nt_pres_in : forall regs regs' : bvmap 5 word, aregs_preserved regs regs' ->
forall r : bv 5, In r CALLEE_SAVED -> getr regs' r = getr regs r.
Proof.
intros regs regs' Hp r Hin. unfold CALLEE_SAVED in Hin. cbn [In] in Hin.
repeat (destruct Hin as [<- | Hin]); [ | | | | | | | | | | | | | | | destruct Hin].
- exact (Hp 2 ltac:(unfold acallee_saved; lia)).
- exact (Hp 3 ltac:(unfold acallee_saved; lia)).
- exact (Hp 4 ltac:(unfold acallee_saved; lia)).
- exact (Hp 8 ltac:(unfold acallee_saved; lia)).
- exact (Hp 9 ltac:(unfold acallee_saved; lia)).
- exact (Hp 18 ltac:(unfold acallee_saved; lia)).
- exact (Hp 19 ltac:(unfold acallee_saved; lia)).
- exact (Hp 20 ltac:(unfold acallee_saved; lia)).
- exact (Hp 21 ltac:(unfold acallee_saved; lia)).
- exact (Hp 22 ltac:(unfold acallee_saved; lia)).
- exact (Hp 23 ltac:(unfold acallee_saved; lia)).
- exact (Hp 24 ltac:(unfold acallee_saved; lia)).
- exact (Hp 25 ltac:(unfold acallee_saved; lia)).
- exact (Hp 26 ltac:(unfold acallee_saved; lia)).
- exact (Hp 27 ltac:(unfold acallee_saved; lia)).
Qed.
Definition p0_mem : smem := [ stack_region 192; got_region; bcell_region 32 ].
Definition p0_facts : facts := mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (32%nat, mkAF SB SB 0) ] [] [].
Definition ss_P0 : sstate := mkSS A_new_tree_node sr_atoms p0_mem None p0_facts.
Definition P0_post (fx : FPState) (STK sp0 : Z) (FP : list (Z * Z)) ly S W0 mem0 md0 own lyc Sc (W : world trasegs) (memc : word -> option byte)
(regs : bvmap 5 word) (palp frp nln imin imax cidx k : Z) : world trasegs -> config -> Prop :=
fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z) (memP : word -> option byte),
c2 = mkCfg (@mkst fx regs2 (Z_to_bv 64 TN_RET0) mem2 (seg_rom trasegs)) md2 /\
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + 1) /\ frames S2 = frames Sc /\ bud_le Sc S2 1 1 208 0 /\
getr regs2 2 = w64 (spZ regs - 192) /\ getr regs2 8 = w64 nln /\ getr regs2 10 = w64 res /\ getr regs2 18 = w64 cidx /\
getr regs2 19 = w64 imax /\ getr regs2 20 = w64 imin /\ getr regs2 21 = w64 frp /\ getr regs2 22 = w64 palp /\ getr regs2 23 = w64 SB /\
(forall rr : bv 5, In rr NT_KEPT -> getr regs2 rr = getr regs rr) /\
obj_at trasegs (mrestrict (w_H W2) mem2) (spZ regs - 192) LAY_NTF (ntf_vals regs) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 192 <= a < spZ regs) -> aview trasegs (w_H W) memP a = aview trasegs (w_H W) memc a) /\
(forall a, apresent (w_H W) memc a -> apresent (w_H W) memP a) /\
((res = 0 /\ ablocks B ly2 S2 = ablocks B lyc Sc /\
acall_kept trasegs B lyc Sc W memP W2 mem2 (spZ regs - 192 - ASTACK) (spZ regs - 192) (fun _ => False))
\/ (4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, NODE_SIZE)] /\
acall_kept trasegs B lyc Sc W memP W2 mem2 (spZ regs - 192 - ASTACK) (spZ regs - 192) (fun a => res <= a < res + req_size NODE_SIZE))).
Lemma ntn_p0 : forall (fx : FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(palp frp nln imin imax cidx : Z),
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - TNTN_STK -> spZ regs <= sp0 ->
getr regs 10 = w64 palp -> getr regs 11 = w64 frp -> getr regs 12 = w64 nln ->
getr regs 13 = w64 imin -> getr regs 14 = w64 imax -> getr regs 15 = w64 cidx ->
spZ regs <= nln -> nln + 2 <= sp0 -> nln mod 8 = 2 ->
vev Sc < VEV_MAX -> blocks_bytes Sc + NODE_SIZE <= LIVE_MAX ->
SRr trasegs W (mkCfg (@mkst fx regs (Z_to_bv 64 A_new_tree_node) memc (seg_rom trasegs)) mdc)
(P0_post fx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc regs palp frp nln imin imax cidx k).
Proof.
intros fx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs palp frp nln imin imax cidx
HJ Hgp Htp Hal16 Hbud Hsptop Ga0 Ga1 Ga2 Ga3 Ga4 Ga5 Hnl1 Hnl2 Hnl8 Hev Hlive.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & Hnev & Hk0 & _ & _ & _ & _ & _ & Hpres & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : TNTN_STK = 16576) by reflexivity. assert (HAS : ASTACK = 16384) by reflexivity.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
set (E := Ereg regs [Z_to_bv 64 SB]).
assert (HE : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (HE 2%nat 2%bv eq_refl); reflexivity).
assert (HS : @st_ok trasegs fx E ss_P0 (restrict (w_H W) (@mkst fx regs (Z_to_bv 64 A_new_tree_node) memc (seg_rom trasegs)))).
{ rewrite restrict_mkst_fx. unfold ss_P0. apply (entry_st_ok_full trasegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold p0_mem, stack_region, got_region, bcell_region. repeat apply Forall_cons; try apply Forall_nil.
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. fold E. rewrite Usp.
split; [clear - Hbud Hsptop Hslo Hceil C1 WS Hstk0; lia|]. split; [clear - Hsptop Hshi H47; lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable trasegs). apply Hpres. clear - Ho Hbud Hsptop WS. lia.
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. unfold A_GOT_shadow.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 663904) at 1.
apply (chunk_ok_val trasegs _ _ 0 663904 8 (SLit A_shadow_glob) A_shadow_glob); [reflexivity | unfold A_shadow_glob; zside | zside |].
exact (val_mem_of_rdword trasegs (w_H W) memc _ _ Kgot).
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. unfold A_shadow_glob.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 696760) at 1.
apply (chunk_ok_val trasegs _ _ 0 696760 8 (SOff 32 0) SB);
[cbn [sv_denot]; fold E; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
exact (val_mem_of_rdword trasegs (w_H W) memc _ _ Kcell).
- apply pairwise_disjoint_of_extents. unfold p0_mem, stack_region, got_region, bcell_region, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. fold E. rewrite Usp. unfold A_GOT_shadow, A_shadow_glob.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
clear - Hslo Hshi H47 Hceil Hbud Hsptop C1 Hstk0 WS. repeat split; lia.
- split; [|split; [exact I | exact I]].
cbn [p0_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E.
rewrite Usp, E32, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
clear - Hslo Hshi H47 Hceil Hbud Hsptop Hal16 C1 Hstk0 WS. unfold SB. repeat match goal with |- _ /\ _ => split end; lia. }
assert (SHOK : sh_ok trasegs (SOff 32 0) [] E (mrestrict (w_H W) memc)) by constructor.
change memc with (ms_mem (@mkst fx regs (Z_to_bv 64 A_new_tree_node) memc (seg_rom trasegs))) in HJ.
aj_run_to_tok tratbl_lib_ok HS HJ SHOK nt_Bspan A_wrap_malloc.
{ unfold p0_mem. eapply awr_ok_cons_stack_off with (n := 2%nat) (d := spZ regs - sp0);
[reflexivity | rewrite Usp; clear; lia | cbn [YQ0b.r_wlo stack_region]; clear - Hbud WS; lia | cbn [YQ0b.r_whi stack_region]; clear - Hsptop; lia |].
apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
cbn [ms_mem mkst] in HFr, HG.
rreg HS (1%bv : bv 5) Qra. rreg HS (2%bv : bv 5) Qsp. rreg HS (3%bv : bv 5) Qgp. rreg HS (4%bv : bv 5) Qtp. rreg HS (8%bv : bv 5) Qs0.
rreg HS (10%bv : bv 5) Qa0. rreg HS (18%bv : bv 5) Q18. rreg HS (19%bv : bv 5) Q19. rreg HS (20%bv : bv 5) Q20.
rreg HS (21%bv : bv 5) Q21. rreg HS (22%bv : bv 5) Q22. rreg HS (23%bv : bv 5) Q23. rreg HS (26%bv : bv 5) Q26. rreg HS (27%bv : bv 5) Q27.
assert (Rsp : alloc_ceiling + 16384 <= spZ regs - 192 /\ spZ regs <= 2 ^ 47) by (clear - Hbud Hsptop Hslo Hshi H47 Hceil WS; lia).
pose proof (st_ok_region_nth _ _ _ 0%nat _ HS ltac:(reflexivity)) as HR0. cbn [ms_mem restrict] in HR0.
assert (SVP : obj_at trasegs (mrestrict (w_H W) (ms_mem ms)) (spZ regs - 192) LAY_NTF (ntf_vals regs)).
{ assert (SL : forall od (r : bv 5) n, Z.of_nat n = bv_unsigned r ->
In (YQ0b.mkChunk od (CVal 8 (SOff n 0)))
[YQ0b.mkChunk (-88) (CVal 8 (SOff 25 0)); YQ0b.mkChunk (-80) (CVal 8 (SOff 24 0)); YQ0b.mkChunk (-72) (CVal 8 (SOff 23 0));
YQ0b.mkChunk (-64) (CVal 8 (SOff 22 0)); YQ0b.mkChunk (-56) (CVal 8 (SOff 21 0)); YQ0b.mkChunk (-48) (CVal 8 (SOff 20 0));
YQ0b.mkChunk (-40) (CVal 8 (SOff 19 0)); YQ0b.mkChunk (-32) (CVal 8 (SOff 18 0)); YQ0b.mkChunk (-24) (CVal 8 (SOff 9 0));
YQ0b.mkChunk (-16) (CVal 8 (SOff 8 0)); YQ0b.mkChunk (-8) (CVal 8 (SOff 1 0))] ->
field_ok trasegs (mrestrict (w_H W) (ms_mem ms)) (spZ regs - 192) (od + 192, 8%N) (bv_unsigned (getr regs r))).
{ intros od r n Hn Hin. pose proof (bv_unsigned_in_range 64 (getr regs r)) as Hrg. change (bv_modulus 64) with (2 ^ 64) in Hrg.
split; [|cbn [snd Z.of_N]; exact Hrg]. cbn [fst snd]. replace (spZ regs - 192 + (od + 192)) with (spZ regs + od) by lia.
lazymatch type of HR0 with region_ok _ _ _ (YQ0b.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
apply (slot_of_region E _ (spZ regs) cs lo hi wlo whi od (SOff n 0) _ HR0 Usp Hin); [|exact Hrg] end.
cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. rewrite (HE n r Hn). symmetry. apply Z_to_bv_bv_unsigned. }
unfold LAY_NTF, ntf_vals, NTF_REGS. cbn [obj_at map].
split; [exact (SL (-88) (25%bv : bv 5) 25%nat eq_refl ltac:(cbn; tauto))|].
split; [exact (SL (-80) (24%bv : bv 5) 24%nat eq_refl ltac:(cbn; tauto))|].
split; [exact (SL (-72) (23%bv : bv 5) 23%nat eq_refl ltac:(cbn; tauto))|].
split; [exact (SL (-64) (22%bv : bv 5) 22%nat eq_refl ltac:(cbn; tauto))|].
split; [exact (SL (-56) (21%bv : bv 5) 21%nat eq_refl ltac:(cbn; tauto))|].
split; [exact (SL (-48) (20%bv : bv 5) 20%nat eq_refl ltac:(cbn; tauto))|].
split; [exact (SL (-40) (19%bv : bv 5) 19%nat eq_refl ltac:(cbn; tauto))|].
split; [exact (SL (-32) (18%bv : bv 5) 18%nat eq_refl ltac:(cbn; tauto))|].
split; [exact (SL (-24) (9%bv : bv 5) 9%nat eq_refl ltac:(cbn; tauto))|].
split; [exact (SL (-16) (8%bv : bv 5) 8%nat eq_refl ltac:(cbn; tauto))|].
split; [exact (SL (-8) (1%bv : bv 5) 1%nat eq_refl ltac:(cbn; tauto))|].
exact I. }
assert (KP : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 192 <= a < spZ regs) -> aview trasegs (w_H W) (ms_mem ms) a = aview trasegs (w_H W) memc a).
{ intros a Ha Hnw. apply aview_eq_of. apply HFr. rewrite unsigned_lit_small by lia.
intros (rr & Hin & Hr). cbn [ss_mem ss_P0 p0_mem In] in Hin.
destruct Hin as [<- | [<- | [<- | []]]]; cbn [stack_region got_region bcell_region YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hr;
[rewrite Usp in Hr; clear - Hr Hnw; lia | clear - Hr; lia | clear - Hr; lia]. }
assert (PP : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem ms) a) by (intros a Ha; exact (apresent_grows _ _ _ _ HG Ha)).
clear HF HFr HG HR0.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
replace (Z_to_bv 64 340228) with (Z_to_bv 64 (pc_wrap_malloc (as_code B))) by (rewrite HBcode; reflexivity).
assert (CH : chain_pre lyc (aview trasegs (w_H W) (ms_mem ms)) (ms_regs ms) []).
{ eapply (achain_chain_pre lyc _ (spZ regs - 192) nln []).
- left. split; [right; right; rewrite Hnl8; discriminate | reflexivity].
- unfold spZ at 1 2. rewrite Qsp, Usp. rewrite unsigned_lit_small by (clear - Rsp C1; lia). clear - Rsp. lia.
- unfold s0Z. rewrite Qs0, (HE 12%nat 12%bv eq_refl), Ga2. apply unsigned_lit_small. clear - Hnl1 Hnl2 Hbud Hslo Hceil Hshi H47 C1 WS Hstk0. lia.
- unfold raZ. rewrite Qra, unsigned_lit_small by lia. lia. }
eapply SRr_mono.
{ eapply (aj_malloc_atD trasegs B LAWS Hsegs errno_low ML (AMALLOC fx) W (ms_regs ms) (ms_mem ms) STK sp0 FP ly S W0 mem0 md0 own
lyc Sc _ k NODE_SIZE (spZ regs - 192 - sp0) (Z_to_bv 64 0x84fbc) [] HJ);
[ rewrite Qa0; reflexivity
| unfold MALLOC_MAX, NODE_SIZE; lia
| exact Hlive
| unfold spZ at 1; rewrite Qsp, Usp; rewrite unsigned_lit_small by (clear - Rsp C1; lia); lia
| replace (spZ regs - 192 - sp0) with (spZ regs - sp0 + (-12) * 16) by lia; rewrite Z_mod_plus_full, Zminus_mod, Hal16, Hsp0al; reflexivity
| clear - Hsptop; lia
| rewrite HAS; clear - Hbud WS; lia
| rewrite Qgp, (HE 3%nat 3%bv eq_refl); exact Hgp
| rewrite Qtp, (HE 4%nat 4%bv eq_refl); exact Htp
| exact Qra
| vm_compute; reflexivity
| exact Hev
| exact CH
| rewrite call_trace_nil; unfold raZ; rewrite Qra, unsigned_lit_small by lia; rewrite HBcode; apply (tl_universe B TL);
apply TRACES_new_tree_node_U; apply memZL_In; vm_compute; reflexivity ]. }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & res & -> & HJ2 & HP2 & Ha02 & Hfrs2 & Hd2 & Hres).
pose proof (nt_pres_in _ _ HP2) as PI.
exists ly2, S2, regs2, mem2, md2, res, (ms_mem ms).
split; [reflexivity|]. split; [exact HJ2|]. split; [exact Hfrs2|]. split; [exact Hd2|].
split; [rewrite (PI (2%bv : bv 5) ltac:(cbv; tauto)), Qsp, Usp; reflexivity|].
split; [rewrite (PI (8%bv : bv 5) ltac:(cbv; tauto)), Qs0, (HE 12%nat 12%bv eq_refl); exact Ga2|].
split; [exact Ha02|].
split; [rewrite (PI (18%bv : bv 5) ltac:(cbv; tauto)), Q18, (HE 15%nat 15%bv eq_refl); exact Ga5|].
split; [rewrite (PI (19%bv : bv 5) ltac:(cbv; tauto)), Q19, (HE 14%nat 14%bv eq_refl); exact Ga4|].
split; [rewrite (PI (20%bv : bv 5) ltac:(cbv; tauto)), Q20, (HE 13%nat 13%bv eq_refl); exact Ga3|].
split; [rewrite (PI (21%bv : bv 5) ltac:(cbv; tauto)), Q21, (HE 11%nat 11%bv eq_refl); exact Ga1|].
split; [rewrite (PI (22%bv : bv 5) ltac:(cbv; tauto)), Q22, (HE 10%nat 10%bv eq_refl); exact Ga0|].
split; [rewrite (PI (23%bv : bv 5) ltac:(cbv; tauto)), Q23, E32; reflexivity|].
split.
{ intros rr Hrr. cbv [NT_KEPT In] in Hrr.
destruct Hrr as [<- | [<- | [<- | [<- | []]]]];
[ rewrite (PI (3%bv : bv 5) ltac:(cbv; tauto)), Qgp; apply (HE 3%nat 3%bv eq_refl)
| rewrite (PI (4%bv : bv 5) ltac:(cbv; tauto)), Qtp; apply (HE 4%nat 4%bv eq_refl)
| rewrite (PI (26%bv : bv 5) ltac:(cbv; tauto)), Q26; apply (HE 26%nat 26%bv eq_refl)
| rewrite (PI (27%bv : bv 5) ltac:(cbv; tauto)), Q27; apply (HE 27%nat 27%bv eq_refl) ]. }
assert (K1 : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs - 192 - ASTACK <= a < spZ regs - 192) ->
aview trasegs (w_H W2) mem2 a = aview trasegs (w_H W) (ms_mem ms) a).
{ destruct Hres as [(_ & _ & (K & _)) | (_ & _ & (K & _))]; intros a Ha Hn; apply K; [exact Ha | replace (sp0 + (spZ regs - 192 - sp0)) with (spZ regs - 192) by lia; exact Hn
| exact Ha | replace (sp0 + (spZ regs - 192 - sp0)) with (spZ regs - 192) by lia; exact Hn]. }
split.
{ apply (obj_at_transport trasegs _ _ (spZ regs - 192) LAY_NTF _ SVP).
intros f i Hf Hi. apply (mbyte_of_aview trasegs). apply K1.
- unfold LAY_NTF in Hf. cbn [In] in Hf. repeat (destruct Hf as [<- | Hf]; [cbn [fst snd Z.of_N] in Hi |- *; clear - Hi Rsp; lia|]). destruct Hf.
- unfold LAY_NTF in Hf. cbn [In] in Hf. repeat (destruct Hf as [<- | Hf]; [cbn [fst snd Z.of_N] in Hi |- *; clear - Hi; lia|]). destruct Hf. }
split; [exact KP|]. split; [exact PP|].
replace (sp0 + (spZ regs - 192 - sp0)) with (spZ regs - 192) in Hres by lia. exact Hres.
Qed.
Definition pf_mem : smem := [ YQ0b.mkRegion (Some 2%nat) 0 192 0 0 (obj_chunks_from LAY_NTF 32) ].
Definition pf_facts : facts := mkFacts [ (2%nat, mkAF (2^46) (2^47) 4) ] [] [].
Definition ss_PF : sstate := mkSS TN_RET0 (sr_set sr_atoms 10%bv (SLit 0)) pf_mem None pf_facts.
Lemma ntn_pfail : forall (fx : FPState) STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k (regs0 regs : bvmap 5 word),
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k ->
YK0s.ret_ok (getr regs0 1) ->
spZ regs0 mod 16 = 0 -> sp0 - STK <= spZ regs0 - TNTN_STK -> spZ regs0 <= sp0 ->
getr regs 2 = w64 (spZ regs0 - 192) -> getr regs 10 = w64 0 ->
(forall rr : bv 5, In rr NT_KEPT -> getr regs rr = getr regs0 rr) ->
obj_at trasegs (mrestrict (w_H W2) mem2) (spZ regs0 - 192) LAY_NTF (ntf_vals regs0) ->
SRr trasegs W2 (mkCfg (@mkst fx regs (Z_to_bv 64 TN_RET0) mem2 (seg_rom trasegs)) md2)
(fun W' c' => W' = W2 /\ exists regs' mem' md',
c' = mkCfg (@mkst fx regs' (getr regs0 1) mem' (seg_rom trasegs)) md' /\
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem' md' k /\
aregs_preserved regs0 regs' /\ getr regs' 10 = w64 0 /\
(forall a, 0 <= a < 2 ^ 64 -> aview trasegs (w_H W2) mem' a = aview trasegs (w_H W2) mem2 a) /\
(forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem' a)).
Proof.
intros fx STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k regs0 regs HJ Hra Hal16 Hbud Hsptop G2 G10 GK HSV.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof asan_consts as (C1 & _).
assert (WS : TNTN_STK = 16576) by reflexivity.
assert (Rsp : alloc_ceiling + 16384 <= spZ regs0 - 192 /\ spZ regs0 <= 2 ^ 47) by (clear - Hbud Hsptop Hslo Hshi H47 Hceil WS; lia).
set (E := Ereg regs (map (Z_to_bv 64) (ntf_vals regs0))).
assert (HE : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HVF : forall j v, nth_error (ntf_vals regs0) j = Some v -> ew E (32 + j) = Z_to_bv 64 v).
{ intros j v Hj. subst E. rewrite <- (app_nil_r (map (Z_to_bv 64) (ntf_vals regs0))). apply Ereg_vals. exact Hj. }
assert (U2 : bv_unsigned (ew E 2) = spZ regs0 - 192) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; clear - Rsp C1; lia).
assert (HS : @st_ok trasegs fx E ss_PF (restrict (w_H W2) (@mkst fx regs (Z_to_bv 64 TN_RET0) mem2 (seg_rom trasegs)))).
{ rewrite restrict_mkst_fx. unfold ss_PF. apply (entry_st_ok_full trasegs).
- apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X |]. rewrite G10. reflexivity.
- vm_compute. reflexivity.
- unfold pf_mem. repeat apply Forall_cons; try apply Forall_nil.
eapply (region_ok_obj trasegs _ _ 2 (spZ regs0 - 192)); [exact U2 | clear - Rsp C1; lia | clear - Rsp; lia | exact HSV | reflexivity | exact HVF | intros i Hi; lia].
- apply pairwise_disjoint_of_extents. unfold pf_mem, extent_of_region. cbn [map zpairwise_disjoint zall_disjoint]. repeat split.
- split; [|split; exact I].
cbn [pf_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E. rewrite U2. change (2 ^ 4) with 16.
assert (Qal : (spZ regs0 - 192) mod 16 = 0) by (rewrite Zminus_mod, Hal16; reflexivity).
clear - Rsp Qal C1. repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
assert (SHOK : sh_ok trasegs l1_Bx [] E (mrestrict (w_H W2) mem2)) by constructor.
change mem2 with (ms_mem (@mkst fx regs (Z_to_bv 64 TN_RET0) mem2 (seg_rom trasegs))) in HJ.
aj_run_to_tok tratbl_lib_ok HS HJ SHOK nt_Bspan TN_RET.
{ unfold pf_mem. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
cbn [ms_mem mkst] in HFr, HG.
assert (FV : forall j (r : bv 5), nth_error NTF_REGS j = Some r -> ew E (32 + j) = getr regs0 r).
{ intros j r Hj. rewrite (HVF j (bv_unsigned (getr regs0 r))); [apply Z_to_bv_bv_unsigned|]. unfold ntf_vals. rewrite nth_error_map, Hj. reflexivity. }
pose proof (FV 0%nat _ eq_refl) as F32. pose proof (FV 1%nat _ eq_refl) as F33. pose proof (FV 2%nat _ eq_refl) as F34.
pose proof (FV 3%nat _ eq_refl) as F35. pose proof (FV 4%nat _ eq_refl) as F36. pose proof (FV 5%nat _ eq_refl) as F37.
pose proof (FV 6%nat _ eq_refl) as F38. pose proof (FV 7%nat _ eq_refl) as F39. pose proof (FV 8%nat _ eq_refl) as F40.
pose proof (FV 9%nat _ eq_refl) as F41. pose proof (FV 10%nat _ eq_refl) as F42.
cbn [Nat.add] in F32, F33, F34, F35, F36, F37, F38, F39, F40, F41, F42.
rreg HS (1%bv : bv 5) Qra. rreg HS (10%bv : bv 5) Qa0.
eapply (SRr_ret_at trasegs tratbl_lib tratbl_lib_ok Hwx W2 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. split; [reflexivity|].
exists (ms_regs ms), (ms_mem ms). eexists. split; [rewrite Qra, F42, Hra; reflexivity|].
split; [cbn [ms_mem]; apply (ajournal_materialize trasegs B LAWS Hsegs); exact HJ|].
split.
{ intros r Hr. unfold acallee_saved in Hr.
assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
clear Hr.
repeat (destruct Hc as [-> | Hc]); [ | | | | | | | | | | | | | | subst r].
+ assert (X : getr (ms_regs ms) (2%bv : bv 5) = getr regs0 (2%bv : bv 5)); [|exact X]. rreg HS (2%bv : bv 5) Rk. rewrite Rk, U2.
replace (spZ regs0 - 192 + 192) with (spZ regs0) by lia. unfold spZ. apply Z_to_bv_bv_unsigned.
+ assert (X : getr (ms_regs ms) (3%bv : bv 5) = getr regs0 (3%bv : bv 5)); [|exact X]. rreg HS (3%bv : bv 5) Rk. rewrite Rk, (HE 3%nat 3%bv eq_refl). apply GK. cbv. tauto.
+ assert (X : getr (ms_regs ms) (4%bv : bv 5) = getr regs0 (4%bv : bv 5)); [|exact X]. rreg HS (4%bv : bv 5) Rk. rewrite Rk, (HE 4%nat 4%bv eq_refl). apply GK. cbv. tauto.
+ assert (X : getr (ms_regs ms) (8%bv : bv 5) = getr regs0 (8%bv : bv 5)); [|exact X]. rreg HS (8%bv : bv 5) Rk. rewrite Rk. exact F41.
+ assert (X : getr (ms_regs ms) (9%bv : bv 5) = getr regs0 (9%bv : bv 5)); [|exact X]. rreg HS (9%bv : bv 5) Rk. rewrite Rk. exact F40.
+ assert (X : getr (ms_regs ms) (18%bv : bv 5) = getr regs0 (18%bv : bv 5)); [|exact X]. rreg HS (18%bv : bv 5) Rk. rewrite Rk. exact F39.
+ assert (X : getr (ms_regs ms) (19%bv : bv 5) = getr regs0 (19%bv : bv 5)); [|exact X]. rreg HS (19%bv : bv 5) Rk. rewrite Rk. exact F38.
+ assert (X : getr (ms_regs ms) (20%bv : bv 5) = getr regs0 (20%bv : bv 5)); [|exact X]. rreg HS (20%bv : bv 5) Rk. rewrite Rk. exact F37.
+ assert (X : getr (ms_regs ms) (21%bv : bv 5) = getr regs0 (21%bv : bv 5)); [|exact X]. rreg HS (21%bv : bv 5) Rk. rewrite Rk. exact F36.
+ assert (X : getr (ms_regs ms) (22%bv : bv 5) = getr regs0 (22%bv : bv 5)); [|exact X]. rreg HS (22%bv : bv 5) Rk. rewrite Rk. exact F35.
+ assert (X : getr (ms_regs ms) (23%bv : bv 5) = getr regs0 (23%bv : bv 5)); [|exact X]. rreg HS (23%bv : bv 5) Rk. rewrite Rk. exact F34.
+ assert (X : getr (ms_regs ms) (24%bv : bv 5) = getr regs0 (24%bv : bv 5)); [|exact X]. rreg HS (24%bv : bv 5) Rk. rewrite Rk. exact F33.
+ assert (X : getr (ms_regs ms) (25%bv : bv 5) = getr regs0 (25%bv : bv 5)); [|exact X]. rreg HS (25%bv : bv 5) Rk. rewrite Rk. exact F32.
+ assert (X : getr (ms_regs ms) (26%bv : bv 5) = getr regs0 (26%bv : bv 5)); [|exact X]. rreg HS (26%bv : bv 5) Rk. rewrite Rk, (HE 26%nat 26%bv eq_refl). apply GK. cbv. tauto.
+ assert (X : getr (ms_regs ms) (27%bv : bv 5) = getr regs0 (27%bv : bv 5)); [|exact X]. rreg HS (27%bv : bv 5) Rk. rewrite Rk, (HE 27%nat 27%bv eq_refl). apply GK. cbv. tauto. }
split; [exact Qa0|].
split.
- intros a Ha. cbn [ms_mem]. apply aview_eq_of. apply HFr. rewrite unsigned_lit_small by lia.
intros (rr & Hin & Hr). cbn [ss_mem ss_PF pf_mem In] in Hin. destruct Hin as [<- | []].
cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hr. clear - Hr. lia.
- intros a Ha. exact (apresent_grows _ _ _ _ HG Ha).
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).


Lemma ntn_kept : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world trasegs) memc mdc k
(memP : word -> option byte) (W2 : world trasegs) (mem2 mem8 : word -> option byte) (spz : Z) (E2 EF : Z -> Prop),
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
sp0 - STK <= spz - TNTN_STK -> spz <= sp0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spz - 192 <= a < spz) -> aview trasegs (w_H W) memP a = aview trasegs (w_H W) memc a) ->
(forall a, apresent (w_H W) memc a -> apresent (w_H W) memP a) ->
acall_kept trasegs B lyc Sc W memP W2 mem2 (spz - 192 - ASTACK) (spz - 192) E2 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spz - TNTN_STK <= a < spz) -> ~ E2 a -> ~ EF a ->
aview trasegs (w_H W2) mem8 a = aview trasegs (w_H W2) mem2 a) ->
(forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem8 a) ->
(forall a, spz - TNTN_STK <= a < spz -> apresent (w_H W2) mem8 a) ->
(forall a, E2 a -> 4096 <= a < alloc_ceiling /\ ~ in_img trasegs a /\ (a < kLowShadowBeg \/ kHighMemBeg <= a)) ->
(forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> ~ E2 (b + i)) ->
(forall cid pos a, In (cid, pos) (frames Sc) -> in_zr a (frame_rng lyc (cid, pos)) -> ~ E2 a) ->
(forall a, EF a -> alloc_ceiling <= a) ->
acall_keptE trasegs B lyc Sc W memc W2 mem8 (spz - TNTN_STK) spz EF.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k memP W2 mem2 mem8 spz E2 EF
HJ Hbud Hsptop K0 P0 (A1 & A2 & A3 & A4 & A5 & A6) K3 P3 PW HE2 HE2b HE2f HEF.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : TNTN_STK = 16576) by reflexivity. assert (HAS : ASTACK = 16384) by reflexivity.
assert (Rsp : alloc_ceiling <= spz - TNTN_STK /\ spz <= 2 ^ 47) by (clear - Hbud Hsptop Hslo Hshi H47 Hceil WS; lia).
split; [|split; [|split; [|split; [|split]]]].
- intros a Ha Hnw HnEF.
rewrite K3; [| clear - Ha C1; lia | exact Hnw | intros X; destruct (HE2 a X) as (X1 & _); clear - X1 Ha; lia | exact HnEF].
rewrite A1; [| exact Ha | clear - Hnw WS HAS; lia]. apply K0; [clear - Ha C1; lia | clear - Hnw WS; lia].
- intros b m i Hb Hi HnE. destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb) as (_ & Hb4096 & Hbceil & _).
rewrite K3; [| clear - Hi Hb4096 Hbceil C1; lia | clear - Hi Hbceil Rsp; lia | exact (HE2b b m i Hb Hi) | exact HnE].
rewrite (A2 b m i Hb Hi (HE2b b m i Hb Hi)). apply K0; [clear - Hi Hb4096 Hbceil C1; lia | clear - Hi Hbceil Rsp WS; lia].
- intros a Him Hno Hne. pose proof (tra_img_range a Him) as Hr.
rewrite K3; [| clear - Hr; lia | clear - Hr Rsp C1; lia | intros X; exact (proj1 (proj2 (HE2 a X)) Him) | intros X; pose proof (HEF a X) as X1; clear - X1 Hr C1; lia].
rewrite (A3 a Him Hno Hne). apply K0; [clear - Hr; lia | clear - Hr Rsp C1 WS; lia].
- intros cid pos a Hin Hr HnE.
destruct (frames_bounds trasegs B LAWS _ _ _ _ _ cid pos HAR Hin) as (HF4096 & HFceil & _).
pose proof (fs_frame_bytes_nonneg cid) as HFB.
assert (Ra : 4096 <= a < alloc_ceiling /\ (in_zr a (frame_rng lyc (cid, pos)) \/ (kLowShadowBeg <= a < kHighMemBeg))).
{ destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr.
- split; [clear - Hr HF4096 HFceil; lia|]. left. exact Hr.
- unfold shadow_addr, SHADOW_OFF in Hr. unfold kLowShadowBeg, kHighMemBeg. clear - Hr HF4096 HFceil HFB C1. lia. }
destruct Ra as [Ra Rk].
assert (HnE2 : ~ E2 a).
{ destruct Rk as [Rk | Rk]; [exact (HE2f cid pos a Hin Rk)|]. intros X. destruct (HE2 a X) as (_ & _ & Hz). clear - Hz Rk. lia. }
rewrite K3; [| clear - Ra C1; lia | clear - Ra Rsp; lia | exact HnE2 | exact HnE].
rewrite (A4 cid pos a Hin Hr HnE2). apply K0; [clear - Ra C1; lia | clear - Ra Rsp WS; lia].
- intros a Ha Hnw Hp. apply P3. apply A5; [exact Ha | clear - Hnw WS HAS; lia | apply P0; exact Hp].
- exact PW.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma nt_mbyte_of_apresent : forall H (m : word -> option byte) a, apresent H m a -> exists b, mbyte trasegs (mrestrict H m) a = Some b.
Proof. intros H m a [EH [b Hb]]. exists b. unfold mbyte, mrestrict. rewrite EH, Hb. reflexivity. Qed.
Lemma nt_val_mem_kept : forall H H' (m m' : word -> option byte) a (n : nat) v,
val_mem trasegs (mrestrict H m) a n v -> (forall x, a <= x < a + Z.of_nat n -> aview trasegs H' m' x = aview trasegs H m x) ->
val_mem trasegs (mrestrict H' m') a n v.
Proof. intros H H' m m' a n v V K j Hj. rewrite <- (V j Hj). apply (mbyte_of_aview trasegs). apply K. lia. Qed.
Theorem tra_new_tree_node2V : tntn_spec2V B.
Proof.
intros fx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs palp frp nln imin imax cidx n0 pal fr pb pm fb fm
HJ Hra Hra4096 Hgp Htp Hal16 Hbud Hsptop Hfrm Ga0 Ga1 Ga2 Ga3 Ga4 Ga5
HinPc HpP0 HpP1 HinFc HfF0 HfF1 Hfr4 HPF Hpa Hfa Hii Himax Hlenp Hlenf Hcidx Hfr1 Hsum
Hnlc1 Hnlc2 Hnl_al Vnc Hn0 Hev Hlive.
pose proof HJ as (HARc & Hlyc & _ & _ & _ & Hfrsc & _ & _ & _ & _ & _ & _ & _ & Hpresc & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : TNTN_STK = 16576) by reflexivity. assert (HAS : ASTACK = 16384) by reflexivity.
assert (HnlC : alloc_ceiling + 16384 + 192 <= nln /\ nln + 2 <= 2 ^ 47) by (clear - Hnlc1 Hnlc2 Hbud Hslo Hceil Hshi H47 WS Hstk0; lia).
assert (HEF : forall a, nln <= a < nln + 2 -> alloc_ceiling <= a) by (intros a Ha; clear - Ha HnlC; lia).
eapply SRr_bind.
{ exact (ntn_p0 fx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs palp frp nln imin imax cidx
HJ Hgp Htp Hal16 Hbud Hsptop Ga0 Ga1 Ga2 Ga3 Ga4 Ga5 Hnlc1 Hnlc2 Hnl_al Hev Hlive). }
cbv beta. intros W2 c1 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & res & memP & -> & HJ2 & Hfrs2 & Hd2 & G2 & G8 & G10 & G18 & G19 & G20 & G21 & G22 & G23 & GK2 & SV2 & KP & PP & Hres).
pose proof HJ2 as (HAR2 & Hly2 & _ & _ & _ & Hfrs2' & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
destruct Hres as [(-> & Ebl & HK) | (Hr4096 & Ebl & HK)].
-
eapply SRr_mono.
{ exact (ntn_pfail fx STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + 1) regs regs2 HJ2 Hra Hal16 Hbud Hsptop G2 G10 GK2 SV2). }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & G310 & KM3 & PM3).
exists fx, ly2, S2, regs3, mem3, md3, 0.
split; [reflexivity|]. split; [exact Hfrm|]. split; [exact HJ3|]. split; [exact HP3|]. split; [exact Hfrs2|]. split; [exact Hd2|]. split; [exact G310|].
split.
{ apply (ntn_kept STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k memP W2 mem2 mem3 (spZ regs) (fun _ => False) (fun a => nln <= a < nln + 2)
HJ Hbud Hsptop KP PP HK).
- intros a Ha _ _ _. exact (KM3 a Ha).
- exact PM3.
- intros a Ha. pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp3 & _). apply Hp3. clear - Ha Hbud Hsptop. lia.
- intros a [].
- intros b m i _ _ [].
- intros c p a _ _ [].
- exact HEF. }
left. split; [reflexivity|]. split; [exact Ebl|].
assert (Hnlin : forall j, 0 <= j < 2 -> aview trasegs (w_H W2) mem3 (nln + j) = aview trasegs (w_H W) memc (nln + j)).
{ intros j Hj. rewrite KM3 by (clear - Hj HnlC C1; lia).
destruct HK as (K1 & _). rewrite (K1 (nln + j)); [| clear - Hj HnlC; lia | clear - Hj Hnlc1 HAS; lia].
apply KP; [clear - Hj HnlC C1; lia | clear - Hj Hnlc1; lia]. }
intros j Hj. rewrite <- (Vnc j Hj). apply (mbyte_of_aview trasegs). apply Hnlin. clear - Hj. lia.
-
pose (k1 := k). pose (regs0 := regs). pose (memM := mem2).
assert (HinN : In (res, NODE_SIZE) (ablocks B ly2 S2)) by (rewrite Ebl; apply in_app_iff; right; left; reflexivity).
assert (HinP : In (pb, pm) (ablocks B ly2 S2)) by (rewrite Ebl; apply in_app_iff; left; exact HinPc).
assert (HinF : In (fb, fm) (ablocks B ly2 S2)) by (rewrite Ebl; apply in_app_iff; left; exact HinFc).
assert (Hsep : forall b m, In (b, m) (ablocks B lyc Sc) -> zdisjoint (b, req_size m) (res, req_size NODE_SIZE)).
{ intros b m Hb. destruct (in_split _ _ Hb) as (l1 & l2 & El).
pose proof (sep_blocks_pos trasegs B LAWS ly2 S2 W2 mem2 md2 (b, m) (res, NODE_SIZE) l1 l2 [] HAR2
ltac:(rewrite Ebl, El, <- app_assoc; reflexivity)) as Hd.
unfold block_rng in Hd. cbn [fst snd] in Hd. exact Hd. }
change (req_size NODE_SIZE) with 56 in Hsep, HK.
assert (HnPF : (res, NODE_SIZE) <> (pb, pm)).
{ intros X. injection X as X1 X2. pose proof (Hsep pb pm HinPc) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
rewrite <- X2 in Hd. change (req_size NODE_SIZE) with 56 in Hd. clear - Hd X1. lia. }
assert (HnFF : (res, NODE_SIZE) <> (fb, fm)).
{ intros X. injection X as X1 X2. pose proof (Hsep fb fm HinFc) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
rewrite <- X2 in Hd. change (req_size NODE_SIZE) with 56 in Hd. clear - Hd X1. lia. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ res NODE_SIZE HAR2 HinN) as (Qr16 & Qr0 & Qr1 & Qrapp & Hnpres & _). change (req_size NODE_SIZE) with 56 in Qr1, Qrapp, Hnpres.
pose proof (blk_off_img _ _ _ _ _ _ res NODE_SIZE HAR2 HinN) as Qrimg. change (req_size NODE_SIZE) with 56 in Qrimg.
assert (KB2 : forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> aview trasegs (w_H W2) mem2 (b + i) = aview trasegs (w_H W) memc (b + i)).
{ intros b m i Hb Hi. destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HARc Hb) as (_ & Hb4096 & Hbceil & _).
destruct HK as (_ & K2 & _). rewrite (K2 b m i Hb Hi); [| pose proof (Hsep b m Hb) as Hd; unfold zdisjoint in Hd; cbn [fst snd] in Hd; clear - Hd Hi; lia].
apply KP; [clear - Hi Hb4096 Hbceil C1; lia | clear - Hi Hbceil Hbud Hslo Hceil WS; lia]. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ pb pm HARc HinPc) as (_ & _ & _ & _ & _ & _ & Hpm0).
destruct (al_blocks _ _ LAWS _ _ _ _ _ fb fm HARc HinFc) as (_ & _ & _ & _ & _ & _ & Hfm0).
pose proof (req_size_pos pm ltac:(lia)) as [_ Hrpm]. pose proof (req_size_pos fm ltac:(lia)) as [_ Hrfm].
assert (HpaM : arr8 trasegs (mrestrict (w_H W2) mem2) palp pal).
{ apply (arr8_frame trasegs _ _ palp pal Hpa). intros a Ha. apply (mbyte_of_aview trasegs).
replace a with (pb + (a - pb)) by lia. apply (KB2 pb pm (a - pb) HinPc). clear - Ha HpP0 HpP1 Hrpm. lia. }
assert (HfaM : arr32 trasegs (mrestrict (w_H W2) mem2) frp fr).
{ apply (arr32_frame trasegs _ _ frp fr Hfa). intros a Ha. apply (mbyte_of_aview trasegs).
replace a with (fb + (a - fb)) by lia. apply (KB2 fb fm (a - fb) HinFc). clear - Ha HfF0 HfF1 Hrfm. lia. }
assert (HNW : forall blc i lyq, In (res, NODE_SIZE) blc -> 0 <= i < 56 -> awr_byte STK sp0 FP (ablocks B ly S) blc lyq own (res + i)).
{ intros blc i lyq Hin Hi. exact (awr_new_block trasegs B LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ly2 S2 W2 mem2 md2 res NODE_SIZE blc i lyq
HJ HAR2 Ebl ltac:(unfold NODE_SIZE; lia) Hin Hi). }
assert (EFA : forall c p, frame_addr ly2 c p = frame_addr lyc c p).
{ intros c p. unfold frame_addr. destruct Hly2 as (_ & _ & _ & _ & _ & -> & _). destruct Hlyc as (_ & _ & _ & _ & _ & -> & _). reflexivity. }
assert (Hnl1 : spZ regs0 <= nln) by exact Hnlc1.
assert (Hnl2 : nln + 2 <= sp0) by exact Hnlc2.
assert (KS2 : forall j, 0 <= j < 2 -> aview trasegs (w_H W2) mem2 (nln + j) = aview trasegs (w_H W) memc (nln + j)).
{ intros j Hj. destruct HK as (K1 & _). rewrite (K1 (nln + j)); [| clear - Hj HnlC; lia | clear - Hj Hnlc1 HAS; lia].
apply KP; [clear - Hj HnlC C1; lia | clear - Hj Hnlc1; lia]. }
assert (Qsp : alloc_ceiling + 16384 <= spZ regs - 192 /\ spZ regs <= 2 ^ 47) by (clear - Hbud Hsptop Hslo Hshi H47 Hceil WS; lia).
ltac2:(satvl saved_ok_kept using (sat_vars ()) as SVK).
eapply SRr_bind.
{ ltac2:(satvl ntn_p1 using (sat_vars ()) as LEM1). exact (LEM1 fx regs2 md2 HJ2 Hfrm G2 G8 G10 G18 G19 G20 G21 G22 G23 GK2 SV2). }
cbv beta. intros W3 c3 _ (-> & fy3 & regs3 & mem3 & md3 & -> & HI3 & G312 & G311 & G320 & G324 & G325 & Z3 & Vmin3 & Vmax3 & SV3).
assert (Z3' : forall j, 0 <= j < 12 -> val_mem trasegs (mrestrict (w_H W2) mem3) (spZ regs - 192 + (8 + 8 * j)) 8 0).
{ intros j Hj. replace (spZ regs - 192 + (8 + 8 * j)) with (spZ regs - 192 + 8 + 8 * j) by lia. exact (Z3 j Hj). }
eapply SRr_bind.
{ ltac2:(satvl ntn_loop1 using (sat_vars ()) as LEM2). eapply (LEM2 (Z.to_nat (imax - imin)) fy3 regs3 mem3 md3 imin); [clear - Hii; lia | clear - Hii; lia |].
split; [exact HI3|]. split; [exact G312|]. split; [exact G311|].
exists 0, 0, 0, 0, 0, 0. rewrite !nlp_nil. cbn [wsum wdot fold_right].
split; [exact (Z3' 6 ltac:(lia))|]. split; [exact (Z3' 7 ltac:(lia))|]. split; [exact (Z3' 8 ltac:(lia))|].
split; [exact (Z3' 9 ltac:(lia))|]. split; [exact (Z3' 10 ltac:(lia))|]. split; [exact (Z3' 11 ltac:(lia))|].
repeat (split; [lia|]). repeat split; apply is_intd_zero. }
cbv beta. intros W4 c4 _ (-> & fy4 & regs4 & mem4 & md4 & -> & HI4 & GK4 & KM4 & PM4).
destruct HI4 as (HI4 & G412 & G411 & xs0 & xs1 & xs2 & xm0 & xm1 & xm2 & V56 & V64 & V72 & V80 & V88 & V96 & Rs0 & Rs1 & Rs2 & Rm0 & Rm1 & Rm2 & Is0 & Is1 & Is2 & Im0 & Im1 & Im2).
rewrite !nlp_full in Is0, Is1, Is2, Im0, Im1, Im2.
assert (SV4 : obj_at trasegs (mrestrict (w_H W2) mem4) (spZ regs - 192) LAY_NTF (ntf_vals regs)).
{ apply (SVK mem3 mem4 SV3). intros a Ha. apply KM4; [clear - Ha Qsp C1; lia | clear - Ha; lia]. }
eapply SRr_bind.
{ ltac2:(satvl ntn_meandiv using (sat_vars ()) as LEM3).
eapply (LEM3 fy4 regs4 mem4 md4 xs0 xs1 xs2 xm0 xm1 xm2 HI4);
[ rewrite (GK4 (20%bv : bv 5) ltac:(cbv; tauto)); exact G320 | rewrite (GK4 (24%bv : bv 5) ltac:(cbv; tauto)); exact G324
| rewrite (GK4 (25%bv : bv 5) ltac:(cbv; tauto)); exact G325
| exact V56 | exact V64 | exact V72 | exact V80 | exact V88 | exact V96 | exact Rs0 | exact Rs1 | exact Rs2 | exact Rm0 | exact Rm1 | exact Rm2
| exact Is0 | exact Is1 | exact Is2 | exact Im0 | exact Im1 | exact Im2 ]. }
cbv beta. intros W5 c5 _ (-> & fy5 & regs5 & mem5 & md5 & -> & HI5 & G512 & G513 & G514 & GK5 &
(mn0 & mn1 & mn2 & M16 & M24 & M32 & Rmn0 & Rmn1 & Rmn2 & Qmn0 & Qmn1 & Qmn2 & Lmn0 & Lmn1 & Lmn2) & KM5 & PM5).
assert (SV5 : obj_at trasegs (mrestrict (w_H W2) mem5) (spZ regs - 192) LAY_NTF (ntf_vals regs)).
{ apply (SVK mem4 mem5 SV4). intros a Ha. apply KM5; [clear - Ha Qsp C1; lia | clear - Ha Qr1 Qsp; lia]. }
assert (Z5 : forall j, 0 <= j < 6 -> val_mem trasegs (mrestrict (w_H W2) mem5) (spZ regs - 192 + (8 + 8 * j)) 8 0).
{ intros j Hj. apply (nt_val_mem_kept (w_H W2) (w_H W2) mem3 mem5 _ 8 0 (Z3' j ltac:(lia))).
intros x Hx. cbn in Hx. rewrite KM5 by (clear - Hx Hj Qsp Qr1 C1; lia). apply KM4; [clear - Hx Hj Qsp C1; lia | clear - Hx Hj; lia]. }
eapply SRr_bind.
{ ltac2:(satvl ntn_loop2 using (sat_vars ()) as LEM4). eapply (LEM4 (Z.to_nat (imax - imin)) fy5 regs5 mem5 md5 imin); [clear - Hii; lia | clear - Hii; lia |].
split; [exact HI5|].
split; [rewrite (GK5 (20%bv : bv 5) ltac:(cbv; tauto)), (GK4 (20%bv : bv 5) ltac:(cbv; tauto)); exact G320|].
split; [exact G514|]. split; [exact G512|]. split; [exact G513|].
split; [exact M16|]. split; [exact M24|]. split; [exact M32|].
exists 0, 0, 0, 0. rewrite !nlp_nil, Z.sub_diag. cbn [wsum fold_right neq_meanb existsb].
split; [exact (Z5 0 ltac:(lia))|]. split; [exact (Z5 1 ltac:(lia))|]. split; [exact (Z5 2 ltac:(lia))|].
split; [exact (Z5 3 ltac:(lia))|]. split; [exact (Z5 4 ltac:(lia))|]. split; [exact (Z5 5 ltac:(lia))|].
repeat (split; [lia|]). split; [apply is_intd_zero|]. repeat split; apply variance_init. }
cbv beta. intros W6 c6 _ (-> & fy6 & regs6 & mem6 & md6 & -> & HI6 & GK6 & KM6 & PM6).
destruct HI6 as (HI6 & G620 & G614 & G612 & G613 & M16' & M24' & M32' & xs & xv0 & xv1 & xv2 & W8 & W16 & W24 & W32 & W40 & W48 & Rxs & Rv0 & Rv1 & Rv2 & Is' & Hv0 & Hv1 & Hv2).
rewrite !nlp_full in Is', Hv0, Hv1, Hv2.
assert (SV6 : obj_at trasegs (mrestrict (w_H W2) mem6) (spZ regs - 192) LAY_NTF (ntf_vals regs)).
{ apply (SVK mem5 mem6 SV5). intros a Ha. apply KM6; [clear - Ha Qsp C1; lia | clear - Ha; lia]. }
eapply SRr_bind.
{ ltac2:(satvl ntn_va using (sat_vars ()) as LEM5).
exact (LEM5 fy6 regs6 mem6 md6 xs xv0 xv1 xv2 HI6 W8 W16 W24 W32 W40 W48 Rxs Rv0 Rv1 Rv2 Is' Hv0 Hv1 Hv2). }
cbv beta. intros W7 c7 _ (-> & fy7 & regs7 & mem7 & md7 & cut & -> & HI7 & G713 & Hcut & Hsplit & GK7 & KM7 & PM7).
assert (SV7 : obj_at trasegs (mrestrict (w_H W2) mem7) (spZ regs - 192) LAY_NTF (ntf_vals regs)).
{ apply (SVK mem6 mem7 SV6). intros a Ha. apply KM7; [clear - Ha Qsp C1; lia | clear - Ha; lia]. }
pose proof HI7 as (HJ7 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & KEPT7 & PRES7).
assert (KS7 : forall j, 0 <= j < 2 -> aview trasegs (w_H W2) mem7 (nln + j) = aview trasegs (w_H W) memc (nln + j)).
{ intros j Hj. rewrite <- (KS2 j Hj). apply KEPT7; [clear - Hj HnlC C1; lia | clear - Hj Hnlc1; lia | unfold NODE_SIZE; clear - Hj Qr1 HnlC; lia]. }
assert (Vn7 : val_mem trasegs (mrestrict (w_H W2) mem7) nln 2 n0).
{ apply (nt_val_mem_kept (w_H W) (w_H W2) memc mem7 nln 2 n0 Vnc). intros x Hx. cbn in Hx.
replace x with (nln + (x - nln)) by lia. apply KS7. clear - Hx. lia. }
pose proof HJ7 as (HAR7 & Hly7 & _). pose proof Hly7 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo7 & Ehi7 & _).
destruct (rg_stack_shadow B LAWS W2 ly2 S2 mem7 md7 nln 2 HAR7
ltac:(rewrite Elo7; clear - Hnlc1 Hbud Hslo WS; lia) ltac:(rewrite Ehi7; clear - Hnlc2 Hshi; lia) ltac:(lia)) as [HRA7 _].
eapply SRr_mono.
{ ltac2:(satvl ntn_tail using (sat_vars ()) as LEM6). exact (LEM6 fy7 regs7 mem7 md7 cut HI7 G713 Hcut SV7 Vn7 HRA7). }
cbv beta. intros Wt c8 _ (-> & fy8 & regs8 & mem8 & md8 & -> & Hfrm8 & HJ8 & HP8 & G810 & Vcut & Vcidx & Vleaf & Vn8 & KM8 & PM8).
exists fy8, ly2, S2, regs8, mem8, md8, res.
split; [reflexivity|]. split; [exact Hfrm8|]. split; [exact HJ8|]. split; [exact HP8|]. split; [exact Hfrs2|]. split; [exact Hd2|]. split; [exact G810|].
pose proof HI3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PRES3).
pose proof HI4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PRES4).
split.
{ apply (ntn_kept STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k memP W2 mem2 mem8 (spZ regs) (fun a => res <= a < res + 56) (fun a => nln <= a < nln + 2)
HJ Hbud Hsptop KP PP HK).
- intros a Ha Hnw HnE Hnn. rewrite KM8; [| exact Ha | clear - HnE; lia | exact Hnn]. apply KEPT7; [exact Ha | exact Hnw | unfold NODE_SIZE; exact HnE].
- intros a Ha. apply PM8. apply PRES7. exact Ha.
- intros a Ha. pose proof HJ8 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp8 & _). apply Hp8. clear - Ha Hbud Hsptop. lia.
- intros a Ha. split; [clear - Ha Qr0 Qr1; lia|]. split.
+ intros Him. pose proof (tra_img_range a Him) as Hr. unfold off_img in Qrimg. clear - Ha Hr Qrimg. lia.
+ destruct Qrapp as [_ Qz]. unfold kLowShadowBeg, kHighMemBeg in *. clear - Ha Qz. lia.
- intros b m i Hb Hi. pose proof (Hsep b m Hb) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. clear - Hd Hi. lia.
- intros c p a Hcp Hr. pose proof (sep_block_frame trasegs _ LAWS ly2 S2 _ _ _ res NODE_SIZE c p HAR2 HinN ltac:(rewrite Hfrs2; exact Hcp)) as Dd.
rewrite EFA in Dd. unfold zdisjoint in Dd. cbn [fst snd] in Dd. change (req_size NODE_SIZE) with 56 in Dd.
unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr. clear - Dd Hr. lia.
- exact HEF. }
right. split; [exact Hr4096|]. split; [exact Ebl|]. split; [exact Vn8|].
assert (KN8 : forall (m : word -> option byte) a (n : nat) v, val_mem trasegs (mrestrict (w_H W2) m) a n v ->
(forall x, a <= x < a + Z.of_nat n -> aview trasegs (w_H W2) mem8 x = aview trasegs (w_H W2) m x) ->
val_mem trasegs (mrestrict (w_H W2) mem8) a n v).
{ intros m a n v V K. exact (nt_val_mem_kept (w_H W2) (w_H W2) m mem8 a n v V K). }
assert (K78 : forall x, res <= x < res + 48 -> aview trasegs (w_H W2) mem8 x = aview trasegs (w_H W2) mem7 x).
{ intros x Hx. apply KM8; [clear - Hx Qr0 Qr1 C1; lia | clear - Hx; lia | clear - Hx Qr1 HnlC; lia]. }
assert (K67 : forall x, res <= x < res + 56 -> aview trasegs (w_H W2) mem7 x = aview trasegs (w_H W2) mem6 x).
{ intros x Hx. apply KM7; [clear - Hx Qr0 Qr1 C1; lia | clear - Hx Qr1 Qsp; lia]. }
assert (K56 : forall x, res <= x < res + 56 -> aview trasegs (w_H W2) mem6 x = aview trasegs (w_H W2) mem5 x).
{ intros x Hx. apply KM6; [clear - Hx Qr0 Qr1 C1; lia | clear - Hx Qr1 Qsp; lia]. }
assert (K45 : forall x, res + 40 <= x < res + 48 -> aview trasegs (w_H W2) mem5 x = aview trasegs (w_H W2) mem4 x).
{ intros x Hx. apply KM5; [clear - Hx Qr0 Qr1 C1; lia | clear - Hx; lia]. }
assert (K34 : forall x, res <= x < res + 56 -> aview trasegs (w_H W2) mem4 x = aview trasegs (w_H W2) mem3 x).
{ intros x Hx. apply KM4; [clear - Hx Qr0 Qr1 C1; lia | clear - Hx Qr1 Qsp; lia]. }
assert (MK : forall off v, 16 <= off -> off + 8 <= 40 -> val_mem trasegs (mrestrict (w_H W2) mem6) (res + off) 8 v -> val_mem trasegs (mrestrict (w_H W2) mem8) (res + off) 8 v).
{ intros off v Ho1 Ho2 V. apply (KN8 mem6 _ 8%nat v V). intros x Hx. cbn in Hx. rewrite K78 by lia. apply K67. lia. }
assert (IK : forall off v, 40 <= off -> off + 4 <= 48 -> val_mem trasegs (mrestrict (w_H W2) mem3) (res + off) 4 v -> val_mem trasegs (mrestrict (w_H W2) mem8) (res + off) 4 v).
{ intros off v Ho1 Ho2 V. apply (KN8 mem3 _ 4%nat v V). intros x Hx. cbn in Hx. rewrite K78, K67, K56, K45 by lia. apply K34. lia. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ res NODE_SIZE (proj1 HJ8) HinN) as (_ & _ & _ & _ & Hnpres8 & _). change (req_size NODE_SIZE) with 56 in Hnpres8.
destruct (val_mem_of_present8 trasegs (mrestrict (w_H W2) mem8) res
ltac:(intros i Hi; apply nt_mbyte_of_apresent; apply (proj1 (Hnpres8 (res + i) ltac:(lia))))) as (c0 & Rc0 & Vc0).
destruct (val_mem_of_present8 trasegs (mrestrict (w_H W2) mem8) (res + 8)
ltac:(intros i Hi; apply nt_mbyte_of_apresent; rewrite <- Z.add_assoc; apply (proj1 (Hnpres8 (res + (8 + i)) ltac:(lia))))) as (c1 & Rc1 & Vc1).
exists (mkTN res [mn0; mn1; mn2] imin imax cut cidx). cbn [tn_addr tn_imin tn_imax tn_cidx tn_cut tn_mean].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split.
{ cbn [tree_at tn_addr tn_mean]. split; [clear - Hr4096; lia|]. split; [reflexivity|]. exists c0, c1.
cbn [obj_at LAY_Node node_vals tn_mean tn_imin tn_imax tn_cut tn_cidx app]. unfold field_ok. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add Z.of_N Z.mul Pos.mul].
rewrite Z.add_0_r.
split; [split; [exact Vc0 | exact Rc0]|]. split; [split; [exact Vc1 | exact Rc1]|].
split; [split; [apply MK; [lia | lia | exact M16'] | exact Rmn0]|]. split; [split; [apply MK; [lia | lia | exact M24'] | exact Rmn1]|].
split; [split; [apply MK; [lia | lia | exact M32'] | exact Rmn2]|].
split; [split; [apply IK; [lia | lia | exact Vmin3] | clear - Hii Himax; lia]|]. split; [split; [apply IK; [lia | lia | exact Vmax3] | clear - Hii Himax; lia]|].
split; [split; [exact Vcut | clear - Hcut; lia]|]. split; [split; [exact Vcidx | clear - Hcidx; lia]|]. split; [split; [exact Vleaf | lia]|]. exact I. }
split.
{ unfold tnode_wf. cbn [tn_cut tn_cidx tn_imin tn_imax tn_mean]. split; [exact Hcut|]. split; [exact Hcidx|]. split; [exact Hii|]. split; [clear - Himax; lia|].
split; [reflexivity|]. repeat constructor; lia. }
split.
{ intros d Hd. assert (Hd3 : d = 0 \/ d = 1 \/ d = 2) by lia.
destruct Hd3 as [-> | [-> | ->]]; cbn [Z.to_nat nth Pos.to_nat Pos.iter_op]; [exact Qmn0 | exact Qmn1 | exact Qmn2]. }
exact Hsplit.
Qed.
End S.
