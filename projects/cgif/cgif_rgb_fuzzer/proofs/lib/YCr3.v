(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0p YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI01.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YF9i YCeb YCe8 YCfq YCdy YCfr YCe9 YCi1 YCie YCph YCrr YCrd YCrc.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG0n YG0o YG0t YG0r YG0q YC00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Definition RT_stack_malloc_ra : Z := 0x812e4.
Definition RT_memset_ra : Z := 0x813f4.
Definition RT_rd1_ra : Z := 0x81408.
Definition RT_rd2_ra : Z := 0x81420.
Definition RT_rd3_ra : Z := 0x81434.
Definition RT_rd4_ra : Z := 0x81448.
Definition RT_rd5_ra : Z := 0x81464.
Definition RT_newgif_ra : Z := 0x81498.
Definition RT_rfc1_ra : Z := 0x814b4.
Definition RT_addframe_ra : Z := 0x814c8.
Definition RT_free_ra : Z := 0x814d0.
Definition RT_rfc2_ra : Z := 0x814e8.
Definition RT_close_ra : Z := 0x814f4.
Definition A_writecb_h : Z := 0x81658.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition RTBx : sv := SOff 32 0.
Definition RTBspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition rt_extra : list word := [Z_to_bv 64 SB].
Definition rt_regions0 : smem := [ stack_region 176; got_region; bcell_region 32; uar_got_region; uar_cell_region ].
Definition rt_atoms0 : list (nat * afact) := [ (2%nat, mkAF (2^46) (2^47) 4); (11%nat, mkAF 0 (2^26 - 1) 0); (32%nat, mkAF SB SB 0) ].
Definition ss_rt0 : sstate := mkSS A_LLVMF sr_atoms rt_regions0 None (mkFacts rt_atoms0 [] []).
Record rtcx := mkRTCX {
c_ly : alayout; c_S : astate; c_W : world trbsegs; c_regs : bvmap 5 word; c_mem : word -> option byte; c_md : Model;
c_p : Z; c_n : Z; c_fpos : Z; c_sp1 : Z; c_E0 : env }.
Definition rt_base (B : asyms) (cx : rtcx) : Prop :=
afn_pre trbsegs B LLVMF_STK (c_ly cx) (c_S cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [] /\
raZ (c_regs cx) = RA_LLVMF /\
getr (c_regs cx) 10 = w64 (c_p cx) /\ getr (c_regs cx) 11 = w64 (c_n cx) /\
((c_n cx = 0 /\ c_p cx = A_EMPTY) \/ (0 < c_n cx < 2 ^ 26 /\ In (c_p cx, c_n cx) (ablocks B (c_ly cx) (c_S cx)))) /\
frames (c_S cx) = [] /\ bud_ok (c_S cx) EV_RLIBV CN_RLIB WT_RLIB HL_RLIB   /\ blocks_bytes (c_S cx) + LIVE_LIB <= LIVE_MAX /\
arodata_ok B (aview trbsegs (w_H (c_W cx)) (c_mem cx)) /\
c_sp1 cx = 32 * ((spZ (c_regs cx) + -160) / 32) /\
(forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (c_E0 cx) n = getr (c_regs cx) r) /\
ew (c_E0 cx) 32 = Z_to_bv 64 SB /\
bv_unsigned (ew (c_E0 cx) 2) = spZ (c_regs cx).
Definition rt_F (cx : rtcx) : Z := frame_addr (c_ly cx) 2 (c_fpos cx).
Definition rt_FL (cx : rtcx) : Z := flag_addr (c_ly cx) 2 (c_fpos cx).
Definition rt_E (cx : rtcx) (E : env) : Prop :=
(forall n, (n < 33)%nat -> ew E n = ew (c_E0 cx) n) /\
ew E 70 = Z_to_bv 64 (c_sp1 cx) /\ ew E 75 = Z_to_bv 64 (rt_F cx) /\ ew E 87 = Z_to_bv 64 (rt_FL cx) /\ ew E 88 = Z_to_bv 64 (SB + rt_F cx / 8).
Definition rt_post (B : asyms) (cx : rtcx) : world trbsegs -> config -> Prop :=
trb_rlibV_post B (c_regs cx) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx).
Definition rt_from (B : asyms) (ss : sstate)
(INV : rtcx -> env -> Z -> alayout -> astate -> world trbsegs -> machine_state -> Model -> Prop) : Prop :=
forall (cx : rtcx) (E : env) (k : Z) ly3 S3 W3 (ms3 : machine_state) md3,
rt_base B cx -> rt_E cx E -> frm_zero fp_csr ->
ajournal trbsegs B LLVMF_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
[(2, c_fpos cx)] ly3 S3 W3 (ms_mem ms3) md3 k ->
frames S3 = [(2, c_fpos cx)] ->
INV cx E k ly3 S3 W3 ms3 md3 ->
st_ok trbsegs E ss (restrict (w_H W3) ms3) ->
SRr trbsegs W3 (mkCfg ms3 md3) (rt_post B cx).
Lemma rt_bv_j : forall B STK sp0 FP ly S W mem md own ly3 S3 W3 mem3 md3 k J F,
ajournal trbsegs B STK sp0 FP ly S W mem md own ly3 S3 W3 mem3 md3 k -> k <= J -> 0 <= F -> rbv S S3 J F.
Proof.
intros B STK sp0 FP ly S W mem md own ly3 S3 W3 mem3 md3 k J F (_ & _ & _ & _ & _ & _ & D & K & _) HJ HF.
apply (rbv_of_jbud S S3 k J F D); [split; [exact K | exact HJ] | exact HF].
Qed.
Definition INV_0 (B : asyms) (kmax : Z) : rtcx -> env -> Z -> alayout -> astate -> world trbsegs -> machine_state -> Model -> Prop :=
fun cx E k ly3 S3 W3 ms3 md3 => k <= kmax /\ ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx).
Definition rt_ch (cx : rtcx) : list (Z * Z * Z) :=
if spZ (c_regs cx) + 16 <? ly_top (c_ly cx) then [(spZ (c_regs cx), raZ (c_regs cx), s0Z (c_regs cx))] else [].
Lemma rt_ch_spine : forall cx, spine (rt_ch cx) = (if spZ (c_regs cx) + 16 <? ly_top (c_ly cx) then [raZ (c_regs cx)] else []).
Proof. intros cx. unfold rt_ch. destruct (spZ (c_regs cx) + 16 <? ly_top (c_ly cx)); reflexivity. Qed.
Lemma rt_ctx_in : forall cx (site : Z) (L : list (list Z)),
raZ (c_regs cx) = RA_LLVMF -> In [site] L -> In [site; RA_LLVMF] L -> In (site :: spine (rt_ch cx)) L.
Proof.
intros cx site L Hra H1 H2. rewrite rt_ch_spine. destruct (spZ (c_regs cx) + 16 <? ly_top (c_ly cx)); [rewrite Hra; exact H2 | exact H1].
Qed.
Lemma rt_E_havoc : forall cx E N vs, (89 <= N)%nat -> rt_E cx E -> rt_E cx (havoc E N vs).
Proof.
intros cx E N vs HN (AG & E70 & E75 & E87 & E88). unfold rt_E. rewrite !ew_havoc_old by lia.
split; [|split; [exact E70 | split; [exact E75 | split; [exact E87 | exact E88]]]].
intros n Hn. rewrite ew_havoc_old by lia. apply AG. exact Hn.
Qed.
Lemma rt_E_ewset : forall cx E n w, (89 <= n)%nat -> rt_E cx E -> rt_E cx (ewset E n w).
Proof.
intros cx E n w HN (AG & E70 & E75 & E87 & E88). unfold rt_E. rewrite !ew_ewset_other by lia.
split; [|split; [exact E70 | split; [exact E75 | split; [exact E87 | exact E88]]]].
intros m Hm. rewrite ew_ewset_other by lia. apply AG. exact Hm.
Qed.
Lemma denot_havoc_below : forall E k l e, sv_atoms_lt k e = true -> sv_denot (havoc E k l) e = sv_denot E e.
Proof. intros E k l e He. apply (sv_denot_agree k E); [apply env_agree_havoc_ge; [lia | apply env_agree_refl] | exact He]. Qed.

Lemma rt_trace_in : forall (pcf ra : Z) (regsT : bvmap 5 word) (cx : rtcx),
raZ (c_regs cx) = RA_LLVMF -> raZ regsT = ra ->
(pcf = 0x53508 /\ ra = 0x814d0) ->
In (call_trace0 pcf regsT (rt_ch cx)) Trb_universe.
Proof.
intros pcf ra regsT cx Hra0 Hra Hpc.
rewrite call_trace_of_spine, rt_ch_spine, Hra, Hra0.
destruct Hpc as [-> ->];
(destruct (spZ (c_regs cx) + 16 <? ly_top (c_ly cx)); apply TRACES_LLVMFuzzerTestOneInput_U; vm_compute; repeat (first [left; reflexivity | right])).
Qed.
Section RT.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL.
Lemma rt_chain : forall ly (rd rd' : reader) (regs : bvmap 5 word) sp',
achain ly rd (spZ regs) (s0Z regs) [] -> ly_top ly <= 2 ^ 64 ->
(forall a, spZ regs <= a < 2 ^ 64 -> rd' a = rd a) ->
rdword rd' (spZ regs - 8) = Some (raZ regs) -> rdword rd' (spZ regs - 16) = Some (s0Z regs) -> 4096 <= raZ regs ->
alloc_ceiling <= spZ regs -> spZ regs mod 8 = 0 -> sp' + 16 <= spZ regs ->
achain ly rd' sp' (spZ regs) (if spZ regs + 16 <? ly_top ly then [(spZ regs, raZ regs, s0Z regs)] else []).
Proof.
intros ly rd rd' regs sp' Hch Htop64 Hk H8 H16 Hra Hceil Hal Hsp'.
destruct (Z.ltb_spec (spZ regs + 16) (ly_top ly)) as [Hlt | Hge].
- replace (spZ regs - 8) with (spZ regs + -8) in H8 by lia. replace (spZ regs - 16) with (spZ regs + -16) in H16 by lia.
apply (achain_push ly rd rd' (spZ regs) (s0Z regs) (raZ regs) [] sp' Hch Htop64 Hk);
[replace (spZ regs - 8) with (spZ regs + -8) by lia; exact H8 | replace (spZ regs - 16) with (spZ regs + -16) by lia; exact H16
| exact Hra | exact Hceil | exact Hal | lia | exact Hsp'].
- left. split; [right; left; lia | reflexivity].
Qed.
Lemma rt_entry : forall W ly S regs mem md p n,
afn_pre trbsegs B LLVMF_STK ly S W regs mem md [] ->
getr regs 10 = w64 p -> getr regs 11 = w64 n ->
((n = 0 /\ p = A_EMPTY) \/ (0 < n < 2 ^ 26 /\ In (p, n) (ablocks B ly S))) ->
st_ok trbsegs (Ereg regs rt_extra) ss_rt0 (restrict (w_H W) (mkst regs (Z_to_bv 64 A_LLVMF) mem (seg_rom trbsegs))).
Proof.
intros W ly S regs mem md p n HPRE H10 H11 Hpn.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (FFS : LLVMF_STK = 32768) by reflexivity.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell. rewrite HBguar, HBuar in Kguar. rewrite HBuar in Kuar.
rewrite restrict_mkst_fx.
set (E := Ereg regs rt_extra).
assert (E2 : ew E 2 = getr regs 2) by (subst E; exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E11 : ew E 11 = Z_to_bv 64 n) by (subst E; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (Hn : 0 <= n < 2 ^ 26) by (destruct Hpn as [[-> _] | [Hn _]]; lia).
unfold ss_rt0. apply (entry_st_ok_full trbsegs); change (Ereg regs rt_extra) with E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold rt_regions0, stack_region, got_region, bcell_region, uar_got_region, uar_cell_region.
repeat apply Forall_cons; try apply Forall_nil.
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. rewrite Usp.
split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. apply (apresent_writable trbsegs). apply Hpres. lia.
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. unfold A_GOT_shadow.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 668240) at 1.
apply (chunk_ok_val trbsegs E _ 0 668240 8 (SLit A_shadow_glob) A_shadow_glob); [reflexivity | unfold A_shadow_glob; zside | zside |].
exact (val_mem_of_rdword trbsegs (w_H W) mem _ _ Kgot).
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. unfold A_shadow_glob.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 701048) at 1.
apply (chunk_ok_val trbsegs E _ 0 701048 8 (SOff 32 0) SB);
[cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
exact (val_mem_of_rdword trbsegs (w_H W) mem _ _ Kcell).
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. unfold A_GOT_uar.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 668328) at 1.
apply (chunk_ok_val trbsegs E _ 0 668328 8 (SLit A_uar_glob) A_uar_glob); [reflexivity | unfold A_uar_glob; zside | zside |].
exact (val_mem_of_rdword trbsegs (w_H W) mem _ _ Kguar).
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. unfold A_uar_glob.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 701056) at 1.
apply (chunk_ok_val trbsegs E _ 0 701056 4 (SLit 1) 1); [reflexivity | zside | zside |].
exact (val_mem_of_rd32 trbsegs (w_H W) mem _ _ Kuar).
- apply pairwise_disjoint_of_extents.
unfold rt_regions0, stack_region, got_region, bcell_region, uar_got_region, uar_cell_region, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi]. cbn [base_val]. rewrite Usp.
unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil C1 C3 FFS Hstk0. clear. unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowShadowBeg, kHighMemBeg. intros. repeat split; lia.
- split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok rt_atoms0]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E11, E32. rewrite !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil C1 C3 FFS Hstk0 Hal16 Hn. clear. unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowShadowBeg, kHighMemBeg. intros.
repeat match goal with |- _ /\ _ => split end; lia.
Qed.
End RT.
End b.
Definition rt_inv_t {fx : YK11.FPState} : Type := rtcx -> env -> Z -> alayout -> astate -> world trbsegs -> machine_state -> Model -> Prop.
Definition rt_fromA {rc : YN05.RunCeil} (B : asyms) (ss : sstate) (INV : forall fx : YK11.FPState, @rt_inv_t fx) : Prop :=
forall fx : YK11.FPState, @rt_from fx rc B ss (INV fx).
