(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0l YK0s YK0o YQ0k YK1d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ0a YQ04 YQ05 YQ0e YQ02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10 YP0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YG0e.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YE1j YF8r YF64 YE0v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Definition ssh_ranges {imgk : img} : list (Z * nat) := [((0x54fb8 + D_2c4), 6%nat); ((0x550d8 + D_2c4), 6%nat)].
Definition tbl_ssh {imgk : img} : ctable := ltac:(img_eval_sel (fun imgk : img => (build_ranges ssh_ranges TEmpty))).
Lemma tbl_ssh_eq {imgk : img} : tbl_ssh = build_ranges ssh_ranges TEmpty. Proof. img_case; lazymatch goal with |- ?l_ = _ => vm_cast_no_check (@eq_refl ctable l_) end. Qed.
Lemma tbl_ssh_ok {imgk : img} : table_ok tfxsegs tbl_ssh.
Proof. img_destruct imgk. all: rewrite tbl_ssh_eq. all: img_apply build_ranges_ok; [img_try (unfold ssh_ranges; repeat constructor; cbn; discriminate) | img_try (img_apply table_ok_empty)]. Qed.
Definition ssh_rodata {imgk : img} : list (Z * Z * list (Z * BinNums.N * Z)) := [((0xa2180 + D_10f0), 8, [(0, 8%N, (0xa4000 + D_10f0))]); ((0xa4000 + D_10f0), 8, [(0, 8%N, (0x9b894 + D_10ec))])].
Lemma ssh_rodata_chk {imgk : img} : forall ly, rodata_chk ly ssh_rodata = true.
Proof. intros ly. img_case; vm_compute. all: img_refl. Qed.
Definition RUN {imgk : img} (s : sstate) := sym_runN tfxsegs tbl_ssh FUEL s.
Definition ss_ent {imgk : img} (pc : Z) : sstate := mkSS pc sr_atoms (map ro_region ssh_rodata) None (mkFacts [] [] []).
Definition e_00 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (ss_ent (0x54fb8 + D_2c4)))))).
Definition e_f8 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (ss_ent (0x550d8 + D_2c4)))))).
Lemma r_00 {imgk : img} : RUN (ss_ent (0x54fb8 + D_2c4)) = (e_00, RS_stopped SR_fetch). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma r_f8 {imgk : img} : RUN (ss_ent (0x550d8 + D_2c4)) = (e_f8, RS_stopped SR_fetch). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition keep_regs : list Z := [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 10].
Definition stub_shape {imgk : img} (ss : sstate) (v : Z) : bool :=
(ss_pc ss =? tfx_A_musl_memset) && (match ss_resv ss with None => true | _ => false end) &&
sv_eqb (sr_get (ss_regs ss) 11%bv) (SLit v) && sv_eqb (sr_get (ss_regs ss) 12%bv) (SOff 11 0) &&
forallb (fun r => sv_eqb (sr_get (ss_regs ss) (Z_to_bv 5 r)) (SOff (Z.to_nat r) 0)) keep_regs.
Lemma shape_00 {imgk : img} : stub_shape e_00 0 = true. Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma shape_f8 {imgk : img} : stub_shape e_f8 0xf8 = true. Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma ssh_phase {imgk : img} : forall (W : world tfxsegs) E ss ss' st ms md,
st_ok tfxsegs E ss (restrict (w_H W) ms) -> sym_runN tfxsegs tbl_ssh FUEL ss = (ss', st) ->
SRr tfxsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
match st with RS_ecall => st_ok_ecall tfxsegs E ss' (restrict (w_H W) ms1) | _ => st_ok tfxsegs E ss' (restrict (w_H W) ms1) end /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\ frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
intros W E ss ss' st ms md HS Hrun.
eapply (SRr_run_gen tfxsegs tbl_ssh tbl_ssh_ok YF8r.Hwx_tfa W FUEL E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF HFr. img_apply SRr_ret. split; [img_refl|]. exists ms1, mat1. split; [img_refl|]. split; [img_try (img_exact HS1)|]. split; [img_try (img_exact HF) | img_try (img_exact HFr)].
Qed.
Section d. Context {imgk : img}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfxsegs B.
Hypothesis TB : TfxSyms B.
Variables (pc v : Z) (e1 : sstate).
Hypothesis Hrun : RUN (ss_ent pc) = (e1, RS_stopped SR_fetch).
Hypothesis Hshape : stub_shape e1 v = true.
Hypothesis Hv : 0 <= v < 256.
Theorem set_shadow_gen : aset_shadow_realizes tfxsegs B pc v.
Proof.
intros ly S W regs mem md cid pos q n HPRE Hin G10 G11 Hn Hq1 Hq2.
pose proof HPRE as (HAR & Hra & Hal16 & Hslo & Htop & HpresE & Hgp & Htp).
pose proof YF8r.Hwx_tfa as Hwx.
set (H := w_H W) in *.
destruct (al_frames _ _ LAWS ly S W mem md cid pos HAR Hin) as (_ & Happ & _ & Hsh).
set (fa := frame_addr ly cid pos) in *. set (fb := fs_frame_bytes cid) in *.
assert (PR : forall a, q <= a < q + n -> apresent H mem a /\ ~ aowned B ly S a).
{ intros a Ha. replace a with (shadow_addr fa + (a - shadow_addr fa)) by img_lia. img_apply Hsh. img_lia. }
assert (RNG : TFX_IMG_END <= q /\ q + n <= 2 ^ 46).
{ destruct Happ as [F0 F1]. pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as CR. unfold YG0h.ASAN_CEIL in CR.
assert (F2 : fa + fb <= 2 ^ 47) by (img_try (destruct F1 as [F1 | [_ F1]]; unfold kLowShadowBeg, YG0h.ASAN_CEIL in *; img_lia)).
assert (D1 : 0 <= fa / 8 <= 2 ^ 44) by (img_try (split; [img_try (img_apply Z.div_pos; img_lia) | img_try (img_apply Z.div_le_upper_bound; img_lia)])).
assert (D2 : fb / 8 <= 2 ^ 44) by (img_try (img_apply Z.div_le_upper_bound; img_lia)).
unfold shadow_addr, SHADOW_OFF, TFX_IMG_END in *. img_lia. }
destruct RNG as [Rlo Rhi]. assert (Rimg0 : 0 <= TFX_IMG_END) by (img_try (unfold TFX_IMG_END; img_lia)).
set (EE := YE0v.Env regs []).
assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (img_try (intros; img_apply YE0v.Env_reg; assumption)).
assert (HS0 : st_ok tfxsegs EE (ss_ent pc) (restrict H (mkst regs (Z_to_bv 64 pc) mem (seg_rom tfxsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_ent, EE, YE0v.Env. img_apply (entry_st_ok_full tfxsegs).
- img_apply regs_ok_Ereg.
- img_case; vm_compute. all: img_refl.
- img_exact (rodata_ok B TB ssh_rodata ly S H mem _ (ssh_rodata_chk ly) (proj1 HAR)).
- img_apply pairwise_disjoint_of_extents. unfold ssh_rodata, ro_region, extent_of_region. cbn [map fst snd YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; img_lia.
- split; [|img_try (split; img_exact I)]. img_exact I. }
unfold cfg_at. img_change (w64 pc) with (Z_to_bv 64 pc).
eapply SRr_bind; [img_try (img_apply (ssh_phase W EE _ _ _ _ _ HS0 Hrun))|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1).
assert (MEQ1 : forall z, ms_mem ms1 z = mem z).
{ intros z. img_apply HF1. intros Hw. destruct (in_wrange_windows EE _ _ Hw) as (b & lo & hi & Ht & Hb).
cbn in Ht. destruct Ht as [Hq|[Hq|[]]]; injection Hq as <- <- <-; cbn [base_val] in Hb; img_lia. }
unfold stub_shape in Hshape. apply andb_prop in Hshape as [Hshape KR]. apply andb_prop in Hshape as [Hshape S12].
apply andb_prop in Hshape as [Hshape S11]. apply andb_prop in Hshape as [Spc Srv].
apply Z.eqb_eq in Spc. assert (Hrv : ss_resv e1 = None) by (img_try (destruct (ss_resv e1); [img_try (discriminate) | img_refl])).
apply sv_eqb_eq in S11. apply sv_eqb_eq in S12. rewrite forallb_forall in KR.
pose proof (st_ok_restrict_mkst tfxsegs H EE _ _ HS1 Hrv) as Hshape1. rewrite Spc in Hshape1.
set (regs1 := ms_regs ms1) in *. set (mem1 := ms_mem ms1) in *.
assert (KEEP1 : forall r, In r keep_regs -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hr. unfold regs1. rewrite (st_ok_restrict_reg tfxsegs H EE e1 ms1 _ HS1). specialize (KR r Hr). apply sv_eqb_eq in KR. rewrite KR.
cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. img_apply EEreg.
unfold keep_regs in Hr. cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [img_refl|]). destruct Hr. }
assert (A10 : getr regs1 10 = w64 q) by (img_try (rewrite <- G10; img_exact (KEEP1 10 ltac:(unfold keep_regs; cbn [In]; tauto)))).
assert (A11 : getr regs1 11 = w64 v) by (img_try (unfold regs1; rewrite (st_ok_restrict_reg tfxsegs H EE e1 ms1 11%bv HS1), S11; img_refl)).
assert (A12 : getr regs1 12 = w64 n).
{ unfold regs1. rewrite (st_ok_restrict_reg tfxsegs H EE e1 ms1 12%bv HS1), S12. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EEreg 11%nat 11%bv eq_refl). img_exact G11. }
assert (A1 : getr regs1 1 = getr regs 1) by (img_try (img_exact (KEEP1 1 ltac:(unfold keep_regs; cbn [In]; tauto)))).
assert (DW : forall a, q <= a < q + n -> writable_at tfxsegs (mrestrict H mem1) a /\ H (Z_to_bv 64 a) = false).
{ intros a Ha. destruct (PR a Ha) as [[Hh [b Hb]] _]. split; [|img_try (img_exact Hh)].
img_apply YE0v.apresent_writable. split; [img_try (img_exact Hh)|]. exists b. unfold mem1. rewrite MEQ1. img_exact Hb. }
set (nn := Z.to_nat n). assert (Hnn : Z.of_nat nn = n) by (img_try ((subst nn; cbv beta); img_lia)).
assert (SOK : store_ok tfxsegs (mrestrict H mem1) (w64 q) nn = true).
{ img_apply store_ok_of_all; unfold w64; rewrite unsigned_lit_small by img_lia; [img_lia|].
intros z Hz. pose proof (proj1 (DW (bv_unsigned z) ltac:(img_lia))) as Wz. unfold writable_at in Wz. rewrite Z_to_bv_bv_unsigned in Wz. img_exact Wz. }
destruct (tfx_memset (w64 q) (w64 v) (w64 n) nn (mrestrict H mem1) (seg_rom tfxsegs) regs1 A10 A11 A12
ltac:(img_try (unfold w64; rewrite unsigned_lit_small by img_lia; img_lia)) SOK ltac:(img_try (unfold w64; rewrite unsigned_lit_small by img_lia; img_lia)))
as (regs2 & Hms & B10 & Hkeep).
rewrite A1, Hra in Hms.
set (cb := Z_to_bv 8 (bv_unsigned (w64 v) mod 256)) in Hms.
set (m1r := mrestrict H mem1) in *. set (m2r := wbytes m1r (w64 q) (repeat cb nn)) in Hms.
set (mem2 := munrestrict H mem1 m2r).
rewrite Hshape1. fold regs1 mem1.
eapply (SRr_msteps tfxsegs Hwx W); [img_try (rewrite restrict_mkst_fx; img_exact Hms)|].
intros model' Hsbm _.
pose proof (same_but_materialized_trans _ _ _ (with_vm_backing_same md mat1) Hsbm) as HSBM.
img_change (unrestrict H mem1 (mkst regs2 (getr regs 1) m2r (seg_rom tfxsegs))) with (mkst regs2 (getr regs 1) mem2 (seg_rom tfxsegs)).
assert (LEN : Z.of_nat (length (repeat cb nn)) = n) by (img_try (rewrite repeat_length; img_exact Hnn)).
assert (M2out : forall z : word, ~ (q <= bv_unsigned z < q + n) -> mem2 z = mem z).
{ intros z Hz. (subst mem2 m2r; cbv beta). unfold munrestrict. rewrite <- (MEQ1 z). fold mem1. destruct (H z) eqn:Hh; [img_refl|].
assert (Ew : wbytes m1r (w64 q) (repeat cb nn) z = m1r z).
{ destruct (Z_lt_le_dec (bv_unsigned z) q) as [L|L].
- img_apply wbytes_below; unfold w64; rewrite ?LEN, unsigned_lit_small by img_lia; img_lia.
- img_apply wbytes_above. unfold w64. rewrite LEN, unsigned_lit_small by img_lia. img_lia. }
rewrite Ew. (subst m1r; cbv beta). unfold mrestrict. rewrite Hh. img_refl. }
assert (M2in : forall i, 0 <= i < n -> mem2 (Z_to_bv 64 (q + i)) = Some cb).
{ intros i Hi. (subst mem2; cbv beta). unfold munrestrict. rewrite (proj2 (DW (q + i) ltac:(img_lia))).
(subst m2r; cbv beta). rewrite (wbytes_inside (repeat cb nn) m1r (w64 q) (Z_to_bv 64 (q + i)));
unfold w64; rewrite ?LEN, ?unsigned_lit_small by img_lia; [|img_lia|img_lia].
replace (Z.to_nat (q + i - q)) with (Z.to_nat i) by img_lia. img_apply nth_error_repeat. img_lia. }
assert (CB : bv_unsigned cb = v).
{ (subst cb; cbv beta). rewrite Z_to_bv_unsigned. unfold bv_wrap. img_change (bv_modulus 8) with 256. unfold w64. rewrite unsigned_lit_small by img_lia. rewrite Z.mod_mod by img_lia. img_apply Z.mod_small. img_lia. }
assert (AVout : forall a, 0 <= a < 2 ^ 64 -> ~ (q <= a < q + n) -> aview tfxsegs H mem2 a = aview tfxsegs H mem a).
{ intros a Hr Ha. img_apply aview_same. img_apply M2out. rewrite unsigned_lit_small by img_lia. img_exact Ha. }
assert (AVin : forall i, 0 <= i < n -> aview tfxsegs H mem2 (q + i) = Some v).
{ intros i Hi. unfold aview, mbyte, mrestrict. rewrite (proj2 (DW (q + i) ltac:(img_lia))), (M2in i Hi). cbn [option_map]. rewrite CB. img_refl. }
img_apply SRr_ret. split; [img_refl|]. exists regs2, mem2, model'.
pose proof (same_but_materialized_frame md model' HSBM) as MF.
split; [img_try (unfold cfg_at, raZ, w64; rewrite Z_to_bv_bv_unsigned; img_refl)|].
split; [|img_try (split; [|split; [img_exact HSBM|split; [img_exact AVin|split; [img_exact AVout|]]]])].
-
img_apply (al_frame _ _ LAWS ly S W mem md mem2 model' HAR).
+ intros a Hr Hown. img_apply AVout; [img_try (img_exact Hr)|]. intros Ha. img_exact (proj2 (PR a Ha) Hown).
+ intros a Hvw. rewrite (YE0v.aview_mod _ mem2 a). rewrite (YE0v.aview_mod _ mem a) in Hvw.
assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (img_try (img_apply Z.mod_pos_bound; img_lia)). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' q) as [L1|L1]; [img_try (rewrite AVout by img_lia; img_exact Hvw)|].
destruct (Z_lt_le_dec a' (q + n)) as [L2|L2]; [|img_try (rewrite AVout by img_lia; img_exact Hvw)].
replace a' with (q + (a' - q)) by img_lia. rewrite AVin by img_lia. discriminate.
+ img_apply MF. + img_apply MF. + img_apply MF.
+ intros a Hb Hh. img_change (w_H W (w64 a)) with (H (Z_to_bv 64 a)) in Hh. img_apply M2out. unfold w64. rewrite unsigned_lit_small by (img_try (img_exact (YE0v.in_band_rw_u64 a Hb))).
intros Ha. rewrite (proj2 (DW a Ha)) in Hh. discriminate.
-
intros r Hr.
assert (NE : forall x : bv 5, 11 <= bv_unsigned x <= 16 -> Z_to_bv 5 r <> x).
{ intros x Hx E. rewrite <- E in Hx. rewrite Z_to_bv_unsigned in Hx. unfold bv_wrap in Hx. img_change (bv_modulus 5) with 32 in Hx.
unfold acallee_saved in Hr. rewrite Z.mod_small in Hx by img_lia. img_lia. }
rewrite Hkeep; [img_try (img_apply KEEP1; unfold acallee_saved in Hr; unfold keep_regs; cbn [In]; img_lia) | | | | | |]; img_apply NE; (split; img_apply Z.leb_le; img_refl).
-
intros a Ha. destruct (HpresE a Ha) as [Hh [b Hb]].
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
assert (HES : ESTACK = 4096) by img_refl. assert (Hsp44 : 2 ^ 44 <= spZ regs <= 2 ^ 47) by (img_try (unfold kHighMemBeg, kHighMemEnd in *; img_lia)).
split; [img_try (img_exact Hh)|].
destruct (Z_lt_le_dec a q) as [L1|L1]; [| img_try (destruct (Z_lt_le_dec a (q + n)) as [L2|L2])].
+ exists b. rewrite M2out; [img_try (img_exact Hb)|]. rewrite unsigned_lit_small by img_lia. img_lia.
+ exists cb. replace a with (q + (a - q)) by img_lia. img_apply M2in. img_lia.
+ exists b. rewrite M2out; [img_try (img_exact Hb)|]. rewrite unsigned_lit_small by img_lia. img_lia.
Qed.
End d.
Theorem tfx_set_shadow_00 {imgk : img} : forall (B : asyms), AR_laws tfxsegs B -> TfxSyms B -> aset_shadow_realizes tfxsegs B (0x54fb8 + D_2c4) 0.
Proof. intros B LAWS TB. img_exact (set_shadow_gen B LAWS TB (0x54fb8 + D_2c4) 0 e_00 r_00 shape_00 ltac:(img_lia)). Qed.
Theorem tfx_set_shadow_f8 {imgk : img} : forall (B : asyms), AR_laws tfxsegs B -> TfxSyms B -> aset_shadow_realizes tfxsegs B (0x550d8 + D_2c4) 0xf8.
Proof. intros B LAWS TB. img_exact (set_shadow_gen B LAWS TB (0x550d8 + D_2c4) 0xf8 e_f8 r_f8 shape_f8 ltac:(img_lia)). Qed.
End c.
