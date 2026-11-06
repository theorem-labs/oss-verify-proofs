(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YQ0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG04 YG06 YG07 YG03 YG0h YG10 YG0u YG0d YG0y YG0w.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP09.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF64 YF3v YF3y YF54 YF41 YF3i.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Set Printing Depth 50. Set Printing Width 180.
Section g. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Ltac zlia := first [ img_lia | ceil; unfold zone3, zone3cases, off_img, in_app, app_addr, in_band_rw, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPrimResvSize, kSpaceSize in *; img_lia ].
Ltac zcanon_simp :=
repeat match goal with
| |- context [zcanon ?x] =>
lazymatch x with
| context [zcanon _] => fail
| context [Z.shiftl _ _] => fail | context [Z.shiftr _ _] => fail | context [Z.land _ _] => fail
| context [Z.lor _ _] => fail | context [Z.lxor _ _] => fail
| _ => rewrite (zcanon_id x) by (img_try (unfold M64; img_lia))
end
end.
Ltac is_zlit a := lazymatch a with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.
Ltac land_lits :=
repeat match goal with
| |- context [Z.land ?a ?b] => is_zlit a; is_zlit b; let c := img_ev (Z.land a b) in img_change (Z.land a b) with c
end.
Ltac numconst := ceil; unfold zone3, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize,
t_cache, t_unwinding, t_stats, ASTACK, TFX_IMG_END, TFX_IMG_LO, kLowShadowBeg, UNW_STK, BST_SIZE, DEP_STK in *.
Ltac pin_zev :=
lazymatch goal with |- U _ _ = U _ (sr_get ?sr ?r) => let t := img_ev (sr_get sr r) in img_change (sr_get sr r) with t end;
img_apply U_eq_by_zev; [img_refl | img_refl |]; cbn [zev zalu_raw zmd_raw]; unfold rho_of.
Ltac memv HS i j :=
lazymatch goal with |- val_mem _ _ ?a ?n ?v =>
let nn := lazymatch n with 1%nat => constr:(1%N) | 2%nat => constr:(2%N) | 4%nat => constr:(4%N) | _ => constr:(8%N) end in
lazymatch type of HS with st_ok _ ?E ?ss (restrict ?H ?ms) =>
eapply (chunk_val_at H E ss ms i j _ _ nn _ v a HS);
[ img_refl | img_refl | cbn [base_val YQ0b.r_base]
| | lazymatch goal with |- _ <= _ < ?p => let q := img_ev constr:(p) in img_change p with q end
| cbn; img_lia ]
end
end.
Ltac forget_regs HS k clob :=
lazymatch type of HS with st_ok _ ?E ?ss (restrict ?H ?ms) =>
let ss' := img_ev (ss_after_stretch ss (ss_mem ss) k clob (ss_pc ss)) in
let HS2 := fresh "HSf" in
pose proof (st_ok_forget2 k E ss ss' H ms clob HS eq_refl
ltac:(img_try ((img_case; vm_compute); img_refl)) ltac:(img_try ((img_case; vm_compute); img_refl)) ltac:(img_try ((img_case; vm_compute); img_refl)) ltac:(img_try ((img_case; vm_compute); img_refl))
eq_refl eq_refl ltac:(img_try ((img_case; vm_compute); img_refl))) as HS2; clear HS; rename HS2 into HS
end.
Section h. Context {imgk : img}.
Variables (W : world tfxsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (n : Z) (ch : list (Z * Z * Z)).
Variables (cl cnt v csz j0 jb j1 j2 j3 j4 : Z).
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Local Abbreviation RZ := (@YF54.RZ).
Local Abbreviation NPv := (@YF54.NPv n).
Local Abbreviation R8v := (@YF54.R8v n).
Local Abbreviation N8D := (@YF54.N8D n).
Local Abbreviation Pv := (@YF54.Pv ly cl).
Local Abbreviation PVv := (@YF54.PVv ly cl cnt).
Local Abbreviation Kv := (@YF54.Kv ly cl v).
Local Abbreviation SHBv := (@YF54.SHBv).
Local Abbreviation SKv := (@YF54.SKv ly cl v).
Local Abbreviation SSLOTv := (@YF54.SSLOTv ly cl).
Local Abbreviation AR7 f := (f n cl v) (only parsing).
Local Abbreviation PBv := (AR7 (@YF54.PBv ly)).
Local Abbreviation Uv := (@YF54.Uv ly cl v).
Local Abbreviation SUv := (@YF54.SUv ly cl v).
Local Abbreviation FILv := (@YF54.FILv n).
Local Abbreviation NDv := (@YF54.NDv n).
Local Abbreviation AR2 f := (f imgk ly regs0) (only parsing).
Local Abbreviation tr := ((AR2 (@YF54.tr)) ch).
Local Abbreviation AR0 f := (f n ch cl cnt v csz j0 jb j1 j2 j3 j4) (only parsing).
Local Abbreviation XW := (AR0 (AR2 (@YF54.XW))).
Local Abbreviation E0 := (AR0 (AR2 (@YF54.E0))).
Local Abbreviation EaT := (AR0 (AR2 (@YF54.EaT))).
Local Abbreviation EaC := (AR0 (AR2 (@YF54.EaC))).
Local Abbreviation EaSB := (AR0 (AR2 (@YF54.EaSB))).
Local Abbreviation EaTOP := (AR0 (AR2 (@YF54.EaTOP))).
Local Abbreviation Er := (AR0 (AR2 (@YF54.Er))).
Local Abbreviation E2 := (AR0 (AR2 (@YF54.E2))).
Local Abbreviation E1 := (AR0 (AR2 (@YF54.E1))).
Local Abbreviation E8 := (AR0 (AR2 (@YF54.E8))).
Local Abbreviation E10 := (AR0 (AR2 (@YF54.E10))).
Local Abbreviation E4 := (AR0 (AR2 (@YF54.E4))).
Local Abbreviation EaP := (AR0 (AR2 (@YF54.EaP))).
Local Abbreviation EaR8 := (AR0 (AR2 (@YF54.EaR8))).
Local Abbreviation EaK := (AR0 (AR2 (@YF54.EaK))).
Local Abbreviation EaSK := (AR0 (AR2 (@YF54.EaSK))).
Local Abbreviation EaSSLOT := (AR0 (AR2 (@YF54.EaSSLOT))).
Local Abbreviation EaPB := (AR0 (AR2 (@YF54.EaPB))).
Local Abbreviation EaPV := (AR0 (AR2 (@YF54.EaPV))).
Local Abbreviation EaRZ := (AR0 (AR2 (@YF54.EaRZ))).
Local Abbreviation EaU := (AR0 (AR2 (@YF54.EaU))).
Local Abbreviation EaSU := (AR0 (AR2 (@YF54.EaSU))).
Local Abbreviation EaFIL := (AR0 (AR2 (@YF54.EaFIL))).
Local Abbreviation EaNP := (AR0 (AR2 (@YF54.EaNP))).
Local Abbreviation EaND := (AR0 (AR2 (@YF54.EaND))).
Local Abbreviation WINT := (@YF54.WINT ly cl).
Local Abbreviation PBW := (AR7 (@YF54.PBW ly)).
Local Abbreviation WIN := (AR7 (@YF54.WIN ly regs0)).
Local Abbreviation win_in_WIN := (AR7 (@YF54.win_in_WIN ly regs0)).
Hypotheses (Hcl : 1 <= cl <= 31) (Hv : 0 <= v /\ 16 * v + 2 ^ 16 <= 2 ^ 32) (Hcnt : 1 <= cnt <= 16) (Hjb : 0 <= jb <= 255).
Hypothesis Hv2 : v mod 2 = 0.
Hypothesis LY : layout_ok ly.
Hypothesis IMG : img_cover ly.
Hypothesis Hn : getr regs0 10 = w64 n.
Hypothesis Htp : getr regs0 4 = w64 TFX_TP.
Hypothesis Hra : YK0s.ret_ok (getr regs0 1).
Hypothesis Hra4096 : 4096 <= bv_unsigned (getr regs0 1).
Hypothesis Hsp : ly_stk_lo ly + ASTACK <= sp0 /\ ly_bot ly < sp0 /\ sp0 <= ly_stk_hi ly /\ sp0 mod 16 = 0.
Hypothesis Hch : if sp0 + 16 <? ly_top ly
then (if bad_next sp0 (ly_top ly) (bv_unsigned (getr regs0 8)) then ch = []
else sp0 + 16 <= bv_unsigned (getr regs0 8) /\
fpchain (rdword (aview tfxsegs (w_H W) mem0)) (bv_unsigned (getr regs0 8)) (ly_top ly) ch)
else ch = [].
Local Abbreviation HCdisj := (@YF54.HCdisj _ ly regs0 v Hv LY).
Local Abbreviation DZONE := (@YF54.DZONE imgk ly).
Variable DPOST : Z -> (word -> option byte) -> Prop.
Local Abbreviation HC_NB := (@YF54.HC_NB _ ly LY).
Hypothesis HKpres : forall a, Kv <= a < Kv + RZ + R8v -> apresent (w_H W) mem0 a.
Hypothesis HSKpres : forall a, SKv <= a < SKv + (RZ + R8v) / 8 -> apresent (w_H W) mem0 a.
Hypothesis HPB250 : NPv mod 8 <> 0 -> val_mem tfxsegs (mrestrict (w_H W) mem0) PBv 1 250.
Local Abbreviation HCX := (@YF54.HCX _ ly LY).
Local Abbreviation tr_length := ((AR2 (@YF54.tr_length)) mem0 n ch v DPOST).
Local Abbreviation AR4 f := (f ly regs0 mem0) (only parsing).
Local Abbreviation Kv_range := ((AR7 (AR4 (@YF54.Kv_range))) Hcl Hv Hv2 DPOST).
Local Abbreviation AR6 f := (AR2 f mem0 n v Hv LY IMG DPOST) (only parsing).
Local Abbreviation high_facts := (AR6 (@YF54.high_facts _)).
Local Abbreviation blocks_facts := (@YF54.blocks_facts _ imgk ly LY IMG).
Local Abbreviation off_T := (AR6 (@YF54.off_T _)).
Local Abbreviation off_C := (AR6 (@YF54.off_C _)).
Local Abbreviation off_NB := (@YF54.off_NB _ imgk ly LY IMG).
Local Abbreviation off_SB := (@YF54.off_SB _ imgk ly LY IMG).
Ltac off_by tac :=
first [ img_apply off_img_high; tac
| img_apply off_T; unfold kThreadObjSize; tac
| img_apply off_C; tac
| img_apply off_NB; unfold kNodesBlockSize; tac
| img_apply off_SB; unfold kStoreBlockSize; tac
| unfold off_img; unfold TFX_IMG_LO; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; tac ].
Hypothesis Nrange : 0 <= n <= 48.
Local Abbreviation K0_facts := (@YF54.K0_facts n Nrange).
Local Abbreviation RZ_num := (@YF54.RZ_num n Nrange).
Ltac numconst ::= (ceil; unfold zone3, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize,
t_cache, t_unwinding, t_stats, ASTACK, TFX_IMG_END, TFX_IMG_LO, kLowShadowBeg, UNW_STK, BST_SIZE, DEP_STK in * ); try pose proof RZ_num as RZN.
Local Abbreviation AR3 f := (f Hcl Hv Hcnt Hv2 LY IMG DPOST Nrange) (only parsing).
Local Abbreviation derived_ranges := (AR3 ((AR2 (@YF54.derived_ranges _)) mem0 n cl cnt v)).
Hypothesis Hcl_def : cl = class_id (R8v + RZ).
Local Abbreviation CLk := (@YF54.CLk).
Local Abbreviation CLk_E := ((AR0 ((AR2 (@YF54.CLk_E)) mem0)) DPOST Nrange Hcl_def).
Local Abbreviation WIN1 := (AR7 (@YF54.WIN1 ly regs0)).
Local Abbreviation WIN1_WIN := ((AR7 (AR4 (@YF54.WIN1_WIN))) DPOST).
Local Abbreviation AR5 f := (f n cl cnt v jb Hcl Hv Hcnt Hjb Hsp DPOST Nrange) (only parsing).
Local Abbreviation WIN_odd := (AR5 (AR4 (@YF54.WIN_odd))).
Local Abbreviation WIN1_odd := (AR5 (AR4 (@YF54.WIN1_odd))).
Local Abbreviation WSKEL := (@YF54.WSKEL).
Local Abbreviation WSKEL1 := (@YF54.WSKEL1).
Local Abbreviation win_sub := (@YF54.win_sub).
Local Abbreviation win_sub_sound := ((AR4 (@YF54.win_sub_sound)) n v Hv DPOST).
Local Abbreviation WSKEL_WIN := (AR3 (AR0 ((AR2 (@YF54.WSKEL_WIN _)) mem0))).
Local Abbreviation WSKEL1_WIN1 := (AR3 (AR0 ((AR2 (@YF54.WSKEL1_WIN1 _)) mem0))).
Local Abbreviation windows_WIN := (AR3 (AR0 ((AR2 (@YF54.windows_WIN _)) mem0))).
Local Abbreviation windows_WIN1 := (AR3 (AR0 ((AR2 (@YF54.windows_WIN1 _)) mem0))).
Local Abbreviation frame_WIN1 := (AR3 (AR0 ((AR2 (@YF54.frame_WIN1 _)) mem0))).
Local Abbreviation AR1 f := (f _ imgk ly regs0 mem0 n cl cnt v Hcl Hv Hcnt Hv2 LY IMG Hsp DPOST Nrange) (only parsing).
Local Abbreviation WIN_not_high := (AR1 (@YF54.WIN_not_high)).
Variables (mat0 : list word).
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 (0x53104 + D_2c4)) mem0 (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis U1 : tfx_unwind_spec.
Hypothesis SEED : st_ok tfxsegs E0 SS0K (restrict (w_H W) (mkst regs0 (w64 (0x53104 + D_2c4)) mem0 (seg_rom tfxsegs))).
Local Abbreviation all_disjoint_of_forall := (@YF54.all_disjoint_of_forall).
Local Abbreviation kept_of_frame := ((AR4 (@YF54.kept_of_frame imgk W)) n v DPOST).
Local Abbreviation SKEL_TAIL := (@YF54.SKEL_TAIL imgk).
Local Abbreviation stack_ivs := ((AR4 (@YF54.stack_ivs _)) n v Hv LY Hsp DPOST).
Local Abbreviation stack_ivs2 := ((AR4 (@YF54.stack_ivs2 _)) n v Hv LY Hsp DPOST).
Local Abbreviation DZONE_disj := (AR1 (@YF54.DZONE_disj)).
Local Abbreviation RFACTS := (AR7 (AR2 (@YF54.RFACTS))).
Local Abbreviation zone_lit := (AR1 (@YF54.zone_lit)).
Local Abbreviation zone_T := (AR1 (@YF54.zone_T)).
Local Abbreviation zone_C := (AR1 (@YF54.zone_C)).
Local Abbreviation zone_K := (AR1 (@YF54.zone_K)).
Local Abbreviation zone_SH := (AR1 (@YF54.zone_SH)).
Local Abbreviation tail_ext_ok := ((AR0 ((AR2 (@YF54.tail_ext_ok _)) mem0)) Hcl Hv Hcnt Hv2 LY IMG Hsp DPOST Nrange).
Local Abbreviation at_ST := (AR0 ((AR4 (@YF54.at_ST _ imgk W)) md0)).
Local Abbreviation at_ST2 := ((AR0 ((AR4 (@YF54.at_ST2 _ imgk W)) md0)) DPOST).
Local Abbreviation at_S2 := ((AR0 ((AR4 (@YF54.at_S2 _ imgk W)) md0)) DPOST).
Local Abbreviation at_RET := ((AR4 (@YF54.at_RET _ imgk W)) md0 n cl cnt v jb DPOST).
Ltac frame_acc HE :=
match goal with
| MEQ : (forall x : word, ~ WIN1 ?odd (bv_unsigned x) -> ?m1 x = ?mb x), HFx : frame_of ?E ?rs ?m1 ?m2 |- _ =>
let MEQ' := fresh "MEQ" in
assert (MEQ' : forall x : word, ~ WIN1 odd (bv_unsigned x) -> m2 x = mb x)
by (img_try (intros x Hx; transitivity (m1 x); [img_try (img_exact (frame_WIN1 odd E rs m1 m2 HE ltac:((img_case; vm_compute); img_refl) HFx x Hx)) | img_try (img_exact (MEQ x Hx))]));
clear MEQ HFx; rename MEQ' into MEQ
end.
Local Abbreviation memset_stretch := ((AR5 ((AR4 (@YF54.memset_stretch _ imgk W)) md0)) mat0).
Variables (B : asyms) (S : astate) (l : list Z) (off : Z).
Hypothesis TS : TfxSyms B.
Hypothesis HTSD : ly_tsd ly = TFX_TSD.
Hypothesis HARm : ARm B ly S (aview tfxsegs (w_H W) mem0).
Hypothesis Hgp : getr regs0 3 = w64 (as_gp B).
Hypothesis Hpres0 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem0 a.
Hypothesis Hinited : st_cache_inited S = true.
Hypothesis Hcache : pc_chunks (cache S cl) = l ++ [off].
Hypothesis Hcl_class : cl = chunk_class n.
Hypothesis Hcnt_def : cnt = Z.of_nat (length (l ++ [off])).
Hypothesis Hoff_def : off = 16 * v.
Hypothesis Hcsz_def : csz = class_size cl.
Hypothesis Hj0 : val_mem tfxsegs (mrestrict (w_H W) mem0) (T + 2784) 8 j0.
Hypothesis Hj1 : val_mem tfxsegs (mrestrict (w_H W) mem0) (T + 2800) 8 j1.
Hypothesis Hj2 : val_mem tfxsegs (mrestrict (w_H W) mem0) (T + 2808) 8 j2.
Hypothesis Hj3 : val_mem tfxsegs (mrestrict (w_H W) mem0) (T + 2816) 8 j3.
Hypothesis Hj4 : val_mem tfxsegs (mrestrict (w_H W) mem0) SSLOTv 8 j4.
Hypothesis Hjb_def : val_mem tfxsegs (mrestrict (w_H W) mem0) (Kv + RZ - 15) 1 jb.
Hypothesis HQT : qtight S.
Local Abbreviation case0_sizes := (@YF54.case0_sizes n Nrange).
Local Abbreviation Kv_is_sptr := (@YF54.Kv_is_sptr ly cl v Hcl B off Hoff_def).
Local Ltac addr_tac :=
cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi];
rewrite ?EaT, ?EaC, ?EaTOP, ?EaSB, ?E2; ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, w64, ly_bot, kStackSpan, t_unwinding, t_cache, t_stats, TFX_IMG_END, UNW_STK, BST_SIZE, ASTACK, IFRAME, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *;
rewrite ?unsigned_lit_small by zlia; zlia.
Local Ltac denot_tac :=
cbn [sv_denot]; rewrite ?EaT, ?EaC, ?EaTOP, ?EaSB, ?E2; unfold w64, ly_bot, kStackSpan in *;
first [ rewrite Z.add_0_r, Z_to_bv_bv_unsigned; img_refl
| rewrite Zbv_add_unsigned; f_equal; zlia
| rewrite unsigned_lit_small by zlia; f_equal; zlia
| img_refl ].
Ltac cleanM := try clear Hcache; try clear Hinited; try clear HKpres; try clear HSKpres; try clear HPB250; try clear Hjb_def; try clear SEED; try clear U1;
try clear Hcnt_def; try clear Hoff_def; try clear HQT.
Let m0 := mrestrict (w_H W) mem0.
Let rd0 : reader := aview tfxsegs (w_H W) mem0.
Lemma cell_symM : forall e (w : nat) e', cell_lookup (Tfx_const ly) e = Some (ACell e w (AV e')) -> val_mem tfxsegs m0 (aeval B ly e) w (aeval B ly e').
Proof. cleanM. intros e w e' E. img_exact (tfx_const_lookup_sym B TS ly S (w_H W) mem0 e w e' HARm E). Qed.
Lemma cell_litM : forall a (w : nat) x, cell_lookup (Tfx_const ly) (ANum a) = Some (ACell (ANum a) w (AV (ANum x))) -> val_mem tfxsegs m0 a w x.
Proof. cleanM. intros a w x E. img_exact (tfx_const_lookup B TS ly S (w_H W) mem0 a w x HARm E). Qed.
Lemma cell_stateM : forall c e (w : nat) x, In c (acells B ly S) -> c = ACell e w (AV (ANum x)) -> val_mem tfxsegs m0 (aeval B ly e) w x.
Proof. cleanM.
intros c e w x Hin ->. img_apply (cell_holds_val_mem B ly (w_H W) mem0 e w (ANum x)). img_exact (proj1 (Forall_forall _ _) (am_cells B ly S rd0 HARm) _ Hin).
Qed.
Lemma unwinding_valM : val_mem tfxsegs m0 (T + t_unwinding) 1 0.
Proof. cleanM.
replace (T + t_unwinding) with (aeval B ly (AT t_unwinding)) by img_refl.
eapply cell_stateM; [|img_refl]. unfold acells. do 8 (img_apply in_or_app; right). left. img_refl.
Qed.
Lemma count0 : pc_chunks (cache S cl) = [] -> val_mem tfxsegs m0 Pv 4 0.
Proof. cleanM.
intros Hc. replace Pv with (aeval B ly (AT (t_cache + 80 * cl))) by (img_try (cbn; unfold Pv, T; zlia)).
eapply cell_stateM; [|img_refl]. unfold acells. img_apply in_or_app. right. img_apply in_or_app. left. img_apply in_flat_map. exists cl.
split; [img_try (img_apply In_zseq; zlia)|]. unfold cache_cells. rewrite Hc. destruct (st_cache_inited S); left; img_refl.
Qed.
Lemma chunk_litM : forall a (nn : BinNums.N) x, val_mem tfxsegs m0 a (N.to_nat nn) x -> 0 <= x < 2 ^ (8 * Z.of_N nn) -> Z.of_N nn <= 8 ->
YQ0b.chunk_ok tfxsegs E0 m0 0 (YQ0b.mkChunk a (CVal nn (SLit x))).
Proof. cleanM. intros a nn x H Hx Hnn. eapply chunk_ok_val; [img_refl | img_try (img_exact Hx) | img_try (img_exact Hnn) | img_try (rewrite Z.add_0_l; img_exact H)]. Qed.
Lemma chunk_lit_atM : forall base a (nn : BinNums.N) x, val_mem tfxsegs m0 (base + a) (N.to_nat nn) x -> 0 <= x < 2 ^ (8 * Z.of_N nn) -> Z.of_N nn <= 8 ->
YQ0b.chunk_ok tfxsegs E0 m0 base (YQ0b.mkChunk a (CVal nn (SLit x))).
Proof. cleanM. intros base a nn x H Hx Hnn. eapply chunk_ok_val; [img_refl | img_try (img_exact Hx) | img_try (img_exact Hnn) | img_try (img_exact H)]. Qed.
Lemma chunk_atomM : forall base a (nn : BinNums.N) k d x, ew E0 k = w64 (x - d) -> 0 <= x - d < 2 ^ 64 ->
val_mem tfxsegs m0 (base + a) (N.to_nat nn) x -> 0 <= x < 2 ^ (8 * Z.of_N nn) -> Z.of_N nn <= 8 ->
YQ0b.chunk_ok tfxsegs E0 m0 base (YQ0b.mkChunk a (CVal nn (SOff k d))).
Proof. cleanM.
intros base a nn k d x Hk Hr H Hx Hnn. eapply chunk_ok_val; [| img_try (img_exact Hx) | img_try (img_exact Hnn) | img_try (img_exact H)].
cbn [sv_denot]. rewrite Hk. unfold w64. rewrite Zbv_add_unsigned. f_equal. zlia.
Qed.
Local Ltac reg_introM := unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
Local Ltac lit_regionM :=
reg_introM; split; [img_try (zlia)|]; split; [img_try (zlia)|]; split; [img_try (intros o Ho; zlia)|];
repeat (img_apply Forall_cons; [img_try (img_apply chunk_litM; [img_apply cell_litM; (img_case; vm_compute); img_refl | cbn; zlia | cbn; zlia]) |]); img_apply Forall_nil.
Local Ltac bare_regionM := reg_introM; rewrite ?EaT, ?EaP, ?EaPV, ?EaK, ?EaU, ?EaSK, ?EaSSLOT; unfold w64; rewrite ?unsigned_lit_small by zlia; split; [img_try (zlia)|]; split; [img_try (zlia)|]; split; [img_try (intros o Ho; zlia) | img_try (img_apply Forall_nil)].
Lemma REGM_ok : pc_chunks (cache S cl) = [] -> Forall (region_ok tfxsegs E0 m0) MKREG0.
Proof. cleanM.
intros Hc0. pose proof (count0 Hc0) as CV0. clear Hc0.
pose proof high_facts as (hf1 & hf2 & hf3 & hf4 & hf5 & hf6 & hf7 & hf8 & hf9). pose proof derived_ranges as DR. pose proof Kv_range as HKR.
pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). destruct Hsp as (S1 & S2 & S3 & S4).
ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, t_cache, t_unwinding in hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, DR, HKR, T2, T4, T7.
pose proof RZ_num as (RZr & RZ8 & Nlo & NPr & R8r & NPR8 & N8r & NPN8 & FILN).
unfold MKREG0, REG0K, lit1, lit4, lit8, lits8, atom8, CTZ_TABLE. cbn [map combine seq length Z.of_nat Pos.of_succ_nat Pos.succ fst snd Z.mul Z.add Pos.mul Pos.add].
unfold aSB, aSHB, aC, aT, aTOP, aJ0, aJ1, aJ2, aJ3, aJ4, aCNT, aCSZ, aV, aJB, aSK, aP, aPV, aK, aU, aSSLOT.
img_apply Forall_cons.
{   img_apply (region_ok_stack tfxsegs E0 m0 2 sp0 (- ASTACK)); [img_try (rewrite E2; img_refl) | img_try (unfold ASTACK; zlia) | img_try (zlia) |].
intros a Ha. img_apply apresent_writable_off; [img_try (off_by ltac:(unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END, ASTACK in *; zlia)) | img_try (img_apply Hpres0; img_exact Ha)]. }
do 8 (img_apply Forall_cons; [img_try (lit_regionM)|]).
img_apply Forall_cons. {   reg_introM. split; [img_try (zlia)|]. split; [img_try (zlia)|]. split; [img_try (intros o Ho; zlia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply (chunk_atomM 0 _ 8 34%nat 0 SB); [img_try (rewrite EaSB; unfold w64; f_equal; zlia) | img_try (unfold SB; zlia) | | img_try (unfold SB; cbn; zlia) | img_try (cbn; zlia)].
rewrite Z.add_0_l. replace (682872 + D_10c0) with (aeval B ly (AInst o_space)) by (img_try (cbn; rewrite (ts_inst B TS); img_refl)).
replace SB with (aeval B ly (ASp 0)) by (img_try (cbn; unfold SB; zlia)). img_apply cell_symM. img_case; vm_compute. all: img_refl. }
do 14 (img_apply Forall_cons; [img_try (lit_regionM)|]).
img_apply Forall_cons. {   reg_introM. split; [img_try (zlia)|]. split; [img_try (zlia)|]. split; [img_try (intros o Ho; zlia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply (chunk_atomM 0 _ 8 47%nat 0 SHBv); [img_refl | img_try (unfold SHBv; zlia) | | img_try (unfold SHBv; cbn; zlia) | img_try (cbn; zlia)].
rewrite Z.add_0_l. img_apply cell_litM. img_case; vm_compute. all: img_refl. }
do 7 (img_apply Forall_cons; [img_try (lit_regionM)|]).
img_apply Forall_cons. {   reg_introM. split; [img_try (zlia)|]. split; [img_try (zlia)|]. split; [img_try (intros o Ho; zlia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply chunk_litM; [| img_try (cbn; zlia) | img_try (cbn; zlia)]. pose proof (cell_litM (0x5dd160 + D_10c0) 8 0 ltac:(img_try ((img_case; vm_compute); img_refl))) as H8.
intros k Hk. rewrite (H8 k ltac:(img_try (zlia))). rewrite !le_byte_zero. img_refl. }
img_apply Forall_cons; [img_try (lit_regionM)|].
img_apply Forall_cons. {   reg_introM. unfold TFX_TP. split; [img_try (zlia)|]. split; [img_try (zlia)|]. split; [img_try (intros o Ho; zlia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply chunk_litM; [| img_try (unfold TFX_TSD; cbn; zlia) | img_try (cbn; zlia)].
replace (6148344 + D_10c0) with (aeval B ly (ATp (-88))) by (img_try (cbn; rewrite (ts_tp B TS); img_refl)).
replace (6284536 + D_10c0) with (aeval B ly (ATsd 0)) by (img_try (cbn; rewrite HTSD; img_refl)). img_apply cell_symM. img_case; vm_compute. all: img_refl. }
img_apply Forall_cons. {   reg_introM. unfold TFX_TSD. split; [img_try (zlia)|]. split; [img_try (zlia)|]. split; [img_try (intros o Ho; zlia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply (chunk_atomM 0 _ 8 33%nat 0 (ly_C ly)); [img_try (rewrite EaC; unfold w64; f_equal; zlia) | img_try (zlia) | | img_try (cbn; zlia) | img_try (cbn; zlia)].
rewrite Z.add_0_l. replace (6284536 + D_10c0) with (aeval B ly (ATsd 0)) by (img_try (cbn; rewrite HTSD; img_refl)).
replace (ly_C ly) with (aeval B ly (AC 0)) by (img_try (cbn; zlia)). img_apply cell_symM. img_case; vm_compute. all: img_refl. }
img_apply Forall_cons. {   reg_introM. rewrite EaC. unfold w64. rewrite unsigned_lit_small by zlia.
split; [img_try (zlia)|]. split; [img_try (zlia)|]. split; [img_try (intros o Ho; zlia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_nil])].
- img_apply chunk_lit_atM; [| img_try (cbn; zlia) | img_try (cbn; zlia)]. replace (ly_C ly + 8) with (aeval B ly (AC 8)) by img_refl. img_apply (cell_symM (AC 8) 4 (ANum 0)). img_case; vm_compute. all: img_refl.
- img_apply (chunk_atomM _ _ 8 32%nat 0 T); [img_try (rewrite EaT; unfold w64; f_equal; zlia) | img_try (zlia) | | img_try (cbn; zlia) | img_try (cbn; zlia)].
replace (ly_C ly + 152) with (aeval B ly (AC 152)) by img_refl. replace T with (aeval B ly (AT 0)) by (img_try (cbn; unfold T; zlia)).
img_apply cell_symM. img_case; vm_compute. all: img_refl. }
img_apply Forall_cons. {   reg_introM. rewrite EaT. unfold w64. rewrite unsigned_lit_small by zlia.
split; [img_try (zlia)|]. split; [img_try (zlia)|]. split; [img_try (intros o Ho; zlia)|].
img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_cons; [|img_apply Forall_cons; [|img_apply Forall_nil]]])].
- img_apply (chunk_atomM _ _ 8 33%nat 0 (ly_C ly)); [img_try (rewrite EaC; unfold w64; f_equal; zlia) | img_try (zlia) | | img_try (cbn; zlia) | img_try (cbn; zlia)].
replace (ly_T ly + 0) with (aeval B ly (AT 0)) by (img_try (cbn; zlia)). replace (ly_C ly) with (aeval B ly (AC 0)) by (img_try (cbn; zlia)). img_apply cell_symM. img_case; vm_compute. all: img_refl.
- img_apply (chunk_atomM _ _ 8 35%nat 0 (ly_top ly)); [img_try (rewrite EaTOP; unfold w64; f_equal; zlia) | img_try (zlia) | | img_try (cbn; zlia) | img_try (cbn; zlia)].
replace (ly_T ly + 8) with (aeval B ly (AT 8)) by (img_try (cbn; zlia)). replace (ly_top ly) with (aeval B ly (ATop 0)) by (img_try (cbn; zlia)). img_apply cell_symM. img_case; vm_compute. all: img_refl.
- img_apply (chunk_atomM _ _ 8 35%nat (- kStackSpan) (ly_top ly - kStackSpan)); [img_try (rewrite EaTOP; unfold w64; f_equal; zlia) | img_try (unfold kStackSpan; zlia) | | img_try (unfold kStackSpan; cbn; zlia) | img_try (cbn; zlia)].
replace (ly_T ly + 16) with (aeval B ly (AT 16)) by (img_try (cbn; zlia)). replace (ly_top ly - kStackSpan) with (aeval B ly (ATop (- kStackSpan))) by (img_try (cbn; zlia)).
img_apply cell_symM. img_case; vm_compute. all: img_refl.
- img_apply chunk_lit_atM; [| img_try (cbn; zlia) | img_try (cbn; zlia)]. replace (ly_T ly + 40) with (aeval B ly (AT 40)) by (img_try (cbn; zlia)). img_apply (cell_symM (AT 40) 1 (ANum 0)). img_case; vm_compute. all: img_refl. }
img_apply Forall_cons; [img_try (bare_regionM)|].
img_apply Forall_cons. {   reg_introM. rewrite EaT. unfold w64. rewrite unsigned_lit_small by zlia. unfold t_unwinding.
split; [img_try (zlia)|]. split; [img_try (zlia)|]. split.
{ intros o Ho. img_apply apresent_writable_off; [img_try (off_by ltac:(unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; zlia)) |]. replace (ly_T ly + o) with (ly_T ly + 3168) by zlia.
pose proof unwinding_valM as U.
eapply mbyte_off_apresent; [img_try (off_by ltac:(unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; zlia)) |]. unfold T, t_unwinding in U. rewrite <- (Z.add_0_r (ly_T ly + 3168)). img_exact (U 0%nat ltac:(img_try (zlia))). }
img_apply Forall_cons; [|img_try (img_apply Forall_nil)]. img_apply chunk_lit_atM; [| img_try (cbn; zlia) | img_try (cbn; zlia)]. img_exact unwinding_valM. }
img_apply Forall_cons; [img_try (bare_regionM)|].
img_apply Forall_cons; [img_try (bare_regionM)|].
img_apply Forall_cons. {   reg_introM. rewrite EaP. unfold w64. rewrite unsigned_lit_small by zlia.
split; [img_try (zlia)|]. split; [img_try (zlia)|]. split; [img_try (intros o Ho; zlia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply chunk_lit_atM; [| img_try (cbn; zlia) | img_try (cbn; zlia)]. rewrite Z.add_0_r. img_exact CV0. }
img_apply Forall_cons; [img_try (bare_regionM)|].
img_apply Forall_cons; [img_try (bare_regionM)|].
img_apply Forall_cons; [img_try (bare_regionM)|].
img_apply Forall_cons; [img_try (bare_regionM)|img_try (img_apply Forall_nil)].
Qed.
Lemma PAIRSM_ok : pairwise_disjoint E0 MKREG0.
Proof. cleanM.
img_apply (pairwise_disjoint_ext3 E0 REG0K MKREG0 (eq_sym MKREG0_skel)).
pose proof high_facts as (hf1 & hf2 & hf3 & hf4 & hf5 & hf6 & hf7 & hf8 & hf9). pose proof derived_ranges as DR. pose proof Kv_range as HKR.
pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). destruct Hsp as (S1 & S2 & S3 & S4).
ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, t_cache, t_unwinding in hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, DR, HKR, T2, T4, T7.
img_apply pairwise_disjoint_of_extents. unfold REG0K, lit1, lit4, lit8, lits8, atom8, extent_of_region, CTZ_TABLE.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val length Z.of_nat Pos.of_succ_nat Pos.succ].
unfold aSB, aSHB, aC, aT, aTOP, aSK, aP, aPV, aK, aSSLOT.
rewrite E2, EaT, EaC, EaP, EaPV, EaK, EaSK, EaSSLOT. unfold w64. rewrite !unsigned_lit_small by zlia.
pose proof stack_ivs as (SI1 & SI2 & SI3). pose proof HCX as [CP CT]. unfold zdisjoint in CP, CT. cbn [fst snd] in CP, CT.
pose proof blocks_facts as (_ & _ & _ & _ & _ & _ & _ & _ & PT). unfold zdisjoint in PT. cbn [fst snd] in PT.
pose proof RZ_num as RZN. clear - sp0 T SB S1 S3 T2 T4 T7 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hf8 DR HKR SI1 SI2 SI3 CP CT PT Hcl Hcnt RZN.
unfold TFX_TP, TFX_TSD, t_unwinding, ASTACK in *. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
unfold sp0, T, SB in *. unfold PVv, SSLOTv, Pv in *. unfold t_cache, t_stats, kThreadObjSize, kPrimResvSize in *.
repeat split; first [clear; zlia | zlia].
Qed.
Lemma Kv32M : Kv mod 32 = 0.
Proof. cleanM.
pose proof (lo_space_al ly LY) as SAL. apply Z.mod_divide in SAL as [q Hq]; [|img_try (zlia)]. apply Z.mod_divide in Hv2 as [w Hw]; [|img_try (zlia)].
unfold Kv, SB. rewrite Hq, Hw. img_apply Z.mod_divide; [img_try (zlia)|]. exists (q * 2048 + cl * 2 ^ 27 + w). zlia.
Qed.
Lemma cl_k0M : 1 <= cl <= 2.
Proof. cleanM.
pose proof RZ_num as (RZr & RZ8 & Nlo & NPr & R8r & NPR8 & N8r & NPN8 & FILN).
rewrite Hcl_def. unfold class_id. replace (R8v + RZ <=? 512) with true by (img_try (symmetry; img_apply Z.leb_le; zlia)).
pose proof (Z.div_le_lower_bound (R8v + RZ + 31) 32 1 ltac:(img_try (zlia)) ltac:(img_try (zlia))). pose proof (Z.div_lt_upper_bound (R8v + RZ + 31) 32 3 ltac:(img_try (zlia)) ltac:(img_try (zlia))). zlia.
Qed.
Lemma FACTSM_ok : atoms_ok E0 (f_atoms FK).
Proof. cleanM.
pose proof high_facts as (hf1 & hf2 & hf3 & hf4 & hf5 & hf6 & hf7 & hf8 & hf9). pose proof derived_ranges as DR. pose proof Kv_range as HKR.
pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). destruct Hsp as (S1 & S2 & S3 & S4).
ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, t_cache, t_unwinding in hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, DR, HKR, T2, T4, T7.
pose proof tr_length as TL. pose proof (lo_space_al ly LY) as SAL. pose proof (lo_T_al ly LY) as TAL. pose proof (lo_C_al ly LY) as CAL.
unfold page_aligned in TAL.
assert (V1 : 17594333495296 <= Kv) by (img_try (clear - HKR hf3 hf4; zlia)). assert (V2 : Kv + 2 ^ 16 <= 140737479966720) by (img_try (clear - HKR hf5 hf6; zlia)).
assert (E2' : ew E0 2 = w64 sp0) by (img_try (rewrite E2; unfold sp0, w64; symmetry; img_apply Z_to_bv_bv_unsigned)).
assert (AF : forall k X lo hi al, ew E0 k = w64 X -> 0 <= X < 2 ^ 64 -> lo <= X <= hi -> X mod 2 ^ al = 0 -> 0 <= al <= 64 -> afact_ok E0 k (mkAF lo hi al)).
{ clear. intros k X lo hi al HE HX HB HM HA. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE. unfold w64. rewrite unsigned_lit_small by img_exact HX. repeat split; zlia. }
cbn [FK f_atoms atoms_ok]. unfold aSB, aSHB, aC, aT, aTOP, aSK, aP, aPV, aK, aSSLOT, aLEN, aJ0, aR8, aCL, aCNT, aV, aCSZ, aJB, aJ1, aJ2, aJ3, aJ4, aPB, aN8D, aCNT8, aNP, aND.
pose proof RZ_num as (RZr & RZ8 & Nlo & NPr & R8r & NPR8 & N8r & NPN8 & FILN). pose proof Kv32M as K32. pose proof K0_facts as KF. pose proof cl_k0M as CK.
ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, ASTACK.
split. { img_apply (AF 2%nat sp0); [img_try (img_exact E2')| | | |].
all: pose proof (u64_range (getr regs0 2)) as U; clear - U S1 S3 S4 T4 T7; unfold ASTACK in *; first [zlia | replace (2 ^ 4) with 16 by img_refl; img_exact S4]. }
split. { img_apply (AF 10%nat n); [img_try (rewrite E10, Hn; img_refl)| | | |].
all: clear - Nlo; first [zlia | replace (2 ^ 0) with 1 by img_refl; img_apply Z.mod_1_r]. }
split. { img_apply (AF 32%nat T); [img_try (img_exact EaT)| | | |].
all: clear - hf1 hf2 TAL; first [zlia | img_exact TAL]. }
split. { img_apply (AF 33%nat (ly_C ly)); [img_try (img_exact EaC)| | | |].
all: clear - hf7 hf8 CAL; first [zlia | img_exact CAL]. }
split. { img_apply (AF 34%nat SB); [img_try (img_exact EaSB)| | | |].
all: clear - hf3 hf4 hf5 hf6 SAL; first [zlia | img_exact SAL]. }
split. { img_apply (AF 35%nat (ly_top ly)); [img_try (img_exact EaTOP)| | | |].
all: clear - T1 T2 T3 T4 T7; first [zlia | img_exact T3]. }
split. { img_apply (AF 36%nat (Z.of_nat (length tr))); [img_refl| | | |].
all: clear - TL; first [zlia | replace (2 ^ 0) with 1 by img_refl; img_apply Z.mod_1_r]. }
split. { img_apply (AF 37%nat (j0 mod 2 ^ 64)); [img_try (img_apply Z_to_bv64_eq_mod; rewrite Z.mod_mod by zlia; img_refl)| | | |].
all: clear - j0; first [zlia | pose proof (Z.mod_pos_bound j0 (2 ^ 64) ltac:(img_try (zlia))); zlia | replace (2 ^ 0) with 1 by img_refl; img_apply Z.mod_1_r]. }
split. { img_apply (AF 38%nat R8v); [img_refl| | | |].
all: clear - DR R8r; first [zlia | replace (2 ^ 3) with 8 by img_refl; zlia]. }
split. { img_apply (AF 39%nat cl); [img_refl| | | |].
all: clear - CK; first [zlia | replace (2 ^ 0) with 1 by img_refl; img_apply Z.mod_1_r]. }
split. { img_apply (AF 40%nat Pv); [img_try (img_exact EaP)| | | |].
all: clear - DR hf1 hf2 TAL; unfold Pv, t_cache in *; first [zlia | replace (2 ^ 4) with 16 by img_refl; apply Z.mod_divide in TAL as [q Hq]; [|img_try (zlia)]; img_apply Z.mod_divide; [img_try (zlia)|]; exists (q * 256 + 13 + 5 * cl); zlia]. }
split. { img_apply (AF 41%nat cnt); [img_refl| | | |].
all: clear - Hcnt; first [zlia | replace (2 ^ 0) with 1 by img_refl; img_apply Z.mod_1_r]. }
split. { img_apply (AF 42%nat v); [img_refl| | | |].
all: clear - Hv; first [zlia | replace (2 ^ 0) with 1 by img_refl; img_apply Z.mod_1_r]. }
split. { img_apply (AF 43%nat (csz mod 2 ^ 64)); [img_try (img_apply Z_to_bv64_eq_mod; rewrite Z.mod_mod by zlia; img_refl)| | | |].
all: clear - csz; first [zlia | pose proof (Z.mod_pos_bound csz (2 ^ 64) ltac:(img_try (zlia))); zlia | replace (2 ^ 0) with 1 by img_refl; img_apply Z.mod_1_r]. }
split. { img_apply (AF 44%nat PVv); [img_try (img_exact EaPV)| | | |].
all: clear - DR hf1 hf2 TAL Hcnt; unfold PVv, Pv, t_cache in *; first [zlia | replace (2 ^ 2) with 4 by img_refl; apply Z.mod_divide in TAL as [q Hq]; [|img_try (zlia)]; img_apply Z.mod_divide; [img_try (zlia)|]; exists (q * 1024 + 56 + 20 * cl + (cnt - 1)); zlia]. }
split. { img_apply (AF 45%nat Kv); [img_try (img_exact EaK)| | | |].
all: clear - V1 V2 K32; first [zlia | replace (2 ^ 5) with 32 by img_refl; img_exact K32]. }
split. { img_apply (AF 46%nat jb); [img_refl| | | |].
all: clear - Hjb; first [zlia | replace (2 ^ 0) with 1 by img_refl; img_apply Z.mod_1_r]. }
split. { img_apply (AF 47%nat SHBv); [img_refl| | | |].
all: clear; unfold SHBv; first [zlia | img_refl]. }
split. { img_apply (AF 48%nat SKv); [img_try (img_exact EaSK)| | | |].
all: clear - DR K32; unfold SKv, SHBv in *; first [zlia | replace (2 ^ 2) with 4 by img_refl; apply Z.mod_divide in K32 as [q Hq]; [|img_try (zlia)]; img_apply Z.mod_divide; [img_try (zlia)|]; exists (536862720 + q); rewrite Hq; replace (q * 32) with (q * 4 * 8) by zlia; rewrite Z.div_mul by zlia; zlia]. }
split. { img_apply (AF 49%nat (j1 mod 2 ^ 64)); [img_try (img_apply Z_to_bv64_eq_mod; rewrite Z.mod_mod by zlia; img_refl)| | | |].
all: clear - j1; first [zlia | pose proof (Z.mod_pos_bound j1 (2 ^ 64) ltac:(img_try (zlia))); zlia | replace (2 ^ 0) with 1 by img_refl; img_apply Z.mod_1_r]. }
split. { img_apply (AF 50%nat (j2 mod 2 ^ 64)); [img_try (img_apply Z_to_bv64_eq_mod; rewrite Z.mod_mod by zlia; img_refl)| | | |].
all: clear - j2; first [zlia | pose proof (Z.mod_pos_bound j2 (2 ^ 64) ltac:(img_try (zlia))); zlia | replace (2 ^ 0) with 1 by img_refl; img_apply Z.mod_1_r]. }
split. { img_apply (AF 51%nat (j3 mod 2 ^ 64)); [img_try (img_apply Z_to_bv64_eq_mod; rewrite Z.mod_mod by zlia; img_refl)| | | |].
all: clear - j3; first [zlia | pose proof (Z.mod_pos_bound j3 (2 ^ 64) ltac:(img_try (zlia))); zlia | replace (2 ^ 0) with 1 by img_refl; img_apply Z.mod_1_r]. }
split. { img_apply (AF 52%nat SSLOTv); [img_try (img_exact EaSSLOT)| | | |].
all: clear - DR hf1 hf2 TAL; unfold SSLOTv, t_stats in *; first [zlia | replace (2 ^ 3) with 8 by img_refl; apply Z.mod_divide in TAL as [q Hq]; [|img_try (zlia)]; img_apply Z.mod_divide; [img_try (zlia)|]; exists (q * 512 + 364 + cl); zlia]. }
split. { img_apply (AF 53%nat (j4 mod 2 ^ 64)); [img_try (img_apply Z_to_bv64_eq_mod; rewrite Z.mod_mod by zlia; img_refl)| | | |].
all: clear - j4; first [zlia | pose proof (Z.mod_pos_bound j4 (2 ^ 64) ltac:(img_try (zlia))); zlia | replace (2 ^ 0) with 1 by img_refl; img_apply Z.mod_1_r]. }
split. { img_apply (AF 54%nat PBv); [img_try (img_exact EaPB)| | | |].
all: clear - DR; first [zlia | replace (2 ^ 0) with 1 by img_refl; img_apply Z.mod_1_r]. }
split. { img_apply (AF 55%nat N8D); [img_refl| | | |].
all: clear - DR Nlo; first [zlia | replace (2 ^ 3) with 8 by img_refl; zlia]. }
split. { img_apply (AF 56%nat (N8D / 8)); [img_refl| | | |].
all: clear - DR Nlo; first [zlia | replace (2 ^ 0) with 1 by img_refl; img_apply Z.mod_1_r]. }
split. { img_apply (AF 62%nat NPv); [img_try (img_exact EaNP)| | | |].
all: clear - NPr; first [zlia | replace (2 ^ 0) with 1 by img_refl; img_apply Z.mod_1_r]. }
split; [|img_try (img_exact I)]. { img_apply (AF 63%nat NDv); [img_try (img_exact EaND)| | | |].
all: clear - KF DR; first [zlia | replace (2 ^ 3) with 8 by img_refl; zlia]. }
Qed.
Lemma SEEDM_ok : pc_chunks (cache S cl) = [] -> st_ok tfxsegs E0 MK0 (restrict (w_H W) (mkst regs0 (w64 (0x53104 + D_2c4)) mem0 (seg_rom tfxsegs))).
Proof. cleanM.
intros Hc0. rewrite restrict_mkst_fx. unfold MK0, w64. img_apply (entry_st_ok_full tfxsegs).
- img_apply regs_ok_pin; [img_try (img_apply regs_ok_Ereg) | img_try (intros X; discriminate) | img_try (cbn [sv_denot]; img_exact Htp)].
- img_case; vm_compute. all: img_refl.
- cbn [ms_mem mkst]. img_exact (REGM_ok Hc0).
- img_exact PAIRSM_ok.
- split; [img_try (img_exact FACTSM_ok) | img_try (split; img_exact I)].
Qed.
End h.
End g.
