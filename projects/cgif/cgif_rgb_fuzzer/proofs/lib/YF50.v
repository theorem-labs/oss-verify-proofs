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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF64 YF3v YF4q YF3w YF40 YF4w YF4x YF4y YF4v YF4z YF4n YF4o YF4p.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac img_facts ::= lazymatch goal with k : img |- _ => let F := fresh "IMGF" in pose proof (P_facts k) as F end.
Ltac img_lia ::=
first [ (img_goal_has_k; img_facts; lia)
| lia
| (img_inst; lia)
| (try img_inst;
first [ (img_local; img_local_unfold; img_unfold_all; lia)
| (img_arith_rel; first [ (img_facts; lia)
| (img_has_moddiv; img_case; img_unfold_all; lia)
| (first [ img_has_moddiv | img_has_match ]; img_concrete; img_unfold_all; lia) ]) ]) ].
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Set Printing Depth 50. Set Printing Width 180.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Ltac zlia := first [ img_lia | ceil; unfold zone3, zone3cases, in_app, app_addr, in_band_rw, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, ASAN_CEIL in *; img_lia ].
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
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
eq_refl eq_refl ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))) as HS2; clear HS; rename HS2 into HS
end.
Section e. Context {imgk : img}.
Variables (W : world tfxsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (n : Z) (ch : list (Z * Z * Z)).
Variables (cl cnt v csz j0 jb j1 j2 j3 j4 : Z).
Variable kz : Z.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Local Abbreviation RZ := (@YF4q.RZ kz).
Local Abbreviation R8v := (@YF4q.R8v n).
Local Abbreviation N8D := (@YF4q.N8D n).
Local Abbreviation Pv := (@YF4q.Pv ly cl).
Local Abbreviation PVv := (@YF4q.PVv ly cl cnt).
Local Abbreviation Kv := (@YF4q.Kv ly cl v).
Local Abbreviation SHBv := (@YF4q.SHBv ).
Local Abbreviation SKv := (@YF4q.SKv ly cl v).
Local Abbreviation SSLOTv := (@YF4q.SSLOTv ly cl).
Local Abbreviation AR9 f := (f n cl v kz) (only parsing).
Local Abbreviation PBv := (AR9 (@YF4q.PBv ly)).
Local Abbreviation Uv := (@YF4q.Uv ly cl v kz).
Local Abbreviation SUv := (@YF4q.SUv ly cl v kz).
Local Abbreviation FILv := (@YF4q.FILv n).
Local Abbreviation NDv := (@YF4q.NDv n kz).
Local Abbreviation AR5 f := (f imgk ly regs0) (only parsing).
Local Abbreviation tr := ((AR5 (@YF4q.tr)) ch).
Local Abbreviation AR0 f := (f n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz) (only parsing).
Local Abbreviation XW := (AR0 (AR5 (@YF4q.XW))).
Local Abbreviation E0 := (AR0 (AR5 (@YF4q.E0))).
Local Abbreviation EaT := (AR0 (AR5 (@YF4q.EaT))).
Local Abbreviation EaC := (AR0 (AR5 (@YF4q.EaC))).
Local Abbreviation EaSB := (AR0 (AR5 (@YF4q.EaSB))).
Local Abbreviation EaTOP := (AR0 (AR5 (@YF4q.EaTOP))).
Local Abbreviation Er := (AR0 (AR5 (@YF4q.Er))).
Local Abbreviation E2 := (AR0 (AR5 (@YF4q.E2))).
Local Abbreviation E1 := (AR0 (AR5 (@YF4q.E1))).
Local Abbreviation E8 := (AR0 (AR5 (@YF4q.E8))).
Local Abbreviation E10 := (AR0 (AR5 (@YF4q.E10))).
Local Abbreviation E4 := (AR0 (AR5 (@YF4q.E4))).
Local Abbreviation EaP := (AR0 (AR5 (@YF4q.EaP))).
Local Abbreviation EaK := (AR0 (AR5 (@YF4q.EaK))).
Local Abbreviation EaSK := (AR0 (AR5 (@YF4q.EaSK))).
Local Abbreviation EaSSLOT := (AR0 (AR5 (@YF4q.EaSSLOT))).
Local Abbreviation EaPB := (AR0 (AR5 (@YF4q.EaPB))).
Local Abbreviation EaPV := (AR0 (AR5 (@YF4q.EaPV))).
Local Abbreviation EaKL := (AR0 (AR5 (@YF4q.EaKL))).
Local Abbreviation EaRZ := (AR0 (AR5 (@YF4q.EaRZ))).
Local Abbreviation EaU := (AR0 (AR5 (@YF4q.EaU))).
Local Abbreviation EaSU := (AR0 (AR5 (@YF4q.EaSU))).
Local Abbreviation EaFIL := (AR0 (AR5 (@YF4q.EaFIL))).
Local Abbreviation EaND := (AR0 (AR5 (@YF4q.EaND))).
Local Abbreviation WINT := (@YF4q.WINT ly cl).
Local Abbreviation PBW := (AR9 (@YF4q.PBW ly)).
Local Abbreviation WIN := (AR9 (@YF4q.WIN ly regs0)).
Local Abbreviation win_in_WIN := (AR9 (@YF4q.win_in_WIN ly regs0)).
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
Local Abbreviation HCdisj := (@YF4q.HCdisj _ ly regs0 v Hv LY).
Local Abbreviation DZONE := (@YF4q.DZONE imgk ly).
Variable DPOST : Z -> (word -> option byte) -> Prop.
Local Abbreviation HC_NB := (@YF4q.HC_NB _ ly LY).
Hypothesis HKpres : forall a, Kv <= a < Kv + RZ + R8v -> apresent (w_H W) mem0 a.
Hypothesis HSKpres : forall a, SKv <= a < SKv + (RZ + R8v) / 8 -> apresent (w_H W) mem0 a.
Hypothesis HPB250 : n mod 8 <> 0 -> val_mem tfxsegs (mrestrict (w_H W) mem0) PBv 1 250.
Local Abbreviation HCX := (@YF4q.HCX _ ly LY).
Local Abbreviation tr_length := ((AR5 (@YF4q.tr_length)) mem0 n ch v kz DPOST).
Local Abbreviation ARi f := (f ly regs0 mem0) (only parsing).
Local Abbreviation Kv_range := ((AR9 (ARi (@YF4q.Kv_range))) Hcl Hv Hv2 DPOST).
Local Abbreviation ARc f := (f mem0 n v kz Hv) (only parsing).
Local Abbreviation high_facts := ((ARc (AR5 (@YF4q.high_facts _))) LY IMG DPOST).
Local Abbreviation blocks_facts := (@YF4q.blocks_facts _ imgk ly LY IMG).
Local Abbreviation off_T := ((ARc (AR5 (@YF4q.off_T _))) LY IMG DPOST).
Local Abbreviation off_C := ((ARc (AR5 (@YF4q.off_C _))) LY IMG DPOST).
Local Abbreviation off_NB := (@YF4q.off_NB _ imgk ly LY IMG).
Local Abbreviation off_SB := (@YF4q.off_SB _ imgk ly LY IMG).
Ltac off_by tac :=
first [ img_apply off_img_high; tac
| img_apply off_T; unfold kThreadObjSize; tac
| img_apply off_C; tac
| img_apply off_NB; unfold kNodesBlockSize; tac
| img_apply off_SB; unfold kStoreBlockSize; tac
| unfold off_img; unfold TFX_IMG_LO; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; tac ].
Hypothesis Hkz : 1 <= kz <= 6.
Hypothesis Nrange : rz_lo kz <= n <= rz_hi kz.
Local Abbreviation kz_cases := (@YF4q.kz_cases kz Hkz).
Local Abbreviation RZ_facts := (@YF4q.RZ_facts n kz Hkz Nrange).
Local Abbreviation RZ_num := (@YF4q.RZ_num n kz Hkz Nrange).
Ltac numconst ::= (ceil; unfold zone3, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize,
t_cache, t_unwinding, t_stats, ASTACK, TFX_IMG_END, TFX_IMG_LO, kLowShadowBeg, UNW_STK, BST_SIZE, DEP_STK in * ); try pose proof RZ_num as RZN.
Local Abbreviation AR7 f := (f DPOST Hkz Nrange) (only parsing).
Local Abbreviation AR8 f := (f Hcl Hv Hcnt Hv2 LY IMG) (only parsing).
Local Abbreviation derived_ranges := (AR7 (AR8 ((AR5 (@YF4q.derived_ranges _)) mem0 n cl cnt v kz))).
Hypothesis Hcl_def : cl = class_id (R8v + RZ).
Local Abbreviation NDv_facts := (AR7 ((ARi (@YF4q.NDv_facts)) n v kz)).
Local Abbreviation CL_hi_E := ((AR7 (AR0 ((AR5 (@YF4q.CL_hi_E)) mem0))) Hcl_def).
Local Abbreviation CL_lo_E := ((AR7 (AR0 ((AR5 (@YF4q.CL_lo_E)) mem0))) Hcl_def).
Local Abbreviation WIN1 := (AR9 (@YF4q.WIN1 ly regs0)).
Local Abbreviation WIN1_WIN := ((AR9 (ARi (@YF4q.WIN1_WIN))) DPOST).
Local Abbreviation ARg f := (f cl cnt v jb kz Hcl Hv Hcnt Hjb Hsp) (only parsing).
Local Abbreviation WIN_odd := (AR7 (ARg ((ARi (@YF4q.WIN_odd)) n))).
Local Abbreviation WIN1_odd := (AR7 (ARg ((ARi (@YF4q.WIN1_odd)) n))).
Local Abbreviation WSKEL := (@YF4q.WSKEL ).
Local Abbreviation WSKEL1 := (@YF4q.WSKEL1 ).
Local Abbreviation win_sub := (@YF4q.win_sub ).
Local Abbreviation win_sub_sound := ((ARc (@YF4q.win_sub_sound ly regs0)) DPOST).
Local Abbreviation WSKEL_WIN := (AR7 (AR8 (AR0 ((AR5 (@YF4q.WSKEL_WIN _)) mem0)))).
Local Abbreviation WSKEL1_WIN1 := (AR7 (AR8 (AR0 ((AR5 (@YF4q.WSKEL1_WIN1 _)) mem0)))).
Local Abbreviation windows_WIN := (AR7 (AR8 (AR0 ((AR5 (@YF4q.windows_WIN _)) mem0)))).
Local Abbreviation windows_WIN1 := (AR7 (AR8 (AR0 ((AR5 (@YF4q.windows_WIN1 _)) mem0)))).
Local Abbreviation frame_WIN1 := (AR7 (AR8 (AR0 ((AR5 (@YF4q.frame_WIN1 _)) mem0)))).
Local Abbreviation AR3 f := (f _ imgk ly regs0 mem0 n cl cnt v kz Hcl Hv Hcnt Hv2 LY IMG Hsp DPOST Hkz Nrange) (only parsing).
Local Abbreviation WIN_not_high := (AR3 (@YF4q.WIN_not_high)).
Variables (mat0 : list word).
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 (0x53104 + D_2c4)) mem0 (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis U1 : tfx_unwind_spec.
Hypothesis SEED : st_ok tfxsegs E0 SS0 (restrict (w_H W) (mkst regs0 (w64 (0x53104 + D_2c4)) mem0 (seg_rom tfxsegs))).
Local Abbreviation all_disjoint_of_forall := (@YF4q.all_disjoint_of_forall ).
Local Abbreviation AR2 f := (f imgk W ly regs0 mem0) (only parsing).
Local Abbreviation kept_of_frame := ((AR2 (@YF4q.kept_of_frame)) n v kz DPOST).
Local Abbreviation SKEL_TAIL := (@YF4q.SKEL_TAIL imgk ).
Local Abbreviation stack_ivs := ((ARc (@YF4q.stack_ivs _ ly regs0)) LY Hsp DPOST).
Local Abbreviation stack_ivs2 := ((ARc (@YF4q.stack_ivs2 _ ly regs0)) LY Hsp DPOST).
Local Abbreviation DZONE_disj := (AR3 (@YF4q.DZONE_disj)).
Local Abbreviation RFACTS := (AR9 (AR5 (@YF4q.RFACTS))).
Local Abbreviation zone_lit := (AR3 (@YF4q.zone_lit)).
Local Abbreviation zone_T := (AR3 (@YF4q.zone_T)).
Local Abbreviation zone_C := (AR3 (@YF4q.zone_C)).
Local Abbreviation zone_K := (AR3 (@YF4q.zone_K)).
Local Abbreviation zone_SH := (AR3 (@YF4q.zone_SH)).
Local Abbreviation tail_ext_ok := (AR7 ((AR8 (AR0 ((AR5 (@YF4q.tail_ext_ok _)) mem0))) Hsp)).
Local Abbreviation ARh f := (AR2 f md0) (only parsing).
Local Abbreviation at_ST := (AR0 (ARh (@YF4q.at_ST _))).
Local Abbreviation at_ST2 := ((AR0 (ARh (@YF4q.at_ST2 _))) DPOST).
Local Abbreviation at_S2 := ((AR0 (ARh (@YF4q.at_S2 _))) DPOST).
Local Abbreviation at_RET := ((ARh (@YF4q.at_RET _)) n cl cnt v jb kz DPOST).
Ltac frame_acc HE :=
match goal with
| MEQ : (forall x : word, ~ WIN1 ?odd (bv_unsigned x) -> ?m1 x = ?mb x), HFx : frame_of ?E ?rs ?m1 ?m2 |- _ =>
let MEQ' := fresh "MEQ" in
assert (MEQ' : forall x : word, ~ WIN1 odd (bv_unsigned x) -> m2 x = mb x)
by (img_try (intros x Hx; transitivity (m1 x); [img_try (img_exact (frame_WIN1 odd E rs m1 m2 HE ltac:((try img_inst; img_case; vm_compute); img_refl) HFx x Hx)) | img_try (img_exact (MEQ x Hx))]));
clear MEQ HFx; rename MEQ' into MEQ
end.
Local Abbreviation memset_stretch := ((AR7 (ARg ((ARh (@YF4q.memset_stretch _)) n))) mat0).
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
Local Abbreviation casek_sizes := (@YF4q.casek_sizes n kz Hkz Nrange).
Local Abbreviation Kv_is_sptr := (@YF4q.Kv_is_sptr ly cl v Hcl B off Hoff_def).
Local Abbreviation cl_range := ((AR7 (AR9 (ARi (@YF4w.cl_range)))) l off Hcl_class).
Local Abbreviation cls_geom := ((AR7 (AR9 (ARi (@YF4w.cls_geom)))) l off Hcl_class).
Local Abbreviation ARa f := (f B S l off) (only parsing).
Local Abbreviation cls_wf := ((ARa (AR7 (AR9 (AR2 (@YF4w.cls_wf _))))) HARm Hcl_class).
Local Abbreviation AR1 f := (f DPOST Hkz Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def) (only parsing).
Local Abbreviation AR4 f := (AR2 f n cl cnt v) (only parsing).
Local Abbreviation off_facts := (AR1 ((AR4 (@YF4w.off_facts _)) kz Hv2)).
Local Abbreviation Kv_base := ((AR7 (AR9 (ARi (@YF4w.Kv_base)))) l off Hcl_class Hoff_def).
Local Abbreviation ARd f := (AR4 f csz kz Hv2 LY) (only parsing).
Local Abbreviation Kv_geom := ((AR1 (ARd (@YF4w.Kv_geom _))) Hcsz_def).
Local Abbreviation Hcl' := ((AR7 (AR9 (ARi (@YF4w.Hcl')))) l off Hcl_class).
Local Abbreviation ARe f := (AR4 f kz Hv2 Hsp) (only parsing).
Local Abbreviation Hcnt' := (AR1 (ARe (@YF4w.Hcnt' _))).
Local Abbreviation Hv' := (AR1 ((AR4 (@YF4w.Hv' _)) kz Hv2)).
Local Abbreviation cached_vs_chunk := ((AR1 ((ARd (@YF4w.cached_vs_chunk _)) Hsp)) Hcsz_def).
Local Abbreviation find_chunk_at_none := (AR1 (ARe (@YF4w.find_chunk_at_none _))).
Local Abbreviation shadow250 := ((AR1 ((ARd (@YF4w.shadow250 _)) Hsp)) Hcsz_def).
Local Abbreviation shadow_present := ((AR1 ((ARd (@YF4w.shadow_present _)) IMG Hsp)) Hcsz_def).
Local Abbreviation vis_present := (AR1 (ARe (@YF4w.vis_present _))).
Local Abbreviation KPRES := ((AR1 ((ARd (@YF4w.KPRES _)) Hsp)) Hcsz_def).
Local Abbreviation SKPRES := ((AR1 ((ARd (@YF4w.SKPRES _)) IMG Hsp)) Hcsz_def).
Local Abbreviation PB250 := ((AR1 ((ARd (@YF4w.PB250 _)) IMG Hsp)) Hcsz_def).
Local Abbreviation in_thread_junk := (AR1 (ARe (@YF4w.in_thread_junk _))).
Local Abbreviation junk_word := (AR1 ((AR4 (@YF4w.junk_word _)) kz Hv2 LY IMG Hsp)).
Local Abbreviation junk_byte := ((AR1 ((ARd (@YF4w.junk_byte _)) Hsp)) Hcsz_def).
Local Abbreviation junk_values := ((AR1 ((ARd (@YF4w.junk_values _)) IMG Hsp)) Hcsz_def).
Local Abbreviation ARf f := (f Hinited Hcache Hcl_class Hcnt_def Hoff_def) (only parsing).
Local Abbreviation cell_sym := (ARf ((ARa (AR7 (ARe (@YF4w.cell_sym _)))) TS HARm)).
Local Abbreviation cell_lit := (ARf ((ARa (AR7 (ARe (@YF4w.cell_lit _)))) TS HARm)).
Local Abbreviation cell_state := (AR1 (ARe (@YF4w.cell_state _))).
Local Abbreviation In_acells_cache := (AR1 (ARe (@YF4w.In_acells_cache _))).
Local Abbreviation In_combine_seq_last := (AR1 (ARe (@YF4w.In_combine_seq_last _))).
Local Abbreviation cache_vals := ((AR1 ((AR4 (@YF4w.cache_vals _)) csz kz Hv2 Hsp)) Hcsz_def).
Local Abbreviation unwinding_val := (AR1 (ARe (@YF4w.unwinding_val _))).
Local Abbreviation sk_val := ((AR1 ((ARd (@YF4w.sk_val _)) IMG Hsp)) Hcsz_def).
Local Abbreviation val_mem_mod8 := (AR1 (ARe (@YF4w.val_mem_mod8 _))).
Local Abbreviation chunk_lit := (AR1 ((AR0 (AR2 (@YF4w.chunk_lit _))) Hv2 Hsp)).
Local Abbreviation chunk_lit_at := (AR1 ((AR0 (AR2 (@YF4w.chunk_lit_at _))) Hv2 Hsp)).
Local Abbreviation chunk_atom := (AR1 ((AR0 (AR2 (@YF4w.chunk_atom _))) Hv2 Hsp)).
Local Abbreviation AR6 f := (f Hcl Hv Hcnt Hjb Hv2 LY IMG) (only parsing).
Local Abbreviation REG0_ok := ((ARf ((ARa (AR7 ((AR6 (AR0 (AR2 (@YF4x.REG0_ok _)))) Hsp))) TS HTSD HARm Hpres0)) Hcsz_def Hj0 Hj1 Hj2 Hj3 Hj4 Hjb_def).
Local Abbreviation Kv32 := ((AR9 (AR2 (@YF4y.Kv32 _))) Hv2 LY DPOST l off).
Local Abbreviation PAIRS_ok := ((AR1 ((AR8 (AR0 (AR2 (@YF4y.PAIRS_ok _)))) Hsp)) Hcsz_def).
Local Abbreviation FACTS_ok := ((AR1 ((AR6 (AR0 (AR2 (@YF4y.FACTS_ok _)))) Hn Hsp)) Hcsz_def).
Local Abbreviation SEED_ok := ((ARf ((ARa (AR7 ((AR6 (AR0 (AR2 (@YF4y.SEED_ok _ _)))) Hn Htp Hsp))) TS HTSD HARm Hpres0)) Hcsz_def Hj0 Hj1 Hj2 Hj3 Hj4 Hjb_def).
Local Abbreviation CZONE := (@YF4v.CZONE imgk ly).
Local Abbreviation abs_cell_ok := (@YF4v.abs_cell_ok imgk ).
Local Abbreviation abs_cells_ok := (@YF4v.abs_cells_ok imgk ).
Local Abbreviation const_cells_zone := ((ARc (AR5 (@YF4v.const_cells_zone))) DPOST B l off TS HTSD).
Local Abbreviation CZONE_untouched := ((AR3 (@YF4v.CZONE_untouched)) l off).
Local Abbreviation cell_holds_agree := ((ARc (@YF4v.cell_holds_agree ly regs0)) DPOST B l off).
Local Abbreviation aview_agree := (@YF4v.aview_agree imgk W).
Local Abbreviation const_kept := ((AR7 ((AR8 ((AR4 (@YF4v.const_kept _)) kz)) Hsp)) B l off TS HTSD).
Local Abbreviation depot_ids_bound := ((ARc (AR5 (@YF4v.depot_ids_bound))) DPOST B l off TS).
Local Abbreviation depot_mem_ok_agree := ((ARc (AR5 (@YF4v.depot_mem_ok_agree))) DPOST B l off TS).
Local Abbreviation depot_ok_ext := (@YF4v.depot_ok_ext ly B).
Local Abbreviation depot_at0 := ((AR7 ((AR4 (@YF4v.depot_at0 _)) jb kz Hcl Hv Hcnt Hjb Hsp)) B S HARm).
Local Abbreviation DPOST3 := (@YF4v.DPOST3 imgk W ly regs0 ch B S).
Local Abbreviation ARj f := (f n ch cl) (only parsing).
Local Abbreviation D1W_ok := ((ARa (AR7 ((AR6 ((ARj (AR2 (@YF4v.D1W_ok _ _))) cnt v jb kz)) Hsp))) TS HTSD HARm Hgp).
Local Abbreviation st_popped := (@YF4v.st_popped ).
Local Abbreviation new_chunk := (@YF4v.new_chunk ).
Local Abbreviation st_final := (@YF4v.st_final ).
Local Abbreviation Kc_user := ((ARa (AR7 ((ARj ((AR5 (@YF4v.Kc_user)) mem0)) v kz Hcl))) Hoff_def).
Local Abbreviation MPF := (ARa (ARj (AR5 (@YF4v.MPF)))).
Local Abbreviation AR_final_stmt := (ARa ((ARj (ARh (@YF4v.AR_final_stmt _ _))) cnt v jb kz DPOST)).
Local Abbreviation WR_owned := ((ARf ((ARa (AR7 ((AR6 ((ARj (AR2 (@YF4v.WR_owned _))) cnt v csz jb kz)) Hsp))) TS HARm)) Hcsz_def).
Local Abbreviation LEAF_ok := ((ARf ((ARa ((AR7 ((AR6 ((ARj (ARh (@YF4v.LEAF_ok _ _))) cnt v csz jb kz)) Hsp)) mat0)) TS HARm)) Hcsz_def).
Local Abbreviation ARb f := (AR2 f n ch cl cnt v kz Hcl Hv Hv2) (only parsing).
Local Abbreviation Kc_fresh := (AR1 (ARb (@YF4v.Kc_fresh _))).
Local Abbreviation upd_chunk_fresh := (@YF4v.upd_chunk_fresh n cl off).
Local Abbreviation SF_chunks := (AR1 (ARb (@YF4v.SF_chunks _))).
Local Abbreviation SF_same := ((ARj (AR5 (@YF4v.SF_same))) S l off).
Local Abbreviation SF_sec_extents := (AR1 (ARb (@YF4v.SF_sec_extents _))).
Local Abbreviation SF_sec_live := (AR1 (ARb (@YF4v.SF_sec_live _))).
Local Abbreviation SF_ledger := (AR1 (ARb (@YF4v.SF_ledger _))).
Local Abbreviation cell_holds_agree2 := (ARa (AR7 (ARg ((AR5 (@YF4v.cell_holds_agree2)) mem0 n ch)))).
Local Abbreviation zrange_dec := (@YF4z.zrange_dec ).
Local Abbreviation apresent_word := (@YF4z.apresent_word ).
Local Abbreviation val_mem_cell := (ARa ((ARj (AR2 (@YF4z.val_mem_cell))) v kz DPOST)).
Local Abbreviation le_byte_1_0 := ((ARj ((AR5 (@YF4z.le_byte_1_0)) mem0)) v kz DPOST S l off).
Local Abbreviation find_chunk_at_app1 := (@YF4z.find_chunk_at_app1 ly B).
Local Abbreviation find_chunk_at_app2 := (@YF4z.find_chunk_at_app2 ly B).
Local Abbreviation In_combine_seq_app := (@YF4z.In_combine_seq_app ).
Local Abbreviation Kc_facts := ((AR9 (@YF4z.Kc_facts ly)) Hcl Hkz Nrange B off Hcl_class Hoff_def).
Local Abbreviation NLOf := (@YF4z.NLOf n kz Hkz Nrange).
Local Abbreviation AR_final := ((ARf ((ARa ((AR6 (AR0 (ARh (@YF4z.AR_final _ _)))) Hsp DPOST HKpres HSKpres HPB250 Hkz Nrange Hcl_def SEED)) TS HTSD HARm)) Hcsz_def Hj4 Hjb_def).
Local Abbreviation LEAF_final := ((ARf ((ARa ((AR6 (AR0 (ARh (@YF4z.LEAF_final _ _)))) Hsp DPOST HKpres HSKpres HPB250 Hkz Nrange Hcl_def mat0 SEED)) TS HTSD HARm)) Hcsz_def Hj4 Hjb_def).
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
Local Open Scope am_scope.
Let rd0 : reader := aview tfxsegs (w_H W) mem0.
Let WF := am_wf B ly S rd0 HARm.
Let c0 : config := cfg_at tfxsegs (0x53104 + D_2c4) regs0 mem0 md0.
Hypothesis Htr : In tr (as_universe B).
Hypothesis HAR : AR tfxsegs B ly S W mem0 md0.
Hypothesis HD1 : tfx_depot_spec B.
Hypothesis HDPOST : forall z m, DPOST z m -> DPOST3 z m.
Hypothesis HDPOST' : forall z m, DPOST3 z m -> DPOST z m.
Hypothesis Hmat0 : mat0 = m_vm_materialized md0.
Lemma D1w : forall (regs : bvmap 5 word) (mem : word -> option byte) (md : Model),
getr regs 10 = Z_to_bv 64 (sp0 - IFRAME + 16) -> getr regs 11 = Z_to_bv 64 (Z.of_nat (length tr)) ->
getr regs 3 = getr regs0 3 -> getr regs 4 = Z_to_bv 64 TFX_TP -> getr regs 1 = Z_to_bv 64 (0x31cc8 + D_150) ->
bv_unsigned (getr regs 2) = sp0 - 2272 ->
(forall i, (i < length tr)%nat -> val_mem tfxsegs (mrestrict (w_H W) mem) (sp0 - IFRAME + 16 + 8 * Z.of_nat i) 8 (nth i tr 0)) ->
(forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem a) ->
(forall x : word, ~ WIN false (bv_unsigned x) -> mem x = mem0 x) ->
SRr tfxsegs W (mkCfg (mkst regs (Z_to_bv 64 A_StackDepotPut) mem (seg_rom tfxsegs)) md)
(fun W' c' => W' = W /\ exists z regs' mem' mat,
c' = mkCfg (mkst regs' (Z_to_bv 64 (0x31cc8 + D_150)) mem' (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md) mat md) /\
regs_preserved regs regs' /\
(forall x : word, ~ (sp0 - 2272 - DEP_STK <= bv_unsigned x < sp0 - 2272) -> ~ DZONE (bv_unsigned x) -> mem' x = mem x) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
DPOST z mem').
Proof.
intros regs mem md R10 R11 R3 R4 R1 Rsp BUF PRES MEQ.
eapply SRr_mono; [img_try (img_exact (D1W_ok Htr HD1 regs mem md R10 R11 R3 R4 R1 Rsp BUF PRES MEQ))|].
intros W' c' _ (-> & z & regs' & mem' & mat & -> & RP & FR & PR & DP). split; [img_refl|].
exists z, regs', mem', mat. repeat (split; [assumption || img_refl|]). img_apply HDPOST'. img_exact DP.
Qed.
Local Abbreviation seg1J := ((AR7 ((AR6 (AR0 (ARh (@YF4n.seg1J _ _)))) Hn Hra4096 Hsp Hch)) Hcl_def mat0 U1 SEED l off).
Local Abbreviation segC2 := ((AR7 ((AR8 (AR0 (ARh (@YF4n.segC2 _ _)))) Hn Hsp)) l off).
Local Abbreviation segD := ((AR0 (ARh (@YF4o.segD _ _))) LY Hsp DPOST l off D1w).
Local Abbreviation seg2a_even := ((AR6 (AR0 (ARh (@YF4o.seg2a_even _ _)))) Hn Hsp DPOST HSKpres Hkz Nrange Hcl_def mat0 l off).
Local Abbreviation seg2b_even := ((AR7 ((AR8 (AR0 (ARh (@YF4o.seg2b_even _ _)))) Hn Hsp)) l off).
Local Abbreviation seg2c_even := ((AR6 (AR0 (ARh (@YF4o.seg2c_even _ _)))) Hn Htp Hra Hsp DPOST HKpres Hkz Nrange mat0 l off).
Local Abbreviation seg2a_odd := ((AR6 (AR0 (ARh (@YF4p.seg2a_odd _ _)))) Hn Hsp DPOST HSKpres HPB250 Hkz Nrange Hcl_def mat0 l off).
Local Abbreviation seg2b_odd := ((AR8 (AR0 (ARh (@YF4p.seg2b_odd _ _)))) Hn Hsp DPOST HPB250 Hkz Nrange l off).
Local Abbreviation seg2c_odd := ((AR6 (AR0 (ARh (@YF4p.seg2c_odd _ _)))) Hn Htp Hra Hsp DPOST HKpres HPB250 Hkz Nrange mat0 l off).
Theorem tail_inner : forall c1, at_ST SS_JN W c1 ->
amreal tfxsegs (malloc_join n tr cl S) W c1
(fun r W' c' => Wf (as_universe B) (snd r) /\ qtight (snd r) -> malloc_leaf tfxsegs B ly S W regs0 mem0 md0 n r W' c').
Proof.
intros c1 HJ.
pose proof casek_sizes as (L & RS & R8 & NP & FP & NS & RQ). pose proof RZ_facts as (_ & _ & _ & RF4 & _).
unfold malloc_join. rewrite bind_assoc_eq. eapply amreal_pure; [img_try (img_exact (pop_hit S cl l off Hcache))|]. eapply amreal_pure; [img_refl|].
unfold malloc_K. cbv beta iota. img_change (YF40.st_popped S cl l) with (st_popped S cl l).
img_change {| ck_beg := PPrim (region_off cl + off); ck_req := n; ck_state := CAllocated |} with (new_chunk cl off n).
replace (needs_remap (ck_n (new_chunk cl off n))) with false.
2:{ symmetry. img_apply Z.leb_gt. unfold new_chunk, ck_n. cbn [ck_req]. rewrite RQ. unfold kClearShadowMmapThreshold.
img_apply Z.div_lt_upper_bound; zlia. }
unfold depot_put. rewrite bind_assoc_eq. unfold bind at 1. unfold askz. cbn [ibind amreal].
eapply SRr_bind. { img_exact (segC2 W c1 HJ). }
intros W1 c1' Hle1 HPD.
eapply SRr_mono. { img_exact (segD W1 c1' HPD). }
intros W2 c2 Hle2 [z HPD2]. exists z.
split. { destruct HPD2 as (_ & ms2 & mat2 & E2 & regs2 & mem2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & HDP). img_exact (proj1 (HDPOST _ _ HDP)). }
assert (FIN : forall s', s' = depot_after z tr (st_popped S cl l) ->
amreal tfxsegs ((ret () ;; modify (fun s : astate => set_chunks (upd_chunk (st_chunks s) (new_chunk cl off n)) s) ;;
ret (ck_user (new_chunk cl off n))) s') W2 c2
(fun r W' c' => Wf (as_universe B) (snd r) /\ qtight (snd r) -> malloc_leaf tfxsegs B ly S W regs0 mem0 md0 n r W' c')).
{ intros s' ->. eapply amreal_pure; [img_refl|]. eapply amreal_pure; [img_refl|]. cbn [amreal ret].
img_change (set_chunks (upd_chunk (st_chunks (depot_after z tr (st_popped S cl l))) (new_chunk cl off n)) (depot_after z tr (st_popped S cl l)))
with (st_final S cl l off n tr z).
destruct (Z.eq_dec (n mod 8) 0) as [H8|H8].
- eapply SRr_bind; [img_try (img_exact (seg2a_even H8 z W2 c2 HPD2))|]. intros W3 c3 _ H3.
eapply SRr_bind; [img_try (img_exact (seg2b_even H8 z W3 c3 H3))|]. intros W4 c4 _ H4.
eapply SRr_mono; [img_try (img_exact (seg2c_even H8 z W4 c4 H4))|]. intros W' c' _ HR MP.
img_exact (LEAF_final HDPOST HAR false z W' c' HR ltac:(img_try (split; [img_try (intros E; discriminate E) | img_try (intros X; exfalso; img_exact (X H8))])) MP).
- eapply SRr_bind; [img_try (img_exact (seg2a_odd H8 z W2 c2 HPD2))|]. intros W3 c3 _ H3.
eapply SRr_bind; [img_try (img_exact (seg2b_odd H8 z W3 c3 H3))|]. intros W4 c4 _ H4.
eapply SRr_mono; [img_try (img_exact (seg2c_odd H8 z W4 c4 H4))|]. intros W' c' _ HR MP.
img_exact (LEAF_final HDPOST HAR true z W' c' HR ltac:(img_try (split; [img_try (intros _; img_exact H8) | img_try (intros _; img_refl)])) MP). }
destruct (z =? 0) eqn:Ez.
- eapply amreal_pure; [img_refl|]. img_apply FIN. unfold depot_after. rewrite Ez. img_refl.
- rewrite bind_assoc_eq. eapply amreal_pure; [img_refl|].
rewrite bind_assoc_eq. unfold mcheck at 1.
destruct (depot_ids (st_popped S cl l) + 1 <? kDepotIdsPerBlock); [| img_try (unfold bind at 1; unfold fail; cbn [ibind amreal]; img_exact I)].
eapply amreal_pure; [img_refl|].
rewrite bind_assoc_eq. unfold mcheck at 1.
destruct (kStartFramesMax + depot_frames (st_popped S cl l) + Z.of_nat (length tr) + 1 <? kStoreFramesPerBlock);
[| img_try (unfold bind at 1; unfold fail; cbn [ibind amreal]; img_exact I)].
eapply amreal_pure; [img_refl|]. eapply amreal_pure; [img_refl|].
img_apply FIN. unfold depot_after. rewrite Ez. img_refl.
Qed.
Theorem hitg_inner : amreal tfxsegs (malloc_join n tr cl S) W c0
(fun r W' c' => Wf (as_universe B) (snd r) /\ qtight (snd r) -> malloc_leaf tfxsegs B ly S W regs0 mem0 md0 n r W' c').
Proof.
eapply amreal_SRr_pre.
{ replace c0 with cfg0 by (img_try ((subst c0 cfg0; cbv beta); unfold cfg_at; rewrite Hmat0, with_vm_backing_id; img_refl)). img_exact seg1J. }
intros W1 c1 _ HJ. pose proof (proj1 HJ) as EW. (subst W1; cbv beta). img_exact (tail_inner c1 HJ).
Qed.
End e.
End d.
