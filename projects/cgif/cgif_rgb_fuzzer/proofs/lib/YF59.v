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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF64 YF3v YF3y YF54 YF5a YF5b YF5c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
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
Local Abbreviation ARa f := (f n cl v) (only parsing).
Local Abbreviation PBv := (ARa (@YF54.PBv ly)).
Local Abbreviation Uv := (@YF54.Uv ly cl v).
Local Abbreviation SUv := (@YF54.SUv ly cl v).
Local Abbreviation FILv := (@YF54.FILv n).
Local Abbreviation NDv := (@YF54.NDv n).
Local Abbreviation AR3 f := (f imgk ly regs0) (only parsing).
Local Abbreviation tr := ((AR3 (@YF54.tr)) ch).
Local Abbreviation AR0 f := (f n ch cl cnt v csz j0 jb j1 j2 j3 j4) (only parsing).
Local Abbreviation XW := (AR0 (AR3 (@YF54.XW))).
Local Abbreviation E0 := (AR0 (AR3 (@YF54.E0))).
Local Abbreviation EaT := (AR0 (AR3 (@YF54.EaT))).
Local Abbreviation EaC := (AR0 (AR3 (@YF54.EaC))).
Local Abbreviation EaSB := (AR0 (AR3 (@YF54.EaSB))).
Local Abbreviation EaTOP := (AR0 (AR3 (@YF54.EaTOP))).
Local Abbreviation Er := (AR0 (AR3 (@YF54.Er))).
Local Abbreviation E2 := (AR0 (AR3 (@YF54.E2))).
Local Abbreviation E1 := (AR0 (AR3 (@YF54.E1))).
Local Abbreviation E8 := (AR0 (AR3 (@YF54.E8))).
Local Abbreviation E10 := (AR0 (AR3 (@YF54.E10))).
Local Abbreviation E4 := (AR0 (AR3 (@YF54.E4))).
Local Abbreviation EaP := (AR0 (AR3 (@YF54.EaP))).
Local Abbreviation EaR8 := (AR0 (AR3 (@YF54.EaR8))).
Local Abbreviation EaK := (AR0 (AR3 (@YF54.EaK))).
Local Abbreviation EaSK := (AR0 (AR3 (@YF54.EaSK))).
Local Abbreviation EaSSLOT := (AR0 (AR3 (@YF54.EaSSLOT))).
Local Abbreviation EaPB := (AR0 (AR3 (@YF54.EaPB))).
Local Abbreviation EaPV := (AR0 (AR3 (@YF54.EaPV))).
Local Abbreviation EaRZ := (AR0 (AR3 (@YF54.EaRZ))).
Local Abbreviation EaU := (AR0 (AR3 (@YF54.EaU))).
Local Abbreviation EaSU := (AR0 (AR3 (@YF54.EaSU))).
Local Abbreviation EaFIL := (AR0 (AR3 (@YF54.EaFIL))).
Local Abbreviation EaNP := (AR0 (AR3 (@YF54.EaNP))).
Local Abbreviation EaND := (AR0 (AR3 (@YF54.EaND))).
Local Abbreviation WINT := (@YF54.WINT ly cl).
Local Abbreviation PBW := (ARa (@YF54.PBW ly)).
Local Abbreviation WIN := (ARa (@YF54.WIN ly regs0)).
Local Abbreviation win_in_WIN := (ARa (@YF54.win_in_WIN ly regs0)).
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
Local Abbreviation tr_length := ((AR3 (@YF54.tr_length)) mem0 n ch v DPOST).
Local Abbreviation Kv_range := ((ARa (@YF54.Kv_range ly regs0 mem0)) Hcl Hv Hv2 DPOST).
Local Abbreviation ARc f := (f mem0 n v Hv LY) (only parsing).
Local Abbreviation high_facts := ((ARc (AR3 (@YF54.high_facts _))) IMG DPOST).
Local Abbreviation blocks_facts := (@YF54.blocks_facts _ imgk ly LY IMG).
Local Abbreviation off_T := ((ARc (AR3 (@YF54.off_T _))) IMG DPOST).
Local Abbreviation off_C := ((ARc (AR3 (@YF54.off_C _))) IMG DPOST).
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
Local Abbreviation AR2 f := (f ly regs0 mem0 n cl cnt v) (only parsing).
Local Abbreviation AR4 f := (f Hcl Hv Hcnt Hv2 LY IMG) (only parsing).
Local Abbreviation derived_ranges := ((AR4 (AR2 (@YF54.derived_ranges _ imgk))) DPOST Nrange).
Hypothesis Hcl_def : cl = class_id (R8v + RZ).
Local Abbreviation CLk := (@YF54.CLk).
Local Abbreviation CLk_E := ((AR0 ((AR3 (@YF54.CLk_E)) mem0)) DPOST Nrange Hcl_def).
Local Abbreviation WIN1 := (ARa (@YF54.WIN1 ly regs0)).
Local Abbreviation WIN1_WIN := ((ARa (@YF54.WIN1_WIN ly regs0 mem0)) DPOST).
Local Abbreviation AR7 f := (f Hsp DPOST Nrange) (only parsing).
Local Abbreviation ARe f := (f Hcl Hv Hcnt Hjb) (only parsing).
Local Abbreviation WIN_odd := (AR7 (ARe ((AR2 (@YF54.WIN_odd)) jb))).
Local Abbreviation WIN1_odd := (AR7 (ARe ((AR2 (@YF54.WIN1_odd)) jb))).
Local Abbreviation WSKEL := (@YF54.WSKEL).
Local Abbreviation WSKEL1 := (@YF54.WSKEL1).
Local Abbreviation win_sub := (@YF54.win_sub).
Local Abbreviation win_sub_sound := (@YF54.win_sub_sound ly regs0 mem0 n v Hv DPOST).
Local Abbreviation WSKEL_WIN := ((AR4 (AR0 ((AR3 (@YF54.WSKEL_WIN _)) mem0))) DPOST Nrange).
Local Abbreviation WSKEL1_WIN1 := ((AR4 (AR0 ((AR3 (@YF54.WSKEL1_WIN1 _)) mem0))) DPOST Nrange).
Local Abbreviation windows_WIN := ((AR4 (AR0 ((AR3 (@YF54.windows_WIN _)) mem0))) DPOST Nrange).
Local Abbreviation windows_WIN1 := ((AR4 (AR0 ((AR3 (@YF54.windows_WIN1 _)) mem0))) DPOST Nrange).
Local Abbreviation frame_WIN1 := ((AR4 (AR0 ((AR3 (@YF54.frame_WIN1 _)) mem0))) DPOST Nrange).
Local Abbreviation WIN_not_high := (AR7 (AR4 (AR2 (@YF54.WIN_not_high _ imgk)))).
Variables (mat0 : list word).
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 (0x53104 + D_2c4)) mem0 (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis U1 : tfx_unwind_spec.
Hypothesis SEED : st_ok tfxsegs E0 SS0K (restrict (w_H W) (mkst regs0 (w64 (0x53104 + D_2c4)) mem0 (seg_rom tfxsegs))).
Local Abbreviation all_disjoint_of_forall := (@YF54.all_disjoint_of_forall).
Local Abbreviation AR5 f := (f imgk W ly regs0 mem0) (only parsing).
Local Abbreviation kept_of_frame := ((AR5 (@YF54.kept_of_frame)) n v DPOST).
Local Abbreviation SKEL_TAIL := (@YF54.SKEL_TAIL imgk).
Local Abbreviation stack_ivs := ((ARc (@YF54.stack_ivs _ ly regs0)) Hsp DPOST).
Local Abbreviation stack_ivs2 := ((ARc (@YF54.stack_ivs2 _ ly regs0)) Hsp DPOST).
Local Abbreviation DZONE_disj := (AR7 (AR4 (AR2 (@YF54.DZONE_disj _ imgk)))).
Local Abbreviation RFACTS := (ARa (AR3 (@YF54.RFACTS))).
Local Abbreviation zone_lit := (AR7 (AR4 (AR2 (@YF54.zone_lit _ imgk)))).
Local Abbreviation zone_T := (AR7 (AR4 (AR2 (@YF54.zone_T _ imgk)))).
Local Abbreviation zone_C := (AR7 (AR4 (AR2 (@YF54.zone_C _ imgk)))).
Local Abbreviation zone_K := (AR7 (AR4 (AR2 (@YF54.zone_K _ imgk)))).
Local Abbreviation zone_SH := (AR7 (AR4 (AR2 (@YF54.zone_SH _ imgk)))).
Local Abbreviation tail_ext_ok := (AR7 (AR4 (AR0 ((AR3 (@YF54.tail_ext_ok _)) mem0)))).
Local Abbreviation at_ST := (AR0 ((AR5 (@YF54.at_ST _)) md0)).
Local Abbreviation at_ST2 := ((AR0 ((AR5 (@YF54.at_ST2 _)) md0)) DPOST).
Local Abbreviation at_S2 := ((AR0 ((AR5 (@YF54.at_S2 _)) md0)) DPOST).
Local Abbreviation at_RET := ((AR5 (@YF54.at_RET _)) md0 n cl cnt v jb DPOST).
Ltac frame_acc HE :=
match goal with
| MEQ : (forall x : word, ~ WIN1 ?odd (bv_unsigned x) -> ?m1 x = ?mb x), HFx : frame_of ?E ?rs ?m1 ?m2 |- _ =>
let MEQ' := fresh "MEQ" in
assert (MEQ' : forall x : word, ~ WIN1 odd (bv_unsigned x) -> m2 x = mb x)
by (img_try (intros x Hx; transitivity (m1 x); [img_try (img_exact (frame_WIN1 odd E rs m1 m2 HE ltac:((img_case; vm_compute); img_refl) HFx x Hx)) | img_try (img_exact (MEQ x Hx))]));
clear MEQ HFx; rename MEQ' into MEQ
end.
Local Abbreviation memset_stretch := ((AR7 (ARe ((AR5 (@YF54.memset_stretch _)) md0 n cl cnt v jb))) mat0).
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
Local Abbreviation AR6 f := (f ly regs0 mem0 n cl v DPOST Nrange l off Hcl_class) (only parsing).
Local Abbreviation cl_range := (AR6 (@YF5a.cl_range)).
Local Abbreviation cls_geom := (AR6 (@YF5a.cls_geom)).
Local Abbreviation cls_wf := ((ARa (AR5 (@YF5a.cls_wf _))) DPOST Nrange B S l off HARm Hcl_class).
Local Abbreviation AR1 f := (f DPOST Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def) (only parsing).
Local Abbreviation AR9 f := (f _ imgk W) (only parsing).
Local Abbreviation off_facts := (AR1 ((AR2 (AR9 (@YF5a.off_facts))) Hv2)).
Local Abbreviation Kv_base := ((AR6 (@YF5a.Kv_base)) Hoff_def).
Local Abbreviation AR8 f := (AR2 f csz Hv2 LY) (only parsing).
Local Abbreviation Kv_geom := ((AR1 (AR8 (AR9 (@YF5a.Kv_geom)))) Hcsz_def).
Local Abbreviation Hcl' := (AR6 (@YF5a.Hcl')).
Local Abbreviation cl_k0 := ((ARa (@YF5a.cl_k0 ly regs0 mem0)) DPOST Nrange Hcl_def l off).
Local Abbreviation ARd f := (AR2 f Hv2 Hsp) (only parsing).
Local Abbreviation Hcnt' := (AR1 (ARd (AR9 (@YF5a.Hcnt')))).
Local Abbreviation Hv' := (AR1 ((AR2 (AR9 (@YF5a.Hv'))) Hv2)).
Local Abbreviation cached_vs_chunk := ((AR1 ((AR8 (AR9 (@YF5a.cached_vs_chunk))) Hsp)) Hcsz_def).
Local Abbreviation find_chunk_at_none := (AR1 (ARd (AR9 (@YF5a.find_chunk_at_none)))).
Local Abbreviation shadow250 := ((AR1 ((AR8 (AR9 (@YF5a.shadow250))) Hsp)) Hcsz_def).
Local Abbreviation shadow_present := ((AR1 ((AR8 (AR9 (@YF5a.shadow_present))) IMG Hsp)) Hcsz_def).
Local Abbreviation vis_present := (AR1 (ARd (AR9 (@YF5a.vis_present)))).
Local Abbreviation KPRES := ((AR1 ((AR8 (AR9 (@YF5a.KPRES))) Hsp)) Hcsz_def).
Local Abbreviation SKPRES := ((AR1 ((AR8 (AR9 (@YF5a.SKPRES))) IMG Hsp)) Hcsz_def).
Local Abbreviation PB250 := ((AR1 ((AR8 (AR9 (@YF5a.PB250))) IMG Hsp)) Hcsz_def).
Local Abbreviation in_thread_junk := (AR1 (ARd (AR9 (@YF5a.in_thread_junk)))).
Local Abbreviation junk_word := (AR1 ((AR2 (AR9 (@YF5a.junk_word))) Hv2 LY IMG Hsp)).
Local Abbreviation junk_byte := ((AR1 ((AR8 (AR9 (@YF5a.junk_byte))) Hsp)) Hcsz_def).
Local Abbreviation junk_values := ((AR1 ((AR8 (AR9 (@YF5a.junk_values))) IMG Hsp)) Hcsz_def).
Local Abbreviation cell_sym := ((AR7 ((AR2 (AR9 (@YF5a.cell_sym))) Hv2)) B S l off TS HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation cell_lit := ((AR7 ((AR2 (AR9 (@YF5a.cell_lit))) Hv2)) B S l off TS HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation cell_state := (AR1 (ARd (AR9 (@YF5a.cell_state)))).
Local Abbreviation In_acells_cache := (AR1 (ARd (AR9 (@YF5a.In_acells_cache)))).
Local Abbreviation In_combine_seq_last := (AR1 (ARd (AR9 (@YF5a.In_combine_seq_last)))).
Local Abbreviation cache_vals := ((AR1 ((AR2 (AR9 (@YF5a.cache_vals))) csz Hv2 Hsp)) Hcsz_def).
Local Abbreviation unwinding_val := (AR1 (ARd (AR9 (@YF5a.unwinding_val)))).
Local Abbreviation sk_val := ((AR1 ((AR8 (AR9 (@YF5a.sk_val))) IMG Hsp)) Hcsz_def).
Local Abbreviation val_mem_mod8 := (AR1 (ARd (AR9 (@YF5a.val_mem_mod8)))).
Local Abbreviation chunk_lit := (AR1 ((AR0 (AR5 (@YF5a.chunk_lit _))) Hv2 Hsp)).
Local Abbreviation chunk_lit_at := (AR1 ((AR0 (AR5 (@YF5a.chunk_lit_at _))) Hv2 Hsp)).
Local Abbreviation chunk_atom := (AR1 ((AR0 (AR5 (@YF5a.chunk_atom _))) Hv2 Hsp)).
Local Abbreviation ARb f := (f B S l off TS HTSD HARm Hpres0 Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def Hj0 Hj1 Hj2 Hj3 Hj4 Hjb_def) (only parsing).
Local Abbreviation REG0_ok := (ARb (AR7 ((ARe (AR0 (AR5 (@YF5b.REG0_ok _)))) Hv2 LY IMG))).
Local Abbreviation Kv32 := ((ARa (AR5 (@YF5c.Kv32 _))) Hv2 LY DPOST l off).
Local Abbreviation PAIRS_ok := ((AR1 ((AR4 (AR0 (AR5 (@YF5c.PAIRS_ok _)))) Hsp)) Hcsz_def).
Local Abbreviation FACTS_ok := ((AR7 ((ARe (AR0 (AR5 (@YF5c.FACTS_ok _)))) Hv2 LY IMG Hn)) Hcl_def B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def).
Local Abbreviation SEED_ok := (ARb ((AR7 ((ARe (AR0 (AR5 (@YF5c.SEED_ok _ _)))) Hv2 LY IMG Hn Htp)) Hcl_def)).
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
Let rd0 : reader := aview tfxsegs (w_H W) mem0.
Let WF := am_wf B ly S rd0 HARm.
Definition CZONE (a : Z) : Prop :=
(0x10000 <= a < (0x5ff000 + D_1000))   \/ (0x7fff8000 <= a < 0x80050000) \/ (T <= a < T + 80) \/ (ly_C ly <= a < ly_C ly + 160) \/ (TFX_TSD <= a < TFX_TSD + 8) \/
(ly_D ly <= a < ly_D ly + 4096).
Definition abs_cell_ok {imgk : img} (c : acell) : bool :=
match c_at c with
| ANum a => (0x10000 <=? a) && ((a + Z.max 1 (Z.of_nat (c_w c)) <=? (0x5ff000 + D_1000)) || ((0x7fff8000 <=? a) && (a + Z.max 1 (Z.of_nat (c_w c)) <=? 0x80050000)))
| _ => false
end.
Lemma abs_cells_ok : forallb abs_cell_ok (Tfx_const_abs ++ Tfx_const_shadow) = true.
Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma const_cells_zone : forall c k, In c (as_const B ly) -> 0 <= k < Z.max 1 (Z.of_nat (c_w c)) -> CZONE (aeval B ly (c_at c) + k).
Proof.
intros c k Hin Hk. rewrite (ts_const B TS ly) in Hin. unfold Tfx_const in Hin. apply in_app_iff in Hin as [Hin|Hin].
- unfold Tfx_const_sym in Hin. cbn [In] in Hin. unfold CZONE, T.
pose proof (ts_tp B TS) as ETP. pose proof (ts_inst B TS) as EIN.
repeat match type of Hin with
| _ \/ _ => destruct Hin as [<-|Hin]; [img_try (cbn [c_at c_w aeval aoff z8 z4 z1 c8 c4 c1] in *; cbn in Hk; rewrite ?ETP, ?EIN, ?HTSD;
unfold TFX_TP, TFX_INST, TFX_TSD, o_space, o_rinfo, o_sec_chunks, kStackSpan in *; zlia) |]
| False => destruct Hin
end.
- pose proof (proj1 (forallb_forall _ _) abs_cells_ok c Hin) as Hc. unfold abs_cell_ok in Hc.
destruct (c_at c) eqn:Ea; try discriminate. cbn [aeval].
apply andb_prop in Hc as [Hz Hc]. apply Z.leb_le in Hz.
apply Bool.orb_prop in Hc. unfold CZONE. destruct Hc as [Hc|Hc]; [img_try (apply Z.leb_le in Hc; zlia)|].
apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. zlia.
Qed.
Lemma CZONE_untouched : forall odd a, CZONE a ->
0 <= a < 2 ^ 64 /\ ~ WIN odd a /\ ~ (Kv + RZ <= a < Kv + RZ + NPv) /\ ~ (SUv <= a < SUv + N8D / 8) /\
~ (sp0 - 2272 - DEP_STK <= a < sp0 - 2272) /\ ~ (ly_NB ly <= a < ly_NB ly + kNodesBlockSize) /\ ~ (ly_SB ly <= a < ly_SB ly + kStoreBlockSize).
Proof.
intros odd a Ha. pose proof derived_ranges as DR. pose proof high_facts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & _).
pose proof Kv_range as HKR. pose proof stack_ivs as (SI1 & SI2 & SI3). pose proof blocks_facts as (NBhi & SBhi & TNB & TSB & _ & _ & _ & _ & PT).
pose proof HC_NB as [CNB CSB]. pose proof HCX as [CP CT]. destruct Hsp as (S1 & _ & S3 & _). pose proof (lo_top ly LY) as (_ & _ & _ & T4 & _ & _ & T7).
unfold zdisjoint in TNB, TSB, CNB, CSB, CP, CT, PT. cbn [fst snd] in TNB, TSB, CNB, CSB, CP, CT, PT.
pose proof (pairwise_ij _ _ 2 4 _ _ (lo_disj ly LY) eq_refl eq_refl) as DT. pose proof (pairwise_ij _ _ 0 6 _ _ (lo_disj ly LY) eq_refl eq_refl) as DP.
pose proof (pairwise_ij _ _ 4 2 _ _ (lo_disj ly LY) eq_refl eq_refl) as DNB. pose proof (pairwise_ij _ _ 5 1 _ _ (lo_disj ly LY) eq_refl eq_refl) as DSB.
pose proof (pairwise_ij _ _ 7 0 _ _ (lo_disj ly LY) eq_refl eq_refl) as DSTK. pose proof (Forall_nth' _ _ 7 _ (lo_app ly LY) eq_refl) as DH. cbv beta in DH. unfold in_app in DH.
unfold zdisjoint in DT, DP, DNB, DSB, DSTK. cbn [fst snd] in DT, DP, DNB, DSB, DSTK, DH.
pose proof (zone3_apart_img _ _ a F1) as TI. pose proof (zone3_apart_hsh _ _ a F1) as TH.
pose proof (zone3_apart_img _ _ a F7) as CI. pose proof (zone3_apart_hsh _ _ a F7) as CH.
pose proof (zone3_apart_img _ _ a NBhi) as NI. pose proof (zone3_apart_hsh _ _ a NBhi) as NH.
pose proof (zone3_apart_img _ _ a SBhi) as BI. pose proof (zone3_apart_hsh _ _ a SBhi) as BH.
unfold CZONE, WIN, WINT, PBW, TFX_TSD in *. numconst. unfold T, sp0 in *.
destruct Ha as [Ha|[Ha|[Ha|[Ha|[Ha|Ha]]]]].
- clear SI1 SI2 SI3 TNB TSB CNB CSB CP CT PT DT DP DNB DSB DSTK DH TH CH NH BH. repeat split; zlia.
- clear SI1 SI2 SI3 TNB TSB CNB CSB CP CT PT DT DP DNB DSB DSTK DH TI CI NI BI. repeat split; zlia.
- clear SI2 SI3 CNB CSB CP CT DT DP DNB DSB DSTK DH TI CI CH NI NH BI BH. repeat split; zlia.
- clear SI1 SI2 TNB TSB PT DT DP DNB DSB DSTK DH TI TH CI NI NH BI BH. repeat split; zlia.
- clear SI1 SI2 SI3 TNB TSB CNB CSB CP CT PT DT DP DNB DSB DSTK DH TH CH NH BH. repeat split; zlia.
- clear SI2 TNB TSB CNB CSB CP CT PT TI TH CI CH NI NH BI BH. repeat split; zlia.
Qed.
Lemma cell_holds_agree : forall (rd rd' : reader) c,
(forall k, 0 <= k < Z.max 1 (Z.of_nat (c_w c)) -> rd' (aeval B ly (c_at c) + k) = rd (aeval B ly (c_at c) + k)) ->
cell_holds B ly rd c -> cell_holds B ly rd' c.
Proof.
intros rd rd' c He Hc. unfold cell_holds in *. destruct (c_val c) as [e|m vv].
- intros k Hk. rewrite He by zlia. img_exact (Hc k Hk).
- destruct Hc as (b & Hb & Hm). exists b. split; [|img_try (img_exact Hm)]. rewrite <- (Z.add_0_r (aeval B ly (c_at c))). rewrite He by zlia. rewrite Z.add_0_r. img_exact Hb.
Qed.
Lemma aview_agree : forall (mem mem' : word -> option byte) a, 0 <= a < 2 ^ 64 ->
mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a) -> aview tfxsegs (w_H W) mem' a = aview tfxsegs (w_H W) mem a.
Proof. intros mem mem' a Ha He. unfold aview. rewrite (mbyte_mrestrict_same (w_H W) mem mem' a He). img_refl. Qed.
Lemma const_kept : forall mem1 mem2, Forall (cell_holds B ly (aview tfxsegs (w_H W) mem1)) (as_const B ly) ->
(forall x : word, CZONE (bv_unsigned x) -> mem2 x = mem1 x) ->
Forall (cell_holds B ly (aview tfxsegs (w_H W) mem2)) (as_const B ly).
Proof.
intros mem1 mem2 HC He. img_apply Forall_forall. intros c Hc.
img_apply (cell_holds_agree (aview tfxsegs (w_H W) mem1)); [| img_try (img_exact (proj1 (Forall_forall _ _) HC c Hc))].
intros k Hk. pose proof (const_cells_zone c k Hc Hk) as Z1. pose proof (proj1 (CZONE_untouched false _ Z1)) as R.
img_apply aview_agree; [img_try (img_exact R)|]. img_apply He. rewrite unsigned_lit_small by img_exact R. img_exact Z1.
Qed.
Lemma depot_ids_bound : forall S', List.NoDup (st_depot S') -> incl (st_depot S') (as_universe B) -> depot_ids S' <= 4097.
Proof.
intros S' ND INC. pose proof (ts_universe B TS) as (U1' & _ & _). unfold depot_ids, DEPOT_MAX in *.
pose proof (NoDup_incl_length ND INC). zlia.
Qed.
Lemma depot_mem_ok_agree : forall S' (rd rd' : reader), depot_ids S' <= 4098 ->
(forall a, DZONE a -> rd' a = rd a) -> depot_mem_ok B ly S' rd -> depot_mem_ok B ly S' rd'.
Proof.
intros S' rd rd' HID He (D1' & D2 & D3). pose proof (ts_depot B TS) as ED. pose proof (ts_store B TS) as ES.
assert (EZ : forall a, (TFX_DEPOT <= a < TFX_DEPOT + d_map1 + 8) \/ (TFX_STORE <= a < TFX_STORE + 32) \/
(ly_NB ly <= a < ly_NB ly + kNodesBlockSize) \/ (ly_SB ly <= a < ly_SB ly + kStoreBlockSize) -> rd' a = rd a).
{ intros a Ha. img_apply He. unfold DZONE, TFX_DEPOT, TFX_STORE, d_map1 in *. zlia. }
split; [|img_try (split)].
- img_apply Forall_forall. intros c Hc. img_apply (cell_holds_agree rd); [| img_try (img_exact (proj1 (Forall_forall _ _) D1' c Hc))].
intros k Hk. img_apply EZ. unfold depot_cells in Hc. cbn in Hc.
destruct Hc as [<-|[<-|[<-|[<-|[]]]]]; cbn [c_at c_w aeval aoff z4 z8 c4 c8] in *; cbn in Hk; rewrite ?ED, ?ES; unfold d_nuniq, d_map1, s_total, s_block0 in *; zlia.
- destruct D2 as (heads & links & H1 & H2 & H3). exists heads, links. split; [|img_try (split; [|img_exact H3])].
+ intros b Hb. destruct (H1 b Hb) as [Hh Hr]. split; [img_try (img_exact Hh)|]. intros k Hk. rewrite EZ; [img_try (img_exact (Hr k Hk))|].
rewrite ED. unfold d_tab_words, d_map1 in *. zlia.
+ intros id Hid. destruct (H2 id Hid) as (L1 & L2 & L3). split; [img_try (img_exact L1)|]. split.
* intros k Hk. rewrite EZ; [img_try (img_exact (L2 k Hk))|]. unfold kNodesBlockSize. zlia.
* intros k Hk. rewrite EZ; [img_try (img_exact (L3 k Hk))|]. unfold kNodesBlockSize. zlia.
- img_apply Forall_forall. intros r Hr i Hi. rewrite EZ; [img_try (img_exact (proj1 (Forall_forall _ _) D3 r Hr i Hi))|].
cbn in Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd aeval aoff] in *; rewrite ?ED, ?ES; unfold d_nuniq, d_map1 in *; zlia.
Qed.
Lemma depot_ok_ext : forall S1 S2 (rd : reader), st_depot S1 = st_depot S2 -> depot_ok B ly rd S1 -> depot_ok B ly rd S2.
Proof. intros S1 S2 rd E. unfold depot_ok, depot_ids, depot_traces. rewrite E. img_exact (fun H => H). Qed.
Lemma depot_at0 : depot_mem_ok B ly S rd0.
Proof.
split; [|img_try (split)].
- img_apply Forall_forall. intros c Hc. img_apply (proj1 (Forall_forall _ _) (am_cells B ly S rd0 HARm)).
unfold acells. do 6 (img_apply in_or_app; right). img_apply in_or_app. left. img_exact Hc.
- img_exact (am_depot B ly S rd0 HARm).
- img_apply Forall_forall. intros r Hr. cbn in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]].
1-3: img_apply (proj1 (Forall_forall _ _) (am_junk B ly S rd0 HARm)); unfold ajunk; right; right; do 6 (img_apply in_or_app; right); img_apply in_or_app; left; cbn; tauto.
all: img_apply (proj1 (Forall_forall _ _) (am_areas B ly S rd0 HARm)); unfold aareas; do 3 (img_apply in_or_app; right); cbn; tauto.
Qed.
Definition DPOST3 (z : Z) (mem2 : word -> option byte) : Prop :=
aok S (KDepot tr) z /\ depot_mem_ok B ly (depot_after z tr S) (aview tfxsegs (w_H W) mem2) /\
Forall (cell_holds B ly (aview tfxsegs (w_H W) mem2)) (as_const B ly).
Hypothesis Htr : In tr (as_universe B).
Lemma D1W_ok : tfx_depot_spec B ->
forall (regs : bvmap 5 word) (mem : word -> option byte) (md : Model),
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
DPOST3 z mem').
Proof.
intros HD1 regs mem md R10 R11 R3 R4 R1 Rsp BUF PRES MEQ.
destruct Hsp as (S1 & S2 & S3 & S4). pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
assert (CST : Forall (cell_holds B ly (aview tfxsegs (w_H W) mem)) (as_const B ly)).
{ img_apply (const_kept mem0); [img_try (img_exact (am_const B ly S rd0 HARm))|]. intros x Hx. img_apply MEQ. img_exact (proj1 (proj2 (CZONE_untouched false _ Hx))). }
assert (DEP : depot_mem_ok B ly S (aview tfxsegs (w_H W) mem)).
{ img_apply (depot_mem_ok_agree S rd0).
- pose proof (wf_depot _ _ _ _ _ WF) as [ND INC]. pose proof (depot_ids_bound S ND INC). zlia.
- intros a Ha. pose proof (DZONE_disj false a Ha) as (N1 & _). pose proof blocks_facts as (NBhi & SBhi & _).
assert (Ra : 0 <= a < 2 ^ 64) by (img_try (clear - Ha NBhi SBhi LY; unfold DZONE in Ha; numconst; zlia)).
img_apply aview_agree; [img_try (img_exact Ra)|]. img_apply MEQ. rewrite unsigned_lit_small by img_exact Ra. img_exact N1.
- img_exact depot_at0. }
eapply SRr_mono.
{ img_apply (HD1 W ly S regs mem md (sp0 - IFRAME + 16) tr LY IMG WF Htr CST DEP R10 R11).
- rewrite R3, Hgp. img_refl.
- img_exact R4.
- rewrite R1. img_apply ret_ok_even. img_refl.
- img_exact BUF.
- unfold IFRAME. img_apply Z.mod_divide; [img_try (zlia)|]. pose proof S4 as S4'. apply Z.mod_divide in S4' as [q Hq]; [|img_try (zlia)]. exists (2 * q - 264). zlia.
- unfold IFRAME, ASTACK in *. zlia.
- unfold IFRAME, ASTACK in *. zlia.
- right. rewrite Rsp. unfold IFRAME. zlia.
- rewrite Rsp. img_apply Z.mod_divide; [img_try (zlia)|]. pose proof S4 as S4'. apply Z.mod_divide in S4' as [q Hq]; [|img_try (zlia)]. exists (q - 142). zlia.
- rewrite Rsp. unfold DEP_STK, ASTACK in *. zlia.
- rewrite Rsp. zlia.
- rewrite Rsp. intros a Ha. img_apply PRES. unfold DEP_STK, ASTACK in *. zlia. }
intros W' c' Hle (-> & z & regs' & mem' & mat & -> & AOK & RP & FR & PR' & DEP' & CST'). split; [img_refl|].
exists z, regs', mem', mat. split; [img_try (rewrite R1; img_refl)|]. split; [img_try (img_exact RP)|]. split; [|img_try (split; [img_exact PR'| img_exact (conj AOK (conj DEP' CST'))])].
intros x N1 N2. img_apply FR; [img_try (rewrite Rsp; img_exact N1)|].
intros FP. img_apply N2. unfold depot_footprint, DZONE in *. rewrite (ts_depot B TS), (ts_store B TS) in FP. unfold TFX_DEPOT, TFX_STORE, d_map1 in FP. zlia.
Qed.
Definition st_popped (S0 : astate) (c : Z) (l0 : list Z) : astate :=
set_cache (zupd c (mkPC (pc_max (cache S0 c)) l0) (st_cache S0)) S0.
Definition new_chunk (c o n0 : Z) : chunk := mkChunk (PPrim (region_off c + o)) n0 CAllocated.
Definition st_final (S0 : astate) (c : Z) (l0 : list Z) (o n0 : Z) (t : list Z) (z : Z) : astate :=
let s1 := depot_after z t (st_popped S0 c l0) in
set_chunks (upd_chunk (st_chunks s1) (new_chunk c o n0)) s1.
Let Kc : chunk := new_chunk cl off n.
Let SF (z : Z) : astate := st_final S cl l off n tr z.
Lemma Kc_user : sptr_addr B ly (ck_user Kc) = Kv + RZ.
Proof.
pose proof case0_sizes as (_ & RS & _). unfold Kc, new_chunk, ck_user, ck_rz. cbn [ck_beg ck_req padd]. rewrite RS.
rewrite Kv_is_sptr. unfold sptr_addr. cbn. zlia.
Qed.
Definition MPF (z : Z) : Prop := Wf (as_universe B) (SF z) /\ qtight (SF z).
Definition AR_final_stmt : Prop := forall odd z regs' mem' mat,
at_RET odd z W (mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md0) mat md0)) ->
(odd = true <-> NPv mod 8 <> 0) ->
MPF z ->
AR tfxsegs B ly S W mem0 md0 ->
AR tfxsegs B ly (SF z) W mem' (with_vm_backing (m_vm_lazy md0) mat md0).
Lemma WR_owned : forall odd a, 0 <= a < 2 ^ 64 -> (odd = true -> NPv mod 8 <> 0) ->
WIN odd a \/ DZONE a \/ (SUv <= a < SUv + N8D / 8) ->
(sp0 - ASTACK <= a < sp0) \/ aowned B ly S a.
Proof.
pose proof HPB250 as HPB250_pin; clear HPB250_pin.
intros odd a Ra Hodd Hw. pose proof derived_ranges as DR. pose proof Kv_geom as (V1 & V2 & V3 & V4 & V5). pose proof cls_geom as (K1 & _ & _ & _ & K5 & K6).
pose proof high_facts as (F1 & F2 & _).
assert (OWN_SH : forall g, Kv <= g < Kv + class_size cl -> aowned B ly S (shadow_addr g)).
{ intros g Hg. img_apply (own_shadow_prim B ly S rd0 g HARm). zlia. }
assert (OWN_K : forall b, Kv <= b < Kv + RZ -> aowned B ly S b).
{ intros b Hb. img_apply (own_prim_nonuser B ly S rd0 b HARm); [img_try (zlia)|]. intros k Hk _.
pose proof (cached_vs_chunk k Hk) as D. pose proof (chunk_facts B ly S rd0 k HARm Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _). zlia. }
pose proof RZ_num as (RZr & RZ8 & Nlo & NPr & R8r & NPR8 & N8r & NPN8 & FILN).
destruct Hw as [Hw|[Hw|Hw]].
- unfold WIN, WINT, PBW in Hw. destruct Hw as [Hs|[Hw|[[Hw|Hw]|[Ho Hw]]]]; [img_try (left; img_exact Hs)| img_try (right) | img_try (right; img_apply OWN_K; clear - Hw RZr; zlia) | img_try (right; img_apply OWN_K; clear - Hw RZr DR; zlia) | img_try (right)].
+ img_apply (own_core B ly S rd0 (ly_T ly, kThreadObjSize) a HARm); [img_try (unfold core_extents; cbn; tauto)|]. cbn [fst snd].
ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, t_cache, t_unwinding in *. unfold T in Hw. zlia.
+ replace a with (shadow_addr (Kv + RZ + N8D)) by (img_try (unfold shadow_addr, PBv, SHBv, SHADOW_OFF in *; zlia)). img_apply OWN_SH.
pose proof (Hodd Ho) as E8. pose proof (Z.div_mod NPv 8 ltac:(img_try (zlia))) as DM. pose proof (Z.mod_pos_bound NPv 8 ltac:(img_try (zlia))) as MB. clear - E8 DM MB K5 RZr NPr. unfold N8D in *. zlia.
- right. unfold DZONE in Hw. destruct Hw as [Hw|[Hw|Hw]].
+ img_apply (own_static B ly S rd0 a HARm). rewrite (ts_owned B TS). unfold Tfx_owned_static. img_apply Exists_exists.
eexists. split; [img_try (right; right; right; left; img_refl)|]. unfold in_zr; cbn. zlia.
+ img_apply (own_core B ly S rd0 (ly_NB ly, kNodesBlockSize) a HARm); [img_try (unfold core_extents; cbn; tauto)| img_try (cbn [fst snd]; img_exact Hw)].
+ img_apply (own_core B ly S rd0 (ly_SB ly, kStoreBlockSize) a HARm); [img_try (unfold core_extents; cbn; tauto)| img_try (cbn [fst snd]; img_exact Hw)].
- right. replace a with (shadow_addr (Kv + 8 * (a - SKv))).
2:{ unfold shadow_addr, SKv, SHBv, SHADOW_OFF in *. rewrite (Z.mul_comm 8 (a - (2147450880 + Kv / 8))), Z.div_add by zlia. zlia. }
img_apply OWN_SH. unfold SKv, SHBv in *. pose proof (Z.div_mod Kv 8 ltac:(img_try (zlia))). pose proof (Z.mod_pos_bound Kv 8 ltac:(img_try (zlia))).
pose proof (div8_bounds NPv ltac:(img_try (zlia))). unfold N8D in *. rewrite Z.div_mul in Hw by zlia. clear - Hw H H0 H1 K5 RZr RZ8 NPr DR V3. zlia.
Qed.
Lemma LEAF_ok : AR_final_stmt -> AR tfxsegs B ly S W mem0 md0 ->
forall odd z W' c', at_RET odd z W' c' -> (odd = true <-> NPv mod 8 <> 0) ->
MPF z ->
malloc_leaf tfxsegs B ly S W regs0 mem0 md0 n (ck_user Kc, SF z) W' c'.
Proof.
pose proof HPB250 as HPB250_pin; clear HPB250_pin.
intros ARF HAR odd z W' c' HR Hodd MP.
pose proof HR as HR0. destruct HR as (-> & regs' & mem' & mat & -> & R10 & RCS & (memD & DP & PRD & EQD) & MEQF & PRS & PRW & VALS).
exists ly, regs', mem', (with_vm_backing (m_vm_lazy md0) mat md0).
split. { unfold cfg_at, raZ, w64. rewrite Z_to_bv_bv_unsigned. img_refl. }
cbn [fst snd]. split; [| img_try (split; [rewrite R10, Kc_user; img_refl | img_exact (proj2 MP)])].
split; [img_try (img_exact (ARF odd z regs' mem' mat HR0 Hodd MP HAR))|].
split; [img_try (img_apply layout_le_refl)|].
split; [img_try (img_apply wle_refl)|].
split. { intros r Hr. img_apply RCS. unfold acallee_saved in Hr.
assert (H18 : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by zlia.
clear - RCS H18.
assert (E5 : forall k : Z, 0 <= k < 32 -> forall b : bv 5, bv_unsigned b = k -> Z_to_bv 5 k = b) by (img_try (intros k Hk b Hb; img_apply bv_eq; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; img_change (2 ^ Z.of_N 5) with 32; rewrite Z.mod_small by zlia; symmetry; img_exact Hb)).
destruct H18 as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
[ img_try (rewrite (E5 2 ltac:(zlia) 2%bv eq_refl)) | img_try (rewrite (E5 3 ltac:(zlia) 3%bv eq_refl)) | img_try (rewrite (E5 4 ltac:(zlia) 4%bv eq_refl))
| img_try (rewrite (E5 8 ltac:(zlia) 8%bv eq_refl)) | img_try (rewrite (E5 9 ltac:(zlia) 9%bv eq_refl)) | img_try (rewrite (E5 18 ltac:(zlia) 18%bv eq_refl))
| img_try (rewrite (E5 19 ltac:(zlia) 19%bv eq_refl)) | img_try (rewrite (E5 20 ltac:(zlia) 20%bv eq_refl)) | img_try (rewrite (E5 21 ltac:(zlia) 21%bv eq_refl))
| img_try (rewrite (E5 22 ltac:(zlia) 22%bv eq_refl)) | img_try (rewrite (E5 23 ltac:(zlia) 23%bv eq_refl)) | img_try (rewrite (E5 24 ltac:(zlia) 24%bv eq_refl))
| img_try (rewrite (E5 25 ltac:(zlia) 25%bv eq_refl)) | img_try (rewrite (E5 26 ltac:(zlia) 26%bv eq_refl)) | img_try (rewrite (E5 27 ltac:(zlia) 27%bv eq_refl)) ];
cbn [In]; tauto. }
split. { unfold same_io. destruct md0; cbn; repeat split; img_refl. }
split.
-
intros a Ra NO NO' NS NE. img_apply aview_agree; [img_try (img_exact Ra)|]. img_apply MEQF; rewrite unsigned_lit_small by img_exact Ra.
+ intros Hw. destruct (WR_owned odd a Ra ltac:(img_try (intros Ho; img_apply Hodd; img_exact Ho)) (or_introl Hw)) as [Hs|Ho]; [|img_try (img_exact (NO Ho))].
img_apply NS. unfold ascratch, spZ. left. img_exact Hs.
+ intros Hw. destruct (WR_owned odd a Ra ltac:(img_try (intros Ho; img_apply Hodd; img_exact Ho)) (or_intror (or_introl Hw))) as [Hs|Ho]; [|img_try (img_exact (NO Ho))].
img_apply NS. unfold ascratch, spZ. left. img_exact Hs.
+ intros Hu. img_apply NE. split; [img_try (discriminate)|]. rewrite Kc_user. pose proof case0_sizes as (_ & _ & _ & _ & _ & _ & RQ). rewrite RQ. img_exact Hu.
+ intros Hw. destruct (WR_owned odd a Ra ltac:(img_try (intros Ho; img_apply Hodd; img_exact Ho)) (or_intror (or_intror Hw))) as [Hs|Ho]; [|img_try (img_exact (NO Ho))].
img_apply NS. unfold ascratch, spZ. left. img_exact Hs.
- intros a Ha. img_exact (PRS a Ha).
Qed.
Lemma Kc_fresh : forall k, In k (st_chunks S) -> sptr_eqb (ck_beg k) (ck_beg Kc) = false.
Proof.
intros k Hk. pose proof off_facts as (_ & _ & _ & _ & _ & NI & _).
destruct (sptr_eqb (ck_beg k) (ck_beg Kc)) eqn:E; [|img_refl]. exfalso.
unfold Kc, new_chunk in E. cbn [ck_beg] in E. destruct (ck_beg k) as [|o|r o|c p] eqn:Eb; cbn in E; try discriminate.
apply Z.eqb_eq in E. img_apply NI. img_apply in_or_app. right. img_apply in_or_app. left.
pose proof (In_chunk_offs S k o Hk Eb) as IN. rewrite E in IN.
replace (prim_class (region_off cl + off)) with cl in IN.
2:{ pose proof off_facts as (O1 & O2 & _). pose proof cls_geom as (K1 & _). pose proof cl_range.
unfold prim_class. rewrite region_off_eq by zlia. symmetry. rewrite Z.shiftr_div_pow2 by zlia.
pose proof (mapped_user_bound (as_universe B) 0 0 0 S cl WF ltac:(img_try (zlia))). unfold kUserMapSize, EV_MAX in *.
rewrite Z.div_add_l by zlia. rewrite Z.div_small by zlia. zlia. }
rewrite region_off_eq in IN by (img_try (pose proof cl_range; zlia)). replace (cl * 2 ^ 32 + off - cl * 2 ^ 32) with off in IN by zlia. img_exact IN.
Qed.
Lemma upd_chunk_fresh : forall lst, (forall k, In k lst -> sptr_eqb (ck_beg k) (ck_beg Kc) = false) -> upd_chunk lst Kc = lst ++ [Kc].
Proof.
induction lst as [|k t IH]; intros H; [img_refl|]. cbn [upd_chunk app]. rewrite (H k (or_introl eq_refl)). f_equal. img_apply IH. intros k' Hk'. img_apply H. right. img_exact Hk'.
Qed.
Lemma SF_chunks : forall z, st_chunks (SF z) = st_chunks S ++ [Kc].
Proof.
intros z. unfold SF, st_final. cbn [st_chunks set_chunks]. replace (st_chunks (depot_after z tr (st_popped S cl l))) with (st_chunks S).
- img_apply upd_chunk_fresh. img_exact Kc_fresh.
- unfold depot_after, st_popped. destruct (z =? 0); img_refl.
Qed.
Lemma SF_same : forall z,
st_regions (SF z) = st_regions S /\ st_cache_inited (SF z) = st_cache_inited S /\ st_secs (SF z) = st_secs S /\
st_sec_arr (SF z) = st_sec_arr S /\ st_sec_reserved (SF z) = st_sec_reserved S /\ st_qthread (SF z) = st_qthread S /\
st_qglobal (SF z) = st_qglobal S /\ st_fs (SF z) = st_fs S /\ st_internal_inited (SF z) = st_internal_inited S /\
st_nev (SF z) = st_nev S /\ st_cache (SF z) = zupd cl (mkPC (pc_max (cache S cl)) l) (st_cache S) /\
st_depot (SF z) = (if z =? 0 then st_depot S else st_depot S ++ [tr]).
Proof.
intros z. unfold SF, st_final, depot_after, st_popped. destruct (z =? 0); cbn; repeat split; img_refl.
Qed.
Lemma SF_sec_extents : forall z, sec_extents ly (SF z) = sec_extents ly S.
Proof.
intros z. unfold sec_extents. rewrite SF_chunks. rewrite flat_map_app. cbn. rewrite app_nil_r. img_refl.
Qed.
Lemma SF_sec_live : forall z, sec_live_bytes (SF z) = sec_live_bytes S.
Proof.
intros z. unfold sec_live_bytes. rewrite SF_chunks. rewrite fold_right_app. cbn. img_refl.
Qed.
Lemma SF_ledger : forall z md, ALedger tfxsegs ly S md -> ALedger tfxsegs ly (SF z) md.
Proof.
intros z md L. pose proof (SF_same z) as (R1 & _ & _ & _ & Rres & _ & _ & _ & _ & Rnev & _).
destruct L as [L0 L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12 L13].
constructor; try assumption.
- destruct L3 as (pieces & P1 & P2). exists pieces. split; [|img_try (img_exact P2)].
destruct P1 as (Q1 & Q2 & Q3). unfold prim_pieces_ok, cut_ok, prim_hole_at, reg in *. rewrite R1. img_exact (conj Q1 (conj Q2 Q3)).
- rewrite SF_sec_extents. img_exact L6.
- rewrite SF_sec_extents. img_exact L7.
-   rewrite SF_sec_extents, Rres. unfold prim_committed in *. rewrite R1. img_exact L8.
-   rewrite SF_sec_extents. img_exact L11.
Qed.
Lemma cell_holds_agree2 : forall (rd1 rd2 rd' : reader) c,
(forall k, 0 <= k < Z.max 1 (Z.of_nat (c_w c)) ->
rd' (aeval B ly (c_at c) + k) = rd1 (aeval B ly (c_at c) + k) \/ rd' (aeval B ly (c_at c) + k) = rd2 (aeval B ly (c_at c) + k)) ->
cell_holds B ly rd1 c -> cell_holds B ly rd2 c -> cell_holds B ly rd' c.
Proof.
intros rd1 rd2 rd' c He H1 H2. unfold cell_holds in *. destruct (c_val c) as [e|m vv].
- intros k Hk. destruct (He (Z.of_nat k) ltac:(img_try (zlia))) as [E|E]; rewrite E; [img_try (img_exact (H1 k Hk)) | img_try (img_exact (H2 k Hk))].
- destruct H1 as (b1 & Hb1 & Hm1). destruct H2 as (b2 & Hb2 & Hm2).
destruct (He 0 ltac:(img_try (zlia))) as [E|E]; rewrite Z.add_0_r in E; rewrite E; [img_try (exists b1) | img_try (exists b2)]; tauto.
Qed.
End h.
End d.
