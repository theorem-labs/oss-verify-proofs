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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF64 YF3v YF3y YF54 YF5a.
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
Section e. Context {imgk : img}.
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
Local Abbreviation AR8 f := (f n cl v) (only parsing).
Local Abbreviation PBv := (AR8 (@YF54.PBv ly)).
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
Local Abbreviation PBW := (AR8 (@YF54.PBW ly)).
Local Abbreviation WIN := (AR8 (@YF54.WIN ly regs0)).
Local Abbreviation win_in_WIN := (AR8 (@YF54.win_in_WIN ly regs0)).
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
Local Abbreviation AR5 f := (f ly regs0 mem0) (only parsing).
Local Abbreviation Kv_range := ((AR8 (AR5 (@YF54.Kv_range))) Hcl Hv Hv2 DPOST).
Local Abbreviation ARc f := (AR3 f mem0 n v Hv LY IMG DPOST) (only parsing).
Local Abbreviation high_facts := (ARc (@YF54.high_facts _)).
Local Abbreviation blocks_facts := (@YF54.blocks_facts _ imgk ly LY IMG).
Local Abbreviation off_T := (ARc (@YF54.off_T _)).
Local Abbreviation off_C := (ARc (@YF54.off_C _)).
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
Local Abbreviation WIN1 := (AR8 (@YF54.WIN1 ly regs0)).
Local Abbreviation WIN1_WIN := ((AR8 (AR5 (@YF54.WIN1_WIN))) DPOST).
Local Abbreviation AR9 f := (f Hsp DPOST Nrange) (only parsing).
Local Abbreviation WIN_odd := (AR9 ((AR2 (@YF54.WIN_odd)) jb Hcl Hv Hcnt Hjb)).
Local Abbreviation WIN1_odd := (AR9 ((AR2 (@YF54.WIN1_odd)) jb Hcl Hv Hcnt Hjb)).
Local Abbreviation WSKEL := (@YF54.WSKEL).
Local Abbreviation WSKEL1 := (@YF54.WSKEL1).
Local Abbreviation win_sub := (@YF54.win_sub).
Local Abbreviation win_sub_sound := ((AR5 (@YF54.win_sub_sound)) n v Hv DPOST).
Local Abbreviation WSKEL_WIN := ((AR4 (AR0 ((AR3 (@YF54.WSKEL_WIN _)) mem0))) DPOST Nrange).
Local Abbreviation WSKEL1_WIN1 := ((AR4 (AR0 ((AR3 (@YF54.WSKEL1_WIN1 _)) mem0))) DPOST Nrange).
Local Abbreviation windows_WIN := ((AR4 (AR0 ((AR3 (@YF54.windows_WIN _)) mem0))) DPOST Nrange).
Local Abbreviation windows_WIN1 := ((AR4 (AR0 ((AR3 (@YF54.windows_WIN1 _)) mem0))) DPOST Nrange).
Local Abbreviation frame_WIN1 := ((AR4 (AR0 ((AR3 (@YF54.frame_WIN1 _)) mem0))) DPOST Nrange).
Local Abbreviation WIN_not_high := (AR9 (AR4 (AR2 (@YF54.WIN_not_high _ imgk)))).
Variables (mat0 : list word).
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 (0x53104 + D_2c4)) mem0 (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis U1 : tfx_unwind_spec.
Hypothesis SEED : st_ok tfxsegs E0 SS0K (restrict (w_H W) (mkst regs0 (w64 (0x53104 + D_2c4)) mem0 (seg_rom tfxsegs))).
Local Abbreviation all_disjoint_of_forall := (@YF54.all_disjoint_of_forall).
Local Abbreviation kept_of_frame := ((AR5 (@YF54.kept_of_frame imgk W)) n v DPOST).
Local Abbreviation SKEL_TAIL := (@YF54.SKEL_TAIL imgk).
Local Abbreviation stack_ivs := ((AR5 (@YF54.stack_ivs _)) n v Hv LY Hsp DPOST).
Local Abbreviation stack_ivs2 := ((AR5 (@YF54.stack_ivs2 _)) n v Hv LY Hsp DPOST).
Local Abbreviation DZONE_disj := (AR9 (AR4 (AR2 (@YF54.DZONE_disj _ imgk)))).
Local Abbreviation RFACTS := (AR8 (AR3 (@YF54.RFACTS))).
Local Abbreviation zone_lit := (AR9 (AR4 (AR2 (@YF54.zone_lit _ imgk)))).
Local Abbreviation zone_T := (AR9 (AR4 (AR2 (@YF54.zone_T _ imgk)))).
Local Abbreviation zone_C := (AR9 (AR4 (AR2 (@YF54.zone_C _ imgk)))).
Local Abbreviation zone_K := (AR9 (AR4 (AR2 (@YF54.zone_K _ imgk)))).
Local Abbreviation zone_SH := (AR9 (AR4 (AR2 (@YF54.zone_SH _ imgk)))).
Local Abbreviation tail_ext_ok := (AR9 (AR4 (AR0 ((AR3 (@YF54.tail_ext_ok _)) mem0)))).
Local Abbreviation AR6 f := (f _ imgk W) (only parsing).
Local Abbreviation at_ST := (AR0 ((AR5 (AR6 (@YF54.at_ST))) md0)).
Local Abbreviation at_ST2 := ((AR0 ((AR5 (AR6 (@YF54.at_ST2))) md0)) DPOST).
Local Abbreviation at_S2 := ((AR0 ((AR5 (AR6 (@YF54.at_S2))) md0)) DPOST).
Local Abbreviation at_RET := ((AR5 (AR6 (@YF54.at_RET))) md0 n cl cnt v jb DPOST).
Ltac frame_acc HE :=
match goal with
| MEQ : (forall x : word, ~ WIN1 ?odd (bv_unsigned x) -> ?m1 x = ?mb x), HFx : frame_of ?E ?rs ?m1 ?m2 |- _ =>
let MEQ' := fresh "MEQ" in
assert (MEQ' : forall x : word, ~ WIN1 odd (bv_unsigned x) -> m2 x = mb x)
by (img_try (intros x Hx; transitivity (m1 x); [img_try (img_exact (frame_WIN1 odd E rs m1 m2 HE ltac:((img_case; vm_compute); img_refl) HFx x Hx)) | img_try (img_exact (MEQ x Hx))]));
clear MEQ HFx; rename MEQ' into MEQ
end.
Local Abbreviation memset_stretch := ((AR9 ((AR5 (AR6 (@YF54.memset_stretch))) md0 n cl cnt v jb Hcl Hv Hcnt Hjb)) mat0).
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
Local Abbreviation ARb f := (AR8 f DPOST Nrange l off Hcl_class) (only parsing).
Local Abbreviation cl_range := (ARb (AR5 (@YF5a.cl_range))).
Local Abbreviation cls_geom := (ARb (AR5 (@YF5a.cls_geom))).
Local Abbreviation cls_wf := ((AR8 (AR5 (AR6 (@YF5a.cls_wf)))) DPOST Nrange B S l off HARm Hcl_class).
Local Abbreviation AR1 f := (f DPOST Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def) (only parsing).
Local Abbreviation off_facts := (AR1 ((AR2 (AR6 (@YF5a.off_facts))) Hv2)).
Local Abbreviation Kv_base := ((ARb (AR5 (@YF5a.Kv_base))) Hoff_def).
Local Abbreviation AR7 f := (AR2 f csz Hv2 LY) (only parsing).
Local Abbreviation Kv_geom := ((AR1 (AR7 (AR6 (@YF5a.Kv_geom)))) Hcsz_def).
Local Abbreviation Hcl' := (ARb (AR5 (@YF5a.Hcl'))).
Local Abbreviation cl_k0 := ((AR8 (AR5 (@YF5a.cl_k0))) DPOST Nrange Hcl_def l off).
Local Abbreviation ARa f := (AR2 f Hv2 Hsp) (only parsing).
Local Abbreviation Hcnt' := (AR1 (ARa (AR6 (@YF5a.Hcnt')))).
Local Abbreviation Hv' := (AR1 ((AR2 (AR6 (@YF5a.Hv'))) Hv2)).
Local Abbreviation cached_vs_chunk := ((AR1 ((AR7 (AR6 (@YF5a.cached_vs_chunk))) Hsp)) Hcsz_def).
Local Abbreviation find_chunk_at_none := (AR1 (ARa (AR6 (@YF5a.find_chunk_at_none)))).
Local Abbreviation shadow250 := ((AR1 ((AR7 (AR6 (@YF5a.shadow250))) Hsp)) Hcsz_def).
Local Abbreviation shadow_present := ((AR1 ((AR7 (AR6 (@YF5a.shadow_present))) IMG Hsp)) Hcsz_def).
Local Abbreviation vis_present := (AR1 (ARa (AR6 (@YF5a.vis_present)))).
Local Abbreviation KPRES := ((AR1 ((AR7 (AR6 (@YF5a.KPRES))) Hsp)) Hcsz_def).
Local Abbreviation SKPRES := ((AR1 ((AR7 (AR6 (@YF5a.SKPRES))) IMG Hsp)) Hcsz_def).
Local Abbreviation PB250 := ((AR1 ((AR7 (AR6 (@YF5a.PB250))) IMG Hsp)) Hcsz_def).
Local Abbreviation in_thread_junk := (AR1 (ARa (AR6 (@YF5a.in_thread_junk)))).
Local Abbreviation junk_word := (AR1 ((AR2 (AR6 (@YF5a.junk_word))) Hv2 LY IMG Hsp)).
Local Abbreviation junk_byte := ((AR1 ((AR7 (AR6 (@YF5a.junk_byte))) Hsp)) Hcsz_def).
Local Abbreviation junk_values := ((AR1 ((AR7 (AR6 (@YF5a.junk_values))) IMG Hsp)) Hcsz_def).
Local Abbreviation cell_sym := ((AR9 ((AR2 (AR6 (@YF5a.cell_sym))) Hv2)) B S l off TS HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation cell_lit := ((AR9 ((AR2 (AR6 (@YF5a.cell_lit))) Hv2)) B S l off TS HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation cell_state := (AR1 (ARa (AR6 (@YF5a.cell_state)))).
Local Abbreviation In_acells_cache := (AR1 (ARa (AR6 (@YF5a.In_acells_cache)))).
Local Abbreviation In_combine_seq_last := (AR1 (ARa (AR6 (@YF5a.In_combine_seq_last)))).
Local Abbreviation cache_vals := ((AR1 ((AR2 (AR6 (@YF5a.cache_vals))) csz Hv2 Hsp)) Hcsz_def).
Local Abbreviation unwinding_val := (AR1 (ARa (AR6 (@YF5a.unwinding_val)))).
Local Abbreviation sk_val := ((AR1 ((AR7 (AR6 (@YF5a.sk_val))) IMG Hsp)) Hcsz_def).
Local Abbreviation val_mem_mod8 := (AR1 (ARa (AR6 (@YF5a.val_mem_mod8)))).
Local Abbreviation chunk_lit := (AR1 ((AR0 (AR5 (AR6 (@YF5a.chunk_lit)))) Hv2 Hsp)).
Local Abbreviation chunk_lit_at := (AR1 ((AR0 (AR5 (AR6 (@YF5a.chunk_lit_at)))) Hv2 Hsp)).
Local Abbreviation chunk_atom := (AR1 ((AR0 (AR5 (AR6 (@YF5a.chunk_atom)))) Hv2 Hsp)).
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
Let m0 := mrestrict (w_H W) mem0.
Local Ltac reg_intro := unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
Local Ltac lit_region :=
reg_intro; split; [img_try (zlia)|]; split; [img_try (zlia)|]; split; [img_try (intros o Ho; zlia)|];
repeat (img_apply Forall_cons; [img_try (img_apply chunk_lit; [img_apply cell_lit; (img_case; vm_compute); img_refl | cbn; zlia | cbn; zlia]) |]); img_apply Forall_nil.
Lemma REG0_ok : Forall (region_ok tfxsegs E0 m0) REG0K.
Proof.
pose proof high_facts as (hf1 & hf2 & hf3 & hf4 & hf5 & hf6 & hf7 & hf8 & hf9). pose proof derived_ranges as DR. pose proof Kv_range as HKR.
pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). destruct Hsp as (S1 & S2 & S3 & S4).
pose proof cache_vals as (CV1 & CV2 & CV3). pose proof off_facts as (O1 & O2 & O3 & O4 & O5 & NI & C1 & C2 & PM). pose proof cls_geom as (K1 & K2 & K3 & K4 & K5 & K6).
ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, t_cache, t_unwinding in hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, DR, HKR, T2, T4, T7.
unfold REG0K, lit1, lit4, lit8, lits8, atom8, CTZ_TABLE. cbn [map combine seq length Z.of_nat Pos.of_succ_nat Pos.succ fst snd Z.mul Z.add Pos.mul Pos.add].
unfold aSB, aSHB, aC, aT, aTOP, aJ0, aJ1, aJ2, aJ3, aJ4, aCNT, aCSZ, aV, aJB, aSK, aP, aPV, aK, aSSLOT.
img_apply Forall_cons.
{   img_apply (region_ok_stack tfxsegs E0 m0 2 sp0 (- ASTACK)); [img_try (rewrite E2; img_refl) | img_try (unfold ASTACK; zlia) | img_try (zlia) |].
intros a Ha. img_apply apresent_writable_off; [img_try (off_by ltac:(unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END, ASTACK in *; zlia)) | img_try (img_apply Hpres0; img_exact Ha)]. }
do 8 (img_apply Forall_cons; [img_try (lit_region)|]).
img_apply Forall_cons. {   reg_intro. split; [img_try (zlia)|]. split; [img_try (zlia)|]. split; [img_try (intros o Ho; zlia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply (chunk_atom 0 _ 8 34%nat 0 SB); [img_try (rewrite EaSB; unfold w64; f_equal; zlia) | img_try (unfold SB; zlia) | | img_try (unfold SB; cbn; zlia) | img_try (cbn; zlia)].
rewrite Z.add_0_l. replace (682872 + D_10c0) with (aeval B ly (AInst o_space)) by (img_try (cbn; rewrite (ts_inst B TS); img_refl)).
replace SB with (aeval B ly (ASp 0)) by (img_try (cbn; unfold SB; zlia)). img_apply cell_sym. img_case; vm_compute. all: img_refl. }
do 14 (img_apply Forall_cons; [img_try (lit_region)|]).
img_apply Forall_cons. {   reg_intro. split; [img_try (zlia)|]. split; [img_try (zlia)|]. split; [img_try (intros o Ho; zlia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply (chunk_atom 0 _ 8 47%nat 0 SHBv); [img_refl | img_try (unfold SHBv; zlia) | | img_try (unfold SHBv; cbn; zlia) | img_try (cbn; zlia)].
rewrite Z.add_0_l. img_apply cell_lit. img_case; vm_compute. all: img_refl. }
do 7 (img_apply Forall_cons; [img_try (lit_region)|]).
img_apply Forall_cons. {   reg_intro. split; [img_try (zlia)|]. split; [img_try (zlia)|]. split; [img_try (intros o Ho; zlia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply chunk_lit; [| img_try (cbn; zlia) | img_try (cbn; zlia)]. pose proof (cell_lit (0x5dd160 + D_10c0) 8 0 ltac:(img_try ((img_case; vm_compute); img_refl))) as H8.
intros k Hk. rewrite (H8 k ltac:(img_try (zlia))). rewrite !le_byte_zero. img_refl. }
img_apply Forall_cons; [img_try (lit_region)|].
img_apply Forall_cons. {   reg_intro. unfold TFX_TP. split; [img_try (zlia)|]. split; [img_try (zlia)|]. split; [img_try (intros o Ho; zlia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply chunk_lit; [| img_try (unfold TFX_TSD; cbn; zlia) | img_try (cbn; zlia)].
replace ((6148432 + D_10c0) - 88) with (aeval B ly (ATp (-88))) by (img_try (cbn; rewrite (ts_tp B TS); img_refl)).
replace TFX_TSD with (aeval B ly (ATsd 0)) by (img_try (cbn; rewrite HTSD; unfold TFX_TSD; zlia)). img_apply cell_sym. img_case; vm_compute. all: img_refl. }
img_apply Forall_cons. {   reg_intro. unfold TFX_TSD. split; [img_try (zlia)|]. split; [img_try (zlia)|]. split; [img_try (intros o Ho; zlia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply (chunk_atom 0 _ 8 33%nat 0 (ly_C ly)); [img_try (rewrite EaC; unfold w64; f_equal; zlia) | img_try (zlia) | | img_try (cbn; zlia) | img_try (cbn; zlia)].
rewrite Z.add_0_l. replace (6284536 + D_10c0) with (aeval B ly (ATsd 0)) by (img_try (cbn; rewrite HTSD; img_refl)).
replace (ly_C ly) with (aeval B ly (AC 0)) by (img_try (cbn; zlia)). img_apply cell_sym. img_case; vm_compute. all: img_refl. }
img_apply Forall_cons. {   reg_intro. rewrite EaC. unfold w64. rewrite unsigned_lit_small by zlia.
split; [img_try (zlia)|]. split; [img_try (zlia)|]. split; [img_try (intros o Ho; zlia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_nil])].
- img_apply chunk_lit_at; [| img_try (cbn; zlia) | img_try (cbn; zlia)]. replace (ly_C ly + 8) with (aeval B ly (AC 8)) by img_refl. img_apply (cell_sym (AC 8) 4 (ANum 0)). img_case; vm_compute. all: img_refl.
- img_apply (chunk_atom _ _ 8 32%nat 0 T); [img_try (rewrite EaT; unfold w64; f_equal; zlia) | img_try (zlia) | | img_try (cbn; zlia) | img_try (cbn; zlia)].
replace (ly_C ly + 152) with (aeval B ly (AC 152)) by img_refl. replace T with (aeval B ly (AT 0)) by (img_try (cbn; unfold T; zlia)).
img_apply cell_sym. img_case; vm_compute. all: img_refl. }
img_apply Forall_cons. {   reg_intro. rewrite EaT. unfold w64. rewrite unsigned_lit_small by zlia.
split; [img_try (zlia)|]. split; [img_try (zlia)|]. split; [img_try (intros o Ho; zlia)|].
img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_cons; [|img_apply Forall_cons; [|img_apply Forall_nil]]])].
- img_apply (chunk_atom _ _ 8 33%nat 0 (ly_C ly)); [img_try (rewrite EaC; unfold w64; f_equal; zlia) | img_try (zlia) | | img_try (cbn; zlia) | img_try (cbn; zlia)].
replace (ly_T ly + 0) with (aeval B ly (AT 0)) by (img_try (cbn; zlia)). replace (ly_C ly) with (aeval B ly (AC 0)) by (img_try (cbn; zlia)). img_apply cell_sym. img_case; vm_compute. all: img_refl.
- img_apply (chunk_atom _ _ 8 35%nat 0 (ly_top ly)); [img_try (rewrite EaTOP; unfold w64; f_equal; zlia) | img_try (zlia) | | img_try (cbn; zlia) | img_try (cbn; zlia)].
replace (ly_T ly + 8) with (aeval B ly (AT 8)) by (img_try (cbn; zlia)). replace (ly_top ly) with (aeval B ly (ATop 0)) by (img_try (cbn; zlia)). img_apply cell_sym. img_case; vm_compute. all: img_refl.
- img_apply (chunk_atom _ _ 8 35%nat (- kStackSpan) (ly_top ly - kStackSpan)); [img_try (rewrite EaTOP; unfold w64; f_equal; zlia) | img_try (unfold kStackSpan; zlia) | | img_try (unfold kStackSpan; cbn; zlia) | img_try (cbn; zlia)].
replace (ly_T ly + 16) with (aeval B ly (AT 16)) by (img_try (cbn; zlia)). replace (ly_top ly - kStackSpan) with (aeval B ly (ATop (- kStackSpan))) by (img_try (cbn; zlia)).
img_apply cell_sym. img_case; vm_compute. all: img_refl.
- img_apply chunk_lit_at; [| img_try (cbn; zlia) | img_try (cbn; zlia)]. replace (ly_T ly + 40) with (aeval B ly (AT 40)) by (img_try (cbn; zlia)). img_apply (cell_sym (AT 40) 1 (ANum 0)). img_case; vm_compute. all: img_refl. }
img_apply Forall_cons. {   reg_intro. rewrite EaT. unfold w64. rewrite unsigned_lit_small by zlia.
split; [img_try (zlia)|]. split; [img_try (zlia)|]. split.
{ intros o Ho. img_apply apresent_writable_off; [img_try (off_by ltac:(unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; zlia)) |].
img_apply (vis_present (AT t_cache_stats) (t_stats - t_cache_stats)); [img_try (left; img_apply in_thread_junk; right; left; img_refl) | img_try (cbn; unfold t_cache_stats, t_stats, T in *; zlia) | img_try (off_by ltac:(unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; zlia)) ]. }
img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply (chunk_atom _ _ 8 37%nat 0 (j0 mod 2 ^ 64)); [img_try (rewrite Z.sub_0_r; img_apply Z_to_bv64_eq_mod; rewrite Z.mod_mod by zlia; img_refl)
| img_try (pose proof (Z.mod_pos_bound j0 (2 ^ 64)); zlia) | img_try (img_apply val_mem_mod8; img_exact Hj0) | img_try (cbn; pose proof (Z.mod_pos_bound j0 (2 ^ 64)); zlia) | img_try (cbn; zlia)]. }
img_apply Forall_cons. {   reg_intro. rewrite EaT. unfold w64. rewrite unsigned_lit_small by zlia. unfold t_unwinding.
split; [img_try (zlia)|]. split; [img_try (zlia)|]. split.
{ intros o Ho. img_apply apresent_writable_off; [img_try (off_by ltac:(unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; zlia)) |]. replace (ly_T ly + o) with (ly_T ly + 3168) by zlia.
pose proof unwinding_val as U.
eapply mbyte_off_apresent; [img_try (off_by ltac:(unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; zlia)) |]. unfold T, t_unwinding in U. rewrite <- (Z.add_0_r (ly_T ly + 3168)). img_exact (U 0%nat ltac:(img_try (zlia))). }
img_apply Forall_cons; [|img_try (img_apply Forall_nil)]. img_apply chunk_lit_at; [| img_try (cbn; zlia) | img_try (cbn; zlia)]. img_exact unwinding_val. }
img_apply Forall_cons. {   reg_intro. rewrite EaT. unfold w64. rewrite unsigned_lit_small by zlia.
split; [img_try (zlia)|]. split; [img_try (zlia)|]. split.
{ intros o Ho. img_apply apresent_writable_off; [img_try (off_by ltac:(unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; zlia)) |].
img_apply (vis_present (AT t_stats) (t_unwinding - t_stats)); [img_try (left; img_apply in_thread_junk; right; right; left; img_refl) | img_try (cbn; unfold t_stats, t_unwinding, T in *; zlia) | img_try (off_by ltac:(unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; zlia)) ]. }
img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_cons; [|img_apply Forall_nil]])].
- img_apply (chunk_atom _ _ 8 49%nat 0 (j1 mod 2 ^ 64)); [img_try (rewrite Z.sub_0_r; img_apply Z_to_bv64_eq_mod; rewrite Z.mod_mod by zlia; img_refl)
| img_try (pose proof (Z.mod_pos_bound j1 (2 ^ 64)); zlia) | img_try (img_apply val_mem_mod8; img_exact Hj1) | img_try (cbn; pose proof (Z.mod_pos_bound j1 (2 ^ 64)); zlia) | img_try (cbn; zlia)].
- img_apply (chunk_atom _ _ 8 50%nat 0 (j2 mod 2 ^ 64)); [img_try (rewrite Z.sub_0_r; img_apply Z_to_bv64_eq_mod; rewrite Z.mod_mod by zlia; img_refl)
| img_try (pose proof (Z.mod_pos_bound j2 (2 ^ 64)); zlia) | img_try (img_apply val_mem_mod8; img_exact Hj2) | img_try (cbn; pose proof (Z.mod_pos_bound j2 (2 ^ 64)); zlia) | img_try (cbn; zlia)].
- img_apply (chunk_atom _ _ 8 51%nat 0 (j3 mod 2 ^ 64)); [img_try (rewrite Z.sub_0_r; img_apply Z_to_bv64_eq_mod; rewrite Z.mod_mod by zlia; img_refl)
| img_try (pose proof (Z.mod_pos_bound j3 (2 ^ 64)); zlia) | img_try (img_apply val_mem_mod8; img_exact Hj3) | img_try (cbn; pose proof (Z.mod_pos_bound j3 (2 ^ 64)); zlia) | img_try (cbn; zlia)]. }
img_apply Forall_cons. {   reg_intro. rewrite EaSSLOT. unfold w64. rewrite unsigned_lit_small by zlia.
split; [img_try (zlia)|]. split; [img_try (zlia)|]. split.
{ intros o Ho. img_apply apresent_writable_off; [img_try (off_by ltac:(unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; zlia)) |].
img_apply (vis_present (AT t_stats) (t_unwinding - t_stats)); [img_try (left; img_apply in_thread_junk; right; right; left; img_refl) | img_try (cbn; unfold SSLOTv, t_stats, t_unwinding, T in *; zlia) | img_try (off_by ltac:(unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; zlia)) ]. }
img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply (chunk_atom _ _ 8 53%nat 0 (j4 mod 2 ^ 64)); [img_try (rewrite Z.sub_0_r; img_apply Z_to_bv64_eq_mod; rewrite Z.mod_mod by zlia; img_refl)
| img_try (pose proof (Z.mod_pos_bound j4 (2 ^ 64)); zlia) | img_try (img_apply val_mem_mod8; rewrite Z.add_0_r; img_exact Hj4) | img_try (cbn; pose proof (Z.mod_pos_bound j4 (2 ^ 64)); zlia) | img_try (cbn; zlia)]. }
img_apply Forall_cons. {   reg_intro. rewrite EaP. unfold w64. rewrite unsigned_lit_small by zlia.
split; [img_try (zlia)|]. split; [img_try (zlia)|]. split.
{ intros o Ho. img_apply apresent_writable_off; [img_try (off_by ltac:(unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; zlia)) |]. destruct (Z.eq_dec o 0) as [->|]; [|img_try (destruct (Z.eq_dec o 1) as [->|]; [|destruct (Z.eq_dec o 2) as [->|]; [|replace o with 3 by zlia]])];
[ img_try (eapply mbyte_off_apresent; [off_by ltac:(unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; zlia) | rewrite <- (eq_refl : Pv + Z.of_nat 0 = Pv + 0); img_exact (CV1 0%nat ltac:(zlia))])
| img_try (eapply mbyte_off_apresent; [off_by ltac:(unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; zlia) | rewrite <- (eq_refl : Pv + Z.of_nat 1 = Pv + 1); img_exact (CV1 1%nat ltac:(zlia))])
| img_try (eapply mbyte_off_apresent; [off_by ltac:(unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; zlia) | rewrite <- (eq_refl : Pv + Z.of_nat 2 = Pv + 2); img_exact (CV1 2%nat ltac:(zlia))])
| img_try (eapply mbyte_off_apresent; [off_by ltac:(unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; zlia) | rewrite <- (eq_refl : Pv + Z.of_nat 3 = Pv + 3); img_exact (CV1 3%nat ltac:(zlia))]) ]. }
img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply (chunk_atom _ _ 4 41%nat 0 cnt); [img_try (rewrite Z.sub_0_r; img_refl) | img_try (zlia) | img_try (rewrite Z.add_0_r; img_exact CV1) | img_try (cbn; zlia) | img_try (cbn; zlia)]. }
img_apply Forall_cons. {   reg_intro. rewrite EaP. unfold w64. rewrite unsigned_lit_small by zlia.
split; [img_try (zlia)|]. split; [img_try (zlia)|]. split; [img_try (intros o Ho; zlia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply (chunk_atom _ _ 8 43%nat 0 (csz mod 2 ^ 64)); [img_try (rewrite Z.sub_0_r; img_apply Z_to_bv64_eq_mod; rewrite Z.mod_mod by zlia; img_refl)
| img_try (pose proof (Z.mod_pos_bound csz (2 ^ 64)); zlia) | img_try (img_apply val_mem_mod8; img_exact CV2) | img_try (cbn; pose proof (Z.mod_pos_bound csz (2 ^ 64)); zlia) | img_try (cbn; zlia)]. }
img_apply Forall_cons. {   reg_intro. rewrite EaPV. unfold w64. rewrite unsigned_lit_small by zlia.
split; [img_try (zlia)|]. split; [img_try (zlia)|]. split; [img_try (intros o Ho; zlia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply (chunk_atom _ _ 4 42%nat 0 v); [img_try (rewrite Z.sub_0_r; img_refl) | img_try (zlia) | img_try (rewrite Z.add_0_r; img_exact CV3) | img_try (cbn; zlia) | img_try (cbn; zlia)]. }
img_apply Forall_cons. {   reg_intro. rewrite EaK. unfold w64. rewrite unsigned_lit_small by zlia.
split; [img_try (zlia)|]. split; [img_try (zlia)|]. split.
{ intros o Ho. img_apply apresent_writable_off; [img_try (off_by ltac:(unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; zlia)) |]. img_apply KPRES. zlia. }
img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply (chunk_atom _ _ 1 46%nat 0 jb); [img_try (rewrite Z.sub_0_r; img_refl) | img_try (zlia) | | img_try (cbn; zlia) | img_try (cbn; zlia)].
replace (Kv + 1) with (Kv + RZ - 15) by zlia. img_exact Hjb_def. }
img_apply Forall_cons; [|img_try (img_apply Forall_nil)]. {   reg_intro. rewrite EaSK. unfold w64. rewrite unsigned_lit_small by zlia.
split; [img_try (zlia)|]. split; [img_try (zlia)|]. split; [img_try (intros o Ho; zlia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply chunk_lit_at; [| img_try (cbn; zlia) | img_try (cbn; zlia)]. rewrite Z.add_0_r. img_exact sk_val. }
Qed.
End e.
End d.
