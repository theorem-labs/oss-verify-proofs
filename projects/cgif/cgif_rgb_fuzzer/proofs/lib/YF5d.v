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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF64 YF3v YF3y YF54 YF40 YF5a YF5b YF5c YF59.
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
Section a0. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
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
Section b0. Context {imgk : img}.
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
Local Abbreviation ARb f := (f n cl v) (only parsing).
Local Abbreviation PBv := (ARb (@YF54.PBv ly)).
Local Abbreviation Uv := (@YF54.Uv ly cl v).
Local Abbreviation SUv := (@YF54.SUv ly cl v).
Local Abbreviation FILv := (@YF54.FILv n).
Local Abbreviation NDv := (@YF54.NDv n).
Local Abbreviation AR5 f := (f imgk ly regs0) (only parsing).
Local Abbreviation tr := ((AR5 (@YF54.tr)) ch).
Local Abbreviation AR0 f := (f n ch cl cnt v csz j0 jb j1 j2 j3 j4) (only parsing).
Local Abbreviation XW := (AR0 (AR5 (@YF54.XW))).
Local Abbreviation E0 := (AR0 (AR5 (@YF54.E0))).
Local Abbreviation EaT := (AR0 (AR5 (@YF54.EaT))).
Local Abbreviation EaC := (AR0 (AR5 (@YF54.EaC))).
Local Abbreviation EaSB := (AR0 (AR5 (@YF54.EaSB))).
Local Abbreviation EaTOP := (AR0 (AR5 (@YF54.EaTOP))).
Local Abbreviation Er := (AR0 (AR5 (@YF54.Er))).
Local Abbreviation E2 := (AR0 (AR5 (@YF54.E2))).
Local Abbreviation E1 := (AR0 (AR5 (@YF54.E1))).
Local Abbreviation E8 := (AR0 (AR5 (@YF54.E8))).
Local Abbreviation E10 := (AR0 (AR5 (@YF54.E10))).
Local Abbreviation E4 := (AR0 (AR5 (@YF54.E4))).
Local Abbreviation EaP := (AR0 (AR5 (@YF54.EaP))).
Local Abbreviation EaR8 := (AR0 (AR5 (@YF54.EaR8))).
Local Abbreviation EaK := (AR0 (AR5 (@YF54.EaK))).
Local Abbreviation EaSK := (AR0 (AR5 (@YF54.EaSK))).
Local Abbreviation EaSSLOT := (AR0 (AR5 (@YF54.EaSSLOT))).
Local Abbreviation EaPB := (AR0 (AR5 (@YF54.EaPB))).
Local Abbreviation EaPV := (AR0 (AR5 (@YF54.EaPV))).
Local Abbreviation EaRZ := (AR0 (AR5 (@YF54.EaRZ))).
Local Abbreviation EaU := (AR0 (AR5 (@YF54.EaU))).
Local Abbreviation EaSU := (AR0 (AR5 (@YF54.EaSU))).
Local Abbreviation EaFIL := (AR0 (AR5 (@YF54.EaFIL))).
Local Abbreviation EaNP := (AR0 (AR5 (@YF54.EaNP))).
Local Abbreviation EaND := (AR0 (AR5 (@YF54.EaND))).
Local Abbreviation WINT := (@YF54.WINT ly cl).
Local Abbreviation PBW := (ARb (@YF54.PBW ly)).
Local Abbreviation WIN := (ARb (@YF54.WIN ly regs0)).
Local Abbreviation win_in_WIN := (ARb (@YF54.win_in_WIN ly regs0)).
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
Local Abbreviation AR3 f := (f ly regs0 mem0) (only parsing).
Local Abbreviation tr_length := ((AR3 (@YF54.tr_length imgk)) n ch v DPOST).
Local Abbreviation Kv_range := ((ARb (AR3 (@YF54.Kv_range))) Hcl Hv Hv2 DPOST).
Local Abbreviation ARc f := (AR3 f n v Hv) (only parsing).
Local Abbreviation high_facts := ((ARc (@YF54.high_facts _ imgk)) LY IMG DPOST).
Local Abbreviation blocks_facts := (@YF54.blocks_facts _ imgk ly LY IMG).
Local Abbreviation off_T := ((ARc (@YF54.off_T _ imgk)) LY IMG DPOST).
Local Abbreviation off_C := ((ARc (@YF54.off_C _ imgk)) LY IMG DPOST).
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
Local Abbreviation CLk_E := ((AR0 (AR3 (@YF54.CLk_E imgk))) DPOST Nrange Hcl_def).
Local Abbreviation WIN1 := (ARb (@YF54.WIN1 ly regs0)).
Local Abbreviation WIN1_WIN := ((ARb (AR3 (@YF54.WIN1_WIN))) DPOST).
Local Abbreviation AR7 f := (f Hsp DPOST Nrange) (only parsing).
Local Abbreviation ARf f := (f jb Hcl Hv Hcnt Hjb) (only parsing).
Local Abbreviation WIN_odd := (AR7 (ARf (AR2 (@YF54.WIN_odd)))).
Local Abbreviation WIN1_odd := (AR7 (ARf (AR2 (@YF54.WIN1_odd)))).
Local Abbreviation WSKEL := (@YF54.WSKEL).
Local Abbreviation WSKEL1 := (@YF54.WSKEL1).
Local Abbreviation win_sub := (@YF54.win_sub).
Local Abbreviation win_sub_sound := ((ARc (@YF54.win_sub_sound)) DPOST).
Local Abbreviation WSKEL_WIN := ((AR4 (AR0 (AR3 (@YF54.WSKEL_WIN _ imgk)))) DPOST Nrange).
Local Abbreviation WSKEL1_WIN1 := ((AR4 (AR0 (AR3 (@YF54.WSKEL1_WIN1 _ imgk)))) DPOST Nrange).
Local Abbreviation windows_WIN := ((AR4 (AR0 (AR3 (@YF54.windows_WIN _ imgk)))) DPOST Nrange).
Local Abbreviation windows_WIN1 := ((AR4 (AR0 (AR3 (@YF54.windows_WIN1 _ imgk)))) DPOST Nrange).
Local Abbreviation frame_WIN1 := ((AR4 (AR0 (AR3 (@YF54.frame_WIN1 _ imgk)))) DPOST Nrange).
Local Abbreviation WIN_not_high := (AR7 (AR4 (AR2 (@YF54.WIN_not_high _ imgk)))).
Variables (mat0 : list word).
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 (0x53104 + D_2c4)) mem0 (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis U1 : tfx_unwind_spec.
Hypothesis SEED : st_ok tfxsegs E0 SS0K (restrict (w_H W) (mkst regs0 (w64 (0x53104 + D_2c4)) mem0 (seg_rom tfxsegs))).
Local Abbreviation all_disjoint_of_forall := (@YF54.all_disjoint_of_forall).
Local Abbreviation kept_of_frame := ((AR3 (@YF54.kept_of_frame imgk W)) n v DPOST).
Local Abbreviation SKEL_TAIL := (@YF54.SKEL_TAIL imgk).
Local Abbreviation stack_ivs := ((ARc (@YF54.stack_ivs _)) LY Hsp DPOST).
Local Abbreviation stack_ivs2 := ((ARc (@YF54.stack_ivs2 _)) LY Hsp DPOST).
Local Abbreviation DZONE_disj := (AR7 (AR4 (AR2 (@YF54.DZONE_disj _ imgk)))).
Local Abbreviation RFACTS := (ARb (AR5 (@YF54.RFACTS))).
Local Abbreviation zone_lit := (AR7 (AR4 (AR2 (@YF54.zone_lit _ imgk)))).
Local Abbreviation zone_T := (AR7 (AR4 (AR2 (@YF54.zone_T _ imgk)))).
Local Abbreviation zone_C := (AR7 (AR4 (AR2 (@YF54.zone_C _ imgk)))).
Local Abbreviation zone_K := (AR7 (AR4 (AR2 (@YF54.zone_K _ imgk)))).
Local Abbreviation zone_SH := (AR7 (AR4 (AR2 (@YF54.zone_SH _ imgk)))).
Local Abbreviation tail_ext_ok := (AR7 (AR4 (AR0 (AR3 (@YF54.tail_ext_ok _ imgk))))).
Local Abbreviation AR6 f := (f _ imgk W) (only parsing).
Local Abbreviation at_ST := (AR0 ((AR3 (AR6 (@YF54.at_ST))) md0)).
Local Abbreviation at_ST2 := ((AR0 ((AR3 (AR6 (@YF54.at_ST2))) md0)) DPOST).
Local Abbreviation at_S2 := ((AR0 ((AR3 (AR6 (@YF54.at_S2))) md0)) DPOST).
Local Abbreviation at_RET := ((AR3 (AR6 (@YF54.at_RET))) md0 n cl cnt v jb DPOST).
Ltac frame_acc HE :=
match goal with
| MEQ : (forall x : word, ~ WIN1 ?odd (bv_unsigned x) -> ?m1 x = ?mb x), HFx : frame_of ?E ?rs ?m1 ?m2 |- _ =>
let MEQ' := fresh "MEQ" in
assert (MEQ' : forall x : word, ~ WIN1 odd (bv_unsigned x) -> m2 x = mb x)
by (img_try (intros x Hx; transitivity (m1 x); [img_try (img_exact (frame_WIN1 odd E rs m1 m2 HE ltac:((try img_inst; img_case; vm_compute); img_refl) HFx x Hx)) | img_try (img_exact (MEQ x Hx))]));
clear MEQ HFx; rename MEQ' into MEQ
end.
Local Abbreviation memset_stretch := ((AR7 (ARf ((AR3 (AR6 (@YF54.memset_stretch))) md0 n cl cnt v))) mat0).
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
Local Abbreviation ARh f := (ARb f DPOST Nrange l off Hcl_class) (only parsing).
Local Abbreviation cl_range := (ARh (AR3 (@YF5a.cl_range))).
Local Abbreviation cls_geom := (ARh (AR3 (@YF5a.cls_geom))).
Local Abbreviation AR9 f := (f B S l off) (only parsing).
Local Abbreviation cls_wf := ((AR9 ((ARb (AR3 (AR6 (@YF5a.cls_wf)))) DPOST Nrange)) HARm Hcl_class).
Local Abbreviation AR1 f := (f DPOST Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def) (only parsing).
Local Abbreviation off_facts := (AR1 ((AR2 (AR6 (@YF5a.off_facts))) Hv2)).
Local Abbreviation Kv_base := ((ARh (AR3 (@YF5a.Kv_base))) Hoff_def).
Local Abbreviation ARd f := (AR2 f csz Hv2 LY) (only parsing).
Local Abbreviation Kv_geom := ((AR1 (ARd (AR6 (@YF5a.Kv_geom)))) Hcsz_def).
Local Abbreviation Hcl' := (ARh (AR3 (@YF5a.Hcl'))).
Local Abbreviation cl_k0 := ((ARb (AR3 (@YF5a.cl_k0))) DPOST Nrange Hcl_def l off).
Local Abbreviation ARg f := (AR2 f Hv2 Hsp) (only parsing).
Local Abbreviation Hcnt' := (AR1 (ARg (AR6 (@YF5a.Hcnt')))).
Local Abbreviation Hv' := (AR1 ((AR2 (AR6 (@YF5a.Hv'))) Hv2)).
Local Abbreviation cached_vs_chunk := ((AR1 ((ARd (AR6 (@YF5a.cached_vs_chunk))) Hsp)) Hcsz_def).
Local Abbreviation find_chunk_at_none := (AR1 (ARg (AR6 (@YF5a.find_chunk_at_none)))).
Local Abbreviation shadow250 := ((AR1 ((ARd (AR6 (@YF5a.shadow250))) Hsp)) Hcsz_def).
Local Abbreviation shadow_present := ((AR1 ((ARd (AR6 (@YF5a.shadow_present))) IMG Hsp)) Hcsz_def).
Local Abbreviation vis_present := (AR1 (ARg (AR6 (@YF5a.vis_present)))).
Local Abbreviation KPRES := ((AR1 ((ARd (AR6 (@YF5a.KPRES))) Hsp)) Hcsz_def).
Local Abbreviation SKPRES := ((AR1 ((ARd (AR6 (@YF5a.SKPRES))) IMG Hsp)) Hcsz_def).
Local Abbreviation PB250 := ((AR1 ((ARd (AR6 (@YF5a.PB250))) IMG Hsp)) Hcsz_def).
Local Abbreviation in_thread_junk := (AR1 (ARg (AR6 (@YF5a.in_thread_junk)))).
Local Abbreviation junk_word := (AR1 ((AR2 (AR6 (@YF5a.junk_word))) Hv2 LY IMG Hsp)).
Local Abbreviation junk_byte := ((AR1 ((ARd (AR6 (@YF5a.junk_byte))) Hsp)) Hcsz_def).
Local Abbreviation junk_values := ((AR1 ((ARd (AR6 (@YF5a.junk_values))) IMG Hsp)) Hcsz_def).
Local Abbreviation ARe f := (f Hinited Hcache Hcl_class Hcnt_def Hoff_def) (only parsing).
Local Abbreviation cell_sym := (ARe ((AR9 (AR7 ((AR2 (AR6 (@YF5a.cell_sym))) Hv2))) TS HARm)).
Local Abbreviation cell_lit := (ARe ((AR9 (AR7 ((AR2 (AR6 (@YF5a.cell_lit))) Hv2))) TS HARm)).
Local Abbreviation cell_state := (AR1 (ARg (AR6 (@YF5a.cell_state)))).
Local Abbreviation In_acells_cache := (AR1 (ARg (AR6 (@YF5a.In_acells_cache)))).
Local Abbreviation In_combine_seq_last := (AR1 (ARg (AR6 (@YF5a.In_combine_seq_last)))).
Local Abbreviation cache_vals := ((AR1 ((AR2 (AR6 (@YF5a.cache_vals))) csz Hv2 Hsp)) Hcsz_def).
Local Abbreviation unwinding_val := (AR1 (ARg (AR6 (@YF5a.unwinding_val)))).
Local Abbreviation sk_val := ((AR1 ((ARd (AR6 (@YF5a.sk_val))) IMG Hsp)) Hcsz_def).
Local Abbreviation val_mem_mod8 := (AR1 (ARg (AR6 (@YF5a.val_mem_mod8)))).
Local Abbreviation chunk_lit := (AR1 ((AR0 (AR3 (AR6 (@YF5a.chunk_lit)))) Hv2 Hsp)).
Local Abbreviation chunk_lit_at := (AR1 ((AR0 (AR3 (AR6 (@YF5a.chunk_lit_at)))) Hv2 Hsp)).
Local Abbreviation chunk_atom := (AR1 ((AR0 (AR3 (AR6 (@YF5a.chunk_atom)))) Hv2 Hsp)).
Local Abbreviation ARa f := (f Hcl Hv Hcnt Hjb Hv2 LY IMG) (only parsing).
Local Abbreviation REG0_ok := ((ARe ((AR9 (AR7 (ARa (AR0 (AR3 (AR6 (@YF5b.REG0_ok))))))) TS HTSD HARm Hpres0)) Hcsz_def Hj0 Hj1 Hj2 Hj3 Hj4 Hjb_def).
Local Abbreviation Kv32 := ((ARb (AR3 (AR6 (@YF5c.Kv32)))) Hv2 LY DPOST l off).
Local Abbreviation PAIRS_ok := ((AR1 ((AR4 (AR0 (AR3 (AR6 (@YF5c.PAIRS_ok))))) Hsp)) Hcsz_def).
Local Abbreviation FACTS_ok := ((ARe ((AR9 ((AR7 ((ARa (AR0 (AR3 (AR6 (@YF5c.FACTS_ok))))) Hn)) Hcl_def)) HARm)) Hcsz_def).
Local Abbreviation SEED_ok := ((ARe ((AR9 ((AR7 ((ARa (AR0 (AR3 (AR6 (@YF5c.SEED_ok _))))) Hn Htp)) Hcl_def)) TS HTSD HARm Hpres0)) Hcsz_def Hj0 Hj1 Hj2 Hj3 Hj4 Hjb_def).
Local Abbreviation CZONE := (@YF59.CZONE imgk ly).
Local Abbreviation abs_cell_ok := (@YF59.abs_cell_ok imgk).
Local Abbreviation abs_cells_ok := (@YF59.abs_cells_ok imgk).
Local Abbreviation const_cells_zone := ((ARc (@YF59.const_cells_zone imgk)) DPOST B l off TS HTSD).
Local Abbreviation CZONE_untouched := ((AR7 (AR4 (AR2 (@YF59.CZONE_untouched _ imgk)))) l off).
Local Abbreviation cell_holds_agree := ((ARc (@YF59.cell_holds_agree)) DPOST B l off).
Local Abbreviation aview_agree := (@YF59.aview_agree imgk W).
Local Abbreviation const_kept := ((AR7 (AR4 (AR2 (AR6 (@YF59.const_kept))))) B l off TS HTSD).
Local Abbreviation depot_ids_bound := ((ARc (@YF59.depot_ids_bound imgk)) DPOST B l off TS).
Local Abbreviation depot_mem_ok_agree := ((ARc (@YF59.depot_mem_ok_agree imgk)) DPOST B l off TS).
Local Abbreviation depot_ok_ext := (@YF59.depot_ok_ext ly B).
Local Abbreviation depot_at0 := ((AR7 (ARf (AR2 (AR6 (@YF59.depot_at0))))) B S HARm).
Local Abbreviation DPOST3 := (@YF59.DPOST3 imgk W ly regs0 ch B S).
Local Abbreviation AR8 f := (f n ch cl cnt v) (only parsing).
Local Abbreviation D1W_ok := ((AR9 (AR7 (ARa ((AR8 (AR3 (AR6 (@YF59.D1W_ok _)))) jb)))) TS HTSD HARm Hgp).
Local Abbreviation st_popped := (@YF59.st_popped).
Local Abbreviation new_chunk := (@YF59.new_chunk).
Local Abbreviation st_final := (@YF59.st_final).
Local Abbreviation Kc_user := ((AR9 ((AR3 (@YF59.Kc_user imgk)) n ch cl v Hcl DPOST Nrange)) Hoff_def).
Local Abbreviation MPF := (AR9 ((AR5 (@YF59.MPF)) n ch cl)).
Local Abbreviation AR_final_stmt := (AR9 ((AR8 ((AR3 (AR6 (@YF59.AR_final_stmt _))) md0)) jb DPOST)).
Local Abbreviation WR_owned := ((ARe ((AR9 ((ARa ((AR8 (AR3 (AR6 (@YF59.WR_owned)))) csz jb)) Hsp DPOST HPB250 Nrange)) TS HARm)) Hcsz_def).
Local Abbreviation LEAF_ok := ((ARe ((AR9 ((ARa ((AR8 ((AR3 (AR6 (@YF59.LEAF_ok _))) md0)) csz jb)) Hsp DPOST HPB250 Nrange mat0)) TS HARm)) Hcsz_def).
Local Abbreviation Kc_fresh := (AR1 ((AR8 (AR3 (AR6 (@YF59.Kc_fresh)))) Hcl Hv Hv2)).
Local Abbreviation upd_chunk_fresh := (@YF59.upd_chunk_fresh n cl off).
Local Abbreviation SF_chunks := (AR1 ((AR8 (AR3 (AR6 (@YF59.SF_chunks)))) Hcl Hv Hv2)).
Local Abbreviation SF_same := ((AR5 (@YF59.SF_same)) n ch cl S l off).
Local Abbreviation SF_sec_extents := (AR1 ((AR8 (AR3 (AR6 (@YF59.SF_sec_extents)))) Hcl Hv Hv2)).
Local Abbreviation SF_sec_live := (AR1 ((AR8 (AR3 (AR6 (@YF59.SF_sec_live)))) Hcl Hv Hv2)).
Local Abbreviation SF_ledger := (AR1 ((AR8 (AR3 (AR6 (@YF59.SF_ledger)))) Hcl Hv Hv2)).
Local Abbreviation cell_holds_agree2 := (AR9 (AR7 (ARf (AR8 (AR3 (@YF59.cell_holds_agree2 imgk)))))).
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
Let Kc : chunk := new_chunk cl off n.
Let SF (z : Z) : astate := st_final S cl l off n tr z.
Lemma zrange_dec : forall lo hi a : Z, {lo <= a < hi} + {~ (lo <= a < hi)}.
Proof.
intros lo hi a. destruct (Z_le_dec lo a) as [H1|H1]; [img_try (destruct (Z_lt_dec a hi) as [H2|H2]; [left; img_exact (conj H1 H2) | right; intros [_ H]; img_exact (H2 H)]) | img_try (right; intros [H _]; img_exact (H1 H))].
Qed.
Lemma apresent_word : forall (Hh : word -> bool) mem a, apresent Hh mem a <-> apresent Hh mem (bv_unsigned (Z_to_bv 64 a)).
Proof. intros Hh mem a. unfold apresent. rewrite Z_to_bv_bv_unsigned. split; intros H; img_exact H. Qed.
Lemma val_mem_cell : forall mem e (w : nat) e',
val_mem tfxsegs (mrestrict (w_H W) mem) (aeval B ly e) w (aeval B ly e') -> cell_holds B ly (aview tfxsegs (w_H W) mem) (ACell e w (AV e')).
Proof.
intros mem e w e' HV k Hk. cbn [c_at c_val c_w]. unfold aview. rewrite (HV k Hk). cbn [option_map].
rewrite <- le_byte_eq. rewrite unsigned_lit_small8; [img_refl|]. unfold YG0h.le_byte. img_apply Z.mod_pos_bound. zlia.
Qed.
Lemma le_byte_1_0 : forall x, 0 <= x < 256 -> YP0g.le_byte x 1 0 = x.
Proof.
intros x Hx. unfold YP0g.le_byte. img_change (2 ^ (8 * Z.of_nat 1)) with 256. img_change (8 * Z.of_nat 0)%Z with 0.
rewrite Z.shiftr_0_r, Z.mod_mod by zlia. img_apply Z.mod_small. img_exact Hx.
Qed.
Lemma find_chunk_at_app1 : forall l1 l2 g k, find_chunk_at B ly l1 g = Some k -> find_chunk_at B ly (l1 ++ l2) g = Some k.
Proof.
induction l1 as [|k' t IH]; intros l2 g k H; [img_try (discriminate)|]. cbn [find_chunk_at app] in *.
destruct (andb _ _); [img_try (img_exact H) | img_try (img_exact (IH l2 g k H))].
Qed.
Lemma find_chunk_at_app2 : forall l1 l2 g, find_chunk_at B ly l1 g = None -> find_chunk_at B ly (l1 ++ l2) g = find_chunk_at B ly l2 g.
Proof.
induction l1 as [|k' t IH]; intros l2 g H; [img_refl|]. cbn [find_chunk_at app] in *.
destruct (andb _ _); [img_try (discriminate) | img_try (img_exact (IH l2 g H))].
Qed.
Lemma In_combine_seq_app : forall (l0 : list Z) (x : Z) s p, In p (combine (seq s (length l0)) l0) -> In p (combine (seq s (length l0 + 1)) (l0 ++ [x])).
Proof.
induction l0 as [|y t IH]; intros x s p H; [img_try (destruct H)|]. cbn [length combine seq app Nat.add] in *.
destruct H as [H|H]; [img_try (left; img_exact H) | img_try (right)]. img_apply IH. img_exact H.
Qed.
Lemma Kc_facts : ck_base B ly Kc = Kv /\ ck_rz Kc = RZ /\ ck_n Kc = NPv /\ ck_extent Kc = class_size cl /\ ck_state Kc = CAllocated /\
ck_beg Kc = PPrim (region_off cl + off) /\ aeval B ly (sptr_exp (ck_beg Kc)) = Kv.
Proof.
pose proof case0_sizes as (_ & RS & _ & _ & FP & _ & RQ).
unfold Kc, new_chunk, ck_base, ck_rz, ck_n, ck_extent. cbn [ck_beg ck_req ck_state]. rewrite RS, RQ, FP, <- Hcl_class, <- Kv_is_sptr.
repeat split; try img_refl. rewrite Kv_is_sptr. img_refl.
Qed.
Lemma NLOf : 1 <= NPv <= 48 /\ RZ = 16 /\ RZ = RZ / 8 * 8 /\ RZ / 8 = 2.
Proof. pose proof RZ_num as (X1 & X2 & X3 & X4 & X5). clear - X1 X2 X3 X4 X5. repeat split; zlia. Qed.
Section c0.
Variables (odd : bool) (z : Z) (regs' : bvmap 5 word) (mem' memD : word -> option byte) (mat : list word).
Let rd' : reader := aview tfxsegs (w_H W) mem'.
Let rdD : reader := aview tfxsegs (w_H W) memD.
Let m' := mrestrict (w_H W) mem'.
Hypothesis Hodd : odd = true <-> NPv mod 8 <> 0.
Hypothesis MP : MPF z.
Hypothesis HAR : AR tfxsegs B ly S W mem0 md0.
Hypothesis AOK : aok S (KDepot tr) z.
Hypothesis DEPD : depot_mem_ok B ly (depot_after z tr S) rdD.
Hypothesis CSTD : Forall (cell_holds B ly rdD) (as_const B ly).
Hypothesis PRD : forall a, DZONE a -> apresent (w_H W) mem0 a -> apresent (w_H W) memD a.
Hypothesis EQD : forall x : word, DZONE (bv_unsigned x) -> mem' x = memD x.
Hypothesis MEQF : forall x : word, ~ WIN odd (bv_unsigned x) -> ~ DZONE (bv_unsigned x) -> ~ (Kv + RZ <= bv_unsigned x < Kv + RZ + NPv) ->
~ (SUv <= bv_unsigned x < SUv + N8D / 8) -> mem' x = mem0 x.
Hypothesis PRS : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem' a.
Hypothesis PRW : forall a, WINT a \/ (Kv <= a < Kv + RZ + NPv) \/ PBW odd a -> apresent (w_H W) mem' a.
Hypotheses (V3 : val_mem tfxsegs m' (Kv + RZ - 16) 1 2) (V4 : val_mem tfxsegs m' (Kv + RZ - 15) 1 (hdr_byte1 jb))
(V5 : val_mem tfxsegs m' (Kv + RZ - 14) 2 0) (V6 : val_mem tfxsegs m' (Kv + RZ - 12) 4 NPv)
(V7 : val_mem tfxsegs m' Pv 4 (cnt - 1)) (V8 : val_mem tfxsegs m' (T + t_unwinding) 1 0)
(V9 : forall x : word, SUv <= bv_unsigned x < SUv + N8D / 8 -> mem' x = Some (Z_to_bv 8 0))
(V10 : odd = true -> val_mem tfxsegs m' PBv 1 (NPv mod 8))
(V11 : forall x : word, Kv + RZ <= bv_unsigned x < Kv + RZ + FILv -> mem' x = Some (Z_to_bv 8 190)).
Let MA : ARm B ly S rd0 := proj1 HAR.
Lemma AGREE0 : forall a, 0 <= a < 2 ^ 64 -> ~ WIN odd a -> ~ DZONE a -> ~ (Kv + RZ <= a < Kv + RZ + NPv) ->
~ (SUv <= a < SUv + N8D / 8) -> rd' a = rd0 a.
Proof. intros a Ra N1 N2 N3 N4. unfold rd', rd0. img_apply aview_same. img_apply MEQF; rewrite unsigned_lit_small by img_exact Ra; assumption. Qed.
Lemma AGREED : forall a, 0 <= a < 2 ^ 64 -> DZONE a -> rd' a = rdD a.
Proof. intros a Ra Hd. unfold rd', rdD. img_apply aview_same. img_apply EQD. rewrite unsigned_lit_small by img_exact Ra. img_exact Hd. Qed.
Definition SHX (a : Z) : Prop := (SUv <= a < SUv + N8D / 8) \/ PBW odd a.
Definition XC (a : Z) : Prop := WINT a \/ (Kv <= a < Kv + RZ + NPv) \/ SHX a \/ DZONE a.
Lemma AGX : forall a, aowned B ly S a -> ~ XC a -> rd' a = rd0 a.
Proof.
intros a Ho Hx. pose proof (AR_owned_low_law_ok tfxsegs B ly S W mem0 md0 a HAR Ho) as Ra.
ceil.
pose proof (AR_stack_law_ok tfxsegs B ly S W mem0 md0 a HAR) as NS.
destruct Hsp as (S1 & S2 & S3 & S4). unfold XC, SHX in Hx.
img_apply AGREE0.
- clear - Ra CR0. zlia.
- intros Hw. unfold WIN in Hw. destruct Hw as [Hs|[Hw|[Hw|Hw]]].
+ img_apply NS; [|img_try (img_exact Ho)]. clear - Hs S1 S3. unfold sp0 in *. zlia.
+ img_apply Hx. left. img_exact Hw.
+ img_apply Hx. right; left. pose proof NLOf as (Nlo & RZr & _). pose proof derived_ranges as DR'. clear - Hw Nlo RZr DR'. zlia.
+ img_apply Hx. right; right; left. right. img_exact Hw.
- intros Hd. img_apply Hx. right; right; right. img_exact Hd.
- intros Hu. img_apply Hx. right; left. pose proof NLOf as (Nlo & RZr & _). clear - Hu RZr. zlia.
- intros Hs. img_apply Hx. right; right; left. left. img_exact Hs.
Qed.
Lemma XC_where : forall a, XC a ->
(T <= a < T + kThreadObjSize /\ WINT a) \/ (Kv <= a < Kv + class_size cl) \/ (0x2008fff7000 <= a < kHighMemBeg /\ SHX a) \/
((0x17c088 + D_10c0) <= a < (0x5cc810 + D_10c0)) \/ (ly_NB ly <= a < ly_NB ly + kNodesBlockSize) \/ (ly_SB ly <= a < ly_SB ly + kStoreBlockSize).
Proof.
intros a Hx. pose proof derived_ranges as DR. pose proof cls_geom as (_ & _ & _ & _ & K5 & _).
unfold XC, SHX, WINT, PBW, DZONE in Hx. unfold t_unwinding, t_cache, kThreadObjSize in *.
decompose [or and] Hx; clear Hx.
- left. split; [img_try (zlia) | img_try (unfold WINT; unfold t_cache; zlia)].
- left. split; [img_try (zlia) | img_try (unfold WINT; zlia)].
- left. split; [img_try (zlia) | img_try (unfold WINT; zlia)].
- left. split; [img_try (zlia) | img_try (unfold WINT; unfold t_unwinding; zlia)].
- right; left. zlia.
- right; right; left. split; [img_try (zlia) | img_try (left; zlia)].
- right; right; left. split; [img_try (zlia) | img_try (right; split; [assumption | zlia])].
- do 3 right. left. zlia.
- do 4 right. left. zlia.
- do 5 right. zlia.
Qed.
Lemma Z_low : forall a, TFX_IMG_LO <= a < (0x17c088 + D_10c0) -> ~ XC a.
Proof.
intros a Ha Hx. apply XC_where in Hx. pose proof high_facts as (F1 & _). pose proof Kv_geom as (G1 & _). pose proof blocks_facts as (NBhi & SBhi & _).
clear - Ha Hx F1 G1 NBhi SBhi. numconst. unfold zone3cases in *. numconst. unfold T in *. decompose [and or] Hx; clear Hx; first [zlia | tauto].
Qed.
Lemma Z_band : forall a, kLowShadowBeg <= a < 0x2008fff7000 -> ~ XC a.
Proof.
intros a Ha Hx. apply XC_where in Hx. pose proof high_facts as (F1 & _). pose proof Kv_geom as (G1 & _). pose proof blocks_facts as (NBhi & SBhi & _).
clear - Ha Hx F1 G1 NBhi SBhi. numconst. unfold zone3cases in *. numconst. unfold T in *. decompose [and or] Hx; clear Hx; first [zlia | tauto].
Qed.
Lemma Z_sh : forall a, kLowShadowBeg <= a < kHighMemBeg -> ~ SHX a -> ~ XC a.
Proof.
intros a Ha Hs Hx. apply XC_where in Hx. pose proof high_facts as (F1 & _). pose proof Kv_geom as (G1 & _). pose proof blocks_facts as (NBhi & SBhi & _).
clear - Ha Hs Hx F1 G1 NBhi SBhi. numconst. unfold zone3cases in *. numconst. unfold T in *. destruct Hx as [Hx|[Hx|[[_ Hx]|Hx]]]; [img_try (zlia) | img_try (zlia) | img_try (img_exact (Hs Hx)) | img_try (zlia)].
Qed.
Lemma Z_T : forall a, T <= a < T + kThreadObjSize -> ~ WINT a -> ~ XC a.
Proof.
intros a Ha Hw Hx. apply XC_where in Hx. pose proof high_facts as (F1 & _). pose proof Kv_geom as (G1 & G2 & G3 & G4 & G5).
pose proof blocks_facts as (NBhi & SBhi & TNB & TSB & _ & _ & _ & _ & PT). unfold zdisjoint in TNB, TSB, PT. cbn [fst snd] in TNB, TSB, PT.
clear - Ha Hw Hx F1 G1 G4 G5 NBhi SBhi TNB TSB PT. numconst. unfold zone3cases in *. numconst. unfold T in *. decompose [and or] Hx; clear Hx; first [zlia | tauto].
Qed.
Lemma Z_prim : forall a, ly_prim ly <= a < ly_prim ly + kPrimResvSize -> ~ (Kv <= a < Kv + class_size cl) -> ~ XC a.
Proof.
intros a Ha HK Hx. apply XC_where in Hx. pose proof high_facts as (F1 & _ & F3 & _).
pose proof blocks_facts as (NBhi & SBhi & _ & _ & PNB & PSB & _ & _ & PT). unfold zdisjoint in PNB, PSB, PT. cbn [fst snd] in PNB, PSB, PT.
clear - Ha HK Hx F1 F3 NBhi SBhi PNB PSB PT. numconst. unfold zone3cases in *. numconst. unfold T in *. decompose [and or] Hx; clear Hx; first [zlia | tauto].
Qed.
Lemma Z_high : forall a, kHighMemBeg <= a -> ~ (T <= a < T + kThreadObjSize) -> ~ (ly_prim ly <= a < ly_prim ly + kPrimResvSize) ->
~ (ly_NB ly <= a < ly_NB ly + kNodesBlockSize) -> ~ (ly_SB ly <= a < ly_SB ly + kStoreBlockSize) -> ~ XC a.
Proof.
intros a Ha NT NP NNB NSB Hx. apply XC_where in Hx. pose proof Kv_geom as (G1 & G2 & G3 & G4 & G5).
clear - Ha NT NP NNB NSB Hx G4 G5. numconst. decompose [and or] Hx; clear Hx; first [zlia | tauto].
Qed.
Lemma Z_out : forall x sz a, zone3 x sz -> x <= a < x + sz -> ~ (T <= a < T + kThreadObjSize) -> ~ (ly_prim ly <= a < ly_prim ly + kPrimResvSize) ->
~ (ly_NB ly <= a < ly_NB ly + kNodesBlockSize) -> ~ (ly_SB ly <= a < ly_SB ly + kStoreBlockSize) -> ~ XC a.
Proof.
intros x sz a Z3 Ha NT NP NNB NSB Hx. apply XC_where in Hx. pose proof Kv_geom as (G1 & G2 & G3 & G4 & G5).
clear - Z3 Ha NT NP NNB NSB Hx G4 G5. numconst. unfold zone3cases in *. numconst. decompose [and or] Hx; clear Hx; first [zlia | tauto].
Qed.
Lemma Z_ext : forall (i : nat) e a, nth_error (owned_extents ly) i = Some e -> (i = 1 \/ i = 3 \/ i = 6)%nat ->
fst e <= a < fst e + snd e -> ~ XC a.
Proof.
intros i e a He Hi Ha. pose proof (lo_app ly LY) as HI. pose proof (lo_disj ly LY) as HD.
pose proof (Forall_nth' _ _ i _ HI He) as IH. cbv beta in IH.
assert (He2 : nth_error (static_extents ly) i = Some e) by (img_try (unfold static_extents; rewrite nth_error_app1 by (cbn; zlia); img_exact He)).
assert (D : forall j e', nth_error (static_extents ly) j = Some e' -> (j = 0 \/ j = 2 \/ j = 4 \/ j = 5 \/ j = 9)%nat -> zdisjoint e e').
{ intros j e' He' Hj.
destruct (Nat.lt_ge_cases i j) as [L|L].
- replace j with (i + Datatypes.S (j - i - 1))%nat in He' by zlia. img_exact (pairwise_ij _ _ _ _ _ _ HD He2 He').
- img_apply zdisjoint_sym. assert (j <> i) by (img_try (intros ->; zlia)). replace i with (j + Datatypes.S (i - j - 1))%nat in He2 by zlia. img_exact (pairwise_ij _ _ _ _ _ _ HD He' He2). }
pose proof (D 0%nat _ eq_refl ltac:(img_try (zlia))) as D0. pose proof (D 2%nat _ eq_refl ltac:(img_try (zlia))) as D2.
pose proof (D 4%nat _ eq_refl ltac:(img_try (zlia))) as D4. pose proof (D 5%nat _ eq_refl ltac:(img_try (zlia))) as D5. pose proof (D 9%nat _ eq_refl ltac:(img_try (zlia))) as D9.
assert (SZ : 0 <= snd e) by (img_try (destruct Hi as [-> |[-> | ->]]; injection He as <-; cbn; unfold kPtrArrayResv, kFakeStackSize; zlia)).
pose proof (zone3_intro ly (fst e) (snd e) IMG SZ IH ltac:(img_try (destruct e; img_exact D9))) as Z3.
unfold zdisjoint in D0, D2, D4, D5. cbn [fst snd] in D0, D2, D4, D5.
img_apply (Z_out (fst e) (snd e)); unfold T in *; clear - Z3 Ha D0 D2 D4 D5; try img_exact Z3; numconst; zlia.
Qed.
Lemma Z_sec : forall e a, In e (sec_extents ly S) -> fst e <= a < fst e + snd e -> ~ XC a.
Proof.
intros e a He Ha. pose proof (am_placed _ _ _ _ MA) as [PL PD]. pose proof (proj1 (Forall_forall _ _) PL e He) as (_ & HIA & _).
assert (D : forall e', In e' (static_extents ly) -> zdisjoint e e').
{ intros e' He'. img_exact (pairwise_In zdisjoint _ e e' (sec_extents ly S) (static_extents ly) eq_refl PD He He'). }
pose proof (D (ly_prim ly, kPrimResvSize) ltac:(img_try (unfold static_extents, owned_extents; cbn; tauto))) as D0.
pose proof (D (ly_T ly, kThreadObjSize) ltac:(img_try (unfold static_extents, owned_extents; cbn; tauto))) as D2.
pose proof (D (ly_NB ly, kNodesBlockSize) ltac:(img_try (unfold static_extents, owned_extents; cbn; tauto))) as D4.
pose proof (D (ly_SB ly, kStoreBlockSize) ltac:(img_try (unfold static_extents, owned_extents; cbn; tauto))) as D5.
pose proof (D (ly_img ly) ltac:(img_try (unfold static_extents; img_apply in_app_iff; right; cbn; tauto))) as D9.
assert (SZ : 0 <= snd e) by (img_try (clear - Ha; zlia)).
pose proof (zone3_intro ly (fst e) (snd e) IMG SZ HIA ltac:(img_try (destruct e; img_exact D9))) as Z3.
unfold zdisjoint in D0, D2, D4, D5. cbn [fst snd] in D0, D2, D4, D5.
img_apply (Z_out (fst e) (snd e)); unfold T in *; clear - Z3 Ha D0 D2 D4 D5; try img_exact Z3; numconst; zlia.
Qed.
Lemma SHX_bounds : forall a, SHX a -> SHBv + Kv / 8 + RZ / 8 <= a < SHBv + (Kv + class_size cl) / 8.
Proof.
intros a Hs. pose proof cls_geom as (_ & K2 & _ & _ & K5 & _). pose proof Kv_geom as (_ & _ & G3 & _). pose proof derived_ranges as DR. pose proof NLOf as (Nlo & RZr & RZ8 & _).
pose proof (Z.div_mod NPv 8 ltac:(img_try (zlia))) as DM. pose proof (Z.mod_pos_bound NPv 8 ltac:(img_try (zlia))) as MB.
apply Z.mod_divide in K2 as [r Hr]; [|img_try (zlia)]. apply Z.mod_divide in G3 as [q Hq]; [|img_try (zlia)].
assert (EK8 : Kv / 8 = 2 * q) by (img_try (rewrite Hq; replace (q * 16) with (2 * q * 8) by zlia; img_apply Z.div_mul; zlia)).
assert (EKC : (Kv + class_size cl) / 8 = 2 * q + 4 * r) by (img_try (rewrite Hq, Hr; replace (q * 16 + r * 32) with ((2 * q + 4 * r) * 8) by zlia; img_apply Z.div_mul; zlia)).
assert (EN8 : N8D / 8 = NPv / 8) by (img_try (unfold N8D; img_apply Z.div_mul; zlia)).
unfold SHX, PBW in Hs. rewrite EK8, EKC. destruct Hs as [Hs|[Ho Hs]].
- clear - Hs K5 DM MB EK8 Hr Hq Nlo RZr RZ8 DR EN8. unfold SKv in *. zlia.
- apply Hodd in Ho. clear - Ho Hs K5 DM MB EK8 Hr Hq Nlo RZr RZ8 DR EN8. unfold SKv in *. zlia.
Qed.
Lemma PRES_MONO : forall a, apresent (w_H W) mem0 a -> apresent (w_H W) mem' a.
Proof.
assert (G : forall u, 0 <= u < 2 ^ 64 -> apresent (w_H W) mem0 u -> apresent (w_H W) mem' u).
{ pose proof NLOf as (Nlo & RZr & _). pose proof derived_ranges as DR'. clear - EQD PRD PRS PRW V9 MEQF T Nlo RZr DR'. intros u Ru Hp.
destruct (zrange_dec (0x17c088 + D_10c0) (0x5cc810 + D_10c0) u) as [D1|D1].
{ eapply apresent_same; [img_try (img_apply EQD) | img_try (img_apply PRD; [|img_exact Hp])]; [img_try (rewrite unsigned_lit_small by img_exact Ru)|]; unfold DZONE; left; img_exact D1. }
destruct (zrange_dec (ly_NB ly) (ly_NB ly + kNodesBlockSize) u) as [D2|D2].
{ eapply apresent_same; [img_try (img_apply EQD) | img_try (img_apply PRD; [|img_exact Hp])]; [img_try (rewrite unsigned_lit_small by img_exact Ru)|]; unfold DZONE; right; left; img_exact D2. }
destruct (zrange_dec (ly_SB ly) (ly_SB ly + kStoreBlockSize) u) as [D3|D3].
{ eapply apresent_same; [img_try (img_apply EQD) | img_try (img_apply PRD; [|img_exact Hp])]; [img_try (rewrite unsigned_lit_small by img_exact Ru)|]; unfold DZONE; right; right; img_exact D3. }
destruct (zrange_dec (sp0 - ASTACK) sp0 u) as [D4|D4]; [img_try (img_apply PRS; img_exact D4)|].
destruct (zrange_dec Pv (Pv + 4) u) as [D5|D5]; [img_try (img_apply PRW; left; unfold WINT; left; img_exact D5)|].
destruct (zrange_dec (T + 2768) (T + 2824) u) as [D6|D6]; [img_try (img_apply PRW; left; right; left; img_exact D6)|].
destruct (zrange_dec SSLOTv (SSLOTv + 8) u) as [D7|D7]; [img_try (img_apply PRW; left; right; right; left; img_exact D7)|].
destruct (zrange_dec (T + t_unwinding) (T + t_unwinding + 1) u) as [D8|D8]; [img_try (img_apply PRW; left; right; right; right; img_exact D8)|].
destruct (zrange_dec Kv (Kv + RZ + NPv) u) as [D9|D9]; [img_try (img_apply PRW; right; left; img_exact D9)|].
destruct (zrange_dec (SUv) (SUv + N8D / 8) u) as [D11|D11].
{ destruct Hp as [Hh _]. split; [img_try (img_exact Hh) | img_try (exists (Z_to_bv 8 0); img_apply V9; rewrite unsigned_lit_small by img_exact Ru; img_exact D11)]. }
assert (NW : ~ PBW odd u -> apresent (w_H W) mem' u).
{ intros D10. eapply apresent_same; [|img_try (img_exact Hp)]. img_apply MEQF; rewrite unsigned_lit_small by img_exact Ru.
- intros [Hs|[Hw|[Hk|Ho]]]; [img_try (img_exact (D4 Hs)) | | img_try (clear - Hk D9 Nlo RZr DR'; zlia) | img_try (img_exact (D10 Ho))].
destruct Hw as [Hw|[Hw|[Hw|Hw]]]; [img_try (img_exact (D5 Hw)) | img_try (img_exact (D6 Hw)) | img_try (img_exact (D7 Hw)) | img_try (img_exact (D8 Hw))].
- intros [Hd|[Hd|Hd]]; [img_try (img_exact (D1 Hd)) | img_try (img_exact (D2 Hd)) | img_try (img_exact (D3 Hd))].
- clear - D9 RZr. zlia.
- img_exact D11. }
destruct odd; [|img_try (img_apply NW; intros [E _]; discriminate)].
destruct (zrange_dec PBv (PBv + 1) u) as [D10|D10]; [img_try (img_apply PRW; right; right; split; [img_refl | img_exact D10])|].
img_apply NW. intros [_ Hb]. img_exact (D10 Hb). }
intros a Hp. img_apply (proj2 (apresent_word _ _ a)). img_apply G; [img_try (pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 a)) as R; img_change (bv_modulus 64) with (2 ^ 64) in R; img_exact R)|].
img_apply (proj1 (apresent_word _ _ a)). img_exact Hp.
Qed.
Lemma ZKEEP : forall g, g mod 8 = 0 -> in_app g 8 -> hfree ly S g ->
mem' (w64 (shadow_addr g)) = mem0 (w64 (shadow_addr g)).
Proof.
intros g Hg Happ HF. pose proof high_facts as (F1 & F2 & F3 & F4 & F5 & F6 & _). pose proof Kv_range as [K1 K2].
pose proof derived_ranges as DR. pose proof blocks_facts as (NBhi & SBhi & _).
pose proof (shadow_addr_band_rw g Happ) as SBg. unfold in_band_rw, kLowShadowEnd in SBg.
pose proof (zone3_apart_hsh _ _ (shadow_addr g) F1) as TH. pose proof (zone3_apart_hsh _ _ (shadow_addr g) NBhi) as NH. pose proof (zone3_apart_hsh _ _ (shadow_addr g) SBhi) as BH.
assert (Hlo : 4096 <= g) by (img_try (clear - Happ; unfold in_app in Happ; zlia)).
assert (GP : g + 8 <= ly_prim ly \/ ly_prim ly + kPrimResvSize <= g).
{ unfold hfree in HF. pose proof (proj1 (Forall_forall _ _) HF (ly_prim ly, kPrimResvSize)
ltac:(img_try (img_apply in_app_iff; left; unfold static_extents, owned_extents; img_apply in_app_iff; left; left; img_refl))) as X. img_exact X. }
assert (G0 : 0 <= g) by (img_try (clear - Hlo; zlia)).
assert (KP : ly_prim ly <= Kv /\ Kv + 2 ^ 16 <= ly_prim ly + kPrimResvSize) by (img_try (clear - F4 F5 K1 K2; unfold kSpaceSize, kPrimResvSize in *; zlia)).
assert (AP : forall x y, Kv <= x -> y <= Kv + 2 ^ 16 -> shadow_addr g + 1 <= shadow_addr x \/ SHADOW_OFF + y / 8 <= shadow_addr g).
{ intros x y Hx Hy. img_apply shadow_apart; [img_try (img_exact Hg) | img_try (img_exact G0) | img_try (clear - Hx KP F3; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg in *; zlia) | img_try (clear - GP KP Hx Hy; zlia)]. }
unfold w64. img_apply MEQF; rewrite unsigned_lit_small by (img_try (clear - SBg; unfold kLowShadowBeg, kHighShadowBeg, kHighShadowEnd in SBg; zlia)).
- intros HW. unfold WIN, WINT, PBW in HW.
destruct HW as [HW|[HW|[HW|[_ HW]]]].
+ pose proof Hsp as (S1 & _). pose proof (lo_top ly LY) as (_ & _ & _ & T4 & _ & _ & T7). clear - HW SBg F3 S1 T7. unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, kHighMemEnd, ASTACK in *. unfold sp0 in *. zlia.
+ clear - HW SBg TH DR T. unfold zone3, kThreadObjSize, TFX_IMG_LO, kLowShadowBeg, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, t_cache, t_unwinding in *. unfold T in *. zlia.
+ clear - HW SBg DR. unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighShadowBeg, kHighShadowEnd, kHighMemBeg in *. zlia.
+ destruct (AP (Kv + RZ + N8D) (Kv + RZ + N8D + 8) ltac:(img_try (clear - DR; zlia)) ltac:(img_try (clear - DR; zlia))) as [X|X];
unfold PBv, SHBv in HW; unfold shadow_addr, SHADOW_OFF in *; clear - HW X; [img_try (zlia)|].
replace (Kv + RZ + N8D + 8) with (Kv + RZ + N8D + 1 * 8) in X by zlia. rewrite Z.div_add in X by zlia. zlia.
- intros Hd. unfold DZONE in Hd. clear - Hd SBg NBhi SBhi. unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, kNodesBlockSize, kStoreBlockSize in *. zlia.
- clear - SBg DR. unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighShadowBeg, kHighShadowEnd, kHighMemBeg in *. zlia.
- destruct (AP Uv (Uv + N8D) ltac:(img_try (clear - DR; zlia)) ltac:(img_try (clear - DR; zlia))) as [X|X];
unfold SUv, SHBv; unfold shadow_addr, SHADOW_OFF in *; clear - X DR; [img_try (zlia)|].
intros [_ R].
assert ((Uv + N8D) / 8 >= Uv / 8 + N8D / 8)%Z by (img_try (img_apply Z.le_ge; img_apply Z.div_le_lower_bound; [img_try (zlia)|]; pose proof (Z.mul_div_le Uv 8 ltac:(zlia)); pose proof (Z.mul_div_le N8D 8 ltac:(zlia)); zlia)). zlia.
Qed.
Lemma BANDKEEP : forall a, in_band_rw a -> mem0 (w64 a) <> None -> mem' (w64 a) <> None.
Proof.
pose proof derived_ranges as (DK1 & _). pose proof NLOf as (Nlo & RF1 & _). pose proof blocks_facts as (NBhi & SBhi & _).
clear - MEQF PRS PRW V9 T DK1 Nlo RF1 NBhi SBhi. intros a Ha H0.
pose proof (zone3_apart_hsh _ _ a NBhi) as NH. pose proof (zone3_apart_hsh _ _ a SBhi) as BH.
unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha. unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg in NH, BH.
assert (Ra : 0 <= a < 2 ^ 64) by (img_try (clear - Ha; zlia)).
assert (PW : apresent (w_H W) mem' a -> mem' (w64 a) <> None) by (img_try (intros [_ [b Hb]]; unfold w64; rewrite Hb; discriminate)).
destruct (zrange_dec SUv (SUv + N8D / 8) a) as [D11|D11].
{ rewrite (V9 (w64 a)); [img_try (discriminate) | img_try (unfold w64; rewrite unsigned_lit_small by img_exact Ra; img_exact D11)]. }
destruct (zrange_dec (sp0 - ASTACK) sp0 a) as [D4|D4]; [img_try (img_exact (PW (PRS a D4)))|].
assert (NW : ~ WIN odd a \/ apresent (w_H W) mem' a).
{ unfold WIN. destruct (zrange_dec Kv (Kv + RZ + NPv) a) as [D9|D9]; [img_try (right; img_apply PRW; right; left; img_exact D9)|].
destruct odd.
- destruct (zrange_dec PBv (PBv + 1) a) as [D10|D10]; [img_try (right; img_apply PRW; right; right; split; [img_refl | img_exact D10])|].
assert (NT : ~ WINT a \/ apresent (w_H W) mem' a).
{ unfold WINT. destruct (zrange_dec Pv (Pv + 4) a) as [D5|D5]; [img_try (right; img_apply PRW; left; unfold WINT; tauto)|].
destruct (zrange_dec (T + 2768) (T + 2824) a) as [D6|D6]; [img_try (right; img_apply PRW; left; unfold WINT; tauto)|].
destruct (zrange_dec SSLOTv (SSLOTv + 8) a) as [D7|D7]; [img_try (right; img_apply PRW; left; unfold WINT; tauto)|].
destruct (zrange_dec (T + t_unwinding) (T + t_unwinding + 1) a) as [D8|D8]; [img_try (right; img_apply PRW; left; unfold WINT; tauto)|]. left; tauto. }
destruct NT as [NT|NT]; [|img_try (right; img_exact NT)]. left. intros [Hs|[Hw|[Hk|[_ Ho]]]]; [img_try (img_exact (D4 Hs)) | img_try (img_exact (NT Hw)) | img_try (unfold Uv in Hk; clear - Hk D9 Nlo RF1; zlia) | img_try (img_exact (D10 Ho))].
- assert (NT : ~ WINT a \/ apresent (w_H W) mem' a).
{ unfold WINT. destruct (zrange_dec Pv (Pv + 4) a) as [D5|D5]; [img_try (right; img_apply PRW; left; unfold WINT; tauto)|].
destruct (zrange_dec (T + 2768) (T + 2824) a) as [D6|D6]; [img_try (right; img_apply PRW; left; unfold WINT; tauto)|].
destruct (zrange_dec SSLOTv (SSLOTv + 8) a) as [D7|D7]; [img_try (right; img_apply PRW; left; unfold WINT; tauto)|].
destruct (zrange_dec (T + t_unwinding) (T + t_unwinding + 1) a) as [D8|D8]; [img_try (right; img_apply PRW; left; unfold WINT; tauto)|]. left; tauto. }
destruct NT as [NT|NT]; [|img_try (right; img_exact NT)]. left. intros [Hs|[Hw|[Hk|[E _]]]]; [img_try (img_exact (D4 Hs)) | img_try (img_exact (NT Hw)) | img_try (unfold Uv in Hk; clear - Hk D9 Nlo RF1; zlia) | img_try (discriminate E)]. }
destruct NW as [NW|PWa]; [|img_try (img_exact (PW PWa))].
unfold w64. rewrite MEQF; [img_try (img_exact H0) | | | |]; rewrite ?unsigned_lit_small by img_exact Ra.
- img_exact NW.
- intros Hd. unfold DZONE in Hd. clear - Hd Ha NH BH. unfold kNodesBlockSize, kStoreBlockSize in *. zlia.
- clear - Ha DK1 Nlo RF1. unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg in *. zlia.
- img_exact D11.
Qed.
Lemma VIS_MONO : forall a, rd0 a <> None -> rd' a <> None.
Proof.
intros a HV. unfold rd', rd0, aview, mbyte in *.
destruct (seg_rom tfxsegs (Z_to_bv 64 a)) as [r|] eqn:ER.
- destruct (mrestrict (w_H W) mem' (Z_to_bv 64 a)); cbn; discriminate.
- assert (Hp : apresent (w_H W) mem0 a).
{ unfold mrestrict in HV. unfold apresent. destruct (w_H W (Z_to_bv 64 a)); [img_try (exfalso; img_apply HV; img_refl)|].
split; [img_refl|]. destruct (mem0 (Z_to_bv 64 a)) as [b|]; [img_try (exists b; img_refl) | img_try (exfalso; img_apply HV; img_refl)]. }
destruct (PRES_MONO a Hp) as [Hh [b Hb]]. unfold mrestrict. rewrite Hh, Hb. cbn. discriminate.
Qed.
Definition loc_ok (lo len : Z) : Prop := forall a, lo <= a < lo + len -> ~ XC a.
Lemma keep_cells : forall lst lo len, loc_ok lo len -> incl lst (acells B ly S) ->
Forall (fun c => lo <= aeval B ly (c_at c) /\ aeval B ly (c_at c) + Z.max 1 (Z.of_nat (c_w c)) <= lo + len) lst ->
Forall (cell_holds B ly rd') lst.
Proof.
intros lst lo len LOC INC RNG. img_apply Forall_forall. intros c Hc.
pose proof (proj1 (Forall_forall _ _) RNG c Hc) as [R1 R2]. cbv beta in R1, R2.
img_apply (YG0w.cell_holds_agree B ly rd0); [img_try (img_exact (proj1 (Forall_forall _ _) (am_cells _ _ _ _ MA) c (INC c Hc)))|].
intros k Hk. img_apply AGX.
- img_exact (proj1 (Forall_forall _ _) (acells_owned B ly S rd0 MA) c (INC c Hc) k Hk).
- img_apply LOC. zlia.
Qed.
Lemma keep_cell : forall c lo len, loc_ok lo len -> In c (acells B ly S) ->
lo <= aeval B ly (c_at c) -> aeval B ly (c_at c) + Z.max 1 (Z.of_nat (c_w c)) <= lo + len -> cell_holds B ly rd' c.
Proof.
intros c lo len LOC Hc R1 R2. img_exact (proj1 (Forall_forall _ _) (keep_cells [c] lo len LOC ltac:(img_try (intros x [<-|[]]; img_exact Hc)) ltac:(img_try (constructor; [img_try (split; assumption) | img_try (constructor)]))) c (or_introl eq_refl)).
Qed.
Lemma SF_parts :
(forall c, reg (SF z) c = reg S c) /\ st_cache_inited (SF z) = st_cache_inited S /\
(forall c, 0 <= c -> c <> cl -> cache (SF z) c = cache S c) /\ cache (SF z) cl = mkPC (pc_max (cache S cl)) l /\
frames (SF z) = frames S /\ st_qthread (SF z) = st_qthread S /\ st_qglobal (SF z) = st_qglobal S /\
st_fs (SF z) = st_fs S /\ st_internal_inited (SF z) = st_internal_inited S /\ st_sec_arr (SF z) = st_sec_arr S /\
st_sec_reserved (SF z) = st_sec_reserved S /\ st_depot (SF z) = st_depot (depot_after z tr S).
Proof.
unfold SF. pose proof (SF_same z) as (Rregs & Rinit & Rsecs & Rarr & Rres & Rqt & Rqg & Rfs & Rii & Rnev & Rcache & Rdep).
repeat split; try assumption.
- intros c. unfold reg. rewrite Rregs. img_refl.
- intros c Hc Hne. unfold cache. rewrite Rcache. img_apply znth_zupd_other; [img_try (pose proof cl_range; zlia) | img_try (img_exact Hc) | img_try (congruence)].
- unfold cache at 1. rewrite Rcache. img_apply znth_zupd_same; [img_try (pose proof cl_range; zlia)|]. rewrite (wf_len_cache _ _ _ _ _ WF). pose proof cl_range. zlia.
- unfold frames. rewrite Rfs. img_refl.
- rewrite Rdep. unfold depot_after. destruct (z =? 0); img_refl.
Qed.
Ltac fcons' := img_apply Forall_cons; [img_try (cbn; zlia)|].
Lemma val_mem_at : forall a a' (w : nat) x, a = a' -> val_mem tfxsegs m' a' w x -> val_mem tfxsegs m' a w x.
Proof. intros a a' w x -> H. img_exact H. Qed.
Lemma cells_regions : Forall (cell_holds B ly rd') (flat_map (region_cells (SF z)) (zseq 1 31)).
Proof.
pose proof SF_parts as (Rreg & _). img_apply Forall_flat_map'. intros c Hc. apply zseq_In in Hc.
replace (region_cells (SF z) c) with (region_cells S c) by (img_try (unfold region_cells; rewrite Rreg; img_refl)).
pose proof high_facts as (F1 & F2 & F3 & F4 & F5 & _). pose proof Kv_range as [KR1 KR2]. pose proof cls_geom as (_ & _ & K3 & _).
img_apply (keep_cells _ (ly_space ly + kRegionInfoOff) 4096).
- intros a Ha. img_apply Z_prim; clear - Ha F3 F4 F5 KR1 KR2 K3; unfold kRegionInfoOff, kMaxSize in *; numconst; zlia.
- intros x Hx. unfold acells. img_apply in_app_iff. left. img_apply in_flat_map. exists c. split; [img_try (img_apply In_zseq; zlia) | img_try (img_exact Hx)].
- unfold region_cells, kRegionInfoOff. repeat fcons'. img_apply Forall_nil.
Qed.
Lemma cells_caches : Forall (cell_holds B ly rd') (flat_map (cache_cells (SF z)) (zseq 1 31)).
Proof.
pose proof SF_parts as (_ & Rinit & Rother & Rcl & _). img_apply Forall_flat_map'. intros c Hc. apply zseq_In in Hc.
pose proof derived_ranges as DR. pose proof cl_range as CR.
destruct (Z.eq_dec c cl) as [->|Hne].
-
unfold cache_cells. rewrite Rinit, Hinited, Rcl. cbn [pc_chunks pc_max].
assert (INC : forall x, In x (cache_cells S cl) -> In x (acells B ly S)) by (img_try (intros x Hx; img_exact (In_acells_cache x Hx))).
unfold cache_cells in INC. rewrite Hinited, Hcache in INC.
assert (LOC : loc_ok (Pv + 4) 76).
{ intros a Ha. img_apply Z_T; unfold WINT, Pv in *; unfold T in *; clear - Ha DR CR; numconst; zlia. }
pose proof off_facts as (_ & _ & _ & _ & _ & _ & _ & CN & _).
constructor.
{ img_apply val_mem_cell. img_apply (val_mem_at _ Pv); [img_try (cbn; unfold Pv, T; numconst; zlia)|]. cbn [aeval].
replace (Z.of_nat (length l)) with (cnt - 1) by zlia. img_exact V7. }
constructor. { img_apply (keep_cell _ (Pv + 4) 76 LOC); [img_try (img_apply INC; right; left; img_refl) | img_try (cbn; unfold Pv, T; numconst; zlia) | img_try (cbn; unfold Pv, T; numconst; zlia)]. }
constructor. { img_apply (keep_cell _ (Pv + 4) 76 LOC); [img_try (img_apply INC; right; right; left; img_refl) | img_try (cbn; unfold Pv, T; numconst; zlia) | img_try (cbn; unfold Pv, T; numconst; zlia)]. }
img_apply Forall_forall. intros x Hx. apply in_map_iff in Hx as ([i vv] & <- & Hiv).
pose proof Hiv as Hi. apply in_combine_l in Hi. apply in_seq in Hi.
img_apply (keep_cell _ (Pv + 4) 76 LOC).
+ img_apply INC. right; right; right. img_apply in_map_iff. exists (i, vv). split; [img_refl|].
rewrite length_app. cbn [length]. img_apply In_combine_seq_app. img_exact Hiv.
+ cbn. unfold Pv. unfold T in *. clear - Hi CN. numconst. zlia.
+ cbn. unfold Pv. unfold T in *. clear - Hi CN Hcnt. numconst. zlia.
-
replace (cache_cells (SF z) c) with (cache_cells S c) by (img_try (unfold cache_cells; rewrite Rinit, (Rother c) by zlia; img_refl)).
img_apply (keep_cells _ (T + t_cache + 80 * c) 80).
+ intros a Ha. img_apply Z_T; unfold WINT, Pv in *; unfold T in *; clear - Ha Hc Hne DR CR; numconst; zlia.
+ intros x Hx. unfold acells. img_apply in_app_iff. right. img_apply in_app_iff. left. img_apply in_flat_map. exists c. split; [img_try (img_apply In_zseq; zlia) | img_try (img_exact Hx)].
+ unfold cache_cells. pose proof (wf_classes _ _ _ _ _ WF c ltac:(img_try (zlia))) as CL. pose proof (wr_cache _ _ _ _ _ _ CL) as WC.
pose proof (class_ok c ltac:(img_try (zlia))) as (_ & _ & _ & K4 & _). unfold T.
destruct (st_cache_inited S).
* destruct WC as [PM PL]. unfold t_cache. repeat fcons'. img_apply Forall_forall. intros x Hx. apply in_map_iff in Hx as ([i vv] & <- & Hiv).
apply in_combine_l in Hiv. apply in_seq in Hiv. cbn. zlia.
* unfold t_cache. repeat fcons'. img_apply Forall_nil.
Qed.
Lemma cells_chunks : Forall (cell_holds B ly rd') (flat_map chunk_cells (st_chunks (SF z))).
Proof.
unfold SF. rewrite SF_chunks, flat_map_app. img_apply Forall_app. split.
-
img_apply Forall_flat_map'. intros k Hk.
pose proof (chunk_facts B ly S rd0 k MA Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
pose proof (req_size_bounds (ck_req k) ltac:(img_try (zlia))) as (Q1 & Q2 & Q3).
img_apply (keep_cells _ (ck_base B ly k) (ck_rz k)).
+ intros a Ha. destruct (extent_zone B ly S rd0 k MA Hk) as [[X1 X2]|(m & len & Hin & X1 & X2)].
* img_apply Z_prim; [img_try (clear - Ha X1 X2 G8 Q2; zlia)|]. intros HK. pose proof (cached_vs_chunk k Hk) as D. clear - Ha HK D G8 Q2. zlia.
* img_apply (Z_sec (m, len)); [img_try (img_exact Hin) | img_try (cbn [fst snd]; clear - Ha X1 X2 G8 Q2; unfold kPage in *; zlia)].
+ intros x Hx. unfold acells. do 2 (img_apply in_app_iff; right). img_apply in_app_iff; left. img_apply in_flat_map. exists k. split; [img_try (img_exact Hk) | img_try (img_exact Hx)].
+ assert (EA : forall d, aeval B ly (aoff (sptr_exp (ck_beg k)) d) = ck_base B ly k + d).
{ intros d. unfold ck_base, sptr_addr. destruct (ck_beg k) as [|o|r o|c p]; try solve [destruct GG]; cbn; zlia. }
assert (EA2 : forall d d', aeval B ly (aoff (aoff (sptr_exp (ck_beg k)) d) d') = ck_base B ly k + d + d').
{ intros d d'. unfold ck_base, sptr_addr. destruct (ck_beg k) as [|o|r o|c p]; try solve [destruct GG]; cbn; zlia. }
assert (EA0 : aeval B ly (sptr_exp (ck_beg k)) = ck_base B ly k) by img_refl.
clear GG. unfold chunk_cells, kChunkHeaderSize. img_apply Forall_app. split.
* repeat (img_apply Forall_cons; [img_try (cbn [c_at c_w z1 z2 z4 c1 c2 c4]; rewrite ?EA2, ?EA, ?EA0; cbn [Z.max Z.of_nat Pos.of_succ_nat Pos.succ]; zlia)|]). img_apply Forall_nil.
* destruct (Z.eqb_spec (ck_rz k) 16); [img_try (img_apply Forall_nil)|].
assert (32 <= ck_rz k). { apply Z.mod_divide in G6 as [q Hq]; [|img_try (zlia)]. zlia. }
repeat (img_apply Forall_cons; [img_try (cbn [c_at c_w z8 c8]; rewrite ?EA2, ?EA, ?EA0; cbn [Z.max Z.of_nat Pos.of_succ_nat Pos.succ]; zlia)|]). img_apply Forall_nil.
-
cbn [flat_map]. rewrite app_nil_r. pose proof Kc_facts as (KB & KR & KN & KE & KS & KBEG & KA). unfold Kc in KB, KR, KN, KE, KS, KBEG, KA.
unfold chunk_cells, hdr_state. rewrite KR, KN, KS, KBEG. unfold kChunkHeaderSize.
pose proof NLOf as (_ & RZr & _). replace (RZ =? 16) with true by (img_try (symmetry; img_apply Z.eqb_eq; img_exact RZr)). cbn [sptr_exp app].
assert (EK : ly_space ly + (region_off cl + off) = Kv) by (img_try (rewrite Kv_is_sptr; img_refl)).
pose proof V3 as W3. pose proof V4 as W4. pose proof V5 as W5. pose proof V6 as W6.
constructor. { img_apply val_mem_cell. cbn [aeval aoff]. img_apply (val_mem_at _ (Kv + RZ - 16)); [img_try (clear - EK; zlia) | img_try (img_exact W3)]. }
constructor. { cbn [cell_holds c_at c_val c_w aeval aoff]. pose proof (W4 0%nat ltac:(img_try (zlia))) as X. rewrite Z.add_0_r in X. unfold m' in X.
pose proof (hdr_byte1_ok jb Hjb) as [B1 B2]. set (h := hdr_byte1 jb) in *. exists h. split; [|img_try (img_exact B2)].
unfold rd', aview. replace (ly_space ly + (region_off cl + off + (RZ - 16) + 1)) with (Kv + RZ - 15) by (img_try (clear - EK; zlia)). rewrite X. cbn [option_map].
rewrite le_byte_1_0 by zlia. rewrite unsigned_lit_small8 by zlia. img_refl. }
constructor. { img_apply val_mem_cell. cbn [aeval aoff]. img_apply (val_mem_at _ (Kv + RZ - 14)); [img_try (clear - EK; zlia) | img_try (img_exact W5)]. }
constructor. { img_apply val_mem_cell. cbn [aeval aoff]. img_apply (val_mem_at _ (Kv + RZ - 12)); [img_try (clear - EK; zlia) | img_try (img_exact W6)]. }
img_apply Forall_nil.
Qed.
Lemma cells_sec : Forall (cell_holds B ly rd') (sec_cells (SF z)).
Proof.
pose proof SF_parts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Rarr & Rres & _).
replace (sec_cells (SF z)) with (sec_cells S).
2:{ unfold sec_cells. rewrite Rres, Rarr. unfold SF. rewrite SF_chunks, flat_map_app. unfold Kc, new_chunk. cbn [flat_map ck_beg app]. rewrite app_nil_r. img_refl. }
assert (INC : forall x, In x (sec_cells S) -> In x (acells B ly S)) by (img_try (intros x Hx; unfold acells; do 3 (img_apply in_app_iff; right); img_apply in_app_iff; left; img_exact Hx)).
pose proof (ts_inst B TS) as EI.
assert (LOCI : loc_ok 0x10000 (0x16c088 + D_10c0)) by (img_try (intros a Ha; img_apply Z_low; unfold TFX_IMG_LO; zlia)).
pose proof (wf_secondary _ _ _ _ _ WF) as X. destruct X as [Snd Sac Sal Sres Sral].
unfold sec_cells in *.
img_apply Forall_cons; [img_try (img_apply (keep_cell _ 0x10000 (0x16c088 + D_10c0) LOCI); [img_apply INC; left; img_refl | cbn; rewrite EI; unfold TFX_INST, o_sec_reserved; zlia | cbn; rewrite EI; unfold TFX_INST, o_sec_reserved; zlia])|].
img_apply Forall_cons; [img_try (img_apply (keep_cell _ 0x10000 (0x16c088 + D_10c0) LOCI); [img_apply INC; right; left; img_refl | cbn; rewrite EI; unfold TFX_INST, o_sec_n; zlia | cbn; rewrite EI; unfold TFX_INST, o_sec_n; zlia])|].
img_apply Forall_cons; [img_try (img_apply (keep_cell _ 0x10000 (0x16c088 + D_10c0) LOCI); [img_apply INC; right; right; left; img_refl | cbn; rewrite EI; unfold TFX_INST, o_sec_mutex; zlia | cbn; rewrite EI; unfold TFX_INST, o_sec_mutex; zlia])|].
img_apply Forall_app. split.
- img_apply (keep_cells _ (ly_Q ly) kPtrArrayResv).
+ intros a Ha. img_apply (Z_ext 1 (ly_Q ly, kPtrArrayResv)); [img_refl | img_try (zlia) | img_try (cbn [fst snd]; img_exact Ha)].
+ intros x Hx. img_apply INC. do 3 right. img_apply in_app_iff. left. img_exact Hx.
+ img_apply Forall_forall. intros c Hc. apply in_map_iff in Hc as ([i r] & <- & Hir). apply in_combine_l in Hir. apply in_seq in Hir.
cbn. unfold kPtrArrayResv, kPtrArrayEntriesPerCommit in *. zlia.
- img_apply Forall_flat_map'. intros k Hk.
pose proof (chunk_facts B ly S rd0 k MA Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
pose proof (req_size_bounds (ck_req k) ltac:(img_try (zlia))) as (Q1 & Q2 & Q3).
destruct (ck_beg k) as [|o|r o|c' p] eqn:Eb; try img_apply Forall_nil.
destruct GG as (_ & _ & Gbase & Gext & Gin & _).
img_apply (keep_cells _ (ly_sec ly r) (sec_map_size (ck_req k))).
+ intros a Ha. img_apply (Z_sec (ly_sec ly r, sec_map_size (ck_req k))); [img_try (img_exact Gin) | img_try (cbn [fst snd]; img_exact Ha)].
+ intros x Hx. img_apply INC. do 3 right. img_apply in_app_iff. right. img_apply in_flat_map. exists k. rewrite Eb. split; [img_try (img_exact Hk) | img_try (img_exact Hx)].
+ unfold kPage in *. repeat fcons'. img_apply Forall_nil.
Qed.
Lemma keep_batches : forall bl, incl bl (all_batches S) -> incl (batch_cells bl) (acells B ly S) -> Forall (cell_holds B ly rd') (batch_cells bl).
Proof.
induction bl as [|b t IH]; intros Hincl INC; [img_try (img_apply Forall_nil)|]. cbn [batch_cells].
pose proof (wq_batches _ (wf_quarantine _ _ _ _ _ WF)) as BL.
pose proof (proj1 (Forall_forall _ _) BL b (Hincl b (or_introl eq_refl))) as [L1 L2]. unfold kBatchSlots in L2.
assert (LOC : loc_ok (ly_space ly + b_self b) kBatchBytes).
{ pose proof (wf_classes _ _ _ _ _ WF kBatchClass ltac:(img_try (unfold kBatchClass; zlia))) as CL.
set (x := b_self b - region_off kBatchClass).
assert (INB : In x (batch_offs S kBatchClass)) by (img_try (rewrite batch_offs_24; img_apply in_map_iff; exists b; split; [img_refl | img_try (img_apply Hincl; left; img_refl)])).
pose proof (proj1 (Forall_forall _ _) (wr_elems _ _ _ _ _ _ CL) x ltac:(img_try (rewrite !in_app_iff; tauto))) as [X1 X2].
pose proof (wr_alloc _ _ _ _ _ _ CL) as AL. pose proof (mapped_user_bound (as_universe B) 0 0 0 S kBatchClass WF ltac:(img_try (unfold kBatchClass; zlia))) as MB.
pose proof (region_in_prim ly kBatchClass LY ltac:(img_try (unfold kBatchClass; zlia))) as (R1 & R2 & R3 & R4 & R5).
assert (CS : class_size kBatchClass = 8192) by img_refl. rewrite CS in X2.
assert (BX : ly_space ly + b_self b = region_base ly kBatchClass + x) by (img_try (unfold region_base; (subst x; cbv beta); zlia)).
pose proof off_facts as (O1 & O2 & O3 & _ & O5 & NI & _). pose proof Kv_base as KB. pose proof cls_geom as (K1 & _).
intros a Ha. img_apply Z_prim.
- clear - Ha X1 X2 AL MB R1 R2 BX. unfold kBatchBytes, kUserMapSize, EV_MAX in *. zlia.
- intros HK. destruct (Z.eq_dec cl kBatchClass) as [Ec|Nc].
+ assert (Nx : off <> x) by (img_try (intros E; img_apply NI; rewrite E; img_apply in_app_iff; right; img_apply in_app_iff; right; rewrite Ec; img_exact INB)).
rewrite Ec, CS in *. apply Z.mod_divide in X2 as [qx Hqx]; [|img_try (zlia)]. apply Z.mod_divide in O3 as [qo Hqo]; [|img_try (zlia)].
clear - Ha HK BX KB Nx Hqx Hqo. unfold kBatchBytes in *. assert (qx <> qo) by (img_try (intros ->; img_apply Nx; zlia)). nia.
+ unfold region_base in BX, KB. rewrite region_off_eq in BX by (img_try (unfold kBatchClass; zlia)). rewrite region_off_eq in KB by zlia.
clear - Ha HK BX KB Nc X1 X2 AL MB O1 O2 O5 K1. unfold kBatchBytes, kBatchClass, kUserMapSize, EV_MAX in *. nia.
}
img_apply Forall_cons; [img_try (img_apply (keep_cell _ _ _ LOC); [img_apply INC; left; img_refl | cbn; zlia | cbn; unfold kBatchBytes; zlia])|].
img_apply Forall_cons; [img_try (img_apply (keep_cell _ _ _ LOC); [img_apply INC; right; left; img_refl | cbn; zlia | cbn; unfold kBatchBytes; zlia])|].
img_apply Forall_cons; [img_try (img_apply (keep_cell _ _ _ LOC); [img_apply INC; right; right; left; img_refl | cbn; zlia | cbn; unfold kBatchBytes; zlia])|].
img_apply Forall_app. split.
- img_apply (keep_cells _ _ _ LOC).
+ intros y Hy. img_apply INC. do 3 right. img_apply in_app_iff. left. img_exact Hy.
+ img_apply Forall_forall. intros c Hc. apply in_map_iff in Hc as ([i k] & <- & Hik). apply in_combine_l in Hik. apply in_seq in Hik.
cbn. unfold kBatchBytes. zlia.
- img_apply IH; [img_try (intros y Hy; img_apply Hincl; right; img_exact Hy) | img_try (intros y Hy; img_apply INC; do 3 right; img_apply in_app_iff; right; img_exact Hy)].
Qed.
Lemma cells_quar : Forall (cell_holds B ly rd') (quar_cells (SF z)).
Proof.
pose proof SF_parts as (_ & _ & _ & _ & _ & Rqt & Rqg & _).
replace (quar_cells (SF z)) with (quar_cells S) by (img_try (unfold quar_cells; rewrite Rqt, Rqg; img_refl)).
assert (INC : forall x, In x (quar_cells S) -> In x (acells B ly S)) by (img_try (intros x Hx; unfold acells; do 4 (img_apply in_app_iff; right); img_apply in_app_iff; left; img_exact Hx)).
pose proof (ts_inst B TS) as EI. pose proof derived_ranges as DR. pose proof cl_range as CR.
assert (LOCI : loc_ok 0x10000 (0x16c088 + D_10c0)) by (img_try (intros a Ha; img_apply Z_low; unfold TFX_IMG_LO; zlia)).
assert (LOCT : loc_ok (T + t_qc) 32) by (img_try (intros a Ha; img_apply Z_T; unfold WINT, Pv, t_qc in *; unfold T in *; clear - Ha DR CR; numconst; zlia)).
unfold quar_cells, qc_cells in *. unfold o_q_cmutex, o_q_rmutex, o_q_size, t_qc in *.
img_apply Forall_cons; [img_try (img_apply (keep_cell _ 0x10000 (0x16c088 + D_10c0) LOCI); [img_apply INC; left; img_refl | cbn; rewrite EI; unfold TFX_INST; zlia | cbn; rewrite EI; unfold TFX_INST; zlia])|].
img_apply Forall_cons; [img_try (img_apply (keep_cell _ 0x10000 (0x16c088 + D_10c0) LOCI); [img_apply INC; right; left; img_refl | cbn; rewrite EI; unfold TFX_INST; zlia | cbn; rewrite EI; unfold TFX_INST; zlia])|].
img_apply Forall_app. split.
- do 4 (img_apply Forall_cons; [img_try (img_apply (keep_cell _ _ _ LOCT); [img_apply INC; right; right; img_apply in_app_iff; left; cbn; tauto | cbn; unfold T; zlia | cbn; unfold T; zlia])|]).
img_apply keep_batches; [img_try (intros b Hb; unfold all_batches; img_apply in_app_iff; left; img_exact Hb)|].
intros y Hy. img_apply INC. right; right. img_apply in_app_iff. left. do 4 right. img_exact Hy.
- do 4 (img_apply Forall_cons; [img_try (img_apply (keep_cell _ 0x10000 (0x16c088 + D_10c0) LOCI); [img_apply INC; right; right; img_apply in_app_iff; right; cbn; tauto | cbn; rewrite EI; unfold TFX_INST; zlia | cbn; rewrite EI; unfold TFX_INST; zlia])|]).
img_apply keep_batches; [img_try (intros b Hb; unfold all_batches; img_apply in_app_iff; right; img_exact Hb)|].
intros y Hy. img_apply INC. right; right. img_apply in_app_iff. right. do 4 right. img_exact Hy.
Qed.
Lemma cells_fs : Forall (cell_holds B ly rd') (fs_cells (SF z)).
Proof.
pose proof SF_parts as (_ & _ & _ & _ & _ & _ & _ & Rfs & _).
replace (fs_cells (SF z)) with (fs_cells S) by (img_try (unfold fs_cells; rewrite Rfs; img_refl)).
img_apply (keep_cells _ (ly_F ly) kFakeStackSize).
- intros a Ha. img_apply (Z_ext 3 (ly_F ly, kFakeStackSize)); [img_refl | img_try (zlia) | img_try (cbn [fst snd]; img_exact Ha)].
- intros x Hx. unfold acells. do 5 (img_apply in_app_iff; right). img_apply in_app_iff. left. img_exact Hx.
- unfold fs_cells, kFakeStackSize. fcons'. fcons'. img_apply Forall_forall. intros c Hc. apply in_map_iff in Hc as ([i h] & <- & Hih).
apply in_combine_l in Hih. apply in_seq in Hih. cbn. zlia.
Qed.
Lemma DZONE64 : forall a, DZONE a -> 0 <= a < 2 ^ 64.
Proof.
intros a Ha. pose proof blocks_facts as (NBhi & SBhi & _). unfold DZONE in Ha.
clear - Ha NBhi SBhi. numconst. zlia.
Qed.
Lemma depot_final : depot_mem_ok B ly (depot_after z tr S) rd'.
Proof.
img_apply (depot_mem_ok_agree _ rdD).
- pose proof (wf_depot _ _ _ _ _ WF) as [ND INCL]. pose proof (depot_ids_bound S ND INCL). unfold depot_after. destruct (z =? 0); [img_try (zlia)|].
unfold depot_ids in *. cbn. rewrite length_app. cbn. zlia.
- intros a Ha. img_apply AGREED; [img_try (img_exact (DZONE64 a Ha)) | img_try (img_exact Ha)].
- img_exact DEPD.
Qed.
Lemma cells_depot : Forall (cell_holds B ly rd') (depot_cells ly (SF z)).
Proof.
pose proof SF_parts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Rdep).
replace (depot_cells ly (SF z)) with (depot_cells ly (depot_after z tr S)) by (img_try (unfold depot_cells, depot_ids, depot_frames; rewrite Rdep; img_refl)).
img_exact (proj1 depot_final).
Qed.
Lemma cells_ialloc : Forall (cell_holds B ly rd') (ialloc_cells B (SF z)).
Proof.
pose proof SF_parts as (_ & _ & _ & _ & _ & _ & _ & _ & Rii & _).
replace (ialloc_cells B (SF z)) with (ialloc_cells B S) by (img_try (unfold ialloc_cells; rewrite Rii; img_refl)).
pose proof (ts_ial_lo B TS) as E1. pose proof (ts_ial_w B TS) as E2. pose proof (ts_ial_flag B TS) as E3.
img_apply (keep_cells _ 0x10000 (0x16c088 + D_10c0)).
- intros a Ha. img_apply Z_low. unfold TFX_IMG_LO. zlia.
- intros x Hx. unfold acells. do 7 (img_apply in_app_iff; right). img_apply in_app_iff. left. img_exact Hx.
- unfold ialloc_cells. rewrite E1, E2, E3. unfold TFX_IAL_LO, TFX_IAL_W, TFX_IAL_FLAG.
repeat (img_apply Forall_cons; [img_try (cbn; rewrite ?E1, ?E3; unfold TFX_IAL_LO, TFX_IAL_FLAG; zlia)|]). img_apply Forall_nil.
Qed.
Lemma cells_thread : Forall (cell_holds B ly rd') thread_cells.
Proof.
unfold thread_cells. constructor; [|img_try (img_apply Forall_nil)]. img_apply val_mem_cell. cbn [aeval]. img_exact V8.
Qed.
Lemma cells_final : Forall (cell_holds B ly rd') (acells B ly (SF z)).
Proof.
unfold acells.
img_apply Forall_app; split; [img_try (img_exact cells_regions)|]. img_apply Forall_app; split; [img_try (img_exact cells_caches)|]. img_apply Forall_app; split; [img_try (img_exact cells_chunks)|].
img_apply Forall_app; split; [img_try (img_exact cells_sec)|]. img_apply Forall_app; split; [img_try (img_exact cells_quar)|]. img_apply Forall_app; split; [img_try (img_exact cells_fs)|].
img_apply Forall_app; split; [img_try (img_exact cells_depot)|]. img_apply Forall_app; split; [img_try (img_exact cells_ialloc) | img_try (img_exact cells_thread)].
Qed.
Lemma fa_final : fa_entries_ok ly rd' (SF z).
Proof.
pose proof SF_parts as (Rreg & _). intros c i vv Hc Hi HV k Hk. rewrite Rreg in Hi, HV.
pose proof (wf_classes _ _ _ _ _ WF c Hc) as CL. pose proof (wr_fa_len _ _ _ _ _ _ CL) as FL. pose proof (wr_fa_bound _ _ _ _ _ _ CL) as FB.
rewrite AGX; [img_try (img_exact (am_fa _ _ _ _ MA c i vv Hc Hi HV k Hk)) | img_try (eapply own_fa; [img_exact MA | img_exact Hc | zlia]) |].
pose proof (region_in_prim ly c LY Hc) as (R1 & R2 & _). pose proof off_facts as (O1 & O2 & _ & _ & O5 & _). pose proof Kv_base as KB. pose proof cls_geom as (K1 & _).
unfold fa_base, region_base, kFreeArrayOffset, kFreeArrayMax in *. rewrite region_off_eq in * by zlia.
img_apply Z_prim; clear - Hk Hi FL FB R1 R2 KB O1 O2 O5 K1 Hc; zlia.
Qed.
Lemma flags_final : fs_flags_ok ly rd' (SF z).
Proof.
pose proof SF_parts as (_ & _ & _ & _ & Rfr & _). intros cid pos Hc Hp. rewrite Rfr.
pose proof (flag_off_bounds cid pos Hc Hp) as FB.
rewrite AGX; [img_try (img_exact (am_flags _ _ _ _ MA cid pos Hc Hp)) | img_try (unfold flag_addr, kFakeFlagsOff in *; eapply own_F_low; [img_exact MA | zlia]) |].
img_apply (Z_ext 3 (ly_F ly, kFakeStackSize)); [img_refl | img_try (zlia) | img_try (cbn [fst snd])].
unfold flag_addr, kFakeFlagsOff, kFakeFramesOff, kFakeStackSize in *. zlia.
Qed.
Lemma sh_of_granule : forall j, shadow_addr (Kv + 8 * j) = SKv + j.
Proof.
intros j. unfold shadow_addr, SKv, SHBv, SHADOW_OFF. replace (Kv + 8 * j) with (j * 8 + Kv) by zlia. rewrite Z.div_add_l by zlia. zlia.
Qed.
Lemma SHX_granule : forall g, g mod 8 = 0 -> SHX (shadow_addr g) -> Kv + RZ <= g < Kv + class_size cl.
Proof.
intros g Hg HS. apply SHX_bounds in HS. pose proof cls_geom as (_ & K2 & _). pose proof Kv_geom as (_ & _ & G3 & _).
pose proof (Z.div_mod g 8 ltac:(img_try (zlia))) as D1. pose proof (Z.div_mod Kv 8 ltac:(img_try (zlia))) as D2. pose proof (Z.mod_pos_bound Kv 8 ltac:(img_try (zlia))) as M2.
pose proof (Z.div_mod (Kv + class_size cl) 8 ltac:(img_try (zlia))) as D3. pose proof (Z.mod_pos_bound (Kv + class_size cl) 8 ltac:(img_try (zlia))) as M3.
apply Z.mod_divide in K2 as [r Hr]; [|img_try (zlia)]. apply Z.mod_divide in G3 as [q Hq]; [|img_try (zlia)].
pose proof NLOf as (_ & RZr & RZ8 & _).
unfold shadow_addr, SHBv, SHADOW_OFF in *. clear - Hg HS D1 D2 M2 D3 M3 Hr Hq RZr RZ8. zlia.
Qed.
Lemma sh_band : forall g, 0 <= g -> g < ASAN_CEIL -> kLowShadowBeg <= shadow_addr g < kHighMemBeg.
Proof.
intros g H1 H2. unfold shadow_addr. pose proof (Z.div_mod g 8 ltac:(img_try (zlia))) as D1. pose proof (Z.mod_pos_bound g 8 ltac:(img_try (zlia))) as M1.
clear - H1 H2 D1 M1. numconst. unfold SHADOW_OFF. zlia.
Qed.
Lemma shadow_final : shadow_ok B ly rd' (SF z).
Proof.
pose proof (SF_same z) as (Rregs & _). pose proof Kc_facts as (KB & KR & KN & KE & KS & KBEG & KA). unfold Kc in KB, KR, KN, KE, KS, KBEG, KA.
pose proof cls_geom as (K1 & K2 & K3 & K4 & K5 & K6). pose proof Kv_geom as (G1 & G2 & G3 & G4 & G5). pose proof derived_ranges as DR.
assert (FPR : fa_poison_ranges ly (SF z) = fa_poison_ranges ly S).
{ unfold fa_poison_ranges, reg. unfold SF. rewrite Rregs, SF_chunks, flat_map_app. unfold new_chunk. cbn [flat_map ck_beg app]. rewrite app_nil_r. img_refl. }
unfold SF in FPR. intros g vv Hg8 HV. unfold ashadow in HV. unfold SF in HV. rewrite SF_chunks in HV.
destruct (find_chunk_at B ly (st_chunks S) g) as [k0|] eqn:F0.
-
rewrite (find_chunk_at_app1 _ _ _ _ F0) in HV.
assert (A0 : ashadow B ly S g = Some vv) by (img_try (unfold ashadow; rewrite F0; img_exact HV)).
rewrite AGX; [img_try (img_exact (am_shadow _ _ _ _ MA g vv Hg8 A0)) | img_try (img_exact (ashadow_owned B ly S rd0 g vv MA A0)) |].
apply find_chunk_at_In in F0 as [Hk0 Hg0]. pose proof (chunk_facts B ly S rd0 k0 MA Hk0) as (C1 & C2 & _).
img_apply Z_sh; [img_try (img_apply sh_band; zlia)|]. intros HS. apply (SHX_granule g Hg8) in HS. pose proof (cached_vs_chunk k0 Hk0) as D. pose proof NLOf as (_ & RZr & _). clear - HS D Hg0 RZr. zlia.
- rewrite (find_chunk_at_app2 _ _ _ F0) in HV. cbn [find_chunk_at] in HV. rewrite KB, KE in HV.
destruct (andb (Kv <=? g) (g <? Kv + class_size cl)) eqn:CK.
+
apply andb_prop in CK as [CK1 CK2]. apply Z.leb_le in CK1. apply Z.ltb_lt in CK2.
injection HV as HV'. rewrite KB in HV'. unfold chunk_granule in HV'. rewrite KR, KN, KS in HV'.
pose proof NLOf as (Nlo & RZr & RZ8 & U8). set (u := RZ / 8) in *.
set (j := (g - Kv) / 8) in HV'.
assert (Hgj : g = Kv + 8 * j).
{ (subst j; cbv beta). pose proof (Z.div_mod (g - Kv) 8 ltac:(img_try (zlia))) as D1. apply Z.mod_divide in G3 as [q Hq]; [|img_try (zlia)]. apply Z.mod_divide in Hg8 as [s Hs]; [|img_try (zlia)].
assert ((g - Kv) mod 8 = 0) by (img_try (rewrite Hs, Hq; replace (s * 8 - q * 16) with ((s - 2 * q) * 8) by zlia; img_apply Z.mod_mul; zlia)). zlia. }
pose proof (sh_of_granule j) as SA. rewrite <- Hgj in SA.
assert (N8 : N8D / 8 = NPv / 8) by (img_try (unfold N8D; img_apply Z.div_mul; zlia)).
pose proof (Z.div_mod NPv 8 ltac:(img_try (zlia))) as DM. pose proof (Z.mod_pos_bound NPv 8 ltac:(img_try (zlia))) as MB.
destruct (Z.ltb_spec j u) as [J1|J1].
*
(subst vv; cbv beta). rewrite AGX; [img_try (img_exact (shadow250 g Hg8 (conj CK1 CK2))) | img_try (eapply own_shadow_prim; [img_exact MA | zlia]) |].
img_apply Z_sh; [img_try (img_apply sh_band; zlia)|]. intros HS. apply (SHX_granule g Hg8) in HS. clear - HS Hgj J1 RZ8 U8. zlia.
* destruct (Z.ltb_spec j (u + NPv / 8)) as [J2|J2].
--
(subst vv; cbv beta). unfold rd', aview, mbyte, mrestrict. rewrite SA.
destruct (HSKpres (SKv + j) ltac:(img_try (clear - J1 J2 DR DM MB RZ8 U8; zlia))) as [Hh _]. rewrite Hh.
rewrite (V9 (Z_to_bv 64 (SKv + j))) by (img_try (rewrite unsigned_lit_small by (clear - J1 J2 DR RZ8 U8; numconst; zlia); clear - J1 J2 N8 DR; zlia)). img_refl.
-- destruct (andb (j =? u + NPv / 8) (negb (NPv mod 8 =? 0))) eqn:PJ.
++
apply andb_prop in PJ as [PJ1 PJ2]. apply Z.eqb_eq in PJ1. apply Bool.negb_true_iff in PJ2. apply Z.eqb_neq in PJ2. (subst vv; cbv beta).
assert (Ho : odd = true) by (img_try (img_apply Hodd; img_exact PJ2)).
pose proof (V10 Ho 0%nat ltac:(img_try (zlia))) as X. rewrite Z.add_0_r in X. unfold m' in X.
assert (EP : PBv = SKv + j) by (img_try (clear - DR PJ1 N8 RZ8; zlia)).
unfold rd', aview. rewrite SA, <- EP, X. cbn [option_map]. rewrite le_byte_1_0 by zlia. rewrite unsigned_lit_small8 by zlia. img_refl.
++
(subst vv; cbv beta). rewrite AGX; [img_try (img_exact (shadow250 g Hg8 (conj CK1 CK2))) | img_try (eapply own_shadow_prim; [img_exact MA | zlia]) |].
img_apply Z_sh; [img_try (img_apply sh_band; zlia)|]. intros HS. unfold SHX, PBW in HS. rewrite SA in HS.
apply Bool.andb_false_iff in PJ. destruct HS as [HS|[Ho HS]]; [img_try (clear - HS J2 N8 DR; zlia)|].
apply Hodd in Ho. assert (EP : PBv = SUv + NPv / 8) by (img_try (clear - DR N8; zlia)).
destruct PJ as [PJ|PJ]; [img_try (apply Z.eqb_neq in PJ; clear - HS EP PJ DR; zlia) | img_try (apply Bool.negb_false_iff in PJ; apply Z.eqb_eq in PJ; img_exact (Ho PJ))].
+
rewrite FPR in HV. assert (A0 : ashadow B ly S g = Some vv) by (img_try (unfold ashadow; rewrite F0; img_exact HV)).
rewrite AGX; [img_try (img_exact (am_shadow _ _ _ _ MA g vv Hg8 A0)) | img_try (img_exact (ashadow_owned B ly S rd0 g vv MA A0)) |].
destruct (in_rangesb g (fa_poison_ranges ly S)) eqn:IR; [|img_try (discriminate)].
apply in_rangesb_true in IR as (lo & len & Hin & Hglo).
assert (GB : 0 <= g < ASAN_CEIL).
{ unfold fa_poison_ranges in Hin. apply in_app_iff in Hin as [Hin|Hin].
- apply in_flat_map in Hin as (c & Hc & Hin). apply zseq_In in Hc.
pose proof (region_in_prim ly c LY ltac:(img_try (zlia))) as (R1 & R2 & R3 & R4 & R5).
pose proof (wf_classes _ _ _ _ _ WF c ltac:(img_try (zlia))) as CL. pose proof (wr_alloc _ _ _ _ _ _ CL) as A1. pose proof (wr_fa _ _ _ _ _ _ CL) as [A2 _].
pose proof (wr_fa_bound _ _ _ _ _ _ CL) as A3. pose proof (mapped_user_bound (as_universe B) 0 0 0 S c WF ltac:(img_try (zlia))) as MB.
unfold kUserMapSize, EV_MAX, kFreeArrayMax in *. unfold fa_base, kFreeArrayOffset in Hin. unfold region_base in *.
destruct Hin as [E|[E|[]]]; injection E as <- <-; clear - Hglo R1 R2 R4 R5 A1 A2 A3 MB; zlia.
- apply in_flat_map in Hin as (k & Hk & Hin). destruct (ck_beg k) as [|o|r o|c p] eqn:Eb; try (destruct Hin; fail). destruct Hin as [E|[]]. injection E as <- <-.
pose proof (am_placed _ _ _ _ MA) as [PL _].
pose proof (proj1 (Forall_forall _ _) PL (ly_sec ly r, sec_map_size (ck_req k)) ltac:(img_try (unfold sec_extents; img_apply in_flat_map; exists k; rewrite Eb; split; [img_try (img_exact Hk) | img_try (left; img_refl)]))) as (_ & [H1 _] & H2).
cbn [fst snd] in H1, H2. clear - Hglo H1 H2. zlia. }
img_apply Z_sh; [img_try (img_apply sh_band; zlia)|]. intros HS. apply (SHX_granule g Hg8) in HS. apply Bool.andb_false_iff in CK.
pose proof NLOf as (_ & RZr & _).
destruct CK as [CK|CK]; [img_try (apply Z.leb_gt in CK) | img_try (apply Z.ltb_ge in CK)]; clear - HS CK RZr; zlia.
Qed.
Lemma zshadow_final : zshadow_ok B ly rd'.
Proof.
unfold zshadow_ok. img_apply Forall_forall. intros r Hr i Hi. unfold shadow_of_addr. img_change (SHADOW_OFF + fst r / 8) with (shadow_addr (fst r)).
rewrite AGX; [img_try (img_exact (proj1 (Forall_forall _ _) (am_zshadow _ _ _ _ MA) r Hr i Hi)) | img_try (eapply own_shadow_zero; [img_exact MA | img_exact Hr | img_exact Hi]) |].
pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). pose proof Kv_geom as (G1 & G2 & G3 & G4 & G5). pose proof cls_geom as (K1 & K2 & _).
unfold zero_shadow_ranges in Hr. destruct Hr as [<-|Hr].
-
cbn [fst snd] in *.
pose proof (pairwise_ij _ _ 0 7 _ _ (lo_disj ly LY) eq_refl eq_refl) as PS. unfold zdisjoint in PS. cbn [fst snd] in PS.
pose proof (Z.div_mod (ly_stk_lo ly) 8 ltac:(img_try (zlia))) as D1. pose proof (Z.div_mod (ly_stk_hi ly - ly_stk_lo ly) 8 ltac:(img_try (zlia))) as D2.
pose proof (Z.mod_pos_bound (ly_stk_hi ly - ly_stk_lo ly) 8 ltac:(img_try (zlia))) as M2.
assert (A8 : ly_stk_lo ly mod 8 = 0) by (img_try (unfold page_aligned in T5; apply Z.mod_divide in T5 as [q Hq]; [|img_try (zlia)]; rewrite Hq; replace (q * 4096) with (q * 512 * 8) by zlia; img_apply Z.mod_mul; zlia)).
img_apply Z_sh.
+ unfold shadow_addr. clear - Hi T1 T2 T4 T7 D1 D2 M2 A8. numconst. unfold SHADOW_OFF. zlia.
+ intros HS. apply SHX_bounds in HS. unfold shadow_addr, SHBv, SHADOW_OFF in HS.
pose proof (Z.div_mod Kv 8 ltac:(img_try (zlia))) as D3. pose proof (Z.mod_pos_bound Kv 8 ltac:(img_try (zlia))) as M3.
pose proof (Z.div_mod (Kv + class_size cl) 8 ltac:(img_try (zlia))) as D4. pose proof (Z.mod_pos_bound (Kv + class_size cl) 8 ltac:(img_try (zlia))) as M4.
pose proof NLOf as (_ & RZr & RZ8 & U8). clear - Hi HS PS G4 G5 K1 D1 D2 M2 A8 D3 M3 D4 M4 RZ8 U8. zlia.
-
pose proof (proj1 (Forall_forall _ _) (aso_zshadow _ (am_syms _ _ _ _ MA)) r Hr) as (Z1 & Z2 & Z3 & Z4 & Z5).
img_apply Z_band. unfold shadow_addr. unfold kLowMemEnd in Z5.
pose proof (Z.div_mod (fst r) 8 ltac:(img_try (zlia))) as D1. pose proof (Z.div_mod (snd r) 8 ltac:(img_try (zlia))) as D2.
clear - Hi Z1 Z2 Z3 Z4 Z5 D1 D2. unfold SHADOW_OFF. zlia.
Qed.
Lemma apresent_vis : forall a, apresent (w_H W) mem' a -> rd' a <> None.
Proof. intros a [Hh [b Hb]]. unfold rd', aview, mbyte, mrestrict. rewrite Hh, Hb. cbn. discriminate. Qed.
Lemma cell_vis : forall c k, In c (acells B ly S) -> (exists e, c_val c = AV e) -> (k < c_w c)%nat -> rd0 (aeval B ly (c_at c) + Z.of_nat k) <> None.
Proof.
intros c k Hc [e He] Hk. pose proof (proj1 (Forall_forall _ _) (am_cells _ _ _ _ MA) c Hc) as CH. unfold cell_holds in CH. rewrite He in CH.
rewrite (CH k Hk). discriminate.
Qed.
Lemma Kext_vis : forall a, Kv <= a < Kv + class_size cl -> rd' a <> None.
Proof.
intros a Ha. img_apply VIS_MONO. pose proof off_facts as (O1 & O2 & _ & _ & O5 & _). pose proof Kv_base as KB. pose proof cl_range as CR.
pose proof (proj1 (Forall_forall _ _) (am_areas _ _ _ _ MA) (ASp (region_off cl), rg_mapped_user (reg S cl))
ltac:(img_try (unfold aareas; img_apply in_app_iff; left; img_apply in_flat_map; exists cl; split; [img_try (img_apply In_zseq; zlia) | img_try (left; img_refl)]))) as RV.
specialize (RV (a - region_base ly cl)). cbn [fst snd aeval] in RV. unfold region_base in *.
replace (ly_space ly + region_off cl + (a - (ly_space ly + region_off cl))) with a in RV by zlia. img_apply RV. zlia.
Qed.
Lemma vis_keep : forall lst, incl lst (ajunk B ly S) \/ incl lst (aareas S) \/ incl lst (aclient S) -> Forall (range_vis B ly rd') lst.
Proof.
intros lst H. img_apply (Forall_range_vis_keep B ly rd0 rd' lst VIS_MONO).
destruct H as [H|[H|H]]; (eapply incl_Forall; [img_try (img_exact H)|]); [img_try (img_exact (am_junk _ _ _ _ MA)) | img_try (img_exact (am_areas _ _ _ _ MA)) | img_try (img_exact (am_client _ _ _ _ MA))].
Qed.
Lemma vis_final : Forall (range_vis B ly rd') (ajunk B ly (SF z)) /\ Forall (range_vis B ly rd') (aareas (SF z)) /\ Forall (range_vis B ly rd') (aclient (SF z)).
Proof.
pose proof (SF_same z) as (Rregs & _ & _ & _ & _ & _ & _ & _ & _ & _ & Rcache & _).
pose proof SF_parts as (Rreg & Rinit & Rother & Rcl & Rfr & Rqt & Rqg & Rfs & Rii & Rarr & Rres & Rdep).
pose proof Kc_facts as (KB & KR & KN & KE & KS & KBEG & KA). unfold Kc in KB, KR, KN, KE, KS, KBEG, KA.
pose proof cls_geom as (K1 & K2 & K3 & K4 & K5 & K6). pose proof cl_range as CR. pose proof off_facts as (_ & _ & _ & _ & _ & _ & _ & CN & _).
assert (EK : ly_space ly + (region_off cl + off) = Kv) by (img_try (rewrite Kv_is_sptr; img_refl)).
unfold SF in *. split; [|img_try (split)].
-
unfold ajunk. rewrite SF_chunks.
img_apply Forall_cons. { refine (proj1 (Forall_forall _ _) (vis_keep [_] _) _ (or_introl eq_refl)). left. intros x [<-|[]]. unfold ajunk. left. img_refl. }
img_apply Forall_cons. { refine (proj1 (Forall_forall _ _) (vis_keep [_] _) _ (or_introl eq_refl)). left. intros x [<-|[]]. unfold ajunk. right; left. img_refl. }
img_apply Forall_app; split; [img_try (img_apply vis_keep; left; intros x Hx; unfold ajunk; do 2 right; img_apply in_app_iff; left; img_exact Hx)|].
img_apply Forall_app; split.
{ img_apply Forall_flat_map'. intros c Hc. apply zseq_In in Hc. destruct (Z.eq_dec c cl) as [->|Hne].
- unfold cache_junk. rewrite Rinit, Hinited, Rcl. cbn [pc_chunks].
constructor; [|img_try (img_apply Forall_nil)]. intros i Hi. cbn [fst snd aeval] in *.
destruct (Z_lt_le_dec i 4) as [I4|I4].
+
replace (ly_T ly + (t_cache + 80 * cl + 16 + 4 * Z.of_nat (length l)) + i) with (aeval B ly (c_at (z4 (aoff (AT (t_cache + 80 * cl)) (16 + 4 * Z.of_nat (length l))) (off / 16))) + Z.of_nat (Z.to_nat i)) by (img_try (cbn; zlia)).
img_apply VIS_MONO. img_apply cell_vis; [| img_try (eexists; img_refl) | img_try (cbn; zlia)].
img_apply In_acells_cache. unfold cache_cells. rewrite Hinited, Hcache. do 3 right. img_apply in_map_iff. exists (length l, off). split; [img_refl|].
rewrite length_app. cbn [length]. replace (length l) with (0 + length l)%nat at 1 by zlia. img_apply In_combine_seq_last.
+
pose proof (proj1 (Forall_forall _ _) (am_junk _ _ _ _ MA) (AT (t_cache + 80 * cl + 16 + 4 * cnt), 64 - 4 * cnt)
ltac:(img_try (unfold ajunk; do 2 right; img_apply in_app_iff; right; img_apply in_app_iff; left; img_apply in_flat_map; exists cl; split; [img_try (img_apply In_zseq; zlia)|];
unfold cache_junk; rewrite Hinited, Hcache, length_app; cbn [length]; left; f_equal; [img_try (f_equal; zlia) | img_try (zlia)]))) as RV.
specialize (RV (i - 4) ltac:(img_try (cbn [snd]; zlia))). cbn [fst snd aeval] in RV. img_apply VIS_MONO.
replace (ly_T ly + (t_cache + 80 * cl + 16 + 4 * Z.of_nat (length l)) + i) with (ly_T ly + (t_cache + 80 * cl + 16 + 4 * cnt) + (i - 4)) by zlia. img_exact RV.
- img_apply vis_keep. left. intros x Hx. unfold ajunk. do 2 right. img_apply in_app_iff; right. img_apply in_app_iff; left. img_apply in_flat_map. exists c. split; [img_try (img_apply In_zseq; zlia)|].
unfold cache_junk in *. rewrite Rinit, (Rother c) in Hx by zlia. img_exact Hx. }
img_apply Forall_app; split.
{ rewrite flat_map_app. img_apply Forall_app; split.
- img_apply vis_keep. left. intros x Hx. unfold ajunk. do 2 right. do 2 (img_apply in_app_iff; right). img_apply in_app_iff; left. img_exact Hx.
- cbn [flat_map]. rewrite app_nil_r. unfold chunk_junk. rewrite KR, KN, KS, KBEG, KE. unfold kChunkHeaderSize.
pose proof NLOf as (Nlo & RZr & _). replace (RZ =? 16) with true by (img_try (symmetry; img_apply Z.eqb_eq; img_exact RZr)). cbn [sptr_exp app].
repeat (img_apply Forall_cons; [img_try (intros i Hi; cbn [fst snd aeval aoff] in *; img_apply Kext_vis; clear - Hi EK K5 Nlo RZr; zlia)|]). img_apply Forall_nil. }
img_apply Forall_app; split.
{ img_apply vis_keep. left. intros x Hx. unfold ajunk. do 2 right. do 3 (img_apply in_app_iff; right). img_apply in_app_iff; left.
unfold sec_junk in *. rewrite Rarr, Rres, SF_chunks, flat_map_app in Hx. unfold new_chunk in Hx. cbn [flat_map ck_beg app] in Hx. rewrite app_nil_r in Hx. img_exact Hx. }
img_apply Forall_app; split.
{ img_apply vis_keep. left. intros x Hx. unfold ajunk. do 2 right. do 4 (img_apply in_app_iff; right). img_apply in_app_iff; left.
unfold quar_junk, all_batches in *. rewrite Rqt, Rqg in Hx. img_exact Hx. }
img_apply vis_keep. left. intros x Hx. unfold ajunk. do 2 right. do 5 (img_apply in_app_iff; right). img_exact Hx.
-
replace (aareas (st_final S cl l off n tr z)) with (aareas S); [img_try (img_apply vis_keep; right; left; intros x Hx; img_exact Hx)|].
unfold aareas, reg. rewrite Rregs, Rres, SF_chunks, flat_map_app. unfold new_chunk. cbn [flat_map ck_beg app]. rewrite app_nil_r. img_refl.
-
unfold aclient. rewrite Rfr. rewrite SF_chunks, flat_map_app.
img_apply Forall_app; split; [img_try (img_apply Forall_app; split)|].
+ img_apply vis_keep. do 2 right. intros x Hx. unfold aclient. img_apply in_app_iff. left. img_exact Hx.
+ cbn [flat_map]. rewrite app_nil_r. unfold chunk_user. rewrite KS, KN. unfold ck_user. rewrite KBEG, KR. cbn [padd sptr_exp].
constructor; [|img_try (img_apply Forall_nil)]. intros i Hi. cbn [fst snd aeval] in *. img_apply apresent_vis. img_apply PRW. right; left. pose proof NLOf as (Nlo & RZr & _). clear - Hi EK Nlo RZr. zlia.
+ img_apply vis_keep. do 2 right. intros x Hx. unfold aclient. img_apply in_app_iff. right. img_exact Hx.
Qed.
Lemma AR_transport : AR tfxsegs B ly (SF z) W mem' (with_vm_backing (m_vm_lazy md0) mat md0).
Proof.
pose proof HAR as (M0 & L & BUD & MW & HS0).
pose proof (SF_same z) as (Rregs & Rinit & Rsecs & Rarr & Rres & Rqt & Rqg & Rfs & Rii & Rnev & Rcache & Rdep).
unfold SF. split; [|img_try (split; [|split; [|split]])].
- destruct M0 as [Mwf Mun Msy Mly Mpl Mco Mcow Mce Mfa Mfl Mde Msh Mzs Mju Mar Mcl Mze Mts Msi].
constructor.
+   img_exact (proj1 MP).
+ img_exact Mun.
+ img_exact Msy.
+ img_exact Mly.
+   unfold sec_placed in *. unfold SF. rewrite SF_sec_extents. img_exact Mpl.
+   img_apply Forall_forall. intros c Hc.
img_apply (cell_holds_agree2 rd0 rdD); [| img_try (img_exact (proj1 (Forall_forall _ _) Mco c Hc)) | img_try (img_exact (proj1 (Forall_forall _ _) CSTD c Hc))].
intros k Hk. pose proof (const_cells_zone c k Hc Hk) as Z1. pose proof (CZONE_untouched odd _ Z1) as (Ra & N1 & N3 & N4 & _ & _ & _).
destruct (Z_lt_le_dec (aeval B ly (c_at c) + k) (0x17c088 + D_10c0)) as [Hlo|Hge].
* left. img_apply AGREE0; try assumption. unfold DZONE. pose proof blocks_facts as (NBhi & SBhi & _). clear - Hlo NBhi SBhi. numconst. zlia.
* destruct (Z_lt_le_dec (aeval B ly (c_at c) + k) (0x5cc810 + D_10c0)) as [Hlo2|Hge2].
-- right. img_apply AGREED; [img_try (img_exact Ra)|]. unfold DZONE. left. zlia.
-- left. img_apply AGREE0; try assumption. unfold DZONE. unfold CZONE in Z1. pose proof blocks_facts as (NBhi & SBhi & TNB & TSB & _).
pose proof HC_NB as [CNB CSB]. unfold zdisjoint in CNB, CSB, TNB, TSB. cbn [fst snd] in CNB, CSB, TNB, TSB. unfold T in Z1.
pose proof (pairwise_ij _ _ 4 2 _ _ (lo_disj ly LY) eq_refl eq_refl) as DNB. pose proof (pairwise_ij _ _ 5 1 _ _ (lo_disj ly LY) eq_refl eq_refl) as DSB. unfold zdisjoint in DNB, DSB. cbn [fst snd] in DNB, DSB.
clear - Z1 Hge2 NBhi SBhi CNB CSB TNB TSB DNB DSB. unfold TFX_TSD in *. numconst. zlia.
+ img_exact Mcow.
+ img_exact cells_final.
+ img_exact fa_final.
+ img_exact flags_final.
+   img_apply (depot_ok_ext (depot_after z tr S)); [img_try (rewrite Rdep; unfold depot_after; destruct (z =? 0); img_refl) | img_try (img_exact (proj1 (proj2 depot_final)))].
+ img_exact shadow_final.
+ img_exact zshadow_final.
+ img_exact (proj1 vis_final).
+ img_exact (proj1 (proj2 vis_final)).
+ img_exact (proj2 (proj2 vis_final)).
+
img_apply Forall_forall. intros r Hr i Hi. rewrite <- (proj1 (Forall_forall _ _) Mze r Hr i Hi). img_apply AGX.
* pose proof (aso_ialloc _ Msy) as [I1 I2].
eapply (own_area B ly S rd0 (as_ialloc_lo B, as_ialloc_hi B - as_ialloc_lo B)); [img_try (img_exact MA) | img_try (cbn; tauto) |].
unfold ialloc_zero in Hr. cbn [fst snd]. destruct Hr as [<-|[<-|[]]]; cbn [fst snd aeval] in *; zlia.
* img_apply Z_low. unfold TFX_IMG_LO. unfold ialloc_zero in Hr. pose proof (ts_ial_lo B TS) as E1. pose proof (ts_ial_hi B TS) as E2. pose proof (ts_ial_w B TS) as E3.
destruct Hr as [<-|[<-|[]]]; cbn [fst snd aeval] in *; rewrite ?E1, ?E2, ?E3 in *; unfold TFX_IAL_LO, TFX_IAL_HI, TFX_IAL_W in *; zlia.
+   img_exact Mts.
+   img_exact Msi.
- unfold SF. img_exact (SF_ledger z _ (ALedger_same tfxsegs ly S md0 _ L (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) ltac:(img_try (unfold eager_used; rewrite m_vmmaps_wvb, m_vm_lazy_wvb; img_refl)))).
-   destruct BUD as [BUD PIN].
split; [| img_try (intros e He; unfold SF in He; rewrite SF_sec_extents in He; img_exact (PIN e He))].
unfold abudget, sec_hulls in *. rewrite Rnev, Rsecs  . unfold SF. rewrite SF_sec_live. unfold EV_A in *. zlia.
-   img_exact (amwf_same md0 _ (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) MW).
-   destruct HS0 as [HS0 HZ0]. split.
+ intros a Ha NC HV. img_apply (BANDKEEP a Ha). img_apply (HS0 a Ha); [|img_try (img_exact HV)].
intros CL. img_apply NC. destruct CL as [(k & Hk & Hst & Hr) | (cp & Hcp & Hr)].
* left. exists k. split; [img_try (unfold SF; rewrite SF_chunks; img_apply in_app_iff; left; img_exact Hk) | img_try (img_exact (conj Hst Hr))].
* right. exists cp. split; [unfold SF, frames in Hcp |- *; rewrite Rfs; img_exact Hcp | img_exact Hr].
+
img_apply (ahz_keep ly S (SF z) mem0 mem'); [|img_try (img_exact HZ0)]. intros g Hg Happ HF.
assert (HF0 : hfree ly S g) by (img_try (unfold hfree in HF |- *; unfold SF in HF; rewrite SF_sec_extents in HF; img_exact HF)).
split; [img_try (img_exact HF0) | img_try (img_exact (ZKEEP g Hg Happ HF0))].
Qed.
End c0.
Hypothesis HDPOST : forall z m, DPOST z m -> DPOST3 z m.
Lemma AR_final : AR_final_stmt.
Proof.
intros odd z regs' mem' mat HR Hodd MP HAR.
destruct HR as (_ & regs2 & mem2 & mat2 & EC & R10 & RCS & (memD & DP & PRD & EQD) & MEQF & PRS & PRW & VALS).
injection EC as E1 E2 E3. (subst regs2 mem2 mat2; cbv beta). try clear EC.
destruct (HDPOST z memD DP) as (AOK & DEPD & CSTD).
destruct VALS as (V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11).
eapply AR_transport; eassumption.
Qed.
Lemma LEAF_final : AR tfxsegs B ly S W mem0 md0 -> forall odd z W' c',
at_RET odd z W' c' -> (odd = true <-> NPv mod 8 <> 0) -> MPF z ->
malloc_leaf tfxsegs B ly S W regs0 mem0 md0 n (ck_user Kc, SF z) W' c'.
Proof. intros HAR odd z W' c' HR Hodd MP. img_exact (LEAF_ok AR_final HAR odd z W' c' HR Hodd MP). Qed.
End b0.
End a0.
