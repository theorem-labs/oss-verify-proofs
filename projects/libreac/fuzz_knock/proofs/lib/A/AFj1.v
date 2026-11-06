(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AFj1.v, with its module paths changed and its addresses moved to libreac/fuzz_knock's ASan build; AB1v's tfibsegs is A/AWalkFw0.v's. *)
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.A Require Import AWalkFw0 AB1q AF0l AF0m AF0x AFl0.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.A Require Import AB1w AE3d AFhy AFis AFi3 AFiy AFiz AFj0 AFix.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YM05 KnBlockExt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac YM03.lf_lia_orig ::= Zify.zify; xlia zchecker.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Set Printing Depth 50. Set Printing Width 180.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Ltac zlia := first [ lia | ceil; unfold zone3, zone3cases, in_app, app_addr, in_band_rw, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, ASAN_CEIL, YImgTop.IMG_LO, YImgTop.IMG_TOP in *; lia ].
Ltac zcanon_simp :=
repeat match goal with
| |- context [zcanon ?x] =>
lazymatch x with
| context [zcanon _] => fail
| context [Z.shiftl _ _] => fail | context [Z.shiftr _ _] => fail | context [Z.land _ _] => fail
| context [Z.lor _ _] => fail | context [Z.lxor _ _] => fail
| _ => rewrite (zcanon_id x) by (unfold M64; lia)
end
end.
Ltac is_zlit a := lazymatch a with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.
Ltac land_lits :=
repeat match goal with
| |- context [Z.land ?a ?b] => is_zlit a; is_zlit b; let c := eval vm_compute in (Z.land a b) in change (Z.land a b) with c
end.
Ltac numconst := ceil; unfold zone3, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize,
t_cache, t_unwinding, t_stats, ASTACK, TFIB_IMG_END, TFIB_IMG_LO, kLowShadowBeg, UNW_STK, BST_SIZE, DEP_STK, YImgTop.IMG_LO, YImgTop.IMG_TOP in *.
Ltac pin_zev :=
lazymatch goal with |- U _ _ = U _ (sr_get ?sr ?r) => let t := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with t end;
apply U_eq_by_zev; [reflexivity | reflexivity |]; cbn [zev zalu_raw zmd_raw]; unfold rho_of.
Ltac memv HS i j :=
lazymatch goal with |- val_mem _ _ ?a ?n ?v =>
let nn := lazymatch n with 1%nat => constr:(1%N) | 2%nat => constr:(2%N) | 4%nat => constr:(4%N) | _ => constr:(8%N) end in
lazymatch type of HS with st_ok _ ?E ?ss (restrict ?H ?ms) =>
eapply (chunk_val_at H E ss ms i j _ _ nn _ v a HS);
[ reflexivity | reflexivity | cbn [base_val YP09.r_base]
| | lazymatch goal with |- _ <= _ < ?p => let q := eval vm_compute in p in change p with q end
| cbn; lia ]
end
end.
Ltac forget_regs HS k clob :=
lazymatch type of HS with st_ok _ ?E ?ss (restrict ?H ?ms) =>
let ss' := eval vm_compute in (ss_after_stretch ss (ss_mem ss) k clob (ss_pc ss)) in
let HS2 := fresh "HSf" in
pose proof (st_ok_forget2 k E ss ss' H ms clob HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
eq_refl eq_refl ltac:(vm_compute; reflexivity)) as HS2; clear HS; rename HS2 into HS
end.
Section a0.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (n : Z) (ch : list (Z * Z * Z)).
Variables (cl cnt v csz j0 jb j1 j2 j3 j4 : Z).
Variable kz : Z.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Local Abbreviation RZ := (@AFis.RZ kz).
Local Abbreviation R8v := (@AFis.R8v n).
Local Abbreviation N8D := (@AFis.N8D n).
Local Abbreviation Pv := (@AFis.Pv ly cl).
Local Abbreviation PVv := (@AFis.PVv ly cl cnt).
Local Abbreviation Kv := (@AFis.Kv ly cl v).
Local Abbreviation SHBv := (@AFis.SHBv).
Local Abbreviation SKv := (@AFis.SKv ly cl v).
Local Abbreviation SSLOTv := (@AFis.SSLOTv ly cl).
Local Abbreviation PBv := (@AFis.PBv ly n cl v kz).
Local Abbreviation Uv := (@AFis.Uv ly cl v kz).
Local Abbreviation SUv := (@AFis.SUv ly cl v kz).
Local Abbreviation FILv := (@AFis.FILv n).
Local Abbreviation NDv := (@AFis.NDv n kz).
Local Abbreviation tr := (@AFis.tr ly regs0 ch).
Local Abbreviation XW := (@AFis.XW ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation E0 := (@AFis.E0 ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaT := (@AFis.EaT ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaC := (@AFis.EaC ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaSB := (@AFis.EaSB ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaTOP := (@AFis.EaTOP ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation Er := (@AFis.Er ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation E2 := (@AFis.E2 ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation E1 := (@AFis.E1 ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation E8 := (@AFis.E8 ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation E10 := (@AFis.E10 ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation E4 := (@AFis.E4 ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaP := (@AFis.EaP ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaK := (@AFis.EaK ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaSK := (@AFis.EaSK ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaSSLOT := (@AFis.EaSSLOT ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaPB := (@AFis.EaPB ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaPV := (@AFis.EaPV ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaKL := (@AFis.EaKL ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaRZ := (@AFis.EaRZ ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaU := (@AFis.EaU ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaSU := (@AFis.EaSU ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaFIL := (@AFis.EaFIL ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaND := (@AFis.EaND ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation WINT := (@AFis.WINT ly cl).
Local Abbreviation PBW := (@AFis.PBW ly n cl v kz).
Local Abbreviation WIN := (@AFis.WIN ly regs0 n cl v kz).
Local Abbreviation win_in_WIN := (@AFis.win_in_WIN ly regs0 n cl v kz).
Hypotheses (Hcl : 1 <= cl <= 31) (Hv : 0 <= v /\ 16 * v + 2 ^ 16 <= 2 ^ 32) (Hcnt : 1 <= cnt <= 16) (Hjb : 0 <= jb <= 255).
Hypothesis Hv2 : v mod 2 = 0.
Hypothesis LY : layout_ok ly.
Hypothesis IMG : img_cover ly.
Hypothesis Hn : getr regs0 10 = w64 n.
Hypothesis Htp : getr regs0 4 = w64 TFIB_TP.
Hypothesis Hra : YK0s.ret_ok (getr regs0 1).
Hypothesis Hra4096 : 4096 <= bv_unsigned (getr regs0 1).
Hypothesis Hsp : ly_stk_lo ly + ASTACK <= sp0 /\ ly_bot ly < sp0 /\ sp0 <= ly_stk_hi ly /\ sp0 mod 16 = 0.
Hypothesis Hch : if sp0 + 16 <? ly_top ly
then (if bad_next sp0 (ly_top ly) (bv_unsigned (getr regs0 8)) then ch = []
else sp0 + 16 <= bv_unsigned (getr regs0 8) /\
fpchain (rdword (aview tfibsegs (w_H W) mem0)) (bv_unsigned (getr regs0 8)) (ly_top ly) ch)
else ch = [].
Local Abbreviation HCdisj := (@AFis.HCdisj _ ly regs0 v Hv LY).
Local Abbreviation DZONE := (@AFis.DZONE ly).
Variable DPOST : alayout -> world tfibsegs -> Model -> Z -> (word -> option byte) -> Prop.
Local Abbreviation HC_NB := (@AFis.HC_NB _ ly LY).
Hypothesis HKpres : forall a, Kv <= a < Kv + RZ + R8v -> apresent (w_H W) mem0 a.
Hypothesis HSKpres : forall a, SKv <= a < SKv + (RZ + R8v) / 8 -> apresent (w_H W) mem0 a.
Hypothesis HPB250 : n mod 8 <> 0 -> val_mem tfibsegs (mrestrict (w_H W) mem0) PBv 1 250.
Local Abbreviation HCX := (@AFis.HCX _ ly LY).
Local Abbreviation tr_length := (@AFis.tr_length ly regs0 mem0 n ch v kz DPOST).
Local Abbreviation Kv_range := (@AFis.Kv_range ly regs0 mem0 n cl v kz Hcl Hv Hv2 DPOST).
Local Abbreviation high_facts := (@AFis.high_facts _ ly regs0 mem0 n v kz Hv LY IMG DPOST).
Local Abbreviation blocks_facts := (@AFis.blocks_facts _ ly LY IMG).
Local Abbreviation off_T := (@AFis.off_T _ ly regs0 mem0 n v kz Hv LY IMG DPOST).
Local Abbreviation off_C := (@AFis.off_C _ ly regs0 mem0 n v kz Hv LY IMG DPOST).
Local Abbreviation off_NB := (@AFis.off_NB _ ly LY IMG).
Local Abbreviation off_SB := (@AFis.off_SB _ ly LY IMG).
Ltac off_by tac :=
first [ apply off_img_high; tac
| apply off_T; unfold kThreadObjSize; tac
| apply off_C; tac
| apply off_NB; tac
| apply off_SB; tac
| unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP; unfold TFIB_IMG_LO, YImgTop.IMG_LO, YImgTop.IMG_TOP; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END, YImgTop.IMG_LO, YImgTop.IMG_TOP; tac ].
Hypothesis Hkz : 1 <= kz <= 6.
Hypothesis Nrange : rz_lo kz <= n <= rz_hi kz.
Local Abbreviation kz_cases := (@AFis.kz_cases kz Hkz).
Local Abbreviation RZ_facts := (@AFis.RZ_facts n kz Hkz Nrange).
Local Abbreviation RZ_num := (@AFis.RZ_num n kz Hkz Nrange).
Ltac numconst ::= (ceil; unfold zone3, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize,
t_cache, t_unwinding, t_stats, ASTACK, TFIB_IMG_END, TFIB_IMG_LO, kLowShadowBeg, UNW_STK, BST_SIZE, DEP_STK, YImgTop.IMG_LO, YImgTop.IMG_TOP in * ); try pose proof RZ_num as RZN.
Local Abbreviation derived_ranges := (@AFis.derived_ranges _ ly regs0 mem0 n cl cnt v kz Hcl Hv Hcnt Hv2 LY IMG DPOST Hkz Nrange).
Hypothesis Hcl_def : cl = class_id (R8v + RZ).
Local Abbreviation NDv_facts := (@AFis.NDv_facts ly regs0 mem0 n v kz DPOST Hkz Nrange).
Local Abbreviation CL_hi_E := (@AFis.CL_hi_E ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz DPOST Hkz Nrange Hcl_def).
Local Abbreviation CL_lo_E := (@AFis.CL_lo_E ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz DPOST Hkz Nrange Hcl_def).
Local Abbreviation WIN1 := (@AFis.WIN1 ly regs0 n cl v kz).
Local Abbreviation WIN1_WIN := (@AFis.WIN1_WIN ly regs0 mem0 n cl v kz DPOST).
Local Abbreviation WIN_odd := (@AFis.WIN_odd ly regs0 mem0 n cl cnt v jb kz Hcl Hv Hcnt Hjb Hsp DPOST Hkz Nrange).
Local Abbreviation WIN1_odd := (@AFis.WIN1_odd ly regs0 mem0 n cl cnt v jb kz Hcl Hv Hcnt Hjb Hsp DPOST Hkz Nrange).
Local Abbreviation WSKEL := (@AFis.WSKEL).
Local Abbreviation WSKEL1 := (@AFis.WSKEL1).
Local Abbreviation win_sub := (@AFis.win_sub).
Local Abbreviation win_sub_sound := (@AFis.win_sub_sound ly regs0 mem0 n v kz Hv DPOST).
Local Abbreviation WSKEL_WIN := (@AFis.WSKEL_WIN _ ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz Hcl Hv Hcnt Hv2 LY IMG DPOST Hkz Nrange).
Local Abbreviation WSKEL1_WIN1 := (@AFis.WSKEL1_WIN1 _ ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz Hcl Hv Hcnt Hv2 LY IMG DPOST Hkz Nrange).
Local Abbreviation windows_WIN := (@AFis.windows_WIN _ ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz Hcl Hv Hcnt Hv2 LY IMG DPOST Hkz Nrange).
Local Abbreviation windows_WIN1 := (@AFis.windows_WIN1 _ ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz Hcl Hv Hcnt Hv2 LY IMG DPOST Hkz Nrange).
Local Abbreviation frame_WIN1 := (@AFis.frame_WIN1 _ ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz Hcl Hv Hcnt Hv2 LY IMG DPOST Hkz Nrange).
Local Abbreviation WIN_not_high := (@AFis.WIN_not_high _ ly regs0 mem0 n cl cnt v kz Hcl Hv Hcnt Hv2 LY IMG Hsp DPOST Hkz Nrange).
Variables (mat0 : list word).
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 0x51370) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis U1 : tfib_unwind_spec.
Hypothesis SEED : st_ok tfibsegs E0 SS0 (restrict (w_H W) (mkst regs0 (w64 0x51370) mem0 (seg_rom tfibsegs))).
Local Abbreviation all_disjoint_of_forall := (@AFis.all_disjoint_of_forall).
Local Abbreviation kept_of_frame := (@AFis.kept_of_frame W ly regs0 mem0 n v kz DPOST).
Local Abbreviation SKEL_TAIL := (@AFis.SKEL_TAIL).
Local Abbreviation stack_ivs := (@AFis.stack_ivs _ ly regs0 mem0 n v kz Hv LY Hsp DPOST).
Local Abbreviation stack_ivs2 := (@AFis.stack_ivs2 _ ly regs0 mem0 n v kz Hv LY Hsp DPOST).
Local Abbreviation DZONE_disj := (@AFis.DZONE_disj _ ly regs0 mem0 n cl cnt v kz Hcl Hv Hcnt Hv2 LY IMG Hsp DPOST Hkz Nrange).
Local Abbreviation RFACTS := (@AFis.RFACTS ly regs0 n cl v kz).
Local Abbreviation zone_lit := (@AFis.zone_lit _ ly regs0 mem0 n cl cnt v kz Hcl Hv Hcnt Hv2 LY IMG Hsp DPOST Hkz Nrange).
Local Abbreviation zone_T := (@AFis.zone_T _ ly regs0 mem0 n cl cnt v kz Hcl Hv Hcnt Hv2 LY IMG Hsp DPOST Hkz Nrange).
Local Abbreviation zone_C := (@AFis.zone_C _ ly regs0 mem0 n cl cnt v kz Hcl Hv Hcnt Hv2 LY IMG Hsp DPOST Hkz Nrange).
Local Abbreviation zone_K := (@AFis.zone_K _ ly regs0 mem0 n cl cnt v kz Hcl Hv Hcnt Hv2 LY IMG Hsp DPOST Hkz Nrange).
Local Abbreviation zone_SH := (@AFis.zone_SH _ ly regs0 mem0 n cl cnt v kz Hcl Hv Hcnt Hv2 LY IMG Hsp DPOST Hkz Nrange).
Local Abbreviation tail_ext_ok := (@AFis.tail_ext_ok _ ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz Hcl Hv Hcnt Hv2 LY IMG Hsp DPOST Hkz Nrange).
Local Abbreviation at_ST := (@AFis.at_ST _ W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation at_ST2 := (@AFis.at_ST2 _ _ W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz DPOST).
Local Abbreviation at_S2 := (@AFis.at_S2 _ _ W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz DPOST).
Local Abbreviation at_RET := (@AFis.at_RET _ _ W ly regs0 mem0 md0 n cl cnt v jb kz DPOST).
Ltac frame_acc HE :=
match goal with
| MEQ : (forall x : word, ~ WIN1 ?odd (bv_unsigned x) -> ?m1 x = ?mb x), HFx : frame_of ?E ?rs ?m1 ?m2 |- _ =>
let MEQ' := fresh "MEQ" in
assert (MEQ' : forall x : word, ~ WIN1 odd (bv_unsigned x) -> m2 x = mb x)
by (intros x Hx; transitivity (m1 x); [exact (frame_WIN1 odd E rs m1 m2 HE ltac:(vm_compute; reflexivity) HFx x Hx) | exact (MEQ x Hx)]);
clear MEQ HFx; rename MEQ' into MEQ
end.
Local Abbreviation memset_stretch := (@AFis.memset_stretch _ W ly regs0 mem0 n cl cnt v jb kz Hcl Hv Hcnt Hjb Hsp DPOST Hkz Nrange).
Variables (B : asyms) (S : astate) (l : list Z) (off : Z).
Hypothesis TS : TfibSyms B.
Hypothesis HTSD : ly_tsd ly = TFIB_TSD.
Hypothesis HARm : ARm B ly S (aview tfibsegs (w_H W) mem0).
Hypothesis Hgp : getr regs0 3 = w64 (as_gp B).
Hypothesis Hpres0 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem0 a.
Hypothesis Hinited : st_cache_inited S = true.
Hypothesis Hcache : pc_chunks (cache S cl) = l ++ [off].
Hypothesis Hcl_class : cl = chunk_class n.
Hypothesis Hcnt_def : cnt = Z.of_nat (length (l ++ [off])).
Hypothesis Hoff_def : off = 16 * v.
Hypothesis Hcsz_def : csz = class_size cl.
Hypothesis Hj0 : val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2784) 8 j0.
Hypothesis Hj1 : val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2800) 8 j1.
Hypothesis Hj2 : val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2808) 8 j2.
Hypothesis Hj3 : val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2816) 8 j3.
Hypothesis Hj4 : val_mem tfibsegs (mrestrict (w_H W) mem0) SSLOTv 8 j4.
Hypothesis Hjb_def : val_mem tfibsegs (mrestrict (w_H W) mem0) (Kv + RZ - 15) 1 jb.
Hypothesis HQT : qmeter S.
Local Abbreviation casek_sizes := (@AFis.casek_sizes n kz Hkz Nrange).
Local Abbreviation Kv_is_sptr := (@AFis.Kv_is_sptr ly cl v Hcl B off Hoff_def).
Local Abbreviation cl_range := (@AFiy.cl_range ly regs0 mem0 n cl v kz DPOST Hkz Nrange l off Hcl_class).
Local Abbreviation cls_geom := (@AFiy.cls_geom ly regs0 mem0 n cl v kz DPOST Hkz Nrange l off Hcl_class).
Local Abbreviation cls_wf := (@AFiy.cls_wf _ W ly regs0 mem0 n cl v kz DPOST Hkz Nrange B S l off HARm Hcl_class).
Local Abbreviation off_facts := (@AFiy.off_facts _ W ly regs0 mem0 n cl cnt v kz Hv2 DPOST Hkz Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation Kv_base := (@AFiy.Kv_base ly regs0 mem0 n cl v kz DPOST Hkz Nrange l off Hcl_class Hoff_def).
Local Abbreviation Kv_geom := (@AFiy.Kv_geom _ W ly regs0 mem0 n cl cnt v csz kz Hv2 LY DPOST Hkz Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def).
Local Abbreviation Hcl' := (@AFiy.Hcl' ly regs0 mem0 n cl v kz DPOST Hkz Nrange l off Hcl_class).
Local Abbreviation Hcnt' := (@AFiy.Hcnt' _ W ly regs0 mem0 n cl cnt v kz Hv2 Hsp DPOST Hkz Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation Hv' := (@AFiy.Hv' _ W ly regs0 mem0 n cl cnt v kz Hv2 DPOST Hkz Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation cached_vs_chunk := (@AFiy.cached_vs_chunk _ W ly regs0 mem0 n cl cnt v csz kz Hv2 LY Hsp DPOST Hkz Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def).
Local Abbreviation find_chunk_at_none := (@AFiy.find_chunk_at_none _ W ly regs0 mem0 n cl cnt v kz Hv2 Hsp DPOST Hkz Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation shadow250 := (@AFiy.shadow250 _ W ly regs0 mem0 n cl cnt v csz kz Hv2 LY Hsp DPOST Hkz Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def).
Local Abbreviation shadow_present := (@AFiy.shadow_present _ W ly regs0 mem0 n cl cnt v csz kz Hv2 LY IMG Hsp DPOST Hkz Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def).
Local Abbreviation vis_present := (@AFiy.vis_present _ W ly regs0 mem0 n cl cnt v kz Hv2 Hsp DPOST Hkz Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation KPRES := (@AFiy.KPRES _ W ly regs0 mem0 n cl cnt v csz kz Hv2 LY Hsp DPOST Hkz Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def).
Local Abbreviation SKPRES := (@AFiy.SKPRES _ W ly regs0 mem0 n cl cnt v csz kz Hv2 LY IMG Hsp DPOST Hkz Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def).
Local Abbreviation PB250 := (@AFiy.PB250 _ W ly regs0 mem0 n cl cnt v csz kz Hv2 LY IMG Hsp DPOST Hkz Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def).
Local Abbreviation in_thread_junk := (@AFiy.in_thread_junk _ W ly regs0 mem0 n cl cnt v kz Hv2 Hsp DPOST Hkz Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation junk_word := (@AFiy.junk_word _ W ly regs0 mem0 n cl cnt v kz Hv2 LY IMG Hsp DPOST Hkz Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation junk_byte := (@AFiy.junk_byte _ W ly regs0 mem0 n cl cnt v csz kz Hv2 LY Hsp DPOST Hkz Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def).
Local Abbreviation junk_values := (@AFiy.junk_values _ W ly regs0 mem0 n cl cnt v csz kz Hv2 LY IMG Hsp DPOST Hkz Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def).
Local Abbreviation cell_sym := (@AFiy.cell_sym _ W ly regs0 mem0 n cl cnt v kz Hv2 Hsp DPOST Hkz Nrange B S l off TS HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation cell_lit := (@AFiy.cell_lit _ W ly regs0 mem0 n cl cnt v kz Hv2 Hsp DPOST Hkz Nrange B S l off TS HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation cell_state := (@AFiy.cell_state _ W ly regs0 mem0 n cl cnt v kz Hv2 Hsp DPOST Hkz Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation In_acells_cache := (@AFiy.In_acells_cache _ W ly regs0 mem0 n cl cnt v kz Hv2 Hsp DPOST Hkz Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation In_combine_seq_last := (@AFiy.In_combine_seq_last _ W ly regs0 mem0 n cl cnt v kz Hv2 Hsp DPOST Hkz Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation cache_vals := (@AFiy.cache_vals _ W ly regs0 mem0 n cl cnt v csz kz Hv2 Hsp DPOST Hkz Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def).
Local Abbreviation unwinding_val := (@AFiy.unwinding_val _ W ly regs0 mem0 n cl cnt v kz Hv2 Hsp DPOST Hkz Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation sk_val := (@AFiy.sk_val _ W ly regs0 mem0 n cl cnt v csz kz Hv2 LY IMG Hsp DPOST Hkz Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def).
Local Abbreviation val_mem_mod8 := (@AFiy.val_mem_mod8 _ W ly regs0 mem0 n cl cnt v kz Hv2 Hsp DPOST Hkz Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation chunk_lit := (@AFiy.chunk_lit _ W ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz Hv2 Hsp DPOST Hkz Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation chunk_lit_at := (@AFiy.chunk_lit_at _ W ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz Hv2 Hsp DPOST Hkz Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation chunk_atom := (@AFiy.chunk_atom _ W ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz Hv2 Hsp DPOST Hkz Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation REG0_ok := (@AFiz.REG0_ok _ W ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz Hcl Hv Hcnt Hjb Hv2 LY IMG Hsp DPOST Hkz Nrange B S l off TS HTSD HARm Hpres0 Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def Hj0 Hj1 Hj2 Hj3 Hj4 Hjb_def).
Local Abbreviation Kv32 := (@AFj0.Kv32 _ W ly regs0 mem0 n cl v kz Hv2 LY DPOST l off).
Local Abbreviation PAIRS_ok := (@AFj0.PAIRS_ok _ W ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz Hcl Hv Hcnt Hv2 LY IMG Hsp DPOST Hkz Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def).
Local Abbreviation FACTS_ok := (@AFj0.FACTS_ok _ W ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz Hcl Hv Hcnt Hjb Hv2 LY IMG Hn Hsp DPOST Hkz Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def).
Local Abbreviation SEED_ok := (@AFj0.SEED_ok _ _ W ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz Hcl Hv Hcnt Hjb Hv2 LY IMG Hn Htp Hsp DPOST Hkz Nrange B S l off TS HTSD HARm Hpres0 Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def Hj0 Hj1 Hj2 Hj3 Hj4 Hjb_def).
Local Abbreviation CZONE := (@AFix.CZONE ly).
Local Abbreviation abs_cell_ok := (@AFix.abs_cell_ok).
Local Abbreviation abs_cells_ok := (@AFix.abs_cells_ok).
Local Abbreviation const_cells_zone := (@AFix.const_cells_zone ly regs0 mem0 n v kz Hv DPOST B l off TS HTSD).
Local Abbreviation CZONE_untouched := (@AFix.CZONE_untouched _ ly regs0 mem0 n cl cnt v kz Hcl Hv Hcnt Hv2 LY IMG Hsp DPOST Hkz Nrange l off).
Local Abbreviation cell_holds_agree := (@AFix.cell_holds_agree ly regs0 mem0 n v kz Hv DPOST B l off).
Local Abbreviation aview_agree := (@AFix.aview_agree W).
Local Abbreviation const_kept := (@AFix.const_kept _ W ly regs0 mem0 n cl cnt v kz Hcl Hv Hcnt Hv2 LY IMG Hsp DPOST Hkz Nrange B l off TS HTSD).
Local Abbreviation depot_ids_bound := (@AFix.depot_ids_bound ly regs0 mem0 n v kz Hv DPOST B l off TS).
Local Abbreviation depot_mem_ok_agree := (@AFix.depot_mem_ok_agree ly regs0 mem0 n v kz Hv DPOST B l off TS).
Local Abbreviation depot_ok_ext := (@AFix.depot_ok_ext ly B).
Local Abbreviation depot_at0 := (@AFix.depot_at0 _ W ly regs0 mem0 n cl cnt v jb kz Hcl Hv Hcnt Hjb Hsp DPOST Hkz Nrange B S HARm).
Local Abbreviation DPOST3 := (@AFix.DPOST3 _ _ W ly regs0 ch B S AD3j.as_const_g2f).
Local Abbreviation at_RET_at := (@AFis.at_RET_at _ _ W ly regs0 mem0 md0 n cl cnt v jb kz DPOST).
Local Abbreviation D1W_ok := (@AFix.D1W_ok _ _ W ly regs0 mem0 n ch cl cnt v jb kz Hcl Hv Hcnt Hjb Hv2 LY IMG Hsp DPOST Hkz Nrange B S l off TS HTSD HARm Hgp).
Local Abbreviation st_popped := (@AFix.st_popped).
Local Abbreviation new_chunk := (@AFix.new_chunk).
Local Abbreviation st_final := (@AFix.st_final).
Local Abbreviation Kc_user := (@AFix.Kc_user ly regs0 mem0 n ch cl v kz Hcl DPOST Hkz Nrange B S l off Hoff_def).
Local Abbreviation MPF := (@AFix.MPF ly regs0 n ch cl B S l off).
Local Abbreviation AR_final_stmt := (@AFix.AR_final_stmt _ _ W ly regs0 mem0 md0 n ch cl cnt v jb kz DPOST B S l off).
Local Abbreviation WR_owned := (@AFix.WR_owned _ W ly regs0 mem0 n ch cl cnt v csz jb kz Hcl Hv Hcnt Hjb Hv2 LY IMG Hsp DPOST Hkz Nrange B S l off TS HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def).
Local Abbreviation LEAF_ok := (@AFix.LEAF_ok _ _ W ly regs0 mem0 md0 n ch cl cnt v csz jb kz Hcl Hv Hcnt Hjb Hv2 LY IMG Hsp DPOST Hkz Nrange mat0 B S l off TS HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def).
Local Abbreviation Kc_fresh := (@AFix.Kc_fresh _ W ly regs0 mem0 n ch cl cnt v kz Hcl Hv Hv2 DPOST Hkz Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation upd_chunk_fresh := (@AFix.upd_chunk_fresh n cl off).
Local Abbreviation SF_chunks := (@AFix.SF_chunks _ W ly regs0 mem0 n ch cl cnt v kz Hcl Hv Hv2 DPOST Hkz Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation SF_same := (@AFix.SF_same ly regs0 n ch cl S l off).
Local Abbreviation SF_sec_extents := (@AFix.SF_sec_extents _ W ly regs0 mem0 n ch cl cnt v kz Hcl Hv Hv2 DPOST Hkz Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation SF_sec_live := (@AFix.SF_sec_live _ W ly regs0 mem0 n ch cl cnt v kz Hcl Hv Hv2 DPOST Hkz Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation SF_ledger := (@AFix.SF_ledger _ W ly regs0 mem0 n ch cl cnt v kz Hcl Hv Hv2 DPOST Hkz Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation cell_holds_agree2 := (@AFix.cell_holds_agree2 ly regs0 mem0 n ch cl cnt v jb kz Hcl Hv Hcnt Hjb Hsp DPOST Hkz Nrange B S l off).
Local Ltac addr_tac :=
cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi];
rewrite ?EaT, ?EaC, ?EaTOP, ?EaSB, ?E2; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, w64, ly_bot, kStackSpan, t_unwinding, t_cache, t_stats, TFIB_IMG_END, UNW_STK, BST_SIZE, ASTACK, IFRAME, kHighMemBeg, kHighMemEnd, ASAN_CEIL, YImgTop.IMG_LO, YImgTop.IMG_TOP in *;
rewrite ?unsigned_lit_small by zlia; zlia.
Local Ltac denot_tac :=
cbn [sv_denot]; rewrite ?EaT, ?EaC, ?EaTOP, ?EaSB, ?E2; unfold w64, ly_bot, kStackSpan in *;
first [ rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| rewrite Zbv_add_unsigned; f_equal; zlia
| rewrite unsigned_lit_small by zlia; f_equal; zlia
| reflexivity ].
Let rd0 : reader := aview tfibsegs (w_H W) mem0.
Let WF := am_wf B ly S rd0 HARm.
Let Kc : chunk := new_chunk cl off n.
Let SF (z : Z) : astate := st_final S cl l off n tr z.
Lemma zrange_dec : forall lo hi a : Z, {lo <= a < hi} + {~ (lo <= a < hi)}.
Proof.
intros lo hi a. destruct (Z_le_dec lo a) as [H1|H1]; [destruct (Z_lt_dec a hi) as [H2|H2]; [left; exact (conj H1 H2) | right; intros [_ H]; exact (H2 H)] | right; intros [H _]; exact (H1 H)].
Qed.
Lemma apresent_word : forall (Hh : word -> bool) mem a, apresent Hh mem a <-> apresent Hh mem (bv_unsigned (Z_to_bv 64 a)).
Proof. intros Hh mem a. unfold apresent. rewrite Z_to_bv_bv_unsigned. split; intros H; exact H. Qed.
Lemma val_mem_cell : forall mem e (w : nat) e',
val_mem tfibsegs (mrestrict (w_H W) mem) (aeval B ly e) w (aeval B ly e') -> cell_holds B ly (aview tfibsegs (w_H W) mem) (ACell e w (AV e')).
Proof.
intros mem e w e' HV k Hk. cbn [c_at c_val c_w]. unfold aview. rewrite (HV k Hk). cbn [option_map].
rewrite <- le_byte_eq. rewrite unsigned_lit_small8; [reflexivity|]. unfold YG0f.le_byte. apply Z.mod_pos_bound. zlia.
Qed.
Lemma le_byte_1_0 : forall x, 0 <= x < 256 -> YO0f.le_byte x 1 0 = x.
Proof.
intros x Hx. unfold YO0f.le_byte. change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0)%Z with 0.
rewrite Z.shiftr_0_r, Z.mod_mod by zlia. apply Z.mod_small. exact Hx.
Qed.
Lemma find_chunk_at_app1 : forall l1 l2 g k, find_chunk_at B ly l1 g = Some k -> find_chunk_at B ly (l1 ++ l2) g = Some k.
Proof.
induction l1 as [|k' t IH]; intros l2 g k H; [discriminate|]. cbn [find_chunk_at app] in *.
destruct (andb _ _); [exact H | exact (IH l2 g k H)].
Qed.
Lemma find_chunk_at_app2 : forall l1 l2 g, find_chunk_at B ly l1 g = None -> find_chunk_at B ly (l1 ++ l2) g = find_chunk_at B ly l2 g.
Proof.
induction l1 as [|k' t IH]; intros l2 g H; [reflexivity|]. cbn [find_chunk_at app] in *.
destruct (andb _ _); [discriminate | exact (IH l2 g H)].
Qed.
Lemma In_combine_seq_app : forall (l0 : list Z) (x : Z) s p, In p (combine (seq s (length l0)) l0) -> In p (combine (seq s (length l0 + 1)) (l0 ++ [x])).
Proof.
induction l0 as [|y t IH]; intros x s p H; [destruct H|]. cbn [length combine seq app Nat.add] in *.
destruct H as [H|H]; [left; exact H | right]. apply IH. exact H.
Qed.
Lemma Kc_facts : ck_base B ly Kc = Kv /\ ck_rz Kc = RZ /\ ck_n Kc = n /\ ck_extent Kc = class_size cl /\ ck_state Kc = CAllocated /\
ck_beg Kc = PPrim (region_off cl + off) /\ aeval B ly (sptr_exp (ck_beg Kc)) = Kv.
Proof.
pose proof casek_sizes as (_ & RS & _ & _ & FP & _ & RQ).
unfold Kc, new_chunk, ck_base, ck_rz, ck_n, ck_extent. cbn [ck_beg ck_req ck_state]. rewrite RS, RQ, FP, <- Hcl_class, <- Kv_is_sptr.
repeat split; try reflexivity. rewrite Kv_is_sptr. reflexivity.
Qed.
Lemma NLOf : 49 <= n <= 64512 /\ 32 <= RZ <= 1024 /\ RZ = RZ / 8 * 8 /\ 4 <= RZ / 8 <= 128.
Proof. pose proof RZ_num as (X1 & X2 & X3 & X4 & X5). clear - X1 X2 X3 X4 X5. repeat split; zlia. Qed.
Section b0.
Variables (odd : bool) (z : Z) (regs' : bvmap 5 word) (mem' memD : word -> option byte) (mat : list word).
Variables (zn ln zs ls : Z).
Let FZ (a : Z) : Prop := (zn <= a < zn + ln) \/ (zs <= a < zs + ls).
Hypothesis FZD : forall a, FZ a -> ~ aowned B ly S a /\ ~ CZONE a /\ ~ (kLowShadowBeg <= a < kHighShadowEnd).
Let rd' : reader := aview tfibsegs (w_H W) mem'.
Let rdD : reader := aview tfibsegs (w_H W) memD.
Let m' := mrestrict (w_H W) mem'.
Hypothesis Hodd : odd = true <-> n mod 8 <> 0.
Hypothesis MP : MPF z.
Hypothesis HAR : AR tfibsegs B ly S W mem0 md0.
Hypothesis AOK : aok S (KDepot tr) z.
Hypothesis DEPD : st_depot S <> [] -> depot_mem_ok B ly (depot_after z tr S) rdD.
Hypothesis CSTD : Forall (cell_holds B ly rdD) (AD3j.as_const_g2f B ly).
Hypothesis PRD : forall a, DZONE a \/ FZ a -> apresent (w_H W) mem0 a -> apresent (w_H W) memD a.
Hypothesis EQD : forall x : word, DZONE (bv_unsigned x) \/ FZ (bv_unsigned x) -> mem' x = memD x.
Hypothesis MEQF : forall x : word, ~ WIN odd (bv_unsigned x) -> ~ DZONE (bv_unsigned x) -> ~ FZ (bv_unsigned x) -> ~ (Kv + RZ <= bv_unsigned x < Kv + RZ + n) ->
~ (SUv <= bv_unsigned x < SUv + N8D / 8) -> mem' x = mem0 x.
Hypothesis PRS : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem' a.
Hypothesis PRW : forall a, WINT a \/ (Kv <= a < Kv + RZ + n) \/ PBW odd a -> apresent (w_H W) mem' a.
Hypotheses (V1 : val_mem tfibsegs m' Kv 8 0xCC6E96B9CC6E96B9) (V2 : val_mem tfibsegs m' (Kv + 8) 8 (Kv + RZ - 16))
(V3 : val_mem tfibsegs m' (Kv + RZ - 16) 1 2) (V4 : val_mem tfibsegs m' (Kv + RZ - 15) 1 (hdr_byte1 jb))
(V5 : val_mem tfibsegs m' (Kv + RZ - 14) 2 0) (V6 : val_mem tfibsegs m' (Kv + RZ - 12) 4 n)
(V7 : val_mem tfibsegs m' Pv 4 (cnt - 1)) (V8 : val_mem tfibsegs m' (T + t_unwinding) 1 0)
(V9 : forall x : word, SUv <= bv_unsigned x < SUv + N8D / 8 -> mem' x = Some (Z_to_bv 8 0))
(V10 : odd = true -> val_mem tfibsegs m' PBv 1 (n mod 8))
(V11 : forall x : word, Kv + RZ <= bv_unsigned x < Kv + RZ + FILv -> mem' x = Some (Z_to_bv 8 190)).
Let MA : ARm B ly S rd0 := proj1 HAR.
Lemma AGREE0 : forall a, 0 <= a < 2 ^ 64 -> ~ WIN odd a -> ~ DZONE a -> ~ FZ a -> ~ (Kv + RZ <= a < Kv + RZ + n) ->
~ (SUv <= a < SUv + N8D / 8) -> rd' a = rd0 a.
Proof. intros a Ra N1 N2 N5 N3 N4. unfold rd', rd0. apply aview_same. apply MEQF; rewrite unsigned_lit_small by exact Ra; assumption. Qed.
Lemma AGREED : forall a, 0 <= a < 2 ^ 64 -> DZONE a -> rd' a = rdD a.
Proof. intros a Ra Hd. unfold rd', rdD. apply aview_same. apply EQD. rewrite unsigned_lit_small by exact Ra. left. exact Hd. Qed.
(* The two new blocks (FZ) miss every owned byte, every const-cell byte and the shadow bands (from FZD). *)
Lemma FZ_owned : forall a, aowned B ly S a -> ~ FZ a.
Proof. intros a Ho Hf. exact (proj1 (FZD a Hf) Ho). Qed.
Lemma FZ_czone : forall a, CZONE a -> ~ FZ a.
Proof. intros a Hc Hf. exact (proj1 (proj2 (FZD a Hf)) Hc). Qed.
Lemma FZ_band : forall a, kLowShadowBeg <= a < kHighShadowEnd -> ~ FZ a.
Proof. intros a Hb Hf. exact (proj2 (proj2 (FZD a Hf)) Hb). Qed.

Definition SHX (a : Z) : Prop := (SUv <= a < SUv + N8D / 8) \/ PBW odd a.
Definition XC (a : Z) : Prop := WINT a \/ (Kv <= a < Kv + RZ + n) \/ SHX a \/ DZONE a.
Lemma AGX : forall a, aowned B ly S a -> ~ XC a -> rd' a = rd0 a.
Proof.
intros a Ho Hx. pose proof (AR_owned_low_law_ok tfibsegs B ly S W mem0 md0 a HAR Ho) as Ra.
ceil.
pose proof (AR_stack_law_ok tfibsegs B ly S W mem0 md0 a HAR) as NS.
destruct Hsp as (S1 & S2 & S3 & S4). unfold XC, SHX in Hx.
apply AGREE0.
- clear - Ra CR0. zlia.
- intros Hw. unfold WIN in Hw. destruct Hw as [Hs|[Hw|[Hw|Hw]]].
+ apply NS; [|exact Ho]. clear - Hs S1 S3. unfold sp0 in *. zlia.
+ apply Hx. left. exact Hw.
+ apply Hx. right; left. pose proof NLOf as (Nlo & RZr & _). pose proof derived_ranges as DR'. clear - Hw Nlo RZr DR'. zlia.
+ apply Hx. right; right; left. right. exact Hw.
- intros Hd. apply Hx. right; right; right. exact Hd.
- exact (FZ_owned a Ho).
- intros Hu. apply Hx. right; left. pose proof NLOf as (Nlo & RZr & _). clear - Hu RZr. zlia.
- intros Hs. apply Hx. right; right; left. left. exact Hs.
Qed.
Lemma XC_where : forall a, XC a ->
(T <= a < T + kThreadObjSize /\ WINT a) \/ (Kv <= a < Kv + class_size cl) \/ (0x2008fff7000 <= a < kHighMemBeg /\ SHX a) \/
(0x170408 <= a < 0x5c0b90) \/ (fst (nb_ext ly) <= a < fst (nb_ext ly) + snd (nb_ext ly)) \/ (fst (sb_ext ly) <= a < fst (sb_ext ly) + snd (sb_ext ly)).
Proof.
intros a Hx. pose proof derived_ranges as DR. pose proof cls_geom as (_ & _ & _ & _ & K5 & _).
unfold XC, SHX, WINT, PBW, DZONE, KnBlockExt.DZONE_at, AD3j.tfib_dzone_lo, AD3j.tfib_dzone_hi in Hx. unfold t_unwinding, t_cache, kThreadObjSize in *.
decompose [or and] Hx; clear Hx.
- left. split; [zlia | unfold WINT; unfold t_cache; zlia].
- left. split; [zlia | unfold WINT; zlia].
- left. split; [zlia | unfold WINT; zlia].
- left. split; [zlia | unfold WINT; unfold t_unwinding; zlia].
- right; left. zlia.
- right; right; left. split; [zlia | left; zlia].
- right; right; left. split; [zlia | right; split; [assumption | zlia]].
- do 3 right. left. zlia.
- do 4 right. left. zlia.
- do 5 right. zlia.
Qed.
Lemma Z_low : forall a, TFIB_IMG_LO <= a < 0x170408 -> ~ XC a.
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
clear - Ha Hs Hx F1 G1 NBhi SBhi. numconst. unfold zone3cases in *. numconst. unfold T in *. destruct Hx as [Hx|[Hx|[[_ Hx]|Hx]]]; [zlia | zlia | exact (Hs Hx) | zlia].
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
~ (fst (nb_ext ly) <= a < fst (nb_ext ly) + snd (nb_ext ly)) -> ~ (fst (sb_ext ly) <= a < fst (sb_ext ly) + snd (sb_ext ly)) -> ~ XC a.
Proof.
intros a Ha NT NP NNB NSB Hx. apply XC_where in Hx. pose proof Kv_geom as (G1 & G2 & G3 & G4 & G5).
clear - Ha NT NP NNB NSB Hx G4 G5. numconst. decompose [and or] Hx; clear Hx; first [zlia | tauto].
Qed.
Lemma Z_out : forall x sz a, zone3 x sz -> x <= a < x + sz -> ~ (T <= a < T + kThreadObjSize) -> ~ (ly_prim ly <= a < ly_prim ly + kPrimResvSize) ->
~ (fst (nb_ext ly) <= a < fst (nb_ext ly) + snd (nb_ext ly)) -> ~ (fst (sb_ext ly) <= a < fst (sb_ext ly) + snd (sb_ext ly)) -> ~ XC a.
Proof.
intros x sz a Z3 Ha NT NP NNB NSB Hx. apply XC_where in Hx. pose proof Kv_geom as (G1 & G2 & G3 & G4 & G5).
clear - Z3 Ha NT NP NNB NSB Hx G4 G5. numconst. unfold zone3cases in *. numconst. decompose [and or] Hx; clear Hx; first [zlia | tauto].
Qed.
Lemma Z_ext : forall (i : nat) e a, nth_error (owned_extents ly) i = Some e -> (i = 1 \/ i = 3 \/ i = 6)%nat ->
fst e <= a < fst e + snd e -> ~ XC a.
Proof.
intros i e a He Hi Ha. pose proof (lo_app ly LY) as HI. pose proof (lo_disj ly LY) as HD.
pose proof (Forall_nth' _ _ i _ HI He) as IH. cbv beta in IH.
assert (He2 : nth_error (static_extents ly) i = Some e) by (unfold static_extents; rewrite nth_error_app1 by (cbn; zlia); exact He).
assert (D : forall j e', nth_error (static_extents ly) j = Some e' -> (j = 0 \/ j = 2 \/ j = 4 \/ j = 5 \/ j = 9)%nat -> zdisjoint e e').
{ intros j e' He' Hj.
destruct (Nat.lt_ge_cases i j) as [L|L].
- replace j with (i + Datatypes.S (j - i - 1))%nat in He' by zlia. exact (pairwise_ij _ _ _ _ _ _ HD He2 He').
- apply zdisjoint_sym. assert (j <> i) by (intros ->; zlia). replace i with (j + Datatypes.S (i - j - 1))%nat in He2 by zlia. exact (pairwise_ij _ _ _ _ _ _ HD He' He2). }
pose proof (D 0%nat _ eq_refl ltac:(zlia)) as D0. pose proof (D 2%nat _ eq_refl ltac:(zlia)) as D2.
pose proof (D 4%nat _ (nb_ext_nth_st ly) ltac:(zlia)) as D4. pose proof (D 5%nat _ (sb_ext_nth_st ly) ltac:(zlia)) as D5. pose proof (D 9%nat _ eq_refl ltac:(zlia)) as D9.
assert (SZ : 0 <= snd e) by (destruct Hi as [-> |[-> | ->]]; injection He as <-; cbn; unfold kPtrArrayResv, kFakeStackSize; zlia).
pose proof (zone3_intro ly (fst e) (snd e) IMG SZ IH ltac:(destruct e; exact D9)) as Z3.
unfold zdisjoint in D0, D2, D4, D5. cbn [fst snd] in D0, D2, D4, D5.
apply (Z_out (fst e) (snd e)); unfold T in *; clear - Z3 Ha D0 D2 D4 D5; try exact Z3; numconst; zlia.
Qed.
Lemma Z_sec : forall e a, In e (sec_extents ly S) -> fst e <= a < fst e + snd e -> ~ XC a.
Proof.
intros e a He Ha. pose proof (am_placed _ _ _ _ MA) as [PL PD]. pose proof (proj1 (Forall_forall _ _) PL e He) as (_ & HIA & _).
assert (D : forall e', In e' (static_extents ly) -> zdisjoint e e').
{ intros e' He'. exact (pairwise_In zdisjoint _ e e' (sec_extents ly S) (static_extents ly) eq_refl PD He He'). }
pose proof (D (ly_prim ly, kPrimResvSize) ltac:(unfold static_extents, owned_extents; cbn; tauto)) as D0.
pose proof (D (ly_T ly, kThreadObjSize) ltac:(unfold static_extents, owned_extents; cbn; tauto)) as D2.
pose proof (D (nb_ext ly) (nth_error_In _ 4 (nb_ext_nth_st ly))) as D4.
pose proof (D (sb_ext ly) (nth_error_In _ 5 (sb_ext_nth_st ly))) as D5.
pose proof (D (ly_img ly) ltac:(unfold static_extents; apply in_app_iff; right; cbn; tauto)) as D9.
assert (SZ : 0 <= snd e) by (clear - Ha; zlia).
pose proof (zone3_intro ly (fst e) (snd e) IMG SZ HIA ltac:(destruct e; exact D9)) as Z3.
unfold zdisjoint in D0, D2, D4, D5. cbn [fst snd] in D0, D2, D4, D5.
apply (Z_out (fst e) (snd e)); unfold T in *; clear - Z3 Ha D0 D2 D4 D5; try exact Z3; numconst; zlia.
Qed.
Lemma SHX_bounds : forall a, SHX a -> SHBv + Kv / 8 + RZ / 8 <= a < SHBv + (Kv + class_size cl) / 8.
Proof.
intros a Hs. pose proof cls_geom as (_ & K2 & _ & _ & K5 & _). pose proof Kv_geom as (_ & _ & G3 & _). pose proof derived_ranges as DR. pose proof NLOf as (Nlo & RZr & RZ8 & _).
pose proof (Z.div_mod n 8 ltac:(zlia)) as DM. pose proof (Z.mod_pos_bound n 8 ltac:(zlia)) as MB.
apply Z.mod_divide in K2 as [r Hr]; [|zlia]. apply Z.mod_divide in G3 as [q Hq]; [|zlia].
assert (EK8 : Kv / 8 = 2 * q) by (rewrite Hq; replace (q * 16) with (2 * q * 8) by zlia; apply Z.div_mul; zlia).
assert (EKC : (Kv + class_size cl) / 8 = 2 * q + 4 * r) by (rewrite Hq, Hr; replace (q * 16 + r * 32) with ((2 * q + 4 * r) * 8) by zlia; apply Z.div_mul; zlia).
assert (EN8 : N8D / 8 = n / 8) by (unfold N8D; apply Z.div_mul; zlia).
unfold SHX, PBW in Hs. rewrite EK8, EKC. destruct Hs as [Hs|[Ho Hs]].
- clear - Hs K5 DM MB EK8 Hr Hq Nlo RZr RZ8 DR EN8. unfold SKv in *. zlia.
- apply Hodd in Ho. clear - Ho Hs K5 DM MB EK8 Hr Hq Nlo RZr RZ8 DR EN8. unfold SKv in *. zlia.
Qed.
Lemma PRES_MONO : forall a, apresent (w_H W) mem0 a -> apresent (w_H W) mem' a.
Proof.
assert (G : forall u, 0 <= u < 2 ^ 64 -> apresent (w_H W) mem0 u -> apresent (w_H W) mem' u).
{ pose proof NLOf as (Nlo & RZr & _). pose proof derived_ranges as DR'. clear - EQD PRD PRS PRW V9 MEQF T Nlo RZr DR'. intros u Ru Hp.
destruct (zrange_dec 0x170408 0x5c0b90 u) as [D1|D1].
{ eapply apresent_same; [apply EQD | apply PRD; [|exact Hp]]; [rewrite unsigned_lit_small by exact Ru|]; left; unfold DZONE, KnBlockExt.DZONE_at, AD3j.tfib_dzone_lo, AD3j.tfib_dzone_hi; left; exact D1. }
destruct (zrange_dec (fst (nb_ext ly)) (fst (nb_ext ly) + snd (nb_ext ly)) u) as [D2|D2].
{ eapply apresent_same; [apply EQD | apply PRD; [|exact Hp]]; [rewrite unsigned_lit_small by exact Ru|]; left; unfold DZONE, KnBlockExt.DZONE_at, AD3j.tfib_dzone_lo, AD3j.tfib_dzone_hi; right; left; exact D2. }
destruct (zrange_dec (fst (sb_ext ly)) (fst (sb_ext ly) + snd (sb_ext ly)) u) as [D3|D3].
{ eapply apresent_same; [apply EQD | apply PRD; [|exact Hp]]; [rewrite unsigned_lit_small by exact Ru|]; left; unfold DZONE, KnBlockExt.DZONE_at, AD3j.tfib_dzone_lo, AD3j.tfib_dzone_hi; right; right; exact D3. }
destruct (zrange_dec zn (zn + ln) u) as [D2a|D2a].
{ eapply apresent_same; [apply EQD | apply PRD; [|exact Hp]]; [rewrite unsigned_lit_small by exact Ru|]; right; left; exact D2a. }
destruct (zrange_dec zs (zs + ls) u) as [D2b|D2b].
{ eapply apresent_same; [apply EQD | apply PRD; [|exact Hp]]; [rewrite unsigned_lit_small by exact Ru|]; right; right; exact D2b. }
destruct (zrange_dec (sp0 - ASTACK) sp0 u) as [D4|D4]; [apply PRS; exact D4|].
destruct (zrange_dec Pv (Pv + 4) u) as [D5|D5]; [apply PRW; left; unfold WINT; left; exact D5|].
destruct (zrange_dec (T + 2768) (T + 2824) u) as [D6|D6]; [apply PRW; left; right; left; exact D6|].
destruct (zrange_dec SSLOTv (SSLOTv + 8) u) as [D7|D7]; [apply PRW; left; right; right; left; exact D7|].
destruct (zrange_dec (T + t_unwinding) (T + t_unwinding + 1) u) as [D8|D8]; [apply PRW; left; right; right; right; exact D8|].
destruct (zrange_dec Kv (Kv + RZ + n) u) as [D9|D9]; [apply PRW; right; left; exact D9|].
destruct (zrange_dec (SUv) (SUv + N8D / 8) u) as [D11|D11].
{ destruct Hp as [Hh _]. split; [exact Hh | exists (Z_to_bv 8 0); apply V9; rewrite unsigned_lit_small by exact Ru; exact D11]. }
assert (NW : ~ PBW odd u -> apresent (w_H W) mem' u).
{ intros D10. eapply apresent_same; [|exact Hp]. apply MEQF; rewrite unsigned_lit_small by exact Ru.
- intros [Hs|[Hw|[Hk|Ho]]]; [exact (D4 Hs) | | clear - Hk D9 Nlo RZr DR'; zlia | exact (D10 Ho)].
destruct Hw as [Hw|[Hw|[Hw|Hw]]]; [exact (D5 Hw) | exact (D6 Hw) | exact (D7 Hw) | exact (D8 Hw)].
- intros [Hd|[Hd|Hd]]; [exact (D1 Hd) | exact (D2 Hd) | exact (D3 Hd)].
- intros [Hf|Hf]; [exact (D2a Hf) | exact (D2b Hf)].
- clear - D9 RZr. zlia.
- exact D11. }
destruct odd; [|apply NW; intros [E _]; discriminate].
destruct (zrange_dec PBv (PBv + 1) u) as [D10|D10]; [apply PRW; right; right; split; [reflexivity | exact D10]|].
apply NW. intros [_ Hb]. exact (D10 Hb). }
intros a Hp. apply (proj2 (apresent_word _ _ a)). apply G; [pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 a)) as R; change (bv_modulus 64) with (2 ^ 64) in R; exact R|].
apply (proj1 (apresent_word _ _ a)). exact Hp.
Qed.
Lemma ZKEEP : forall g, g mod 8 = 0 -> in_app g 8 -> hfree ly S g ->
mem' (w64 (shadow_addr g)) = mem0 (w64 (shadow_addr g)).
Proof.
intros g Hg Happ HF. pose proof high_facts as (F1 & F2 & F3 & F4 & F5 & F6 & _). pose proof Kv_range as [K1 K2].
pose proof derived_ranges as (DK1 & _). pose proof NLOf as (Nlo & RF1 & RF8 & _). pose proof blocks_facts as (NBhi & SBhi & _).
pose proof (shadow_addr_band_rw g Happ) as SBg. unfold in_band_rw, kLowShadowEnd in SBg.
pose proof (zone3_apart_hsh _ _ (shadow_addr g) F1) as TH. pose proof (zone3_apart_hsh _ _ (shadow_addr g) NBhi) as NH. pose proof (zone3_apart_hsh _ _ (shadow_addr g) SBhi) as BH.
assert (Hlo : 4096 <= g) by (clear - Happ; unfold in_app in Happ; zlia).
assert (GP : g + 8 <= ly_prim ly \/ ly_prim ly + kPrimResvSize <= g).
{ unfold hfree in HF. pose proof (proj1 (Forall_forall _ _) HF (ly_prim ly, kPrimResvSize)
ltac:(apply in_app_iff; left; unfold static_extents, owned_extents; apply in_app_iff; left; left; reflexivity)) as X. exact X. }
assert (G0 : 0 <= g) by (clear - Hlo; zlia).
assert (KP : ly_prim ly <= Kv /\ Kv + 2 ^ 16 + 4096 <= ly_prim ly + kPrimResvSize) by (clear - F4 F5 K1 K2; unfold kSpaceSize, kPrimResvSize in *; zlia).
assert (AP : forall x y, Kv <= x -> y <= Kv + 2 ^ 16 + 4096 -> shadow_addr g + 1 <= shadow_addr x \/ SHADOW_OFF + y / 8 <= shadow_addr g).
{ intros x y Hx Hy. apply shadow_apart; [exact Hg | exact G0 | clear - Hx KP F3; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, YImgTop.IMG_LO, YImgTop.IMG_TOP in *; zlia | clear - GP KP Hx Hy; zlia]. }
unfold w64. apply MEQF; rewrite unsigned_lit_small by (clear - SBg; unfold kLowShadowBeg, kHighShadowBeg, kHighShadowEnd in SBg; zlia).
-
intros HW. unfold WIN, WINT, PBW in HW. pose proof derived_ranges as DR.
destruct HW as [HW|[HW|[HW|[_ HW]]]].
+ pose proof Hsp as (S1 & _). pose proof (lo_top ly LY) as (_ & _ & _ & T4 & _ & _ & T7). clear - HW SBg F3 S1 T7. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, kHighMemEnd, ASTACK, YImgTop.IMG_LO, YImgTop.IMG_TOP in *. unfold sp0 in *. zlia.
+ clear - HW SBg TH DR T. unfold zone3, kThreadObjSize, TFIB_IMG_LO, kLowShadowBeg, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, t_cache, t_unwinding, YImgTop.IMG_LO, YImgTop.IMG_TOP in *. unfold T in *. zlia.
+ clear - HW SBg DK1 Nlo RF1. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, Uv, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, YImgTop.IMG_LO, YImgTop.IMG_TOP in *. zlia.
+ destruct (AP (Kv + RZ + N8D) (Kv + RZ + N8D + 8) ltac:(clear - Nlo RF1 DR; zlia) ltac:(clear - Nlo RF1 DR; zlia)) as [X|X];
unfold PBv, SHBv in HW; unfold shadow_addr, SHADOW_OFF in *; clear - HW X; [zlia|].
replace (Kv + RZ + N8D + 8) with (Kv + RZ + N8D + 1 * 8) in X by zlia. rewrite Z.div_add in X by zlia. zlia.
-   intros Hd. unfold DZONE, KnBlockExt.DZONE_at, AD3j.tfib_dzone_lo, AD3j.tfib_dzone_hi in Hd. clear - Hd SBg NH BH. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, kNodesBlockSize, kStoreBlockSize, YImgTop.IMG_LO, YImgTop.IMG_TOP in *. zlia.
- apply FZ_band. clear - SBg. unfold kLowShadowBeg, kHighShadowBeg, kHighShadowEnd in *. zlia.
-   clear - SBg DK1 Nlo RF1. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, YImgTop.IMG_LO, YImgTop.IMG_TOP in *. zlia.
-
destruct (AP Uv (Uv + N8D) ltac:(unfold Uv; clear - RF1; zlia) ltac:(unfold Uv; pose proof derived_ranges as DR; clear - Nlo RF1 DR; zlia)) as [X|X];
unfold SUv, SHBv; unfold shadow_addr, SHADOW_OFF in *; clear - X; [zlia|].
intros [_ R].
assert ((Uv + N8D) / 8 >= Uv / 8 + N8D / 8)%Z by (apply Z.le_ge; apply Z.div_le_lower_bound; [zlia|]; pose proof (Z.mul_div_le Uv 8 ltac:(zlia)); pose proof (Z.mul_div_le N8D 8 ltac:(zlia)); zlia). zlia.
Qed.
Lemma BANDKEEP : forall a, in_band_rw a -> mem0 (w64 a) <> None -> mem' (w64 a) <> None.
Proof.
pose proof derived_ranges as (DK1 & _). pose proof NLOf as (Nlo & RF1 & _). pose proof blocks_facts as (NBhi & SBhi & _).
clear - MEQF FZD PRS PRW V9 T DK1 Nlo RF1 NBhi SBhi. intros a Ha H0.
pose proof (zone3_apart_hsh _ _ a NBhi) as NH. pose proof (zone3_apart_hsh _ _ a SBhi) as BH.
unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, YImgTop.IMG_LO, YImgTop.IMG_TOP in NH, BH.
assert (Ra : 0 <= a < 2 ^ 64) by (clear - Ha; zlia).
assert (PW : apresent (w_H W) mem' a -> mem' (w64 a) <> None) by (intros [_ [b Hb]]; unfold w64; rewrite Hb; discriminate).
destruct (zrange_dec SUv (SUv + N8D / 8) a) as [D11|D11].
{ rewrite (V9 (w64 a)); [discriminate | unfold w64; rewrite unsigned_lit_small by exact Ra; exact D11]. }
destruct (zrange_dec (sp0 - ASTACK) sp0 a) as [D4|D4]; [exact (PW (PRS a D4))|].
assert (NW : ~ WIN odd a \/ apresent (w_H W) mem' a).
{ unfold WIN. destruct (zrange_dec Kv (Kv + RZ + n) a) as [D9|D9]; [right; apply PRW; right; left; exact D9|].
destruct odd.
- destruct (zrange_dec PBv (PBv + 1) a) as [D10|D10]; [right; apply PRW; right; right; split; [reflexivity | exact D10]|].
assert (NT : ~ WINT a \/ apresent (w_H W) mem' a).
{ unfold WINT. destruct (zrange_dec Pv (Pv + 4) a) as [D5|D5]; [right; apply PRW; left; unfold WINT; tauto|].
destruct (zrange_dec (T + 2768) (T + 2824) a) as [D6|D6]; [right; apply PRW; left; unfold WINT; tauto|].
destruct (zrange_dec SSLOTv (SSLOTv + 8) a) as [D7|D7]; [right; apply PRW; left; unfold WINT; tauto|].
destruct (zrange_dec (T + t_unwinding) (T + t_unwinding + 1) a) as [D8|D8]; [right; apply PRW; left; unfold WINT; tauto|]. left; tauto. }
destruct NT as [NT|NT]; [|right; exact NT]. left. intros [Hs|[Hw|[Hk|[_ Ho]]]]; [exact (D4 Hs) | exact (NT Hw) | unfold Uv in Hk; clear - Hk D9 Nlo RF1; zlia | exact (D10 Ho)].
- assert (NT : ~ WINT a \/ apresent (w_H W) mem' a).
{ unfold WINT. destruct (zrange_dec Pv (Pv + 4) a) as [D5|D5]; [right; apply PRW; left; unfold WINT; tauto|].
destruct (zrange_dec (T + 2768) (T + 2824) a) as [D6|D6]; [right; apply PRW; left; unfold WINT; tauto|].
destruct (zrange_dec SSLOTv (SSLOTv + 8) a) as [D7|D7]; [right; apply PRW; left; unfold WINT; tauto|].
destruct (zrange_dec (T + t_unwinding) (T + t_unwinding + 1) a) as [D8|D8]; [right; apply PRW; left; unfold WINT; tauto|]. left; tauto. }
destruct NT as [NT|NT]; [|right; exact NT]. left. intros [Hs|[Hw|[Hk|[E _]]]]; [exact (D4 Hs) | exact (NT Hw) | unfold Uv in Hk; clear - Hk D9 Nlo RF1; zlia | discriminate E]. }
destruct NW as [NW|PWa]; [|exact (PW PWa)].
unfold w64. rewrite MEQF; [exact H0 | | | | |]; rewrite ?unsigned_lit_small by exact Ra.
- exact NW.
- intros Hd. unfold DZONE, KnBlockExt.DZONE_at, AD3j.tfib_dzone_lo, AD3j.tfib_dzone_hi in Hd. clear - Hd Ha NH BH. unfold kNodesBlockSize, kStoreBlockSize in *. zlia.
- apply FZ_band. clear - Ha. unfold kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *. zlia.
- clear - Ha DK1 Nlo RF1. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, YImgTop.IMG_LO, YImgTop.IMG_TOP in *. zlia.
- exact D11.
Qed.
Lemma VIS_MONO : forall a, rd0 a <> None -> rd' a <> None.
Proof.
intros a HV. unfold rd', rd0, aview, mbyte in *.
destruct (seg_rom tfibsegs (Z_to_bv 64 a)) as [r|] eqn:ER.
- destruct (mrestrict (w_H W) mem' (Z_to_bv 64 a)); cbn; discriminate.
- assert (Hp : apresent (w_H W) mem0 a).
{ unfold mrestrict in HV. unfold apresent. destruct (w_H W (Z_to_bv 64 a)); [exfalso; apply HV; reflexivity|].
split; [reflexivity|]. destruct (mem0 (Z_to_bv 64 a)) as [b|]; [exists b; reflexivity | exfalso; apply HV; reflexivity]. }
destruct (PRES_MONO a Hp) as [Hh [b Hb]]. unfold mrestrict. rewrite Hh, Hb. cbn. discriminate.
Qed.
Definition loc_ok (lo len : Z) : Prop := forall a, lo <= a < lo + len -> ~ XC a.
Lemma keep_cells : forall lst lo len, loc_ok lo len -> incl lst (acells B ly S) ->
Forall (fun c => lo <= aeval B ly (c_at c) /\ aeval B ly (c_at c) + Z.max 1 (Z.of_nat (c_w c)) <= lo + len) lst ->
Forall (cell_holds B ly rd') lst.
Proof.
intros lst lo len LOC INC RNG. apply Forall_forall. intros c Hc.
pose proof (proj1 (Forall_forall _ _) RNG c Hc) as [R1 R2]. cbv beta in R1, R2.
apply (YG0q.cell_holds_agree B ly rd0); [exact (proj1 (Forall_forall _ _) (am_cells _ _ _ _ MA) c (INC c Hc))|].
intros k Hk. apply AGX.
- exact (proj1 (Forall_forall _ _) (acells_owned B ly S rd0 MA) c (INC c Hc) k Hk).
- apply LOC. zlia.
Qed.
Lemma keep_cell : forall c lo len, loc_ok lo len -> In c (acells B ly S) ->
lo <= aeval B ly (c_at c) -> aeval B ly (c_at c) + Z.max 1 (Z.of_nat (c_w c)) <= lo + len -> cell_holds B ly rd' c.
Proof.
intros c lo len LOC Hc R1 R2. exact (proj1 (Forall_forall _ _) (keep_cells [c] lo len LOC ltac:(intros x [<-|[]]; exact Hc) ltac:(constructor; [split; assumption | constructor])) c (or_introl eq_refl)).
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
- intros c. unfold reg. rewrite Rregs. reflexivity.
- intros c Hc Hne. unfold cache. rewrite Rcache. apply znth_zupd_other; [pose proof cl_range; zlia | exact Hc | congruence].
- unfold cache at 1. rewrite Rcache. apply znth_zupd_same; [pose proof cl_range; zlia|]. rewrite (wf_len_cache _ _ _ _ _ WF). pose proof cl_range. zlia.
- unfold frames. rewrite Rfs. reflexivity.
- rewrite Rdep. unfold depot_after. destruct (z =? 0); reflexivity.
Qed.
Ltac fcons' := apply Forall_cons; [cbn; zlia|].
Lemma val_mem_at : forall a a' (w : nat) x, a = a' -> val_mem tfibsegs m' a' w x -> val_mem tfibsegs m' a w x.
Proof. intros a a' w x -> H. exact H. Qed.
Lemma cells_regions : Forall (cell_holds B ly rd') (flat_map (region_cells (SF z)) (zseq 1 31)).
Proof.
pose proof SF_parts as (Rreg & _). apply Forall_flat_map'. intros c Hc. apply zseq_In in Hc.
replace (region_cells (SF z) c) with (region_cells S c) by (unfold region_cells; rewrite Rreg; reflexivity).
pose proof high_facts as (F1 & F2 & F3 & F4 & F5 & _). pose proof Kv_range as [KR1 KR2]. pose proof cls_geom as (_ & _ & K3 & _).
apply (keep_cells _ (ly_space ly + kRegionInfoOff) 4096).
- intros a Ha. apply Z_prim; clear - Ha F3 F4 F5 KR1 KR2 K3; unfold kRegionInfoOff, kMaxSize in *; numconst; zlia.
- intros x Hx. unfold acells. apply in_app_iff. left. apply in_flat_map. exists c. split; [apply In_zseq; zlia | exact Hx].
- unfold region_cells, kRegionInfoOff. repeat fcons'. apply Forall_nil.
Qed.
Lemma cells_caches : Forall (cell_holds B ly rd') (flat_map (cache_cells (SF z)) (zseq 1 31)).
Proof.
pose proof SF_parts as (_ & Rinit & Rother & Rcl & _). apply Forall_flat_map'. intros c Hc. apply zseq_In in Hc.
pose proof derived_ranges as DR. pose proof cl_range as CR.
destruct (Z.eq_dec c cl) as [->|Hne].
-
unfold cache_cells. rewrite Rinit, Hinited, Rcl. cbn [pc_chunks pc_max].
assert (INC : forall x, In x (cache_cells S cl) -> In x (acells B ly S)) by (intros x Hx; exact (In_acells_cache x Hx)).
unfold cache_cells in INC. rewrite Hinited, Hcache in INC.
assert (LOC : loc_ok (Pv + 4) 76).
{ intros a Ha. apply Z_T; unfold WINT, Pv in *; unfold T in *; clear - Ha DR CR; numconst; zlia. }
pose proof off_facts as (_ & _ & _ & _ & _ & _ & _ & CN & _).
constructor.
{ apply val_mem_cell. apply (val_mem_at _ Pv); [cbn; unfold Pv, T; numconst; zlia|]. cbn [aeval].
replace (Z.of_nat (length l)) with (cnt - 1) by zlia. exact V7. }
constructor. { apply (keep_cell _ (Pv + 4) 76 LOC); [apply INC; right; left; reflexivity | cbn; unfold Pv, T; numconst; zlia | cbn; unfold Pv, T; numconst; zlia]. }
constructor. { apply (keep_cell _ (Pv + 4) 76 LOC); [apply INC; right; right; left; reflexivity | cbn; unfold Pv, T; numconst; zlia | cbn; unfold Pv, T; numconst; zlia]. }
apply Forall_forall. intros x Hx. apply in_map_iff in Hx as ([i vv] & <- & Hiv).
pose proof Hiv as Hi. apply in_combine_l in Hi. apply in_seq in Hi.
apply (keep_cell _ (Pv + 4) 76 LOC).
+ apply INC. right; right; right. apply in_map_iff. exists (i, vv). split; [reflexivity|].
rewrite length_app. cbn [length]. apply In_combine_seq_app. exact Hiv.
+ cbn. unfold Pv. unfold T in *. clear - Hi CN. numconst. zlia.
+ cbn. unfold Pv. unfold T in *. clear - Hi CN Hcnt. numconst. zlia.
-
replace (cache_cells (SF z) c) with (cache_cells S c) by (unfold cache_cells; rewrite Rinit, (Rother c) by zlia; reflexivity).
apply (keep_cells _ (T + t_cache + 80 * c) 80).
+ intros a Ha. apply Z_T; unfold WINT, Pv in *; unfold T in *; clear - Ha Hc Hne DR CR; numconst; zlia.
+ intros x Hx. unfold acells. apply in_app_iff. right. apply in_app_iff. left. apply in_flat_map. exists c. split; [apply In_zseq; zlia | exact Hx].
+ unfold cache_cells. pose proof (wf_classes _ _ _ _ _ WF c ltac:(zlia)) as CL. pose proof (wr_cache _ _ _ _ _ _ CL) as WC.
pose proof (class_ok c ltac:(zlia)) as (_ & _ & _ & K4 & _). unfold T.
destruct (st_cache_inited S).
* destruct WC as [PM PL]. unfold t_cache. repeat fcons'. apply Forall_forall. intros x Hx. apply in_map_iff in Hx as ([i vv] & <- & Hiv).
apply in_combine_l in Hiv. apply in_seq in Hiv. cbn. zlia.
* unfold t_cache. repeat fcons'. apply Forall_nil.
Qed.
Lemma cells_chunks : Forall (cell_holds B ly rd') (flat_map chunk_cells (st_chunks (SF z))).
Proof.
unfold SF. rewrite SF_chunks, flat_map_app. apply Forall_app. split.
-
apply Forall_flat_map'. intros k Hk.
pose proof (chunk_facts B ly S rd0 k MA Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
pose proof (req_size_bounds (ck_req k) ltac:(zlia)) as (Q1 & Q2 & Q3).
apply (keep_cells _ (ck_base B ly k) (ck_rz k)).
+ intros a Ha. destruct (extent_zone B ly S rd0 k MA Hk) as [[X1 X2]|(m & len & Hin & X1 & X2)].
* apply Z_prim; [clear - Ha X1 X2 G8 Q2; zlia|]. intros HK. pose proof (cached_vs_chunk k Hk) as D. clear - Ha HK D G8 Q2. zlia.
* apply (Z_sec (m, len)); [exact Hin | cbn [fst snd]; clear - Ha X1 X2 G8 Q2; unfold kPage in *; zlia].
+ intros x Hx. unfold acells. do 2 (apply in_app_iff; right). apply in_app_iff; left. apply in_flat_map. exists k. split; [exact Hk | exact Hx].
+ assert (EA : forall d, aeval B ly (aoff (sptr_exp (ck_beg k)) d) = ck_base B ly k + d).
{ intros d. unfold ck_base, sptr_addr. destruct (ck_beg k) as [|o|r o|c p]; try solve [destruct GG]; cbn; zlia. }
assert (EA2 : forall d d', aeval B ly (aoff (aoff (sptr_exp (ck_beg k)) d) d') = ck_base B ly k + d + d').
{ intros d d'. unfold ck_base, sptr_addr. destruct (ck_beg k) as [|o|r o|c p]; try solve [destruct GG]; cbn; zlia. }
assert (EA0 : aeval B ly (sptr_exp (ck_beg k)) = ck_base B ly k) by reflexivity.
clear GG. unfold chunk_cells, kChunkHeaderSize. apply Forall_app. split.
* repeat (apply Forall_cons; [cbn [c_at c_w z1 z2 z4 c1 c2 c4]; rewrite ?EA2, ?EA, ?EA0; cbn [Z.max Z.of_nat Pos.of_succ_nat Pos.succ]; zlia|]). apply Forall_nil.
* destruct (Z.eqb_spec (ck_rz k) 16); [apply Forall_nil|].
assert (32 <= ck_rz k). { apply Z.mod_divide in G6 as [q Hq]; [|zlia]. zlia. }
repeat (apply Forall_cons; [cbn [c_at c_w z8 c8]; rewrite ?EA2, ?EA, ?EA0; cbn [Z.max Z.of_nat Pos.of_succ_nat Pos.succ]; zlia|]). apply Forall_nil.
-
cbn [flat_map]. rewrite app_nil_r. pose proof Kc_facts as (KB & KR & KN & KE & KS & KBEG & KA). unfold Kc in KB, KR, KN, KE, KS, KBEG, KA.
unfold chunk_cells, hdr_state. rewrite KR, KN, KS, KBEG. unfold kChunkHeaderSize.
pose proof NLOf as (_ & RZr & _). replace (RZ =? 16) with false by (symmetry; apply Z.eqb_neq; clear - RZr; zlia). cbn [sptr_exp app].
assert (EK : ly_space ly + (region_off cl + off) = Kv) by (rewrite Kv_is_sptr; reflexivity).
pose proof V3 as W3. pose proof V4 as W4. pose proof V5 as W5. pose proof V6 as W6. pose proof V1 as W1. pose proof V2 as W2.
constructor. { apply val_mem_cell. cbn [aeval aoff]. apply (val_mem_at _ (Kv + RZ - 16)); [clear - EK; zlia | exact W3]. }
constructor. { cbn [cell_holds c_at c_val c_w aeval aoff]. pose proof (W4 0%nat ltac:(zlia)) as X. rewrite Z.add_0_r in X. unfold m' in X.
pose proof (hdr_byte1_ok jb Hjb) as [B1 B2]. set (h := hdr_byte1 jb) in *. exists h. split; [|exact B2].
unfold rd', aview. replace (ly_space ly + (region_off cl + off + (RZ - 16) + 1)) with (Kv + RZ - 15) by (clear - EK; zlia). rewrite X. cbn [option_map].
rewrite le_byte_1_0 by zlia. rewrite unsigned_lit_small8 by zlia. reflexivity. }
constructor. { apply val_mem_cell. cbn [aeval aoff]. apply (val_mem_at _ (Kv + RZ - 14)); [clear - EK; zlia | exact W5]. }
constructor. { apply val_mem_cell. cbn [aeval aoff]. apply (val_mem_at _ (Kv + RZ - 12)); [clear - EK; zlia | exact W6]. }
constructor. { apply val_mem_cell. cbn [aeval aoff]. apply (val_mem_at _ Kv); [clear - EK; zlia | exact W1]. }
constructor. { apply val_mem_cell. cbn [aeval aoff]. apply (val_mem_at _ (Kv + 8)); [clear - EK; zlia |]. replace (ly_space ly + (region_off cl + off + (RZ - 16))) with (Kv + RZ - 16) by (clear - EK; zlia). exact W2. }
apply Forall_nil.
Qed.
Lemma cells_sec : Forall (cell_holds B ly rd') (sec_cells (SF z)).
Proof.
pose proof SF_parts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Rarr & Rres & _).
replace (sec_cells (SF z)) with (sec_cells S).
2:{ unfold sec_cells. rewrite Rres, Rarr. unfold SF. rewrite SF_chunks, flat_map_app. unfold Kc, new_chunk. cbn [flat_map ck_beg app]. rewrite app_nil_r. reflexivity. }
assert (INC : forall x, In x (sec_cells S) -> In x (acells B ly S)) by (intros x Hx; unfold acells; do 3 (apply in_app_iff; right); apply in_app_iff; left; exact Hx).
pose proof (ts_inst B TS) as EI.
assert (LOCI : loc_ok 0x10000 0x160408) by (intros a Ha; apply Z_low; unfold TFIB_IMG_LO, YImgTop.IMG_LO, YImgTop.IMG_TOP; zlia).
pose proof (wf_secondary _ _ _ _ _ WF) as X. destruct X as [Snd Sac Sal Sres Sral].
unfold sec_cells in *.
apply Forall_cons; [apply (keep_cell _ 0x10000 0x160408 LOCI); [apply INC; left; reflexivity | cbn; rewrite EI; unfold TFIB_INST, o_sec_reserved; zlia | cbn; rewrite EI; unfold TFIB_INST, o_sec_reserved; zlia]|].
apply Forall_cons; [apply (keep_cell _ 0x10000 0x160408 LOCI); [apply INC; right; left; reflexivity | cbn; rewrite EI; unfold TFIB_INST, o_sec_n; zlia | cbn; rewrite EI; unfold TFIB_INST, o_sec_n; zlia]|].
apply Forall_cons; [apply (keep_cell _ 0x10000 0x160408 LOCI); [apply INC; right; right; left; reflexivity | cbn; rewrite EI; unfold TFIB_INST, o_sec_mutex; zlia | cbn; rewrite EI; unfold TFIB_INST, o_sec_mutex; zlia]|].
apply Forall_app. split.
- apply (keep_cells _ (ly_Q ly) kPtrArrayResv).
+ intros a Ha. apply (Z_ext 1 (ly_Q ly, kPtrArrayResv)); [reflexivity | zlia | cbn [fst snd]; exact Ha].
+ intros x Hx. apply INC. do 3 right. apply in_app_iff. left. exact Hx.
+ apply Forall_forall. intros c Hc. apply in_map_iff in Hc as ([i r] & <- & Hir). apply in_combine_l in Hir. apply in_seq in Hir.
cbn. unfold kPtrArrayResv, kPtrArrayEntriesPerCommit in *. zlia.
- apply Forall_flat_map'. intros k Hk.
pose proof (chunk_facts B ly S rd0 k MA Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
pose proof (req_size_bounds (ck_req k) ltac:(zlia)) as (Q1 & Q2 & Q3).
destruct (ck_beg k) as [|o|r o|c' p] eqn:Eb; try apply Forall_nil.
destruct GG as (_ & _ & Gbase & Gext & Gin & _).
apply (keep_cells _ (ly_sec ly r) (sec_map_size (ck_req k))).
+ intros a Ha. apply (Z_sec (ly_sec ly r, sec_map_size (ck_req k))); [exact Gin | cbn [fst snd]; exact Ha].
+ intros x Hx. apply INC. do 3 right. apply in_app_iff. right. apply in_flat_map. exists k. rewrite Eb. split; [exact Hk | exact Hx].
+ unfold kPage in *. repeat fcons'. apply Forall_nil.
Qed.
Lemma keep_batches : forall bl, incl bl (all_batches S) -> incl (batch_cells bl) (acells B ly S) -> Forall (cell_holds B ly rd') (batch_cells bl).
Proof.
induction bl as [|b t IH]; intros Hincl INC; [apply Forall_nil|]. cbn [batch_cells].
pose proof (wq_batches _ (wf_quarantine _ _ _ _ _ WF)) as BL.
pose proof (proj1 (Forall_forall _ _) BL b (Hincl b (or_introl eq_refl))) as [L1 L2]. unfold kBatchSlots in L2.
assert (LOC : loc_ok (ly_space ly + b_self b) kBatchBytes).
{ pose proof (wf_classes _ _ _ _ _ WF kBatchClass ltac:(unfold kBatchClass; zlia)) as CL.
set (x := b_self b - region_off kBatchClass).
assert (INB : In x (batch_offs S kBatchClass)) by (rewrite batch_offs_24; apply in_map_iff; exists b; split; [reflexivity | apply Hincl; left; reflexivity]).
pose proof (proj1 (Forall_forall _ _) (wr_elems _ _ _ _ _ _ CL) x ltac:(rewrite !in_app_iff; tauto)) as [X1 X2].
pose proof (wr_alloc _ _ _ _ _ _ CL) as AL. pose proof (mapped_user_bound (as_universe B) 0 0 0 S kBatchClass WF ltac:(unfold kBatchClass; zlia)) as MB.
pose proof (region_in_prim ly kBatchClass LY ltac:(unfold kBatchClass; zlia)) as (R1 & R2 & R3 & R4 & R5).
assert (CS : class_size kBatchClass = 8192) by reflexivity. rewrite CS in X2.
assert (BX : ly_space ly + b_self b = region_base ly kBatchClass + x) by (unfold region_base; subst x; zlia).
pose proof off_facts as (O1 & O2 & O3 & _ & O5 & NI & _). pose proof Kv_base as KB. pose proof cls_geom as (K1 & _).
intros a Ha. apply Z_prim.
- clear - Ha X1 X2 AL MB R1 R2 BX. unfold kBatchBytes, kUserMapSize, EV_MAX in *. zlia.
- intros HK. destruct (Z.eq_dec cl kBatchClass) as [Ec|Nc].
+ assert (Nx : off <> x) by (intros E; apply NI; rewrite E; apply in_app_iff; right; apply in_app_iff; right; rewrite Ec; exact INB).
rewrite Ec, CS in *. apply Z.mod_divide in X2 as [qx Hqx]; [|zlia]. apply Z.mod_divide in O3 as [qo Hqo]; [|zlia].
clear - Ha HK BX KB Nx Hqx Hqo. unfold kBatchBytes in *. assert (qx <> qo) by (intros ->; apply Nx; zlia). nia.
+ unfold region_base in BX, KB. rewrite region_off_eq in BX by (unfold kBatchClass; zlia). rewrite region_off_eq in KB by zlia.
clear - Ha HK BX KB Nc X1 X2 AL MB O1 O2 O5 K1. unfold kBatchBytes, kBatchClass, kUserMapSize, EV_MAX in *. nia.
}
apply Forall_cons; [apply (keep_cell _ _ _ LOC); [apply INC; left; reflexivity | cbn; zlia | cbn; unfold kBatchBytes; zlia]|].
apply Forall_cons; [apply (keep_cell _ _ _ LOC); [apply INC; right; left; reflexivity | cbn; zlia | cbn; unfold kBatchBytes; zlia]|].
apply Forall_cons; [apply (keep_cell _ _ _ LOC); [apply INC; right; right; left; reflexivity | cbn; zlia | cbn; unfold kBatchBytes; zlia]|].
apply Forall_app. split.
- apply (keep_cells _ _ _ LOC).
+ intros y Hy. apply INC. do 3 right. apply in_app_iff. left. exact Hy.
+ apply Forall_forall. intros c Hc. apply in_map_iff in Hc as ([i k] & <- & Hik). apply in_combine_l in Hik. apply in_seq in Hik.
cbn. unfold kBatchBytes. zlia.
- apply IH; [intros y Hy; apply Hincl; right; exact Hy | intros y Hy; apply INC; do 3 right; apply in_app_iff; right; exact Hy].
Qed.
Lemma cells_quar : Forall (cell_holds B ly rd') (quar_cells (SF z)).
Proof.
pose proof SF_parts as (_ & _ & _ & _ & _ & Rqt & Rqg & _).
replace (quar_cells (SF z)) with (quar_cells S) by (unfold quar_cells; rewrite Rqt, Rqg; reflexivity).
assert (INC : forall x, In x (quar_cells S) -> In x (acells B ly S)) by (intros x Hx; unfold acells; do 4 (apply in_app_iff; right); apply in_app_iff; left; exact Hx).
pose proof (ts_inst B TS) as EI. pose proof derived_ranges as DR. pose proof cl_range as CR.
assert (LOCI : loc_ok 0x10000 0x160408) by (intros a Ha; apply Z_low; unfold TFIB_IMG_LO, YImgTop.IMG_LO, YImgTop.IMG_TOP; zlia).
assert (LOCT : loc_ok (T + t_qc) 32) by (intros a Ha; apply Z_T; unfold WINT, Pv, t_qc in *; unfold T in *; clear - Ha DR CR; numconst; zlia).
unfold quar_cells, qc_cells in *. unfold o_q_cmutex, o_q_rmutex, o_q_size, t_qc in *.
apply Forall_cons; [apply (keep_cell _ 0x10000 0x160408 LOCI); [apply INC; left; reflexivity | cbn; rewrite EI; unfold TFIB_INST; zlia | cbn; rewrite EI; unfold TFIB_INST; zlia]|].
apply Forall_cons; [apply (keep_cell _ 0x10000 0x160408 LOCI); [apply INC; right; left; reflexivity | cbn; rewrite EI; unfold TFIB_INST; zlia | cbn; rewrite EI; unfold TFIB_INST; zlia]|].
apply Forall_app. split.
- do 4 (apply Forall_cons; [apply (keep_cell _ _ _ LOCT); [apply INC; right; right; apply in_app_iff; left; cbn; tauto | cbn; unfold T; zlia | cbn; unfold T; zlia]|]).
apply keep_batches; [intros b Hb; unfold all_batches; apply in_app_iff; left; exact Hb|].
intros y Hy. apply INC. right; right. apply in_app_iff. left. do 4 right. exact Hy.
- do 4 (apply Forall_cons; [apply (keep_cell _ 0x10000 0x160408 LOCI); [apply INC; right; right; apply in_app_iff; right; cbn; tauto | cbn; rewrite EI; unfold TFIB_INST; zlia | cbn; rewrite EI; unfold TFIB_INST; zlia]|]).
apply keep_batches; [intros b Hb; unfold all_batches; apply in_app_iff; right; exact Hb|].
intros y Hy. apply INC. right; right. apply in_app_iff. right. do 4 right. exact Hy.
Qed.
Lemma cells_fs : Forall (cell_holds B ly rd') (fs_cells (SF z)).
Proof.
pose proof SF_parts as (_ & _ & _ & _ & _ & _ & _ & Rfs & _).
replace (fs_cells (SF z)) with (fs_cells S) by (unfold fs_cells; rewrite Rfs; reflexivity).
apply (keep_cells _ (ly_F ly) kFakeStackSize).
- intros a Ha. apply (Z_ext 3 (ly_F ly, kFakeStackSize)); [reflexivity | zlia | cbn [fst snd]; exact Ha].
- intros x Hx. unfold acells. do 5 (apply in_app_iff; right). apply in_app_iff. left. exact Hx.
- unfold fs_cells, kFakeStackSize. fcons'. fcons'. apply Forall_forall. intros c Hc. apply in_map_iff in Hc as ([i h] & <- & Hih).
apply in_combine_l in Hih. apply in_seq in Hih. cbn. zlia.
Qed.
Lemma DZONE64 : forall a, DZONE a -> 0 <= a < 2 ^ 64.
Proof.
intros a Ha. pose proof blocks_facts as (NBhi & SBhi & _). unfold DZONE, KnBlockExt.DZONE_at, AD3j.tfib_dzone_lo, AD3j.tfib_dzone_hi in Ha.
clear - Ha NBhi SBhi. numconst. zlia.
Qed.
Lemma depot_after_ne : st_depot S <> [] -> st_depot (depot_after z tr S) <> [].
Proof. intros NE. unfold depot_after. destruct (z =? 0); cbn; [exact NE|]. intros Hc. apply app_eq_nil in Hc as [_ Hc]. discriminate. Qed.
Lemma depot_final : st_depot S <> [] -> depot_mem_ok B ly (depot_after z tr S) rd'.
Proof.
intros NE. apply (depot_mem_ok_agree _ rdD); [exact (depot_after_ne NE)| | |].
- pose proof (wf_depot _ _ _ _ _ WF) as [ND INCL]. pose proof (depot_ids_bound S ND INCL). unfold depot_after. destruct (z =? 0); [zlia|].
unfold depot_ids in *. cbn. rewrite length_app. cbn. zlia.
- intros a Ha. apply AGREED; [exact (DZONE64 a Ha) | exact Ha].
- exact (DEPD NE).
Qed.
Lemma cells_depot : st_depot S <> [] -> Forall (cell_holds B ly rd') (depot_cells ly (SF z)).
Proof.
intros NE.
pose proof SF_parts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Rdep).
replace (depot_cells ly (SF z)) with (depot_cells ly (depot_after z tr S)) by (unfold depot_cells, depot_ids, depot_frames; rewrite Rdep; reflexivity).
exact (proj1 (depot_final NE)).
Qed.
Lemma cells_ialloc : Forall (cell_holds B ly rd') (ialloc_cells B (SF z)).
Proof.
pose proof SF_parts as (_ & _ & _ & _ & _ & _ & _ & _ & Rii & _).
replace (ialloc_cells B (SF z)) with (ialloc_cells B S) by (unfold ialloc_cells; rewrite Rii; reflexivity).
pose proof (ts_ial_lo B TS) as E1. pose proof (ts_ial_w B TS) as E2. pose proof (ts_ial_flag B TS) as E3.
apply (keep_cells _ 0x10000 0x160408).
- intros a Ha. apply Z_low. unfold TFIB_IMG_LO, YImgTop.IMG_LO, YImgTop.IMG_TOP. zlia.
- intros x Hx. unfold acells. do 7 (apply in_app_iff; right). apply in_app_iff. left. exact Hx.
- unfold ialloc_cells. rewrite E1, E2, E3. unfold TFIB_IAL_LO, TFIB_IAL_W, TFIB_IAL_FLAG.
repeat (apply Forall_cons; [cbn; rewrite ?E1, ?E3; unfold TFIB_IAL_LO, TFIB_IAL_FLAG; zlia|]). apply Forall_nil.
Qed.
Lemma cells_thread : Forall (cell_holds B ly rd') thread_cells.
Proof.
unfold thread_cells. constructor; [|apply Forall_nil]. apply val_mem_cell. cbn [aeval]. exact V8.
Qed.
Lemma cells_nodepot : forall c, In c (acells B ly (SF z)) -> ~ In c (depot_cells ly (SF z)) -> cell_holds B ly rd' c.
Proof.
intros c Hc ND. unfold acells in Hc. rewrite !in_app_iff in Hc.
destruct Hc as [H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]].
- exact (proj1 (Forall_forall _ _) cells_regions c H).
- exact (proj1 (Forall_forall _ _) cells_caches c H).
- exact (proj1 (Forall_forall _ _) cells_chunks c H).
- exact (proj1 (Forall_forall _ _) cells_sec c H).
- exact (proj1 (Forall_forall _ _) cells_quar c H).
- exact (proj1 (Forall_forall _ _) cells_fs c H).
- exfalso. exact (ND H).
- exact (proj1 (Forall_forall _ _) cells_ialloc c H).
- exact (proj1 (Forall_forall _ _) cells_thread c H).
Qed.
Lemma cells_final : st_depot S <> [] -> Forall (cell_holds B ly rd') (acells B ly (SF z)).
Proof.
intros NE.
unfold acells.
apply Forall_app; split; [exact cells_regions|]. apply Forall_app; split; [exact cells_caches|]. apply Forall_app; split; [exact cells_chunks|].
apply Forall_app; split; [exact cells_sec|]. apply Forall_app; split; [exact cells_quar|]. apply Forall_app; split; [exact cells_fs|].
apply Forall_app; split; [exact (cells_depot NE)|]. apply Forall_app; split; [exact cells_ialloc | exact cells_thread].
Qed.
Lemma fa_final : fa_entries_ok ly rd' (SF z).
Proof.
pose proof SF_parts as (Rreg & _). intros c i vv Hc Hi HV k Hk. rewrite Rreg in Hi, HV.
pose proof (wf_classes _ _ _ _ _ WF c Hc) as CL. pose proof (wr_fa_len _ _ _ _ _ _ CL) as FL. pose proof (wr_fa_bound _ _ _ _ _ _ CL) as FB.
rewrite AGX; [exact (am_fa _ _ _ _ MA c i vv Hc Hi HV k Hk) | eapply own_fa; [exact MA | exact Hc | zlia] |].
pose proof (region_in_prim ly c LY Hc) as (R1 & R2 & _). pose proof off_facts as (O1 & O2 & _ & _ & O5 & _). pose proof Kv_base as KB. pose proof cls_geom as (K1 & _).
unfold fa_base, region_base, kFreeArrayOffset, kFreeArrayMax in *. rewrite region_off_eq in * by zlia.
apply Z_prim; clear - Hk Hi FL FB R1 R2 KB O1 O2 O5 K1 Hc; zlia.
Qed.
Lemma flags_final : fs_flags_ok ly rd' (SF z).
Proof.
pose proof SF_parts as (_ & _ & _ & _ & Rfr & _). intros cid pos Hc Hp. rewrite Rfr.
pose proof (flag_off_bounds cid pos Hc Hp) as FB.
rewrite AGX; [exact (am_flags _ _ _ _ MA cid pos Hc Hp) | unfold flag_addr, kFakeFlagsOff in *; eapply own_F_low; [exact MA | zlia] |].
apply (Z_ext 3 (ly_F ly, kFakeStackSize)); [reflexivity | zlia | cbn [fst snd]].
unfold flag_addr, kFakeFlagsOff, kFakeFramesOff, kFakeStackSize in *. zlia.
Qed.
Lemma sh_of_granule : forall j, shadow_addr (Kv + 8 * j) = SKv + j.
Proof.
intros j. unfold shadow_addr, SKv, SHBv, SHADOW_OFF. replace (Kv + 8 * j) with (j * 8 + Kv) by zlia. rewrite Z.div_add_l by zlia. zlia.
Qed.
Lemma SHX_granule : forall g, g mod 8 = 0 -> SHX (shadow_addr g) -> Kv + RZ <= g < Kv + class_size cl.
Proof.
intros g Hg HS. apply SHX_bounds in HS. pose proof cls_geom as (_ & K2 & _). pose proof Kv_geom as (_ & _ & G3 & _).
pose proof (Z.div_mod g 8 ltac:(zlia)) as D1. pose proof (Z.div_mod Kv 8 ltac:(zlia)) as D2. pose proof (Z.mod_pos_bound Kv 8 ltac:(zlia)) as M2.
pose proof (Z.div_mod (Kv + class_size cl) 8 ltac:(zlia)) as D3. pose proof (Z.mod_pos_bound (Kv + class_size cl) 8 ltac:(zlia)) as M3.
apply Z.mod_divide in K2 as [r Hr]; [|zlia]. apply Z.mod_divide in G3 as [q Hq]; [|zlia].
pose proof NLOf as (_ & RZr & RZ8 & _).
unfold shadow_addr, SHBv, SHADOW_OFF in *. clear - Hg HS D1 D2 M2 D3 M3 Hr Hq RZr RZ8. zlia.
Qed.
Lemma sh_band : forall g, 0 <= g -> g < ASAN_CEIL -> kLowShadowBeg <= shadow_addr g < kHighMemBeg.
Proof.
intros g H1 H2. unfold shadow_addr. pose proof (Z.div_mod g 8 ltac:(zlia)) as D1. pose proof (Z.mod_pos_bound g 8 ltac:(zlia)) as M1.
clear - H1 H2 D1 M1. numconst. unfold SHADOW_OFF. zlia.
Qed.
Lemma shadow_final : shadow_ok B ly rd' (SF z).
Proof.
pose proof (SF_same z) as (Rregs & _). pose proof Kc_facts as (KB & KR & KN & KE & KS & KBEG & KA). unfold Kc in KB, KR, KN, KE, KS, KBEG, KA.
pose proof cls_geom as (K1 & K2 & K3 & K4 & K5 & K6). pose proof Kv_geom as (G1 & G2 & G3 & G4 & G5). pose proof derived_ranges as DR.
assert (FPR : fa_poison_ranges ly (SF z) = fa_poison_ranges ly S).
{ unfold fa_poison_ranges, reg. unfold SF. rewrite Rregs, SF_chunks, flat_map_app. unfold new_chunk. cbn [flat_map ck_beg app]. rewrite app_nil_r. reflexivity. }
unfold SF in FPR. intros g vv Hg8 HV. unfold ashadow in HV. unfold SF in HV. rewrite SF_chunks in HV.
destruct (find_chunk_at B ly (st_chunks S) g) as [k0|] eqn:F0.
-
rewrite (find_chunk_at_app1 _ _ _ _ F0) in HV.
assert (A0 : ashadow B ly S g = Some vv) by (unfold ashadow; rewrite F0; exact HV).
rewrite AGX; [exact (am_shadow _ _ _ _ MA g vv Hg8 A0) | exact (ashadow_owned B ly S rd0 g vv MA A0) |].
apply find_chunk_at_In in F0 as [Hk0 Hg0]. pose proof (chunk_facts B ly S rd0 k0 MA Hk0) as (C1 & C2 & _).
apply Z_sh; [apply sh_band; zlia|]. intros HS. apply (SHX_granule g Hg8) in HS. pose proof (cached_vs_chunk k0 Hk0) as D. pose proof NLOf as (_ & RZr & _). clear - HS D Hg0 RZr. zlia.
- rewrite (find_chunk_at_app2 _ _ _ F0) in HV. cbn [find_chunk_at] in HV. rewrite KB, KE in HV.
destruct (andb (Kv <=? g) (g <? Kv + class_size cl)) eqn:CK.
+
apply andb_prop in CK as [CK1 CK2]. apply Z.leb_le in CK1. apply Z.ltb_lt in CK2.
injection HV as HV'. rewrite KB in HV'. unfold chunk_granule in HV'. rewrite KR, KN, KS in HV'.
pose proof NLOf as (Nlo & RZr & RZ8 & U8). set (u := RZ / 8) in *.
set (j := (g - Kv) / 8) in HV'.
assert (Hgj : g = Kv + 8 * j).
{ subst j. pose proof (Z.div_mod (g - Kv) 8 ltac:(zlia)) as D1. apply Z.mod_divide in G3 as [q Hq]; [|zlia]. apply Z.mod_divide in Hg8 as [s Hs]; [|zlia].
assert ((g - Kv) mod 8 = 0) by (rewrite Hs, Hq; replace (s * 8 - q * 16) with ((s - 2 * q) * 8) by zlia; apply Z.mod_mul; zlia). zlia. }
pose proof (sh_of_granule j) as SA. rewrite <- Hgj in SA.
assert (N8 : N8D / 8 = n / 8) by (unfold N8D; apply Z.div_mul; zlia).
pose proof (Z.div_mod n 8 ltac:(zlia)) as DM. pose proof (Z.mod_pos_bound n 8 ltac:(zlia)) as MB.
destruct (Z.ltb_spec j u) as [J1|J1].
*
subst vv. rewrite AGX; [exact (shadow250 g Hg8 (conj CK1 CK2)) | eapply own_shadow_prim; [exact MA | zlia] |].
apply Z_sh; [apply sh_band; zlia|]. intros HS. apply (SHX_granule g Hg8) in HS. clear - HS Hgj J1 RZ8 U8. zlia.
* destruct (Z.ltb_spec j (u + n / 8)) as [J2|J2].
--
subst vv. unfold rd', aview, mbyte, mrestrict. rewrite SA.
destruct (HSKpres (SKv + j) ltac:(clear - J1 J2 DR DM MB RZ8 U8; zlia)) as [Hh _]. rewrite Hh.
rewrite (V9 (Z_to_bv 64 (SKv + j))) by (rewrite unsigned_lit_small by (clear - J1 J2 DR RZ8 U8; numconst; zlia); clear - J1 J2 N8 DR; zlia). reflexivity.
-- destruct (andb (j =? u + n / 8) (negb (n mod 8 =? 0))) eqn:PJ.
++
apply andb_prop in PJ as [PJ1 PJ2]. apply Z.eqb_eq in PJ1. apply Bool.negb_true_iff in PJ2. apply Z.eqb_neq in PJ2. subst vv.
assert (Ho : odd = true) by (apply Hodd; exact PJ2).
pose proof (V10 Ho 0%nat ltac:(zlia)) as X. rewrite Z.add_0_r in X. unfold m' in X.
assert (EP : PBv = SKv + j) by (clear - DR PJ1 N8 RZ8; zlia).
unfold rd', aview. rewrite SA, <- EP, X. cbn [option_map]. rewrite le_byte_1_0 by zlia. rewrite unsigned_lit_small8 by zlia. reflexivity.
++
subst vv. rewrite AGX; [exact (shadow250 g Hg8 (conj CK1 CK2)) | eapply own_shadow_prim; [exact MA | zlia] |].
apply Z_sh; [apply sh_band; zlia|]. intros HS. unfold SHX, PBW in HS. rewrite SA in HS.
apply Bool.andb_false_iff in PJ. destruct HS as [HS|[Ho HS]]; [clear - HS J2 N8 DR; zlia|].
apply Hodd in Ho. assert (EP : PBv = SUv + n / 8) by (clear - DR N8; zlia).
destruct PJ as [PJ|PJ]; [apply Z.eqb_neq in PJ; clear - HS EP PJ DR; zlia | apply Bool.negb_false_iff in PJ; apply Z.eqb_eq in PJ; exact (Ho PJ)].
+
rewrite FPR in HV. assert (A0 : ashadow B ly S g = Some vv) by (unfold ashadow; rewrite F0; exact HV).
rewrite AGX; [exact (am_shadow _ _ _ _ MA g vv Hg8 A0) | exact (ashadow_owned B ly S rd0 g vv MA A0) |].
destruct (in_rangesb g (fa_poison_ranges ly S)) eqn:IR; [|discriminate].
apply in_rangesb_true in IR as (lo & len & Hin & Hglo).
assert (GB : 0 <= g < ASAN_CEIL).
{ unfold fa_poison_ranges in Hin. apply in_app_iff in Hin as [Hin|Hin].
- apply in_flat_map in Hin as (c & Hc & Hin). apply zseq_In in Hc.
pose proof (region_in_prim ly c LY ltac:(zlia)) as (R1 & R2 & R3 & R4 & R5).
pose proof (wf_classes _ _ _ _ _ WF c ltac:(zlia)) as CL. pose proof (wr_alloc _ _ _ _ _ _ CL) as A1. pose proof (wr_fa _ _ _ _ _ _ CL) as [A2 _].
pose proof (wr_fa_bound _ _ _ _ _ _ CL) as A3. pose proof (mapped_user_bound (as_universe B) 0 0 0 S c WF ltac:(zlia)) as MB.
unfold kUserMapSize, EV_MAX, kFreeArrayMax in *. unfold fa_base, kFreeArrayOffset in Hin. unfold region_base in *.
destruct Hin as [E|[E|[]]]; injection E as <- <-; clear - Hglo R1 R2 R4 R5 A1 A2 A3 MB; zlia.
- apply in_flat_map in Hin as (k & Hk & Hin). destruct (ck_beg k) as [|o|r o|c p] eqn:Eb; try (destruct Hin; fail). destruct Hin as [E|[]]. injection E as <- <-.
pose proof (am_placed _ _ _ _ MA) as [PL _].
pose proof (proj1 (Forall_forall _ _) PL (ly_sec ly r, sec_map_size (ck_req k)) ltac:(unfold sec_extents; apply in_flat_map; exists k; rewrite Eb; split; [exact Hk | left; reflexivity])) as (_ & [H1 _] & H2).
cbn [fst snd] in H1, H2. clear - Hglo H1 H2. zlia. }
apply Z_sh; [apply sh_band; zlia|]. intros HS. apply (SHX_granule g Hg8) in HS. apply Bool.andb_false_iff in CK.
pose proof NLOf as (_ & RZr & _).
destruct CK as [CK|CK]; [apply Z.leb_gt in CK | apply Z.ltb_ge in CK]; clear - HS CK RZr; zlia.
Qed.
Lemma zshadow_final : zshadow_ok B ly rd'.
Proof.
unfold zshadow_ok. apply Forall_forall. intros r Hr i Hi. unfold shadow_of_addr. change (SHADOW_OFF + fst r / 8) with (shadow_addr (fst r)).
rewrite AGX; [exact (proj1 (Forall_forall _ _) (am_zshadow _ _ _ _ MA) r Hr i Hi) | eapply own_shadow_zero; [exact MA | exact Hr | exact Hi] |].
pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). pose proof Kv_geom as (G1 & G2 & G3 & G4 & G5). pose proof cls_geom as (K1 & K2 & _).
unfold zero_shadow_ranges in Hr. destruct Hr as [<-|Hr].
-
cbn [fst snd] in *.
pose proof (pairwise_ij _ _ 0 7 _ _ (lo_disj ly LY) eq_refl eq_refl) as PS. unfold zdisjoint in PS. cbn [fst snd] in PS.
pose proof (Z.div_mod (ly_stk_lo ly) 8 ltac:(zlia)) as D1. pose proof (Z.div_mod (ly_stk_hi ly - ly_stk_lo ly) 8 ltac:(zlia)) as D2.
pose proof (Z.mod_pos_bound (ly_stk_hi ly - ly_stk_lo ly) 8 ltac:(zlia)) as M2.
assert (A8 : ly_stk_lo ly mod 8 = 0) by (unfold page_aligned in T5; apply Z.mod_divide in T5 as [q Hq]; [|zlia]; rewrite Hq; replace (q * 4096) with (q * 512 * 8) by zlia; apply Z.mod_mul; zlia).
apply Z_sh.
+ unfold shadow_addr. clear - Hi T1 T2 T4 T7 D1 D2 M2 A8. numconst. unfold SHADOW_OFF. zlia.
+ intros HS. apply SHX_bounds in HS. unfold shadow_addr, SHBv, SHADOW_OFF in HS.
pose proof (Z.div_mod Kv 8 ltac:(zlia)) as D3. pose proof (Z.mod_pos_bound Kv 8 ltac:(zlia)) as M3.
pose proof (Z.div_mod (Kv + class_size cl) 8 ltac:(zlia)) as D4. pose proof (Z.mod_pos_bound (Kv + class_size cl) 8 ltac:(zlia)) as M4.
pose proof NLOf as (_ & RZr & RZ8 & U8). clear - Hi HS PS G4 G5 K1 D1 D2 M2 A8 D3 M3 D4 M4 RZ8 U8. zlia.
-
pose proof (proj1 (Forall_forall _ _) (aso_zshadow _ (am_syms _ _ _ _ MA)) r Hr) as (Z1 & Z2 & Z3 & Z4 & Z5).
apply Z_band. unfold shadow_addr. unfold kLowMemEnd in Z5.
pose proof (Z.div_mod (fst r) 8 ltac:(zlia)) as D1. pose proof (Z.div_mod (snd r) 8 ltac:(zlia)) as D2.
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
intros a Ha. apply VIS_MONO. pose proof off_facts as (O1 & O2 & _ & _ & O5 & _). pose proof Kv_base as KB. pose proof cl_range as CR.
pose proof (proj1 (Forall_forall _ _) (am_areas _ _ _ _ MA) (ASp (region_off cl), rg_mapped_user (reg S cl))
ltac:(unfold aareas; apply in_app_iff; left; apply in_flat_map; exists cl; split; [apply In_zseq; zlia | left; reflexivity])) as RV.
specialize (RV (a - region_base ly cl)). cbn [fst snd aeval] in RV. unfold region_base in *.
replace (ly_space ly + region_off cl + (a - (ly_space ly + region_off cl))) with a in RV by zlia. apply RV. zlia.
Qed.
Lemma vis_keep : forall lst, incl lst (ajunk B ly S) \/ incl lst (aareas S) \/ incl lst (aclient S) -> Forall (range_vis B ly rd') lst.
Proof.
intros lst H. apply (Forall_range_vis_keep B ly rd0 rd' lst VIS_MONO).
destruct H as [H|[H|H]]; (eapply incl_Forall; [exact H|]); [exact (am_junk _ _ _ _ MA) | exact (am_areas _ _ _ _ MA) | exact (am_client _ _ _ _ MA)].
Qed.
Lemma vis_final : Forall (range_vis B ly rd') (ajunk B ly (SF z)) /\
(forall r, In r (aareas (SF z)) -> fst r <> ANB 0 -> fst r <> ASB 0 -> range_vis B ly rd' r) /\ Forall (range_vis B ly rd') (aclient (SF z)).
Proof.
pose proof (SF_same z) as (Rregs & _ & _ & _ & _ & _ & _ & _ & _ & _ & Rcache & _).
pose proof SF_parts as (Rreg & Rinit & Rother & Rcl & Rfr & Rqt & Rqg & Rfs & Rii & Rarr & Rres & Rdep).
pose proof Kc_facts as (KB & KR & KN & KE & KS & KBEG & KA). unfold Kc in KB, KR, KN, KE, KS, KBEG, KA.
pose proof cls_geom as (K1 & K2 & K3 & K4 & K5 & K6). pose proof cl_range as CR. pose proof off_facts as (_ & _ & _ & _ & _ & _ & _ & CN & _).
assert (EK : ly_space ly + (region_off cl + off) = Kv) by (rewrite Kv_is_sptr; reflexivity).
unfold SF in *. split; [|split].
-
unfold ajunk. rewrite SF_chunks.
apply Forall_cons. { refine (proj1 (Forall_forall _ _) (vis_keep [_] _) _ (or_introl eq_refl)). left. intros x [<-|[]]. unfold ajunk. left. reflexivity. }
apply Forall_cons. { refine (proj1 (Forall_forall _ _) (vis_keep [_] _) _ (or_introl eq_refl)). left. intros x [<-|[]]. unfold ajunk. right; left. reflexivity. }
apply Forall_app; split; [apply vis_keep; left; intros x Hx; unfold ajunk; do 2 right; apply in_app_iff; left; exact Hx|].
apply Forall_app; split.
{ apply Forall_flat_map'. intros c Hc. apply zseq_In in Hc. destruct (Z.eq_dec c cl) as [->|Hne].
- unfold cache_junk. rewrite Rinit, Hinited, Rcl. cbn [pc_chunks].
constructor; [|apply Forall_nil]. intros i Hi. cbn [fst snd aeval] in *.
destruct (Z_lt_le_dec i 4) as [I4|I4].
+
replace (ly_T ly + (t_cache + 80 * cl + 16 + 4 * Z.of_nat (length l)) + i) with (aeval B ly (c_at (z4 (aoff (AT (t_cache + 80 * cl)) (16 + 4 * Z.of_nat (length l))) (off / 16))) + Z.of_nat (Z.to_nat i)) by (cbn; zlia).
apply VIS_MONO. apply cell_vis; [| eexists; reflexivity | cbn; zlia].
apply In_acells_cache. unfold cache_cells. rewrite Hinited, Hcache. do 3 right. apply in_map_iff. exists (length l, off). split; [reflexivity|].
rewrite length_app. cbn [length]. replace (length l) with (0 + length l)%nat at 1 by zlia. apply In_combine_seq_last.
+
pose proof (proj1 (Forall_forall _ _) (am_junk _ _ _ _ MA) (AT (t_cache + 80 * cl + 16 + 4 * cnt), 64 - 4 * cnt)
ltac:(unfold ajunk; do 2 right; apply in_app_iff; right; apply in_app_iff; left; apply in_flat_map; exists cl; split; [apply In_zseq; zlia|];
unfold cache_junk; rewrite Hinited, Hcache, length_app; cbn [length]; left; f_equal; [f_equal; zlia | zlia])) as RV.
specialize (RV (i - 4) ltac:(cbn [snd]; zlia)). cbn [fst snd aeval] in RV. apply VIS_MONO.
replace (ly_T ly + (t_cache + 80 * cl + 16 + 4 * Z.of_nat (length l)) + i) with (ly_T ly + (t_cache + 80 * cl + 16 + 4 * cnt) + (i - 4)) by zlia. exact RV.
- apply vis_keep. left. intros x Hx. unfold ajunk. do 2 right. apply in_app_iff; right. apply in_app_iff; left. apply in_flat_map. exists c. split; [apply In_zseq; zlia|].
unfold cache_junk in *. rewrite Rinit, (Rother c) in Hx by zlia. exact Hx. }
apply Forall_app; split.
{ rewrite flat_map_app. apply Forall_app; split.
- apply vis_keep. left. intros x Hx. unfold ajunk. do 2 right. do 2 (apply in_app_iff; right). apply in_app_iff; left. exact Hx.
- cbn [flat_map]. rewrite app_nil_r. unfold chunk_junk. rewrite KR, KN, KS, KBEG, KE. unfold kChunkHeaderSize.
pose proof NLOf as (Nlo & RZr & _). replace (RZ =? 16) with false by (symmetry; apply Z.eqb_neq; clear - RZr; zlia). cbn [sptr_exp app].
repeat (apply Forall_cons; [intros i Hi; cbn [fst snd aeval aoff] in *; apply Kext_vis; clear - Hi EK K5 Nlo RZr; zlia|]). apply Forall_nil. }
apply Forall_app; split.
{ apply vis_keep. left. intros x Hx. unfold ajunk. do 2 right. do 3 (apply in_app_iff; right). apply in_app_iff; left.
unfold sec_junk in *. rewrite Rarr, Rres, SF_chunks, flat_map_app in Hx. unfold new_chunk in Hx. cbn [flat_map ck_beg app] in Hx. rewrite app_nil_r in Hx. exact Hx. }
apply Forall_app; split.
{ apply vis_keep. left. intros x Hx. unfold ajunk. do 2 right. do 4 (apply in_app_iff; right). apply in_app_iff; left.
unfold quar_junk, all_batches in *. rewrite Rqt, Rqg in Hx. exact Hx. }
apply vis_keep. left. intros x Hx. unfold ajunk. do 2 right. do 5 (apply in_app_iff; right). exact Hx.
-
intros r Hr N1 N2. refine (proj1 (Forall_forall _ _) (vis_keep [r] _) r (or_introl eq_refl)). right; left. intros x [<-|[]].
unfold aareas, reg in Hr |- *. rewrite Rregs, Rres, SF_chunks, flat_map_app in Hr. unfold new_chunk in Hr. cbn [flat_map ck_beg app] in Hr. rewrite app_nil_r in Hr.
apply in_app_iff in Hr as [H|Hr]; [apply in_app_iff; left; exact H|]. apply in_app_iff; right.
cbn [app] in Hr |- *. destruct Hr as [<-|Hr]; [left; reflexivity|]. right.
apply in_app_iff in Hr as [H|Hr]; [apply in_app_iff; left; exact H|]. apply in_app_iff; right.
cbn [In] in Hr |- *. destruct Hr as [<-|[E|[E|H]]]; [left; reflexivity | exfalso; apply N1; rewrite <- E; reflexivity | exfalso; apply N2; rewrite <- E; reflexivity | right; right; right; exact H].
-
unfold aclient. rewrite Rfr. rewrite SF_chunks, flat_map_app.
apply Forall_app; split; [apply Forall_app; split|].
+ apply vis_keep. do 2 right. intros x Hx. unfold aclient. apply in_app_iff. left. exact Hx.
+ cbn [flat_map]. rewrite app_nil_r. unfold chunk_user. rewrite KS, KN. unfold ck_user. rewrite KBEG, KR. cbn [padd sptr_exp].
constructor; [|apply Forall_nil]. intros i Hi. cbn [fst snd aeval] in *. apply apresent_vis. apply PRW. right; left. pose proof NLOf as (Nlo & RZr & _). clear - Hi EK Nlo RZr. zlia.
+ apply vis_keep. do 2 right. intros x Hx. unfold aclient. apply in_app_iff. right. exact Hx.
Qed.
Lemma areas_NE : st_depot S <> [] -> Forall (range_vis B ly rd') (aareas (SF z)).
Proof.
intros NE. pose proof (depot_after_ne NE) as NE'.
pose proof SF_parts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Rdep).
pose proof (SF_same z) as (Rregs & _ & _ & _ & Rres & _).
assert (E : aareas (SF z) = aareas S).
{ unfold aareas. rewrite Rdep. destruct (st_depot (depot_after z tr S)) eqn:E1; [exfalso; exact (NE' eq_refl)|].
destruct (st_depot S) eqn:E2; [exfalso; exact (NE eq_refl)|].
unfold SF. unfold reg. rewrite Rregs, Rres, SF_chunks, flat_map_app. unfold new_chunk. cbn [flat_map ck_beg app]. rewrite app_nil_r. reflexivity. }
rewrite E. apply vis_keep. right; left. intros x Hx. exact Hx.
Qed.
Lemma AR_transport : st_depot S <> [] -> AR tfibsegs B ly (SF z) W mem' (with_vm_backing (m_vm_lazy md0) mat md0).
Proof.
intros NE.
pose proof HAR as (M0 & L & BUD & MW & HS0).
pose proof (SF_same z) as (Rregs & Rinit & Rsecs & Rarr & Rres & Rqt & Rqg & Rfs & Rii & Rnev & Rcache & Rdep).
unfold SF. split; [|split; [|split; [|split]]].
- destruct M0 as [Mwf Mun Msy Mly Mpl Mco Mcow Mce Mfa Mfl Mde Msh Mzs Mju Mar Mcl Mze Mts Msi].
constructor.
+   exact (proj1 MP).
+ exact Mun.
+ exact Msy.
+ exact Mly.
+   unfold sec_placed in *. unfold SF. rewrite SF_sec_extents. exact Mpl.
+   apply Forall_forall. intros c Hc.
destruct (match c_at c with ANum a => a =? as_store B + AD3c.ss_alloc | _ => false end) eqn:EB.
{ apply (AD3j.kd_alloc_row_rev6 B ly rd' c TS Hc).
- destruct (c_at c) eqn:EC; try discriminate EB. apply Z.eqb_eq in EB. rewrite EB. reflexivity.
- pose proof (cells_depot NE) as CD. revert CD. unfold depot_cells. pose proof SF_parts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Rdep2).
rewrite Rdep2. destruct (st_depot (depot_after z tr S)) eqn:E1; [exfalso; exact (depot_after_ne NE E1)|].
intros CD. do 4 (apply Forall_cons_iff in CD as [_ CD]). apply Forall_cons_iff in CD as [CD _]. exact CD. }
assert (Hc2 : In c (AD3j.as_const_g2f B ly)).
{ apply (proj2 (AD3j.as_const_g2f_def B ly c)). split; [exact Hc|]. intros E. rewrite E, Z.eqb_refl in EB. discriminate EB. }
apply (cell_holds_agree2 rd0 rdD); [| exact (proj1 (Forall_forall _ _) Mco c Hc) | exact (proj1 (Forall_forall _ _) CSTD c Hc2)].
intros k Hk. pose proof (const_cells_zone c k Hc Hk) as Z1. pose proof (CZONE_untouched odd _ Z1) as (Ra & N1 & N3 & N4 & _ & _ & _). pose proof (FZ_czone _ Z1) as NF.
destruct (Z_lt_le_dec (aeval B ly (c_at c) + k) 0x170408) as [Hlo|Hge].
* left. apply AGREE0; try assumption. unfold DZONE, KnBlockExt.DZONE_at, AD3j.tfib_dzone_lo, AD3j.tfib_dzone_hi. pose proof blocks_facts as (NBhi & SBhi & _).
assert (NBc : snd (nb_ext ly) = 0 \/ snd (nb_ext ly) = kNodesBlockSize) by (rewrite nb_ext_eq; destruct (ly_NB ly =? 0); [left | right]; reflexivity).
assert (SBc : snd (sb_ext ly) = 0 \/ snd (sb_ext ly) = kStoreBlockSize) by (rewrite sb_ext_eq; destruct (ly_SB ly =? 0); [left | right]; reflexivity).
clear - Hlo NBhi SBhi NBc SBc. numconst. zlia.
* destruct (Z_lt_le_dec (aeval B ly (c_at c) + k) 0x5c0b90) as [Hlo2|Hge2].
-- right. apply AGREED; [exact Ra|]. unfold DZONE, KnBlockExt.DZONE_at, AD3j.tfib_dzone_lo, AD3j.tfib_dzone_hi. left. zlia.
-- left. apply AGREE0; try assumption. unfold DZONE, KnBlockExt.DZONE_at, AD3j.tfib_dzone_lo, AD3j.tfib_dzone_hi. unfold CZONE in Z1. pose proof blocks_facts as (NBhi & SBhi & TNB & TSB & _).
pose proof HC_NB as [CNB CSB]. unfold zdisjoint in CNB, CSB, TNB, TSB. cbn [fst snd] in CNB, CSB, TNB, TSB. unfold T in Z1.
pose proof (pairwise_ij _ _ 4 2 _ _ (lo_disj ly LY) (nb_ext_nth_st ly) eq_refl) as DNB. pose proof (pairwise_ij _ _ 5 1 _ _ (lo_disj ly LY) (sb_ext_nth_st ly) eq_refl) as DSB. unfold zdisjoint in DNB, DSB. cbn [fst snd] in DNB, DSB.
clear - Z1 Hge2 NBhi SBhi CNB CSB TNB TSB DNB DSB. unfold TFIB_TSD in *. numconst. zlia.
+ exact Mcow.
+ exact (cells_final NE).
+ exact fa_final.
+ exact flags_final.
+   apply (depot_ok_ext (depot_after z tr S)); [exact (depot_after_ne NE) | rewrite Rdep; unfold depot_after; destruct (z =? 0); reflexivity | exact (proj1 (proj2 (depot_final NE)))].
+ exact shadow_final.
+ exact zshadow_final.
+ exact (proj1 vis_final).
+ exact (areas_NE NE).
+ exact (proj2 (proj2 vis_final)).
+
apply Forall_forall. intros r Hr i Hi. rewrite <- (proj1 (Forall_forall _ _) Mze r Hr i Hi). apply AGX.
* pose proof (aso_ialloc _ Msy) as [I1 I2].
eapply (own_area B ly S rd0 (as_ialloc_lo B, as_ialloc_hi B - as_ialloc_lo B)); [exact MA | cbn; tauto |].
unfold ialloc_zero in Hr. cbn [fst snd]. destruct Hr as [<-|[<-|[]]]; cbn [fst snd aeval] in *; zlia.
* apply Z_low. unfold TFIB_IMG_LO, YImgTop.IMG_LO, YImgTop.IMG_TOP. unfold ialloc_zero in Hr. pose proof (ts_ial_lo B TS) as E1. pose proof (ts_ial_hi B TS) as E2. pose proof (ts_ial_w B TS) as E3.
destruct Hr as [<-|[<-|[]]]; cbn [fst snd aeval] in *; rewrite ?E1, ?E2, ?E3 in *; unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_W in *; zlia.
+   exact Mts.
+   exact Msi.
- unfold SF. exact (SF_ledger z _ (ALedger_same tfibsegs ly S md0 _ L (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) ltac:(unfold eager_used; rewrite m_vmmaps_wvb, m_vm_lazy_wvb; reflexivity))).
-   destruct BUD as [BUD PIN].
split; [| intros e He; unfold SF in He; rewrite SF_sec_extents in He; exact (PIN e He)].
assert (DA : depot_abytes S <= depot_abytes (st_final S cl l off n tr z)).
{ unfold depot_abytes. pose proof SF_parts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RdepS). unfold SF in RdepS. rewrite RdepS.
destruct (st_depot S) eqn:E2; [destruct (st_depot (depot_after z tr S)); unfold kNodesBlockSize, kStoreBlockSize; lia|].
assert (NE2 : st_depot S <> []) by (rewrite E2; discriminate). pose proof (depot_after_ne NE2) as NE2'.
destruct (st_depot (depot_after z tr S)) eqn:E1; [exfalso; exact (NE2' eq_refl)|]. lia. }
unfold abudget, sec_hulls in *. rewrite Rnev, Rsecs  . unfold SF. rewrite SF_sec_live. unfold EV_A in *. zlia.
-   exact (amwf_same md0 _ (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) MW).
-   destruct HS0 as [HS0 HZ0]. split.
+ intros a Ha NC HV. apply (BANDKEEP a Ha). apply (HS0 a Ha); [|exact HV].
intros CL. apply NC. destruct CL as [(k & Hk & Hst & Hr) | (cp & Hcp & Hr)].
* left. exists k. split; [unfold SF; rewrite SF_chunks; apply in_app_iff; left; exact Hk | exact (conj Hst Hr)].
* right. exists cp. split; [unfold SF, frames in Hcp |- *; rewrite Rfs; exact Hcp | exact Hr].
+
apply (ahz_keep ly S (SF z) mem0 mem'); [|exact HZ0]. intros g Hg Happ HF.
assert (HF0 : hfree ly S g) by (unfold hfree in HF |- *; unfold SF in HF; rewrite SF_sec_extents in HF; exact HF).
split; [exact HF0 | exact (ZKEEP g Hg Happ HF0)].
Qed.
(* AR at the OLD layout ly, the entry world W and the pre-Put maps, minus what the first Put changes (the depot cells,
   the NB / SB areas, am_depot): the input of AD3j.AR_but_depot_grow on the first-Put arm. *)
Lemma ABD_old : AD3j.AR_but_depot AD3j.as_const_g2f B ly (SF z) W mem' (with_vm_backing (m_vm_lazy md0) mat md0).
Proof.
pose proof HAR as (M0 & L & BUD & MW & HS0).
pose proof (SF_same z) as (Rregs & Rinit & Rsecs & Rarr & Rres & Rqt & Rqg & Rfs & Rii & Rnev & Rcache & Rdep).
pose proof (SF_ledger z (with_vm_backing (m_vm_lazy md0) mat md0) (ALedger_same tfibsegs ly S md0 (with_vm_backing (m_vm_lazy md0) mat md0) L
(m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) ltac:(unfold eager_used; rewrite m_vmmaps_wvb, m_vm_lazy_wvb; reflexivity))) as LF.
destruct M0 as [Mwf Mun Msy Mly Mpl Mco Mcow Mce Mfa Mfl Mde Msh Mzs Mju Mar Mcl Mze Mts Msi].
destruct LF as [Limg Llim Lres Lprim LQ Lhs Lsec Lcov Leag Lperm Lband Lsecx Ltop Limgcov Lshna].
unfold AD3j.AR_but_depot. cbv zeta.
split; [exact (proj1 MP)|]. split; [exact Mun|]. split; [exact Msy|].
split; [unfold sec_placed in *; unfold SF; rewrite SF_sec_extents; exact Mpl|].
split.
{ apply Forall_forall. intros c Hc2.
pose proof (proj1 (proj1 (AD3j.as_const_g2f_def B ly c) Hc2)) as Hc.
apply (cell_holds_agree2 rd0 rdD); [| exact (proj1 (Forall_forall _ _) Mco c Hc) | exact (proj1 (Forall_forall _ _) CSTD c Hc2)].
intros k Hk. pose proof (const_cells_zone c k Hc Hk) as Z1. pose proof (CZONE_untouched odd _ Z1) as (Ra & N1 & N3 & N4 & _ & _ & _). pose proof (FZ_czone _ Z1) as NF.
destruct (Z_lt_le_dec (aeval B ly (c_at c) + k) 0x170408) as [Hlo|Hge].
* left. apply AGREE0; try assumption. unfold DZONE, KnBlockExt.DZONE_at, AD3j.tfib_dzone_lo, AD3j.tfib_dzone_hi. pose proof blocks_facts as (NBhi & SBhi & _).
assert (NBc : snd (nb_ext ly) = 0 \/ snd (nb_ext ly) = kNodesBlockSize) by (rewrite nb_ext_eq; destruct (ly_NB ly =? 0); [left | right]; reflexivity).
assert (SBc : snd (sb_ext ly) = 0 \/ snd (sb_ext ly) = kStoreBlockSize) by (rewrite sb_ext_eq; destruct (ly_SB ly =? 0); [left | right]; reflexivity).
clear - Hlo NBhi SBhi NBc SBc. numconst. zlia.
* destruct (Z_lt_le_dec (aeval B ly (c_at c) + k) 0x5c0b90) as [Hlo2|Hge2].
-- right. apply AGREED; [exact Ra|]. unfold DZONE, KnBlockExt.DZONE_at, AD3j.tfib_dzone_lo, AD3j.tfib_dzone_hi. left. zlia.
-- left. apply AGREE0; try assumption. unfold DZONE, KnBlockExt.DZONE_at, AD3j.tfib_dzone_lo, AD3j.tfib_dzone_hi. unfold CZONE in Z1. pose proof blocks_facts as (NBhi & SBhi & TNB & TSB & _).
pose proof HC_NB as [CNB CSB]. unfold zdisjoint in CNB, CSB, TNB, TSB. cbn [fst snd] in CNB, CSB, TNB, TSB. unfold T in Z1.
pose proof (pairwise_ij _ _ 4 2 _ _ (lo_disj ly LY) (nb_ext_nth_st ly) eq_refl) as DNB. pose proof (pairwise_ij _ _ 5 1 _ _ (lo_disj ly LY) (sb_ext_nth_st ly) eq_refl) as DSB. unfold zdisjoint in DNB, DSB. cbn [fst snd] in DNB, DSB.
clear - Z1 Hge2 NBhi SBhi CNB CSB TNB TSB DNB DSB. unfold TFIB_TSD in *. numconst. zlia. }
split; [exact Mcow|].
split.
{ intros c Hc ND. pose proof (cells_nodepot c Hc ND) as X. exact X. }
split; [exact fa_final|]. split; [exact flags_final|]. split; [exact shadow_final|]. split; [exact zshadow_final|].
split; [exact (proj1 vis_final)|].
split; [exact (proj1 (proj2 vis_final))|].
split; [exact (proj2 (proj2 vis_final))|].
split.
{ apply Forall_forall. intros r Hr i Hi. rewrite <- (proj1 (Forall_forall _ _) Mze r Hr i Hi). apply AGX.
* pose proof (aso_ialloc _ Msy) as [I1 I2].
eapply (own_area B ly S rd0 (as_ialloc_lo B, as_ialloc_hi B - as_ialloc_lo B)); [exact MA | cbn; tauto |].
unfold ialloc_zero in Hr. cbn [fst snd]. destruct Hr as [<-|[<-|[]]]; cbn [fst snd aeval] in *; zlia.
* apply Z_low. unfold TFIB_IMG_LO, YImgTop.IMG_LO, YImgTop.IMG_TOP. unfold ialloc_zero in Hr. pose proof (ts_ial_lo B TS) as E1. pose proof (ts_ial_hi B TS) as E2. pose proof (ts_ial_w B TS) as E3.
destruct Hr as [<-|[<-|[]]]; cbn [fst snd aeval] in *; rewrite ?E1, ?E2, ?E3 in *; unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_W in *; zlia. }
split; [exact Mts|]. split; [exact Msi|].
split; [exact Limg|]. split; [exact Llim|]. split; [exact Lres|]. split; [exact Lprim|]. split; [exact LQ|]. split; [exact Lhs|].
split; [exact Lsec|]. split; [intros e He _; exact (Lcov e He)|]. split; [exact Leag|].
split; [intros z0 Hz0 _; exact (Lperm z0 Hz0)|]. split; [exact Lband|]. split; [exact Lsecx|]. split; [exact Ltop|].
split; [exact Limgcov|]. split; [exact Lshna|].
split.
{ destruct BUD as [BUD PIN].
split; [| intros e He; unfold SF in He; rewrite SF_sec_extents in He; exact (PIN e He)].
assert (DA : depot_abytes S <= depot_abytes (st_final S cl l off n tr z)).
{ unfold depot_abytes. pose proof SF_parts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RdepS). unfold SF in RdepS. rewrite RdepS.
destruct (st_depot S) eqn:E2; [destruct (st_depot (depot_after z tr S)); unfold kNodesBlockSize, kStoreBlockSize; lia|].
assert (NE2 : st_depot S <> []) by (rewrite E2; discriminate). pose proof (depot_after_ne NE2) as NE2'.
destruct (st_depot (depot_after z tr S)) eqn:E1; [exfalso; exact (NE2' eq_refl)|]. lia. }
unfold SF in *. unfold abudget, sec_hulls in *. rewrite Rnev, Rsecs. rewrite SF_sec_live. unfold EV_A in *. zlia. }
split; [exact (amwf_same md0 _ (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) MW)|].
destruct HS0 as [HS0 HZ0]. split.
+ intros a Ha NC HV. apply (BANDKEEP a Ha). apply (HS0 a Ha); [|exact HV].
intros CL. apply NC. destruct CL as [(k & Hk & Hst & Hr) | (cp & Hcp & Hr)].
* left. exists k. split; [unfold SF; rewrite SF_chunks; apply in_app_iff; left; exact Hk | exact (conj Hst Hr)].
* right. exists cp. split; [unfold SF, frames in Hcp |- *; rewrite Rfs; exact Hcp | exact Hr].
+
apply (ahz_keep ly S (SF z) mem0 mem'); [|exact HZ0]. intros g Hg Happ HF.
assert (HF0 : hfree ly S g) by (unfold hfree in HF |- *; unfold SF in HF; rewrite SF_sec_extents in HF; exact HF).
split; [exact HF0 | exact (ZKEEP g Hg Happ HF0)].
Qed.

End b0.
Hypothesis HDPOST : forall ly' W' md' z m, DPOST ly' W' md' z m -> DPOST3 ly' W' md' z m.
(* The first Put's arm of AR_final (finish text v1.2 steps 1-7): ABD_old at the old layout / entry world with FZ := the two
   new blocks, AD3j.AR_but_depot_grow to the grown layout / post-Put world / final model, AD3j.first_malloc_AR. *)
Lemma AR_final_first : st_depot S = [] -> forall ly' md' odd z W' regs' mem' mat,
at_RET_at ly' md' odd z W' (mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md') mat md')) ->
(odd = true <-> n mod 8 <> 0) -> MPF z -> AR tfibsegs B ly S W mem0 md0 ->
AR tfibsegs B ly' (SF z) W' mem' (with_vm_backing (m_vm_lazy md') mat md').
Proof.
intros ES ly' md' odd z W' regs' mem' mat HR Hodd MP HAR.
destruct HR as (PE & LY' & IMG' & WLE & regs2 & mem2 & mat2 & EC & R10 & RCS & (memD & DP & PRD & EQD) & MEQF & PRS & PRW & VALS).
injection EC as E1 E2 E3. subst regs2 mem2. try clear EC.
destruct (HDPOST _ _ _ _ _ DP) as (AOK & DEP3 & CK & T1).
destruct VALS as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11).
pose proof (proj1 (proj1 (proj2 (proj2 (proj1 (depot_ok_pre B ly _ S ES) (am_depot B ly S _ HARm))))) ES) as [HN0 HS0].
destruct (T1 ES) as (Ez & regsc & memc & mdc & regs2c & PEc & FPP). subst z.
pose proof FPP as FPP0. unfold AD3j.depot_first_put_post in FPP0. cbv zeta in FPP0.
destruct FPP0 as (regsP & memP & EcP & _ & _ & _ & _ & _ & _ & FACTS & _ & _ & _ & IA1 & _ & IA2 & _ & FNB & FSB & _).
pose proof FACTS as (HNz & HSz & _).
destruct PE as [(Ely & EW & SBM) | (nb & sb & HN0' & HS0' & NZ & SZ & Ely & HG & WA & WH & IO & VM & LZ)].
{ exfalso. rewrite Ely in HNz. exact (HNz HN0). }
assert (Enb : ly_NB ly' = nb) by (rewrite Ely; reflexivity). assert (Esb : ly_SB ly' = sb) by (rewrite Ely; reflexivity).
rewrite Enb in IA1, FNB. rewrite Esb in IA2, FSB.
set (FZ' := fun a => (nb <= a < nb + kNodesBlockSize) \/ (sb <= a < sb + kStoreBlockSize)).
assert (NOTIN : forall e a, In e (AD3j.first_put_avoid ly S) -> fst e <= a < fst e + snd e -> ~ FZ' a).
{ intros e a He Ha [Hf|Hf].
- pose proof (proj1 (Forall_forall _ _) FNB e He) as D. unfold zdisjoint in D. cbn [fst snd] in D. lia.
- pose proof (proj1 (Forall_forall _ _) FSB e He) as D. unfold zdisjoint in D. cbn [fst snd] in D. lia. }
assert (APP : forall a, FZ' a -> a < kLowShadowBeg \/ kHighMemBeg <= a).
{ intros a [Hf|Hf]; [unfold in_app in IA1 | unfold in_app in IA2]; lia. }
assert (INEXT : forall e, In e [(ly_prim ly, kPrimResvSize); (ly_Q ly, kPtrArrayResv); (ly_T ly, kThreadObjSize); (ly_F ly, kFakeStackSize);
(ly_C ly, 256); (ly_D ly, 4096); (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly); ly_img ly] -> In e (AD3j.first_put_avoid ly S)).
{ intros e He. unfold AD3j.first_put_avoid, AD3g.ext_but_NB. apply in_app_iff. left. apply in_app_iff. left. exact He. }
pose proof IMG as [IC1 IC2].
assert (FZDp : forall a, FZ' a -> ~ aowned B ly S a /\ ~ CZONE a /\ ~ (kLowShadowBeg <= a < kHighShadowEnd)).
{ intros a Hf. split; [|split].
- intros [Ho _]. destruct Ho as [O|[O|[O|[O|O]]]].
+ apply Exists_exists in O as (r & Hr & Ha).
pose proof (proj1 (Forall_forall _ _) (am_static_img _ _ _ _ HARm) r ltac:(apply in_app_iff; left; exact Hr)) as ZS.
unfold zr_sub, in_zr in ZS, Ha. apply (NOTIN (ly_img ly) a); [apply INEXT; cbn; tauto | lia | exact Hf].
+ apply Exists_exists in O as (e & He & Ha). unfold owned_extents in He. rewrite HN0, HS0 in He. cbn in He. unfold in_zr in Ha.
destruct He as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; cbn [fst snd] in Ha; try lia;
(lazymatch type of Ha with ?lo <= a < ?lo + ?len => apply (NOTIN (lo, len) a); [apply INEXT; cbn; tauto | cbn [fst snd]; exact Ha | exact Hf] end).
+ apply (NOTIN (ly_C ly, 256) a); [apply INEXT; cbn; tauto | exact O | exact Hf].
+ apply Exists_exists in O as (e & He & Ha). apply (NOTIN e a); [|exact Ha|exact Hf].
unfold AD3j.first_put_avoid. apply in_app_iff; right. apply in_app_iff; right. apply in_app_iff; left. exact He.
+ pose proof (owned_shadow_bound B ly S _ a HARm O) as SBd. destruct (APP a Hf); unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *; lia.
- intros Hc. unfold CZONE in Hc. destruct Hc as [H|[H|[H|[H|[H|H]]]]].
+ apply (NOTIN (ly_img ly) a); [apply INEXT; cbn; tauto | unfold TFIB_IMG_LO, TFIB_IMG_END, YImgTop.IMG_LO, YImgTop.IMG_TOP in *; lia | exact Hf].
+ destruct (APP a Hf); unfold kLowShadowBeg, kHighMemBeg in *; lia.
+ apply (NOTIN (ly_T ly, kThreadObjSize) a); [apply INEXT; cbn; tauto | unfold T, kThreadObjSize in *; cbn [fst snd]; lia | exact Hf].
+ apply (NOTIN (ly_C ly, 256) a); [apply INEXT; cbn; tauto | cbn [fst snd]; lia | exact Hf].
+ apply (NOTIN (ly_img ly) a); [apply INEXT; cbn; tauto | unfold TFIB_TSD, TFIB_IMG_LO, TFIB_IMG_END, YImgTop.IMG_LO, YImgTop.IMG_TOP in *; lia | exact Hf].
+ apply (NOTIN (ly_D ly, 4096) a); [apply INEXT; cbn; tauto | cbn [fst snd]; lia | exact Hf].
- intros Hb. destruct (APP a Hf); unfold kLowShadowBeg, kHighShadowEnd, kHighMemBeg in *; lia. }
assert (ZT : forall a, KnBlockExt.DZONE_at AD3j.tfib_dzone_lo AD3j.tfib_dzone_hi ly' a <-> DZONE a \/ FZ' a).
{ intros a. unfold DZONE, KnBlockExt.DZONE_at. rewrite (nb_ext_set ly' HNz), (sb_ext_set ly' HSz), Enb, Esb.
rewrite (nb_ext_eq ly), (sb_ext_eq ly), HN0, HS0. cbn [fst snd Z.eqb]. unfold FZ'. split; intros; lia. }
pose proof Kv_range as [K1 K2]. pose proof high_facts as (F1 & F2 & F3 & F4 & F5 & F6 & _). pose proof derived_ranges as DR.
pose proof NLOf as (Nlo & RZr & RZ8 & _).
pose proof (lo_top ly LY) as (LT1 & LT2 & LT3 & LT4 & LT5 & LT6 & LT7).
assert (KP : ly_prim ly <= Kv /\ Kv + 2 ^ 16 + 4096 <= ly_prim ly + kPrimResvSize) by (clear - F4 F5 K1 K2; unfold kSpaceSize, kPrimResvSize in *; zlia).
assert (NPRIM : forall a, ly_prim ly <= a < ly_prim ly + kPrimResvSize -> ~ FZ' a)
by (intros a Ha; apply (NOTIN (ly_prim ly, kPrimResvSize) a); [apply INEXT; cbn; tauto | exact Ha]).
assert (NTT : forall a, ly_T ly <= a < ly_T ly + kThreadObjSize -> ~ FZ' a)
by (intros a Ha; apply (NOTIN (ly_T ly, kThreadObjSize) a); [apply INEXT; cbn; tauto | exact Ha]).
assert (NSH : forall a, kLowShadowBeg <= a < kHighMemBeg -> ~ FZ' a) by (intros a Ha Hf; destruct (APP a Hf); unfold kLowShadowBeg, kHighMemBeg in *; lia).
assert (WHa : forall a, 0 <= a < 2 ^ 64 -> ~ FZ' a -> w_H W' (Z_to_bv 64 a) = w_H W (Z_to_bv 64 a)).
{ intros a Ra NF. apply WH; rewrite unsigned_lit_small by exact Ra; intros X; apply NF; unfold FZ'; tauto. }
assert (PRDw : forall a, DZONE a \/ FZ' a -> apresent (w_H W) mem0 a -> apresent (w_H W) memD a).
{ intros a Hz Hp. destruct (PRD a (proj2 (ZT a) Hz) Hp) as [_ Hb]. exact (conj (proj1 Hp) Hb). }
assert (EQDw : forall x : word, DZONE (bv_unsigned x) \/ FZ' (bv_unsigned x) -> mem' x = memD x).
{ intros x Hz. exact (EQD x (proj2 (ZT _) Hz)). }
assert (MEQFw : forall x : word, ~ WIN odd (bv_unsigned x) -> ~ DZONE (bv_unsigned x) -> ~ FZ' (bv_unsigned x) ->
~ (Kv + RZ <= bv_unsigned x < Kv + RZ + n) -> ~ (SUv <= bv_unsigned x < SUv + N8D / 8) -> mem' x = mem0 x).
{ intros x N1 N2 N3 N4 N5. apply MEQF; [exact N1 | intros Hz; destruct (proj1 (ZT _) Hz) as [Hd|Hd]; [exact (N2 Hd) | exact (N3 Hd)] | exact N4 | exact N5]. }
assert (PRSw : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem' a).
{ intros a Ha. exact (conj (proj1 (Hpres0 a Ha)) (proj2 (PRS a Ha))). }
assert (TB : 4096 <= ly_T ly /\ ly_T ly + kThreadObjSize < 2 ^ 64).
{ pose proof (proj1 (Forall_forall _ _) (lo_app _ LY) (ly_T ly, kThreadObjSize) ltac:(unfold owned_extents; cbn; tauto)) as TA.
clear - TA. unfold in_app in TA. cbn [fst snd] in TA. ceil. unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg, kThreadObjSize in *. lia. }
assert (WINT_T : forall a, WINT a -> 0 <= a < 2 ^ 64 /\ ly_T ly <= a < ly_T ly + kThreadObjSize).
{ intros a Hw. clear - Hw TB Hcl T. unfold WINT, Pv, SSLOTv, t_cache, t_stats, t_unwinding, kThreadObjSize in *. unfold T in *. lia. }
assert (CHK_P : forall a, Kv <= a < Kv + RZ + n -> 0 <= a < 2 ^ 64 /\ ly_prim ly <= a < ly_prim ly + kPrimResvSize).
{ intros a Ha. split; [clear - Ha Nlo RZr DR; zlia | clear - Ha KP Nlo RZr DR; zlia]. }
assert (PB_S : forall a, PBW odd a -> 0 <= a < 2 ^ 64 /\ kLowShadowBeg <= a < kHighMemBeg).
{ intros a [_ Ha]. clear - Ha DR. unfold kLowShadowBeg, kHighMemBeg in *. zlia. }
assert (PRWw : forall a, WINT a \/ (Kv <= a < Kv + RZ + n) \/ PBW odd a -> apresent (w_H W) mem' a).
{ intros a Hw. destruct (PRW a Hw) as [Hh Hb]. split; [|exact Hb].
destruct Hw as [Hw|[Hw|Hw]].
- destruct (WINT_T a Hw) as [Ra HT]. rewrite <- (WHa a Ra (NTT a HT)). exact Hh.
- destruct (CHK_P a Hw) as [Ra HP]. rewrite <- (WHa a Ra (NPRIM a HP)). exact Hh.
- destruct (PB_S a Hw) as [Ra HS]. rewrite <- (WHa a Ra (NSH a HS)). exact Hh. }
assert (VMw : forall a (w : nat) v0, (forall k, (k < w)%nat -> 0 <= a + Z.of_nat k < 2 ^ 64 /\ ~ FZ' (a + Z.of_nat k)) ->
val_mem tfibsegs (mrestrict (w_H W') mem') a w v0 -> val_mem tfibsegs (mrestrict (w_H W) mem') a w v0).
{ intros a w v0 HkF HvM k0 Hk0. rewrite <- (HvM k0 Hk0). unfold mbyte, mrestrict. destruct (HkF k0 Hk0) as [Ra NF]. rewrite (WHa _ Ra NF). reflexivity. }
assert (KR : forall o (w : nat), 0 <= o -> o + Z.of_nat w <= 2 ^ 16 -> forall k, (k < w)%nat -> 0 <= Kv + o + Z.of_nat k < 2 ^ 64 /\ ~ FZ' (Kv + o + Z.of_nat k)).
{ intros o w Ho Hw k Hk. split; [clear - DR Ho Hw Hk; zlia | apply NPRIM; clear - KP Ho Hw Hk; zlia]. }
pose proof (VMw Kv 8%nat _ ltac:(intros k Hk; pose proof (KR 0 8%nat ltac:(lia) ltac:(lia) k Hk) as X; rewrite Z.add_0_r in X; exact X) V1) as V1w.
pose proof (VMw (Kv + 8) 8%nat _ (KR 8 8%nat ltac:(lia) ltac:(lia)) V2) as V2w.
pose proof (VMw (Kv + RZ - 16) 1%nat _ ltac:(intros k Hk; replace (Kv + RZ - 16) with (Kv + (RZ - 16)) by lia; apply (KR (RZ - 16) 1%nat); [clear - RZr; zlia | clear - RZr; zlia | exact Hk]) V3) as V3w.
pose proof (VMw (Kv + RZ - 15) 1%nat _ ltac:(intros k Hk; replace (Kv + RZ - 15) with (Kv + (RZ - 15)) by lia; apply (KR (RZ - 15) 1%nat); [clear - RZr; zlia | clear - RZr; zlia | exact Hk]) V4) as V4w.
pose proof (VMw (Kv + RZ - 14) 2%nat _ ltac:(intros k Hk; replace (Kv + RZ - 14) with (Kv + (RZ - 14)) by lia; apply (KR (RZ - 14) 2%nat); [clear - RZr; zlia | clear - RZr; zlia | exact Hk]) V5) as V5w.
pose proof (VMw (Kv + RZ - 12) 4%nat _ ltac:(intros k Hk; replace (Kv + RZ - 12) with (Kv + (RZ - 12)) by lia; apply (KR (RZ - 12) 4%nat); [clear - RZr; zlia | clear - RZr; zlia | exact Hk]) V6) as V6w.
pose proof (VMw Pv 4%nat _ ltac:(intros k Hk; destruct (WINT_T (Pv + Z.of_nat k) ltac:(unfold WINT; left; lia)) as [Ra HT]; exact (conj Ra (NTT _ HT))) V7) as V7w.
pose proof (VMw (T + t_unwinding) 1%nat _ ltac:(intros k Hk; destruct (WINT_T (T + t_unwinding + Z.of_nat k) ltac:(unfold WINT; right; right; right; lia)) as [Ra HT]; exact (conj Ra (NTT _ HT))) V8) as V8w.
assert (V10w : odd = true -> val_mem tfibsegs (mrestrict (w_H W) mem') PBv 1 (n mod 8)).
{ intros Ho. apply (VMw PBv 1%nat _); [|exact (V10 Ho)]. intros k Hk.
destruct (PB_S (PBv + Z.of_nat k) ltac:(split; [exact Ho | lia])) as [Ra HS]. exact (conj Ra (NSH _ HS)). }
assert (CSTDw : Forall (cell_holds B ly (aview tfibsegs (w_H W) memD)) (AD3j.as_const_g2f B ly)).
{ apply Forall_forall. intros c Hc2. pose proof (proj1 (proj1 (AD3j.as_const_g2f_def B ly c) Hc2)) as Hc.
assert (Hc2' : In c (AD3j.as_const_g2f B ly')).
{ rewrite Ely. unfold AD3j.as_const_g2f in *. rewrite (ts_const B TS) in *.
change (Tfib_const (AD3c.set_ly_SB (AD3g.set_ly_NB ly nb) sb)) with (Tfib_const ly). exact Hc2. }
pose proof (proj1 (Forall_forall _ _) CK c Hc2') as H1.
pose proof Hc as Hc0. rewrite (ts_const B TS) in Hc0.
pose proof (proj1 (forallb_forall _ _) (AD3j.b2_const_ok ly) c Hc0) as OK. unfold AD3j.b2_cell_ok in OK.
apply andb_prop in OK as [OK _]. apply andb_prop in OK as [N1 N2].
assert (H2 : cell_holds B ly (aview tfibsegs (w_H W') memD) c).
{ rewrite Ely in H1. unfold cell_holds in *. rewrite (AD3j.aeval_nonbsb B ly nb sb _ N1) in H1.
destruct (c_val c) as [e|mk v0] eqn:EV; [| exact H1]. rewrite (AD3j.aeval_nonbsb B ly nb sb _ N2) in H1. exact H1. }
apply (AD3j.cell_agree B ly (aview tfibsegs (w_H W') memD) (aview tfibsegs (w_H W) memD) c); [|exact H2].
intros k Hk. pose proof (const_cells_zone c k Hc Hk) as Z1. pose proof (CZONE_untouched odd _ Z1) as (Ra & _).
unfold aview, mbyte, mrestrict. rewrite (WHa _ Ra (fun Hf => proj1 (proj2 (FZDp _ Hf)) Z1)). reflexivity. }
assert (ABD0 : AD3j.AR_but_depot AD3j.as_const_g2f B ly (SF 1) W mem' (with_vm_backing (m_vm_lazy md0) mat md0)).
{ eapply ABD_old with (zn := nb) (ln := kNodesBlockSize) (zs := sb) (ls := kStoreBlockSize) (memD := memD) (odd := odd);
first [ exact FZDp | exact Hodd | exact MP | exact HAR | exact AOK | exact CSTDw | exact PRDw | exact EQDw | exact MEQFw | exact PRSw
| exact PRWw | exact V1w | exact V2w | exact V3w | exact V4w | exact V5w | exact V6w | exact V7w | exact V8w | exact V9 | exact V10w
| exact V11 | (intros X; exfalso; exact (X ES)) ]. }
set (mdold := with_vm_backing (m_vm_lazy md0) mat md0).
set (mdf := with_vm_backing (m_vm_lazy md') mat md').
set (cP := mkCfg (mkst regs2c (Z_to_bv 64 0x3108c) memD (seg_rom tfibsegs)) md').
pose proof PEc as PEc0.
destruct PEc as [(Elyc & _ & _) | (nbc & sbc & _ & _ & _ & _ & Elyc & _ & WAc & _ & _ & VMc & LZc)].
{ exfalso. rewrite Elyc in HNz. exact (HNz HN0). }
assert (LZE : m_vm_lazy md0 = m_vm_lazy mdc).
{ rewrite LZ in LZc. injection LZc as _ X. exact X. }
assert (VME : m_vmmaps md0 = m_vmmaps mdc).
{ rewrite VM in VMc. unfold YK0v.mmap_model in VMc. cbn in VMc.
destruct (m_vmmaps md0), (m_vmmaps mdc). cbn in VMc. injection VMc as X1 _ _ X2 X3 X4 X5 X6 X7 X8. subst. reflexivity. }
assert (MAP1 : m_vmmaps mdold = m_vmmaps mdc) by (unfold mdold; rewrite m_vmmaps_wvb; exact VME).
assert (LZ1 : m_vm_lazy mdold = m_vm_lazy mdc) by (unfold mdold; rewrite m_vm_lazy_wvb; exact LZE).
assert (MAP2 : m_vmmaps mdf = m_vmmaps md') by (unfold mdf; apply m_vmmaps_wvb).
assert (LZ2 : m_vm_lazy mdf = m_vm_lazy md') by (unfold mdf; apply m_vm_lazy_wvb).
assert (LYF : ly' = set_ly_SB (set_ly_NB ly (ly_NB ly')) (ly_SB ly')) by (rewrite Enb, Esb; exact Ely).
pose proof (SF_same 1) as (Rregs & Rinit & Rsecs & Rarr & Rres & Rqt & Rqg & Rfs & Rii & Rnev & Rcache & Rdep).
assert (DEP1 : st_depot (SF 1) = st_depot (depot_after 1 tr S)) by (unfold SF; rewrite Rdep; unfold depot_after; cbn; reflexivity).
assert (ABY : A_bytes (w_A W') <= abudget (SF 1)).
{ pose proof HAR as (_ & _ & BUD & _ & _). destruct BUD as [BUD _].
assert (DA : depot_abytes (SF 1) = kNodesBlockSize + kStoreBlockSize) by (unfold depot_abytes; rewrite DEP1; unfold depot_after; cbn; rewrite ES; reflexivity).
assert (DA0 : depot_abytes S = 0) by (unfold depot_abytes; rewrite ES; reflexivity).
rewrite WA. cbn [A_bytes fst snd]. unfold abudget in *. rewrite DA. rewrite DA0 in BUD.
unfold SF in *. unfold sec_hulls in *. rewrite Rnev, Rsecs. rewrite SF_sec_live. unfold EV_A in *. unfold kNodesBlockSize, kStoreBlockSize in *. zlia. }
pose proof (AD3j.AR_but_depot_grow layout_grow AD3j.kd_inst_grow_NB AD3j.kd_inst_grow_SB AD3j.kd_inst_grow_trans depot_ok
AD3j.kd_inst_depot_ok_pre AD3j.kd_inst_depot_ok_post AD3j.as_const_g2f AD3j.as_const_g2f_def am_depot_mono_d
AD3j.kd_inst_am_depot_mono_intro am_alloc_depot_d AD3j.kd_inst_am_alloc_depot_intro
B W ly S regsc memc mdc tr ly' W' md' cP (SF 1) mem' ly ly' mdold mdf
TS ES HN0 LY IMG PEc0 FPP eq_refl LYF MAP1 LZ1 MAP2 LZ2 WLE ABY ABD0) as ABD1.
assert (FRM : forall a : word, ((AD3j.tfib_dzone_lo <= bv_unsigned a < AD3j.tfib_dzone_hi) \/
(fst (nb_ext ly') <= bv_unsigned a < fst (nb_ext ly') + snd (nb_ext ly')) \/
(fst (sb_ext ly') <= bv_unsigned a < fst (sb_ext ly') + snd (sb_ext ly'))) ->
mem' a = ms_mem (cfg_ms cP) a /\ w_H W' a = w_H W' a).
{ intros a Ha. split; [|reflexivity]. unfold cP. cbn [cfg_ms ms_mem]. apply EQD. unfold KnBlockExt.DZONE_at. exact Ha. }
pose proof (AD3j.first_malloc_AR layout_grow AD3j.kd_inst_grow_NB AD3j.kd_inst_grow_SB AD3j.kd_inst_grow_trans depot_ok
AD3j.kd_inst_depot_ok_pre AD3j.kd_inst_depot_ok_post AD3j.as_const_g2f AD3j.as_const_g2f_def am_depot_mono_d
AD3j.kd_inst_am_depot_mono_intro am_alloc_depot_d AD3j.kd_inst_am_alloc_depot_intro
B W ly S regsc memc mdc tr ly' W' md' cP (SF 1) W' mem' mdf
TS ES HN0 LY IMG PEc0 FPP ABD1 DEP1 FRM ltac:(intros e He; rewrite MAP2; exact He) ltac:(intros e He; rewrite LZ2; exact He)) as (ARf & _).
exact ARf.
Qed.
Lemma AR_final : AR_final_stmt.
Proof.
intros ly' md' odd z W' regs' mem' mat HR Hodd MP HAR.
destruct (st_depot S) as [|t0 l0] eqn:ES.
{ exact (AR_final_first ES ly' md' odd z W' regs' mem' mat HR Hodd MP HAR). }
assert (NE : st_depot S <> []) by (rewrite ES; discriminate).
destruct HR as (PE & LY' & IMG' & WLE & regs2 & mem2 & mat2 & EC & R10 & RCS & (memD & DP & PRD & EQD) & MEQF & PRS & PRW & VALS).
injection EC as E1 E2 E3. subst regs2 mem2. try clear EC.
destruct PE as [(-> & -> & SBM) | (nb & sb & HN0 & _)].
2:{ exfalso. pose proof (depot_ok_mapped B ly _ S (am_depot B ly S _ HARm) NE) as [HNz _]. exact (HNz HN0). }
destruct (HDPOST _ _ _ _ _ DP) as (AOK & DEP3 & CK & _).
destruct VALS as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11).
pose proof (same_but_materialized_frame _ _ SBM) as (_ & _ & LZ & _).
assert (EW : with_vm_backing (m_vm_lazy md') mat md' = with_vm_backing (m_vm_lazy md0) mat md0).
{ rewrite (same_but_materialized_wvb md0 md' SBM). rewrite m_vm_lazy_wvb. rewrite wvb_wvb. reflexivity. }
rewrite EW.
assert (NFZ : forall a, ~ ((0 <= a < 0 + 0) \/ (0 <= a < 0 + 0))) by (intros a [X|X]; lia).
assert (FZD0 : forall a, (0 <= a < 0 + 0) \/ (0 <= a < 0 + 0) -> ~ aowned B ly S a /\ ~ CZONE a /\ ~ (kLowShadowBeg <= a < kHighShadowEnd))
by (intros a Hf; exfalso; exact (NFZ a Hf)).
assert (DEPD0 : st_depot S <> [] -> depot_mem_ok B ly (depot_after z tr S) (aview tfibsegs (w_H W) memD)).
{ intros NE0. apply DEP3. unfold depot_after. destruct (z =? 0); cbn; [exact NE0|]. intros Hc. apply app_eq_nil in Hc as [_ Hc]. discriminate. }
assert (PRD0 : forall a, DZONE a \/ ((0 <= a < 0 + 0) \/ (0 <= a < 0 + 0)) -> apresent (w_H W) mem0 a -> apresent (w_H W) memD a).
{ intros a [Hd|Hf] Hp; [exact (PRD a Hd Hp) | exfalso; exact (NFZ a Hf)]. }
assert (EQD0 : forall x : word, DZONE (bv_unsigned x) \/ ((0 <= bv_unsigned x < 0 + 0) \/ (0 <= bv_unsigned x < 0 + 0)) -> mem' x = memD x).
{ intros x [Hd|Hf]; [exact (EQD x Hd) | exfalso; exact (NFZ _ Hf)]. }
assert (MEQF0 : forall x : word, ~ WIN odd (bv_unsigned x) -> ~ DZONE (bv_unsigned x) -> ~ ((0 <= bv_unsigned x < 0 + 0) \/ (0 <= bv_unsigned x < 0 + 0)) ->
~ (Kv + RZ <= bv_unsigned x < Kv + RZ + n) -> ~ (SUv <= bv_unsigned x < SUv + N8D / 8) -> mem' x = mem0 x).
{ intros x N1 N2 _ N3 N4. exact (MEQF x N1 N2 N3 N4). }
eapply AR_transport with (zn := 0) (ln := 0) (zs := 0) (ls := 0) (memD := memD) (odd := odd);
first [ exact NE | exact FZD0 | exact Hodd | exact MP | exact HAR | exact AOK | exact DEPD0 | exact CK | exact PRD0 | exact EQD0 | exact MEQF0
| exact PRS | exact PRW | exact V1 | exact V2 | exact V3 | exact V4 | exact V5 | exact V6 | exact V7 | exact V8 | exact V9 | exact V10 | exact V11 ].
Qed.
Lemma LEAF_final : AR tfibsegs B ly S W mem0 md0 -> forall odd z W' c',
at_RET odd z W' c' -> (odd = true <-> n mod 8 <> 0) -> MPF z ->
malloc_leaf tfibsegs B ly S W regs0 mem0 md0 n (ck_user Kc, SF z) W' c'.
Proof. intros HAR odd z W' c' HR Hodd MP. exact (LEAF_ok AR_final HAR odd z W' c' HR Hodd MP). Qed.
End a0.
End f.
