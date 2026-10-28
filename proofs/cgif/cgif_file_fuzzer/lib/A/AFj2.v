(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG04 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1w AE3d AFhy AFis AFhz AFi3 AFiy AFiz AFj0 AFix AFj1 AFip AFiq AFir.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Set Printing Depth 50. Set Printing Width 180.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Ltac zlia := first [ lia | ceil; unfold zone3, zone3cases, in_app, app_addr, in_band_rw, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, ASAN_CEIL in *; lia ].
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
t_cache, t_unwinding, t_stats, ASTACK, TFIB_IMG_END, TFIB_IMG_LO, kLowShadowBeg, UNW_STK, BST_SIZE, DEP_STK in *.
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
Section e.
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
Local Abbreviation SHBv := (@AFis.SHBv ).
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
Variable DPOST : Z -> (word -> option byte) -> Prop.
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
| apply off_NB; unfold kNodesBlockSize; tac
| apply off_SB; unfold kStoreBlockSize; tac
| unfold off_img; unfold TFIB_IMG_LO; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; tac ].
Hypothesis Hkz : 1 <= kz <= 6.
Hypothesis Nrange : rz_lo kz <= n <= rz_hi kz.
Local Abbreviation kz_cases := (@AFis.kz_cases kz Hkz).
Local Abbreviation RZ_facts := (@AFis.RZ_facts n kz Hkz Nrange).
Local Abbreviation RZ_num := (@AFis.RZ_num n kz Hkz Nrange).
Ltac numconst ::= (ceil; unfold zone3, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize,
t_cache, t_unwinding, t_stats, ASTACK, TFIB_IMG_END, TFIB_IMG_LO, kLowShadowBeg, UNW_STK, BST_SIZE, DEP_STK in * ); try pose proof RZ_num as RZN.
Local Abbreviation derived_ranges := (@AFis.derived_ranges _ ly regs0 mem0 n cl cnt v kz Hcl Hv Hcnt Hv2 LY IMG DPOST Hkz Nrange).
Hypothesis Hcl_def : cl = class_id (R8v + RZ).
Local Abbreviation NDv_facts := (@AFis.NDv_facts ly regs0 mem0 n v kz DPOST Hkz Nrange).
Local Abbreviation CL_hi_E := (@AFis.CL_hi_E ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz DPOST Hkz Nrange Hcl_def).
Local Abbreviation CL_lo_E := (@AFis.CL_lo_E ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz DPOST Hkz Nrange Hcl_def).
Local Abbreviation WIN1 := (@AFis.WIN1 ly regs0 n cl v kz).
Local Abbreviation WIN1_WIN := (@AFis.WIN1_WIN ly regs0 mem0 n cl v kz DPOST).
Local Abbreviation WIN_odd := (@AFis.WIN_odd ly regs0 mem0 n cl cnt v jb kz Hcl Hv Hcnt Hjb Hsp DPOST Hkz Nrange).
Local Abbreviation WIN1_odd := (@AFis.WIN1_odd ly regs0 mem0 n cl cnt v jb kz Hcl Hv Hcnt Hjb Hsp DPOST Hkz Nrange).
Local Abbreviation WSKEL := (@AFis.WSKEL ).
Local Abbreviation WSKEL1 := (@AFis.WSKEL1 ).
Local Abbreviation win_sub := (@AFis.win_sub ).
Local Abbreviation win_sub_sound := (@AFis.win_sub_sound ly regs0 mem0 n v kz Hv DPOST).
Local Abbreviation WSKEL_WIN := (@AFis.WSKEL_WIN _ ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz Hcl Hv Hcnt Hv2 LY IMG DPOST Hkz Nrange).
Local Abbreviation WSKEL1_WIN1 := (@AFis.WSKEL1_WIN1 _ ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz Hcl Hv Hcnt Hv2 LY IMG DPOST Hkz Nrange).
Local Abbreviation windows_WIN := (@AFis.windows_WIN _ ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz Hcl Hv Hcnt Hv2 LY IMG DPOST Hkz Nrange).
Local Abbreviation windows_WIN1 := (@AFis.windows_WIN1 _ ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz Hcl Hv Hcnt Hv2 LY IMG DPOST Hkz Nrange).
Local Abbreviation frame_WIN1 := (@AFis.frame_WIN1 _ ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz Hcl Hv Hcnt Hv2 LY IMG DPOST Hkz Nrange).
Local Abbreviation WIN_not_high := (@AFis.WIN_not_high _ ly regs0 mem0 n cl cnt v kz Hcl Hv Hcnt Hv2 LY IMG Hsp DPOST Hkz Nrange).
Variables (mat0 : list word).
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 0x52930) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis U1 : tfib_unwind_spec.
Hypothesis SEED : st_ok tfibsegs E0 SS0 (restrict (w_H W) (mkst regs0 (w64 0x52930) mem0 (seg_rom tfibsegs))).
Local Abbreviation all_disjoint_of_forall := (@AFis.all_disjoint_of_forall ).
Local Abbreviation kept_of_frame := (@AFis.kept_of_frame W ly regs0 mem0 n v kz DPOST).
Local Abbreviation SKEL_TAIL := (@AFis.SKEL_TAIL ).
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
Local Abbreviation at_ST2 := (@AFis.at_ST2 _ W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz DPOST).
Local Abbreviation at_S2 := (@AFis.at_S2 _ W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz DPOST).
Local Abbreviation at_RET := (@AFis.at_RET _ W ly regs0 mem0 md0 n cl cnt v jb kz DPOST).
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
Local Abbreviation abs_cell_ok := (@AFix.abs_cell_ok ).
Local Abbreviation abs_cells_ok := (@AFix.abs_cells_ok ).
Local Abbreviation const_cells_zone := (@AFix.const_cells_zone ly regs0 mem0 n v kz Hv DPOST B l off TS HTSD).
Local Abbreviation CZONE_untouched := (@AFix.CZONE_untouched _ ly regs0 mem0 n cl cnt v kz Hcl Hv Hcnt Hv2 LY IMG Hsp DPOST Hkz Nrange l off).
Local Abbreviation cell_holds_agree := (@AFix.cell_holds_agree ly regs0 mem0 n v kz Hv DPOST B l off).
Local Abbreviation aview_agree := (@AFix.aview_agree W).
Local Abbreviation const_kept := (@AFix.const_kept _ W ly regs0 mem0 n cl cnt v kz Hcl Hv Hcnt Hv2 LY IMG Hsp DPOST Hkz Nrange B l off TS HTSD).
Local Abbreviation depot_ids_bound := (@AFix.depot_ids_bound ly regs0 mem0 n v kz Hv DPOST B l off TS).
Local Abbreviation depot_mem_ok_agree := (@AFix.depot_mem_ok_agree ly regs0 mem0 n v kz Hv DPOST B l off TS).
Local Abbreviation depot_ok_ext := (@AFix.depot_ok_ext ly B).
Local Abbreviation depot_at0 := (@AFix.depot_at0 _ W ly regs0 mem0 n cl cnt v jb kz Hcl Hv Hcnt Hjb Hsp DPOST Hkz Nrange B S HARm).
Local Abbreviation DPOST3 := (@AFix.DPOST3 W ly regs0 ch B S).
Local Abbreviation D1W_ok := (@AFix.D1W_ok _ _ W ly regs0 mem0 n ch cl cnt v jb kz Hcl Hv Hcnt Hjb Hv2 LY IMG Hsp DPOST Hkz Nrange B S l off TS HTSD HARm Hgp).
Local Abbreviation st_popped := (@AFix.st_popped ).
Local Abbreviation new_chunk := (@AFix.new_chunk ).
Local Abbreviation st_final := (@AFix.st_final ).
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
Local Abbreviation zrange_dec := (@AFj1.zrange_dec ).
Local Abbreviation apresent_word := (@AFj1.apresent_word ).
Local Abbreviation val_mem_cell := (@AFj1.val_mem_cell W ly regs0 mem0 n ch cl v kz DPOST B S l off).
Local Abbreviation le_byte_1_0 := (@AFj1.le_byte_1_0 ly regs0 mem0 n ch cl v kz DPOST S l off).
Local Abbreviation find_chunk_at_app1 := (@AFj1.find_chunk_at_app1 ly B).
Local Abbreviation find_chunk_at_app2 := (@AFj1.find_chunk_at_app2 ly B).
Local Abbreviation In_combine_seq_app := (@AFj1.In_combine_seq_app ).
Local Abbreviation Kc_facts := (@AFj1.Kc_facts ly n cl v kz Hcl Hkz Nrange B off Hcl_class Hoff_def).
Local Abbreviation NLOf := (@AFj1.NLOf n kz Hkz Nrange).
Local Abbreviation AR_final := (@AFj1.AR_final _ _ W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz Hcl Hv Hcnt Hjb Hv2 LY IMG Hsp DPOST HKpres HSKpres HPB250 Hkz Nrange Hcl_def SEED B S l off TS HTSD HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def Hj4 Hjb_def).
Local Abbreviation LEAF_final := (@AFj1.LEAF_final _ _ W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz Hcl Hv Hcnt Hjb Hv2 LY IMG Hsp DPOST HKpres HSKpres HPB250 Hkz Nrange Hcl_def mat0 SEED B S l off TS HTSD HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def Hj4 Hjb_def).
Local Ltac addr_tac :=
cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi];
rewrite ?EaT, ?EaC, ?EaTOP, ?EaSB, ?E2; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, w64, ly_bot, kStackSpan, t_unwinding, t_cache, t_stats, TFIB_IMG_END, UNW_STK, BST_SIZE, ASTACK, IFRAME, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *;
rewrite ?unsigned_lit_small by zlia; zlia.
Local Ltac denot_tac :=
cbn [sv_denot]; rewrite ?EaT, ?EaC, ?EaTOP, ?EaSB, ?E2; unfold w64, ly_bot, kStackSpan in *;
first [ rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| rewrite Zbv_add_unsigned; f_equal; zlia
| rewrite unsigned_lit_small by zlia; f_equal; zlia
| reflexivity ].
Local Open Scope am_scope.
Let rd0 : reader := aview tfibsegs (w_H W) mem0.
Let WF := am_wf B ly S rd0 HARm.
Let c0 : config := cfg_at tfibsegs 0x52930 regs0 mem0 md0.
Hypothesis Htr : In tr (as_universe B).
Hypothesis HAR : AR tfibsegs B ly S W mem0 md0.
Hypothesis HD1 : tfib_depot_spec B.
Hypothesis HDPOST : forall z m, DPOST z m -> DPOST3 z m.
Hypothesis HDPOST' : forall z m, DPOST3 z m -> DPOST z m.
Hypothesis Hmat0 : mat0 = m_vm_materialized md0.
Lemma D1w : forall (regs : bvmap 5 word) (mem : word -> option byte) (md : Model),
getr regs 10 = Z_to_bv 64 (sp0 - IFRAME + 16) -> getr regs 11 = Z_to_bv 64 (Z.of_nat (length tr)) ->
getr regs 3 = getr regs0 3 -> getr regs 4 = Z_to_bv 64 TFIB_TP -> getr regs 1 = Z_to_bv 64 0x318cc ->
bv_unsigned (getr regs 2) = sp0 - 2272 ->
(forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W) mem) (sp0 - IFRAME + 16 + 8 * Z.of_nat i) 8 (nth i tr 0)) ->
(forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem a) ->
(forall x : word, ~ WIN false (bv_unsigned x) -> mem x = mem0 x) ->
SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 A_StackDepotPut) mem (seg_rom tfibsegs)) md)
(fun W' c' => W' = W /\ exists z regs' mem' mat,
c' = mkCfg (mkst regs' (Z_to_bv 64 0x318cc) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md) /\
regs_preserved regs regs' /\
(forall x : word, ~ (sp0 - 2272 - DEP_STK <= bv_unsigned x < sp0 - 2272) -> ~ DZONE (bv_unsigned x) -> mem' x = mem x) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
DPOST z mem').
Proof.
intros regs mem md R10 R11 R3 R4 R1 Rsp BUF PRES MEQ.
eapply SRr_mono; [exact (D1W_ok Htr HD1 regs mem md R10 R11 R3 R4 R1 Rsp BUF PRES MEQ)|].
intros W' c' _ (-> & z & regs' & mem' & mat & -> & RP & FR & PR & DP). split; [reflexivity|].
exists z, regs', mem', mat. repeat (split; [assumption || reflexivity|]). apply HDPOST'. exact DP.
Qed.
Local Abbreviation seg1J := (@AFip.seg1J _ _ W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz Hcl Hv Hcnt Hjb Hv2 LY IMG Hn Hra4096 Hsp Hch DPOST Hkz Nrange Hcl_def mat0 U1 SEED l off).
Local Abbreviation segC2 := (@AFip.segC2 _ _ W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz Hcl Hv Hcnt Hv2 LY IMG Hn Hsp DPOST Hkz Nrange l off).
Local Abbreviation segD := (@AFiq.segD _ _ W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz LY Hsp DPOST l off D1w).
Local Abbreviation seg2a_even := (@AFiq.seg2a_even _ _ W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz Hcl Hv Hcnt Hjb Hv2 LY IMG Hn Hsp DPOST HSKpres Hkz Nrange Hcl_def l off).
Local Abbreviation seg2b_even := (@AFiq.seg2b_even _ _ W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz Hcl Hv Hcnt Hv2 LY IMG Hn Hsp DPOST Hkz Nrange l off).
Local Abbreviation seg2c_even := (@AFiq.seg2c_even _ _ W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz Hcl Hv Hcnt Hjb Hv2 LY IMG Hn Htp Hra Hsp DPOST HKpres Hkz Nrange l off).
Local Abbreviation seg2a_odd := (@AFir.seg2a_odd _ _ W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz Hcl Hv Hcnt Hjb Hv2 LY IMG Hn Hsp DPOST HSKpres HPB250 Hkz Nrange Hcl_def l off).
Local Abbreviation seg2b_odd := (@AFir.seg2b_odd _ _ W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz Hcl Hv Hcnt Hv2 LY IMG Hn Hsp DPOST HPB250 Hkz Nrange l off).
Local Abbreviation seg2c_odd := (@AFir.seg2c_odd _ _ W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz Hcl Hv Hcnt Hjb Hv2 LY IMG Hn Htp Hra Hsp DPOST HKpres HPB250 Hkz Nrange l off).
Theorem tail_inner : forall c1, at_ST SS_JN W c1 ->
amreal tfibsegs (malloc_join n tr cl S) W c1
(fun r W' c' => Wf (as_universe B) (snd r) /\ qtight (snd r) -> malloc_leaf tfibsegs B ly S W regs0 mem0 md0 n r W' c').
Proof.
intros c1 HJ.
pose proof casek_sizes as (L & RS & R8 & NP & FP & NS & RQ). pose proof RZ_facts as (_ & _ & _ & RF4 & _).
unfold malloc_join. rewrite bind_assoc_eq. eapply amreal_pure; [exact (pop_hit S cl l off Hcache)|]. eapply amreal_pure; [reflexivity|].
unfold malloc_K. cbv beta iota. change (AFi3.st_popped S cl l) with (st_popped S cl l).
change {| ck_beg := PPrim (region_off cl + off); ck_req := n; ck_state := CAllocated |} with (new_chunk cl off n).
replace (needs_remap (ck_n (new_chunk cl off n))) with false.
2:{ symmetry. apply Z.leb_gt. unfold new_chunk, ck_n. cbn [ck_req]. rewrite RQ. unfold kClearShadowMmapThreshold.
apply Z.div_lt_upper_bound; zlia. }
unfold depot_put. rewrite bind_assoc_eq. unfold bind at 1. unfold askz. cbn [ibind amreal].
eapply SRr_bind. { exact (segC2 W c1 HJ). }
intros W1 c1' Hle1 HPD.
eapply SRr_mono. { exact (segD W1 c1' HPD). }
intros W2 c2 Hle2 [z HPD2]. exists z.
split. { destruct HPD2 as (_ & ms2 & mat2 & E2 & regs2 & mem2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & HDP). exact (proj1 (HDPOST _ _ HDP)). }
assert (FIN : forall s', s' = depot_after z tr (st_popped S cl l) ->
amreal tfibsegs ((ret () ;; modify (fun s : astate => set_chunks (upd_chunk (st_chunks s) (new_chunk cl off n)) s) ;;
ret (ck_user (new_chunk cl off n))) s') W2 c2
(fun r W' c' => Wf (as_universe B) (snd r) /\ qtight (snd r) -> malloc_leaf tfibsegs B ly S W regs0 mem0 md0 n r W' c')).
{ intros s' ->. eapply amreal_pure; [reflexivity|]. eapply amreal_pure; [reflexivity|]. cbn [amreal ret].
change (set_chunks (upd_chunk (st_chunks (depot_after z tr (st_popped S cl l))) (new_chunk cl off n)) (depot_after z tr (st_popped S cl l)))
with (st_final S cl l off n tr z).
destruct (Z.eq_dec (n mod 8) 0) as [H8|H8].
- eapply SRr_bind; [exact (seg2a_even H8 z W2 c2 HPD2)|]. intros W3 c3 _ H3.
eapply SRr_bind; [exact (seg2b_even H8 z W3 c3 H3)|]. intros W4 c4 _ H4.
eapply SRr_mono; [exact (seg2c_even H8 z W4 c4 H4)|]. intros W' c' _ HR MP.
exact (LEAF_final HDPOST HAR false z W' c' HR ltac:(split; [intros E; discriminate E | intros X; exfalso; exact (X H8)]) MP).
- eapply SRr_bind; [exact (seg2a_odd H8 z W2 c2 HPD2)|]. intros W3 c3 _ H3.
eapply SRr_bind; [exact (seg2b_odd H8 z W3 c3 H3)|]. intros W4 c4 _ H4.
eapply SRr_mono; [exact (seg2c_odd H8 z W4 c4 H4)|]. intros W' c' _ HR MP.
exact (LEAF_final HDPOST HAR true z W' c' HR ltac:(split; [intros _; exact H8 | intros _; reflexivity]) MP). }
destruct (z =? 0) eqn:Ez.
- eapply amreal_pure; [reflexivity|]. apply FIN. unfold depot_after. rewrite Ez. reflexivity.
- rewrite bind_assoc_eq. eapply amreal_pure; [reflexivity|].
rewrite bind_assoc_eq. unfold mcheck at 1.
destruct (depot_ids (st_popped S cl l) + 1 <? kDepotIdsPerBlock); [| unfold bind at 1; unfold fail; cbn [ibind amreal]; exact I].
eapply amreal_pure; [reflexivity|].
rewrite bind_assoc_eq. unfold mcheck at 1.
destruct (kStartFramesMax + depot_frames (st_popped S cl l) + Z.of_nat (length tr) + 1 <? kStoreFramesPerBlock);
[| unfold bind at 1; unfold fail; cbn [ibind amreal]; exact I].
eapply amreal_pure; [reflexivity|]. eapply amreal_pure; [reflexivity|].
apply FIN. unfold depot_after. rewrite Ez. reflexivity.
Qed.
Theorem hitg_inner : amreal tfibsegs (malloc_join n tr cl S) W c0
(fun r W' c' => Wf (as_universe B) (snd r) /\ qtight (snd r) -> malloc_leaf tfibsegs B ly S W regs0 mem0 md0 n r W' c').
Proof.
eapply amreal_SRr_pre.
{ replace c0 with cfg0 by (subst c0 cfg0; unfold cfg_at; rewrite Hmat0, with_vm_backing_id; reflexivity). exact seg1J. }
intros W1 c1 _ HJ. pose proof (proj1 HJ) as EW. subst W1. exact (tail_inner c1 HJ).
Qed.
End e.
End d.
