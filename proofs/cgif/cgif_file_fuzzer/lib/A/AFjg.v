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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1w AE3d AFhy AFi1 AFj6 AFi3 AFhz AFi0 AFi2 AFjc AFjd AFje AFjb AFjf AFj3 AFj4 AFj5.
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
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Local Abbreviation RZ := (@AFj6.RZ ).
Local Abbreviation NPv := (@AFj6.NPv n).
Local Abbreviation R8v := (@AFj6.R8v n).
Local Abbreviation N8D := (@AFj6.N8D n).
Local Abbreviation Pv := (@AFj6.Pv ly cl).
Local Abbreviation PVv := (@AFj6.PVv ly cl cnt).
Local Abbreviation Kv := (@AFj6.Kv ly cl v).
Local Abbreviation SHBv := (@AFj6.SHBv ).
Local Abbreviation SKv := (@AFj6.SKv ly cl v).
Local Abbreviation SSLOTv := (@AFj6.SSLOTv ly cl).
Local Abbreviation PBv := (@AFj6.PBv ly n cl v).
Local Abbreviation Uv := (@AFj6.Uv ly cl v).
Local Abbreviation SUv := (@AFj6.SUv ly cl v).
Local Abbreviation FILv := (@AFj6.FILv n).
Local Abbreviation NDv := (@AFj6.NDv n).
Local Abbreviation tr := (@AFj6.tr ly regs0 ch).
Local Abbreviation XW := (@AFj6.XW ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation E0 := (@AFj6.E0 ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaT := (@AFj6.EaT ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaC := (@AFj6.EaC ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaSB := (@AFj6.EaSB ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaTOP := (@AFj6.EaTOP ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation Er := (@AFj6.Er ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation E2 := (@AFj6.E2 ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation E1 := (@AFj6.E1 ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation E8 := (@AFj6.E8 ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation E10 := (@AFj6.E10 ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation E4 := (@AFj6.E4 ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaP := (@AFj6.EaP ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaR8 := (@AFj6.EaR8 ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaK := (@AFj6.EaK ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaSK := (@AFj6.EaSK ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaSSLOT := (@AFj6.EaSSLOT ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaPB := (@AFj6.EaPB ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaPV := (@AFj6.EaPV ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaRZ := (@AFj6.EaRZ ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaU := (@AFj6.EaU ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaSU := (@AFj6.EaSU ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaFIL := (@AFj6.EaFIL ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaNP := (@AFj6.EaNP ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaND := (@AFj6.EaND ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation WINT := (@AFj6.WINT ly cl).
Local Abbreviation PBW := (@AFj6.PBW ly n cl v).
Local Abbreviation WIN := (@AFj6.WIN ly regs0 n cl v).
Local Abbreviation win_in_WIN := (@AFj6.win_in_WIN ly regs0 n cl v).
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
Local Abbreviation HCdisj := (@AFj6.HCdisj _ ly regs0 v Hv LY).
Local Abbreviation DZONE := (@AFj6.DZONE ly).
Variable DPOST : Z -> (word -> option byte) -> Prop.
Local Abbreviation HC_NB := (@AFj6.HC_NB _ ly LY).
Hypothesis HKpres : forall a, Kv <= a < Kv + RZ + R8v -> apresent (w_H W) mem0 a.
Hypothesis HSKpres : forall a, SKv <= a < SKv + (RZ + R8v) / 8 -> apresent (w_H W) mem0 a.
Hypothesis HPB250 : NPv mod 8 <> 0 -> val_mem tfibsegs (mrestrict (w_H W) mem0) PBv 1 250.
Local Abbreviation HCX := (@AFj6.HCX _ ly LY).
Local Abbreviation tr_length := (@AFj6.tr_length ly regs0 mem0 n ch v DPOST).
Local Abbreviation Kv_range := (@AFj6.Kv_range ly regs0 mem0 n cl v Hcl Hv Hv2 DPOST).
Local Abbreviation high_facts := (@AFj6.high_facts _ ly regs0 mem0 n v Hv LY IMG DPOST).
Local Abbreviation blocks_facts := (@AFj6.blocks_facts _ ly LY IMG).
Local Abbreviation off_T := (@AFj6.off_T _ ly regs0 mem0 n v Hv LY IMG DPOST).
Local Abbreviation off_C := (@AFj6.off_C _ ly regs0 mem0 n v Hv LY IMG DPOST).
Local Abbreviation off_NB := (@AFj6.off_NB _ ly LY IMG).
Local Abbreviation off_SB := (@AFj6.off_SB _ ly LY IMG).
Ltac off_by tac :=
first [ apply off_img_high; tac
| apply off_T; unfold kThreadObjSize; tac
| apply off_C; tac
| apply off_NB; unfold kNodesBlockSize; tac
| apply off_SB; unfold kStoreBlockSize; tac
| unfold off_img; unfold TFIB_IMG_LO; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; tac ].
Hypothesis Nrange : 0 <= n <= 48.
Local Abbreviation K0_facts := (@AFj6.K0_facts n Nrange).
Local Abbreviation RZ_num := (@AFj6.RZ_num n Nrange).
Ltac numconst ::= (ceil; unfold zone3, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize,
t_cache, t_unwinding, t_stats, ASTACK, TFIB_IMG_END, TFIB_IMG_LO, kLowShadowBeg, UNW_STK, BST_SIZE, DEP_STK in * ); try pose proof RZ_num as RZN.
Local Abbreviation derived_ranges := (@AFj6.derived_ranges _ ly regs0 mem0 n cl cnt v Hcl Hv Hcnt Hv2 LY IMG DPOST Nrange).
Hypothesis Hcl_def : cl = class_id (R8v + RZ).
Local Abbreviation CLk := (@AFj6.CLk ).
Local Abbreviation CLk_E := (@AFj6.CLk_E ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 DPOST Nrange Hcl_def).
Local Abbreviation WIN1 := (@AFj6.WIN1 ly regs0 n cl v).
Local Abbreviation WIN1_WIN := (@AFj6.WIN1_WIN ly regs0 mem0 n cl v DPOST).
Local Abbreviation WIN_odd := (@AFj6.WIN_odd ly regs0 mem0 n cl cnt v jb Hcl Hv Hcnt Hjb Hsp DPOST Nrange).
Local Abbreviation WIN1_odd := (@AFj6.WIN1_odd ly regs0 mem0 n cl cnt v jb Hcl Hv Hcnt Hjb Hsp DPOST Nrange).
Local Abbreviation WSKEL := (@AFj6.WSKEL ).
Local Abbreviation WSKEL1 := (@AFj6.WSKEL1 ).
Local Abbreviation win_sub := (@AFj6.win_sub ).
Local Abbreviation win_sub_sound := (@AFj6.win_sub_sound ly regs0 mem0 n v Hv DPOST).
Local Abbreviation WSKEL_WIN := (@AFj6.WSKEL_WIN _ ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 Hcl Hv Hcnt Hv2 LY IMG DPOST Nrange).
Local Abbreviation WSKEL1_WIN1 := (@AFj6.WSKEL1_WIN1 _ ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 Hcl Hv Hcnt Hv2 LY IMG DPOST Nrange).
Local Abbreviation windows_WIN := (@AFj6.windows_WIN _ ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 Hcl Hv Hcnt Hv2 LY IMG DPOST Nrange).
Local Abbreviation windows_WIN1 := (@AFj6.windows_WIN1 _ ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 Hcl Hv Hcnt Hv2 LY IMG DPOST Nrange).
Local Abbreviation frame_WIN1 := (@AFj6.frame_WIN1 _ ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 Hcl Hv Hcnt Hv2 LY IMG DPOST Nrange).
Local Abbreviation WIN_not_high := (@AFj6.WIN_not_high _ ly regs0 mem0 n cl cnt v Hcl Hv Hcnt Hv2 LY IMG Hsp DPOST Nrange).
Variables (mat0 : list word).
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 0x52930) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis U1 : tfib_unwind_spec.
Hypothesis SEED : st_ok tfibsegs E0 SS0K (restrict (w_H W) (mkst regs0 (w64 0x52930) mem0 (seg_rom tfibsegs))).
Local Abbreviation all_disjoint_of_forall := (@AFj6.all_disjoint_of_forall ).
Local Abbreviation kept_of_frame := (@AFj6.kept_of_frame W ly regs0 mem0 n v DPOST).
Local Abbreviation SKEL_TAIL := (@AFj6.SKEL_TAIL ).
Local Abbreviation stack_ivs := (@AFj6.stack_ivs _ ly regs0 mem0 n v Hv LY Hsp DPOST).
Local Abbreviation stack_ivs2 := (@AFj6.stack_ivs2 _ ly regs0 mem0 n v Hv LY Hsp DPOST).
Local Abbreviation DZONE_disj := (@AFj6.DZONE_disj _ ly regs0 mem0 n cl cnt v Hcl Hv Hcnt Hv2 LY IMG Hsp DPOST Nrange).
Local Abbreviation RFACTS := (@AFj6.RFACTS ly regs0 n cl v).
Local Abbreviation zone_lit := (@AFj6.zone_lit _ ly regs0 mem0 n cl cnt v Hcl Hv Hcnt Hv2 LY IMG Hsp DPOST Nrange).
Local Abbreviation zone_T := (@AFj6.zone_T _ ly regs0 mem0 n cl cnt v Hcl Hv Hcnt Hv2 LY IMG Hsp DPOST Nrange).
Local Abbreviation zone_C := (@AFj6.zone_C _ ly regs0 mem0 n cl cnt v Hcl Hv Hcnt Hv2 LY IMG Hsp DPOST Nrange).
Local Abbreviation zone_K := (@AFj6.zone_K _ ly regs0 mem0 n cl cnt v Hcl Hv Hcnt Hv2 LY IMG Hsp DPOST Nrange).
Local Abbreviation zone_SH := (@AFj6.zone_SH _ ly regs0 mem0 n cl cnt v Hcl Hv Hcnt Hv2 LY IMG Hsp DPOST Nrange).
Local Abbreviation tail_ext_ok := (@AFj6.tail_ext_ok _ ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 Hcl Hv Hcnt Hv2 LY IMG Hsp DPOST Nrange).
Local Abbreviation at_ST := (@AFj6.at_ST _ W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation at_ST2 := (@AFj6.at_ST2 _ W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 DPOST).
Local Abbreviation at_S2 := (@AFj6.at_S2 _ W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 DPOST).
Local Abbreviation at_RET := (@AFj6.at_RET _ W ly regs0 mem0 md0 n cl cnt v jb DPOST).
Ltac frame_acc HE :=
match goal with
| MEQ : (forall x : word, ~ WIN1 ?odd (bv_unsigned x) -> ?m1 x = ?mb x), HFx : frame_of ?E ?rs ?m1 ?m2 |- _ =>
let MEQ' := fresh "MEQ" in
assert (MEQ' : forall x : word, ~ WIN1 odd (bv_unsigned x) -> m2 x = mb x)
by (intros x Hx; transitivity (m1 x); [exact (frame_WIN1 odd E rs m1 m2 HE ltac:(vm_compute; reflexivity) HFx x Hx) | exact (MEQ x Hx)]);
clear MEQ HFx; rename MEQ' into MEQ
end.
Local Abbreviation memset_stretch := (@AFj6.memset_stretch _ W ly regs0 mem0 n cl cnt v jb Hcl Hv Hcnt Hjb Hsp DPOST Nrange).
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
Local Abbreviation case0_sizes := (@AFj6.case0_sizes n Nrange).
Local Abbreviation Kv_is_sptr := (@AFj6.Kv_is_sptr ly cl v Hcl B off Hoff_def).
Local Abbreviation cl_range := (@AFjc.cl_range ly regs0 mem0 n cl v DPOST Nrange l off Hcl_class).
Local Abbreviation cls_geom := (@AFjc.cls_geom ly regs0 mem0 n cl v DPOST Nrange l off Hcl_class).
Local Abbreviation cls_wf := (@AFjc.cls_wf _ W ly regs0 mem0 n cl v DPOST Nrange B S l off HARm Hcl_class).
Local Abbreviation off_facts := (@AFjc.off_facts _ W ly regs0 mem0 n cl cnt v Hv2 DPOST Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation Kv_base := (@AFjc.Kv_base ly regs0 mem0 n cl v DPOST Nrange l off Hcl_class Hoff_def).
Local Abbreviation Kv_geom := (@AFjc.Kv_geom _ W ly regs0 mem0 n cl cnt v csz Hv2 LY DPOST Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def).
Local Abbreviation Hcl' := (@AFjc.Hcl' ly regs0 mem0 n cl v DPOST Nrange l off Hcl_class).
Local Abbreviation cl_k0 := (@AFjc.cl_k0 ly regs0 mem0 n cl v DPOST Nrange Hcl_def l off).
Local Abbreviation Hcnt' := (@AFjc.Hcnt' _ W ly regs0 mem0 n cl cnt v Hv2 Hsp DPOST Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation Hv' := (@AFjc.Hv' _ W ly regs0 mem0 n cl cnt v Hv2 DPOST Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation cached_vs_chunk := (@AFjc.cached_vs_chunk _ W ly regs0 mem0 n cl cnt v csz Hv2 LY Hsp DPOST Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def).
Local Abbreviation find_chunk_at_none := (@AFjc.find_chunk_at_none _ W ly regs0 mem0 n cl cnt v Hv2 Hsp DPOST Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation shadow250 := (@AFjc.shadow250 _ W ly regs0 mem0 n cl cnt v csz Hv2 LY Hsp DPOST Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def).
Local Abbreviation shadow_present := (@AFjc.shadow_present _ W ly regs0 mem0 n cl cnt v csz Hv2 LY IMG Hsp DPOST Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def).
Local Abbreviation vis_present := (@AFjc.vis_present _ W ly regs0 mem0 n cl cnt v Hv2 Hsp DPOST Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation KPRES := (@AFjc.KPRES _ W ly regs0 mem0 n cl cnt v csz Hv2 LY Hsp DPOST Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def).
Local Abbreviation SKPRES := (@AFjc.SKPRES _ W ly regs0 mem0 n cl cnt v csz Hv2 LY IMG Hsp DPOST Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def).
Local Abbreviation PB250 := (@AFjc.PB250 _ W ly regs0 mem0 n cl cnt v csz Hv2 LY IMG Hsp DPOST Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def).
Local Abbreviation in_thread_junk := (@AFjc.in_thread_junk _ W ly regs0 mem0 n cl cnt v Hv2 Hsp DPOST Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation junk_word := (@AFjc.junk_word _ W ly regs0 mem0 n cl cnt v Hv2 LY IMG Hsp DPOST Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation junk_byte := (@AFjc.junk_byte _ W ly regs0 mem0 n cl cnt v csz Hv2 LY Hsp DPOST Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def).
Local Abbreviation junk_values := (@AFjc.junk_values _ W ly regs0 mem0 n cl cnt v csz Hv2 LY IMG Hsp DPOST Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def).
Local Abbreviation cell_sym := (@AFjc.cell_sym _ W ly regs0 mem0 n cl cnt v Hv2 Hsp DPOST Nrange B S l off TS HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation cell_lit := (@AFjc.cell_lit _ W ly regs0 mem0 n cl cnt v Hv2 Hsp DPOST Nrange B S l off TS HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation cell_state := (@AFjc.cell_state _ W ly regs0 mem0 n cl cnt v Hv2 Hsp DPOST Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation In_acells_cache := (@AFjc.In_acells_cache _ W ly regs0 mem0 n cl cnt v Hv2 Hsp DPOST Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation In_combine_seq_last := (@AFjc.In_combine_seq_last _ W ly regs0 mem0 n cl cnt v Hv2 Hsp DPOST Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation cache_vals := (@AFjc.cache_vals _ W ly regs0 mem0 n cl cnt v csz Hv2 Hsp DPOST Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def).
Local Abbreviation unwinding_val := (@AFjc.unwinding_val _ W ly regs0 mem0 n cl cnt v Hv2 Hsp DPOST Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation sk_val := (@AFjc.sk_val _ W ly regs0 mem0 n cl cnt v csz Hv2 LY IMG Hsp DPOST Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def).
Local Abbreviation val_mem_mod8 := (@AFjc.val_mem_mod8 _ W ly regs0 mem0 n cl cnt v Hv2 Hsp DPOST Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation chunk_lit := (@AFjc.chunk_lit _ W ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 Hv2 Hsp DPOST Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation chunk_lit_at := (@AFjc.chunk_lit_at _ W ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 Hv2 Hsp DPOST Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation chunk_atom := (@AFjc.chunk_atom _ W ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 Hv2 Hsp DPOST Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation REG0_ok := (@AFjd.REG0_ok _ W ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 Hcl Hv Hcnt Hjb Hv2 LY IMG Hsp DPOST Nrange B S l off TS HTSD HARm Hpres0 Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def Hj0 Hj1 Hj2 Hj3 Hj4 Hjb_def).
Local Abbreviation Kv32 := (@AFje.Kv32 _ W ly regs0 mem0 n cl v Hv2 LY DPOST l off).
Local Abbreviation PAIRS_ok := (@AFje.PAIRS_ok _ W ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 Hcl Hv Hcnt Hv2 LY IMG Hsp DPOST Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def).
Local Abbreviation FACTS_ok := (@AFje.FACTS_ok _ W ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 Hcl Hv Hcnt Hjb Hv2 LY IMG Hn Hsp DPOST Nrange Hcl_def B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def).
Local Abbreviation SEED_ok := (@AFje.SEED_ok _ _ W ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 Hcl Hv Hcnt Hjb Hv2 LY IMG Hn Htp Hsp DPOST Nrange Hcl_def B S l off TS HTSD HARm Hpres0 Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def Hj0 Hj1 Hj2 Hj3 Hj4 Hjb_def).
Local Abbreviation CZONE := (@AFjb.CZONE ly).
Local Abbreviation abs_cell_ok := (@AFjb.abs_cell_ok ).
Local Abbreviation abs_cells_ok := (@AFjb.abs_cells_ok ).
Local Abbreviation const_cells_zone := (@AFjb.const_cells_zone ly regs0 mem0 n v Hv DPOST B l off TS HTSD).
Local Abbreviation CZONE_untouched := (@AFjb.CZONE_untouched _ ly regs0 mem0 n cl cnt v Hcl Hv Hcnt Hv2 LY IMG Hsp DPOST Nrange l off).
Local Abbreviation cell_holds_agree := (@AFjb.cell_holds_agree ly regs0 mem0 n v Hv DPOST B l off).
Local Abbreviation aview_agree := (@AFjb.aview_agree W).
Local Abbreviation const_kept := (@AFjb.const_kept _ W ly regs0 mem0 n cl cnt v Hcl Hv Hcnt Hv2 LY IMG Hsp DPOST Nrange B l off TS HTSD).
Local Abbreviation depot_ids_bound := (@AFjb.depot_ids_bound ly regs0 mem0 n v Hv DPOST B l off TS).
Local Abbreviation depot_mem_ok_agree := (@AFjb.depot_mem_ok_agree ly regs0 mem0 n v Hv DPOST B l off TS).
Local Abbreviation depot_ok_ext := (@AFjb.depot_ok_ext ly B).
Local Abbreviation depot_at0 := (@AFjb.depot_at0 _ W ly regs0 mem0 n cl cnt v jb Hcl Hv Hcnt Hjb Hsp DPOST Nrange B S HARm).
Local Abbreviation DPOST3 := (@AFjb.DPOST3 W ly regs0 ch B S).
Local Abbreviation D1W_ok := (@AFjb.D1W_ok _ _ W ly regs0 mem0 n ch cl cnt v jb Hcl Hv Hcnt Hjb Hv2 LY IMG Hsp DPOST Nrange B S l off TS HTSD HARm Hgp).
Local Abbreviation st_popped := (@AFjb.st_popped ).
Local Abbreviation new_chunk := (@AFjb.new_chunk ).
Local Abbreviation st_final := (@AFjb.st_final ).
Local Abbreviation Kc_user := (@AFjb.Kc_user ly regs0 mem0 n ch cl v Hcl DPOST Nrange B S l off Hoff_def).
Local Abbreviation MPF := (@AFjb.MPF ly regs0 n ch cl B S l off).
Local Abbreviation AR_final_stmt := (@AFjb.AR_final_stmt _ _ W ly regs0 mem0 md0 n ch cl cnt v jb DPOST B S l off).
Local Abbreviation WR_owned := (@AFjb.WR_owned _ W ly regs0 mem0 n ch cl cnt v csz jb Hcl Hv Hcnt Hjb Hv2 LY IMG Hsp DPOST HPB250 Nrange B S l off TS HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def).
Local Abbreviation LEAF_ok := (@AFjb.LEAF_ok _ _ W ly regs0 mem0 md0 n ch cl cnt v csz jb Hcl Hv Hcnt Hjb Hv2 LY IMG Hsp DPOST HPB250 Nrange mat0 B S l off TS HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def).
Local Abbreviation Kc_fresh := (@AFjb.Kc_fresh _ W ly regs0 mem0 n ch cl cnt v Hcl Hv Hv2 DPOST Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation upd_chunk_fresh := (@AFjb.upd_chunk_fresh n cl off).
Local Abbreviation SF_chunks := (@AFjb.SF_chunks _ W ly regs0 mem0 n ch cl cnt v Hcl Hv Hv2 DPOST Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation SF_same := (@AFjb.SF_same ly regs0 n ch cl S l off).
Local Abbreviation SF_sec_extents := (@AFjb.SF_sec_extents _ W ly regs0 mem0 n ch cl cnt v Hcl Hv Hv2 DPOST Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation SF_sec_live := (@AFjb.SF_sec_live _ W ly regs0 mem0 n ch cl cnt v Hcl Hv Hv2 DPOST Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation SF_ledger := (@AFjb.SF_ledger _ W ly regs0 mem0 n ch cl cnt v Hcl Hv Hv2 DPOST Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation cell_holds_agree2 := (@AFjb.cell_holds_agree2 ly regs0 mem0 n ch cl cnt v jb Hcl Hv Hcnt Hjb Hsp DPOST Nrange B S l off).
Local Abbreviation zrange_dec := (@AFjf.zrange_dec ).
Local Abbreviation apresent_word := (@AFjf.apresent_word ).
Local Abbreviation val_mem_cell := (@AFjf.val_mem_cell W ly regs0 mem0 n ch cl v DPOST B S l off).
Local Abbreviation le_byte_1_0 := (@AFjf.le_byte_1_0 ly regs0 mem0 n ch cl v DPOST S l off).
Local Abbreviation find_chunk_at_app1 := (@AFjf.find_chunk_at_app1 ly B).
Local Abbreviation find_chunk_at_app2 := (@AFjf.find_chunk_at_app2 ly B).
Local Abbreviation In_combine_seq_app := (@AFjf.In_combine_seq_app ).
Local Abbreviation Kc_facts := (@AFjf.Kc_facts ly n cl v Hcl Nrange B off Hcl_class Hoff_def).
Local Abbreviation NLOf := (@AFjf.NLOf n Nrange).
Local Abbreviation AR_final := (@AFjf.AR_final _ _ W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 Hcl Hv Hcnt Hjb Hv2 LY IMG Hsp DPOST HKpres HSKpres HPB250 Nrange Hcl_def SEED B S l off TS HTSD HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def Hj4 Hjb_def).
Local Abbreviation LEAF_final := (@AFjf.LEAF_final _ _ W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 Hcl Hv Hcnt Hjb Hv2 LY IMG Hsp DPOST HKpres HSKpres HPB250 Nrange Hcl_def mat0 SEED B S l off TS HTSD HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def Hj4 Hjb_def).
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
Local Abbreviation seg1J := (@AFj3.seg1J _ _ W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 Hcl Hv Hcnt Hjb Hv2 LY IMG Hn Hra4096 Hsp Hch DPOST Nrange Hcl_def mat0 U1 SEED l off).
Local Abbreviation segC2 := (@AFj3.segC2 _ _ W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 Hcl Hv Hcnt Hv2 LY IMG Hn Hsp DPOST Nrange l off).
Local Abbreviation segD := (@AFj4.segD _ _ W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 LY Hsp DPOST l off D1w).
Local Abbreviation seg2aK := (@AFj4.seg2aK _ _ W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 Hcl Hv Hcnt Hjb Hv2 LY IMG Hsp DPOST HSKpres Nrange l off).
Local Abbreviation seg2b_even := (@AFj4.seg2b_even _ _ W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 Hcl Hv Hcnt Hv2 LY IMG Hsp DPOST Nrange Hcl_def l off).
Local Abbreviation seg2c_even := (@AFj4.seg2c_even _ _ W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 Hcl Hv Hcnt Hjb Hv2 LY IMG Htp Hra Hsp DPOST HKpres Nrange l off).
Local Abbreviation seg2b_odd := (@AFj5.seg2b_odd _ _ W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 Hcl Hv Hcnt Hjb Hv2 LY IMG Hsp DPOST HSKpres HPB250 Nrange Hcl_def l off).
Local Abbreviation seg2c_odd := (@AFj5.seg2c_odd _ _ W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 Hcl Hv Hcnt Hjb Hv2 LY IMG Htp Hra Hsp DPOST HKpres HPB250 Nrange l off).
Theorem tail_inner : forall c1, at_ST KS_JN W c1 ->
amreal tfibsegs (malloc_join n tr cl S) W c1
(fun r W' c' => Wf (as_universe B) (snd r) /\ qtight (snd r) -> malloc_leaf tfibsegs B ly S W regs0 mem0 md0 n r W' c').
Proof.
intros c1 HJ.
pose proof case0_sizes as (L & RS & R8 & NP & FP & NS & RQ). pose proof K0_facts as (_ & RF4 & NPr & _).
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
destruct (Z.eq_dec (NPv mod 8) 0) as [H8|H8].
- eapply SRr_bind; [exact (seg2aK z W2 c2 HPD2)|]. intros W3 c3 _ H3.
eapply SRr_bind; [exact (seg2b_even H8 z W3 c3 H3)|]. intros W4 c4 _ H4.
eapply SRr_mono; [exact (seg2c_even H8 z W4 c4 H4)|]. intros W' c' _ HR MP.
exact (LEAF_final HDPOST HAR false z W' c' HR ltac:(split; [intros E; discriminate E | intros X; exfalso; exact (X H8)]) MP).
- eapply SRr_bind; [exact (seg2aK z W2 c2 HPD2)|]. intros W3 c3 _ H3.
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
Theorem hitk_inner : amreal tfibsegs (malloc_join n tr cl S) W c0
(fun r W' c' => Wf (as_universe B) (snd r) /\ qtight (snd r) -> malloc_leaf tfibsegs B ly S W regs0 mem0 md0 n r W' c').
Proof.
eapply amreal_SRr_pre.
{ replace c0 with cfg0 by (subst c0 cfg0; unfold cfg_at; rewrite Hmat0, with_vm_backing_id; reflexivity). exact seg1J. }
intros W1 c1 _ HJ. pose proof (proj1 HJ) as EW. subst W1. exact (tail_inner c1 HJ).
Qed.
End e.
End d.
