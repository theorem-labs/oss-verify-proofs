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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1w AE3d AFhy AFi1 AFj6 AFjc AFjd AFje.
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
Section f.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (n : Z) (ch : list (Z * Z * Z)).
Variables (cl cnt v csz j0 jb j1 j2 j3 j4 : Z).
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Local Abbreviation RZ := (@AFj6.RZ).
Local Abbreviation NPv := (@AFj6.NPv n).
Local Abbreviation R8v := (@AFj6.R8v n).
Local Abbreviation N8D := (@AFj6.N8D n).
Local Abbreviation Pv := (@AFj6.Pv ly cl).
Local Abbreviation PVv := (@AFj6.PVv ly cl cnt).
Local Abbreviation Kv := (@AFj6.Kv ly cl v).
Local Abbreviation SHBv := (@AFj6.SHBv).
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
Local Abbreviation CLk := (@AFj6.CLk).
Local Abbreviation CLk_E := (@AFj6.CLk_E ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 DPOST Nrange Hcl_def).
Local Abbreviation WIN1 := (@AFj6.WIN1 ly regs0 n cl v).
Local Abbreviation WIN1_WIN := (@AFj6.WIN1_WIN ly regs0 mem0 n cl v DPOST).
Local Abbreviation WIN_odd := (@AFj6.WIN_odd ly regs0 mem0 n cl cnt v jb Hcl Hv Hcnt Hjb Hsp DPOST Nrange).
Local Abbreviation WIN1_odd := (@AFj6.WIN1_odd ly regs0 mem0 n cl cnt v jb Hcl Hv Hcnt Hjb Hsp DPOST Nrange).
Local Abbreviation WSKEL := (@AFj6.WSKEL).
Local Abbreviation WSKEL1 := (@AFj6.WSKEL1).
Local Abbreviation win_sub := (@AFj6.win_sub).
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
Local Abbreviation all_disjoint_of_forall := (@AFj6.all_disjoint_of_forall).
Local Abbreviation kept_of_frame := (@AFj6.kept_of_frame W ly regs0 mem0 n v DPOST).
Local Abbreviation SKEL_TAIL := (@AFj6.SKEL_TAIL).
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
Let rd0 : reader := aview tfibsegs (w_H W) mem0.
Let WF := am_wf B ly S rd0 HARm.
Definition CZONE (a : Z) : Prop :=
(0x10000 <= a < 0x5fb000)   \/ (0x7fff8000 <= a < 0x80050000) \/ (T <= a < T + 80) \/ (ly_C ly <= a < ly_C ly + 160) \/ (TFIB_TSD <= a < TFIB_TSD + 8) \/
(ly_D ly <= a < ly_D ly + 4096).
Definition abs_cell_ok (c : acell) : bool :=
match c_at c with
| ANum a => (0x10000 <=? a) && ((a + Z.max 1 (Z.of_nat (c_w c)) <=? 0x5fb000) || ((0x7fff8000 <=? a) && (a + Z.max 1 (Z.of_nat (c_w c)) <=? 0x80050000)))
| _ => false
end.
Lemma abs_cells_ok : forallb abs_cell_ok (Tfib_const_abs ++ Tfib_const_shadow) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma const_cells_zone : forall c k, In c (as_const B ly) -> 0 <= k < Z.max 1 (Z.of_nat (c_w c)) -> CZONE (aeval B ly (c_at c) + k).
Proof.
intros c k Hin Hk. rewrite (ts_const B TS ly) in Hin. unfold Tfib_const in Hin. apply in_app_iff in Hin as [Hin|Hin].
- unfold Tfib_const_sym in Hin. cbn [In] in Hin. unfold CZONE, T.
pose proof (ts_tp B TS) as ETP. pose proof (ts_inst B TS) as EIN.
repeat match type of Hin with
| _ \/ _ => destruct Hin as [<-|Hin]; [cbn [c_at c_w aeval aoff z8 z4 z1 c8 c4 c1] in *; cbn in Hk; rewrite ?ETP, ?EIN, ?HTSD;
unfold TFIB_TP, TFIB_INST, TFIB_TSD, o_space, o_rinfo, o_sec_chunks, kStackSpan in *; zlia |]
| False => destruct Hin
end.
- pose proof (proj1 (forallb_forall _ _) abs_cells_ok c Hin) as Hc. unfold abs_cell_ok in Hc.
destruct (c_at c) eqn:Ea; try discriminate. cbn [aeval].
apply andb_prop in Hc as [Hz Hc]. apply Z.leb_le in Hz.
apply Bool.orb_prop in Hc. unfold CZONE. destruct Hc as [Hc|Hc]; [apply Z.leb_le in Hc; zlia|].
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
unfold CZONE, WIN, WINT, PBW, TFIB_TSD in *. numconst. unfold T, sp0 in *.
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
- intros k Hk. rewrite He by zlia. exact (Hc k Hk).
- destruct Hc as (b & Hb & Hm). exists b. split; [|exact Hm]. rewrite <- (Z.add_0_r (aeval B ly (c_at c))). rewrite He by zlia. rewrite Z.add_0_r. exact Hb.
Qed.
Lemma aview_agree : forall (mem mem' : word -> option byte) a, 0 <= a < 2 ^ 64 ->
mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a) -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a.
Proof. intros mem mem' a Ha He. unfold aview. rewrite (mbyte_mrestrict_same (w_H W) mem mem' a He). reflexivity. Qed.
Lemma const_kept : forall mem1 mem2, Forall (cell_holds B ly (aview tfibsegs (w_H W) mem1)) (as_const B ly) ->
(forall x : word, CZONE (bv_unsigned x) -> mem2 x = mem1 x) ->
Forall (cell_holds B ly (aview tfibsegs (w_H W) mem2)) (as_const B ly).
Proof.
intros mem1 mem2 HC He. apply Forall_forall. intros c Hc.
apply (cell_holds_agree (aview tfibsegs (w_H W) mem1)); [| exact (proj1 (Forall_forall _ _) HC c Hc)].
intros k Hk. pose proof (const_cells_zone c k Hc Hk) as Z1. pose proof (proj1 (CZONE_untouched false _ Z1)) as R.
apply aview_agree; [exact R|]. apply He. rewrite unsigned_lit_small by exact R. exact Z1.
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
assert (EZ : forall a, (TFIB_DEPOT <= a < TFIB_DEPOT + d_map1 + 8) \/ (TFIB_STORE <= a < TFIB_STORE + 32) \/
(ly_NB ly <= a < ly_NB ly + kNodesBlockSize) \/ (ly_SB ly <= a < ly_SB ly + kStoreBlockSize) -> rd' a = rd a).
{ intros a Ha. apply He. unfold DZONE, TFIB_DEPOT, TFIB_STORE, d_map1 in *. zlia. }
split; [|split].
- apply Forall_forall. intros c Hc. apply (cell_holds_agree rd); [| exact (proj1 (Forall_forall _ _) D1' c Hc)].
intros k Hk. apply EZ. unfold depot_cells in Hc. cbn in Hc.
destruct Hc as [<-|[<-|[<-|[<-|[]]]]]; cbn [c_at c_w aeval aoff z4 z8 c4 c8] in *; cbn in Hk; rewrite ?ED, ?ES; unfold d_nuniq, d_map1, s_total, s_block0 in *; zlia.
- destruct D2 as (heads & links & H1 & H2 & H3). exists heads, links. split; [|split; [|exact H3]].
+ intros b Hb. destruct (H1 b Hb) as [Hh Hr]. split; [exact Hh|]. intros k Hk. rewrite EZ; [exact (Hr k Hk)|].
rewrite ED. unfold d_tab_words, d_map1 in *. zlia.
+ intros id Hid. destruct (H2 id Hid) as (L1 & L2 & L3). split; [exact L1|]. split.
* intros k Hk. rewrite EZ; [exact (L2 k Hk)|]. unfold kNodesBlockSize. zlia.
* intros k Hk. rewrite EZ; [exact (L3 k Hk)|]. unfold kNodesBlockSize. zlia.
- apply Forall_forall. intros r Hr i Hi. rewrite EZ; [exact (proj1 (Forall_forall _ _) D3 r Hr i Hi)|].
cbn in Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd aeval aoff] in *; rewrite ?ED, ?ES; unfold d_nuniq, d_map1 in *; zlia.
Qed.
Lemma depot_ok_ext : forall S1 S2 (rd : reader), st_depot S1 = st_depot S2 -> depot_ok B ly rd S1 -> depot_ok B ly rd S2.
Proof. intros S1 S2 rd E. unfold depot_ok, depot_ids, depot_traces. rewrite E. exact (fun H => H). Qed.
Lemma depot_at0 : depot_mem_ok B ly S rd0.
Proof.
split; [|split].
- apply Forall_forall. intros c Hc. apply (proj1 (Forall_forall _ _) (am_cells B ly S rd0 HARm)).
unfold acells. do 6 (apply in_or_app; right). apply in_or_app. left. exact Hc.
- exact (am_depot B ly S rd0 HARm).
- apply Forall_forall. intros r Hr. cbn in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]].
1-3: apply (proj1 (Forall_forall _ _) (am_junk B ly S rd0 HARm)); unfold ajunk; right; right; do 6 (apply in_or_app; right); apply in_or_app; left; cbn; tauto.
all: apply (proj1 (Forall_forall _ _) (am_areas B ly S rd0 HARm)); unfold aareas; do 3 (apply in_or_app; right); cbn; tauto.
Qed.
Definition DPOST3 (z : Z) (mem2 : word -> option byte) : Prop :=
aok S (KDepot tr) z /\ depot_mem_ok B ly (depot_after z tr S) (aview tfibsegs (w_H W) mem2) /\
Forall (cell_holds B ly (aview tfibsegs (w_H W) mem2)) (as_const B ly).
Hypothesis Htr : In tr (as_universe B).
Lemma D1W_ok : tfib_depot_spec B ->
forall (regs : bvmap 5 word) (mem : word -> option byte) (md : Model),
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
DPOST3 z mem').
Proof.
intros HD1 regs mem md R10 R11 R3 R4 R1 Rsp BUF PRES MEQ.
destruct Hsp as (S1 & S2 & S3 & S4). pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
assert (CST : Forall (cell_holds B ly (aview tfibsegs (w_H W) mem)) (as_const B ly)).
{ apply (const_kept mem0); [exact (am_const B ly S rd0 HARm)|]. intros x Hx. apply MEQ. exact (proj1 (proj2 (CZONE_untouched false _ Hx))). }
assert (DEP : depot_mem_ok B ly S (aview tfibsegs (w_H W) mem)).
{ apply (depot_mem_ok_agree S rd0).
- pose proof (wf_depot _ _ _ _ _ WF) as [ND INC]. pose proof (depot_ids_bound S ND INC). zlia.
- intros a Ha. pose proof (DZONE_disj false a Ha) as (N1 & _). pose proof blocks_facts as (NBhi & SBhi & _).
assert (Ra : 0 <= a < 2 ^ 64) by (clear - Ha NBhi SBhi LY; unfold DZONE in Ha; numconst; zlia).
apply aview_agree; [exact Ra|]. apply MEQ. rewrite unsigned_lit_small by exact Ra. exact N1.
- exact depot_at0. }
eapply SRr_mono.
{ apply (HD1 W ly S regs mem md (sp0 - IFRAME + 16) tr LY IMG WF Htr CST DEP R10 R11).
- rewrite R3, Hgp. reflexivity.
- exact R4.
- rewrite R1. apply ret_ok_even. reflexivity.
- exact BUF.
- unfold IFRAME. apply Z.mod_divide; [zlia|]. pose proof S4 as S4'. apply Z.mod_divide in S4' as [q Hq]; [|zlia]. exists (2 * q - 264). zlia.
- unfold IFRAME, ASTACK in *. zlia.
- unfold IFRAME, ASTACK in *. zlia.
- right. rewrite Rsp. unfold IFRAME. zlia.
- rewrite Rsp. apply Z.mod_divide; [zlia|]. pose proof S4 as S4'. apply Z.mod_divide in S4' as [q Hq]; [|zlia]. exists (q - 142). zlia.
- rewrite Rsp. unfold DEP_STK, ASTACK in *. zlia.
- rewrite Rsp. zlia.
- rewrite Rsp. intros a Ha. apply PRES. unfold DEP_STK, ASTACK in *. zlia. }
intros W' c' Hle (-> & z & regs' & mem' & mat & -> & AOK & RP & FR & PR' & DEP' & CST'). split; [reflexivity|].
exists z, regs', mem', mat. split; [rewrite R1; reflexivity|]. split; [exact RP|]. split; [|split; [exact PR'| exact (conj AOK (conj DEP' CST'))]].
intros x N1 N2. apply FR; [rewrite Rsp; exact N1|].
intros FP. apply N2. unfold depot_footprint, DZONE in *. rewrite (ts_depot B TS), (ts_store B TS) in FP. unfold TFIB_DEPOT, TFIB_STORE, d_map1 in FP. zlia.
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
at_RET odd z W (mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat md0)) ->
(odd = true <-> NPv mod 8 <> 0) ->
MPF z ->
AR tfibsegs B ly S W mem0 md0 ->
AR tfibsegs B ly (SF z) W mem' (with_vm_backing (m_vm_lazy md0) mat md0).
Lemma WR_owned : forall odd a, 0 <= a < 2 ^ 64 -> (odd = true -> NPv mod 8 <> 0) ->
WIN odd a \/ DZONE a \/ (SUv <= a < SUv + N8D / 8) ->
(sp0 - ASTACK <= a < sp0) \/ aowned B ly S a.
Proof.
intros odd a Ra Hodd Hw. pose proof derived_ranges as DR. pose proof Kv_geom as (V1 & V2 & V3 & V4 & V5). pose proof cls_geom as (K1 & _ & _ & _ & K5 & K6).
pose proof high_facts as (F1 & F2 & _).
assert (OWN_SH : forall g, Kv <= g < Kv + class_size cl -> aowned B ly S (shadow_addr g)).
{ intros g Hg. apply (own_shadow_prim B ly S rd0 g HARm). zlia. }
assert (OWN_K : forall b, Kv <= b < Kv + RZ -> aowned B ly S b).
{ intros b Hb. apply (own_prim_nonuser B ly S rd0 b HARm); [zlia|]. intros k Hk _.
pose proof (cached_vs_chunk k Hk) as D. pose proof (chunk_facts B ly S rd0 k HARm Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _). zlia. }
pose proof RZ_num as (RZr & RZ8 & Nlo & NPr & R8r & NPR8 & N8r & NPN8 & FILN).
destruct Hw as [Hw|[Hw|Hw]].
- unfold WIN, WINT, PBW in Hw. destruct Hw as [Hs|[Hw|[[Hw|Hw]|[Ho Hw]]]]; [left; exact Hs| right | right; apply OWN_K; clear - Hw RZr; zlia | right; apply OWN_K; clear - Hw RZr DR; zlia | right].
+ apply (own_core B ly S rd0 (ly_T ly, kThreadObjSize) a HARm); [unfold core_extents; cbn; tauto|]. cbn [fst snd].
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, t_cache, t_unwinding in *. unfold T in Hw. zlia.
+ replace a with (shadow_addr (Kv + RZ + N8D)) by (unfold shadow_addr, PBv, SHBv, SHADOW_OFF in *; zlia). apply OWN_SH.
pose proof (Hodd Ho) as E8. pose proof (Z.div_mod NPv 8 ltac:(zlia)) as DM. pose proof (Z.mod_pos_bound NPv 8 ltac:(zlia)) as MB. clear - E8 DM MB K5 RZr NPr. unfold N8D in *. zlia.
- right. unfold DZONE in Hw. destruct Hw as [Hw|[Hw|Hw]].
+ apply (own_static B ly S rd0 a HARm). rewrite (ts_owned B TS). unfold Tfib_owned_static. apply Exists_exists.
exists (0xa5850, 0x5c8650 - 0xa5850). split; [cbn; tauto|]. unfold in_zr; cbn. zlia.
+ apply (own_core B ly S rd0 (ly_NB ly, kNodesBlockSize) a HARm); [unfold core_extents; cbn; tauto| cbn [fst snd]; exact Hw].
+ apply (own_core B ly S rd0 (ly_SB ly, kStoreBlockSize) a HARm); [unfold core_extents; cbn; tauto| cbn [fst snd]; exact Hw].
- right. replace a with (shadow_addr (Kv + 8 * (a - SKv))).
2:{ unfold shadow_addr, SKv, SHBv, SHADOW_OFF in *. rewrite (Z.mul_comm 8 (a - (2147450880 + Kv / 8))), Z.div_add by zlia. zlia. }
apply OWN_SH. unfold SKv, SHBv in *. pose proof (Z.div_mod Kv 8 ltac:(zlia)). pose proof (Z.mod_pos_bound Kv 8 ltac:(zlia)).
pose proof (div8_bounds NPv ltac:(zlia)). unfold N8D in *. rewrite Z.div_mul in Hw by zlia. clear - Hw H H0 H1 K5 RZr RZ8 NPr DR V3. zlia.
Qed.
Lemma LEAF_ok : AR_final_stmt -> AR tfibsegs B ly S W mem0 md0 ->
forall odd z W' c', at_RET odd z W' c' -> (odd = true <-> NPv mod 8 <> 0) ->
MPF z ->
malloc_leaf tfibsegs B ly S W regs0 mem0 md0 n (ck_user Kc, SF z) W' c'.
Proof.
intros ARF HAR odd z W' c' HR Hodd MP.
pose proof HR as HR0. destruct HR as (-> & regs' & mem' & mat & -> & R10 & RCS & (memD & DP & PRD & EQD) & MEQF & PRS & PRW & VALS).
exists ly, regs', mem', (with_vm_backing (m_vm_lazy md0) mat md0).
split. { unfold cfg_at, raZ, w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
cbn [fst snd]. split; [| split; [rewrite R10, Kc_user; reflexivity | exact (proj2 MP)]].
split; [exact (ARF odd z regs' mem' mat HR0 Hodd MP HAR)|].
split; [apply layout_le_refl|].
split; [apply wle_refl|].
split. { intros r Hr. apply RCS. unfold acallee_saved in Hr.
assert (H18 : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by zlia.
clear - RCS H18.
assert (E5 : forall k : Z, 0 <= k < 32 -> forall b : bv 5, bv_unsigned b = k -> Z_to_bv 5 k = b) by (intros k Hk b Hb; apply bv_eq; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 5) with 32; rewrite Z.mod_small by zlia; symmetry; exact Hb).
destruct H18 as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
[ rewrite (E5 2 ltac:(zlia) 2%bv eq_refl) | rewrite (E5 3 ltac:(zlia) 3%bv eq_refl) | rewrite (E5 4 ltac:(zlia) 4%bv eq_refl)
| rewrite (E5 8 ltac:(zlia) 8%bv eq_refl) | rewrite (E5 9 ltac:(zlia) 9%bv eq_refl) | rewrite (E5 18 ltac:(zlia) 18%bv eq_refl)
| rewrite (E5 19 ltac:(zlia) 19%bv eq_refl) | rewrite (E5 20 ltac:(zlia) 20%bv eq_refl) | rewrite (E5 21 ltac:(zlia) 21%bv eq_refl)
| rewrite (E5 22 ltac:(zlia) 22%bv eq_refl) | rewrite (E5 23 ltac:(zlia) 23%bv eq_refl) | rewrite (E5 24 ltac:(zlia) 24%bv eq_refl)
| rewrite (E5 25 ltac:(zlia) 25%bv eq_refl) | rewrite (E5 26 ltac:(zlia) 26%bv eq_refl) | rewrite (E5 27 ltac:(zlia) 27%bv eq_refl) ];
cbn [In]; tauto. }
split. { unfold same_io. destruct md0; cbn; repeat split; reflexivity. }
split.
-
intros a Ra NO NO' NS NE. apply aview_agree; [exact Ra|]. apply MEQF; rewrite unsigned_lit_small by exact Ra.
+ intros Hw. destruct (WR_owned odd a Ra ltac:(intros Ho; apply Hodd; exact Ho) (or_introl Hw)) as [Hs|Ho]; [|exact (NO Ho)].
apply NS. unfold ascratch, spZ. left. exact Hs.
+ intros Hw. destruct (WR_owned odd a Ra ltac:(intros Ho; apply Hodd; exact Ho) (or_intror (or_introl Hw))) as [Hs|Ho]; [|exact (NO Ho)].
apply NS. unfold ascratch, spZ. left. exact Hs.
+ intros Hu. apply NE. split; [discriminate|]. rewrite Kc_user. pose proof case0_sizes as (_ & _ & _ & _ & _ & _ & RQ). rewrite RQ. exact Hu.
+ intros Hw. destruct (WR_owned odd a Ra ltac:(intros Ho; apply Hodd; exact Ho) (or_intror (or_intror Hw))) as [Hs|Ho]; [|exact (NO Ho)].
apply NS. unfold ascratch, spZ. left. exact Hs.
- intros a Ha. exact (PRS a Ha).
Qed.
Lemma Kc_fresh : forall k, In k (st_chunks S) -> sptr_eqb (ck_beg k) (ck_beg Kc) = false.
Proof.
intros k Hk. pose proof off_facts as (_ & _ & _ & _ & _ & NI & _).
destruct (sptr_eqb (ck_beg k) (ck_beg Kc)) eqn:E; [|reflexivity]. exfalso.
unfold Kc, new_chunk in E. cbn [ck_beg] in E. destruct (ck_beg k) as [|o|r o|c p] eqn:Eb; cbn in E; try discriminate.
apply Z.eqb_eq in E. apply NI. apply in_or_app. right. apply in_or_app. left.
pose proof (In_chunk_offs S k o Hk Eb) as IN. rewrite E in IN.
replace (prim_class (region_off cl + off)) with cl in IN.
2:{ pose proof off_facts as (O1 & O2 & _). pose proof cls_geom as (K1 & _). pose proof cl_range.
unfold prim_class. rewrite region_off_eq by zlia. symmetry. rewrite Z.shiftr_div_pow2 by zlia.
pose proof (mapped_user_bound (as_universe B) 0 0 0 S cl WF ltac:(zlia)). unfold kUserMapSize, EV_MAX in *.
rewrite Z.div_add_l by zlia. rewrite Z.div_small by zlia. zlia. }
rewrite region_off_eq in IN by (pose proof cl_range; zlia). replace (cl * 2 ^ 32 + off - cl * 2 ^ 32) with off in IN by zlia. exact IN.
Qed.
Lemma upd_chunk_fresh : forall lst, (forall k, In k lst -> sptr_eqb (ck_beg k) (ck_beg Kc) = false) -> upd_chunk lst Kc = lst ++ [Kc].
Proof.
induction lst as [|k t IH]; intros H; [reflexivity|]. cbn [upd_chunk app]. rewrite (H k (or_introl eq_refl)). f_equal. apply IH. intros k' Hk'. apply H. right. exact Hk'.
Qed.
Lemma SF_chunks : forall z, st_chunks (SF z) = st_chunks S ++ [Kc].
Proof.
intros z. unfold SF, st_final. cbn [st_chunks set_chunks]. replace (st_chunks (depot_after z tr (st_popped S cl l))) with (st_chunks S).
- apply upd_chunk_fresh. exact Kc_fresh.
- unfold depot_after, st_popped. destruct (z =? 0); reflexivity.
Qed.
Lemma SF_same : forall z,
st_regions (SF z) = st_regions S /\ st_cache_inited (SF z) = st_cache_inited S /\ st_secs (SF z) = st_secs S /\
st_sec_arr (SF z) = st_sec_arr S /\ st_sec_reserved (SF z) = st_sec_reserved S /\ st_qthread (SF z) = st_qthread S /\
st_qglobal (SF z) = st_qglobal S /\ st_fs (SF z) = st_fs S /\ st_internal_inited (SF z) = st_internal_inited S /\
st_nev (SF z) = st_nev S /\ st_cache (SF z) = zupd cl (mkPC (pc_max (cache S cl)) l) (st_cache S) /\
st_depot (SF z) = (if z =? 0 then st_depot S else st_depot S ++ [tr]).
Proof.
intros z. unfold SF, st_final, depot_after, st_popped. destruct (z =? 0); cbn; repeat split; reflexivity.
Qed.
Lemma SF_sec_extents : forall z, sec_extents ly (SF z) = sec_extents ly S.
Proof.
intros z. unfold sec_extents. rewrite SF_chunks. rewrite flat_map_app. cbn. rewrite app_nil_r. reflexivity.
Qed.
Lemma SF_sec_live : forall z, sec_live_bytes (SF z) = sec_live_bytes S.
Proof.
intros z. unfold sec_live_bytes. rewrite SF_chunks. rewrite fold_right_app. cbn. reflexivity.
Qed.
Lemma SF_ledger : forall z md, ALedger tfibsegs ly S md -> ALedger tfibsegs ly (SF z) md.
Proof.
intros z md L. pose proof (SF_same z) as (R1 & _ & _ & _ & Rres & _ & _ & _ & _ & Rnev & _).
destruct L as [L0 L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12 L13].
constructor; try assumption.
- destruct L3 as (pieces & P1 & P2). exists pieces. split; [|exact P2].
destruct P1 as (Q1 & Q2 & Q3). unfold prim_pieces_ok, cut_ok, prim_hole_at, reg in *. rewrite R1. exact (conj Q1 (conj Q2 Q3)).
- rewrite SF_sec_extents. exact L6.
- rewrite SF_sec_extents. exact L7.
-   rewrite SF_sec_extents, Rres. unfold prim_committed in *. rewrite R1. exact L8.
-   rewrite SF_sec_extents. exact L11.
Qed.
Lemma cell_holds_agree2 : forall (rd1 rd2 rd' : reader) c,
(forall k, 0 <= k < Z.max 1 (Z.of_nat (c_w c)) ->
rd' (aeval B ly (c_at c) + k) = rd1 (aeval B ly (c_at c) + k) \/ rd' (aeval B ly (c_at c) + k) = rd2 (aeval B ly (c_at c) + k)) ->
cell_holds B ly rd1 c -> cell_holds B ly rd2 c -> cell_holds B ly rd' c.
Proof.
intros rd1 rd2 rd' c He H1 H2. unfold cell_holds in *. destruct (c_val c) as [e|m vv].
- intros k Hk. destruct (He (Z.of_nat k) ltac:(zlia)) as [E|E]; rewrite E; [exact (H1 k Hk) | exact (H2 k Hk)].
- destruct H1 as (b1 & Hb1 & Hm1). destruct H2 as (b2 & Hb2 & Hm2).
destruct (He 0 ltac:(zlia)) as [E|E]; rewrite Z.add_0_r in E; rewrite E; [exists b1 | exists b2]; tauto.
Qed.
End f.
End d.
