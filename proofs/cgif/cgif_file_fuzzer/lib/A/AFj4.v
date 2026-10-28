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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1w AE3d AFhy AFi1 AFj6 AFhz AFi0 AFi2.
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
Hypothesis D1w : forall (regs : bvmap 5 word) (mem : word -> option byte) (md : Model),
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
Lemma segD : forall W0 c, at_ST KS_PD W0 c -> SRr tfibsegs W0 c (fun W' c' => exists z, at_ST2 KS_PD z W' c').
Proof.
intros W0 c (-> & ms & mat & En & -> & HEn & HS & MEQ0 & PRES & BUF). pose proof Hwx_tfa as Hwx.
pose proof Hsp as (Hlo & Hbot & Hhi & Hal). pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd in T2, T4, T7.
assert (Usp : 0 <= bv_unsigned (getr regs0 2) < 2 ^ 64) by apply u64_range.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) En _ _ HS eq_refl) as Hshape; cbn [ss_pc] in Hshape;
lazymatch type of Hshape with _ = mkst _ (Z_to_bv 64 (ss_pc ?s)) _ _ => let p := eval vm_compute in (ss_pc s) in change (ss_pc s) with p in Hshape | _ => idtac end. rewrite Hshape.
rreg HS (2%bv : bv 5) R2. rewrite (HEn 2%nat (ltHAV 2 eq_refl)), E2 in R2.
eapply SRr_mono.
{ apply (D1w (ms_regs ms) (ms_mem ms)).
- rreg HS (10%bv : bv 5) R; rewrite R, (HEn 2%nat (ltHAV 2 eq_refl)), E2. unfold IFRAME, sp0. f_equal; zlia.
- rreg HS (11%bv : bv 5) R; rewrite R, (HEn 36%nat (ltHAV 36 eq_refl)). reflexivity.
- rreg HS (3%bv : bv 5) R; rewrite R, (HEn 3%nat (ltHAV 3 eq_refl)). exact (Er 3 3%bv eq_refl).
- rreg HS (4%bv : bv 5) R; rewrite R. reflexivity.
- rreg HS (1%bv : bv 5) R; rewrite R. reflexivity.
- rewrite R2. clear - cfg0 sp0 T SB Hlo Hhi T4 T7. rewrite unsigned_lit_small by addr_tac. unfold sp0; zlia.
- exact BUF.
- exact PRES.
- exact MEQ0. }
intros W' c' Hle (-> & z & regs2 & mem2 & mat2 & -> & HP & Hfr & Hpr & HDP). exists z.
split; [reflexivity|]. exists ms, mat2, En, regs2, mem2.
split; [rewrite wvb_collapse; reflexivity|].
split; [exact HEn|]. split; [exact HS|]. split; [exact MEQ0|]. split; [exact PRES|]. split; [exact BUF|].
split; [exact HP|]. split; [exact Hfr|]. split; [exact Hpr|]. exact HDP.
Qed.
Local Ltac stack_pres En HEn HS PCH PRESB :=
intros a Ha; pose proof Hsp as (Hlo_ & Hbot_ & Hhi_ & Hal_); pose proof (lo_top ly LY) as (T1' & T2' & T3' & T4' & T5' & T6' & T7');
assert (Ra : 0 <= a < 2 ^ 64) by (clear - Ha Hlo_ Hhi_ T4' T7'; addr_tac);
destruct (Z_lt_le_dec a (sp0 - 2272)) as [H1|H1];
[ eapply (st_ok_window_apresent_off (w_H W) En _ _ 0 _ a HS); [reflexivity | clear - Ha Ra H1 Hlo_ Hhi_ T4' T7' HEn; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn 2%nat (ltHAV 2 eq_refl)), E2; addr_tac | off_by ltac:(addr_tac) ]
| destruct (Z_lt_le_dec a (sp0 - 2128)) as [H2|H2];
[ eapply (st_ok_window_apresent_off (w_H W) En _ _ 2 _ a HS); [reflexivity | clear - Ha Ra H1 H2 Hlo_ Hhi_ T4' T7' HEn; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn 2%nat (ltHAV 2 eq_refl)), E2; addr_tac | off_by ltac:(addr_tac) ]
| destruct (Z_lt_le_dec a (sp0 - 64)) as [H3|H3];
[ apply PCH; [| exact Ra | apply PRESB; zlia];
pose proof derived_ranges as DR'; pose proof high_facts as LF'; pose proof stack_ivs as SI; pose proof Kv_range as HKR_;
clear - H2 H3 DR' LF' SI HKR_ Hlo_ T7'; unfold WIN1, WINT, PBW, IFRAME; numconst; zlia
| eapply (st_ok_window_apresent_off (w_H W) En _ _ 3 _ a HS); [reflexivity | clear - Ha Ra H1 H2 H3 Hlo_ Hhi_ T4' T7' HEn; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn 2%nat (ltHAV 2 eq_refl)), E2; addr_tac | off_by ltac:(addr_tac) ] ] ] ].
Local Ltac stack_pres_odd En HEn HS PCH PRESB :=
intros a Ha; pose proof Hsp as (Hlo_ & Hbot_ & Hhi_ & Hal_); pose proof (lo_top ly LY) as (T1' & T2' & T3' & T4' & T5' & T6' & T7');
assert (Ra : 0 <= a < 2 ^ 64) by (clear - Ha Hlo_ Hhi_ T4' T7'; addr_tac);
destruct (Z_lt_le_dec a (sp0 - 2272)) as [H1|H1];
[ eapply (st_ok_window_apresent_off (w_H W) En _ _ 1 _ a HS); [reflexivity | clear - Ha Ra H1 Hlo_ Hhi_ T4' T7' HEn; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn 2%nat (ltHAV 2 eq_refl)), E2; addr_tac | off_by ltac:(addr_tac) ]
| destruct (Z_lt_le_dec a (sp0 - 2128)) as [H2|H2];
[ eapply (st_ok_window_apresent_off (w_H W) En _ _ 3 _ a HS); [reflexivity | clear - Ha Ra H1 H2 Hlo_ Hhi_ T4' T7' HEn; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn 2%nat (ltHAV 2 eq_refl)), E2; addr_tac | off_by ltac:(addr_tac) ]
| destruct (Z_lt_le_dec a (sp0 - 64)) as [H3|H3];
[ apply PCH; [| exact Ra | apply PRESB; zlia];
pose proof derived_ranges as DR'; pose proof high_facts as LF'; pose proof stack_ivs as SI; pose proof Kv_range as HKR_;
clear - H2 H3 DR' LF' SI HKR_ Hlo_ T7'; unfold WIN1, WINT, PBW, IFRAME; numconst; zlia
| eapply (st_ok_window_apresent_off (w_H W) En _ _ 4 _ a HS); [reflexivity | clear - Ha Ra H1 H2 H3 Hlo_ Hhi_ T4' T7' HEn; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn 2%nat (ltHAV 2 eq_refl)), E2; addr_tac | off_by ltac:(addr_tac) ] ] ] ].
Local Ltac join_close HS :=
lazymatch type of HS with st_ok _ ?E ?ss ?ms0 =>
let rs := eval vm_compute in (R_scr2 :: tl (ss_mem ss)) in
pose proof (st_ok_submem tfibsegs E ss ms0 rs HS
ltac:(let m := eval vm_compute in (ss_mem ss) in change (ss_mem ss) with m;
apply submem_keep; [ unfold subregion; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
split; [reflexivity|]; split; [zlia|]; split; [zlia|]; split; [right; zlia|]; intros cc Hcc; destruct Hcc
| apply submem_refl ])
ltac:(vm_compute; reflexivity)) as HSJ;
clear HS; rename HSJ into HS; cbn [ss_pc ss_regs ss_resv ss_facts] in HS
end;
forget_regs HS 139%nat ([1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28]%bv : list (bv 5));
apply (YP03.st_ok_prune tfibsegs _ _ _ [] []) in HS;
lazymatch type of HS with st_ok _ _ ?ss _ => replace ss with KS_Q in HS by (vm_compute; reflexivity) end.
Lemma seg2aK : forall z W0 c, at_ST2 KS_PD z W0 c -> SRr tfibsegs W0 c (at_S2 false KS_Q z).
Proof.
intros z W0 c (-> & ms & mat & En & regs2 & mem2 & -> & HEn & HS & MEQ0 & PRES & BUF & HP & Hfr & Hpr & HDP). pose proof Hwx_tfa as Hwx.
pose proof Hsp as (Hlo & Hbot & Hhi & Hal). pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
pose proof derived_ranges as DR. pose proof high_facts as LF. pose proof K0_facts as (_ & NR & NPr & NP0 & NP1 & R8r & R8m & NPR8 & _ & N8r & N8m & NPN8 & _).
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, t_cache, t_unwinding in DR, LF.
assert (Usp : 0 <= bv_unsigned (getr regs0 2) < 2 ^ 64) by apply u64_range.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) En _ _ HS eq_refl) as Hshape; cbn [ss_pc] in Hshape;
lazymatch type of Hshape with _ = mkst _ (Z_to_bv 64 (ss_pc ?s)) _ _ => let p := eval vm_compute in (ss_pc s) in change (ss_pc s) with p in Hshape | _ => idtac end.
rreg HS (2%bv : bv 5) R2. rewrite (HEn 2%nat (ltHAV 2 eq_refl)), E2 in R2.
set (XD := fun a : Z => (sp0 - 2272 - DEP_STK <= a < sp0 - 2272) \/ DZONE a).
assert (Hfr' : forall x : word, ~ XD (bv_unsigned x) -> mem2 x = ms_mem ms x).
{ intros x Hx. subst XD. apply Hfr; [unfold sp0 in *; zlia | tauto]. }
pose proof (DZONE_disj false) as DZD0.
assert (PRD2 : forall a, DZONE a -> apresent (w_H W) mem0 a -> apresent (w_H W) mem2 a).
{ intros a Ha Hp. apply Hpr. apply (apresent_same (w_H W) mem0); [|exact Hp]. apply MEQ0.
destruct (DZD0 a Ha) as (N0 & _). pose proof blocks_facts as (NBhi & SBhi & _).
rewrite unsigned_lit_small; [exact N0|]. clear - Ha NBhi SBhi LY; unfold DZONE in Ha.
numconst. zlia.   }
lazymatch type of HS with st_ok _ _ ?ss ?ms0 =>
let m := eval vm_compute in (ss_mem ss) in
lazymatch m with ?r0 :: ?r1 :: ?rest =>
pose proof (st_ok_after_call tfibsegs 117 En ss ms0 regs2 (mrestrict (w_H W) mem2) (r0 :: trim_lo r1 (-2272) :: rest) 0x318cc HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(apply submem_keep; [apply subregion_refl|]; apply submem_keep; [apply subregion_trim_lo | apply submem_refl])
ltac:(vm_compute; reflexivity) HP) as HS1;
let rsv := eval vm_compute in (r0 :: trim_lo r1 (-2272) :: rest) in
change (r0 :: trim_lo r1 (-2272) :: rest) with rsv in HS1;
let ss2 := eval vm_compute in (ss_after_call ss rsv 117 0x318cc) in
change (ss_after_call ss rsv 117 0x318cc) with ss2 in HS1
end
end.
cbn [ms_mem restrict] in HS1.
lazymatch type of HS1 with Forall _ (?r0 :: ?r1 :: ?r2 :: ?tail) -> _ =>
assert (KEPT : Forall (region_kept tfibsegs En (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) mem2)) (r0 :: r1 :: r2 :: tail));
[ pose proof (DZONE_disj false) as DZD;
constructor; [|constructor; [|constructor]];
[ eapply (kept_of_frame En _ _ XD _ Hfr' Hpr); cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi];
clear - HEn XD DZD Hlo Hhi T4 T7; rewrite (HEn 2%nat (ltHAV 2 eq_refl)), E2; subst XD; intros a Ha; cbn beta;
[ split; [ intros [Hs|Hd]; [unfold DEP_STK in Hs; zlia | exact (proj2 (proj2 (proj2 (DZD a Hd))) ltac:(unfold ASTACK; zlia))]
| unfold zone3, TFIB_IMG_LO, kLowShadowBeg, ASTACK, kHighMemBeg, kHighMemEnd in *; zlia ]
| unfold zone3, TFIB_IMG_LO, kLowShadowBeg, ASTACK, TFIB_IMG_END, kHighMemBeg, kHighMemEnd in *; zlia ]
| eapply (kept_of_frame En _ _ XD _ Hfr' Hpr); cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi];
clear - HEn XD DZD Hlo Hhi T4 T7; rewrite (HEn 2%nat (ltHAV 2 eq_refl)), E2; subst XD; intros a Ha; cbn beta;
[ split; [ intros [Hs|Hd]; [unfold DEP_STK in Hs; zlia | exact (proj2 (proj2 (proj2 (DZD a Hd))) ltac:(unfold ASTACK; zlia))]
| unfold zone3, TFIB_IMG_LO, kLowShadowBeg, ASTACK, kHighMemBeg, kHighMemEnd in *; zlia ]
| unfold zone3, TFIB_IMG_LO, kLowShadowBeg, ASTACK, TFIB_IMG_END, kHighMemBeg, kHighMemEnd in *; zlia ]
| eapply (kept_of_frame En _ _ XD _ Hfr' Hpr); cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi];
clear - HEn XD DZD Hlo Hhi T4 T7; rewrite (HEn 2%nat (ltHAV 2 eq_refl)), E2; subst XD; intros a Ha; cbn beta;
[ split; [ intros [Hs|Hd]; [unfold DEP_STK in Hs; zlia | exact (proj2 (proj2 (proj2 (DZD a Hd))) ltac:(unfold ASTACK; zlia))]
| unfold zone3, TFIB_IMG_LO, kLowShadowBeg, ASTACK, kHighMemBeg, kHighMemEnd in *; zlia ]
| unfold zone3, TFIB_IMG_LO, kLowShadowBeg, ASTACK, TFIB_IMG_END, kHighMemBeg, kHighMemEnd in *; zlia ]
| apply Forall_forall; intros r Hr;
apply (in_map skel) in Hr; replace (map skel tail) with SKEL_TAIL in Hr by (vm_compute; reflexivity);
pose proof (tail_ext_ok En r HEn Hr) as (X1 & X2 & X3 & X4 & X5 & X6);
eapply (kept_of_frame En _ _ XD _ Hfr' Hpr); clear - XD X1 X2 X3 X4 X5 X6; intros a Ha; subst XD; cbn beta;
[ split; [ intros [Hs|Hd]; [unfold DEP_STK, ASTACK in *; zlia | unfold DZONE in Hd; numconst; zlia] | zlia ]
| numconst; zlia ] ]
| specialize (HS1 KEPT); clear KEPT ]
end.
assert (PRES2 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem2 a) by (intros a Ha; apply Hpr, PRES, Ha).
set (En3 := havoc En 117 (map (getr regs2) CLOB)) in HS1.
assert (HEn3 : forall k, (k < aHAV)%nat -> ew En3 k = ew E0 k) by (intros k Hk; subst En3; unfold aHAV in Hk; rewrite ew_havoc_old by zlia; apply HEn; exact Hk).
apply (st_ok_add_region _ _ _ (YP09.mkRegion (Some 2%nat) (- ASTACK) (- 2272) (- ASTACK) (- 2272) [])) in HS1;
[ | reflexivity
| unfold YP09.region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem];
rewrite (HEn3 2%nat (ltHAV 2 eq_refl)), E2;
split; [addr_tac|]; split; [addr_tac|]; split; [intros o Ho; apply apresent_writable_off; [off_by ltac:(addr_tac) | apply PRES2; addr_tac] | constructor]
| apply all_disjoint_of_forall; intros r' [<-|[<-|[<-|Hr']]];
[ unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; unfold ASTACK; zlia
| unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; unfold ASTACK; zlia
| unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; unfold ASTACK; zlia
| apply (in_map skel) in Hr';
lazymatch type of Hr' with In _ (map skel ?tl) => replace (map skel tl) with SKEL_TAIL in Hr' by (vm_compute; reflexivity) end;
pose proof (tail_ext_ok En3 r' HEn3 Hr') as (X1 & X2 & X3 & X4 & X5 & X6);
unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite (HEn3 2%nat (ltHAV 2 eq_refl)), E2;
unfold ASTACK, sp0 in *; zlia ] ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1.
rewrite <- (restrict_mkst_fx (w_H W)) in HS1. clear HS. rename HS1 into HS.
assert (MEQ : forall x : word, ~ WIN1 false (bv_unsigned x) -> mem2 x = mem2 x) by (intros; reflexivity).
srr_run_sh tfibtbl_rtA_ok HS. frame_acc HEn3.
apply (st_ok_pin_regU _ _ _ 10%bv (SOff aSK 0)) in HS. 2:{ intros X; discriminate. }
2:{ clear - HEn3 DR LF Hcl Hcnt Hv. pin_zev. unfold aSK.
rewrite (HEn3 48%nat (ltHAV 48 eq_refl)), (HEn3 47%nat (ltHAV 47 eq_refl)), (HEn3 45%nat (ltHAV 45 eq_refl)), EaSK, EaK, (eq_refl : ew E0 47 = w64 SHBv).
unfold w64. unfold SKv, SHBv in *. rewrite !unsigned_lit_small by zlia. zcanon_simp.
land_lits. rewrite Z.shiftr_div_pow2 by zlia. change (2 ^ 3) with 8.
pose proof (div8_bounds Kv ltac:(zlia)). zcanon_simp. zlia. }
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_sh tfibtbl_rtA_ok HS. frame_acc HEn3.
apply (st_ok_pin_regU _ _ _ 22%bv (SOff aN8D 0)) in HS. 2:{ intros X; discriminate. }
2:{ clear - HEn3 DR LF Hcl Hcnt Hv NPr. pin_zev. unfold aN8D, aNP.
rewrite (HEn3 55%nat (ltHAV 55 eq_refl)), (HEn3 62%nat (ltHAV 62 eq_refl)), (eq_refl : ew E0 55 = w64 N8D), EaNP.
unfold w64. unfold N8D in *. rewrite !unsigned_lit_small by zlia. zcanon_simp.
change 281474976710648 with (2 ^ 48 - 8). rewrite land_m8_48 by zlia.
pose proof (div8_bounds NPv ltac:(zlia)). pose proof (Z.div_mod NPv 8 ltac:(zlia)). zcanon_simp. zlia. }
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
assert (EN8 : U En3 (SOff 55 0) = N8D) by (clear - HEn3 DR; apply U_atom; [rewrite (HEn3 55%nat (ltHAV 55 eq_refl)); reflexivity | zlia]).
srr_branch_sh tfibtbl_rtA_ok HS.
{
rewrite branch_eq_U, EN8, (U_lit En3 0) in Hc by zlia. apply Z.eqb_eq in Hc.
srr_run_to_sh tfibtbl_rtA_ok HS 0x319d8. frame_acc HEn3.
join_close HS.
lazymatch type of HS with st_ok _ ?E2 _ _ => set (EnS := E2) in HS end.
assert (HEnS : forall j, (j < aHAV)%nat -> ew EnS j = ew E0 j) by (intros j Hj; subst EnS; unfold aHAV in Hj; rewrite ew_havoc_old by zlia; apply HEn3; exact Hj).
match type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msS end.
assert (CH2 : forall x : word, ~ WIN1 false (bv_unsigned x) -> ~ (SUv <= bv_unsigned x < SUv + N8D / 8) -> ms_mem msS x = mem2 x).
{ intros x NA NB. exact (MEQ x NA). }
assert (PCH2 : forall a, ~ WIN1 false a -> 0 <= a < 2 ^ 64 -> apresent (w_H W) mem2 a -> apresent (w_H W) (ms_mem msS) a).
{ intros a NA Ra Hp. apply (apresent_same (w_H W) mem2); [apply MEQ; rewrite unsigned_lit_small by exact Ra; exact NA|]. exact Hp. }
pose proof (DZONE_disj false) as DZDo.
apply SRr_ret. split; [reflexivity|]. lazymatch goal with |- context [mkCfg ?msf (with_vm_backing _ ?matf _)] => exists msf, matf, EnS, mem2 end. split; [reflexivity|]. split; [exact HEnS|]. split; [exact HS|]. split; [exact HDP|]. split; [exact PRD2|].
split. { intros x Hd. destruct (DZDo _ Hd) as (D0 & D2 & D3 & D4). apply CH2; [intros H1; apply D0, WIN1_WIN, H1 | exact D3]. }
split. { intros x NA ND NB. rewrite (CH2 x) by (try exact NB; intros H1; apply NA, WIN1_WIN, H1).
rewrite Hfr' by (subst XD; cbn beta; intros [H1|H1]; [apply NA; unfold WIN; left; clear - H1; numconst; zlia | exact (ND H1)]).
apply MEQ0. exact NA. }
split. { stack_pres EnS HEnS HS PCH2 PRES2. }
split. { intros x Hx. exfalso. clear - Hx Hc N8r. rewrite Hc in Hx. change (0 / 8) with 0 in Hx. zlia. }
intros HH; discriminate HH. }
rewrite branch_eq_U, EN8, (U_lit En3 0) in Hc by zlia. apply Z.eqb_neq in Hc.
srr_run_sh tfibtbl_rtA_ok HS. frame_acc HEn3.
assert (E16 : Kv = 16 * (Kv / 16)) by (clear - DR; pose proof (Z.div_mod Kv 16 ltac:(zlia)); zlia).
assert (EN8' : N8D = 8 * (N8D / 8)) by (clear - DR; pose proof (Z.div_mod N8D 8 ltac:(zlia)); zlia).
assert (EK8 : Kv / 8 = 2 * (Kv / 16)) by (clear - E16 DR; rewrite E16 at 1; replace (16 * (Kv / 16)) with ((2 * (Kv / 16)) * 8) by zlia; apply Z.div_mul; zlia).
assert (EU8 : (Kv + 16) / 8 = 2 * (Kv / 16) + 2) by (clear - E16 DR; replace (Kv + 16) with ((2 * (Kv / 16) + 2) * 8) by zlia; apply Z.div_mul; zlia).
assert (EP8 : (Kv + 8 + N8D) / 8 = N8D / 8 + 2 * (Kv / 16) + 1) by (clear - E16 EN8' DR; replace (Kv + 8 + N8D) with ((N8D / 8 + 2 * (Kv / 16) + 1) * 8) by zlia; apply Z.div_mul; zlia).
apply (st_ok_pin_regU _ _ _ 8%bv (SOff aCNT8 0)) in HS. 2:{ intros X; discriminate. }
2:{ clear - HEn3 DR E16 EN8' EK8 EU8 EP8. pin_zev. unfold aCNT8, aN8D, aK.
rewrite (HEn3 56%nat (ltHAV 56 eq_refl)), (HEn3 45%nat (ltHAV 45 eq_refl)), (HEn3 55%nat (ltHAV 55 eq_refl)), EaK, (eq_refl : ew E0 56 = w64 (N8D / 8)), (eq_refl : ew E0 55 = w64 N8D).
unfold w64. rewrite !unsigned_lit_small by zlia. zcanon_simp. land_lits. rewrite !Z.shiftr_div_pow2 by zlia. change (2 ^ 3) with 8.
zcanon_simp. rewrite ?EP8, ?EU8. zcanon_simp. zlia. }
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
apply (st_ok_pin_regU _ _ _ 10%bv (SOff aSK 2)) in HS. 2:{ intros X; discriminate. }
2:{ clear - HEn3 DR E16 EK8 EU8. pin_zev. unfold aSK, aSHB, aK.
rewrite (HEn3 48%nat (ltHAV 48 eq_refl)), (HEn3 47%nat (ltHAV 47 eq_refl)), (HEn3 45%nat (ltHAV 45 eq_refl)), EaSK, EaK, (eq_refl : ew E0 47 = w64 SHBv).
unfold w64. unfold SUv, SKv, SHBv in *. rewrite !unsigned_lit_small by zlia. zcanon_simp. land_lits. rewrite !Z.shiftr_div_pow2 by zlia. change (2 ^ 3) with 8.
zcanon_simp. rewrite ?EU8, ?EK8 in *. zcanon_simp. zlia. }
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_sh tfibtbl_rtA_ok HS. frame_acc HEn3.
match type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msM end.
assert (SHPRES : forall a, SUv <= a < SUv + N8D / 8 -> apresent (w_H W) (ms_mem msM) a).
{ intros a Ha.
assert (NW : ~ WIN false a) by (clear - Ha DR LF Hlo T7; unfold WIN, WINT, PBW, IFRAME in *; numconst; zlia).
assert (Ra : 0 <= a < 2 ^ 64) by (clear - Ha DR; numconst; zlia).
apply (apresent_same (w_H W) mem2); [apply MEQ; rewrite unsigned_lit_small by exact Ra; intros H1; apply NW, WIN1_WIN, H1|].
apply Hpr. apply (apresent_same (w_H W) mem0); [apply MEQ0; rewrite unsigned_lit_small by exact Ra; exact NW|].
apply HSKpres. clear - Ha DR. pose proof (Z.div_le_mono N8D R8v 8 ltac:(zlia) ltac:(zlia)). replace (RZ + R8v) with (2 * 8 + R8v) by zlia. rewrite Z.div_add_l by zlia. zlia. }
rreg HS (11%bv : bv 5) RA1m1.
eapply (memset_stretch 133 En3 _ _ _ SUv (N8D / 8) 0x319d8);
[ exact HS | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
| rreg HS (10%bv : bv 5) R; rewrite R, (HEn3 48%nat (ltHAV 48 eq_refl)), EaSK; unfold w64; rewrite ?Zbv_add_unsigned, ?Z.add_0_r; f_equal; clear - DR; zlia
| rreg HS (12%bv : bv 5) R; rewrite R, (HEn3 56%nat (ltHAV 56 eq_refl)); reflexivity
| rreg HS (1%bv : bv 5) R; rewrite R; reflexivity
| clear - DR; zlia | clear - DR; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; zlia | clear - DR; numconst; zlia | reflexivity | clear; zlia
| exact SHPRES
| intros r Hr | intros r a Hr | intros r a Hr | ].
1-3: cbn [ss_mem] in Hr; destruct Hr as [<-|[<-|[<-|[<-|Hr]]]];
[ cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; clear - DR LF Hlo T7 Hhi T2 T4 Usp HEn3; rewrite (HEn3 2%nat (ltHAV 2 eq_refl)), E2; numconst; zlia
| cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; clear - DR LF Hlo T7 Hhi T2 T4 Usp HEn3; rewrite (HEn3 2%nat (ltHAV 2 eq_refl)), E2; numconst; zlia
| cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; clear - DR LF Hlo T7 Hhi T2 T4 Usp HEn3; rewrite (HEn3 2%nat (ltHAV 2 eq_refl)), E2; numconst; zlia
| cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; clear - DR LF Hlo T7 Hhi T2 T4 Usp HEn3; rewrite (HEn3 2%nat (ltHAV 2 eq_refl)), E2; numconst; zlia
| apply (in_map skel) in Hr;
lazymatch type of Hr with In _ (map skel ?tl) => replace (map skel tl) with SKEL_TAIL in Hr by (vm_compute; reflexivity) end;
pose proof (tail_ext_ok En3 r HEn3 Hr) as (X1 & X2 & X3 & X4 & X5 & X6); clear - DR LF X1 X2 X3 X4 X5 X6; numconst; zlia ].
intros regs3 mem3 mat3 HS3 H10c Hfr3 Hpr3 Hin3. clear HS. rename HS3 into HS.
lazymatch type of HS with st_ok _ ?E ?ss _ => set (En4 := E) in HS; let ss' := eval vm_compute in ss in change ss with ss' in HS end.
assert (HEn4 : forall k, (k < aHAV)%nat -> ew En4 k = ew E0 k) by (intros k Hk; subst En4; unfold aHAV in Hk; rewrite ew_havoc_old by zlia; apply HEn3; exact Hk).
assert (MEQ3 : forall x : word, ~ WIN1 false (bv_unsigned x) -> mem3 x = mem3 x) by (intros; reflexivity).
rename MEQ into MEQ2. rename MEQ3 into MEQ.
join_close HS.
lazymatch type of HS with st_ok _ ?E2 _ _ => set (EnS := E2) in HS end.
assert (HEnS : forall j, (j < aHAV)%nat -> ew EnS j = ew E0 j) by (intros j Hj; subst EnS; unfold aHAV in Hj; rewrite ew_havoc_old by zlia; apply HEn4; exact Hj).
assert (CH2 : forall x : word, ~ WIN1 false (bv_unsigned x) -> ~ (SUv <= bv_unsigned x < SUv + N8D / 8) -> mem3 x = mem2 x).
{ intros x NA NB. rewrite (Hfr3 x NB). apply MEQ2. exact NA. }
assert (PCH2 : forall a, ~ WIN1 false a -> 0 <= a < 2 ^ 64 -> apresent (w_H W) mem2 a -> apresent (w_H W) mem3 a).
{ intros a NA Ra Hp. apply Hpr3. apply (apresent_same (w_H W) mem2); [apply MEQ2; rewrite unsigned_lit_small by exact Ra; exact NA|]. exact Hp. }
pose proof (DZONE_disj false) as DZDo.
apply SRr_ret. split; [reflexivity|]. lazymatch goal with |- context [mkCfg ?msf (with_vm_backing _ ?matf _)] => exists msf, matf, EnS, mem2 end. split; [reflexivity|]. split; [exact HEnS|]. split; [exact HS|]. split; [exact HDP|]. split; [exact PRD2|].
cbn [ms_mem mkst].
split. { intros x Hd. destruct (DZDo _ Hd) as (D0 & D2 & D3 & D4). apply CH2; [intros H1; apply D0, WIN1_WIN, H1 | exact D3]. }
split. { intros x NA ND NB. cbn [ms_mem mkst]. etransitivity; [apply CH2; [intros H1; apply NA, WIN1_WIN, H1 | exact NB] |].
rewrite Hfr' by (subst XD; cbn beta; intros [H1|H1]; [apply NA; unfold WIN; left; clear - H1; numconst; zlia | exact (ND H1)]).
apply MEQ0. exact NA. }
split. { stack_pres EnS HEnS HS PCH2 PRES2. }
split. { intros x Hx. cbn [ms_mem mkst]. rewrite (Hin3 x Hx), RA1m1. reflexivity. }
intros HH; discriminate HH.
Qed.
Local Ltac close2b EnW HEnW HS MEQ EQD M0 PRS SRZ PBVt memD HDP PRD2 :=
apply SRr_ret; split; [reflexivity|];
lazymatch goal with |- context [mkCfg ?msf (with_vm_backing _ ?matf _)] => exists msf, matf, EnW, memD end;
split; [reflexivity|]; split; [exact HEnW|]; split; [exact HS|]; split; [exact HDP|]; split; [exact PRD2|];
pose proof (DZONE_disj false) as DZDo;
split; [ intros x Hd; destruct (DZDo _ Hd) as (D0 & D2 & D3 & D4); rewrite (MEQ x) by (intros H1; apply D0, WIN1_WIN, H1); apply EQD, Hd |];
split; [ intros x NA ND NB; rewrite (MEQ x) by (intros H1; apply NA, WIN1_WIN, H1); apply M0; [intros H1; apply NA; first [exact H1 | apply WIN_odd; exact H1] | exact ND | exact NB] |];
split; [| split; [ intros x Hx; pose proof Kv_range as HKR; pose proof derived_ranges as DR'; pose proof high_facts as LF'; pose proof Hsp as (Hlo_ & _); pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7_);
rewrite (MEQ x) by (pose proof stack_ivs as SI; clear - Hx DR' LF' HKR Hlo_ T7_ SI; unfold WIN1, WINT, PBW, IFRAME; numconst; zlia); apply SRZ, Hx
| PBVt ] ].
Local Ltac sslot_pin HS En HEn :=
apply (st_ok_pin_regU _ _ _ 10%bv (SOff aSSLOT 0)) in HS;
[ | intros X; discriminate
| lazymatch goal with |- U ?E _ = U _ (sr_get ?sr ?r) => let t := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with t end;
lazymatch goal with |- U ?E _ = U _ ?t => change t with SSLOT_term end;
apply U_eq_by_zev; [reflexivity | clear; vm_compute; reflexivity |];
change (zev (rho_of En) (SOff aSSLOT 0) = zcanon (zalu_raw 63 64 ALU_ADD (zev (rho_of En) (SOff aT 2912)) (zcanon (zalu_raw 63 64 ALU_SLL (zev (rho_of En) CLk) (zev (rho_of En) (SLit 3))))));
rewrite (CLk_E En HEn); pose proof derived_ranges as DR'; pose proof high_facts as LF'; clear - HEn Hcl DR' LF';
cbn [zev zalu_raw]; unfold rho_of, aSSLOT, aT; rewrite (HEn 52%nat (ltHAV 52 eq_refl)), (HEn 32%nat (ltHAV 32 eq_refl)), EaSSLOT, EaT;
unfold w64; unfold SSLOTv in *; numconst; rewrite !unsigned_lit_small by zlia; zcanon_simp; land_lits; rewrite ?Z.shiftl_mul_pow2 by zlia;
change (2 ^ 3) with 8; zcanon_simp; zlia ];
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
Lemma seg2b_even : NPv mod 8 = 0 -> forall z W0 c, at_S2 false KS_Q z W0 c -> SRr tfibsegs W0 c (at_S2 false KS_Te z).
Proof.
intros H8 z W0 c (-> & ms & mat & En & mem2 & -> & HEn & HS & HDP & PRD2 & EQD & M0 & PRS & SRZ & PBV). pose proof Hwx_tfa as Hwx.
pose proof Hsp as (Hlo & Hbot & Hhi & Hal). pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
pose proof derived_ranges as DR. pose proof high_facts as LF. pose proof K0_facts as (_ & NR & NPr & NP0 & NP1 & R8r & R8m & NPR8 & _ & N8r & N8m & NPN8 & _).
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, t_cache, t_unwinding in DR, LF.
assert (Usp : 0 <= bv_unsigned (getr regs0 2) < 2 ^ 64) by apply u64_range.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) En _ _ HS eq_refl) as Hshape; cbn [ss_pc] in Hshape;
lazymatch type of Hshape with _ = mkst _ (Z_to_bv 64 (ss_pc ?s)) _ _ => let p := eval vm_compute in (ss_pc s) in change (ss_pc s) with p in Hshape | _ => idtac end.
rewrite Hshape in HS. rewrite Hshape. set (mem1 := ms_mem ms) in *.
assert (MEQ : forall x : word, ~ WIN1 false (bv_unsigned x) -> mem1 x = mem1 x) by (intros; reflexivity).
assert (ENP : U En (SOff 62 0) = NPv) by (clear - HEn NPr; apply U_atom; [rewrite (HEn 62%nat (ltHAV 62 eq_refl)); exact EaNP | zlia]).
assert (EN8 : U En (SOff 55 0) = N8D) by (clear - HEn DR; apply U_atom; [rewrite (HEn 55%nat (ltHAV 55 eq_refl)); reflexivity | zlia]).
srr_branch_sh tfibtbl_rtA_ok HS.
-
clear Hc. srr_run_sh tfibtbl_rtA_ok HS. frame_acc HEn.
sslot_pin HS En HEn.
lazymatch type of HS with st_ok _ _ ?ss _ => replace ss with KS_Te in HS by (vm_compute; reflexivity) end.
close2b En HEn HS MEQ EQD M0 PRS SRZ ltac:(idtac) mem2 HDP PRD2.
+ match type of HS with st_ok _ _ _ (restrict _ ?msx) => assert (PCH : forall a, ~ WIN1 false a -> 0 <= a < 2 ^ 64 -> apresent (w_H W) mem1 a -> apresent (w_H W) (ms_mem msx) a)
by (intros a NA Ra Hp; apply (apresent_same (w_H W) mem1); [apply MEQ; rewrite unsigned_lit_small by exact Ra; exact NA | exact Hp]) end.
stack_pres En HEn HS PCH PRS.
+ intros HH; discriminate HH.
-
exfalso. clear - Hc ENP EN8 H8 NPr N8m NPN8 DR. rewrite branch_eq_U, ENP, EN8 in Hc. apply Z.eqb_neq in Hc.
pose proof (Z.div_mod NPv 8 ltac:(zlia)). zlia.
Qed.
Lemma seg2c_even : NPv mod 8 = 0 -> forall z W0 c, at_S2 false KS_Te z W0 c -> SRr tfibsegs W0 c (at_RET false z).
Proof.
intros H8 z W0 c (-> & ms & mat & En & mem2 & -> & HEn & HS & HDP & PRD2 & EQD & M0 & PRS & SRZ & PBV). pose proof Hwx_tfa as Hwx.
pose proof Hsp as (Hlo & Hbot & Hhi & Hal). pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
pose proof derived_ranges as DR. pose proof high_facts as LF. pose proof K0_facts as (_ & NR & NPr & NP0 & NP1 & R8r & R8m & NPR8 & _ & N8r & N8m & NPN8 & _).
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, t_cache, t_unwinding in DR, LF.
assert (Usp : 0 <= bv_unsigned (getr regs0 2) < 2 ^ 64) by apply u64_range.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) En _ _ HS eq_refl) as Hshape; cbn [ss_pc] in Hshape;
lazymatch type of Hshape with _ = mkst _ (Z_to_bv 64 (ss_pc ?s)) _ _ => let p := eval vm_compute in (ss_pc s) in change (ss_pc s) with p in Hshape | _ => idtac end.
assert (PBV1 : false = true -> val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) PBv 1 (NPv mod 8)) by exact PBV.
assert (EUv : Uv = Kv + 16) by (clear - DR; zlia).
rewrite Hshape in HS. rewrite Hshape. set (mem1 := ms_mem ms) in *.
assert (MEQ : forall x : word, ~ WIN1 false (bv_unsigned x) -> mem1 x = mem1 x) by (intros; reflexivity).
srr_run_sh tfibtbl_rtA_ok HS. frame_acc HEn.
match type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msF end.
pose proof Kv_range as HKR. pose proof blocks_facts as (_ & _ & _ & _ & _ & _ & _ & _ & PT). unfold zdisjoint in PT. cbn [fst snd] in PT.
assert (UPRES : forall a, Uv <= a < Uv + FILv -> apresent (w_H W) (ms_mem msF) a).
{ intros a Ha. pose proof high_facts as (_ & _ & _ & _ & _ & _ & _ & _ & F9).
assert (Ra : 0 <= a < 2 ^ 64) by (clear - Ha DR; numconst; zlia).
assert (NS : ~ (sp0 - ASTACK <= a < sp0)).
{ intros Hs. destruct (F9 a) as [N1' N2']; [clear - Hs Hlo Hhi T2; numconst; zlia|]. apply N2'. clear - Ha HKR LF DR. numconst. zlia. }
assert (NW : ~ WIN false a) by (clear - Ha NS DR LF Hlo T7 HKR PT; unfold WIN, WINT, PBW, IFRAME in *; numconst; zlia).
assert (ND : ~ DZONE a).
{ pose proof blocks_facts as BF. clear - Ha DR LF Hlo T7 BF HKR. unfold zdisjoint in BF. cbn [fst snd] in BF. unfold DZONE. numconst. zlia. }
apply (apresent_same (w_H W) mem1). { apply MEQ. rewrite unsigned_lit_small by exact Ra. intros H1; apply NW, WIN1_WIN, H1. }
apply (apresent_same (w_H W) mem0). { apply M0; rewrite unsigned_lit_small by exact Ra; [exact NW | exact ND | clear - Ha DR; numconst; zlia]. }
apply HKpres. clear - Ha DR. numconst. zlia. }
rreg HS (11%bv : bv 5) RA1m2.
eapply (memset_stretch 152 En _ _ _ Uv FILv 0x31c00);
[ exact HS | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
| rreg HS (10%bv : bv 5) R; rewrite R, (HEn 45%nat (ltHAV 45 eq_refl)), EaK, EUv; unfold w64; rewrite ?Zbv_add_unsigned, ?Z.add_0_r; reflexivity
| rreg HS (12%bv : bv 5) R; rewrite R, (HEn 62%nat (ltHAV 62 eq_refl)), EaFIL; unfold w64; rewrite ?Zbv_add_unsigned, ?Z.add_0_r; reflexivity
| rreg HS (1%bv : bv 5) R; rewrite R; reflexivity
| clear - DR; zlia | clear - DR; numconst; zlia | clear - DR; numconst; zlia | reflexivity | clear; zlia
| exact UPRES
| intros r Hr | intros r a Hr | intros r a Hr | ].
1-3: cbn [ss_mem] in Hr; destruct Hr as [<-|[<-|[<-|[<-|Hr]]]];
[ cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; pose proof stack_ivs as SI; clear - DR LF Hlo T7 Hhi T2 T4 Usp HKR SI HEn; rewrite (HEn 2%nat (ltHAV 2 eq_refl)), E2; numconst; unfold sp0 in *; zlia
| cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; pose proof stack_ivs as SI; clear - DR LF Hlo T7 Hhi T2 T4 Usp HKR SI HEn; rewrite (HEn 2%nat (ltHAV 2 eq_refl)), E2; numconst; unfold sp0 in *; zlia
| cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; pose proof stack_ivs as SI; clear - DR LF Hlo T7 Hhi T2 T4 Usp HKR SI HEn; rewrite (HEn 2%nat (ltHAV 2 eq_refl)), E2; numconst; unfold sp0 in *; zlia
| cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; pose proof stack_ivs as SI; clear - DR LF Hlo T7 Hhi T2 T4 Usp HKR SI HEn; rewrite (HEn 2%nat (ltHAV 2 eq_refl)), E2; numconst; unfold sp0 in *; zlia
| apply (in_map skel) in Hr;
lazymatch type of Hr with In _ (map skel ?tl) => replace (map skel tl) with SKEL_TAIL in Hr by (vm_compute; reflexivity) end;
pose proof (tail_ext_ok En r HEn Hr) as (X1 & X2 & X3 & X4 & X5 & X6); clear - DR LF X1 X2 X3 X4 X5 X6; numconst; zlia ].
intros regs4 mem4 mat4 HS4 H10d Hfr4 Hpr4 Hin4. clear HS. rename HS4 into HS.
lazymatch type of HS with st_ok _ ?E ?ss _ => set (En5 := E) in HS; let ss' := eval vm_compute in ss in change ss with ss' in HS end.
assert (HEn5 : forall k, (k < aHAV)%nat -> ew En5 k = ew E0 k) by (intros k Hk; subst En5; unfold aHAV in Hk; rewrite ew_havoc_old by zlia; apply HEn; exact Hk).
assert (MEQ4 : forall x : word, ~ WIN1 false (bv_unsigned x) -> mem4 x = mem4 x) by (intros; reflexivity).
rename MEQ into MEQ3. rename MEQ4 into MEQ.
srr_run_sh tfibtbl_rtA_ok HS. frame_acc HEn5.
eapply (SRr_ret_at tfibsegs tfibtbl_rtA tfibtbl_rtA_ok Hwx W En5); [exact HS | reflexivity | vm_compute; reflexivity |].
intros matZ. match type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msZ end.
rreg HS (1%bv : bv 5) RZ1. rewrite (HEn5 1%nat (ltHAV 1 eq_refl)), E1 in RZ1. rewrite RZ1. unfold YK0s.ret_ok in Hra. rewrite Hra.
pose proof (DZONE_disj false) as DZD.
assert (CH1 : forall x : word, ~ WIN1 false (bv_unsigned x) -> ~ (Uv <= bv_unsigned x < Uv + FILv) -> ms_mem msZ x = mem1 x).
{ intros x N1' N2'. rewrite (MEQ x N1'), (Hfr4 x N2'), (MEQ3 x N1'). reflexivity. }
assert (PCH1 : forall a, ~ WIN1 false a -> 0 <= a < 2 ^ 64 -> apresent (w_H W) mem1 a -> apresent (w_H W) (ms_mem msZ) a).
{ intros a N1' Ra Hp. apply (apresent_same (w_H W) mem4); [apply MEQ; rewrite unsigned_lit_small by exact Ra; exact N1'|].
apply Hpr4. apply (apresent_same (w_H W) mem1); [apply MEQ3; rewrite unsigned_lit_small by exact Ra; exact N1'|]. exact Hp. }
split; [reflexivity|]. exists (ms_regs msZ), (ms_mem msZ), matZ. split; [reflexivity|].
split. { rreg HS (10%bv : bv 5) R; rewrite R, (HEn5 45%nat (ltHAV 45 eq_refl)), EaK. unfold w64. rewrite ?Zbv_add_unsigned, ?Z.add_0_r. first [reflexivity | f_equal; clear - DR; zlia]. }
split. { intros r Hr. cbn [In] in Hr.
repeat match type of Hr with _ \/ _ => destruct Hr as [<-|Hr] | False => destruct Hr end;
lazymatch goal with |- getr _ ?r = _ =>
let R := fresh "R" in rreg HS r R; rewrite R;
let k := eval cbv in (Z.to_nat (bv_unsigned r)) in
first [ rewrite (HEn5 k (ltHAV k eq_refl)); symmetry; exact (Er k r eq_refl) | symmetry; exact Htp ] end. }
split. { exists mem2. split; [exact HDP|]. split; [exact PRD2|].
intros x Hx. destruct (DZD _ Hx) as (N0 & N2' & N3 & N4). rewrite CH1; [apply EQD, Hx | intros H1; apply N0, WIN1_WIN, H1 |].
clear - N2' DR. zlia. }
split. { intros x N0 ND N2' N3. rewrite CH1; [apply M0; assumption | intros H1; apply N0, WIN1_WIN, H1 | clear - N2' DR; zlia]. }
split. {   stack_pres En5 HEn5 HS PCH1 PRS. }
split. {   intros a Ha.
assert (Ra : 0 <= a < 2 ^ 64) by (clear - Ha DR LF HKR; unfold WINT, PBW in Ha; numconst; destruct Ha as [Ha|[Ha|[_ Ha]]]; zlia).
destruct Ha as [Hw|[Hk|Hpb]].
- unfold WINT in Hw. destruct Hw as [Hw|[Hw|[Hw|Hw]]].
+ eapply (st_ok_window_apresent_off (w_H W) En5 _ _ 45%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn5 40%nat (ltHAV 40 eq_refl)), EaP; unfold w64; rewrite unsigned_lit_small by (clear - DR LF; numconst; zlia); zlia | off_by ltac:(clear - Hw DR LF; numconst; zlia) ].
+ destruct (Z_lt_le_dec a (T + 2800)) as [H28|H28].
* eapply (st_ok_window_apresent_off (w_H W) En5 _ _ 41%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn5 32%nat (ltHAV 32 eq_refl)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - DR LF; numconst; zlia); unfold T in *; zlia | off_by ltac:(clear - Hw DR LF; numconst; zlia) ].
* eapply (st_ok_window_apresent_off (w_H W) En5 _ _ 43%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn5 32%nat (ltHAV 32 eq_refl)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - DR LF; numconst; zlia); unfold T in *; zlia | off_by ltac:(clear - Hw H28 DR LF; numconst; zlia) ].
+ eapply (st_ok_window_apresent_off (w_H W) En5 _ _ 44%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn5 52%nat (ltHAV 52 eq_refl)), EaSSLOT; unfold w64; rewrite unsigned_lit_small by (clear - DR LF; numconst; zlia); zlia | off_by ltac:(clear - Hw DR LF; numconst; zlia) ].
+ eapply (st_ok_window_apresent_off (w_H W) En5 _ _ 42%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn5 32%nat (ltHAV 32 eq_refl)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - DR LF; numconst; zlia); unfold T in *; numconst; zlia | off_by ltac:(clear - Hw DR LF; numconst; zlia) ].
- destruct (Z_lt_le_dec a (Kv + 16)) as [H1|H1].
+ eapply (st_ok_window_apresent_off (w_H W) En5 _ _ 48%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn5 45%nat (ltHAV 45 eq_refl)), EaK; unfold w64; rewrite unsigned_lit_small by (clear - DR LF; numconst; zlia); zlia | off_by ltac:(clear - Hk H1 DR LF HKR; numconst; zlia) ].
+
split. { destruct (HKpres a ltac:(clear - Hk H1 DR; numconst; zlia)) as [Hh _]. exact Hh. }
exists (Z_to_bv 8 190).
pose proof (Hin4 (Z_to_bv 64 a)) as Hi. rewrite unsigned_lit_small in Hi by exact Ra. rewrite RA1m2, unsigned_lit_small in Hi by zlia.
rewrite (MEQ (Z_to_bv 64 a)); [exact (Hi ltac:(clear - Hk H1 DR EUv; zlia))|].
rewrite unsigned_lit_small by exact Ra. pose proof stack_ivs as SI. clear - Hk H1 DR LF HKR Hlo T7 SI PT. unfold WIN1, WINT, PBW, IFRAME. numconst. zlia.
- destruct Hpb as [Hpb _]. discriminate Hpb. }
cbv zeta.
assert (RK : 0 <= Kv /\ Kv + 2 ^ 16 < 2 ^ 64) by (clear - DR; numconst; zlia).
split. { memv HS 48%nat 0%nat; [cbn [base_val YP09.r_base]; rewrite (HEn5 45%nat (ltHAV 45 eq_refl)), EaK; unfold w64; rewrite unsigned_lit_small by (clear - DR; numconst; zlia); clear - DR; zlia | reflexivity | zlia]. }
split. { pose proof (hdr_byte1_ok jb Hjb) as [B1 B2].
memv HS 48%nat 1%nat; [cbn [base_val YP09.r_base]; rewrite (HEn5 45%nat (ltHAV 45 eq_refl)), EaK; unfold w64; rewrite unsigned_lit_small by (clear - DR; numconst; zlia); clear - DR; zlia | | zlia].
lazymatch goal with |- sv_denot ?E ?t = _ =>
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E t)); f_equal; change (bv_unsigned (sv_denot E t)) with (U E t); rewrite (U_zev E t eq_refl) end.
cbn [zev zalu_raw]. unfold rho_of. rewrite (HEn5 46%nat (ltHAV 46 eq_refl)), (eq_refl : ew E0 46 = w64 jb). unfold w64. rewrite unsigned_lit_small by zlia.
unfold hdr_byte1. reflexivity. }
split. { memv HS 48%nat 4%nat; [cbn [base_val YP09.r_base]; rewrite (HEn5 45%nat (ltHAV 45 eq_refl)), EaK; unfold w64; rewrite unsigned_lit_small by (clear - DR; numconst; zlia); clear - DR; zlia | | zlia].
lazymatch goal with |- sv_denot ?E ?t = _ =>
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E t)); f_equal; change (bv_unsigned (sv_denot E t)) with (U E t); rewrite (U_zev E t eq_refl) end.
cbn [zev zalu_raw]. unfold rho_of. rewrite (HEn5 62%nat (ltHAV 62 eq_refl)), EaNP. unfold w64. rewrite unsigned_lit_small by zlia.
zcanon_simp. land_lits. rewrite Z.shiftr_div_pow2 by zlia. rewrite Z.div_small by zlia. reflexivity. }
split. { memv HS 48%nat 3%nat; [cbn [base_val YP09.r_base]; rewrite (HEn5 45%nat (ltHAV 45 eq_refl)), EaK; unfold w64; rewrite unsigned_lit_small by (clear - DR; numconst; zlia); clear - DR; zlia
| cbn [sv_denot]; rewrite (HEn5 62%nat (ltHAV 62 eq_refl)), EaNP; unfold w64; rewrite ?Zbv_add_unsigned, ?Z.add_0_r; f_equal; zlia | zlia]. }
split. { memv HS 45%nat 0%nat; [cbn [base_val YP09.r_base]; rewrite (HEn5 40%nat (ltHAV 40 eq_refl)), EaP; unfold w64; rewrite unsigned_lit_small by (clear - DR LF; numconst; zlia); zlia
| cbn [sv_denot]; rewrite (HEn5 41%nat (ltHAV 41 eq_refl)), (eq_refl : ew E0 41 = w64 cnt); unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia | zlia]. }
split. { memv HS 42%nat 0%nat; [cbn [base_val YP09.r_base]; rewrite (HEn5 32%nat (ltHAV 32 eq_refl)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - DR LF; numconst; zlia); unfold T; numconst; zlia | reflexivity | zlia]. }
split. {   intros x Hx. pose proof (u64_range x) as Rx.
assert (N1' : ~ WIN1 false (bv_unsigned x)).
{ pose proof stack_ivs as SI. clear - Hx DR LF HKR Hlo T7 SI. unfold WIN1, WINT, PBW, IFRAME. numconst. zlia. }
rewrite (CH1 x N1') by (clear - Hx DR LF HKR; numconst; zlia). apply SRZ, Hx. }
split. {   intros HH; discriminate HH. }
intros x Hx. pose proof (u64_range x) as Rx.
assert (N1' : ~ WIN1 false (bv_unsigned x)).
{ pose proof stack_ivs as SI. clear - Hx DR LF HKR Hlo T7 SI PT. unfold WIN1, WINT, PBW, IFRAME. numconst. zlia. }
rewrite (MEQ x N1'), (Hin4 x Hx), RA1m2. reflexivity.
Qed.
End e.
End d.
