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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1w AE3d AFhy AFi1 AFj6 AFi4 AFhm.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Set Printing Depth 50. Set Printing Width 180.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Ltac zlia := first [ lia | ceil; unfold zone3, zone3cases, off_img, in_app, app_addr, in_band_rw, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPrimResvSize, kSpaceSize in *; lia ].
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
Section g.
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
Ltac cleanM := try clear Hcache; try clear Hinited; try clear HKpres; try clear HSKpres; try clear HPB250; try clear Hjb_def; try clear SEED; try clear U1;
try clear Hcnt_def; try clear Hoff_def; try clear HQT.
Let m0 := mrestrict (w_H W) mem0.
Let rd0 : reader := aview tfibsegs (w_H W) mem0.
Lemma cell_symM : forall e (w : nat) e', cell_lookup (Tfib_const ly) e = Some (ACell e w (AV e')) -> val_mem tfibsegs m0 (aeval B ly e) w (aeval B ly e').
Proof. cleanM. intros e w e' E. exact (tfib_const_lookup_sym B TS ly S (w_H W) mem0 e w e' HARm E). Qed.
Lemma cell_litM : forall a (w : nat) x, cell_lookup (Tfib_const ly) (ANum a) = Some (ACell (ANum a) w (AV (ANum x))) -> val_mem tfibsegs m0 a w x.
Proof. cleanM. intros a w x E. exact (tfib_const_lookup B TS ly S (w_H W) mem0 a w x HARm E). Qed.
Lemma cell_stateM : forall c e (w : nat) x, In c (acells B ly S) -> c = ACell e w (AV (ANum x)) -> val_mem tfibsegs m0 (aeval B ly e) w x.
Proof. cleanM.
intros c e w x Hin ->. apply (cell_holds_val_mem B ly (w_H W) mem0 e w (ANum x)). exact (proj1 (Forall_forall _ _) (am_cells B ly S rd0 HARm) _ Hin).
Qed.
Lemma unwinding_valM : val_mem tfibsegs m0 (T + t_unwinding) 1 0.
Proof. cleanM.
replace (T + t_unwinding) with (aeval B ly (AT t_unwinding)) by reflexivity.
eapply cell_stateM; [|reflexivity]. unfold acells. do 8 (apply in_or_app; right). left. reflexivity.
Qed.
Lemma count0 : pc_chunks (cache S cl) = [] -> val_mem tfibsegs m0 Pv 4 0.
Proof. cleanM.
intros Hc. replace Pv with (aeval B ly (AT (t_cache + 80 * cl))) by (cbn; unfold Pv, T; zlia).
eapply cell_stateM; [|reflexivity]. unfold acells. apply in_or_app. right. apply in_or_app. left. apply in_flat_map. exists cl.
split; [apply In_zseq; zlia|]. unfold cache_cells. rewrite Hc. destruct (st_cache_inited S); left; reflexivity.
Qed.
Lemma chunk_litM : forall a (nn : BinNums.N) x, val_mem tfibsegs m0 a (N.to_nat nn) x -> 0 <= x < 2 ^ (8 * Z.of_N nn) -> Z.of_N nn <= 8 ->
YP09.chunk_ok tfibsegs E0 m0 0 (YP09.mkChunk a (CVal nn (SLit x))).
Proof. cleanM. intros a nn x H Hx Hnn. eapply chunk_ok_val; [reflexivity | exact Hx | exact Hnn | rewrite Z.add_0_l; exact H]. Qed.
Lemma chunk_lit_atM : forall base a (nn : BinNums.N) x, val_mem tfibsegs m0 (base + a) (N.to_nat nn) x -> 0 <= x < 2 ^ (8 * Z.of_N nn) -> Z.of_N nn <= 8 ->
YP09.chunk_ok tfibsegs E0 m0 base (YP09.mkChunk a (CVal nn (SLit x))).
Proof. cleanM. intros base a nn x H Hx Hnn. eapply chunk_ok_val; [reflexivity | exact Hx | exact Hnn | exact H]. Qed.
Lemma chunk_atomM : forall base a (nn : BinNums.N) k d x, ew E0 k = w64 (x - d) -> 0 <= x - d < 2 ^ 64 ->
val_mem tfibsegs m0 (base + a) (N.to_nat nn) x -> 0 <= x < 2 ^ (8 * Z.of_N nn) -> Z.of_N nn <= 8 ->
YP09.chunk_ok tfibsegs E0 m0 base (YP09.mkChunk a (CVal nn (SOff k d))).
Proof. cleanM.
intros base a nn k d x Hk Hr H Hx Hnn. eapply chunk_ok_val; [| exact Hx | exact Hnn | exact H].
cbn [sv_denot]. rewrite Hk. unfold w64. rewrite Zbv_add_unsigned. f_equal. zlia.
Qed.
Local Ltac reg_introM := unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
Local Ltac lit_regionM :=
reg_introM; split; [zlia|]; split; [zlia|]; split; [intros o Ho; zlia|];
repeat (apply Forall_cons; [apply chunk_litM; [apply cell_litM; vm_compute; reflexivity | cbn; zlia | cbn; zlia] |]); apply Forall_nil.
Local Ltac bare_regionM := reg_introM; rewrite ?EaT, ?EaP, ?EaPV, ?EaK, ?EaU, ?EaSK, ?EaSSLOT; unfold w64; rewrite ?unsigned_lit_small by zlia; split; [zlia|]; split; [zlia|]; split; [intros o Ho; zlia | apply Forall_nil].
Lemma REGM_ok : pc_chunks (cache S cl) = [] -> Forall (region_ok tfibsegs E0 m0) MKREG0.
Proof. cleanM.
intros Hc0. pose proof (count0 Hc0) as CV0. clear Hc0.
pose proof high_facts as (hf1 & hf2 & hf3 & hf4 & hf5 & hf6 & hf7 & hf8 & hf9). pose proof derived_ranges as DR. pose proof Kv_range as HKR.
pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). destruct Hsp as (S1 & S2 & S3 & S4).
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, t_cache, t_unwinding in hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, DR, HKR, T2, T4, T7.
pose proof RZ_num as (RZr & RZ8 & Nlo & NPr & R8r & NPR8 & N8r & NPN8 & FILN).
unfold MKREG0, REG0K, lit1, lit4, lit8, lits8, atom8, CTZ_TABLE. cbn [map combine seq length Z.of_nat Pos.of_succ_nat Pos.succ fst snd Z.mul Z.add Pos.mul Pos.add].
unfold aSB, aSHB, aC, aT, aTOP, aJ0, aJ1, aJ2, aJ3, aJ4, aCNT, aCSZ, aV, aJB, aSK, aP, aPV, aK, aU, aSSLOT.
apply Forall_cons.
{   apply (region_ok_stack tfibsegs E0 m0 2 sp0 (- ASTACK)); [rewrite E2; reflexivity | unfold ASTACK; zlia | zlia |].
intros a Ha. apply apresent_writable_off; [off_by ltac:(unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END, ASTACK in *; zlia) | apply Hpres0; exact Ha]. }
do 8 (apply Forall_cons; [lit_regionM|]).
apply Forall_cons. {   reg_introM. split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia|]. apply Forall_cons; [|apply Forall_nil].
apply (chunk_atomM 0 _ 8 34%nat 0 SB); [rewrite EaSB; unfold w64; f_equal; zlia | unfold SB; zlia | | unfold SB; cbn; zlia | cbn; zlia].
rewrite Z.add_0_l. replace 666040 with (aeval B ly (AInst o_space)) by (cbn; rewrite (ts_inst B TS); reflexivity).
replace SB with (aeval B ly (ASp 0)) by (cbn; unfold SB; zlia). apply cell_symM. vm_compute. reflexivity. }
do 14 (apply Forall_cons; [lit_regionM|]).
apply Forall_cons. {   reg_introM. split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia|]. apply Forall_cons; [|apply Forall_nil].
apply (chunk_atomM 0 _ 8 47%nat 0 SHBv); [reflexivity | unfold SHBv; zlia | | unfold SHBv; cbn; zlia | cbn; zlia].
rewrite Z.add_0_l. apply cell_litM. vm_compute. reflexivity. }
do 7 (apply Forall_cons; [lit_regionM|]).
apply Forall_cons. {   reg_introM. split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia|]. apply Forall_cons; [|apply Forall_nil].
apply chunk_litM; [| cbn; zlia | cbn; zlia]. pose proof (cell_litM 0x5d8fa0 8 0 ltac:(vm_compute; reflexivity)) as H8.
intros k Hk. rewrite (H8 k ltac:(zlia)). rewrite !le_byte_zero. reflexivity. }
apply Forall_cons; [lit_regionM|].
apply Forall_cons. {   reg_introM. unfold TFIB_TP. split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia|]. apply Forall_cons; [|apply Forall_nil].
apply chunk_litM; [| unfold TFIB_TSD; cbn; zlia | cbn; zlia].
replace 6131512 with (aeval B ly (ATp (-88))) by (cbn; rewrite (ts_tp B TS); reflexivity).
replace 6267704 with (aeval B ly (ATsd 0)) by (cbn; rewrite HTSD; reflexivity). apply cell_symM. vm_compute. reflexivity. }
apply Forall_cons. {   reg_introM. unfold TFIB_TSD. split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia|]. apply Forall_cons; [|apply Forall_nil].
apply (chunk_atomM 0 _ 8 33%nat 0 (ly_C ly)); [rewrite EaC; unfold w64; f_equal; zlia | zlia | | cbn; zlia | cbn; zlia].
rewrite Z.add_0_l. replace 6267704 with (aeval B ly (ATsd 0)) by (cbn; rewrite HTSD; reflexivity).
replace (ly_C ly) with (aeval B ly (AC 0)) by (cbn; zlia). apply cell_symM. vm_compute. reflexivity. }
apply Forall_cons. {   reg_introM. rewrite EaC. unfold w64. rewrite unsigned_lit_small by zlia.
split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia|]. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
- apply chunk_lit_atM; [| cbn; zlia | cbn; zlia]. replace (ly_C ly + 8) with (aeval B ly (AC 8)) by reflexivity. apply (cell_symM (AC 8) 4 (ANum 0)). vm_compute. reflexivity.
- apply (chunk_atomM _ _ 8 32%nat 0 T); [rewrite EaT; unfold w64; f_equal; zlia | zlia | | cbn; zlia | cbn; zlia].
replace (ly_C ly + 152) with (aeval B ly (AC 152)) by reflexivity. replace T with (aeval B ly (AT 0)) by (cbn; unfold T; zlia).
apply cell_symM. vm_compute. reflexivity. }
apply Forall_cons. {   reg_introM. rewrite EaT. unfold w64. rewrite unsigned_lit_small by zlia.
split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
- apply (chunk_atomM _ _ 8 33%nat 0 (ly_C ly)); [rewrite EaC; unfold w64; f_equal; zlia | zlia | | cbn; zlia | cbn; zlia].
replace (ly_T ly + 0) with (aeval B ly (AT 0)) by (cbn; zlia). replace (ly_C ly) with (aeval B ly (AC 0)) by (cbn; zlia). apply cell_symM. vm_compute. reflexivity.
- apply (chunk_atomM _ _ 8 35%nat 0 (ly_top ly)); [rewrite EaTOP; unfold w64; f_equal; zlia | zlia | | cbn; zlia | cbn; zlia].
replace (ly_T ly + 8) with (aeval B ly (AT 8)) by (cbn; zlia). replace (ly_top ly) with (aeval B ly (ATop 0)) by (cbn; zlia). apply cell_symM. vm_compute. reflexivity.
- apply (chunk_atomM _ _ 8 35%nat (- kStackSpan) (ly_top ly - kStackSpan)); [rewrite EaTOP; unfold w64; f_equal; zlia | unfold kStackSpan; zlia | | unfold kStackSpan; cbn; zlia | cbn; zlia].
replace (ly_T ly + 16) with (aeval B ly (AT 16)) by (cbn; zlia). replace (ly_top ly - kStackSpan) with (aeval B ly (ATop (- kStackSpan))) by (cbn; zlia).
apply cell_symM. vm_compute. reflexivity.
- apply chunk_lit_atM; [| cbn; zlia | cbn; zlia]. replace (ly_T ly + 40) with (aeval B ly (AT 40)) by (cbn; zlia). apply (cell_symM (AT 40) 1 (ANum 0)). vm_compute. reflexivity. }
apply Forall_cons; [bare_regionM|].
apply Forall_cons. {   reg_introM. rewrite EaT. unfold w64. rewrite unsigned_lit_small by zlia. unfold t_unwinding.
split; [zlia|]. split; [zlia|]. split.
{ intros o Ho. apply apresent_writable_off; [off_by ltac:(unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; zlia) |]. replace (ly_T ly + o) with (ly_T ly + 3168) by zlia.
pose proof unwinding_valM as U.
eapply mbyte_off_apresent; [off_by ltac:(unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; zlia) |]. unfold T, t_unwinding in U. rewrite <- (Z.add_0_r (ly_T ly + 3168)). exact (U 0%nat ltac:(zlia)). }
apply Forall_cons; [|apply Forall_nil]. apply chunk_lit_atM; [| cbn; zlia | cbn; zlia]. exact unwinding_valM. }
apply Forall_cons; [bare_regionM|].
apply Forall_cons; [bare_regionM|].
apply Forall_cons. {   reg_introM. rewrite EaP. unfold w64. rewrite unsigned_lit_small by zlia.
split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia|]. apply Forall_cons; [|apply Forall_nil].
apply chunk_lit_atM; [| cbn; zlia | cbn; zlia]. rewrite Z.add_0_r. exact CV0. }
apply Forall_cons; [bare_regionM|].
apply Forall_cons; [bare_regionM|].
apply Forall_cons; [bare_regionM|].
apply Forall_cons; [bare_regionM|apply Forall_nil].
Qed.
Lemma PAIRSM_ok : pairwise_disjoint E0 MKREG0.
Proof. cleanM.
apply (pairwise_disjoint_ext3 E0 REG0K MKREG0 (eq_sym MKREG0_skel)).
pose proof high_facts as (hf1 & hf2 & hf3 & hf4 & hf5 & hf6 & hf7 & hf8 & hf9). pose proof derived_ranges as DR. pose proof Kv_range as HKR.
pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). destruct Hsp as (S1 & S2 & S3 & S4).
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, t_cache, t_unwinding in hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, DR, HKR, T2, T4, T7.
apply pairwise_disjoint_of_extents. unfold REG0K, lit1, lit4, lit8, lits8, atom8, extent_of_region, CTZ_TABLE.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val length Z.of_nat Pos.of_succ_nat Pos.succ].
unfold aSB, aSHB, aC, aT, aTOP, aSK, aP, aPV, aK, aSSLOT.
rewrite E2, EaT, EaC, EaP, EaPV, EaK, EaSK, EaSSLOT. unfold w64. rewrite !unsigned_lit_small by zlia.
pose proof stack_ivs as (SI1 & SI2 & SI3). pose proof HCX as [CP CT]. unfold zdisjoint in CP, CT. cbn [fst snd] in CP, CT.
pose proof blocks_facts as (_ & _ & _ & _ & _ & _ & _ & _ & PT). unfold zdisjoint in PT. cbn [fst snd] in PT.
pose proof RZ_num as RZN. clear - sp0 T SB S1 S3 T2 T4 T7 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hf8 DR HKR SI1 SI2 SI3 CP CT PT Hcl Hcnt RZN.
unfold TFIB_TP, TFIB_TSD, t_unwinding, ASTACK in *. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
unfold sp0, T, SB in *. unfold PVv, SSLOTv, Pv in *. unfold t_cache, t_stats, kThreadObjSize, kPrimResvSize in *.
repeat split; first [clear; zlia | zlia].
Qed.
Lemma Kv32M : Kv mod 32 = 0.
Proof. cleanM.
pose proof (lo_space_al ly LY) as SAL. apply Z.mod_divide in SAL as [q Hq]; [|zlia]. apply Z.mod_divide in Hv2 as [w Hw]; [|zlia].
unfold Kv, SB. rewrite Hq, Hw. apply Z.mod_divide; [zlia|]. exists (q * 2048 + cl * 2 ^ 27 + w). zlia.
Qed.
Lemma cl_k0M : 1 <= cl <= 2.
Proof. cleanM.
pose proof RZ_num as (RZr & RZ8 & Nlo & NPr & R8r & NPR8 & N8r & NPN8 & FILN).
rewrite Hcl_def. unfold class_id. replace (R8v + RZ <=? 512) with true by (symmetry; apply Z.leb_le; zlia).
pose proof (Z.div_le_lower_bound (R8v + RZ + 31) 32 1 ltac:(zlia) ltac:(zlia)). pose proof (Z.div_lt_upper_bound (R8v + RZ + 31) 32 3 ltac:(zlia) ltac:(zlia)). zlia.
Qed.
Lemma FACTSM_ok : atoms_ok E0 (f_atoms FK).
Proof. cleanM.
pose proof high_facts as (hf1 & hf2 & hf3 & hf4 & hf5 & hf6 & hf7 & hf8 & hf9). pose proof derived_ranges as DR. pose proof Kv_range as HKR.
pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). destruct Hsp as (S1 & S2 & S3 & S4).
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, t_cache, t_unwinding in hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, DR, HKR, T2, T4, T7.
pose proof tr_length as TL. pose proof (lo_space_al ly LY) as SAL. pose proof (lo_T_al ly LY) as TAL. pose proof (lo_C_al ly LY) as CAL.
unfold page_aligned in TAL.
assert (V1 : 17594333495296 <= Kv) by (clear - HKR hf3 hf4; zlia). assert (V2 : Kv + 2 ^ 16 <= 140737479966720) by (clear - HKR hf5 hf6; zlia).
assert (E2' : ew E0 2 = w64 sp0) by (rewrite E2; unfold sp0, w64; symmetry; apply Z_to_bv_bv_unsigned).
assert (AF : forall k X lo hi al, ew E0 k = w64 X -> 0 <= X < 2 ^ 64 -> lo <= X <= hi -> X mod 2 ^ al = 0 -> 0 <= al <= 64 -> afact_ok E0 k (mkAF lo hi al)).
{ clear. intros k X lo hi al HE HX HB HM HA. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE. unfold w64. rewrite unsigned_lit_small by exact HX. repeat split; zlia. }
cbn [FK f_atoms atoms_ok]. unfold aSB, aSHB, aC, aT, aTOP, aSK, aP, aPV, aK, aSSLOT, aLEN, aJ0, aR8, aCL, aCNT, aV, aCSZ, aJB, aJ1, aJ2, aJ3, aJ4, aPB, aN8D, aCNT8, aNP, aND.
pose proof RZ_num as (RZr & RZ8 & Nlo & NPr & R8r & NPR8 & N8r & NPN8 & FILN). pose proof Kv32M as K32. pose proof K0_facts as KF. pose proof cl_k0M as CK.
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, ASTACK.
split. { apply (AF 2%nat sp0); [exact E2'| | | |].
all: pose proof (u64_range (getr regs0 2)) as U; clear - U S1 S3 S4 T4 T7; unfold ASTACK in *; first [zlia | replace (2 ^ 4) with 16 by reflexivity; exact S4]. }
split. { apply (AF 10%nat n); [rewrite E10, Hn; reflexivity| | | |].
all: clear - Nlo; first [zlia | replace (2 ^ 0) with 1 by reflexivity; apply Z.mod_1_r]. }
split. { apply (AF 32%nat T); [exact EaT| | | |].
all: clear - hf1 hf2 TAL; first [zlia | exact TAL]. }
split. { apply (AF 33%nat (ly_C ly)); [exact EaC| | | |].
all: clear - hf7 hf8 CAL; first [zlia | exact CAL]. }
split. { apply (AF 34%nat SB); [exact EaSB| | | |].
all: clear - hf3 hf4 hf5 hf6 SAL; first [zlia | exact SAL]. }
split. { apply (AF 35%nat (ly_top ly)); [exact EaTOP| | | |].
all: clear - T1 T2 T3 T4 T7; first [zlia | exact T3]. }
split. { apply (AF 36%nat (Z.of_nat (length tr))); [reflexivity| | | |].
all: clear - TL; first [zlia | replace (2 ^ 0) with 1 by reflexivity; apply Z.mod_1_r]. }
split. { apply (AF 37%nat (j0 mod 2 ^ 64)); [apply Z_to_bv64_eq_mod; rewrite Z.mod_mod by zlia; reflexivity| | | |].
all: clear - j0; first [zlia | pose proof (Z.mod_pos_bound j0 (2 ^ 64) ltac:(zlia)); zlia | replace (2 ^ 0) with 1 by reflexivity; apply Z.mod_1_r]. }
split. { apply (AF 38%nat R8v); [reflexivity| | | |].
all: clear - DR R8r; first [zlia | replace (2 ^ 3) with 8 by reflexivity; zlia]. }
split. { apply (AF 39%nat cl); [reflexivity| | | |].
all: clear - CK; first [zlia | replace (2 ^ 0) with 1 by reflexivity; apply Z.mod_1_r]. }
split. { apply (AF 40%nat Pv); [exact EaP| | | |].
all: clear - DR hf1 hf2 TAL; unfold Pv, t_cache in *; first [zlia | replace (2 ^ 4) with 16 by reflexivity; apply Z.mod_divide in TAL as [q Hq]; [|zlia]; apply Z.mod_divide; [zlia|]; exists (q * 256 + 13 + 5 * cl); zlia]. }
split. { apply (AF 41%nat cnt); [reflexivity| | | |].
all: clear - Hcnt; first [zlia | replace (2 ^ 0) with 1 by reflexivity; apply Z.mod_1_r]. }
split. { apply (AF 42%nat v); [reflexivity| | | |].
all: clear - Hv; first [zlia | replace (2 ^ 0) with 1 by reflexivity; apply Z.mod_1_r]. }
split. { apply (AF 43%nat (csz mod 2 ^ 64)); [apply Z_to_bv64_eq_mod; rewrite Z.mod_mod by zlia; reflexivity| | | |].
all: clear - csz; first [zlia | pose proof (Z.mod_pos_bound csz (2 ^ 64) ltac:(zlia)); zlia | replace (2 ^ 0) with 1 by reflexivity; apply Z.mod_1_r]. }
split. { apply (AF 44%nat PVv); [exact EaPV| | | |].
all: clear - DR hf1 hf2 TAL Hcnt; unfold PVv, Pv, t_cache in *; first [zlia | replace (2 ^ 2) with 4 by reflexivity; apply Z.mod_divide in TAL as [q Hq]; [|zlia]; apply Z.mod_divide; [zlia|]; exists (q * 1024 + 56 + 20 * cl + (cnt - 1)); zlia]. }
split. { apply (AF 45%nat Kv); [exact EaK| | | |].
all: clear - V1 V2 K32; first [zlia | replace (2 ^ 5) with 32 by reflexivity; exact K32]. }
split. { apply (AF 46%nat jb); [reflexivity| | | |].
all: clear - Hjb; first [zlia | replace (2 ^ 0) with 1 by reflexivity; apply Z.mod_1_r]. }
split. { apply (AF 47%nat SHBv); [reflexivity| | | |].
all: clear; unfold SHBv; first [zlia | reflexivity]. }
split. { apply (AF 48%nat SKv); [exact EaSK| | | |].
all: clear - DR K32; unfold SKv, SHBv in *; first [zlia | replace (2 ^ 2) with 4 by reflexivity; apply Z.mod_divide in K32 as [q Hq]; [|zlia]; apply Z.mod_divide; [zlia|]; exists (536862720 + q); rewrite Hq; replace (q * 32) with (q * 4 * 8) by zlia; rewrite Z.div_mul by zlia; zlia]. }
split. { apply (AF 49%nat (j1 mod 2 ^ 64)); [apply Z_to_bv64_eq_mod; rewrite Z.mod_mod by zlia; reflexivity| | | |].
all: clear - j1; first [zlia | pose proof (Z.mod_pos_bound j1 (2 ^ 64) ltac:(zlia)); zlia | replace (2 ^ 0) with 1 by reflexivity; apply Z.mod_1_r]. }
split. { apply (AF 50%nat (j2 mod 2 ^ 64)); [apply Z_to_bv64_eq_mod; rewrite Z.mod_mod by zlia; reflexivity| | | |].
all: clear - j2; first [zlia | pose proof (Z.mod_pos_bound j2 (2 ^ 64) ltac:(zlia)); zlia | replace (2 ^ 0) with 1 by reflexivity; apply Z.mod_1_r]. }
split. { apply (AF 51%nat (j3 mod 2 ^ 64)); [apply Z_to_bv64_eq_mod; rewrite Z.mod_mod by zlia; reflexivity| | | |].
all: clear - j3; first [zlia | pose proof (Z.mod_pos_bound j3 (2 ^ 64) ltac:(zlia)); zlia | replace (2 ^ 0) with 1 by reflexivity; apply Z.mod_1_r]. }
split. { apply (AF 52%nat SSLOTv); [exact EaSSLOT| | | |].
all: clear - DR hf1 hf2 TAL; unfold SSLOTv, t_stats in *; first [zlia | replace (2 ^ 3) with 8 by reflexivity; apply Z.mod_divide in TAL as [q Hq]; [|zlia]; apply Z.mod_divide; [zlia|]; exists (q * 512 + 364 + cl); zlia]. }
split. { apply (AF 53%nat (j4 mod 2 ^ 64)); [apply Z_to_bv64_eq_mod; rewrite Z.mod_mod by zlia; reflexivity| | | |].
all: clear - j4; first [zlia | pose proof (Z.mod_pos_bound j4 (2 ^ 64) ltac:(zlia)); zlia | replace (2 ^ 0) with 1 by reflexivity; apply Z.mod_1_r]. }
split. { apply (AF 54%nat PBv); [exact EaPB| | | |].
all: clear - DR; first [zlia | replace (2 ^ 0) with 1 by reflexivity; apply Z.mod_1_r]. }
split. { apply (AF 55%nat N8D); [reflexivity| | | |].
all: clear - DR Nlo; first [zlia | replace (2 ^ 3) with 8 by reflexivity; zlia]. }
split. { apply (AF 56%nat (N8D / 8)); [reflexivity| | | |].
all: clear - DR Nlo; first [zlia | replace (2 ^ 0) with 1 by reflexivity; apply Z.mod_1_r]. }
split. { apply (AF 62%nat NPv); [exact EaNP| | | |].
all: clear - NPr; first [zlia | replace (2 ^ 0) with 1 by reflexivity; apply Z.mod_1_r]. }
split; [|exact I]. { apply (AF 63%nat NDv); [exact EaND| | | |].
all: clear - KF DR; first [zlia | replace (2 ^ 3) with 8 by reflexivity; zlia]. }
Qed.
Lemma SEEDM_ok : pc_chunks (cache S cl) = [] -> st_ok tfibsegs E0 MK0 (restrict (w_H W) (mkst regs0 (w64 0x52930) mem0 (seg_rom tfibsegs))).
Proof. cleanM.
intros Hc0. rewrite restrict_mkst_fx. unfold MK0, w64. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate | cbn [sv_denot]; exact Htp].
- vm_compute. reflexivity.
- cbn [ms_mem mkst]. exact (REGM_ok Hc0).
- exact PAIRSM_ok.
- split; [exact FACTSM_ok | split; exact I].
Qed.
End g.
End f.
