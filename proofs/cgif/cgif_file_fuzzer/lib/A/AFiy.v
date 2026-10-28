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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1w AE3d AFhy AFis.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Set Printing Depth 50. Set Printing Width 180.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
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
Section h.
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
Let cfg0 : config := mkCfg (mkst regs0 (w64 0x52930) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis U1 : tfib_unwind_spec.
Hypothesis SEED : st_ok tfibsegs E0 SS0 (restrict (w_H W) (mkst regs0 (w64 0x52930) mem0 (seg_rom tfibsegs))).
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
Ltac clean := try clear Hcl; try clear Hv; try clear Hcnt; try clear Hjb; try clear HKpres; try clear HSKpres; try clear HPB250; try clear SEED; try clear U1;
pose proof RZ_num as (RZr & RZ8 & RZ88 & Nlo & NRZ).
Lemma cl_range : 1 <= cl <= 30.
Proof. clean.
pose proof casek_sizes as (_ & _ & _ & _ & FP & _).
pose proof (primary_geometry n ltac:(zlia) FP) as (G & _). rewrite <- Hcl_class in G. exact G.
Qed.
Lemma cls_geom :
0 < class_size cl /\ class_size cl mod 32 = 0 /\ class_size cl <= kMaxSize /\ 2 <= max_cached cl <= 16 /\
RZ + n <= class_size cl /\ RZ + R8v <= class_size cl.
Proof. clean.
pose proof casek_sizes as (_ & RS & R8 & NP & FP & NS & RQ).
pose proof (primary_geometry n ltac:(zlia) FP) as (G1 & G2 & G3 & G4 & G5). rewrite <- Hcl_class in *.
pose proof (class_ok cl ltac:(zlia)) as (K1 & K2 & K3 & K4 & K5 & K6).
rewrite RS, RQ, NS in G2. repeat split; try zlia.
Qed.
Lemma cls_wf : cls_ok cl (reg S cl) (cache S cl) (st_cache_inited S) (chunk_offs S cl) (batch_offs S cl).
Proof. clean. exact (wf_classes _ _ _ _ _ WF cl ltac:(pose proof cl_range; zlia)). Qed.
Lemma off_facts :
0 <= off /\ off + class_size cl <= rg_alloc_user (reg S cl) /\ off mod class_size cl = 0 /\ off mod 16 = 0 /\
rg_alloc_user (reg S cl) <= rg_mapped_user (reg S cl) <= 2 ^ 31 /\
~ In off ((fa_elems (class_size cl) (rg_free (reg S cl)) ++ l) ++ (chunk_offs S cl ++ batch_offs S cl)) /\
1 <= cnt <= 16 /\ cnt = Z.of_nat (length l) + 1 /\ pc_max (cache S cl) = max_cached cl.
Proof. clean.
pose proof cls_wf as CL. pose proof cls_geom as (K1 & K2 & K3 & K4 & K5 & K6). pose proof cl_range as CR.
pose proof (wr_elems _ _ _ _ _ _ CL) as EL. pose proof (wr_nodup _ _ _ _ _ _ CL) as ND. pose proof (wr_alloc _ _ _ _ _ _ CL) as AL.
pose proof (wr_alloc_al _ _ _ _ _ _ CL) as AA. pose proof (wr_cache _ _ _ _ _ _ CL) as WC. rewrite Hinited in WC. destruct WC as [WM WL].
pose proof (mapped_user_bound (as_universe B) 0 0 0 S cl WF ltac:(zlia)) as MB. unfold kUserMapSize, EV_MAX in MB.
rewrite Hcache in EL, ND, WL.
assert (IN : In off (fa_elems (class_size cl) (rg_free (reg S cl)) ++ (l ++ [off]) ++ chunk_offs S cl ++ batch_offs S cl)).
{ apply in_app_iff. right. apply in_app_iff. left. apply in_app_iff. right. left. reflexivity. }
pose proof (proj1 (Forall_forall _ _) EL off IN) as [O1 O2].
assert (XS : off + class_size cl <= rg_alloc_user (reg S cl)).
{ pose proof O2 as O2'. apply Z.mod_divide in O2' as [qx Hqx]; [|zlia]. pose proof AA as AA'. apply Z.mod_divide in AA' as [qa Hqa]; [|zlia].
assert (Hq : qx < qa) by (apply (Z.mul_lt_mono_pos_r (class_size cl)); zlia).
pose proof (Z.mul_le_mono_nonneg_r (qx + 1) qa (class_size cl) ltac:(zlia) ltac:(zlia)). zlia. }
assert (M16 : off mod 16 = 0).
{ apply Z.mod_divide in O2 as [q Hq]; [|zlia]. apply Z.mod_divide in K2 as [q' Hq']; [|zlia]. apply Z.mod_divide; [zlia|]. exists (q * (q' * 2)). zlia. }
rewrite length_app in Hcnt_def, WL. cbn [length] in Hcnt_def, WL.
assert (NI : ~ In off ((fa_elems (class_size cl) (rg_free (reg S cl)) ++ l) ++ (chunk_offs S cl ++ batch_offs S cl))).
{ apply NoDup_remove_2. replace ((fa_elems (class_size cl) (rg_free (reg S cl)) ++ l) ++ off :: chunk_offs S cl ++ batch_offs S cl)
with (fa_elems (class_size cl) (rg_free (reg S cl)) ++ (l ++ [off]) ++ chunk_offs S cl ++ batch_offs S cl); [exact ND|].
rewrite <- !app_assoc. reflexivity. }
repeat split; try zlia. exact NI.
Qed.
Lemma Kv_base : Kv = region_base ly cl + off.
Proof. clean. unfold Kv, SB, region_base. pose proof cl_range. rewrite region_off_eq by zlia. zlia. Qed.
Lemma Kv_geom : kHighMemBeg <= Kv /\ Kv + class_size cl <= ASAN_CEIL /\ Kv mod 16 = 0 /\
ly_prim ly <= Kv /\ Kv + class_size cl <= ly_prim ly + kPrimResvSize.
Proof. clean.
pose proof off_facts as (O1 & O2 & O3 & O4 & O5 & _). pose proof (region_in_prim ly cl LY ltac:(pose proof cl_range; zlia)) as (R1 & R2 & R3 & R4 & R5).
rewrite Kv_base. repeat split; zlia.
Qed.
Lemma Hcl' : 1 <= cl <= 31. Proof. clean. pose proof cl_range. zlia. Qed.
Lemma Hcnt' : 1 <= cnt <= 16. Proof. clean. pose proof off_facts; tauto. Qed.
Lemma Hv' : 0 <= v /\ 16 * v + 2 ^ 16 <= 2 ^ 32.
Proof. clean. pose proof off_facts as (O1 & O2 & _ & _ & O5 & _). pose proof cls_geom as (K1 & _). zlia. Qed.
Ltac clean2 := clean; pose proof Hcl' as Hcl; pose proof Hv' as Hv; pose proof Hcnt' as Hcnt.
Lemma cached_vs_chunk : forall k, In k (st_chunks S) -> ck_base B ly k + ck_extent k <= Kv \/ Kv + class_size cl <= ck_base B ly k.
Proof. clean2.
intros k Hk.
pose proof (chunk_facts B ly S rd0 k HARm Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
pose proof off_facts as (O1 & O2 & O3 & O4 & O5 & NI & _). pose proof Kv_geom as (V1 & V2 & V3 & V4 & V5). pose proof cls_geom as (K1 & _).
destruct (ck_beg k) as [|o|r o|c p] eqn:Eb; try solve [destruct GG].
-
cbv zeta in GG. destruct GG as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9).
set (c' := prim_class o) in *. set (x' := o - region_off c') in *.
rewrite C4, C5. rewrite Kv_base. unfold region_base.
destruct (Z.eq_dec c' cl) as [E|NE].
+
rewrite E in *.
assert (NEQ : x' <> off).
{ intros EQ. apply NI. apply in_app_iff. right. apply in_app_iff. left.
pose proof (In_chunk_offs S k o Hk Eb) as IN. fold c' in IN. fold x' in IN. rewrite E, EQ in IN. exact IN. }
apply Z.mod_divide in C7 as [q Hq]; [|zlia]. apply Z.mod_divide in O3 as [q' Hq']; [|zlia].
assert (q <> q') by (intros ->; apply NEQ; zlia).
destruct (Z_lt_le_dec q q').
* left. pose proof (Z.mul_le_mono_nonneg_r (q + 1) q' (class_size cl) ltac:(zlia) ltac:(zlia)). zlia.
* right. pose proof (Z.mul_le_mono_nonneg_r (q' + 1) q (class_size cl) ltac:(zlia) ltac:(zlia)). zlia.
+
pose proof (mapped_user_bound (as_universe B) 0 0 0 S c' WF ltac:(zlia)) as MB. unfold kUserMapSize, EV_MAX in MB.
pose proof (class_ok c' ltac:(zlia)) as (K1' & _).
rewrite !region_off_eq by zlia.
destruct (Z_lt_le_dec c' cl).
* left. assert (c' * 2 ^ 32 + 2 ^ 32 <= cl * 2 ^ 32) by nia. zlia.
* right. assert (cl * 2 ^ 32 + 2 ^ 32 <= c' * 2 ^ 32) by nia. zlia.
-
destruct GG as (S1 & S2 & S3 & S4 & S5 & S6 & S7).
pose proof (am_placed B ly S rd0 HARm) as [_ PD].
pose proof (pairwise_In zdisjoint (sec_extents ly S ++ static_extents ly) (ly_sec ly r, sec_map_size (ck_req k)) (ly_prim ly, kPrimResvSize)
(sec_extents ly S) (static_extents ly) eq_refl PD S5 ltac:(unfold static_extents, owned_extents; cbn; tauto)) as D.
unfold zdisjoint in D. cbn [fst snd] in D. rewrite S3, S4. unfold kPage in *. zlia.
Qed.
Lemma find_chunk_at_none : forall lst g, (forall k, In k lst -> ~ (ck_base B ly k <= g < ck_base B ly k + ck_extent k)) -> find_chunk_at B ly lst g = None.
Proof. clean2.
induction lst as [|k t IH]; intros g H; [reflexivity|]. cbn [find_chunk_at].
destruct (Z.leb_spec (ck_base B ly k) g); destruct (Z.ltb_spec g (ck_base B ly k + ck_extent k)); cbn [andb];
try (apply IH; intros k' Hk'; apply H; right; exact Hk').
exfalso. apply (H k (or_introl eq_refl)). zlia.
Qed.
Lemma shadow250 : forall g, g mod 8 = 0 -> Kv <= g < Kv + class_size cl -> rd0 (shadow_addr g) = Some 250.
Proof. clean2.
intros g Hg8 Hg.
apply (am_shadow B ly S rd0 HARm g 250 Hg8). unfold ashadow.
rewrite find_chunk_at_none.
2:{ intros k Hk. pose proof (cached_vs_chunk k Hk). zlia. }
pose proof off_facts as (O1 & O2 & O3 & O4 & O5 & _).
rewrite (in_rangesb_In g (fa_poison_ranges ly S) (region_base ly cl) (rg_mapped_user (reg S cl))); [reflexivity| |rewrite Kv_base in Hg; zlia].
unfold fa_poison_ranges. apply in_app_iff. left. apply in_flat_map. exists cl. split; [apply In_zseq; pose proof cl_range; zlia|]. left. reflexivity.
Qed.
Lemma shadow_present : forall s, SKv <= s < SKv + class_size cl / 8 -> rd0 s = Some 250 /\ apresent (w_H W) mem0 s.
Proof. clean2.
intros s Hs.
pose proof Kv_geom as (V1 & V2 & V3 & _). pose proof cls_geom as (K1 & K2 & _).
assert (E : s = shadow_addr (Kv + 8 * (s - SKv))).
{ unfold shadow_addr. rewrite (Z.mul_comm 8 (s - SKv)), Z.div_add by zlia. unfold SKv, SHBv, SHADOW_OFF. zlia. }
assert (R : rd0 s = Some 250).
{ rewrite E. apply shadow250; [| unfold SKv, SHBv in *; pose proof (Z.div_mod Kv 8 ltac:(zlia));
pose proof (Z.div_le_mono (8 * (s - (2147450880 + Kv / 8)) + 7) (class_size cl) 8 ltac:(zlia)); nia].
rewrite Z.add_mod, Z.mul_comm, Z_mod_mult by zlia. replace (Kv mod 8) with 0; [reflexivity|].
symmetry. apply Z.mod_divide in V3 as [q Hq]; [|zlia]. apply Z.mod_divide; [zlia|]. exists (2 * q). zlia. }
split; [exact R|].
pose proof (aview_byte (w_H W) mem0 s 250 R) as R'. eapply mbyte_off_apresent; [off_by ltac:(idtac) | exact R'].
pose proof derived_ranges as (_ & _ & _ & D4 & D5 & _). pose proof (Z.div_le_mono (class_size cl) kMaxSize 8 ltac:(zlia) ltac:(pose proof cls_geom; tauto)) as DM.
change (kMaxSize / 8) with 8192 in DM. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END, kHighMemBeg in *. zlia.
Qed.
Lemma vis_present : forall e len a, In (e, len) (ajunk B ly S) \/ In (e, len) (aareas S) ->
aeval B ly e <= a < aeval B ly e + len -> off_img a -> apresent (w_H W) mem0 a.
Proof. clean2.
intros e len a Hin Ha Hhi.
assert (RV : range_vis B ly rd0 (e, len)).
{ destruct Hin as [Hin|Hin]; [exact (proj1 (Forall_forall _ _) (am_junk B ly S rd0 HARm) _ Hin) | exact (proj1 (Forall_forall _ _) (am_areas B ly S rd0 HARm) _ Hin)]. }
destruct (range_vis_mbyte B ly (w_H W) mem0 e len (a - aeval B ly e) RV ltac:(zlia)) as [b Hb].
replace (aeval B ly e + (a - aeval B ly e)) with a in Hb by zlia. exact (mbyte_off_apresent (w_H W) mem0 a b Hhi Hb).
Qed.
Lemma KPRES : forall a, Kv <= a < Kv + RZ + R8v -> apresent (w_H W) mem0 a.
Proof. clean2.
intros a Ha. pose proof off_facts as (O1 & O2 & O3 & O4 & O5 & _). pose proof Kv_geom as (V1 & V2 & _). pose proof cls_geom as (K1 & _ & _ & _ & _ & K6).
apply (vis_present (ASp (region_off cl)) (rg_mapped_user (reg S cl))).
- right. unfold aareas. apply in_app_iff. left. apply in_flat_map. exists cl. split; [apply In_zseq; pose proof cl_range; zlia|]. left. reflexivity.
- cbn [aeval]. fold (region_base ly cl). pose proof Kv_base. unfold region_base in *. zlia.
- apply off_img_high. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END, kHighMemBeg, ASAN_CEIL in *. zlia.
Qed.
Lemma SKPRES : forall a, SKv <= a < SKv + (RZ + R8v) / 8 -> apresent (w_H W) mem0 a.
Proof. clean2.
intros a Ha. pose proof cls_geom as (K1 & _ & _ & _ & _ & K6).
apply shadow_present. pose proof (Z.div_le_mono (RZ + R8v) (class_size cl) 8 ltac:(zlia) K6). zlia.
Qed.
Lemma PB250 : n mod 8 <> 0 -> val_mem tfibsegs (mrestrict (w_H W) mem0) PBv 1 250.
Proof. clean2.
intros E8. pose proof cls_geom as (K1 & _ & _ & _ & _ & K6). pose proof derived_ranges as DR.
assert (R8odd : R8v = N8D + 8).
{ clear - Nlo E8. unfold R8v, N8D. pose proof (Z.div_mod n 8 ltac:(zlia)). pose proof (Z.mod_pos_bound n 8 ltac:(zlia)).
assert ((n + 7) / 8 = n / 8 + 1) by (symmetry; apply (Z.div_unique_pos (n+7) 8 (n/8 + 1) (n mod 8 - 1)); zlia). zlia. }
destruct (shadow_present PBv) as [R _].
{ pose proof (Z.div_le_mono (RZ + R8v) (class_size cl) 8 ltac:(zlia) K6) as DM.
replace ((RZ + R8v) / 8) with (RZ / 8 + N8D / 8 + 1) in DM; [zlia|]. rewrite R8odd.
replace (RZ + (N8D + 8)) with ((RZ / 8 + N8D / 8 + 1) * 8) by zlia. rewrite Z.div_mul by zlia. reflexivity. }
intros k Hk. replace (PBv + Z.of_nat k) with PBv by zlia. rewrite (aview_byte _ _ _ _ R). destruct k; [reflexivity | zlia].
Qed.
Lemma in_thread_junk : forall r, In r thread_junk -> In r (ajunk B ly S).
Proof. clean2. intros r Hr. unfold ajunk. right. right. do 5 (apply in_or_app; right). apply in_or_app. left. exact Hr. Qed.
Lemma junk_word : forall a, T + t_cache_stats <= a -> a + 8 <= T + t_unwinding -> exists w, val_mem tfibsegs (mrestrict (w_H W) mem0) a 8 w.
Proof. clean2.
intros a H1 H2. pose proof high_facts as (F1 & F2 & _).
assert (BY : forall k, (k < 8)%nat -> exists b, mbyte tfibsegs (mrestrict (w_H W) mem0) (a + Z.of_nat k) = Some b).
{ intros k Hk. set (i := Z.of_nat k). assert (Hi : 0 <= i < 8) by zlia. clearbody i. destruct (Z_lt_le_dec (a + i) (T + t_stats)).
- destruct (range_vis_mbyte B ly (w_H W) mem0 (AT t_cache_stats) (t_stats - t_cache_stats) (a + i - (T + t_cache_stats))
(proj1 (Forall_forall _ _) (am_junk B ly S rd0 HARm) (AT t_cache_stats, t_stats - t_cache_stats) (in_thread_junk _ (or_intror (or_introl eq_refl))))
ltac:(unfold t_cache_stats, t_stats, t_unwinding in *; cbn; zlia)) as [b Hb].
exists b. cbn [aeval] in Hb. replace (ly_T ly + t_cache_stats + (a + i - (T + t_cache_stats))) with (a + i) in Hb by (unfold T; zlia). exact Hb.
- destruct (range_vis_mbyte B ly (w_H W) mem0 (AT t_stats) (t_unwinding - t_stats) (a + i - (T + t_stats))
(proj1 (Forall_forall _ _) (am_junk B ly S rd0 HARm) (AT t_stats, t_unwinding - t_stats) (in_thread_junk _ (or_intror (or_intror (or_introl eq_refl)))))
ltac:(unfold t_cache_stats, t_stats, t_unwinding in *; cbn; zlia)) as [b Hb].
exists b. cbn [aeval] in Hb. replace (ly_T ly + t_stats + (a + i - (T + t_stats))) with (a + i) in Hb by (unfold T; zlia). exact Hb. }
destruct (BY 0%nat ltac:(zlia)) as [b0 B0]. destruct (BY 1%nat ltac:(zlia)) as [b1 B1]. destruct (BY 2%nat ltac:(zlia)) as [b2 B2]. destruct (BY 3%nat ltac:(zlia)) as [b3 B3].
destruct (BY 4%nat ltac:(zlia)) as [b4 B4]. destruct (BY 5%nat ltac:(zlia)) as [b5 B5]. destruct (BY 6%nat ltac:(zlia)) as [b6 B6]. destruct (BY 7%nat ltac:(zlia)) as [b7 B7].
pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1. pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3.
pose proof (bv_unsigned_in_range 8 b4) as R4. pose proof (bv_unsigned_in_range 8 b5) as R5. pose proof (bv_unsigned_in_range 8 b6) as R6. pose proof (bv_unsigned_in_range 8 b7) as R7.
change (bv_modulus 8) with 256 in R0, R1, R2, R3, R4, R5, R6, R7.
exists (bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7))))))).
assert (LB : forall (z q b : Z) (k : nat) r, (k < 8)%nat -> 0 <= b < 256 -> 0 <= q -> 0 <= r < 2 ^ (8 * Z.of_nat k) ->
z = 2 ^ (8 * Z.of_nat k) * (b + 256 * q) + r -> z < 2 ^ 64 -> le_byte z 8 k = b).
{ clear. intros z q b k r Hk Hb Hq Hr Hz Hz64. unfold le_byte. rewrite Z.shiftr_div_pow2 by zlia.
rewrite (Z.mod_small z) by (change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64); zlia).
rewrite <- (Z.div_unique z (2 ^ (8 * Z.of_nat k)) (b + 256 * q) r ltac:(left; exact Hr) Hz).
symmetry. apply (Z.mod_unique _ 256 q b); zlia. }
match goal with |- val_mem _ _ _ _ ?w => set (WW := w) end.
assert (GOAL : forall (bk : byte) kk, mbyte tfibsegs (mrestrict (w_H W) mem0) (a + Z.of_nat kk) = Some bk -> YG0f.le_byte WW 8 kk = bv_unsigned bk ->
mbyte tfibsegs (mrestrict (w_H W) mem0) (a + Z.of_nat kk) = Some (Z_to_bv 8 (YO0f.le_byte WW 8 kk))).
{ intros bk kk Hm Hl. rewrite Hm, <- le_byte_eq, Hl, Z_to_bv_bv_unsigned. reflexivity. }
intros k Hk.
destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; [..|zlia];
[ apply (GOAL b0 0%nat B0) | apply (GOAL b1 1%nat B1) | apply (GOAL b2 2%nat B2) | apply (GOAL b3 3%nat B3)
| apply (GOAL b4 4%nat B4) | apply (GOAL b5 5%nat B5) | apply (GOAL b6 6%nat B6) | apply (GOAL b7 7%nat B7) ]; subst WW.
- apply (LB _ ((bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7))))))) _ 0%nat (0)); [zlia | zlia | zlia | change (2 ^ (8 * Z.of_nat 0)) with 1; zlia | change (2 ^ (8 * Z.of_nat 0)) with 1; zlia | zlia].
- apply (LB _ ((bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7)))))) _ 1%nat (bv_unsigned b0)); [zlia | zlia | zlia | change (2 ^ (8 * Z.of_nat 1)) with 256; zlia | change (2 ^ (8 * Z.of_nat 1)) with 256; zlia | zlia].
- apply (LB _ ((bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7))))) _ 2%nat ((bv_unsigned b0 + 256 * bv_unsigned b1))); [zlia | zlia | zlia | change (2 ^ (8 * Z.of_nat 2)) with 65536; zlia | change (2 ^ (8 * Z.of_nat 2)) with 65536; zlia | zlia].
- apply (LB _ ((bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7)))) _ 3%nat ((bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * bv_unsigned b2)))); [zlia | zlia | zlia | change (2 ^ (8 * Z.of_nat 3)) with 16777216; zlia | change (2 ^ (8 * Z.of_nat 3)) with 16777216; zlia | zlia].
- apply (LB _ ((bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7))) _ 4%nat ((bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * bv_unsigned b3))))); [zlia | zlia | zlia | change (2 ^ (8 * Z.of_nat 4)) with 4294967296; zlia | change (2 ^ (8 * Z.of_nat 4)) with 4294967296; zlia | zlia].
- apply (LB _ ((bv_unsigned b6 + 256 * bv_unsigned b7)) _ 5%nat ((bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * bv_unsigned b4)))))); [zlia | zlia | zlia | change (2 ^ (8 * Z.of_nat 5)) with 1099511627776; zlia | change (2 ^ (8 * Z.of_nat 5)) with 1099511627776; zlia | zlia].
- apply (LB _ (bv_unsigned b7) _ 6%nat ((bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * bv_unsigned b5))))))); [zlia | zlia | zlia | change (2 ^ (8 * Z.of_nat 6)) with 281474976710656; zlia | change (2 ^ (8 * Z.of_nat 6)) with 281474976710656; zlia | zlia].
- apply (LB _ (0) _ 7%nat ((bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * bv_unsigned b6)))))))); [zlia | zlia | zlia | change (2 ^ (8 * Z.of_nat 7)) with 72057594037927936; zlia | change (2 ^ (8 * Z.of_nat 7)) with 72057594037927936; zlia | zlia].
Qed.
Lemma junk_byte : forall a, Kv <= a < Kv + RZ + R8v -> exists b, 0 <= b <= 255 /\ val_mem tfibsegs (mrestrict (w_H W) mem0) a 1 b.
Proof. clean2.
intros a Ha. destruct (KPRES a Ha) as [Hh [b Hb]]. exists (bv_unsigned b).
pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R. split; [zlia|].
intros k Hk. destruct k; [|zlia]. rewrite Z.add_0_r. unfold mbyte, mrestrict. rewrite Hh, Hb. f_equal.
rewrite <- le_byte_eq. unfold YG0f.le_byte. rewrite Z.shiftr_0_r. change (2 ^ (8 * Z.of_nat 1)) with 256.
rewrite (Z.mod_small (bv_unsigned b)) by zlia. rewrite Z.mod_small by zlia. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma junk_values : exists j0' j1' j2' j3' j4' jb',
val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2784) 8 j0' /\ val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2800) 8 j1' /\
val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2808) 8 j2' /\ val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2816) 8 j3' /\
val_mem tfibsegs (mrestrict (w_H W) mem0) SSLOTv 8 j4' /\ 0 <= jb' <= 255 /\ val_mem tfibsegs (mrestrict (w_H W) mem0) (Kv + RZ - 15) 1 jb'.
Proof. clean2.
pose proof cl_range as CR.
destruct (junk_word (T + 2784)) as [x0 Q0]; [unfold t_cache_stats; zlia | unfold t_unwinding; zlia |].
destruct (junk_word (T + 2800)) as [x1 Q1]; [unfold t_cache_stats; zlia | unfold t_unwinding; zlia |].
destruct (junk_word (T + 2808)) as [x2 Q2]; [unfold t_cache_stats; zlia | unfold t_unwinding; zlia |].
destruct (junk_word (T + 2816)) as [x3 Q3]; [unfold t_cache_stats; zlia | unfold t_unwinding; zlia |].
destruct (junk_word SSLOTv) as [x4 Q4]; [unfold SSLOTv, t_stats, t_cache_stats; zlia | unfold SSLOTv, t_stats, t_unwinding; zlia |].
destruct (junk_byte (Kv + RZ - 15)) as (xb & Rb & Hb); [unfold R8v; pose proof (div8_bounds (n + 7)); zlia|].
exists x0, x1, x2, x3, x4, xb. repeat split; try assumption; zlia.
Qed.
Let m0 := mrestrict (w_H W) mem0.
Lemma cell_sym : forall e (w : nat) e', cell_lookup (Tfib_const ly) e = Some (ACell e w (AV e')) -> val_mem tfibsegs m0 (aeval B ly e) w (aeval B ly e').
Proof. clean2. intros e w e' E. exact (tfib_const_lookup_sym B TS ly S (w_H W) mem0 e w e' HARm E). Qed.
Lemma cell_lit : forall a (w : nat) x, cell_lookup (Tfib_const ly) (ANum a) = Some (ACell (ANum a) w (AV (ANum x))) -> val_mem tfibsegs m0 a w x.
Proof. clean2. intros a w x E. exact (tfib_const_lookup B TS ly S (w_H W) mem0 a w x HARm E). Qed.
Lemma cell_state : forall c e (w : nat) x, In c (acells B ly S) -> c = ACell e w (AV (ANum x)) -> val_mem tfibsegs m0 (aeval B ly e) w x.
Proof. clean2.
intros c e w x Hin ->. apply (cell_holds_val_mem B ly (w_H W) mem0 e w (ANum x)).
exact (proj1 (Forall_forall _ _) (am_cells B ly S rd0 HARm) _ Hin).
Qed.
Lemma In_acells_cache : forall c, In c (cache_cells S cl) -> In c (acells B ly S).
Proof. clean2.
intros c Hc. unfold acells. apply in_or_app. right. apply in_or_app. left. apply in_flat_map. exists cl.
split; [apply In_zseq; pose proof cl_range; zlia | exact Hc].
Qed.
Lemma In_combine_seq_last : forall (l0 : list Z) (x : Z) s, In ((s + length l0)%nat, x) (combine (seq s (length l0 + 1)) (l0 ++ [x])).
Proof. clean2.
induction l0 as [|y l0 IH]; intros x s; cbn.
- left. f_equal. zlia.
- right. replace (s + Datatypes.S (length l0))%nat with (Datatypes.S s + length l0)%nat by zlia. apply IH.
Qed.
Lemma cache_vals : val_mem tfibsegs m0 Pv 4 cnt /\ val_mem tfibsegs m0 (Pv + 8) 8 csz /\ val_mem tfibsegs m0 PVv 4 v.
Proof. clean2.
pose proof off_facts as (O1 & O2 & O3 & O4 & O5 & NI & C1 & C2 & PM).
assert (EP : forall d, aeval B ly (aoff (AT (t_cache + 80 * cl)) d) = Pv + d) by (intros d; cbn; unfold Pv, T; zlia).
assert (EP0 : aeval B ly (AT (t_cache + 80 * cl)) = Pv) by (cbn; unfold Pv, T; zlia).
unfold cache_cells in *.
split; [|split].
- rewrite <- EP0. eapply cell_state; [apply In_acells_cache; unfold cache_cells; rewrite Hinited; left; reflexivity|].
rewrite Hcache, length_app. cbn [length]. unfold z4, c4. f_equal. f_equal. f_equal. zlia.
- rewrite <- (EP 8). eapply cell_state; [apply In_acells_cache; unfold cache_cells; rewrite Hinited; right; right; left; reflexivity|].
rewrite Hcsz_def. reflexivity.
- replace PVv with (aeval B ly (aoff (AT (t_cache + 80 * cl)) (16 + 4 * Z.of_nat (length l)))) by (rewrite EP; unfold PVv; zlia).
eapply cell_state; [apply In_acells_cache; unfold cache_cells; rewrite Hinited; right; right; right|].
+ apply in_map_iff. exists (length l, off). split; [reflexivity|]. rewrite Hcache.
rewrite length_app. cbn [length]. apply (In_combine_seq_last l off 0).
+ cbn [fst snd]. unfold z4, c4. f_equal. f_equal. f_equal. rewrite Hoff_def. rewrite Z.mul_comm, Z.div_mul by zlia. reflexivity.
Qed.
Lemma unwinding_val : val_mem tfibsegs m0 (T + t_unwinding) 1 0.
Proof. clean2.
replace (T + t_unwinding) with (aeval B ly (AT t_unwinding)) by reflexivity.
eapply cell_state; [|reflexivity]. unfold acells. do 8 (apply in_or_app; right). left. reflexivity.
Qed.
Lemma sk_val : val_mem tfibsegs m0 SKv 1 250.
Proof. clean2.
pose proof cls_geom as (K1 & _ & _ & _ & K5 & _). destruct (shadow_present SKv) as [R _]; [pose proof (Z.div_le_mono RZ (class_size cl) 8); zlia|].
intros k Hk. destruct k; [|zlia]. rewrite Z.add_0_r. exact (aview_byte _ _ _ _ R).
Qed.
Lemma val_mem_mod8 : forall m a x, val_mem tfibsegs m a 8 x -> val_mem tfibsegs m a 8 (x mod 2 ^ 64).
Proof. clean2.
intros m a x H k Hk. rewrite (H k Hk). do 2 f_equal. rewrite <- (le_byte_eq x), <- (le_byte_eq (x mod 2 ^ 64)). unfold YG0f.le_byte.
replace (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) by reflexivity. rewrite Z.mod_mod by zlia. reflexivity.
Qed.
Lemma chunk_lit : forall a (nn : BinNums.N) x, val_mem tfibsegs m0 a (N.to_nat nn) x -> 0 <= x < 2 ^ (8 * Z.of_N nn) -> Z.of_N nn <= 8 ->
YP09.chunk_ok tfibsegs E0 m0 0 (YP09.mkChunk a (CVal nn (SLit x))).
Proof. clean2. intros a nn x H Hx Hnn. eapply chunk_ok_val; [reflexivity | exact Hx | exact Hnn | rewrite Z.add_0_l; exact H]. Qed.
Lemma chunk_lit_at : forall base a (nn : BinNums.N) x, val_mem tfibsegs m0 (base + a) (N.to_nat nn) x -> 0 <= x < 2 ^ (8 * Z.of_N nn) -> Z.of_N nn <= 8 ->
YP09.chunk_ok tfibsegs E0 m0 base (YP09.mkChunk a (CVal nn (SLit x))).
Proof. clean2. intros base a nn x H Hx Hnn. eapply chunk_ok_val; [reflexivity | exact Hx | exact Hnn | exact H]. Qed.
Lemma chunk_atom : forall base a (nn : BinNums.N) k d x, ew E0 k = w64 (x - d) -> 0 <= x - d < 2 ^ 64 ->
val_mem tfibsegs m0 (base + a) (N.to_nat nn) x -> 0 <= x < 2 ^ (8 * Z.of_N nn) -> Z.of_N nn <= 8 ->
YP09.chunk_ok tfibsegs E0 m0 base (YP09.mkChunk a (CVal nn (SOff k d))).
Proof. clean2.
intros base a nn k d x Hk Hr H Hx Hnn. eapply chunk_ok_val; [| exact Hx | exact Hnn | exact H].
cbn [sv_denot]. rewrite Hk. unfold w64. rewrite Zbv_add_unsigned. f_equal. zlia.
Qed.
Local Ltac reg_intro := unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
Local Ltac lit_region :=
reg_intro; split; [zlia|]; split; [zlia|]; split; [intros o Ho; zlia|];
repeat (apply Forall_cons; [apply chunk_lit; [apply cell_lit; vm_compute; reflexivity | cbn; zlia | cbn; zlia] |]); apply Forall_nil.
End h.
End f.
