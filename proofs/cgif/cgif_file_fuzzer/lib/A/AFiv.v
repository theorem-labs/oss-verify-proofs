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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1w AE3d AFhy AFis AFhz AFi4.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Set Printing Depth 50. Set Printing Width 180.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
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
Definition WINN (a : Z) : Prop :=
(sp0 - ASTACK <= a < sp0 - IFRAME) \/ (sp0 - 64 <= a < sp0) \/ (TFIB_OOM <= a < TFIB_OOM + 1) \/ (TFIB_ERRNO <= a < TFIB_ERRNO + 4).
Definition WSKELN : list (option nat * Z * Z) :=
[(Some 2%nat, - ASTACK, - IFRAME); (Some 2%nat, -64, 0); (None, TFIB_OOM, TFIB_OOM + 1); (None, TFIB_ERRNO, TFIB_ERRNO + 4)].
Lemma WSKELN_WINN : forall (E : env) a t,
(forall k, (k < aHAV)%nat -> ew E k = ew E0 k) -> In t WSKELN ->
base_val E (fst (fst t)) + snd (fst t) <= a < base_val E (fst (fst t)) + snd t -> WINN a.
Proof.
intros E a t HE Hin Hr. unfold WSKELN in Hin. cbn [In] in Hin. unfold WINN. unfold aHAV, IFRAME, ASTACK in *.
repeat match type of Hin with _ \/ _ => destruct Hin as [<-|Hin] | False => destruct Hin end;
cbn [fst snd base_val] in Hr; rewrite ?HE in Hr by zlia; rewrite ?E2 in Hr; unfold sp0 in *; zlia.
Qed.
Lemma windows_WINN : forall (E : env) rs a,
(forall k, (k < aHAV)%nat -> ew E k = ew E0 k) ->
forallb (fun t => existsb (win_sub t) WSKELN || (snd t <=? snd (fst t))) (windows rs) = true ->
in_wrange E rs a -> WINN a.
Proof.
intros E rs a HE Hb Hw. destruct (in_wrange_windows E rs a Hw) as (b & lo & hi & Hin & Hr).
pose proof (proj1 (forallb_forall _ _) Hb _ Hin) as Ht. cbn beta in Ht. apply Bool.orb_prop in Ht as [Ht|Ht].
- apply existsb_exists in Ht as (u & Hinu & Hsub). exact (WSKELN_WINN E a u HE Hinu (win_sub_sound E a _ u Hsub Hr)).
- cbn [fst snd] in Ht. apply Z.leb_le in Ht. zlia.
Qed.
Definition at_STN (ss : sstate) (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ exists ms mat (E' : env),
c' = mkCfg ms (with_vm_backing (m_vm_lazy md0) mat md0) /\
(forall k, (k < aHAV)%nat -> ew E' k = ew E0 k) /\
st_ok tfibsegs E' ss (restrict (w_H W) ms) /\
ms_mem ms = mem0 /\
(forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) (ms_mem ms) a).
Definition at_RETN (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat md0) /\
getr regs' 10 = Z_to_bv 64 0 /\
(forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs0 r) /\
(forall x : word, ~ WINN (bv_unsigned x) -> mem' x = mem0 x) /\
(forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem' a) /\
val_mem tfibsegs (mrestrict (w_H W) mem') TFIB_OOM 1 1 /\ val_mem tfibsegs (mrestrict (w_H W) mem') TFIB_ERRNO 4 12.
Lemma segN : forall W0 c, at_STN MS_N0 W0 c -> SRr tfibsegs W0 c at_RETN.
Proof.
intros W0 c (-> & ms & mat & En & -> & HEn & HS & MEM0 & PRESW). pose proof Hwx_tfa as Hwx.
pose proof Hsp as (Hlo & Hbot & Hhi & Hal). pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
assert (Usp : 0 <= bv_unsigned (getr regs0 2) < 2 ^ 64) by apply u64_range.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) En _ _ HS eq_refl) as Hshape; cbn [ss_pc] in Hshape;
lazymatch type of Hshape with _ = mkst _ (Z_to_bv 64 (ss_pc ?s)) _ _ => let p := eval vm_compute in (ss_pc s) in change (ss_pc s) with p in Hshape | _ => idtac end.
rewrite Hshape in HS. rewrite Hshape. cbn [ms_mem] in MEM0, PRESW. set (mem1 := ms_mem ms) in *.
srr_run_to_sh tfibtbl_rtA_ok HS 0x52c5c.
match type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msZ end.
lazymatch type of HF with frame_of ?E ?rs ?ma ?mb =>
assert (MEQ : forall x : word, ~ WINN (bv_unsigned x) -> mb x = ma x)
by (intros x Hx; apply HF; intros Hw; apply Hx; exact (windows_WINN E rs (bv_unsigned x) HEn ltac:(vm_compute; reflexivity) Hw))
end. clear HF HFr.
eapply (SRr_ret_at tfibsegs tfibtbl_rtA tfibtbl_rtA_ok Hwx W En); [exact HS | reflexivity | vm_compute; reflexivity |].
intros matZ.
rreg HS (1%bv : bv 5) RZ1. rewrite (HEn 1%nat (ltHAV 1 eq_refl)), E1 in RZ1. rewrite RZ1. unfold YK0s.ret_ok in Hra. rewrite Hra.
split; [reflexivity|]. exists (ms_regs msZ), (ms_mem msZ), matZ. split; [reflexivity|].
split. { rreg HS (10%bv : bv 5) R. exact R. }
split. { intros r Hr. cbn [In] in Hr.
repeat match type of Hr with _ \/ _ => destruct Hr as [<-|Hr] | False => destruct Hr end;
lazymatch goal with |- getr _ ?r = _ =>
let R := fresh "R" in rreg HS r R; rewrite R;
first [ let k := eval cbv in (Z.to_nat (bv_unsigned r)) in rewrite (HEn k (ltHAV k eq_refl)); exact (Er k r eq_refl)
| symmetry; exact Htp ] end. }
split. { intros x Hx. rewrite (MEQ x Hx). subst mem1. rewrite MEM0. reflexivity. }
split. { pose proof high_facts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
intros a Ha. assert (Ha' : TFIB_IMG_END <= a < 2 ^ 64) by (clear - Ha Hlo T7 Usp; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END, ASTACK, kHighMemBeg in *; unfold sp0 in *; zlia).
destruct (Z_lt_le_dec a (sp0 - IFRAME)) as [Hlo'|Hge].
- eapply (st_ok_window_apresent_off (w_H W) En _ _ 1 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn 2%nat (ltHAV 2 eq_refl)), E2; clear - Ha Hlo'; unfold IFRAME, ASTACK in *; unfold sp0 in *; zlia | off_by ltac:(exact Ha') ].
- destruct (Z_lt_le_dec a (sp0 - 64)) as [Hmid|Htop'].
+ apply (apresent_same (w_H W) mem1); [| apply PRESW; exact Ha]. apply MEQ. rewrite unsigned_lit_small by (clear - Ha'; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END in *; zlia).
clear - Hge Hmid Ha'. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, WINN, IFRAME, TFIB_OOM, TFIB_ERRNO, TFIB_IMG_END in *. zlia.
+ eapply (st_ok_window_apresent_off (w_H W) En _ _ 2 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn 2%nat (ltHAV 2 eq_refl)), E2; clear - Ha Htop'; unfold sp0 in *; zlia | off_by ltac:(exact Ha') ]. }
split. { memv HS 4%nat 0%nat; [reflexivity | reflexivity | zlia]. }
memv HS 5%nat 0%nat; [reflexivity | reflexivity | zlia].
Qed.
End e.
End d.
