(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/A/AFjg.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_identity's ASan build. *)
(* Modified by Theorem Labs, 2026-11: made from A/AFjg.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Theorem Labs, 2026-11: cut for the usage path at 16 GiB: the pruning removed declarations that this path does not use; some unused declarations can remain. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YK18_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK0s YO0d.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YA0n_w YA0o_w YA0p_w YA0q_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG06 YG07 YG03 YG0f YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YG0n_w YG0d_w YG0s_w YG0q_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A Require Import AB1v AB1q AF0l AF0m.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import AF0x_w AFl0_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A Require Import AB1w AE3d.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import AFhy_w AFi1_w AFj6_w AFi3_w AFhz_w AFi0_w AFi2_w AFjc_w AFjd_w AFje_w AFjb_w AFjf_w AFj3_w AFj4_w AFj5_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Set Printing Depth 50. Set Printing Width 180.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Ltac zlia := first [ lia | ceil; unfold zone3, zone3cases, in_app, app_addr, in_band_rw, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, ASAN_CEIL in *; lia ].
Ltac numconst := ceil; unfold zone3, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize,
t_cache, t_unwinding, t_stats, ASTACK, TFIB_IMG_END, TFIB_IMG_LO, kLowShadowBeg, UNW_STK, BST_SIZE, DEP_STK in *.
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
Section e.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (n : Z) (ch : list (Z * Z * Z)).
Variables (cl cnt v csz j0 jb j1 j2 j3 j4 : Z).
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Local Abbreviation RZ := (@AFj6_w.RZ ).
Local Abbreviation NPv := (@AFj6_w.NPv n).
Local Abbreviation R8v := (@AFj6_w.R8v n).
Local Abbreviation N8D := (@AFj6_w.N8D n).
Local Abbreviation Pv := (@AFj6_w.Pv ly cl).
Local Abbreviation PVv := (@AFj6_w.PVv ly cl cnt).
Local Abbreviation Kv := (@AFj6_w.Kv ly cl v).
Local Abbreviation SHBv := (@AFj6_w.SHBv ).
Local Abbreviation SKv := (@AFj6_w.SKv ly cl v).
Local Abbreviation SSLOTv := (@AFj6_w.SSLOTv ly cl).
Local Abbreviation PBv := (@AFj6_w.PBv ly n cl v).
Local Abbreviation Uv := (@AFj6_w.Uv ly cl v).
Local Abbreviation SUv := (@AFj6_w.SUv ly cl v).
Local Abbreviation FILv := (@AFj6_w.FILv n).
Local Abbreviation NDv := (@AFj6_w.NDv n).
Local Abbreviation tr := (@AFj6_w.tr ly regs0 ch).
Local Abbreviation XW := (@AFj6_w.XW ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation E0 := (@AFj6_w.E0 ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaT := (@AFj6_w.EaT ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaC := (@AFj6_w.EaC ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaSB := (@AFj6_w.EaSB ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaTOP := (@AFj6_w.EaTOP ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation Er := (@AFj6_w.Er ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation E2 := (@AFj6_w.E2 ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation E1 := (@AFj6_w.E1 ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation E8 := (@AFj6_w.E8 ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation E10 := (@AFj6_w.E10 ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation E4 := (@AFj6_w.E4 ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaP := (@AFj6_w.EaP ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaR8 := (@AFj6_w.EaR8 ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaK := (@AFj6_w.EaK ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaSK := (@AFj6_w.EaSK ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaSSLOT := (@AFj6_w.EaSSLOT ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaPB := (@AFj6_w.EaPB ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaPV := (@AFj6_w.EaPV ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaRZ := (@AFj6_w.EaRZ ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaU := (@AFj6_w.EaU ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaSU := (@AFj6_w.EaSU ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaFIL := (@AFj6_w.EaFIL ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaNP := (@AFj6_w.EaNP ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaND := (@AFj6_w.EaND ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation WINT := (@AFj6_w.WINT ly cl).
Local Abbreviation PBW := (@AFj6_w.PBW ly n cl v).
Local Abbreviation WIN := (@AFj6_w.WIN ly regs0 n cl v).
Local Abbreviation win_in_WIN := (@AFj6_w.win_in_WIN ly regs0 n cl v).
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
Local Abbreviation HCdisj := (@AFj6_w.HCdisj _ ly regs0 v Hv LY).
Local Abbreviation DZONE := (@AFj6_w.DZONE ly).
Variable DPOST : Z -> (word -> option byte) -> Prop.
Local Abbreviation HC_NB := (@AFj6_w.HC_NB _ ly LY).
Hypothesis HKpres : forall a, Kv <= a < Kv + RZ + R8v -> apresent (w_H W) mem0 a.
Hypothesis HSKpres : forall a, SKv <= a < SKv + (RZ + R8v) / 8 -> apresent (w_H W) mem0 a.
Hypothesis HPB250 : NPv mod 8 <> 0 -> val_mem tfibsegs (mrestrict (w_H W) mem0) PBv 1 250.
Local Abbreviation HCX := (@AFj6_w.HCX _ ly LY).
Local Abbreviation tr_length := (@AFj6_w.tr_length ly regs0 mem0 n ch v DPOST).
Local Abbreviation Kv_range := (@AFj6_w.Kv_range ly regs0 mem0 n cl v Hcl Hv Hv2 DPOST).
Local Abbreviation high_facts := (@AFj6_w.high_facts _ ly regs0 mem0 n v Hv LY IMG DPOST).
Local Abbreviation blocks_facts := (@AFj6_w.blocks_facts _ ly LY IMG).
Local Abbreviation off_T := (@AFj6_w.off_T _ ly regs0 mem0 n v Hv LY IMG DPOST).
Local Abbreviation off_C := (@AFj6_w.off_C _ ly regs0 mem0 n v Hv LY IMG DPOST).
Local Abbreviation off_NB := (@AFj6_w.off_NB _ ly LY IMG).
Local Abbreviation off_SB := (@AFj6_w.off_SB _ ly LY IMG).
Hypothesis Nrange : 0 <= n <= 48.
Local Abbreviation K0_facts := (@AFj6_w.K0_facts n Nrange).
Local Abbreviation RZ_num := (@AFj6_w.RZ_num n Nrange).
Ltac numconst ::= (ceil; unfold zone3, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize,
t_cache, t_unwinding, t_stats, ASTACK, TFIB_IMG_END, TFIB_IMG_LO, kLowShadowBeg, UNW_STK, BST_SIZE, DEP_STK in * ); try pose proof RZ_num as RZN.
Local Abbreviation derived_ranges := (@AFj6_w.derived_ranges _ ly regs0 mem0 n cl cnt v Hcl Hv Hcnt Hv2 LY IMG DPOST Nrange).
Hypothesis Hcl_def : cl = class_id (R8v + RZ).
Local Abbreviation CLk := (@AFj6_w.CLk ).
Local Abbreviation CLk_E := (@AFj6_w.CLk_E ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 DPOST Nrange Hcl_def).
Local Abbreviation WIN1 := (@AFj6_w.WIN1 ly regs0 n cl v).
Local Abbreviation WIN1_WIN := (@AFj6_w.WIN1_WIN ly regs0 mem0 n cl v DPOST).
Local Abbreviation WIN_odd := (@AFj6_w.WIN_odd ly regs0 mem0 n cl cnt v jb Hcl Hv Hcnt Hjb Hsp DPOST Nrange).
Local Abbreviation WIN1_odd := (@AFj6_w.WIN1_odd ly regs0 mem0 n cl cnt v jb Hcl Hv Hcnt Hjb Hsp DPOST Nrange).
Local Abbreviation WSKEL := (@AFj6_w.WSKEL ).
Local Abbreviation WSKEL1 := (@AFj6_w.WSKEL1 ).
Local Abbreviation win_sub := (@AFj6_w.win_sub ).
Local Abbreviation win_sub_sound := (@AFj6_w.win_sub_sound ly regs0 mem0 n v Hv DPOST).
Local Abbreviation WSKEL_WIN := (@AFj6_w.WSKEL_WIN _ ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 Hcl Hv Hcnt Hv2 LY IMG DPOST Nrange).
Local Abbreviation WSKEL1_WIN1 := (@AFj6_w.WSKEL1_WIN1 _ ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 Hcl Hv Hcnt Hv2 LY IMG DPOST Nrange).
Local Abbreviation windows_WIN := (@AFj6_w.windows_WIN _ ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 Hcl Hv Hcnt Hv2 LY IMG DPOST Nrange).
Local Abbreviation windows_WIN1 := (@AFj6_w.windows_WIN1 _ ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 Hcl Hv Hcnt Hv2 LY IMG DPOST Nrange).
Local Abbreviation frame_WIN1 := (@AFj6_w.frame_WIN1 _ ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 Hcl Hv Hcnt Hv2 LY IMG DPOST Nrange).
Local Abbreviation WIN_not_high := (@AFj6_w.WIN_not_high _ ly regs0 mem0 n cl cnt v Hcl Hv Hcnt Hv2 LY IMG Hsp DPOST Nrange).
Variables (mat0 : list word).
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 0x52bac) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis U1 : tfib_unwind_spec.
Hypothesis SEED : st_ok tfibsegs E0 SS0K (restrict (w_H W) (mkst regs0 (w64 0x52bac) mem0 (seg_rom tfibsegs))).
Local Abbreviation all_disjoint_of_forall := (@AFj6_w.all_disjoint_of_forall ).
Local Abbreviation kept_of_frame := (@AFj6_w.kept_of_frame W ly regs0 mem0 n v DPOST).
Local Abbreviation SKEL_TAIL := (@AFj6_w.SKEL_TAIL ).
Local Abbreviation stack_ivs := (@AFj6_w.stack_ivs _ ly regs0 mem0 n v Hv LY Hsp DPOST).
Local Abbreviation stack_ivs2 := (@AFj6_w.stack_ivs2 _ ly regs0 mem0 n v Hv LY Hsp DPOST).
Local Abbreviation DZONE_disj := (@AFj6_w.DZONE_disj _ ly regs0 mem0 n cl cnt v Hcl Hv Hcnt Hv2 LY IMG Hsp DPOST Nrange).
Local Abbreviation RFACTS := (@AFj6_w.RFACTS ly regs0 n cl v).
Local Abbreviation zone_lit := (@AFj6_w.zone_lit _ ly regs0 mem0 n cl cnt v Hcl Hv Hcnt Hv2 LY IMG Hsp DPOST Nrange).
Local Abbreviation zone_T := (@AFj6_w.zone_T _ ly regs0 mem0 n cl cnt v Hcl Hv Hcnt Hv2 LY IMG Hsp DPOST Nrange).
Local Abbreviation zone_C := (@AFj6_w.zone_C _ ly regs0 mem0 n cl cnt v Hcl Hv Hcnt Hv2 LY IMG Hsp DPOST Nrange).
Local Abbreviation zone_K := (@AFj6_w.zone_K _ ly regs0 mem0 n cl cnt v Hcl Hv Hcnt Hv2 LY IMG Hsp DPOST Nrange).
Local Abbreviation zone_SH := (@AFj6_w.zone_SH _ ly regs0 mem0 n cl cnt v Hcl Hv Hcnt Hv2 LY IMG Hsp DPOST Nrange).
Local Abbreviation tail_ext_ok := (@AFj6_w.tail_ext_ok _ ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 Hcl Hv Hcnt Hv2 LY IMG Hsp DPOST Nrange).
Local Abbreviation at_ST := (@AFj6_w.at_ST _ W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation at_ST2 := (@AFj6_w.at_ST2 _ W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 DPOST).
Local Abbreviation at_S2 := (@AFj6_w.at_S2 _ W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 DPOST).
Local Abbreviation at_RET := (@AFj6_w.at_RET _ W ly regs0 mem0 md0 n cl cnt v jb DPOST).
Local Abbreviation memset_stretch := (@AFj6_w.memset_stretch _ W ly regs0 mem0 n cl cnt v jb Hcl Hv Hcnt Hjb Hsp DPOST Nrange).
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
Local Abbreviation case0_sizes := (@AFj6_w.case0_sizes n Nrange).
Local Abbreviation Kv_is_sptr := (@AFj6_w.Kv_is_sptr ly cl v Hcl B off Hoff_def).
Local Abbreviation cl_range := (@AFjc_w.cl_range ly regs0 mem0 n cl v DPOST Nrange l off Hcl_class).
Local Abbreviation cls_geom := (@AFjc_w.cls_geom ly regs0 mem0 n cl v DPOST Nrange l off Hcl_class).
Local Abbreviation cls_wf := (@AFjc_w.cls_wf _ W ly regs0 mem0 n cl v DPOST Nrange B S l off HARm Hcl_class).
Local Abbreviation off_facts := (@AFjc_w.off_facts _ W ly regs0 mem0 n cl cnt v Hv2 DPOST Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation Kv_base := (@AFjc_w.Kv_base ly regs0 mem0 n cl v DPOST Nrange l off Hcl_class Hoff_def).
Local Abbreviation Kv_geom := (@AFjc_w.Kv_geom _ W ly regs0 mem0 n cl cnt v csz Hv2 LY DPOST Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def).
Local Abbreviation Hcl' := (@AFjc_w.Hcl' ly regs0 mem0 n cl v DPOST Nrange l off Hcl_class).
Local Abbreviation cl_k0 := (@AFjc_w.cl_k0 ly regs0 mem0 n cl v DPOST Nrange Hcl_def l off).
Local Abbreviation Hcnt' := (@AFjc_w.Hcnt' _ W ly regs0 mem0 n cl cnt v Hv2 Hsp DPOST Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation Hv' := (@AFjc_w.Hv' _ W ly regs0 mem0 n cl cnt v Hv2 DPOST Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation cached_vs_chunk := (@AFjc_w.cached_vs_chunk _ W ly regs0 mem0 n cl cnt v csz Hv2 LY Hsp DPOST Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def).
Local Abbreviation find_chunk_at_none := (@AFjc_w.find_chunk_at_none _ W ly regs0 mem0 n cl cnt v Hv2 Hsp DPOST Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation shadow250 := (@AFjc_w.shadow250 _ W ly regs0 mem0 n cl cnt v csz Hv2 LY Hsp DPOST Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def).
Local Abbreviation shadow_present := (@AFjc_w.shadow_present _ W ly regs0 mem0 n cl cnt v csz Hv2 LY IMG Hsp DPOST Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def).
Local Abbreviation vis_present := (@AFjc_w.vis_present _ W ly regs0 mem0 n cl cnt v Hv2 Hsp DPOST Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation KPRES := (@AFjc_w.KPRES _ W ly regs0 mem0 n cl cnt v csz Hv2 LY Hsp DPOST Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def).
Local Abbreviation SKPRES := (@AFjc_w.SKPRES _ W ly regs0 mem0 n cl cnt v csz Hv2 LY IMG Hsp DPOST Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def).
Local Abbreviation PB250 := (@AFjc_w.PB250 _ W ly regs0 mem0 n cl cnt v csz Hv2 LY IMG Hsp DPOST Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def).
Local Abbreviation in_thread_junk := (@AFjc_w.in_thread_junk _ W ly regs0 mem0 n cl cnt v Hv2 Hsp DPOST Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation junk_word := (@AFjc_w.junk_word _ W ly regs0 mem0 n cl cnt v Hv2 LY IMG Hsp DPOST Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation junk_byte := (@AFjc_w.junk_byte _ W ly regs0 mem0 n cl cnt v csz Hv2 LY Hsp DPOST Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def).
Local Abbreviation junk_values := (@AFjc_w.junk_values _ W ly regs0 mem0 n cl cnt v csz Hv2 LY IMG Hsp DPOST Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def).
Local Abbreviation cell_sym := (@AFjc_w.cell_sym _ W ly regs0 mem0 n cl cnt v Hv2 Hsp DPOST Nrange B S l off TS HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation cell_lit := (@AFjc_w.cell_lit _ W ly regs0 mem0 n cl cnt v Hv2 Hsp DPOST Nrange B S l off TS HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation cell_state := (@AFjc_w.cell_state _ W ly regs0 mem0 n cl cnt v Hv2 Hsp DPOST Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation In_acells_cache := (@AFjc_w.In_acells_cache _ W ly regs0 mem0 n cl cnt v Hv2 Hsp DPOST Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation In_combine_seq_last := (@AFjc_w.In_combine_seq_last _ W ly regs0 mem0 n cl cnt v Hv2 Hsp DPOST Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation cache_vals := (@AFjc_w.cache_vals _ W ly regs0 mem0 n cl cnt v csz Hv2 Hsp DPOST Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def).
Local Abbreviation unwinding_val := (@AFjc_w.unwinding_val _ W ly regs0 mem0 n cl cnt v Hv2 Hsp DPOST Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation sk_val := (@AFjc_w.sk_val _ W ly regs0 mem0 n cl cnt v csz Hv2 LY IMG Hsp DPOST Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def).
Local Abbreviation val_mem_mod8 := (@AFjc_w.val_mem_mod8 _ W ly regs0 mem0 n cl cnt v Hv2 Hsp DPOST Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation chunk_lit := (@AFjc_w.chunk_lit _ W ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 Hv2 Hsp DPOST Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation chunk_lit_at := (@AFjc_w.chunk_lit_at _ W ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 Hv2 Hsp DPOST Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation chunk_atom := (@AFjc_w.chunk_atom _ W ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 Hv2 Hsp DPOST Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation REG0_ok := (@AFjd_w.REG0_ok _ W ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 Hcl Hv Hcnt Hjb Hv2 LY IMG Hsp DPOST Nrange B S l off TS HTSD HARm Hpres0 Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def Hj0 Hj1 Hj2 Hj3 Hj4 Hjb_def).
Local Abbreviation Kv32 := (@AFje_w.Kv32 _ W ly regs0 mem0 n cl v Hv2 LY DPOST l off).
Local Abbreviation PAIRS_ok := (@AFje_w.PAIRS_ok _ W ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 Hcl Hv Hcnt Hv2 LY IMG Hsp DPOST Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def).
Local Abbreviation FACTS_ok := (@AFje_w.FACTS_ok _ W ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 Hcl Hv Hcnt Hjb Hv2 LY IMG Hn Hsp DPOST Nrange Hcl_def B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def).
Local Abbreviation SEED_ok := (@AFje_w.SEED_ok _ _ W ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 Hcl Hv Hcnt Hjb Hv2 LY IMG Hn Htp Hsp DPOST Nrange Hcl_def B S l off TS HTSD HARm Hpres0 Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def Hj0 Hj1 Hj2 Hj3 Hj4 Hjb_def).
Local Abbreviation CZONE := (@AFjb_w.CZONE ly).
Local Abbreviation abs_cell_ok := (@AFjb_w.abs_cell_ok ).
Local Abbreviation abs_cells_ok := (@AFjb_w.abs_cells_ok ).
Local Abbreviation const_cells_zone := (@AFjb_w.const_cells_zone ly regs0 mem0 n v Hv DPOST B l off TS HTSD).
Local Abbreviation CZONE_untouched := (@AFjb_w.CZONE_untouched _ ly regs0 mem0 n cl cnt v Hcl Hv Hcnt Hv2 LY IMG Hsp DPOST Nrange l off).
Local Abbreviation cell_holds_agree := (@AFjb_w.cell_holds_agree ly regs0 mem0 n v Hv DPOST B l off).
Local Abbreviation aview_agree := (@AFjb_w.aview_agree W).
Local Abbreviation const_kept := (@AFjb_w.const_kept _ W ly regs0 mem0 n cl cnt v Hcl Hv Hcnt Hv2 LY IMG Hsp DPOST Nrange B l off TS HTSD).
Local Abbreviation depot_ids_bound := (@AFjb_w.depot_ids_bound ly regs0 mem0 n v Hv DPOST B l off TS).
Local Abbreviation depot_mem_ok_agree := (@AFjb_w.depot_mem_ok_agree ly regs0 mem0 n v Hv DPOST B l off TS).
Local Abbreviation depot_ok_ext := (@AFjb_w.depot_ok_ext ly B).
Local Abbreviation depot_at0 := (@AFjb_w.depot_at0 _ W ly regs0 mem0 n cl cnt v jb Hcl Hv Hcnt Hjb Hsp DPOST Nrange B S HARm).
Local Abbreviation DPOST3 := (@AFjb_w.DPOST3 W ly regs0 ch B S).
Local Abbreviation D1W_ok := (@AFjb_w.D1W_ok _ _ W ly regs0 mem0 n ch cl cnt v jb Hcl Hv Hcnt Hjb Hv2 LY IMG Hsp DPOST Nrange B S l off TS HTSD HARm Hgp).
Local Abbreviation st_popped := (@AFjb_w.st_popped ).
Local Abbreviation new_chunk := (@AFjb_w.new_chunk ).
Local Abbreviation st_final := (@AFjb_w.st_final ).
Local Abbreviation Kc_user := (@AFjb_w.Kc_user ly regs0 mem0 n ch cl v Hcl DPOST Nrange B S l off Hoff_def).
Local Abbreviation MPF := (@AFjb_w.MPF ly regs0 n ch cl B S l off).
Local Abbreviation AR_final_stmt := (@AFjb_w.AR_final_stmt _ _ W ly regs0 mem0 md0 n ch cl cnt v jb DPOST B S l off).
Local Abbreviation WR_owned := (@AFjb_w.WR_owned _ W ly regs0 mem0 n ch cl cnt v csz jb Hcl Hv Hcnt Hjb Hv2 LY IMG Hsp DPOST HPB250 Nrange B S l off TS HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def).
Local Abbreviation LEAF_ok := (@AFjb_w.LEAF_ok _ _ W ly regs0 mem0 md0 n ch cl cnt v csz jb Hcl Hv Hcnt Hjb Hv2 LY IMG Hsp DPOST HPB250 Nrange mat0 B S l off TS HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def).
Local Abbreviation Kc_fresh := (@AFjb_w.Kc_fresh _ W ly regs0 mem0 n ch cl cnt v Hcl Hv Hv2 DPOST Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation upd_chunk_fresh := (@AFjb_w.upd_chunk_fresh n cl off).
Local Abbreviation SF_chunks := (@AFjb_w.SF_chunks _ W ly regs0 mem0 n ch cl cnt v Hcl Hv Hv2 DPOST Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation SF_same := (@AFjb_w.SF_same ly regs0 n ch cl S l off).
Local Abbreviation SF_sec_extents := (@AFjb_w.SF_sec_extents _ W ly regs0 mem0 n ch cl cnt v Hcl Hv Hv2 DPOST Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation SF_sec_live := (@AFjb_w.SF_sec_live _ W ly regs0 mem0 n ch cl cnt v Hcl Hv Hv2 DPOST Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation SF_ledger := (@AFjb_w.SF_ledger _ W ly regs0 mem0 n ch cl cnt v Hcl Hv Hv2 DPOST Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation cell_holds_agree2 := (@AFjb_w.cell_holds_agree2 ly regs0 mem0 n ch cl cnt v jb Hcl Hv Hcnt Hjb Hsp DPOST Nrange B S l off).
Local Abbreviation zrange_dec := (@AFjf_w.zrange_dec ).
Local Abbreviation apresent_word := (@AFjf_w.apresent_word ).
Local Abbreviation val_mem_cell := (@AFjf_w.val_mem_cell W ly regs0 mem0 n ch cl v DPOST B S l off).
Local Abbreviation le_byte_1_0 := (@AFjf_w.le_byte_1_0 ly regs0 mem0 n ch cl v DPOST S l off).
Local Abbreviation find_chunk_at_app1 := (@AFjf_w.find_chunk_at_app1 ly B).
Local Abbreviation find_chunk_at_app2 := (@AFjf_w.find_chunk_at_app2 ly B).
Local Abbreviation In_combine_seq_app := (@AFjf_w.In_combine_seq_app ).
Local Abbreviation Kc_facts := (@AFjf_w.Kc_facts ly n cl v Hcl Nrange B off Hcl_class Hoff_def).
Local Abbreviation NLOf := (@AFjf_w.NLOf n Nrange).
Local Abbreviation AR_final := (@AFjf_w.AR_final _ _ W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 Hcl Hv Hcnt Hjb Hv2 LY IMG Hsp DPOST HKpres HSKpres HPB250 Nrange Hcl_def SEED B S l off TS HTSD HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def Hj4 Hjb_def).
Local Abbreviation LEAF_final := (@AFjf_w.LEAF_final _ _ W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 Hcl Hv Hcnt Hjb Hv2 LY IMG Hsp DPOST HKpres HSKpres HPB250 Nrange Hcl_def mat0 SEED B S l off TS HTSD HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def Hj4 Hjb_def).
Local Open Scope am_scope.
Let rd0 : reader := aview tfibsegs (w_H W) mem0.
Let WF := am_wf B ly S rd0 HARm.
Let c0 : config := cfg_at tfibsegs 0x52bac regs0 mem0 md0.
Hypothesis Htr : In tr (as_universe B).
Hypothesis HAR : AR tfibsegs B ly S W mem0 md0.
Hypothesis HD1 : tfib_depot_spec B.
Hypothesis HDPOST : forall z m, DPOST z m -> DPOST3 z m.
Hypothesis HDPOST' : forall z m, DPOST3 z m -> DPOST z m.
Hypothesis Hmat0 : mat0 = m_vm_materialized md0.
Lemma D1w : forall (regs : bvmap 5 word) (mem : word -> option byte) (md : Model),
getr regs 10 = Z_to_bv 64 (sp0 - IFRAME + 16) -> getr regs 11 = Z_to_bv 64 (Z.of_nat (length tr)) ->
getr regs 3 = getr regs0 3 -> getr regs 4 = Z_to_bv 64 TFIB_TP -> getr regs 1 = Z_to_bv 64 0x31fa8 ->
bv_unsigned (getr regs 2) = sp0 - 2272 ->
(forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W) mem) (sp0 - IFRAME + 16 + 8 * Z.of_nat i) 8 (nth i tr 0)) ->
(forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem a) ->
(forall x : word, ~ WIN false (bv_unsigned x) -> mem x = mem0 x) ->
SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 A_StackDepotPut) mem (seg_rom tfibsegs)) md)
(fun W' c' => W' = W /\ exists z regs' mem' mat,
c' = mkCfg (mkst regs' (Z_to_bv 64 0x31fa8) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md) /\
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
Local Abbreviation seg1J := (@AFj3_w.seg1J _ _ W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 Hcl Hv Hcnt Hjb Hv2 LY IMG Hn Hra4096 Hsp Hch DPOST Nrange Hcl_def mat0 U1 SEED l off).
Local Abbreviation segC2 := (@AFj3_w.segC2 _ _ W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 Hcl Hv Hcnt Hv2 LY IMG Hn Hsp DPOST Nrange l off).
Local Abbreviation segD := (@AFj4_w.segD _ _ W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 LY Hsp DPOST l off D1w).
Local Abbreviation seg2aK := (@AFj4_w.seg2aK _ _ W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 Hcl Hv Hcnt Hjb Hv2 LY IMG Hsp DPOST HSKpres Nrange l off).
Local Abbreviation seg2b_even := (@AFj4_w.seg2b_even _ _ W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 Hcl Hv Hcnt Hv2 LY IMG Hsp DPOST Nrange Hcl_def l off).
Local Abbreviation seg2c_even := (@AFj4_w.seg2c_even _ _ W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 Hcl Hv Hcnt Hjb Hv2 LY IMG Htp Hra Hsp DPOST HKpres Nrange l off).
Local Abbreviation seg2b_odd := (@AFj5_w.seg2b_odd _ _ W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 Hcl Hv Hcnt Hjb Hv2 LY IMG Hsp DPOST HSKpres HPB250 Nrange Hcl_def l off).
Local Abbreviation seg2c_odd := (@AFj5_w.seg2c_odd _ _ W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 Hcl Hv Hcnt Hjb Hv2 LY IMG Htp Hra Hsp DPOST HKpres HPB250 Nrange l off).
Theorem tail_inner : forall c1, at_ST KS_JN W c1 ->
amreal tfibsegs (malloc_join n tr cl S) W c1
(fun r W' c' => Wf (as_universe B) (snd r) /\ qtight (snd r) -> malloc_leaf tfibsegs B ly S W regs0 mem0 md0 n r W' c').
Proof.
intros c1 HJ.
pose proof case0_sizes as (L & RS & R8 & NP & FP & NS & RQ). pose proof K0_facts as (_ & RF4 & NPr & _).
unfold malloc_join. rewrite bind_assoc_eq. eapply amreal_pure; [exact (pop_hit S cl l off Hcache)|]. eapply amreal_pure; [reflexivity|].
unfold malloc_K. cbv beta iota. change (AFi3_w.st_popped S cl l) with (st_popped S cl l).
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
