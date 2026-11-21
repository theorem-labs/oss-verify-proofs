(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/A/AFj2.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_identity's ASan build. *)
(* Modified by Theorem Labs, 2026-11: made from A/AFj2.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import AFhy_w AFis_w AFhz_w AFi3_w AFiy_w AFiz_w AFj0_w AFix_w AFj1_w AFip_w AFiq_w AFir_w.
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
Variable kz : Z.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Local Abbreviation RZ := (@AFis_w.RZ kz).
Local Abbreviation R8v := (@AFis_w.R8v n).
Local Abbreviation N8D := (@AFis_w.N8D n).
Local Abbreviation Pv := (@AFis_w.Pv ly cl).
Local Abbreviation PVv := (@AFis_w.PVv ly cl cnt).
Local Abbreviation Kv := (@AFis_w.Kv ly cl v).
Local Abbreviation SHBv := (@AFis_w.SHBv ).
Local Abbreviation SKv := (@AFis_w.SKv ly cl v).
Local Abbreviation SSLOTv := (@AFis_w.SSLOTv ly cl).
Local Abbreviation PBv := (@AFis_w.PBv ly n cl v kz).
Local Abbreviation Uv := (@AFis_w.Uv ly cl v kz).
Local Abbreviation SUv := (@AFis_w.SUv ly cl v kz).
Local Abbreviation FILv := (@AFis_w.FILv n).
Local Abbreviation NDv := (@AFis_w.NDv n kz).
Local Abbreviation tr := (@AFis_w.tr ly regs0 ch).
Local Abbreviation XW := (@AFis_w.XW ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation E0 := (@AFis_w.E0 ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaT := (@AFis_w.EaT ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaC := (@AFis_w.EaC ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaSB := (@AFis_w.EaSB ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaTOP := (@AFis_w.EaTOP ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation Er := (@AFis_w.Er ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation E2 := (@AFis_w.E2 ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation E1 := (@AFis_w.E1 ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation E8 := (@AFis_w.E8 ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation E10 := (@AFis_w.E10 ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation E4 := (@AFis_w.E4 ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaP := (@AFis_w.EaP ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaK := (@AFis_w.EaK ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaSK := (@AFis_w.EaSK ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaSSLOT := (@AFis_w.EaSSLOT ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaPB := (@AFis_w.EaPB ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaPV := (@AFis_w.EaPV ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaKL := (@AFis_w.EaKL ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaRZ := (@AFis_w.EaRZ ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaU := (@AFis_w.EaU ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaSU := (@AFis_w.EaSU ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaFIL := (@AFis_w.EaFIL ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaND := (@AFis_w.EaND ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation WINT := (@AFis_w.WINT ly cl).
Local Abbreviation PBW := (@AFis_w.PBW ly n cl v kz).
Local Abbreviation WIN := (@AFis_w.WIN ly regs0 n cl v kz).
Local Abbreviation win_in_WIN := (@AFis_w.win_in_WIN ly regs0 n cl v kz).
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
Local Abbreviation HCdisj := (@AFis_w.HCdisj _ ly regs0 v Hv LY).
Local Abbreviation DZONE := (@AFis_w.DZONE ly).
Variable DPOST : Z -> (word -> option byte) -> Prop.
Local Abbreviation HC_NB := (@AFis_w.HC_NB _ ly LY).
Hypothesis HKpres : forall a, Kv <= a < Kv + RZ + R8v -> apresent (w_H W) mem0 a.
Hypothesis HSKpres : forall a, SKv <= a < SKv + (RZ + R8v) / 8 -> apresent (w_H W) mem0 a.
Hypothesis HPB250 : n mod 8 <> 0 -> val_mem tfibsegs (mrestrict (w_H W) mem0) PBv 1 250.
Local Abbreviation HCX := (@AFis_w.HCX _ ly LY).
Local Abbreviation tr_length := (@AFis_w.tr_length ly regs0 mem0 n ch v kz DPOST).
Local Abbreviation Kv_range := (@AFis_w.Kv_range ly regs0 mem0 n cl v kz Hcl Hv Hv2 DPOST).
Local Abbreviation high_facts := (@AFis_w.high_facts _ ly regs0 mem0 n v kz Hv LY IMG DPOST).
Local Abbreviation blocks_facts := (@AFis_w.blocks_facts _ ly LY IMG).
Local Abbreviation off_T := (@AFis_w.off_T _ ly regs0 mem0 n v kz Hv LY IMG DPOST).
Local Abbreviation off_C := (@AFis_w.off_C _ ly regs0 mem0 n v kz Hv LY IMG DPOST).
Local Abbreviation off_NB := (@AFis_w.off_NB _ ly LY IMG).
Local Abbreviation off_SB := (@AFis_w.off_SB _ ly LY IMG).
Hypothesis Hkz : 1 <= kz <= 6.
Hypothesis Nrange : rz_lo kz <= n <= rz_hi kz.
Local Abbreviation kz_cases := (@AFis_w.kz_cases kz Hkz).
Local Abbreviation RZ_facts := (@AFis_w.RZ_facts n kz Hkz Nrange).
Local Abbreviation RZ_num := (@AFis_w.RZ_num n kz Hkz Nrange).
Ltac numconst ::= (ceil; unfold zone3, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize,
t_cache, t_unwinding, t_stats, ASTACK, TFIB_IMG_END, TFIB_IMG_LO, kLowShadowBeg, UNW_STK, BST_SIZE, DEP_STK in * ); try pose proof RZ_num as RZN.
Local Abbreviation derived_ranges := (@AFis_w.derived_ranges _ ly regs0 mem0 n cl cnt v kz Hcl Hv Hcnt Hv2 LY IMG DPOST Hkz Nrange).
Hypothesis Hcl_def : cl = class_id (R8v + RZ).
Local Abbreviation NDv_facts := (@AFis_w.NDv_facts ly regs0 mem0 n v kz DPOST Hkz Nrange).
Local Abbreviation CL_hi_E := (@AFis_w.CL_hi_E ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz DPOST Hkz Nrange Hcl_def).
Local Abbreviation CL_lo_E := (@AFis_w.CL_lo_E ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz DPOST Hkz Nrange Hcl_def).
Local Abbreviation WIN1 := (@AFis_w.WIN1 ly regs0 n cl v kz).
Local Abbreviation WIN1_WIN := (@AFis_w.WIN1_WIN ly regs0 mem0 n cl v kz DPOST).
Local Abbreviation WIN_odd := (@AFis_w.WIN_odd ly regs0 mem0 n cl cnt v jb kz Hcl Hv Hcnt Hjb Hsp DPOST Hkz Nrange).
Local Abbreviation WIN1_odd := (@AFis_w.WIN1_odd ly regs0 mem0 n cl cnt v jb kz Hcl Hv Hcnt Hjb Hsp DPOST Hkz Nrange).
Local Abbreviation WSKEL := (@AFis_w.WSKEL ).
Local Abbreviation WSKEL1 := (@AFis_w.WSKEL1 ).
Local Abbreviation win_sub := (@AFis_w.win_sub ).
Local Abbreviation win_sub_sound := (@AFis_w.win_sub_sound ly regs0 mem0 n v kz Hv DPOST).
Local Abbreviation WSKEL_WIN := (@AFis_w.WSKEL_WIN _ ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz Hcl Hv Hcnt Hv2 LY IMG DPOST Hkz Nrange).
Local Abbreviation WSKEL1_WIN1 := (@AFis_w.WSKEL1_WIN1 _ ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz Hcl Hv Hcnt Hv2 LY IMG DPOST Hkz Nrange).
Local Abbreviation windows_WIN := (@AFis_w.windows_WIN _ ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz Hcl Hv Hcnt Hv2 LY IMG DPOST Hkz Nrange).
Local Abbreviation windows_WIN1 := (@AFis_w.windows_WIN1 _ ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz Hcl Hv Hcnt Hv2 LY IMG DPOST Hkz Nrange).
Local Abbreviation frame_WIN1 := (@AFis_w.frame_WIN1 _ ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz Hcl Hv Hcnt Hv2 LY IMG DPOST Hkz Nrange).
Local Abbreviation WIN_not_high := (@AFis_w.WIN_not_high _ ly regs0 mem0 n cl cnt v kz Hcl Hv Hcnt Hv2 LY IMG Hsp DPOST Hkz Nrange).
Variables (mat0 : list word).
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 0x52bac) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis U1 : tfib_unwind_spec.
Hypothesis SEED : st_ok tfibsegs E0 SS0 (restrict (w_H W) (mkst regs0 (w64 0x52bac) mem0 (seg_rom tfibsegs))).
Local Abbreviation all_disjoint_of_forall := (@AFis_w.all_disjoint_of_forall ).
Local Abbreviation kept_of_frame := (@AFis_w.kept_of_frame W ly regs0 mem0 n v kz DPOST).
Local Abbreviation SKEL_TAIL := (@AFis_w.SKEL_TAIL ).
Local Abbreviation stack_ivs := (@AFis_w.stack_ivs _ ly regs0 mem0 n v kz Hv LY Hsp DPOST).
Local Abbreviation stack_ivs2 := (@AFis_w.stack_ivs2 _ ly regs0 mem0 n v kz Hv LY Hsp DPOST).
Local Abbreviation DZONE_disj := (@AFis_w.DZONE_disj _ ly regs0 mem0 n cl cnt v kz Hcl Hv Hcnt Hv2 LY IMG Hsp DPOST Hkz Nrange).
Local Abbreviation RFACTS := (@AFis_w.RFACTS ly regs0 n cl v kz).
Local Abbreviation zone_lit := (@AFis_w.zone_lit _ ly regs0 mem0 n cl cnt v kz Hcl Hv Hcnt Hv2 LY IMG Hsp DPOST Hkz Nrange).
Local Abbreviation zone_T := (@AFis_w.zone_T _ ly regs0 mem0 n cl cnt v kz Hcl Hv Hcnt Hv2 LY IMG Hsp DPOST Hkz Nrange).
Local Abbreviation zone_C := (@AFis_w.zone_C _ ly regs0 mem0 n cl cnt v kz Hcl Hv Hcnt Hv2 LY IMG Hsp DPOST Hkz Nrange).
Local Abbreviation zone_K := (@AFis_w.zone_K _ ly regs0 mem0 n cl cnt v kz Hcl Hv Hcnt Hv2 LY IMG Hsp DPOST Hkz Nrange).
Local Abbreviation zone_SH := (@AFis_w.zone_SH _ ly regs0 mem0 n cl cnt v kz Hcl Hv Hcnt Hv2 LY IMG Hsp DPOST Hkz Nrange).
Local Abbreviation tail_ext_ok := (@AFis_w.tail_ext_ok _ ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz Hcl Hv Hcnt Hv2 LY IMG Hsp DPOST Hkz Nrange).
Local Abbreviation at_ST := (@AFis_w.at_ST _ W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation at_ST2 := (@AFis_w.at_ST2 _ W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz DPOST).
Local Abbreviation at_S2 := (@AFis_w.at_S2 _ W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz DPOST).
Local Abbreviation at_RET := (@AFis_w.at_RET _ W ly regs0 mem0 md0 n cl cnt v jb kz DPOST).
Local Abbreviation memset_stretch := (@AFis_w.memset_stretch _ W ly regs0 mem0 n cl cnt v jb kz Hcl Hv Hcnt Hjb Hsp DPOST Hkz Nrange).
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
Local Abbreviation casek_sizes := (@AFis_w.casek_sizes n kz Hkz Nrange).
Local Abbreviation Kv_is_sptr := (@AFis_w.Kv_is_sptr ly cl v Hcl B off Hoff_def).
Local Abbreviation cl_range := (@AFiy_w.cl_range ly regs0 mem0 n cl v kz DPOST Hkz Nrange l off Hcl_class).
Local Abbreviation cls_geom := (@AFiy_w.cls_geom ly regs0 mem0 n cl v kz DPOST Hkz Nrange l off Hcl_class).
Local Abbreviation cls_wf := (@AFiy_w.cls_wf _ W ly regs0 mem0 n cl v kz DPOST Hkz Nrange B S l off HARm Hcl_class).
Local Abbreviation off_facts := (@AFiy_w.off_facts _ W ly regs0 mem0 n cl cnt v kz Hv2 DPOST Hkz Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation Kv_base := (@AFiy_w.Kv_base ly regs0 mem0 n cl v kz DPOST Hkz Nrange l off Hcl_class Hoff_def).
Local Abbreviation Kv_geom := (@AFiy_w.Kv_geom _ W ly regs0 mem0 n cl cnt v csz kz Hv2 LY DPOST Hkz Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def).
Local Abbreviation Hcl' := (@AFiy_w.Hcl' ly regs0 mem0 n cl v kz DPOST Hkz Nrange l off Hcl_class).
Local Abbreviation Hcnt' := (@AFiy_w.Hcnt' _ W ly regs0 mem0 n cl cnt v kz Hv2 Hsp DPOST Hkz Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation Hv' := (@AFiy_w.Hv' _ W ly regs0 mem0 n cl cnt v kz Hv2 DPOST Hkz Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation cached_vs_chunk := (@AFiy_w.cached_vs_chunk _ W ly regs0 mem0 n cl cnt v csz kz Hv2 LY Hsp DPOST Hkz Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def).
Local Abbreviation find_chunk_at_none := (@AFiy_w.find_chunk_at_none _ W ly regs0 mem0 n cl cnt v kz Hv2 Hsp DPOST Hkz Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation shadow250 := (@AFiy_w.shadow250 _ W ly regs0 mem0 n cl cnt v csz kz Hv2 LY Hsp DPOST Hkz Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def).
Local Abbreviation shadow_present := (@AFiy_w.shadow_present _ W ly regs0 mem0 n cl cnt v csz kz Hv2 LY IMG Hsp DPOST Hkz Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def).
Local Abbreviation vis_present := (@AFiy_w.vis_present _ W ly regs0 mem0 n cl cnt v kz Hv2 Hsp DPOST Hkz Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation KPRES := (@AFiy_w.KPRES _ W ly regs0 mem0 n cl cnt v csz kz Hv2 LY Hsp DPOST Hkz Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def).
Local Abbreviation SKPRES := (@AFiy_w.SKPRES _ W ly regs0 mem0 n cl cnt v csz kz Hv2 LY IMG Hsp DPOST Hkz Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def).
Local Abbreviation PB250 := (@AFiy_w.PB250 _ W ly regs0 mem0 n cl cnt v csz kz Hv2 LY IMG Hsp DPOST Hkz Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def).
Local Abbreviation in_thread_junk := (@AFiy_w.in_thread_junk _ W ly regs0 mem0 n cl cnt v kz Hv2 Hsp DPOST Hkz Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation junk_word := (@AFiy_w.junk_word _ W ly regs0 mem0 n cl cnt v kz Hv2 LY IMG Hsp DPOST Hkz Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation junk_byte := (@AFiy_w.junk_byte _ W ly regs0 mem0 n cl cnt v csz kz Hv2 LY Hsp DPOST Hkz Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def).
Local Abbreviation junk_values := (@AFiy_w.junk_values _ W ly regs0 mem0 n cl cnt v csz kz Hv2 LY IMG Hsp DPOST Hkz Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def).
Local Abbreviation cell_sym := (@AFiy_w.cell_sym _ W ly regs0 mem0 n cl cnt v kz Hv2 Hsp DPOST Hkz Nrange B S l off TS HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation cell_lit := (@AFiy_w.cell_lit _ W ly regs0 mem0 n cl cnt v kz Hv2 Hsp DPOST Hkz Nrange B S l off TS HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation cell_state := (@AFiy_w.cell_state _ W ly regs0 mem0 n cl cnt v kz Hv2 Hsp DPOST Hkz Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation In_acells_cache := (@AFiy_w.In_acells_cache _ W ly regs0 mem0 n cl cnt v kz Hv2 Hsp DPOST Hkz Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation In_combine_seq_last := (@AFiy_w.In_combine_seq_last _ W ly regs0 mem0 n cl cnt v kz Hv2 Hsp DPOST Hkz Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation cache_vals := (@AFiy_w.cache_vals _ W ly regs0 mem0 n cl cnt v csz kz Hv2 Hsp DPOST Hkz Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def).
Local Abbreviation unwinding_val := (@AFiy_w.unwinding_val _ W ly regs0 mem0 n cl cnt v kz Hv2 Hsp DPOST Hkz Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation sk_val := (@AFiy_w.sk_val _ W ly regs0 mem0 n cl cnt v csz kz Hv2 LY IMG Hsp DPOST Hkz Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def).
Local Abbreviation val_mem_mod8 := (@AFiy_w.val_mem_mod8 _ W ly regs0 mem0 n cl cnt v kz Hv2 Hsp DPOST Hkz Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation chunk_lit := (@AFiy_w.chunk_lit _ W ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz Hv2 Hsp DPOST Hkz Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation chunk_lit_at := (@AFiy_w.chunk_lit_at _ W ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz Hv2 Hsp DPOST Hkz Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation chunk_atom := (@AFiy_w.chunk_atom _ W ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz Hv2 Hsp DPOST Hkz Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation REG0_ok := (@AFiz_w.REG0_ok _ W ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz Hcl Hv Hcnt Hjb Hv2 LY IMG Hsp DPOST Hkz Nrange B S l off TS HTSD HARm Hpres0 Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def Hj0 Hj1 Hj2 Hj3 Hj4 Hjb_def).
Local Abbreviation Kv32 := (@AFj0_w.Kv32 _ W ly regs0 mem0 n cl v kz Hv2 LY DPOST l off).
Local Abbreviation PAIRS_ok := (@AFj0_w.PAIRS_ok _ W ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz Hcl Hv Hcnt Hv2 LY IMG Hsp DPOST Hkz Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def).
Local Abbreviation FACTS_ok := (@AFj0_w.FACTS_ok _ W ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz Hcl Hv Hcnt Hjb Hv2 LY IMG Hn Hsp DPOST Hkz Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def).
Local Abbreviation SEED_ok := (@AFj0_w.SEED_ok _ _ W ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz Hcl Hv Hcnt Hjb Hv2 LY IMG Hn Htp Hsp DPOST Hkz Nrange B S l off TS HTSD HARm Hpres0 Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def Hj0 Hj1 Hj2 Hj3 Hj4 Hjb_def).
Local Abbreviation CZONE := (@AFix_w.CZONE ly).
Local Abbreviation abs_cell_ok := (@AFix_w.abs_cell_ok ).
Local Abbreviation abs_cells_ok := (@AFix_w.abs_cells_ok ).
Local Abbreviation const_cells_zone := (@AFix_w.const_cells_zone ly regs0 mem0 n v kz Hv DPOST B l off TS HTSD).
Local Abbreviation CZONE_untouched := (@AFix_w.CZONE_untouched _ ly regs0 mem0 n cl cnt v kz Hcl Hv Hcnt Hv2 LY IMG Hsp DPOST Hkz Nrange l off).
Local Abbreviation cell_holds_agree := (@AFix_w.cell_holds_agree ly regs0 mem0 n v kz Hv DPOST B l off).
Local Abbreviation aview_agree := (@AFix_w.aview_agree W).
Local Abbreviation const_kept := (@AFix_w.const_kept _ W ly regs0 mem0 n cl cnt v kz Hcl Hv Hcnt Hv2 LY IMG Hsp DPOST Hkz Nrange B l off TS HTSD).
Local Abbreviation depot_ids_bound := (@AFix_w.depot_ids_bound ly regs0 mem0 n v kz Hv DPOST B l off TS).
Local Abbreviation depot_mem_ok_agree := (@AFix_w.depot_mem_ok_agree ly regs0 mem0 n v kz Hv DPOST B l off TS).
Local Abbreviation depot_ok_ext := (@AFix_w.depot_ok_ext ly B).
Local Abbreviation depot_at0 := (@AFix_w.depot_at0 _ W ly regs0 mem0 n cl cnt v jb kz Hcl Hv Hcnt Hjb Hsp DPOST Hkz Nrange B S HARm).
Local Abbreviation DPOST3 := (@AFix_w.DPOST3 W ly regs0 ch B S).
Local Abbreviation D1W_ok := (@AFix_w.D1W_ok _ _ W ly regs0 mem0 n ch cl cnt v jb kz Hcl Hv Hcnt Hjb Hv2 LY IMG Hsp DPOST Hkz Nrange B S l off TS HTSD HARm Hgp).
Local Abbreviation st_popped := (@AFix_w.st_popped ).
Local Abbreviation new_chunk := (@AFix_w.new_chunk ).
Local Abbreviation st_final := (@AFix_w.st_final ).
Local Abbreviation Kc_user := (@AFix_w.Kc_user ly regs0 mem0 n ch cl v kz Hcl DPOST Hkz Nrange B S l off Hoff_def).
Local Abbreviation MPF := (@AFix_w.MPF ly regs0 n ch cl B S l off).
Local Abbreviation AR_final_stmt := (@AFix_w.AR_final_stmt _ _ W ly regs0 mem0 md0 n ch cl cnt v jb kz DPOST B S l off).
Local Abbreviation WR_owned := (@AFix_w.WR_owned _ W ly regs0 mem0 n ch cl cnt v csz jb kz Hcl Hv Hcnt Hjb Hv2 LY IMG Hsp DPOST Hkz Nrange B S l off TS HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def).
Local Abbreviation LEAF_ok := (@AFix_w.LEAF_ok _ _ W ly regs0 mem0 md0 n ch cl cnt v csz jb kz Hcl Hv Hcnt Hjb Hv2 LY IMG Hsp DPOST Hkz Nrange mat0 B S l off TS HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def).
Local Abbreviation Kc_fresh := (@AFix_w.Kc_fresh _ W ly regs0 mem0 n ch cl cnt v kz Hcl Hv Hv2 DPOST Hkz Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation upd_chunk_fresh := (@AFix_w.upd_chunk_fresh n cl off).
Local Abbreviation SF_chunks := (@AFix_w.SF_chunks _ W ly regs0 mem0 n ch cl cnt v kz Hcl Hv Hv2 DPOST Hkz Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation SF_same := (@AFix_w.SF_same ly regs0 n ch cl S l off).
Local Abbreviation SF_sec_extents := (@AFix_w.SF_sec_extents _ W ly regs0 mem0 n ch cl cnt v kz Hcl Hv Hv2 DPOST Hkz Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation SF_sec_live := (@AFix_w.SF_sec_live _ W ly regs0 mem0 n ch cl cnt v kz Hcl Hv Hv2 DPOST Hkz Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation SF_ledger := (@AFix_w.SF_ledger _ W ly regs0 mem0 n ch cl cnt v kz Hcl Hv Hv2 DPOST Hkz Nrange B S l off HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation cell_holds_agree2 := (@AFix_w.cell_holds_agree2 ly regs0 mem0 n ch cl cnt v jb kz Hcl Hv Hcnt Hjb Hsp DPOST Hkz Nrange B S l off).
Local Abbreviation zrange_dec := (@AFj1_w.zrange_dec ).
Local Abbreviation apresent_word := (@AFj1_w.apresent_word ).
Local Abbreviation val_mem_cell := (@AFj1_w.val_mem_cell W ly regs0 mem0 n ch cl v kz DPOST B S l off).
Local Abbreviation le_byte_1_0 := (@AFj1_w.le_byte_1_0 ly regs0 mem0 n ch cl v kz DPOST S l off).
Local Abbreviation find_chunk_at_app1 := (@AFj1_w.find_chunk_at_app1 ly B).
Local Abbreviation find_chunk_at_app2 := (@AFj1_w.find_chunk_at_app2 ly B).
Local Abbreviation In_combine_seq_app := (@AFj1_w.In_combine_seq_app ).
Local Abbreviation Kc_facts := (@AFj1_w.Kc_facts ly n cl v kz Hcl Hkz Nrange B off Hcl_class Hoff_def).
Local Abbreviation NLOf := (@AFj1_w.NLOf n kz Hkz Nrange).
Local Abbreviation AR_final := (@AFj1_w.AR_final _ _ W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz Hcl Hv Hcnt Hjb Hv2 LY IMG Hsp DPOST HKpres HSKpres HPB250 Hkz Nrange Hcl_def SEED B S l off TS HTSD HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def Hj4 Hjb_def).
Local Abbreviation LEAF_final := (@AFj1_w.LEAF_final _ _ W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz Hcl Hv Hcnt Hjb Hv2 LY IMG Hsp DPOST HKpres HSKpres HPB250 Hkz Nrange Hcl_def mat0 SEED B S l off TS HTSD HARm Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def Hj4 Hjb_def).
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
Local Abbreviation seg1J := (@AFip_w.seg1J _ _ W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz Hcl Hv Hcnt Hjb Hv2 LY IMG Hn Hra4096 Hsp Hch DPOST Hkz Nrange Hcl_def mat0 U1 SEED l off).
Local Abbreviation segC2 := (@AFip_w.segC2 _ _ W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz Hcl Hv Hcnt Hv2 LY IMG Hn Hsp DPOST Hkz Nrange l off).
Local Abbreviation segD := (@AFiq_w.segD _ _ W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz LY Hsp DPOST l off D1w).
Local Abbreviation seg2a_even := (@AFiq_w.seg2a_even _ _ W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz Hcl Hv Hcnt Hjb Hv2 LY IMG Hn Hsp DPOST HSKpres Hkz Nrange Hcl_def l off).
Local Abbreviation seg2b_even := (@AFiq_w.seg2b_even _ _ W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz Hcl Hv Hcnt Hv2 LY IMG Hn Hsp DPOST Hkz Nrange l off).
Local Abbreviation seg2c_even := (@AFiq_w.seg2c_even _ _ W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz Hcl Hv Hcnt Hjb Hv2 LY IMG Hn Htp Hra Hsp DPOST HKpres Hkz Nrange l off).
Local Abbreviation seg2a_odd := (@AFir_w.seg2a_odd _ _ W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz Hcl Hv Hcnt Hjb Hv2 LY IMG Hn Hsp DPOST HSKpres HPB250 Hkz Nrange Hcl_def l off).
Local Abbreviation seg2b_odd := (@AFir_w.seg2b_odd _ _ W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz Hcl Hv Hcnt Hv2 LY IMG Hn Hsp DPOST HPB250 Hkz Nrange l off).
Local Abbreviation seg2c_odd := (@AFir_w.seg2c_odd _ _ W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz Hcl Hv Hcnt Hjb Hv2 LY IMG Hn Htp Hra Hsp DPOST HKpres HPB250 Hkz Nrange l off).
Theorem tail_inner : forall c1, at_ST SS_JN W c1 ->
amreal tfibsegs (malloc_join n tr cl S) W c1
(fun r W' c' => Wf (as_universe B) (snd r) /\ qtight (snd r) -> malloc_leaf tfibsegs B ly S W regs0 mem0 md0 n r W' c').
Proof.
intros c1 HJ.
pose proof casek_sizes as (L & RS & R8 & NP & FP & NS & RQ). pose proof RZ_facts as (_ & _ & _ & RF4 & _).
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
