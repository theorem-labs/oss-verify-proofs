(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/A/AFj7.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_identity's ASan build. *)
(* Modified by Theorem Labs, 2026-11: made from A/AFj7.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import AFhy_w AFi1_w AFj6_w AFhz_w AFi2_w AFi4_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Set Printing Depth 50. Set Printing Width 180.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Ltac zlia := first [ lia | ceil; unfold zone3, zone3cases, off_img, in_app, app_addr, in_band_rw, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPrimResvSize, kSpaceSize in *; lia ].
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
Local Abbreviation RZ := (@AFj6_w.RZ).
Local Abbreviation NPv := (@AFj6_w.NPv n).
Local Abbreviation R8v := (@AFj6_w.R8v n).
Local Abbreviation N8D := (@AFj6_w.N8D n).
Local Abbreviation Pv := (@AFj6_w.Pv ly cl).
Local Abbreviation PVv := (@AFj6_w.PVv ly cl cnt).
Local Abbreviation Kv := (@AFj6_w.Kv ly cl v).
Local Abbreviation SHBv := (@AFj6_w.SHBv).
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
Ltac off_by tac :=
first [ apply off_img_high; tac
| apply off_T; unfold kThreadObjSize; tac
| apply off_C; tac
| apply off_NB; unfold kNodesBlockSize; tac
| apply off_SB; unfold kStoreBlockSize; tac
| unfold off_img; unfold TFIB_IMG_LO; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; tac ].
Hypothesis Nrange : 0 <= n <= 48.
Local Abbreviation K0_facts := (@AFj6_w.K0_facts n Nrange).
Local Abbreviation RZ_num := (@AFj6_w.RZ_num n Nrange).
Ltac numconst ::= (ceil; unfold zone3, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize,
t_cache, t_unwinding, t_stats, ASTACK, TFIB_IMG_END, TFIB_IMG_LO, kLowShadowBeg, UNW_STK, BST_SIZE, DEP_STK in * ); try pose proof RZ_num as RZN.
Local Abbreviation derived_ranges := (@AFj6_w.derived_ranges _ ly regs0 mem0 n cl cnt v Hcl Hv Hcnt Hv2 LY IMG DPOST Nrange).
Hypothesis Hcl_def : cl = class_id (R8v + RZ).
Local Abbreviation CLk := (@AFj6_w.CLk).
Local Abbreviation CLk_E := (@AFj6_w.CLk_E ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 DPOST Nrange Hcl_def).
Local Abbreviation WIN1 := (@AFj6_w.WIN1 ly regs0 n cl v).
Local Abbreviation WIN1_WIN := (@AFj6_w.WIN1_WIN ly regs0 mem0 n cl v DPOST).
Local Abbreviation WIN_odd := (@AFj6_w.WIN_odd ly regs0 mem0 n cl cnt v jb Hcl Hv Hcnt Hjb Hsp DPOST Nrange).
Local Abbreviation WIN1_odd := (@AFj6_w.WIN1_odd ly regs0 mem0 n cl cnt v jb Hcl Hv Hcnt Hjb Hsp DPOST Nrange).
Local Abbreviation WSKEL := (@AFj6_w.WSKEL).
Local Abbreviation WSKEL1 := (@AFj6_w.WSKEL1).
Local Abbreviation win_sub := (@AFj6_w.win_sub).
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
Local Abbreviation all_disjoint_of_forall := (@AFj6_w.all_disjoint_of_forall).
Local Abbreviation kept_of_frame := (@AFj6_w.kept_of_frame W ly regs0 mem0 n v DPOST).
Local Abbreviation SKEL_TAIL := (@AFj6_w.SKEL_TAIL).
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
Ltac frame_acc HE :=
match goal with
| MEQ : (forall x : word, ~ WIN1 ?odd (bv_unsigned x) -> ?m1 x = ?mb x), HFx : frame_of ?E ?rs ?m1 ?m2 |- _ =>
let MEQ' := fresh "MEQ" in
assert (MEQ' : forall x : word, ~ WIN1 odd (bv_unsigned x) -> m2 x = mb x)
by (intros x Hx; transitivity (m1 x); [exact (frame_WIN1 odd E rs m1 m2 HE ltac:(vm_compute; reflexivity) HFx x Hx) | exact (MEQ x Hx)]);
clear MEQ HFx; rename MEQ' into MEQ
end.
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
Local Ltac addr_tac :=
cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi];
rewrite ?EaT, ?EaC, ?EaTOP, ?EaSB, ?E2; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, w64, ly_bot, kStackSpan, t_unwinding, t_cache, t_stats, TFIB_IMG_END, UNW_STK, BST_SIZE, ASTACK, IFRAME, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *;
rewrite ?unsigned_lit_small by zlia; zlia.
Local Ltac close_ST En HEn HS memB MEQ MEQW PRESW BUFW :=
apply SRr_ret; split; [reflexivity|];
lazymatch goal with |- context [mkCfg ?msf (with_vm_backing _ ?matf _)] => exists msf, matf, En end;
split; [reflexivity|]; split; [exact HEn|]; split; [exact HS|];
pose proof derived_ranges as DR'; pose proof high_facts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9); pose proof Kv_range as HKR;
pose proof (lo_top ly LY) as (T1' & T2' & T3' & T4' & T5' & T6' & T7'); pose proof Hsp as (Hlo_ & Hbot_ & Hhi_ & Hal_);
split; [|split];
[ intros x Hx; rewrite (MEQ x) by (intros H1; apply Hx, WIN1_WIN, H1); apply MEQW, Hx
| intros a Ha; destruct (Z_lt_le_dec a (sp0 - IFRAME)) as [Hlo'|Hge];
[ eapply (st_ok_window_apresent_off (w_H W) En _ _ 1 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn 2%nat (ltHAV 2 eq_refl)), E2; addr_tac | off_by ltac:(addr_tac) ]
| destruct (Z_lt_le_dec a (sp0 - 64)) as [Hmid|Htop'];
[ apply (apresent_same (w_H W) memB);
[ apply MEQ; assert (Hx : ly_stk_lo ly <= a < ly_stk_hi ly) by (clear - Hge Hmid Hlo_ Hhi_; unfold IFRAME, ASTACK in *; zlia);
destruct (F9 a Hx) as [N1 N2]; pose proof (HCdisj a Hx) as HC;
clear - Hge Hmid DR' HKR N1 N2 HC T7' T4' Hlo_ Hhi_ F1 F2 F3 F4 F5 F6 F7 F8;
unfold WIN1, WINT, PBW, IFRAME in *; numconst; rewrite unsigned_lit_small by zlia; zlia
| apply PRESW; unfold IFRAME in *; zlia ]
| eapply (st_ok_window_apresent_off (w_H W) En _ _ 2 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn 2%nat (ltHAV 2 eq_refl)), E2; addr_tac | off_by ltac:(addr_tac) ] ] ]
| intros i Hi; pose proof tr_length as LEN;
eapply val_mem_frame; [|eapply val_mem_addr; [exact (BUFW i Hi) | clear - Hi LEN Hlo_ Hhi_ T4' T7'; addr_tac]];
intros k Hk; apply MEQ;
assert (Hx : ly_stk_lo ly <= sp0 - IFRAME + 16 + 8 * Z.of_nat i + Z.of_nat k < ly_stk_hi ly) by (clear - Hi Hk LEN Hlo_ Hhi_; unfold IFRAME, ASTACK in *; zlia);
destruct (F9 _ Hx) as [N1 N2]; pose proof (HCdisj _ Hx) as HC;
clear - Hi Hk LEN DR' HKR N1 N2 HC T7' T4' Hlo_ Hhi_ F1 F2 F3 F4 F5 F6 F7 F8;
unfold WIN1, WINT, PBW, IFRAME in *; numconst; rewrite unsigned_lit_small by zlia; zlia ].
Lemma segJ : forall W0 c, at_ST MK_AFTER W0 c -> SRr tfibsegs W0 c (at_ST KS_JN).
Proof.
intros W0 c (-> & ms & mat & En & -> & HEn & HS & MEQW & PRESW & BUFW). pose proof Hwx_tfa as Hwx.
pose proof Hsp as (Hlo & Hbot & Hhi & Hal). pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
pose proof derived_ranges as DR. pose proof high_facts as LF. pose proof K0_facts as (_ & NR & NPr & _ & _ & R8r & R8m & NPR8 & _).
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, t_cache, t_unwinding in DR, LF.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) En _ _ HS eq_refl) as Hshape; cbn [ss_pc] in Hshape;
lazymatch type of Hshape with _ = mkst _ (Z_to_bv 64 (ss_pc ?s)) _ _ => let p := eval vm_compute in (ss_pc s) in change (ss_pc s) with p in Hshape | _ => idtac end.
rewrite Hshape in HS. rewrite Hshape. set (mem1 := ms_mem ms) in *.
assert (MEQ : forall x : word, ~ WIN1 false (bv_unsigned x) -> mem1 x = mem1 x) by (intros; reflexivity).
srr_run_to_sh tfibtbl_rtA_ok HS 0x36244. frame_acc HEn.
forget_regs HS 103%nat ([1; 5; 6; 7; 14; 15; 16; 17; 19; 20; 28; 29; 30; 31]%bv : list (bv 5)).
apply (YP03.st_ok_prune tfibsegs _ _ _ [] []) in HS.
lazymatch type of HS with st_ok _ _ ?ss _ => replace ss with KS_JN in HS by (vm_compute; reflexivity) end.
lazymatch type of HS with st_ok _ ?E2 _ _ => set (EnE := E2) in HS end.
assert (HEnE : forall j, (j < aHAV)%nat -> ew EnE j = ew E0 j) by (intros j Hj; subst EnE; unfold aHAV in Hj; rewrite ew_havoc_old by zlia; apply HEn; exact Hj).
close_ST EnE HEnE HS mem1 MEQ MEQW PRESW BUFW.
Qed.
End e.
End d.
