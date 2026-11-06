(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/AGj2.v (a working branch ced28ed2383, file sha256 1efd63514872) onto omx-clap-core/fuzz_state's asan image (unstripped fuzz_state.asan, sha256 7c4afaee248b); module paths changed; its 3 image addresses moved by code-verified function pairs (4 port_addr_check 16f8a030c869 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py); no other numeral changed. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1w AE3d AFhy AGhy AGis AGhz AFi3 AGip AGiq AGir AGif0cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import AGif0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AGif2cgif.
(* The can_fill = 0 tail (a Theorem Labs lane): AGc1.seg2cf0_even / _odd end in AGc0.at_RET0. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require AGc0 AGc1.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
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
t_cache, t_unwinding, t_stats, AFSTACK, TFIB_IMG_END, TFIB_IMG_LO, kLowShadowBeg, UNW_STK, BST_SIZE, DEP_STK in *.
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
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (n : Z) (tr : list Z).
Variables (cl cnt v csz j0 jb j1 j2 j3 j4 : Z).
Variable kz : Z.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let SOv : Z := bv_unsigned (getr regs0 13).
Let BPv : Z := bv_unsigned (getr regs0 12).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Local Abbreviation RZ := (@AGis.RZ kz).
Local Abbreviation R8v := (@AGis.R8v n).
Local Abbreviation N8D := (@AGis.N8D n).
Local Abbreviation Pv := (@AGis.Pv ly cl).
Local Abbreviation PVv := (@AGis.PVv ly cl cnt).
Local Abbreviation Kv := (@AGis.Kv ly cl v).
Local Abbreviation SHBv := (@AGis.SHBv).
Local Abbreviation SKv := (@AGis.SKv ly cl v).
Local Abbreviation SSLOTv := (@AGis.SSLOTv ly cl).
Local Abbreviation PBv := (@AGis.PBv ly n cl v kz).
Local Abbreviation Uv := (@AGis.Uv ly cl v kz).
Local Abbreviation SUv := (@AGis.SUv ly cl v kz).
Local Abbreviation FILv := (@AGis.FILv n).
Local Abbreviation NDv := (@AGis.NDv n kz).
Local Abbreviation XW := (@AGis.XW ly n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation E0 := (@AGis.E0 ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaT := (@AGis.EaT ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaC := (@AGis.EaC ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaSB := (@AGis.EaSB ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaTOP := (@AGis.EaTOP ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation Er := (@AGis.Er ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation E2 := (@AGis.E2 ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation E1 := (@AGis.E1 ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation E8 := (@AGis.E8 ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation E10 := (@AGis.E10 ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation E4 := (@AGis.E4 ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaP := (@AGis.EaP ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaK := (@AGis.EaK ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaSK := (@AGis.EaSK ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaSSLOT := (@AGis.EaSSLOT ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaPB := (@AGis.EaPB ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaPV := (@AGis.EaPV ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaKL := (@AGis.EaKL ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaRZ := (@AGis.EaRZ ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaU := (@AGis.EaU ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaSU := (@AGis.EaSU ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaFIL := (@AGis.EaFIL ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaND := (@AGis.EaND ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation WINT := (@AGis.WINT ly cl).
Local Abbreviation PBW := (@AGis.PBW ly n cl v kz).
Local Abbreviation WIN := (@AGis.WIN ly regs0 n cl v kz).
Local Abbreviation win_in_WIN := (@AGis.win_in_WIN ly regs0 n cl v kz).
Hypotheses (Hcl : 1 <= cl <= 31) (Hv : 0 <= v /\ 16 * v + 2 ^ 16 <= 2 ^ 32) (Hcnt : 1 <= cnt <= 16) (Hjb : 0 <= jb <= 255).
Hypothesis Hv2 : v mod 2 = 0.
Hypothesis LY : layout_ok ly.
Hypothesis IMG : img_cover ly.
Hypothesis Hn : getr regs0 10 = w64 n.
Hypothesis Htp : getr regs0 4 = w64 TFIB_TP.
(* can_fill (virtual x15): 0 (calloc) or 1. *)
Hypothesis Hcf : getr regs0 15 = w64 0 \/ getr regs0 15 = w64 1.
Hypothesis Hra : YK0s.ret_ok (getr regs0 1).
Hypothesis Hra4096 : 4096 <= bv_unsigned (getr regs0 1).
Hypothesis Hsp : ly_stk_lo ly + AFSTACK <= sp0 /\ ly_bot ly < sp0 /\ sp0 <= ly_stk_hi ly /\ sp0 mod 16 = 0.
Hypothesis Htrlen : (1 <= length tr <= 30)%nat.
Hypothesis Hso : sp0 <= SOv /\ SOv + 16 <= ly_stk_hi ly /\ SOv mod 8 = 0.
Hypothesis Hbp : sp0 <= BPv /\ BPv + 8 * 30 <= ly_stk_hi ly /\ BPv mod 8 = 0.
(* The allocator instance (atom aINST = register 11 of the virtual regs0) lies in the image, below the depot. *)
Hypothesis Hinst : TFIB_IMG_LO <= bv_unsigned (getr regs0 11) /\ bv_unsigned (getr regs0 11) + 0xe60 <= 0x179e08.
Local Abbreviation HCdisj := (@AGis.HCdisj _ ly regs0 tr v Hv LY Htrlen).
Local Abbreviation DZONE := (@AGis.DZONE ly).
Variable DPOST : Z -> (word -> option byte) -> Prop.
Local Abbreviation HC_NB := (@AGis.HC_NB _ ly LY).
Hypothesis HKpres : forall a, Kv <= a < Kv + RZ + R8v -> apresent (w_H W) mem0 a.
Hypothesis HSKpres : forall a, SKv <= a < SKv + (RZ + R8v) / 8 -> apresent (w_H W) mem0 a.
Hypothesis HPB250 : n mod 8 <> 0 -> val_mem tfibsegs (mrestrict (w_H W) mem0) PBv 1 250.
Local Abbreviation HCX := (@AGis.HCX _ ly LY).
Local Abbreviation tr_length := (@AGis.tr_length tr Htrlen).
Local Abbreviation Kv_range := (@AGis.Kv_range ly regs0 mem0 n tr cl v kz Hcl Hv Hv2 Htrlen DPOST).
Local Abbreviation high_facts := (@AGis.high_facts _ ly regs0 mem0 n tr v kz Hv LY IMG Htrlen DPOST).
Local Abbreviation blocks_facts := (@AGis.blocks_facts _ ly LY IMG).
Local Abbreviation off_T := (@AGis.off_T _ ly regs0 mem0 n tr v kz Hv LY IMG Htrlen DPOST).
Local Abbreviation off_C := (@AGis.off_C _ ly regs0 mem0 n tr v kz Hv LY IMG Htrlen DPOST).
Local Abbreviation off_NB := (@AGis.off_NB _ ly LY IMG).
Local Abbreviation off_SB := (@AGis.off_SB _ ly LY IMG).
Ltac off_by tac :=
first [ apply off_img_high; tac
| apply off_T; unfold kThreadObjSize; tac
| apply off_C; tac
| apply off_NB; unfold kNodesBlockSize; tac
| apply off_SB; unfold kStoreBlockSize; tac
| unfold off_img; unfold TFIB_IMG_LO; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; tac ].
Hypothesis Hkz : 1 <= kz <= 6.
Hypothesis Nrange : rz_lo kz <= n <= rz_hi kz.
Local Abbreviation kz_cases := (@AGis.kz_cases kz Hkz).
Local Abbreviation RZ_facts := (@AGis.RZ_facts n kz Hkz Nrange).
Local Abbreviation RZ_num := (@AGis.RZ_num n kz Hkz Nrange).
#[local] Ltac numconst ::= (ceil; unfold zone3, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize,
t_cache, t_unwinding, t_stats, AFSTACK, TFIB_IMG_END, TFIB_IMG_LO, kLowShadowBeg, UNW_STK, BST_SIZE, DEP_STK in * ); try pose proof RZ_num as RZN.
Local Abbreviation derived_ranges := (@AGis.derived_ranges _ ly regs0 mem0 n tr cl cnt v kz Hcl Hv Hcnt Hv2 LY IMG Htrlen DPOST Hkz Nrange).
Hypothesis Hcl_def : cl = class_id (R8v + RZ).
Local Abbreviation NDv_facts := (@AGis.NDv_facts ly regs0 mem0 n tr v kz Htrlen DPOST Hkz Nrange).
Local Abbreviation CL_hi_E := (@AGis.CL_hi_E ly regs0 mem0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz Htrlen DPOST Hkz Nrange Hcl_def).
Local Abbreviation CL_lo_E := (@AGis.CL_lo_E ly regs0 mem0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz Htrlen DPOST Hkz Nrange Hcl_def).
Local Abbreviation WIN1 := (@AGis.WIN1 ly regs0 n cl v kz).
Local Abbreviation WIN1_WIN := (@AGis.WIN1_WIN ly regs0 mem0 n tr cl v kz Htrlen DPOST).
Local Abbreviation WIN_odd := (@AGis.WIN_odd ly regs0 mem0 n tr cl cnt v jb kz Hcl Hv Hcnt Hjb Hsp Htrlen Hso Hbp DPOST Hkz Nrange).
Local Abbreviation WIN1_odd := (@AGis.WIN1_odd ly regs0 mem0 n tr cl cnt v jb kz Hcl Hv Hcnt Hjb Hsp Htrlen Hso Hbp DPOST Hkz Nrange).
Local Abbreviation WSKEL := (@AGis.WSKEL).
Local Abbreviation WSKEL1 := (@AGis.WSKEL1).
Local Abbreviation win_sub := (@AGis.win_sub).
Local Abbreviation win_sub_sound := (@AGis.win_sub_sound ly regs0 mem0 n tr v kz Hv Htrlen DPOST).
Local Abbreviation WSKEL_WIN := (@AGis.WSKEL_WIN _ ly regs0 mem0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz Hcl Hv Hcnt Hv2 LY IMG Htrlen DPOST Hkz Nrange).
Local Abbreviation WSKEL1_WIN1 := (@AGis.WSKEL1_WIN1 _ ly regs0 mem0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz Hcl Hv Hcnt Hv2 LY IMG Htrlen DPOST Hkz Nrange).
Local Abbreviation windows_WIN := (@AGis.windows_WIN _ ly regs0 mem0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz Hcl Hv Hcnt Hv2 LY IMG Htrlen DPOST Hkz Nrange).
Local Abbreviation windows_WIN1 := (@AGis.windows_WIN1 _ ly regs0 mem0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz Hcl Hv Hcnt Hv2 LY IMG Htrlen DPOST Hkz Nrange).
Local Abbreviation frame_WIN1 := (@AGis.frame_WIN1 _ ly regs0 mem0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz Hcl Hv Hcnt Hv2 LY IMG Htrlen DPOST Hkz Nrange).
Local Abbreviation WIN_not_high := (@AGis.WIN_not_high _ ly regs0 mem0 n tr cl cnt v kz Hcl Hv Hcnt Hv2 LY IMG Hsp Htrlen Hso Hbp DPOST Hkz Nrange).
Variables (mat0 : list word).
Let H0 := w_H W.
(* The registers at Allocate's entry, over the virtual regs0 of E0 (AGhy.REGS_G). *)
Variable regsU : bvmap 5 word.
Let cfg0 : config := mkCfg (mkst regsU (w64 A_Allocate) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis SEED : st_ok tfibsegs E0 SS_1 (restrict (w_H W) (mkst regsU (w64 A_Allocate) mem0 (seg_rom tfibsegs))).
Hypothesis PBUF0 : forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W) mem0) (BPv + 8 * Z.of_nat i) 8 (nth i tr 0).
Local Abbreviation all_disjoint_of_forall := (@AGis.all_disjoint_of_forall).
Local Abbreviation kept_of_frame := (@AGis.kept_of_frame W ly regs0 mem0 n tr v kz Htrlen DPOST).
Local Abbreviation SKEL_TAIL := (@AGis.SKEL_TAIL).
Local Abbreviation stack_ivs := (@AGis.stack_ivs _ ly regs0 mem0 n tr v kz Hv LY Hsp Htrlen Hbp DPOST).
Local Abbreviation stack_ivs2 := (@AGis.stack_ivs2 _ ly regs0 mem0 n tr v kz Hv LY Hsp Htrlen Hbp DPOST).
Local Abbreviation DZONE_disj := (@AGis.DZONE_disj _ ly regs0 mem0 n tr cl cnt v kz Hcl Hv Hcnt Hv2 LY IMG Hsp Htrlen Hso Hbp DPOST Hkz Nrange).
Local Abbreviation RFACTS := (@AGis.RFACTS ly regs0 n cl v kz).
Local Abbreviation zone_lit := (@AGis.zone_lit _ ly regs0 mem0 n tr cl cnt v kz Hcl Hv Hcnt Hv2 LY IMG Hsp Htrlen DPOST Hkz Nrange).
Local Abbreviation zone_T := (@AGis.zone_T _ ly regs0 mem0 n tr cl cnt v kz Hcl Hv Hcnt Hv2 LY IMG Hsp Htrlen Hbp DPOST Hkz Nrange).
Local Abbreviation zone_C := (@AGis.zone_C _ ly regs0 mem0 n tr cl cnt v kz Hcl Hv Hcnt Hv2 LY IMG Hsp Htrlen Hbp DPOST Hkz Nrange).
Local Abbreviation zone_K := (@AGis.zone_K _ ly regs0 mem0 n tr cl cnt v kz Hcl Hv Hcnt Hv2 LY IMG Hsp Htrlen Hbp DPOST Hkz Nrange).
Local Abbreviation zone_SH := (@AGis.zone_SH _ ly regs0 mem0 n tr cl cnt v kz Hcl Hv Hcnt Hv2 LY IMG Hsp Htrlen DPOST Hkz Nrange).
Local Abbreviation tail_ext_ok := (@AGis.tail_ext_ok _ ly regs0 mem0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz Hcl Hv Hcnt Hv2 LY IMG Hsp Htrlen Hbp DPOST Hkz Nrange).
Local Abbreviation at_ST := (@AGis.at_ST _ W ly regs0 mem0 md0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation at_ST2 := (@AGis.at_ST2 _ W ly regs0 mem0 md0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz DPOST).
Local Abbreviation at_S2 := (@AGis.at_S2 _ W ly regs0 mem0 md0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz DPOST).
Local Abbreviation at_RET := (@AGis.at_RET _ W ly regs0 mem0 md0 n cl cnt v jb kz DPOST).
Ltac frame_acc HE :=
match goal with
| MEQ : (forall x : word, ~ WIN1 ?odd (bv_unsigned x) -> ?m1 x = ?mb x), HFx : frame_of ?E ?rs ?m1 ?m2 |- _ =>
let MEQ' := fresh "MEQ" in
assert (MEQ' : forall x : word, ~ WIN1 odd (bv_unsigned x) -> m2 x = mb x)
by (intros x Hx; transitivity (m1 x); [exact (frame_WIN1 odd E rs m1 m2 HE ltac:(vm_compute; reflexivity) HFx x Hx) | exact (MEQ x Hx)]);
clear MEQ HFx; rename MEQ' into MEQ
end.
Local Abbreviation memset_stretch := (@AGis.memset_stretch _ W ly regs0 mem0 n tr cl cnt v jb kz Hcl Hv Hcnt Hjb Hsp Htrlen Hso Hbp DPOST Hkz Nrange).
Variables (B : asyms) (S : astate) (l : list Z) (off : Z).
(* The spin tag of the model's dead shadow-remap branch (AGif0n.malloc_join_t; 12 in this unit, label 449860 in cgif_file). *)
Variable stag : Z.
Hypothesis TS : TfibSyms B.
Hypothesis HTSD : ly_tsd ly = TFIB_TSD.
Hypothesis Hgp : getr regs0 3 = w64 (as_gp B).
Hypothesis Hpres0 : forall a, sp0 - AFSTACK <= a < sp0 -> apresent (w_H W) mem0 a.
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
Local Abbreviation casek_sizes := (@AGis.casek_sizes n kz Hkz Nrange).
Local Abbreviation Kv_is_sptr := (@AGis.Kv_is_sptr ly cl v Hcl B off Hoff_def).
Local Ltac addr_tac :=
cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi];
rewrite ?EaT, ?EaC, ?EaTOP, ?EaSB, ?E2; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, w64, ly_bot, kStackSpan, t_unwinding, t_cache, t_stats, TFIB_IMG_END, UNW_STK, BST_SIZE, AFSTACK, IFRAME, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *;
rewrite ?unsigned_lit_small by zlia; zlia.
Local Ltac denot_tac :=
cbn [sv_denot]; rewrite ?EaT, ?EaC, ?EaTOP, ?EaSB, ?E2; unfold w64, ly_bot, kStackSpan in *;
first [ rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| rewrite Zbv_add_unsigned; f_equal; zlia
| rewrite unsigned_lit_small by zlia; f_equal; zlia
| reflexivity ].
Local Open Scope am_scope.
Let c0 : config := cfg_at tfibsegs A_Allocate regsU mem0 md0.
Hypothesis Hmat0 : mat0 = m_vm_materialized md0.
(* The callee contract of StackDepotPut (AGif0n.if_depot at this walk's allocator), with its post DPOST. *)
Hypothesis HDEP : forall (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (buf : Z),
(forall x : word, DZONE (bv_unsigned x) \/ CZONE ly (bv_unsigned x) -> mem x = mem0 x) ->
getr regs 10 = Z_to_bv 64 buf -> getr regs 11 = Z_to_bv 64 (Z.of_nat (length tr)) ->
getr regs 3 = Z_to_bv 64 (as_gp B) -> getr regs 4 = Z_to_bv 64 TFIB_TP -> YK0s.ret_ok (getr regs 1) ->
(forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W) mem) (buf + 8 * Z.of_nat i) 8 (nth i tr 0)) ->
buf mod 8 = 0 -> ly_stk_lo ly <= buf -> buf + 8 * 30 <= ly_stk_hi ly ->
buf + 8 * 30 <= bv_unsigned (getr regs 2) - DEP_STK \/ bv_unsigned (getr regs 2) <= buf ->
bv_unsigned (getr regs 2) mod 16 = 0 -> ly_stk_lo ly <= bv_unsigned (getr regs 2) - DEP_STK ->
bv_unsigned (getr regs 2) <= ly_stk_hi ly ->
(forall a, bv_unsigned (getr regs 2) - DEP_STK <= a < bv_unsigned (getr regs 2) -> apresent (w_H W) mem a) ->
SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 A_StackDepotPut) mem (seg_rom tfibsegs)) md)
(fun W' c' => W' = W /\ exists z regs' mem' mat,
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md) /\
regs_preserved regs regs' /\
(forall x : word, ~ (bv_unsigned (getr regs 2) - DEP_STK <= bv_unsigned x < bv_unsigned (getr regs 2)) ->
~ DZONE (bv_unsigned x) -> mem' x = mem x) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
DPOST z mem').
(* DPOST answers the model's depot query (AGif0n.if_dpost_aok). *)
Hypothesis HDAOK : forall z m, DPOST z m -> aok S (KDepot tr) z.
(* Speed (CZONE_untouched): lia's cost grows with the disjunctions and the size of its context.  The proof clears the
   facts the address arithmetic does not use, keeps only the linear part of the zone3 facts, turns each apart fact
   [P -> ~ Q] into [~ Q] or [~ P] at the case's range, keeps the disjunctive facts in a bag [Hide _] out of lia's sight,
   splits [~ WIN] into its windows, and gives each goal to lia with no disjunctive fact, then with each one alone, then
   with all of them. *)
Local Ltac zlia2 := ceil; unfold zone3, zone3cases, in_app, app_addr, in_band_rw, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, ASAN_CEIL in *; lia.
Local Ltac apart Ha := repeat match goal with H : ?P -> ~ ?Q |- _ =>
  first [ specialize (H ltac:(clear - Ha; zlia2))
        | assert (~ P) by (let Hp := fresh "Hp" in intros Hp; apply (H Hp); clear - Ha; zlia2); clear H ] end.
Local Definition Hide (P : Prop) : Prop := P.
Local Ltac bag_add H := match goal with HB : Hide ?R |- _ => lazymatch type of H with ?P =>
  let B' := fresh "HBAG" in assert (B' : Hide (P /\ R)) by exact (conj H HB); clear H HB end end.
Local Ltac bag_up :=
  let B0 := fresh "HBAG" in assert (B0 : Hide True) by exact I;
  repeat match goal with
  | H : ~ _ |- _ => bag_add H
  | H : _ \/ _ |- _ => bag_add H
  | H : ?P |- _ => lazymatch P with Hide _ => fail | forall _ : _, _ => fail | context [_ \/ _] => bag_add H end
  end.
Local Ltac try_each B tac :=
  lazymatch type of B with
  | Hide (?P /\ ?R) => first [ let H := fresh "Hd" in assert (H : P) by exact (proj1 B); tac
                             | let B' := fresh "HB" in assert (B' : Hide R) by exact (proj2 B); try_each B' tac ]
  end.
Local Ltac unbag := match goal with HB : Hide ?R |- _ => let H := fresh "Hd" in assert (H : R) by exact HB; clear HB end;
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
Local Ltac solve1 := first [ zlia2 | match goal with HB : Hide _ |- _ => try_each HB zlia2 end | unbag; zlia2 ].
Local Ltac split_neg := lazymatch goal with |- ~ _ => let Hw := fresh "Hw" in intros Hw; repeat match type of Hw with _ \/ _ => destruct Hw as [Hw|Hw] end | _ => idtac end.
(* The walk's writes avoid the constant cells' zone (AGix.CZONE_untouched of the released route). *)
Lemma CZONE_untouched : forall odd a, CZONE ly a ->
0 <= a < 2 ^ 64 /\ ~ WIN odd a /\ ~ (Kv + RZ <= a < Kv + RZ + n) /\ ~ (SUv <= a < SUv + N8D / 8) /\
~ (sp0 - 128 - DEP_STK <= a < sp0 - 128) /\ ~ (ly_NB ly <= a < ly_NB ly + kNodesBlockSize) /\ ~ (ly_SB ly <= a < ly_SB ly + kStoreBlockSize).
Proof.
try clear Hcf. try clear HPB250. try clear HDEP. try clear HDAOK. try clear SEED. try clear PBUF0. try clear HKpres. try clear HSKpres. try clear Hpres0. try clear Hj0. try clear Hj1. try clear Hj2. try clear Hj3. try clear Hj4. try clear Hjb_def. try clear Hcache. try clear Hcnt_def. try clear Hcl_def. try clear Hcl_class. try clear Hgp. try clear Htp. try clear Hn. try clear Hra. try clear Hra4096. try clear TS. try clear HTSD. try clear Hmat0.
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
unfold zone3 in F1, F7, NBhi, SBhi. destruct F1 as (F1a & F1b & _). destruct F7 as (F7a & F7b & _). destruct NBhi as (NBa & NBb & _). destruct SBhi as (SBa & SBb & _).
unfold CZONE, WIN, WINT, PBW, TFIB_TSD in *. numconst. unfold T, sp0 in *.
destruct Ha as [Ha|[Ha|[Ha|[Ha|[Ha|Ha]]]]].
- clear SI1 SI2 SI3 TNB TSB CNB CSB CP CT PT DT DP DNB DSB DSTK DH TH CH NH BH. apart Ha. bag_up. repeat split; split_neg; solve1.
- clear SI1 SI2 SI3 TNB TSB CNB CSB CP CT PT DT DP DNB DSB DSTK DH TI CI NI BI. apart Ha. bag_up. repeat split; split_neg; solve1.
- clear SI2 SI3 CNB CSB CP CT DT DP DNB DSB DSTK DH TI CI CH NI NH BI BH. apart Ha. bag_up. repeat split; split_neg; solve1.
- clear SI1 SI2 TNB TSB PT DT DP DNB DSB DSTK DH TI TH CI NI NH BI BH. apart Ha. bag_up. repeat split; split_neg; solve1.
- clear SI1 SI2 SI3 TNB TSB CNB CSB CP CT PT DT DP DNB DSB DSTK DH TH CH NH BH. apart Ha. bag_up. repeat split; split_neg; solve1.
- clear SI2 TNB TSB CNB CSB CP CT PT TI TH CI CH NI NH BI BH. apart Ha. bag_up. repeat split; split_neg; solve1.
Qed.
(* The depot call as the segment files use it (the released D1w), from HDEP. *)
Lemma D1w : forall (regs : bvmap 5 word) (mem : word -> option byte) (md : Model),
getr regs 10 = Z_to_bv 64 BPv -> getr regs 11 = Z_to_bv 64 (Z.of_nat (length tr)) ->
getr regs 3 = getr regs0 3 -> getr regs 4 = Z_to_bv 64 TFIB_TP -> getr regs 1 = Z_to_bv 64 0x322a0 ->
bv_unsigned (getr regs 2) = sp0 - 128 ->
(forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W) mem) (BPv + 8 * Z.of_nat i) 8 (nth i tr 0)) ->
(forall a, sp0 - AFSTACK <= a < sp0 -> apresent (w_H W) mem a) ->
(forall x : word, ~ WIN false (bv_unsigned x) -> mem x = mem0 x) ->
SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 A_StackDepotPut) mem (seg_rom tfibsegs)) md)
(fun W' c' => W' = W /\ exists z regs' mem' mat,
c' = mkCfg (mkst regs' (Z_to_bv 64 0x322a0) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md) /\
regs_preserved regs regs' /\
(forall x : word, ~ (sp0 - 128 - DEP_STK <= bv_unsigned x < sp0 - 128) -> ~ DZONE (bv_unsigned x) -> mem' x = mem x) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
DPOST z mem').
Proof.
intros regs mem md R10 R11 R3 R4 R1 Rsp BUF PRES MEQ.
pose proof Hsp as (S1 & S2 & S3 & S4). pose proof Hbp as (B1 & B2 & B3).
eapply SRr_mono.
{ apply (HDEP regs mem md BPv).
- intros x [Hx|Hx]; apply MEQ; [exact (proj1 (DZONE_disj false _ Hx)) | exact (proj1 (proj2 (CZONE_untouched false _ Hx)))].
- exact R10.
- exact R11.
- rewrite R3, Hgp. reflexivity.
- exact R4.
- rewrite R1. apply ret_ok_even. reflexivity.
- exact BUF.
- exact B3.
- unfold AFSTACK in *. zlia.
- exact B2.
- right. rewrite Rsp. zlia.
- rewrite Rsp. apply Z.mod_divide; [zlia|]. pose proof S4 as S4'. apply Z.mod_divide in S4' as [q Hq]; [|zlia]. exists (q - 8). zlia.
- rewrite Rsp. unfold DEP_STK, AFSTACK in *. zlia.
- rewrite Rsp. zlia.
- rewrite Rsp. intros a Ha. apply PRES. unfold DEP_STK, AFSTACK in *. zlia. }
intros W' c' _ (-> & z & regs' & mem' & mat & -> & RP & FR & PR' & DP). split; [reflexivity|].
exists z, regs', mem', mat. split; [rewrite R1; reflexivity|]. split; [exact RP|]. split; [|split; [exact PR' | exact DP]].
intros x N1 N2. apply FR; [rewrite Rsp; exact N1 | exact N2].
Qed.
(* The segment lemmas take the section's hypotheses; [seg] applies one and discharges them from the context. *)
Local Ltac seg L := eapply L; first [eassumption | exact D1w].
(* The cf = 0 post (AGc0.at_RET0: at_RET's clauses with the block's bytes kept in place of the fill) gives at_RETw. *)
Lemma at_RET0_w : forall odd z W' c', AGc0.at_RET0 W ly regs0 mem0 md0 n cl cnt v jb kz DPOST odd z W' c' ->
at_RETw W ly regs0 mem0 md0 n cl cnt v jb kz DPOST odd z W' c'.
Proof.
intros odd z W' c' H. unfold AGc0.at_RET0, at_RETw in *. cbv zeta in *.
destruct H as (HW & regs' & mem' & mat & Hc & R10 & RCS & DD & MEQF & PRS & PRW & V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11).
split; [exact HW|]. exists regs', mem', mat. repeat (split; [assumption|]). exact V10.
Qed.
(* From the cache join to Allocate's ret: the model's pop, the depot query and the store of the new chunk. *)
Theorem tail_inner : forall c1, at_ST SS_JN W c1 ->
amreal tfibsegs (malloc_join_t stag n tr cl S) W c1
(fun r W' c' => exists odd z, r = (ck_user (new_chunk cl off n), st_final S cl l off n tr z) /\
(odd = true <-> n mod 8 <> 0) /\ at_RETw W ly regs0 mem0 md0 n cl cnt v jb kz DPOST odd z W' c').
Proof.
intros c1 HJ.
pose proof casek_sizes as (L & RS & R8 & NP & FP & NS & RQ). pose proof RZ_facts as (_ & _ & _ & RF4 & _).
unfold malloc_join_t. rewrite bind_assoc_eq. eapply amreal_pure; [exact (pop_hit S cl l off Hcache)|]. eapply amreal_pure; [reflexivity|].
unfold malloc_K_t. cbv beta iota.
change {| ck_beg := PPrim (region_off cl + off); ck_req := n; ck_state := CAllocated |} with (new_chunk cl off n).
replace (needs_remap (ck_n (new_chunk cl off n))) with false.
2:{ symmetry. apply Z.leb_gt. unfold new_chunk, ck_n. cbn [ck_req]. rewrite RQ. unfold kClearShadowMmapThreshold.
apply Z.div_lt_upper_bound; zlia. }
unfold depot_put. rewrite bind_assoc_eq. unfold bind at 1. unfold askz. cbn [ibind amreal].
eapply SRr_bind. { seg AGip.segC2. }
intros W1 c1' Hle1 HPD.
eapply SRr_mono. { seg AGiq.segD. }
intros W2 c2 Hle2 [z HPD2]. exists z.
split. { destruct HPD2 as (_ & ms2 & mat2 & E2' & regs2 & mem2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & HDP). exact (HDAOK _ _ HDP). }
assert (FIN : forall s', s' = depot_after z tr (st_popped S cl l) ->
amreal tfibsegs ((ret () ;; modify (fun s : astate => set_chunks (upd_chunk (st_chunks s) (new_chunk cl off n)) s) ;;
ret (ck_user (new_chunk cl off n))) s') W2 c2
(fun r W' c' => exists odd z, r = (ck_user (new_chunk cl off n), st_final S cl l off n tr z) /\
(odd = true <-> n mod 8 <> 0) /\ at_RETw W ly regs0 mem0 md0 n cl cnt v jb kz DPOST odd z W' c')).
{ intros s' ->. eapply amreal_pure; [reflexivity|]. eapply amreal_pure; [reflexivity|]. cbn [amreal ret].
change (set_chunks (upd_chunk (st_chunks (depot_after z tr (st_popped S cl l))) (new_chunk cl off n)) (depot_after z tr (st_popped S cl l)))
with (st_final S cl l off n tr z).
destruct (Z.eq_dec (n mod 8) 0) as [H8|H8]; destruct Hcf as [Hcf0|Hcf1].
- eapply SRr_bind; [seg AGiq.seg2a_even|]. intros W3 c3 _ H3.
eapply SRr_mono; [seg AGc1.seg2cf0_even|]. intros W' c' _ HR.
exists false, z. split; [reflexivity|]. split; [split; [intros E; discriminate E | intros X; exfalso; exact (X H8)] | exact (at_RET0_w _ _ _ _ HR)].
- eapply SRr_bind; [seg AGiq.seg2a_even|]. intros W3 c3 _ H3.
eapply SRr_bind; [seg AGiq.seg2b_even|]. intros W4 c4 _ H4.
eapply SRr_mono; [seg AGiq.seg2c_even|]. intros W' c' _ HR.
exists false, z. split; [reflexivity|]. split; [split; [intros E; discriminate E | intros X; exfalso; exact (X H8)] | exact (at_RET_w _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HR)].
- eapply SRr_bind; [seg AGir.seg2a_odd|]. intros W3 c3 _ H3.
eapply SRr_mono; [seg AGc1.seg2cf0_odd|]. intros W' c' _ HR.
exists true, z. split; [reflexivity|]. split; [split; [intros _; exact H8 | intros _; reflexivity] | exact (at_RET0_w _ _ _ _ HR)].
- eapply SRr_bind; [seg AGir.seg2a_odd|]. intros W3 c3 _ H3.
eapply SRr_bind; [seg AGir.seg2b_odd|]. intros W4 c4 _ H4.
eapply SRr_mono; [seg AGir.seg2c_odd|]. intros W' c' _ HR.
exists true, z. split; [reflexivity|]. split; [split; [intros _; exact H8 | intros _; reflexivity] | exact (at_RET_w _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HR)]. }
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
Unshelve. all: first [exact DPOST | exact mat0 | exact regsU | exact B | exact S | exact l | exact off | exact (fun _ => True)].
Qed.
(* The hit-g walk from Allocate's entry: the machine post at Allocate's ret (AGis.at_RET) for the model's result. *)
Theorem hitg_inner : amreal tfibsegs (malloc_join_t stag n tr cl S) W c0
(fun r W' c' => exists odd z, r = (ck_user (new_chunk cl off n), st_final S cl l off n tr z) /\
(odd = true <-> n mod 8 <> 0) /\ at_RETw W ly regs0 mem0 md0 n cl cnt v jb kz DPOST odd z W' c').
Proof.
eapply amreal_SRr_pre.
{ replace c0 with cfg0 by (subst c0 cfg0; unfold cfg_at; rewrite Hmat0, with_vm_backing_id; reflexivity). seg AGip.seg1J. }
intros W1 c1 _ HJ. pose proof (proj1 HJ) as EW. subst W1. exact (tail_inner c1 HJ).
Unshelve. all: first [exact DPOST | exact mat0 | exact regsU | exact B | exact S | exact l | exact off | exact (fun _ => True)].
Qed.
End e.
End d.
