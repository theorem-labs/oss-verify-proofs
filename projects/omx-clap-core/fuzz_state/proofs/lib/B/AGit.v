(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/AGit.v (a working branch ced28ed2383, file sha256 601cac4fd465) onto omx-clap-core/fuzz_state's asan-ubsan image (fuzz_state.asan-ubsan, pinned sha256 5ac5ce0954f8; addresses read from its unstripped build b1566a1ca816); module paths changed; its 1 image addresses moved by code-verified function pairs (2 port_addr_check 16f8a030c869 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py); no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10-29: the tactic redefinition is #[local], as installed c5 a working branch fec848885a7 (a Theorem Labs lane gs8, b5ba9853e26). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YB1q YF0l YF0m YF0x YFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1w YE3d YFhy AGhy AGis AGhz AGi4.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
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
Hypothesis Hra : YK0s.ret_ok (getr regs0 1).
Hypothesis Hra4096 : 4096 <= bv_unsigned (getr regs0 1).
Hypothesis Hsp : ly_stk_lo ly + AFSTACK <= sp0 /\ ly_bot ly < sp0 /\ sp0 <= ly_stk_hi ly /\ sp0 mod 16 = 0.
Hypothesis Htrlen : (1 <= length tr <= 30)%nat.
Hypothesis Hso : sp0 <= SOv /\ SOv + 16 <= ly_stk_hi ly /\ SOv mod 8 = 0.
Hypothesis Hbp : sp0 <= BPv /\ BPv + 8 * 30 <= ly_stk_hi ly /\ BPv mod 8 = 0.
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
Hypothesis TS : TfibSyms B.
Hypothesis HTSD : ly_tsd ly = TFIB_TSD.
Hypothesis HARm : ARm B ly S (aview tfibsegs (w_H W) mem0).
Hypothesis Hgp : getr regs0 3 = w64 (as_gp B).
Hypothesis Hpres0 : forall a, sp0 - AFSTACK <= a < sp0 -> apresent (w_H W) mem0 a.
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
Local Ltac close_ST En HEn HS memB MEQ MEQW PRESW BUFW :=
apply SRr_ret; split; [reflexivity|];
lazymatch goal with |- context [mkCfg ?msf (with_vm_backing _ ?matf _)] => exists msf, matf, En end;
split; [reflexivity|]; split; [exact HEn|]; split; [exact HS|];
pose proof derived_ranges as DR'; pose proof high_facts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9); pose proof Kv_range as HKR;
pose proof (lo_top ly LY) as (T1' & T2' & T3' & T4' & T5' & T6' & T7'); pose proof Hsp as (Hlo_ & Hbot_ & Hhi_ & Hal_);
split; [|split];
[ intros x Hx; rewrite (MEQ x) by (intros H1; apply Hx, WIN1_WIN, H1); apply MEQW, Hx
| intros a Ha;
eapply (st_ok_window_apresent_off (w_H W) En _ _ 1 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn 2%nat (ltHAV 2 eq_refl)), E2; addr_tac | off_by ltac:(addr_tac) ]
| intros i Hi; pose proof tr_length as LEN;
eapply val_mem_frame; [|eapply val_mem_addr; [exact (BUFW i Hi) | clear - Hi LEN Hlo_ Hhi_ Hbp T4' T7'; addr_tac]];
intros k Hk; apply MEQ;
assert (Hx : ly_stk_lo ly <= BPv + 8 * Z.of_nat i + Z.of_nat k < ly_stk_hi ly) by (clear - Hi Hk LEN Hlo_ Hhi_ Hbp; unfold AFSTACK in *; zlia);
destruct (F9 _ Hx) as [N1 N2]; pose proof (HCdisj _ Hx) as HC;
clear - Hi Hk LEN Hbp DR' HKR N1 N2 HC T7' T4' Hlo_ Hhi_ F1 F2 F3 F4 F5 F6 F7 F8;
unfold WIN1, WINT, PBW in *; numconst; rewrite unsigned_lit_small by zlia; zlia ].
Lemma segJ : forall W0 c, at_ST MS_AFTER W0 c -> SRr tfibsegs W0 c (at_ST SS_JN).
Proof.
intros W0 c (-> & ms & mat & En & -> & HEn & HS & MEQW & PRESW & BUFW). pose proof Hwx_tfa as Hwx.
pose proof Hsp as (Hlo & Hbot & Hhi & Hal). pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
pose proof derived_ranges as DR. pose proof high_facts as LF. pose proof RZ_facts as (RF1 & RF2 & RF3 & RF4 & RF5 & RF6). pose proof NDv_facts as (ND1 & ND2 & ND3 & ND4 & ND5).
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, t_cache, t_unwinding in DR, LF.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) En _ _ HS eq_refl) as Hshape; cbn [ss_pc] in Hshape;
lazymatch type of Hshape with _ = mkst _ (Z_to_bv 64 (ss_pc ?s)) _ _ => let p := eval vm_compute in (ss_pc s) in change (ss_pc s) with p in Hshape | _ => idtac end.
rewrite Hshape in HS. rewrite Hshape. set (mem1 := ms_mem ms) in *.
assert (MEQ : forall x : word, ~ WIN1 false (bv_unsigned x) -> mem1 x = mem1 x) by (intros; reflexivity).
srr_run_to_sh tfibtbl_rtA_ok HS 0x367b8. frame_acc HEn.
forget_regs HS 103%nat ([1; 5; 6; 7; 14; 15; 16; 17; 19; 20; 28; 29; 30; 31]%bv : list (bv 5)).
apply (YP03.st_ok_prune tfibsegs _ _ _ [] []) in HS.
lazymatch type of HS with st_ok _ _ ?ss _ => replace ss with SS_JN in HS by (vm_compute; reflexivity) end.
lazymatch type of HS with st_ok _ ?E2 _ _ => set (EnE := E2) in HS end.
assert (HEnE : forall j, (j < aHAV)%nat -> ew EnE j = ew E0 j) by (intros j Hj; subst EnE; unfold aHAV in Hj; rewrite ew_havoc_old by zlia; apply HEn; exact Hj).
close_ST EnE HEnE HS mem1 MEQ MEQW PRESW BUFW.
Qed.
End e.
End d.
