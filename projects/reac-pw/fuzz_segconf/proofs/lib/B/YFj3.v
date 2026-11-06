(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AFj3.v, with its module paths changed, names TfibSyms -> CmdBSyms and its addresses moved to plugin-hostd/fuzz_command's ASan build. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_command/lib/A/AFj3.v (donor image sha256 c0661b96b5bd), with its module paths changed, names CmdBSyms -> SegBSyms and its addresses moved to reac-pw/fuzz_segconf's ASan build. *)
(* Modified by Theorem Labs, 2026-10: the image-B copy (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca) of lib/A/AFj3.v, derived mechanically (derive_y.py b7b132fb12a7; every changed numeral checked against alreloc.py a5c53bb2bed4 and against image B), with its module paths changed (lib/A to lib/B) and its addresses moved to reac-pw/fuzz_segconf's ASan+UBSan build. The comments are the A file's. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.

From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.

From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG06 YG07 YG03.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YB1v YB1q YF0l YF0m YF0x YFl0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YB1w YE3d YFhy YFi1 YFj6 YFi2.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
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
t_cache, t_unwinding, t_stats, MALLOC_IN_STK, IFRAME, TFIB_IMG_END, TFIB_IMG_LO, kLowShadowBeg, UNW_STK, BST_SIZE, DEP_STK in *.
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
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (n : Z) (ch : list Z).
Variables (cl cnt v csz j0 jb j1 j2 j3 j4 : Z).
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let pT : Z := bv_unsigned (getr regs0 11).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Local Abbreviation RZ := (@YFj6.RZ).
Local Abbreviation NPv := (@YFj6.NPv n).
Local Abbreviation R8v := (@YFj6.R8v n).
Local Abbreviation N8D := (@YFj6.N8D n).
Local Abbreviation Pv := (@YFj6.Pv ly cl).
Local Abbreviation PVv := (@YFj6.PVv ly cl cnt).
Local Abbreviation Kv := (@YFj6.Kv ly cl v).
Local Abbreviation SHBv := (@YFj6.SHBv).
Local Abbreviation SKv := (@YFj6.SKv ly cl v).
Local Abbreviation SSLOTv := (@YFj6.SSLOTv ly cl).
Local Abbreviation PBv := (@YFj6.PBv ly n cl v).
Local Abbreviation Uv := (@YFj6.Uv ly cl v).
Local Abbreviation SUv := (@YFj6.SUv ly cl v).
Local Abbreviation FILv := (@YFj6.FILv n).
Local Abbreviation NDv := (@YFj6.NDv n).
Local Abbreviation tr := (@YFj6.tr ch).
Local Abbreviation XW := (@YFj6.XW ly n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation E0 := (@YFj6.E0 ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaT := (@YFj6.EaT ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaC := (@YFj6.EaC ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaSB := (@YFj6.EaSB ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaTOP := (@YFj6.EaTOP ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation Er := (@YFj6.Er ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation E2 := (@YFj6.E2 ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation E1 := (@YFj6.E1 ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation E8 := (@YFj6.E8 ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation E10 := (@YFj6.E10 ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation E4 := (@YFj6.E4 ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaP := (@YFj6.EaP ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaR8 := (@YFj6.EaR8 ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaK := (@YFj6.EaK ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaSK := (@YFj6.EaSK ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaSSLOT := (@YFj6.EaSSLOT ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaPB := (@YFj6.EaPB ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaPV := (@YFj6.EaPV ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaRZ := (@YFj6.EaRZ ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaU := (@YFj6.EaU ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaSU := (@YFj6.EaSU ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaFIL := (@YFj6.EaFIL ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaNP := (@YFj6.EaNP ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaND := (@YFj6.EaND ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation WINT := (@YFj6.WINT ly cl).
Local Abbreviation PBW := (@YFj6.PBW ly n cl v).
Local Abbreviation WIN := (@YFj6.WIN ly regs0 n cl v).
Local Abbreviation win_in_WIN := (@YFj6.win_in_WIN ly regs0 n cl v).
Hypotheses (Hcl : 1 <= cl <= 31) (Hv : 0 <= v /\ 16 * v + 2 ^ 16 <= 2 ^ 32) (Hcnt : 1 <= cnt <= 16) (Hjb : 0 <= jb <= 255).
Hypothesis Hv2 : v mod 2 = 0.
Hypothesis LY : layout_ok ly.
Hypothesis IMG : img_cover ly.
Hypothesis Hn : getr regs0 10 = w64 n.
Hypothesis Htp : getr regs0 4 = w64 TFIB_TP.
Hypothesis Hra : YK0s.ret_ok (getr regs0 1).
Hypothesis Hra4096 : 4096 <= bv_unsigned (getr regs0 1).
Hypothesis Hsp : ly_stk_lo ly + MALLOC_IN_STK <= sp0 /\ sp0 - IFRAME <= pT /\ sp0 <= ly_stk_hi ly /\ sp0 mod 16 = 0.
(* the caller's trace object at p = a1 (RtDDefs.v amalloc_inner_realizes) *)
Hypothesis Hch : (1 <= length ch <= 30)%nat /\ pT mod 8 = 0 /\ pT + 16 + 8 * 30 <= ly_stk_hi ly /\ astrace_at tfibsegs W mem0 pT ch.
Local Abbreviation HCdisj := (@YFj6.HCdisj _ W ly regs0 mem0 ch v Hv LY Hch).
Local Abbreviation DZONE := (@YFj6.DZONE ly).
Variable DPOST : Z -> (word -> option byte) -> Prop.
Local Abbreviation HC_NB := (@YFj6.HC_NB _ ly LY).
Hypothesis HKpres : forall a, Kv <= a < Kv + RZ + R8v -> apresent (w_H W) mem0 a.
Hypothesis HSKpres : forall a, SKv <= a < SKv + (RZ + R8v) / 8 -> apresent (w_H W) mem0 a.
Hypothesis HPB250 : NPv mod 8 <> 0 -> val_mem tfibsegs (mrestrict (w_H W) mem0) PBv 1 250.
Local Abbreviation HCX := (@YFj6.HCX _ ly LY).
Local Abbreviation tr_length := (@YFj6.tr_length W ly regs0 mem0 ch Hch).
Local Abbreviation trace_obj := (@YFj6.trace_obj W ly regs0 mem0 n ch v Hch DPOST).
Local Abbreviation Kv_range := (@YFj6.Kv_range W ly regs0 mem0 n ch cl v Hcl Hv Hv2 Hch DPOST).
Local Abbreviation high_facts := (@YFj6.high_facts _ W ly regs0 mem0 n ch v Hv LY IMG Hch DPOST).
Local Abbreviation blocks_facts := (@YFj6.blocks_facts _ ly LY IMG).
Local Abbreviation off_T := (@YFj6.off_T _ W ly regs0 mem0 n ch v Hv LY IMG Hch DPOST).
Local Abbreviation off_C := (@YFj6.off_C _ W ly regs0 mem0 n ch v Hv LY IMG Hch DPOST).
Local Abbreviation off_NB := (@YFj6.off_NB _ ly LY IMG).
Local Abbreviation off_SB := (@YFj6.off_SB _ ly LY IMG).
Ltac off_by tac :=
first [ apply off_img_high; tac
| apply off_T; unfold kThreadObjSize; tac
| apply off_C; tac
| apply off_NB; unfold kNodesBlockSize; tac
| apply off_SB; unfold kStoreBlockSize; tac
| unfold off_img; unfold TFIB_IMG_LO; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; tac ].
Hypothesis Nrange : 0 <= n <= 48.
Local Abbreviation K0_facts := (@YFj6.K0_facts n Nrange).
Local Abbreviation RZ_num := (@YFj6.RZ_num n Nrange).
Ltac numconst ::= (ceil; unfold zone3, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize,
t_cache, t_unwinding, t_stats, MALLOC_IN_STK, IFRAME, TFIB_IMG_END, TFIB_IMG_LO, kLowShadowBeg, UNW_STK, BST_SIZE, DEP_STK in * ); try pose proof RZ_num as RZN.
Local Abbreviation derived_ranges := (@YFj6.derived_ranges _ W ly regs0 mem0 n ch cl cnt v Hcl Hv Hcnt Hv2 LY IMG Hch DPOST Nrange).
Hypothesis Hcl_def : cl = class_id (R8v + RZ).
Local Abbreviation CLk := (@YFj6.CLk).
Local Abbreviation CLk_E := (@YFj6.CLk_E W ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 Hch DPOST Nrange Hcl_def).
Local Abbreviation WIN1 := (@YFj6.WIN1 ly regs0 n cl v).
Local Abbreviation WIN1_WIN := (@YFj6.WIN1_WIN W ly regs0 mem0 n ch cl v Hch DPOST).
Local Abbreviation WIN_odd := (@YFj6.WIN_odd W ly regs0 mem0 n ch cl cnt v jb Hcl Hv Hcnt Hjb Hsp Hch DPOST Nrange).
Local Abbreviation WIN1_odd := (@YFj6.WIN1_odd W ly regs0 mem0 n ch cl cnt v jb Hcl Hv Hcnt Hjb Hsp Hch DPOST Nrange).
Local Abbreviation WSKEL := (@YFj6.WSKEL).
Local Abbreviation WSKEL1 := (@YFj6.WSKEL1).
Local Abbreviation win_sub := (@YFj6.win_sub).
Local Abbreviation win_sub_sound := (@YFj6.win_sub_sound W ly regs0 mem0 n ch v Hv Hch DPOST).
Local Abbreviation WSKEL_WIN := (@YFj6.WSKEL_WIN _ W ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 Hcl Hv Hcnt Hv2 LY IMG Hch DPOST Nrange).
Local Abbreviation WSKEL1_WIN1 := (@YFj6.WSKEL1_WIN1 _ W ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 Hcl Hv Hcnt Hv2 LY IMG Hch DPOST Nrange).
Local Abbreviation windows_WIN := (@YFj6.windows_WIN _ W ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 Hcl Hv Hcnt Hv2 LY IMG Hch DPOST Nrange).
Local Abbreviation windows_WIN1 := (@YFj6.windows_WIN1 _ W ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 Hcl Hv Hcnt Hv2 LY IMG Hch DPOST Nrange).
Local Abbreviation frame_WIN1 := (@YFj6.frame_WIN1 _ W ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 Hcl Hv Hcnt Hv2 LY IMG Hch DPOST Nrange).
Local Abbreviation WIN_not_high := (@YFj6.WIN_not_high _ W ly regs0 mem0 n ch cl cnt v Hcl Hv Hcnt Hv2 LY IMG Hsp Hch DPOST Nrange).
Variables (mat0 : list word).
Let H0 := w_H W.
Variables (regsI : bvmap 5 word).
(* the run starts with regsI: regs0 with sp = sp0 - IFRAME *)
Hypotheses (RIo : forall r : bv 5, r <> 2%bv -> getr regsI r = getr regs0 r) (RI2 : getr regsI 2 = w64 (sp0 - IFRAME)).
Let cfg0 : config := mkCfg (mkst regsI (w64 PC_asan_malloc) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis SEED : st_ok tfibsegs E0 SS0K (restrict (w_H W) (mkst regsI (w64 PC_asan_malloc) mem0 (seg_rom tfibsegs))).
Local Abbreviation all_disjoint_of_forall := (@YFj6.all_disjoint_of_forall).
Local Abbreviation kept_of_frame := (@YFj6.kept_of_frame W ly regs0 mem0 n ch v Hch DPOST).
Local Abbreviation SKEL_TAIL := (@YFj6.SKEL_TAIL).
Local Abbreviation stack_ivs := (@YFj6.stack_ivs _ W ly regs0 mem0 n ch v Hv LY Hsp Hch DPOST).
Local Abbreviation stack_ivs2 := (@YFj6.stack_ivs2 _ W ly regs0 mem0 n ch v Hv LY Hsp Hch DPOST).
Local Abbreviation trace_ivs := (@YFj6.trace_ivs _ W ly regs0 mem0 n ch v Hv LY Hsp Hch DPOST).
Local Abbreviation DZONE_disj := (@YFj6.DZONE_disj _ W ly regs0 mem0 n ch cl cnt v Hcl Hv Hcnt Hv2 LY IMG Hsp Hch DPOST Nrange).
Local Abbreviation RFACTS := (@YFj6.RFACTS ly regs0 n cl v).
Local Abbreviation zone_lit := (@YFj6.zone_lit _ W ly regs0 mem0 n ch cl cnt v Hcl Hv Hcnt Hv2 LY IMG Hsp Hch DPOST Nrange).
Local Abbreviation zone_T := (@YFj6.zone_T _ W ly regs0 mem0 n ch cl cnt v Hcl Hv Hcnt Hv2 LY IMG Hsp Hch DPOST Nrange).
Local Abbreviation zone_C := (@YFj6.zone_C _ W ly regs0 mem0 n ch cl cnt v Hcl Hv Hcnt Hv2 LY IMG Hsp Hch DPOST Nrange).
Local Abbreviation zone_K := (@YFj6.zone_K _ W ly regs0 mem0 n ch cl cnt v Hcl Hv Hcnt Hv2 LY IMG Hsp Hch DPOST Nrange).
Local Abbreviation zone_SH := (@YFj6.zone_SH _ W ly regs0 mem0 n ch cl cnt v Hcl Hv Hcnt Hv2 LY IMG Hsp Hch DPOST Nrange).
Local Abbreviation tail_ext_ok := (@YFj6.tail_ext_ok _ W ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 Hcl Hv Hcnt Hv2 LY IMG Hsp Hch DPOST Nrange).
Local Abbreviation at_ST := (@YFj6.at_ST _ W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation at_ST2 := (@YFj6.at_ST2 _ W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 DPOST).
Local Abbreviation at_S2 := (@YFj6.at_S2 _ W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 DPOST).
Local Abbreviation at_RET := (@YFj6.at_RET _ W ly regs0 mem0 md0 n cl cnt v jb DPOST).
Ltac frame_acc HE :=
match goal with
| MEQ : (forall x : word, ~ WIN1 ?odd (bv_unsigned x) -> ?m1 x = ?mb x), HFx : frame_of ?E ?rs ?m1 ?m2 |- _ =>
let MEQ' := fresh "MEQ" in
assert (MEQ' : forall x : word, ~ WIN1 odd (bv_unsigned x) -> m2 x = mb x)
by (intros x Hx; transitivity (m1 x); [exact (frame_WIN1 odd E rs m1 m2 HE ltac:(vm_compute; reflexivity) HFx x Hx) | exact (MEQ x Hx)]);
clear MEQ HFx; rename MEQ' into MEQ
end.
Local Abbreviation memset_stretch := (@YFj6.memset_stretch _ W ly regs0 mem0 n ch cl cnt v jb Hcl Hv Hcnt Hjb Hsp Hch DPOST Nrange).
Variables (B : asyms) (S : astate) (l : list Z) (off : Z).
Hypothesis TS : SegBSyms B.
Hypothesis HTSD : ly_tsd ly = TFIB_TSD.
Hypothesis HARm : ARm B ly S (aview tfibsegs (w_H W) mem0).
Hypothesis Hgp : getr regs0 3 = w64 (as_gp B).
Hypothesis Hpres0 : forall a, sp0 - MALLOC_IN_STK <= a < sp0 - IFRAME -> apresent (w_H W) mem0 a.
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
Local Abbreviation case0_sizes := (@YFj6.case0_sizes n Nrange).
Local Abbreviation Kv_is_sptr := (@YFj6.Kv_is_sptr ly cl v Hcl B off Hoff_def).
Local Ltac addr_tac :=
cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi];
rewrite ?EaT, ?EaC, ?EaTOP, ?EaSB, ?E2; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, w64, ly_bot, kStackSpan, t_unwinding, t_cache, t_stats, TFIB_IMG_END, UNW_STK, BST_SIZE, MALLOC_IN_STK, IFRAME, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *;
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
pose proof (lo_top ly LY) as (T1' & T2' & T3' & T4' & T5' & T6' & T7'); pose proof Hsp as (Hlo_ & Hpl_ & Hhi_ & Hal_);
pose proof Hch as (_ & _ & Hpt_ & _);
split; [|split];
[ intros x Hx; rewrite (MEQ x) by (intros H1; apply Hx, WIN1_WIN, H1); apply MEQW, Hx
| intros a Ha; eapply (st_ok_window_apresent_off (w_H W) En _ _ 1 _ a HS);
[reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn 2%nat (ltHAV 2 eq_refl)), E2; addr_tac | off_by ltac:(addr_tac)]
| intros i Hi; pose proof tr_length as LEN;
eapply val_mem_frame; [|exact (BUFW i Hi)];
intros k Hk; apply MEQ;
assert (Hx : ly_stk_lo ly <= pT + 16 + 8 * Z.of_nat i + Z.of_nat k < ly_stk_hi ly) by (clear - Hi Hk LEN Hlo_ Hpl_ Hpt_; unfold IFRAME, MALLOC_IN_STK in *; zlia);
destruct (F9 _ Hx) as [N1 N2]; pose proof (HCdisj _ Hx) as HC;
clear - Hi Hk LEN DR' HKR N1 N2 HC T7' T4' Hlo_ Hpl_ Hpt_ F1 F2 F3 F4 F5 F6 F7 F8;
unfold WIN1, WINT, PBW, IFRAME in *; numconst; rewrite unsigned_lit_small by zlia; zlia ].
Lemma segA : SRr tfibsegs W cfg0 (at_ST KS_B).
Proof.
pose proof Hwx_tfa as Hwx. pose proof SEED as HS.
pose proof Hsp as (Hlo & Hbot & Hhi & Hal).
pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
unfold cfg0.
set (En1 := E0) in HS.
assert (HEn1 : forall k, (k < aHAV)%nat -> ew En1 k = ew E0 k) by (intros; reflexivity).
assert (MEQ : forall x : word, ~ WIN1 false (bv_unsigned x) -> mem0 x = mem0 x) by (intros; reflexivity).
assert (MEQW : forall x : word, ~ WIN false (bv_unsigned x) -> mem0 x = mem0 x) by (intros; reflexivity).
pose proof Hpres0 as PRESW. pose proof trace_obj as (_ & _ & BUFW).
srr_run_sh tfibtbl_rtA_ok HS. frame_acc HEn1.
pose proof K0_facts as (_ & NR & _ & _ & _ & R8r & R8m & _ & _ & _ & _ & _ & _ & _ & _ & _ & R8def).
assert (En10 : U En1 (SOff 10 0) = n).
{ clear - HEn1 Hn NR. rewrite U_zev by reflexivity. cbn [zev]. unfold rho_of. rewrite (HEn1 10%nat (ltHAV 10 eq_refl)), E10, Hn. unfold w64.
rewrite unsigned_lit_small by zlia. rewrite Z.add_0_r. apply zcanon_id. unfold M64. zlia. }
srr_branch_sh tfibtbl_rtA_ok HS.
2:{   rewrite branch_ltu_U, En10, (U_lit En1 8) in Hc by zlia. apply Z.ltb_ge in Hc.
srr_run_to_sh tfibtbl_rtA_ok HS 0x3337c. frame_acc HEn1.
apply (st_ok_pin_regU _ _ _ 10%bv (SOff aR8 0)) in HS. 2:{ intros X; discriminate. }
2:{ clear - HEn1 Hc NR R8def. pin_zev. unfold aR8. rewrite (HEn1 38%nat (ltHAV 38 eq_refl)), EaR8. unfold w64. rewrite unsigned_lit_small by zlia.
rewrite R8def, Z.max_r by zlia. rewrite !zcanon_id by (unfold M64; zlia). reflexivity. }
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
apply (YP03.st_ok_prune tfibsegs _ _ _ [] []) in HS.
lazymatch type of HS with st_ok _ _ ?ss _ => replace ss with KS_B in HS by (vm_compute; reflexivity) end.
close_ST En1 HEn1 HS mem0 MEQ MEQW PRESW BUFW. }
rewrite branch_ltu_U, En10, (U_lit En1 8) in Hc by zlia. apply Z.ltb_lt in Hc.
assert (ZR8 : zev (rho_of En1) (SAlu ALU_AND (SOff 10 7) (SLit 18446744073709551608)) = R8v).
{ clear - HEn1 Hn NR Hc R8def.
cbn [zev zalu_raw]. unfold rho_of. rewrite (HEn1 10%nat (ltHAV 10 eq_refl)), E10, Hn. unfold w64. rewrite unsigned_lit_small by zlia.
rewrite (zcanon_id (n + 7)) by (unfold M64; zlia). rewrite (zcanon_id 18446744073709551608) by (unfold M64; zlia).
change 18446744073709551608 with (2 ^ 64 - 8). rewrite land_m8_64 by zlia. rewrite R8def, Z.max_l by zlia.
pose proof (Z.div_mod (n + 7) 8 ltac:(zlia)). pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(zlia)). rewrite zcanon_id; unfold M64; zlia. }
srr_run_to_sh tfibtbl_rtA_ok HS 0x3337c. frame_acc HEn1.
apply (st_ok_pin_regU _ _ _ 10%bv (SOff aR8 0)) in HS. 2:{ intros X; discriminate. }
2:{ clear - HEn1 ZR8 R8r. apply U_eq_by_zev; [reflexivity | reflexivity |]. cbn [sr_get ss_regs nth]. unfold aR8.
change (zev (rho_of En1) (SOff 38 0) = zcanon (zalu_raw 63 64 ALU_ADD (zev (rho_of En1) (SAlu ALU_AND (SOff 10 7) (SLit 18446744073709551608))) (zev (rho_of En1) (SLit 0)))).
rewrite ZR8. cbn [zev zalu_raw]. unfold rho_of. rewrite (HEn1 38%nat (ltHAV 38 eq_refl)), EaR8. unfold w64.
rewrite unsigned_lit_small by zlia. zcanon_simp. zlia. }
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
apply (st_ok_pin_regU _ _ _ 11%bv (SLit 0)) in HS. 2:{ intros X; discriminate. }
2:{ clear - HEn1 ZR8 R8r R8m. apply U_eq_by_zev; [reflexivity | reflexivity |]. cbn [sr_get ss_regs nth].
change (zev (rho_of En1) (SLit 0) = zcanon (zalu_raw 63 64 ALU_AND (zcanon (zalu_raw 63 64 ALU_ADD (zev (rho_of En1) (SAlu ALU_AND (SOff 10 7) (SLit 18446744073709551608))) (zev (rho_of En1) (SLit 0)))) (zev (rho_of En1) (SLit 7)))).
rewrite ZR8. cbn [zev zalu_raw]. zcanon_simp. rewrite Z.add_0_r, land_7_mod by zlia. rewrite R8m. reflexivity. }
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
apply (YP03.st_ok_prune tfibsegs _ _ _ [] []) in HS.
lazymatch type of HS with st_ok _ _ ?ss _ => replace ss with KS_B in HS by (vm_compute; reflexivity) end.
close_ST En1 HEn1 HS mem0 MEQ MEQW PRESW BUFW.
Qed.
Lemma segB : forall W0 c, at_ST KS_B W0 c -> SRr tfibsegs W0 c (at_ST KS_E).
Proof.
intros W0 c (-> & ms & mat & En & -> & HEn & HS & MEQW & PRESW & BUFW). pose proof Hwx_tfa as Hwx.
pose proof Hsp as (Hlo & Hbot & Hhi & Hal). pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
pose proof derived_ranges as DR. pose proof high_facts as LF.
pose proof K0_facts as (_ & NR & NPr & NP0 & NP1 & R8r & R8m & _).
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, t_cache, t_unwinding in DR, LF.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) En _ _ HS eq_refl) as Hshape; cbn [ss_pc] in Hshape;
lazymatch type of Hshape with _ = mkst _ (Z_to_bv 64 (ss_pc ?s)) _ _ => let p := eval vm_compute in (ss_pc s) in change (ss_pc s) with p in Hshape | _ => idtac end.
rewrite Hshape in HS. rewrite Hshape. set (mem1 := ms_mem ms) in *.
assert (MEQ : forall x : word, ~ WIN1 false (bv_unsigned x) -> mem1 x = mem1 x) by (intros; reflexivity).
srr_run_to_sh tfibtbl_rtA_ok HS 0x33398. frame_acc HEn.
apply (st_ok_pin_regU _ _ _ 9%bv (SOff aNP 0)) in HS. 2:{ intros X; discriminate. }
2:{ clear - HEn Hn NR NPr NP0 NP1. pin_zev. unfold aNP. rewrite (HEn 62%nat (ltHAV 62 eq_refl)), (HEn 10%nat (ltHAV 10 eq_refl)), EaNP, E10, Hn.
unfold w64. rewrite !unsigned_lit_small by zlia. rewrite (zcanon_id (n + 0)) by (unfold M64; zlia). rewrite (zcanon_id 1) by (unfold M64; zlia).
destruct (Z.ltb_spec (n + 0) 1);
[ rewrite (zcanon_id 1) by (unfold M64; zlia) | rewrite (zcanon_id 0) by (unfold M64; zlia) ]; rewrite !zcanon_id by (unfold M64; zlia); zlia. }
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_sh tfibtbl_rtA_ok HS. frame_acc HEn.
srr_branch_sh tfibtbl_rtA_ok HS.
2:{ exfalso. clear - Hc HEn R8r. rewrite branch_geu_U in Hc. apply Bool.negb_false_iff in Hc. apply Z.ltb_lt in Hc. revert Hc.
rewrite !U_zev by reflexivity. cbn [zev zalu_raw]. unfold rho_of, aR8.
rewrite (HEn 38%nat (ltHAV 38 eq_refl)), EaR8. unfold w64. rewrite unsigned_lit_small by zlia.
rewrite (zcanon_id (R8v + 16)) by (unfold M64; zlia). change (zcanon (-1)) with (2 ^ 64 - 1). rewrite lxor_ones64 by zlia.
zcanon_simp. zlia. }
clear Hc.
srr_run_to_sh tfibtbl_rtA_ok HS 0x378ac. frame_acc HEn.
apply (st_ok_pin_regU _ _ _ 8%bv (SOff aCL 0)) in HS;
[ | intros X; discriminate
| lazymatch goal with |- U ?E _ = U _ (sr_get ?sr ?r) => let t := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with t end;
lazymatch goal with |- U ?E _ = U _ ?t => change t with CLk end;
apply U_eq_by_zev; [reflexivity | clear; vm_compute; reflexivity |]; rewrite (CLk_E En HEn);
cbn [zev]; unfold rho_of, aCL; rewrite (HEn 39%nat (ltHAV 39 eq_refl)), (eq_refl : ew E0 39 = w64 cl); unfold w64;
rewrite unsigned_lit_small by zlia; rewrite Z.add_0_r; apply zcanon_id; unfold M64; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
apply (YP03.st_ok_prune tfibsegs _ _ _ [] []) in HS.
lazymatch type of HS with st_ok _ _ ?ss _ => replace ss with KS_E in HS by (vm_compute; reflexivity) end.
close_ST En HEn HS mem1 MEQ MEQW PRESW BUFW.
Qed.
Lemma segC1 : forall W0 c, at_ST KS_E W0 c -> SRr tfibsegs W0 c (at_ST KS_JN).
Proof.
intros W0 c (-> & ms & mat & En & -> & HEn & HS & MEQW & PRESW & BUFW). pose proof Hwx_tfa as Hwx.
pose proof Hsp as (Hlo & Hbot & Hhi & Hal). pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
pose proof derived_ranges as DR. pose proof high_facts as LF. pose proof K0_facts as (_ & NR & NPr & _ & _ & R8r & R8m & NPR8 & _).
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, t_cache, t_unwinding in DR, LF.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) En _ _ HS eq_refl) as Hshape; cbn [ss_pc] in Hshape;
lazymatch type of Hshape with _ = mkst _ (Z_to_bv 64 (ss_pc ?s)) _ _ => let p := eval vm_compute in (ss_pc s) in change (ss_pc s) with p in Hshape | _ => idtac end.
rewrite Hshape in HS. rewrite Hshape. set (mem1 := ms_mem ms) in *.
assert (MEQ : forall x : word, ~ WIN1 false (bv_unsigned x) -> mem1 x = mem1 x) by (intros; reflexivity).
srr_run_sh tfibtbl_rtA_ok HS. frame_acc HEn.
apply (st_ok_pin_regU _ _ _ 9%bv (SOff aP 0)) in HS;
[ | intros X; discriminate
| clear - T SB HEn DR LF Hcl Hcnt Hv Hn; pin_zev; unfold aP;
rewrite (HEn 40%nat (ltHAV 40 eq_refl)), (HEn 32%nat (ltHAV 32 eq_refl)), (HEn 39%nat (ltHAV 39 eq_refl)), EaP, EaT, (eq_refl : ew E0 39 = w64 cl);
unfold w64; rewrite !unsigned_lit_small by (unfold Pv, t_cache in *; zlia); unfold Pv, t_cache in *; zcanon_simp; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_to_sh tfibtbl_rtA_ok HS 0x378cc. frame_acc HEn.
forget_regs HS 103%nat ([1; 5; 6; 7; 14; 15; 16; 17; 19; 20; 28; 29; 30; 31]%bv : list (bv 5)).
apply (YP03.st_ok_prune tfibsegs _ _ _ [] []) in HS.
lazymatch type of HS with st_ok _ _ ?ss _ => replace ss with KS_JN in HS by (vm_compute; reflexivity) end.
lazymatch type of HS with st_ok _ ?E2 _ _ => set (EnE := E2) in HS end.
assert (HEnE : forall j, (j < aHAV)%nat -> ew EnE j = ew E0 j) by (intros j Hj; subst EnE; unfold aHAV in Hj; rewrite ew_havoc_old by zlia; apply HEn; exact Hj).
close_ST EnE HEnE HS mem1 MEQ MEQW PRESW BUFW.
Qed.
Lemma segC2 : forall W0 c, at_ST KS_JN W0 c -> SRr tfibsegs W0 c (at_ST KS_PD).
Proof.
intros W0 c (-> & ms & mat & En & -> & HEn & HS & MEQW & PRESW & BUFW). pose proof Hwx_tfa as Hwx.
pose proof Hsp as (Hlo & Hbot & Hhi & Hal). pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
pose proof derived_ranges as DR. pose proof high_facts as LF. pose proof K0_facts as (_ & NR & NPr & _ & _ & R8r & R8m & NPR8 & _).
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, t_cache, t_unwinding in DR, LF.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) En _ _ HS eq_refl) as Hshape; cbn [ss_pc] in Hshape;
lazymatch type of Hshape with _ = mkst _ (Z_to_bv 64 (ss_pc ?s)) _ _ => let p := eval vm_compute in (ss_pc s) in change (ss_pc s) with p in Hshape | _ => idtac end.
rewrite Hshape in HS. rewrite Hshape. set (mem1 := ms_mem ms) in *.
assert (MEQ : forall x : word, ~ WIN1 false (bv_unsigned x) -> mem1 x = mem1 x) by (intros; reflexivity).
srr_run_sh tfibtbl_rtA_ok HS. frame_acc HEn.
apply (st_ok_pin_regU _ _ _ 14%bv (SOff aPV (-16))) in HS. 2:{ intros X; discriminate. }
2:{ clear - T SB HEn DR LF Hcl Hcnt Hv Hn. pin_zev. unfold aPV.
rewrite (HEn 44%nat (ltHAV 44 eq_refl)), (HEn 40%nat (ltHAV 40 eq_refl)), (HEn 41%nat (ltHAV 41 eq_refl)), EaPV, EaP, (eq_refl : ew E0 41 = w64 cnt).
unfold w64. unfold PVv, Pv in *. rewrite !unsigned_lit_small by zlia. zcanon_simp.
land_lits. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by zlia.
rewrite (zcanon_id ((cnt + 0) * 2 ^ 32)) by (unfold M64; zlia).
replace (zcanon ((cnt + 0) * 2 ^ 32 + zcanon (-4294967296))) with ((cnt - 1) * 2 ^ 32).
2:{ unfold zcanon, M64. change ((-4294967296) mod 2 ^ 64) with (2 ^ 64 - 2 ^ 32).
replace ((cnt + 0) * 2 ^ 32 + (2 ^ 64 - 2 ^ 32)) with ((cnt - 1) * 2 ^ 32 + 1 * 2 ^ 64) by zlia.
rewrite Z_mod_plus_full. symmetry. apply Z.mod_small. zlia. }
replace ((cnt - 1) * 2 ^ 32 / 2 ^ 30) with ((cnt - 1) * 4) by (apply Z.div_unique_exact; zlia).
zcanon_simp. zlia. }
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_to_sh tfibtbl_rtA_ok HS 0x33444. frame_acc HEn.
apply (st_ok_pin_regU _ _ _ 10%bv (SOff aK 0)) in HS. 2:{ intros X; discriminate. }
2:{ clear - T SB HEn DR LF Hcl Hcnt Hv Hn. pin_zev. unfold aK.
rewrite (HEn 45%nat (ltHAV 45 eq_refl)), (HEn 34%nat (ltHAV 34 eq_refl)), (HEn 39%nat (ltHAV 39 eq_refl)), (HEn 42%nat (ltHAV 42 eq_refl)),
EaK, EaSB, (eq_refl : ew E0 39 = w64 cl), (eq_refl : ew E0 42 = w64 v).
unfold w64. unfold Kv in *. rewrite !unsigned_lit_small by zlia. zcanon_simp.
land_lits. rewrite !Z.shiftl_mul_pow2 by zlia. change (2 ^ 4) with 16.
zcanon_simp. unfold SB. zlia. }
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_sh tfibtbl_rtA_ok HS. frame_acc HEn.
srr_branch_sh tfibtbl_rtA_ok HS.
{ exfalso. clear - Hc HEn DR LF R8r NPr NPR8. rewrite branch_ltu_U in Hc. apply Z.ltb_lt in Hc. revert Hc.
rewrite !U_zev by reflexivity. cbn [zev zalu_raw]. unfold rho_of, aK, aR8, aNP.
rewrite (HEn 38%nat (ltHAV 38 eq_refl)), (HEn 45%nat (ltHAV 45 eq_refl)), (HEn 62%nat (ltHAV 62 eq_refl)), EaK, EaR8, EaNP.
unfold w64. rewrite !unsigned_lit_small by zlia. zcanon_simp. zlia. }
clear Hc. srr_run_sh tfibtbl_rtA_ok HS. frame_acc HEn.
srr_branch_sh tfibtbl_rtA_ok HS.
{ exfalso. clear - Hc HEn DR NR Hn. rewrite branch_ne_U in Hc. apply Bool.negb_true_iff in Hc. apply Z.eqb_neq in Hc. apply Hc.
rewrite !U_zev by reflexivity. cbn [zev zalu_raw]. unfold rho_of.
rewrite (HEn 10%nat (ltHAV 10 eq_refl)), E10, Hn. unfold w64. rewrite !unsigned_lit_small by zlia. zcanon_simp.
land_lits. rewrite Z.shiftr_div_pow2 by zlia. rewrite Z.div_small by zlia. reflexivity. }
clear Hc. srr_run_sh tfibtbl_rtA_ok HS. frame_acc HEn.
close_ST En HEn HS mem1 MEQ MEQW PRESW BUFW.
Qed.
Lemma seg1J : SRr tfibsegs W cfg0 (at_ST KS_JN).
Proof.
eapply SRr_bind; [exact segA|]. intros W1 c1 _ H1.
eapply SRr_bind; [exact (segB W1 c1 H1)|]. intros W2 c2 _ H2. exact (segC1 W2 c2 H2).
Qed.
Lemma seg1 : SRr tfibsegs W cfg0 (at_ST KS_PD).
Proof.
eapply SRr_bind; [exact seg1J|]. intros W3 c3 _ H3. exact (segC2 W3 c3 H3).
Qed.
End e.
End d.
