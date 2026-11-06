(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AFiu.v, with its module paths changed, names TfibSyms -> CmdBSyms and its addresses moved to plugin-hostd/fuzz_command's ASan build. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_command/lib/A/AFiu.v (donor image sha256 c0661b96b5bd), with its module paths changed, names CmdBSyms -> SegBSyms and its addresses moved to reac-pw/fuzz_segconf's ASan build. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.

From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.

From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import AB1w AE3d AFhy AFis AFhz AFho AFi4.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
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
Variable kz : Z.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let pT : Z := bv_unsigned (getr regs0 11).
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
Local Abbreviation tr := (@AFis.tr ch).
Local Abbreviation XW := (@AFis.XW ly n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz).
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
Hypothesis Hsp : ly_stk_lo ly + MALLOC_IN_STK <= sp0 /\ sp0 - IFRAME <= pT /\ sp0 <= ly_stk_hi ly /\ sp0 mod 16 = 0.
(* the caller's trace object at p = a1 (RtDDefs.v amalloc_inner_realizes) *)
Hypothesis Hch : (1 <= length ch <= 30)%nat /\ pT mod 8 = 0 /\ pT + 16 + 8 * 30 <= ly_stk_hi ly /\ astrace_at tfibsegs W mem0 pT ch.
Local Abbreviation HCdisj := (@AFis.HCdisj _ W ly regs0 mem0 ch v Hv LY Hch).
Local Abbreviation DZONE := (@AFis.DZONE ly).
Variable DPOST : Z -> (word -> option byte) -> Prop.
Local Abbreviation HC_NB := (@AFis.HC_NB _ ly LY).
Hypothesis HKpres : forall a, Kv <= a < Kv + RZ + R8v -> apresent (w_H W) mem0 a.
Hypothesis HSKpres : forall a, SKv <= a < SKv + (RZ + R8v) / 8 -> apresent (w_H W) mem0 a.
Hypothesis HPB250 : n mod 8 <> 0 -> val_mem tfibsegs (mrestrict (w_H W) mem0) PBv 1 250.
Local Abbreviation HCX := (@AFis.HCX _ ly LY).
Local Abbreviation tr_length := (@AFis.tr_length W ly regs0 mem0 ch Hch).
Local Abbreviation trace_obj := (@AFis.trace_obj W ly regs0 mem0 n ch v kz Hch DPOST).
Local Abbreviation Kv_range := (@AFis.Kv_range W ly regs0 mem0 n ch cl v kz Hcl Hv Hv2 Hch DPOST).
Local Abbreviation high_facts := (@AFis.high_facts _ W ly regs0 mem0 n ch v kz Hv LY IMG Hch DPOST).
Local Abbreviation blocks_facts := (@AFis.blocks_facts _ ly LY IMG).
Local Abbreviation off_T := (@AFis.off_T _ W ly regs0 mem0 n ch v kz Hv LY IMG Hch DPOST).
Local Abbreviation off_C := (@AFis.off_C _ W ly regs0 mem0 n ch v kz Hv LY IMG Hch DPOST).
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
t_cache, t_unwinding, t_stats, MALLOC_IN_STK, IFRAME, TFIB_IMG_END, TFIB_IMG_LO, kLowShadowBeg, UNW_STK, BST_SIZE, DEP_STK in * ); try pose proof RZ_num as RZN.
Local Abbreviation derived_ranges := (@AFis.derived_ranges _ W ly regs0 mem0 n ch cl cnt v kz Hcl Hv Hcnt Hv2 LY IMG Hch DPOST Hkz Nrange).
Hypothesis Hcl_def : cl = class_id (R8v + RZ).
Local Abbreviation NDv_facts := (@AFis.NDv_facts W ly regs0 mem0 n ch v kz Hch DPOST Hkz Nrange).
Local Abbreviation CL_hi_E := (@AFis.CL_hi_E W ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz Hch DPOST Hkz Nrange Hcl_def).
Local Abbreviation CL_lo_E := (@AFis.CL_lo_E W ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz Hch DPOST Hkz Nrange Hcl_def).
Local Abbreviation WIN1 := (@AFis.WIN1 ly regs0 n cl v kz).
Local Abbreviation WIN1_WIN := (@AFis.WIN1_WIN W ly regs0 mem0 n ch cl v kz Hch DPOST).
Local Abbreviation WIN_odd := (@AFis.WIN_odd W ly regs0 mem0 n ch cl cnt v jb kz Hcl Hv Hcnt Hjb Hsp Hch DPOST Hkz Nrange).
Local Abbreviation WIN1_odd := (@AFis.WIN1_odd W ly regs0 mem0 n ch cl cnt v jb kz Hcl Hv Hcnt Hjb Hsp Hch DPOST Hkz Nrange).
Local Abbreviation WSKEL := (@AFis.WSKEL).
Local Abbreviation WSKEL1 := (@AFis.WSKEL1).
Local Abbreviation win_sub := (@AFis.win_sub).
Local Abbreviation win_sub_sound := (@AFis.win_sub_sound W ly regs0 mem0 n ch v kz Hv Hch DPOST).
Local Abbreviation WSKEL_WIN := (@AFis.WSKEL_WIN _ W ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz Hcl Hv Hcnt Hv2 LY IMG Hch DPOST Hkz Nrange).
Local Abbreviation WSKEL1_WIN1 := (@AFis.WSKEL1_WIN1 _ W ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz Hcl Hv Hcnt Hv2 LY IMG Hch DPOST Hkz Nrange).
Local Abbreviation windows_WIN := (@AFis.windows_WIN _ W ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz Hcl Hv Hcnt Hv2 LY IMG Hch DPOST Hkz Nrange).
Local Abbreviation windows_WIN1 := (@AFis.windows_WIN1 _ W ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz Hcl Hv Hcnt Hv2 LY IMG Hch DPOST Hkz Nrange).
Local Abbreviation frame_WIN1 := (@AFis.frame_WIN1 _ W ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz Hcl Hv Hcnt Hv2 LY IMG Hch DPOST Hkz Nrange).
Local Abbreviation WIN_not_high := (@AFis.WIN_not_high _ W ly regs0 mem0 n ch cl cnt v kz Hcl Hv Hcnt Hv2 LY IMG Hsp Hch DPOST Hkz Nrange).
Variables (mat0 : list word).
Let H0 := w_H W.
Variables (regsI : bvmap 5 word).
(* the run starts with regsI: regs0 with sp = sp0 - IFRAME *)
Hypotheses (RIo : forall r : bv 5, r <> 2%bv -> getr regsI r = getr regs0 r) (RI2 : getr regsI 2 = w64 (sp0 - IFRAME)).
Let cfg0 : config := mkCfg (mkst regsI (w64 PC_asan_malloc) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis SEED : st_ok tfibsegs E0 SS0 (restrict (w_H W) (mkst regsI (w64 PC_asan_malloc) mem0 (seg_rom tfibsegs))).
Local Abbreviation all_disjoint_of_forall := (@AFis.all_disjoint_of_forall).
Local Abbreviation kept_of_frame := (@AFis.kept_of_frame W ly regs0 mem0 n ch v kz Hch DPOST).
Local Abbreviation SKEL_TAIL := (@AFis.SKEL_TAIL).
Local Abbreviation stack_ivs := (@AFis.stack_ivs _ W ly regs0 mem0 n ch v kz Hv LY Hsp Hch DPOST).
Local Abbreviation stack_ivs2 := (@AFis.stack_ivs2 _ W ly regs0 mem0 n ch v kz Hv LY Hsp Hch DPOST).
Local Abbreviation trace_ivs := (@AFis.trace_ivs _ W ly regs0 mem0 n ch v kz Hv LY Hsp Hch DPOST).
Local Abbreviation DZONE_disj := (@AFis.DZONE_disj _ W ly regs0 mem0 n ch cl cnt v kz Hcl Hv Hcnt Hv2 LY IMG Hsp Hch DPOST Hkz Nrange).
Local Abbreviation RFACTS := (@AFis.RFACTS ly regs0 n cl v kz).
Local Abbreviation zone_lit := (@AFis.zone_lit _ W ly regs0 mem0 n ch cl cnt v kz Hcl Hv Hcnt Hv2 LY IMG Hsp Hch DPOST Hkz Nrange).
Local Abbreviation zone_T := (@AFis.zone_T _ W ly regs0 mem0 n ch cl cnt v kz Hcl Hv Hcnt Hv2 LY IMG Hsp Hch DPOST Hkz Nrange).
Local Abbreviation zone_C := (@AFis.zone_C _ W ly regs0 mem0 n ch cl cnt v kz Hcl Hv Hcnt Hv2 LY IMG Hsp Hch DPOST Hkz Nrange).
Local Abbreviation zone_K := (@AFis.zone_K _ W ly regs0 mem0 n ch cl cnt v kz Hcl Hv Hcnt Hv2 LY IMG Hsp Hch DPOST Hkz Nrange).
Local Abbreviation zone_SH := (@AFis.zone_SH _ W ly regs0 mem0 n ch cl cnt v kz Hcl Hv Hcnt Hv2 LY IMG Hsp Hch DPOST Hkz Nrange).
Local Abbreviation tail_ext_ok := (@AFis.tail_ext_ok _ W ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz Hcl Hv Hcnt Hv2 LY IMG Hsp Hch DPOST Hkz Nrange).
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
Local Abbreviation memset_stretch := (@AFis.memset_stretch _ W ly regs0 mem0 n ch cl cnt v jb kz Hcl Hv Hcnt Hjb Hsp Hch DPOST Hkz Nrange).
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
Local Abbreviation casek_sizes := (@AFis.casek_sizes n kz Hkz Nrange).
Local Abbreviation Kv_is_sptr := (@AFis.Kv_is_sptr ly cl v Hcl B off Hoff_def).
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
Hypothesis SEEDM : st_ok tfibsegs E0 MS0 (restrict (w_H W) (mkst regsI (w64 PC_asan_malloc) mem0 (seg_rom tfibsegs))).
Definition WINM (a : Z) : Prop := (sp0 - MALLOC_IN_STK <= a < sp0 - IFRAME) \/ (T + t_unwinding <= a < T + t_unwinding + 1).
Definition WINM1 (a : Z) : Prop :=
(sp0 - MALLOC_IN_STK <= a < sp0 - IFRAME) \/ (sp0 - IFRAME <= a < sp0 - IFRAME) \/ (T + t_unwinding <= a < T + t_unwinding + 1).
Lemma WINM1_WINM : forall a, WINM1 a -> WINM a.
Proof. intros a H. unfold WINM1, WINM, IFRAME, MALLOC_IN_STK in *. zlia. Qed.
Lemma WINM_WIN : forall a, WINM a -> WIN false a.
Proof. intros a H. unfold WINM, WIN, WINT in *. destruct H as [H|H]; [left; exact H | right; left; right; right; right; exact H]. Qed.
Definition WSKELM : list (option nat * Z * Z) := [(Some 2%nat, - MALLOC_IN_STK, - IFRAME); (Some 32%nat, t_unwinding, t_unwinding + 1)].
Definition WSKELM1 : list (option nat * Z * Z) := [(Some 2%nat, - MALLOC_IN_STK, - IFRAME); (Some 2%nat, - IFRAME, - IFRAME); (Some 32%nat, t_unwinding, t_unwinding + 1)].
Lemma WSKELM_WINM : forall (E : env) a t,
(forall k, (k < aHAV)%nat -> ew E k = ew E0 k) -> In t WSKELM ->
base_val E (fst (fst t)) + snd (fst t) <= a < base_val E (fst (fst t)) + snd t -> WINM a.
Proof.
intros E a t HE Hin Hr. pose proof derived_ranges as DR. pose proof high_facts as HF'.
unfold WSKELM in Hin. cbn [In] in Hin. unfold WINM.
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, t_cache, t_unwinding, kThreadObjSize, aHAV in *.
repeat match type of Hin with _ \/ _ => destruct Hin as [<-|Hin] | False => destruct Hin end;
cbn [fst snd base_val] in Hr; rewrite HE in Hr by zlia; rewrite ?E2, ?EaT in Hr; unfold w64 in Hr; rewrite ?unsigned_lit_small in Hr by zlia;
unfold sp0 in *; zlia.
Qed.
Lemma WSKELM1_WINM1 : forall (E : env) a t,
(forall k, (k < aHAV)%nat -> ew E k = ew E0 k) -> In t WSKELM1 ->
base_val E (fst (fst t)) + snd (fst t) <= a < base_val E (fst (fst t)) + snd t -> WINM1 a.
Proof.
intros E a t HE Hin Hr. pose proof derived_ranges as DR. pose proof high_facts as HF'.
unfold WSKELM1 in Hin. cbn [In] in Hin. unfold WINM1.
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, t_cache, t_unwinding, kThreadObjSize, aHAV, IFRAME in *.
repeat match type of Hin with _ \/ _ => destruct Hin as [<-|Hin] | False => destruct Hin end;
cbn [fst snd base_val] in Hr; rewrite HE in Hr by zlia; rewrite ?E2, ?EaT in Hr; unfold w64 in Hr; rewrite ?unsigned_lit_small in Hr by zlia;
unfold sp0 in *; zlia.
Qed.
Lemma windows_WINM : forall (E : env) rs a,
(forall k, (k < aHAV)%nat -> ew E k = ew E0 k) ->
forallb (fun t => existsb (win_sub t) WSKELM || (snd t <=? snd (fst t))) (windows rs) = true ->
in_wrange E rs a -> WINM a.
Proof.
intros E rs a HE Hb Hw. destruct (in_wrange_windows E rs a Hw) as (b & lo & hi & Hin & Hr).
pose proof (proj1 (forallb_forall _ _) Hb _ Hin) as Ht. cbn beta in Ht. apply Bool.orb_prop in Ht as [Ht|Ht].
- apply existsb_exists in Ht as (u & Hinu & Hsub). exact (WSKELM_WINM E a u HE Hinu (win_sub_sound E a _ u Hsub Hr)).
- cbn [fst snd] in Ht. apply Z.leb_le in Ht. zlia.
Qed.
Lemma windows_WINM1 : forall (E : env) rs a,
(forall k, (k < aHAV)%nat -> ew E k = ew E0 k) ->
forallb (fun t => existsb (win_sub t) WSKELM1 || (snd t <=? snd (fst t))) (windows rs) = true ->
in_wrange E rs a -> WINM1 a.
Proof.
intros E rs a HE Hb Hw. destruct (in_wrange_windows E rs a Hw) as (b & lo & hi & Hin & Hr).
pose proof (proj1 (forallb_forall _ _) Hb _ Hin) as Ht. cbn beta in Ht. apply Bool.orb_prop in Ht as [Ht|Ht].
- apply existsb_exists in Ht as (u & Hinu & Hsub). exact (WSKELM1_WINM1 E a u HE Hinu (win_sub_sound E a _ u Hsub Hr)).
- cbn [fst snd] in Ht. apply Z.leb_le in Ht. zlia.
Qed.
Lemma frame_WINM1 : forall (E : env) rs (m m' : word -> option byte),
(forall k, (k < aHAV)%nat -> ew E k = ew E0 k) ->
forallb (fun t => existsb (win_sub t) WSKELM1 || (snd t <=? snd (fst t))) (windows rs) = true ->
frame_of E rs m m' -> forall x : word, ~ WINM1 (bv_unsigned x) -> m' x = m x.
Proof. intros E rs m m' HE Hb HF x Hx. apply HF. intros Hw. apply Hx. exact (windows_WINM1 E rs _ HE Hb Hw). Qed.
Definition at_STM (ss : sstate) (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ exists ms mat (E' : env),
c' = mkCfg ms (with_vm_backing (m_vm_lazy md0) mat md0) /\
(forall k, (k < aHAV)%nat -> ew E' k = ew E0 k) /\
st_ok tfibsegs E' ss (restrict (w_H W) ms) /\
(forall x : word, ~ WINM (bv_unsigned x) -> ms_mem ms x = mem0 x) /\
(forall a, sp0 - MALLOC_IN_STK <= a < sp0 - IFRAME -> apresent (w_H W) (ms_mem ms) a) /\
(forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (pT + 16 + 8 * Z.of_nat i) 8 (nth i tr 0)).
Lemma at_STM_ST : forall ss W' c', at_STM ss W' c' -> at_ST ss W' c'.
Proof.
intros ss W' c' (HW & ms & mat & E' & Hc & HE & HS & HM & HP & HB). split; [exact HW|]. exists ms, mat, E'.
repeat (split; [assumption|]). split; [|split; assumption]. intros x Hx. apply HM. intros H. apply Hx. exact (WINM_WIN _ H).
Qed.
Ltac frame_accM HE :=
match goal with
| MEQ : (forall x : word, ~ WINM1 (bv_unsigned x) -> ?m1 x = ?mb x), HFx : frame_of ?E ?rs ?m1 ?m2 |- _ =>
let MEQ' := fresh "MEQ" in
assert (MEQ' : forall x : word, ~ WINM1 (bv_unsigned x) -> m2 x = mb x)
by (intros x Hx; transitivity (m1 x); [exact (frame_WINM1 E rs m1 m2 HE ltac:(vm_compute; reflexivity) HFx x Hx) | exact (MEQ x Hx)]);
clear MEQ HFx; rename MEQ' into MEQ
end.
Local Ltac close_ST En HEn HS memB MEQ MEQW PRESW BUFW :=
apply SRr_ret; split; [reflexivity|];
lazymatch goal with |- context [mkCfg ?msf (with_vm_backing _ ?matf _)] => exists msf, matf, En end;
split; [reflexivity|]; split; [exact HEn|]; split; [exact HS|];
pose proof derived_ranges as DR'; pose proof high_facts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9); pose proof Kv_range as HKR;
pose proof (lo_top ly LY) as (T1' & T2' & T3' & T4' & T5' & T6' & T7'); pose proof Hsp as (Hlo_ & Hpl_ & Hhi_ & Hal_);
pose proof Hch as (_ & _ & Hpt_ & _);
split; [|split];
[ intros x Hx; rewrite (MEQ x) by (intros H1; apply Hx, WINM1_WINM, H1); apply MEQW, Hx
| intros a Ha; eapply (st_ok_window_apresent_off (w_H W) En _ _ 1 _ a HS);
[reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn 2%nat (ltHAV 2 eq_refl)), E2; addr_tac | off_by ltac:(addr_tac)]
| intros i Hi; pose proof tr_length as LEN;
eapply val_mem_frame; [|exact (BUFW i Hi)];
intros k Hk; apply MEQ;
assert (Hx : ly_stk_lo ly <= pT + 16 + 8 * Z.of_nat i + Z.of_nat k < ly_stk_hi ly) by (clear - Hi Hk LEN Hlo_ Hpl_ Hpt_; unfold IFRAME, MALLOC_IN_STK in *; zlia);
destruct (F9 _ Hx) as [N1 N2]; pose proof (HCdisj _ Hx) as HC;
clear - Hi Hk LEN DR' HKR N1 N2 HC T7' T4' Hlo_ Hpl_ Hpt_ F1 F2 F3 F4 F5 F6 F7 F8;
unfold WINM1, IFRAME in *; numconst; rewrite unsigned_lit_small by zlia; zlia ].
Definition SKEL_TAILM : list (option nat * Z * Z * Z * Z) := skeleton (skipn 3 MREG0).
Lemma tail_ext_okM : forall (E : env) r,
(forall k, (k < aHAV)%nat -> ew E k = ew E0 k) -> In (skel r) SKEL_TAILM ->
let b := base_val E (YP09.r_base r) in
(b + YP09.r_hi r <= sp0 - MALLOC_IN_STK \/ sp0 - IFRAME <= b + YP09.r_lo r) /\ 0 <= b + YP09.r_lo r /\ b + YP09.r_hi r <= 2 ^ 64 /\
(YP09.r_whi r <= YP09.r_wlo r \/ (TFIB_IMG_END <= b + YP09.r_wlo r /\ b + YP09.r_whi r <= 2 ^ 64) \/ (0 <= b + YP09.r_wlo r /\ b + YP09.r_whi r <= TFIB_IMG_LO)) /\
((b + YP09.r_hi r <= 0x17dec8 \/ 0x5ce650 <= b + YP09.r_lo r) /\
(b + YP09.r_hi r <= ly_NB ly \/ ly_NB ly + kNodesBlockSize <= b + YP09.r_lo r) /\
(b + YP09.r_hi r <= ly_SB ly \/ ly_SB ly + kStoreBlockSize <= b + YP09.r_lo r)) /\
((b + YP09.r_hi r <= SUv \/ PBv <= b + YP09.r_lo r) /\ (b + YP09.r_hi r <= Kv + RZ \/ Kv + RZ + 4096 <= b + YP09.r_lo r) /\
(b + YP09.r_hi r <= PBv \/ PBv + 1 <= b + YP09.r_lo r)).
Proof.
intros E r HE Hin. pose proof derived_ranges as DR. pose proof high_facts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & _).
destruct r as [bs lo hi wlo whi cs]. unfold skel in Hin. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi].
let sk := eval vm_compute in SKEL_TAILM in change SKEL_TAILM with sk in Hin. cbn [In] in Hin.
repeat match type of Hin with _ \/ _ => destruct Hin as [Hin|Hin]; [injection Hin as <- <- <- <- <-|] | False => destruct Hin end.
all: cbn [base_val].
all: rewrite ?HE by (clear - HE; cbv; zlia); rewrite ?E2, ?EaT, ?EaC, ?EaP, ?EaK, ?EaU, ?EaSK, ?EaSSLOT, ?EaPB, ?EaPV; unfold w64;
rewrite ?unsigned_lit_small by (clear - DR F1 F2 F3 F4 F5 F6 F7 F8; numconst; try unfold T in *; zlia).
all: lazymatch goal with |- (?b + ?hi' <= ?s \/ ?s' <= ?b' + ?lo') /\ ?B /\ ?C /\ (?whi' <= ?wlo' \/ ?D) /\ ?R =>
enough (RF : (b + hi' <= s \/ s' <= b' + lo') /\ B /\ C /\ (b + whi' <= b + wlo' \/ D) /\ R) by (clear - RF; destruct RF as (X1 & X2 & X3 & X4 & X5); refine (conj X1 (conj X2 (conj X3 (conj _ X5)))); clear - X4; unfold TFIB_IMG_LO, TFIB_IMG_END in *; zlia) end.
all: first [ apply zone_lit; clear - DR; numconst; unfold TFIB_TSD, TFIB_TP; zlia
| apply zone_SH; clear - DR; numconst; zlia
| apply zone_K; clear - DR; numconst; zlia
| apply zone_T; clear - DR F1 F2; numconst; try unfold T in *; zlia
| apply zone_C; clear - DR F7 F8; numconst; zlia
].
Qed.
Local Ltac ladder_close HS HEn1 EnKL :=
srr_run_to_sh tfibtbl_rtA_ok HS 0x33288; frame_accM HEn1;
apply (st_ok_pin_regU _ _ _ 19%bv (SOff aKL 0)) in HS;
[ | intros X; discriminate
| pin_zev; unfold aKL; rewrite (HEn1 57%nat (ltHAV 57 eq_refl)), EaKL; unfold w64; rewrite unsigned_lit_small by zlia; rewrite !zcanon_id by (unfold M64; zlia); zlia ];
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS;
apply (YP03.st_ok_prune tfibsegs _ _ _ [] []) in HS;
lazymatch type of HS with st_ok _ _ ?ss _ => replace ss with MS_L in HS by (vm_compute; reflexivity) end.
Lemma missA : SRr tfibsegs W cfg0 (at_STM MS_L).
Proof.
pose proof Hwx_tfa as Hwx. pose proof SEEDM as HS.
pose proof Hsp as (Hlo & Hbot & Hhi & Hal).
pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
unfold cfg0.
set (En1 := E0) in HS.
assert (HEn1 : forall k, (k < aHAV)%nat -> ew En1 k = ew E0 k) by (intros; reflexivity).
assert (MEQ : forall x : word, ~ WINM1 (bv_unsigned x) -> mem0 x = mem0 x) by (intros; reflexivity).
assert (MEQW : forall x : word, ~ WINM (bv_unsigned x) -> mem0 x = mem0 x) by (intros; reflexivity).
pose proof Hpres0 as PRESW. pose proof trace_obj as (_ & _ & BUFW).
srr_run_sh tfibtbl_rtA_ok HS. frame_accM HEn1.
pose proof RZ_facts as (_ & _ & _ & _ & _ & NR). pose proof kz_cases as KC.
assert (En10 : U En1 (SOff 10 0) = n).
{ clear - HEn1 Hn NR KC. rewrite U_zev by reflexivity. cbn [zev]. unfold rho_of. rewrite (HEn1 10%nat (ltHAV 10 eq_refl)), E10, Hn. unfold w64.
rewrite unsigned_lit_small by (destruct KC as [->|[->|[->|[->|[->| ->]]]]]; cbn in NR; zlia). rewrite Z.add_0_r. apply zcanon_id. unfold M64.
destruct KC as [->|[->|[->|[->|[->| ->]]]]]; cbn in NR; zlia. }
assert (EnKL : U En1 (SOff aKL 0) = kz).
{ clear - HEn1 Hkz. rewrite U_zev by reflexivity. cbn [zev]. unfold rho_of, aKL. rewrite (HEn1 57%nat (ltHAV 57 eq_refl)), EaKL. unfold w64.
rewrite unsigned_lit_small by zlia. rewrite Z.add_0_r. apply zcanon_id. unfold M64. zlia. }
srr_branch_sh tfibtbl_rtA_ok HS.
2:{   rewrite branch_geu_U, En10, U_lit in Hc by zlia.
assert (K1 : kz = 1) by (clear - Hc NR KC; apply Bool.negb_false_iff in Hc; apply Z.ltb_lt in Hc;
destruct KC as [->|[->|[->|[->|[->| ->]]]]]; cbn in NR; zlia).
ladder_close HS HEn1 EnKL. close_ST En1 HEn1 HS mem0 MEQ MEQW PRESW BUFW. }
rewrite branch_geu_U, En10, (U_lit En1 97) in Hc by zlia. apply Bool.negb_true_iff in Hc. apply Z.ltb_ge in Hc. rename Hc into Hc1.
srr_run_sh tfibtbl_rtA_ok HS. frame_accM HEn1.
srr_branch_sh tfibtbl_rtA_ok HS.
2:{ rewrite branch_geu_U, En10, (U_lit En1 449) in Hc by zlia.
assert (K2 : kz = 2) by (clear - Hc Hc1 NR KC; apply Bool.negb_false_iff in Hc; apply Z.ltb_lt in Hc; destruct KC as [->|[->|[->|[->|[->| ->]]]]]; cbn in NR; zlia).
ladder_close HS HEn1 EnKL. close_ST En1 HEn1 HS mem0 MEQ MEQW PRESW BUFW. }
rewrite branch_geu_U, En10, (U_lit En1 449) in Hc by zlia. apply Bool.negb_true_iff in Hc. apply Z.ltb_ge in Hc. rename Hc into Hc2.
srr_run_sh tfibtbl_rtA_ok HS. frame_accM HEn1.
srr_branch_sh tfibtbl_rtA_ok HS.
2:{ rewrite branch_geu_U, En10, (U_lit En1 3969) in Hc by zlia.
assert (K3 : kz = 3) by (clear - Hc Hc2 NR KC; apply Bool.negb_false_iff in Hc; apply Z.ltb_lt in Hc; destruct KC as [->|[->|[->|[->|[->| ->]]]]]; cbn in NR; zlia).
ladder_close HS HEn1 EnKL. close_ST En1 HEn1 HS mem0 MEQ MEQW PRESW BUFW. }
rewrite branch_geu_U, En10, (U_lit En1 3969) in Hc by zlia. apply Bool.negb_true_iff in Hc. apply Z.ltb_ge in Hc. rename Hc into Hc3.
srr_run_sh tfibtbl_rtA_ok HS. frame_accM HEn1.
srr_branch_sh tfibtbl_rtA_ok HS.
2:{ rewrite branch_geu_U, En10, (U_lit En1 16129) in Hc by zlia.
assert (K4 : kz = 4) by (clear - Hc Hc3 NR KC; apply Bool.negb_false_iff in Hc; apply Z.ltb_lt in Hc; destruct KC as [->|[->|[->|[->|[->| ->]]]]]; cbn in NR; zlia).
ladder_close HS HEn1 EnKL. close_ST En1 HEn1 HS mem0 MEQ MEQW PRESW BUFW. }
rewrite branch_geu_U, En10, (U_lit En1 16129) in Hc by zlia. apply Bool.negb_true_iff in Hc. apply Z.ltb_ge in Hc. rename Hc into Hc4.
srr_run_sh tfibtbl_rtA_ok HS. frame_accM HEn1.
srr_branch_sh tfibtbl_rtA_ok HS.
2:{ rewrite branch_geu_U, En10, (U_lit En1 32257) in Hc by zlia.
assert (K5 : kz = 5) by (clear - Hc Hc4 NR KC; apply Bool.negb_false_iff in Hc; apply Z.ltb_lt in Hc; destruct KC as [->|[->|[->|[->|[->| ->]]]]]; cbn in NR; zlia).
ladder_close HS HEn1 EnKL. close_ST En1 HEn1 HS mem0 MEQ MEQW PRESW BUFW. }
rewrite branch_geu_U, En10, (U_lit En1 32257) in Hc by zlia. apply Bool.negb_true_iff in Hc. apply Z.ltb_ge in Hc. rename Hc into Hc5.
assert (K6 : kz = 6) by (clear - Hc5 NR KC; destruct KC as [->|[->|[->|[->|[->| ->]]]]]; cbn in NR; zlia).
ladder_close HS HEn1 EnKL. close_ST En1 HEn1 HS mem0 MEQ MEQW PRESW BUFW.
Qed.
Local Ltac class_close HS HEn CLV CLT :=
apply (st_ok_pin_regU _ _ _ 8%bv (SOff aCL 0)) in HS;
[ | intros X; discriminate
| lazymatch goal with |- U ?E _ = U _ (sr_get ?sr ?r) => let t := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with t end;
lazymatch goal with |- U ?E _ = U _ ?t => replace t with CLT by (vm_compute; reflexivity) end;
apply U_eq_by_zev; [reflexivity | clear; vm_compute; reflexivity |]; rewrite CLV;
cbn [zev]; unfold rho_of, aCL; rewrite (HEn 39%nat (ltHAV 39 eq_refl)), (eq_refl : ew E0 39 = w64 cl); unfold w64;
rewrite unsigned_lit_small by zlia; rewrite Z.add_0_r; apply zcanon_id; unfold M64; zlia ];
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS;
forget_regs HS 80%nat ([5; 6; 12; 14; 15; 16; 17]%bv : list (bv 5));
apply (YP03.st_ok_prune tfibsegs _ _ _ [] []) in HS;
lazymatch type of HS with st_ok _ _ ?ss _ => replace ss with MS_E in HS by (vm_compute; reflexivity) end.
Lemma missB : forall W0 c, at_STM MS_L W0 c -> SRr tfibsegs W0 c (at_STM MS_E).
Proof.
intros W0 c (-> & ms & mat & En & -> & HEn & HS & MEQW & PRESW & BUFW). pose proof Hwx_tfa as Hwx.
pose proof Hsp as (Hlo & Hbot & Hhi & Hal). pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
pose proof derived_ranges as DR. pose proof high_facts as LF. pose proof RZ_facts as (RF1 & RF2 & RF3 & RF4 & RF5 & RF6). pose proof NDv_facts as (ND1 & ND2 & ND3 & ND4 & ND5).
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, t_cache, t_unwinding in DR, LF.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) En _ _ HS eq_refl) as Hshape; cbn [ss_pc] in Hshape;
lazymatch type of Hshape with _ = mkst _ (Z_to_bv 64 (ss_pc ?s)) _ _ => let p := eval vm_compute in (ss_pc s) in change (ss_pc s) with p in Hshape | _ => idtac end.
rewrite Hshape in HS. rewrite Hshape. set (mem1 := ms_mem ms) in *.
assert (MEQ : forall x : word, ~ WINM1 (bv_unsigned x) -> mem1 x = mem1 x) by (intros; reflexivity).
srr_run_sh tfibtbl_rtA_ok HS. frame_accM HEn.
assert (ZR8 : zev (rho_of En) (SAlu ALU_AND (SOff 10 7) (SLit 18446744073709551608)) = R8v).
{ clear - HEn Hn RF4.
cbn [zev zalu_raw]. unfold rho_of. rewrite (HEn 10%nat (ltHAV 10 eq_refl)), E10, Hn. unfold w64. rewrite unsigned_lit_small by zlia.
rewrite (zcanon_id (n + 7)) by (unfold M64; zlia). rewrite (zcanon_id 18446744073709551608) by (unfold M64; zlia).
change 18446744073709551608 with (2 ^ 64 - 8). rewrite land_m8_64 by zlia. unfold R8v.
pose proof (Z.div_mod (n + 7) 8 ltac:(zlia)). pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(zlia)). rewrite zcanon_id; unfold M64; zlia. }
apply (st_ok_pin_regU _ _ _ 10%bv (SOff aR8 0)) in HS. 2:{ intros X; discriminate. }
2:{ clear - HEn ZR8 DR. apply U_eq_by_zev; [reflexivity | reflexivity |]. cbn [sr_get ss_regs nth]. unfold aR8.
change (zev (rho_of En) (SOff 38 0) = zcanon (zalu_raw 63 64 ALU_ADD (zev (rho_of En) (SAlu ALU_AND (SOff 10 7) (SLit 18446744073709551608))) (zev (rho_of En) (SLit 0)))).
rewrite ZR8. cbn [zev zalu_raw]. unfold rho_of. rewrite (HEn 38%nat (ltHAV 38 eq_refl)), (eq_refl : ew E0 38 = w64 R8v). unfold w64.
rewrite unsigned_lit_small by zlia. zcanon_simp. zlia. }
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
apply (st_ok_pin_regU _ _ _ 11%bv (SLit 0)) in HS. 2:{ intros X; discriminate. }
2:{ clear - HEn ZR8 DR. apply U_eq_by_zev; [reflexivity | reflexivity |]. cbn [sr_get ss_regs nth].
change (zev (rho_of En) (SLit 0) = zcanon (zalu_raw 63 64 ALU_AND (zcanon (zalu_raw 63 64 ALU_ADD (zev (rho_of En) (SAlu ALU_AND (SOff 10 7) (SLit 18446744073709551608))) (zev (rho_of En) (SLit 0)))) (zev (rho_of En) (SLit 7)))).
rewrite ZR8. cbn [zev zalu_raw]. zcanon_simp. rewrite Z.add_0_r, land_7_mod by zlia. replace (R8v mod 8) with 0 by zlia. reflexivity. }
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_to_sh tfibtbl_rtA_ok HS 0x33304. frame_accM HEn.
apply (st_ok_pin_regU _ _ _ 20%bv (SOff aRZ 0)) in HS. 2:{ intros X; discriminate. }
2:{ pose proof kz_cases as KC. clear - HEn KC. pin_zev. unfold aRZ, aKL. rewrite (HEn 58%nat (ltHAV 58 eq_refl)), (HEn 57%nat (ltHAV 57 eq_refl)), EaRZ, EaKL.
unfold w64, RZ, rz_of. destruct KC as [->|[->|[->|[->|[->| ->]]]]]; vm_compute; reflexivity. }
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_to_sh tfibtbl_rtA_ok HS 0x33314. frame_accM HEn.
apply (st_ok_pin_regU _ _ _ 19%bv (SOff aND 0)) in HS. 2:{ intros X; discriminate. }
2:{ clear - HEn ND1 ND5 RF1 DR. pin_zev. unfold aND, aR8, aRZ. rewrite (HEn 63%nat (ltHAV 63 eq_refl)), (HEn 38%nat (ltHAV 38 eq_refl)), (HEn 58%nat (ltHAV 58 eq_refl)), EaND, EaRZ,
(eq_refl : ew E0 38 = w64 R8v). unfold w64. rewrite !unsigned_lit_small by zlia. zcanon_simp. zlia. }
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_sh tfibtbl_rtA_ok HS. frame_accM HEn.
srr_branch_sh tfibtbl_rtA_ok HS.
2:{ exfalso. clear - Hc HEn ND5. rewrite branch_geu_U in Hc. apply Bool.negb_false_iff in Hc. apply Z.ltb_lt in Hc. revert Hc.
rewrite !U_zev by reflexivity. cbn [zev zalu_raw]. unfold rho_of, aND.
rewrite (HEn 63%nat (ltHAV 63 eq_refl)), EaND. unfold w64. rewrite unsigned_lit_small by zlia.
rewrite (zcanon_id (NDv + 0)) by (unfold M64; zlia). change (zcanon (-1)) with (2 ^ 64 - 1). rewrite lxor_ones64 by zlia.
zcanon_simp. zlia. }
clear Hc.
srr_run_sh tfibtbl_rtA_ok HS. frame_accM HEn.
srr_branch_sh tfibtbl_rtA_ok HS.
-
rewrite branch_ltu_U, (U_lit En 512) in Hc by zlia. apply Z.ltb_lt in Hc.
assert (EN : U En (SOff 63 0) = NDv) by (clear - HEn ND5; apply U_atom; [rewrite (HEn 63%nat (ltHAV 63 eq_refl)); exact EaND | zlia]). rewrite EN in Hc.
assert (K3 : 3 <= kz) by (clear - Hc ND4 Hkz; zlia).
srr_run_to_sh tfibtbl_rtA_ok HS 0x37820. frame_accM HEn.
class_close HS HEn (CL_hi_E En HEn K3) CL_hi.
lazymatch type of HS with st_ok _ ?E2 _ _ => set (EnE := E2) in HS end.
assert (HEnE : forall j, (j < aHAV)%nat -> ew EnE j = ew E0 j) by (intros j Hj; subst EnE; unfold aHAV in Hj; rewrite ew_havoc_old by zlia; apply HEn; exact Hj).
close_ST EnE HEnE HS mem1 MEQ MEQW PRESW BUFW.
-
rewrite branch_ltu_U, (U_lit En 512) in Hc by zlia. apply Z.ltb_ge in Hc.
assert (EN : U En (SOff 63 0) = NDv) by (clear - HEn ND5; apply U_atom; [rewrite (HEn 63%nat (ltHAV 63 eq_refl)); exact EaND | zlia]). rewrite EN in Hc.
assert (K2 : kz <= 2) by (clear - Hc ND3 Hkz; pose proof kz_cases as KC; destruct KC as [->|[->|[->|[->|[->| ->]]]]]; cbn in ND3; zlia).
srr_run_to_sh tfibtbl_rtA_ok HS 0x37820. frame_accM HEn.
class_close HS HEn (CL_lo_E En HEn K2) CL_lo.
lazymatch type of HS with st_ok _ ?E2 _ _ => set (EnE := E2) in HS end.
assert (HEnE : forall j, (j < aHAV)%nat -> ew EnE j = ew E0 j) by (intros j Hj; subst EnE; unfold aHAV in Hj; rewrite ew_havoc_old by zlia; apply HEn; exact Hj).
close_ST EnE HEnE HS mem1 MEQ MEQW PRESW BUFW.
Qed.
Lemma missC : forall W0 c, at_STM MS_E W0 c -> SRr tfibsegs W0 c (at_STM MS_CALL).
Proof.
intros W0 c (-> & ms & mat & En & -> & HEn & HS & MEQW & PRESW & BUFW). pose proof Hwx_tfa as Hwx.
pose proof Hsp as (Hlo & Hbot & Hhi & Hal). pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
pose proof derived_ranges as DR. pose proof high_facts as LF. pose proof RZ_facts as (RF1 & RF2 & RF3 & RF4 & RF5 & RF6). pose proof NDv_facts as (ND1 & ND2 & ND3 & ND4 & ND5).
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, t_cache, t_unwinding in DR, LF.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) En _ _ HS eq_refl) as Hshape; cbn [ss_pc] in Hshape;
lazymatch type of Hshape with _ = mkst _ (Z_to_bv 64 (ss_pc ?s)) _ _ => let p := eval vm_compute in (ss_pc s) in change (ss_pc s) with p in Hshape | _ => idtac end.
rewrite Hshape in HS. rewrite Hshape. set (mem1 := ms_mem ms) in *.
assert (MEQ : forall x : word, ~ WINM1 (bv_unsigned x) -> mem1 x = mem1 x) by (intros; reflexivity).
srr_run_sh tfibtbl_rtA_ok HS. frame_accM HEn.
apply (st_ok_pin_regU _ _ _ 9%bv (SOff aP 0)) in HS;
[ | intros X; discriminate
| clear - T SB HEn DR LF Hcl Hcnt Hv Hn; pin_zev; unfold aP;
rewrite (HEn 40%nat (ltHAV 40 eq_refl)), (HEn 32%nat (ltHAV 32 eq_refl)), (HEn 39%nat (ltHAV 39 eq_refl)), EaP, EaT, (eq_refl : ew E0 39 = w64 cl);
unfold w64; rewrite !unsigned_lit_small by (unfold Pv, t_cache in *; zlia); unfold Pv, t_cache in *; zcanon_simp; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_to_sh tfibtbl_rtA_ok HS 0x37ddc. frame_accM HEn.
close_ST En HEn HS mem1 MEQ MEQW PRESW BUFW.
Qed.
Lemma miss1 : SRr tfibsegs W cfg0 (at_STM MS_CALL).
Proof.
eapply SRr_bind; [exact missA|]. intros W1 c1 _ H1.
eapply SRr_bind; [exact (missB W1 c1 H1)|]. intros W2 c2 _ H2. exact (missC W2 c2 H2).
Qed.
End e.
End d.
