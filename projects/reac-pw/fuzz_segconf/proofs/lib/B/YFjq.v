(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AFjq.v, with its module paths changed, names TfibSyms -> CmdBSyms and its addresses moved to plugin-hostd/fuzz_command's ASan build. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_command/lib/A/AFjq.v (donor image sha256 c0661b96b5bd), with its module paths changed, names CmdBSyms -> SegBSyms and its addresses moved to reac-pw/fuzz_segconf's ASan build. *)
(* Modified by Theorem Labs, 2026-10: the image-B copy (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca) of lib/A/AFjq.v, derived mechanically (derive_y.py b7b132fb12a7; every changed numeral checked against alreloc.py a5c53bb2bed4 and against image B), with its module paths changed (lib/A to lib/B) and its addresses moved to reac-pw/fuzz_segconf's ASan+UBSan build. The comments are the A file's. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YB1w YE3d YB1q YFhy YFhz YFi0 YFi4 YFi9 YB1h YFjm YFid YFie YFif YFig YFjv YFjw YFjx YFjh YFjn YFjo YFjk YFjl YFjp.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Set Printing Depth 50. Set Printing Width 180.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Ltac zlia := first [ lia | ceil; unfold zone3, zone3cases, off_img, in_app, app_addr, in_band_rw, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPrimResvSize, kSpaceSize, kPtrArrayResv, kMaxNumChunks in *; lia ].
Ltac zcanon_simp :=
repeat match goal with
| |- context [zcanon ?x] =>
lazymatch x with
| context [zcanon _] => fail
| context [Z.shiftl _ _] => fail | context [Z.shiftr _ _] => fail | context [Z.land _ _] => fail
| context [Z.lor _ _] => fail | context [Z.lxor _ _] => fail
| _ => rewrite (zcanon_id x) by (unfold M64; zlia)
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
Section g.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (n : Z) (ch : list Z).
Variables (idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 : Z).
Variable mb : Z.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let pT : Z := bv_unsigned (getr regs0 11).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Let Qb : Z := ly_Q ly.
Local Abbreviation R8v := (@YFjm.R8v n).
Local Abbreviation N8D := (@YFjm.N8D n).
Local Abbreviation NDv := (@YFjm.NDv n).
Local Abbreviation MSv := (@YFjm.MSv n).
Local Abbreviation SHBv := (@YFjm.SHBv).
Local Abbreviation QSv := (@YFjm.QSv ly idx).
Local Abbreviation Kv := (@YFjm.Kv mb).
Local Abbreviation Uv := (@YFjm.Uv mb).
Local Abbreviation ENDv := (@YFjm.ENDv n mb).
Local Abbreviation TLv := (@YFjm.TLv n).
Local Abbreviation UEv := (@YFjm.UEv n mb).
Local Abbreviation RLv := (@YFjm.RLv n).
Local Abbreviation SMv := (@YFjm.SMv mb).
Local Abbreviation PBv := (@YFjm.PBv n mb).
Local Abbreviation LGv := (@YFjm.LGv n).
Local Abbreviation BSLv := (@YFjm.BSLv n).
Local Abbreviation tr := (@YFjm.tr ch).
Local Abbreviation XW := (@YFjm.XW ly n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation E0 := (@YFjm.E0 ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation Er := (@YFjm.Er ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation E1 := (@YFjm.E1 ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation E2 := (@YFjm.E2 ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation E4 := (@YFjm.E4 ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation E8 := (@YFjm.E8 ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation E10 := (@YFjm.E10 ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaT := (@YFjm.EaT ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaC := (@YFjm.EaC ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaSB := (@YFjm.EaSB ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaTOP := (@YFjm.EaTOP ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaR8 := (@YFjm.EaR8 ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaQ := (@YFjm.EaQ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaRES := (@YFjm.EaRES ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaNCH := (@YFjm.EaNCH ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaMS := (@YFjm.EaMS ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaMAP := (@YFjm.EaMAP ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaEND := (@YFjm.EaEND ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaSHB := (@YFjm.EaSHB ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaTL := (@YFjm.EaTL ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaQS := (@YFjm.EaQS ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaBSL := (@YFjm.EaBSL ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaSM := (@YFjm.EaSM ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaUE := (@YFjm.EaUE ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaND := (@YFjm.EaND ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaRL := (@YFjm.EaRL ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaN8D := (@YFjm.EaN8D ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaPB := (@YFjm.EaPB ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Hypothesis LY : layout_ok ly.
Hypothesis IMG : img_cover ly.
Hypothesis Hn : getr regs0 10 = w64 n.
Hypothesis Htp : getr regs0 4 = w64 TFIB_TP.
Hypothesis Hra : YK0s.ret_ok (getr regs0 1).
Hypothesis Hra4096 : 4096 <= bv_unsigned (getr regs0 1).
Hypothesis Hsp : ly_stk_lo ly + MALLOC_IN_STK <= sp0 /\ sp0 - IFRAME <= pT /\ sp0 <= ly_stk_hi ly /\ sp0 mod 16 = 0.
(* the caller's trace object at p = a1 (RtDDefs.v amalloc_inner_realizes) *)
Hypothesis Hch : (1 <= length ch <= 30)%nat /\ pT mod 8 = 0 /\ pT + 16 + 8 * 30 <= ly_stk_hi ly /\ astrace_at tfibsegs W mem0 pT ch.
Hypothesis Nrange : 64513 <= n < MALLOC_MAX.
Hypothesis Hidx : 0 <= idx < kMaxNumChunks.
Hypothesis Hres : idx <= res <= kMaxNumChunks /\ res mod kPtrArrayEntriesPerCommit = 0.
Local Abbreviation mod0_of_mul := (@YFjm.mod0_of_mul).
Local Abbreviation size_facts := (@YFjm.size_facts n Nrange).
Local Abbreviation tr_length := (@YFjm.tr_length W ly regs0 mem0 ch Hch).
Local Abbreviation trace_obj := (@YFjm.trace_obj W ly regs0 mem0 ch idx res Hch Hidx).
Local Abbreviation high_facts := (@YFjm.high_facts _ W ly regs0 mem0 ch idx res LY IMG Hch Hidx Hres).
Local Abbreviation stack_ivs := (@YFjm.stack_ivs _ W ly regs0 mem0 ch idx res LY Hsp Hch Hidx Hres).
Local Abbreviation HCX := (@YFjm.HCX _ ly LY).
Hypothesis Hpres0 : forall a, sp0 - MALLOC_IN_STK <= a < sp0 - IFRAME -> apresent (w_H W) mem0 a.
Hypothesis Hmap : mb mod 4096 = 0 /\ mzone mb MSv.
Hypothesis Hmap_apart :
zdisjoint (mb, MSv) (T, kThreadObjSize) /\ zdisjoint (mb, MSv) (ly_C ly, kCtxMapSize) /\
zdisjoint (mb, MSv) (ly_prim ly, kPrimResvSize) /\ zdisjoint (mb, MSv) (Qb, kPtrArrayResv) /\
zdisjoint (mb, MSv) (ly_NB ly, kNodesBlockSize) /\ zdisjoint (mb, MSv) (ly_SB ly, kStoreBlockSize) /\
zdisjoint (mb, MSv) (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly).
Local Abbreviation map_facts := (@YFjm.map_facts _ W ly regs0 mem0 n ch idx res mb Hch Nrange Hidx Hres Hmap).
Local Abbreviation map_zone := (@YFjm.map_zone _ W ly regs0 mem0 n ch idx res mb Hch Nrange Hidx Hmap).
Local Abbreviation map_zoneN := (@YFjm.map_zoneN _ W ly regs0 mem0 n ch idx res mb Hch Nrange Hidx Hres Hmap).
Local Abbreviation map_in_band := (@YFjm.map_in_band _ W ly regs0 mem0 n ch idx res mb Hch Nrange Hidx Hmap).
Local Abbreviation map_off_img := (@YFjm.map_off_img _ n mb Hmap).
Local Abbreviation WINT := (@YFjm.WINT ly).
Local Abbreviation WINI := (@YFjm.WINI n).
Local Abbreviation WINM := (@YFjm.WINM ly n idx mb).
Local Abbreviation WIN := (@YFjm.WIN ly regs0 n idx mb).
Local Abbreviation WINN := (@YFjm.WINN ly regs0).
Local Abbreviation WINP := (@YFjm.WINP ly regs0 n).
Local Abbreviation WINP_WIN := (@YFjm.WINP_WIN ly regs0 n idx mb).
Local Abbreviation WIN1P := (@YFjm.WIN1P ly regs0 n).
Local Abbreviation WIN1 := (@YFjm.WIN1 ly regs0 n idx mb).
Local Abbreviation WIN1P_WINP := (@YFjm.WIN1P_WINP W ly regs0 mem0 n ch idx res mb Hch Hidx).
Local Abbreviation WIN1_WIN := (@YFjm.WIN1_WIN W ly regs0 mem0 n ch idx res mb Hch Hidx).
Local Abbreviation WIN1P_WIN1 := (@YFjm.WIN1P_WIN1 ly regs0 n idx mb).
Local Abbreviation LGv_range := (@YFjm.LGv_range n Nrange).
Local Abbreviation BSLv_range := (@YFjm.BSLv_range W ly regs0 mem0 n ch idx res mb Hch Nrange Hidx).
Local Abbreviation WSKELP := (@YFjm.WSKELP).
Local Abbreviation WSKEL1P := (@YFjm.WSKEL1P).
Local Abbreviation WMAP := (@YFjm.WMAP).
Local Abbreviation WSKEL := (@YFjm.WSKEL).
Local Abbreviation WSKEL1 := (@YFjm.WSKEL1).
Local Abbreviation win_sub := (@YFjm.win_sub).
Local Abbreviation win_sub_sound := (@YFjm.win_sub_sound W ly regs0 mem0 ch idx res mb Hch Hidx Hres).
Local Abbreviation in_win := (@YFjm.in_win).
Local Abbreviation WSKELP_WINP := (@YFjm.WSKELP_WINP _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hch Nrange Hidx Hres).
Local Abbreviation WSKEL1P_WIN1P := (@YFjm.WSKEL1P_WIN1P _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hch Nrange Hidx Hres).
Local Abbreviation WMAP_WINM := (@YFjm.WMAP_WINM _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hch Nrange Hidx Hres Hmap).
Local Abbreviation WSKEL_WIN := (@YFjm.WSKEL_WIN _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hch Nrange Hidx Hres Hmap).
Local Abbreviation WSKEL1_WIN1 := (@YFjm.WSKEL1_WIN1 _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hch Nrange Hidx Hres Hmap).
Local Abbreviation windows_in := (@YFjm.windows_in W ly regs0 mem0 ch idx res mb Hch Hidx Hres).
Local Abbreviation windows_WINP := (@YFjm.windows_WINP _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hch Nrange Hidx Hres).
Local Abbreviation windows_WIN1P := (@YFjm.windows_WIN1P _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hch Nrange Hidx Hres).
Local Abbreviation windows_WIN := (@YFjm.windows_WIN _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hch Nrange Hidx Hres Hmap).
Local Abbreviation windows_WIN1 := (@YFjm.windows_WIN1 _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hch Nrange Hidx Hres Hmap).
Local Abbreviation frame_WIN1P := (@YFjm.frame_WIN1P _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hch Nrange Hidx Hres).
Local Abbreviation frame_WIN1 := (@YFjm.frame_WIN1 _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hch Nrange Hidx Hres Hmap).
Local Abbreviation WINP_not_high := (@YFjm.WINP_not_high _ W ly regs0 mem0 n ch idx res mb LY IMG Hsp Hch Nrange Hidx Hres).
Local Abbreviation WIN_not_high := (@YFjm.WIN_not_high _ W ly regs0 mem0 n ch idx res mb LY IMG Hsp Hch Nrange Hidx Hres Hmap).
Variables (mat0 : list word).
Let H0 := w_H W.
Variables (regsI : bvmap 5 word).
(* the run starts with regsI: regs0 with sp = sp0 - IFRAME *)
Hypotheses (RIo : forall r : bv 5, r <> 2%bv -> getr regsI r = getr regs0 r) (RI2 : getr regsI 2 = w64 (sp0 - IFRAME)).
Let cfg0 : config := mkCfg (mkst regsI (w64 PC_asan_malloc) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Local Abbreviation all_disjoint_of_forall := (@YFjm.all_disjoint_of_forall).
Local Abbreviation img_rw_writable := (@YFjm.img_rw_writable W ly regs0 mem0 ch idx res mb Hch Hidx).
Local Abbreviation kept_of_frame := (@YFjm.kept_of_frame W ly regs0 mem0 ch idx res mb Hch Hidx).
Local Abbreviation SKEL_TAIL := (@YFjm.SKEL_TAIL).
Local Abbreviation blocks_facts := (@YFjm.blocks_facts _ ly LY IMG).
Local Abbreviation off_T := (@YFjm.off_T _ W ly regs0 mem0 ch idx res LY IMG Hch Hidx Hres).
Local Abbreviation off_C := (@YFjm.off_C _ W ly regs0 mem0 ch idx res LY IMG Hch Hidx Hres).
Local Abbreviation off_Q := (@YFjm.off_Q _ W ly regs0 mem0 ch idx res LY IMG Hch Hidx Hres).
Local Abbreviation off_NB := (@YFjm.off_NB _ ly LY IMG).
Local Abbreviation off_SB := (@YFjm.off_SB _ ly LY IMG).
Local Abbreviation off_shadow := (@YFjm.off_shadow W ly regs0 mem0 ch idx res mb Hch Hidx).
Ltac off_by tac :=
first [ apply off_img_high; tac | apply off_T; tac | apply off_C; tac | apply off_Q; tac | apply off_NB; tac | apply off_SB; tac
| apply map_off_img; tac | apply off_shadow; tac
| unfold off_img; unfold TFIB_IMG_LO; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; tac ].
Local Abbreviation DZONE := (@YFjm.DZONE ly).
Variable DPOST : Z -> (word -> option byte) -> Prop.
Local Abbreviation DZONE_disj := (@YFjm.DZONE_disj _ W ly regs0 mem0 n ch idx res mb LY IMG Hsp Hch Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation RFACTS := (@YFjm.RFACTS ly regs0).
Local Abbreviation zone_lit := (@YFjm.zone_lit _ ly regs0 LY IMG Hsp).
Local Abbreviation zone_irw := (@YFjm.zone_irw _ ly regs0 LY IMG Hsp).
Local Abbreviation zone_T := (@YFjm.zone_T _ W ly regs0 mem0 ch idx res LY IMG Hsp Hch Hidx Hres).
Local Abbreviation zone_C := (@YFjm.zone_C _ W ly regs0 mem0 ch idx res LY IMG Hsp Hch Hidx Hres).
Local Abbreviation tail_ext_ok := (@YFjm.tail_ext_ok _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Hch Nrange Hidx Hres).
Local Abbreviation RFACTS_map := (@YFjm.RFACTS_map _ W ly regs0 mem0 n ch idx res mb LY IMG Hch Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation at_ST := (@YFjm.at_ST _ W ly regs0 mem0 md0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation memset_stretch := (@YFjm.memset_stretch _ _ W ly regs0 mem0 n ch idx res mb Hsp Hch Nrange Hidx Hres Hmap Hmap_apart DPOST).
Ltac clearM := try clear DPOST; try clear Hmap_apart; try clear Hmap.
Local Abbreviation at_S := (@YFjm.at_S _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation at_N := (@YFjm.at_N _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation at_RETS := (@YFjm.at_RETS _ regs0 mem0).
Local Abbreviation pstable := (@YFjm.pstable).
Local Abbreviation stack_shaped := (@YFjm.stack_shaped).
Local Abbreviation window_present := (@YFjm.window_present W ly regs0 mem0 ch idx res Hch Hidx).
Local Abbreviation stack_present_of := (@YFjm.stack_present_of _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY Hsp Hch Hidx).
Local Abbreviation mid_not_WIN1P := (@YFjm.mid_not_WIN1P _ W ly regs0 mem0 n ch idx res mb LY IMG Hsp Hch Nrange Hidx Hres).
Local Abbreviation mid_not_WIN1 := (@YFjm.mid_not_WIN1 _ W ly regs0 mem0 n ch idx res mb LY IMG Hsp Hch Nrange Hidx Hres Hmap).
Local Abbreviation wins_ok := (@YFjm.wins_ok).
Local Abbreviation at_S_run_gen := (@YFjm.at_S_run_gen _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY Hsp Hch Hidx).
Local Abbreviation at_S_run_ecall_gen := (@YFjm.at_S_run_ecall_gen _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY Hsp Hch Hidx).
Local Abbreviation at_S_runP := (@YFjm.at_S_runP _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Hch Nrange Hidx Hres).
Local Abbreviation at_S_runM := (@YFjm.at_S_runM _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Hch Nrange Hidx Hres Hmap).
Local Abbreviation at_S_run_ecallP := (@YFjm.at_S_run_ecallP _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Hch Nrange Hidx Hres).
Local Abbreviation at_S_run_ecallM := (@YFjm.at_S_run_ecallM _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Hch Nrange Hidx Hres Hmap).
Local Abbreviation at_S_pin := (@YFjm.at_S_pin _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation at_S_arm := (@YFjm.at_S_arm _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation at_S_forget := (@YFjm.at_S_forget _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation at_S_noconds := (@YFjm.at_S_noconds _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation at_S_weaken := (@YFjm.at_S_weaken _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation at_S_facts := (@YFjm.at_S_facts _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation at_S_strengthen := (@YFjm.at_S_strengthen _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation at_S_eq := (@YFjm.at_S_eq _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation at_S_open := (@YFjm.at_S_open _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation CSAVEDS := (@YFjm.CSAVEDS).
Local Abbreviation sv_denot_SOff0 := (@YFjm.sv_denot_SOff0).
Local Abbreviation at_S_ret := (@YFjm.at_S_ret _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Htp Hra Hsp Hch Nrange Hidx Hres).
Local Abbreviation kept_of_frame2 := (@YFjm.kept_of_frame2 W ly regs0 mem0 ch idx res Hch Hidx).
Local Abbreviation at_N_cont := (@YFjm.at_N_cont _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY Hsp Hch Hidx).
Variables (B : asyms) (S : astate).
Hypothesis TS : SegBSyms B.
Hypothesis HTSD : ly_tsd ly = TFIB_TSD.
Hypothesis HARm : ARm B ly S (aview tfibsegs (w_H W) mem0).
Hypothesis Hgp : getr regs0 3 = w64 (as_gp B).
Hypothesis Hidx_def : idx = Z.of_nat (length (st_sec_arr S)).
Hypothesis Hres_def : res = st_sec_reserved S.
Hypothesis Hj0 : val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2784) 8 j0.
Hypothesis Hj1 : val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2800) 8 j1.
Hypothesis Hj2 : val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2808) 8 j2.
Hypothesis Hj3 : val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2816) 8 j3.
Hypothesis Hj4 : val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2872) 8 j4.
Hypothesis Hj5 : val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2880) 8 j5.
Hypothesis Hj9 : val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2904) 8 j9.
Hypothesis Hj6 : val_mem tfibsegs (mrestrict (w_H W) mem0) 0xa9418 8 j6.
Hypothesis Hj7 : val_mem tfibsegs (mrestrict (w_H W) mem0) 0xa9420 8 j7.
Hypothesis Hj8 : val_mem tfibsegs (mrestrict (w_H W) mem0) BSLv 8 j8.
Hypothesis Hi1 : val_mem tfibsegs (mrestrict (w_H W) mem0) (TFIB_INST + o_sec_stats) 8 i1.
Hypothesis Hi2 : val_mem tfibsegs (mrestrict (w_H W) mem0) (TFIB_INST + o_sec_stats + 16) 8 i2.
Hypothesis Hi3 : val_mem tfibsegs (mrestrict (w_H W) mem0) (TFIB_INST + o_sec_stats + 24) 8 i3.
Hypothesis HQT : qmeter S.
Local Abbreviation vis_present := (@YFjv.vis_present _ W ly regs0 mem0 ch idx res Hch Hidx DPOST B S HARm).
Local Abbreviation in_thread_junk := (@YFjv.in_thread_junk ly B S).
Local Abbreviation in_sec_junk := (@YFjv.in_sec_junk ly B S).
Local Abbreviation in_as_junk := (@YFjv.in_as_junk ly B S).
Local Abbreviation junk_word := (@YFjv.junk_word _ W ly regs0 mem0 ch idx res LY IMG Hch Hidx Hres DPOST B S HARm).
Local Abbreviation cell_sym := (@YFjv.cell_sym _ W ly mem0 B S TS HARm).
Local Abbreviation cell_lit := (@YFjv.cell_lit _ W ly mem0 B S TS HARm).
Local Abbreviation cell_state := (@YFjv.cell_state _ W ly mem0 B S HARm).
Local Abbreviation In_acells_sec := (@YFjv.In_acells_sec ly B S).
Local Abbreviation sec_vals := (@YFjv.sec_vals _ W ly mem0 idx res B S TS HARm Hidx_def Hres_def).
Local Abbreviation unwinding_val := (@YFjv.unwinding_val _ W ly mem0 B S HARm).
Local Abbreviation rw_writable := (@YFjv.rw_writable W ly regs0 mem0 ch idx res Hch Hidx DPOST S).
Local Abbreviation val_mem_mod8 := (@YFjv.val_mem_mod8 W ly regs0 mem0 ch idx res Hch Hidx DPOST S).
Local Abbreviation chunk_lit := (@YFjv.chunk_lit W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation chunk_lit_at := (@YFjv.chunk_lit_at W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation chunk_atom := (@YFjv.chunk_atom W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Hch Hidx DPOST S).
Local Abbreviation SREG0_ok := (@YFjw.SREG0_ok _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Hch Nrange Hidx Hres Hpres0 DPOST B S TS HTSD HARm Hidx_def Hres_def Hj0 Hj1 Hj2 Hj3 Hj4 Hj5 Hj9 Hj6 Hj7 Hj8 Hi1 Hi2 Hi3).
Local Abbreviation PAIRS_ok := (@YFjx.PAIRS_ok _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Hch Nrange Hidx Hres DPOST S).
Local Abbreviation FACTS_ok := (@YFjx.FACTS_ok _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hn Hsp Hch Nrange Hidx Hres DPOST S).
Local Abbreviation SEED_ok := (@YFjx.SEED_ok _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hn Htp Hsp Hch Nrange Hidx Hres Hpres0 regsI RIo RI2 DPOST B S TS HTSD HARm Hidx_def Hres_def Hj0 Hj1 Hj2 Hj3 Hj4 Hj5 Hj9 Hj6 Hj7 Hj8 Hi1 Hi2 Hi3).
Local Abbreviation PBUF := (@YFjh.PBUF W regs0 ch).
Local Abbreviation PBUF_stableP := (@YFjh.PBUF_stableP _ W ly regs0 mem0 n ch idx res mb LY IMG Hsp Hch Nrange Hidx Hres).
Local Abbreviation PBUF_stableM := (@YFjh.PBUF_stableM _ W ly regs0 mem0 n ch idx res mb LY IMG Hsp Hch Nrange Hidx Hres Hmap).
Local Abbreviation buf_addr := (@YFjh.buf_addr _ W ly regs0 mem0 ch LY Hsp Hch).
Local Abbreviation seg0 := (@YFjh.seg0 _ _ W ly regs0 mem0 md0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hn Htp Hsp Hch Nrange Hidx Hres Hpres0 mat0 regsI RIo RI2 DPOST B S TS HTSD HARm Hidx_def Hres_def Hj0 Hj1 Hj2 Hj3 Hj4 Hj5 Hj9 Hj6 Hj7 Hj8 Hi1 Hi2 Hi3).
Local Abbreviation appregs := (@YFjn.appregs).
Local Abbreviation st_ok_appregs := (@YFjn.st_ok_appregs _).
Local Abbreviation at_S_app := (@YFjn.at_S_app _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation WIN1N := (@YFjn.WIN1N ly regs0 n).
Local Abbreviation WINPN := (@YFjn.WINPN ly regs0 n).
Local Abbreviation WSKEL1N := (@YFjn.WSKEL1N).
Local Abbreviation WIN1N_WINPN := (@YFjn.WIN1N_WINPN W ly regs0 mem0 n ch idx res mb Hch Hidx).
Local Abbreviation windows_WIN1N := (@YFjn.windows_WIN1N _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hch Nrange Hidx Hres).
Local Abbreviation mid_not_WIN1N := (@YFjn.mid_not_WIN1N _ W ly regs0 mem0 n ch idx res mb LY IMG Hsp Hch Nrange Hidx Hres).
Local Abbreviation at_S_runN := (@YFjn.at_S_runN _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Hch Nrange Hidx Hres).
Local Abbreviation PBUF_stableN := (@YFjn.PBUF_stableN _ W ly regs0 mem0 n ch idx res mb LY IMG Hsp Hch Nrange Hidx Hres).
Local Abbreviation at_S_val := (@YFjn.at_S_val _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation memset_stretchW := (@YFjn.memset_stretchW _ W ly regs0 mem0 n ch idx res Hsp Hch Nrange Hidx Hres DPOST S).
Local Abbreviation at_S_memset := (@YFjn.at_S_memset _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Hsp Hch Nrange Hidx Hres DPOST S).
Local Abbreviation WIN1T := (@YFjn.WIN1T ly regs0 n idx mb).
Local Abbreviation WIN1T_WIN := (@YFjn.WIN1T_WIN _ W ly regs0 mem0 n ch idx res mb Hch Nrange Hidx Hres Hmap).
Local Abbreviation windows_WIN1T := (@YFjn.windows_WIN1T _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hch Nrange Hidx Hres Hmap).
Local Abbreviation WIN1T_WIN1_aux := (@YFjn.WIN1T_WIN1_aux _ W ly regs0 mem0 n ch idx res mb Hch Nrange Hidx Hres Hmap).
Local Abbreviation mid_not_WIN1T := (@YFjn.mid_not_WIN1T _ W ly regs0 mem0 n ch idx res mb LY IMG Hsp Hch Nrange Hidx Hres Hmap).
Local Abbreviation at_S_runT := (@YFjn.at_S_runT _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Hch Nrange Hidx Hres Hmap).
Local Abbreviation at_S_run_ecallT := (@YFjn.at_S_run_ecallT _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Hch Nrange Hidx Hres Hmap).
Local Abbreviation PBUFW := (@YFjn.PBUFW regs0 ch).
Local Abbreviation PBUFW_stableT := (@YFjn.PBUFW_stableT _ W ly regs0 mem0 n ch idx res mb LY IMG Hsp Hch Nrange Hidx Hres Hmap).
Local Abbreviation WIN1S := (@YFjo.WIN1S ly regs0 n idx mb).
Local Abbreviation WSKEL1S := (@YFjo.WSKEL1S).
Local Abbreviation WIN1S_WIN1T := (@YFjo.WIN1S_WIN1T ly regs0 n idx mb).
Local Abbreviation WIN1S_WIN := (@YFjo.WIN1S_WIN _ W ly regs0 mem0 n ch idx res mb Hch Nrange Hidx Hres Hmap).
Local Abbreviation windows_WIN1S := (@YFjo.windows_WIN1S _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hch Nrange Hidx Hres Hmap).
Local Abbreviation mid_not_WIN1S := (@YFjo.mid_not_WIN1S _ W ly regs0 mem0 n ch idx res mb LY IMG Hsp Hch Nrange Hidx Hres Hmap).
Local Abbreviation at_S_runS := (@YFjo.at_S_runS _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Hch Nrange Hidx Hres Hmap).
Local Abbreviation at_S_run_ecallS := (@YFjo.at_S_run_ecallS _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Hch Nrange Hidx Hres Hmap).
Local Abbreviation brun := (@YFjo.brun).
Local Abbreviation run_ok := (@YFjo.run_ok n mb).
Local Abbreviation PS := (@YFjo.PS regs0 n ch mb).
Local Abbreviation runs_not_WIN1S := (@YFjo.runs_not_WIN1S _ W ly regs0 mem0 n ch idx res mb LY IMG Hsp Hch Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation runs_not_stack := (@YFjo.runs_not_stack _ W ly regs0 mem0 n ch idx res mb LY Hsp Hch Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation runs_off_stack := (@YFjo.runs_off_stack _ W ly regs0 mem0 n ch idx res mb LY Hch Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation PS_stable := (@YFjo.PS_stable _ W ly regs0 mem0 n ch idx res mb LY IMG Hsp Hch Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation cut1 := (@YFjo.cut1).
Local Abbreviation cut := (@YFjo.cut).
Local Abbreviation cut_sound := (@YFjo.cut_sound _ W ly regs0 mem0 n ch idx res mb Hch Nrange Hidx Hres Hmap DPOST S).
Local Abbreviation cut_ok := (@YFjo.cut_ok W ly regs0 mem0 n ch idx res mb Hch Hidx Hres DPOST S).
Local Abbreviation at_S_memsetS := (@YFjo.at_S_memsetS _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY Hsp Hch Nrange Hidx Hres Hmap Hmap_apart DPOST S).
Local Abbreviation skel_okb := (@YFjo.skel_okb).
Local Abbreviation skel_cases := (@YFjo.skel_cases idx res Hidx Hres S Hidx_def Hres_def).
Local Abbreviation skel_apart := (@YFjo.skel_apart _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Hch Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation skel_u64 := (@YFjo.skel_u64 _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Hch Nrange Hidx Hres Hmap DPOST S Hidx_def Hres_def).
Local Abbreviation memset_ext_of_skel := (@YFjo.memset_ext_of_skel _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Hch Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation memset_u64_of_skel := (@YFjo.memset_u64_of_skel _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Hch Nrange Hidx Hres Hmap DPOST S Hidx_def Hres_def).
Local Abbreviation WIN1R := (@YFjo.WIN1R ly regs0 n mb).
Local Abbreviation WSKEL1R := (@YFjo.WSKEL1R).
Local Abbreviation WIN1R_WIN1S := (@YFjo.WIN1R_WIN1S ly regs0 n idx mb).
Local Abbreviation WIN1R_WIN := (@YFjo.WIN1R_WIN _ W ly regs0 mem0 n ch idx res mb Hch Nrange Hidx Hres Hmap).
Local Abbreviation windows_WIN1R := (@YFjo.windows_WIN1R _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hch Nrange Hidx Hres Hmap).
Local Abbreviation mid_not_WIN1R := (@YFjo.mid_not_WIN1R _ W ly regs0 mem0 n ch idx res mb LY IMG Hsp Hch Nrange Hidx Hres Hmap).
Local Abbreviation at_S_runR := (@YFjo.at_S_runR _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Hch Nrange Hidx Hres Hmap).
Local Abbreviation at_S_run_ecallR := (@YFjo.at_S_run_ecallR _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Hch Nrange Hidx Hres Hmap).
Local Abbreviation PSR := (@YFjo.PSR regs0 n ch mb).
Local Abbreviation rstable := (@YFjo.rstable ly regs0 n mb).
Local Abbreviation rstable_true := (@YFjo.rstable_true ly regs0 n mb).
Local Abbreviation PSR_stable := (@YFjo.PSR_stable _ W ly regs0 mem0 n ch idx res mb LY IMG Hsp Hch Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation QSP := (@YFjo.QSP ly idx).
Local Abbreviation QS_not_WIN1R := (@YFjo.QS_not_WIN1R _ W ly regs0 mem0 n ch idx res mb LY IMG Hsp Hch Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation QSP_rstable := (@YFjo.QSP_rstable _ W ly regs0 mem0 n ch idx res mb LY IMG Hsp Hch Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation at_S_memsetSR := (@YFjo.at_S_memsetSR _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY Hsp Hch Nrange Hidx Hres Hmap Hmap_apart DPOST S).
Local Abbreviation chunk_eqb := (@YFjo.chunk_eqb).
Local Abbreviation chunk_eqb_eq := (@YFjo.chunk_eqb_eq idx res Hidx Hres S Hidx_def Hres_def).
Local Abbreviation subregionb := (@YFjo.subregionb).
Local Abbreviation subregionb_sound := (@YFjo.subregionb_sound W ly regs0 mem0 ch idx res Hch Hidx Hres DPOST S Hidx_def Hres_def).
Local Abbreviation submemb := (@YFjo.submemb).
Local Abbreviation submemb_sound := (@YFjo.submemb_sound W ly regs0 mem0 ch idx res Hch Hidx Hres DPOST S Hidx_def Hres_def).
Local Abbreviation at_S_submem := (@YFjo.at_S_submem _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Hch Hidx Hres DPOST S Hidx_def Hres_def).
Local Abbreviation at_S_addreg := (@YFjo.at_S_addreg _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation PSR_runs := (@YFjk.PSR_runs _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation place_WIN := (@YFjk.place_WIN ly regs0 n idx mb).
Local Abbreviation SH0 := (@YFjk.SH0 n mb).
Local Abbreviation SH1 := (@YFjk.SH1 n mb).
Local Abbreviation SH2 := (@YFjk.SH2 n mb).
Local Abbreviation SH_ok := (@YFjk.SH_ok _ W ly regs0 mem0 n ch idx res mb Hch Nrange Hidx Hres Hmap).
Local Abbreviation segG1 := (@YFjk.segG1 _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Hch Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation RX_stableS := (@YFjl.RX_stableS ly regs0 n idx mb).
Local Abbreviation rstable_and := (@YFjl.rstable_and ly regs0 n mb).
Local Abbreviation pstable_and := (@YFjl.pstable_and).
Local Abbreviation PSR_stableS' := (@YFjl.PSR_stableS' _ W ly regs0 mem0 n ch idx res mb LY IMG Hsp Hch Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation pairwise_disjoint_map := (@YFjl.pairwise_disjoint_map).
Local Abbreviation at_S_setchunks := (@YFjl.at_S_setchunks _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation chunk_ok_CVal_eqv := (@YFjl.chunk_ok_CVal_eqv).
Local Abbreviation RES2T_ne := (@YFjl.RES2T_ne ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Hidx Hres).
Local Abbreviation RES2T_eq := (@YFjl.RES2T_eq ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Hidx Hres).
Local Abbreviation sv_denot_eq_of_U := (@YFjl.sv_denot_eq_of_U ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation skel_apart_QS := (@YFjl.skel_apart_QS _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Hch Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation QSPX := (@YFjl.QSPX ly idx).
Local Abbreviation segNE := (@YFjl.segNE _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Hch Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation segEQa := (@YFjl.segEQa _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Hch Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation zev_SAlu := (@YFjl.zev_SAlu).
Local Abbreviation zev_SLit := (@YFjl.zev_SLit).
Local Abbreviation zev_SOff := (@YFjl.zev_SOff).
Local Abbreviation segJ2 := (@YFjl.segJ2 _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Hch Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation segJ := (@YFjl.segJ _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Hch Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation QR := (@YFjp.QR ly res).
Local Abbreviation segT1 := (@YFjp.segT1 _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hn Hsp Hch Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation DX := (@YFjp.DX ly regs0).
Local Abbreviation PD := (@YFjp.PD ly mem0 DPOST).
Local Abbreviation PD_rstable := (@YFjp.PD_rstable _ W ly regs0 mem0 n ch idx res mb LY IMG Hsp Hch Nrange Hidx Hres Hmap Hmap_apart DPOST).
Local Abbreviation PD_stableT := (@YFjp.PD_stableT _ W ly regs0 mem0 n ch idx res mb LY IMG Hsp Hch Nrange Hidx Hres Hmap Hmap_apart DPOST).
Local Abbreviation PSR_stableS := (@YFjp.PSR_stableS _ W ly regs0 mem0 n ch idx res mb LY IMG Hsp Hch Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation PD_stableS := (@YFjp.PD_stableS _ W ly regs0 mem0 n ch idx res mb LY IMG Hsp Hch Nrange Hidx Hres Hmap Hmap_apart DPOST).
Local Abbreviation PDX := (@YFjp.PDX ly mem0 DPOST).
Local Abbreviation PDX_rstable := (@YFjp.PDX_rstable _ W ly regs0 mem0 n ch idx res mb LY IMG Hsp Hch Nrange Hidx Hres Hmap Hmap_apart DPOST).
Local Abbreviation PDX_stableT := (@YFjp.PDX_stableT _ W ly regs0 mem0 n ch idx res mb LY IMG Hsp Hch Nrange Hidx Hres Hmap Hmap_apart DPOST).
Local Abbreviation PDX_stableS := (@YFjp.PDX_stableS _ W ly regs0 mem0 n ch idx res mb LY IMG Hsp Hch Nrange Hidx Hres Hmap Hmap_apart DPOST).
Local Abbreviation dx_okb := (@YFjp.dx_okb).
Local Abbreviation skel_apart_DX := (@YFjp.skel_apart_DX _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Hch Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation skel_apart_stk := (@YFjp.skel_apart_stk _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Hch Nrange Hidx Hres Hmap Hmap_apart S Hidx_def Hres_def).
Local Abbreviation at_S_depot := (@YFjp.at_S_depot _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Hch Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation SH3 := (@YFjp.SH3 n mb).
Local Abbreviation SH4 := (@YFjp.SH4 n mb).
Local Abbreviation shadow_marks := (@YFjp.shadow_marks _ W ly regs0 mem0 n ch idx res mb Hch Nrange Hidx Hres Hmap).
Local Abbreviation SH34_ok := (@YFjp.SH34_ok _ W ly regs0 mem0 n ch idx res mb Hch Nrange Hidx Hres Hmap).
Local Abbreviation segT2b := (@YFjp.segT2b _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hn Hsp Hch Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation segT2 := (@YFjp.segT2 _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hn Hsp Hch Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Ltac addr_tac :=
cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi];
rewrite ?EaT, ?EaC, ?EaTOP, ?EaSB, ?EaQ, ?EaMAP, ?EaQS, ?EaBSL, ?EaSM, ?EaPB, ?E2; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, w64, ly_bot, kStackSpan, t_unwinding, t_cache, t_stats, TFIB_IMG_END, UNW_STK, BST_SIZE, MALLOC_IN_STK, IFRAME, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *;
rewrite ?unsigned_lit_small by zlia; zlia.
Local Ltac denot_tac :=
cbn [sv_denot]; rewrite ?EaT, ?EaC, ?EaTOP, ?EaSB, ?EaQ, ?EaMAP, ?E2; unfold w64, ly_bot, kStackSpan in *;
first [ rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| rewrite Zbv_add_unsigned; f_equal; zlia
| rewrite unsigned_lit_small by zlia; f_equal; zlia
| reflexivity ].
Local Ltac clearP := try clear Hmap_apart; try clear Hmap.
Local Ltac s_station HR ss' :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let H2 := fresh "HR" in
pose proof (at_S_eq Wx md X P ss ss' W' c' HR ltac:(vm_compute; reflexivity)) as H2; clear HR; rename H2 into HR end.
Local Ltac s_runP HR tbl tblok stop ss' HX HP :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let st := eval vm_compute in (snd (sym_run_toN_sh tfibsegs tbl FUEL stop ss)) in
eapply SRr_bind;
[ eapply (at_S_runP Wx tbl tblok stop md X P ss ss' st W' c' HR);
[ vm_compute; reflexivity | exact I | exact HX | vm_compute; reflexivity | exact HP | vm_compute; reflexivity ]
| clear HR; let W2 := fresh "W" in let c2 := fresh "c" in intros W2 c2 _ HR ] end.
Local Ltac s_runM HR tbl tblok stop ss' HX HP :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let st := eval vm_compute in (snd (sym_run_toN_sh tfibsegs tbl FUEL stop ss)) in
eapply SRr_bind;
[ eapply (at_S_runM Wx tbl tblok stop md X P ss ss' st W' c' HR);
[ vm_compute; reflexivity | exact I | exact HX | vm_compute; reflexivity | exact HP | vm_compute; reflexivity ]
| clear HR; let W2 := fresh "W" in let c2 := fresh "c" in intros W2 c2 _ HR ] end.
Local Ltac s_ecallP HR tbl tblok ss' HX HP :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
eapply (at_S_run_ecallP Wx tbl tblok 0x7ffffff0 md X P ss ss' W' c' HR);
[ vm_compute; reflexivity | reflexivity | exact HX | vm_compute; reflexivity | exact HP | vm_compute; reflexivity ] end.
Local Ltac s_ecallM HR tbl tblok ss' HX HP :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
eapply (at_S_run_ecallM Wx tbl tblok 0x7ffffff0 md X P ss ss' W' c' HR);
[ vm_compute; reflexivity | reflexivity | exact HX | vm_compute; reflexivity | exact HP | vm_compute; reflexivity ] end.
Local Ltac unfold_atoms := unfold aT, aC, aSB, aTOP, aLEN, aJ0, aR8, aQ, aRES, aNCH, aMS, aMAP, aEND, aSHB, aTL, aQS, aBSL, aJ4, aJ5, aJ6, aJ7, aJ8, aJ9, aI1, aI2, aI3, aSM, aUE, aND, aRL, aN8DS, aPBS.
Local Ltac pin_zevS := apply U_eq_by_zev; [reflexivity | reflexivity |]; cbn [zev zalu_raw zmd_raw]; unfold rho_of; try unfold_atoms.
Local Ltac s_pin HR r e :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let t := eval vm_compute in (sr_get (ss_regs ss) r) in
let HU := fresh "HU" in
assert (HU : U E0 e = U E0 t);
[ | let H2 := fresh "HR" in
pose proof (at_S_pin Wx md X P ss W' c' r e HR ltac:(intros XX; discriminate XX) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HU) as H2;
clear HU HR; rename H2 into HR ] end.
Local Ltac s_arm HR cnd tk a b :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let HB := fresh "HB" in
assert (HB : branch_taken cnd (sv_denot E0 a) (sv_denot E0 b) = tk);
[ | let H2 := fresh "HR" in
pose proof (at_S_arm Wx md X P ss W' c' cnd tk a b HR ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HB) as H2;
clear HB HR; rename H2 into HR ] end.
Local Ltac s_forget HR k clob :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let H2 := fresh "HR" in
pose proof (at_S_forget Wx md X P ss W' c' k clob HR ltac:(unfold sHAV; cbv; zlia) eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as H2;
clear HR; rename H2 into HR end.
Local Ltac s_noconds HR :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let H2 := fresh "HR" in pose proof (at_S_noconds Wx md X P ss W' c' HR) as H2; clear HR; rename H2 into HR end.
Local Ltac arm_zevS := rewrite ?branch_geu_U, ?branch_ltu_U, ?branch_eq_U, ?branch_ne_U;
rewrite !U_zev by (vm_compute; reflexivity); cbn [zev zalu_raw zmd_raw]; unfold rho_of; try unfold_atoms.
Local Ltac U_zevS := rewrite U_zev by reflexivity; cbn [zev zalu_raw zmd_raw]; unfold rho_of; try unfold_atoms.
Local Ltac s_armR HR cnd tk r1 r2 :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let a := eval vm_compute in (sr_get (ss_regs ss) r1) in
let b := eval vm_compute in (sr_get (ss_regs ss) r2) in
s_arm HR cnd tk a b end.
Local Ltac ladder_arith Z :=
let MF := fresh "MF" in let SF := fresh "SF" in let NRx := fresh "NRx" in
pose proof map_facts as MF; pose proof size_facts as SF; pose proof Nrange as NRx;
arm_zevS; rewrite ?EaSHB, ?EaMAP, ?EaEND, ?EaTL, ?EaUE, ?EaRL, ?EaN8D, ?EaND, ?EaMS; unfold w64;
clear - Z MF SF NRx;
destruct MF as (M1x & M2x & M3x & K4x & U5x & E6x & UE7x & E8x & UE9x & MTx & MUx & SM1x & SM2x & SM3x & PBx & SMAx);
destruct SF as (Z1x & Z2x & Z3x & Z4x & Z5x & Z6x & Z7x & Z8x & Z9x & Z10x & Z11x & Z12x & Z13x & Z14x);
unfold YFjm.SHBv, YFjm.Kv, YFjm.Uv, YFjm.SMv, YFjm.PBv, MALLOC_MAX,
kLowShadowBeg, kHighShadowEnd, TFIB_IMG_END in *;
rewrite !unsigned_lit_small by zlia; zcanon_simp;
first [ rewrite (proj2 (Z.ltb_ge _ _)) by zlia | rewrite (proj2 (Z.ltb_lt _ _)) by zlia ]; reflexivity.
Local Ltac s_join HR k clob SJ := s_forget HR k clob; s_noconds HR; s_station HR SJ; apply SRr_ret; exact HR.
Local Ltac s_ladder RUN HR tbl tblok STOP Sl Slo Sh Sh2 Sh3 Shi SJ k clob HX HP :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let HQ := fresh "HQ" in
assert (HQ : SRr tfibsegs W' c' (at_S Wx md X P SJ));
[ let MZ := fresh "MZ" in pose proof map_zoneN as MZ; destruct MZ as [ZLO|ZHI];
[ s_armR HR BC_GEU true (14%bv : bv 5) (10%bv : bv 5); [ladder_arith ZLO|];
RUN HR tbl tblok 0x57fdc Sl HX HP;
s_armR HR BC_GEU true (14%bv : bv 5) (11%bv : bv 5); [ladder_arith ZLO|];
RUN HR tbl tblok STOP Slo HX HP;
s_join HR k clob SJ
| s_armR HR BC_GEU false (14%bv : bv 5) (10%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok 0x57e34 Sh HX HP;
s_armR HR BC_LTU true (7%bv : bv 5) (10%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok 0x57fdc Sh2 HX HP;
s_armR HR BC_GEU false (14%bv : bv 5) (11%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok 0x5801c Sh3 HX HP;
s_armR HR BC_GEU false (5%bv : bv 5) (11%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok STOP Shi HX HP;
s_join HR k clob SJ ]
| clear HR; eapply SRr_bind; [exact HQ | clear HQ; let W2 := fresh "WL" in let c2 := fresh "cL" in intros W2 c2 _ HR ] ]
end.
Local Ltac s_ladderW RUN HR tbl tblok STOP Sl Slo Sh Sh2 Sh3a Sh3 Shi SJ k clob HX HP :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let HQ := fresh "HQ" in
assert (HQ : SRr tfibsegs W' c' (at_S Wx md X P SJ));
[ let MZ := fresh "MZ" in pose proof map_zoneN as MZ; destruct MZ as [ZLO|ZHI];
[ s_armR HR BC_GEU true (14%bv : bv 5) (10%bv : bv 5); [ladder_arith ZLO|];
RUN HR tbl tblok 0x57fdc Sl HX HP;
s_armR HR BC_GEU true (14%bv : bv 5) (11%bv : bv 5); [ladder_arith ZLO|];
RUN HR tbl tblok STOP Slo HX HP;
s_join HR k clob SJ
| s_armR HR BC_GEU false (14%bv : bv 5) (10%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok 0x57e34 Sh HX HP;
s_armR HR BC_LTU true (7%bv : bv 5) (10%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok 0x57fdc Sh2 HX HP;
s_armR HR BC_GEU false (14%bv : bv 5) (11%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok 0x58018 Sh3a HX HP;
s_armR HR BC_LTU false (6%bv : bv 5) (11%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok 0x5801c Sh3 HX HP;
s_armR HR BC_GEU false (5%bv : bv 5) (11%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok STOP Shi HX HP;
s_join HR k clob SJ ]
| clear HR; eapply SRr_bind; [exact HQ | clear HQ; let W2 := fresh "WL" in let c2 := fresh "cL" in intros W2 c2 _ HR ] ]
end.
Local Ltac s_ladderM RUN HR tbl tblok STOP Slo Sh Sh2 Shi SJ k clob HX HP :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let HQ := fresh "HQ" in
assert (HQ : SRr tfibsegs W' c' (at_S Wx md X P SJ));
[ let MZ := fresh "MZ" in pose proof map_zoneN as MZ; destruct MZ as [ZLO|ZHI];
[ s_armR HR BC_GEU true (12%bv : bv 5) (22%bv : bv 5); [ladder_arith ZLO|];
RUN HR tbl tblok STOP Slo HX HP;
s_join HR k clob SJ
| s_armR HR BC_GEU false (12%bv : bv 5) (22%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok 0x336c4 Sh HX HP;
s_armR HR BC_LTU false (17%bv : bv 5) (22%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok 0x336c8 Sh2 HX HP;
s_armR HR BC_GEU false (16%bv : bv 5) (22%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok STOP Shi HX HP;
s_join HR k clob SJ ]
| clear HR; eapply SRr_bind; [exact HQ | clear HQ; let W2 := fresh "WL" in let c2 := fresh "cL" in intros W2 c2 _ HR ] ]
end.
Variables (Wy : world tfibsegs) (md1 : Model).
Variable RX : (word -> option byte) -> Prop.
Hypothesis RXs : rstable RX.
Hypothesis RXt : pstable WIN1T RX.
Local Ltac s_runS HR tbl tblok stop ss' HX HP :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let st := eval vm_compute in (snd (sym_run_toN_sh tfibsegs tbl FUEL stop ss)) in
eapply SRr_bind;
[ eapply (at_S_runS Wx tbl tblok stop md X P ss ss' st W' c' HR);
[ vm_compute; reflexivity | exact I | exact HX | vm_compute; reflexivity | exact HP | vm_compute; reflexivity ]
| clear HR; let W2 := fresh "W" in let c2 := fresh "c" in intros W2 c2 _ HR ] end.
Local Ltac s_runT HR tbl tblok stop ss' HX HP :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let st := eval vm_compute in (snd (sym_run_toN_sh tfibsegs tbl FUEL stop ss)) in
eapply SRr_bind;
[ eapply (at_S_runT Wx tbl tblok stop md X P ss ss' st W' c' HR);
[ vm_compute; reflexivity | exact I | exact HX | vm_compute; reflexivity | exact HP | vm_compute; reflexivity ]
| clear HR; let W2 := fresh "W" in let c2 := fresh "c" in intros W2 c2 _ HR ] end.
Definition SH5 : list (Z * Z * Z) :=
[(SMv + 768, SMv + 768 + N8D / 8, 0); (SHBv + UEv / 8, SMv + MSv / 8, 250); (SMv + 512, SMv + 768, 250); (SMv, SMv + 512, 250); (SMv + 768 + N8D / 8, SHBv + UEv / 8, 0)].
Definition SH6 : list (Z * Z * Z) := (Uv, Uv + 4096, 190) :: SH5.
Lemma user_marks : 8064 <= N8D / 8 <= R8v / 8 /\ (n mod 8 = 0 -> N8D / 8 = R8v / 8) /\ (n mod 8 <> 0 -> N8D / 8 + 1 = R8v / 8) /\ PBv = SMv + 768 + N8D / 8 /\ Uv = mb + 6144.
Proof.
pose proof map_facts as (_ & _ & _ & _ & U5 & _ & _ & _ & _ & _ & _ & _ & _ & _ & PB & _). pose proof map_zoneN as MZ.
pose proof size_facts as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & _). pose proof Nrange as NR. unfold MALLOC_MAX in Z1, NR. clear - U5 PB Z1 Z2 Z3 Z4 Z5 Z6 NR MZ.
apply Z.mod_divide in Z2 as [q Hq]; [|zlia]. apply Z.mod_divide in Z5 as [p Hp]; [|zlia]. rewrite Hq, Hp in *. rewrite !Z_div_mult by zlia.
unfold R8v, N8D in *. pose proof (Z.div_mod n 8 ltac:(zlia)) as D1. pose proof (Z.mod_pos_bound n 8 ltac:(zlia)) as B1.
pose proof (Z.div_mod (n + 7) 8 ltac:(zlia)) as D2. pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(zlia)) as B2.
repeat split; try zlia; intros H8; nia.
Qed.
Lemma SH56_ok : Forall run_ok SH5 /\ Forall run_ok SH6.
Proof.
pose proof shadow_marks as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9). pose proof user_marks as (B1 & _ & _ & _ & B5).
pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & _). clear - A1 A2 A3 A4 A5 A6 A7 A8 A9 B1 B5 Z8.
unfold SH5, SH6, run_ok. repeat split; repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; zlia.
Qed.
Section U.
Variables (X : Z -> Prop) (z : Z).
Hypothesis HXW : forall a, WIN a -> X a.
Hypothesis Hsmall : N8D / 8 < 18446744073709551615.
Let place_X : forall d len a, ((mb + 6144 <= d /\ d + len <= mb + MSv) \/ (SMv <= d /\ d + len <= SMv + MSv / 8)) -> d <= a < d + len -> X a :=
fun d len a PL Ha => HXW a (place_WIN d len a PL Ha).
Local Ltac s_memsetR HR ss' k d len vb retpc OK RS :=
lazymatch type of HR with at_S ?Wx ?md ?X (PSR _ ?sh ?R) ?ss ?W' ?c' =>
let ed := eval vm_compute in (sr_get (ss_regs ss) 10%bv) in
let el := eval vm_compute in (sr_get (ss_regs ss) 12%bv) in
let Ud := fresh "Ud" in let Ul := fresh "Ul" in let PL := fresh "PL" in
assert (Ud : U E0 ed = d); [|
assert (Ul : U E0 el = len); [|
assert (PL : (mb + 6144 <= d /\ d + len <= mb + MSv) \/ (SMv <= d /\ d + len <= SMv + MSv / 8)); [|
eapply SRr_bind;
[ eapply (at_S_memsetSR Wx md X sh R ss W' c' k ed el d len vb retpc HR RS eq_refl ltac:(vm_compute; reflexivity) ltac:(unfold sHAV; cbv; zlia)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) Ud Ul);
[ (clear; zlia) || zlia | clear; cbv; reflexivity | clear; zlia | clear; zlia | exact PL | exact OK | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply (place_X d len a PL Ha)
| exact (memset_ext_of_skel false d len ss ltac:(vm_compute; reflexivity) PL ltac:(intros XX; discriminate XX))
| exact (memset_u64_of_skel false ss ltac:(vm_compute; reflexivity)) ]
| clear HR Ud Ul; let W2 := fresh "W" in let c2 := fresh "c" in intros W2 c2 _ HR;
lazymatch type of HR with at_S _ _ _ _ ?ss2 _ _ => replace ss2 with ss' in HR by (vm_compute; reflexivity) end ] ] ] ] end.
Lemma segU1 : forall W' c, at_S Wy md1 X (PSR Wy SH4 (PDX Wy RX z)) T_R W' c -> SRr tfibsegs W' c (at_S Wy md1 X (PSR Wy SH5 (PDX Wy RX z)) U_QJ).
Proof.
intros W1 c HR. pose proof SH34_ok as [_ OK4]. pose proof SH56_ok as [OK5 _]. pose proof (PDX_rstable Wy RX RXs z) as RS.
pose proof (PSR_stableS Wy SH4 (PDX Wy RX z) OK4 (PDX_stableS Wy RX RXt z)) as HP4. pose proof (PSR_stableS Wy SH5 (PDX Wy RX z) OK5 (PDX_stableS Wy RX RXt z)) as HP5.
assert (HX : forall a, WIN1S a -> X a) by (intros a Ha; apply HXW, WIN1S_WIN, Ha).
pose proof map_facts as (M1 & M2 & M3 & _). pose proof map_zoneN as MZ. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in M1, M2.
pose proof size_facts as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & _). pose proof Nrange as NR. unfold MALLOC_MAX in Z1, Z8, NR.
pose proof shadow_marks as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9). pose proof user_marks as (B1 & B2 & B3 & B4 & B5).
s_arm HR BC_LTU true USH_LEN (SLit 18446744073709551615).
{ clear - M1 M2 M3 Z8 Z4 Z5 NR Hsmall MZ. arm_zevS. unfold USH_LEN. cbn [zev zalu_raw]. unfold_atoms. rewrite EaMAP, EaN8D. unfold w64. rewrite !unsigned_lit_small by zlia.
zcanon_simp. land_lits. rewrite !Z.shiftr_div_pow2 by zlia. change (2 ^ 3) with 8.
apply Z.mod_divide in M3 as [u Hu]; [|zlia]. apply Z.mod_divide in Z5 as [p Hp]; [|zlia]. rewrite Hu, Hp in *.
replace (u * 4096 + 6136 + (p * 8 + 0)) with ((u * 512 + 767 + p) * 8) by zlia. replace (u * 4096 + 6144) with ((u * 512 + 768) * 8) by zlia.
rewrite !Z_div_mult in * by zlia. zcanon_simp. apply Z.ltb_lt. zlia. }
s_runS HR tfibtbl_rtA tfibtbl_rtA_ok 0x9afd4 U_M5 HX HP4.
s_memsetR HR U_Q sM5 constr:(SMv + 768) constr:(N8D / 8) 0 0x3365c OK4 RS.
{ clear - M1 M2 M3 Z8 A7 MZ. U_zevS. rewrite (eq_refl : ew E0 47 = w64 SHBv), EaMAP. unfold w64, YFjm.SHBv in *. rewrite !unsigned_lit_small by zlia.
zcanon_simp. land_lits. rewrite Z.shiftr_div_pow2 by zlia. change (2 ^ 3) with 8.
apply Z.mod_divide in M3 as [u Hu]; [|zlia]. rewrite Hu in *. replace (u * 4096 + 6144) with ((u * 512 + 768) * 8) by zlia. rewrite Z_div_mult by zlia.
rewrite A7. replace (u * 4096) with ((u * 512) * 8) by zlia. rewrite Z_div_mult by zlia. zcanon_simp. zlia. }
{ clear - M1 M2 M3 Z8 Z4 Z5 NR MZ. U_zevS. unfold USH_LEN. cbn [zev zalu_raw]. unfold_atoms. rewrite EaMAP, EaN8D. unfold w64. rewrite !unsigned_lit_small by zlia.
zcanon_simp. land_lits. rewrite !Z.shiftr_div_pow2 by zlia. change (2 ^ 3) with 8.
apply Z.mod_divide in M3 as [u Hu]; [|zlia]. apply Z.mod_divide in Z5 as [p Hp]; [|zlia]. rewrite Hu, Hp in *.
replace (u * 4096 + 6136 + (p * 8 + 0)) with ((u * 512 + 767 + p) * 8) by zlia. replace (u * 4096 + 6144) with ((u * 512 + 768) * 8) by zlia.
rewrite !Z_div_mult in * by zlia. zcanon_simp. zlia. }
{ right. clear - A2 A3 A5 A6 B1 MZ. zlia. }
apply (PSR_runs Wy md1 X _ SH5 (PDX Wy RX z) U_Q) in HR.
2:{ intros m HF. pose proof (Forall_inv HF) as C0. pose proof (Forall_inv_tail HF) as B2'. clear HF.
unfold cut, SH4 in B2'. cbn [flat_map app] in B2'. unfold cut1 in B2'. cbn [fst snd] in B2'.
assert (G1 : (SHBv + UEv / 8 <? SMv + 768) = false) by (clear - A2 A5 MZ; apply Z.ltb_ge; zlia).
assert (G2 : (SMv + 768 + N8D / 8 <? SMv + MSv / 8) = true) by (clear - A2 A3 A5 A6 B1 MZ; apply Z.ltb_lt; zlia).
assert (G3 : (SMv + 512 <? SMv + 768) = true) by (apply Z.ltb_lt; zlia).
assert (G4 : (SMv + 768 + N8D / 8 <? SMv + 768) = false) by (clear - B1 MZ; apply Z.ltb_ge; zlia).
assert (G5 : (SMv <? SMv + 768) = true) by (apply Z.ltb_lt; zlia).
assert (G6 : (SMv + 768 + N8D / 8 <? SMv + 512) = false) by (clear - B1 MZ; apply Z.ltb_ge; zlia).
assert (G7 : (SMv + 768 <? SMv + 768) = false) by (apply Z.ltb_irrefl).
rewrite G1, G2, G3, G4, G5, G6, G7 in B2'. cbn [app] in B2'.
pose proof (Forall_inv B2') as C1. pose proof (Forall_inv (Forall_inv_tail B2')) as C2. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail B2'))) as C3.
pose proof (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail B2'))) as C4'. clear B2'.
rewrite Z.max_l in C1 by (clear - A2 A5 B1 MZ; zlia). rewrite Z.min_l in C2 by zlia. rewrite Z.min_l in C3 by zlia.
unfold SH5. apply Forall_cons; [exact C0|]. apply Forall_cons; [exact C1|]. apply Forall_cons; [exact C2|]. apply Forall_cons; [exact C3|].
apply Forall_cons; [|apply Forall_nil].
destruct (SMv + 768 + N8D / 8 <? SHBv + UEv / 8) eqn:G8; cbn [app] in C4'.
- pose proof (Forall_inv C4') as C4. rewrite Z.max_r in C4 by (clear - B1 MZ; zlia). exact C4.
- apply Z.ltb_ge in G8. intros a Ha. cbn [fst snd] in Ha. exfalso. clear - G8 Ha MZ. zlia. }
lazymatch type of HR with at_S ?Wx ?md ?X0 ?P ?ss ?W' ?c' =>
apply (at_S_submem Wx md X0 P ss W' c' (trimscratch (-2272) (ss_mem U_Q))) in HR; [| vm_compute; reflexivity | vm_compute; reflexivity] end.
s_forget HR kJQ CLOBJ. s_noconds HR. s_station HR U_QJ.
apply SRr_ret. exact HR.
Qed.
Lemma SH6_of_cut : forall m, Forall (brun m) ((Uv, Uv + 4096, 190) :: cut Uv (Uv + 4096) SH5) -> Forall (brun m) SH6.
Proof.
intros m HF. pose proof (Forall_inv HF) as C0. pose proof (Forall_inv_tail HF) as B'. clear HF.
pose proof shadow_marks as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9). pose proof user_marks as (B1 & _ & _ & _ & B5).
pose proof map_facts as (M1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _). pose proof map_zoneN as MZ. pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & _).
unfold cut, SH5 in B'. cbn [flat_map app] in B'. unfold cut1 in B'. cbn [fst snd] in B'.
destruct MZ as [ZLO|ZHI].
-
assert (BOT : Uv + 4096 < SMv) by (clear - ZLO B5 Z8; unfold MALLOC_MAX in *; zlia).
assert (G1 : forall x, SMv <= x -> (x <? Uv) = false) by (intros x Hx; apply Z.ltb_ge; clear - Hx BOT; zlia).
assert (G2 : forall x, SMv <= x -> (Uv + 4096 <? x) = true) by (intros x Hx; apply Z.ltb_lt; clear - Hx BOT; zlia).
rewrite !G1 in B' by (clear - A1 A2 A3 A4 A5 A6 A7 A8 A9 B1; zlia). rewrite !G2 in B' by (clear - A1 A2 A3 A4 A5 A6 A7 A8 A9 B1; zlia). cbn [app] in B'.
rewrite !Z.max_l in B' by (clear - A1 A2 A3 A4 A5 A6 A7 A8 A9 B1 BOT; zlia).
unfold SH6, SH5. apply Forall_cons; [exact C0 | exact B'].
-
assert (TOP : SMv + MSv / 8 < Uv) by (clear - ZHI B5; zlia).
assert (G1 : forall x, x <= SMv + MSv / 8 -> (x <? Uv) = true) by (intros x Hx; apply Z.ltb_lt; clear - Hx TOP; zlia).
assert (G2 : forall x, x <= SMv + MSv / 8 -> (Uv + 4096 <? x) = false) by (intros x Hx; apply Z.ltb_ge; clear - Hx TOP; zlia).
rewrite !G1 in B' by (clear - A1 A2 A3 A4 A5 A6 A7 A8 A9 B1; zlia). rewrite !G2 in B' by (clear - A1 A2 A3 A4 A5 A6 A7 A8 A9 B1; zlia). cbn [app] in B'.
rewrite !Z.min_l in B' by (clear - A1 A2 A3 A4 A5 A6 A7 A8 A9 B1 TOP; zlia).
unfold SH6, SH5. apply Forall_cons; [exact C0 | exact B'].
Qed.
Lemma segUe : n mod 8 = 0 -> forall W' c, at_S Wy md1 X (PSR Wy SH5 (PDX Wy RX z)) U_QJ W' c -> SRr tfibsegs W' c (at_S Wy md1 X (PSR Wy SH6 (PDX Wy RX z)) Ue_RET).
Proof.
intros H8 W1 c HR. pose proof SH56_ok as [OK5 OK6]. pose proof (PDX_rstable Wy RX RXs z) as RS.
pose proof (PSR_stableS Wy SH5 (PDX Wy RX z) OK5 (PDX_stableS Wy RX RXt z)) as HP5. pose proof (PSR_stableS Wy SH6 (PDX Wy RX z) OK6 (PDX_stableS Wy RX RXt z)) as HP6.
assert (HX : forall a, WIN1S a -> X a) by (intros a Ha; apply HXW, WIN1S_WIN, Ha).
pose proof map_facts as (M1 & M2 & M3 & _). pose proof map_zoneN as MZ. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in M1, M2.
pose proof size_facts as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & _). pose proof Nrange as NR. unfold MALLOC_MAX in Z1, Z8, NR.
pose proof user_marks as (B1 & B2 & B3 & B4 & B5).
s_arm HR BC_EQ true (SOff 10 0) (SOff aN8DS 0).
{ clear - H8 NR Hn Z4 Z6 MZ. arm_zevS. rewrite E10, Hn, EaN8D. unfold w64. rewrite !unsigned_lit_small by zlia. zcanon_simp. apply Z.eqb_eq.
unfold N8D in *. pose proof (Z.div_mod n 8 ltac:(zlia)). zlia. }
s_runS HR tfibtbl_rtA tfibtbl_rtA_ok 0x9afd4 Ue_MF HX HP5.
s_memsetR HR (ss_after_stretch Ue_MF (ss_mem Ue_MF) sMF CLOB_MS 0x33884) sMF constr:(Uv) 4096 190 0x33884 OK5 RS.
{ clear - M1 M2 Z8 B5 MZ. U_zevS. rewrite EaMAP. unfold w64. rewrite !unsigned_lit_small by zlia. zcanon_simp. zlia. }
{ clear. U_zevS. reflexivity. }
{ left. clear - Z8 B5 MZ. zlia. }
apply (PSR_runs Wy md1 X _ SH6 (PDX Wy RX z)) in HR; [|exact SH6_of_cut].
s_runS HR tfibtbl_rtA tfibtbl_rtA_ok 0x338ac (runto 0x338ac (ss_after_stretch Ue_MF (ss_mem Ue_MF) sMF CLOB_MS 0x33884)) HX HP6.
s_arm HR BC_EQ false (SOff aMAP 6128) (SOff aMAP 4096).
{ clear - M1 M2 Z8 MZ. arm_zevS. rewrite EaMAP. unfold w64. rewrite !unsigned_lit_small by zlia. zcanon_simp. apply Z.eqb_neq. zlia. }
s_runS HR tfibtbl_rtA tfibtbl_rtA_ok 0x338b4 (runto 0x338b4 (arm BC_EQ false (SOff aMAP 6128) (SOff aMAP 4096) (runto 0x338ac (ss_after_stretch Ue_MF (ss_mem Ue_MF) sMF CLOB_MS 0x33884)))) HX HP6.
s_arm HR BC_LTU false (SOff aMAP 6128) (SOff aMAP 4112).
{ clear - M1 M2 Z8 MZ. arm_zevS. rewrite EaMAP. unfold w64. rewrite !unsigned_lit_small by zlia. zcanon_simp. apply Z.ltb_ge. zlia. }
s_runS HR tfibtbl_rtA tfibtbl_rtA_ok 0x56ff0 Ue_RET HX HP6.
apply SRr_ret. exact HR.
Qed.
Definition PT (sh : list (Z * Z * Z)) (R : (word -> option byte) -> Prop) (m : word -> option byte) : Prop :=
PBUFW Wy m /\ (forall a, mb + 6144 <= a < mb + MSv -> apresent (w_H Wy) m a) /\
(forall a, SMv <= a < SMv + MSv / 8 -> a <> PBv -> apresent (w_H Wy) m a) /\ Forall (brun m) sh /\ R m.
Definition run_okT (r : Z * Z * Z) : Prop := run_ok r /\ (snd (fst r) <= PBv \/ PBv + 1 <= fst (fst r)).
Definition SH5o : list (Z * Z * Z) :=
[(SMv + 768, SMv + 768 + N8D / 8, 0); (SHBv + UEv / 8, SMv + MSv / 8, 250); (SMv + 512, SMv + 768, 250); (SMv, SMv + 512, 250); (PBv + 1, SHBv + UEv / 8, 0)].
Definition SH6o : list (Z * Z * Z) := (Uv, Uv + 4096, 190) :: SH5o.
Lemma SH56o_ok : n mod 8 <> 0 -> Forall run_okT SH5o /\ Forall run_okT SH6o.
Proof.
intros H8. pose proof shadow_marks as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9). pose proof user_marks as (B1 & _ & B3 & B4 & B5). specialize (B3 H8).
pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & _). pose proof map_facts as (M1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _). pose proof map_zoneN as MZ.
unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg in M1. unfold kHighShadowEnd in SM2. clear - A1 A2 A3 A4 A5 A6 A7 A8 A9 B1 B3 B4 B5 Z8 M1 SM2 MZ.
unfold SH5o, SH6o, run_okT, run_ok. repeat split; repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; zlia.
Qed.
Lemma PT_stableT : forall sh R, Forall run_okT sh -> pstable WIN1T R -> pstable WIN1T (PT sh R).
Proof.
intros sh R OK RS m m' FR (HB & HM & HSH & HR' & HQ).
pose proof map_facts as (M1 & M2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _). pose proof map_zoneN as MZ.
assert (U : forall a, (mb + 6144 <= a < mb + MSv) \/ (SMv <= a < SMv + MSv / 8) -> a <> PBv -> m' (w64 a) = m (w64 a)).
{ intros a Ha Hne. apply FR. unfold w64. rewrite unsigned_lit_small by (clear - Ha M1 M2 SM1 SM2 MZ; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighShadowBeg, kHighShadowEnd, ASAN_CEIL in *; zlia).
intros [Hw|[Hw|[Hw|Hw]]]; [exact (runs_not_WIN1S a Ha (or_introl Hw)) | exact (runs_not_WIN1S a Ha (or_intror (or_introl Hw))) | exact (runs_not_WIN1S a Ha (or_intror (or_intror Hw))) | clear - Hw Hne MZ; zlia]. }
split; [exact (PBUFW_stableT Wy m m' FR HB)|].
pose proof user_marks as (B1 & _ & _ & B4 & _). pose proof shadow_marks as (_ & A2 & A3 & _ & _ & A6 & _).
split; [intros a Ha; apply (apresent_same (w_H Wy) m); [apply (U a (or_introl Ha)); clear - Ha B4 B1 A2 A3 A6 M1 SM2 MZ; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighShadowEnd in *; zlia | exact (HM a Ha)]|].
split; [intros a Ha Hne; apply (apresent_same (w_H Wy) m); [exact (U a (or_intror Ha) Hne) | exact (HSH a Ha Hne)]|].
split; [|exact (RS m m' FR HQ)].
apply Forall_forall. intros r Hr a Ha. pose proof (proj1 (Forall_forall _ _) OK r Hr) as [RO RP]. pose proof (proj1 (Forall_forall _ _) HR' r Hr a Ha) as V.
rewrite (U a); [exact V | unfold run_ok in RO; clear - RO Ha MZ; zlia | clear - RP Ha MZ; zlia].
Qed.
Lemma segUo : n mod 8 <> 0 -> forall W' c, at_S Wy md1 X (PSR Wy SH5 (PDX Wy RX z)) U_QJ W' c -> SRr tfibsegs W' c (at_S Wy md1 X (PT SH6o (PDX Wy RX z)) Uo_RET).
Proof.
intros H8 W1 c HR. pose proof SH56_ok as [OK5 _]. pose proof (SH56o_ok H8) as [OK5o OK6o].
pose proof (PSR_stableS Wy SH5 (PDX Wy RX z) OK5 (PDX_stableS Wy RX RXt z)) as HP5.
pose proof (PT_stableT SH5o (PDX Wy RX z) OK5o (PDX_stableT Wy RX RXt z)) as HT5. pose proof (PT_stableT SH6o (PDX Wy RX z) OK6o (PDX_stableT Wy RX RXt z)) as HT6.
assert (HX : forall a, WIN1S a -> X a) by (intros a Ha; apply HXW, WIN1S_WIN, Ha).
assert (HXT : forall a, WIN1T a -> X a) by (intros a Ha; apply HXW, WIN1T_WIN, Ha).
pose proof map_facts as (M1 & M2 & M3 & K4 & U5 & E6 & UE7 & E8 & UE9 & MT & MU & SM1 & SM2 & SM3 & PB & SMA). pose proof map_zoneN as MZ. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in M1, M2. unfold kHighShadowBeg, kHighShadowEnd in SM1, SM2.
pose proof size_facts as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & _). pose proof Nrange as NR. unfold MALLOC_MAX in Z1, Z8, NR.
pose proof user_marks as (B1 & B2 & B3 & B4 & B5). specialize (B3 H8). pose proof shadow_marks as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
assert (PLfill : (mb + 6144 <= Uv /\ Uv + 4096 <= mb + MSv) \/ (SMv <= Uv /\ Uv + 4096 <= SMv + MSv / 8)) by (left; clear - B5 Z8 MZ; zlia).
s_arm HR BC_EQ false (SOff 10 0) (SOff aN8DS 0).
{ clear - H8 NR Hn Z4 Z6 MZ. arm_zevS. rewrite E10, Hn, EaN8D. unfold w64. rewrite !unsigned_lit_small by zlia. zcanon_simp. apply Z.eqb_neq.
unfold N8D in *. pose proof (Z.div_mod n 8 ltac:(zlia)). zlia. }
s_runS HR tfibtbl_rtA tfibtbl_rtA_ok 0x33688 Uo_L6 HX HP5.
s_ladderM s_runS HR tfibtbl_rtA tfibtbl_rtA_ok 0x336ec Uo_L6lo Uo_L6h Uo_L6h2 Uo_L6hi Uo_P0 sL6 CLOB_L6 HX HP5.
s_pin HR (10%bv : bv 5) (SOff aPBS 0).
{ clear - M1 M2 M3 Z8 Z4 Z5 NR A7 B4 MZ. pin_zevS. rewrite EaPB, (eq_refl : ew E0 47 = w64 SHBv), EaMAP, EaN8D. unfold w64, YFjm.SHBv in *.
rewrite B4 in *. rewrite A7 in *. rewrite !unsigned_lit_small by zlia.
zcanon_simp. land_lits. rewrite Z.shiftr_div_pow2 by zlia. change (2 ^ 3) with 8.
apply Z.mod_divide in M3 as [u Hu]; [|zlia]. apply Z.mod_divide in Z5 as [p Hp]; [|zlia]. rewrite Hu, Hp in *.
replace (u * 4096 + 6144 + (p * 8 + 0)) with ((u * 512 + 768 + p) * 8) by zlia. replace (u * 4096) with ((u * 512) * 8) by zlia. rewrite !Z_div_mult in * by zlia.
zcanon_simp. zlia. }
apply (at_S_addreg Wy md1 X _ _ _ _ R_pbS) in HR; [| reflexivity |].
2:{ intros E' m HE MEQ PRS [(HB & HM & HSH & HRs) HQ] HMok. pose proof (proj1 HE) as HEn.
assert (BP : base_val E' (Some aPBS) = PBv).
{ cbn [base_val]. unfold aPBS. rewrite (HEn 66%nat ltac:(unfold sHAV; zlia)), EaPB. unfold w64. apply unsigned_lit_small. clear - B4 B1 A2 A5 A3 A6 SM1 SM2 MZ. zlia. }
split.
- unfold region_ok, R_pbS. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite BP.
split; [clear - B4 B1 SM1 MZ; zlia|]. split; [clear - B4 B1 A2 A3 A5 A6 SM2 MZ; zlia|]. split; [|apply Forall_nil].
intros o Ho. apply apresent_writable_off; [off_by ltac:(clear - Ho B4 B1 SM1 A2 A3 A5 A6 SM2 MZ; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; zlia) |]. apply HSH. clear - Ho B4 B1 A2 A3 A5 A6 MZ. zlia.
- intros r2 Hr2. unfold extent_disjoint, R_pbS. cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite !BP.
lazymatch type of Hr2 with In _ ?l =>
pose proof (proj1 (forallb_forall _ _) (eq_refl : forallb (fun r => skel_okb false (skel r) && ((YP09.r_lo r <? YP09.r_hi r)
|| match YP09.r_base r with Some 2%nat => (- MALLOC_IN_STK <=? YP09.r_lo r) | _ => false end)) l = true) r2 Hr2) as CK end.
cbn beta in CK. apply andb_prop in CK as [CK1 CK2]. apply Bool.orb_prop in CK2 as [CK2|CK2].
+ apply Z.ltb_lt in CK2.
pose proof (skel_apart E' false PBv 1 HE ltac:(right; clear - B4 B1 A2 A3 A5 A6 MZ; zlia) ltac:(intros XX; discriminate XX) r2 CK1) as AP. clear - AP CK2 MZ. zlia.
+ (* an empty stack slot (AFhy.v R_nofr): the shadow byte PBv lies below the stack *)
destruct r2 as [b2 lo2 hi2 wlo2 whi2 cs2]; cbn [YP09.r_base YP09.r_lo YP09.r_hi] in CK2 |- *; destruct b2 as [[|[|[|k2]]]|]; simpl in CK2; try discriminate CK2.
apply Z.leb_le in CK2. cbn [base_val]. rewrite (HEn 2%nat ltac:(unfold sHAV; zlia)), E2.
pose proof Hsp as (S1 & _ & S3 & _). pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7).
left. clear - CK2 S1 T7 B4 B1 A2 A3 A5 A6 SM1 SM2 MZ. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighShadowEnd, kHighMemBeg, MALLOC_IN_STK, IFRAME in *. try unfold sp0 in *. zlia. }
s_station HR Uo_P.
apply (at_S_weaken Wy md1 X X _ (PT SH5o (PDX Wy RX z)) Uo_P) in HR; [| intros a Ha; exact Ha |].
2:{ intros m [(HB & HM & HSH & HRs) HQ]. split; [exact HB|]. split; [exact HM|]. split; [intros a Ha _; exact (HSH a Ha)|]. split; [|exact HQ].
unfold SH5o. unfold SH5 in HRs.
pose proof (Forall_inv HRs) as C1. pose proof (Forall_inv (Forall_inv_tail HRs)) as C2. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HRs))) as C3.
pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail HRs)))) as C4. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail HRs))))) as C5.
repeat (apply Forall_cons); [exact C1 | exact C2 | exact C3 | exact C4 | | apply Forall_nil].
intros a Ha. apply C5. cbn [fst snd] in *. clear - Ha B4 MZ. zlia. }
s_runT HR tfibtbl_rtA tfibtbl_rtA_ok 0x9afd4 Uo_MF HXT HT5.
lazymatch type of HR with at_S ?Wx ?md ?X0 ?P ?ss ?W' ?c' =>
eapply SRr_bind;
[ eapply (at_S_memset Wx md X0 P (PT SH6o (PDX Wy RX z)) ss W' c' sMF (SOff aMAP 6144) (SLit 4096) Uv 4096 190 0x33884 HR eq_refl ltac:(vm_compute; reflexivity) ltac:(unfold sHAV, sMF; zlia)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
| clear HR; intros W3 c3 _ HR ] end.
{ clear - M1 M2 Z8 B5 MZ. U_zevS. rewrite EaMAP. unfold w64. rewrite !unsigned_lit_small by zlia. zcanon_simp. zlia. }
{ clear. U_zevS. reflexivity. }
{ clear; zlia. }
{ clear - M1 B5 MZ. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END. zlia. }
{ clear - M2 Z8 B5 MZ. zlia. }
{ clear; cbv; reflexivity. }
{ clear; zlia. }
{ clear; zlia. }
{ intros m MEQ (HB & HM & HSH & HRs & HQ) a Ha. apply HM. clear - Ha B5 Z8 MZ. zlia. }
{ refine (memset_ext_of_skel true Uv 4096 Uo_MF ltac:(vm_compute; reflexivity) PLfill _); intros _; clear - B1 B4 B5 M1 SM2 A2 A3 A5 A6 MZ; zlia. }
{ exact (memset_u64_of_skel true Uo_MF ltac:(vm_compute; reflexivity)). }
{ intros m m' MEQ (HB & HM & HSH & HRs & HQ) FR FILL.
assert (FR' : forall a, 0 <= a < 2 ^ 64 -> ~ (Uv <= a < Uv + 4096) -> m' (w64 a) = m (w64 a)).
{ intros a Ha Hna. apply FR. unfold w64. rewrite unsigned_lit_small by exact Ha. exact Hna. }
assert (TOP : SMv + MSv / 8 < Uv \/ Uv + 4096 < SMv) by (clear - B5 Z8 MZ; unfold MALLOC_MAX in *; zlia).
split; [|split; [|split; [|split]]].
- intros i Hi. eapply val_mem_frame; [|exact (HB i Hi)]. intros kk Hkk.
destruct (buf_addr i kk Hi Hkk) as [BA BR]. pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7). destruct Hsp as (S1 & _ & S3 & _).
apply FR'; [exact BR|]. intros Hin.
apply (runs_off_stack (bv_unsigned (getr regs0 11) + 16 + 8 * Z.of_nat i + Z.of_nat kk)); [left; clear - Hin B5 Z8 MZ; zlia | clear - BA S1 S3 T7; unfold IFRAME, MALLOC_IN_STK in *; try unfold sp0 in *; zlia].
- intros a Ha. destruct (HM a Ha) as [Hh [b Hb]]. split; [exact Hh|].
destruct (Z_lt_le_dec a (Uv + 4096)) as [L|GE].
+ exists (Z_to_bv 8 190). apply FILL. unfold w64. rewrite unsigned_lit_small by (clear - Ha M1 M2 Z8 MZ; zlia). clear - Ha L B5 MZ; zlia.
+ exists b. rewrite <- Hb. apply (FR' a); clear - Ha GE M1 M2 Z8 MZ; zlia.
- intros a Ha Hne. destruct (HSH a Ha Hne) as [Hh [b Hb]]. split; [exact Hh|]. exists b. rewrite <- Hb. apply (FR' a); [clear - Ha SM1 SM2 MZ; zlia | clear - Ha TOP MZ; zlia].
- unfold SH6o. apply Forall_cons.
+ intros a Ha. cbn [fst snd] in Ha. apply FILL. unfold w64. rewrite unsigned_lit_small by (clear - Ha M1 M2 Z8 B5 MZ; zlia). exact Ha.
+ apply Forall_forall. intros r Hr a Ha. pose proof (proj1 (Forall_forall _ _) OK5o r Hr) as [RO _].
rewrite FR'; [exact (proj1 (Forall_forall _ _) HRs r Hr a Ha) | unfold run_ok in RO; clear - RO Ha M1 M2 SM1 SM2 Z8 MZ; zlia |].
unfold run_ok in RO. unfold SH5o in Hr. cbn [In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd] in Ha; clear - Ha TOP B1 B4 A2 A3 A5 A6 MZ; zlia.
- destruct HQ as [(memD & D1' & D2 & D3) HRX]. split; [| exact (proj2 RXs m m' Uv 4096 PLfill FR HRX)].
exists memD. split; [exact D1'|]. split; [exact D2|]. intros x Hx. rewrite FR; [exact (D3 x Hx)|].
intros Hin. exact (proj1 (DZONE_disj _ Hx) (place_WIN Uv 4096 _ PLfill Hin)). }
apply (at_S_weaken Wy md1 _ X _ (PT SH6o (PDX Wy RX z))) in HR; [| intros a [Ha|Ha]; [exact Ha | exact (HXW a (place_WIN Uv 4096 a PLfill Ha))] | intros m Hm; exact Hm].
lazymatch type of HR with at_S _ _ _ _ ?ss2 _ _ => replace ss2 with (ss_after_stretch Uo_MF (ss_mem Uo_MF) sMF CLOB_MS 0x33884) in HR by (vm_compute; reflexivity) end.
s_runT HR tfibtbl_rtA tfibtbl_rtA_ok 0x338ac (runto 0x338ac (ss_after_stretch Uo_MF (ss_mem Uo_MF) sMF CLOB_MS 0x33884)) HXT HT6.
s_arm HR BC_EQ false (SOff aMAP 6128) (SOff aMAP 4096).
{ clear - M1 M2 Z8 MZ. arm_zevS. rewrite EaMAP. unfold w64. rewrite !unsigned_lit_small by zlia. zcanon_simp. apply Z.eqb_neq. zlia. }
s_runT HR tfibtbl_rtA tfibtbl_rtA_ok 0x338b4 (runto 0x338b4 (arm BC_EQ false (SOff aMAP 6128) (SOff aMAP 4096) (runto 0x338ac (ss_after_stretch Uo_MF (ss_mem Uo_MF) sMF CLOB_MS 0x33884)))) HXT HT6.
s_arm HR BC_LTU false (SOff aMAP 6128) (SOff aMAP 4112).
{ clear - M1 M2 Z8 MZ. arm_zevS. rewrite EaMAP. unfold w64. rewrite !unsigned_lit_small by zlia. zcanon_simp. apply Z.ltb_ge. zlia. }
s_runT HR tfibtbl_rtA tfibtbl_rtA_ok 0x56ff0 Uo_RET HXT HT6.
apply SRr_ret. exact HR.
Qed.
End U.
End g.
End f.
