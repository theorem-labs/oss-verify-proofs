(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AFk0.v, with its module paths changed and its addresses moved to libreac/fuzz_knock's ASan build; AB1v's tfibsegs is A/AWalkFw0.v's; the mcheck / spin / FCheck / ISpin arguments are opaque labels, the tags 1..14 of the allocator model (until 2026-10-30 they kept cgif's values, by a Theorem Labs lane ruling of 2026-10-29). Kernel rev6b (knock maps the StackDepot blocks at the first Put): DPOST over (layout, world, model, z, memory); Section h's D1 is YD3j.tfib_depot_put_any_spec and HDP reads YFju.DPOSTS with the Put's call world existential (finish-jfamily-text v1.3); the post-Put tail (TAILg / TAILgB / after_depot) is at the grown layout ly' (J4); the first Put's premises come from YFix.first_put_pre_of_AR_at and the grown ledger from YFk0g.ALedger_grow. *)
(* Modified by Theorem Labs, 2026-10: derived from lib/A/AFk0.v of this library by derive_y.py: module names A.Axyz -> AU.Yxyz, addresses moved from libreac/fuzz_knock's asan image to its asan-ubsan image. The Modified-by lines above describe how lib/A/AFk0.v was made and quote that file's asan-image values; the code below carries the asan-ubsan values. *)
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.AU Require Import AWalkFw0 YB1q YF0l YF0m YF0x YFl0.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.AU Require Import YB1w YE3d YB1q YFhy YFhz YFi0 YFi4 YFi9 YB1h YFjm.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YK0v YK13 YP0n YA05 YA09 YG0b YG0h YG0j.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.AU Require Import YFia YFib YFic YFid YFie YFif YFig.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YFen.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.AU Require Import YFjv YFjw YFjx YFjh YFji YFjj YFjn YFjo YFjk YFjl YFjp YFjq YFjr YFjs YFjt YFju YFjy YFjz.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import KnBlockExt.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YF06 YK0g YG08 YG0s.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.AU Require YD3c YD3d YD3g YD3j YFix YFk0g.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YF05.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.AU Require Import YFih YFii YFk1 YFi3.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YA00.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.AU Require Import YFia.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YM05.
Import ListNotations.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YG0g.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Set Printing Depth 50. Set Printing Width 180.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Ltac zlia := first [ lia | ceil; unfold zone3, zone3cases, off_img, in_app, app_addr, in_band_rw, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPrimResvSize, kSpaceSize, kPtrArrayResv, kMaxNumChunks, YImgTop.IMG_LO, YImgTop.IMG_TOP in *; lia ].
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
t_cache, t_unwinding, t_stats, ASTACK, TFIB_IMG_END, TFIB_IMG_LO, kLowShadowBeg, UNW_STK, BST_SIZE, DEP_STK, YImgTop.IMG_LO, YImgTop.IMG_TOP in *.
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
Section f.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (n : Z) (ch : list (Z * Z * Z)).
Variables (idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 : Z).
Variable mb : Z.
Let sp0 : Z := bv_unsigned (getr regs0 2).
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
Local Abbreviation tr := (@YFjm.tr ly regs0 ch).
Local Abbreviation XW := (@YFjm.XW ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
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
Hypothesis Hsp : ly_stk_lo ly + ASTACK <= sp0 /\ ly_bot ly < sp0 /\ sp0 <= ly_stk_hi ly /\ sp0 mod 16 = 0.
Hypothesis Hch : if sp0 + 16 <? ly_top ly
then (if bad_next sp0 (ly_top ly) (bv_unsigned (getr regs0 8)) then ch = []
else sp0 + 16 <= bv_unsigned (getr regs0 8) /\
fpchain (rdword (aview tfibsegs (w_H W) mem0)) (bv_unsigned (getr regs0 8)) (ly_top ly) ch)
else ch = [].
Hypothesis Nrange : 64513 <= n < MALLOC_MAX.
Hypothesis Hidx : 0 <= idx < kMaxNumChunks.
Hypothesis Hres : idx <= res <= kMaxNumChunks /\ res mod kPtrArrayEntriesPerCommit = 0.
Local Abbreviation mod0_of_mul := (@YFjm.mod0_of_mul).
Local Abbreviation size_facts := (@YFjm.size_facts n Nrange).
Local Abbreviation tr_length := (@YFjm.tr_length ly regs0 ch idx res Hidx).
Local Abbreviation high_facts := (@YFjm.high_facts _ ly regs0 idx res LY IMG Hidx Hres).
Local Abbreviation stack_ivs := (@YFjm.stack_ivs _ ly regs0 idx res LY Hsp Hidx Hres).
Local Abbreviation HCX := (@YFjm.HCX _ ly LY).
Hypothesis Hpres0 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem0 a.
Hypothesis Hmap : mb mod 4096 = 0 /\ mzone mb MSv.
Hypothesis Hmap_apart :
zdisjoint (mb, MSv) (T, kThreadObjSize) /\ zdisjoint (mb, MSv) (ly_C ly, kCtxMapSize) /\
zdisjoint (mb, MSv) (ly_prim ly, kPrimResvSize) /\ zdisjoint (mb, MSv) (Qb, kPtrArrayResv) /\
zdisjoint (mb, MSv) (nb_ext ly) /\ zdisjoint (mb, MSv) (sb_ext ly) /\
zdisjoint (mb, MSv) (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly).
Local Abbreviation map_facts := (@YFjm.map_facts _ ly regs0 n idx res mb Nrange Hidx Hres Hmap).
Local Abbreviation map_zone := (@YFjm.map_zone _ ly regs0 n idx res mb Nrange Hidx Hmap).
Local Abbreviation map_zoneN := (@YFjm.map_zoneN _ ly regs0 n idx res mb Nrange Hidx Hres Hmap).
Local Abbreviation map_in_band := (@YFjm.map_in_band _ ly regs0 n idx res mb Nrange Hidx Hmap).
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
Local Abbreviation WIN1P_WINP := (@YFjm.WIN1P_WINP ly regs0 n idx res mb Hidx).
Local Abbreviation WIN1_WIN := (@YFjm.WIN1_WIN ly regs0 n idx res mb Hidx).
Local Abbreviation WIN1P_WIN1 := (@YFjm.WIN1P_WIN1 ly regs0 n idx mb).
Local Abbreviation LGv_range := (@YFjm.LGv_range n Nrange).
Local Abbreviation BSLv_range := (@YFjm.BSLv_range ly regs0 n idx res mb Nrange Hidx).
Local Abbreviation WSKELP := (@YFjm.WSKELP).
Local Abbreviation WSKEL1P := (@YFjm.WSKEL1P).
Local Abbreviation WMAP := (@YFjm.WMAP).
Local Abbreviation WSKEL := (@YFjm.WSKEL).
Local Abbreviation WSKEL1 := (@YFjm.WSKEL1).
Local Abbreviation win_sub := (@YFjm.win_sub).
Local Abbreviation win_sub_sound := (@YFjm.win_sub_sound ly regs0 idx res mb Hidx Hres).
Local Abbreviation in_win := (@YFjm.in_win).
Local Abbreviation WSKELP_WINP := (@YFjm.WSKELP_WINP _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Nrange Hidx Hres).
Local Abbreviation WSKEL1P_WIN1P := (@YFjm.WSKEL1P_WIN1P _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Nrange Hidx Hres).
Local Abbreviation WMAP_WINM := (@YFjm.WMAP_WINM _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Nrange Hidx Hres Hmap).
Local Abbreviation WSKEL_WIN := (@YFjm.WSKEL_WIN _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Nrange Hidx Hres Hmap).
Local Abbreviation WSKEL1_WIN1 := (@YFjm.WSKEL1_WIN1 _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Nrange Hidx Hres Hmap).
Local Abbreviation windows_in := (@YFjm.windows_in ly regs0 idx res mb Hidx Hres).
Local Abbreviation windows_WINP := (@YFjm.windows_WINP _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Nrange Hidx Hres).
Local Abbreviation windows_WIN1P := (@YFjm.windows_WIN1P _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Nrange Hidx Hres).
Local Abbreviation windows_WIN := (@YFjm.windows_WIN _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Nrange Hidx Hres Hmap).
Local Abbreviation windows_WIN1 := (@YFjm.windows_WIN1 _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Nrange Hidx Hres Hmap).
Local Abbreviation frame_WIN1P := (@YFjm.frame_WIN1P _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Nrange Hidx Hres).
Local Abbreviation frame_WIN1 := (@YFjm.frame_WIN1 _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Nrange Hidx Hres Hmap).
Local Abbreviation WINP_not_high := (@YFjm.WINP_not_high _ ly regs0 n idx res mb LY IMG Hsp Nrange Hidx Hres).
Local Abbreviation WIN_not_high := (@YFjm.WIN_not_high _ ly regs0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap).
Variables (mat0 : list word).
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 0x51370) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis U1 : tfib_unwind_spec.
Local Abbreviation all_disjoint_of_forall := (@YFjm.all_disjoint_of_forall).
Local Abbreviation img_rw_writable := (@YFjm.img_rw_writable ly regs0 idx res mb Hidx).
Local Abbreviation kept_of_frame := (@YFjm.kept_of_frame W ly regs0 idx res mb Hidx).
Local Abbreviation SKEL_TAIL := (@YFjm.SKEL_TAIL).
Local Abbreviation blocks_facts := (@YFjm.blocks_facts _ ly LY IMG).
Local Abbreviation off_T := (@YFjm.off_T _ ly regs0 idx res LY IMG Hidx Hres).
Local Abbreviation off_C := (@YFjm.off_C _ ly regs0 idx res LY IMG Hidx Hres).
Local Abbreviation off_Q := (@YFjm.off_Q _ ly regs0 idx res LY IMG Hidx Hres).
Local Abbreviation off_NB := (@YFjm.off_NB _ ly LY IMG).
Local Abbreviation off_SB := (@YFjm.off_SB _ ly LY IMG).
Local Abbreviation off_shadow := (@YFjm.off_shadow ly regs0 idx res mb Hidx).
Ltac off_by tac :=
first [ apply off_img_high; tac | apply off_T; tac | apply off_C; tac | apply off_Q; tac | apply off_NB; tac | apply off_SB; tac
| apply map_off_img; tac | apply off_shadow; tac
| unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP; unfold TFIB_IMG_LO, YImgTop.IMG_LO, YImgTop.IMG_TOP; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END, YImgTop.IMG_LO, YImgTop.IMG_TOP; tac ].
Local Abbreviation DZONE := (@YFjm.DZONE ly).
Variable DPOST : alayout -> world tfibsegs -> Model -> Z -> (word -> option byte) -> Prop.
Local Abbreviation DZONE_disj := (@YFjm.DZONE_disj _ ly regs0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation RFACTS := (@YFjm.RFACTS ly regs0).
Local Abbreviation zone_lit := (@YFjm.zone_lit _ ly regs0 LY IMG Hsp).
Local Abbreviation zone_irw := (@YFjm.zone_irw _ ly regs0 LY IMG Hsp).
Local Abbreviation zone_T := (@YFjm.zone_T _ ly regs0 idx res LY IMG Hsp Hidx Hres).
Local Abbreviation zone_C := (@YFjm.zone_C _ ly regs0 idx res LY IMG Hsp Hidx Hres).
Local Abbreviation tail_ext_ok := (@YFjm.tail_ext_ok _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres).
Local Abbreviation RFACTS_map := (@YFjm.RFACTS_map _ ly regs0 n idx res mb LY IMG Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation at_ST := (@YFjm.at_ST _ W ly regs0 mem0 md0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation memset_stretch := (@YFjm.memset_stretch _ _ W ly regs0 mem0 n idx res mb Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST).
Ltac clearM := try clear DPOST; try clear Hmap_apart; try clear Hmap.
Local Abbreviation at_S := (@YFjm.at_S _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation at_N := (@YFjm.at_N _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation at_RETS := (@YFjm.at_RETS _ regs0 mem0).
Local Abbreviation pstable := (@YFjm.pstable).
Local Abbreviation stack_shaped := (@YFjm.stack_shaped).
Local Abbreviation window_present := (@YFjm.window_present ly regs0 idx res Hidx).
Local Abbreviation stack_present_of := (@YFjm.stack_present_of _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY Hsp Hidx).
Local Abbreviation mid_not_WIN1P := (@YFjm.mid_not_WIN1P _ ly regs0 n idx res mb LY IMG Hsp Nrange Hidx Hres).
Local Abbreviation mid_not_WIN1 := (@YFjm.mid_not_WIN1 _ ly regs0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap).
Local Abbreviation wins_ok := (@YFjm.wins_ok).
Local Abbreviation at_S_run_gen := (@YFjm.at_S_run_gen _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY Hsp Hidx).
Local Abbreviation at_S_run_ecall_gen := (@YFjm.at_S_run_ecall_gen _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY Hsp Hidx).
Local Abbreviation at_S_runP := (@YFjm.at_S_runP _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres).
Local Abbreviation at_S_runM := (@YFjm.at_S_runM _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap).
Local Abbreviation at_S_run_ecallP := (@YFjm.at_S_run_ecallP _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres).
Local Abbreviation at_S_run_ecallM := (@YFjm.at_S_run_ecallM _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap).
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
Local Abbreviation at_S_ret := (@YFjm.at_S_ret _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Htp Hra Hsp Nrange Hidx Hres).
Local Abbreviation kept_of_frame2 := (@YFjm.kept_of_frame2 ly regs0 idx res Hidx).
Local Abbreviation at_N_cont := (@YFjm.at_N_cont _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY Hsp Hidx).
Variables (B : asyms) (S : astate).
Hypothesis TS : TfibSyms B.
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
Hypothesis Hj6 : val_mem tfibsegs (mrestrict (w_H W) mem0) 0x9b1d8 8 j6.
Hypothesis Hj7 : val_mem tfibsegs (mrestrict (w_H W) mem0) 0x9b1e0 8 j7.
Hypothesis Hj8 : val_mem tfibsegs (mrestrict (w_H W) mem0) BSLv 8 j8.
Hypothesis Hi1 : val_mem tfibsegs (mrestrict (w_H W) mem0) (TFIB_INST + o_sec_stats) 8 i1.
Hypothesis Hi2 : val_mem tfibsegs (mrestrict (w_H W) mem0) (TFIB_INST + o_sec_stats + 16) 8 i2.
Hypothesis Hi3 : val_mem tfibsegs (mrestrict (w_H W) mem0) (TFIB_INST + o_sec_stats + 24) 8 i3.
Hypothesis HQT : qmeter S.
Local Abbreviation vis_present := (@YFjv.vis_present _ W ly regs0 mem0 idx res Hidx DPOST B S HARm).
Local Abbreviation in_thread_junk := (@YFjv.in_thread_junk ly B S).
Local Abbreviation in_sec_junk := (@YFjv.in_sec_junk ly B S).
Local Abbreviation in_as_junk := (@YFjv.in_as_junk ly B S).
Local Abbreviation junk_word := (@YFjv.junk_word _ W ly regs0 mem0 idx res LY IMG Hidx Hres DPOST B S HARm).
Local Abbreviation cell_sym := (@YFjv.cell_sym _ W ly mem0 B S TS HARm).
Local Abbreviation cell_lit := (@YFjv.cell_lit _ W ly mem0 B S TS HARm).
Local Abbreviation cell_state := (@YFjv.cell_state _ W ly mem0 B S HARm).
Local Abbreviation In_acells_sec := (@YFjv.In_acells_sec ly B S).
Local Abbreviation sec_vals := (@YFjv.sec_vals _ W ly mem0 idx res B S TS HARm Hidx_def Hres_def).
Local Abbreviation unwinding_val := (@YFjv.unwinding_val _ W ly mem0 B S HARm).
Local Abbreviation rw_writable := (@YFjv.rw_writable ly regs0 idx res Hidx DPOST S).
Local Abbreviation val_mem_mod8 := (@YFjv.val_mem_mod8 W ly regs0 mem0 idx res Hidx DPOST S).
Local Abbreviation chunk_lit := (@YFjv.chunk_lit W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation chunk_lit_at := (@YFjv.chunk_lit_at W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation chunk_atom := (@YFjv.chunk_atom W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Hidx DPOST S).
Local Abbreviation SREG0_ok := (@YFjw.SREG0_ok _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hpres0 DPOST B S TS HTSD HARm Hidx_def Hres_def Hj0 Hj1 Hj2 Hj3 Hj4 Hj5 Hj9 Hj6 Hj7 Hj8 Hi1 Hi2 Hi3).
Local Abbreviation PAIRS_ok := (@YFjx.PAIRS_ok _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres DPOST S).
Local Abbreviation FACTS_ok := (@YFjx.FACTS_ok _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hn Hsp Nrange Hidx Hres DPOST S).
Local Abbreviation SEED_ok := (@YFjx.SEED_ok _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hn Htp Hsp Nrange Hidx Hres Hpres0 DPOST B S TS HTSD HARm Hidx_def Hres_def Hj0 Hj1 Hj2 Hj3 Hj4 Hj5 Hj9 Hj6 Hj7 Hj8 Hi1 Hi2 Hi3).
Local Abbreviation PBUF := (@YFjh.PBUF W ly regs0 ch).
Local Abbreviation PBUF_stableP := (@YFjh.PBUF_stableP _ W ly regs0 n ch idx res mb LY IMG Hsp Nrange Hidx Hres).
Local Abbreviation PBUF_stableM := (@YFjh.PBUF_stableM _ W ly regs0 n ch idx res mb LY IMG Hsp Nrange Hidx Hres Hmap).
Local Abbreviation seg0 := (@YFjh.seg0 _ _ W ly regs0 mem0 md0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hn Htp Hra4096 Hsp Hch Nrange Hidx Hres Hpres0 mat0 U1 DPOST B S TS HTSD HARm Hidx_def Hres_def Hj0 Hj1 Hj2 Hj3 Hj4 Hj5 Hj9 Hj6 Hj7 Hj8 Hi1 Hi2 Hi3).
Local Abbreviation seg1 := (@YFji.seg1 _ _ W ly regs0 mem0 md0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hn Hsp Nrange Hidx Hres).
Local Abbreviation PNULL := (@YFjj.PNULL W ly regs0 ch).
Local Abbreviation PNULLX := (@YFjj.PNULLX W ly regs0 n ch idx res).
Local Abbreviation tail_lits_apart := (@YFjj.tail_lits_apart).
Local Abbreviation segR := (@YFjj.segR _ _ W ly regs0 mem0 md0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Htp Hra Hsp Nrange Hidx Hres DPOST B S TS HARm).
Local Abbreviation appregs := (@YFjn.appregs).
Local Abbreviation st_ok_appregs := (@YFjn.st_ok_appregs _).
Local Abbreviation at_S_app := (@YFjn.at_S_app _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation WIN1N := (@YFjn.WIN1N ly regs0 n).
Local Abbreviation WINPN := (@YFjn.WINPN ly regs0 n).
Local Abbreviation WSKEL1N := (@YFjn.WSKEL1N).
Local Abbreviation WIN1N_WINPN := (@YFjn.WIN1N_WINPN ly regs0 n idx res mb Hidx).
Local Abbreviation windows_WIN1N := (@YFjn.windows_WIN1N _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Nrange Hidx Hres).
Local Abbreviation mid_not_WIN1N := (@YFjn.mid_not_WIN1N _ ly regs0 n idx res mb LY IMG Hsp Nrange Hidx Hres).
Local Abbreviation at_S_runN := (@YFjn.at_S_runN _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres).
Local Abbreviation PBUF_stableN := (@YFjn.PBUF_stableN _ W ly regs0 n ch idx res mb LY IMG Hsp Nrange Hidx Hres).
Local Abbreviation at_S_val := (@YFjn.at_S_val _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation memset_stretchW := (@YFjn.memset_stretchW _ W ly regs0 mem0 n idx res Hsp Nrange Hidx Hres DPOST S).
Local Abbreviation at_S_memset := (@YFjn.at_S_memset _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Hsp Nrange Hidx Hres DPOST S).
Local Abbreviation WIN1T := (@YFjn.WIN1T ly regs0 n idx mb).
Local Abbreviation WIN1T_WIN := (@YFjn.WIN1T_WIN _ ly regs0 n idx res mb Nrange Hidx Hres Hmap).
Local Abbreviation windows_WIN1T := (@YFjn.windows_WIN1T _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Nrange Hidx Hres Hmap).
Local Abbreviation WIN1T_WIN1_aux := (@YFjn.WIN1T_WIN1_aux _ ly regs0 n idx res mb Nrange Hidx Hres Hmap).
Local Abbreviation mid_not_WIN1T := (@YFjn.mid_not_WIN1T _ ly regs0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap).
Local Abbreviation at_S_runT := (@YFjn.at_S_runT _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap).
Local Abbreviation at_S_run_ecallT := (@YFjn.at_S_run_ecallT _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap).
Local Abbreviation PBUFW := (@YFjn.PBUFW ly regs0 ch).
Local Abbreviation PBUFW_stableT := (@YFjn.PBUFW_stableT _ ly regs0 n ch idx res mb LY IMG Hsp Nrange Hidx Hres Hmap).
Local Abbreviation WIN1S := (@YFjo.WIN1S ly regs0 n idx mb).
Local Abbreviation WSKEL1S := (@YFjo.WSKEL1S).
Local Abbreviation WIN1S_WIN1T := (@YFjo.WIN1S_WIN1T ly regs0 n idx mb).
Local Abbreviation WIN1S_WIN := (@YFjo.WIN1S_WIN _ ly regs0 n idx res mb Nrange Hidx Hres Hmap).
Local Abbreviation windows_WIN1S := (@YFjo.windows_WIN1S _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Nrange Hidx Hres Hmap).
Local Abbreviation mid_not_WIN1S := (@YFjo.mid_not_WIN1S _ ly regs0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap).
Local Abbreviation at_S_runS := (@YFjo.at_S_runS _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap).
Local Abbreviation at_S_run_ecallS := (@YFjo.at_S_run_ecallS _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap).
Local Abbreviation brun := (@YFjo.brun).
Local Abbreviation run_ok := (@YFjo.run_ok n mb).
Local Abbreviation PS := (@YFjo.PS ly regs0 n ch mb).
Local Abbreviation runs_not_WIN1S := (@YFjo.runs_not_WIN1S _ ly regs0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation runs_not_stack := (@YFjo.runs_not_stack _ ly regs0 n idx res mb LY Hsp Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation PS_stable := (@YFjo.PS_stable _ ly regs0 n ch idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation cut1 := (@YFjo.cut1).
Local Abbreviation cut := (@YFjo.cut).
Local Abbreviation cut_sound := (@YFjo.cut_sound _ ly regs0 mem0 n idx res mb Nrange Hidx Hres Hmap DPOST S).
Local Abbreviation cut_ok := (@YFjo.cut_ok ly regs0 mem0 n idx res mb Hidx Hres DPOST S).
Local Abbreviation at_S_memsetS := (@YFjo.at_S_memsetS _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S).
Local Abbreviation skel_okb := (@YFjo.skel_okb).
Local Abbreviation skel_cases := (@YFjo.skel_cases idx res Hidx Hres S Hidx_def Hres_def).
Local Abbreviation skel_apart := (@YFjo.skel_apart _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation skel_u64 := (@YFjo.skel_u64 _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap DPOST S Hidx_def Hres_def).
Local Abbreviation memset_ext_of_skel := (@YFjo.memset_ext_of_skel _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation memset_u64_of_skel := (@YFjo.memset_u64_of_skel _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap DPOST S Hidx_def Hres_def).
Local Abbreviation WIN1R := (@YFjo.WIN1R ly regs0 n mb).
Local Abbreviation WSKEL1R := (@YFjo.WSKEL1R).
Local Abbreviation WIN1R_WIN1S := (@YFjo.WIN1R_WIN1S ly regs0 n idx mb).
Local Abbreviation WIN1R_WIN := (@YFjo.WIN1R_WIN _ ly regs0 n idx res mb Nrange Hidx Hres Hmap).
Local Abbreviation windows_WIN1R := (@YFjo.windows_WIN1R _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Nrange Hidx Hres Hmap).
Local Abbreviation mid_not_WIN1R := (@YFjo.mid_not_WIN1R _ ly regs0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap).
Local Abbreviation at_S_runR := (@YFjo.at_S_runR _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap).
Local Abbreviation at_S_run_ecallR := (@YFjo.at_S_run_ecallR _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap).
Local Abbreviation PSR := (@YFjo.PSR ly regs0 n ch mb).
Local Abbreviation rstable := (@YFjo.rstable ly regs0 n mb).
Local Abbreviation rstable_true := (@YFjo.rstable_true ly regs0 n mb).
Local Abbreviation PSR_stable := (@YFjo.PSR_stable _ ly regs0 n ch idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation QSP := (@YFjo.QSP ly idx).
Local Abbreviation QS_not_WIN1R := (@YFjo.QS_not_WIN1R _ ly regs0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation QSP_rstable := (@YFjo.QSP_rstable _ ly regs0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation at_S_memsetSR := (@YFjo.at_S_memsetSR _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S).
Local Abbreviation chunk_eqb := (@YFjo.chunk_eqb).
Local Abbreviation chunk_eqb_eq := (@YFjo.chunk_eqb_eq idx res Hidx Hres S Hidx_def Hres_def).
Local Abbreviation subregionb := (@YFjo.subregionb).
Local Abbreviation subregionb_sound := (@YFjo.subregionb_sound ly regs0 mem0 idx res Hidx Hres DPOST S Hidx_def Hres_def).
Local Abbreviation submemb := (@YFjo.submemb).
Local Abbreviation submemb_sound := (@YFjo.submemb_sound ly regs0 mem0 idx res Hidx Hres DPOST S Hidx_def Hres_def).
Local Abbreviation at_S_submem := (@YFjo.at_S_submem _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Hidx Hres DPOST S Hidx_def Hres_def).
Local Abbreviation at_S_addreg := (@YFjo.at_S_addreg _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation PSR_runs := (@YFjk.PSR_runs _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation place_WIN := (@YFjk.place_WIN ly regs0 n idx mb).
Local Abbreviation SH0 := (@YFjk.SH0 n mb).
Local Abbreviation SH1 := (@YFjk.SH1 n mb).
Local Abbreviation SH2 := (@YFjk.SH2 n mb).
Local Abbreviation SH_ok := (@YFjk.SH_ok _ ly regs0 n idx res mb Nrange Hidx Hres Hmap).
Local Abbreviation segG1 := (@YFjk.segG1 _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation RX_stableS := (@YFjl.RX_stableS ly regs0 n idx mb).
Local Abbreviation rstable_and := (@YFjl.rstable_and ly regs0 n mb).
Local Abbreviation pstable_and := (@YFjl.pstable_and).
Local Abbreviation PSR_stableS' := (@YFjl.PSR_stableS' _ ly regs0 n ch idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation pairwise_disjoint_map := (@YFjl.pairwise_disjoint_map).
Local Abbreviation at_S_setchunks := (@YFjl.at_S_setchunks _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation chunk_ok_CVal_eqv := (@YFjl.chunk_ok_CVal_eqv).
Local Abbreviation RES2T_ne := (@YFjl.RES2T_ne ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Hidx Hres).
Local Abbreviation RES2T_eq := (@YFjl.RES2T_eq ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Hidx Hres).
Local Abbreviation sv_denot_eq_of_U := (@YFjl.sv_denot_eq_of_U ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation skel_apart_QS := (@YFjl.skel_apart_QS _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation QSPX := (@YFjl.QSPX ly idx).
Local Abbreviation segNE := (@YFjl.segNE _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation segEQa := (@YFjl.segEQa _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation zev_SAlu := (@YFjl.zev_SAlu).
Local Abbreviation zev_SLit := (@YFjl.zev_SLit).
Local Abbreviation zev_SOff := (@YFjl.zev_SOff).
Local Abbreviation segJ2 := (@YFjl.segJ2 _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation segJ := (@YFjl.segJ _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation QR := (@YFjp.QR ly res).
Local Abbreviation segT1 := (@YFjp.segT1 _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hn Hsp Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation DX := (@YFjp.DX ly regs0).
Local Abbreviation DX_at := (@YFjp.DX_at regs0).
Local Notation DZONE_at := YFjm.DZONE (only parsing).
Local Abbreviation PD := (@YFjp.PD mem0 DPOST).
Local Abbreviation PD_rstable := (@YFjp.PD_rstable _ ly regs0 mem0 n idx res mb Nrange Hidx Hres Hmap DPOST).
Local Abbreviation PD_stableT := (@YFjp.PD_stableT _ ly regs0 mem0 n idx res mb Nrange Hidx Hres Hmap DPOST).
Local Abbreviation PSR_stableS := (@YFjp.PSR_stableS _ ly regs0 n ch idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation PD_stableS := (@YFjp.PD_stableS _ ly regs0 mem0 n idx res mb Nrange Hidx Hres Hmap DPOST).
Local Abbreviation PDX := (@YFjp.PDX mem0 DPOST).
Local Abbreviation PDX_rstable := (@YFjp.PDX_rstable _ ly regs0 mem0 n idx res mb Nrange Hidx Hres Hmap DPOST).
Local Abbreviation PDX_stableT := (@YFjp.PDX_stableT _ ly regs0 mem0 n idx res mb Nrange Hidx Hres Hmap DPOST).
Local Abbreviation PDX_stableS := (@YFjp.PDX_stableS _ ly regs0 mem0 n idx res mb Nrange Hidx Hres Hmap DPOST).
Local Abbreviation dx_okb := (@YFjp.dx_okb).
Local Abbreviation skel_apart_DX := (@YFjp.skel_apart_DX _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation skel_apart_stk := (@YFjp.skel_apart_stk _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart S Hidx_def Hres_def).
Local Abbreviation at_S_depot := (@YFjp.at_S_depot _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST B S TS Hidx_def Hres_def).
Local Abbreviation SH3 := (@YFjp.SH3 n mb).
Local Abbreviation SH4 := (@YFjp.SH4 n mb).
Local Abbreviation shadow_marks := (@YFjp.shadow_marks _ ly regs0 n idx res mb Nrange Hidx Hres Hmap).
Local Abbreviation SH34_ok := (@YFjp.SH34_ok _ ly regs0 n idx res mb Nrange Hidx Hres Hmap).
Local Abbreviation segT2b := (@YFjp.segT2b _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hn Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation segT2 := (@YFjp.segT2 _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hn Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation SH5 := (@YFjq.SH5 n mb).
Local Abbreviation SH6 := (@YFjq.SH6 n mb).
Local Abbreviation user_marks := (@YFjq.user_marks _ ly regs0 n idx res mb Nrange Hidx Hres Hmap).
Local Abbreviation SH56_ok := (@YFjq.SH56_ok _ ly regs0 n idx res mb Nrange Hidx Hres Hmap).
Local Abbreviation segU1 := (@YFjq.segU1 _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation SH6_of_cut := (@YFjq.SH6_of_cut _ ly regs0 n idx res mb Nrange Hidx Hres Hmap).
Local Abbreviation segUe := (@YFjq.segUe _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hn Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation PT := (@YFjq.PT ly regs0 n ch mb).
Local Abbreviation run_okT := (@YFjq.run_okT n mb).
Local Abbreviation SH5o := (@YFjq.SH5o n mb).
Local Abbreviation SH6o := (@YFjq.SH6o n mb).
Local Abbreviation SH56o_ok := (@YFjq.SH56o_ok _ ly regs0 n idx res mb Nrange Hidx Hres Hmap).
Local Abbreviation PT_stableT := (@YFjq.PT_stableT _ ly regs0 n ch idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation segUo := (@YFjq.segUo _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hn Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation E0_at := (@YFjr.E0_at ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3).
Local Abbreviation map_atom := (@YFjr.map_atom).
Local Abbreviation E0_at_other := (@YFjr.E0_at_other ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation ed_E0_at := (@YFjr.ed_E0_at ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation st_ok_ecall_agree_on := (@YFjr.st_ok_ecall_agree_on _).
Local Abbreviation Esw := (@YFjr.Esw ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation Esw_agree := (@YFjr.Esw_agree ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation Esw_on := (@YFjr.Esw_on ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation at_S_facts_atoms := (@YFjr.at_S_facts_atoms _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation atoms_ok_app := (@YFjr.atoms_ok_app).
Local Abbreviation FS2_ok := (@YFjr.FS2_ok _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hn Hsp Nrange Hidx Hres Hmap DPOST S).
Local Abbreviation at_S_addreg_cfg := (@YFjr.at_S_addreg_cfg _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation S_N_apart := (@YFjr.S_N_apart _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart S).
Local Abbreviation S_N_nomap := (@YFjr.S_N_nomap).
Local Abbreviation grant_cont := (@YFjr.grant_cont _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hn Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S).
Local Abbreviation SHLO := (@YFjs.SHLO).
Local Abbreviation SHHI := (@YFjs.SHHI n).
Local Abbreviation SH_hull := (@YFjs.SH_hull ly regs0 n res Nrange S).
Local Abbreviation lit_m1 := (@YFjs.lit_m1).
Local Abbreviation lit_enomem := (@YFjs.lit_enomem).
Local Abbreviation nores34 := (@YFjs.nores34).
Local Abbreviation core34 := (@YFjs.core34).
Local Abbreviation pru_MS := (@YFjs.pru_MS ly regs0 n res Nrange S).
Local Abbreviation grant_anon_shape := (@YFjs.grant_anon_shape).
Local Abbreviation Hcut_out := (@YFjs.Hcut_out).
Local Abbreviation slackS := (@YFjs.slackS _ W ly mem0 md0 B S HARm HQT).
Local Abbreviation S_N_facts := (@YFjs.S_N_facts).
Local Abbreviation S_N_ext64 := (@YFjs.S_N_ext64 _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres S).
Local Abbreviation S_N_win64 := (@YFjs.S_N_win64 _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres S).
Local Abbreviation nodeS := (@YFjs.nodeS _ _ W ly regs0 mem0 md0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres B S HARm HQT).
Local Abbreviation S_VG := (@YFjt.S_VG).
Local Abbreviation TQ := (@YFjt.TQ).
Local Abbreviation S_V_facts := (@YFjt.S_V_facts).
Local Abbreviation ZQF := (@YFjt.ZQF ly res).
Local Abbreviation ZQ := (@YFjt.ZQ ly idx res).
Local Abbreviation QR_facts := (@YFjt.QR_facts _ ly regs0 idx res mb LY IMG Hidx Hres S Hidx_def).
Local Abbreviation ZQ_of_ZQF := (@YFjt.ZQ_of_ZQF ly idx res).
Local Abbreviation QR_not_WIN1T := (@YFjt.QR_not_WIN1T _ ly regs0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart S Hidx_def).
Local Abbreviation ZQ_stableT := (@YFjt.ZQ_stableT _ ly regs0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart S Hidx_def).
Local Abbreviation ZQ_rstable := (@YFjt.ZQ_rstable _ ly regs0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart S Hidx_def).
Local Abbreviation ZQ_stableD := (@YFjt.ZQ_stableD _ ly regs0 idx res mb LY IMG Hsp Hidx Hres S Hidx_def).
Local Abbreviation skel_apart_Q := (@YFjt.skel_apart_Q _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart S Hidx_def Hres_def).
Local Abbreviation TQ_val := (@YFjt.TQ_val _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hidx Hres S Hidx_def).
Local Abbreviation nores50 := (@YFjt.nores50).
Local Abbreviation core50 := (@YFjt.core50).
Local Abbreviation pru17 := (@YFjt.pru17).
Local Abbreviation grant_piece_shape := (@YFjt.grant_piece_shape).
Local Abbreviation nodeV := (@YFjt.nodeV _ _ ly regs0 mem0 md0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation RZF := (@YFjt.RZF ly res).
Local Abbreviation RZ := (@YFjt.RZ ly idx res).
Local Abbreviation ZQF_rstable := (@YFjt.ZQF_rstable _ ly regs0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart S Hidx_def).
Local Abbreviation segV := (@YFjt.segV _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation CZI := (@YFju.CZI).
Local Abbreviation CZ := (@YFju.CZ ly).
Local Abbreviation abs_cell_okS := (@YFju.abs_cell_okS).
Local Abbreviation abs_cells_okS := (@YFju.abs_cells_okS).
Local Abbreviation MPAD := (@YFju.MPAD).
Local Abbreviation padb := (@YFju.padb).
Local Abbreviation const_cells_CZ := (@YFju.const_cells_CZ ly regs0 n idx res mb Nrange Hidx B TS HTSD).
Local Abbreviation CZ_untouched := (@YFju.CZ_untouched _ ly regs0 mem0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S).
Local Abbreviation cell_holds_agree := (@YFju.cell_holds_agree ly regs0 mem0 idx res Hidx Hres DPOST B S).
Local Abbreviation aview_agreeW := (@YFju.aview_agreeW W).
Local Abbreviation rd_ext_Wy := (@YFju.rd_ext_Wy W).
Local Abbreviation depot_ids_bound := (@YFju.depot_ids_bound ly regs0 mem0 idx res mb Hidx Hres DPOST B S TS).
Local Abbreviation depot_mem_ok_agree := (@YFju.depot_mem_ok_agree ly regs0 mem0 idx res mb Hidx Hres DPOST B S TS).
Local Abbreviation depot_mem_ok_ext := (@YFju.depot_mem_ok_ext ly B).
Local Abbreviation depot_at0 := (@YFju.depot_at0 _ W ly regs0 mem0 n idx res mb Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST B S HARm).
Local Abbreviation DPOSTS := (YFju.DPOSTS ly regs0 ch B S).
Local Abbreviation D1W_ok := (@YFju.D1W_ok _ _ W ly regs0 mem0 n ch idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST B S TS HTSD HARm Hgp).
Local Abbreviation lyF := (@YFjy.lyF ly mb S).
Local Abbreviation lyF_at := (@YFjy.lyF_at mb S).
Local Abbreviation SFS := (@YFjy.SFS ly regs0 n ch S).
Local Abbreviation KSc := (@YFjy.KSc n S).
Local Abbreviation lyF_le := (@YFjy.lyF_le ly mb S).
Local Abbreviation lyF_sec := (@YFjy.lyF_sec ly mb S).
Local Abbreviation lyF_eqs := (@YFjy.lyF_eqs ly mb S).
Local Abbreviation lyF_ok := (@YFjy.lyF_ok _ ly mb LY S).
Local Abbreviation sizes_model := (@YFjy.sizes_model ly regs0 n res Nrange S).
Local Abbreviation val_mem_cell := (@YFjy.val_mem_cell ly regs0 res B S).
Local Abbreviation le_byte_1_0 := (@YFjy.le_byte_1_0 ly regs0 res S).
Local Abbreviation find_chunk_at_app1 := (@YFjy.find_chunk_at_app1 B).
Local Abbreviation find_chunk_at_app2 := (@YFjy.find_chunk_at_app2 B).
Local Abbreviation In_combine_seq_app := (@YFjy.In_combine_seq_app).
Local Abbreviation combine_seq_last := (@YFjy.combine_seq_last ly regs0 res S).
Local Abbreviation in_combine_seq := (@YFjy.in_combine_seq ly regs0 res S).
Local Abbreviation combine_seq_in := (@YFjy.combine_seq_in ly regs0 res S).
Local Abbreviation index_of_app_old := (@YFjy.index_of_app_old).
Local Abbreviation index_ofZ_app_old := (@YFjy.index_ofZ_app_old).
Local Abbreviation index_of_app_new := (@YFjy.index_of_app_new ly regs0 res S).
Local Abbreviation index_ofZ_app_new := (@YFjy.index_ofZ_app_new ly regs0 res S).
Local Abbreviation fin_facts := (@YFjy.fin_facts _ _ ly regs0 mem0 n ch idx res mb B S).
Local Abbreviation wz_facts := (@YFjy.wz_facts _ W ly regs0 n ch res mb S).
Local Abbreviation S_AR_final := (@YFjy.S_AR_final _ _ W ly regs0 mem0 md0 n ch idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST B S TS HTSD HARm Hidx_def Hres_def).
Local Abbreviation SF_parts := (@YFjy.SF_parts ly regs0 n ch res S Hres_def).
Local Abbreviation rS_not_in_arr := (@YFjy.rS_not_in_arr _ W ly regs0 mem0 n res mb B S HARm).
Local Abbreviation len_arr := (@YFjy.len_arr idx S Hidx_def).
Local Abbreviation ck_base_new := (@YFjy.ck_base_new ly regs0 n res mb Nrange B S).
Local Abbreviation SEF := (@YFjy.SEF _ W ly regs0 mem0 n ch res mb Nrange B S HARm Hres_def).
Local Abbreviation staticF := (@YFjy.staticF ly mb S).
Local Abbreviation placed_finalG := (@YFjy.placed_finalG _ W ly regs0 mem0 md0 n ch idx res mb Nrange Hidx Hres Hmap B S HARm Hres_def).
Local Abbreviation sec_live_final := (@YFjy.sec_live_final ly regs0 n ch res mb Nrange S Hres_def).
Local Abbreviation FQ := (@YFjz.FQ ly n idx res mb).
Local Abbreviation OWN_T := (@YFjz.OWN_T _ W ly regs0 mem0 n idx res Hsp Nrange Hidx Hres DPOST B S HARm).
Local Abbreviation OWN_I := (@YFjz.OWN_I _ W ly regs0 mem0 n idx res mb Hsp Nrange Hidx Hres DPOST B S TS HARm).
Local Abbreviation OWN_Q := (@YFjz.OWN_Q _ W ly regs0 mem0 n idx res Hsp Nrange Hidx Hres DPOST B S HARm).
Local Abbreviation OWN_D := (@YFjz.OWN_D _ W ly regs0 mem0 n idx res Hsp Nrange Hidx Hres DPOST B S TS HARm).
Local Abbreviation band_core := (@YFjz.band_core ly B S).
Local Abbreviation OWN_SH := (@YFjz.OWN_SH _ W ly regs0 mem0 n idx res mb Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST B S HARm).
Local Abbreviation OWN_BANDhid := (@YFjz.OWN_BANDhid _ W ly mem0 md0 LY B S HARm).
Local Abbreviation NEWOWN := (@YFjz.NEWOWN _ W ly regs0 mem0 n ch idx res mb Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST B S HARm Hres_def).
Local Abbreviation fin_pack := (YFjz.fin_pack ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb DPOST B S).
Local Abbreviation fin_post := (YFjz.fin_post ly regs0 mem0 n ch idx res mb B S).
Local Abbreviation finE := (@YFjz.finE _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hn Htp Hra Hsp Nrange Hidx Hres Hmap DPOST B S Hidx_def).
Local Abbreviation finO := (@YFjz.finO _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hn Htp Hra Hsp Nrange Hidx Hres Hmap DPOST B S Hidx_def).
Local Abbreviation LEAF_S := (@YFjz.LEAF_S _ _ W ly regs0 mem0 md0 n ch idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST B S TS HTSD HARm Hidx_def Hres_def).
Local Abbreviation BCELLS := (@YFk1.BCELLS W mem0).
Local Abbreviation PGBv := (@YFk1.PGBv mb).
Local Abbreviation PGEv := (@YFk1.PGEv n mb).
Local Abbreviation big_marks := (@YFk1.big_marks _ ly regs0 n idx res mb Nrange Hidx Hres Hmap).
Local Abbreviation sm_bounds := (@YFk1.sm_bounds _ ly regs0 n idx res mb Nrange Hidx Hres Hmap).
Local Abbreviation U_SHBT := (@YFk1.U_SHBT _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Nrange Hidx Hres Hmap).
Local Abbreviation U_SHET := (@YFk1.U_SHET _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Nrange Hidx Hres Hmap).
Local Abbreviation U_PGBT := (@YFk1.U_PGBT _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Nrange Hidx Hres Hmap).
Local Abbreviation U_PGET := (@YFk1.U_PGET _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Nrange Hidx Hres Hmap).
Local Abbreviation U_SHB_X := (@YFk1.U_SHB_X _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Nrange Hidx Hres Hmap).
Local Abbreviation U_SHE_X := (@YFk1.U_SHE_X _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Nrange Hidx Hres Hmap).
Local Abbreviation in_bimg := (@YFk1.in_bimg).
Local Abbreviation in_bimg_facts := (@YFk1.in_bimg_facts _ ly regs0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap).
Local Abbreviation val_mem_xfer_bimg := (@YFk1.val_mem_xfer_bimg _ W ly regs0 mem0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap S).
Local Abbreviation can_word := (@YFk1.can_word W ly regs0 mem0 n idx res Hidx DPOST S).
Local Abbreviation B_R_ok := (@YFk1.B_R_ok _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap DPOST B S TS HARm).
Local Abbreviation zcanon_m1 := (@YFk1.zcanon_m1).
Local Abbreviation U_PGB_X := (@YFk1.U_PGB_X _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Nrange Hidx Hres Hmap).
Local Abbreviation U_PGE_X := (@YFk1.U_PGE_X _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Nrange Hidx Hres Hmap).
Local Abbreviation brun_refill := (@YFk1.brun_refill ly regs0 n idx res Hres S Hidx_def).
Local Abbreviation SH4_head := (@YFk1.SH4_head _ ly regs0 n idx res mb Nrange Hidx Hres Hmap S Hidx_def).
Local Abbreviation SH4_tail := (@YFk1.SH4_tail _ ly regs0 n idx res mb Nrange Hidx Hres Hmap S Hidx_def).
Local Abbreviation segB1a := (@YFk1.segB1a _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation zc_m1 := (@YFk1.zc_m1).
Local Abbreviation zc_idem := (@YFk1.zc_idem).
Local Abbreviation zc_add_l := (@YFk1.zc_add_l).
Local Abbreviation zc_sub_l := (@YFk1.zc_sub_l).
Local Abbreviation zc_sub_r := (@YFk1.zc_sub_r).
Local Abbreviation land_page_id := (@YFk1.land_page_id).
Local Abbreviation U_KA0 := (@YFk1.U_KA0 _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Nrange Hidx Hres Hmap).
Local Abbreviation U_KA1 := (@YFk1.U_KA1 _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Nrange Hidx Hres Hmap).
Local Abbreviation U_REM1 := (@YFk1.U_REM1 _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Nrange Hidx Hres Hmap).
Local Abbreviation U_REM2 := (@YFk1.U_REM2 _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Nrange Hidx Hres Hmap).
Local Abbreviation segB1b := (@YFk1.segB1b _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST).
Local Abbreviation segB1 := (@YFk1.segB1 _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST B S TS HARm Hidx_def Hres_def).
Local Abbreviation nores4032 := (@YFk1.nores4032).
Local Abbreviation core4032 := (@YFk1.core4032).
Local Abbreviation lit4032 := (@YFk1.lit4032).
Local Abbreviation S_K_facts := (@YFk1.S_K_facts).
Local Abbreviation nodeK := (@YFk1.nodeK _ _ ly regs0 mem0 md0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation submemb2 := (@YFk1.submemb2).
Local Abbreviation submemb2_sound := (@YFk1.submemb2_sound ly regs0 mem0 idx res Hidx Hres DPOST S Hidx_def Hres_def).
Local Abbreviation at_S_submem2 := (@YFk1.at_S_submem2 _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Hidx Hres DPOST S Hidx_def Hres_def).
Local Abbreviation SH5_of_SH4 := (@YFk1.SH5_of_SH4 _ ly regs0 n idx res mb Nrange Hidx Hres Hmap).
Local Abbreviation segB2 := (@YFk1.segB2 _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation allow_of_hull := (@YFk1.allow_of_hull _ ly regs0 n idx res mb Nrange Hidx Hres Hmap S).
Local Ltac addr_tac :=
cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi];
rewrite ?EaT, ?EaC, ?EaTOP, ?EaSB, ?EaQ, ?EaMAP, ?EaQS, ?EaBSL, ?EaSM, ?EaPB, ?E2; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, w64, ly_bot, kStackSpan, t_unwinding, t_cache, t_stats, TFIB_IMG_END, UNW_STK, BST_SIZE, ASTACK, IFRAME, kHighMemBeg, kHighMemEnd, ASAN_CEIL, YImgTop.IMG_LO, YImgTop.IMG_TOP in *;
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
kLowShadowBeg, kHighShadowEnd, TFIB_IMG_END, YImgTop.IMG_LO, YImgTop.IMG_TOP in *;
rewrite !unsigned_lit_small by zlia; zcanon_simp;
first [ rewrite (proj2 (Z.ltb_ge _ _)) by zlia | rewrite (proj2 (Z.ltb_lt _ _)) by zlia ]; reflexivity.
Local Ltac s_join HR k clob SJ := s_forget HR k clob; s_noconds HR; s_station HR SJ; apply SRr_ret; exact HR.
Local Ltac s_ladder RUN HR tbl tblok STOP Sl Slo Sh Sh2 Sh3 Shi SJ k clob HX HP :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let HQ := fresh "HQ" in
assert (HQ : SRr tfibsegs W' c' (at_S Wx md X P SJ));
[ let MZ := fresh "MZ" in pose proof map_zoneN as MZ; destruct MZ as [ZLO|ZHI];
[ s_armR HR BC_GEU true (14%bv : bv 5) (10%bv : bv 5); [ladder_arith ZLO|];
RUN HR tbl tblok 0x52450 Sl HX HP;
s_armR HR BC_GEU true (14%bv : bv 5) (11%bv : bv 5); [ladder_arith ZLO|];
RUN HR tbl tblok STOP Slo HX HP;
s_join HR k clob SJ
| s_armR HR BC_GEU false (14%bv : bv 5) (10%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok 0x522a8 Sh HX HP;
s_armR HR BC_LTU true (7%bv : bv 5) (10%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok 0x52450 Sh2 HX HP;
s_armR HR BC_GEU false (14%bv : bv 5) (11%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok 0x52490 Sh3 HX HP;
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
RUN HR tbl tblok 0x52450 Sl HX HP;
s_armR HR BC_GEU true (14%bv : bv 5) (11%bv : bv 5); [ladder_arith ZLO|];
RUN HR tbl tblok STOP Slo HX HP;
s_join HR k clob SJ
| s_armR HR BC_GEU false (14%bv : bv 5) (10%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok 0x522a8 Sh HX HP;
s_armR HR BC_LTU true (7%bv : bv 5) (10%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok 0x52450 Sh2 HX HP;
s_armR HR BC_GEU false (14%bv : bv 5) (11%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok 0x5248c Sh3a HX HP;
s_armR HR BC_LTU false (6%bv : bv 5) (11%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok 0x52490 Sh3 HX HP;
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
RUN HR tbl tblok 0x31200 Sh HX HP;
s_armR HR BC_LTU false (17%bv : bv 5) (22%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok 0x31204 Sh2 HX HP;
s_armR HR BC_GEU false (16%bv : bv 5) (22%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok STOP Shi HX HP;
s_join HR k clob SJ ]
| clear HR; eapply SRr_bind; [exact HQ | clear HQ; let W2 := fresh "WL" in let c2 := fresh "cL" in intros W2 c2 _ HR ] ]
end.
Let rd0 : reader := aview tfibsegs (w_H W) mem0.
Let WF := am_wf B ly S rd0 HARm.
Definition S1 : astate := set_nev (st_nev S + 1) S.
Definition QLEAF (r : sptr * astate) (W' : world tfibsegs) (c' : config) : Prop :=
Wf (as_universe B) (snd r) /\ qtight (snd r) -> malloc_leaf tfibsegs B ly S W regs0 mem0 md0 n r W' c'.
Local Open Scope am_scope.
Definition sec_body : M (option sptr) :=
s <- YG00.get ;;
mcheck (Z.of_nat (length (st_sec_arr s)) <? kMaxNumChunks) 9 ;;
YG00.put (set_secs (st_secs s ++ [mkSec (sec_map_size n) (needed_size n) true]) s) ;;
(if Z.of_nat (length (st_sec_arr s)) =? st_sec_reserved s then
z2 <- askz (KMapPtrArray (8 * Z.of_nat (length (st_sec_arr s))) kPtrArrayCommit) ;;
if aGranted z2 then YG00.modify (fun s0 => set_sec_reserved (st_sec_reserved s0 + kPtrArrayEntriesPerCommit) s0) else spin 11
else YG00.ret tt) ;;
YG00.modify (fun s0 => set_sec_arr (st_sec_arr s0 ++ [length (st_secs s)]) s0) ;;
YG00.ret (Some (PSec (length (st_secs s)) kPage)).
Definition KSEC (z : Z) : itree astate (sptr * astate) := (ob <- (if z =? 0 then YG00.ret None else sec_body) ;; malloc_K n tr ob) S1.
Lemma malloc_secondary_eq : forall s, from_primary n = false ->
malloc n tr s = (tick ;; mcheck (n <? kMaxAllowedMalloc - kPage) 3 ;; ob <- sec_alloc n ;; malloc_K n tr ob) s.
Proof. clearP. intros s FP. unfold malloc, malloc_K. rewrite FP. reflexivity. Qed.
Lemma sec_ask_eq : forall (Wx : world tfibsegs) c Q,
amreal tfibsegs ((ob <- sec_alloc n ;; malloc_K n tr ob) S1) Wx c Q = amreal tfibsegs (IAsk (KMmapSec (sec_map_size n)) S1 KSEC) Wx c Q.
Proof. clearP. intros Wx c Q. reflexivity. Qed.
Lemma at_S_wvb : forall (Wx : world tfibsegs) md mat X P ss W' c',
at_S Wx (with_vm_backing (m_vm_lazy md) mat md) X P ss W' c' -> at_S Wx md X P ss W' c'.
Proof. clear. intros Wx md mat X P ss W' c' (-> & ms & mat' & E' & -> & HE & HS & MEQ & PRS & HP). split; [reflexivity|]. exists ms, mat', E'. rewrite wvb_collapse. split; [reflexivity|]. repeat (split; [assumption|]). exact HP. Qed.
Lemma aowned_tick : forall a, aowned B ly S1 a <-> aowned B ly S a.
Proof. clear. intros a. unfold S1, aowned, aclient_byte, sec_extents, frames. cbn. tauto. Qed.
Lemma errno_not_owned : AR tfibsegs B ly S W mem0 md0 -> forall a, TFIB_ERRNO <= a < TFIB_ERRNO + 4 -> ~ aowned B ly S a.
Proof.
clearP. intros HAR a Ha O.
assert (IMGa : in_img tfibsegs a).
{ unfold in_img. change tfibsegs with YB1h.TSEGS. unfold YB1h.TSEGS. eexists. split; [do 3 right; left; reflexivity|]. cbn. unfold TFIB_ERRNO in Ha. zlia. }
apply (proj1 (AR_owned_image_law_ok tfibsegs B ly S W mem0 md0 a HAR IMGa)) in O.
rewrite (ts_owned B TS) in O. unfold Tfib_owned_static in O. apply Exists_exists in O as (r & Hr & [X1 X2]). cbn [In] in Hr. unfold TFIB_ERRNO in Ha.
repeat match type of Hr with _ \/ _ => destruct Hr as [<-|Hr]; [cbn [fst snd] in X1, X2; zlia|] | False => destruct Hr end.
Qed.
Lemma oom_owned : aowned B ly S TFIB_OOM.
Proof. clearP. apply (own_area B ly S _ (as_oom_byte B, 1) TFIB_OOM HARm); [unfold asyms_areas; cbn; tauto|]. cbn [fst snd]. rewrite (ts_oom B TS). zlia. Qed.
Lemma val_mem_aview : forall (Hh : word -> bool) m a (w : nat) v k, val_mem tfibsegs (mrestrict Hh m) a w v -> (k < w)%nat ->
aview tfibsegs Hh m (a + Z.of_nat k) = Some (YG0f.le_byte v w k).
Proof.
clear. intros Hh m a w v k Hv Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. change (YG0f.le_byte v w k) with (YO0f.le_byte v w k). f_equal.
apply unsigned_lit_small8. unfold YO0f.le_byte. apply Z.mod_pos_bound. zlia.
Qed.
Theorem refuseS : forall (mat : list word) c',
AR tfibsegs B ly S W mem0 md0 -> aregime S   ->
at_S W (with_vm_backing (m_vm_lazy md0) mat md0) WINP PBUF (resume S_N (SLit ENOMEM_RETv) (ss_mem S_N) (ss_facts S_N)) W c' ->
amreal tfibsegs (KSEC 0) W c' QLEAF.
Proof.
clearP. intros mat c' HAR Hev HR. change (amreal tfibsegs (KSEC 0) W c' QLEAF) with (SRr tfibsegs W c' (QLEAF (PNull, S1))).
apply at_S_wvb in HR. eapply SRr_mono; [exact (segR _ _ HR)|].
intros W2 c2 _ (-> & regs' & mem' & mat2 & -> & R10 & RCS & MEQ & PRS & ((HB & VOOM & VERR) & (Vunw & Vres & Vnch & Vmtx & PRT & VISI))) [WF1 QT1]. cbn [fst snd] in WF1, QT1.
pose proof Hsp as (S1' & S2' & S3' & S4'). pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). pose proof BSLv_range as HB'.
pose proof high_facts as (F1 & F2 & _ & _ & _ & _ & _ & _ & F9 & F10 & _). pose proof (ts_inst B TS) as EI.
set (md' := with_vm_backing (m_vm_lazy md0) mat2 md0).
assert (NW : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - ASTACK <= a < sp0) -> ~ WINT a -> ~ WINI a -> a <> TFIB_OOM -> ~ (TFIB_ERRNO <= a < TFIB_ERRNO + 4) ->
mem' (Z_to_bv 64 a) = mem0 (Z_to_bv 64 a)).
{ intros a Ra N1 N2 N3 N4 N5. apply MEQ. rewrite unsigned_lit_small by exact Ra. unfold WINPN, WINP. clear - N1 N2 N3 N4 N5. intros [[X|[X|X]]|[X|X]]; try tauto; zlia. }
assert (ARF : AR tfibsegs B ly S W mem' md').
{ apply (YFic.AR_snull B ly S W mem0 mem' md0 md' BSLv HB' TS HAR).
-
intros a Ra Ho NX. apply aview_same. apply NW; [exact Ra | | | | |].
+ intros ST. exact (AR_stack_law_ok tfibsegs B ly S W mem0 md0 a HAR ltac:(clear - ST S1' S3'; unfold ASTACK in *; try unfold sp0 in *; zlia) Ho).
+ intros X. apply NX. unfold YFic.XN. unfold WINT, t_unwinding in X. unfold T in X. clear - X. zlia.
+ intros X. apply NX. unfold YFic.XN. unfold WINI in X. clear - X. zlia.
+ intros ->. apply NX. unfold YFic.XN. left. zlia.
+ intros X. exact (errno_not_owned HAR a X Ho).
-
intros a0 HV0. set (a := bv_unsigned (Z_to_bv 64 a0)).
assert (Ra : 0 <= a < 2 ^ 64) by (pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 a0)) as R; change (bv_modulus 64) with (2 ^ 64) in R; exact R).
assert (Ex : Z_to_bv 64 a = Z_to_bv 64 a0) by (subst a; apply Z_to_bv_bv_unsigned).
assert (AV : forall (Hh : word -> bool) m, aview tfibsegs Hh m a0 = aview tfibsegs Hh m a) by (intros Hh m; unfold aview, mbyte, mrestrict; rewrite Ex; reflexivity).
rewrite AV in HV0 |- *. clearbody a. clear Ex AV a0.
assert (PRES : forall u, apresent (w_H W) mem' u -> aview tfibsegs (w_H W) mem' u <> None) by (clear; intros u [Hh [b Hb]]; unfold aview, mbyte, mrestrict; rewrite Hh, Hb; cbn; discriminate).
assert (VAL : forall u base (w : nat) v, val_mem tfibsegs (mrestrict (w_H W) mem') base w v -> base <= u < base + Z.of_nat w -> aview tfibsegs (w_H W) mem' u <> None).
{ clear. intros u base w v HV Hu. replace u with (base + Z.of_nat (Z.to_nat (u - base))) by zlia. rewrite (val_mem_aview (w_H W) mem' base w v (Z.to_nat (u - base)) HV ltac:(zlia)). discriminate. }
destruct (zr_dec (sp0 - ASTACK) sp0 a) as [D1|D1]; [apply PRES; apply PRS; exact D1|].
assert (DT : WINT a \/ ~ WINT a) by (clear; unfold WINT; zlia). destruct DT as [D2|D2]; [apply PRES; apply PRT; exact D2|].
assert (DI : WINI a \/ ~ WINI a) by (clear; unfold WINI; zlia). destruct DI as [D3|D3]; [exact (VISI a D3)|].
destruct (Z.eq_dec a TFIB_OOM) as [->|D4]; [apply (VAL _ _ _ _ VOOM); cbn; zlia|].
destruct (zr_dec TFIB_ERRNO (TFIB_ERRNO + 4) a) as [D5|D5]; [apply (VAL _ _ _ _ VERR); cbn; zlia|].
rewrite (aview_same (w_H W) mem0 mem' a (NW a Ra D1 D2 D3 D4 D5)). exact HV0.
-   pose proof (val_mem_aview _ _ _ _ _ 0%nat Vunw ltac:(zlia)) as X. rewrite Z.add_0_r in X. unfold T in X. exact X.
- intros k Hk. rewrite <- Hres_def. exact (val_mem_aview _ _ _ _ _ k Vres Hk).
- intros k Hk. rewrite <- Hidx_def. exact (val_mem_aview _ _ _ _ _ k Vnch Hk).
- intros k Hk. replace k with (Z.of_nat (Z.to_nat k)) by zlia. rewrite (val_mem_aview _ _ _ _ _ (Z.to_nat k) Vmtx ltac:(zlia)). f_equal.
clear - Hk. unfold YG0f.le_byte. rewrite Z.shiftr_0_l. reflexivity.
- unfold md'. apply m_vmmaps_wvb.
- unfold md'. apply m_vm_lazy_wvb.
- unfold md'. apply eager_used_wvb.
-   intros a Ha _. unfold YG0n.w64. apply NW.
+ clear - Ha. unfold kHighShadowBeg, kHighShadowEnd in Ha. zlia.
+ clear - Ha S1' T7. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, ASTACK, YImgTop.IMG_LO, YImgTop.IMG_TOP in *. try unfold sp0 in *. zlia.
+ clear - Ha F1. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, WINT, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, t_unwinding, YImgTop.IMG_LO, YImgTop.IMG_TOP in *. try unfold T in *. zlia.
+ clear - Ha HB'. unfold WINI, kHighShadowBeg, kHighShadowEnd, TFIB_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex in *. zlia.
+ clear - Ha. unfold kHighShadowBeg, kHighShadowEnd, TFIB_OOM in *. zlia.
+ clear - Ha. unfold kHighShadowBeg, kHighShadowEnd, TFIB_ERRNO in *. zlia. }
exists ly, regs', mem', md'.
split. { unfold cfg_at, raZ, YG0d.w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
split; [| split; [rewrite R10; cbn [fst sptr_addr sptr_exp aeval]; reflexivity | exact QT1]].
split; [exact (AR_tick B ly S W mem' md' ARF Hev)|].
split; [apply layout_gle_refl|].
split; [apply wle_refl|].
split. { intros r Hr. apply RCS. unfold acallee_saved in Hr.
assert (H18 : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by zlia.
clear - H18.
assert (E5 : forall k : Z, 0 <= k < 32 -> forall b : bv 5, bv_unsigned b = k -> Z_to_bv 5 k = b) by (intros k Hk b Hb; apply bv_eq; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 5) with 32; rewrite Z.mod_small by zlia; symmetry; exact Hb).
destruct H18 as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
[ rewrite (E5 2 ltac:(zlia) 2%bv eq_refl) | rewrite (E5 3 ltac:(zlia) 3%bv eq_refl) | rewrite (E5 4 ltac:(zlia) 4%bv eq_refl)
| rewrite (E5 8 ltac:(zlia) 8%bv eq_refl) | rewrite (E5 9 ltac:(zlia) 9%bv eq_refl) | rewrite (E5 18 ltac:(zlia) 18%bv eq_refl)
| rewrite (E5 19 ltac:(zlia) 19%bv eq_refl) | rewrite (E5 20 ltac:(zlia) 20%bv eq_refl) | rewrite (E5 21 ltac:(zlia) 21%bv eq_refl)
| rewrite (E5 22 ltac:(zlia) 22%bv eq_refl) | rewrite (E5 23 ltac:(zlia) 23%bv eq_refl) | rewrite (E5 24 ltac:(zlia) 24%bv eq_refl)
| rewrite (E5 25 ltac:(zlia) 25%bv eq_refl) | rewrite (E5 26 ltac:(zlia) 26%bv eq_refl) | rewrite (E5 27 ltac:(zlia) 27%bv eq_refl) ];
cbn [In]; tauto. }
split; [unfold md'; apply YG0b.same_io_with_vm_backing|].
split; [| exact PRS].
intros a Ra NO NO' NS NE. apply aview_same. apply NW; [exact Ra | | | | |].
- intros ST. apply NS. unfold ascratch, spZ. left. exact ST.
- intros X. exact (NO (OWN_T a X)).
- intros X. exact (NO (OWN_I a X)).
- intros ->. exact (NO oom_owned).
- intros X. apply NS. unfold ascratch. right. rewrite (ts_errno B TS). exact X.
Qed.
Local Ltac step HR e :=
eapply SRr_bind; [exact e | clear HR; let W2 := fresh "W" in let c2 := fresh "c" in intros W2 c2 _ HR].
Section h.
Variables (W3 : world tfibsegs) (mat : list word) (ms : machine_state) (E' : env) (mb0 : Z).
Let mdN : Model := with_vm_backing (m_vm_lazy md0) mat md0.
Let md2 : Model := mmap_model (w64 mb) (w64 MSv) mdN.
Let ccont : config := mkCfg (mkst (regupd (ms_regs ms) 10%bv (w64 mb)) (v_addi (Z_to_bv 64 (ss_pc S_N)) 4) (zfill (w64 mb) (w64 MSv) (ms_mem ms)) (seg_rom tfibsegs)) md2.
Hypothesis HAR : AR tfibsegs B ly S W mem0 md0.
Hypothesis Hev : aregime S.
Hypothesis Htr : In tr (as_universe B).
Hypothesis D1 : YD3j.tfib_depot_put_any_spec layout_grow depot_ok YD3j.as_const_g2f B.
Hypothesis HBC : BCELLS.
Hypothesis HDP : forall l W' md'' z m, DPOST l W' md'' z m <-> exists Wc, DPOSTS Wc YD3j.as_const_g2f l W' md'' z m.
Hypothesis GOK : grant_ok_na_pin mdN (w64 mb) MSv = true.
Hypothesis LE3 : wle W W3.
Hypothesis SUB3 : hsub (w_H W3) (w_H W).
Hypothesis MON3 : forall x : word, w_H W x = false -> w_H W3 x = false.
Hypothesis A3 : w_A W3 = (SHLO mb, SHHI mb) :: (mb, mb + MSv) :: w_A W.
Hypothesis VISM3 : forall x : word, mb <= bv_unsigned x < mb + MSv -> w_H W3 x = false.
Hypothesis VISH3 : forall x : word, SHLO mb <= bv_unsigned x < SHHI mb -> w_H W3 x = false.
Hypothesis OUT3 : forall x : word, ~ (mb <= bv_unsigned x < mb + MSv) -> ~ (SHLO mb <= bv_unsigned x < SHHI mb) -> w_H W3 x = w_H W x.
Hypothesis AI2 : AI tfibsegs (w_H W3) (w_A W3) md2.
Hypothesis MW2 : amwf md2.
Hypothesis IO2 : same_io md0 md2.
Hypothesis EG2 : eager_used md2 <= eager_used mdN + MSv.
Hypothesis VM2 : vm_maps (m_vmmaps md2) = (w64 mb, w64 MSv) :: vm_maps (m_vmmaps mdN) /\ vm_reserved (m_vmmaps md2) = vm_reserved (m_vmmaps mdN) /\
vm_limit (m_vmmaps md2) = vm_limit (m_vmmaps mdN) /\ vm_mmap_base (m_vmmaps md2) = vm_mmap_base (m_vmmaps mdN).
Hypothesis HE' : env_agree sHAV (E0_at mb0) E'.
Hypothesis HS : st_ok_ecall tfibsegs E' S_N (restrict (w_H W) ms).
Hypothesis MEQ : forall x : word, ~ WINP (bv_unsigned x) -> ms_mem ms x = mem0 x.
Hypothesis PRS : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) (ms_mem ms) a.
Hypothesis HB : PBUF (ms_mem ms).
Let MA : ARm B ly S rd0 := proj1 HAR.
Lemma LN : ALedger tfibsegs ly S mdN.
Proof. exact (ALedger_same tfibsegs ly S md0 mdN (proj1 (proj2 HAR)) (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) (eager_used_wvb _ _)). Qed.
Lemma MWN : amwf mdN.
Proof. exact (amwf_same md0 mdN (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) (proj1 (proj2 (proj2 (proj2 HAR))))). Qed.
Lemma MSB : 0 < MSv <= MALLOC_MAX + 4 * 4096.
Proof. clearP. pose proof size_facts as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & _). clear - Z8 Z1 Z2 Z3. unfold MALLOC_MAX in *. zlia. Qed.
Lemma Umb : bv_unsigned (w64 mb) = mb.
Proof. pose proof map_facts as (M1 & M2 & _). pose proof map_zoneN as MZ. pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & _). unfold w64. apply unsigned_lit_small. clear - M1 M2 Z8 MZ. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, YImgTop.IMG_LO, YImgTop.IMG_TOP in *. zlia. Qed.
Lemma GAP : Forall (zdisjoint (mb, MSv)) (static_extents ly ++ vis0_zones ly ++ sec_extents ly S).
Proof.
pose proof (YFia.grant_apart B ly S rd0 mdN (w64 mb) MSv MA LN MSB ltac:(pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & _ & Z9 & _); exact Z9) GOK) as X.
rewrite Umb in X. exact X.
Qed.
Lemma SHZ : forall a, SMv <= a < SMv + MSv / 8 -> w_H W3 (w64 a) = false /\ ms_mem ms (w64 a) = Some (Z_to_bv 8 0).
Proof.
intros a Ha. pose proof map_facts as (M1 & M2 & M3 & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _ & _ & SMA). pose proof map_zoneN as MZ. pose proof (SH_hull mb) as (H1 & H2 & _).
pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & Z9 & _).
assert (Ra : 0 <= a < 2 ^ 64) by (clear - Ha SM1 SM2 MZ; unfold kHighShadowBeg, kHighShadowEnd in *; zlia).
split; [apply VISH3; unfold w64; rewrite unsigned_lit_small by exact Ra; rewrite SMA in Ha; clear - Ha H1 H2 MZ; zlia|].
set (g := mb + 8 * (a - SMv)).
assert (Hg : shadow_addr g = a).
{ subst g. rewrite SMA. unfold shadow_addr. apply Z.mod_divide in M3 as [p Hp]; [|zlia]. rewrite Hp.
replace (p * 4096) with (p * 512 * 8) by zlia. rewrite (Z.div_mul (p * 512) 8) by zlia.
replace (p * 512 * 8 + 8 * (a - (SHADOW_OFF + p * 512))) with ((p * 512 + (a - (SHADOW_OFF + p * 512))) * 8) by zlia.
rewrite Z.div_mul by zlia. zlia. }
rewrite <- Hg. unfold w64. rewrite MEQ.
- pose proof (Z.div_mod MSv 8 ltac:(zlia)) as DM8. assert (M8 : MSv mod 8 = 0) by (clear - Z9 MZ; apply Z.mod_divide in Z9 as [u Hu]; [|zlia]; rewrite Hu; replace (u * 4096) with ((u * 512) * 8) by zlia; apply Z.mod_mul; zlia).
apply (YFia.grant_shadow_zero B ly S rd0 mdN (w64 mb) MSv MA LN MSB Z9 GOK mem0 g (proj2 (proj2 (proj2 (proj2 (proj2 HAR)))))).
+ subst g. apply Z.mod_divide; [zlia|]. apply Z.mod_divide in M3 as [p Hp]; [|zlia]. exists (p * 512 + (a - SMv)). zlia.
+ rewrite Umb. subst g. clear - Ha MZ. zlia.
+ rewrite Umb. subst g. clear - Ha DM8 M8 MZ. zlia.
- rewrite unsigned_lit_small by (rewrite Hg; exact Ra). rewrite Hg. intros Hw. unfold WINP, WINT, WINI in Hw. pose proof BSLv_range as HBS. pose proof high_facts as (F1 & _).
destruct Hsp as (S1' & _). pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7).
clear - Hw Ha SM1 SM2 F1 S1' T7 HBS MZ. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, ASTACK, t_unwinding, TFIB_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex, YImgTop.IMG_LO, YImgTop.IMG_TOP in *.
try unfold sp0 in *. try unfold T in *. zlia.
Qed.
Lemma VISM : forall a, mb <= a < mb + MSv -> w_H W3 (w64 a) = false.
Proof. intros a Ha. pose proof map_facts as (M1 & M2 & _). pose proof map_zoneN as MZ. apply VISM3. unfold w64. rewrite unsigned_lit_small; [exact Ha | clear - Ha M1 M2 MZ; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, YImgTop.IMG_LO, YImgTop.IMG_TOP in *; zlia]. Qed.
Lemma WZ3 : forall z mat', ALedger tfibsegs lyF (SFS false z) md2 -> wz_facts false z ly W3 (with_vm_backing (m_vm_lazy md2) mat' md2).
Proof.
intros z mat' L2. pose proof (SH_hull mb) as (H1 & H2 & H3 & _). constructor.
- exact MON3.
- exact VISM3.
- exact VISH3.
- intros E; discriminate E.
- rewrite A3. cbn [A_bytes fst snd]. zlia.
- intros i Hi. rewrite A3. cbn. right; right. exact Hi.
- rewrite A3. cbn. right; left. reflexivity.
- rewrite A3. cbn. left. reflexivity.
- exact (ALedger_same tfibsegs lyF (SFS false z) md2 _ L2 (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) (eager_used_wvb _ _)).
- exact (amwf_same md2 _ (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) MW2).
- exact GAP.
Qed.
Lemma wz_facts_same : forall grow z l (Wz : world tfibsegs) md md', m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md ->
eager_used md' = eager_used md -> wz_facts grow z l Wz md -> wz_facts grow z l Wz md'.
Proof.
clear. intros grow z l Wz md md' E1 E2 E3 [F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11]. constructor; try assumption.
- exact (ALedger_same tfibsegs (lyF_at l) (SFS grow z) md md' F9 E1 E2 E3).
- exact (amwf_same md md' E1 E2 F10).
Qed.
(* The walk's facts at the Put's call world / model, moved to at_S_depot's post (ly', W4, md4) (finish-jfamily-text J2's
   wz_facts at the post-Put layout). The no-growth arm is the call's own; the growth arm adds the two blocks to w_A and
   takes the grown ledger and amwf of the post model as GR. *)
Lemma WZ_put : forall (grow : bool) z (Wy W4 : world tfibsegs) (mdy md4 : Model) ly',
(forall mat', wz_facts grow z ly Wy (with_vm_backing (m_vm_lazy mdy) mat' mdy)) ->
wle Wy W4 -> YD3j.put_effect layout_grow ly Wy mdy ly' W4 md4 ->
(ly_NB ly = 0 -> ly_NB ly' <> 0 -> ALedger tfibsegs (lyF_at ly') (SFS grow z) md4 /\ amwf md4) ->
forall mat', wz_facts grow z ly' W4 (with_vm_backing (m_vm_lazy md4) mat' md4).
Proof.
clear. intros grow z Wy W4 mdy md4 ly' HWy LE PE GR mat'.
destruct PE as [(-> & -> & SBM) | (nb & sb & N0 & S0 & NZ & SZ & EL & _ & WA & _ & _ & _ & _)].
- apply (wz_facts_same grow z ly Wy (with_vm_backing (m_vm_lazy mdy) mat' mdy)); [| | | exact (HWy mat')].
+ rewrite !m_vmmaps_wvb. exact (YD3j.sbm_vmmaps _ _ SBM).
+ rewrite !m_vm_lazy_wvb. exact (YD3j.sbm_lazy _ _ SBM).
+ rewrite !eager_used_wvb. apply YD3j.b2_eager_eq; [exact (YD3j.sbm_vmmaps _ _ SBM) | exact (YD3j.sbm_lazy _ _ SBM)].
- pose proof (HWy mat') as [F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11].
assert (NB' : ly_NB ly' = nb) by (rewrite EL; reflexivity).
assert (SB' : ly_SB ly' = sb) by (rewrite EL; reflexivity).
assert (NB0 : ly_NB ly' <> 0) by (rewrite NB'; exact NZ).
assert (SB0 : ly_SB ly' <> 0) by (rewrite SB'; exact SZ).
destruct (GR N0 NB0) as [LG4 MW4].
assert (MONw : forall x : word, w_H Wy x = false -> w_H W4 x = false).
{ intros x Hx. destruct (w_H W4 x) eqn:E; [|reflexivity]. rewrite (LE x E) in Hx. discriminate Hx. }
constructor.
+ intros x Hx. exact (MONw x (F1 x Hx)).
+ intros x Hx. exact (MONw x (F2 x Hx)).
+ intros x Hx. exact (MONw x (F3 x Hx)).
+ intros G x Hx. exact (MONw x (F4 G x Hx)).
+ rewrite WA. cbn [A_bytes fst snd]. rewrite F5.
rewrite (nb_ext_set ly' NB0), (sb_ext_set ly' SB0), NB', SB', (nb_ext_eq ly), (sb_ext_eq ly), N0, S0. cbn [Z.eqb fst snd].
unfold kNodesBlockSize, kStoreBlockSize. lia.
+ intros i Hi. rewrite WA. right; right. exact (F6 i Hi).
+ rewrite WA. right; right. exact F7.
+ rewrite WA. right; right. exact F8.
+ exact (ALedger_same tfibsegs _ (SFS grow z) md4 _ LG4 (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) (eager_used_wvb _ _)).
+ exact (amwf_same md4 _ (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) MW4).
+ exact F11.
Qed.
Lemma LED0 : forall z, ALedger tfibsegs lyF (SFS false z) md2.
Proof.
intros z. pose proof (SF_parts false z) as (Rreg & _ & _ & _ & _ & _ & _ & _ & Rarr & Rres & _ & Rck & Rsecs & Rnev & Rregs).
pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & Z9 & _).
assert (UMS : bv_unsigned (w64 MSv) = MSv) by (unfold w64; apply unsigned_lit_small; clear - Z8; unfold MALLOC_MAX in Z8; zlia).
unfold md2. apply (YG0j.ALedger_anon tfibsegs (as_universe B) 0 0 0 ly S (SFS false z) mdN (w64 mb) (w64 MSv) (rS S) mb LY WF (am_placed _ _ _ _ MA) MWN LN).
- rewrite UMS. exact GOK.
- exact Hev.
- rewrite UMS. exact MSB.
- rewrite UMS. exact Z9.
- intros c Hc. exact (Rreg c).
- unfold prim_committed. rewrite Rregs. reflexivity.
- rewrite Umb, UMS. exact (SEF false z).
- exact Rnev.
- rewrite Rres, <- Hres_def. reflexivity.
Qed.
Lemma COV_Q : forall mdV, amwf mdV -> idx = res ->
forall x, ~ (ly_Q ly <= x < ly_Q ly + kPtrArrayResv) ->
YK0g.covered (vm_noaccess (m_vmmaps (grant_md false (Z_to_bv 64 50) (w64 QSv) (w64 131072) mdV)) ++ m_vm_lazy (grant_md false (Z_to_bv 64 50) (w64 QSv) (w64 131072) mdV)) x
= YK0g.covered (vm_noaccess (m_vmmaps mdV) ++ m_vm_lazy mdV) x.
Proof.
intros mdV [(W1 & W2 & W3' & _ & W5) _] Heq x Hx.     pose proof (QR_facts Heq) as (E1 & _ & QA & F9 & Q5 & F10 & EQR).
assert (UQa : bv_unsigned (w64 QSv) = QSv) by (unfold w64; apply unsigned_lit_small; clear - F9 Q5 F10; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kPtrArrayResv, YImgTop.IMG_LO, YImgTop.IMG_TOP in *; try unfold Qb in *; zlia).
assert (UQb : bv_unsigned (w64 131072) = 131072) by (unfold w64; apply unsigned_lit_small; zlia).
apply (YG0j.cov_grant_md false (Z_to_bv 64 50) (w64 QSv) (w64 131072) mdV x).
- unfold YK0g.model_ivs_wf. split; [|split; [|split; [|exact W5]]]; intros q Hq; [exact (W1 q Hq) | exact (W2 q Hq) | exact (W3' q Hq)].
- rewrite UQa, UQb. clear - F9 Q5 F10. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kPtrArrayResv, YImgTop.IMG_LO, YImgTop.IMG_TOP in *. try unfold Qb in *. zlia.
- rewrite UQa, UQb. intros Hin. apply Hx. clear - Hin F9 Q5. unfold kPtrArrayResv in *. try unfold Qb in *. zlia.
Qed.
Lemma grant50_isp : forall (a k : word) md, vm_init_sp (m_vmmaps (grant_md false (Z_to_bv 64 50) a k md)) = vm_init_sp (m_vmmaps md).
Proof.
clear. intros a k md. unfold grant_md, fixedin_ok_model, fixedin_ok_vmmaps, with_mmap_replacement, with_mmap_backing. rewrite YFjt.nores50. cbn.
destruct md as [fd [maps lazy mat] io fs pr lim tm sg sc]. cbn. destruct maps; cbn; reflexivity.
Qed.
Lemma LED1 : forall z mdV md5, idx = res -> ALedger tfibsegs lyF (SFS false z) mdV ->
vm_maps (m_vmmaps md5) = vm_maps (m_vmmaps mdV) -> vm_reserved (m_vmmaps md5) = vm_reserved (m_vmmaps mdV) ->
vm_limit (m_vmmaps md5) = vm_limit (m_vmmaps mdV) -> vm_mmap_base (m_vmmaps md5) = vm_mmap_base (m_vmmaps mdV) ->
vm_init_sp (m_vmmaps md5) = vm_init_sp (m_vmmaps mdV) ->
(forall x, ~ (ly_Q ly <= x < ly_Q ly + kPtrArrayResv) ->
YK0g.covered (vm_noaccess (m_vmmaps md5) ++ m_vm_lazy md5) x = YK0g.covered (vm_noaccess (m_vmmaps mdV) ++ m_vm_lazy mdV) x) ->
eager_used md5 <= eager_used mdV + 131072 ->
(forall lo n, region_free (vm_noaccess (m_vmmaps mdV)) lo n = true -> region_free (vm_noaccess (m_vmmaps md5)) lo n = true) ->
ALedger tfibsegs lyF (SFS true z) md5.
Proof.
intros z mdV md5 Heq LV VM RES LIM MMB ISP COV EG NAF.
pose proof (SF_parts false z) as (Rreg0 & _ & _ & _ & _ & _ & _ & _ & _ & Rres0 & _ & _ & _ & Rnev0 & Rregs0).
pose proof (SF_parts true z) as (Rreg1 & _ & _ & _ & _ & _ & _ & _ & _ & Rres1 & _ & _ & _ & Rnev1 & Rregs1).
pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & Z9 & _).
apply (YG0j.ALedger_qcommit' tfibsegs lyF (SFS false z) (SFS true z) mdV md5).
- exact lyF_ok.
- rewrite (SEF false z). apply Forall_app. split; [exact (YG08.sec_extents_sizes64P _ 0 0 0 ly S WF)|]. constructor; [|constructor]. cbn [snd]. clear - Z8 Z9. unfold MALLOC_MAX in Z8. zlia.
- exact (placed_finalG false z HAR GAP).
- exact LV.
- exact VM.
- exact RES.
- exact LIM.
- exact MMB.
- exact ISP.
- intros x Hx. apply COV. exact Hx.
- clear - EG. unfold kPtrArrayEntriesPerCommit. zlia.
- intros c Hc. rewrite (Rreg1 c), (Rreg0 c). reflexivity.
- rewrite (SEF true z), (SEF false z). reflexivity.
- unfold prim_committed. rewrite Rregs1, Rregs0. reflexivity.
- rewrite Rnev1, Rnev0. reflexivity.
- rewrite Rres1, Rres0. reflexivity.
- exact NAF.
Qed.
Definition KDEP (s : astate) (beg : sptr) (z : Z) : itree astate (sptr * astate) :=
((if z =? 0 then YG00.ret tt
else (s' <- YG00.get ;;
mcheck (depot_ids s' + 1 <? kDepotIdsPerBlock) 14 ;;
mcheck (kStartFramesMax + depot_frames s' + Z.of_nat (length tr) + 1 <? kStoreFramesPerBlock) 13 ;;
YG00.put (set_depot (st_depot s' ++ [tr]) s'))) ;;
(let k := mkChunk beg n CAllocated in
(if needs_remap (ck_n k) then z <- askz (KShadowRemap (ck_user k) (8 * (ck_n k / 8))) ;; if aGranted z then YG00.ret tt else spin 12 else YG00.ret tt) ;;
YG00.modify (fun s0 => set_chunks (upd_chunk (st_chunks s0) k) s0) ;;
YG00.ret (ck_user k))) s.
Lemma malloc_K_some : forall beg s (Wx : world tfibsegs) c Q,
amreal tfibsegs (malloc_K n tr (Some beg) s) Wx c Q = SRr tfibsegs Wx c (fun W1 c1 => exists z, aok s (KDepot tr) z /\ amreal tfibsegs (KDEP s beg z) W1 c1 Q).
Proof. clearP. intros. reflexivity. Qed.
Lemma NR : N8D / 8 < 18446744073709551615 -> needs_remap (ck_n (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated)) = false.
Proof.
intros Hsmall. pose proof sizes_model as (_ & _ & RS & _). unfold ck_n, needs_remap. cbn [YG00.ck_req]. rewrite RS. apply Z.leb_gt.
clear - Hsmall Nrange. unfold N8D, kClearShadowMmapThreshold in *. rewrite Z.div_mul in Hsmall by zlia. zlia.
Qed.
Lemma NRb : 18446744073709551615 <= N8D / 8 -> needs_remap (ck_n (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated)) = true.
Proof.
intros Hbig. pose proof sizes_model as (_ & _ & RS & _). unfold ck_n, needs_remap. cbn [YG00.ck_req]. rewrite RS. apply Z.leb_le.
clear - Hbig Nrange. unfold N8D, kClearShadowMmapThreshold in *. rewrite Z.div_mul in Hbig by zlia. zlia.
Qed.
Lemma KS_user : ck_user (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated) = PSec (length (st_secs S1)) 6144 /\
8 * (ck_n (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated) / 8) = N8D.
Proof.
pose proof sizes_model as (_ & _ & RS & RZ & _). unfold ck_user, ck_rz, ck_n, N8D, padd. cbn [YG00.ck_req YG00.ck_beg]. rewrite RS, RZ.
split; [reflexivity | clear; zlia].
Qed.
(* finish-jfamily-text v1.3: HDP's two directions. <- gives D1W_ok's HDPOST' at each Put's call
   world; -> moves the call world into the first-Put conjunct (YFjz Section g's HDPOST). *)
Lemma HDPOST'_at : forall (Wc : world tfibsegs) l W' md'' z m, DPOSTS Wc YD3j.as_const_g2f l W' md'' z m -> DPOST l W' md'' z m.
Proof. intros Wc l W' md'' z m H. exact (proj2 (HDP l W' md'' z m) (ex_intro _ Wc H)). Qed.
Lemma HDPOST_from : (forall l W' md'' zz m, DPOST l W' md'' zz m -> exists Wc, DPOSTS Wc YD3j.as_const_g2f l W' md'' zz m) ->
forall l W' md'' zz m, DPOST l W' md'' zz m -> aok S (KDepot tr) zz /\
  (st_depot (depot_after zz tr S) <> [] -> depot_mem_ok B l (depot_after zz tr S) (aview tfibsegs (w_H W') m)) /\
  Forall (cell_holds B l (aview tfibsegs (w_H W') m)) (YD3j.as_const_g2f B l) /\
  (st_depot S = [] -> zz = 1 /\ exists (Wc : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
     (regs2 : bvmap 5 word), YD3j.put_effect layout_grow ly Wc md l W' md'' /\
     YD3j.depot_first_put_post depot_ok YD3j.as_const_g2f B Wc ly S regs mem md tr l W' md''
     (mkCfg (mkst regs2 (Z_to_bv 64 0x3108c) m (seg_rom tfibsegs)) md'')).
Proof.
clear. intros HD l W' md'' zz m Hd. destruct (HD l W' md'' zz m Hd) as (Wc & A1 & A2 & A3c & A4).
split; [exact A1|]. split; [exact A2|]. split; [exact A3c|].
intros E. destruct (A4 E) as (Z1 & regs & mem & md & regs2 & PE & FP). split; [exact Z1|].
exists Wc, regs, mem, md, regs2. exact (conj PE FP).
Qed.
Lemma TAILg : N8D / 8 < 18446744073709551615 -> forall (grow : bool) (Wz : world tfibsegs) (mdz : Model) (ly' : alayout) (RX : (word -> option byte) -> Prop) (Xd : Z -> Prop) z c4 s4,
(grow = true <-> idx = res) -> rstable RX -> pstable WIN1T RX -> (grow = true -> forall m, RX m -> ZQ Wz m) ->
(forall a, WIN a -> Xd a) -> (forall a, Xd a -> WIN a \/ (grow = true /\ QR a) \/ DX_at ly' a) ->
wle W Wz -> same_io md0 mdz -> (forall mat', wz_facts grow z ly' Wz (with_vm_backing (m_vm_lazy mdz) mat' mdz)) ->
(forall x : word, ~ (mb <= bv_unsigned x < mb + MSv) -> ~ (SHLO mb <= bv_unsigned x < SHHI mb) ->
~ (grow = true /\ QSv <= bv_unsigned x < QSv + 131072) ->
~ (fst (nb_ext ly') <= bv_unsigned x < fst (nb_ext ly') + snd (nb_ext ly')) ->
~ (fst (sb_ext ly') <= bv_unsigned x < fst (sb_ext ly') + snd (sb_ext ly')) -> w_H Wz x = w_H W x) ->
layout_grow ly ly' -> layout_ok ly' -> img_cover ly' -> (forall a, DZONE_at ly' a -> ~ WIN a /\ ~ (sp0 - ASTACK <= a < sp0)) ->
(forall l W' md'' zz m, DPOST l W' md'' zz m -> exists Wc, DPOSTS Wc YD3j.as_const_g2f l W' md'' zz m) ->
at_S Wz mdz Xd (PSR Wz SH2 (PDX Wz RX ly' Wz mdz z)) T_2 Wz c4 ->
st_depot s4 = st_depot (depot_after z tr S) -> st_chunks s4 = st_chunks S -> st_secs s4 = st_secs S ++ [mkSec (sec_map_size n) (needed_size n) true] ->
st_sec_arr s4 = st_sec_arr S ++ [length (st_secs S)] ->
st_sec_reserved s4 = (if grow then st_sec_reserved S + kPtrArrayEntriesPerCommit else st_sec_reserved S) -> st_regions s4 = st_regions S ->
st_nev s4 = st_nev S + 1 -> st_cache_inited s4 = st_cache_inited S -> st_cache s4 = st_cache S -> st_qthread s4 = st_qthread S ->
st_qglobal s4 = st_qglobal S -> st_fs s4 = st_fs S -> st_internal_inited s4 = st_internal_inited S ->
amreal tfibsegs ((YG00.ret tt ;;
(YG00.modify (fun s0 => set_chunks (upd_chunk (st_chunks s0) (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated)) s0) ;;
YG00.ret (ck_user (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated)))) s4) Wz c4 QLEAF.
Proof.
intros Hsmall grow Wz mdz ly' RX Xd z c4 s4 Hgrow RXs RXt HRXQ HXW HXsub LEz IOz HWZ HOUT LG LY' IMG' DZ' HDPz HR D4 C4 SE4 A4 R4 RG4 N4 CI4 CA4 QT4 QG4 FS4 II4.
pose proof sizes_model as (ND & MS & RS & RZ & FP & KN & KR & KE & KQ & KB & KST).
eapply amreal_pure; [reflexivity|]. eapply amreal_pure; [reflexivity|]. cbn [amreal].
assert (LEAF : forall W' c', fin_post Wz mdz grow z ly' W' c' ->
QLEAF (ck_user (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated), set_chunks (upd_chunk (st_chunks s4) (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated)) s4) W' c').
{ intros W' c' (-> & regs' & mem' & mat' & memD' & -> & HF) MP.
assert (EQS : set_chunks (upd_chunk (st_chunks s4) (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated)) s4 = SFS grow z).
{ pose proof (YFib.upd_chunk_fresh (st_chunks S) (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated)
(YFib.KS_fresh S (as_universe B) 0 0 0 WF)) as UF.
clear HR. destruct s4; cbn in *. subst. unfold SFS, YFib.sfinal, YFib.depF, YFib.resF, YFib.KS, YFib.rS. cbn. cbn in UF. rewrite UF.
rewrite MS, ND. unfold depot_after. destruct grow; destruct (z =? 0); reflexivity. }
rewrite EQS in MP |- *. change (ck_user (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated)) with (ck_user KSc).
eapply (LEAF_S grow z Wz mdz ly'); eassumption. }
pose proof (HDPOST_from HDPz) as HDPOST.
step HR (segT2 Wz mdz RX RXs RXt Xd z HXW ly' DZ' _ _ HR). pose proof (proj1 HR) as EW. subst W0.
step HR (segU1 Wz mdz RX RXs RXt Xd z HXW ly' DZ' Hsmall _ _ HR). pose proof (proj1 HR) as EW. subst W0.
destruct (Z.eq_dec (n mod 8) 0) as [H8|H8].
- step HR (segUe Wz mdz RX RXs RXt Xd z HXW ly' DZ' H8 _ _ HR). pose proof (proj1 HR) as EW. subst W0.
eapply SRr_mono; [eapply (finE Wz mdz Xd RX grow z ly'); eassumption|].
intros W' c' _ HP. exact (LEAF W' c' HP).
- step HR (segUo Wz mdz RX RXs RXt Xd z HXW ly' DZ' H8 _ _ HR). pose proof (proj1 HR) as EW. subst W0.
eapply SRr_mono; [eapply (finO Wz mdz Xd RX grow z ly'); eassumption|].
intros W' c' _ HP. exact (LEAF W' c' HP).
Qed.
Lemma SRr_with_AI : forall (Wx : world tfibsegs) cx (Q : world tfibsegs -> config -> Prop),
SRr tfibsegs Wx cx Q -> SRr tfibsegs Wx cx (fun W' c' => AI tfibsegs (w_H W') (w_A W') (cfg_model c') /\ Q W' c').
Proof. clear. intros Wx cx Q H HI T HK. apply (H HI T). intros W' c' Hle HI' HQ. exact (HK W' c' Hle HI' (conj HI' HQ)). Qed.
Lemma amreal_askV : forall (q : kreq) (sN : astate) (Kc : Z -> itree astate (sptr * astate)) (Wx : world tfibsegs) (cx : config)
(Q : sptr * astate -> world tfibsegs -> config -> Prop),
match q with KDepot _ => False | _ => True end ->
SRr tfibsegs Wx cx (fun W1 c1 => exists (I : Type) (nx : I -> config) (bit : I -> Z) (sp : I -> bool) (i0 : I),
node_ok tfibsegs c1 I (fun _ => []) nx /\
(forall i, AI tfibsegs (w_H W1) (w_A W1) (cfg_model c1) -> AI tfibsegs (w_H W1) (w_A W1) (cfg_model (nx i))) /\
(forall i, aok sN q (bit i)) /\ sp i0 = false /\ bit i0 = 1 /\
(forall i, sp i = false -> bit i = 1) /\
(forall i, sp i = true -> AI tfibsegs (w_H W1) (w_A W1) (cfg_model (nx i)) -> srealizes tfibsegs (nx i) t_nil) /\
(forall i, sp i = false -> amreal tfibsegs (Kc (bit i)) W1 (nx i) Q)) ->
amreal tfibsegs (IAsk q sN Kc) Wx cx Q.
Proof. clear. intros q sN Kc Wx cx Q Hq H. destruct q; try (destruct Hq); cbn [amreal]; exact H. Qed.
Lemma same_io_wvb : forall md mat', same_io md0 md -> same_io md0 (with_vm_backing (m_vm_lazy md) mat' md).
Proof. clear. intros md mat' (X1 & X2 & X3 & X4). unfold same_io in *. rewrite <- X1, <- X2, <- X3, <- X4. repeat split; reflexivity. Qed.
Lemma TAILgB : 18446744073709551615 <= N8D / 8 -> forall (grow : bool) (Wz : world tfibsegs) (mdz : Model) (ly' : alayout) (RX : (word -> option byte) -> Prop) (Xd : Z -> Prop) z c4 s4,
(grow = true <-> idx = res) -> rstable RX -> pstable WIN1T RX -> (grow = true -> forall m, RX m -> ZQ Wz m) ->
(forall a, WIN a -> Xd a) -> (forall a, Xd a -> WIN a \/ (grow = true /\ QR a) \/ DX_at ly' a) ->
wle W Wz -> same_io md0 mdz -> (forall mat', wz_facts grow z ly' Wz (with_vm_backing (m_vm_lazy mdz) mat' mdz)) ->
(forall x : word, ~ (mb <= bv_unsigned x < mb + MSv) -> ~ (SHLO mb <= bv_unsigned x < SHHI mb) ->
~ (grow = true /\ QSv <= bv_unsigned x < QSv + 131072) ->
~ (fst (nb_ext ly') <= bv_unsigned x < fst (nb_ext ly') + snd (nb_ext ly')) ->
~ (fst (sb_ext ly') <= bv_unsigned x < fst (sb_ext ly') + snd (sb_ext ly')) -> w_H Wz x = w_H W x) ->
layout_grow ly ly' -> layout_ok ly' -> img_cover ly' -> (forall a, DZONE_at ly' a -> ~ WIN a /\ ~ (sp0 - ASTACK <= a < sp0)) ->
(forall l W' md'' zz m, DPOST l W' md'' zz m -> exists Wc, DPOSTS Wc YD3j.as_const_g2f l W' md'' zz m) ->
In (SHLO mb, SHHI mb) (w_A Wz) ->
at_S Wz mdz Xd (PSR Wz SH2 (PDX Wz RX ly' Wz mdz z)) T_2 Wz c4 ->
st_depot s4 = st_depot (depot_after z tr S) -> st_chunks s4 = st_chunks S -> st_secs s4 = st_secs S ++ [mkSec (sec_map_size n) (needed_size n) true] ->
st_sec_arr s4 = st_sec_arr S ++ [length (st_secs S)] ->
st_sec_reserved s4 = (if grow then st_sec_reserved S + kPtrArrayEntriesPerCommit else st_sec_reserved S) -> st_regions s4 = st_regions S ->
st_nev s4 = st_nev S + 1 -> st_cache_inited s4 = st_cache_inited S -> st_cache s4 = st_cache S -> st_qthread s4 = st_qthread S ->
st_qglobal s4 = st_qglobal S -> st_fs s4 = st_fs S -> st_internal_inited s4 = st_internal_inited S ->
amreal tfibsegs (((z' <- askz (KShadowRemap (ck_user (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated))
(8 * (ck_n (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated) / 8))) ;;
(if aGranted z' then YG00.ret tt else spin 12)) ;;
(YG00.modify (fun s0 => set_chunks (upd_chunk (st_chunks s0) (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated)) s0) ;;
YG00.ret (ck_user (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated)))) s4) Wz c4 QLEAF.
Proof.
intros Hbig. exfalso. clear - Hbig Nrange. unfold YFjm.N8D in Hbig. unfold MALLOC_MAX in Nrange.
rewrite Z.div_mul in Hbig by (clear; lia).
pose proof (Z.div_lt_upper_bound n 8 (2 ^ 25) ltac:(clear; lia) ltac:(clear - Nrange; lia)) as HH. clear Nrange. lia.
Qed.
Lemma after_depot : forall (grow : bool) (Wz : world tfibsegs) (mdz : Model) (ly' : alayout) (RX : (word -> option byte) -> Prop) (Xd : Z -> Prop) z c4 s3,
(grow = true <-> idx = res) -> rstable RX -> pstable WIN1T RX -> (grow = true -> forall m, RX m -> ZQ Wz m) ->
(forall a, WIN a -> Xd a) -> (forall a, Xd a -> WIN a \/ (grow = true /\ QR a) \/ DX_at ly' a) ->
wle W Wz -> same_io md0 mdz -> (forall mat', wz_facts grow z ly' Wz (with_vm_backing (m_vm_lazy mdz) mat' mdz)) ->
(forall x : word, ~ (mb <= bv_unsigned x < mb + MSv) -> ~ (SHLO mb <= bv_unsigned x < SHHI mb) ->
~ (grow = true /\ QSv <= bv_unsigned x < QSv + 131072) ->
~ (fst (nb_ext ly') <= bv_unsigned x < fst (nb_ext ly') + snd (nb_ext ly')) ->
~ (fst (sb_ext ly') <= bv_unsigned x < fst (sb_ext ly') + snd (sb_ext ly')) -> w_H Wz x = w_H W x) ->
layout_grow ly ly' -> layout_ok ly' -> img_cover ly' -> (forall a, DZONE_at ly' a -> ~ WIN a /\ ~ (sp0 - ASTACK <= a < sp0)) ->
(forall l W' md'' zz m, DPOST l W' md'' zz m -> exists Wc, DPOSTS Wc YD3j.as_const_g2f l W' md'' zz m) ->
In (SHLO mb, SHHI mb) (w_A Wz) ->
at_S Wz mdz Xd (PSR Wz SH2 (PDX Wz RX ly' Wz mdz z)) T_2 Wz c4 ->
st_depot s3 = st_depot S -> st_chunks s3 = st_chunks S -> st_secs s3 = st_secs S ++ [mkSec (sec_map_size n) (needed_size n) true] ->
st_sec_arr s3 = st_sec_arr S ++ [length (st_secs S)] ->
st_sec_reserved s3 = (if grow then st_sec_reserved S + kPtrArrayEntriesPerCommit else st_sec_reserved S) -> st_regions s3 = st_regions S ->
st_nev s3 = st_nev S + 1 -> st_cache_inited s3 = st_cache_inited S -> st_cache s3 = st_cache S -> st_qthread s3 = st_qthread S ->
st_qglobal s3 = st_qglobal S -> st_fs s3 = st_fs S -> st_internal_inited s3 = st_internal_inited S ->
amreal tfibsegs (KDEP s3 (PSec (length (st_secs S1)) kPage) z) Wz c4 QLEAF.
Proof.
intros grow Wz mdz ly' RX Xd z c4 s3 Hgrow RXs RXt HRXQ HXW HXsub LEz IOz HWZ HOUT LG LY' IMG' DZ' HDPz HULL HR D3 C3 SE3 A3' R3 RG3 N3 CI3 CA3 QT3 QG3 FS3 II3.
unfold KDEP. destruct (Z_lt_le_dec (N8D / 8) 18446744073709551615) as [Hsm|Hbg].
-
pose proof (fun s4 => TAILg Hsm grow Wz mdz ly' RX Xd z c4 s4 Hgrow RXs RXt HRXQ HXW HXsub LEz IOz HWZ HOUT LG LY' IMG' DZ' HDPz HR) as TAIL.
rewrite (NR Hsm).
destruct (Z.eqb_spec z 0) as [Z0|Z0].
+ eapply amreal_pure; [reflexivity|]. apply TAIL; try assumption. rewrite D3. unfold depot_after. rewrite (proj2 (Z.eqb_eq z 0) Z0). reflexivity.
+ cbn beta iota. rewrite !bind_assoc_eq. eapply amreal_pure; [reflexivity|]. rewrite !bind_assoc_eq.
unfold mcheck at 1. destruct (depot_ids _ + 1 <? kDepotIdsPerBlock); [| cbn [amreal YG00.bind fail ibind]; exact I].
eapply amreal_pure; [reflexivity|]. rewrite !bind_assoc_eq.
unfold mcheck at 1. destruct (kStartFramesMax + _ + _ + 1 <? kStoreFramesPerBlock); [| cbn [amreal YG00.bind fail ibind]; exact I].
eapply amreal_pure; [reflexivity|]. eapply amreal_pure; [reflexivity|].
apply TAIL; cbn; try assumption. rewrite D3. unfold depot_after. rewrite (proj2 (Z.eqb_neq z 0) Z0). reflexivity.
-
pose proof (fun s4 => TAILgB Hbg grow Wz mdz ly' RX Xd z c4 s4 Hgrow RXs RXt HRXQ HXW HXsub LEz IOz HWZ HOUT LG LY' IMG' DZ' HDPz HULL HR) as TAIL.
rewrite (NRb Hbg).
destruct (Z.eqb_spec z 0) as [Z0|Z0].
+ eapply amreal_pure; [reflexivity|]. apply TAIL; try assumption. rewrite D3. unfold depot_after. rewrite (proj2 (Z.eqb_eq z 0) Z0). reflexivity.
+ cbn beta iota. rewrite !bind_assoc_eq. eapply amreal_pure; [reflexivity|]. rewrite !bind_assoc_eq.
unfold mcheck at 1. destruct (depot_ids _ + 1 <? kDepotIdsPerBlock); [| cbn [amreal YG00.bind fail ibind]; exact I].
eapply amreal_pure; [reflexivity|]. rewrite !bind_assoc_eq.
unfold mcheck at 1. destruct (kStartFramesMax + _ + _ + 1 <? kStoreFramesPerBlock); [| cbn [amreal YG00.bind fail ibind]; exact I].
eapply amreal_pure; [reflexivity|]. eapply amreal_pure; [reflexivity|].
apply TAIL; cbn; try assumption. rewrite D3. unfold depot_after. rewrite (proj2 (Z.eqb_neq z 0) Z0). reflexivity.
Qed.
Lemma QSP3 : idx <> res -> QSP W3 (zfill (w64 mb) (w64 MSv) (ms_mem ms)).
Proof.
intros NE u Hu. pose proof high_facts as (_ & _ & _ & _ & _ & _ & _ & _ & F9 & F10 & _). pose proof map_facts as (M1 & M2 & _). pose proof map_zoneN as MZ.
pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & _). pose proof Hidx as HI. pose proof Hres as [HRS HRA].
assert (Ru : TFIB_IMG_END <= u < 2 ^ 64) by (clear - Hu F9 F10 HI HRS MZ; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, QSv, TFIB_IMG_END, kHighMemBeg, ASAN_CEIL, kPtrArrayResv, kMaxNumChunks, YImgTop.IMG_LO, YImgTop.IMG_TOP in *; try unfold Qb in *; zlia).
assert (P0 : apresent (w_H W) mem0 u).
{ apply (vis_present (AQ 0) (8 * st_sec_reserved S) u); [right; unfold aareas; apply in_app_iff; right; left; reflexivity | cbn [aeval]; rewrite <- Hres_def; unfold QSv in Hu; try unfold Qb in Hu; clear - Hu HI HRS NE MZ; zlia | off_by ltac:(exact Ru) ]. }
destruct P0 as [Hh [b Hb']]. split; [exact (MON3 _ Hh)|]. exists b. rewrite zfill_out.
- rewrite MEQ; [exact Hb'|]. rewrite unsigned_lit_small by (clear - Ru MZ; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END, YImgTop.IMG_LO, YImgTop.IMG_TOP in Ru; zlia). unfold WINP, WINT, WINI. pose proof BSLv_range as HBS. pose proof high_facts as (F1 & _). destruct Hsp as (S1' & _ & S3' & _).
pose proof stack_ivs as (_ & _ & _ & SI4). pose proof HCX as (_ & _ & QT & _). unfold zdisjoint in QT. cbn [fst snd] in QT.
clear - Hu F1 F9 F10 HI HRS HBS S1' S3' SI4 QT MZ. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, QSv, kHighMemBeg, ASAN_CEIL, kPtrArrayResv, kMaxNumChunks, ASTACK, t_unwinding, kThreadObjSize, TFIB_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex, YImgTop.IMG_LO, YImgTop.IMG_TOP in *.
try unfold Qb in *. try unfold T in *. try unfold sp0 in *. zlia.
- rewrite Umb. unfold w64. rewrite !unsigned_lit_small by (clear - Ru M1 M2 Z8 MZ; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END, kHighMemBeg, ASAN_CEIL, MALLOC_MAX, YImgTop.IMG_LO, YImgTop.IMG_TOP in *; zlia).
destruct Hmap_apart as (_ & _ & _ & MQ & _). unfold zdisjoint in MQ. cbn [fst snd] in MQ. clear - Hu MQ HI HRS F9 F10 MZ. unfold QSv, kPtrArrayResv, kMaxNumChunks in *. try unfold Qb in *. zlia.
Qed.
Lemma HmapD : zdisjoint (mb, MSv) (ly_D ly, 4096).
Proof. apply (proj1 (Forall_forall _ _) GAP). apply in_app_iff. left. unfold static_extents, owned_extents. apply in_app_iff. left. cbn. tauto. Qed.
Lemma UMS : bv_unsigned (w64 MSv) = MSv.
Proof. pose proof MSB as MS'. unfold w64. apply unsigned_lit_small. clear - MS'. unfold MALLOC_MAX in MS'. zlia. Qed.
Lemma grant50_top : forall (a k : word) md, alloc_top (m_vmmaps (grant_md false (Z_to_bv 64 50) a k md)) = alloc_top (m_vmmaps md).
Proof.
clear. intros a k md. unfold grant_md, fixedin_ok_model, fixedin_ok_vmmaps, with_mmap_replacement, with_mmap_backing. rewrite YFjt.nores50. cbn.
destruct md as [fd [maps lazy mat'] io fs pr lim tm sg sc]. cbn. destruct maps; cbn; reflexivity.
Qed.
Lemma SZF : forall grow z, Forall (fun e => 0 <= snd e < 2 ^ 64) (sec_extents lyF (SFS grow z)).
Proof.
intros grow z. pose proof MSB as MS'. rewrite (SEF grow z). apply Forall_app. split.
- eapply Forall_impl; [|exact (YG08.sec_extents_sizes64P _ 0 0 0 ly S WF)]. cbv beta. intros e He. lia.
- constructor; [|constructor]. cbn [snd]. clear - MS'. unfold MALLOC_MAX in MS'. lia.
Qed.
(* The static depot zone [tfib_dzone_lo, tfib_dzone_hi) misses the walk's map, its shadow hull and the Q commit. *)
Lemma dzone_apart : forall a, YD3j.tfib_dzone_lo <= a < YD3j.tfib_dzone_hi ->
0 <= a < 2 ^ 64 /\ ~ (mb <= a < mb + MSv) /\ ~ (SHLO mb <= a < SHHI mb) /\ (idx = res -> ~ (QSv <= a < QSv + 131072)).
Proof.
intros a Ha. pose proof map_facts as (M1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & _ & _ & _ & SMA). pose proof map_zoneN as MZ.
assert (SL : shadow_addr mb - 4096 < SHLO mb).
{ unfold YFjs.SHLO. pose proof (Z.mod_pos_bound (shadow_addr mb) 4096 ltac:(lia)) as MB. pose proof (Z.div_mod (shadow_addr mb) 4096 ltac:(lia)) as DM. lia. }
rewrite <- SMA in SL. unfold YD3j.tfib_dzone_lo, YD3j.tfib_dzone_hi in Ha.
split; [lia|]. split; [|split].
- clear - Ha M1 MZ. zlia.
- clear - Ha SL MZ. zlia.
- intros EQ. pose proof (QR_facts EQ) as (_ & _ & _ & F9 & _). clear - Ha F9. try unfold Qb in *. zlia.
Qed.
Lemma dzone_view : forall (Wc : world tfibsegs),
(forall a, YD3j.tfib_dzone_lo <= a < YD3j.tfib_dzone_hi -> w_H Wc (Z_to_bv 64 a) = w_H W (Z_to_bv 64 a)) ->
forall a, YD3j.tfib_dzone_lo <= a < YD3j.tfib_dzone_hi -> aview tfibsegs (w_H Wc) mem0 a = aview tfibsegs (w_H W) mem0 a.
Proof. clear. intros Wc EH a Ha. unfold aview, mrestrict, YP09.mbyte. cbn beta. rewrite (EH a Ha). reflexivity. Qed.
(* The first Put's premises at a Put's call world Wc / model md (YFix.first_put_pre_of_AR_at, X := the walk's map). *)
Lemma FPP_site : forall (Wc : world tfibsegs) (md : Model) (k : Z),
(forall a, YD3j.tfib_dzone_lo <= a < YD3j.tfib_dzone_hi -> w_H Wc (Z_to_bv 64 a) = w_H W (Z_to_bv 64 a)) ->
vm_limit (m_vmmaps md) = vm_limit (m_vmmaps md2) -> vm_reserved (m_vmmaps md) = vm_reserved (m_vmmaps md2) ->
alloc_top (m_vmmaps md) = alloc_top (m_vmmaps md2) -> vm_maps (m_vmmaps md) = vm_maps (m_vmmaps md2) -> amwf md ->
eager_used md <= eager_used md0 + k -> A_bytes (w_A Wc) <= A_bytes (w_A W) + k -> 0 <= k -> 2 * k + 11 * 2 ^ 20 <= 2 ^ 30 ->
st_depot S = [] -> YD3j.depot_first_put_pre depot_ok B Wc ly S mem0 md tr.
Proof.
intros Wc md k EH LIM RES TOP MAPS MWd EG AB Hk HK E0.
pose proof VM2 as (VMa & VMr & VMl & _).
assert (MN : m_vmmaps mdN = m_vmmaps md0) by (unfold mdN; apply m_vmmaps_wvb).
assert (TOP2 : alloc_top (m_vmmaps md2) = alloc_top (m_vmmaps md0))
  by (unfold md2; rewrite (proj1 (proj2 (proj2 (YD3j.b2_mmap_vm (w64 mb) (w64 MSv) mdN)))), MN; reflexivity).
assert (TOPd : alloc_top (m_vmmaps md) = alloc_top (m_vmmaps md0)) by (rewrite TOP, TOP2; reflexivity).
assert (RESd : vm_reserved (m_vmmaps md) = vm_reserved (m_vmmaps md0)) by (rewrite RES, VMr, MN; reflexivity).
assert (MAPSd : vm_maps (m_vmmaps md) = (w64 mb, w64 MSv) :: vm_maps (m_vmmaps md0)) by (rewrite MAPS, VMa, MN; reflexivity).
pose proof MSB as MS'. pose proof UMS as UM.
apply (YFix.first_put_pre_of_AR_at B W Wc ly S mem0 mem0 md0 md tr [(w64 mb, w64 MSv)] k TS IMG HAR (proj2 HQT) E0).
- exact (dzone_view Wc EH).
- rewrite LIM, VMl, MN; reflexivity.
- exact RESd.
- rewrite TOPd. lia.
- intros e He. rewrite MAPSd in He. destruct He as [<-|He]; [right; left; reflexivity | left; exact He].
- constructor; [|constructor]. cbn [snd]. rewrite UM. unfold YF06.NOB. clear - MS'. unfold MALLOC_MAX in MS'. lia.
- cbn. lia.
- exact EG.
- exact AB.
- exact Hk.
- exact HK.
- pose proof (proj1 (YG0b.amwf_MWF md) (proj1 MWd)) as [(MI & _) _]. exact MI.
- rewrite TOPd. exact (al_top _ _ _ _ (proj1 (proj2 HAR))).
- intros e. unfold YD3d.md_takes. rewrite TOPd, RESd, MAPSd. intros [[P C]|F]; [left; split; [exact P|] | right; exact F].
intros a Ha. pose proof (C a Ha) as Ex. apply Exists_exists in Ex as (q & Hq & Hqa). apply Exists_exists. exists q. split; [|exact Hqa].
apply in_app_iff in Hq as [Hq|Hq]; apply in_app_iff; [left; exact Hq | right; right; exact Hq].
Qed.
(* dpost-jfamily-text §3b's HMAPD at a Put's call (Wy, md1) whose maps hold the walk's map (mb, MSv): the no-growth arm by
   Hmap_apart, the growth arm by amendment 11 (YD3j.first_put_vm_maps_fresh). *)
Lemma HMAPD_of : forall (Wy : world tfibsegs) (md1 : Model), In (w64 mb, w64 MSv) (vm_maps (m_vmmaps md1)) ->
forall md l W' md' regs mem c', same_but_materialized md1 md -> YD3j.put_effect layout_grow ly Wy md l W' md' ->
(st_depot S = [] -> YD3j.depot_first_put_post depot_ok YD3j.as_const_g2f B Wy ly S regs mem md tr l W' md' c') ->
zdisjoint (mb, MSv) (nb_ext l) /\ zdisjoint (mb, MSv) (sb_ext l).
Proof.
intros Wy md1 IN md l W' md' regs mem c' SBM PE FPP.
destruct PE as [(-> & _ & _) | (nb & sb & N0 & _)].
- destruct Hmap_apart as (_ & _ & _ & _ & A5 & A6 & _). exact (conj A5 A6).
- assert (E0 : st_depot S = []).
{ destruct (st_depot S) as [|t0 l0] eqn:ES; [reflexivity|]. exfalso.
exact (proj1 (depot_ok_mapped B ly rd0 S (am_depot B ly S rd0 MA) ltac:(rewrite ES; discriminate)) N0). }
assert (IN' : In (w64 mb, w64 MSv) (vm_maps (m_vmmaps md))) by (rewrite (YD3j.sbm_vmmaps _ _ SBM); exact IN).
pose proof (YD3j.first_put_vm_maps_fresh depot_ok YD3j.as_const_g2f B Wy ly S regs mem md tr l W' md' c' (w64 mb, w64 MSv) (FPP E0) IN') as FP.
cbn [fst snd] in FP. rewrite Umb, UMS in FP. exact FP.
Qed.
(* YFjp.nb_facts_at / DZONE_disj_at, restated here (their closures are not pinned). *)
Lemma nbf_at : forall l, layout_ok l -> img_cover l -> layout_grow ly l ->
zone3 (fst (nb_ext l)) (snd (nb_ext l)) /\ zone3 (fst (sb_ext l)) (snd (sb_ext l)) /\
zdisjoint (ly_T ly, kThreadObjSize) (nb_ext l) /\ zdisjoint (ly_T ly, kThreadObjSize) (sb_ext l) /\
zdisjoint (ly_Q ly, kPtrArrayResv) (nb_ext l) /\ zdisjoint (ly_Q ly, kPtrArrayResv) (sb_ext l) /\
zdisjoint (nb_ext l) (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) /\
zdisjoint (sb_ext l) (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) /\
zdisjoint (ly_C ly, 256) (nb_ext l) /\ zdisjoint (ly_C ly, 256) (sb_ext l).
Proof.
intros l LYl IMGl GR.
assert (GF : ly_T l = ly_T ly /\ ly_Q l = ly_Q ly /\ ly_C l = ly_C ly /\ ly_stk_lo l = ly_stk_lo ly /\ ly_stk_hi l = ly_stk_hi ly)
by (destruct GR as (nb & sb & _ & _ & ->); repeat split).
destruct GF as (GT & GQ & GC & GSL & GSH).
pose proof (@YFjm.blocks_facts _ l LYl IMGl) as BF. rewrite GT, GQ, GC, GSL, GSH in BF. exact BF.
Qed.
Lemma DZ_at : forall l, layout_ok l -> img_cover l -> layout_grow ly l ->
zdisjoint (mb, MSv) (nb_ext l) -> zdisjoint (mb, MSv) (sb_ext l) ->
forall a, DZONE_at l a -> ~ WIN a /\ ~ (sp0 - ASTACK <= a < sp0).
Proof.
intros l LYl IMGl GR MNB MSB' a Ha. pose proof high_facts as (F1 & _ & _ & _ & _ & _ & _ & _ & F9 & _).
pose proof (nbf_at l LYl IMGl GR) as (NBhi & SBhi & TNB & TSB & QNB & QSB & NBS & SBS & _).
destruct Hsp as (S1' & _ & S3' & _). pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7). pose proof BSLv_range as HB'.
pose proof map_facts as (M1 & M2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _). pose proof Hidx as HI.
unfold zdisjoint in TNB, TSB, QNB, QSB, NBS, SBS, MNB, MSB'. cbn [fst snd] in TNB, TSB, QNB, QSB, NBS, SBS, MNB, MSB'.
clear - Ha F1 F9 NBhi SBhi TNB TSB QNB QSB NBS SBS T7 HB' M1 M2 SM1 SM2 HI MNB MSB' S1' S3'.
unfold YFjm.DZONE, KnBlockExt.DZONE_at, YD3j.tfib_dzone_lo, YD3j.tfib_dzone_hi, WIN, WINT, WINI, WINM, QSv in *.
ceil; unfold zone3, zone3cases, kHighMemBeg, kHighShadowBeg, kHighShadowEnd, kLowShadowBeg, TFIB_IMG_LO, TFIB_IMG_END, ASAN_CEIL, t_unwinding, kThreadObjSize, ASTACK, kPtrArrayResv, kMaxNumChunks,
kNodesBlockSize, kStoreBlockSize, TFIB_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex, YImgTop.IMG_LO, YImgTop.IMG_TOP in *. try unfold T in *. try unfold Qb in *.
destruct Ha as [Ha|[Ha|Ha]].
- clear TNB TSB QNB QSB NBS SBS MNB MSB'. split; lia.
- clear SBhi TSB QSB SBS MSB'. split; lia.
- clear NBhi TNB QNB NBS MNB. split; lia.
Qed.
(* RXd (dpost-jfamily-text §3) for the grow = true walk's RX: the Q commit misses DX_at l for every grown l. *)
Lemma RZ_stable_at : forall (Wz : world tfibsegs) l, layout_ok l -> img_cover l -> layout_grow ly l -> pstable (DX_at l) (RZ Wz (fun _ => True)).
Proof.
intros Wz l LYl IMGl GR m m' FR [_ H]. split; [exact I|].
intros Heq a Ha Hs. destruct (H Heq a Ha Hs) as [H1 H2]. split; [exact H1|]. rewrite FR; [exact H2|].
pose proof (QR_facts Heq) as (_ & _ & _ & F9 & Q5 & F10 & EQ). pose proof (proj1 (EQ a) Ha) as Ra.
rewrite unsigned_lit_small by (clear - Ra F9 F10 Q5; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kPtrArrayResv, YImgTop.IMG_LO, YImgTop.IMG_TOP in *; try unfold Qb in *; zlia).
pose proof (nbf_at l LYl IMGl GR) as (NBhi & SBhi & _ & _ & QNB & QSB & _). unfold zdisjoint in QNB, QSB. cbn [fst snd] in QNB, QSB.
destruct Hsp as (S1' & _ & S3' & _). pose proof (lo_stk_ceil ly LY) as SC.
intros [Hd|Hd]; revert Hd; clear - Ra F9 F10 Q5 QNB QSB S1' S3' SC; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, KnBlockExt.DZONE_at, YD3j.tfib_dzone_lo, YD3j.tfib_dzone_hi, DEP_STK, ASTACK, kHighMemBeg, ASAN_CEIL, kPtrArrayResv, kNodesBlockSize, kStoreBlockSize, YImgTop.IMG_LO, YImgTop.IMG_TOP in *; try unfold Qb in *; try unfold sp0 in *; zlia.
Qed.
(* put_effect's world / model facts the tail reads at the post-Put world. *)
Lemma put_frame : forall (Wy W2 : world tfibsegs) md1 ly' md', YD3j.put_effect layout_grow ly Wy md1 ly' W2 md' ->
forall x : word, ~ (fst (nb_ext ly') <= bv_unsigned x < fst (nb_ext ly') + snd (nb_ext ly')) ->
~ (fst (sb_ext ly') <= bv_unsigned x < fst (sb_ext ly') + snd (sb_ext ly')) -> w_H W2 x = w_H Wy x.
Proof.
clear. intros Wy W2 md1 ly' md' [(_ & -> & _) | (nb & sb & _ & _ & NZ & SZ & EL & _ & _ & WH & _)] x N1 N2; [reflexivity|].
assert (NB' : ly_NB ly' = nb) by (rewrite EL; reflexivity). assert (SB' : ly_SB ly' = sb) by (rewrite EL; reflexivity).
rewrite (nb_ext_set ly' ltac:(rewrite NB'; exact NZ)), NB' in N1. rewrite (sb_ext_set ly' ltac:(rewrite SB'; exact SZ)), SB' in N2.
cbn [fst snd] in N1, N2. exact (WH x N1 N2).
Qed.
Lemma put_io : forall (Wy W2 : world tfibsegs) md1 ly' md', YD3j.put_effect layout_grow ly Wy md1 ly' W2 md' -> same_io md1 md'.
Proof. clear. intros Wy W2 md1 ly' md' [(_ & _ & SBM) | (nb & sb & _ & _ & _ & _ & _ & _ & _ & _ & IO & _)]; [exact (YD3j.sbm_io _ _ SBM) | exact IO]. Qed.
Lemma put_wA : forall (Wy W2 : world tfibsegs) md1 ly' md', YD3j.put_effect layout_grow ly Wy md1 ly' W2 md' ->
forall i, In i (w_A Wy) -> In i (w_A W2).
Proof. clear. intros Wy W2 md1 ly' md' [(_ & -> & _) | (nb & sb & _ & _ & _ & _ & _ & _ & WA & _)] i Hi; [exact Hi | rewrite WA; right; right; exact Hi]. Qed.
(* at_S_depot's post at the post-Put world W2: the layout step, DZ' (dpost-jfamily-text §5 / J4: DZONE_disj at ly' with
   HMAPD's facts), the depot answer z, PDX read at W2 (its mem0 presence clause moves from the call world Wy to W2: on
   the two new blocks B2's depot_first_put_facts make memD visible, elsewhere w_H W2 = w_H Wy), and B2's post for the
   grown ledger. *)
Lemma post_put : forall (Wy W2 : world tfibsegs) (md1 md' : Model) ly' z (RX : (word -> option byte) -> Prop) (X : Z -> Prop) c,
In (w64 mb, w64 MSv) (vm_maps (m_vmmaps md1)) ->
YD3j.put_effect layout_grow ly Wy md1 ly' W2 md' -> layout_ok ly' -> img_cover ly' ->
at_S W2 md' X (PSR W2 SH2 (PDX Wy RX ly' W2 md' z)) T_2 W2 c ->
layout_grow ly ly' /\ (forall a, DZONE_at ly' a -> ~ WIN a /\ ~ (sp0 - ASTACK <= a < sp0)) /\ aok S (KDepot tr) z /\
at_S W2 md' X (PSR W2 SH2 (PDX W2 RX ly' W2 md' z)) T_2 W2 c /\
(ly_NB ly = 0 -> st_depot S = [] /\ exists (Wc : world tfibsegs) regs mem (md : Model) c',
   vm_maps (m_vmmaps md) = vm_maps (m_vmmaps md1) /\
   YD3j.depot_first_put_post depot_ok YD3j.as_const_g2f B Wc ly S regs mem md tr ly' W2 md' c').
Proof.
intros Wy W2 md1 md' ly' z RX X c IN PE LY' IMG' HR.
pose proof HR as HRc. destruct HRc as (_ & ms' & mat' & E & _ & _ & _ & _ & _ & [_ [(memD & DP & _ & _) _]]).
destruct (proj1 (HDP ly' W2 md' z memD) DP) as (Wc & AOK & _ & _ & FPP).
assert (E0of : ly_NB ly = 0 -> st_depot S = []).
{ intros N0. destruct (st_depot S) as [|t0 l0] eqn:ES; [reflexivity|]. exfalso.
exact (proj1 (depot_ok_mapped B ly rd0 S (am_depot B ly S rd0 MA) ltac:(rewrite ES; discriminate)) N0). }
destruct PE as [(-> & -> & SBM) | (nb & sb & N0 & S0 & NZ & SZ & EL & LGk & WA & WH & IO & VM & LZ)].
- split; [apply layout_grow_refl|]. split; [intros a Ha; exact (DZONE_disj a Ha)|]. split; [exact AOK|]. split; [exact HR|].
intros N0. exfalso. destruct (FPP (E0of N0)) as (_ & r1 & r2 & r3 & r4 & _ & POST).
destruct POST as (regs' & mem' & _ & _ & _ & _ & _ & _ & _ & (HN & _) & _). exact (HN N0).
- pose proof (E0of N0) as E0.
assert (NB' : ly_NB ly' = nb) by (rewrite EL; reflexivity). assert (SB' : ly_SB ly' = sb) by (rewrite EL; reflexivity).
assert (NB0 : ly_NB ly' <> 0) by (rewrite NB'; exact NZ). assert (SB0 : ly_SB ly' <> 0) by (rewrite SB'; exact SZ).
destruct (FPP E0) as (_ & regsc & memc & mdc & regs2 & PEc & POSTc).
assert (VMc : vm_maps (m_vmmaps mdc) = vm_maps (m_vmmaps md1)).
{ destruct PEc as [(Ely & _ & _) | (nb2 & sb2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & VMd & _)].
- exfalso. apply NB0. rewrite Ely. exact N0.
- assert (VMM : forall (a n0 : word) (m0 : Model), vm_maps (m_vmmaps (mmap_model a n0 m0)) = (a, n0) :: vm_maps (m_vmmaps m0))
by (intros a n0 m0; exact (proj1 (proj2 (proj2 (proj2 (YD3j.b2_mmap_vm a n0 m0)))))).
pose proof (f_equal (fun h => tl (tl (vm_maps h))) (eq_trans (eq_sym VM) VMd)) as T0. cbv beta in T0.
rewrite !VMM in T0. cbn [tl] in T0. symmetry. exact T0. }
assert (MNB : zdisjoint (mb, MSv) (nb_ext ly') /\ zdisjoint (mb, MSv) (sb_ext ly')).
{ pose proof (YD3j.first_put_vm_maps_fresh depot_ok YD3j.as_const_g2f B Wc ly S regsc memc mdc tr ly' W2 md' _ (w64 mb, w64 MSv) POSTc
ltac:(rewrite VMc; exact IN)) as FP.
cbn [fst snd] in FP. rewrite Umb, UMS in FP. exact FP. }
assert (LGl : layout_grow ly ly') by exact LGk.
assert (CONV : forall memD', DPOST ly' W2 md' z memD' ->
(forall a, DZONE_at ly' a -> apresent (w_H Wy) mem0 a -> apresent (w_H W2) memD' a) ->
forall a, DZONE_at ly' a -> apresent (w_H W2) mem0 a -> apresent (w_H W2) memD' a).
{ intros memD' DP' PRD' a Ha Hp.
destruct (proj1 (HDP ly' W2 md' z memD') DP') as (Wc' & _ & _ & _ & FPP').
destruct (FPP' E0) as (_ & rg & mm & mdd & rg2 & _ & POST').
destruct POST' as (regs' & mem' & Ec & _ & _ & _ & _ & _ & _ & FACTS & _ & _ & _ & IAN & _ & IAS & _ & FNB & FSB & _).
apply (f_equal (fun c0 => ms_mem (cfg_ms c0))) in Ec. cbn in Ec. subst mem'.
destruct FACTS as (_ & _ & _ & _ & _ & _ & RV).
rewrite NB' in IAN, FNB. rewrite SB' in IAS, FSB.
pose proof (proj1 (Forall_forall _ _) FNB (ly_img ly) ltac:(unfold YD3j.first_put_avoid, YD3g.ext_but_NB; rewrite !in_app_iff; left; left; cbn [In]; tauto)) as DNI.
pose proof (proj1 (Forall_forall _ _) FSB (ly_img ly) ltac:(unfold YD3j.first_put_avoid, YD3g.ext_but_NB; rewrite !in_app_iff; left; left; cbn [In]; tauto)) as DSI.
pose proof (YG0s.in_app_small _ _ IAN ltac:(unfold kNodesBlockSize; lia)) as NBR.
pose proof (YG0s.in_app_small _ _ IAS ltac:(unfold kStoreBlockSize; lia)) as SBR.
assert (AA : forall k, In k [(ANB 0, kNodesBlockSize); (ASB 0, kStoreBlockSize)] -> range_vis B ly' (aview tfibsegs (w_H W2) memD') k).
{ intros k Hk. apply (proj1 (Forall_forall _ _) RV). apply in_app_iff. right.
unfold YD3j.aareas_depot_kd, depot_after. cbn. rewrite E0. cbn. exact Hk. }
destruct (zr_dec nb (nb + kNodesBlockSize) a) as [INB|NNB].
{ pose proof (AA _ ltac:(left; reflexivity) (a - nb) ltac:(cbn [snd]; lia)) as V. cbn [fst aeval] in V. rewrite NB' in V.
replace (nb + 0 + (a - nb)) with a in V by lia.
eapply YG0s.aview_present; [exact (proj1 (proj2 HAR)) | lia | | exact V].
unfold zdisjoint in DNI. unfold in_zr. cbn [fst snd] in DNI. lia. }
destruct (zr_dec sb (sb + kStoreBlockSize) a) as [ISB|NSB].
{ pose proof (AA _ ltac:(right; left; reflexivity) (a - sb) ltac:(cbn [snd]; lia)) as V. cbn [fst aeval] in V. rewrite SB' in V.
replace (sb + 0 + (a - sb)) with a in V by lia.
eapply YG0s.aview_present; [exact (proj1 (proj2 HAR)) | lia | | exact V].
unfold zdisjoint in DSI. unfold in_zr. cbn [fst snd] in DSI. lia. }
assert (Ra : 0 <= a < 2 ^ 64).
{ unfold YFjm.DZONE, KnBlockExt.DZONE_at in Ha. rewrite (nb_ext_set ly' NB0), (sb_ext_set ly' SB0), NB', SB' in Ha. cbn [fst snd] in Ha.
unfold YD3j.tfib_dzone_lo, YD3j.tfib_dzone_hi in Ha. lia. }
apply PRD'; [exact Ha|]. destruct Hp as [Hh Hb]. split; [|exact Hb].
rewrite <- (WH (Z_to_bv 64 a)); [exact Hh | rewrite unsigned_lit_small by exact Ra; exact NNB | rewrite unsigned_lit_small by exact Ra; exact NSB]. }
assert (HR' : at_S W2 md' X (PSR W2 SH2 (PDX W2 RX ly' W2 md' z)) T_2 W2 c).
{ apply (at_S_weaken W2 md' X X (PSR W2 SH2 (PDX Wy RX ly' W2 md' z)) _ T_2 W2 c HR (fun a Ha => Ha)).
intros m [HPS [(memD' & DP' & PRD' & EQD') HRX]]. split; [exact HPS|]. split; [|exact HRX].
exists memD'. split; [exact DP'|]. split; [exact (CONV memD' DP' PRD') | exact EQD']. }
split; [exact LGl|]. split; [exact (DZ_at ly' LY' IMG' LGl (proj1 MNB) (proj2 MNB))|]. split; [exact AOK|]. split; [exact HR'|].
intros _. split; [exact E0|]. exists Wc, regsc, memc, mdc. eexists. split; [exact VMc | exact POSTc].
Qed.
(* wz_facts' grown ledger and amwf on the growth arm (WZ_put's GR), from the ledger at the Put's call model md1. *)
Lemma GR_of : forall (grow : bool) z (Wy W4 : world tfibsegs) (md1 md4 : Model) ly',
ALedger tfibsegs lyF (SFS grow z) md1 -> amwf md1 -> YD3j.put_effect layout_grow ly Wy md1 ly' W4 md4 ->
(ly_NB ly = 0 -> st_depot S = [] /\ exists (Wc : world tfibsegs) regs mem (md : Model) c',
   vm_maps (m_vmmaps md) = vm_maps (m_vmmaps md1) /\
   YD3j.depot_first_put_post depot_ok YD3j.as_const_g2f B Wc ly S regs mem md tr ly' W4 md4 c') ->
ly_NB ly = 0 -> ly_NB ly' <> 0 -> ALedger tfibsegs (lyF_at ly') (SFS grow z) md4 /\ amwf md4.
Proof.
intros grow z Wy W4 md1 md4 ly' L1 M1 PE GRW N0 NB0.
destruct PE as [(-> & _ & _) | (nb & sb & _ & S0 & NZ & SZ & EL & _ & _ & _ & _ & VM & LZ)]; [exfalso; exact (NB0 N0)|].
destruct (GRW N0) as (_ & Wc & regs & mem & md & c' & VMd & POST).
subst ly'.
exact (YFk0g.ALedger_grow B ly lyF S (SFS grow z) md1 md4 Wc W4 regs mem md tr nb sb md4 c' eq_refl lyF_ok N0 S0 NZ SZ L1 M1 (SZF grow z)
(placed_finalG grow z HAR GAP) POST VMd VM LZ).
Qed.
Theorem grantS_ne : idx <> res -> amreal tfibsegs (KSEC 1) W3 ccont QLEAF.
Proof.
intros NE. pose proof Hidx as HI. pose proof Hres as [HRS HRA]. pose proof MSB as MS0.
pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & Z9 & _). pose proof (SH_hull mb) as (H1 & H2 & H3 & _).
pose proof (grant_cont mb0 W3 md2 (QSPX W3 (fun _ => True)) ms E' HE' HS MEQ PRS HB SUB3 VISM SHZ (conj (QSP3 NE) I)) as HR.
unfold KSEC. change (1 =? 0) with false. cbn iota. unfold sec_body. rewrite !bind_assoc_eq.
eapply amreal_pure; [reflexivity|]. rewrite !bind_assoc_eq.
eapply amreal_pure; [unfold mcheck; replace (Z.of_nat (length (st_sec_arr S1)) <? kMaxNumChunks) with true by (symmetry; apply Z.ltb_lt; unfold S1; cbn; rewrite <- Hidx_def; exact (proj2 HI)); reflexivity|].
rewrite !bind_assoc_eq. eapply amreal_pure; [reflexivity|]. rewrite !bind_assoc_eq.
replace (Z.of_nat (length (st_sec_arr S1)) =? st_sec_reserved S1) with false by (symmetry; apply Z.eqb_neq; unfold S1; cbn; rewrite <- Hidx_def, <- Hres_def; exact NE).
eapply amreal_pure; [reflexivity|]. rewrite !bind_assoc_eq. eapply amreal_pure; [reflexivity|]. eapply amreal_pure; [reflexivity|].
rewrite malloc_K_some.
pose proof (rstable_and (QSP W3) (fun _ => True) (QSP_rstable W3) rstable_true) as RST.
assert (RXs : rstable (fun _ : word -> option byte => True)) by exact rstable_true.
assert (RXt : pstable WIN1T (fun _ : word -> option byte => True)) by (clear; intros m m' _ _; exact I).
assert (RXd : forall l, layout_ok l -> img_cover l -> layout_grow ly l -> pstable (DX_at l) (fun _ : word -> option byte => True))
by (clear; intros l _ _ _ m m' _ _; exact I).
assert (HXW : forall a, WIN a -> WIN a) by (clear; intros a H; exact H).
assert (HXQ : forall a, WIN a -> WIN a \/ QR a) by (clear; intros a H; left; exact H).
pose proof (D1W_ok W3 MON3 Htr HmapD YD3j.as_const_g2f YD3j.as_const_g2f_def (HDPOST'_at W3) D1) as D1w.
assert (IN3 : In (w64 mb, w64 MSv) (vm_maps (m_vmmaps md2))) by (rewrite (proj1 VM2); left; reflexivity).
assert (FPP3 : st_depot S = [] -> YD3j.depot_first_put_pre depot_ok B W3 ly S mem0 md2 tr).
{ apply (FPP_site W3 md2 (MSv + MSv / 8 + 8192)); try reflexivity.
- intros a Ha. destruct (dzone_apart a Ha) as (Ra & N1 & N2 & _). apply OUT3; rewrite unsigned_lit_small by exact Ra; assumption.
- exact MW2.
- assert (E2 : eager_used mdN = eager_used md0) by (unfold mdN; apply eager_used_wvb). assert (0 <= MSv / 8) by (apply Z.div_pos; lia). lia.
- rewrite A3. cbn [A_bytes fst snd]. assert (0 <= MSv / 8) by (apply Z.div_pos; lia). lia.
- assert (0 <= MSv / 8) by (apply Z.div_pos; lia). lia.
- clear - MS0. unfold MALLOC_MAX in MS0. assert (MSv / 8 <= 2 ^ 26) by (apply Z.div_le_upper_bound; lia). lia. }
step HR (segG1 W3 md2 _ RST ccont HR). pose proof (proj1 HR) as EW. subst W0.
step HR (segNE W3 md2 (fun _ => True) RXs NE _ HR). pose proof (proj1 HR) as EW. subst W0.
step HR (segJ W3 md2 (fun _ => True) RXt WIN HXW _ HR). pose proof (proj1 HR) as EW. subst W0.
step HR (segT1 W3 md2 (fun _ => True) RXt WIN HXW _ HR). pose proof (proj1 HR) as EW. subst W0.
eapply SRr_bind; [exact (at_S_depot W3 md2 YD3j.as_const_g2f (fun _ => True) D1w RXd (HMAPD_of W3 md2 IN3) WIN HXQ HXW FPP3 _ HR)
| clear HR; intros W4 c4 LE34 (ly' & md4 & z & PE & LY' & IMG' & HR)].
destruct (post_put W3 W4 md2 md4 ly' z (fun _ => True) (fun a => WIN a \/ DX_at ly' a) c4 IN3 PE LY' IMG' HR) as (LG & DZ' & AOKz & HR' & GRW).
apply SRr_ret. exists z. split; [exact AOKz|].
assert (Hgrow : false = true <-> idx = res) by (split; [intros E; discriminate E | intros E; exfalso; exact (NE E)]).
assert (HXsub : forall a, (WIN a \/ DX_at ly' a) -> WIN a \/ (false = true /\ QR a) \/ DX_at ly' a) by (clear; intros a [Ha|Ha]; tauto).
assert (HRXQ : false = true -> forall m : word -> option byte, True -> ZQ W4 m) by (intros E; discriminate E).
assert (HXW' : forall a, WIN a -> WIN a \/ DX_at ly' a) by (clear; intros a H; left; exact H).
assert (HOUT : forall x : word, ~ (mb <= bv_unsigned x < mb + MSv) -> ~ (SHLO mb <= bv_unsigned x < SHHI mb) ->
~ (false = true /\ QSv <= bv_unsigned x < QSv + 131072) ->
~ (fst (nb_ext ly') <= bv_unsigned x < fst (nb_ext ly') + snd (nb_ext ly')) ->
~ (fst (sb_ext ly') <= bv_unsigned x < fst (sb_ext ly') + snd (sb_ext ly')) -> w_H W4 x = w_H W x).
{ intros x N1 N2 _ N4 N5. rewrite (put_frame W3 W4 md2 ly' md4 PE x N4 N5). exact (OUT3 x N1 N2). }
assert (HDPz : forall l W' md'' zz m, DPOST l W' md'' zz m -> exists Wc, DPOSTS Wc YD3j.as_const_g2f l W' md'' zz m)
by (intros l W' md'' zz m Hd; exact (proj1 (HDP l W' md'' zz m) Hd)).
apply (after_depot false W4 md4 ly' (fun _ => True) (fun a => WIN a \/ DX_at ly' a) z c4 _ Hgrow RXs RXt HRXQ HXW' HXsub
(wle_trans _ _ _ _ LE3 LE34) (YD3j.same_io_trans3 _ _ _ IO2 (put_io W3 W4 md2 ly' md4 PE))
(WZ_put false z W3 W4 md2 md4 ly' (fun mat' => WZ3 z mat' (LED0 z)) LE34 PE (GR_of false z W3 W4 md2 md4 ly' (LED0 z) MW2 PE GRW))
HOUT LG LY' IMG' DZ' HDPz (put_wA W3 W4 md2 ly' md4 PE (SHLO mb, SHHI mb) ltac:(rewrite A3; left; reflexivity)) HR');
unfold S1; cbn; reflexivity.
Qed.
Theorem grantS_eq : idx = res -> amreal tfibsegs (KSEC 1) W3 ccont QLEAF.
Proof.
intros EQ. pose proof Hidx as HI. pose proof Hres as [HRS HRA]. pose proof (QR_facts EQ) as (E1 & _ & QA & F9 & Q5 & F10 & EQR). pose proof MSB as MS0.
pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & Z9 & _). pose proof (SH_hull mb) as (H1 & H2 & H3 & _).
pose proof (grant_cont mb0 W3 md2 (fun _ => True) ms E' HE' HS MEQ PRS HB SUB3 VISM SHZ I) as HR.
unfold KSEC. change (1 =? 0) with false. cbn iota. unfold sec_body. rewrite !bind_assoc_eq.
eapply amreal_pure; [reflexivity|]. rewrite !bind_assoc_eq.
eapply amreal_pure; [unfold mcheck; replace (Z.of_nat (length (st_sec_arr S1)) <? kMaxNumChunks) with true by (symmetry; apply Z.ltb_lt; unfold S1; cbn; rewrite <- Hidx_def; exact (proj2 HI)); reflexivity|].
rewrite !bind_assoc_eq. eapply amreal_pure; [reflexivity|]. rewrite !bind_assoc_eq.
replace (Z.of_nat (length (st_sec_arr S1)) =? st_sec_reserved S1) with true by (symmetry; apply Z.eqb_eq; unfold S1; cbn; rewrite <- Hidx_def, <- Hres_def; exact EQ).
rewrite !bind_assoc_eq. unfold YG00.bind at 1. unfold askz. cbn [ibind].
replace (8 * Z.of_nat (length (st_sec_arr S1))) with (8 * idx) by (unfold S1; cbn; rewrite <- Hidx_def; reflexivity).
lazymatch goal with |- amreal _ (IAsk _ ?s ?Kc) _ _ _ => set (KV := Kc); set (sV := s) end.
apply amreal_askV; [exact I|].
assert (RXs : rstable (fun _ : word -> option byte => True)) by exact rstable_true.
step HR (segG1 W3 md2 _ RXs ccont HR). pose proof (proj1 HR) as EW. subst W0.
eapply SRr_mono; [exact (SRr_with_AI _ _ _ (segEQa W3 md2 (fun _ => True) RXs EQ _ HR))|].
clear HR. intros W4 c4 _ [HAI HN]. cbv beta. pose proof (proj1 HN) as EW. subst W4.
pose proof HN as HNc. destruct HNc as (_ & msV & matV & EV & EcV & _).
set (mdV := with_vm_backing (m_vm_lazy md2) matV md2) in *.
assert (EcM : cfg_model c4 = mdV) by (rewrite EcV; reflexivity).
assert (LV : forall z, ALedger tfibsegs lyF (SFS false z) mdV) by (intros z; exact (ALedger_same tfibsegs lyF (SFS false z) md2 mdV (LED0 z) (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) (eager_used_wvb _ _))).
assert (MWV : amwf mdV) by (exact (amwf_same md2 mdV (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) MW2)).
pose proof VM2 as (VMa & VMr & VMl & VMb).
apply (nodeV W3 md2 sV KV QLEAF (fun _ => True) c4 EQ HN HAI).
- clear; intros m m' _ _; exact I.
- rewrite EcM. exact MWV.
- rewrite EcM. exact (al_reserved _ _ _ _ (LV 0)).
- exact (al_img_env tfibsegs lyF (SFS false 0) _ lyF_ok (LV 0)).
- rewrite EcM. exact (al_Q _ _ _ _ (LV 0)).
-
rewrite EcM. apply (slackS mdV W3 (MSv + (MSv / 8 + 8192)) HAR Hev (proj1 (proj2 HAR))).
+ unfold mdV. rewrite m_vmmaps_wvb, VMl. unfold mdN. rewrite m_vmmaps_wvb. reflexivity.
+ unfold mdV. rewrite eager_used_wvb. unfold mdN in EG2. rewrite eager_used_wvb in EG2. clear - EG2 Z8. zlia.
+ rewrite A3. cbn [A_bytes fst snd]. clear - H3 Z8. zlia.
+ clear - Z8 Z9. unfold MALLOC_MAX in Z8. split; [zlia|]. assert (MSv / 8 <= 2 ^ 26) by (apply Z.div_le_upper_bound; zlia). zlia.
+
clear - Z8 Z9. unfold MALLOC_MAX in Z8. assert (MSv / 8 <= 2 ^ 26) by (apply Z.div_le_upper_bound; zlia). zlia.
-   rewrite EcM. exact (al_top _ _ _ _ (LV 0)).
- intros z Hz. exact Hz.
-
intros W5 c5. rewrite EcM. intros md5 LE5 SUB5 MON5 A5 VIS5 OUT5 AI5 MW5 IO5 EG5 VM5 HR5.
subst KV sV. cbv beta. change (aGranted 1) with true. cbn iota.
rewrite ?bind_assoc_eq. eapply amreal_pure; [reflexivity|]. rewrite ?bind_assoc_eq. eapply amreal_pure; [reflexivity|]. eapply amreal_pure; [reflexivity|].
rewrite malloc_K_some.
assert (RS5 : rstable (RZ W5 (fun _ => True))) by (exact (rstable_and _ _ RXs (ZQ_rstable W5))).
assert (RT5 : pstable WIN1T (RZ W5 (fun _ => True))) by (apply pstable_and; [clear; intros m m' _ _; exact I | exact (ZQ_stableT W5)]).
assert (RD5 : forall l, layout_ok l -> img_cover l -> layout_grow ly l -> pstable (DX_at l) (RZ W5 (fun _ => True)))
by (intros l LYl IMGl GRl; exact (RZ_stable_at W5 l LYl IMGl GRl)).
assert (HXW5 : forall a, WIN a -> WIN a \/ QR a) by (clear; intros a H; left; exact H).
assert (HXQ5 : forall a, (WIN a \/ QR a) -> WIN a \/ QR a) by (clear; intros a H; exact H).
assert (MON35 : forall x : word, w_H W x = false -> w_H W5 x = false) by (intros x Hx; exact (MON5 x (MON3 x Hx))).
pose proof (D1W_ok W5 MON35 Htr HmapD YD3j.as_const_g2f YD3j.as_const_g2f_def (HDPOST'_at W5) D1) as D1w.
assert (LE35 : wle W W5) by (exact (wle_trans _ _ _ _ LE3 LE5)).
assert (VMV : m_vmmaps mdV = m_vmmaps md2) by (unfold mdV; apply m_vmmaps_wvb).
assert (IN5 : In (w64 mb, w64 MSv) (vm_maps (m_vmmaps md5))) by (rewrite (proj1 VM5), VMV, VMa; left; reflexivity).
assert (FPP5 : st_depot S = [] -> YD3j.depot_first_put_pre depot_ok B W5 ly S mem0 md5 tr).
{ apply (FPP_site W5 md5 (MSv + MSv / 8 + 8192 + 131072)).
- intros a Ha. destruct (dzone_apart a Ha) as (Ra & N1 & N2 & N3).
rewrite (OUT5 (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by exact Ra; exact (N3 EQ)).
apply OUT3; rewrite unsigned_lit_small by exact Ra; assumption.
- rewrite (proj1 (proj2 (proj2 VM5))), VMV; reflexivity.
- rewrite (proj1 (proj2 VM5)), VMV; reflexivity.
- unfold md5. rewrite grant50_top, VMV; reflexivity.
- rewrite (proj1 VM5), VMV; reflexivity.
- exact MW5.
- assert (EV2 : eager_used mdV = eager_used md2) by (unfold mdV; apply eager_used_wvb).
assert (EN : eager_used mdN = eager_used md0) by (unfold mdN; apply eager_used_wvb). assert (0 <= MSv / 8) by (apply Z.div_pos; lia). lia.
- rewrite A5, A3. cbn [A_bytes fst snd]. assert (0 <= MSv / 8) by (apply Z.div_pos; lia). lia.
- assert (0 <= MSv / 8) by (apply Z.div_pos; lia). lia.
- clear - MS0. unfold MALLOC_MAX in MS0. assert (MSv / 8 <= 2 ^ 26) by (apply Z.div_le_upper_bound; lia). lia. }
pose proof HR5 as HR. clear HR5.
step HR (segV W5 md5 (fun _ => True) RXs EQ _ HR). pose proof (proj1 HR) as EW. subst W0.
step HR (segJ W5 md5 (RZ W5 (fun _ => True)) RT5 (fun a => WIN a \/ QR a) HXW5 _ HR). pose proof (proj1 HR) as EW. subst W0.
step HR (segT1 W5 md5 (RZ W5 (fun _ => True)) RT5 (fun a => WIN a \/ QR a) HXW5 _ HR). pose proof (proj1 HR) as EW. subst W0.
eapply SRr_bind; [exact (at_S_depot W5 md5 YD3j.as_const_g2f (RZ W5 (fun _ => True)) D1w RD5 (HMAPD_of W5 md5 IN5) (fun a => WIN a \/ QR a) HXQ5 HXW5 FPP5 _ HR)
| clear HR; intros W6 c6 LE56 (ly' & md6 & z & PE & LY' & IMG' & HR)].
destruct (post_put W5 W6 md5 md6 ly' z (RZ W5 (fun _ => True)) (fun a => (WIN a \/ QR a) \/ DX_at ly' a) c6 IN5 PE LY' IMG' HR) as (LG & DZ' & AOKz & HR' & GRW).
apply SRr_ret. exists z. split; [exact AOKz|].
assert (Hgrow : true = true <-> idx = res) by (split; [intros _; exact EQ | intros _; reflexivity]).
assert (HXsub : forall a, ((WIN a \/ QR a) \/ DX_at ly' a) -> WIN a \/ (true = true /\ QR a) \/ DX_at ly' a) by (clear; intros a [[Ha|Ha]|Ha]; tauto).
assert (HRXQ : true = true -> forall m : word -> option byte, RZ W5 (fun _ => True) m -> ZQ W6 m).
{ intros _ m [_ Hm] Heq a Ha Hs. destruct (Hm Heq a Ha Hs) as [Hh Hb]. split; [|exact Hb].
destruct (w_H W6 (Z_to_bv 64 a)) eqn:EH; [|reflexivity]. rewrite (LE56 _ EH) in Hh. discriminate Hh. }
assert (HXW' : forall a, WIN a -> (WIN a \/ QR a) \/ DX_at ly' a) by (clear; intros a H; left; left; exact H).
assert (HOUT : forall x : word, ~ (mb <= bv_unsigned x < mb + MSv) -> ~ (SHLO mb <= bv_unsigned x < SHHI mb) ->
~ (true = true /\ QSv <= bv_unsigned x < QSv + 131072) ->
~ (fst (nb_ext ly') <= bv_unsigned x < fst (nb_ext ly') + snd (nb_ext ly')) ->
~ (fst (sb_ext ly') <= bv_unsigned x < fst (sb_ext ly') + snd (sb_ext ly')) -> w_H W6 x = w_H W x).
{ intros x N1 N2 N3 N4 N5. rewrite (put_frame W5 W6 md5 ly' md6 PE x N4 N5). rewrite (OUT5 x (fun H => N3 (conj eq_refl H))). exact (OUT3 x N1 N2). }
assert (HDPz : forall l W' md'' zz m, DPOST l W' md'' zz m -> exists Wc, DPOSTS Wc YD3j.as_const_g2f l W' md'' zz m)
by (intros l W' md'' zz m Hd; exact (proj1 (HDP l W' md'' zz m) Hd)).
assert (L5 : ALedger tfibsegs lyF (SFS true z) md5)
by exact (LED1 z mdV md5 EQ (LV z) (proj1 VM5) (proj1 (proj2 VM5)) (proj1 (proj2 (proj2 VM5))) (proj2 (proj2 (proj2 VM5))) (grant50_isp _ _ _) (COV_Q mdV MWV EQ) EG5 (YG0g.naf_grant_md false (Z_to_bv 64 50) mdV _ _ MWV)).
assert (WZ5 : forall mat', wz_facts true z ly W5 (with_vm_backing (m_vm_lazy md5) mat' md5)).
{ intros mat'. constructor.
- exact MON35.
- intros x Hx. exact (MON5 x (VISM3 x Hx)).
- intros x Hx. exact (MON5 x (VISH3 x Hx)).
- intros _ x Hx. apply VIS5. apply EQR. exact Hx.
- rewrite A5, A3. cbn [A_bytes fst snd]. zlia.
- intros i Hi. rewrite A5, A3. cbn. right; right; right. exact Hi.
- rewrite A5, A3. cbn. right; right; left. reflexivity.
- rewrite A5, A3. cbn. right; left. reflexivity.
- exact (ALedger_same tfibsegs lyF (SFS true z) md5 _ L5 (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) (eager_used_wvb _ _)).
- exact (amwf_same md5 _ (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) MW5).
- exact GAP. }
apply (after_depot true W6 md6 ly' (RZ W5 (fun _ => True)) (fun a => (WIN a \/ QR a) \/ DX_at ly' a) z c6 _ Hgrow RS5 RT5 HRXQ HXW' HXsub
(wle_trans _ _ _ _ LE35 LE56) (YD3j.same_io_trans3 _ _ _ IO5 (put_io W5 W6 md5 ly' md6 PE))
(WZ_put true z W5 W6 md5 md6 ly' WZ5 LE56 PE (GR_of true z W5 W6 md5 md6 ly' L5 MW5 PE GRW))
HOUT LG LY' IMG' DZ' HDPz (put_wA W5 W6 md5 ly' md6 PE (SHLO mb, SHHI mb) ltac:(rewrite A5, A3; right; left; reflexivity)) HR');
unfold S1; cbn; try reflexivity.
- rewrite EcM. exact (same_io_wvb md2 matV IO2).
Qed.
End h.
End f.
End d.
