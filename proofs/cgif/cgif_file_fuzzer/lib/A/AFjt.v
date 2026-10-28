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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1w AE3d AB1q AFhy AFhz AFi0 AFi4 AFi9 AB1h AFjm.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK0v YK13 YP0n YA05 YA09 YG0b YG0h.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AFid AFie AFif.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YFen.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AFjv AFjw AFjx AFjh AFjn AFjo AFjk AFjl AFjp AFjs.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YA00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AFia.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0c.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
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
Section g.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (n : Z) (ch : list (Z * Z * Z)).
Variables (idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 : Z).
Variable mb : Z.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Let Qb : Z := ly_Q ly.
Local Abbreviation R8v := (@AFjm.R8v n).
Local Abbreviation N8D := (@AFjm.N8D n).
Local Abbreviation NDv := (@AFjm.NDv n).
Local Abbreviation MSv := (@AFjm.MSv n).
Local Abbreviation SHBv := (@AFjm.SHBv).
Local Abbreviation QSv := (@AFjm.QSv ly idx).
Local Abbreviation Kv := (@AFjm.Kv mb).
Local Abbreviation Uv := (@AFjm.Uv mb).
Local Abbreviation ENDv := (@AFjm.ENDv n mb).
Local Abbreviation TLv := (@AFjm.TLv n).
Local Abbreviation UEv := (@AFjm.UEv n mb).
Local Abbreviation RLv := (@AFjm.RLv n).
Local Abbreviation SMv := (@AFjm.SMv mb).
Local Abbreviation PBv := (@AFjm.PBv n mb).
Local Abbreviation LGv := (@AFjm.LGv n).
Local Abbreviation BSLv := (@AFjm.BSLv n).
Local Abbreviation tr := (@AFjm.tr ly regs0 ch).
Local Abbreviation XW := (@AFjm.XW ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation E0 := (@AFjm.E0 ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation Er := (@AFjm.Er ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation E1 := (@AFjm.E1 ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation E2 := (@AFjm.E2 ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation E4 := (@AFjm.E4 ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation E8 := (@AFjm.E8 ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation E10 := (@AFjm.E10 ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaT := (@AFjm.EaT ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaC := (@AFjm.EaC ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaSB := (@AFjm.EaSB ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaTOP := (@AFjm.EaTOP ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaR8 := (@AFjm.EaR8 ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaQ := (@AFjm.EaQ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaRES := (@AFjm.EaRES ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaNCH := (@AFjm.EaNCH ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaMS := (@AFjm.EaMS ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaMAP := (@AFjm.EaMAP ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaEND := (@AFjm.EaEND ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaSHB := (@AFjm.EaSHB ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaTL := (@AFjm.EaTL ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaQS := (@AFjm.EaQS ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaBSL := (@AFjm.EaBSL ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaSM := (@AFjm.EaSM ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaUE := (@AFjm.EaUE ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaND := (@AFjm.EaND ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaRL := (@AFjm.EaRL ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaN8D := (@AFjm.EaN8D ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaPB := (@AFjm.EaPB ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
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
Local Abbreviation mod0_of_mul := (@AFjm.mod0_of_mul).
Local Abbreviation size_facts := (@AFjm.size_facts n Nrange).
Local Abbreviation tr_length := (@AFjm.tr_length ly regs0 ch idx res Hidx).
Local Abbreviation high_facts := (@AFjm.high_facts _ ly regs0 idx res LY IMG Hidx Hres).
Local Abbreviation stack_ivs := (@AFjm.stack_ivs _ ly regs0 idx res LY Hsp Hidx Hres).
Local Abbreviation HCX := (@AFjm.HCX _ ly LY).
Hypothesis Hpres0 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem0 a.
Hypothesis Hmap : mb mod 4096 = 0 /\ mzone mb MSv.
Hypothesis Hmap_apart :
zdisjoint (mb, MSv) (T, kThreadObjSize) /\ zdisjoint (mb, MSv) (ly_C ly, kCtxMapSize) /\
zdisjoint (mb, MSv) (ly_prim ly, kPrimResvSize) /\ zdisjoint (mb, MSv) (Qb, kPtrArrayResv) /\
zdisjoint (mb, MSv) (ly_NB ly, kNodesBlockSize) /\ zdisjoint (mb, MSv) (ly_SB ly, kStoreBlockSize) /\
zdisjoint (mb, MSv) (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly).
Local Abbreviation map_facts := (@AFjm.map_facts _ ly regs0 n idx res mb Nrange Hidx Hres Hmap).
Local Abbreviation map_zone := (@AFjm.map_zone _ ly regs0 n idx res mb Nrange Hidx Hmap).
Local Abbreviation map_zoneN := (@AFjm.map_zoneN _ ly regs0 n idx res mb Nrange Hidx Hres Hmap).
Local Abbreviation map_in_band := (@AFjm.map_in_band _ ly regs0 n idx res mb Nrange Hidx Hmap).
Local Abbreviation map_off_img := (@AFjm.map_off_img _ n mb Hmap).
Local Abbreviation WINT := (@AFjm.WINT ly).
Local Abbreviation WINI := (@AFjm.WINI n).
Local Abbreviation WINM := (@AFjm.WINM ly n idx mb).
Local Abbreviation WIN := (@AFjm.WIN ly regs0 n idx mb).
Local Abbreviation WINN := (@AFjm.WINN ly regs0).
Local Abbreviation WINP := (@AFjm.WINP ly regs0 n).
Local Abbreviation WINP_WIN := (@AFjm.WINP_WIN ly regs0 n idx mb).
Local Abbreviation WIN1P := (@AFjm.WIN1P ly regs0 n).
Local Abbreviation WIN1 := (@AFjm.WIN1 ly regs0 n idx mb).
Local Abbreviation WIN1P_WINP := (@AFjm.WIN1P_WINP ly regs0 n idx res mb Hidx).
Local Abbreviation WIN1_WIN := (@AFjm.WIN1_WIN ly regs0 n idx res mb Hidx).
Local Abbreviation WIN1P_WIN1 := (@AFjm.WIN1P_WIN1 ly regs0 n idx mb).
Local Abbreviation LGv_range := (@AFjm.LGv_range n Nrange).
Local Abbreviation BSLv_range := (@AFjm.BSLv_range ly regs0 n idx res mb Nrange Hidx).
Local Abbreviation WSKELP := (@AFjm.WSKELP).
Local Abbreviation WSKEL1P := (@AFjm.WSKEL1P).
Local Abbreviation WMAP := (@AFjm.WMAP).
Local Abbreviation WSKEL := (@AFjm.WSKEL).
Local Abbreviation WSKEL1 := (@AFjm.WSKEL1).
Local Abbreviation win_sub := (@AFjm.win_sub).
Local Abbreviation win_sub_sound := (@AFjm.win_sub_sound ly regs0 idx res mb Hidx Hres).
Local Abbreviation in_win := (@AFjm.in_win).
Local Abbreviation WSKELP_WINP := (@AFjm.WSKELP_WINP _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Nrange Hidx Hres).
Local Abbreviation WSKEL1P_WIN1P := (@AFjm.WSKEL1P_WIN1P _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Nrange Hidx Hres).
Local Abbreviation WMAP_WINM := (@AFjm.WMAP_WINM _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Nrange Hidx Hres Hmap).
Local Abbreviation WSKEL_WIN := (@AFjm.WSKEL_WIN _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Nrange Hidx Hres Hmap).
Local Abbreviation WSKEL1_WIN1 := (@AFjm.WSKEL1_WIN1 _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Nrange Hidx Hres Hmap).
Local Abbreviation windows_in := (@AFjm.windows_in ly regs0 idx res mb Hidx Hres).
Local Abbreviation windows_WINP := (@AFjm.windows_WINP _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Nrange Hidx Hres).
Local Abbreviation windows_WIN1P := (@AFjm.windows_WIN1P _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Nrange Hidx Hres).
Local Abbreviation windows_WIN := (@AFjm.windows_WIN _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Nrange Hidx Hres Hmap).
Local Abbreviation windows_WIN1 := (@AFjm.windows_WIN1 _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Nrange Hidx Hres Hmap).
Local Abbreviation frame_WIN1P := (@AFjm.frame_WIN1P _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Nrange Hidx Hres).
Local Abbreviation frame_WIN1 := (@AFjm.frame_WIN1 _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Nrange Hidx Hres Hmap).
Local Abbreviation WINP_not_high := (@AFjm.WINP_not_high _ ly regs0 n idx res mb LY IMG Hsp Nrange Hidx Hres).
Local Abbreviation WIN_not_high := (@AFjm.WIN_not_high _ ly regs0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap).
Variables (mat0 : list word).
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 0x52930) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis U1 : tfib_unwind_spec.
Local Abbreviation all_disjoint_of_forall := (@AFjm.all_disjoint_of_forall).
Local Abbreviation img_rw_writable := (@AFjm.img_rw_writable ly regs0 idx res mb Hidx).
Local Abbreviation kept_of_frame := (@AFjm.kept_of_frame W ly regs0 idx res mb Hidx).
Local Abbreviation SKEL_TAIL := (@AFjm.SKEL_TAIL).
Local Abbreviation blocks_facts := (@AFjm.blocks_facts _ ly LY IMG).
Local Abbreviation off_T := (@AFjm.off_T _ ly regs0 idx res LY IMG Hidx Hres).
Local Abbreviation off_C := (@AFjm.off_C _ ly regs0 idx res LY IMG Hidx Hres).
Local Abbreviation off_Q := (@AFjm.off_Q _ ly regs0 idx res LY IMG Hidx Hres).
Local Abbreviation off_NB := (@AFjm.off_NB _ ly LY IMG).
Local Abbreviation off_SB := (@AFjm.off_SB _ ly LY IMG).
Local Abbreviation off_shadow := (@AFjm.off_shadow ly regs0 idx res mb Hidx).
Ltac off_by tac :=
first [ apply off_img_high; tac | apply off_T; tac | apply off_C; tac | apply off_Q; tac | apply off_NB; tac | apply off_SB; tac
| apply map_off_img; tac | apply off_shadow; tac
| unfold off_img; unfold TFIB_IMG_LO; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; tac ].
Local Abbreviation DZONE := (@AFjm.DZONE ly).
Variable DPOST : Z -> (word -> option byte) -> Prop.
Local Abbreviation DZONE_disj := (@AFjm.DZONE_disj _ ly regs0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation RFACTS := (@AFjm.RFACTS ly regs0).
Local Abbreviation zone_lit := (@AFjm.zone_lit _ ly regs0 LY IMG Hsp).
Local Abbreviation zone_irw := (@AFjm.zone_irw _ ly regs0 LY IMG Hsp).
Local Abbreviation zone_T := (@AFjm.zone_T _ ly regs0 idx res LY IMG Hsp Hidx Hres).
Local Abbreviation zone_C := (@AFjm.zone_C _ ly regs0 idx res LY IMG Hsp Hidx Hres).
Local Abbreviation tail_ext_ok := (@AFjm.tail_ext_ok _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres).
Local Abbreviation RFACTS_map := (@AFjm.RFACTS_map _ ly regs0 n idx res mb LY IMG Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation at_ST := (@AFjm.at_ST _ W ly regs0 mem0 md0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation memset_stretch := (@AFjm.memset_stretch _ _ W ly regs0 mem0 n idx res mb Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST).
Ltac clearM := try clear DPOST; try clear Hmap_apart; try clear Hmap.
Local Abbreviation at_S := (@AFjm.at_S _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation at_N := (@AFjm.at_N _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation at_RETS := (@AFjm.at_RETS _ regs0 mem0).
Local Abbreviation pstable := (@AFjm.pstable).
Local Abbreviation stack_shaped := (@AFjm.stack_shaped).
Local Abbreviation window_present := (@AFjm.window_present ly regs0 idx res Hidx).
Local Abbreviation stack_present_of := (@AFjm.stack_present_of _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY Hsp Hidx).
Local Abbreviation mid_not_WIN1P := (@AFjm.mid_not_WIN1P _ ly regs0 n idx res mb LY IMG Hsp Nrange Hidx Hres).
Local Abbreviation mid_not_WIN1 := (@AFjm.mid_not_WIN1 _ ly regs0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap).
Local Abbreviation wins_ok := (@AFjm.wins_ok).
Local Abbreviation at_S_run_gen := (@AFjm.at_S_run_gen _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY Hsp Hidx).
Local Abbreviation at_S_run_ecall_gen := (@AFjm.at_S_run_ecall_gen _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY Hsp Hidx).
Local Abbreviation at_S_runP := (@AFjm.at_S_runP _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres).
Local Abbreviation at_S_runM := (@AFjm.at_S_runM _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap).
Local Abbreviation at_S_run_ecallP := (@AFjm.at_S_run_ecallP _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres).
Local Abbreviation at_S_run_ecallM := (@AFjm.at_S_run_ecallM _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap).
Local Abbreviation at_S_pin := (@AFjm.at_S_pin _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation at_S_arm := (@AFjm.at_S_arm _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation at_S_forget := (@AFjm.at_S_forget _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation at_S_noconds := (@AFjm.at_S_noconds _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation at_S_weaken := (@AFjm.at_S_weaken _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation at_S_facts := (@AFjm.at_S_facts _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation at_S_strengthen := (@AFjm.at_S_strengthen _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation at_S_eq := (@AFjm.at_S_eq _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation at_S_open := (@AFjm.at_S_open _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation CSAVEDS := (@AFjm.CSAVEDS).
Local Abbreviation sv_denot_SOff0 := (@AFjm.sv_denot_SOff0).
Local Abbreviation at_S_ret := (@AFjm.at_S_ret _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Htp Hra Hsp Nrange Hidx Hres).
Local Abbreviation kept_of_frame2 := (@AFjm.kept_of_frame2 ly regs0 idx res Hidx).
Local Abbreviation at_N_cont := (@AFjm.at_N_cont _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY Hsp Hidx).
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
Hypothesis Hj6 : val_mem tfibsegs (mrestrict (w_H W) mem0) 0xa2c58 8 j6.
Hypothesis Hj7 : val_mem tfibsegs (mrestrict (w_H W) mem0) 0xa2c60 8 j7.
Hypothesis Hj8 : val_mem tfibsegs (mrestrict (w_H W) mem0) BSLv 8 j8.
Hypothesis Hi1 : val_mem tfibsegs (mrestrict (w_H W) mem0) (TFIB_INST + o_sec_stats) 8 i1.
Hypothesis Hi2 : val_mem tfibsegs (mrestrict (w_H W) mem0) (TFIB_INST + o_sec_stats + 16) 8 i2.
Hypothesis Hi3 : val_mem tfibsegs (mrestrict (w_H W) mem0) (TFIB_INST + o_sec_stats + 24) 8 i3.
Hypothesis HQT : qmeter S.
Local Abbreviation vis_present := (@AFjv.vis_present _ W ly regs0 mem0 idx res Hidx DPOST B S HARm).
Local Abbreviation in_thread_junk := (@AFjv.in_thread_junk ly B S).
Local Abbreviation in_sec_junk := (@AFjv.in_sec_junk ly B S).
Local Abbreviation in_as_junk := (@AFjv.in_as_junk ly B S).
Local Abbreviation junk_word := (@AFjv.junk_word _ W ly regs0 mem0 idx res LY IMG Hidx Hres DPOST B S HARm).
Local Abbreviation cell_sym := (@AFjv.cell_sym _ W ly mem0 B S TS HARm).
Local Abbreviation cell_lit := (@AFjv.cell_lit _ W ly mem0 B S TS HARm).
Local Abbreviation cell_state := (@AFjv.cell_state _ W ly mem0 B S HARm).
Local Abbreviation In_acells_sec := (@AFjv.In_acells_sec ly B S).
Local Abbreviation sec_vals := (@AFjv.sec_vals _ W ly mem0 idx res B S TS HARm Hidx_def Hres_def).
Local Abbreviation unwinding_val := (@AFjv.unwinding_val _ W ly mem0 B S HARm).
Local Abbreviation rw_writable := (@AFjv.rw_writable ly regs0 idx res Hidx DPOST S).
Local Abbreviation val_mem_mod8 := (@AFjv.val_mem_mod8 W ly regs0 mem0 idx res Hidx DPOST S).
Local Abbreviation chunk_lit := (@AFjv.chunk_lit W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation chunk_lit_at := (@AFjv.chunk_lit_at W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation chunk_atom := (@AFjv.chunk_atom W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Hidx DPOST S).
Local Abbreviation SREG0_ok := (@AFjw.SREG0_ok _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hpres0 DPOST B S TS HTSD HARm Hidx_def Hres_def Hj0 Hj1 Hj2 Hj3 Hj4 Hj5 Hj9 Hj6 Hj7 Hj8 Hi1 Hi2 Hi3).
Local Abbreviation PAIRS_ok := (@AFjx.PAIRS_ok _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres DPOST S).
Local Abbreviation FACTS_ok := (@AFjx.FACTS_ok _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hn Hsp Nrange Hidx Hres DPOST S).
Local Abbreviation SEED_ok := (@AFjx.SEED_ok _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hn Htp Hsp Nrange Hidx Hres Hpres0 DPOST B S TS HTSD HARm Hidx_def Hres_def Hj0 Hj1 Hj2 Hj3 Hj4 Hj5 Hj9 Hj6 Hj7 Hj8 Hi1 Hi2 Hi3).
Local Abbreviation PBUF := (@AFjh.PBUF W ly regs0 ch).
Local Abbreviation PBUF_stableP := (@AFjh.PBUF_stableP _ W ly regs0 n ch idx res mb LY IMG Hsp Nrange Hidx Hres).
Local Abbreviation PBUF_stableM := (@AFjh.PBUF_stableM _ W ly regs0 n ch idx res mb LY IMG Hsp Nrange Hidx Hres Hmap).
Local Abbreviation seg0 := (@AFjh.seg0 _ _ W ly regs0 mem0 md0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hn Htp Hra4096 Hsp Hch Nrange Hidx Hres Hpres0 mat0 U1 DPOST B S TS HTSD HARm Hidx_def Hres_def Hj0 Hj1 Hj2 Hj3 Hj4 Hj5 Hj9 Hj6 Hj7 Hj8 Hi1 Hi2 Hi3).
Local Abbreviation appregs := (@AFjn.appregs).
Local Abbreviation st_ok_appregs := (@AFjn.st_ok_appregs _).
Local Abbreviation at_S_app := (@AFjn.at_S_app _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation WIN1N := (@AFjn.WIN1N ly regs0 n).
Local Abbreviation WINPN := (@AFjn.WINPN ly regs0 n).
Local Abbreviation WSKEL1N := (@AFjn.WSKEL1N).
Local Abbreviation WIN1N_WINPN := (@AFjn.WIN1N_WINPN ly regs0 n idx res mb Hidx).
Local Abbreviation windows_WIN1N := (@AFjn.windows_WIN1N _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Nrange Hidx Hres).
Local Abbreviation mid_not_WIN1N := (@AFjn.mid_not_WIN1N _ ly regs0 n idx res mb LY IMG Hsp Nrange Hidx Hres).
Local Abbreviation at_S_runN := (@AFjn.at_S_runN _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres).
Local Abbreviation PBUF_stableN := (@AFjn.PBUF_stableN _ W ly regs0 n ch idx res mb LY IMG Hsp Nrange Hidx Hres).
Local Abbreviation at_S_val := (@AFjn.at_S_val _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation memset_stretchW := (@AFjn.memset_stretchW _ W ly regs0 mem0 n idx res Hsp Nrange Hidx Hres DPOST S).
Local Abbreviation at_S_memset := (@AFjn.at_S_memset _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Hsp Nrange Hidx Hres DPOST S).
Local Abbreviation WIN1T := (@AFjn.WIN1T ly regs0 n idx mb).
Local Abbreviation WIN1T_WIN := (@AFjn.WIN1T_WIN _ ly regs0 n idx res mb Nrange Hidx Hres Hmap).
Local Abbreviation windows_WIN1T := (@AFjn.windows_WIN1T _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Nrange Hidx Hres Hmap).
Local Abbreviation WIN1T_WIN1_aux := (@AFjn.WIN1T_WIN1_aux _ ly regs0 n idx res mb Nrange Hidx Hres Hmap).
Local Abbreviation mid_not_WIN1T := (@AFjn.mid_not_WIN1T _ ly regs0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap).
Local Abbreviation at_S_runT := (@AFjn.at_S_runT _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap).
Local Abbreviation at_S_run_ecallT := (@AFjn.at_S_run_ecallT _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap).
Local Abbreviation PBUFW := (@AFjn.PBUFW ly regs0 ch).
Local Abbreviation PBUFW_stableT := (@AFjn.PBUFW_stableT _ ly regs0 n ch idx res mb LY IMG Hsp Nrange Hidx Hres Hmap).
Local Abbreviation WIN1S := (@AFjo.WIN1S ly regs0 n idx mb).
Local Abbreviation WSKEL1S := (@AFjo.WSKEL1S).
Local Abbreviation WIN1S_WIN1T := (@AFjo.WIN1S_WIN1T ly regs0 n idx mb).
Local Abbreviation WIN1S_WIN := (@AFjo.WIN1S_WIN _ ly regs0 n idx res mb Nrange Hidx Hres Hmap).
Local Abbreviation windows_WIN1S := (@AFjo.windows_WIN1S _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Nrange Hidx Hres Hmap).
Local Abbreviation mid_not_WIN1S := (@AFjo.mid_not_WIN1S _ ly regs0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap).
Local Abbreviation at_S_runS := (@AFjo.at_S_runS _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap).
Local Abbreviation at_S_run_ecallS := (@AFjo.at_S_run_ecallS _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap).
Local Abbreviation brun := (@AFjo.brun).
Local Abbreviation run_ok := (@AFjo.run_ok n mb).
Local Abbreviation PS := (@AFjo.PS ly regs0 n ch mb).
Local Abbreviation runs_not_WIN1S := (@AFjo.runs_not_WIN1S _ ly regs0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation runs_not_stack := (@AFjo.runs_not_stack _ ly regs0 n idx res mb LY Hsp Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation PS_stable := (@AFjo.PS_stable _ ly regs0 n ch idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation cut1 := (@AFjo.cut1).
Local Abbreviation cut := (@AFjo.cut).
Local Abbreviation cut_sound := (@AFjo.cut_sound _ ly regs0 mem0 n idx res mb Nrange Hidx Hres Hmap DPOST S).
Local Abbreviation cut_ok := (@AFjo.cut_ok ly regs0 mem0 n idx res mb Hidx Hres DPOST S).
Local Abbreviation at_S_memsetS := (@AFjo.at_S_memsetS _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S).
Local Abbreviation skel_okb := (@AFjo.skel_okb).
Local Abbreviation skel_cases := (@AFjo.skel_cases idx res Hidx Hres S Hidx_def Hres_def).
Local Abbreviation skel_apart := (@AFjo.skel_apart _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation skel_u64 := (@AFjo.skel_u64 _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap DPOST S Hidx_def Hres_def).
Local Abbreviation memset_ext_of_skel := (@AFjo.memset_ext_of_skel _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation memset_u64_of_skel := (@AFjo.memset_u64_of_skel _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap DPOST S Hidx_def Hres_def).
Local Abbreviation WIN1R := (@AFjo.WIN1R ly regs0 n mb).
Local Abbreviation WSKEL1R := (@AFjo.WSKEL1R).
Local Abbreviation WIN1R_WIN1S := (@AFjo.WIN1R_WIN1S ly regs0 n idx mb).
Local Abbreviation WIN1R_WIN := (@AFjo.WIN1R_WIN _ ly regs0 n idx res mb Nrange Hidx Hres Hmap).
Local Abbreviation windows_WIN1R := (@AFjo.windows_WIN1R _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Nrange Hidx Hres Hmap).
Local Abbreviation mid_not_WIN1R := (@AFjo.mid_not_WIN1R _ ly regs0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap).
Local Abbreviation at_S_runR := (@AFjo.at_S_runR _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap).
Local Abbreviation at_S_run_ecallR := (@AFjo.at_S_run_ecallR _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap).
Local Abbreviation PSR := (@AFjo.PSR ly regs0 n ch mb).
Local Abbreviation rstable := (@AFjo.rstable ly regs0 n mb).
Local Abbreviation rstable_true := (@AFjo.rstable_true ly regs0 n mb).
Local Abbreviation PSR_stable := (@AFjo.PSR_stable _ ly regs0 n ch idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation QSP := (@AFjo.QSP ly idx).
Local Abbreviation QS_not_WIN1R := (@AFjo.QS_not_WIN1R _ ly regs0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation QSP_rstable := (@AFjo.QSP_rstable _ ly regs0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation at_S_memsetSR := (@AFjo.at_S_memsetSR _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S).
Local Abbreviation chunk_eqb := (@AFjo.chunk_eqb).
Local Abbreviation chunk_eqb_eq := (@AFjo.chunk_eqb_eq idx res Hidx Hres S Hidx_def Hres_def).
Local Abbreviation subregionb := (@AFjo.subregionb).
Local Abbreviation subregionb_sound := (@AFjo.subregionb_sound ly regs0 mem0 idx res Hidx Hres DPOST S Hidx_def Hres_def).
Local Abbreviation submemb := (@AFjo.submemb).
Local Abbreviation submemb_sound := (@AFjo.submemb_sound ly regs0 mem0 idx res Hidx Hres DPOST S Hidx_def Hres_def).
Local Abbreviation at_S_submem := (@AFjo.at_S_submem _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Hidx Hres DPOST S Hidx_def Hres_def).
Local Abbreviation at_S_addreg := (@AFjo.at_S_addreg _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation PSR_runs := (@AFjk.PSR_runs _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation place_WIN := (@AFjk.place_WIN ly regs0 n idx mb).
Local Abbreviation SH0 := (@AFjk.SH0 n mb).
Local Abbreviation SH1 := (@AFjk.SH1 n mb).
Local Abbreviation SH2 := (@AFjk.SH2 n mb).
Local Abbreviation SH_ok := (@AFjk.SH_ok _ ly regs0 n idx res mb Nrange Hidx Hres Hmap).
Local Abbreviation segG1 := (@AFjk.segG1 _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation RX_stableS := (@AFjl.RX_stableS ly regs0 n idx mb).
Local Abbreviation rstable_and := (@AFjl.rstable_and ly regs0 n mb).
Local Abbreviation pstable_and := (@AFjl.pstable_and).
Local Abbreviation PSR_stableS' := (@AFjl.PSR_stableS' _ ly regs0 n ch idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation pairwise_disjoint_map := (@AFjl.pairwise_disjoint_map).
Local Abbreviation at_S_setchunks := (@AFjl.at_S_setchunks _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation chunk_ok_CVal_eqv := (@AFjl.chunk_ok_CVal_eqv).
Local Abbreviation RES2T_ne := (@AFjl.RES2T_ne ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Hidx Hres).
Local Abbreviation RES2T_eq := (@AFjl.RES2T_eq ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Hidx Hres).
Local Abbreviation sv_denot_eq_of_U := (@AFjl.sv_denot_eq_of_U ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation skel_apart_QS := (@AFjl.skel_apart_QS _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation QSPX := (@AFjl.QSPX ly idx).
Local Abbreviation segNE := (@AFjl.segNE _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation segEQa := (@AFjl.segEQa _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation zev_SAlu := (@AFjl.zev_SAlu).
Local Abbreviation zev_SLit := (@AFjl.zev_SLit).
Local Abbreviation zev_SOff := (@AFjl.zev_SOff).
Local Abbreviation segJ2 := (@AFjl.segJ2 _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation segJ := (@AFjl.segJ _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation QR := (@AFjp.QR ly res).
Local Abbreviation segT1 := (@AFjp.segT1 _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hn Hsp Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation DX := (@AFjp.DX ly regs0).
Local Abbreviation PD := (@AFjp.PD ly mem0 DPOST).
Local Abbreviation PD_rstable := (@AFjp.PD_rstable _ ly regs0 mem0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST).
Local Abbreviation PD_stableT := (@AFjp.PD_stableT _ ly regs0 mem0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST).
Local Abbreviation PSR_stableS := (@AFjp.PSR_stableS _ ly regs0 n ch idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation PD_stableS := (@AFjp.PD_stableS _ ly regs0 mem0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST).
Local Abbreviation PDX := (@AFjp.PDX ly mem0 DPOST).
Local Abbreviation PDX_rstable := (@AFjp.PDX_rstable _ ly regs0 mem0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST).
Local Abbreviation PDX_stableT := (@AFjp.PDX_stableT _ ly regs0 mem0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST).
Local Abbreviation PDX_stableS := (@AFjp.PDX_stableS _ ly regs0 mem0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST).
Local Abbreviation dx_okb := (@AFjp.dx_okb).
Local Abbreviation skel_apart_DX := (@AFjp.skel_apart_DX _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation skel_apart_stk := (@AFjp.skel_apart_stk _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart S Hidx_def Hres_def).
Local Abbreviation at_S_depot := (@AFjp.at_S_depot _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation SH3 := (@AFjp.SH3 n mb).
Local Abbreviation SH4 := (@AFjp.SH4 n mb).
Local Abbreviation shadow_marks := (@AFjp.shadow_marks _ ly regs0 n idx res mb Nrange Hidx Hres Hmap).
Local Abbreviation SH34_ok := (@AFjp.SH34_ok _ ly regs0 n idx res mb Nrange Hidx Hres Hmap).
Local Abbreviation segT2b := (@AFjp.segT2b _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hn Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation segT2 := (@AFjp.segT2 _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hn Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation SHLO := (@AFjs.SHLO).
Local Abbreviation SHHI := (@AFjs.SHHI n).
Local Abbreviation SH_hull := (@AFjs.SH_hull ly regs0 n res Nrange S).
Local Abbreviation lit_m1 := (@AFjs.lit_m1).
Local Abbreviation lit_enomem := (@AFjs.lit_enomem).
Local Abbreviation nores34 := (@AFjs.nores34).
Local Abbreviation core34 := (@AFjs.core34).
Local Abbreviation pru_MS := (@AFjs.pru_MS ly regs0 n res Nrange S).
Local Abbreviation grant_anon_shape := (@AFjs.grant_anon_shape).
Local Abbreviation Hcut_out := (@AFjs.Hcut_out).
Local Abbreviation slackS := (@AFjs.slackS _ W ly mem0 md0 B S HARm HQT).
Local Abbreviation S_N_facts := (@AFjs.S_N_facts).
Local Abbreviation S_N_ext64 := (@AFjs.S_N_ext64 _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres S).
Local Abbreviation S_N_win64 := (@AFjs.S_N_win64 _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres S).
Local Abbreviation nodeS := (@AFjs.nodeS _ _ W ly regs0 mem0 md0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres B S HARm HQT).
Local Ltac addr_tac :=
cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi];
rewrite ?EaT, ?EaC, ?EaTOP, ?EaSB, ?EaQ, ?EaMAP, ?EaQS, ?EaBSL, ?EaSM, ?EaPB, ?E2; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, w64, ly_bot, kStackSpan, t_unwinding, t_cache, t_stats, TFIB_IMG_END, UNW_STK, BST_SIZE, ASTACK, IFRAME, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *;
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
unfold AFjm.SHBv, AFjm.Kv, AFjm.Uv, AFjm.SMv, AFjm.PBv, MALLOC_MAX,
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
RUN HR tbl tblok 0x53a10 Sl HX HP;
s_armR HR BC_GEU true (14%bv : bv 5) (11%bv : bv 5); [ladder_arith ZLO|];
RUN HR tbl tblok STOP Slo HX HP;
s_join HR k clob SJ
| s_armR HR BC_GEU false (14%bv : bv 5) (10%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok 0x53868 Sh HX HP;
s_armR HR BC_LTU true (7%bv : bv 5) (10%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok 0x53a10 Sh2 HX HP;
s_armR HR BC_GEU false (14%bv : bv 5) (11%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok 0x53a50 Sh3 HX HP;
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
RUN HR tbl tblok 0x53a10 Sl HX HP;
s_armR HR BC_GEU true (14%bv : bv 5) (11%bv : bv 5); [ladder_arith ZLO|];
RUN HR tbl tblok STOP Slo HX HP;
s_join HR k clob SJ
| s_armR HR BC_GEU false (14%bv : bv 5) (10%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok 0x53868 Sh HX HP;
s_armR HR BC_LTU true (7%bv : bv 5) (10%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok 0x53a10 Sh2 HX HP;
s_armR HR BC_GEU false (14%bv : bv 5) (11%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok 0x53a4c Sh3a HX HP;
s_armR HR BC_LTU false (6%bv : bv 5) (11%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok 0x53a50 Sh3 HX HP;
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
RUN HR tbl tblok 0x31a40 Sh HX HP;
s_armR HR BC_LTU false (17%bv : bv 5) (22%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok 0x31a44 Sh2 HX HP;
s_armR HR BC_GEU false (16%bv : bv 5) (22%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok STOP Shi HX HP;
s_join HR k clob SJ ]
| clear HR; eapply SRr_bind; [exact HQ | clear HQ; let W2 := fresh "WL" in let c2 := fresh "cL" in intros W2 c2 _ HR ] ]
end.
Variables (Wy : world tfibsegs) (md1 : Model).
Definition S_VG : sstate := Eval vm_compute in mkSS 0x64170 (ss_regs S_V) (ss_mem S_V) None (ss_facts S_V).
Definition TQ : sv := SAlu ALU_ADD (SAlu ALU_AND (SAlu ALU_ADD (SOff aQ 0) (SAlu ALU_SLL (SOff aNCH 0) (SLit 3))) (SLit 18446744073709547520)) (SLit 0).
Lemma S_V_facts : ss_pc S_V = 0x6416c /\ sr_get (ss_regs S_V) 17%bv = SLit 222 /\ sr_get (ss_regs S_V) 10%bv = TQ /\ sr_get (ss_regs S_V) 11%bv = SLit 131072 /\
sr_get (ss_regs S_V) 12%bv = SLit 3 /\ sr_get (ss_regs S_V) 13%bv = SLit 50 /\ sr_get (ss_regs S_V) 14%bv = SLit 18446744073709551615 /\ sr_get (ss_regs S_V) 15%bv = SLit 0 /\
no_cdata (ss_mem S_V) = true /\ resume S_V TQ (ss_mem S_V) (ss_facts S_V) = S_VG /\ sv_atoms_lt sHAV TQ = true.
Proof. clear. vm_compute. repeat split; reflexivity. Qed.
Definition ZQF (Wz : world tfibsegs) (m : word -> option byte) : Prop :=
forall a, QR a -> w_H Wz (Z_to_bv 64 a) = false /\ m (Z_to_bv 64 a) = Some (Z_to_bv 8 0).
Definition ZQ (Wz : world tfibsegs) (m : word -> option byte) : Prop :=
idx = res -> forall a, QR a -> ~ (QSv <= a < QSv + 8) -> w_H Wz (Z_to_bv 64 a) = false /\ m (Z_to_bv 64 a) = Some (Z_to_bv 8 0).
Lemma QR_facts : idx = res -> QSv = Qb + 8 * res /\ QSv mod 131072 = Qb mod 131072 /\ QSv mod 4096 = 0 /\ (4096 <= Qb <= QSv /\ zone3cases Qb kPtrArrayResv) /\ QSv + 131072 <= Qb + kPtrArrayResv /\
Qb + kPtrArrayResv <= ASAN_CEIL /\ (forall a, QR a <-> QSv <= a < QSv + 131072).
Proof.
intros Heq. pose proof high_facts as (_ & _ & _ & _ & _ & _ & _ & _ & F9 & F10 & F11 & _). pose proof Hidx as HI. pose proof Hres as [HRS HRM].
unfold kMaxNumChunks, kPtrArrayEntriesPerCommit in *. unfold page_aligned in F11. unfold zone3 in F9.
assert (E1 : QSv = Qb + 8 * res) by (unfold QSv; try unfold Qb; rewrite Heq; reflexivity).
apply Z.mod_divide in HRM as [q Hq]; [|zlia]. apply Z.mod_divide in F11 as [p Hp]; [|zlia].
split; [exact E1|]. split. { rewrite E1, Hq. replace (Qb + 8 * (q * 16384)) with (Qb + q * 131072) by zlia. rewrite Z.add_mod, Z_mod_mult, Z.add_0_r, Z.mod_mod by zlia. reflexivity. }
split. { rewrite E1, Hq. try unfold Qb in *. rewrite Hp. replace (p * 4096 + 8 * (q * 16384)) with ((p + q * 32) * 4096) by zlia. apply Z_mod_mult. }
split; [split; [rewrite E1; zlia | exact (proj2 (proj2 F9))]|]. split; [rewrite E1; unfold kPtrArrayResv; zlia|]. split; [exact F10|].
intros a. unfold QR. rewrite E1. unfold kPtrArrayEntriesPerCommit, kPtrArrayResv. zlia.
Qed.
Lemma ZQ_of_ZQF : forall Wz m, ZQF Wz m -> ZQ Wz m.
Proof. clearP. intros Wz m H _ a Ha _. exact (H a Ha). Qed.
Lemma QR_not_WIN1T : idx = res -> forall a, QR a -> ~ (QSv <= a < QSv + 8) -> ~ WIN1T a.
Proof.
intros Heq a Ha Hs Hw. pose proof (QR_facts Heq) as (E1 & _ & _ & F9 & Q5 & F10 & EQ). apply EQ in Ha.
pose proof high_facts as (F1 & F2 & _ & _ & _ & _ & F7 & F8 & _ & _ & _ & _ & _ & _ & F15).
pose proof map_facts as (M1 & M2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _ & PB & _). pose proof map_zoneN as MZ. pose proof size_facts as (_ & _ & _ & Z4 & _ & _ & _ & Z8 & _).
pose proof BSLv_range as HB. destruct Hsp as (S1 & _ & S3 & _). pose proof (lo_stk_ceil ly LY) as SC.
destruct Hmap_apart as (_ & _ & _ & MQ & _). pose proof HCX as (_ & _ & QT & CQ). unfold zdisjoint in MQ, QT, CQ. cbn [fst snd] in MQ, QT, CQ.
pose proof Nrange as NR. pose proof shadow_marks as (_ & A2 & A3 & _ & _ & A6 & _). pose proof size_facts as (_ & _ & Z3 & Z4' & _).
assert (D1 : N8D / 8 <= R8v / 8) by (apply Z.div_le_mono; clear - Z3 Z4' MZ; zlia).
pose proof Hidx as HI. pose proof Hres as [HRS _]. unfold kMaxNumChunks in HI, HRS.
unfold WIN1T in Hw. clear EQ. destruct Hw as [Hw|[Hw|[Hw|Hw]]].
- unfold WIN1P, WINT, WINI in Hw. clear - Ha Hw Q5 F9 F10 SC S1 QT HB E1 Heq HI HRS MZ.
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kPtrArrayResv, kThreadObjSize, ASTACK, IFRAME, t_unwinding, TFIB_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex in *.
try unfold T in *. try unfold Qb in *. try unfold sp0 in *. zlia.
- exact (Hs Hw).
- clear - Ha Hw MQ Z8 Q5 E1 Heq HI HRS MZ. unfold kPtrArrayResv, MALLOC_MAX in *. try unfold Qb in *. zlia.
- clear - Ha Hw PB A2 A3 A6 SM2 D1 F9 Q5 E1 Heq HI HRS MZ Z4. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighShadowEnd, kPtrArrayResv in *. try unfold Qb in *. zlia.
Qed.
Lemma ZQ_stableT : forall Wz, pstable WIN1T (ZQ Wz).
Proof.
intros Wz m m' FR H Heq a Ha Hs. destruct (H Heq a Ha Hs) as [H1 H2]. split; [exact H1|]. rewrite FR; [exact H2|].
pose proof (QR_facts Heq) as (_ & _ & _ & F9 & Q5 & F10 & EQ). pose proof (proj1 (EQ a) Ha) as Ra.
rewrite unsigned_lit_small by (clear - Ra F9 F10 Q5; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kPtrArrayResv in *; try unfold Qb in *; zlia). exact (QR_not_WIN1T Heq a Ha Hs).
Qed.
Lemma ZQ_rstable : forall Wz, rstable (ZQ Wz).
Proof.
intros Wz. split.
- intros m m' FR. apply (ZQ_stableT Wz m m'). intros x Hx. apply FR. intros Hw. exact (Hx (WIN1S_WIN1T _ (WIN1R_WIN1S _ Hw))).
- intros m m' d len Hp FR H Heq a Ha Hs. destruct (H Heq a Ha Hs) as [H1 H2]. split; [exact H1|]. rewrite FR; [exact H2|].
pose proof (QR_facts Heq) as (_ & _ & _ & F9 & Q5 & F10 & EQ). pose proof (proj1 (EQ a) Ha) as Ra.
pose proof map_facts as (M1 & M2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _). pose proof map_zoneN as MZ. destruct Hmap_apart as (_ & _ & _ & MQ & _). unfold zdisjoint in MQ. cbn [fst snd] in MQ.
rewrite unsigned_lit_small by (clear - Ra F9 F10 Q5 MZ; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kPtrArrayResv in *; try unfold Qb in *; zlia).
clear - Hp Ra MQ F9 F10 Q5 M1 M2 SM1 SM2 MZ. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kPtrArrayResv, kHighShadowBeg, kHighShadowEnd in *. try unfold Qb in *. zlia.
Qed.
Lemma ZQ_stableD : forall Wz, pstable DX (ZQ Wz).
Proof.
intros Wz m m' FR H Heq a Ha Hs. destruct (H Heq a Ha Hs) as [H1 H2]. split; [exact H1|]. rewrite FR; [exact H2|].
pose proof (QR_facts Heq) as (_ & _ & _ & F9 & Q5 & F10 & EQ). pose proof (proj1 (EQ a) Ha) as Ra.
rewrite unsigned_lit_small by (clear - Ra F9 F10 Q5; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kPtrArrayResv in *; try unfold Qb in *; zlia).
pose proof blocks_facts as (NBhi & SBhi & _ & _ & QNB & QSB & _). unfold zdisjoint in QNB, QSB. cbn [fst snd] in QNB, QSB.
destruct Hsp as (S1 & _ & S3 & _). pose proof (lo_stk_ceil ly LY) as SC.
intros [Hd|Hd]; revert Hd; clear - Ra F9 F10 Q5 QNB QSB S1 S3 SC; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, DZONE, DEP_STK, ASTACK, kHighMemBeg, ASAN_CEIL, kPtrArrayResv, kNodesBlockSize, kStoreBlockSize in *; try unfold Qb in *; try unfold sp0 in *; zlia.
Qed.
Lemma skel_apart_Q : forall (E' : env) r, env_agree sHAV E0 E' -> skel_okb false (skel r) = true -> YP09.r_base r <> Some aQS ->
base_val E' (YP09.r_base r) + YP09.r_hi r <= Qb \/ Qb + kPtrArrayResv <= base_val E' (YP09.r_base r) + YP09.r_lo r \/ YP09.r_hi r <= YP09.r_lo r.
Proof.
intros E' r [HE _] Hs Hnq. destruct r as [b lo hi wlo whi cs]. unfold skel in Hs. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi] in *.
pose proof high_facts as (F1 & F2 & _ & _ & _ & _ & F7 & F8 & F9 & F10 & _ & _ & _ & _ & F15).
pose proof map_facts as (M1 & M2 & _). pose proof map_zoneN as MZ. pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & _). pose proof BSLv_range as HB.
destruct Hsp as (S1 & _ & S3 & _). pose proof (lo_stk_ceil ly LY) as SC.
destruct Hmap_apart as (_ & _ & _ & MQ & _). pose proof HCX as (_ & _ & QT & CQ). unfold zdisjoint in MQ, QT, CQ. cbn [fst snd] in MQ, QT, CQ.
pose proof (u64_range (getr regs0 2)) as U2.
destruct (skel_cases false b lo hi wlo whi Hs) as [(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|(Epb & -> & A1 & A2)]]]]]]]; cbn [base_val].
- clear - A1 A2 F9 MZ. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg in *. try unfold Qb in *. zlia.
- rewrite (HE 2%nat ltac:(unfold sHAV; zlia)), E2. clear - A1 A2 S1 SC F10 U2 MZ. ceil; unfold ASTACK, ASAN_CEIL in *. try unfold Qb in *. try unfold sp0 in *. zlia.
- rewrite (HE 32%nat ltac:(unfold sHAV; zlia)), EaT. unfold w64. rewrite unsigned_lit_small by (clear - F1 F2 MZ; numconst; try unfold T in *; zlia).
clear - A1 A2 QT MZ. unfold kThreadObjSize in *. try unfold T in *. try unfold Qb in *. zlia.
- rewrite (HE 33%nat ltac:(unfold sHAV; zlia)), EaC. unfold w64. rewrite unsigned_lit_small by (clear - F7 F8 MZ; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; zlia).
clear - A1 A2 CQ MZ. try unfold Qb in *. zlia.
- unfold aMAP. rewrite (HE 45%nat ltac:(unfold sHAV; zlia)), EaMAP. unfold w64. rewrite unsigned_lit_small by (clear - M1 M2 Z8 MZ; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; zlia).
clear - A1 A2 MQ Z8 MZ. unfold MALLOC_MAX in *. try unfold Qb in *. zlia.
- exfalso. apply Hnq. reflexivity.
- unfold aBSL. rewrite (HE 55%nat ltac:(unfold sHAV; zlia)), EaBSL. unfold w64. rewrite unsigned_lit_small by (clear - HB MZ; unfold TFIB_INST in *; zlia).
clear - A1 A2 HB F9 MZ. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, TFIB_INST in *. try unfold Qb in *. zlia.
- discriminate Epb.
Qed.
Lemma TQ_val : idx = res -> U E0 TQ = QSv.
Proof.
intros Heq. pose proof (QR_facts Heq) as (E1 & _ & QA & F9 & Q5 & F10 & _). pose proof Hidx as HI. pose proof Hres as [HRS _].
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kMaxNumChunks, kHighMemBeg, ASAN_CEIL, kPtrArrayResv in *.
assert (HQb : 0 <= Qb /\ Qb + 8388608 <= 140737479966720) by (clear - F9 F10; zlia).
clear - Heq E1 QA Q5 HI HRS HQb.
unfold TQ. rewrite U_zev by reflexivity. cbn [zev zalu_raw zmd_raw]. unfold rho_of. unfold_atoms. rewrite EaQ, EaNCH. unfold w64.
try unfold Qb in *. rewrite !unsigned_lit_small by (clear - HI HQb; zlia).
rewrite !Z.add_0_r. rewrite (zcanon_id idx) by (unfold M64; clear - HI; zlia). change (Z.land (zcanon 3) 63) with 3. rewrite Z.shiftl_mul_pow2 by (clear; zlia). change (2 ^ 3) with 8.
rewrite (zcanon_id (idx * 8)) by (unfold M64; clear - HI; zlia). rewrite (zcanon_id (ly_Q ly)) by (unfold M64; clear - HQb; zlia).
rewrite (zcanon_id (ly_Q ly + idx * 8)) by (unfold M64; clear - HI HQb; zlia). change (zcanon 18446744073709547520) with (2 ^ 64 - 2 ^ 12).
rewrite land_neg_pow2_u64 by (clear - HI HQb; zlia). change (2 ^ 12) with 4096.
assert (MZ : (ly_Q ly + idx * 8) mod 4096 = 0) by (rewrite Heq, (Z.mul_comm res 8), <- E1; exact QA).
rewrite MZ, Z.sub_0_r. rewrite (zcanon_id (ly_Q ly + idx * 8)) by (unfold M64; clear - HI HQb; zlia). rewrite zcanon_id by (unfold M64; clear - HI HQb; zlia). rewrite E1, Heq. zlia.
Qed.
Lemma nores50 : mmap_noreserve_b (Z_to_bv 64 50) = false. Proof. clear. reflexivity. Qed.
Lemma core50 : mmap_flags_core (Z_to_bv 64 50) = 50. Proof. clear. reflexivity. Qed.
Lemma pru17 : page_round_up_Z 131072 = 131072. Proof. clear. reflexivity. Qed.
Lemma grant_piece_shape : forall (a k : word) md, let md' := grant_md false (Z_to_bv 64 50) a k md in
vm_maps (m_vmmaps md') = vm_maps (m_vmmaps md) /\ vm_reserved (m_vmmaps md') = vm_reserved (m_vmmaps md) /\
vm_limit (m_vmmaps md') = vm_limit (m_vmmaps md) /\ vm_mmap_base (m_vmmaps md') = vm_mmap_base (m_vmmaps md).
Proof.
clear. intros a k md. cbv zeta. unfold grant_md, fixedin_ok_model, fixedin_ok_vmmaps, with_mmap_replacement, with_mmap_backing. rewrite nores50. cbn.
destruct md as [fd [maps lazy mat] io fs pr lim tm sg sc]. cbn. destruct maps; cbn. repeat split; reflexivity.
Qed.
Lemma nodeV : forall {RT : Type} (sN : astate) (K : Z -> itree astate RT) (Q : RT -> world tfibsegs -> config -> Prop)
(R : (word -> option byte) -> Prop) (c1 : config),
idx = res ->
at_N Wy md1 WIN (PSR Wy SH2 R) S_V Wy c1 -> AI tfibsegs (w_H Wy) (w_A Wy) (cfg_model c1) ->
(forall m m' : word -> option byte, (forall x : word, ~ QR (bv_unsigned x) -> m' x = m x) -> R m -> R m') ->
amwf (cfg_model c1) ->
vm_reserved (m_vmmaps (cfg_model c1)) = segments_reserved tfibsegs ->
(forall sg, In sg tfibsegs -> 4096 <= Z.of_N (seg_base sg) /\ Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <= kImgEnd) ->
In (wiv (Qb, kPtrArrayResv)) (vm_maps (m_vmmaps (cfg_model c1))) ->
eager_used (cfg_model c1) + A_bytes (w_A Wy) + 2 ^ 19 <= vm_limit (m_vmmaps (cfg_model c1)) ->
YM05.ceil_of_top (alloc_top (m_vmmaps (cfg_model c1))) ->
(forall z, z = 0 \/ z = 1 -> aok sN (KMapPtrArray (8 * idx) kPtrArrayCommit) z) ->
(forall (W5 : world tfibsegs) (c' : config), let md5 := grant_md false (Z_to_bv 64 50) (w64 QSv) (w64 131072) (cfg_model c1) in
wle Wy W5 -> hsub (w_H W5) (w_H Wy) -> (forall x : word, w_H Wy x = false -> w_H W5 x = false) ->
w_A W5 = (QSv, QSv + 131072) :: w_A Wy ->
(forall x : word, QSv <= bv_unsigned x < QSv + 131072 -> w_H W5 x = false) ->
(forall x : word, ~ (QSv <= bv_unsigned x < QSv + 131072) -> w_H W5 x = w_H Wy x) ->
AI tfibsegs (w_H W5) (w_A W5) md5 -> amwf md5 -> same_io md0 md5 -> eager_used md5 <= eager_used (cfg_model c1) + 131072 ->
vm_maps (m_vmmaps md5) = vm_maps (m_vmmaps (cfg_model c1)) /\ vm_reserved (m_vmmaps md5) = vm_reserved (m_vmmaps (cfg_model c1)) /\
vm_limit (m_vmmaps md5) = vm_limit (m_vmmaps (cfg_model c1)) /\ vm_mmap_base (m_vmmaps md5) = vm_mmap_base (m_vmmaps (cfg_model c1)) ->
at_S W5 md5 (fun a => WIN a \/ QR a) (PSR W5 SH2 (fun m => R m /\ ZQF W5 m)) S_VG W5 c' ->
amreal tfibsegs (K 1) W5 c' Q) ->
same_io md0 (cfg_model c1) ->
exists (I : Type) (nx : I -> config) (bit : I -> Z) (sp : I -> bool) (i0 : I),
node_ok tfibsegs c1 I (fun _ => []) nx /\
(forall i, AI tfibsegs (w_H Wy) (w_A Wy) (cfg_model c1) -> AI tfibsegs (w_H Wy) (w_A Wy) (cfg_model (nx i))) /\
(forall i, aok sN (KMapPtrArray (8 * idx) kPtrArrayCommit) (bit i)) /\ sp i0 = false /\ bit i0 = 1 /\
(forall i, sp i = false -> bit i = 1) /\
(forall i, sp i = true -> AI tfibsegs (w_H Wy) (w_A Wy) (cfg_model (nx i)) -> srealizes tfibsegs (nx i) t_nil) /\
(forall i, sp i = false -> amreal tfibsegs (K (bit i)) Wy (nx i) Q).
Proof.
intros RT sN K Q R c1 Heq HN HAI RQ MW RSV IMGS INQ SL0 HTOP Haok GRANT IO0.
pose proof (QR_facts Heq) as (E1 & _ & QA & F9 & Q5 & F10 & EQR).
destruct HN as (_ & ms & mat & E' & Ec & HE & HS & Hrv & MEQ & PRS & HPm).
set (mdN := with_vm_backing (m_vm_lazy md1) mat md1) in *.
assert (EcM : cfg_model c1 = mdN) by (rewrite Ec; reflexivity). rewrite EcM in *.
assert (MWF0 : MWF mdN) by (apply (proj1 (amwf_MWF mdN)); exact (proj1 MW)).
destruct (st_ok_ecall_shape_r tfibsegs (w_H Wy) E' S_V ms HS Hrv) as (regs & mem & Hms & Hregs & Hmem & HG).
assert (HEn : forall k, (k < sHAV)%nat -> ew E' k = ew E0 k) by (exact (proj1 HE)).
pose proof S_V_facts as (Hpc & H17 & H10 & H11 & H12 & H13 & H14 & H15 & Hnc & Hres_g & Hatq).
assert (UQS : bv_unsigned (w64 QSv) = QSv) by (unfold w64; apply unsigned_lit_small; clear - F9 F10 Q5 E1; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kPtrArrayResv in *; try unfold Qb in *; zlia).
assert (Un : bv_unsigned (w64 131072) = 131072) by (unfold w64; apply unsigned_lit_small; clear; zlia).
assert (R17 : getr regs 17 = Z_to_bv 64 222) by (rewrite (Hregs 17%bv), H17; reflexivity).
assert (R10 : getr regs 10 = w64 QSv).
{ rewrite (Hregs 10%bv), H10. unfold w64. rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E' TQ)). f_equal.
change (bv_unsigned (sv_denot E' TQ)) with (U E' TQ). rewrite (U_agree sHAV E0 E' TQ HE Hatq). exact (TQ_val Heq). }
assert (R11 : getr regs 11 = Z_to_bv 64 131072) by (rewrite (Hregs 11%bv), H11; reflexivity).
assert (R12 : getr regs 12 = Z_to_bv 64 3) by (rewrite (Hregs 12%bv), H12; reflexivity).
assert (R13 : getr regs 13 = Z_to_bv 64 50) by (rewrite (Hregs 13%bv), H13; reflexivity).
assert (R14 : getr regs 14 = Z_to_bv 64 (-1)) by (rewrite (Hregs 14%bv), H14; cbn [sv_denot]; apply lit_m1).
assert (R15 : getr regs 15 = Z_to_bv 64 0) by (rewrite (Hregs 15%bv), H15; reflexivity).
assert (CEIL : bv_unsigned (w64 QSv) + page_round_up_Z 131072 <= alloc_ceiling).
{ rewrite UQS, pru17. clear - Q5 F10. ceil; unfold ASAN_CEIL, kPtrArrayResv in *. zlia. }
assert (CEILT : bv_unsigned (w64 QSv) + page_round_up_Z 131072 <= alloc_top (m_vmmaps mdN)).
{ eapply Z.le_trans; [exact CEIL | apply YM05.ceil_le_top; exact HTOP]. }
assert (PLACE : region_free (vm_reserved (m_vmmaps mdN)) (w64 QSv) (Z_to_bv 64 (page_round_up_Z 131072)) = true /\
map_contains (vm_maps (m_vmmaps mdN)) (w64 QSv) (Z_to_bv 64 (page_round_up_Z 131072)) = true).
{ rewrite pru17. split.
- rewrite RSV. pose proof high_facts as (_ & _ & _ & _ & _ & _ & _ & _ & F9z & _).
apply (tfib_region_free_reserved QSv 131072); [clear; zlia | clear - F9 F10 Q5 E1; ceil; unfold ASAN_CEIL, kPtrArrayResv in *; try unfold Qb in *; zlia |].
clear - F9z F9 Q5 E1. unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, kPtrArrayResv in *. try unfold Qb in *. zlia.
- apply (YA09.map_contains_intro _ (w64 QSv) (w64 131072) (w64 Qb) (w64 kPtrArrayResv) INQ);
unfold w64; rewrite !unsigned_lit_small by (clear - F9 F10 Q5 E1; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kPtrArrayResv in *; try unfold Qb in *; zlia);
clear - Q5 E1 Heq F9; unfold kPtrArrayResv in *; try unfold Qb in *; zlia. }
assert (SL1 : eager_used mdN + A_bytes (w_A Wy) + page_round_up_Z 131072 <= vm_limit (m_vmmaps mdN)) by (rewrite pru17; clear - SL0; zlia).
assert (ALQ : bv_unsigned (w64 QSv) mod page_size = 0) by (rewrite UQS; unfold page_size; exact QA).
pose proof (commit_AI tfibsegs (w_H Wy) (w_A Wy) mdN false (Z_to_bv 64 50) (w64 QSv) 131072 HAI MWF0 nores50 ALQ ltac:(clear; zlia) CEILT PLACE SL1) as [CG BUD].
pose proof (commit_eager tfibsegs (w_H Wy) (w_A Wy) mdN false (Z_to_bv 64 50) (w64 QSv) 131072 HAI MWF0 nores50 ALQ ltac:(clear; zlia) CEILT PLACE SL1) as EG.
pose proof (commit_nonempty false (Z_to_bv 64 50) (w64 QSv) (Z_to_bv 64 (page_round_up_Z 131072)) mdN ltac:(rewrite pru17; unfold w64 in Un; rewrite Un; clear; zlia) (proj2 MW)) as NZg.
rewrite pru17 in CG, BUD, EG, NZg. fold (w64 131072) in CG, BUD, EG, NZg.
pose proof (destroyed_AI tfibsegs (w_H Wy) (w_A Wy) mdN (w64 QSv) 131072 HAI MWF0 ALQ ltac:(clear; zlia) CEILT) as [CD _].
rewrite pru17 in CD. fold (w64 131072) in CD.
destruct (commit_node3 tfibsegs false regs (Z_to_bv 64 0x6416c) mem (seg_rom tfibsegs) mdN (Z_to_bv 64 50) (w64 QSv) 131072
(AI_halted _ _ _ _ HAI) R17 R10 ALQ ltac:(rewrite UQS; clear - F9; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg in *; zlia)
R11 ltac:(clear; zlia) CEILT R12 R13 core50 R14 R15 PLACE BUD) as (I & nx & bit & i0 & NODE & Bi0 & OUT).
rewrite pru17 in OUT. fold (w64 131072) in OUT.
assert (IOtr : forall m2, YG0b.same_io mdN m2 -> same_io md0 m2).
{ intros m2 (X1 & X2 & X3 & X4). destruct IO0 as (Y1 & Y2 & Y3 & Y4). unfold same_io. rewrite X1, X2, X3, X4. repeat split; assumption. }
exists I, nx, (fun _ => 1), (fun _ => false), i0.
split. { rewrite Ec, Hms, Hpc. exact NODE. }
split. { intros i _. destruct (OUT i) as (md_i & _ & _ & _ & -> & ->); cbn [cfg_model]; exact (proj1 CG). }
split. { intros i. apply Haok. right; reflexivity. }
split; [reflexivity|]. split; [reflexivity|]. split; [intros i _; reflexivity|].
assert (APQ0 : forall r y, In r (ss_mem S_V) -> base_val E' (YP09.r_base r) + YP09.r_lo r <= y < base_val E' (YP09.r_base r) + YP09.r_hi r -> ~ QR y /\ 0 <= y < 2 ^ 64).
{ intros r y Hr Hy.
pose proof (proj1 (forallb_forall _ _) (eq_refl : forallb (fun r => skel_okb false (skel r) && negb (obase_eqb (YP09.r_base r) (Some aQS))) (ss_mem S_V) = true) r Hr) as CK.
cbn beta in CK. apply andb_prop in CK as [CK1 CK2].
assert (NB : YP09.r_base r <> Some aQS) by (intros Eq; rewrite Eq in CK2; discriminate CK2).
split; [| exact (skel_u64 E' false r y HE CK1 Hy)]. intros Hq. apply (proj1 (EQR y)) in Hq.
pose proof (skel_apart_Q E' r HE CK1 NB) as AP. clear - Hy Hq AP Q5 F9. zlia. }
split; [intros i E; discriminate E|].
intros i _.
destruct (OUT i) as (md_i & Hh_i & IO_i & Bv & NX & MD).
rewrite NX. rewrite MD in IO_i |- *.
set (md5 := grant_md false (Z_to_bv 64 50) (w64 QSv) (w64 131072) mdN) in *.
pose proof (grant_piece_shape (w64 QSv) (w64 131072) mdN) as (SH1 & SH2' & SH3 & SH4). cbv zeta in SH1, SH2', SH3, SH4. fold md5 in SH1, SH2', SH3, SH4.
assert (AL1 : QSv <= QSv + 131072) by (clear; zlia).
assert (AL2 : QSv mod page_size = 0) by (unfold page_size; exact QA).
assert (AL3 : (QSv + 131072) mod page_size = 0).
{ unfold page_size. clear - QA. apply Z.mod_divide in QA as [q' Hq]; [|zlia]. rewrite Hq. apply Z.mod_divide; [zlia|]. exists (q' + 32). zlia. }
destruct (allow_expose tfibsegs Wy md5 QSv (QSv + 131072) AL1 AL2 AL3 (proj1 CG) ltac:(rewrite SH3; clear - EG SL0; zlia)) as (LE5 & A5 & AB5 & VIS5 & MON5 & AI5).
set (W5 := wallow tfibsegs Wy QSv (QSv + 131072) AL1 AL2 AL3) in *.
assert (SUB : hsub (w_H W5) (w_H Wy)).
{ intros x Hx. destruct (w_H Wy x) eqn:Ex; [reflexivity|]. rewrite (MON5 x Ex) in Hx. discriminate Hx. }
eapply (amreal_world_le tfibsegs _ Wy W5); [exact LE5 | intros _; exact AI5 |].
apply (GRANT W5); [exact LE5 | exact SUB | exact MON5 | exact A5 | exact VIS5
| intros x Nx; unfold W5, wallow; cbn [w_H]; apply Hcut_out; exact Nx
| exact AI5 | split; [apply (proj2 (amwf_MWF md5)); exact (proj2 CG) | exact NZg] | exact (IOtr _ IO_i) | exact EG
| rewrite SH1, SH2', SH3, SH4; repeat split; reflexivity |].
assert (FRz : forall x : word, ~ QR (bv_unsigned x) -> zfill (w64 QSv) (w64 131072) mem x = mem x).
{ intros x Hx. apply zfill_out. rewrite UQS, Un. pose proof (EQR (bv_unsigned x)) as EQx. clear - Hx EQx.
destruct (Z_lt_le_dec (bv_unsigned x) QSv); [left; zlia|]. right. destruct (Z_lt_le_dec (bv_unsigned x) (QSv + 131072)); [exfalso; apply Hx; apply EQx; zlia | zlia]. }
assert (APQ : forall r y, In r (ss_mem S_V) -> base_val E' (YP09.r_base r) + YP09.r_lo r <= y < base_val E' (YP09.r_base r) + YP09.r_hi r -> ~ QR y /\ 0 <= y < 2 ^ 64).
{ intros r y Hr Hy.
pose proof (proj1 (forallb_forall _ _) (eq_refl : forallb (fun r => skel_okb false (skel r) && negb (obase_eqb (YP09.r_base r) (Some aQS))) (ss_mem S_V) = true) r Hr) as CK.
cbn beta in CK. apply andb_prop in CK as [CK1 CK2].
assert (NB : YP09.r_base r <> Some aQS) by (intros Eq; rewrite Eq in CK2; discriminate CK2).
split; [| exact (skel_u64 E' false r y HE CK1 Hy)]. intros Hq. apply (proj1 (EQR y)) in Hq.
pose proof (skel_apart_Q E' r HE CK1 NB) as AP. clear - Hy Hq AP Q5 F9. zlia. }
pose proof (at_N_cont Wy W5 md5 WIN (PSR W5 SH2 (fun m => R m /\ ZQF W5 m)) S_V TQ (w64 QSv) QR (zfill (w64 QSv) (w64 131072) mem) ms E'
HE HS Hrv MEQ PRS SUB ltac:(rewrite <- R10, (Hregs 10%bv), H10; reflexivity) Hnc ltac:(intros x Hx; rewrite Hms; cbn [ms_mem pend_at]; exact (FRz x Hx))
APQ
(fun r y Hr Hy => APQ r y Hr ltac:(pose proof (region_wf_facts r (regions_wf_In _ r (proj1 Hmem) Hr)) as (_ & WW & _); clear - Hy WW; zlia))
ltac:(intros y Hy Hq; apply (proj1 (EQR y)) in Hq; destruct Hsp as (S1 & _ & S3 & _); pose proof (lo_stk_ceil ly LY) as SC;
clear - Hy Hq S1 S3 SC Q5 F10; ceil; unfold ASAN_CEIL, ASTACK, kPtrArrayResv in *; try unfold sp0 in *; try unfold Qb in *; zlia)) as C.
rewrite Hms in C. cbn [ms_regs ms_mem pend_at] in C. rewrite Hpc, Hres_g in C. apply C. clear C.
rewrite Hms in HPm. cbn [ms_mem pend_at] in HPm. destruct HPm as [(HB & HM & HSH & HRs) HR0].
pose proof map_facts as (M1 & M2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _). pose proof map_zoneN as MZ. destruct Hmap_apart as (_ & _ & _ & MQ & _). unfold zdisjoint in MQ. cbn [fst snd] in MQ.
assert (NQR : forall a, (mb + 6144 <= a < mb + MSv) \/ (SMv <= a < SMv + MSv / 8) -> ~ QR a /\ bv_unsigned (Z_to_bv 64 a) = a).
{ intros a Ha. split.
- intros Hq. apply (proj1 (EQR a)) in Hq. clear - Ha Hq MQ Q5 F9 F10 M1 M2 SM1 SM2 E1 Heq MZ. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kPtrArrayResv, kHighShadowBeg, kHighShadowEnd in *. try unfold Qb in *. zlia.
- apply unsigned_lit_small. clear - Ha M1 M2 SM1 SM2 MZ. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kHighShadowBeg, kHighShadowEnd in *. zlia. }
split; [split; [|split; [|split]]|split].
-   intros j Hj. pose proof tr_length as LEN. pose proof (lo_top ly LY) as (_ & _ & _ & T4 & _ & _ & T7). destruct Hsp as (S1 & _ & S3 & _). pose proof (u64_range (getr regs0 2)) as U2.
pose proof (lo_stk_ceil ly LY) as SC.
intros kk Hkk. pose proof (HB j Hj kk Hkk) as X.
lazymatch goal with |- mbyte _ _ ?A = _ =>
assert (RNG : sp0 - ASTACK <= A < sp0) by (clear - Hj Hkk LEN MZ; unfold IFRAME, ASTACK; zlia);
destruct (PRS _ RNG) as [HhW _];
assert (HhY : w_H W5 (Z_to_bv 64 A) = false) by (apply MON5; exact HhW);
unfold mbyte, mrestrict in X |- *; rewrite HhW in X; rewrite HhY; rewrite (FRz (Z_to_bv 64 A)); [exact X|];
rewrite unsigned_lit_small by (clear - RNG S1 S3 T4 T7 U2 MZ; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, IFRAME, ASTACK, kHighMemBeg, kHighMemEnd in *; try unfold sp0 in *; zlia);
intros Hq; apply (proj1 (EQR _)) in Hq; clear - RNG Hq S1 SC Q5 F10 MZ; ceil; unfold ASAN_CEIL, ASTACK, kPtrArrayResv in *; try unfold sp0 in *; try unfold Qb in *; zlia
end.
- intros a Ha. destruct (NQR a (or_introl Ha)) as [Nq Ua]. destruct (HM a Ha) as [Hh [b Hb]]. split; [exact (MON5 _ Hh)|]. exists b. rewrite FRz; [exact Hb | rewrite Ua; exact Nq].
- intros a Ha. destruct (NQR a (or_intror Ha)) as [Nq Ua]. destruct (HSH a Ha) as [Hh [b Hb]]. split; [exact (MON5 _ Hh)|]. exists b. rewrite FRz; [exact Hb | rewrite Ua; exact Nq].
- pose proof SH_ok as (_ & _ & OK2). apply Forall_forall. intros r Hr a Ha. pose proof (proj1 (Forall_forall _ _) OK2 r Hr) as RO.
assert (PL : (mb + 6144 <= a < mb + MSv) \/ (SMv <= a < SMv + MSv / 8)) by (unfold run_ok in RO; clear - RO Ha MZ; zlia).
destruct (NQR a PL) as [Nq Ua]. unfold w64. rewrite FRz by (rewrite Ua; exact Nq). exact (proj1 (Forall_forall _ _) HRs r Hr a Ha).
- exact (RQ mem _ FRz HR0).
- intros a Hq. pose proof (proj1 (EQR a) Hq) as Ra.
assert (Ua : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit_small; clear - Ra F9 F10 Q5 E1 MZ; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kPtrArrayResv in *; try unfold Qb in *; zlia).
split; [apply VIS5; rewrite Ua; exact Ra|]. apply zfill_in. rewrite UQS, Un, Ua. exact Ra.
Qed.
Local Ltac s_runS HR tbl tblok stop ss' HX HP :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let st := eval vm_compute in (snd (sym_run_toN_sh tfibsegs tbl FUEL stop ss)) in
eapply SRr_bind;
[ eapply (at_S_runS Wx tbl tblok stop md X P ss ss' st W' c' HR);
[ vm_compute; reflexivity | exact I | exact HX | vm_compute; reflexivity | exact HP | vm_compute; reflexivity ]
| clear HR; let W2 := fresh "W" in let c2 := fresh "c" in intros W2 c2 _ HR ] end.
Definition RZF (R : (word -> option byte) -> Prop) (m : word -> option byte) : Prop := R m /\ ZQF Wy m.
Definition RZ (R : (word -> option byte) -> Prop) (m : word -> option byte) : Prop := R m /\ ZQ Wy m.
Lemma ZQF_rstable : idx = res -> rstable (ZQF Wy).
Proof.
intros Heq. pose proof (QR_facts Heq) as (E1 & _ & _ & F9 & Q5 & F10 & EQ).
pose proof map_facts as (M1 & M2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _). pose proof map_zoneN as MZ. destruct Hmap_apart as (_ & _ & _ & MQ & _). unfold zdisjoint in MQ. cbn [fst snd] in MQ.
assert (U64 : forall a, QR a -> bv_unsigned (Z_to_bv 64 a) = a).
{ intros a Ha. pose proof (proj1 (EQ a) Ha) as Ra. apply unsigned_lit_small. clear - Ra F9 F10 Q5 E1 MZ; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kPtrArrayResv in *; try unfold Qb in *; zlia. }
split.
- intros m m' FR H a Ha. destruct (H a Ha) as [H1 H2]. split; [exact H1|]. rewrite FR; [exact H2|]. rewrite (U64 a Ha).
pose proof (proj1 (EQ a) Ha) as Ra. intros Hw. destruct Hw as [Hw|Hw].
+ destruct (Z_lt_le_dec a (QSv + 8)) as [Hl|Hg].
* exact (QS_not_WIN1R a ltac:(clear - Ra Hl MZ; zlia) (or_introl Hw)).
* exact (QR_not_WIN1T Heq a Ha ltac:(clear - Hg MZ; zlia) (or_introl Hw)).
+ pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & _). clear - Hw Ra MQ Q5 F9 Z8 MZ. unfold kPtrArrayResv, MALLOC_MAX in *. try unfold Qb in *. zlia.
- intros m m' d len Hp FR H a Ha. destruct (H a Ha) as [H1 H2]. split; [exact H1|]. rewrite FR; [exact H2|]. rewrite (U64 a Ha).
pose proof (proj1 (EQ a) Ha) as Ra. clear - Hp Ra MQ F9 F10 Q5 M1 M2 SM1 SM2 E1 Heq MZ. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kPtrArrayResv, kHighShadowBeg, kHighShadowEnd in *. try unfold Qb in *. zlia.
Qed.
Local Ltac s_runR HR tbl tblok stop ss' HX HP :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let st := eval vm_compute in (snd (sym_run_toN_sh tfibsegs tbl FUEL stop ss)) in
eapply SRr_bind;
[ eapply (at_S_runR Wx tbl tblok stop md X P ss ss' st W' c' HR);
[ vm_compute; reflexivity | exact I | exact HX | vm_compute; reflexivity | exact HP | vm_compute; reflexivity ]
| clear HR; let W2 := fresh "W" in let c2 := fresh "c" in intros W2 c2 _ HR ] end.
Lemma segV : forall (R : (word -> option byte) -> Prop), rstable R -> idx = res ->
forall c, at_S Wy md1 (fun a => WIN a \/ QR a) (PSR Wy SH2 (RZF R)) S_VG Wy c ->
SRr tfibsegs Wy c (at_S Wy md1 (fun a => WIN a \/ QR a) (PSR Wy SH2 (RZ R)) S_YJ).
Proof.
intros R RS Heq c HR. pose proof SH_ok as (OK0 & OK1 & OK2). pose proof (rstable_and _ _ RS (ZQF_rstable Heq)) as RS2.
pose proof (PSR_stable Wy SH2 (RZF R) OK2 RS2) as HP2.
assert (HX : forall a, WIN1R a -> WIN a \/ QR a) by (intros a Ha; left; exact (WIN1R_WIN a Ha)).
pose proof high_facts as (_ & _ & _ & _ & _ & _ & _ & _ & F9 & F10 & _). pose proof Hidx as HI. pose proof Hres as [HRS _].
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kPtrArrayResv in F9, F10. unfold kMaxNumChunks in HI, HRS.
pose proof (QR_facts Heq) as (E1 & _ & _ & _ & Q5 & _ & EQR).
s_runR HR tfibtbl_rtC tfibtbl_rtC_ok 0x360e8 S_V2 HX HP2.
s_runR HR tfibtbl_rtA tfibtbl_rtA_ok 0x35f04 S_V3 HX HP2.
s_pin HR (12%bv : bv 5) (SOff aQS 0).
{ clear - HI F9 F10. pin_zevS. rewrite EaQS, EaQ, EaNCH. unfold w64. unfold QSv in *. rewrite !unsigned_lit_small by (try unfold Qb in *; zlia).
zcanon_simp. land_lits. rewrite Z.shiftl_mul_pow2 by zlia. change (2 ^ 3) with 8. zcanon_simp. try unfold Qb in *. zlia. }
lazymatch type of HR with at_S _ _ ?X0 _ ?ss _ _ =>
let rs1 := eval vm_compute in (setchunks (TFIB_INST + o_sec_reserved) [YP09.mkChunk (TFIB_INST + o_sec_reserved) (CVal 8 RES2T)] (ss_mem ss)) in
apply (at_S_setchunks Wy md1 X0 _ ss _ _ (TFIB_INST + o_sec_reserved) [YP09.mkChunk (TFIB_INST + o_sec_reserved) (CVal 8 RES2T)]) in HR;
[ change (setchunks _ _ (ss_mem ss)) with rs1 in HR; cbn [ss_pc ss_regs ss_resv ss_facts] in HR | vm_compute; reflexivity | ] end.
2:{ intros E' m HE _ r Hr Hb Hl RO.
lazymatch type of Hr with In _ ?l =>
pose proof (proj1 (forallb_forall _ _) (eq_refl : forallb (fun r => negb (match YP09.r_base r with None => Z.eqb (YP09.r_lo r) (TFIB_INST + o_sec_reserved) | Some _ => false end)
|| existsb (fun c => chunk_eqb c (YP09.mkChunk (TFIB_INST + o_sec_reserved) (CVal 8 (SOff aRES 16384)))) (YP09.r_chunks r)) l = true) r Hr) as CK end.
cbn beta in CK. rewrite Hb, Hl, Z.eqb_refl in CK. cbn [negb orb] in CK.
destruct RO as (_ & _ & _ & RC). apply Forall_cons; [|apply Forall_nil].
apply existsb_exists in CK as (k0 & Hk0 & CK). apply chunk_eqb_eq in CK. subst k0.
pose proof (proj1 (Forall_forall _ _) RC _ Hk0) as RC0. rewrite Hb in RC0. apply (chunk_ok_CVal_eqv E' _ _ _ _ RES2T (SOff aRES 16384)); [|exact RC0].
apply (sv_denot_eq_of_U E' _ _ HE); [vm_compute; reflexivity | vm_compute; reflexivity | exact (RES2T_eq Heq)]. }
lazymatch type of HR with at_S _ _ ?X0 _ ?ss _ _ =>
let rs := eval vm_compute in (trimscratch (-2416) (ss_mem ss)) in
apply (at_S_submem Wy md1 X0 _ ss _ _ rs) in HR; [| vm_compute; reflexivity | vm_compute; reflexivity] end.
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
pose proof (at_S_forget Wx md X P ss W' c' sJY [1; 15; 17; 20]%bv HR ltac:(unfold sHAV, sJY; zlia) eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as HR2; clear HR; rename HR2 into HR end.
s_noconds HR.
lazymatch type of HR with at_S _ _ ?X0 _ _ _ _ =>
apply (at_S_addreg Wy md1 X0 _ _ _ _ R_qs) in HR; [| reflexivity |] end.
2:{ intros E' m HE MEQ PRS [HP [HQ HZ]] HM. pose proof (proj1 HE) as HEn.
assert (BQ : base_val E' (Some aQS) = QSv).
{ cbn [base_val]. unfold aQS. rewrite (HEn 52%nat ltac:(unfold sHAV; zlia)), EaQS. unfold w64. apply unsigned_lit_small. clear - HI F9 F10. unfold QSv in *. try unfold Qb in *. zlia. }
split.
- unfold region_ok, R_qs. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite BQ.
split; [clear - HI F9; unfold QSv in *; try unfold Qb in *; zlia|]. split; [clear - HI F9 F10; unfold QSv in *; try unfold Qb in *; zlia|]. split; [|apply Forall_nil].
intros o Ho. apply apresent_writable_off; [off_by ltac:(clear - Ho HI F9 F10; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, QSv, TFIB_IMG_END in *; try unfold Qb in *; zlia) |].
destruct (HZ (QSv + o) ltac:(apply (proj2 (EQR _)); clear - Ho; zlia)) as [Hh Hz]. split; [exact Hh | exists (Z_to_bv 8 0); exact Hz].
- intros r2 Hr2. unfold extent_disjoint, R_qs. cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite !BQ.
lazymatch type of Hr2 with In _ ?l =>
pose proof (proj1 (forallb_forall _ _) (eq_refl : forallb (fun r => skel_okb false (skel r) && negb (obase_eqb (YP09.r_base r) (Some aQS))) l = true) r2 Hr2) as CK end.
cbn beta in CK. apply andb_prop in CK as [CK1 CK2].
assert (NB : YP09.r_base r2 <> Some aQS) by (intros Eq; rewrite Eq in CK2; discriminate CK2).
pose proof (skel_apart_QS E' false r2 HE CK1 NB) as AP. clear - AP. zlia. }
replace (addreg R_qs _) with S_YJ in HR by (rewrite <- S_VY_join; vm_compute; reflexivity).
apply SRr_ret. eapply at_S_weaken; [exact HR | intros a Ha; exact Ha | intros m [HP [HQ HZ]]; exact (conj HP (conj HQ (ZQ_of_ZQF Wy m HZ)))].
Qed.
End g.
End f.
