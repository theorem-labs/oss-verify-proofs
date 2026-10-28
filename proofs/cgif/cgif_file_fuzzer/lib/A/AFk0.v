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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK0v YK13 YP0n YA05 YA09 YG0b YG0h YG0j.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AFia AFib AFic AFid AFie AFif AFig.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YFen.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AFjv AFjw AFjx AFjh AFji AFjj AFjn AFjo AFjk AFjl AFjp AFjq AFjr AFjs AFjt AFju AFjy AFjz.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YF05.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AFih AFii AFk1 AFi3.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YA00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AFia.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0g.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Set Printing Depth 50. Set Printing Width 180.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
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
Section f.
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
Local Abbreviation seg1 := (@AFji.seg1 _ _ W ly regs0 mem0 md0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hn Hsp Nrange Hidx Hres).
Local Abbreviation PNULL := (@AFjj.PNULL W ly regs0 ch).
Local Abbreviation PNULLX := (@AFjj.PNULLX W ly regs0 n ch idx res).
Local Abbreviation tail_lits_apart := (@AFjj.tail_lits_apart).
Local Abbreviation segR := (@AFjj.segR _ _ W ly regs0 mem0 md0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Htp Hra Hsp Nrange Hidx Hres DPOST B S TS HARm).
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
Local Abbreviation SH5 := (@AFjq.SH5 n mb).
Local Abbreviation SH6 := (@AFjq.SH6 n mb).
Local Abbreviation user_marks := (@AFjq.user_marks _ ly regs0 n idx res mb Nrange Hidx Hres Hmap).
Local Abbreviation SH56_ok := (@AFjq.SH56_ok _ ly regs0 n idx res mb Nrange Hidx Hres Hmap).
Local Abbreviation segU1 := (@AFjq.segU1 _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation SH6_of_cut := (@AFjq.SH6_of_cut _ ly regs0 n idx res mb Nrange Hidx Hres Hmap).
Local Abbreviation segUe := (@AFjq.segUe _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hn Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation PT := (@AFjq.PT ly regs0 n ch mb).
Local Abbreviation run_okT := (@AFjq.run_okT n mb).
Local Abbreviation SH5o := (@AFjq.SH5o n mb).
Local Abbreviation SH6o := (@AFjq.SH6o n mb).
Local Abbreviation SH56o_ok := (@AFjq.SH56o_ok _ ly regs0 n idx res mb Nrange Hidx Hres Hmap).
Local Abbreviation PT_stableT := (@AFjq.PT_stableT _ ly regs0 n ch idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation segUo := (@AFjq.segUo _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hn Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation E0_at := (@AFjr.E0_at ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3).
Local Abbreviation map_atom := (@AFjr.map_atom).
Local Abbreviation E0_at_other := (@AFjr.E0_at_other ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation ed_E0_at := (@AFjr.ed_E0_at ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation st_ok_ecall_agree_on := (@AFjr.st_ok_ecall_agree_on _).
Local Abbreviation Esw := (@AFjr.Esw ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation Esw_agree := (@AFjr.Esw_agree ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation Esw_on := (@AFjr.Esw_on ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation at_S_facts_atoms := (@AFjr.at_S_facts_atoms _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation atoms_ok_app := (@AFjr.atoms_ok_app).
Local Abbreviation FS2_ok := (@AFjr.FS2_ok _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hn Hsp Nrange Hidx Hres Hmap DPOST S).
Local Abbreviation at_S_addreg_cfg := (@AFjr.at_S_addreg_cfg _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation S_N_apart := (@AFjr.S_N_apart _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart S).
Local Abbreviation S_N_nomap := (@AFjr.S_N_nomap).
Local Abbreviation grant_cont := (@AFjr.grant_cont _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hn Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S).
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
Local Abbreviation S_VG := (@AFjt.S_VG).
Local Abbreviation TQ := (@AFjt.TQ).
Local Abbreviation S_V_facts := (@AFjt.S_V_facts).
Local Abbreviation ZQF := (@AFjt.ZQF ly res).
Local Abbreviation ZQ := (@AFjt.ZQ ly idx res).
Local Abbreviation QR_facts := (@AFjt.QR_facts _ ly regs0 idx res mb LY IMG Hidx Hres S Hidx_def).
Local Abbreviation ZQ_of_ZQF := (@AFjt.ZQ_of_ZQF ly idx res).
Local Abbreviation QR_not_WIN1T := (@AFjt.QR_not_WIN1T _ ly regs0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart S Hidx_def).
Local Abbreviation ZQ_stableT := (@AFjt.ZQ_stableT _ ly regs0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart S Hidx_def).
Local Abbreviation ZQ_rstable := (@AFjt.ZQ_rstable _ ly regs0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart S Hidx_def).
Local Abbreviation ZQ_stableD := (@AFjt.ZQ_stableD _ ly regs0 idx res mb LY IMG Hsp Hidx Hres S Hidx_def).
Local Abbreviation skel_apart_Q := (@AFjt.skel_apart_Q _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart S Hidx_def Hres_def).
Local Abbreviation TQ_val := (@AFjt.TQ_val _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hidx Hres S Hidx_def).
Local Abbreviation nores50 := (@AFjt.nores50).
Local Abbreviation core50 := (@AFjt.core50).
Local Abbreviation pru17 := (@AFjt.pru17).
Local Abbreviation grant_piece_shape := (@AFjt.grant_piece_shape).
Local Abbreviation nodeV := (@AFjt.nodeV _ _ ly regs0 mem0 md0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation RZF := (@AFjt.RZF ly res).
Local Abbreviation RZ := (@AFjt.RZ ly idx res).
Local Abbreviation ZQF_rstable := (@AFjt.ZQF_rstable _ ly regs0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart S Hidx_def).
Local Abbreviation segV := (@AFjt.segV _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation CZI := (@AFju.CZI).
Local Abbreviation CZ := (@AFju.CZ ly).
Local Abbreviation abs_cell_okS := (@AFju.abs_cell_okS).
Local Abbreviation abs_cells_okS := (@AFju.abs_cells_okS).
Local Abbreviation MPAD := (@AFju.MPAD).
Local Abbreviation padb := (@AFju.padb).
Local Abbreviation const_cells_CZ := (@AFju.const_cells_CZ ly regs0 n idx res mb Nrange Hidx B TS HTSD).
Local Abbreviation CZ_untouched := (@AFju.CZ_untouched _ ly regs0 mem0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S).
Local Abbreviation cell_holds_agree := (@AFju.cell_holds_agree ly regs0 mem0 idx res Hidx Hres DPOST B S).
Local Abbreviation aview_agreeW := (@AFju.aview_agreeW W).
Local Abbreviation rd_ext_Wy := (@AFju.rd_ext_Wy W).
Local Abbreviation depot_ids_bound := (@AFju.depot_ids_bound ly regs0 mem0 idx res mb Hidx Hres DPOST B S TS).
Local Abbreviation depot_mem_ok_agree := (@AFju.depot_mem_ok_agree ly regs0 mem0 idx res mb Hidx Hres DPOST B S TS).
Local Abbreviation depot_mem_ok_ext := (@AFju.depot_mem_ok_ext ly B).
Local Abbreviation depot_at0 := (@AFju.depot_at0 _ W ly regs0 mem0 n idx res mb Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST B S HARm).
Local Abbreviation DPOSTS := (@AFju.DPOSTS ly regs0 ch B S).
Local Abbreviation D1W_ok := (@AFju.D1W_ok _ _ W ly regs0 mem0 n ch idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST B S TS HTSD HARm Hgp).
Local Abbreviation lyF := (@AFjy.lyF ly mb S).
Local Abbreviation SFS := (@AFjy.SFS ly regs0 n ch S).
Local Abbreviation KSc := (@AFjy.KSc n S).
Local Abbreviation lyF_le := (@AFjy.lyF_le ly mb S).
Local Abbreviation lyF_sec := (@AFjy.lyF_sec ly mb S).
Local Abbreviation lyF_eqs := (@AFjy.lyF_eqs ly mb S).
Local Abbreviation lyF_ok := (@AFjy.lyF_ok _ ly mb LY S).
Local Abbreviation sizes_model := (@AFjy.sizes_model ly regs0 n res Nrange S).
Local Abbreviation val_mem_cell := (@AFjy.val_mem_cell ly regs0 res B S).
Local Abbreviation le_byte_1_0 := (@AFjy.le_byte_1_0 ly regs0 res S).
Local Abbreviation find_chunk_at_app1 := (@AFjy.find_chunk_at_app1 B).
Local Abbreviation find_chunk_at_app2 := (@AFjy.find_chunk_at_app2 B).
Local Abbreviation In_combine_seq_app := (@AFjy.In_combine_seq_app).
Local Abbreviation combine_seq_last := (@AFjy.combine_seq_last ly regs0 res S).
Local Abbreviation in_combine_seq := (@AFjy.in_combine_seq ly regs0 res S).
Local Abbreviation combine_seq_in := (@AFjy.combine_seq_in ly regs0 res S).
Local Abbreviation index_of_app_old := (@AFjy.index_of_app_old).
Local Abbreviation index_ofZ_app_old := (@AFjy.index_ofZ_app_old).
Local Abbreviation index_of_app_new := (@AFjy.index_of_app_new ly regs0 res S).
Local Abbreviation index_ofZ_app_new := (@AFjy.index_ofZ_app_new ly regs0 res S).
Local Abbreviation fin_facts := (@AFjy.fin_facts ly regs0 mem0 n ch idx res mb B S).
Local Abbreviation wz_facts := (@AFjy.wz_facts _ W ly regs0 n ch res mb S).
Local Abbreviation S_AR_final := (@AFjy.S_AR_final _ W ly regs0 mem0 md0 n ch idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST B S TS HTSD HARm Hidx_def Hres_def).
Local Abbreviation SF_parts := (@AFjy.SF_parts ly regs0 n ch res S Hres_def).
Local Abbreviation rS_not_in_arr := (@AFjy.rS_not_in_arr _ W ly regs0 mem0 n res mb B S HARm).
Local Abbreviation len_arr := (@AFjy.len_arr idx S Hidx_def).
Local Abbreviation ck_base_new := (@AFjy.ck_base_new ly regs0 n res mb Nrange B S).
Local Abbreviation SEF := (@AFjy.SEF _ W ly regs0 mem0 n ch res mb Nrange B S HARm Hres_def).
Local Abbreviation staticF := (@AFjy.staticF ly mb S).
Local Abbreviation placed_finalG := (@AFjy.placed_finalG _ W ly regs0 mem0 md0 n ch idx res mb Nrange Hidx Hres Hmap B S HARm Hres_def).
Local Abbreviation sec_live_final := (@AFjy.sec_live_final ly regs0 n ch res mb Nrange S Hres_def).
Local Abbreviation FQ := (@AFjz.FQ ly n idx res mb).
Local Abbreviation OWN_T := (@AFjz.OWN_T _ W ly regs0 mem0 n idx res Hsp Nrange Hidx Hres DPOST B S HARm).
Local Abbreviation OWN_I := (@AFjz.OWN_I _ W ly regs0 mem0 n idx res mb Hsp Nrange Hidx Hres DPOST B S TS HARm).
Local Abbreviation OWN_Q := (@AFjz.OWN_Q _ W ly regs0 mem0 n idx res Hsp Nrange Hidx Hres DPOST B S HARm).
Local Abbreviation OWN_D := (@AFjz.OWN_D _ W ly regs0 mem0 n idx res Hsp Nrange Hidx Hres DPOST B S TS HARm).
Local Abbreviation band_core := (@AFjz.band_core ly B S).
Local Abbreviation OWN_SH := (@AFjz.OWN_SH _ W ly regs0 mem0 n idx res mb Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST B S HARm).
Local Abbreviation OWN_BANDhid := (@AFjz.OWN_BANDhid _ W ly mem0 md0 LY B S HARm).
Local Abbreviation NEWOWN := (@AFjz.NEWOWN _ W ly regs0 mem0 n ch idx res mb Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST B S HARm Hres_def).
Local Abbreviation fin_pack := (@AFjz.fin_pack ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb DPOST B S).
Local Abbreviation fin_post := (@AFjz.fin_post _ ly regs0 mem0 n ch idx res mb B S).
Local Abbreviation finE := (@AFjz.finE _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hn Htp Hra Hsp Nrange Hidx Hres Hmap DPOST B S Hidx_def).
Local Abbreviation finO := (@AFjz.finO _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hn Htp Hra Hsp Nrange Hidx Hres Hmap DPOST B S Hidx_def).
Local Abbreviation LEAF_S := (@AFjz.LEAF_S _ _ W ly regs0 mem0 md0 n ch idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST B S TS HTSD HARm Hidx_def Hres_def).
Local Abbreviation BCELLS := (@AFk1.BCELLS W mem0).
Local Abbreviation PGBv := (@AFk1.PGBv mb).
Local Abbreviation PGEv := (@AFk1.PGEv n mb).
Local Abbreviation big_marks := (@AFk1.big_marks _ ly regs0 n idx res mb Nrange Hidx Hres Hmap).
Local Abbreviation sm_bounds := (@AFk1.sm_bounds _ ly regs0 n idx res mb Nrange Hidx Hres Hmap).
Local Abbreviation U_SHBT := (@AFk1.U_SHBT _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Nrange Hidx Hres Hmap).
Local Abbreviation U_SHET := (@AFk1.U_SHET _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Nrange Hidx Hres Hmap).
Local Abbreviation U_PGBT := (@AFk1.U_PGBT _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Nrange Hidx Hres Hmap).
Local Abbreviation U_PGET := (@AFk1.U_PGET _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Nrange Hidx Hres Hmap).
Local Abbreviation U_SHB_X := (@AFk1.U_SHB_X _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Nrange Hidx Hres Hmap).
Local Abbreviation U_SHE_X := (@AFk1.U_SHE_X _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Nrange Hidx Hres Hmap).
Local Abbreviation in_bimg := (@AFk1.in_bimg).
Local Abbreviation in_bimg_facts := (@AFk1.in_bimg_facts _ ly regs0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap).
Local Abbreviation val_mem_xfer_bimg := (@AFk1.val_mem_xfer_bimg _ W ly regs0 mem0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap S).
Local Abbreviation can_word := (@AFk1.can_word W ly regs0 mem0 n idx res Hidx DPOST S).
Local Abbreviation B_R_ok := (@AFk1.B_R_ok _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap DPOST B S TS HARm).
Local Abbreviation zcanon_m1 := (@AFk1.zcanon_m1).
Local Abbreviation U_PGB_X := (@AFk1.U_PGB_X _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Nrange Hidx Hres Hmap).
Local Abbreviation U_PGE_X := (@AFk1.U_PGE_X _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Nrange Hidx Hres Hmap).
Local Abbreviation brun_refill := (@AFk1.brun_refill ly regs0 n idx res Hres S Hidx_def).
Local Abbreviation SH4_head := (@AFk1.SH4_head _ ly regs0 n idx res mb Nrange Hidx Hres Hmap S Hidx_def).
Local Abbreviation SH4_tail := (@AFk1.SH4_tail _ ly regs0 n idx res mb Nrange Hidx Hres Hmap S Hidx_def).
Local Abbreviation segB1a := (@AFk1.segB1a _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation zc_m1 := (@AFk1.zc_m1).
Local Abbreviation zc_idem := (@AFk1.zc_idem).
Local Abbreviation zc_add_l := (@AFk1.zc_add_l).
Local Abbreviation zc_sub_l := (@AFk1.zc_sub_l).
Local Abbreviation zc_sub_r := (@AFk1.zc_sub_r).
Local Abbreviation land_page_id := (@AFk1.land_page_id).
Local Abbreviation U_KA0 := (@AFk1.U_KA0 _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Nrange Hidx Hres Hmap).
Local Abbreviation U_KA1 := (@AFk1.U_KA1 _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Nrange Hidx Hres Hmap).
Local Abbreviation U_REM1 := (@AFk1.U_REM1 _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Nrange Hidx Hres Hmap).
Local Abbreviation U_REM2 := (@AFk1.U_REM2 _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Nrange Hidx Hres Hmap).
Local Abbreviation segB1b := (@AFk1.segB1b _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST).
Local Abbreviation segB1 := (@AFk1.segB1 _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST B S TS HARm Hidx_def Hres_def).
Local Abbreviation nores4032 := (@AFk1.nores4032).
Local Abbreviation core4032 := (@AFk1.core4032).
Local Abbreviation lit4032 := (@AFk1.lit4032).
Local Abbreviation S_K_facts := (@AFk1.S_K_facts).
Local Abbreviation nodeK := (@AFk1.nodeK _ _ ly regs0 mem0 md0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation submemb2 := (@AFk1.submemb2).
Local Abbreviation submemb2_sound := (@AFk1.submemb2_sound ly regs0 mem0 idx res Hidx Hres DPOST S Hidx_def Hres_def).
Local Abbreviation at_S_submem2 := (@AFk1.at_S_submem2 _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Hidx Hres DPOST S Hidx_def Hres_def).
Local Abbreviation SH5_of_SH4 := (@AFk1.SH5_of_SH4 _ ly regs0 n idx res mb Nrange Hidx Hres Hmap).
Local Abbreviation segB2 := (@AFk1.segB2 _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation allow_of_hull := (@AFk1.allow_of_hull _ ly regs0 n idx res mb Nrange Hidx Hres Hmap S).
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
Let rd0 : reader := aview tfibsegs (w_H W) mem0.
Let WF := am_wf B ly S rd0 HARm.
Definition S1 : astate := set_nev (st_nev S + 1) S.
Definition QLEAF (r : sptr * astate) (W' : world tfibsegs) (c' : config) : Prop :=
Wf (as_universe B) (snd r) /\ qtight (snd r) -> malloc_leaf tfibsegs B ly S W regs0 mem0 md0 n r W' c'.
Local Open Scope am_scope.
Definition sec_body : M (option sptr) :=
s <- YG00.get ;;
mcheck (Z.of_nat (length (st_sec_arr s)) <? kMaxNumChunks) 221048 ;;
YG00.put (set_secs (st_secs s ++ [mkSec (sec_map_size n) (needed_size n) true]) s) ;;
(if Z.of_nat (length (st_sec_arr s)) =? st_sec_reserved s then
z2 <- askz (KMapPtrArray (8 * Z.of_nat (length (st_sec_arr s))) kPtrArrayCommit) ;;
if aGranted z2 then YG00.modify (fun s0 => set_sec_reserved (st_sec_reserved s0 + kPtrArrayEntriesPerCommit) s0) else spin 391236
else YG00.ret tt) ;;
YG00.modify (fun s0 => set_sec_arr (st_sec_arr s0 ++ [length (st_secs s)]) s0) ;;
YG00.ret (Some (PSec (length (st_secs s)) kPage)).
Definition KSEC (z : Z) : itree astate (sptr * astate) := (ob <- (if z =? 0 then YG00.ret None else sec_body) ;; malloc_K n tr ob) S1.
Lemma malloc_secondary_eq : forall s, from_primary n = false ->
malloc n tr s = (tick ;; mcheck (n <? kMaxAllowedMalloc - kPage) 202260 ;; ob <- sec_alloc n ;; malloc_K n tr ob) s.
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
{ unfold in_img. change tfibsegs with AB1h.TSEGS. unfold AB1h.TSEGS. eexists. split; [do 3 right; left; reflexivity|]. cbn. unfold TFIB_ERRNO in Ha. zlia. }
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
{ apply (AFic.AR_snull B ly S W mem0 mem' md0 md' BSLv HB' TS HAR).
-
intros a Ra Ho NX. apply aview_same. apply NW; [exact Ra | | | | |].
+ intros ST. exact (AR_stack_law_ok tfibsegs B ly S W mem0 md0 a HAR ltac:(clear - ST S1' S3'; unfold ASTACK in *; try unfold sp0 in *; zlia) Ho).
+ intros X. apply NX. unfold AFic.XN. unfold WINT, t_unwinding in X. unfold T in X. clear - X. zlia.
+ intros X. apply NX. unfold AFic.XN. unfold WINI in X. clear - X. zlia.
+ intros ->. apply NX. unfold AFic.XN. left. zlia.
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
+ clear - Ha S1' T7. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, ASTACK in *. try unfold sp0 in *. zlia.
+ clear - Ha F1. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, WINT, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, t_unwinding in *. try unfold T in *. zlia.
+ clear - Ha HB'. unfold WINI, kHighShadowBeg, kHighShadowEnd, TFIB_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex in *. zlia.
+ clear - Ha. unfold kHighShadowBeg, kHighShadowEnd, TFIB_OOM in *. zlia.
+ clear - Ha. unfold kHighShadowBeg, kHighShadowEnd, TFIB_ERRNO in *. zlia. }
exists ly, regs', mem', md'.
split. { unfold cfg_at, raZ, YG0d.w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
split; [| split; [rewrite R10; cbn [fst sptr_addr sptr_exp aeval]; reflexivity | exact QT1]].
split; [exact (AR_tick B ly S W mem' md' ARF Hev)|].
split; [apply layout_le_refl|].
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
Hypothesis D1 : tfib_depot_spec B.
Hypothesis HBC : BCELLS.
Hypothesis HDP : forall z m, DPOST z m <-> DPOSTS W3 z m.
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
Proof. pose proof map_facts as (M1 & M2 & _). pose proof map_zoneN as MZ. pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & _). unfold w64. apply unsigned_lit_small. clear - M1 M2 Z8 MZ. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. zlia. Qed.
Lemma GAP : Forall (zdisjoint (mb, MSv)) (static_extents ly ++ vis0_zones ly ++ sec_extents ly S).
Proof.
pose proof (AFia.grant_apart B ly S rd0 mdN (w64 mb) MSv MA LN MSB ltac:(pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & _ & Z9 & _); exact Z9) GOK) as X.
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
apply (AFia.grant_shadow_zero B ly S rd0 mdN (w64 mb) MSv MA LN MSB Z9 GOK mem0 g (proj2 (proj2 (proj2 (proj2 (proj2 HAR)))))).
+ subst g. apply Z.mod_divide; [zlia|]. apply Z.mod_divide in M3 as [p Hp]; [|zlia]. exists (p * 512 + (a - SMv)). zlia.
+ rewrite Umb. subst g. clear - Ha MZ. zlia.
+ rewrite Umb. subst g. clear - Ha DM8 M8 MZ. zlia.
- rewrite unsigned_lit_small by (rewrite Hg; exact Ra). rewrite Hg. intros Hw. unfold WINP, WINT, WINI in Hw. pose proof BSLv_range as HBS. pose proof high_facts as (F1 & _).
destruct Hsp as (S1' & _). pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7).
clear - Hw Ha SM1 SM2 F1 S1' T7 HBS MZ. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, ASTACK, t_unwinding, TFIB_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex in *.
try unfold sp0 in *. try unfold T in *. zlia.
Qed.
Lemma VISM : forall a, mb <= a < mb + MSv -> w_H W3 (w64 a) = false.
Proof. intros a Ha. pose proof map_facts as (M1 & M2 & _). pose proof map_zoneN as MZ. apply VISM3. unfold w64. rewrite unsigned_lit_small; [exact Ha | clear - Ha M1 M2 MZ; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; zlia]. Qed.
Lemma WZ3 : forall z mat', ALedger tfibsegs lyF (SFS false z) md2 -> wz_facts false z W3 (with_vm_backing (m_vm_lazy md2) mat' md2).
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
assert (UQa : bv_unsigned (w64 QSv) = QSv) by (unfold w64; apply unsigned_lit_small; clear - F9 Q5 F10; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kPtrArrayResv in *; try unfold Qb in *; zlia).
assert (UQb : bv_unsigned (w64 131072) = 131072) by (unfold w64; apply unsigned_lit_small; zlia).
apply (YG0j.cov_grant_md false (Z_to_bv 64 50) (w64 QSv) (w64 131072) mdV x).
- unfold YK0g.model_ivs_wf. split; [|split; [|split; [|exact W5]]]; intros q Hq; [exact (W1 q Hq) | exact (W2 q Hq) | exact (W3' q Hq)].
- rewrite UQa, UQb. clear - F9 Q5 F10. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kPtrArrayResv in *. try unfold Qb in *. zlia.
- rewrite UQa, UQb. intros Hin. apply Hx. clear - Hin F9 Q5. unfold kPtrArrayResv in *. try unfold Qb in *. zlia.
Qed.
Lemma grant50_isp : forall (a k : word) md, vm_init_sp (m_vmmaps (grant_md false (Z_to_bv 64 50) a k md)) = vm_init_sp (m_vmmaps md).
Proof.
clear. intros a k md. unfold grant_md, fixedin_ok_model, fixedin_ok_vmmaps, with_mmap_replacement, with_mmap_backing. rewrite AFjt.nores50. cbn.
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
mcheck (depot_ids s' + 1 <? kDepotIdsPerBlock) 469488 ;;
mcheck (kStartFramesMax + depot_frames s' + Z.of_nat (length tr) + 1 <? kStoreFramesPerBlock) 460508 ;;
YG00.put (set_depot (st_depot s' ++ [tr]) s'))) ;;
(let k := mkChunk beg n CAllocated in
(if needs_remap (ck_n k) then z <- askz (KShadowRemap (ck_user k) (8 * (ck_n k / 8))) ;; if aGranted z then YG00.ret tt else spin 449860 else YG00.ret tt) ;;
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
Lemma TAILg : N8D / 8 < 18446744073709551615 -> forall (grow : bool) (Wz : world tfibsegs) (mdz : Model) (RX : (word -> option byte) -> Prop) (Xd : Z -> Prop) z c4 s4,
(grow = true <-> idx = res) -> rstable RX -> pstable WIN1T RX -> (grow = true -> forall m, RX m -> ZQ Wz m) ->
(forall a, WIN a -> Xd a) -> (forall a, Xd a -> WIN a \/ (grow = true /\ QR a) \/ DX a) ->
wle W Wz -> same_io md0 mdz -> (forall mat', wz_facts grow z Wz (with_vm_backing (m_vm_lazy mdz) mat' mdz)) ->
(forall x : word, ~ (mb <= bv_unsigned x < mb + MSv) -> ~ (SHLO mb <= bv_unsigned x < SHHI mb) ->
~ (grow = true /\ QSv <= bv_unsigned x < QSv + 131072) -> w_H Wz x = w_H W x) ->
(forall zz m, DPOST zz m -> DPOSTS Wz zz m) ->
at_S Wz mdz Xd (PSR Wz SH2 (PDX Wz RX z)) T_2 Wz c4 ->
st_depot s4 = st_depot (depot_after z tr S) -> st_chunks s4 = st_chunks S -> st_secs s4 = st_secs S ++ [mkSec (sec_map_size n) (needed_size n) true] ->
st_sec_arr s4 = st_sec_arr S ++ [length (st_secs S)] ->
st_sec_reserved s4 = (if grow then st_sec_reserved S + kPtrArrayEntriesPerCommit else st_sec_reserved S) -> st_regions s4 = st_regions S ->
st_nev s4 = st_nev S + 1 -> st_cache_inited s4 = st_cache_inited S -> st_cache s4 = st_cache S -> st_qthread s4 = st_qthread S ->
st_qglobal s4 = st_qglobal S -> st_fs s4 = st_fs S -> st_internal_inited s4 = st_internal_inited S ->
amreal tfibsegs ((YG00.ret tt ;;
(YG00.modify (fun s0 => set_chunks (upd_chunk (st_chunks s0) (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated)) s0) ;;
YG00.ret (ck_user (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated)))) s4) Wz c4 QLEAF.
Proof.
intros Hsmall grow Wz mdz RX Xd z c4 s4 Hgrow RXs RXt HRXQ HXW HXsub LEz IOz HWZ HOUT HDPz HR D4 C4 SE4 A4 R4 RG4 N4 CI4 CA4 QT4 QG4 FS4 II4.
pose proof sizes_model as (ND & MS & RS & RZ & FP & KN & KR & KE & KQ & KB & KST).
eapply amreal_pure; [reflexivity|]. eapply amreal_pure; [reflexivity|]. cbn [amreal].
assert (LEAF : forall W' c', fin_post Wz mdz grow z W' c' ->
QLEAF (ck_user (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated), set_chunks (upd_chunk (st_chunks s4) (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated)) s4) W' c').
{ intros W' c' (-> & regs' & mem' & mat' & memD' & -> & HF) MP.
assert (EQS : set_chunks (upd_chunk (st_chunks s4) (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated)) s4 = SFS grow z).
{ pose proof (AFib.upd_chunk_fresh (st_chunks S) (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated)
(AFib.KS_fresh S (as_universe B) 0 0 0 WF)) as UF.
clear HR. destruct s4; cbn in *. subst. unfold SFS, AFib.sfinal, AFib.depF, AFib.resF, AFib.KS, AFib.rS. cbn. cbn in UF. rewrite UF.
rewrite MS, ND. unfold depot_after. destruct grow; destruct (z =? 0); reflexivity. }
rewrite EQS in MP |- *. change (ck_user (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated)) with (ck_user KSc).
exact (LEAF_S grow z Wz mdz HAR Hgrow LEz IOz HWZ HOUT regs' mem' memD' mat' MP HF). }
assert (HDPOST : forall zz m, DPOST zz m -> aok S (KDepot tr) zz /\ depot_mem_ok B ly (depot_after zz tr S) (aview tfibsegs (w_H Wz) m) /\ Forall (cell_holds B ly (aview tfibsegs (w_H Wz) m)) (as_const B ly)).
{ intros zz m Hd. exact (HDPz zz m Hd). }
step HR (segT2 Wz mdz RX RXs RXt Xd z HXW _ _ HR). pose proof (proj1 HR) as EW. subst W0.
step HR (segU1 Wz mdz RX RXs RXt Xd z HXW Hsmall _ _ HR). pose proof (proj1 HR) as EW. subst W0.
destruct (Z.eq_dec (n mod 8) 0) as [H8|H8].
- step HR (segUe Wz mdz RX RXs RXt Xd z HXW H8 _ _ HR). pose proof (proj1 HR) as EW. subst W0.
eapply SRr_mono; [exact (finE Wz mdz Xd RX grow z Hgrow HXsub HRXQ HDPOST H8 _ _ HR)|].
intros W' c' _ HP. exact (LEAF W' c' HP).
- step HR (segUo Wz mdz RX RXs RXt Xd z HXW H8 _ _ HR). pose proof (proj1 HR) as EW. subst W0.
eapply SRr_mono; [exact (finO Wz mdz Xd RX grow z Hgrow HXsub HRXQ HDPOST H8 _ _ HR)|].
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
Lemma TAILgB : 18446744073709551615 <= N8D / 8 -> forall (grow : bool) (Wz : world tfibsegs) (mdz : Model) (RX : (word -> option byte) -> Prop) (Xd : Z -> Prop) z c4 s4,
(grow = true <-> idx = res) -> rstable RX -> pstable WIN1T RX -> (grow = true -> forall m, RX m -> ZQ Wz m) ->
(forall a, WIN a -> Xd a) -> (forall a, Xd a -> WIN a \/ (grow = true /\ QR a) \/ DX a) ->
wle W Wz -> same_io md0 mdz -> (forall mat', wz_facts grow z Wz (with_vm_backing (m_vm_lazy mdz) mat' mdz)) ->
(forall x : word, ~ (mb <= bv_unsigned x < mb + MSv) -> ~ (SHLO mb <= bv_unsigned x < SHHI mb) ->
~ (grow = true /\ QSv <= bv_unsigned x < QSv + 131072) -> w_H Wz x = w_H W x) ->
(forall zz m, DPOST zz m -> DPOSTS Wz zz m) ->
In (SHLO mb, SHHI mb) (w_A Wz) ->
at_S Wz mdz Xd (PSR Wz SH2 (PDX Wz RX z)) T_2 Wz c4 ->
st_depot s4 = st_depot (depot_after z tr S) -> st_chunks s4 = st_chunks S -> st_secs s4 = st_secs S ++ [mkSec (sec_map_size n) (needed_size n) true] ->
st_sec_arr s4 = st_sec_arr S ++ [length (st_secs S)] ->
st_sec_reserved s4 = (if grow then st_sec_reserved S + kPtrArrayEntriesPerCommit else st_sec_reserved S) -> st_regions s4 = st_regions S ->
st_nev s4 = st_nev S + 1 -> st_cache_inited s4 = st_cache_inited S -> st_cache s4 = st_cache S -> st_qthread s4 = st_qthread S ->
st_qglobal s4 = st_qglobal S -> st_fs s4 = st_fs S -> st_internal_inited s4 = st_internal_inited S ->
amreal tfibsegs (((z' <- askz (KShadowRemap (ck_user (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated))
(8 * (ck_n (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated) / 8))) ;;
(if aGranted z' then YG00.ret tt else spin 449860)) ;;
(YG00.modify (fun s0 => set_chunks (upd_chunk (st_chunks s0) (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated)) s0) ;;
YG00.ret (ck_user (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated)))) s4) Wz c4 QLEAF.
Proof.
intros Hbig. exfalso. clear - Hbig Nrange. unfold AFjm.N8D in Hbig. unfold MALLOC_MAX in Nrange.
rewrite Z.div_mul in Hbig by (clear; lia).
pose proof (Z.div_lt_upper_bound n 8 (2 ^ 25) ltac:(clear; lia) ltac:(clear - Nrange; lia)) as HH. clear Nrange. lia.
Qed.
Lemma after_depot : forall (grow : bool) (Wz : world tfibsegs) (mdz : Model) (RX : (word -> option byte) -> Prop) (Xd : Z -> Prop) z c4 s3,
(grow = true <-> idx = res) -> rstable RX -> pstable WIN1T RX -> (grow = true -> forall m, RX m -> ZQ Wz m) ->
(forall a, WIN a -> Xd a) -> (forall a, Xd a -> WIN a \/ (grow = true /\ QR a) \/ DX a) ->
wle W Wz -> same_io md0 mdz -> (forall mat', wz_facts grow z Wz (with_vm_backing (m_vm_lazy mdz) mat' mdz)) ->
(forall x : word, ~ (mb <= bv_unsigned x < mb + MSv) -> ~ (SHLO mb <= bv_unsigned x < SHHI mb) ->
~ (grow = true /\ QSv <= bv_unsigned x < QSv + 131072) -> w_H Wz x = w_H W x) ->
(forall zz m, DPOST zz m -> DPOSTS Wz zz m) ->
In (SHLO mb, SHHI mb) (w_A Wz) ->
at_S Wz mdz Xd (PSR Wz SH2 (PDX Wz RX z)) T_2 Wz c4 ->
st_depot s3 = st_depot S -> st_chunks s3 = st_chunks S -> st_secs s3 = st_secs S ++ [mkSec (sec_map_size n) (needed_size n) true] ->
st_sec_arr s3 = st_sec_arr S ++ [length (st_secs S)] ->
st_sec_reserved s3 = (if grow then st_sec_reserved S + kPtrArrayEntriesPerCommit else st_sec_reserved S) -> st_regions s3 = st_regions S ->
st_nev s3 = st_nev S + 1 -> st_cache_inited s3 = st_cache_inited S -> st_cache s3 = st_cache S -> st_qthread s3 = st_qthread S ->
st_qglobal s3 = st_qglobal S -> st_fs s3 = st_fs S -> st_internal_inited s3 = st_internal_inited S ->
amreal tfibsegs (KDEP s3 (PSec (length (st_secs S1)) kPage) z) Wz c4 QLEAF.
Proof.
intros grow Wz mdz RX Xd z c4 s3 Hgrow RXs RXt HRXQ HXW HXsub LEz IOz HWZ HOUT HDPz HULL HR D3 C3 SE3 A3' R3 RG3 N3 CI3 CA3 QT3 QG3 FS3 II3.
unfold KDEP. destruct (Z_lt_le_dec (N8D / 8) 18446744073709551615) as [Hsm|Hbg].
-
pose proof (fun s4 => TAILg Hsm grow Wz mdz RX Xd z c4 s4 Hgrow RXs RXt HRXQ HXW HXsub LEz IOz HWZ HOUT HDPz HR) as TAIL.
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
pose proof (fun s4 => TAILgB Hbg grow Wz mdz RX Xd z c4 s4 Hgrow RXs RXt HRXQ HXW HXsub LEz IOz HWZ HOUT HDPz HULL HR) as TAIL.
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
assert (Ru : TFIB_IMG_END <= u < 2 ^ 64) by (clear - Hu F9 F10 HI HRS MZ; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, QSv, TFIB_IMG_END, kHighMemBeg, ASAN_CEIL, kPtrArrayResv, kMaxNumChunks in *; try unfold Qb in *; zlia).
assert (P0 : apresent (w_H W) mem0 u).
{ apply (vis_present (AQ 0) (8 * st_sec_reserved S) u); [right; unfold aareas; apply in_app_iff; right; left; reflexivity | cbn [aeval]; rewrite <- Hres_def; unfold QSv in Hu; try unfold Qb in Hu; clear - Hu HI HRS NE MZ; zlia | off_by ltac:(exact Ru) ]. }
destruct P0 as [Hh [b Hb']]. split; [exact (MON3 _ Hh)|]. exists b. rewrite zfill_out.
- rewrite MEQ; [exact Hb'|]. rewrite unsigned_lit_small by (clear - Ru MZ; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END in Ru; zlia). unfold WINP, WINT, WINI. pose proof BSLv_range as HBS. pose proof high_facts as (F1 & _). destruct Hsp as (S1' & _ & S3' & _).
pose proof stack_ivs as (_ & _ & _ & SI4). pose proof HCX as (_ & _ & QT & _). unfold zdisjoint in QT. cbn [fst snd] in QT.
clear - Hu F1 F9 F10 HI HRS HBS S1' S3' SI4 QT MZ. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, QSv, kHighMemBeg, ASAN_CEIL, kPtrArrayResv, kMaxNumChunks, ASTACK, t_unwinding, kThreadObjSize, TFIB_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex in *.
try unfold Qb in *. try unfold T in *. try unfold sp0 in *. zlia.
- rewrite Umb. unfold w64. rewrite !unsigned_lit_small by (clear - Ru M1 M2 Z8 MZ; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END, kHighMemBeg, ASAN_CEIL, MALLOC_MAX in *; zlia).
destruct Hmap_apart as (_ & _ & _ & MQ & _). unfold zdisjoint in MQ. cbn [fst snd] in MQ. clear - Hu MQ HI HRS F9 F10 MZ. unfold QSv, kPtrArrayResv, kMaxNumChunks in *. try unfold Qb in *. zlia.
Qed.
Lemma HmapD : zdisjoint (mb, MSv) (ly_D ly, 4096).
Proof. apply (proj1 (Forall_forall _ _) GAP). apply in_app_iff. left. unfold static_extents, owned_extents. apply in_app_iff. left. cbn. tauto. Qed.
Theorem grantS_ne : idx <> res -> amreal tfibsegs (KSEC 1) W3 ccont QLEAF.
Proof.
intros NE. pose proof Hidx as HI. pose proof Hres as [HRS HRA].
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
assert (RXd : pstable DX (fun _ : word -> option byte => True)) by (clear; intros m m' _ _; exact I).
assert (HXW : forall a, WIN a -> WIN a) by (clear; intros a H; exact H).
assert (HXQ : forall a, WIN a -> WIN a \/ QR a) by (clear; intros a H; left; exact H).
pose proof (D1W_ok W3 MON3 Htr HmapD (fun z m H => proj2 (HDP z m) H) D1) as D1w.
step HR (segG1 W3 md2 _ RST ccont HR). pose proof (proj1 HR) as EW. subst W0.
step HR (segNE W3 md2 (fun _ => True) RXs NE _ HR). pose proof (proj1 HR) as EW. subst W0.
step HR (segJ W3 md2 (fun _ => True) RXt WIN HXW _ HR). pose proof (proj1 HR) as EW. subst W0.
step HR (segT1 W3 md2 (fun _ => True) RXt WIN HXW _ HR). pose proof (proj1 HR) as EW. subst W0.
eapply SRr_bind; [exact (at_S_depot W3 md2 (fun _ => True) D1w RXd WIN HXQ HXW _ HR) | clear HR; intros W4 c4 _ [z HR]].
pose proof (proj1 HR) as EW. subst W4.
pose proof HR as HRc. destruct HRc as (_ & ms4 & mat4 & E4 & Ec4 & HE4 & HS4 & MEQ4 & PRS4 & [HPS4 [HPD4 _]]).
destruct HPD4 as (memD & DP & PRD & EQD). pose proof (proj1 (HDP z memD) DP) as (AOKz & DEPz & CSTz).
apply SRr_ret. exists z. split; [exact AOKz|].
assert (Hgrow : false = true <-> idx = res) by (split; [intros E; discriminate E | intros E; exfalso; exact (NE E)]).
assert (HXsub : forall a, (WIN a \/ DX a) -> WIN a \/ (false = true /\ QR a) \/ DX a) by (clear; intros a [Ha|Ha]; tauto).
assert (HRXQ : false = true -> forall m : word -> option byte, True -> ZQ W3 m) by (intros E; discriminate E).
assert (HXW' : forall a, WIN a -> WIN a \/ DX a) by (clear; intros a H; left; exact H).
assert (HOUT : forall x : word, ~ (mb <= bv_unsigned x < mb + MSv) -> ~ (SHLO mb <= bv_unsigned x < SHHI mb) -> ~ (false = true /\ QSv <= bv_unsigned x < QSv + 131072) -> w_H W3 x = w_H W x)
by (intros x N1 N2 _; exact (OUT3 x N1 N2)).
assert (HDP3 : forall zz m, DPOST zz m -> DPOSTS W3 zz m) by (intros zz m Hd; exact (proj1 (HDP zz m) Hd)).
apply (after_depot false W3 md2 (fun _ => True) (fun a => WIN a \/ DX a) z c4 _ Hgrow RXs RXt HRXQ HXW' HXsub LE3 IO2 (fun mat' => WZ3 z mat' (LED0 z)) HOUT HDP3
ltac:(rewrite A3; left; reflexivity) HR);
unfold S1; cbn; reflexivity.
Qed.
Lemma DPOSTS_Q : forall (W5 : world tfibsegs), idx = res -> hsub (w_H W5) (w_H W3) ->
(forall x : word, ~ (QSv <= bv_unsigned x < QSv + 131072) -> w_H W5 x = w_H W3 x) ->
forall z m, DPOSTS W3 z m <-> DPOSTS W5 z m.
Proof.
intros W5 Heq SUB5 OUT5 z m. pose proof (QR_facts Heq) as (E1 & _ & QA & F9 & Q5 & F10 & EQR). pose proof Hidx as HI. pose proof Hres as [HRS _].
assert (X35 : rd_ext (aview tfibsegs (w_H W3) m) (aview tfibsegs (w_H W5) m)) by (apply aview_ext; [apply w_Hoff | exact SUB5]).
assert (AG : forall a, 0 <= a < 2 ^ 64 -> ~ QR a -> aview tfibsegs (w_H W3) m a = aview tfibsegs (w_H W5) m a).
{ intros a Ha Hq. unfold aview, mrestrict, YP09.mbyte. cbn beta. rewrite (OUT5 (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by exact Ha. intros H'. apply Hq. apply EQR. exact H'. }
assert (AGC : forall c, In c (as_const B ly) -> forall k, 0 <= k < Z.max 1 (Z.of_nat (c_w c)) ->
aview tfibsegs (w_H W3) m (aeval B ly (c_at c) + k) = aview tfibsegs (w_H W5) m (aeval B ly (c_at c) + k)).
{ intros c Hc k Hk. pose proof (const_cells_CZ c k Hc Hk) as CK. destruct (padb c).
- apply AG; [| intros Hq; apply EQR in Hq]; unfold MPAD in CK; clear - CK F9 Hq || clear - CK F9;
unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_INST, o_sec_mutex, kHighMemBeg in *; try unfold Qb in *; zlia.
- pose proof (CZ_untouched HmapD _ CK) as (Ra & _ & NQ & _). exact (AG _ Ra NQ). }
assert (AGD : forall a, DZONE a -> aview tfibsegs (w_H W3) m a = aview tfibsegs (w_H W5) m a).
{ intros a Ha. pose proof blocks_facts as (NBhi & SBhi & _ & _ & QNB & QSB & _).
assert (Ra : 0 <= a < 2 ^ 64) by (clear - Ha NBhi SBhi LY; unfold DZONE in Ha; numconst; zlia).
apply (AG _ Ra). unfold zdisjoint in QNB, QSB. cbn [fst snd] in QNB, QSB. unfold QR. clear - Ha QNB QSB F9 HRS HI.
unfold zone3, TFIB_IMG_LO, kLowShadowBeg, DZONE, kHighMemBeg, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kMaxNumChunks, kPtrArrayEntriesPerCommit in *. try unfold Qb in *. zlia. }
assert (IDS : depot_ids (depot_after z tr S) <= 4098).
{ pose proof (wf_depot _ _ _ _ _ WF) as [ND INC]. pose proof (depot_ids_bound S ND INC) as IB. unfold depot_after. destruct (z =? 0); [clear - IB; zlia|].
unfold depot_ids in *. cbn [st_depot set_depot]. rewrite length_app. cbn [length]. clear - IB. zlia. }
split; intros (P1 & P2 & P3); (split; [exact P1|]).
- split; [exact (depot_mem_ok_ext _ _ _ X35 P2) | exact (Forall_cell_holds_ext B ly _ _ _ X35 P3)].
- split.
+ apply (depot_mem_ok_agree (depot_after z tr S) (aview tfibsegs (w_H W5) m)); [exact IDS | exact AGD | exact P2].
+ apply Forall_forall. intros c Hc. apply (cell_holds_agree (aview tfibsegs (w_H W5) m)); [exact (AGC c Hc) | exact (proj1 (Forall_forall _ _) P3 c Hc)].
Qed.
Theorem grantS_eq : idx = res -> amreal tfibsegs (KSEC 1) W3 ccont QLEAF.
Proof.
intros EQ. pose proof Hidx as HI. pose proof Hres as [HRS HRA]. pose proof (QR_facts EQ) as (E1 & _ & QA & F9 & Q5 & F10 & EQR).
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
assert (RD5 : pstable DX (RZ W5 (fun _ => True))) by (apply pstable_and; [clear; intros m m' _ _; exact I | exact (ZQ_stableD W5)]).
assert (HXW5 : forall a, WIN a -> WIN a \/ QR a) by (clear; intros a H; left; exact H).
assert (HXQ5 : forall a, (WIN a \/ QR a) -> WIN a \/ QR a) by (clear; intros a H; exact H).
assert (MON35 : forall x : word, w_H W x = false -> w_H W5 x = false) by (intros x Hx; exact (MON5 x (MON3 x Hx))).
assert (OUT5' : forall x : word, ~ (QSv <= bv_unsigned x < QSv + 131072) -> w_H W5 x = w_H W3 x) by exact OUT5.
pose proof (DPOSTS_Q W5 EQ SUB5 OUT5') as DQ.
assert (HDP5 : forall z m, DPOST z m <-> DPOSTS W5 z m) by (intros z m; rewrite (HDP z m); exact (DQ z m)).
pose proof (D1W_ok W5 MON35 Htr HmapD (fun z m H => proj2 (HDP5 z m) H) D1) as D1w.
assert (LE35 : wle W W5) by (exact (wle_trans _ _ _ _ LE3 LE5)).
pose proof HR5 as HR. clear HR5.
step HR (segV W5 md5 (fun _ => True) RXs EQ _ HR). pose proof (proj1 HR) as EW. subst W0.
step HR (segJ W5 md5 (RZ W5 (fun _ => True)) RT5 (fun a => WIN a \/ QR a) HXW5 _ HR). pose proof (proj1 HR) as EW. subst W0.
step HR (segT1 W5 md5 (RZ W5 (fun _ => True)) RT5 (fun a => WIN a \/ QR a) HXW5 _ HR). pose proof (proj1 HR) as EW. subst W0.
eapply SRr_bind; [exact (at_S_depot W5 md5 (RZ W5 (fun _ => True)) D1w RD5 (fun a => WIN a \/ QR a) HXQ5 HXW5 _ HR) | clear HR; intros W6 c6 _ [z HR]].
pose proof (proj1 HR) as EW. subst W6.
pose proof HR as HRc. destruct HRc as (_ & ms6 & mat6 & E6 & Ec6 & HE6 & HS6 & MEQ6 & PRS6 & [HPS6 [HPD6 _]]).
destruct HPD6 as (memD & DP & PRD & EQD). pose proof (proj1 (HDP5 z memD) DP) as (AOKz & DEPz & CSTz).
apply SRr_ret. exists z. split; [exact AOKz|].
assert (Hgrow : true = true <-> idx = res) by (split; [intros _; exact EQ | intros _; reflexivity]).
assert (HXsub : forall a, ((WIN a \/ QR a) \/ DX a) -> WIN a \/ (true = true /\ QR a) \/ DX a) by (clear; intros a [[Ha|Ha]|Ha]; tauto).
assert (HRXQ : true = true -> forall m : word -> option byte, RZ W5 (fun _ => True) m -> ZQ W5 m) by (intros _ m [_ Hm]; exact Hm).
assert (HXW' : forall a, WIN a -> (WIN a \/ QR a) \/ DX a) by (clear; intros a H; left; left; exact H).
assert (HOUT : forall x : word, ~ (mb <= bv_unsigned x < mb + MSv) -> ~ (SHLO mb <= bv_unsigned x < SHHI mb) -> ~ (true = true /\ QSv <= bv_unsigned x < QSv + 131072) -> w_H W5 x = w_H W x).
{ intros x N1 N2 N3. rewrite (OUT5 x (fun H => N3 (conj eq_refl H))). exact (OUT3 x N1 N2). }
assert (HDPz : forall zz m, DPOST zz m -> DPOSTS W5 zz m) by (intros zz m Hd; exact (proj1 (HDP5 zz m) Hd)).
assert (WZ5 : forall mat', wz_facts true z W5 (with_vm_backing (m_vm_lazy md5) mat' md5)).
{ intros mat'. constructor.
- exact MON35.
- intros x Hx. exact (MON5 x (VISM3 x Hx)).
- intros x Hx. exact (MON5 x (VISH3 x Hx)).
- intros _ x Hx. apply VIS5. apply EQR. exact Hx.
- rewrite A5, A3. cbn [A_bytes fst snd]. zlia.
- intros i Hi. rewrite A5, A3. cbn. right; right; right. exact Hi.
- rewrite A5, A3. cbn. right; right; left. reflexivity.
- rewrite A5, A3. cbn. right; left. reflexivity.
- apply (ALedger_same tfibsegs lyF (SFS true z) md5 _ (LED1 z mdV md5 EQ (LV z) (proj1 VM5) (proj1 (proj2 VM5)) (proj1 (proj2 (proj2 VM5))) (proj2 (proj2 (proj2 VM5))) (grant50_isp _ _ _) (COV_Q mdV MWV EQ) EG5 (YG0g.naf_grant_md false (Z_to_bv 64 50) mdV _ _ MWV))
(m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) (eager_used_wvb _ _)).
- exact (amwf_same md5 _ (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) MW5).
- exact GAP. }
apply (after_depot true W5 md5 (RZ W5 (fun _ => True)) (fun a => (WIN a \/ QR a) \/ DX a) z c6 _ Hgrow RS5 RT5 HRXQ HXW' HXsub LE35 IO5 WZ5 HOUT HDPz
ltac:(rewrite A5, A3; right; left; reflexivity) HR);
unfold S1; cbn; try reflexivity.
- rewrite EcM. exact (same_io_wvb md2 matV IO2).
Qed.
End h.
End f.
End d.
