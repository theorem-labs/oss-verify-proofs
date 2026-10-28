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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1w AE3d AB1q AFhy AFhz AFi0 AFi4 AFi9 AB1h AFjm AFid AFie AFif AFig AFjv AFjw AFjx AFjh AFjn AFjo AFjk AFjl AFjp.
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
s_runS HR tfibtbl_rtA tfibtbl_rtA_ok 0x97698 U_M5 HX HP4.
s_memsetR HR U_Q sM5 constr:(SMv + 768) constr:(N8D / 8) 0 0x319d8 OK4 RS.
{ clear - M1 M2 M3 Z8 A7 MZ. U_zevS. rewrite (eq_refl : ew E0 47 = w64 SHBv), EaMAP. unfold w64, AFjm.SHBv in *. rewrite !unsigned_lit_small by zlia.
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
s_runS HR tfibtbl_rtA tfibtbl_rtA_ok 0x97698 Ue_MF HX HP5.
s_memsetR HR (ss_after_stretch Ue_MF (ss_mem Ue_MF) sMF CLOB_MS 0x31c00) sMF constr:(Uv) 4096 190 0x31c00 OK5 RS.
{ clear - M1 M2 Z8 B5 MZ. U_zevS. rewrite EaMAP. unfold w64. rewrite !unsigned_lit_small by zlia. zcanon_simp. zlia. }
{ clear. U_zevS. reflexivity. }
{ left. clear - Z8 B5 MZ. zlia. }
apply (PSR_runs Wy md1 X _ SH6 (PDX Wy RX z)) in HR; [|exact SH6_of_cut].
s_runS HR tfibtbl_rtA tfibtbl_rtA_ok 0x31c28 (runto 0x31c28 (ss_after_stretch Ue_MF (ss_mem Ue_MF) sMF CLOB_MS 0x31c00)) HX HP6.
s_arm HR BC_EQ false (SOff aMAP 6128) (SOff aMAP 4096).
{ clear - M1 M2 Z8 MZ. arm_zevS. rewrite EaMAP. unfold w64. rewrite !unsigned_lit_small by zlia. zcanon_simp. apply Z.eqb_neq. zlia. }
s_runS HR tfibtbl_rtA tfibtbl_rtA_ok 0x31c30 (runto 0x31c30 (arm BC_EQ false (SOff aMAP 6128) (SOff aMAP 4096) (runto 0x31c28 (ss_after_stretch Ue_MF (ss_mem Ue_MF) sMF CLOB_MS 0x31c00)))) HX HP6.
s_arm HR BC_LTU false (SOff aMAP 6128) (SOff aMAP 4112).
{ clear - M1 M2 Z8 MZ. arm_zevS. rewrite EaMAP. unfold w64. rewrite !unsigned_lit_small by zlia. zcanon_simp. apply Z.ltb_ge. zlia. }
s_runS HR tfibtbl_rtA tfibtbl_rtA_ok 0x52c5c Ue_RET HX HP6.
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
s_runS HR tfibtbl_rtA tfibtbl_rtA_ok 0x31a04 Uo_L6 HX HP5.
s_ladderM s_runS HR tfibtbl_rtA tfibtbl_rtA_ok 0x31a68 Uo_L6lo Uo_L6h Uo_L6h2 Uo_L6hi Uo_P0 sL6 CLOB_L6 HX HP5.
s_pin HR (10%bv : bv 5) (SOff aPBS 0).
{ clear - M1 M2 M3 Z8 Z4 Z5 NR A7 B4 MZ. pin_zevS. rewrite EaPB, (eq_refl : ew E0 47 = w64 SHBv), EaMAP, EaN8D. unfold w64, AFjm.SHBv in *.
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
pose proof (proj1 (forallb_forall _ _) (eq_refl : forallb (fun r => skel_okb false (skel r) && (YP09.r_lo r <? YP09.r_hi r)) l = true) r2 Hr2) as CK end.
cbn beta in CK. apply andb_prop in CK as [CK1 CK2]. apply Z.ltb_lt in CK2.
pose proof (skel_apart E' false PBv 1 HE ltac:(right; clear - B4 B1 A2 A3 A5 A6 MZ; zlia) ltac:(intros XX; discriminate XX) r2 CK1) as AP. clear - AP CK2 MZ. zlia. }
s_station HR Uo_P.
apply (at_S_weaken Wy md1 X X _ (PT SH5o (PDX Wy RX z)) Uo_P) in HR; [| intros a Ha; exact Ha |].
2:{ intros m [(HB & HM & HSH & HRs) HQ]. split; [exact HB|]. split; [exact HM|]. split; [intros a Ha _; exact (HSH a Ha)|]. split; [|exact HQ].
unfold SH5o. unfold SH5 in HRs.
pose proof (Forall_inv HRs) as C1. pose proof (Forall_inv (Forall_inv_tail HRs)) as C2. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HRs))) as C3.
pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail HRs)))) as C4. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail HRs))))) as C5.
repeat (apply Forall_cons); [exact C1 | exact C2 | exact C3 | exact C4 | | apply Forall_nil].
intros a Ha. apply C5. cbn [fst snd] in *. clear - Ha B4 MZ. zlia. }
s_runT HR tfibtbl_rtA tfibtbl_rtA_ok 0x97698 Uo_MF HXT HT5.
lazymatch type of HR with at_S ?Wx ?md ?X0 ?P ?ss ?W' ?c' =>
eapply SRr_bind;
[ eapply (at_S_memset Wx md X0 P (PT SH6o (PDX Wy RX z)) ss W' c' sMF (SOff aMAP 6144) (SLit 4096) Uv 4096 190 0x31c00 HR eq_refl ltac:(vm_compute; reflexivity) ltac:(unfold sHAV, sMF; zlia)
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
- intros i Hi. eapply val_mem_frame; [|exact (HB i Hi)]. intros kk Hkk. pose proof tr_length as LEN.
pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7). destruct Hsp as (S1 & _ & S3 & _). pose proof (u64_range (getr regs0 2)) as U2.
apply FR'; [clear - Hi Hkk LEN T7 S1 S3 U2 MZ; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, IFRAME, ASTACK, kHighMemBeg in *; unfold sp0 in *; zlia|]. intros Hin.
apply (runs_not_stack (sp0 - IFRAME + 16 + 8 * Z.of_nat i + Z.of_nat kk)); [left; clear - Hin B5 Z8 MZ; zlia | clear - Hi Hkk LEN MZ; unfold IFRAME, ASTACK; zlia].
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
lazymatch type of HR with at_S _ _ _ _ ?ss2 _ _ => replace ss2 with (ss_after_stretch Uo_MF (ss_mem Uo_MF) sMF CLOB_MS 0x31c00) in HR by (vm_compute; reflexivity) end.
s_runT HR tfibtbl_rtA tfibtbl_rtA_ok 0x31c28 (runto 0x31c28 (ss_after_stretch Uo_MF (ss_mem Uo_MF) sMF CLOB_MS 0x31c00)) HXT HT6.
s_arm HR BC_EQ false (SOff aMAP 6128) (SOff aMAP 4096).
{ clear - M1 M2 Z8 MZ. arm_zevS. rewrite EaMAP. unfold w64. rewrite !unsigned_lit_small by zlia. zcanon_simp. apply Z.eqb_neq. zlia. }
s_runT HR tfibtbl_rtA tfibtbl_rtA_ok 0x31c30 (runto 0x31c30 (arm BC_EQ false (SOff aMAP 6128) (SOff aMAP 4096) (runto 0x31c28 (ss_after_stretch Uo_MF (ss_mem Uo_MF) sMF CLOB_MS 0x31c00)))) HXT HT6.
s_arm HR BC_LTU false (SOff aMAP 6128) (SOff aMAP 4112).
{ clear - M1 M2 Z8 MZ. arm_zevS. rewrite EaMAP. unfold w64. rewrite !unsigned_lit_small by zlia. zcanon_simp. apply Z.ltb_ge. zlia. }
s_runT HR tfibtbl_rtA tfibtbl_rtA_ok 0x52c5c Uo_RET HXT HT6.
apply SRr_ret. exact HR.
Qed.
End U.
End g.
End f.
