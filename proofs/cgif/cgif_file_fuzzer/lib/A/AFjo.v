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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1w AE3d AB1q AFhy AFhz AFi0 AFi4 AFi9 AB1h AFjm AFjv AFjw AFjx AFjh AFjn.
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
Definition WIN1S (a : Z) : Prop := WIN1P a \/ (QSv <= a < QSv + 8) \/ (mb <= a < mb + 6144).
Definition WSKEL1S : list (option nat * Z * Z) := WSKEL1P ++ [(Some aQS, 0, 8); (Some aMAP, 0, 6144)].
Lemma WIN1S_WIN1T : forall a, WIN1S a -> WIN1T a.
Proof. clearP. intros a [H|[H|H]]; [left | right; left | right; right; left]; exact H. Qed.
Lemma WIN1S_WIN : forall a, WIN1S a -> WIN a.
Proof. intros a H. exact (WIN1T_WIN a (WIN1S_WIN1T a H)). Qed.
Lemma windows_WIN1S : forall (E : env) rs a,
(forall k, (k < sHAV)%nat -> ew E k = ew E0 k) -> wins_ok WSKEL1S rs = true -> in_wrange E rs a -> WIN1S a.
Proof.
intros E rs a HE. apply windows_in. intros t x Ht Hx. unfold WSKEL1S in Ht. apply in_app_iff in Ht as [Ht|Ht].
- left. exact (WSKEL1P_WIN1P E x t HE Ht Hx).
- right. pose proof high_facts as (_ & _ & _ & _ & _ & _ & _ & _ & F9 & F10 & _).
pose proof map_facts as (M1 & M2 & _). pose proof map_zoneN as MZ. pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & _). pose proof Hidx as HI. pose proof Nrange as NR.
unfold in_win in Hx. cbn [In] in Ht.
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kPtrArrayResv, kMaxNumChunks, MALLOC_MAX, sHAV, aQS, aMAP in *.
clear - HE Hx Ht F9 F10 M1 M2 Z8 HI NR MZ.
destruct Ht as [<-|[<-|[]]]; cbn [fst snd base_val] in Hx; rewrite HE in Hx by zlia.
+ rewrite EaQS in Hx. unfold w64 in Hx. unfold QSv in *. rewrite unsigned_lit_small in Hx by zlia. left. zlia.
+ rewrite EaMAP in Hx. unfold w64 in Hx. rewrite unsigned_lit_small in Hx by zlia. right. zlia.
Qed.
Lemma mid_not_WIN1S : forall a, sp0 - IFRAME <= a < sp0 - 64 -> ~ WIN1S a.
Proof. intros a Ha Hw. exact (mid_not_WIN1T a Ha (WIN1S_WIN1T a Hw)). Qed.
Lemma at_S_runS : forall (Wx : world tfibsegs) tbl (tblok : table_ok tfibsegs tbl) stop md X P ss ss' st W' c',
at_S Wx md X P ss W' c' ->
sym_run_toN_sh tfibsegs tbl FUEL stop ss = (ss', st) -> match st with RS_ecall => False | _ => True end ->
(forall a, WIN1S a -> X a) -> wins_ok WSKEL1S (ss_mem ss) = true -> pstable WIN1S P -> stack_shaped ss' = true ->
SRr tfibsegs W' c' (at_S Wx md X P ss').
Proof. exact (at_S_run_gen WSKEL1S WIN1S windows_WIN1S mid_not_WIN1S). Qed.
Lemma at_S_run_ecallS : forall (Wx : world tfibsegs) tbl (tblok : table_ok tfibsegs tbl) stop md X P ss ss' W' c',
at_S Wx md X P ss W' c' ->
sym_run_toN_sh tfibsegs tbl FUEL stop ss = (ss', RS_ecall) -> ss_resv ss' = None ->
(forall a, WIN1S a -> X a) -> wins_ok WSKEL1S (ss_mem ss) = true -> pstable WIN1S P -> stack_shaped ss' = true ->
SRr tfibsegs W' c' (at_N Wx md X P ss').
Proof. exact (at_S_run_ecall_gen WSKEL1S WIN1S windows_WIN1S mid_not_WIN1S). Qed.
Definition brun (m : word -> option byte) (r : Z * Z * Z) : Prop :=
forall a, fst (fst r) <= a < snd (fst r) -> m (w64 a) = Some (Z_to_bv 8 (snd r)).
Definition run_ok (r : Z * Z * Z) : Prop :=
(mb + 6144 <= fst (fst r) /\ snd (fst r) <= mb + MSv) \/ (SMv <= fst (fst r) /\ snd (fst r) <= SMv + MSv / 8).
Definition PS (Wy : world tfibsegs) (sh : list (Z * Z * Z)) (m : word -> option byte) : Prop :=
PBUFW Wy m /\
(forall a, mb + 6144 <= a < mb + MSv -> apresent (w_H Wy) m a) /\
(forall a, SMv <= a < SMv + MSv / 8 -> apresent (w_H Wy) m a) /\
Forall (brun m) sh.
Lemma runs_not_WIN1S : forall a, (mb + 6144 <= a < mb + MSv) \/ (SMv <= a < SMv + MSv / 8) -> ~ WIN1S a.
Proof.
intros a Ha Hw. pose proof high_facts as (F1 & F2 & _ & _ & _ & _ & _ & _ & F9 & F10 & _).
pose proof map_facts as (M1 & M2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _). pose proof map_zoneN as MZ. pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & _).
pose proof Hidx as HI. pose proof Nrange as NR. pose proof BSLv_range as HB. pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7). pose proof (lo_stk_ceil ly LY) as SC.
destruct Hsp as (S1 & _ & S3 & _). destruct Hmap_apart as (MT & _ & _ & MQ & _). unfold zdisjoint in MT, MQ. cbn [fst snd] in MT, MQ.
clear - Ha Hw F1 F2 F9 F10 M1 M2 SM1 SM2 Z8 HI NR HB T7 SC S1 S3 MT MQ MZ.
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, WIN1S, WIN1P, WINT, WINI, QSv, kHighMemBeg, kHighShadowBeg, kHighShadowEnd, ASAN_CEIL, kThreadObjSize, kPtrArrayResv, kMaxNumChunks, MALLOC_MAX, ASTACK, IFRAME, t_unwinding, TFIB_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex in *. unfold T, Qb in *. zlia.
Qed.
Lemma runs_not_stack : forall a, (mb + 6144 <= a < mb + MSv) \/ (SMv <= a < SMv + MSv / 8) -> ~ (sp0 - ASTACK <= a < sp0).
Proof.
intros a Ha Hs. pose proof map_facts as (M1 & M2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _). pose proof map_zoneN as MZ.
pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7). destruct Hsp as (S1 & _ & S3 & _).
destruct Hmap_apart as (_ & _ & _ & _ & _ & _ & MS). unfold zdisjoint in MS. cbn [fst snd] in MS.
clear - Ha Hs M1 M2 SM1 SM2 T7 S1 S3 MS MZ. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighShadowBeg, kHighShadowEnd, ASAN_CEIL, ASTACK in *. zlia.
Qed.
Lemma PS_stable : forall Wy sh, Forall run_ok sh -> pstable WIN1S (PS Wy sh).
Proof.
intros Wy sh Hsh m m' FR (HB & HM & HSH & HR).
assert (U : forall a, (mb + 6144 <= a < mb + MSv) \/ (SMv <= a < SMv + MSv / 8) -> m' (w64 a) = m (w64 a)).
{ intros a Ha. pose proof map_facts as (M1 & M2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _). pose proof map_zoneN as MZ.
apply FR. unfold w64. rewrite unsigned_lit_small by (clear - Ha M1 M2 SM1 SM2 MZ; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighShadowBeg, kHighShadowEnd, ASAN_CEIL in *; zlia).
exact (runs_not_WIN1S a Ha). }
split; [exact (PBUFW_stableT Wy m m' (fun x Hx => FR x (fun Hw => Hx (WIN1S_WIN1T _ Hw))) HB)|].
split; [intros a Ha; apply (apresent_same (w_H Wy) m); [exact (U a (or_introl Ha)) | exact (HM a Ha)]|].
split; [intros a Ha; apply (apresent_same (w_H Wy) m); [exact (U a (or_intror Ha)) | exact (HSH a Ha)]|].
apply Forall_forall. intros r Hr a Ha. pose proof (proj1 (Forall_forall _ _) Hsh r Hr) as OK. pose proof (proj1 (Forall_forall _ _) HR r Hr a Ha) as V.
rewrite (U a); [exact V|]. unfold run_ok in OK. clear - OK Ha. zlia.
Qed.
Definition cut1 (d e : Z) (r : Z * Z * Z) : list (Z * Z * Z) :=
let lo := fst (fst r) in let hi := snd (fst r) in let v := snd r in
(if lo <? d then [(lo, Z.min hi d, v)] else []) ++ (if e <? hi then [(Z.max lo e, hi, v)] else []).
Definition cut (d e : Z) (sh : list (Z * Z * Z)) : list (Z * Z * Z) := flat_map (cut1 d e) sh.
Lemma cut_sound : forall m m' d e sh,
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < e) -> m' (w64 a) = m (w64 a)) -> Forall run_ok sh -> Forall (brun m) sh -> Forall (brun m') (cut d e sh).
Proof.
intros m m' d e sh FR OK H. pose proof map_facts as (M1 & M2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _). pose proof map_zoneN as MZ.
unfold cut. apply Forall_flat_map. apply Forall_forall. intros r Hr.
pose proof (proj1 (Forall_forall _ _) H r Hr) as BR. pose proof (proj1 (Forall_forall _ _) OK r Hr) as RO. unfold run_ok in RO.
unfold cut1. destruct r as [[lo hi] v]. cbn [fst snd] in *.
assert (A64 : forall a, lo <= a < hi -> 0 <= a < 2 ^ 64) by (intros a Ha; clear - Ha RO M1 M2 SM1 SM2 MZ; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighShadowBeg, kHighShadowEnd, ASAN_CEIL in *; zlia).
clear M1 M2 SM1 SM2 RO. apply Forall_app. split.
- destruct (lo <? d) eqn:E1; [|apply Forall_nil]. apply Z.ltb_lt in E1. apply Forall_cons; [|apply Forall_nil].
intros a Ha. cbn [fst snd] in Ha. rewrite FR by (try apply A64; zlia). apply BR. cbn [fst snd]. zlia.
- destruct (e <? hi) eqn:E2; [|apply Forall_nil]. apply Z.ltb_lt in E2. apply Forall_cons; [|apply Forall_nil].
intros a Ha. cbn [fst snd] in Ha. rewrite FR by (try apply A64; zlia). apply BR. cbn [fst snd]. zlia.
Qed.
Lemma cut_ok : forall d e sh, Forall run_ok sh -> Forall run_ok (cut d e sh).
Proof.
clearP. intros d e sh H. unfold cut. apply Forall_flat_map. apply Forall_forall. intros r Hr.
pose proof (proj1 (Forall_forall _ _) H r Hr) as OK. unfold cut1, run_ok in *. destruct r as [[lo hi] v]. cbn [fst snd] in *.
apply Forall_app. split.
- destruct (lo <? d) eqn:E1; [|apply Forall_nil]. apply Z.ltb_lt in E1. apply Forall_cons; [cbn [fst snd]; zlia | apply Forall_nil].
- destruct (e <? hi) eqn:E2; [|apply Forall_nil]. apply Z.ltb_lt in E2. apply Forall_cons; [cbn [fst snd]; zlia | apply Forall_nil].
Qed.
Lemma at_S_memsetS : forall (Wy : world tfibsegs) md X sh ss W' c' (k : nat) (ed el : sv) (d len vb retpc : Z),
at_S Wy md X (PS Wy sh) ss W' c' -> ss_resv ss = None -> ss_pc ss = tfib_A_musl_memset -> (sHAV <= k)%nat ->
ss_atoms_lt k ss = true -> no_cdata (ss_mem ss) = true ->
sr_get (ss_regs ss) 10%bv = ed -> sr_get (ss_regs ss) 12%bv = el -> sr_get (ss_regs ss) 11%bv = SLit vb -> sr_get (ss_regs ss) 1%bv = SLit retpc ->
sv_atoms_lt sHAV ed = true -> sv_atoms_lt sHAV el = true -> U E0 ed = d -> U E0 el = len ->
0 <= len -> retpc mod 4 = 0 -> 0 <= retpc < 2 ^ 64 -> 0 <= vb < 256 ->
((mb + 6144 <= d /\ d + len <= mb + MSv) \/ (SMv <= d /\ d + len <= SMv + MSv / 8)) -> Forall run_ok sh ->
(forall a, d <= a < d + len -> X a) ->
(forall (E' : env), env_agree sHAV E0 E' ->
forall r, In r (ss_mem ss) -> base_val E' (YP09.r_base r) + YP09.r_hi r <= d \/ d + len <= base_val E' (YP09.r_base r) + YP09.r_lo r
\/ YP09.r_hi r <= YP09.r_lo r) ->
(forall (E' : env), env_agree sHAV E0 E' ->
forall r a, In r (ss_mem ss) -> base_val E' (YP09.r_base r) + YP09.r_lo r <= a < base_val E' (YP09.r_base r) + YP09.r_hi r -> 0 <= a < 2 ^ 64) ->
SRr tfibsegs W' c' (at_S Wy md X (PS Wy ((d, d + len, vb) :: cut d (d + len) sh)) (ss_after_stretch ss (ss_mem ss) k CLOB_MS retpc)).
Proof.
intros Wy md X sh ss W' c' k ed el d len vb retpc HR Hrv Hpc Hk Hat Hnc H10 H12 H11 H1 Aed Ael Ud Ul Hlen Hrpc Hrpc' Hvb Hplace Hsh HX HEXT H64.
pose proof map_facts as (M1 & M2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _). pose proof map_zoneN as MZ.
assert (Hd : TFIB_IMG_END <= d /\ d + len < 2 ^ 64) by (clear - Hplace Hlen M1 M2 SM1 SM2 MZ; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END, kHighMemBeg, kHighShadowBeg, kHighShadowEnd, ASAN_CEIL in *; zlia).
eapply (SRr_mono tfibsegs W' c' _ _
(at_S_memset Wy md X (PS Wy sh) (PS Wy ((d, d + len, vb) :: cut d (d + len) sh)) ss W' c' k ed el d len vb retpc HR Hrv Hpc Hk Hat Hnc H10 H12 H11 H1 Aed Ael Ud Ul
Hlen (proj1 Hd) (proj2 Hd) Hrpc Hrpc' Hvb _ HEXT H64 _)).
{ intros W2 c2 _ HA. eapply at_S_weaken; [exact HA | intros a [Ha|Ha]; [exact Ha | exact (HX a Ha)] | intros m Hm; exact Hm]. }
Unshelve.
- intros m MEQ (HB & HM & HSH & HRs) a Ha. destruct Hplace as [[P1 P2]|[P1 P2]]; [apply HM; zlia | apply HSH; zlia].
- intros m m' MEQ (HB & HM & HSH & HRs) FR FILL.
assert (FR' : forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + len) -> m' (w64 a) = m (w64 a)).
{ intros a Ha Hna. apply FR. unfold w64. rewrite unsigned_lit_small by exact Ha. exact Hna. }
assert (FILL' : forall a, d <= a < d + len -> m' (w64 a) = Some (Z_to_bv 8 vb)).
{ intros a Ha. apply FILL. unfold w64. rewrite unsigned_lit_small by (clear - Ha Hd Hplace M1 SM1 MZ; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END, kHighMemBeg, kHighShadowBeg in *; zlia). exact Ha. }
assert (RP : forall a, (mb + 6144 <= a < mb + MSv) \/ (SMv <= a < SMv + MSv / 8) -> apresent (w_H Wy) m a -> apresent (w_H Wy) m' a).
{ intros a Hrng [Hh [b Hb]]. split; [exact Hh|].
assert (A64 : 0 <= a < 2 ^ 64) by (clear - Hrng M1 M2 SM1 SM2 MZ; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighShadowBeg, kHighShadowEnd, ASAN_CEIL in *; zlia).
destruct (Z_lt_le_dec a d) as [L|GE].
- exists b. exact (eq_trans (FR' a A64 ltac:(zlia)) Hb).
- destruct (Z_lt_le_dec a (d + len)) as [L2|GE2]; [exists (Z_to_bv 8 vb); exact (FILL' a ltac:(zlia)) | exists b; exact (eq_trans (FR' a A64 ltac:(zlia)) Hb)]. }
split; [|split; [|split]].
+ intros i Hi. eapply val_mem_frame; [|exact (HB i Hi)]. intros kk Hkk. pose proof tr_length as LEN.
pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7). destruct Hsp as (S1 & _ & S3 & _). pose proof (u64_range (getr regs0 2)) as U2.
apply FR'; [clear - Hi Hkk LEN T7 S1 S3 U2 MZ; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, IFRAME, ASTACK, kHighMemBeg in *; unfold sp0 in *; zlia|]. intros Hin.
apply (runs_not_stack (sp0 - IFRAME + 16 + 8 * Z.of_nat i + Z.of_nat kk)); [clear - Hin Hplace MZ; zlia | clear - Hi Hkk LEN MZ; unfold IFRAME, ASTACK; zlia].
+ intros a Ha. apply RP; [left; exact Ha | exact (HM a Ha)].
+ intros a Ha. apply RP; [right; exact Ha | exact (HSH a Ha)].
+ apply Forall_cons; [intros a Ha; cbn [fst snd] in Ha; exact (FILL' a Ha) | exact (cut_sound m m' d (d + len) sh FR' Hsh HRs)].
Qed.
Definition skel_okb (pb : bool) (s : option nat * Z * Z * Z * Z) : bool :=
match s with (b, lo, hi, _, _) =>
match b with
| None => (0 <=? lo) && (hi <=? 0x5fb000)
| Some k => (Nat.eqb k 2 && (- ASTACK <=? lo) && (hi <=? 0))
|| (Nat.eqb k 32 && (0 <=? lo) && (hi <=? kThreadObjSize))
|| (Nat.eqb k 33 && (0 <=? lo) && (hi <=? 256))
|| (Nat.eqb k aMAP && (0 <=? lo) && (hi <=? 6144))
|| (Nat.eqb k aQS && (0 <=? lo) && (hi <=? 8))
|| (Nat.eqb k aBSL && (0 <=? lo) && (hi <=? 8))
|| (pb && Nat.eqb k aPBS && (0 <=? lo) && (hi <=? 1))
end
end.
Lemma skel_cases : forall pb b lo hi wlo whi, skel_okb pb (b, lo, hi, wlo, whi) = true ->
(b = None /\ 0 <= lo /\ hi <= 0x5fb000) \/ (b = Some 2%nat /\ - ASTACK <= lo /\ hi <= 0) \/ (b = Some 32%nat /\ 0 <= lo /\ hi <= kThreadObjSize) \/
(b = Some 33%nat /\ 0 <= lo /\ hi <= 256) \/ (b = Some aMAP /\ 0 <= lo /\ hi <= 6144) \/ (b = Some aQS /\ 0 <= lo /\ hi <= 8) \/
(b = Some aBSL /\ 0 <= lo /\ hi <= 8) \/ (pb = true /\ b = Some aPBS /\ 0 <= lo /\ hi <= 1).
Proof.
clearP. intros pb b lo hi wlo whi H. unfold skel_okb in H. destruct b as [k|].
- repeat (apply Bool.orb_prop in H; destruct H as [H|H]);
repeat (apply andb_prop in H; destruct H as [H ?HH]);
repeat match goal with X : (_ <=? _) = true |- _ => apply Z.leb_le in X | X : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in X; subst end.
all: first [ right; left; repeat split; assumption | right; right; left; repeat split; assumption | right; right; right; left; repeat split; assumption
| right; right; right; right; left; repeat split; assumption | right; right; right; right; right; left; repeat split; assumption
| right; right; right; right; right; right; left; repeat split; assumption
| right; right; right; right; right; right; right; repeat split; assumption ].
- apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. left. repeat split; assumption.
Qed.
Lemma skel_apart : forall (E' : env) (pb : bool) d len, env_agree sHAV E0 E' ->
((mb + 6144 <= d /\ d + len <= mb + MSv) \/ (SMv <= d /\ d + len <= SMv + MSv / 8)) ->
(pb = true -> d + len <= PBv \/ PBv + 1 <= d) ->
forall r, skel_okb pb (skel r) = true ->
base_val E' (YP09.r_base r) + YP09.r_hi r <= d \/ d + len <= base_val E' (YP09.r_base r) + YP09.r_lo r \/ YP09.r_hi r <= YP09.r_lo r.
Proof.
intros E' pb d len [HE _] Hplace Hpb r Hs. destruct r as [b lo hi wlo whi cs]. unfold skel in Hs. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi] in *.
pose proof high_facts as (F1 & F2 & _ & _ & _ & _ & F7 & F8 & F9 & F10 & _).
pose proof map_facts as (M1 & M2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _ & PB & _). pose proof map_zoneN as MZ. pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & _).
pose proof Hidx as HI. pose proof Nrange as NR. pose proof BSLv_range as HB. pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7). pose proof (lo_stk_ceil ly LY) as SC.
destruct Hsp as (S1 & _ & S3 & _). destruct Hmap_apart as (MT & MC & _ & MQ & _ & _ & MS). unfold zdisjoint in MT, MC, MQ, MS. cbn [fst snd] in MT, MC, MQ, MS.
pose proof (u64_range (getr regs0 2)) as U2.
destruct (Z_le_gt_dec hi lo) as [Hemp|Hne]; [right; right; exact Hemp|].
destruct (skel_cases pb b lo hi wlo whi Hs) as [(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|(Epb & -> & A1 & A2)]]]]]]]; cbn [base_val].
- clear - Hplace A1 A2 M1 SM1 MZ. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighShadowBeg in *. zlia.
- rewrite (HE 2%nat ltac:(unfold sHAV; zlia)), E2. pose proof (runs_not_stack) as RS.
destruct Hplace as [[P1 P2]|[P1 P2]].
+ clear - P1 P2 A1 A2 MS S1 S3 Hne U2 Z8 MZ. unfold ASTACK in *. unfold sp0 in *. destruct MS as [MS|MS]; [right; left; zlia | left; zlia].
+ right; left. clear - P1 P2 A1 A2 SM1 SM2 T7 S1 U2 MZ. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighShadowEnd, kHighMemBeg, ASTACK in *. unfold sp0 in *. zlia.
- rewrite (HE 32%nat ltac:(unfold sHAV; zlia)), EaT. unfold w64. rewrite unsigned_lit_small by (clear - F1 F2 MZ; numconst; try unfold T in *; zlia).
clear - Hplace A1 A2 MT F1 F2 M1 M2 SM1 SM2 Hne MZ. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighShadowBeg, kHighShadowEnd, ASAN_CEIL, kThreadObjSize in *. try unfold T in *.
destruct Hplace as [[P1 P2]|[P1 P2]]; [destruct MT as [MT|MT]; [right; left; zlia | left; zlia] | zlia ].
- rewrite (HE 33%nat ltac:(unfold sHAV; zlia)), EaC. unfold w64. rewrite unsigned_lit_small by (clear - F7 F8 MZ; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; zlia).
clear - Hplace A1 A2 MC F7 F8 M1 M2 SM1 SM2 Hne MZ. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighShadowBeg, kHighShadowEnd, ASAN_CEIL, kCtxMapSize in *.
destruct Hplace as [[P1 P2]|[P1 P2]]; [destruct MC as [MC|MC]; [right; left; zlia | left; zlia] | zlia ].
- unfold aMAP. rewrite (HE 45%nat ltac:(unfold sHAV; zlia)), EaMAP. unfold w64. rewrite unsigned_lit_small by (clear - M1 M2 Z8 MZ; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; zlia).
clear - Hplace A1 A2 M1 M2 SM1 SM2 Z8 Hne MZ. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighShadowBeg, kHighShadowEnd, ASAN_CEIL in *. zlia.
- unfold aQS. rewrite (HE 52%nat ltac:(unfold sHAV; zlia)), EaQS. unfold w64. unfold QSv in *. rewrite unsigned_lit_small by (clear - F9 F10 HI MZ; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kPtrArrayResv, kMaxNumChunks in *; try unfold Qb in *; zlia).
clear - Hplace A1 A2 MQ F9 F10 HI M1 M2 SM1 SM2 Hne MZ. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighShadowBeg, kHighShadowEnd, ASAN_CEIL, kPtrArrayResv, kMaxNumChunks in *. try unfold Qb in *.
destruct Hplace as [[P1 P2]|[P1 P2]]; [destruct MQ as [MQ|MQ]; [right; left; zlia | left; zlia] | zlia ].
- unfold aBSL. rewrite (HE 55%nat ltac:(unfold sHAV; zlia)), EaBSL. unfold w64. rewrite unsigned_lit_small by (clear - HB MZ; unfold TFIB_INST in *; zlia).
clear - Hplace A1 A2 HB M1 SM1 Hne MZ. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighShadowBeg, TFIB_INST in *. zlia.
- unfold aPBS. rewrite (HE 66%nat ltac:(unfold sHAV; zlia)), EaPB. unfold w64. rewrite PB in *.
pose proof size_facts as (_ & _ & Z3 & Z4 & _ & _ & Z7 & _ & _ & Z10 & _).
assert (HND : 8 * (N8D / 8) <= N8D) by (apply Z.mul_div_le; zlia). assert (HM : N8D / 8 + 1024 <= MSv / 8) by (apply Z.div_le_lower_bound; zlia).
pose proof (Z.div_pos N8D 8 ltac:(zlia) ltac:(zlia)) as DP.
rewrite unsigned_lit_small by (clear - SM1 SM2 HND HM DP MZ; unfold kHighShadowBeg, kHighShadowEnd in *; zlia).
specialize (Hpb Epb). clear - Hplace Hpb A1 A2 M1 M2 SM1 SM2 HND HM DP Hne MZ. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighShadowBeg, kHighShadowEnd, ASAN_CEIL in *. zlia.
Qed.
Lemma skel_u64 : forall (E' : env) (pb : bool) r a, env_agree sHAV E0 E' -> skel_okb pb (skel r) = true ->
base_val E' (YP09.r_base r) + YP09.r_lo r <= a < base_val E' (YP09.r_base r) + YP09.r_hi r -> 0 <= a < 2 ^ 64.
Proof.
intros E' pb r a [HE _] Hs Ha. destruct r as [b lo hi wlo whi cs]. unfold skel in Hs. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi] in *.
pose proof high_facts as (F1 & F2 & _ & _ & _ & _ & F7 & F8 & F9 & F10 & _).
pose proof map_facts as (M1 & M2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _ & PB & _). pose proof map_zoneN as MZ. pose proof size_facts as (_ & _ & Z3 & Z4 & _ & _ & Z7 & Z8 & _ & Z10 & _).
pose proof Hidx as HI. pose proof Nrange as NR. pose proof BSLv_range as HB. pose proof (lo_top ly LY) as (_ & _ & _ & T4 & _ & _ & T7).
destruct Hsp as (S1 & _ & S3 & _). pose proof (u64_range (getr regs0 2)) as U2.
destruct (skel_cases pb b lo hi wlo whi Hs) as [(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|(Epb & -> & A1 & A2)]]]]]]]; cbn [base_val] in Ha.
- clear - Ha A1 A2 MZ. zlia.
- rewrite (HE 2%nat ltac:(unfold sHAV; zlia)), E2 in Ha. clear - Ha A1 A2 S1 S3 T4 T7 U2 MZ. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASTACK in *. unfold sp0 in *. zlia.
- rewrite (HE 32%nat ltac:(unfold sHAV; zlia)), EaT in Ha. unfold w64 in Ha. rewrite unsigned_lit_small in Ha by (clear - F1 F2 MZ; numconst; try unfold T in *; zlia).
clear - Ha A1 A2 F1 F2 MZ. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize in *. try unfold T in *. zlia.
- rewrite (HE 33%nat ltac:(unfold sHAV; zlia)), EaC in Ha. unfold w64 in Ha. rewrite unsigned_lit_small in Ha by (clear - F7 F8 MZ; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; zlia).
clear - Ha A1 A2 F7 F8 MZ. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. zlia.
- unfold aMAP in Ha. rewrite (HE 45%nat ltac:(unfold sHAV; zlia)), EaMAP in Ha. unfold w64 in Ha. rewrite unsigned_lit_small in Ha by (clear - M1 M2 Z8 MZ; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; zlia).
clear - Ha A1 A2 M1 M2 Z8 MZ. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. zlia.
- unfold aQS in Ha. rewrite (HE 52%nat ltac:(unfold sHAV; zlia)), EaQS in Ha. unfold w64 in Ha. unfold QSv in *. rewrite unsigned_lit_small in Ha by (clear - F9 F10 HI MZ; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kPtrArrayResv, kMaxNumChunks in *; try unfold Qb in *; zlia).
clear - Ha A1 A2 F9 F10 HI MZ. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kPtrArrayResv, kMaxNumChunks in *. try unfold Qb in *. zlia.
- unfold aBSL in Ha. rewrite (HE 55%nat ltac:(unfold sHAV; zlia)), EaBSL in Ha. unfold w64 in Ha. rewrite unsigned_lit_small in Ha by (clear - HB MZ; unfold TFIB_INST in *; zlia).
clear - Ha A1 A2 HB MZ. unfold TFIB_INST in *. zlia.
- unfold aPBS in Ha. rewrite (HE 66%nat ltac:(unfold sHAV; zlia)), EaPB in Ha. unfold w64 in Ha. rewrite PB in Ha.
assert (HND : 8 * (N8D / 8) <= N8D) by (apply Z.mul_div_le; zlia). assert (HM : N8D / 8 + 1024 <= MSv / 8) by (apply Z.div_le_lower_bound; zlia).
pose proof (Z.div_pos N8D 8 ltac:(zlia) ltac:(zlia)) as DP.
rewrite unsigned_lit_small in Ha by (clear - SM1 SM2 HND HM DP MZ; unfold kHighShadowBeg, kHighShadowEnd in *; zlia).
clear - Ha A1 A2 SM1 SM2 HND HM DP MZ. unfold kHighShadowBeg, kHighShadowEnd in *. zlia.
Qed.
Lemma memset_ext_of_skel : forall (pb : bool) d len ss,
forallb (fun r => skel_okb pb (skel r)) (ss_mem ss) = true ->
((mb + 6144 <= d /\ d + len <= mb + MSv) \/ (SMv <= d /\ d + len <= SMv + MSv / 8)) ->
(pb = true -> d + len <= PBv \/ PBv + 1 <= d) ->
forall (E' : env), env_agree sHAV E0 E' ->
forall r, In r (ss_mem ss) -> base_val E' (YP09.r_base r) + YP09.r_hi r <= d \/ d + len <= base_val E' (YP09.r_base r) + YP09.r_lo r
\/ YP09.r_hi r <= YP09.r_lo r.
Proof. intros pb d len ss Hb Hplace Hpb E' HE r Hr. exact (skel_apart E' pb d len HE Hplace Hpb r (proj1 (forallb_forall _ _) Hb r Hr)). Qed.
Lemma memset_u64_of_skel : forall (pb : bool) ss,
forallb (fun r => skel_okb pb (skel r)) (ss_mem ss) = true ->
forall (E' : env), env_agree sHAV E0 E' ->
forall r a, In r (ss_mem ss) -> base_val E' (YP09.r_base r) + YP09.r_lo r <= a < base_val E' (YP09.r_base r) + YP09.r_hi r -> 0 <= a < 2 ^ 64.
Proof. intros pb ss Hb E' HE r a Hr Ha. exact (skel_u64 E' pb r a HE (proj1 (forallb_forall _ _) Hb r Hr) Ha). Qed.
Definition WIN1R (a : Z) : Prop := WIN1P a \/ (mb <= a < mb + 6144).
Definition WSKEL1R : list (option nat * Z * Z) := WSKEL1P ++ [(Some aMAP, 0, 6144)].
Lemma WIN1R_WIN1S : forall a, WIN1R a -> WIN1S a.
Proof. clearP. intros a [H|H]; [left | right; right]; exact H. Qed.
Lemma WIN1R_WIN : forall a, WIN1R a -> WIN a.
Proof. intros a H. exact (WIN1S_WIN a (WIN1R_WIN1S a H)). Qed.
Lemma windows_WIN1R : forall (E : env) rs a,
(forall k, (k < sHAV)%nat -> ew E k = ew E0 k) -> wins_ok WSKEL1R rs = true -> in_wrange E rs a -> WIN1R a.
Proof.
intros E rs a HE. apply windows_in. intros t x Ht Hx. unfold WSKEL1R in Ht. apply in_app_iff in Ht as [Ht|Ht].
- left. exact (WSKEL1P_WIN1P E x t HE Ht Hx).
- right. pose proof map_facts as (M1 & M2 & _). pose proof map_zoneN as MZ. pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & _).
unfold in_win in Hx. cbn [In] in Ht. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, sHAV, aMAP in *. clear - HE Hx Ht M1 M2 Z8 MZ.
destruct Ht as [<-|[]]; cbn [fst snd base_val] in Hx; rewrite HE in Hx by zlia.
rewrite EaMAP in Hx. unfold w64 in Hx. rewrite unsigned_lit_small in Hx by zlia. zlia.
Qed.
Lemma mid_not_WIN1R : forall a, sp0 - IFRAME <= a < sp0 - 64 -> ~ WIN1R a.
Proof. intros a Ha Hw. exact (mid_not_WIN1S a Ha (WIN1R_WIN1S a Hw)). Qed.
Lemma at_S_runR : forall (Wx : world tfibsegs) tbl (tblok : table_ok tfibsegs tbl) stop md X P ss ss' st W' c',
at_S Wx md X P ss W' c' ->
sym_run_toN_sh tfibsegs tbl FUEL stop ss = (ss', st) -> match st with RS_ecall => False | _ => True end ->
(forall a, WIN1R a -> X a) -> wins_ok WSKEL1R (ss_mem ss) = true -> pstable WIN1R P -> stack_shaped ss' = true ->
SRr tfibsegs W' c' (at_S Wx md X P ss').
Proof. exact (at_S_run_gen WSKEL1R WIN1R windows_WIN1R mid_not_WIN1R). Qed.
Lemma at_S_run_ecallR : forall (Wx : world tfibsegs) tbl (tblok : table_ok tfibsegs tbl) stop md X P ss ss' W' c',
at_S Wx md X P ss W' c' ->
sym_run_toN_sh tfibsegs tbl FUEL stop ss = (ss', RS_ecall) -> ss_resv ss' = None ->
(forall a, WIN1R a -> X a) -> wins_ok WSKEL1R (ss_mem ss) = true -> pstable WIN1R P -> stack_shaped ss' = true ->
SRr tfibsegs W' c' (at_N Wx md X P ss').
Proof. exact (at_S_run_ecall_gen WSKEL1R WIN1R windows_WIN1R mid_not_WIN1R). Qed.
Definition PSR (Wy : world tfibsegs) (sh : list (Z * Z * Z)) (R : (word -> option byte) -> Prop) (m : word -> option byte) : Prop := PS Wy sh m /\ R m.
Definition rstable (R : (word -> option byte) -> Prop) : Prop :=
pstable WIN1R R /\
(forall (m m' : word -> option byte) d len, ((mb + 6144 <= d /\ d + len <= mb + MSv) \/ (SMv <= d /\ d + len <= SMv + MSv / 8)) ->
(forall x : word, ~ (d <= bv_unsigned x < d + len) -> m' x = m x) -> R m -> R m').
Lemma rstable_true : rstable (fun _ => True).
Proof. clearP. split; [intros m m' _ _; exact I | intros m m' d len _ _ _; exact I]. Qed.
Lemma PSR_stable : forall Wy sh R, Forall run_ok sh -> rstable R -> pstable WIN1R (PSR Wy sh R).
Proof.
intros Wy sh R OK [RF _] m m' FR [HP HQ]. split.
- exact (PS_stable Wy sh OK m m' (fun x Hx => FR x (fun Hw => Hx (WIN1R_WIN1S _ Hw))) HP).
- exact (RF m m' FR HQ).
Qed.
Definition QSP (Wy : world tfibsegs) (m : word -> option byte) : Prop := forall a, QSv <= a < QSv + 8 -> apresent (w_H Wy) m a.
Lemma QS_not_WIN1R : forall a, QSv <= a < QSv + 8 -> ~ WIN1R a.
Proof.
intros a Ha Hw. pose proof high_facts as (F1 & F2 & _ & _ & _ & _ & _ & _ & F9 & F10 & _ & _ & _ & _ & F15).
pose proof map_facts as (M1 & M2 & _). pose proof map_zoneN as MZ. pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & _). pose proof Hidx as HI.
pose proof BSLv_range as HB. destruct Hsp as (S1 & _ & S3 & _).
destruct Hmap_apart as (_ & _ & _ & MQ & _). pose proof HCX as (_ & _ & QT & _). unfold zdisjoint in MQ, QT. cbn [fst snd] in MQ, QT.
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, QSv, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kPtrArrayResv, kMaxNumChunks in *. unfold Qb in *.
destruct Hw as [[Hs|[Hs|[Ht|Hi]]]|Hm].
- destruct (F15 a) as (_ & _ & N3 & _); [clear - Hs S1 S3 MZ; unfold ASTACK, IFRAME in *; zlia | clear - N3 Ha HI MZ; zlia].
- destruct (F15 a) as (_ & _ & N3 & _); [clear - Hs S1 S3 MZ; unfold ASTACK, IFRAME in *; zlia | clear - N3 Ha HI MZ; zlia].
- clear - Ht Ha HI QT MZ. unfold WINT, t_unwinding in *. try unfold T in *. zlia.
- clear - Hi Ha HI HB F9 MZ. unfold WINI, TFIB_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex in *. zlia.
- clear - Hm Ha HI MQ Z8 MZ. zlia.
Qed.
Lemma QSP_rstable : forall Wy, rstable (QSP Wy).
Proof.
intros Wy. pose proof high_facts as (_ & _ & _ & _ & _ & _ & _ & _ & F9 & F10 & _). pose proof Hidx as HI.
pose proof map_facts as (M1 & M2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _). pose proof map_zoneN as MZ. pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & _).
destruct Hmap_apart as (_ & _ & _ & MQ & _). unfold zdisjoint in MQ. cbn [fst snd] in MQ.
assert (U64 : forall a, QSv <= a < QSv + 8 -> bv_unsigned (Z_to_bv 64 a) = a).
{ intros a Ha. apply unsigned_lit_small. clear - Ha F9 F10 HI MZ. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, QSv, kHighMemBeg, ASAN_CEIL, kPtrArrayResv, kMaxNumChunks in *. try unfold Qb in *. zlia. }
split.
- intros m m' FR HQ a Ha. apply (apresent_same (w_H Wy) m); [|exact (HQ a Ha)]. apply FR. rewrite (U64 a Ha). exact (QS_not_WIN1R a Ha).
- intros m m' d len Hplace FR HQ a Ha. apply (apresent_same (w_H Wy) m); [|exact (HQ a Ha)]. apply FR. rewrite (U64 a Ha). intros Hin.
clear - Ha Hin Hplace MQ HI F9 F10 M1 SM1 SM2 Z8 MZ. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, QSv, kHighMemBeg, kHighShadowBeg, kHighShadowEnd, ASAN_CEIL, kPtrArrayResv, kMaxNumChunks in *. try unfold Qb in *. zlia.
Qed.
Lemma at_S_memsetSR : forall (Wy : world tfibsegs) md X sh R ss W' c' (k : nat) (ed el : sv) (d len vb retpc : Z),
at_S Wy md X (PSR Wy sh R) ss W' c' -> rstable R -> ss_resv ss = None -> ss_pc ss = tfib_A_musl_memset -> (sHAV <= k)%nat ->
ss_atoms_lt k ss = true -> no_cdata (ss_mem ss) = true ->
sr_get (ss_regs ss) 10%bv = ed -> sr_get (ss_regs ss) 12%bv = el -> sr_get (ss_regs ss) 11%bv = SLit vb -> sr_get (ss_regs ss) 1%bv = SLit retpc ->
sv_atoms_lt sHAV ed = true -> sv_atoms_lt sHAV el = true -> U E0 ed = d -> U E0 el = len ->
0 <= len -> retpc mod 4 = 0 -> 0 <= retpc < 2 ^ 64 -> 0 <= vb < 256 ->
((mb + 6144 <= d /\ d + len <= mb + MSv) \/ (SMv <= d /\ d + len <= SMv + MSv / 8)) -> Forall run_ok sh ->
(forall a, d <= a < d + len -> X a) ->
(forall (E' : env), env_agree sHAV E0 E' ->
forall r, In r (ss_mem ss) -> base_val E' (YP09.r_base r) + YP09.r_hi r <= d \/ d + len <= base_val E' (YP09.r_base r) + YP09.r_lo r
\/ YP09.r_hi r <= YP09.r_lo r) ->
(forall (E' : env), env_agree sHAV E0 E' ->
forall r a, In r (ss_mem ss) -> base_val E' (YP09.r_base r) + YP09.r_lo r <= a < base_val E' (YP09.r_base r) + YP09.r_hi r -> 0 <= a < 2 ^ 64) ->
SRr tfibsegs W' c' (at_S Wy md X (PSR Wy ((d, d + len, vb) :: cut d (d + len) sh) R) (ss_after_stretch ss (ss_mem ss) k CLOB_MS retpc)).
Proof.
intros Wy md X sh R ss W' c' k ed el d len vb retpc HR [_ RM] Hrv Hpc Hk Hat Hnc H10 H12 H11 H1 Aed Ael Ud Ul Hlen Hrpc Hrpc' Hvb Hplace Hsh HX HEXT H64.
pose proof map_facts as (M1 & M2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _). pose proof map_zoneN as MZ.
assert (Hd : TFIB_IMG_END <= d /\ d + len < 2 ^ 64) by (clear - Hplace Hlen M1 M2 SM1 SM2 MZ; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END, kHighMemBeg, kHighShadowBeg, kHighShadowEnd, ASAN_CEIL in *; zlia).
eapply (SRr_mono tfibsegs W' c' _ _
(at_S_memset Wy md X (PSR Wy sh R) (PSR Wy ((d, d + len, vb) :: cut d (d + len) sh) R) ss W' c' k ed el d len vb retpc HR Hrv Hpc Hk Hat Hnc H10 H12 H11 H1 Aed Ael Ud Ul
Hlen (proj1 Hd) (proj2 Hd) Hrpc Hrpc' Hvb _ HEXT H64 _)).
{ intros W2 c2 _ HA. eapply at_S_weaken; [exact HA | intros a [Ha|Ha]; [exact Ha | exact (HX a Ha)] | intros m Hm; exact Hm]. }
Unshelve.
- intros m MEQ [(HB & HM & HSH & HRs) HQ] a Ha. destruct Hplace as [[P1 P2]|[P1 P2]]; [apply HM; zlia | apply HSH; zlia].
- intros m m' MEQ [HP HQ] FR FILL. split; [|exact (RM m m' d len Hplace FR HQ)].
assert (FR' : forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + len) -> m' (w64 a) = m (w64 a)).
{ intros a Ha Hna. apply FR. unfold w64. rewrite unsigned_lit_small by exact Ha. exact Hna. }
assert (FILL' : forall a, d <= a < d + len -> m' (w64 a) = Some (Z_to_bv 8 vb)).
{ intros a Ha. apply FILL. unfold w64. rewrite unsigned_lit_small by (clear - Ha Hd Hplace M1 SM1 MZ; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END, kHighMemBeg, kHighShadowBeg in *; zlia). exact Ha. }
destruct HP as (HB & HM & HSH & HRs).
assert (RP : forall a, (mb + 6144 <= a < mb + MSv) \/ (SMv <= a < SMv + MSv / 8) -> apresent (w_H Wy) m a -> apresent (w_H Wy) m' a).
{ intros a Hrng [Hh [b Hb]]. split; [exact Hh|].
assert (A64 : 0 <= a < 2 ^ 64) by (clear - Hrng M1 M2 SM1 SM2 MZ; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighShadowBeg, kHighShadowEnd, ASAN_CEIL in *; zlia).
destruct (Z_lt_le_dec a d) as [L|GE].
- exists b. exact (eq_trans (FR' a A64 ltac:(zlia)) Hb).
- destruct (Z_lt_le_dec a (d + len)) as [L2|GE2]; [exists (Z_to_bv 8 vb); exact (FILL' a ltac:(zlia)) | exists b; exact (eq_trans (FR' a A64 ltac:(zlia)) Hb)]. }
split; [|split; [|split]].
+ intros i Hi. eapply val_mem_frame; [|exact (HB i Hi)]. intros kk Hkk. pose proof tr_length as LEN.
pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7). destruct Hsp as (S1 & _ & S3 & _). pose proof (u64_range (getr regs0 2)) as U2.
apply FR'; [clear - Hi Hkk LEN T7 S1 S3 U2 MZ; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, IFRAME, ASTACK, kHighMemBeg in *; unfold sp0 in *; zlia|]. intros Hin.
apply (runs_not_stack (sp0 - IFRAME + 16 + 8 * Z.of_nat i + Z.of_nat kk)); [clear - Hin Hplace MZ; zlia | clear - Hi Hkk LEN MZ; unfold IFRAME, ASTACK; zlia].
+ intros a Ha. apply RP; [left; exact Ha | exact (HM a Ha)].
+ intros a Ha. apply RP; [right; exact Ha | exact (HSH a Ha)].
+ apply Forall_cons; [intros a Ha; cbn [fst snd] in Ha; exact (FILL' a Ha) | exact (cut_sound m m' d (d + len) sh FR' Hsh HRs)].
Qed.
Definition chunk_eqb (c c' : YP09.chunk) : bool :=
Z.eqb (YP09.c_off c) (YP09.c_off c') &&
match YP09.c_val c, YP09.c_val c' with
| CVal w v, CVal w' v' => N.eqb w w' && sv_eqb v v'
| CZero l, CZero l' => Z.eqb l l'
| CImg l, CImg l' => Z.eqb l l'
| CData d0 s0 l, CData d1 s1 l' => Nat.eqb d0 d1 && Z.eqb s0 s1 && Z.eqb l l'
| _, _ => false
end.
Lemma chunk_eqb_eq : forall c c', chunk_eqb c c' = true -> c = c'.
Proof.
clearP. intros [o v] [o' v'] H. unfold chunk_eqb in H. cbn [YP09.c_off YP09.c_val] in H. apply andb_prop in H as [Ho Hv]. apply Z.eqb_eq in Ho. subst o'.
destruct v as [w x|l|l|d0 s0 l], v' as [w' x'|l'|l'|d1 s1 l']; try discriminate Hv.
- apply andb_prop in Hv as [Hw Hx]. apply N.eqb_eq in Hw. apply sv_eqb_eq in Hx. subst. reflexivity.
- apply Z.eqb_eq in Hv. subst. reflexivity.
- apply Z.eqb_eq in Hv. subst. reflexivity.
- apply andb_prop in Hv as [Hv Hl]. apply andb_prop in Hv as [Hd Hs]. apply Nat.eqb_eq in Hd. apply Z.eqb_eq in Hs. apply Z.eqb_eq in Hl. subst. reflexivity.
Qed.
Definition subregionb (r' r : YP09.region) : bool :=
obase_eqb (YP09.r_base r') (YP09.r_base r) && (YP09.r_lo r <=? YP09.r_lo r') && (YP09.r_hi r' <=? YP09.r_hi r) &&
((YP09.r_whi r' <=? YP09.r_wlo r') || ((YP09.r_wlo r <=? YP09.r_wlo r') && (YP09.r_whi r' <=? YP09.r_whi r))) &&
forallb (fun c => existsb (chunk_eqb c) (YP09.r_chunks r)) (YP09.r_chunks r').
Lemma subregionb_sound : forall r' r, subregionb r' r = true -> subregion r' r.
Proof.
clearP. intros r' r H. unfold subregionb in H. repeat (apply andb_prop in H; destruct H as [H ?X]).
unfold subregion. split.
{ destruct (YP09.r_base r') as [x|], (YP09.r_base r) as [y|]; cbn in H; try discriminate H; [apply Nat.eqb_eq in H; subst; reflexivity | reflexivity]. }
apply Z.leb_le in X2. apply Z.leb_le in X1. split; [exact X2|]. split; [exact X1|]. split.
- apply Bool.orb_prop in X0 as [E|E]; [left; apply Z.leb_le in E; exact E | right]. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2. zlia.
- intros c Hc. pose proof (proj1 (forallb_forall _ _) X c Hc) as Y. apply existsb_exists in Y as (c' & Hc' & E). apply chunk_eqb_eq in E. subst c'. exact Hc'.
Qed.
Fixpoint submemb (rs' rs : smem) : bool :=
match rs', rs with
| [], _ => true
| r' :: t', r :: t => subregionb r' r && submemb t' t
| _ :: _, [] => false
end.
Lemma submemb_sound : forall rs' rs, submemb rs' rs = true -> submem rs' rs.
Proof.
clearP. intros rs'. induction rs' as [|r' t' IH]; intros rs H; [apply submem_nil|]. destruct rs as [|r t]; [discriminate H|].
cbn [submemb] in H. apply andb_prop in H as [H1 H2]. apply submem_keep; [exact (subregionb_sound _ _ H1) | exact (IH t H2)].
Qed.
Lemma at_S_submem : forall (Wx : world tfibsegs) md X P ss W' c' rs,
at_S Wx md X P ss W' c' -> submemb rs (ss_mem ss) = true -> regions_wf rs = true ->
at_S Wx md X P (mkSS (ss_pc ss) (ss_regs ss) rs (ss_resv ss) (ss_facts ss)) W' c'.
Proof.
clearP. intros Wx md X P ss W' c' rs HR Hsb Hwf. destruct HR as (-> & ms & mat & E' & -> & HE & HS & MEQ & PRS & HPm).
split; [reflexivity|]. exists ms, mat, E'. split; [reflexivity|]. split; [exact HE|]. split; [|exact (conj MEQ (conj PRS HPm))].
exact (st_ok_submem tfibsegs E' ss _ rs HS (submemb_sound _ _ Hsb) Hwf).
Qed.
Lemma at_S_addreg : forall (Wx : world tfibsegs) md X P ss W' c' r,
at_S Wx md X P ss W' c' -> YP09.region_wf r = true ->
(forall (E' : env) (m : word -> option byte),
env_agree sHAV E0 E' -> (forall x : word, ~ X (bv_unsigned x) -> m x = mem0 x) ->
(forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H Wx) m a) -> P m -> mem_ok tfibsegs E' (mrestrict (w_H Wx) m) (ss_mem ss) ->
region_ok tfibsegs E' (mrestrict (w_H Wx) m) r /\ (forall r2, In r2 (ss_mem ss) -> extent_disjoint E' r r2)) ->
at_S Wx md X P (addreg r ss) W' c'.
Proof.
clearP. intros Wx md X P ss W' c' r HR Hwf HOK. destruct HR as (-> & ms & mat & E' & -> & HE & HS & MEQ & PRS & HPm).
split; [reflexivity|]. exists ms, mat, E'. split; [reflexivity|]. split; [exact HE|]. split; [|exact (conj MEQ (conj PRS HPm))].
pose proof (st_ok_mem_ok tfibsegs E' ss _ HS) as HM. destruct (HOK E' (ms_mem ms) HE MEQ PRS HPm HM) as [Hok Hx].
unfold addreg. apply st_ok_add_region; [exact HS | exact Hwf | exact Hok | apply all_disjoint_of_forall; exact Hx].
Qed.
End g.
End f.
