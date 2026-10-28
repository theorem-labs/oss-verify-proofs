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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1w AE3d AB1q AFhy AFhz AFi0 AFi4 AFi9 AB1h AFjm AFid AFie AFif AFjv AFjw AFjx AFjh AFjn AFjo AFjk AFjl.
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
Definition QR (a : Z) : Prop := Qb + 8 * res <= a < Qb + 8 * res + 8 * kPtrArrayEntriesPerCommit /\ a < Qb + kPtrArrayResv.
Hypothesis D1w : forall (X : Z -> Prop) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model),
(forall a, X a -> WIN a \/ QR a) ->
getr regs 10 = Z_to_bv 64 (sp0 - IFRAME + 16) -> getr regs 11 = Z_to_bv 64 (Z.of_nat (length tr)) ->
getr regs 3 = getr regs0 3 -> getr regs 4 = Z_to_bv 64 TFIB_TP -> getr regs 1 = Z_to_bv 64 0x318cc ->
bv_unsigned (getr regs 2) = sp0 - 2272 ->
PBUFW Wy mem -> (forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H Wy) mem a) ->
(forall x : word, ~ X (bv_unsigned x) -> mem x = mem0 x) ->
(forall k, 1 <= k < 4 -> aview tfibsegs (w_H Wy) mem (TFIB_INST + o_sec_mutex + k) = Some 0) ->
SRr tfibsegs Wy (mkCfg (mkst regs (Z_to_bv 64 A_StackDepotPut) mem (seg_rom tfibsegs)) md)
(fun W' c' => W' = Wy /\ exists z regs' mem' mat,
c' = mkCfg (mkst regs' (Z_to_bv 64 0x318cc) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md) /\
regs_preserved regs regs' /\
(forall x : word, ~ (sp0 - 2272 - DEP_STK <= bv_unsigned x < sp0 - 2272) -> ~ DZONE (bv_unsigned x) -> mem' x = mem x) /\
(forall a, apresent (w_H Wy) mem a -> apresent (w_H Wy) mem' a) /\
DPOST z mem').
Local Ltac s_runS HR tbl tblok stop ss' HX HP :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let st := eval vm_compute in (snd (sym_run_toN_sh tfibsegs tbl FUEL stop ss)) in
eapply SRr_bind;
[ eapply (at_S_runS Wx tbl tblok stop md X P ss ss' st W' c' HR);
[ vm_compute; reflexivity | exact I | exact HX | vm_compute; reflexivity | exact HP | vm_compute; reflexivity ]
| clear HR; let W2 := fresh "W" in let c2 := fresh "c" in intros W2 c2 _ HR ] end.
Lemma segT1 : forall (X : Z -> Prop), (forall a, WIN a -> X a) ->
forall c, at_S Wy md1 X (PSR Wy SH2 RX) S_TJ0 Wy c -> SRr tfibsegs Wy c (at_S Wy md1 X (PSR Wy SH2 RX) T_PD).
Proof.
intros X HXW c HR. pose proof SH_ok as (OK0 & OK1 & OK2). pose proof (PSR_stableS' Wy SH2 RX OK2 (RX_stableS RX RXt)) as HP2.
assert (HX : forall a, WIN1S a -> X a) by (intros a Ha; apply HXW, WIN1S_WIN, Ha).
pose proof size_facts as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & _). pose proof Nrange as NR. pose proof map_facts as (M1 & M2 & _). pose proof map_zoneN as MZ.
unfold MALLOC_MAX in Z1, Z8, NR. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in M1, M2.
s_arm HR BC_LTU false (SAlu ALU_ADD (SOff aMAP 4096) (SOff aND 0)) (SAlu ALU_ADD (SOff 10 6144) (SOff aMAP 0)).
{ clear - Z1 Z3 Z7 Z8 NR M1 M2 Hn MZ. arm_zevS. rewrite EaMAP, EaND, E10, Hn. unfold w64. rewrite !unsigned_lit_small by zlia. zcanon_simp.
apply Z.ltb_ge. zlia. }
s_station HR T_J.
s_runS HR tfibtbl_rtA tfibtbl_rtA_ok 0x3180c (runto 0x3180c T_J) HX HP2.
s_arm HR BC_NE false (SAlu ALU_SRL (SOff 10 0) (SLit 48)) (SLit 0).
{ clear - NR Hn MZ. arm_zevS. rewrite E10, Hn. unfold w64. rewrite !unsigned_lit_small by zlia. zcanon_simp. land_lits.
rewrite Z.shiftr_div_pow2 by zlia. rewrite Z.add_0_r, (Z.div_small n (2 ^ 48)) by zlia. reflexivity. }
s_station HR T_K.
s_runS HR tfibtbl_rtA tfibtbl_rtA_ok 0x724b0 T_PD HX HP2.
apply SRr_ret. exact HR.
Qed.
Definition DX (a : Z) : Prop := (sp0 - 2272 - DEP_STK <= a < sp0 - 2272) \/ DZONE a.
Hypothesis RXd : pstable DX RX.
Definition PD (z : Z) (m : word -> option byte) : Prop :=
exists memD, DPOST z memD /\ (forall a, DZONE a -> apresent (w_H Wy) mem0 a -> apresent (w_H Wy) memD a) /\
(forall x : word, DZONE (bv_unsigned x) -> m x = memD x).
Lemma PD_rstable : forall z, rstable (PD z).
Proof.
intros z. split.
- intros m m' FR (memD & D1' & D2 & D3). exists memD. split; [exact D1'|]. split; [exact D2|]. intros x Hx. rewrite FR; [exact (D3 x Hx)|].
intros Hw. exact (proj1 (DZONE_disj _ Hx) (WIN1R_WIN _ Hw)).
- intros m m' d len Hplace FR (memD & D1' & D2 & D3). exists memD. split; [exact D1'|]. split; [exact D2|]. intros x Hx. rewrite FR; [exact (D3 x Hx)|].
intros Hin. exact (proj1 (DZONE_disj _ Hx) (place_WIN d len _ Hplace Hin)).
Qed.
Lemma PD_stableT : forall z, pstable WIN1T (PD z).
Proof.
intros z m m' FR (memD & D1' & D2 & D3). exists memD. split; [exact D1'|]. split; [exact D2|]. intros x Hx. rewrite FR; [exact (D3 x Hx)|].
intros Hw. exact (proj1 (DZONE_disj _ Hx) (WIN1T_WIN _ Hw)).
Qed.
Lemma PSR_stableS : forall sh R, Forall run_ok sh -> pstable WIN1S R -> pstable WIN1S (PSR Wy sh R).
Proof. intros sh R OK RS m m' FR [HP HQ]. split; [exact (PS_stable Wy sh OK m m' FR HP) | exact (RS m m' FR HQ)]. Qed.
Lemma PD_stableS : forall z, pstable WIN1S (PD z).
Proof. intros z m m' FR. apply (PD_stableT z m m'). intros x Hx. apply FR. intros Hw. exact (Hx (WIN1S_WIN1T _ Hw)). Qed.
Definition PDX (z : Z) (m : word -> option byte) : Prop := PD z m /\ RX m.
Lemma PDX_rstable : forall z, rstable (PDX z).
Proof. intros z. exact (rstable_and _ _ (PD_rstable z) RXs). Qed.
Lemma PDX_stableT : forall z, pstable WIN1T (PDX z).
Proof. intros z. exact (pstable_and _ _ _ (PD_stableT z) RXt). Qed.
Lemma PDX_stableS : forall z, pstable WIN1S (PDX z).
Proof. intros z. exact (pstable_and _ _ _ (PD_stableS z) (RX_stableS RX RXt)). Qed.
Definition dx_okb (s : option nat * Z * Z * Z * Z) : bool :=
match s with (b, lo, hi, _, _) =>
match b with
| Some 2%nat => (- 2272 <=? lo) && (hi <=? 0)
| None => (0 <=? lo) && (hi <=? 0x5fb000) && ((hi <=? 0x177ec8) || (0x5c8650 <=? lo))
| _ => skel_okb false s
end
end.
Lemma skel_apart_DX : forall (E' : env) r, env_agree sHAV E0 E' -> dx_okb (skel r) = true ->
(forall a, base_val E' (YP09.r_base r) + YP09.r_lo r <= a < base_val E' (YP09.r_base r) + YP09.r_hi r -> ~ DX a /\ 0 <= a < 2 ^ 64).
Proof.
intros E' r HE Hs a Ha.
assert (SK : skel_okb false (skel r) = true).
{ destruct r as [[k|] lo hi wlo whi cs]; unfold skel, dx_okb in Hs |- *; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi] in *;
[| apply andb_prop in Hs as [Hs _]; exact Hs].
destruct k as [|[|[|k]]]; try exact Hs. unfold skel_okb. apply andb_prop in Hs as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
rewrite (proj2 (Z.leb_le (- ASTACK) lo)) by (unfold ASTACK; zlia). rewrite (proj2 (Z.leb_le hi 0) H2). reflexivity. }
split; [| exact (skel_u64 E' false r a HE SK Ha)].
destruct HE as [HEn _]. pose proof high_facts as (F1 & F2 & _ & _ & _ & _ & F7 & F8 & F9 & F10 & _).
pose proof map_facts as (M1 & M2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _ & PB & _). pose proof map_zoneN as MZ. pose proof size_facts as (_ & _ & Z3 & Z4 & _ & _ & Z7 & Z8 & _ & Z10 & _).
pose proof Hidx as HI. pose proof Nrange as NR. pose proof BSLv_range as HB. pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7). destruct Hsp as (S1 & _ & S3 & _).
pose proof blocks_facts as (NBhi & SBhi & TNB & TSB & QNB & QSB & NBS & SBS & CNB & CSB).
unfold zdisjoint in TNB, TSB, QNB, QSB, NBS, SBS, CNB, CSB. cbn [fst snd] in TNB, TSB, QNB, QSB, NBS, SBS, CNB, CSB.
destruct Hmap_apart as (_ & _ & _ & _ & MNB & MSB & _). unfold zdisjoint in MNB, MSB. cbn [fst snd] in MNB, MSB.
pose proof (u64_range (getr regs0 2)) as U2.
destruct r as [b lo hi wlo whi cs]. unfold skel in Hs, SK. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi] in *.
unfold zone3, TFIB_IMG_LO, kLowShadowBeg, DX, DZONE, DEP_STK, kNodesBlockSize, kStoreBlockSize, kHighMemBeg in *.
destruct (skel_cases false b lo hi wlo whi SK) as [(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|(Epb & -> & A1 & A2)]]]]]]]; cbn [base_val] in Ha.
- unfold dx_okb in Hs. apply andb_prop in Hs as [_ H3]. apply Bool.orb_prop in H3 as [H3|H3]; apply Z.leb_le in H3;
clear - Ha A1 A2 H3 NBhi SBhi S1 T7 MZ; unfold ASTACK in *; try unfold sp0 in *; zlia.
- rewrite (HEn 2%nat ltac:(unfold sHAV; zlia)), E2 in Ha. unfold dx_okb in Hs. apply andb_prop in Hs as [H1 H2]. apply Z.leb_le in H1.
clear - Ha A1 A2 H1 NBS SBS S1 S3 T7 U2 MZ. unfold ASTACK in *. try unfold sp0 in *. zlia.
- rewrite (HEn 32%nat ltac:(unfold sHAV; zlia)), EaT in Ha. unfold w64 in Ha. rewrite unsigned_lit_small in Ha by (clear - F1 F2 MZ; numconst; try unfold T in *; zlia).
pose proof stack_ivs as (DT & _). clear - Ha A1 A2 TNB TSB F1 F2 S1 S3 T7 U2 DT MZ. ceil; unfold kThreadObjSize, ASTACK, ASAN_CEIL in *. try unfold T in *. try unfold sp0 in *. zlia.
- rewrite (HEn 33%nat ltac:(unfold sHAV; zlia)), EaC in Ha. unfold w64 in Ha. rewrite unsigned_lit_small in Ha by (clear - F7 F8 MZ; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; zlia).
pose proof stack_ivs as (_ & _ & DC & _). clear - Ha A1 A2 CNB CSB F7 F8 S1 S3 T7 U2 DC MZ. ceil; unfold ASTACK, ASAN_CEIL in *. try unfold sp0 in *. zlia.
- unfold aMAP in Ha. rewrite (HEn 45%nat ltac:(unfold sHAV; zlia)), EaMAP in Ha. unfold w64 in Ha. rewrite unsigned_lit_small in Ha by (clear - M1 M2 Z8 MZ; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; zlia).
destruct Hmap_apart as (_ & _ & _ & _ & _ & _ & MS). unfold zdisjoint in MS. cbn [fst snd] in MS. clear - Ha A1 A2 MNB MSB M1 M2 Z8 S1 S3 T7 U2 MS MZ.
ceil; unfold ASTACK, ASAN_CEIL in *. try unfold sp0 in *. zlia.
- unfold aQS in Ha. rewrite (HEn 52%nat ltac:(unfold sHAV; zlia)), EaQS in Ha. unfold w64 in Ha. unfold QSv in *. rewrite unsigned_lit_small in Ha by (clear - F9 F10 HI MZ; ceil; unfold ASAN_CEIL, kPtrArrayResv, kMaxNumChunks in *; try unfold Qb in *; zlia).
pose proof stack_ivs as (_ & _ & _ & SQ). clear - Ha A1 A2 QNB QSB F9 F10 HI S1 S3 T7 U2 SQ MZ. ceil; unfold ASTACK, ASAN_CEIL, kPtrArrayResv, kMaxNumChunks in *. try unfold Qb in *. try unfold sp0 in *. zlia.
- unfold aBSL in Ha. rewrite (HEn 55%nat ltac:(unfold sHAV; zlia)), EaBSL in Ha. unfold w64 in Ha. rewrite unsigned_lit_small in Ha by (clear - HB MZ; unfold TFIB_INST in *; zlia).
clear - Ha A1 A2 HB NBhi SBhi S1 T7 MZ. unfold TFIB_INST, ASTACK in *. try unfold sp0 in *. zlia.
- discriminate Epb.
Qed.
Lemma skel_apart_stk : forall (E' : env) r, env_agree sHAV E0 E' -> dx_okb (skel r) = true -> YP09.r_lo r < YP09.r_hi r ->
base_val E' (YP09.r_base r) + YP09.r_hi r <= sp0 - ASTACK \/ sp0 - 2272 <= base_val E' (YP09.r_base r) + YP09.r_lo r.
Proof.
intros E' r HE Hs Hne.
assert (SK : skel_okb false (skel r) = true).
{ destruct r as [[k|] lo hi wlo whi cs]; unfold skel, dx_okb in Hs |- *; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi] in *;
[| apply andb_prop in Hs as [Hs _]; exact Hs].
destruct k as [|[|[|k]]]; try exact Hs. unfold skel_okb. apply andb_prop in Hs as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
rewrite (proj2 (Z.leb_le (- ASTACK) lo)) by (unfold ASTACK; zlia). rewrite (proj2 (Z.leb_le hi 0) H2). reflexivity. }
destruct HE as [HEn _]. pose proof high_facts as (F1 & F2 & _ & _ & _ & _ & F7 & F8 & F9 & F10 & _).
pose proof map_facts as (M1 & M2 & _). pose proof map_zoneN as MZ. pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & _).
pose proof Hidx as HI. pose proof BSLv_range as HB. pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7). destruct Hsp as (S1 & _ & S3 & _).
pose proof stack_ivs as (DT & _ & DC & SQ). destruct Hmap_apart as (_ & _ & _ & _ & _ & _ & MS). unfold zdisjoint in MS. cbn [fst snd] in MS.
pose proof (u64_range (getr regs0 2)) as U2.
destruct r as [b lo hi wlo whi cs]. unfold skel in Hs, SK. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi] in *.
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kPtrArrayResv, kMaxNumChunks in *.
destruct (skel_cases false b lo hi wlo whi SK) as [(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|(Epb & -> & A1 & A2)]]]]]]]; cbn [base_val].
- left. clear - A1 A2 S1 T7 MZ. unfold ASTACK in *. try unfold sp0 in *. zlia.
- right. rewrite (HEn 2%nat ltac:(unfold sHAV; zlia)), E2. unfold dx_okb in Hs. apply andb_prop in Hs as [H1 H2]. apply Z.leb_le in H1. clear - H1 MZ. try unfold sp0 in *. zlia.
- rewrite (HEn 32%nat ltac:(unfold sHAV; zlia)), EaT. unfold w64. rewrite unsigned_lit_small by (clear - F1 F2 MZ; numconst; try unfold T in *; zlia).
clear - A1 A2 DT Hne MZ. unfold ASTACK, kThreadObjSize in *. try unfold T in *. try unfold sp0 in *. zlia.
- rewrite (HEn 33%nat ltac:(unfold sHAV; zlia)), EaC. unfold w64. rewrite unsigned_lit_small by (clear - F7 F8 MZ; zlia).
clear - A1 A2 DC Hne MZ. unfold ASTACK in *. try unfold sp0 in *. zlia.
- unfold aMAP. rewrite (HEn 45%nat ltac:(unfold sHAV; zlia)), EaMAP. unfold w64. rewrite unsigned_lit_small by (clear - M1 M2 Z8 MZ; zlia).
clear - A1 A2 MS M1 M2 Z8 S1 S3 Hne MZ. unfold ASTACK in *. try unfold sp0 in *. zlia.
- unfold aQS. rewrite (HEn 52%nat ltac:(unfold sHAV; zlia)), EaQS. unfold w64. unfold QSv in *. rewrite unsigned_lit_small by (clear - F9 F10 HI MZ; try unfold Qb in *; zlia).
clear - A1 A2 SQ HI Hne MZ. unfold ASTACK, kPtrArrayResv, kMaxNumChunks in *. try unfold Qb in *. try unfold sp0 in *. zlia.
- unfold aBSL. rewrite (HEn 55%nat ltac:(unfold sHAV; zlia)), EaBSL. unfold w64. rewrite unsigned_lit_small by (clear - HB MZ; unfold TFIB_INST in *; zlia).
left. clear - A1 A2 HB S1 T7 MZ. unfold TFIB_INST, ASTACK in *. try unfold sp0 in *. zlia.
- discriminate Epb.
Qed.
Lemma at_S_depot : forall (X : Z -> Prop), (forall a, X a -> WIN a \/ QR a) -> (forall a, WIN a -> X a) ->
forall c, at_S Wy md1 X (PSR Wy SH2 RX) T_PD Wy c ->
SRr tfibsegs Wy c (fun W2 c2 => exists z, at_S Wy md1 (fun a => X a \/ DX a) (PSR Wy SH2 (PDX z)) T_2 W2 c2).
Proof.
intros X HXQ HXW c HR. destruct HR as (EW & ms & mat & E' & -> & HE & HS & MEQ & PRS & HPm). clear EW. pose proof (proj1 HE) as HEn.
pose proof Hwx_tfa as Hwx. pose proof Hsp as (Hlo & Hbot & Hhi & Hal). pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
pose proof (u64_range (getr regs0 2)) as Usp.
pose proof (st_ok_restrict_mkst tfibsegs (w_H Wy) E' _ _ HS eq_refl) as Hshape. cbn [ss_pc] in Hshape.
lazymatch type of Hshape with _ = mkst _ (Z_to_bv 64 (ss_pc ?s)) _ _ => let p := eval vm_compute in (ss_pc s) in change (ss_pc s) with p in Hshape end. rewrite Hshape.
rreg HS (2%bv : bv 5) R2. rewrite (HEn 2%nat ltac:(unfold sHAV; zlia)), E2 in R2.
eapply SRr_mono.
{ apply (D1w X (ms_regs ms) (ms_mem ms) _ HXQ).
- rreg HS (10%bv : bv 5) R; rewrite R, (HEn 2%nat ltac:(unfold sHAV; zlia)), E2. unfold IFRAME, sp0. f_equal; zlia.
- rreg HS (11%bv : bv 5) R; rewrite R, (HEn 36%nat ltac:(unfold sHAV; zlia)). reflexivity.
- rreg HS (3%bv : bv 5) R; rewrite R, (HEn 3%nat ltac:(unfold sHAV; zlia)). exact (Er 3 3%bv eq_refl).
- rreg HS (4%bv : bv 5) R; rewrite R. reflexivity.
- rreg HS (1%bv : bv 5) R; rewrite R. reflexivity.
- rewrite R2. clear - Hlo Hhi T4 T7 Usp. rewrite unsigned_lit_small by (unfold zone3, TFIB_IMG_LO, kLowShadowBeg, ASTACK, kHighMemEnd, kHighMemBeg in *; unfold sp0 in *; zlia). unfold sp0; zlia.
- exact (proj1 (proj1 HPm)).
- exact PRS.
- exact MEQ.
-
destruct (st_ok_mem_ok tfibsegs E' _ _ HS) as (_ & ROK & _).
set (RMUT := YP09.mkRegion None (TFIB_INST + o_sec_mutex) (TFIB_INST + o_sec_mutex + 4) (TFIB_INST + o_sec_mutex) (TFIB_INST + o_sec_mutex + 4)
[YP09.mkChunk (TFIB_INST + o_sec_mutex) (CVal 1 (SLit 0)); YP09.mkChunk (TFIB_INST + o_sec_mutex + 1) (CVal 1 (SLit 0));
YP09.mkChunk (TFIB_INST + o_sec_mutex + 2) (CVal 2 (SLit 0))]).
assert (HIN : In RMUT (ss_mem T_PD)) by (subst RMUT; vm_compute; repeat (first [left; reflexivity | right])).
pose proof (proj1 (Forall_forall _ _) ROK RMUT HIN) as (_ & _ & _ & RC). subst RMUT. cbn [YP09.r_chunks YP09.r_base base_val] in RC.
apply Forall_cons_iff in RC as [_ RC]. apply Forall_cons_iff in RC as [C1 RC]. apply Forall_cons_iff in RC as [C2 _].
intros k Hk. unfold aview. cbn [restrict ms_mem].
assert (Hcase : k = 1 \/ k = 2 \/ k = 3) by zlia. destruct Hcase as [-> | [-> | ->]].
+ destruct (C1 0 ltac:(cbn; zlia)) as (b & Hb & Hm). cbn [YP09.c_off YP09.c_val cbyte restrict ms_mem] in Hb, Hm.
replace (TFIB_INST + o_sec_mutex + 1) with (0 + (TFIB_INST + o_sec_mutex + 1) + 0) by zlia. rewrite Hm. rewrite <- Hb. vm_compute. reflexivity.
+ destruct (C2 0 ltac:(cbn; zlia)) as (b & Hb & Hm). cbn [YP09.c_off YP09.c_val cbyte restrict ms_mem] in Hb, Hm.
replace (TFIB_INST + o_sec_mutex + 2) with (0 + (TFIB_INST + o_sec_mutex + 2) + 0) by zlia. rewrite Hm. rewrite <- Hb. vm_compute. reflexivity.
+ destruct (C2 1 ltac:(cbn; zlia)) as (b & Hb & Hm). cbn [YP09.c_off YP09.c_val cbyte restrict ms_mem] in Hb, Hm.
replace (TFIB_INST + o_sec_mutex + 3) with (0 + (TFIB_INST + o_sec_mutex + 2) + 1) by zlia. rewrite Hm. rewrite <- Hb. vm_compute. reflexivity. }
intros W' c' Hle (-> & z & regs2 & mem2 & mat2 & -> & HP & Hfr & Hpr & HDP). exists z.
set (mem := ms_mem ms) in *.
assert (Hfr' : forall x : word, ~ DX (bv_unsigned x) -> mem2 x = mem x) by (intros x Hx; apply Hfr; unfold DX in Hx; tauto).
lazymatch type of HS with st_ok _ _ ?ss ?ms0 =>
let m := eval vm_compute in (ss_mem ss) in
lazymatch m with ?rq :: ?rm :: ?rb :: ?r1 :: ?rest =>
pose proof (st_ok_after_call tfibsegs sD1 E' ss ms0 regs2 (mrestrict (w_H Wy) mem2) (rq :: rm :: rb :: trim_lo r1 (-2272) :: rest) 0x318cc HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(apply submem_keep; [apply subregion_refl|]; apply submem_keep; [apply subregion_refl|]; apply submem_keep; [apply subregion_refl|];
apply submem_keep; [apply subregion_trim_lo | apply submem_refl])
ltac:(vm_compute; reflexivity) HP) as HS1;
let rsv := eval vm_compute in (rq :: rm :: rb :: trim_lo r1 (-2272) :: rest) in
change (rq :: rm :: rb :: trim_lo r1 (-2272) :: rest) with rsv in HS1;
let ss2 := eval vm_compute in (ss_after_call ss rsv sD1 0x318cc) in
change (ss_after_call ss rsv sD1 0x318cc) with ss2 in HS1
end
end.
cbn [ms_mem restrict] in HS1. fold mem in HS1.
lazymatch type of HS1 with Forall _ ?rs -> _ =>
assert (KEPT : Forall (region_kept tfibsegs E' (mrestrict (w_H Wy) mem) (mrestrict (w_H Wy) mem2)) rs);
[ apply Forall_forall; intros r Hr;
pose proof (proj1 (forallb_forall _ _) (eq_refl : forallb (fun r => dx_okb (skel r)) rs = true) r Hr) as CK; cbn beta in CK;
apply (kept_of_frame2 (w_H Wy) E' mem mem2 DX r Hfr');
[ exact (skel_apart_DX E' r HE CK)
| intros a Ha; pose proof (region_wf_facts r (regions_wf_In rs r ltac:(vm_compute; reflexivity) Hr)) as (_ & WW & _); apply (skel_apart_DX E' r HE CK); clear - Ha WW; zlia ]
| specialize (HS1 KEPT); clear KEPT ]
end.
assert (PRES2 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H Wy) mem2 a) by (intros a Ha; apply Hpr, PRS, Ha).
set (En3 := havoc E' sD1 (map (getr regs2) CLOB)) in HS1.
assert (HE3 : env_agree sHAV E0 En3) by (exact (env_agree_havoc_ge sHAV sD1 E0 E' _ ltac:(unfold sHAV, sD1; zlia) HE)).
pose proof (proj1 HE3) as HEn3.
apply (st_ok_add_region _ _ _ R_scr2) in HS1;
[ | reflexivity
| unfold YP09.region_ok, R_scr2; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem];
rewrite (HEn3 2%nat ltac:(unfold sHAV; zlia)), E2;
split; [clear - Hlo T7; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, ASTACK, kHighMemBeg in *; unfold sp0 in *; zlia|]; split; [clear - Usp; zlia|]; split;
[ intros o Ho; apply apresent_writable_off; [off_by ltac:(clear - Ho Hlo T7 Usp; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, ASTACK, TFIB_IMG_END, kHighMemBeg in *; unfold sp0 in *; zlia) | apply PRES2; clear - Ho; unfold ASTACK in *; zlia] | constructor ]
| apply all_disjoint_of_forall; intros r' Hr';
lazymatch type of Hr' with In _ ?l =>
pose proof (proj1 (forallb_forall _ _) (eq_refl : forallb (fun r => dx_okb (skel r) && (YP09.r_lo r <? YP09.r_hi r)) l = true) r' Hr') as CK; cbn beta in CK end;
apply andb_prop in CK as [CK1 CK2]; apply Z.ltb_lt in CK2;
unfold extent_disjoint, R_scr2; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite (HEn3 2%nat ltac:(unfold sHAV; zlia)), E2;
pose proof (skel_apart_stk En3 r' HE3 CK1 CK2) as AP; clear - AP; unfold sp0 in *; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1.
lazymatch type of HS1 with st_ok _ _ ?ss _ => replace ss with T_2 in HS1 by (vm_compute; reflexivity) end.
split; [reflexivity|]. exists (mkst regs2 (Z_to_bv 64 0x318cc) mem2 (seg_rom tfibsegs)), mat2, En3.
split; [rewrite wvb_collapse; reflexivity|]. split; [exact HE3|]. split; [rewrite restrict_mkst_fx; exact HS1|].
split. { intros x Hx. cbn [ms_mem mkst]. rewrite Hfr' by (intros Hd; apply Hx; right; exact Hd). apply MEQ. intros HX'; apply Hx; left; exact HX'. }
split; [exact PRES2|].
destruct HPm as [(HB & HM & HSH & HRs) HRX]. cbn [ms_mem mkst].
assert (NDX : forall a, (mb + 6144 <= a < mb + MSv) \/ (SMv <= a < SMv + MSv / 8) -> ~ DX a).
{ intros a Ha [Hs|Hd].
- apply (runs_not_stack a Ha). unfold DEP_STK, ASTACK in *. zlia.
- apply (proj1 (DZONE_disj a Hd)). apply (place_WIN a 1 a); [clear - Ha; zlia | zlia]. }
pose proof map_facts as (M1 & M2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _). pose proof map_zoneN as MZ.
assert (U64R : forall a, (mb + 6144 <= a < mb + MSv) \/ (SMv <= a < SMv + MSv / 8) -> bv_unsigned (Z_to_bv 64 a) = a).
{ intros a Ha. apply unsigned_lit_small. clear - Ha M1 M2 SM1 SM2 MZ. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighShadowBeg, kHighShadowEnd, ASAN_CEIL in *. zlia. }
split; [split; [|split; [|split]]|].
- intros i Hi. eapply val_mem_frame; [|exact (HB i Hi)]. intros kk Hkk. apply Hfr'. pose proof tr_length as LEN.
rewrite unsigned_lit_small by (clear - Hi Hkk LEN Hlo Hhi T4 T7 MZ; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, IFRAME, ASTACK, kHighMemBeg, kHighMemEnd in *; unfold sp0 in *; zlia).
intros [Hs|Hd]; [clear - Hs Hi Hkk LEN MZ; unfold IFRAME, DEP_STK in *; zlia|].
apply (proj2 (DZONE_disj _ Hd)). clear - Hi Hkk LEN MZ. unfold IFRAME, ASTACK in *. zlia.
- intros a Ha. apply Hpr. exact (HM a Ha).
- intros a Ha. apply Hpr. exact (HSH a Ha).
- pose proof SH_ok as (_ & _ & OK2). apply Forall_forall. intros r Hr a Ha. pose proof (proj1 (Forall_forall _ _) OK2 r Hr) as RO.
assert (PL : (mb + 6144 <= a < mb + MSv) \/ (SMv <= a < SMv + MSv / 8)) by (unfold run_ok in RO; clear - RO Ha MZ; zlia).
unfold w64. rewrite Hfr' by (rewrite (U64R a PL); exact (NDX a PL)). exact (proj1 (Forall_forall _ _) HRs r Hr a Ha).
- split; [| exact (RXd mem mem2 Hfr' HRX)].
exists mem2. split; [exact HDP|]. split; [|intros x _; reflexivity].
intros a Hd Hp0. apply Hpr. apply (apresent_same (w_H Wy) mem0); [|exact Hp0]. apply MEQ.
pose proof blocks_facts as (NBhi & SBhi & _ & _ & QNB & QSB & _). unfold zdisjoint in QNB, QSB. cbn [fst snd] in QNB, QSB.
pose proof high_facts as (_ & _ & _ & _ & _ & _ & _ & _ & F9 & F10 & _). pose proof Hres as [HRS _].
rewrite unsigned_lit_small by (clear - Hd NBhi SBhi MZ; unfold DZONE in *; numconst; zlia).
intros HXa. destruct (HXQ a HXa) as [Hw|Hq]; [exact (proj1 (DZONE_disj a Hd) Hw)|].
unfold QR in Hq. pose proof Hidx as HI9. clear - Hd Hq QNB QSB F9 HRS HI9 MZ. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, DZONE, kHighMemBeg, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kMaxNumChunks, kPtrArrayEntriesPerCommit in *. try unfold Qb in *. zlia.
Qed.
Definition SH3 : list (Z * Z * Z) :=
[(SMv + 512, SMv + 768, 250); (SHBv + ENDv / 8, SMv + MSv / 8, 250); (SMv, SMv + 512, 250); (SMv + 768, SHBv + ENDv / 8, 0)].
Definition SH4 : list (Z * Z * Z) :=
[(SHBv + UEv / 8, SMv + MSv / 8, 250); (SMv + 512, SMv + 768, 250); (SMv, SMv + 512, 250); (SMv + 768, SHBv + UEv / 8, 0)].
Lemma shadow_marks :
SHBv + ENDv / 8 = SMv + 512 + NDv / 8 /\ SHBv + UEv / 8 = SMv + 768 + R8v / 8 /\ SMv + MSv / 8 = SHBv + UEv / 8 + RLv / 8 /\
NDv / 8 = R8v / 8 + 512 /\ 8065 <= R8v / 8 <= 2 ^ 25 /\ 256 <= RLv / 8 /\ SMv = SHBv + mb / 8 /\ MSv / 8 = NDv / 8 + 512 + TLv / 8 /\ 0 <= TLv / 8.
Proof.
pose proof map_facts as (M1 & M2 & M3 & K4 & U5 & E6 & UE7 & E8 & UE9 & MT & MU & SM1 & SM2 & SM3 & PB & SMA). pose proof map_zoneN as MZ.
pose proof size_facts as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10 & Z11 & Z12 & Z13 & Z14). unfold MALLOC_MAX in Z1, Z8.
clear - M1 M3 U5 E6 UE7 MT MU Z1 Z2 Z7 Z8 Z9 Z10 Z11 Z13 MZ. unfold AFjm.SMv, AFjm.SHBv.
rewrite E6, UE7 in *. rewrite U5 in *. rewrite Z7 in *.
replace RLv with (MSv - R8v - 6144) in * by zlia. replace TLv with (MSv - R8v - 8192) in * by zlia.
apply Z.mod_divide in M3 as [u Hu]; [|zlia]. apply Z.mod_divide in Z2 as [q Hq]; [|zlia]. apply Z.mod_divide in Z9 as [w Hw]; [|zlia].
rewrite Hu, Hq, Hw in *.
replace (u * 4096 + 6144 + q * 8 + 2048) with ((u * 512 + 1024 + q) * 8) by zlia. replace (u * 4096 + 6144 + q * 8) with ((u * 512 + 768 + q) * 8) by zlia.
replace (w * 4096) with ((w * 512) * 8) by zlia. replace (q * 8 + 4096) with ((q + 512) * 8) by zlia.
replace ((w * 512) * 8 - q * 8 - 6144) with ((w * 512 - q - 768) * 8) by zlia. replace (u * 4096) with ((u * 512) * 8) by zlia.
replace ((w * 512) * 8 - q * 8 - 8192) with ((w * 512 - q - 1024) * 8) by zlia.
rewrite !Z_div_mult by zlia. repeat split; zlia.
Qed.
Lemma SH34_ok : Forall run_ok SH3 /\ Forall run_ok SH4.
Proof.
pose proof shadow_marks as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9). clear - A1 A2 A3 A4 A5 A6 A7 A8 A9.
unfold SH3, SH4, run_ok. repeat split; repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; zlia.
Qed.
Section T2.
Variables (X : Z -> Prop) (z : Z).
Hypothesis HXW : forall a, WIN a -> X a.
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
Lemma segT2b : forall W' c, at_S Wy md1 X (PSR Wy SH2 (PDX z)) T_N W' c -> SRr tfibsegs W' c (at_S Wy md1 X (PSR Wy SH4 (PDX z)) T_R).
Proof.
intros W1 c HR. pose proof SH_ok as (_ & _ & OK2). pose proof SH34_ok as [OK3 OK4]. pose proof (PDX_rstable z) as RS.
pose proof (PSR_stableS SH2 (PDX z) OK2 (PDX_stableS z)) as HP2. pose proof (PSR_stableS SH3 (PDX z) OK3 (PDX_stableS z)) as HP3. pose proof (PSR_stableS SH4 (PDX z) OK4 (PDX_stableS z)) as HP4.
assert (HX : forall a, WIN1S a -> X a) by (intros a Ha; apply HXW, WIN1S_WIN, Ha).
pose proof map_facts as (M1 & M2 & M3 & K4 & U5 & E6 & UE7 & E8 & UE9 & MT & MU & SM1 & SM2 & SM3 & PB & SMA). pose proof map_zoneN as MZ.
pose proof size_facts as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10 & Z11 & Z12 & Z13 & Z14). pose proof Nrange as NR.
unfold MALLOC_MAX in Z1, Z8, NR. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kHighShadowBeg, kHighShadowEnd in M1, M2, SM1, SM2.
pose proof shadow_marks as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
s_runS HR tfibtbl_rtA tfibtbl_rtA_ok 0x53828 T_L3 HX HP2.
s_ladder s_runS HR tfibtbl_rtA tfibtbl_rtA_ok 0x97698 T_L3l T_L3lo T_L3h T_L3h2 T_L3h3 T_L3hi T_M3 sL3 CLOB_L HX HP2.
s_memsetR HR T_P3 sM3 constr:(SMv + 512) 256 250 0x319a4 OK2 RS.
{ clear - M1 M2 M3 Z8 A7 MZ. U_zevS. rewrite (eq_refl : ew E0 47 = w64 SHBv), EaMAP. unfold w64, AFjm.SHBv in *. rewrite !unsigned_lit_small by zlia.
zcanon_simp. land_lits. rewrite Z.shiftr_div_pow2 by zlia. change (2 ^ 3) with 8.
apply Z.mod_divide in M3 as [u Hu]; [|zlia]. rewrite Hu in *. replace (u * 4096 + 4096) with ((u * 512 + 512) * 8) by zlia. rewrite Z_div_mult by zlia.
rewrite A7. replace (u * 4096) with ((u * 512) * 8) by zlia. rewrite Z_div_mult by zlia. zcanon_simp. zlia. }
{ clear - M1 M2 M3 Z8 MZ. U_zevS. rewrite EaMAP. unfold w64. rewrite !unsigned_lit_small by zlia.
zcanon_simp. land_lits. rewrite !Z.shiftr_div_pow2 by zlia. change (2 ^ 3) with 8.
apply Z.mod_divide in M3 as [u Hu]; [|zlia]. rewrite Hu.
replace (u * 4096 + 6136) with ((u * 512 + 767) * 8) by zlia. replace (u * 4096 + 4096) with ((u * 512 + 512) * 8) by zlia. rewrite !Z_div_mult by zlia.
zcanon_simp. zlia. }
{ right. clear - A1 A4 A5 A8 A9 MZ. zlia. }
apply (PSR_runs Wy md1 X _ SH3 (PDX z) T_P3) in HR.
2:{ intros m HF. pose proof (Forall_inv HF) as B1. pose proof (Forall_inv_tail HF) as B2'. clear HF.
unfold cut, SH2 in B2'. cbn [flat_map app] in B2'. unfold cut1 in B2'. cbn [fst snd] in B2'.
assert (G1 : (SHBv + ENDv / 8 <? SMv + 512) = false) by (clear - A1 A4 A5 MZ; apply Z.ltb_ge; zlia).
assert (G2 : (SMv + 512 + 256 <? SMv + MSv / 8) = true) by (clear - A4 A5 A8 A9 MZ; apply Z.ltb_lt; zlia).
assert (G3 : (SMv <? SMv + 512) = true) by (apply Z.ltb_lt; zlia).
assert (G4 : (SMv + 512 + 256 <? SMv + 512) = false) by (apply Z.ltb_ge; zlia).
assert (G5 : (SMv + 512 <? SMv + 512) = false) by (apply Z.ltb_irrefl).
assert (G6 : (SMv + 512 + 256 <? SHBv + ENDv / 8) = true) by (clear - A1 A4 A5 MZ; apply Z.ltb_lt; zlia).
rewrite G1, G2, G3, G4, G5, G6 in B2'. cbn [app] in B2'.
pose proof (Forall_inv B2') as C1. pose proof (Forall_inv (Forall_inv_tail B2')) as C2. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail B2'))) as C3. clear B2'.
rewrite Z.max_l in C1 by (clear - A1 A4 A5 MZ; zlia). rewrite Z.min_l in C2 by zlia. rewrite Z.max_r in C3 by zlia.
replace (SMv + 512 + 256) with (SMv + 768) in B1 by zlia.
unfold SH3. apply Forall_cons; [exact B1|]. apply Forall_cons; [exact C1|]. apply Forall_cons; [exact C2|]. apply Forall_cons; [|apply Forall_nil].
intros a Ha. apply C3. cbn [fst snd] in *. zlia. }
s_pin HR (22%bv : bv 5) (SOff aUE 0).
{ clear - M1 M2 M3 Z8 Z1 Z2 Z3 NR UE7 U5 Hn MZ. pin_zevS. rewrite EaUE, EaMAP, E10, Hn. unfold w64. rewrite !unsigned_lit_small by zlia. zcanon_simp.
change (zcanon (-8)) with (2 ^ 64 - 8). rewrite land_m8_64 by zlia. rewrite UE7, U5.
pose proof (Z.div_mod (n + 7) 8 ltac:(zlia)) as D8. pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(zlia)) as B8. unfold R8v in *.
apply Z.mod_divide in M3 as [u Hu]; [|zlia].
replace ((n + 6151 + (mb + 0)) mod 8) with ((n + 7) mod 8); [zcanon_simp; zlia|].
rewrite Hu. replace (n + 6151 + (u * 4096 + 0)) with ((n + 7) + (768 + u * 512) * 8) by zlia. rewrite Z_mod_plus_full. reflexivity. }
s_pin HR (8%bv : bv 5) (SOff aMS (-4096)).
{ clear - Z1 Z7 Z8 Z9 Z10 MZ. pin_zevS. rewrite EaMS, EaND. unfold w64. rewrite !unsigned_lit_small by zlia. zcanon_simp.
change 18446744073709547520 with (2 ^ 64 - 2 ^ 12). rewrite land_neg_pow2_u64 by zlia. change (2 ^ 12) with 4096.
pose proof (Z.div_mod (NDv + 4095) 4096 ltac:(zlia)) as DM. pose proof (Z.mod_pos_bound (NDv + 4095) 4096 ltac:(zlia)) as MB.
unfold AFjm.MSv in *. zcanon_simp. zlia. }
s_station HR T_P4.
s_runS HR tfibtbl_rtA tfibtbl_rtA_ok 0x319b4 (runto 0x319b4 T_P4) HX HP3.
s_pin HR (11%bv : bv 5) (SOff aRL 0).
{ clear - M1 M2 Z8 Z1 Z13 MU UE7 U5 MZ. pin_zevS. rewrite EaRL, EaMS, EaMAP, EaUE. unfold w64. rewrite !unsigned_lit_small by zlia.
rewrite (zcanon_id (RLv + 0)), (zcanon_id (MSv + 0)), (zcanon_id (mb + 0)), (zcanon_id (UEv + 0)), (zcanon_id (MSv + 0 + (mb + 0))) by (unfold M64; zlia).
unfold zcanon, M64. rewrite Zmult_mod_idemp_r. rewrite Zplus_mod_idemp_r.
replace (MSv + 0 + (mb + 0) + (UEv + 0) * 18446744073709551615) with ((RLv + 0) + UEv * 2 ^ 64) by zlia. rewrite Z_mod_plus_full. symmetry. apply Z.mod_small. zlia. }
s_station HR T_P5.
s_runS HR tfibtbl_rtA tfibtbl_rtA_ok 0x53828 T_L4 HX HP3.
s_ladder s_runS HR tfibtbl_rtA tfibtbl_rtA_ok 0x97698 T_L4l T_L4lo T_L4h T_L4h2 T_L4h3 T_L4hi T_M4 sL4 CLOB_L HX HP3.
s_memsetR HR T_P6 sM4 constr:(SHBv + UEv / 8) constr:(RLv / 8) 250 0x319b8 OK3 RS.
{ clear - M1 M2 Z8 Z1 UE7 U5 A2 A7 A5 SM1 MZ. U_zevS. rewrite (eq_refl : ew E0 47 = w64 SHBv), EaUE. unfold w64, AFjm.SHBv in *. rewrite !unsigned_lit_small by zlia.
zcanon_simp. land_lits. rewrite Z.shiftr_div_pow2 by zlia. change (2 ^ 3) with 8.
pose proof (Z.div_pos UEv 8 ltac:(zlia) ltac:(zlia)). pose proof (Z.div_lt_upper_bound UEv 8 (2 ^ 61) ltac:(zlia) ltac:(zlia)). zcanon_simp. zlia. }
{ clear - M1 M2 Z8 Z1 Z13 Z14 UE7 UE9 U5 A2 A3 A5 A6 A7 MZ. U_zevS. rewrite EaUE, EaRL. unfold w64. rewrite !unsigned_lit_small by zlia.
zcanon_simp. land_lits. rewrite !Z.shiftr_div_pow2 by zlia. change (2 ^ 3) with 8.
apply Z.mod_divide in UE9 as [q Hq]; [|zlia]. apply Z.mod_divide in Z14 as [t Ht]; [|zlia]. rewrite Hq, Ht in *.
replace (q * 8 + -8 + (t * 8 + 0)) with ((q + t - 1) * 8) by zlia. replace (q * 8 + 0) with (q * 8) by zlia. rewrite !Z_div_mult in * by zlia.
zcanon_simp. zlia. }
{ right. clear - A2 A3 A5 A6 A4 A8 A9 MZ. zlia. }
apply (PSR_runs Wy md1 X _ SH4 (PDX z) T_P6) in HR.
2:{ intros m HF. pose proof (Forall_inv HF) as B1. pose proof (Forall_inv_tail HF) as B2'. clear HF.
unfold cut, SH3 in B2'. cbn [flat_map app] in B2'. unfold cut1 in B2'. cbn [fst snd] in B2'.
assert (G1 : (SMv + 512 <? SHBv + UEv / 8) = true) by (clear - A2 A5 MZ; apply Z.ltb_lt; zlia).
assert (G2 : (SHBv + UEv / 8 + RLv / 8 <? SMv + 768) = false) by (clear - A2 A5 A6 MZ; apply Z.ltb_ge; zlia).
assert (G3 : (SHBv + ENDv / 8 <? SHBv + UEv / 8) = false) by (clear - A1 A2 A4 MZ; apply Z.ltb_ge; zlia).
assert (G4 : (SHBv + UEv / 8 + RLv / 8 <? SMv + MSv / 8) = false) by (clear - A3 MZ; apply Z.ltb_ge; zlia).
assert (G5 : (SMv <? SHBv + UEv / 8) = true) by (clear - A2 A5 MZ; apply Z.ltb_lt; zlia).
assert (G6 : (SHBv + UEv / 8 + RLv / 8 <? SMv + 512) = false) by (clear - A2 A5 A6 MZ; apply Z.ltb_ge; zlia).
assert (G7 : (SMv + 768 <? SHBv + UEv / 8) = true) by (clear - A2 A5 MZ; apply Z.ltb_lt; zlia).
assert (G8 : (SHBv + UEv / 8 + RLv / 8 <? SHBv + ENDv / 8) = false) by (clear - A1 A3 A4 A8 A9 MZ; apply Z.ltb_ge; zlia).
rewrite G1, G2, G3, G4, G5, G6, G7, G8 in B2'. cbn [app] in B2'.
pose proof (Forall_inv B2') as C1. pose proof (Forall_inv (Forall_inv_tail B2')) as C2. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail B2'))) as C3. clear B2'.
rewrite Z.min_l in C1 by (clear - A2 A5 MZ; zlia). rewrite Z.min_l in C2 by (clear - A2 A5 MZ; zlia). rewrite Z.min_r in C3 by (clear - A1 A2 A4 MZ; zlia).
rewrite <- A3 in B1. unfold SH4. apply Forall_cons; [exact B1|]. apply Forall_cons; [exact C1|]. apply Forall_cons; [exact C2|]. apply Forall_cons; [exact C3 | apply Forall_nil]. }
s_runS HR tfibtbl_rtA tfibtbl_rtA_ok 0x319c4 (runto 0x319c4 T_P6) HX HP4.
s_pin HR (22%bv : bv 5) (SOff aN8DS 0).
{ clear - NR Hn Z4 MZ. pin_zevS. rewrite EaN8D, E10, Hn. unfold w64. rewrite !unsigned_lit_small by zlia. zcanon_simp.
change (zcanon 281474976710648) with (2 ^ 48 - 8). rewrite land_m8_48 by zlia. unfold N8D in *.
pose proof (Z.div_mod n 8 ltac:(zlia)). pose proof (Z.mod_pos_bound n 8 ltac:(zlia)). rewrite Z.add_0_r. zcanon_simp. zlia. }
s_station HR T_P7.
s_runS HR tfibtbl_rtA tfibtbl_rtA_ok 0x53828 T_L5 HX HP4.
s_ladderW s_runS HR tfibtbl_rtA tfibtbl_rtA_ok 0x53a78 T_L5l T_L5lo T_L5h T_L5h2 T_L5h3a T_L5h3 T_L5hi T_R sL5 CLOB_Lt HX HP4.
apply SRr_ret. exact HR.
Qed.
Lemma segT2 : forall W' c, at_S Wy md1 X (PSR Wy SH2 (PDX z)) T_2 W' c -> SRr tfibsegs W' c (at_S Wy md1 X (PSR Wy SH4 (PDX z)) T_R).
Proof.
intros W1 c HR. pose proof SH_ok as (_ & _ & OK2). pose proof (PSR_stableS SH2 (PDX z) OK2 (PDX_stableS z)) as HP2.
assert (HX : forall a, WIN1S a -> X a) by (intros a Ha; apply HXW, WIN1S_WIN, Ha).
pose proof map_facts as (M1 & M2 & _). pose proof map_zoneN as MZ. pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & _).
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in M1, M2. unfold MALLOC_MAX in Z8.
pose proof high_facts as (_ & _ & F3 & F4 & F5 & F6 & _). ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kSpaceSize, kPrimResvSize in F3, F4, F5, F6.
s_runS HR tfibtbl_rtA tfibtbl_rtA_ok 0x31900 T_M0 HX HP2.
destruct Hmap_apart as (_ & _ & MP & _). unfold zdisjoint in MP. cbn [fst snd] in MP. unfold kPrimResvSize in MP.
destruct MP as [MP|MP].
- s_arm HR BC_LTU true (SOff aMAP 4096) (SOff aSB 0).
{ clear - MP M1 M2 Z8 F3 F4 F5 F6 MZ. arm_zevS. rewrite EaMAP, EaSB. unfold w64. rewrite !unsigned_lit_small by (try unfold SB in *; zlia). zcanon_simp. apply Z.ltb_lt. try unfold SB in *. zlia. }
s_runS HR tfibtbl_rtA tfibtbl_rtA_ok 0x31938 T_Ma HX HP2.
lazymatch type of HR with at_S ?Wx ?md ?X0 ?P ?ss ?W' ?c' =>
pose proof (at_S_forget Wx md X0 P ss W' c' sGA [11]%bv HR ltac:(unfold sHAV, sGA; zlia) eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as HR2; clear HR; rename HR2 into HR end.
s_noconds HR. s_station HR T_N. exact (segT2b _ _ HR).
- s_arm HR BC_LTU false (SOff aMAP 4096) (SOff aSB 0).
{ clear - MP M1 M2 Z8 F3 F4 F5 F6 MZ. arm_zevS. rewrite EaMAP, EaSB. unfold w64. rewrite !unsigned_lit_small by (try unfold SB in *; zlia). zcanon_simp. apply Z.ltb_ge. try unfold SB in *. zlia. }
s_runS HR tfibtbl_rtA tfibtbl_rtA_ok 0x31910 (runto 0x31910 (arm BC_LTU false (SOff aMAP 4096) (SOff aSB 0) T_M0)) HX HP2.
s_arm HR BC_GEU true (SOff aMAP 4096) (SOff aSB 137438953472).
{ clear - MP M1 M2 Z8 F3 F4 F5 F6 MZ. arm_zevS. rewrite EaMAP, EaSB. unfold w64. rewrite !unsigned_lit_small by (try unfold SB in *; zlia). zcanon_simp.
rewrite (proj2 (Z.ltb_ge _ _)); [reflexivity|]. try unfold SB in *. zlia. }
s_runS HR tfibtbl_rtA tfibtbl_rtA_ok 0x31938 T_Mb HX HP2.
lazymatch type of HR with at_S ?Wx ?md ?X0 ?P ?ss ?W' ?c' =>
pose proof (at_S_forget Wx md X0 P ss W' c' sGA [11]%bv HR ltac:(unfold sHAV, sGA; zlia) eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as HR2; clear HR; rename HR2 into HR end.
s_noconds HR. s_station HR T_N. exact (segT2b _ _ HR).
Qed.
End T2.
End g.
End f.
