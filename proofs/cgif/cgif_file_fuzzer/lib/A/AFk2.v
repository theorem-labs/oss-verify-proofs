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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK0j.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AFid AFie AFif AFih AFjv AFjw AFjx AFjh AFjn AFjo AFjk AFjl AFjp AFjt.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Set Printing Depth 50. Set Printing Width 180.
Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
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
Section h.
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
Variable XZ : Z -> Prop.
Hypothesis HXZ1 : forall a, WIN a -> XZ a.
Hypothesis HXZ2 : forall a, XZ a -> WIN a \/ ~ (TFIB_IMG_LO <= a < TFIB_IMG_END).
Lemma WIN1R_XZ : forall a, WIN1R a -> XZ a.
Proof. intros a Ha. exact (HXZ1 a (WIN1R_WIN a Ha)). Qed.
Definition DCELLS : Prop :=
val_mem tfibsegs (mrestrict (w_H W) mem0) 0x1cd09 8 0x612079726f6d656d /\ val_mem tfibsegs (mrestrict (w_H W) mem0) 0x1cd11 8 0x7365726464612074 /\
val_mem tfibsegs (mrestrict (w_H W) mem0) 0x1cd19 4 0x70252073 /\ val_mem tfibsegs (mrestrict (w_H W) mem0) 0x1cd1d 1 0 /\
val_mem tfibsegs (mrestrict (w_H W) mem0) 0x20b7c 4 0x45f54.
Hypothesis HDC : DCELLS.
Local Ltac s_runR HR tbl tblok stop ss' HX HP :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let st := eval vm_compute in (snd (sym_run_toN_sh tfibsegs tbl FUEL stop ss)) in
eapply SRr_bind;
[ eapply (at_S_runR Wx tbl tblok stop md X P ss ss' st W' c' HR);
[ vm_compute; reflexivity | exact I | exact HX | vm_compute; reflexivity | exact HP | vm_compute; reflexivity ]
| clear HR; let W2 := fresh "W" in let c2 := fresh "c" in intros W2 c2 _ HR ] end.
Definition PZ : (word -> option byte) -> Prop := PSR Wy SH2 (fun _ => True).
Lemma PZ_stable : pstable WIN1R PZ.
Proof. pose proof SH_ok as (_ & _ & OK2). exact (PSR_stable Wy SH2 (fun _ => True) OK2 rstable_true). Qed.
Lemma img_vis : forall (Wx : world tfibsegs) (a : Z), 0 <= a < 2 ^ 64 -> find_segment tfibsegs a 1 <> None -> w_H Wx (Z_to_bv 64 a) = false.
Proof.
clearP. intros Wx a Ha Hs. destruct (w_H Wx (Z_to_bv 64 a)) eqn:E; [|reflexivity]. exfalso. apply Hs.
pose proof (w_Hoff Wx (Z_to_bv 64 a) E) as X. rewrite unsigned_lit_small in X by exact Ha. exact X.
Qed.
Definition in_dimg (x : Z) : Prop :=
(0x1cd09 <= x < 0x1cd1e) \/ (0x20b7c <= x < 0x20b80) \/ (0x103d8 <= x < 0x103e0) \/ (0x9dfd8 <= x < 0x9dfe0) \/ (0x137b1c <= x < 0x137b20).
Lemma in_dimg_facts : forall x, in_dimg x -> 0 <= x < 2 ^ 64 /\ find_segment tfibsegs x 1 <> None /\ ~ XZ x.
Proof.
intros x R. unfold in_dimg in R. pose proof high_facts as (F1 & _ & _ & _ & _ & _ & _ & _ & F9 & _). pose proof map_facts as (M1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & _). pose proof map_zoneN as MZ.
destruct Hsp as (S1' & _). pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7). pose proof BSLv_range as HB.
split; [zlia|]. split.
- assert (SEG : forall y, 0x10000 <= y < 0x5fb000 -> find_segment tfibsegs y 1 <> None).
{ clear. intros y Hy. change tfibsegs with AB1h.TSEGS. unfold AB1h.TSEGS, Asan.M.loaded_segments.
cbn -[Z_to_bv bv_unsigned Z.leb Z.ltb Z.add].
repeat match goal with |- context [((?x <=? y) && (y + 1 <=? ?z))%bool] => destruct (Z.leb_spec x y); destruct (Z.leb_spec (y + 1) z); cbn [andb] end;
try discriminate; exfalso; zlia. }
apply SEG. zlia.
- intros HXa. destruct (HXZ2 x HXa) as [HW|HO]; [| apply HO; clear - R; unfold in_dimg, TFIB_IMG_LO, TFIB_IMG_END in *; zlia].
revert HW. pose proof Hidx as HI. clear - R F1 F9 M1 SM1 S1' T7 HB HI MZ. intros HW. unfold WIN, WINT, WINI, WINM in HW.
unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighShadowBeg, QSv, ASTACK, t_unwinding, TFIB_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex in *.
try unfold Qb in *. try unfold T in *. try unfold sp0 in *.
destruct HW as [X|[X|[X|X]]]; [zlia | zlia | zlia | zlia].
Qed.
Lemma val_mem_xfer_img : forall (m : word -> option byte) a (w : nat) v,
val_mem tfibsegs (mrestrict (w_H W) mem0) a w v ->
(forall x : word, ~ XZ (bv_unsigned x) -> m x = mem0 x) ->
(forall i, 0 <= i < Z.of_nat w -> in_dimg (a + i)) ->
val_mem tfibsegs (mrestrict (w_H Wy) m) a w v.
Proof.
intros m a w v HV MEQ Hin k Hk. rewrite <- (HV k Hk). destruct (in_dimg_facts (a + Z.of_nat k) (Hin (Z.of_nat k) ltac:(zlia))) as (Ra & Fs & Nw).
unfold mbyte, mrestrict. rewrite (img_vis Wy _ Ra Fs), (img_vis W _ Ra Fs). rewrite MEQ; [reflexivity|]. rewrite unsigned_lit_small by exact Ra. exact Nw.
Qed.
Definition dnewb (lo hi : Z) (r : YP09.region) : bool :=
match YP09.r_base r with
| None => (YP09.r_hi r <=? lo) || (hi <=? YP09.r_lo r)
| Some k => (Nat.eqb k 2 && (-16384 <=? YP09.r_lo r))
|| (((Nat.eqb k 32 && (YP09.r_hi r <=? kThreadObjSize)) || (Nat.eqb k 33 && (YP09.r_hi r <=? 256))
|| (Nat.eqb k aMAP && (YP09.r_hi r <=? 6144)) || (Nat.eqb k aQS && (YP09.r_hi r <=? 8))) && (0 <=? YP09.r_lo r))
|| (Nat.eqb k aBSL && (0 <=? YP09.r_lo r) && (YP09.r_hi r <=? 8))
end.
Lemma dnewb_sound : forall (E' : env) lo hi nr r, env_agree sHAV E0 E' ->
YP09.r_base nr = None -> YP09.r_lo nr = lo -> YP09.r_hi nr = hi -> 0x10000 <= lo -> hi <= 0x5fb000 -> (hi <= 0xa2ac0 \/ 0xa2b40 <= lo) ->
dnewb lo hi r = true -> extent_disjoint E' nr r.
Proof.
intros E' lo hi nr r [HE _] Hb Hlo Hhi B0 B1 B2 Hd. unfold extent_disjoint. rewrite Hb, Hlo, Hhi. cbn [base_val].
unfold dnewb in Hd. destruct (YP09.r_base r) as [k|]; cbn [base_val].
- pose proof high_facts as (F1 & F2 & _ & _ & _ & _ & F7 & F8 & F9 & F10 & _). pose proof map_facts as (M1 & M2 & _). pose proof map_zoneN as MZ. pose proof BSLv_range as HB.
pose proof Hidx as HI. pose proof Hres as [HRS _]. destruct Hsp as (S1' & _). pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7). pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & _).
apply Bool.orb_prop in Hd. destruct Hd as [Hd|Hd]; [apply Bool.orb_prop in Hd; destruct Hd as [Hd|Hd]|].
+   apply andb_prop in Hd as [Hk Hl]. apply Nat.eqb_eq in Hk. subst k. apply Z.leb_le in Hl.
rewrite (HE 2%nat ltac:(unfold sHAV; zlia)), E2. left. clear - S1' T7 Hl B1 MZ. unfold ASTACK in *. numconst. try unfold sp0 in *. zlia.
+   apply andb_prop in Hd as [Hk Hl0]. apply Z.leb_le in Hl0.
repeat (apply Bool.orb_prop in Hk; destruct Hk as [Hk|Hk]); apply andb_prop in Hk as [Hk Hh]; apply Nat.eqb_eq in Hk; apply Z.leb_le in Hh; subst k.
* rewrite (HE 32%nat ltac:(unfold sHAV; zlia)), EaT. unfold w64. rewrite unsigned_lit_small by (clear - F1 F2 MZ; numconst; try unfold T in *; zlia).
pose proof F1 as Z3. unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize in Z3, Hh. clear - Z3 Hl0 Hh B0 B1 MZ. try unfold T in *. zlia.
* rewrite (HE 33%nat ltac:(unfold sHAV; zlia)), EaC. unfold w64. rewrite unsigned_lit_small by (clear - F7 F8 MZ; numconst; zlia).
pose proof F7 as Z3. unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Z3. clear - Z3 Hl0 Hh B0 B1 MZ. zlia.
* unfold aMAP. rewrite (HE 45%nat ltac:(unfold sHAV; zlia)), EaMAP. unfold w64. rewrite unsigned_lit_small by (clear - M1 M2 Z8 MZ; numconst; unfold MALLOC_MAX in *; zlia).
pose proof (mzone_zone3 _ _ (proj2 Hmap)) as Z3. unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, MALLOC_MAX in Z3, Z8. clear - Z3 Z8 Hl0 Hh B0 B1 MZ. zlia.
* unfold aQS. rewrite (HE 52%nat ltac:(unfold sHAV; zlia)), EaQS. unfold w64.
rewrite unsigned_lit_small by (clear - F9 F10 HI MZ; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, QSv, kHighMemBeg, ASAN_CEIL, kPtrArrayResv, kMaxNumChunks in *; try unfold Qb in *; zlia).
pose proof F9 as Z3. unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kPtrArrayResv, kMaxNumChunks in Z3, HI, HRS. unfold QSv in *. try unfold Qb in *. clear - Z3 HI HRS Hl0 Hh B0 B1 MZ. zlia.
+ apply andb_prop in Hd as [Hd Hh]. apply andb_prop in Hd as [Hk Hl]. apply Nat.eqb_eq in Hk. subst k. apply Z.leb_le in Hl. apply Z.leb_le in Hh.
unfold aBSL. rewrite (HE 55%nat ltac:(unfold sHAV; zlia)), EaBSL. unfold w64. rewrite unsigned_lit_small by (clear - HB MZ; unfold TFIB_INST in *; zlia).
clear - HB Hl Hh B2 B0 B1 MZ. unfold TFIB_INST in HB. zlia.
- clear - Hd. repeat (apply Bool.orb_prop in Hd; destruct Hd as [Hd|Hd]); apply Z.leb_le in Hd; zlia.
Qed.
Lemma pat_word : forall m, exists w, val_mem tfibsegs (mrestrict (w_H Wy) m) 0x103d8 8 w /\ 0 <= w < 2 ^ 64.
Proof.
clearP. intros m. destruct pat_bytes as [bs Hbs]. destruct (img_word (w_H Wy) m 0x103d8 bs Hbs) as [w Hw].
exists (w mod 2 ^ 64). split; [exact (val_mem_mod8 _ _ _ Hw) | apply Z.mod_pos_bound; zlia].
Qed.
Theorem D_1_ok : idx = res -> forall c, at_S Wy md1 XZ PZ D_0 Wy c -> at_S Wy md1 XZ PZ D_1 Wy c.
Proof.
intros Heq c HR. pose proof HDC as (C1 & C2 & C3 & C4 & C5).
pose proof (cell_lit 0x9dfd8 8 1 ltac:(vm_compute; reflexivity)) as G1. pose proof (cell_lit 0x137b1c 4 0 ltac:(vm_compute; reflexivity)) as G2.
assert (HR1 : at_S Wy md1 XZ PZ (addreg R_gate2 (addreg R_gate1 (addreg R_pat (addreg R_jt (addreg R_fmt D_0))))) Wy c).
{ destruct HR as (EW & ms & mat & E' & Ec & HE & HS & MEQ & PRS & HPm).
destruct (pat_word (ms_mem ms)) as (wp & Hwp & Rwp).
set (E'' := havoc E' aPAT [w64 wp]).
assert (HE'' : env_agree sHAV E0 E'').
{ destruct HE as [HE1 HE2]. split; [| unfold E'', havoc; cbn [ed]; exact HE2]. intros k Hk. unfold E''. rewrite ew_havoc_old by (unfold aPAT, sHAV in *; zlia). exact (HE1 k Hk). }
assert (AG : env_agree aPAT E' E'') by (split; [intros k Hk; unfold E''; apply ew_havoc_old; exact Hk | reflexivity]).
assert (HS'' : st_ok tfibsegs E'' D_0 (restrict (w_H Wy) ms)) by (exact (st_ok_agree tfibsegs aPAT E' E'' D_0 _ HS AG ltac:(vm_compute; reflexivity))).
split; [exact EW|]. exists ms, mat, E''. split; [exact Ec|]. split; [exact HE''|]. split; [| exact (conj MEQ (conj PRS HPm))].
assert (X1 := val_mem_xfer_img (ms_mem ms) _ _ _ C1 MEQ ltac:(intros i Hi; unfold in_dimg; zlia)).
assert (X2 := val_mem_xfer_img (ms_mem ms) _ _ _ C2 MEQ ltac:(intros i Hi; unfold in_dimg; zlia)).
assert (X3 := val_mem_xfer_img (ms_mem ms) _ _ _ C3 MEQ ltac:(intros i Hi; unfold in_dimg; zlia)).
assert (X4 := val_mem_xfer_img (ms_mem ms) _ _ _ C4 MEQ ltac:(intros i Hi; unfold in_dimg; zlia)).
assert (X5 := val_mem_xfer_img (ms_mem ms) _ _ _ C5 MEQ ltac:(intros i Hi; unfold in_dimg; zlia)).
assert (X6 := val_mem_xfer_img (ms_mem ms) _ _ _ G1 MEQ ltac:(intros i Hi; unfold in_dimg; zlia)).
assert (X7 := val_mem_xfer_img (ms_mem ms) _ _ _ G2 MEQ ltac:(intros i Hi; unfold in_dimg; zlia)).
Local Ltac radd HS EE HEE RR lo hi :=
apply st_ok_add_region; [exact HS | vm_compute; reflexivity | |
apply all_disjoint_of_forall; intros r2 Hr2;
refine (dnewb_sound EE lo hi RR r2 HEE eq_refl eq_refl eq_refl ltac:(clear; zlia) ltac:(clear; zlia) ltac:(clear; zlia) _);
lazymatch goal with |- dnewb _ _ _ = true =>
revert r2 Hr2; apply (proj1 (forallb_forall _ _)); vm_compute; reflexivity end ].
assert (HSa : st_ok tfibsegs E'' (addreg R_fmt D_0) (restrict (w_H Wy) ms)).
{ unfold addreg. radd HS'' E'' HE'' R_fmt 0x1cd09 (0x1cd09 + 21).
unfold R_fmt, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict].
split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia|].
repeat (apply Forall_cons; [eapply chunk_ok_val; [reflexivity | cbn; zlia | cbn; zlia | rewrite Z.add_0_l; cbn [N.to_nat Pos.to_nat]; first [exact X1 | exact X2 | exact X3 | exact X4]] |]). apply Forall_nil. }
assert (HSb : st_ok tfibsegs E'' (addreg R_jt (addreg R_fmt D_0)) (restrict (w_H Wy) ms)).
{ unfold addreg at 1. radd HSa E'' HE'' R_jt 0x20b7c 0x20b80.
unfold R_jt, lit4, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict].
split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia|]. apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [reflexivity | cbn; zlia | cbn; zlia | rewrite Z.add_0_l; exact X5]. }
assert (HSc : st_ok tfibsegs E'' (addreg R_pat (addreg R_jt (addreg R_fmt D_0))) (restrict (w_H Wy) ms)).
{ unfold addreg at 1. radd HSb E'' HE'' R_pat 0x103d8 0x103e0.
unfold R_pat, atom8, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict].
split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia|]. apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [| cbn; exact Rwp | cbn; zlia | rewrite Z.add_0_l; exact Hwp].
cbn [sv_denot]. unfold E'', havoc. cbn [ew Nat.ltb Nat.leb aPAT Nat.sub nth]. unfold w64. rewrite Zbv_add_unsigned. f_equal. zlia. }
assert (HSd : st_ok tfibsegs E'' (addreg R_gate1 (addreg R_pat (addreg R_jt (addreg R_fmt D_0)))) (restrict (w_H Wy) ms)).
{ unfold addreg at 1. radd HSc E'' HE'' R_gate1 0x9dfd8 0x9dfe0.
unfold R_gate1, lit8, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict].
split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia|]. apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [reflexivity | cbn; zlia | cbn; zlia | rewrite Z.add_0_l; exact X6]. }
unfold addreg at 1. radd HSd E'' HE'' R_gate2 0x137b1c 0x137b20.
unfold R_gate2, lit4, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict].
split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia|]. apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [reflexivity | cbn; zlia | cbn; zlia | rewrite Z.add_0_l; exact X7]. }
clear HR. rename HR1 into HR.
s_pin HR (18%bv : bv 5) (SOff aQS 0).
{ pose proof (QR_facts Heq) as (E1 & _ & QA & F9 & Q5 & F10 & _). pose proof (TQ_val Heq) as TV. unfold TQ in TV.
rewrite U_SAlu in TV. cbn [zalu_raw] in TV. change (U E0 (SLit 0)) with 0 in TV. rewrite Z.add_0_r in TV.
rewrite zcanon_id in TV by (apply U_range).
lazymatch goal with |- U E0 ?l = U E0 _ =>
change (U E0 l = U E0 (SAlu ALU_AND (SAlu ALU_ADD (SOff aQ 0) (SAlu ALU_SLL (SOff aNCH 0) (SLit 3))) (SLit 18446744073709547520))) end.
rewrite TV. rewrite U_SOff. unfold aQS. rewrite EaQS. unfold w64.
rewrite unsigned_lit_small by (clear - F9 Q5 F10; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kPtrArrayResv in *; try unfold Qb in *; zlia).
rewrite Z.add_0_r. apply zcanon_id. clear - F9 Q5 F10; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, M64, kHighMemBeg, ASAN_CEIL, kPtrArrayResv in *; try unfold Qb in *; zlia. }
s_station HR D_1. exact HR.
Qed.
Lemma land15_lor240 : forall x, Z.land (zcanon (Z.lor 240 x)) 15 = x mod 16.
Proof.
clear. intros x. unfold zcanon, M64. rewrite <- (Z.land_ones _ 64) by zlia.
rewrite <- Z.land_assoc. change (Z.land (Z.ones 64) 15) with 15.
rewrite Z.land_lor_distr_l. change (Z.land 240 15) with 0. rewrite Z.lor_0_l.
change 15 with (Z.ones 4). rewrite Z.land_ones by zlia. reflexivity.
Qed.
Lemma land15_lorc : forall c x, Z.land (zcanon (Z.lor c x)) 15 = Z.lor (Z.land c 15) (x mod 16).
Proof.
clear. intros c x. unfold zcanon, M64. rewrite <- (Z.land_ones _ 64) by zlia.
rewrite <- Z.land_assoc. change (Z.land (Z.ones 64) 15) with 15.
rewrite Z.land_lor_distr_l. f_equal. change 15 with (Z.ones 4). rewrite Z.land_ones by zlia. reflexivity.
Qed.
Lemma at_S_tighten : forall (Wx : world tfibsegs) md X0 P ss W' c' (k : nat) (f : afact),
at_S Wx md X0 P ss W' c' -> (k < sHAV)%nat -> afact_ok E0 k f -> at_S Wx md X0 P (AFih.tighten k f ss) W' c'.
Proof.
clearP. intros Wx md X0 P ss W' c' k f HR Hk Hf.
destruct HR as (-> & ms & mat & E' & -> & HE & HS & MEQ & PRS & HPm).
split; [reflexivity|]. exists ms, mat, E'. split; [reflexivity|]. split; [exact HE|]. split; [|exact (conj MEQ (conj PRS HPm))].
unfold AFih.tighten. apply (st_ok_facts tfibsegs E' ss _ _ HS).
pose proof (st_ok_facts_ok tfibsegs E' ss _ HS) as (HA & HC & HL). split; [| exact (conj HC HL)].
cbn [f_atoms atoms_ok]. split; [| exact HA].
unfold afact_ok in Hf |- *. rewrite (proj1 HE k Hk). exact Hf.
Qed.
Lemma addzero_region_ok : forall (E : env) (m : word -> option byte) b lo zn (r : YP09.region),
region_ok tfibsegs E m r -> (AFih.zmatch b lo zn r = true -> AFih.zbytes_ok lo zn (YP09.r_chunks r) = true) ->
region_ok tfibsegs E m (AFih.addzero_r b lo zn r).
Proof.
clearP. intros E m b lo zn r (B1 & B2 & WR & CK) Hz. unfold AFih.addzero_r.
destruct (AFih.zmatch b lo zn r) eqn:Em; [| exact (conj B1 (conj B2 (conj WR CK)))].
specialize (Hz eq_refl). unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
split; [exact B1|]. split; [exact B2|]. split; [exact WR|]. constructor; [| exact CK].
intros i Hi. cbn [YP09.c_off YP09.c_val YP09.c_len YP09.cv_len] in Hi |- *. exists (Z_to_bv 8 0). split; [reflexivity|].
unfold AFih.zbytes_ok in Hz.
pose proof (forallb_seq_In _ _ (Z.to_nat i) Hz ltac:(apply Z2Nat.inj_lt; lia)) as X. cbn beta in X. rewrite Z2Nat.id in X by lia.
apply existsb_exists in X as (c & Hc & Zc). destruct c as [off cv]. unfold AFih.zbyte_chunk in Zc. cbn [YP09.c_off YP09.c_val] in Zc.
apply andb_prop in Zc as [Eo Ev]. apply Z.eqb_eq in Eo. destruct cv as [w v| | |]; try discriminate Ev.
apply andb_prop in Ev as [Ew Ev]. apply N.eqb_eq in Ew. apply sv_eqb_eq in Ev. subst v w off.
pose proof (proj1 (Forall_forall _ _) CK _ Hc) as CC.
destruct (CC 0 ltac:(cbn; lia)) as (b0 & Hb1 & Hb2). cbn [YP09.c_off YP09.c_val cbyte] in Hb1, Hb2.
replace (byte_of_word (sv_denot E (SLit 0)) 0) with (Z_to_bv 8 0) in Hb1 by (vm_compute; reflexivity). injection Hb1 as <-.
rewrite Z.add_0_r in Hb2. rewrite Z.add_assoc in Hb2. exact Hb2.
Qed.
Lemma addzero_regions_wf : forall b lo zn rs, regions_wf rs = true -> regions_wf (map (AFih.addzero_r b lo zn) rs) = true.
Proof.
clearP. intros b lo zn rs. induction rs as [|r rs IH]; intros H; [reflexivity|]. cbn [map regions_wf] in H |- *.
apply andb_prop in H as [Hr Hrs]. rewrite (IH Hrs), Bool.andb_true_r.
unfold AFih.addzero_r. destruct (AFih.zmatch b lo zn r) eqn:Em; [|exact Hr].
unfold AFih.zmatch in Em. apply andb_prop in Em as [Em En]. apply andb_prop in Em as [Em Ehi]. apply andb_prop in Em as [_ Elo].
set (nr := YP09.mkRegion _ _ _ _ _ _).
assert (FE : forall l, forallb (YP09.chunk_inside nr) l = forallb (YP09.chunk_inside r) l).
{ intros l. induction l as [|c l IHl]; [reflexivity|]. cbn [forallb]. rewrite IHl. reflexivity. }
unfold YP09.region_wf in Hr |- *. change (YP09.r_chunks nr) with (YP09.mkChunk lo (CZero zn) :: YP09.r_chunks r).
cbn [forallb]. rewrite FE. change (YP09.r_lo nr) with (YP09.r_lo r). change (YP09.r_hi nr) with (YP09.r_hi r).
change (YP09.r_wlo nr) with (YP09.r_wlo r). change (YP09.r_whi nr) with (YP09.r_whi r).
apply andb_prop in Hr as [H12 H3]. rewrite H12, H3, Bool.andb_true_r. cbn [andb].
unfold YP09.chunk_inside. cbn [YP09.c_off YP09.c_len YP09.c_val YP09.cv_len]. change (YP09.r_lo nr) with (YP09.r_lo r). change (YP09.r_hi nr) with (YP09.r_hi r).
apply Z.leb_le in Elo. apply Z.leb_le in Ehi. apply Z.leb_le in En.
rewrite (proj2 (Z.leb_le _ _) Elo), (proj2 (Z.leb_le _ _) Ehi), (proj2 (Z.leb_le _ _) En). reflexivity.
Qed.
Lemma addzero_all_disjoint : forall E b lo zn r rs, all_disjoint E r rs ->
all_disjoint E (AFih.addzero_r b lo zn r) (map (AFih.addzero_r b lo zn) rs).
Proof.
clearP. intros E b lo zn r rs. assert (EXT : forall q, YP09.r_base (AFih.addzero_r b lo zn q) = YP09.r_base q /\
YP09.r_lo (AFih.addzero_r b lo zn q) = YP09.r_lo q /\ YP09.r_hi (AFih.addzero_r b lo zn q) = YP09.r_hi q).
{ intros q. unfold AFih.addzero_r. destruct (AFih.zmatch b lo zn q); repeat split; reflexivity. }
induction rs as [|r' rs IH]; intros H; [exact I|]. cbn [map all_disjoint] in H |- *. destruct H as [H1 H2]. split; [| exact (IH H2)].
unfold extent_disjoint in H1 |- *. destruct (EXT r) as (A1 & A2 & A3). destruct (EXT r') as (C1 & C2 & C3). rewrite A1, A2, A3, C1, C2, C3. exact H1.
Qed.
Lemma addzero_pairwise : forall E b lo zn rs, pairwise_disjoint E rs -> pairwise_disjoint E (map (AFih.addzero_r b lo zn) rs).
Proof.
clearP. intros E b lo zn rs. induction rs as [|r rs IH]; intros H; [exact I|]. cbn [map pairwise_disjoint] in H |- *.
destruct H as [H1 H2]. split; [exact (addzero_all_disjoint E b lo zn r rs H1) | exact (IH H2)].
Qed.
Lemma at_S_addzero : forall (Wx : world tfibsegs) md X0 P ss W' c' b lo zn,
at_S Wx md X0 P ss W' c' -> AFih.addzero_ok b lo zn ss = true -> at_S Wx md X0 P (AFih.addzero b lo zn ss) W' c'.
Proof.
clearP. intros Wx md X0 P ss W' c' b lo zn HR Hok.
destruct HR as (-> & ms & mat & E' & -> & HE & HS & MEQ & PRS & HPm).
split; [reflexivity|]. exists ms, mat, E'. split; [reflexivity|]. split; [exact HE|]. split; [|exact (conj MEQ (conj PRS HPm))].
destruct HS as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & (WF' & O & D) & H9).
unfold AFih.addzero, st_ok. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts]. repeat (split; [assumption|]). split; [| exact H9].
split; [exact (addzero_regions_wf b lo zn _ WF')|]. split; [| exact (addzero_pairwise _ b lo zn _ D)].
apply Forall_forall. intros r' Hin. apply in_map_iff in Hin as (r & <- & Hr).
apply (addzero_region_ok _ _ b lo zn r (proj1 (Forall_forall _ _) O r Hr)). intros Zm.
unfold AFih.addzero_ok in Hok. pose proof (proj1 (forallb_forall _ _) Hok r Hr) as X. cbn beta in X. rewrite Zm in X. exact X.
Qed.
Lemma hexfact_ok : forall d, 16 ^ (d - 1) <= QSv <= 16 ^ d - 8 -> afact_ok E0 aQS (AFih.hexfact d).
Proof.
intros d Hd. pose proof (QR_facts) as QF.
unfold afact_ok, AFih.hexfact. cbn [af_lo af_hi af_al2]. change (ew E0 aQS) with (ew E0 52). rewrite EaQS. unfold w64.
pose proof Hidx as HI. pose proof Hres as [HRS _]. pose proof high_facts as (_ & _ & _ & _ & _ & _ & _ & _ & F9 & F10 & _).
rewrite unsigned_lit_small by (clear - F9 F10 HI HRS; unfold QSv in *; try unfold Qb in *; zlia).
split; [exact Hd|]. split; [| lia]. change (2 ^ 3) with 8.
pose proof high_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F11 & _). unfold page_aligned in F11. apply Z.mod_divide in F11 as [q Hq]; [|lia].
unfold QSv. try unfold Qb. rewrite Hq. replace (q * 4096 + 8 * idx) with ((q * 512 + idx) * 8) by lia. apply Z_mod_mult.
Qed.
Lemma segD1_6 : forall (W' : world tfibsegs) c, at_S Wy md1 XZ PZ D_1_6 W' c -> SRr tfibsegs W' c (at_S Wy md1 XZ PZ DG6_0).
Proof.
intros W' c HR. pose proof WIN1R_XZ as HX. pose proof PZ_stable as HP.
s_runR HR tfibtbl_rtD tfibtbl_rtD_ok 0x63970 D_M6 HX HP.
s_arm HR BC_EQ false MS_AL6 (SLit 0).
{ destruct Hsp as (S1 & _ & _ & S4). pose proof (u64_range (getr regs0 2)) as U2. pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7).
clear - S1 S4 U2 T7. unfold MS_AL6. arm_zevS. rewrite E2. numconst. try unfold sp0 in *.
repeat match goal with |- context [zcanon ?x] => lazymatch x with context [ew _ _] => fail | context [getr _ _] => fail | _ => let y := eval vm_compute in (zcanon x) in change (zcanon x) with y end end.
rewrite (zcanon_id (bv_unsigned (getr regs0 2) + _)) by (unfold M64; zlia).
rewrite land15_lor240.
lazymatch goal with |- context [(?a mod 16)] =>
pose proof (Z.div_mod a 16 ltac:(zlia)) as D1; pose proof (Z.mod_pos_bound a 16 ltac:(zlia)) as B1 end.
pose proof (Z.div_mod (bv_unsigned (getr regs0 2)) 16 ltac:(zlia)) as D0.
rewrite zcanon_id by (unfold M64; zlia). apply Z.eqb_neq. zlia. }
s_runR HR tfibtbl_rtD tfibtbl_rtD_ok 0x63974 D_X6 HX HP.
s_runR HR tfibtbl_rtD tfibtbl_rtD_ok 0x63970 D_P6 HX HP.
s_arm HR BC_EQ false MS_PAD6 (SLit 0).
{ destruct Hsp as (S1 & _ & _ & S4). pose proof (u64_range (getr regs0 2)) as U2. pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7).
clear - S1 S4 U2 T7. unfold MS_PAD6. arm_zevS. rewrite E2. numconst. try unfold sp0 in *.
repeat match goal with |- context [zcanon ?x] => lazymatch x with context [ew _ _] => fail | context [getr _ _] => fail | _ => let y := eval vm_compute in (zcanon x) in change (zcanon x) with y end end.
rewrite (zcanon_id (bv_unsigned (getr regs0 2) + _)) by (unfold M64; lia).
rewrite land15_lorc. rewrite (Z.add_mod (bv_unsigned (getr regs0 2)) (-2984) 16) by zlia. rewrite S4. vm_compute. reflexivity. }
s_runR HR tfibtbl_rtD tfibtbl_rtD_ok 0x67188 D_R6 HX HP.
apply (at_S_addzero _ _ _ _ _ _ _ (Some 2%nat) (-2984) 48) in HR; [| vm_compute; reflexivity].
replace (AFih.addzero (Some 2%nat) (-2984) 48 D_R6) with D_Z6 in HR by (vm_compute; reflexivity).
s_runR HR tfibtbl_rtD tfibtbl_rtD_ok 0x67294 DG6r HX HP.
s_noconds HR. s_station HR DG6_0. apply SRr_ret. exact HR.
Qed.
Lemma segD1_7 : forall (W' : world tfibsegs) c, at_S Wy md1 XZ PZ D_1_7 W' c -> SRr tfibsegs W' c (at_S Wy md1 XZ PZ DG7_0).
Proof.
intros W' c HR. pose proof WIN1R_XZ as HX. pose proof PZ_stable as HP.
s_runR HR tfibtbl_rtD tfibtbl_rtD_ok 0x63970 D_M7 HX HP.
s_arm HR BC_EQ false MS_AL7 (SLit 0).
{ destruct Hsp as (S1 & _ & _ & S4). pose proof (u64_range (getr regs0 2)) as U2. pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7).
clear - S1 S4 U2 T7. unfold MS_AL7. arm_zevS. rewrite E2. numconst. try unfold sp0 in *.
repeat match goal with |- context [zcanon ?x] => lazymatch x with context [ew _ _] => fail | context [getr _ _] => fail | _ => let y := eval vm_compute in (zcanon x) in change (zcanon x) with y end end.
rewrite (zcanon_id (bv_unsigned (getr regs0 2) + _)) by (unfold M64; zlia).
rewrite land15_lor240.
lazymatch goal with |- context [(?a mod 16)] =>
pose proof (Z.div_mod a 16 ltac:(zlia)) as D1; pose proof (Z.mod_pos_bound a 16 ltac:(zlia)) as B1 end.
pose proof (Z.div_mod (bv_unsigned (getr regs0 2)) 16 ltac:(zlia)) as D0.
rewrite zcanon_id by (unfold M64; zlia). apply Z.eqb_neq. zlia. }
s_runR HR tfibtbl_rtD tfibtbl_rtD_ok 0x63974 D_X7 HX HP.
s_runR HR tfibtbl_rtD tfibtbl_rtD_ok 0x63970 D_P7 HX HP.
s_arm HR BC_EQ false MS_PAD7 (SLit 0).
{ destruct Hsp as (S1 & _ & _ & S4). pose proof (u64_range (getr regs0 2)) as U2. pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7).
clear - S1 S4 U2 T7. unfold MS_PAD7. arm_zevS. rewrite E2. numconst. try unfold sp0 in *.
repeat match goal with |- context [zcanon ?x] => lazymatch x with context [ew _ _] => fail | context [getr _ _] => fail | _ => let y := eval vm_compute in (zcanon x) in change (zcanon x) with y end end.
rewrite (zcanon_id (bv_unsigned (getr regs0 2) + _)) by (unfold M64; lia).
rewrite land15_lorc. rewrite (Z.add_mod (bv_unsigned (getr regs0 2)) (-2976) 16) by zlia. rewrite S4. vm_compute. reflexivity. }
s_runR HR tfibtbl_rtD tfibtbl_rtD_ok 0x67188 D_R7 HX HP.
apply (at_S_addzero _ _ _ _ _ _ _ (Some 2%nat) (-2976) 40) in HR; [| vm_compute; reflexivity].
replace (AFih.addzero (Some 2%nat) (-2976) 40 D_R7) with D_Z7 in HR by (vm_compute; reflexivity).
s_runR HR tfibtbl_rtD tfibtbl_rtD_ok 0x67294 DG7r HX HP.
s_noconds HR. s_station HR DG7_0. apply SRr_ret. exact HR.
Qed.
Lemma segD1_8 : forall (W' : world tfibsegs) c, at_S Wy md1 XZ PZ D_1_8 W' c -> SRr tfibsegs W' c (at_S Wy md1 XZ PZ DG8_0).
Proof.
intros W' c HR. pose proof WIN1R_XZ as HX. pose proof PZ_stable as HP.
s_runR HR tfibtbl_rtD tfibtbl_rtD_ok 0x63970 D_M8 HX HP.
s_arm HR BC_EQ false MS_AL8 (SLit 0).
{ destruct Hsp as (S1 & _ & _ & S4). pose proof (u64_range (getr regs0 2)) as U2. pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7).
clear - S1 S4 U2 T7. unfold MS_AL8. arm_zevS. rewrite E2. numconst. try unfold sp0 in *.
repeat match goal with |- context [zcanon ?x] => lazymatch x with context [ew _ _] => fail | context [getr _ _] => fail | _ => let y := eval vm_compute in (zcanon x) in change (zcanon x) with y end end.
rewrite (zcanon_id (bv_unsigned (getr regs0 2) + _)) by (unfold M64; zlia).
rewrite land15_lor240.
lazymatch goal with |- context [(?a mod 16)] =>
pose proof (Z.div_mod a 16 ltac:(zlia)) as D1; pose proof (Z.mod_pos_bound a 16 ltac:(zlia)) as B1 end.
pose proof (Z.div_mod (bv_unsigned (getr regs0 2)) 16 ltac:(zlia)) as D0.
rewrite zcanon_id by (unfold M64; zlia). apply Z.eqb_neq. zlia. }
s_runR HR tfibtbl_rtD tfibtbl_rtD_ok 0x63974 D_X8 HX HP.
s_runR HR tfibtbl_rtD tfibtbl_rtD_ok 0x63970 D_P8 HX HP.
s_arm HR BC_EQ false MS_PAD8 (SLit 0).
{ destruct Hsp as (S1 & _ & _ & S4). pose proof (u64_range (getr regs0 2)) as U2. pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7).
clear - S1 S4 U2 T7. unfold MS_PAD8. arm_zevS. rewrite E2. numconst. try unfold sp0 in *.
repeat match goal with |- context [zcanon ?x] => lazymatch x with context [ew _ _] => fail | context [getr _ _] => fail | _ => let y := eval vm_compute in (zcanon x) in change (zcanon x) with y end end.
rewrite (zcanon_id (bv_unsigned (getr regs0 2) + _)) by (unfold M64; lia).
rewrite land15_lorc. rewrite (Z.add_mod (bv_unsigned (getr regs0 2)) (-2968) 16) by zlia. rewrite S4. vm_compute. reflexivity. }
s_runR HR tfibtbl_rtD tfibtbl_rtD_ok 0x67188 D_R8 HX HP.
apply (at_S_addzero _ _ _ _ _ _ _ (Some 2%nat) (-2968) 32) in HR; [| vm_compute; reflexivity].
replace (AFih.addzero (Some 2%nat) (-2968) 32 D_R8) with D_Z8 in HR by (vm_compute; reflexivity).
s_runR HR tfibtbl_rtD tfibtbl_rtD_ok 0x67294 DG8r HX HP.
s_noconds HR. s_station HR DG8_0. apply SRr_ret. exact HR.
Qed.
Lemma segD1_12 : forall (W' : world tfibsegs) c, at_S Wy md1 XZ PZ D_1_12 W' c -> SRr tfibsegs W' c (at_S Wy md1 XZ PZ DG12_0).
Proof.
intros W' c HR. pose proof WIN1R_XZ as HX. pose proof PZ_stable as HP.
s_runR HR tfibtbl_rtD tfibtbl_rtD_ok 0x63970 D_M12 HX HP.
s_arm HR BC_EQ false MS_AL12 (SLit 0).
{ destruct Hsp as (S1 & _ & _ & S4). pose proof (u64_range (getr regs0 2)) as U2. pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7).
clear - S1 S4 U2 T7. unfold MS_AL12. arm_zevS. rewrite E2. numconst. try unfold sp0 in *.
repeat match goal with |- context [zcanon ?x] => lazymatch x with context [ew _ _] => fail | context [getr _ _] => fail | _ => let y := eval vm_compute in (zcanon x) in change (zcanon x) with y end end.
rewrite (zcanon_id (bv_unsigned (getr regs0 2) + _)) by (unfold M64; zlia).
rewrite land15_lor240.
lazymatch goal with |- context [(?a mod 16)] =>
pose proof (Z.div_mod a 16 ltac:(zlia)) as D1; pose proof (Z.mod_pos_bound a 16 ltac:(zlia)) as B1 end.
pose proof (Z.div_mod (bv_unsigned (getr regs0 2)) 16 ltac:(zlia)) as D0.
rewrite zcanon_id by (unfold M64; zlia). apply Z.eqb_neq. zlia. }
s_runR HR tfibtbl_rtD tfibtbl_rtD_ok 0x67294 DG12r HX HP.
s_noconds HR. s_station HR DG12_0. apply SRr_ret. exact HR.
Qed.
Definition dia_side (k : nat) (tk : bool) (ss J : sstate) : Prop :=
let r := sym_run_toN_sh tfibsegs tfibtbl_rtD FUEL 0x6726c (arm BC_GEU tk (dia_lhs ss) (SLit 10) ss) in
(match snd r with RS_ecall => false | _ => true end
&& stack_shaped (fst r) && (match ss_resv (fst r) with None => true | Some _ => false end)
&& ss_atoms_lt k (fst r) && regions_wf (ss_mem (fst r)) && no_cdata (ss_mem (fst r)) && mem_atoms_lt k (ss_mem (fst r))) = true
/\ noconds (forget (fst r) k [16%bv]) = J.
Lemma diamond : forall (k : nat) (ss J : sstate),
(sHAV <= k)%nat -> sv_atoms_lt sHAV (dia_lhs ss) = true -> wins_ok WSKEL1R (ss_mem ss) = true ->
dia_side k true ss J -> dia_side k false ss J ->
forall (W' : world tfibsegs) c, at_S Wy md1 XZ PZ ss W' c -> SRr tfibsegs W' c (at_S Wy md1 XZ PZ J).
Proof.
intros k ss J Hk Hlhs Hwin HT HF W' c HR. pose proof WIN1R_XZ as HX. pose proof PZ_stable as HP.
assert (ARM : forall tk : bool, dia_side k tk ss J -> branch_taken BC_GEU (sv_denot E0 (dia_lhs ss)) (sv_denot E0 (SLit 10)) = tk ->
SRr tfibsegs W' c (at_S Wy md1 XZ PZ J)).
{ intros tk [CHK EQ] HB. unfold dia_side in CHK, EQ.
destruct (sym_run_toN_sh tfibsegs tfibtbl_rtD FUEL 0x6726c (arm BC_GEU tk (dia_lhs ss) (SLit 10) ss)) as [j st] eqn:RUN. cbn [fst snd] in CHK, EQ.
apply andb_prop in CHK as [CHK A7]. apply andb_prop in CHK as [CHK A6]. apply andb_prop in CHK as [CHK A5].
apply andb_prop in CHK as [CHK A4]. apply andb_prop in CHK as [CHK A3]. apply andb_prop in CHK as [A1 A2].
assert (Hst : match st with RS_ecall => False | _ => True end) by (destruct st; first [exact I | discriminate A1]).
assert (Hrv : ss_resv j = None) by (destruct (ss_resv j); [discriminate A3 | reflexivity]).
pose proof (at_S_arm Wy md1 XZ PZ ss W' c BC_GEU tk (dia_lhs ss) (SLit 10) HR Hlhs eq_refl HB) as HR1.
eapply SRr_bind.
- exact (at_S_runR Wy tfibtbl_rtD tfibtbl_rtD_ok 0x6726c md1 XZ PZ _ j st W' c HR1 RUN Hst HX Hwin HP A2).
- intros W2 c2 _ HR2.
pose proof (at_S_forget Wy md1 XZ PZ j W2 c2 k [16%bv] HR2 Hk Hrv A4 A5 A6 A7 eq_refl eq_refl) as HR3.
apply SRr_ret. rewrite <- EQ. exact (at_S_noconds _ _ _ _ _ _ _ HR3). }
assert (BC : forall b : bool, b = true \/ b = false) by (intros [|]; [left | right]; reflexivity).
destruct (BC (branch_taken BC_GEU (sv_denot E0 (dia_lhs ss)) (sv_denot E0 (SLit 10)))) as [TK|TK]; [exact (ARM true HT TK) | exact (ARM false HF TK)].
Qed.
Local Ltac s_dia HR k ss J :=
lazymatch type of HR with at_S _ _ _ _ _ ?W' ?c' =>
eapply SRr_bind;
[ eapply (diamond k ss J ltac:(unfold sHAV, aDIG; zlia) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(split; vm_compute; reflexivity) ltac:(split; vm_compute; reflexivity) W' c' HR)
| clear HR; let W2 := fresh "W" in let c2 := fresh "c" in intros W2 c2 _ HR ] end.
Lemma digits_6 : forall (W' : world tfibsegs) c, at_S Wy md1 XZ PZ DG6_0 W' c -> SRr tfibsegs W' c (at_S Wy md1 XZ PZ DJ6_5).
Proof.
intros W' c HR. pose proof WIN1R_XZ as HX. pose proof PZ_stable as HP.
s_dia HR (aDIG + 0)%nat DG6_0 DJ6_0. s_runR HR tfibtbl_rtD tfibtbl_rtD_ok 0x67294 DG6_1 HX HP.
s_dia HR (aDIG + 1)%nat DG6_1 DJ6_1. s_runR HR tfibtbl_rtD tfibtbl_rtD_ok 0x67294 DG6_2 HX HP.
s_dia HR (aDIG + 2)%nat DG6_2 DJ6_2. s_runR HR tfibtbl_rtD tfibtbl_rtD_ok 0x67294 DG6_3 HX HP.
s_dia HR (aDIG + 3)%nat DG6_3 DJ6_3. s_runR HR tfibtbl_rtD tfibtbl_rtD_ok 0x67294 DG6_4 HX HP.
s_dia HR (aDIG + 4)%nat DG6_4 DJ6_4. s_runR HR tfibtbl_rtD tfibtbl_rtD_ok 0x67294 DG6_5 HX HP.
s_dia HR (aDIG + 5)%nat DG6_5 DJ6_5. apply SRr_ret. exact HR.
Qed.
Lemma digits_7 : forall (W' : world tfibsegs) c, at_S Wy md1 XZ PZ DG7_0 W' c -> SRr tfibsegs W' c (at_S Wy md1 XZ PZ DJ7_6).
Proof.
intros W' c HR. pose proof WIN1R_XZ as HX. pose proof PZ_stable as HP.
s_dia HR (aDIG + 0)%nat DG7_0 DJ7_0. s_runR HR tfibtbl_rtD tfibtbl_rtD_ok 0x67294 DG7_1 HX HP.
s_dia HR (aDIG + 1)%nat DG7_1 DJ7_1. s_runR HR tfibtbl_rtD tfibtbl_rtD_ok 0x67294 DG7_2 HX HP.
s_dia HR (aDIG + 2)%nat DG7_2 DJ7_2. s_runR HR tfibtbl_rtD tfibtbl_rtD_ok 0x67294 DG7_3 HX HP.
s_dia HR (aDIG + 3)%nat DG7_3 DJ7_3. s_runR HR tfibtbl_rtD tfibtbl_rtD_ok 0x67294 DG7_4 HX HP.
s_dia HR (aDIG + 4)%nat DG7_4 DJ7_4. s_runR HR tfibtbl_rtD tfibtbl_rtD_ok 0x67294 DG7_5 HX HP.
s_dia HR (aDIG + 5)%nat DG7_5 DJ7_5. s_runR HR tfibtbl_rtD tfibtbl_rtD_ok 0x67294 DG7_6 HX HP.
s_dia HR (aDIG + 6)%nat DG7_6 DJ7_6. apply SRr_ret. exact HR.
Qed.
Lemma digits_8 : forall (W' : world tfibsegs) c, at_S Wy md1 XZ PZ DG8_0 W' c -> SRr tfibsegs W' c (at_S Wy md1 XZ PZ DJ8_7).
Proof.
intros W' c HR. pose proof WIN1R_XZ as HX. pose proof PZ_stable as HP.
s_dia HR (aDIG + 0)%nat DG8_0 DJ8_0. s_runR HR tfibtbl_rtD tfibtbl_rtD_ok 0x67294 DG8_1 HX HP.
s_dia HR (aDIG + 1)%nat DG8_1 DJ8_1. s_runR HR tfibtbl_rtD tfibtbl_rtD_ok 0x67294 DG8_2 HX HP.
s_dia HR (aDIG + 2)%nat DG8_2 DJ8_2. s_runR HR tfibtbl_rtD tfibtbl_rtD_ok 0x67294 DG8_3 HX HP.
s_dia HR (aDIG + 3)%nat DG8_3 DJ8_3. s_runR HR tfibtbl_rtD tfibtbl_rtD_ok 0x67294 DG8_4 HX HP.
s_dia HR (aDIG + 4)%nat DG8_4 DJ8_4. s_runR HR tfibtbl_rtD tfibtbl_rtD_ok 0x67294 DG8_5 HX HP.
s_dia HR (aDIG + 5)%nat DG8_5 DJ8_5. s_runR HR tfibtbl_rtD tfibtbl_rtD_ok 0x67294 DG8_6 HX HP.
s_dia HR (aDIG + 6)%nat DG8_6 DJ8_6. s_runR HR tfibtbl_rtD tfibtbl_rtD_ok 0x67294 DG8_7 HX HP.
s_dia HR (aDIG + 7)%nat DG8_7 DJ8_7. apply SRr_ret. exact HR.
Qed.
Lemma digits_12 : forall (W' : world tfibsegs) c, at_S Wy md1 XZ PZ DG12_0 W' c -> SRr tfibsegs W' c (at_S Wy md1 XZ PZ DJ12_11).
Proof.
intros W' c HR. pose proof WIN1R_XZ as HX. pose proof PZ_stable as HP.
s_dia HR (aDIG + 0)%nat DG12_0 DJ12_0. s_runR HR tfibtbl_rtD tfibtbl_rtD_ok 0x67294 DG12_1 HX HP.
s_dia HR (aDIG + 1)%nat DG12_1 DJ12_1. s_runR HR tfibtbl_rtD tfibtbl_rtD_ok 0x67294 DG12_2 HX HP.
s_dia HR (aDIG + 2)%nat DG12_2 DJ12_2. s_runR HR tfibtbl_rtD tfibtbl_rtD_ok 0x67294 DG12_3 HX HP.
s_dia HR (aDIG + 3)%nat DG12_3 DJ12_3. s_runR HR tfibtbl_rtD tfibtbl_rtD_ok 0x67294 DG12_4 HX HP.
s_dia HR (aDIG + 4)%nat DG12_4 DJ12_4. s_runR HR tfibtbl_rtD tfibtbl_rtD_ok 0x67294 DG12_5 HX HP.
s_dia HR (aDIG + 5)%nat DG12_5 DJ12_5. s_runR HR tfibtbl_rtD tfibtbl_rtD_ok 0x67294 DG12_6 HX HP.
s_dia HR (aDIG + 6)%nat DG12_6 DJ12_6. s_runR HR tfibtbl_rtD tfibtbl_rtD_ok 0x67294 DG12_7 HX HP.
s_dia HR (aDIG + 7)%nat DG12_7 DJ12_7. s_runR HR tfibtbl_rtD tfibtbl_rtD_ok 0x67294 DG12_8 HX HP.
s_dia HR (aDIG + 8)%nat DG12_8 DJ12_8. s_runR HR tfibtbl_rtD tfibtbl_rtD_ok 0x67294 DG12_9 HX HP.
s_dia HR (aDIG + 9)%nat DG12_9 DJ12_9. s_runR HR tfibtbl_rtD tfibtbl_rtD_ok 0x67294 DG12_10 HX HP.
s_dia HR (aDIG + 10)%nat DG12_10 DJ12_10. s_runR HR tfibtbl_rtD tfibtbl_rtD_ok 0x67294 DG12_11 HX HP.
s_dia HR (aDIG + 11)%nat DG12_11 DJ12_11. apply SRr_ret. exact HR.
Qed.
Lemma segEND_6 : forall (W' : world tfibsegs) c, at_S Wy md1 XZ PZ DJ6_5 W' c ->
SRr tfibsegs W' c (fun (W'' : world tfibsegs) (c'' : config) => is_self_jump tfibsegs (cfg_ms c'') = true).
Proof.
intros W' c HR. pose proof WIN1R_XZ as HX. pose proof PZ_stable as HP.
s_runR HR tfibtbl_rtD tfibtbl_rtD_ok 0x5f9e4 D_END6 HX HP.
apply SRr_ret. destruct HR as (_ & ms & mat & E' & -> & HE & HS & MEQ & PRS & HPm). cbn [cfg_ms].
pose proof (st_ok_restrict_mkst tfibsegs (w_H Wy) E' D_END6 ms HS ltac:(vm_compute; reflexivity)) as SH.
pose proof (f_equal ms_svc_pending SH) as Hsv. pose proof (f_equal ms_pc_val SH) as Hpc. cbn [ms_svc_pending ms_pc_val YK11.mkst] in Hsv, Hpc.
replace (ss_pc D_END6) with 0x5f9e4 in Hpc by (vm_compute; reflexivity).
unfold is_self_jump, ms_pc. rewrite Hsv, Hpc. rewrite (tfibtbl_rtD_ok 0x5f9e4 111 ltac:(vm_compute; reflexivity)). vm_compute. reflexivity.
Qed.
Lemma segEND_7 : forall (W' : world tfibsegs) c, at_S Wy md1 XZ PZ DJ7_6 W' c ->
SRr tfibsegs W' c (fun (W'' : world tfibsegs) (c'' : config) => is_self_jump tfibsegs (cfg_ms c'') = true).
Proof.
intros W' c HR. pose proof WIN1R_XZ as HX. pose proof PZ_stable as HP.
s_runR HR tfibtbl_rtD tfibtbl_rtD_ok 0x5f9e4 D_END7 HX HP.
apply SRr_ret. destruct HR as (_ & ms & mat & E' & -> & HE & HS & MEQ & PRS & HPm). cbn [cfg_ms].
pose proof (st_ok_restrict_mkst tfibsegs (w_H Wy) E' D_END7 ms HS ltac:(vm_compute; reflexivity)) as SH.
pose proof (f_equal ms_svc_pending SH) as Hsv. pose proof (f_equal ms_pc_val SH) as Hpc. cbn [ms_svc_pending ms_pc_val YK11.mkst] in Hsv, Hpc.
replace (ss_pc D_END7) with 0x5f9e4 in Hpc by (vm_compute; reflexivity).
unfold is_self_jump, ms_pc. rewrite Hsv, Hpc. rewrite (tfibtbl_rtD_ok 0x5f9e4 111 ltac:(vm_compute; reflexivity)). vm_compute. reflexivity.
Qed.
Lemma segEND_8 : forall (W' : world tfibsegs) c, at_S Wy md1 XZ PZ DJ8_7 W' c ->
SRr tfibsegs W' c (fun (W'' : world tfibsegs) (c'' : config) => is_self_jump tfibsegs (cfg_ms c'') = true).
Proof.
intros W' c HR. pose proof WIN1R_XZ as HX. pose proof PZ_stable as HP.
s_runR HR tfibtbl_rtD tfibtbl_rtD_ok 0x5f9e4 D_END8 HX HP.
apply SRr_ret. destruct HR as (_ & ms & mat & E' & -> & HE & HS & MEQ & PRS & HPm). cbn [cfg_ms].
pose proof (st_ok_restrict_mkst tfibsegs (w_H Wy) E' D_END8 ms HS ltac:(vm_compute; reflexivity)) as SH.
pose proof (f_equal ms_svc_pending SH) as Hsv. pose proof (f_equal ms_pc_val SH) as Hpc. cbn [ms_svc_pending ms_pc_val YK11.mkst] in Hsv, Hpc.
replace (ss_pc D_END8) with 0x5f9e4 in Hpc by (vm_compute; reflexivity).
unfold is_self_jump, ms_pc. rewrite Hsv, Hpc. rewrite (tfibtbl_rtD_ok 0x5f9e4 111 ltac:(vm_compute; reflexivity)). vm_compute. reflexivity.
Qed.
Lemma segEND_12 : forall (W' : world tfibsegs) c, at_S Wy md1 XZ PZ DJ12_11 W' c ->
SRr tfibsegs W' c (fun (W'' : world tfibsegs) (c'' : config) => is_self_jump tfibsegs (cfg_ms c'') = true).
Proof.
intros W' c HR. pose proof WIN1R_XZ as HX. pose proof PZ_stable as HP.
s_runR HR tfibtbl_rtD tfibtbl_rtD_ok 0x5f9e4 D_END12 HX HP.
apply SRr_ret. destruct HR as (_ & ms & mat & E' & -> & HE & HS & MEQ & PRS & HPm). cbn [cfg_ms].
pose proof (st_ok_restrict_mkst tfibsegs (w_H Wy) E' D_END12 ms HS ltac:(vm_compute; reflexivity)) as SH.
pose proof (f_equal ms_svc_pending SH) as Hsv. pose proof (f_equal ms_pc_val SH) as Hpc. cbn [ms_svc_pending ms_pc_val YK11.mkst] in Hsv, Hpc.
replace (ss_pc D_END12) with 0x5f9e4 in Hpc by (vm_compute; reflexivity).
unfold is_self_jump, ms_pc. rewrite Hsv, Hpc. rewrite (tfibtbl_rtD_ok 0x5f9e4 111 ltac:(vm_compute; reflexivity)). vm_compute. reflexivity.
Qed.
End h.
End g.
