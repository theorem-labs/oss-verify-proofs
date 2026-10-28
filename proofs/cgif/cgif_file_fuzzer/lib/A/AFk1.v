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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK0j YK0v YK13 YP0n YA05 YA09 YG0b YG0h YF05.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AFid AFie AFif AFig AFih AFii AFjv AFjw AFjx AFjh AFjn AFjo AFjk AFjl AFjp AFjq AFjs AFjt AFk2.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YA00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AFia.
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
Local Abbreviation DCELLS := (@AFk2.DCELLS W mem0).
Local Abbreviation PZ := (@AFk2.PZ ly regs0 n ch mb).
Local Abbreviation PZ_stable := (@AFk2.PZ_stable _ ly regs0 n ch idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation img_vis := (@AFk2.img_vis).
Local Abbreviation in_dimg := (@AFk2.in_dimg).
Local Abbreviation in_dimg_facts := (@AFk2.in_dimg_facts _ ly regs0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap S).
Local Abbreviation val_mem_xfer_img := (@AFk2.val_mem_xfer_img _ W ly regs0 mem0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap S).
Local Abbreviation dnewb := (@AFk2.dnewb).
Local Abbreviation dnewb_sound := (@AFk2.dnewb_sound _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap S).
Local Abbreviation pat_word := (@AFk2.pat_word W ly regs0 mem0 idx res Hidx DPOST S).
Local Abbreviation D_1_ok := (@AFk2.D_1_ok _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap DPOST B S TS HARm Hidx_def).
Local Abbreviation land15_lor240 := (@AFk2.land15_lor240).
Local Abbreviation land15_lorc := (@AFk2.land15_lorc).
Local Abbreviation at_S_tighten := (@AFk2.at_S_tighten _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation addzero_region_ok := (@AFk2.addzero_region_ok ly regs0 res S).
Local Abbreviation addzero_regions_wf := (@AFk2.addzero_regions_wf).
Local Abbreviation addzero_all_disjoint := (@AFk2.addzero_all_disjoint).
Local Abbreviation addzero_pairwise := (@AFk2.addzero_pairwise).
Local Abbreviation at_S_addzero := (@AFk2.at_S_addzero _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb S).
Local Abbreviation hexfact_ok := (@AFk2.hexfact_ok _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hidx Hres S Hidx_def).
Local Abbreviation segD1_6 := (@AFk2.segD1_6 _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart S).
Local Abbreviation segD1_7 := (@AFk2.segD1_7 _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart S).
Local Abbreviation segD1_8 := (@AFk2.segD1_8 _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart S).
Local Abbreviation segD1_12 := (@AFk2.segD1_12 _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation dia_side := (@AFk2.dia_side).
Local Abbreviation diamond := (@AFk2.diamond _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation digits_6 := (@AFk2.digits_6 _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart S).
Local Abbreviation digits_7 := (@AFk2.digits_7 _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart S).
Local Abbreviation digits_8 := (@AFk2.digits_8 _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart S).
Local Abbreviation digits_12 := (@AFk2.digits_12 _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart S).
Local Abbreviation segEND_6 := (@AFk2.segEND_6 _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation segEND_7 := (@AFk2.segEND_7 _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation segEND_8 := (@AFk2.segEND_8 _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation segEND_12 := (@AFk2.segEND_12 _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart).
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
Definition BCELLS : Prop :=
val_mem tfibsegs (mrestrict (w_H W) mem0) 0x9ec38 8 0x5f8fd0 /\ val_mem tfibsegs (mrestrict (w_H W) mem0) 0x5f9250 8 4096 /\
val_mem tfibsegs (mrestrict (w_H W) mem0) 0x214ac 2 0xff04 /\ val_mem tfibsegs (mrestrict (w_H W) mem0) 0x21448 4 0x6b788 /\
val_mem tfibsegs (mrestrict (w_H W) mem0) 0x137c1c 1 1 /\ val_mem tfibsegs (mrestrict (w_H W) mem0) 0x137c03 1 1.
Hypothesis HBC : BCELLS.
Local Ltac s_runS HR tbl tblok stop ss' HX HP :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let st := eval vm_compute in (snd (sym_run_toN_sh tfibsegs tbl FUEL stop ss)) in
eapply SRr_bind;
[ eapply (at_S_runS Wx tbl tblok stop md X P ss ss' st W' c' HR);
[ vm_compute; reflexivity | exact I | exact HX | vm_compute; reflexivity | exact HP | vm_compute; reflexivity ]
| clear HR; let W2 := fresh "W" in let c2 := fresh "c" in intros W2 c2 _ HR ] end.
Local Ltac s_ecallS HR tbl tblok ss' HX HP :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
eapply (at_S_run_ecallS Wx tbl tblok 0x7ffffff0 md X P ss ss' W' c' HR);
[ vm_compute; reflexivity | reflexivity | exact HX | vm_compute; reflexivity | exact HP | vm_compute; reflexivity ] end.
Definition PGBv : Z := (SMv + 768 + 4095) / 4096 * 4096.
Definition PGEv : Z := PBv / 4096 * 4096.
Lemma big_marks : 18446744073709551615 <= N8D / 8 ->
PBv = SMv + 768 + N8D / 8 /\ SMv mod 512 = 0 /\ PGBv mod 4096 = 0 /\ PGEv mod 4096 = 0 /\
SMv + 768 < PGBv /\ PGBv < SMv + 768 + 4096 /\ PGEv <= PBv /\ PBv < PGEv + 4096 /\ PGBv + 4096 <= PGEv /\
kLowShadowBeg + TFIB_IMG_END / 8 <= SMv /\ PBv <= SMv + MSv / 8 /\ SMv + MSv / 8 <= kHighShadowEnd /\ PBv <= SHBv + UEv / 8.
Proof.
intros HB. pose proof map_facts as (M1 & M2 & M3 & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & SM3 & PB & _). pose proof map_zoneN as MZ.
pose proof shadow_marks as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9). pose proof user_marks as (B1 & B2 & B3 & B4 & B5).
pose proof size_facts as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & _).
clear - HB M3 SM1 SM2 SM3 PB A2 A3 A5 A6 B1 Z4 Z8 MZ. unfold PGBv, PGEv.
pose proof (Z.div_mod (SMv + 768 + 4095) 4096 ltac:(zlia)) as D1. pose proof (Z.mod_pos_bound (SMv + 768 + 4095) 4096 ltac:(zlia)) as R1.
pose proof (Z.div_mod PBv 4096 ltac:(zlia)) as D2. pose proof (Z.mod_pos_bound PBv 4096 ltac:(zlia)) as R2.
pose proof SM3 as SM3'. apply Z.mod_divide in SM3' as [u Hu]; [|zlia].
assert (P1 : PGBv mod 4096 = 0) by (unfold PGBv; apply Z_mod_mult). assert (P2 : PGEv mod 4096 = 0) by (unfold PGEv; apply Z_mod_mult).
unfold PGBv, PGEv in *. set (q1 := (SMv + 768 + 4095) / 4096) in *. set (q2 := PBv / 4096) in *.
assert (X1 : SMv + 768 < q1 * 4096 < SMv + 768 + 4096) by (clear - D1 R1 Hu MZ; zlia).
assert (X2 : q2 * 4096 <= PBv < q2 * 4096 + 4096) by (clear - D2 R2 MZ; zlia).
clear D1 R1 D2 R2 Hu. unfold kHighShadowBeg, kHighShadowEnd, MALLOC_MAX in *.
repeat split; first [assumption | zlia].
Qed.
Lemma sm_bounds : 2148217776 <= SMv /\ SMv + 9216 <= SMv + MSv / 8 <= 17594333495296.
Proof.
pose proof map_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _). pose proof map_zoneN as MZ. pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & _).
clear - SM1 SM2 Z8 MZ. unfold kHighShadowBeg, kHighShadowEnd, MALLOC_MAX in *.
pose proof (Z.div_mod MSv 8 ltac:(zlia)). pose proof (Z.mod_pos_bound MSv 8 ltac:(zlia)). zlia.
Qed.
Lemma U_SHBT : U E0 SHBT = SMv + 768.
Proof.
pose proof sm_bounds as SMB. clear - SMB.
unfold SHBT. rewrite U_SOff. unfold aSM. rewrite EaSM. unfold w64. rewrite unsigned_lit_small by zlia. apply zcanon_id. unfold M64. zlia.
Qed.
Lemma U_SHET : 18446744073709551615 <= N8D / 8 -> U E0 SHET = PBv.
Proof.
intros HB. pose proof sm_bounds as SMB. pose proof (big_marks HB) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13). clear - SMB C1 C11 HB.
unfold SHET. rewrite U_SOff. unfold aPBS. rewrite EaPB. unfold w64. rewrite unsigned_lit_small by zlia. rewrite Z.add_0_r. apply zcanon_id. unfold M64. zlia.
Qed.
Lemma U_PGBT : 18446744073709551615 <= N8D / 8 -> U E0 PGBT = PGBv.
Proof.
intros HB. pose proof sm_bounds as SMB. pose proof (big_marks HB) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13). clear - SMB C3 C5 C6 C11 HB.
unfold PGBT. rewrite U_zev by reflexivity. cbn [zev zalu_raw]. unfold rho_of. unfold aSM. rewrite EaSM. unfold w64.
rewrite unsigned_lit_small by zlia. rewrite (zcanon_id (SMv + 4863)) by (unfold M64; zlia).
change (zcanon 18446744073709547520) with (2 ^ 64 - 2 ^ 12). rewrite land_neg_pow2_u64 by zlia. change (2 ^ 12) with 4096.
pose proof (Z.div_mod (SMv + 768 + 4095) 4096 ltac:(zlia)) as D1. pose proof (Z.mod_pos_bound (SMv + 768 + 4095) 4096 ltac:(zlia)) as R1.
replace (SMv + 4863) with (SMv + 768 + 4095) by zlia. unfold PGBv in *. rewrite zcanon_id; unfold M64; zlia.
Qed.
Lemma U_PGET : 18446744073709551615 <= N8D / 8 -> U E0 PGET = PGEv.
Proof.
intros HB. pose proof sm_bounds as SMB. pose proof (big_marks HB) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13). clear - SMB C1 C4 C7 C8 C11 HB.
unfold PGET. rewrite U_zev by reflexivity. cbn [zev zalu_raw]. unfold rho_of. unfold aPBS. rewrite EaPB. unfold w64.
rewrite unsigned_lit_small by zlia. rewrite Z.add_0_r. rewrite (zcanon_id PBv) by (unfold M64; zlia).
change (zcanon 18446744073709547520) with (2 ^ 64 - 2 ^ 12). rewrite land_neg_pow2_u64 by zlia. change (2 ^ 12) with 4096.
pose proof (Z.div_mod PBv 4096 ltac:(zlia)) as D1. pose proof (Z.mod_pos_bound PBv 4096 ltac:(zlia)) as R1.
unfold PGEv in *. rewrite zcanon_id; unfold M64; zlia.
Qed.
Lemma U_SHB_X : U E0 SHB_X = SMv + 768.
Proof.
pose proof map_facts as (M1 & M2 & M3 & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _). pose proof map_zoneN as MZ. pose proof shadow_marks as (_ & _ & _ & _ & _ & _ & A7 & _).
pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & _). clear - M1 M2 M3 SM1 SM2 A7 Z8 MZ.
unfold SHB_X. rewrite U_zev by reflexivity. cbn [zev zalu_raw]. unfold rho_of. rewrite EaSHB, EaMAP. unfold w64, AFjm.SHBv in *.
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kHighShadowBeg, kHighShadowEnd, MALLOC_MAX in *. rewrite !unsigned_lit_small by zlia.
zcanon_simp. land_lits. rewrite Z.shiftr_div_pow2 by zlia. change (2 ^ 3) with 8.
apply Z.mod_divide in M3 as [u Hu]; [|zlia]. rewrite Hu in *. replace (u * 4096 + 6144) with ((u * 512 + 768) * 8) by zlia. rewrite Z_div_mult by zlia.
rewrite A7. replace (u * 4096) with ((u * 512) * 8) by zlia. rewrite Z_div_mult by zlia. zcanon_simp. zlia.
Qed.
Lemma U_SHE_X : U E0 SHE_X = PBv.
Proof.
pose proof map_facts as (M1 & M2 & M3 & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _ & PB & _). pose proof map_zoneN as MZ. pose proof shadow_marks as (_ & _ & _ & _ & _ & _ & A7 & _).
pose proof size_facts as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & _). pose proof Nrange as NR. pose proof user_marks as (B1 & _). clear - M1 M2 M3 SM1 SM2 PB A7 Z4 Z5 Z8 NR B1 MZ.
unfold SHE_X. rewrite U_zev by reflexivity. cbn [zev zalu_raw]. unfold rho_of. rewrite EaSHB, EaMAP, EaN8D. unfold w64, AFjm.SHBv in *.
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kHighShadowBeg, kHighShadowEnd, MALLOC_MAX in *. rewrite !unsigned_lit_small by zlia.
zcanon_simp. land_lits. rewrite Z.shiftr_div_pow2 by zlia. change (2 ^ 3) with 8.
apply Z.mod_divide in M3 as [u Hu]; [|zlia]. apply Z.mod_divide in Z5 as [p Hp]; [|zlia]. rewrite Hu, Hp in *.
replace (u * 4096 + 6136 + (p * 8 + 0)) with ((u * 512 + 767 + p) * 8) by zlia. rewrite Z_div_mult in * by zlia.
rewrite PB, A7. replace (u * 4096) with ((u * 512) * 8) by zlia. rewrite Z_div_mult by zlia. zcanon_simp. zlia.
Qed.
Section U.
Variables (X : Z -> Prop) (z : Z).
Hypothesis HXW : forall a, WIN a -> X a.
Hypothesis HXsub : forall a, X a -> WIN a \/ QR a \/ DX a.
Hypothesis Hbig : 18446744073709551615 <= N8D / 8.
Let place_X : forall d len a, ((mb + 6144 <= d /\ d + len <= mb + MSv) \/ (SMv <= d /\ d + len <= SMv + MSv / 8)) -> d <= a < d + len -> X a :=
fun d len a PL Ha => HXW a (place_WIN d len a PL Ha).
Definition in_bimg (x : Z) : Prop :=
(0x9ec38 <= x < 0x9ec40) \/ (0x5f8fd0 <= x < 0x5f8fd8) \/ (0x5f9250 <= x < 0x5f9258) \/ (0x214ac <= x < 0x214ae) \/ (0x21448 <= x < 0x2144c) \/
(0x9dfd8 <= x < 0x9dfe8) \/ (0x137b1c <= x < 0x137b20) \/ (0x137c1c <= x < 0x137c1d) \/ (0x137c03 <= x < 0x137c04).
Lemma in_bimg_facts : forall x, in_bimg x -> 0 <= x < 2 ^ 64 /\ find_segment tfibsegs x 1 <> None /\ ~ X x.
Proof.
intros x R. unfold in_bimg in R. pose proof high_facts as (F1 & _ & _ & _ & _ & _ & _ & _ & F9 & _). pose proof map_facts as (M1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & _). pose proof map_zoneN as MZ.
destruct Hsp as (S1' & _). pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7). pose proof BSLv_range as HB. pose proof Hres as [HRS _]. pose proof Hidx as HI.
pose proof blocks_facts as (NBhi & SBhi & _).
split; [clear - R MZ; zlia|]. split.
- assert (SEG : forall y, 0x10000 <= y < 0x5fb000 -> find_segment tfibsegs y 1 <> None).
{ clear. intros y Hy. change tfibsegs with AB1h.TSEGS. unfold AB1h.TSEGS, Asan.M.loaded_segments.
cbn -[Z_to_bv bv_unsigned Z.leb Z.ltb Z.add].
repeat match goal with |- context [((?x <=? y) && (y + 1 <=? ?z))%bool] => destruct (Z.leb_spec x y); destruct (Z.leb_spec (y + 1) z); cbn [andb] end;
try discriminate; exfalso; zlia. }
apply SEG. clear - R MZ. zlia.
- intros HXx. destruct (HXsub x HXx) as [HW | [HQ | HD]].
+ clear - R HW F1 F9 M1 SM1 S1' T7 HB HI MZ. unfold WIN, WINT, WINI, WINM in HW.
unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighShadowBeg, QSv, ASTACK, t_unwinding, TFIB_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex in *.
try unfold Qb in *. try unfold T in *. try unfold sp0 in *. zlia.
+ unfold QR in HQ. clear - R HQ F9 HRS HI MZ. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg in *. try unfold Qb in *. zlia.
+ unfold DX, DZONE in HD. clear - R HD S1' T7 NBhi SBhi MZ. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASTACK, DEP_STK in *. try unfold sp0 in *. zlia.
Qed.
Lemma val_mem_xfer_bimg : forall (m : word -> option byte) a (w : nat) v,
val_mem tfibsegs (mrestrict (w_H W) mem0) a w v ->
(forall x : word, ~ X (bv_unsigned x) -> m x = mem0 x) ->
(forall i, 0 <= i < Z.of_nat w -> in_bimg (a + i)) ->
val_mem tfibsegs (mrestrict (w_H Wy) m) a w v.
Proof.
intros m a w v HV MEQ Hin k Hk. rewrite <- (HV k Hk). destruct (in_bimg_facts (a + Z.of_nat k) (Hin (Z.of_nat k) ltac:(zlia))) as (Ra & Fs & Nw).
unfold mbyte, mrestrict. rewrite (img_vis Wy _ Ra Fs), (img_vis W _ Ra Fs). rewrite MEQ; [reflexivity|]. rewrite unsigned_lit_small by exact Ra. exact Nw.
Qed.
Lemma can_word : forall m, exists w, val_mem tfibsegs (mrestrict (w_H Wy) m) 0x5f8fd0 8 w /\ 0 <= w < 2 ^ 64.
Proof.
clearP. intros m. destruct can_bytes as [bs Hbs]. destruct (img_word (w_H Wy) m 0x5f8fd0 bs Hbs) as [w Hw].
exists (w mod 2 ^ 64). split; [exact (val_mem_mod8 _ _ _ Hw) | apply Z.mod_pos_bound; zlia].
Qed.
Theorem B_R_ok : forall (W' : world tfibsegs) c, at_S Wy md1 X (PSR Wy SH4 (PDX Wy RX z)) T_R W' c -> at_S Wy md1 X (PSR Wy SH4 (PDX Wy RX z)) B_R W' c.
Proof.
intros W' c HR. pose proof HBC as (C1 & C2 & C3 & C4 & C5 & C6).
pose proof (cell_lit 0x9dfd8 8 1 ltac:(vm_compute; reflexivity)) as G1. pose proof (cell_lit 0x137b1c 4 0 ltac:(vm_compute; reflexivity)) as G2.
pose proof (cell_lit 0x9dfe0 8 0x137b1c ltac:(vm_compute; reflexivity)) as G3.
pose proof map_facts as (M1 & M2 & M3 & _). pose proof map_zoneN as MZ. pose proof size_facts as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & _). pose proof Nrange as NR.
s_arm HR BC_LTU false USH_LEN (SLit 18446744073709551615).
{ clear - M1 M2 M3 Z8 Z4 Z5 NR Hbig MZ. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, MALLOC_MAX in *. arm_zevS. unfold USH_LEN. cbn [zev zalu_raw]. unfold_atoms. rewrite EaMAP, EaN8D. unfold w64.
rewrite !unsigned_lit_small by zlia. zcanon_simp. land_lits. rewrite !Z.shiftr_div_pow2 by zlia. change (2 ^ 3) with 8.
apply Z.mod_divide in M3 as [u Hu]; [|zlia]. apply Z.mod_divide in Z5 as [p Hp]; [|zlia]. rewrite Hu, Hp in *.
replace (u * 4096 + 6136 + (p * 8 + 0)) with ((u * 512 + 767 + p) * 8) by zlia. replace (u * 4096 + 6144) with ((u * 512 + 768) * 8) by zlia.
rewrite !Z_div_mult in * by zlia. zcanon_simp. apply Z.ltb_ge. zlia. }
destruct HR as (EW & ms & mat & E' & Ec & HE & HS & MEQ & PRS & HPm).
destruct (can_word (ms_mem ms)) as (wc & Hwc & Rwc).
set (E'' := havoc E' aCAN [w64 wc]).
assert (HE'' : env_agree sHAV E0 E'').
{ destruct HE as [HE1 HE2]. split; [| unfold E'', havoc; cbn [ed]; exact HE2]. intros k Hk. unfold E''. rewrite ew_havoc_old by (unfold aCAN, sHAV in *; zlia). exact (HE1 k Hk). }
assert (AG : env_agree aCAN E' E'') by (split; [intros k Hk; unfold E''; apply ew_havoc_old; exact Hk | reflexivity]).
lazymatch type of HS with st_ok _ _ ?ss0 _ =>
assert (HS'' : st_ok tfibsegs E'' ss0 (restrict (w_H Wy) ms)) by (exact (st_ok_agree tfibsegs aCAN E' E'' ss0 _ HS AG ltac:(vm_compute; reflexivity))) end.
split; [exact EW|]. exists ms, mat, E''. split; [exact Ec|]. split; [exact HE''|]. split; [| exact (conj MEQ (conj PRS HPm))].
assert (X1 := val_mem_xfer_bimg (ms_mem ms) _ _ _ C1 MEQ ltac:(intros i Hi; unfold in_bimg; zlia)).
assert (X2 := val_mem_xfer_bimg (ms_mem ms) _ _ _ C2 MEQ ltac:(intros i Hi; unfold in_bimg; zlia)).
assert (X3 := val_mem_xfer_bimg (ms_mem ms) _ _ _ C3 MEQ ltac:(intros i Hi; unfold in_bimg; zlia)).
assert (X4 := val_mem_xfer_bimg (ms_mem ms) _ _ _ C4 MEQ ltac:(intros i Hi; unfold in_bimg; zlia)).
assert (X5 := val_mem_xfer_bimg (ms_mem ms) _ _ _ C5 MEQ ltac:(intros i Hi; unfold in_bimg; zlia)).
assert (X6 := val_mem_xfer_bimg (ms_mem ms) _ _ _ C6 MEQ ltac:(intros i Hi; unfold in_bimg; zlia)).
assert (Y1 := val_mem_xfer_bimg (ms_mem ms) _ _ _ G1 MEQ ltac:(intros i Hi; unfold in_bimg; zlia)).
assert (Y2 := val_mem_xfer_bimg (ms_mem ms) _ _ _ G2 MEQ ltac:(intros i Hi; unfold in_bimg; zlia)).
assert (Y3 := val_mem_xfer_bimg (ms_mem ms) _ _ _ G3 MEQ ltac:(intros i Hi; unfold in_bimg; zlia)).
Local Ltac raddB HS EE HEE RR lo hi :=
apply st_ok_add_region; [exact HS | vm_compute; reflexivity | |
apply all_disjoint_of_forall; intros r2 Hr2;
refine (dnewb_sound EE lo hi RR r2 HEE eq_refl eq_refl eq_refl ltac:(clear; zlia) ltac:(clear; zlia) ltac:(clear; zlia) _);
lazymatch goal with |- dnewb _ _ _ = true =>
revert r2 Hr2; apply (proj1 (forallb_forall _ _)); vm_compute; reflexivity end ].
Local Ltac rlit RR XX :=
unfold RR, lit8, lit4, lit1, region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict];
split; [clear; zlia|]; split; [clear; zlia|]; split; [intros o Ho; clear - Ho; zlia|]; apply Forall_cons; [|apply Forall_nil];
eapply chunk_ok_val; [reflexivity | cbn; clear; zlia | cbn; clear; zlia | rewrite Z.add_0_l; exact XX].
unfold B_R, BREG. cbn [fold_right].
assert (HS1 : st_ok tfibsegs E'' (addreg R_f2 B_0) (restrict (w_H Wy) ms)).
{ unfold addreg. raddB HS'' E'' HE'' R_f2 0x137c03 0x137c04. rlit R_f2 X6. }
assert (HS2 : st_ok tfibsegs E'' (addreg R_f1 (addreg R_f2 B_0)) (restrict (w_H Wy) ms)).
{ unfold addreg at 1. raddB HS1 E'' HE'' R_f1 0x137c1c 0x137c1d. rlit R_f1 X5. }
assert (HS3 : st_ok tfibsegs E'' (addreg R_g2 (addreg R_f1 (addreg R_f2 B_0))) (restrict (w_H Wy) ms)).
{ unfold addreg at 1. raddB HS2 E'' HE'' R_g2 0x137b1c 0x137b20. rlit R_g2 Y2. }
assert (HS4 : st_ok tfibsegs E'' (addreg R_g3 (addreg R_g2 (addreg R_f1 (addreg R_f2 B_0)))) (restrict (w_H Wy) ms)).
{ unfold addreg at 1. raddB HS3 E'' HE'' R_g3 0x9dfe0 0x9dfe8. rlit R_g3 Y3. }
assert (HS5 : st_ok tfibsegs E'' (addreg R_g1 (addreg R_g3 (addreg R_g2 (addreg R_f1 (addreg R_f2 B_0))))) (restrict (w_H Wy) ms)).
{ unfold addreg at 1. raddB HS4 E'' HE'' R_g1 0x9dfd8 0x9dfe0. rlit R_g1 Y1. }
assert (HS6 : st_ok tfibsegs E'' (addreg R_scj (addreg R_g1 (addreg R_g3 (addreg R_g2 (addreg R_f1 (addreg R_f2 B_0)))))) (restrict (w_H Wy) ms)).
{ unfold addreg at 1. raddB HS5 E'' HE'' R_scj 0x21448 0x2144c. rlit R_scj X4. }
assert (HS7 : st_ok tfibsegs E'' (addreg R_sct (addreg R_scj (addreg R_g1 (addreg R_g3 (addreg R_g2 (addreg R_f1 (addreg R_f2 B_0))))))) (restrict (w_H Wy) ms)).
{ unfold addreg at 1. raddB HS6 E'' HE'' R_sct 0x214ac (0x214ac + 2). rlit R_sct X3. }
assert (HS8 : st_ok tfibsegs E'' (addreg R_pgsz (addreg R_sct (addreg R_scj (addreg R_g1 (addreg R_g3 (addreg R_g2 (addreg R_f1 (addreg R_f2 B_0)))))))) (restrict (w_H Wy) ms)).
{ unfold addreg at 1. raddB HS7 E'' HE'' R_pgsz 0x5f9250 0x5f9258. rlit R_pgsz X2. }
assert (HS9 : st_ok tfibsegs E'' (addreg R_can (addreg R_pgsz (addreg R_sct (addreg R_scj (addreg R_g1 (addreg R_g3 (addreg R_g2 (addreg R_f1 (addreg R_f2 B_0))))))))) (restrict (w_H Wy) ms)).
{ unfold addreg at 1. raddB HS8 E'' HE'' R_can 0x5f8fd0 0x5f8fd8.
unfold R_can, atom8, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict].
split; [clear; zlia|]. split; [clear; zlia|]. split; [intros o Ho; clear - Ho MZ; zlia|]. apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [| cbn; exact Rwc | cbn; clear; zlia | rewrite Z.add_0_l; exact Hwc].
cbn [sv_denot]. unfold E'', havoc. cbn [ew Nat.ltb Nat.leb aCAN Nat.sub nth]. unfold w64. rewrite Zbv_add_unsigned. f_equal. clear; zlia. }
unfold addreg at 1. raddB HS9 E'' HE'' R_got 0x9ec38 0x9ec40. rlit R_got X1.
Qed.
Lemma zcanon_m1 : forall x, 1 <= x < M64 -> zcanon (x + zcanon (-1)) = x - 1.
Proof.
clear. intros x Hx. unfold zcanon, M64 in *. change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1).
replace (x + (2 ^ 64 - 1)) with ((x - 1) + 1 * 2 ^ 64) by zlia. rewrite Z_mod_plus_full. apply Z.mod_small. zlia.
Qed.
Lemma U_PGB_X : U E0 PGB_X = PGBv.
Proof.
pose proof map_facts as (M1 & M2 & M3 & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _). pose proof map_zoneN as MZ. pose proof shadow_marks as (_ & _ & _ & _ & _ & _ & A7 & _).
pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & _).
clear - M1 M2 M3 SM1 SM2 A7 Z8 MZ.
unfold PGB_X, PGBv. rewrite U_zev by reflexivity. cbn [zev zalu_raw]. unfold rho_of. rewrite EaSHB, EaMAP. unfold w64, AFjm.SHBv in *.
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kHighShadowBeg, kHighShadowEnd, MALLOC_MAX in *. rewrite !unsigned_lit_small by zlia.
zcanon_simp. land_lits. rewrite Z.shiftr_div_pow2 by zlia. change (2 ^ 3) with 8.
apply Z.mod_divide in M3 as [u Hu]; [|zlia]. rewrite Hu in *. replace (u * 4096 + 6144) with ((u * 512 + 768) * 8) by zlia. rewrite Z_div_mult by zlia.
zcanon_simp. rewrite zcanon_m1 by (unfold M64; zlia). change 18446744073709547520 with (2 ^ 64 - 2 ^ 12).
rewrite land_neg_pow2_u64 by zlia. change (2 ^ 12) with 4096.
rewrite A7. replace (u * 4096) with ((u * 512) * 8) by zlia. rewrite Z_div_mult by zlia.
pose proof (Z.div_mod (2147450880 + u * 512 + 768 + 4095) 4096 ltac:(zlia)) as D1. pose proof (Z.mod_pos_bound (2147450880 + u * 512 + 768 + 4095) 4096 ltac:(zlia)) as R1.
replace (2147450880 + 0 + (u * 512 + 768) + 4096 - 1) with (2147450880 + u * 512 + 768 + 4095) by zlia. rewrite zcanon_id; unfold M64; zlia.
Qed.
Lemma U_PGE_X : U E0 PGE_X = PGEv.
Proof.
pose proof map_facts as (M1 & M2 & M3 & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _ & PB & _). pose proof map_zoneN as MZ. pose proof shadow_marks as (_ & _ & _ & _ & _ & _ & A7 & _).
pose proof size_facts as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & _). pose proof Nrange as NR. pose proof user_marks as (B1 & _).
clear - M1 M2 M3 SM1 SM2 PB A7 Z4 Z5 Z8 NR B1 MZ.
unfold PGE_X, PGEv. rewrite U_zev by reflexivity. cbn [zev zalu_raw]. unfold rho_of. rewrite EaSHB, EaMAP, EaN8D. unfold w64, AFjm.SHBv in *.
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kHighShadowBeg, kHighShadowEnd, MALLOC_MAX in *. rewrite !unsigned_lit_small by zlia.
zcanon_simp. land_lits. rewrite Z.shiftr_div_pow2 by zlia. change (2 ^ 3) with 8.
apply Z.mod_divide in M3 as [u Hu]; [|zlia]. apply Z.mod_divide in Z5 as [p Hp]; [|zlia]. rewrite Hu, Hp in *.
replace (u * 4096 + 6136 + (p * 8 + 0)) with ((u * 512 + 767 + p) * 8) by zlia. rewrite Z_div_mult in * by zlia.
zcanon_simp. change 18446744073709547520 with (2 ^ 64 - 2 ^ 12). rewrite land_neg_pow2_u64 by zlia. change (2 ^ 12) with 4096.
rewrite PB, A7. replace (u * 4096) with ((u * 512) * 8) by zlia. rewrite Z_div_mult by zlia.
rewrite !Z.add_0_r. replace (u * 512 + 767 + p + 1 + 2147450880) with (2147450880 + u * 512 + 768 + p) by zlia.
pose proof (Z.div_mod (2147450880 + u * 512 + 768 + p) 4096 ltac:(zlia)) as D1. pose proof (Z.mod_pos_bound (2147450880 + u * 512 + 768 + p) 4096 ltac:(zlia)) as R1.
rewrite zcanon_id; unfold M64; zlia.
Qed.
Lemma brun_refill : forall (m : word -> option byte) d e v sh,
Forall (brun m) ((d, e, v) :: cut d e sh) ->
(forall r, In r sh -> forall a, fst (fst r) <= a < snd (fst r) -> d <= a < e -> snd r = v) ->
Forall (brun m) sh.
Proof.
clearP. intros m d e v sh HF HV. pose proof (Forall_inv HF) as Hhd. pose proof (Forall_inv_tail HF) as HC. clear HF.
apply Forall_forall. intros r Hr a Ha. destruct r as [[lo hi] vr]. cbn [fst snd] in Ha |- *.
destruct (Z_lt_le_dec a d) as [Hlt|Hge].
-
assert (HP : In (lo, Z.min hi d, vr) (cut d e sh)).
{ unfold cut. apply in_flat_map. exists (lo, hi, vr). split; [exact Hr|]. unfold cut1. cbn [fst snd].
replace (lo <? d) with true by (symmetry; apply Z.ltb_lt; zlia). apply in_or_app. left. left. reflexivity. }
exact (proj1 (Forall_forall _ _) HC _ HP a ltac:(cbn [fst snd]; zlia)).
- destruct (Z_lt_le_dec a e) as [Hlt2|Hge2].
+
pose proof (HV _ Hr a ltac:(cbn [fst snd]; zlia) ltac:(zlia)) as Ev. cbn [snd] in Ev. rewrite Ev. exact (Hhd a ltac:(cbn [fst snd]; zlia)).
+
assert (HP : In (Z.max lo e, hi, vr) (cut d e sh)).
{ unfold cut. apply in_flat_map. exists (lo, hi, vr). split; [exact Hr|]. unfold cut1. cbn [fst snd].
replace (e <? hi) with true by (symmetry; apply Z.ltb_lt; zlia). apply in_or_app. right. left. reflexivity. }
exact (proj1 (Forall_forall _ _) HC _ HP a ltac:(cbn [fst snd]; zlia)).
Qed.
Lemma SH4_head : forall m, Forall (brun m) ((SMv + 768, SMv + 768 + (PGBv - (SMv + 768)), 0) :: cut (SMv + 768) (SMv + 768 + (PGBv - (SMv + 768))) SH4) -> Forall (brun m) SH4.
Proof.
intros m HF. pose proof (big_marks Hbig) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13).
apply (brun_refill m _ _ 0 SH4 HF). clear - C5 C9 C7 C13. intros r Hr a Ha Hd. unfold SH4 in Hr. cbn [In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Ha |- *; zlia.
Qed.
Lemma SH4_tail : forall m, Forall (brun m) ((PGEv, PGEv + (PBv - PGEv), 0) :: cut PGEv (PGEv + (PBv - PGEv)) SH4) -> Forall (brun m) SH4.
Proof.
intros m HF. pose proof (big_marks Hbig) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13).
apply (brun_refill m _ _ 0 SH4 HF). clear - C5 C9 C7 C13. intros r Hr a Ha Hd. unfold SH4 in Hr. cbn [In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Ha |- *; zlia.
Qed.
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
Lemma segB1a : forall (W' : world tfibsegs) c, at_S Wy md1 X (PSR Wy SH4 (PDX Wy RX z)) B_R W' c -> SRr tfibsegs W' c (at_S Wy md1 X (PSR Wy SH4 (PDX Wy RX z)) B_D).
Proof.
intros W1 c HR. pose proof SH34_ok as [_ OK4]. pose proof (PDX_rstable Wy RX RXs z) as RS.
pose proof (PSR_stableS Wy SH4 (PDX Wy RX z) OK4 (PDX_stableS Wy RX RXt z)) as HP4.
assert (HX : forall a, WIN1S a -> X a) by (intros a Ha; apply HXW, WIN1S_WIN, Ha).
pose proof (big_marks Hbig) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13). pose proof sm_bounds as SMB.
pose proof U_SHBT as V1. pose proof (U_SHET Hbig) as V2. pose proof (U_PGBT Hbig) as V3. pose proof (U_PGET Hbig) as V4.
s_runS HR tfibtbl_rtD tfibtbl_rtD_ok 0x53ad4 B_A0 HX HP4.
s_pin HR (10%bv : bv 5) SHBT. { rewrite V1. symmetry. exact U_SHB_X. }
s_pin HR (20%bv : bv 5) SHET. { rewrite V2. symmetry. exact U_SHE_X. }
s_pin HR (9%bv : bv 5) PGBT. { rewrite V3. symmetry. exact U_PGB_X. }
s_pin HR (18%bv : bv 5) PGET. { rewrite V4. symmetry. exact U_PGE_X. }
s_station HR B_A.
s_arm HR BC_GEU false PGBT PGET. { clear - V3 V4 C9. rewrite branch_geu_U, V3, V4. apply Bool.negb_false_iff. apply Z.ltb_lt. zlia. }
s_runS HR tfibtbl_rtD tfibtbl_rtD_ok 0x53ad8 B_B0 HX HP4.
s_arm HR BC_EQ false PGBT SHBT. { clear - V1 V3 C5. rewrite branch_eq_U. rewrite V1, V3. apply Z.eqb_neq. zlia. }
s_runS HR tfibtbl_rtD tfibtbl_rtD_ok 0x97698 B_M1 HX HP4.
s_memsetR HR B_C sB1 constr:(SMv + 768) constr:(PGBv - (SMv + 768)) 0 0x53aec OK4 RS.
{ exact V1. }
{ clear - V1 V3 C5 C6 C7 C8 C9 C11 SMB. change (U E0 (SAlu ALU_SUB PGBT SHBT) = PGBv - (SMv + 768)). rewrite U_SAlu. cbn [zalu_raw]. rewrite V1, V3. apply zcanon_id. unfold M64. zlia. }
{ right. clear - C5 C9 C7 C11. zlia. }
apply (PSR_runs Wy md1 X _ SH4 (PDX Wy RX z) B_C) in HR; [| exact SH4_head].
assert (BC : forall b : bool, b = true \/ b = false) by (intros [|]; [left | right]; reflexivity).
destruct (BC (branch_taken BC_EQ (sv_denot E0 SHET) (sv_denot E0 PGET))) as [TK|TK]; clear BC.
- s_arm HR BC_EQ true SHET PGET. { exact TK. }
s_runS HR tfibtbl_rtD tfibtbl_rtD_ok 0x53b04 B_Ct HX HP4.
s_forget HR kJB CLOBB. s_noconds HR. s_station HR B_D. apply SRr_ret. exact HR.
- s_arm HR BC_EQ false SHET PGET. { exact TK. }
s_runS HR tfibtbl_rtD tfibtbl_rtD_ok 0x97698 B_M2 HX HP4.
s_memsetR HR B_Cf sB2 constr:(PGEv) constr:(PBv - PGEv) 0 0x53b04 OK4 RS.
{ clear - V4 C5 C6 C7 C8 C9 C11 SMB. change (U E0 (SAlu ALU_ADD PGET (SLit 0)) = PGEv). rewrite U_SAlu. cbn [zalu_raw]. rewrite V4. change (U E0 (SLit 0)) with 0. rewrite Z.add_0_r. apply zcanon_id. unfold M64. zlia. }
{ clear - V2 V4 C5 C6 C7 C8 C9 C11 SMB. change (U E0 (SAlu ALU_SUB SHET PGET) = PBv - PGEv). rewrite U_SAlu. cbn [zalu_raw]. rewrite V2, V4. apply zcanon_id. unfold M64. zlia. }
{ right. clear - C5 C9 C7 C11. zlia. }
apply (PSR_runs Wy md1 X _ SH4 (PDX Wy RX z) B_Cf) in HR; [| exact SH4_tail].
s_forget HR kJB CLOBB. s_noconds HR. s_station HR B_D. apply SRr_ret. exact HR.
Qed.
Lemma zc_m1 : forall x, zcanon (x + 18446744073709551615) = zcanon (x - 1).
Proof. clear. intros x. unfold zcanon, M64. replace (x + 18446744073709551615) with ((x - 1) + 1 * 2 ^ 64) by zlia. apply Z_mod_plus_full. Qed.
Lemma zc_idem : forall x, zcanon (zcanon x) = zcanon x.
Proof. clear. intros x. unfold zcanon, M64. apply Z.mod_mod. zlia. Qed.
Lemma zc_add_l : forall x y, zcanon (zcanon x + y) = zcanon (x + y).
Proof. clear. intros x y. unfold zcanon, M64. apply Zplus_mod_idemp_l. Qed.
Lemma zc_sub_l : forall x y, zcanon (zcanon x - y) = zcanon (x - y).
Proof. clear. intros x y. unfold zcanon, M64. unfold Z.sub. apply Zplus_mod_idemp_l. Qed.
Lemma zc_sub_r : forall x y, zcanon (x - zcanon y) = zcanon (x - y).
Proof. clear. intros x y. unfold zcanon, M64. apply Zminus_mod_idemp_r. Qed.
Lemma land_page_id : forall x, 0 <= x < M64 -> x mod 4096 = 0 -> Z.land x 18446744073709547520 = x.
Proof. clear. intros x Hx Hm. change 18446744073709547520 with (2 ^ 64 - 2 ^ 12). unfold M64 in Hx. rewrite land_neg_pow2_u64 by zlia. change (2 ^ 12) with 4096. zlia. Qed.
Lemma U_KA0 : U E0 KA0 = PGBv.
Proof.
pose proof (big_marks Hbig) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13). pose proof sm_bounds as SMB. pose proof (U_PGBT Hbig) as V3.
clear - C3 C5 C6 C7 C9 C11 SMB V3.
change (U E0 (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_AND (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_ADD PGBT (SLit 0)) (SLit 0)) (SLit 0)) (SLit 0)) (SLit 18446744073709547520)) (SLit 0)) (SLit 0)) (SLit 0)) = PGBv).
rewrite !U_SAlu. cbn [zalu_raw]. rewrite V3. change (U E0 (SLit 0)) with 0. change (U E0 (SLit 18446744073709547520)) with 18446744073709547520.
rewrite !Z.add_0_r. rewrite !(zcanon_id PGBv) by (unfold M64; zlia). rewrite land_page_id by (unfold M64; zlia). rewrite !(zcanon_id PGBv) by (unfold M64; zlia). reflexivity.
Qed.
Lemma U_KA1 : U E0 KA1 = PGEv - PGBv.
Proof.
pose proof (big_marks Hbig) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13). pose proof sm_bounds as SMB.
pose proof (U_PGBT Hbig) as V3. pose proof (U_PGET Hbig) as V4. clear - C3 C4 C5 C6 C7 C8 C9 C11 SMB V3 V4.
change (U E0 (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_AND (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_ADD
(SAlu ALU_SUB (SAlu ALU_ADD (SAlu ALU_ADD PGET (SLit (-1))) (SLit 0)) (SAlu ALU_ADD (SAlu ALU_ADD PGBT (SLit 0)) (SLit 0))) (SLit 1)) (SLit 0)) (SLit 0))
(SLit 4096)) (SLit (-1))) (SLit 18446744073709547520)) (SLit 0)) (SLit 0)) (SLit 0)) = PGEv - PGBv).
rewrite !U_SAlu. cbn [zalu_raw]. rewrite V3, V4. change (U E0 (SLit 0)) with 0. change (U E0 (SLit 18446744073709547520)) with 18446744073709547520.
change (U E0 (SLit (-1))) with 18446744073709551615. change (U E0 (SLit 1)) with 1. change (U E0 (SLit 4096)) with 4096.
rewrite !Z.add_0_r. rewrite !zc_idem. rewrite (zc_m1 PGEv). rewrite zc_sub_l, zc_sub_r, !zc_add_l.
rewrite <- (Z.add_assoc (zcanon (PGEv - 1 - PGBv + 1))). rewrite zc_add_l. rewrite Z.add_assoc. rewrite zc_m1.
replace (PGEv - 1 - PGBv + 1 + 4096 - 1) with (PGEv - PGBv + 4095) by zlia. rewrite (zcanon_id (PGEv - PGBv + 4095)) by (unfold M64; zlia).
assert (HM : (PGEv - PGBv + 4095) mod 4096 = 4095).
{ pose proof C3 as C3'. pose proof C4 as C4'. apply Z.mod_divide in C3' as [a Ha]; [|zlia]. apply Z.mod_divide in C4' as [b Hb]; [|zlia]. rewrite Ha, Hb.
replace (b * 4096 - a * 4096 + 4095) with (4095 + (b - a) * 4096) by zlia. rewrite Z_mod_plus_full. reflexivity. }
change 18446744073709547520 with (2 ^ 64 - 2 ^ 12). rewrite land_neg_pow2_u64 by zlia. change (2 ^ 12) with 4096. rewrite HM.
rewrite !zcanon_id by (unfold M64; zlia). zlia.
Qed.
Lemma U_REM1 : U E0 REM1 = 0.
Proof.
pose proof (big_marks Hbig) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13). pose proof sm_bounds as SMB. pose proof (U_PGBT Hbig) as V3.
clear - C3 C5 C6 C9 C11 SMB V3.
change (U E0 (SMd M_REMU (SAlu ALU_ADD (SAlu ALU_ADD PGBT (SLit 0)) (SLit 0)) (SLit 4096)) = 0).
rewrite U_SMd, !U_SAlu. cbn [zalu_raw zmd_raw Z.eqb]. rewrite V3. change (U E0 (SLit 0)) with 0. change (U E0 (SLit 4096)) with 4096.
rewrite !Z.add_0_r. rewrite !(zcanon_id PGBv) by (unfold M64; zlia). rewrite C3. reflexivity.
Qed.
Lemma U_REM2 : U E0 REM2 = 0.
Proof.
pose proof (big_marks Hbig) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13). pose proof sm_bounds as SMB. pose proof (U_PGET Hbig) as V4.
clear - C4 C5 C6 C7 C9 C11 SMB V4.
change (U E0 (SMd M_REMU (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_ADD PGET (SLit (-1))) (SLit 0)) (SLit 1)) (SLit 4096)) = 0).
rewrite U_SMd, !U_SAlu. cbn [zalu_raw zmd_raw Z.eqb]. rewrite V4. change (U E0 (SLit 0)) with 0. change (U E0 (SLit 4096)) with 4096.
change (U E0 (SLit (-1))) with 18446744073709551615. change (U E0 (SLit 1)) with 1.
rewrite !Z.add_0_r. rewrite zc_m1, !zc_add_l. replace (PGEv - 1 + 1) with PGEv by zlia. rewrite !(zcanon_id PGEv) by (unfold M64; zlia). rewrite C4. reflexivity.
Qed.
Lemma segB1b : forall (W' : world tfibsegs) c, at_S Wy md1 X (PSR Wy SH4 (PDX Wy RX z)) B_D W' c -> SRr tfibsegs W' c (at_N Wy md1 X (PSR Wy SH4 (PDX Wy RX z)) S_K).
Proof.
intros W1 c HR. pose proof SH34_ok as [_ OK4]. pose proof (PSR_stableS Wy SH4 (PDX Wy RX z) OK4 (PDX_stableS Wy RX RXt z)) as HP4.
assert (HX : forall a, WIN1S a -> X a) by (intros a Ha; apply HXW, WIN1S_WIN, Ha).
pose proof U_REM1 as R1. pose proof U_REM2 as R2.
s_runS HR tfibtbl_rtD tfibtbl_rtD_ok 0x6beac B_E0 HX HP4.
s_arm HR BC_NE false REM1 (SLit 0). { clear - R1. rewrite branch_ne_U, R1. reflexivity. }
s_station HR B_E.
s_runS HR tfibtbl_rtD tfibtbl_rtD_ok 0x6bebc B_F0 HX HP4.
s_arm HR BC_NE false REM2 (SLit 0). { clear - R2. rewrite branch_ne_U, R2. reflexivity. }
s_station HR B_F.
s_ecallS HR tfibtbl_rtD tfibtbl_rtD_ok S_K HX HP4.
Qed.
Lemma segB1 : forall (W' : world tfibsegs) c, at_S Wy md1 X (PSR Wy SH4 (PDX Wy RX z)) T_R W' c -> SRr tfibsegs W' c (at_N Wy md1 X (PSR Wy SH4 (PDX Wy RX z)) S_K).
Proof.
intros W1 c HR. apply B_R_ok in HR. eapply SRr_bind; [exact (segB1a W1 c HR)|]. clear HR. intros W2 c2 _ HR. exact (segB1b W2 c2 HR).
Qed.
Lemma nores4032 : mmap_noreserve_b (Z_to_bv 64 0x4032) = true. Proof. clear. reflexivity. Qed.
Lemma core4032 : mmap_flags_core (Z_to_bv 64 0x4032) = 50. Proof. clear. reflexivity. Qed.
Lemma lit4032 : Z_to_bv 64 16434 = Z_to_bv 64 0x4032. Proof. clear. reflexivity. Qed.
Lemma S_K_facts :
ss_pc S_K = 0x6416c /\ sr_get (ss_regs S_K) 17%bv = SLit 222 /\ sr_get (ss_regs S_K) 10%bv = KA0 /\ sr_get (ss_regs S_K) 11%bv = KA1 /\
sr_get (ss_regs S_K) 12%bv = SLit 3 /\ sr_get (ss_regs S_K) 13%bv = SLit 0x4032 /\ sr_get (ss_regs S_K) 14%bv = SLit 18446744073709551615 /\
sr_get (ss_regs S_K) 15%bv = SLit 0 /\ no_cdata (ss_mem S_K) = true /\ ss_resv S_K = None /\ sv_atoms_lt sHAV KA0 = true /\ sv_atoms_lt sHAV KA1 = true /\
forallb (fun r => skel_okb false (skel r)) (ss_mem S_K) = true.
Proof. clearP. vm_compute. repeat split; reflexivity. Qed.
Lemma nodeK : forall {RT : Type} (sN : astate) (K : Z -> itree astate RT) (Q : RT -> world tfibsegs -> config -> Prop) (base : sptr) (len8 : Z) (c1 : config),
at_N Wy md1 X (PSR Wy SH4 (PDX Wy RX z)) S_K Wy c1 -> AI tfibsegs (w_H Wy) (w_A Wy) (cfg_model c1) ->
amwf (cfg_model c1) ->
vm_reserved (m_vmmaps (cfg_model c1)) = segments_reserved tfibsegs ->
(forall sg, In sg tfibsegs -> 4096 <= Z.of_N (seg_base sg) /\ Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <= kImgEnd) ->
(forall z, In z band_maps -> In (wiv z) (vm_maps (m_vmmaps (cfg_model c1)))) ->
YM05.ceil_of_top (alloc_top (m_vmmaps (cfg_model c1))) ->
(forall w : word, SMv <= bv_unsigned w < SMv + MSv / 8 -> w_H Wy w = false -> page_allowedb (w_A Wy) (page_base w) = true) ->
(forall zz, zz = 0 \/ zz = 1 -> aok sN (KShadowRemap base len8) zz) ->
(forall (c' : config), let mdK := grant_md false (Z_to_bv 64 0x4032) (w64 PGBv) (w64 (PGEv - PGBv)) (cfg_model c1) in
AI tfibsegs (w_H Wy) (w_A Wy) mdK -> MWF mdK -> same_io md0 mdK ->
at_S Wy mdK X (PSR Wy SH4 (PDX Wy RX z)) K_G0 Wy c' ->
amreal tfibsegs (K 1) Wy c' Q) ->
same_io md0 (cfg_model c1) ->
exists (I : Type) (nx : I -> config) (bit : I -> Z) (sp : I -> bool) (i0 : I),
node_ok tfibsegs c1 I (fun _ => []) nx /\
(forall i, AI tfibsegs (w_H Wy) (w_A Wy) (cfg_model c1) -> AI tfibsegs (w_H Wy) (w_A Wy) (cfg_model (nx i))) /\
(forall i, aok sN (KShadowRemap base len8) (bit i)) /\ sp i0 = false /\ bit i0 = 1 /\
(forall i, sp i = false -> bit i = 1) /\
(forall i, sp i = true -> AI tfibsegs (w_H Wy) (w_A Wy) (cfg_model (nx i)) -> srealizes tfibsegs (nx i) t_nil) /\
(forall i, sp i = false -> amreal tfibsegs (K (bit i)) Wy (nx i) Q).
Proof.
intros. exfalso. clear - Hbig Nrange. unfold AFjm.N8D in Hbig. unfold MALLOC_MAX in Nrange.
rewrite Z.div_mul in Hbig by (clear; lia).
pose proof (Z.div_lt_upper_bound n 8 (2 ^ 25) ltac:(clear; lia) ltac:(clear - Nrange; lia)) as HH. clear Nrange. lia.
Qed.
Fixpoint submemb2 (rs' rs : smem) : bool :=
match rs with
| [] => match rs' with [] => true | _ => false end
| r :: t => match rs' with
| [] => true
| r' :: t' => if subregionb r' r then (if submemb2 t' t then true else submemb2 rs' t) else submemb2 rs' t
end
end.
Lemma submemb2_sound : forall rs rs', submemb2 rs' rs = true -> submem rs' rs.
Proof.
clearP. induction rs as [|r t IH]; intros rs' H.
- destruct rs'; [apply submem_nil | discriminate H].
- destruct rs' as [|r' t']; [apply submem_nil|]. cbn [submemb2] in H.
destruct (subregionb r' r) eqn:H1; [destruct (submemb2 t' t) eqn:H2|].
+ apply submem_keep; [exact (subregionb_sound _ _ H1) | exact (IH _ H2)].
+ apply submem_drop. exact (IH _ H).
+ apply submem_drop. exact (IH _ H).
Qed.
Lemma at_S_submem2 : forall (Wx : world tfibsegs) md X' P ss W' c' rs,
at_S Wx md X' P ss W' c' -> submemb2 rs (ss_mem ss) = true -> regions_wf rs = true ->
at_S Wx md X' P (mkSS (ss_pc ss) (ss_regs ss) rs (ss_resv ss) (ss_facts ss)) W' c'.
Proof.
clearP. intros Wx md X' P ss W' c' rs HR Hsb Hwf. destruct HR as (-> & ms & mat & E' & -> & HE & HS & MEQ & PRS & HPm).
split; [reflexivity|]. exists ms, mat, E'. split; [reflexivity|]. split; [exact HE|]. split; [|exact (conj MEQ (conj PRS HPm))].
exact (st_ok_submem tfibsegs E' ss _ rs HS (submemb2_sound _ _ Hsb) Hwf).
Qed.
Lemma SH5_of_SH4 : forall m, Forall (brun m) SH4 -> Forall (brun m) SH5.
Proof.
intros m HF. pose proof (big_marks Hbig) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13). pose proof user_marks as (B1 & _).
unfold SH4 in HF. pose proof (Forall_inv HF) as R1. pose proof (Forall_inv (Forall_inv_tail HF)) as R2.
pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HF))) as R3. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail HF)))) as R4. clear HF.
unfold SH5. apply Forall_cons; [|apply Forall_cons; [exact R1 | apply Forall_cons; [exact R2 | apply Forall_cons; [exact R3 | apply Forall_cons; [|apply Forall_nil]]]]].
- intros a Ha. cbn [fst snd] in Ha |- *. apply R4. cbn [fst snd]. clear - Ha C1 C13 B1. zlia.
- intros a Ha. cbn [fst snd] in Ha |- *. apply R4. cbn [fst snd]. clear - Ha C1 C13 B1. zlia.
Qed.
Lemma segB2 : forall md c, at_S Wy md X (PSR Wy SH4 (PDX Wy RX z)) K_G0 Wy c -> SRr tfibsegs Wy c (at_S Wy md X (PSR Wy SH5 (PDX Wy RX z)) U_QJ).
Proof.
intros md c HR. pose proof SH34_ok as [_ OK4]. pose proof (PSR_stableS Wy SH4 (PDX Wy RX z) OK4 (PDX_stableS Wy RX RXt z)) as HP4.
assert (HX : forall a, WIN1S a -> X a) by (intros a Ha; apply HXW, WIN1S_WIN, Ha).
s_runS HR tfibtbl_rtD tfibtbl_rtD_ok 0x319d8 B_Q HX HP4.
lazymatch type of HR with at_S ?Wx ?md' ?X0 ?P ?ss ?W' ?c' =>
apply (at_S_submem2 Wx md' X0 P ss W' c' (trimscratch (-2272) (skipn 10 (ss_mem B_Q)))) in HR; [| vm_compute; reflexivity | vm_compute; reflexivity] end.
s_forget HR kJQ CLOBJ. s_noconds HR. s_station HR U_QJ.
apply (PSR_runs Wy md X _ SH5 (PDX Wy RX z) U_QJ) in HR; [| exact SH5_of_SH4].
apply SRr_ret. exact HR.
Qed.
Lemma allow_of_hull : forall (Wz : world tfibsegs), In (SHLO mb, SHHI mb) (w_A Wz) ->
forall w : word, SMv <= bv_unsigned w < SMv + MSv / 8 -> w_H Wz w = false -> page_allowedb (w_A Wz) (page_base w) = true.
Proof.
intros Wz HIN w Hw _. pose proof (SH_hull mb) as (H1 & H2 & _ & H4 & H5 & _). pose proof map_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SMA). pose proof map_zoneN as MZ.
pose proof (YA09.page_base_facts w) as (P1 & P2 & P3). rewrite <- SMA in H1, H2.
unfold page_allowedb. apply existsb_exists. exists (SHLO mb, SHHI mb). split; [exact HIN|]. cbn [fst snd]. unfold page_size.
clear - Hw H1 H2 H4 H5 P1 P2 P3 MZ.
apply Z.mod_divide in H4 as [a Ha]; [|zlia]. apply Z.mod_divide in H5 as [b Hb]; [|zlia]. apply Z.mod_divide in P3 as [c Hc]; [|zlia].
rewrite Ha, Hb, Hc in *. apply andb_true_intro. split; apply Z.leb_le; nia.
Qed.
End U.
End g.
End f.
