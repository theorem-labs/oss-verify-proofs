(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YQ0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG04 YG06 YG07 YG03 YG0h YG10 YG0u YG0d YG0y YG0w.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP09.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF64 YF3v YF3w YF3x YF41 YF47 YF0a YF5k.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK0k YK0v YK13 YQ0k YA05 YA09 YG0b YG0j YF05.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF4b YF4c YF4d YF4e YF4f YF4g YF5t YF5u YF5v YF5f YF5l YF5m YF5i YF5j YF5n YF5o YF5q YF5r YF60.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YA00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF48.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac img_facts ::= lazymatch goal with k : img |- _ => let F := fresh "IMGF" in pose proof (P_facts k) as F end.
Ltac img_lia ::=
first [ (img_goal_has_k; img_facts; lia)
| lia
| (img_inst; lia)
| (try img_inst;
first [ (img_local; img_local_unfold; img_unfold_all; lia)
| (img_arith_rel; first [ (img_facts; lia)
| (img_has_moddiv; img_case; img_unfold_all; lia)
| (first [ img_has_moddiv | img_has_match ]; img_concrete; img_unfold_all; lia) ]) ]) ].
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Set Printing Depth 50. Set Printing Width 180.
Section g. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Ltac zlia := first [ img_lia | ceil; unfold zone3, zone3cases, off_img, in_app, app_addr, in_band_rw, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPrimResvSize, kSpaceSize, kPtrArrayResv, kMaxNumChunks in *; img_lia ].
Ltac zcanon_simp :=
repeat match goal with
| |- context [zcanon ?x] =>
lazymatch x with
| context [zcanon _] => fail
| context [Z.shiftl _ _] => fail | context [Z.shiftr _ _] => fail | context [Z.land _ _] => fail
| context [Z.lor _ _] => fail | context [Z.lxor _ _] => fail
| _ => rewrite (zcanon_id x) by (img_try (unfold M64; zlia))
end
end.
Ltac is_zlit a := lazymatch a with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.
Ltac land_lits :=
repeat match goal with
| |- context [Z.land ?a ?b] => is_zlit a; is_zlit b; let c := img_ev (Z.land a b) in img_change (Z.land a b) with c
end.
Ltac numconst := ceil; unfold zone3, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize,
t_cache, t_unwinding, t_stats, ASTACK, TFX_IMG_END, TFX_IMG_LO, kLowShadowBeg, UNW_STK, BST_SIZE, DEP_STK in *.
Ltac pin_zev :=
lazymatch goal with |- U _ _ = U _ (sr_get ?sr ?r) => let t := img_ev (sr_get sr r) in img_change (sr_get sr r) with t end;
img_apply U_eq_by_zev; [img_refl | img_refl |]; cbn [zev zalu_raw zmd_raw]; unfold rho_of.
Ltac memv HS i j :=
lazymatch goal with |- val_mem _ _ ?a ?n ?v =>
let nn := lazymatch n with 1%nat => constr:(1%N) | 2%nat => constr:(2%N) | 4%nat => constr:(4%N) | _ => constr:(8%N) end in
lazymatch type of HS with st_ok _ ?E ?ss (restrict ?H ?ms) =>
eapply (chunk_val_at H E ss ms i j _ _ nn _ v a HS);
[ img_refl | img_refl | cbn [base_val YQ0b.r_base]
| | lazymatch goal with |- _ <= _ < ?p => let q := img_ev constr:(p) in img_change p with q end
| cbn; img_lia ]
end
end.
Ltac forget_regs HS k clob :=
lazymatch type of HS with st_ok _ ?E ?ss (restrict ?H ?ms) =>
let ss' := img_ev (ss_after_stretch ss (ss_mem ss) k clob (ss_pc ss)) in
let HS2 := fresh "HSf" in
pose proof (st_ok_forget2 k E ss ss' H ms clob HS ltac:(img_eqrefl)
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_eqrefl) ltac:(img_eqrefl) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))) as HS2; clear HS; rename HS2 into HS
end.
Section h. Context {imgk : img}.
Variables (W : world tfxsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (n : Z) (ch : list (Z * Z * Z)).
Variables (idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 : Z).
Variable mb : Z.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Let Qb : Z := ly_Q ly.
Local Abbreviation R8v := (@YF5k.R8v n).
Local Abbreviation N8D := (@YF5k.N8D n).
Local Abbreviation NDv := (@YF5k.NDv n).
Local Abbreviation MSv := (@YF5k.MSv n).
Local Abbreviation SHBv := (@YF5k.SHBv).
Local Abbreviation QSv := (@YF5k.QSv ly idx).
Local Abbreviation Kv := (@YF5k.Kv mb).
Local Abbreviation Uv := (@YF5k.Uv mb).
Local Abbreviation ENDv := (@YF5k.ENDv n mb).
Local Abbreviation TLv := (@YF5k.TLv n).
Local Abbreviation UEv := (@YF5k.UEv n mb).
Local Abbreviation RLv := (@YF5k.RLv n).
Local Abbreviation SMv := (@YF5k.SMv mb).
Local Abbreviation PBv := (@YF5k.PBv n mb).
Local Abbreviation LGv := (@YF5k.LGv n).
Local Abbreviation BSLv := (@YF5k.BSLv n imgk).
Local Abbreviation AR1 f := (f imgk ly regs0) (only parsing).
Local Abbreviation tr := ((AR1 (@YF5k.tr)) ch).
Local Abbreviation AR0 f := (f n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb) (only parsing).
Local Abbreviation XW := (AR0 (AR1 (@YF5k.XW))).
Local Abbreviation E0 := (AR0 (AR1 (@YF5k.E0))).
Local Abbreviation Er := (AR0 (AR1 (@YF5k.Er))).
Local Abbreviation E1 := (AR0 (AR1 (@YF5k.E1))).
Local Abbreviation E2 := (AR0 (AR1 (@YF5k.E2))).
Local Abbreviation E4 := (AR0 (AR1 (@YF5k.E4))).
Local Abbreviation E8 := (AR0 (AR1 (@YF5k.E8))).
Local Abbreviation E10 := (AR0 (AR1 (@YF5k.E10))).
Local Abbreviation EaT := (AR0 (AR1 (@YF5k.EaT))).
Local Abbreviation EaC := (AR0 (AR1 (@YF5k.EaC))).
Local Abbreviation EaSB := (AR0 (AR1 (@YF5k.EaSB))).
Local Abbreviation EaTOP := (AR0 (AR1 (@YF5k.EaTOP))).
Local Abbreviation EaR8 := (AR0 (AR1 (@YF5k.EaR8))).
Local Abbreviation EaQ := (AR0 (AR1 (@YF5k.EaQ))).
Local Abbreviation EaRES := (AR0 (AR1 (@YF5k.EaRES))).
Local Abbreviation EaNCH := (AR0 (AR1 (@YF5k.EaNCH))).
Local Abbreviation EaMS := (AR0 (AR1 (@YF5k.EaMS))).
Local Abbreviation EaMAP := (AR0 (AR1 (@YF5k.EaMAP))).
Local Abbreviation EaEND := (AR0 (AR1 (@YF5k.EaEND))).
Local Abbreviation EaSHB := (AR0 (AR1 (@YF5k.EaSHB))).
Local Abbreviation EaTL := (AR0 (AR1 (@YF5k.EaTL))).
Local Abbreviation EaQS := (AR0 (AR1 (@YF5k.EaQS))).
Local Abbreviation EaBSL := (AR0 (AR1 (@YF5k.EaBSL))).
Local Abbreviation EaSM := (AR0 (AR1 (@YF5k.EaSM))).
Local Abbreviation EaUE := (AR0 (AR1 (@YF5k.EaUE))).
Local Abbreviation EaND := (AR0 (AR1 (@YF5k.EaND))).
Local Abbreviation EaRL := (AR0 (AR1 (@YF5k.EaRL))).
Local Abbreviation EaN8D := (AR0 (AR1 (@YF5k.EaN8D))).
Local Abbreviation EaPB := (AR0 (AR1 (@YF5k.EaPB))).
Hypothesis LY : layout_ok ly.
Hypothesis IMG : img_cover ly.
Hypothesis Hn : getr regs0 10 = w64 n.
Hypothesis Htp : getr regs0 4 = w64 TFX_TP.
Hypothesis Hra : YK0s.ret_ok (getr regs0 1).
Hypothesis Hra4096 : 4096 <= bv_unsigned (getr regs0 1).
Hypothesis Hsp : ly_stk_lo ly + ASTACK <= sp0 /\ ly_bot ly < sp0 /\ sp0 <= ly_stk_hi ly /\ sp0 mod 16 = 0.
Hypothesis Hch : if sp0 + 16 <? ly_top ly
then (if bad_next sp0 (ly_top ly) (bv_unsigned (getr regs0 8)) then ch = []
else sp0 + 16 <= bv_unsigned (getr regs0 8) /\
fpchain (rdword (aview tfxsegs (w_H W) mem0)) (bv_unsigned (getr regs0 8)) (ly_top ly) ch)
else ch = [].
Hypothesis Nrange : 64513 <= n < MALLOC_MAX.
Hypothesis Hidx : 0 <= idx < kMaxNumChunks.
Hypothesis Hres : idx <= res <= kMaxNumChunks /\ res mod kPtrArrayEntriesPerCommit = 0.
Local Abbreviation mod0_of_mul := (@YF5k.mod0_of_mul).
Local Abbreviation size_facts := (@YF5k.size_facts n Nrange).
Local Abbreviation ARf f := (f idx res Hidx) (only parsing).
Local Abbreviation tr_length := (ARf ((AR1 (@YF5k.tr_length)) ch)).
Local Abbreviation ARe f := (f idx res LY IMG Hidx Hres) (only parsing).
Local Abbreviation high_facts := (ARe (AR1 (@YF5k.high_facts _))).
Local Abbreviation stack_ivs := (@YF5k.stack_ivs _ ly regs0 idx res LY Hsp Hidx Hres).
Local Abbreviation HCX := (@YF5k.HCX _ ly LY).
Hypothesis Hpres0 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem0 a.
Hypothesis Hmap : mb mod 4096 = 0 /\ mzone mb MSv.
Hypothesis Hmap_apart :
zdisjoint (mb, MSv) (T, kThreadObjSize) /\ zdisjoint (mb, MSv) (ly_C ly, kCtxMapSize) /\
zdisjoint (mb, MSv) (ly_prim ly, kPrimResvSize) /\ zdisjoint (mb, MSv) (Qb, kPtrArrayResv) /\
zdisjoint (mb, MSv) (ly_NB ly, kNodesBlockSize) /\ zdisjoint (mb, MSv) (ly_SB ly, kStoreBlockSize) /\
zdisjoint (mb, MSv) (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly).
Local Abbreviation AR3 f := (AR1 f n idx res mb) (only parsing).
Local Abbreviation AR5 f := (f Nrange Hidx Hres Hmap) (only parsing).
Local Abbreviation map_facts := (AR5 (AR3 (@YF5k.map_facts _))).
Local Abbreviation map_zone := ((AR3 (@YF5k.map_zone _)) Nrange Hidx Hmap).
Local Abbreviation map_zoneN := (AR5 (AR3 (@YF5k.map_zoneN _))).
Local Abbreviation map_in_band := ((AR3 (@YF5k.map_in_band _)) Nrange Hidx Hmap).
Local Abbreviation map_off_img := (@YF5k.map_off_img _ imgk n mb Hmap).
Local Abbreviation WINT := (@YF5k.WINT ly).
Local Abbreviation WINI := (@YF5k.WINI n imgk).
Local Abbreviation WINM := (@YF5k.WINM ly n idx mb).
Local Abbreviation ARc f := (AR1 f n) (only parsing).
Local Abbreviation ARi f := (ARc f idx mb) (only parsing).
Local Abbreviation WIN := (ARi (@YF5k.WIN)).
Local Abbreviation WINN := (AR1 (@YF5k.WINN)).
Local Abbreviation WINP := (ARc (@YF5k.WINP)).
Local Abbreviation WINP_WIN := (ARi (@YF5k.WINP_WIN)).
Local Abbreviation WIN1P := (ARc (@YF5k.WIN1P)).
Local Abbreviation WIN1 := (ARi (@YF5k.WIN1)).
Local Abbreviation WIN1P_WINP := ((AR3 (@YF5k.WIN1P_WINP)) Hidx).
Local Abbreviation WIN1_WIN := ((AR3 (@YF5k.WIN1_WIN)) Hidx).
Local Abbreviation WIN1P_WIN1 := (ARi (@YF5k.WIN1P_WIN1)).
Local Abbreviation LGv_range := (@YF5k.LGv_range n Nrange).
Local Abbreviation BSLv_range := ((AR3 (@YF5k.BSLv_range)) Nrange Hidx).
Local Abbreviation WSKELP := (@YF5k.WSKELP imgk).
Local Abbreviation WSKEL1P := (@YF5k.WSKEL1P imgk).
Local Abbreviation WMAP := (@YF5k.WMAP).
Local Abbreviation WSKEL := (@YF5k.WSKEL imgk).
Local Abbreviation WSKEL1 := (@YF5k.WSKEL1 imgk).
Local Abbreviation win_sub := (@YF5k.win_sub).
Local Abbreviation AR9 f := (f idx res mb) (only parsing).
Local Abbreviation win_sub_sound := ((AR9 (@YF5k.win_sub_sound ly regs0)) Hidx Hres).
Local Abbreviation in_win := (@YF5k.in_win).
Local Abbreviation ARa f := (AR0 f LY IMG) (only parsing).
Local Abbreviation ARd f := (f Nrange Hidx Hres) (only parsing).
Local Abbreviation WSKELP_WINP := (ARd (ARa (AR1 (@YF5k.WSKELP_WINP _)))).
Local Abbreviation WSKEL1P_WIN1P := (ARd (ARa (AR1 (@YF5k.WSKEL1P_WIN1P _)))).
Local Abbreviation WMAP_WINM := (AR5 (ARa (AR1 (@YF5k.WMAP_WINM _)))).
Local Abbreviation WSKEL_WIN := (AR5 (ARa (AR1 (@YF5k.WSKEL_WIN _)))).
Local Abbreviation WSKEL1_WIN1 := (AR5 (ARa (AR1 (@YF5k.WSKEL1_WIN1 _)))).
Local Abbreviation windows_in := ((AR9 (@YF5k.windows_in ly regs0)) Hidx Hres).
Local Abbreviation windows_WINP := (ARd (ARa (AR1 (@YF5k.windows_WINP _)))).
Local Abbreviation windows_WIN1P := (ARd (ARa (AR1 (@YF5k.windows_WIN1P _)))).
Local Abbreviation windows_WIN := (AR5 (ARa (AR1 (@YF5k.windows_WIN _)))).
Local Abbreviation windows_WIN1 := (AR5 (ARa (AR1 (@YF5k.windows_WIN1 _)))).
Local Abbreviation frame_WIN1P := (ARd (ARa (AR1 (@YF5k.frame_WIN1P _)))).
Local Abbreviation frame_WIN1 := (AR5 (ARa (AR1 (@YF5k.frame_WIN1 _)))).
Local Abbreviation AR2 f := (f LY IMG Hsp Nrange Hidx Hres) (only parsing).
Local Abbreviation WINP_not_high := (AR2 (AR3 (@YF5k.WINP_not_high _))).
Local Abbreviation ARh f := (AR2 f Hmap) (only parsing).
Local Abbreviation WIN_not_high := (ARh (AR3 (@YF5k.WIN_not_high _))).
Variables (mat0 : list word).
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 (0x53104 + D_2c4)) mem0 (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis U1 : tfx_unwind_spec.
Local Abbreviation all_disjoint_of_forall := (@YF5k.all_disjoint_of_forall).
Local Abbreviation img_rw_writable := ((AR9 (AR1 (@YF5k.img_rw_writable))) Hidx).
Local Abbreviation ARg f := (f imgk W ly) (only parsing).
Local Abbreviation kept_of_frame := ((AR9 ((ARg (@YF5k.kept_of_frame)) regs0)) Hidx).
Local Abbreviation SKEL_TAIL := (@YF5k.SKEL_TAIL imgk).
Local Abbreviation blocks_facts := (@YF5k.blocks_facts _ imgk ly LY IMG).
Local Abbreviation off_T := (ARe (AR1 (@YF5k.off_T _))).
Local Abbreviation off_C := (ARe (AR1 (@YF5k.off_C _))).
Local Abbreviation off_Q := (ARe (AR1 (@YF5k.off_Q _))).
Local Abbreviation off_NB := (@YF5k.off_NB _ imgk ly LY IMG).
Local Abbreviation off_SB := (@YF5k.off_SB _ imgk ly LY IMG).
Local Abbreviation off_shadow := ((AR9 (AR1 (@YF5k.off_shadow))) Hidx).
Ltac off_by tac :=
first [ img_apply off_img_high; tac | img_apply off_T; tac | img_apply off_C; tac | img_apply off_Q; tac | img_apply off_NB; tac | img_apply off_SB; tac
| img_apply map_off_img; tac | img_apply off_shadow; tac
| unfold off_img; unfold TFX_IMG_LO; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; tac ].
Local Abbreviation DZONE := (@YF5k.DZONE imgk ly).
Variable DPOST : Z -> (word -> option byte) -> Prop.
Local Abbreviation AR6 f := (AR2 f Hmap Hmap_apart) (only parsing).
Local Abbreviation DZONE_disj := (AR6 (AR3 (@YF5k.DZONE_disj _))).
Local Abbreviation RFACTS := (AR1 (@YF5k.RFACTS)).
Local Abbreviation zone_lit := ((AR1 (@YF5k.zone_lit _)) LY IMG Hsp).
Local Abbreviation zone_irw := ((AR1 (@YF5k.zone_irw _)) LY IMG Hsp).
Local Abbreviation zone_T := ((AR1 (@YF5k.zone_T _)) idx res LY IMG Hsp Hidx Hres).
Local Abbreviation zone_C := ((AR1 (@YF5k.zone_C _)) idx res LY IMG Hsp Hidx Hres).
Local Abbreviation tail_ext_ok := (AR2 (AR0 (AR1 (@YF5k.tail_ext_ok _)))).
Local Abbreviation RFACTS_map := ((AR5 ((AR3 (@YF5k.RFACTS_map _)) LY IMG)) Hmap_apart).
Local Abbreviation AR4 f := (f imgk W ly regs0 mem0) (only parsing).
Local Abbreviation at_ST := (AR0 ((AR4 (@YF5k.at_ST _)) md0)).
Local Abbreviation memset_stretch := ((AR5 ((AR9 ((AR4 (@YF5k.memset_stretch _ _)) md0 n)) Hsp)) Hmap_apart mat0 DPOST).
Ltac clearM := try clear DPOST; try clear Hmap_apart; try clear Hmap.
Local Abbreviation AR7 f := (AR1 f mem0) (only parsing).
Local Abbreviation at_S := (AR0 (AR7 (@YF5k.at_S _))).
Local Abbreviation at_N := (AR0 (AR7 (@YF5k.at_N _))).
Local Abbreviation at_RETS := (@YF5k.at_RETS _ regs0 mem0 imgk).
Local Abbreviation pstable := (@YF5k.pstable).
Local Abbreviation stack_shaped := (@YF5k.stack_shaped).
Local Abbreviation window_present := (ARf (AR1 (@YF5k.window_present))).
Local Abbreviation stack_present_of := ((AR0 (AR1 (@YF5k.stack_present_of _))) LY Hsp Hidx).
Local Abbreviation mid_not_WIN1P := (AR2 (AR3 (@YF5k.mid_not_WIN1P _))).
Local Abbreviation mid_not_WIN1 := (ARh (AR3 (@YF5k.mid_not_WIN1 _))).
Local Abbreviation wins_ok := (@YF5k.wins_ok).
Local Abbreviation at_S_run_gen := ((AR0 (AR7 (@YF5k.at_S_run_gen _ _))) LY Hsp Hidx).
Local Abbreviation at_S_run_ecall_gen := ((AR0 (AR7 (@YF5k.at_S_run_ecall_gen _ _))) LY Hsp Hidx).
Local Abbreviation at_S_runP := (AR2 (AR0 (AR7 (@YF5k.at_S_runP _ _)))).
Local Abbreviation at_S_runM := (ARh (AR0 (AR7 (@YF5k.at_S_runM _ _)))).
Local Abbreviation at_S_run_ecallP := (AR2 (AR0 (AR7 (@YF5k.at_S_run_ecallP _ _)))).
Local Abbreviation at_S_run_ecallM := (ARh (AR0 (AR7 (@YF5k.at_S_run_ecallM _ _)))).
Local Abbreviation at_S_pin := (AR0 (AR7 (@YF5k.at_S_pin _))).
Local Abbreviation at_S_arm := (AR0 (AR7 (@YF5k.at_S_arm _))).
Local Abbreviation at_S_forget := (AR0 (AR7 (@YF5k.at_S_forget _))).
Local Abbreviation at_S_noconds := (AR0 (AR7 (@YF5k.at_S_noconds _))).
Local Abbreviation at_S_weaken := (AR0 (AR7 (@YF5k.at_S_weaken _))).
Local Abbreviation at_S_facts := (AR0 (AR7 (@YF5k.at_S_facts _))).
Local Abbreviation at_S_strengthen := (AR0 (AR7 (@YF5k.at_S_strengthen _))).
Local Abbreviation at_S_eq := (AR0 (AR7 (@YF5k.at_S_eq _))).
Local Abbreviation at_S_open := (AR0 (AR7 (@YF5k.at_S_open _))).
Local Abbreviation CSAVEDS := (@YF5k.CSAVEDS).
Local Abbreviation sv_denot_SOff0 := (@YF5k.sv_denot_SOff0).
Local Abbreviation at_S_ret := (ARd ((AR0 (AR7 (@YF5k.at_S_ret _))) Htp Hra Hsp)).
Local Abbreviation kept_of_frame2 := (ARf (AR1 (@YF5k.kept_of_frame2))).
Local Abbreviation at_N_cont := ((AR0 (AR7 (@YF5k.at_N_cont _ _))) LY Hsp Hidx).
Variables (B : asyms) (S : astate).
Hypothesis TS : TfxSyms B.
Hypothesis HTSD : ly_tsd ly = TFX_TSD.
Hypothesis HARm : ARm B ly S (aview tfxsegs (w_H W) mem0).
Hypothesis Hgp : getr regs0 3 = w64 (as_gp B).
Hypothesis Hidx_def : idx = Z.of_nat (length (st_sec_arr S)).
Hypothesis Hres_def : res = st_sec_reserved S.
Hypothesis Hj0 : val_mem tfxsegs (mrestrict (w_H W) mem0) (T + 2784) 8 j0.
Hypothesis Hj1 : val_mem tfxsegs (mrestrict (w_H W) mem0) (T + 2800) 8 j1.
Hypothesis Hj2 : val_mem tfxsegs (mrestrict (w_H W) mem0) (T + 2808) 8 j2.
Hypothesis Hj3 : val_mem tfxsegs (mrestrict (w_H W) mem0) (T + 2816) 8 j3.
Hypothesis Hj4 : val_mem tfxsegs (mrestrict (w_H W) mem0) (T + 2872) 8 j4.
Hypothesis Hj5 : val_mem tfxsegs (mrestrict (w_H W) mem0) (T + 2880) 8 j5.
Hypothesis Hj9 : val_mem tfxsegs (mrestrict (w_H W) mem0) (T + 2904) 8 j9.
Hypothesis Hj6 : val_mem tfxsegs (mrestrict (w_H W) mem0) (0xa6e18 + D_10c0) 8 j6.
Hypothesis Hj7 : val_mem tfxsegs (mrestrict (w_H W) mem0) (0xa6e20 + D_10c0) 8 j7.
Hypothesis Hj8 : val_mem tfxsegs (mrestrict (w_H W) mem0) BSLv 8 j8.
Hypothesis Hi1 : val_mem tfxsegs (mrestrict (w_H W) mem0) (TFX_INST + o_sec_stats) 8 i1.
Hypothesis Hi2 : val_mem tfxsegs (mrestrict (w_H W) mem0) (TFX_INST + o_sec_stats + 16) 8 i2.
Hypothesis Hi3 : val_mem tfxsegs (mrestrict (w_H W) mem0) (TFX_INST + o_sec_stats + 24) 8 i3.
Hypothesis HQT : qtight S.
Local Abbreviation vis_present := ((ARf (AR4 (@YF5t.vis_present _))) DPOST B S HARm).
Local Abbreviation in_thread_junk := (@YF5t.in_thread_junk ly B S).
Local Abbreviation in_sec_junk := (@YF5t.in_sec_junk ly B S).
Local Abbreviation in_as_junk := (@YF5t.in_as_junk ly B S).
Local Abbreviation junk_word := ((ARe (AR4 (@YF5t.junk_word _))) DPOST B S HARm).
Local Abbreviation cell_sym := ((ARg (@YF5t.cell_sym _)) mem0 B S TS HARm).
Local Abbreviation cell_lit := ((ARg (@YF5t.cell_lit _)) mem0 B S TS HARm).
Local Abbreviation cell_state := ((ARg (@YF5t.cell_state _)) mem0 B S HARm).
Local Abbreviation In_acells_sec := (@YF5t.In_acells_sec ly B S).
Local Abbreviation sec_vals := ((ARg (@YF5t.sec_vals _)) mem0 idx res B S TS HARm Hidx_def Hres_def).
Local Abbreviation unwinding_val := ((ARg (@YF5t.unwinding_val _)) mem0 B S HARm).
Local Abbreviation rw_writable := ((ARf (AR1 (@YF5t.rw_writable))) DPOST S).
Local Abbreviation val_mem_mod8 := ((ARf (AR4 (@YF5t.val_mem_mod8))) DPOST S).
Local Abbreviation chunk_lit := (AR0 (AR4 (@YF5t.chunk_lit))).
Local Abbreviation chunk_lit_at := (AR0 (AR4 (@YF5t.chunk_lit_at))).
Local Abbreviation chunk_atom := ((AR0 (AR4 (@YF5t.chunk_atom))) Hidx DPOST S).
Local Abbreviation ARb f := (f DPOST B S TS HTSD HARm Hidx_def Hres_def Hj0 Hj1 Hj2 Hj3 Hj4 Hj5 Hj9 Hj6 Hj7 Hj8 Hi1 Hi2 Hi3) (only parsing).
Local Abbreviation SREG0_ok := (ARb ((AR2 (AR0 (AR4 (@YF5u.SREG0_ok _)))) Hpres0)).
Local Abbreviation PAIRS_ok := ((AR2 (AR0 (AR4 (@YF5v.PAIRS_ok _)))) DPOST S).
Local Abbreviation FACTS_ok := ((ARd ((ARa (AR4 (@YF5v.FACTS_ok _))) Hn Hsp)) DPOST S).
Local Abbreviation SEED_ok := (ARb ((ARd ((ARa (AR4 (@YF5v.SEED_ok _ _))) Hn Htp Hsp)) Hpres0)).
Local Abbreviation PBUF := ((ARg (@YF5f.PBUF)) regs0 ch).
Local Abbreviation PBUF_stableP := (AR2 (AR9 ((ARg (@YF5f.PBUF_stableP _)) regs0 n ch))).
Local Abbreviation PBUF_stableM := (ARh (AR9 ((ARg (@YF5f.PBUF_stableM _)) regs0 n ch))).
Local Abbreviation seg0 := (ARb ((ARd ((ARa ((AR4 (@YF5f.seg0 _ _)) md0)) Hn Htp Hra4096 Hsp Hch)) Hpres0 mat0 U1)).
Local Abbreviation appregs := (@YF5l.appregs).
Local Abbreviation st_ok_appregs := (@YF5l.st_ok_appregs _ imgk).
Local Abbreviation at_S_app := (AR0 (AR7 (@YF5l.at_S_app _))).
Local Abbreviation WIN1N := (ARc (@YF5l.WIN1N)).
Local Abbreviation WINPN := (ARc (@YF5l.WINPN)).
Local Abbreviation WSKEL1N := (@YF5l.WSKEL1N imgk).
Local Abbreviation WIN1N_WINPN := ((AR3 (@YF5l.WIN1N_WINPN)) Hidx).
Local Abbreviation windows_WIN1N := (ARd (ARa (AR1 (@YF5l.windows_WIN1N _)))).
Local Abbreviation mid_not_WIN1N := (AR2 (AR3 (@YF5l.mid_not_WIN1N _))).
Local Abbreviation at_S_runN := (AR2 (AR0 (AR7 (@YF5l.at_S_runN _ _)))).
Local Abbreviation PBUF_stableN := (AR2 (AR9 ((ARg (@YF5l.PBUF_stableN _)) regs0 n ch))).
Local Abbreviation at_S_val := (AR0 (AR7 (@YF5l.at_S_val _))).
Local Abbreviation memset_stretchW := ((ARd ((AR4 (@YF5l.memset_stretchW _)) md0 n idx res Hsp)) mat0 DPOST S).
Local Abbreviation at_S_memset := ((ARd ((AR0 ((AR4 (@YF5l.at_S_memset _)) md0)) Hsp)) mat0 DPOST S).
Local Abbreviation WIN1T := (ARi (@YF5l.WIN1T)).
Local Abbreviation WIN1T_WIN := (AR5 (AR3 (@YF5l.WIN1T_WIN _))).
Local Abbreviation windows_WIN1T := (AR5 (ARa (AR1 (@YF5l.windows_WIN1T _)))).
Local Abbreviation WIN1T_WIN1_aux := (AR5 (AR3 (@YF5l.WIN1T_WIN1_aux _))).
Local Abbreviation mid_not_WIN1T := (ARh (AR3 (@YF5l.mid_not_WIN1T _))).
Local Abbreviation at_S_runT := (ARh (AR0 (AR7 (@YF5l.at_S_runT _ _)))).
Local Abbreviation at_S_run_ecallT := (ARh (AR0 (AR7 (@YF5l.at_S_run_ecallT _ _)))).
Local Abbreviation PBUFW := ((AR1 (@YF5l.PBUFW)) ch).
Local Abbreviation PBUFW_stableT := (ARh (AR9 ((ARc (@YF5l.PBUFW_stableT _)) ch))).
Local Abbreviation WIN1S := (ARi (@YF5m.WIN1S)).
Local Abbreviation WSKEL1S := (@YF5m.WSKEL1S imgk).
Local Abbreviation WIN1S_WIN1T := (ARi (@YF5m.WIN1S_WIN1T)).
Local Abbreviation WIN1S_WIN := (AR5 (AR3 (@YF5m.WIN1S_WIN _))).
Local Abbreviation windows_WIN1S := (AR5 (ARa (AR1 (@YF5m.windows_WIN1S _)))).
Local Abbreviation mid_not_WIN1S := (ARh (AR3 (@YF5m.mid_not_WIN1S _))).
Local Abbreviation at_S_runS := (ARh (AR0 (AR7 (@YF5m.at_S_runS _ _)))).
Local Abbreviation at_S_run_ecallS := (ARh (AR0 (AR7 (@YF5m.at_S_run_ecallS _ _)))).
Local Abbreviation brun := (@YF5m.brun).
Local Abbreviation run_ok := (@YF5m.run_ok n mb).
Local Abbreviation PS := ((ARc (@YF5m.PS)) ch mb).
Local Abbreviation runs_not_WIN1S := (AR6 (AR3 (@YF5m.runs_not_WIN1S _))).
Local Abbreviation runs_not_stack := ((AR5 ((AR3 (@YF5m.runs_not_stack _)) LY Hsp)) Hmap_apart).
Local Abbreviation PS_stable := (AR6 (AR9 ((ARc (@YF5m.PS_stable _)) ch))).
Local Abbreviation cut1 := (@YF5m.cut1).
Local Abbreviation cut := (@YF5m.cut).
Local Abbreviation cut_sound := ((AR5 (AR9 ((AR7 (@YF5m.cut_sound _)) n))) DPOST S).
Local Abbreviation cut_ok := ((AR9 (@YF5m.cut_ok ly regs0 mem0 n)) Hidx Hres DPOST S).
Local Abbreviation at_S_memsetS := ((AR5 ((AR0 ((AR4 (@YF5m.at_S_memsetS _ _)) md0)) LY Hsp)) Hmap_apart mat0 DPOST S).
Local Abbreviation skel_okb := (@YF5m.skel_okb imgk).
Local Abbreviation skel_cases := ((ARf (@YF5m.skel_cases imgk)) Hres S Hidx_def Hres_def).
Local Abbreviation AR8 f := (f DPOST S Hidx_def Hres_def) (only parsing).
Local Abbreviation skel_apart := (AR8 (AR6 (AR0 (AR7 (@YF5m.skel_apart _))))).
Local Abbreviation skel_u64 := (AR8 (ARh (AR0 (AR7 (@YF5m.skel_u64 _))))).
Local Abbreviation memset_ext_of_skel := (AR8 (AR6 (AR0 (AR7 (@YF5m.memset_ext_of_skel _))))).
Local Abbreviation memset_u64_of_skel := (AR8 (ARh (AR0 (AR7 (@YF5m.memset_u64_of_skel _))))).
Local Abbreviation WIN1R := ((ARc (@YF5m.WIN1R)) mb).
Local Abbreviation WSKEL1R := (@YF5m.WSKEL1R imgk).
Local Abbreviation WIN1R_WIN1S := (ARi (@YF5m.WIN1R_WIN1S)).
Local Abbreviation WIN1R_WIN := (AR5 (AR3 (@YF5m.WIN1R_WIN _))).
Local Abbreviation windows_WIN1R := (AR5 (ARa (AR1 (@YF5m.windows_WIN1R _)))).
Local Abbreviation mid_not_WIN1R := (ARh (AR3 (@YF5m.mid_not_WIN1R _))).
Local Abbreviation at_S_runR := (ARh (AR0 (AR7 (@YF5m.at_S_runR _ _)))).
Local Abbreviation at_S_run_ecallR := (ARh (AR0 (AR7 (@YF5m.at_S_run_ecallR _ _)))).
Local Abbreviation PSR := ((ARc (@YF5m.PSR)) ch mb).
Local Abbreviation rstable := ((ARc (@YF5m.rstable)) mb).
Local Abbreviation rstable_true := ((ARc (@YF5m.rstable_true)) mb).
Local Abbreviation PSR_stable := (AR6 (AR9 ((ARc (@YF5m.PSR_stable _)) ch))).
Local Abbreviation QSP := (@YF5m.QSP imgk ly idx).
Local Abbreviation QS_not_WIN1R := (AR6 (AR3 (@YF5m.QS_not_WIN1R _))).
Local Abbreviation QSP_rstable := (AR6 (AR3 (@YF5m.QSP_rstable _))).
Local Abbreviation at_S_memsetSR := ((AR5 ((AR0 ((AR4 (@YF5m.at_S_memsetSR _ _)) md0)) LY Hsp)) Hmap_apart mat0 DPOST S).
Local Abbreviation chunk_eqb := (@YF5m.chunk_eqb imgk).
Local Abbreviation chunk_eqb_eq := ((ARf (@YF5m.chunk_eqb_eq imgk)) Hres S Hidx_def Hres_def).
Local Abbreviation subregionb := (@YF5m.subregionb imgk).
Local Abbreviation subregionb_sound := (AR8 ((ARf (AR7 (@YF5m.subregionb_sound))) Hres)).
Local Abbreviation submemb := (@YF5m.submemb imgk).
Local Abbreviation submemb_sound := (AR8 ((ARf (AR7 (@YF5m.submemb_sound))) Hres)).
Local Abbreviation at_S_submem := (AR8 ((AR0 (AR7 (@YF5m.at_S_submem _))) Hidx Hres)).
Local Abbreviation at_S_addreg := (AR0 (AR7 (@YF5m.at_S_addreg _))).
Local Abbreviation PSR_runs := (AR0 (AR7 (@YF5i.PSR_runs _))).
Local Abbreviation place_WIN := (ARi (@YF5i.place_WIN)).
Local Abbreviation SH0 := (@YF5i.SH0 n mb).
Local Abbreviation SH1 := (@YF5i.SH1 n mb).
Local Abbreviation SH2 := (@YF5i.SH2 n mb).
Local Abbreviation SH_ok := (AR5 (AR3 (@YF5i.SH_ok _))).
Local Abbreviation segG1 := (AR8 ((AR6 (AR0 ((AR4 (@YF5i.segG1 _ _)) md0))) mat0)).
Local Abbreviation RX_stableS := (ARi (@YF5j.RX_stableS)).
Local Abbreviation rstable_and := ((ARc (@YF5j.rstable_and)) mb).
Local Abbreviation pstable_and := (@YF5j.pstable_and).
Local Abbreviation PSR_stableS' := (AR6 (AR9 ((ARc (@YF5j.PSR_stableS' _)) ch))).
Local Abbreviation pairwise_disjoint_map := (@YF5j.pairwise_disjoint_map).
Local Abbreviation at_S_setchunks := (AR0 (AR7 (@YF5j.at_S_setchunks _))).
Local Abbreviation chunk_ok_CVal_eqv := (@YF5j.chunk_ok_CVal_eqv imgk).
Local Abbreviation RES2T_ne := ((AR0 (AR1 (@YF5j.RES2T_ne))) Hidx Hres).
Local Abbreviation RES2T_eq := ((AR0 (AR1 (@YF5j.RES2T_eq))) Hidx Hres).
Local Abbreviation sv_denot_eq_of_U := (AR0 (AR1 (@YF5j.sv_denot_eq_of_U))).
Local Abbreviation skel_apart_QS := (AR8 (AR6 (AR0 (AR7 (@YF5j.skel_apart_QS _))))).
Local Abbreviation QSPX := (@YF5j.QSPX imgk ly idx).
Local Abbreviation segNE := (AR8 (AR6 (AR0 (AR7 (@YF5j.segNE _ _))))).
Local Abbreviation segEQa := (AR6 (AR0 (AR7 (@YF5j.segEQa _ _)))).
Local Abbreviation zev_SAlu := (@YF5j.zev_SAlu).
Local Abbreviation zev_SLit := (@YF5j.zev_SLit).
Local Abbreviation zev_SOff := (@YF5j.zev_SOff).
Local Abbreviation segJ2 := (AR8 (AR6 (AR0 (AR7 (@YF5j.segJ2 _ _))))).
Local Abbreviation segJ := (AR8 (AR6 (AR0 (AR7 (@YF5j.segJ _ _))))).
Local Abbreviation QR := (@YF5n.QR ly res).
Local Abbreviation segT1 := ((AR5 ((ARa (AR7 (@YF5n.segT1 _ _))) Hn Hsp)) Hmap_apart).
Local Abbreviation DX := (AR1 (@YF5n.DX)).
Local Abbreviation PD := (@YF5n.PD imgk ly mem0 DPOST).
Local Abbreviation PD_rstable := ((AR6 (AR9 ((AR7 (@YF5n.PD_rstable _)) n))) DPOST).
Local Abbreviation PD_stableT := ((AR6 (AR9 ((AR7 (@YF5n.PD_stableT _)) n))) DPOST).
Local Abbreviation PSR_stableS := (AR6 (AR9 ((ARc (@YF5n.PSR_stableS _)) ch))).
Local Abbreviation PD_stableS := ((AR6 (AR9 ((AR7 (@YF5n.PD_stableS _)) n))) DPOST).
Local Abbreviation PDX := (@YF5n.PDX imgk ly mem0 DPOST).
Local Abbreviation PDX_rstable := ((AR6 (AR9 ((AR7 (@YF5n.PDX_rstable _)) n))) DPOST).
Local Abbreviation PDX_stableT := ((AR6 (AR9 ((AR7 (@YF5n.PDX_stableT _)) n))) DPOST).
Local Abbreviation PDX_stableS := ((AR6 (AR9 ((AR7 (@YF5n.PDX_stableS _)) n))) DPOST).
Local Abbreviation dx_okb := (@YF5n.dx_okb imgk).
Local Abbreviation skel_apart_DX := (AR8 (AR6 (AR0 (AR7 (@YF5n.skel_apart_DX _))))).
Local Abbreviation skel_apart_stk := ((AR6 (AR0 (AR1 (@YF5n.skel_apart_stk _)))) S Hidx_def Hres_def).
Local Abbreviation at_S_depot := (AR8 (AR6 (AR0 (AR4 (@YF5n.at_S_depot _ _))))).
Local Abbreviation SH3 := (@YF5n.SH3 n mb).
Local Abbreviation SH4 := (@YF5n.SH4 n mb).
Local Abbreviation shadow_marks := (AR5 (AR3 (@YF5n.shadow_marks _))).
Local Abbreviation SH34_ok := (AR5 (AR3 (@YF5n.SH34_ok _))).
Local Abbreviation segT2b := (AR8 ((AR5 ((ARa ((AR4 (@YF5n.segT2b _ _)) md0)) Hn Hsp)) Hmap_apart mat0)).
Local Abbreviation segT2 := (AR8 ((AR5 ((ARa ((AR4 (@YF5n.segT2 _ _)) md0)) Hn Hsp)) Hmap_apart mat0)).
Local Abbreviation SH5 := (@YF5o.SH5 n mb).
Local Abbreviation SH6 := (@YF5o.SH6 n mb).
Local Abbreviation user_marks := (AR5 (AR3 (@YF5o.user_marks _))).
Local Abbreviation SH56_ok := (AR5 (AR3 (@YF5o.SH56_ok _))).
Local Abbreviation segU1 := (AR8 ((AR6 (AR0 ((AR4 (@YF5o.segU1 _ _)) md0))) mat0)).
Local Abbreviation SH6_of_cut := (AR5 (AR3 (@YF5o.SH6_of_cut _))).
Local Abbreviation segUe := (AR8 ((AR5 ((ARa ((AR4 (@YF5o.segUe _ _)) md0)) Hn Hsp)) Hmap_apart mat0)).
Local Abbreviation PT := ((ARc (@YF5o.PT)) ch mb).
Local Abbreviation run_okT := (@YF5o.run_okT n mb).
Local Abbreviation SH5o := (@YF5o.SH5o n mb).
Local Abbreviation SH6o := (@YF5o.SH6o n mb).
Local Abbreviation SH56o_ok := (AR5 (AR3 (@YF5o.SH56o_ok _))).
Local Abbreviation PT_stableT := (AR6 (AR9 ((ARc (@YF5o.PT_stableT _)) ch))).
Local Abbreviation segUo := (AR8 ((AR5 ((ARa ((AR4 (@YF5o.segUo _ _)) md0)) Hn Hsp)) Hmap_apart mat0)).
Local Abbreviation SHLO := (@YF5q.SHLO).
Local Abbreviation SHHI := (@YF5q.SHHI n).
Local Abbreviation SH_hull := (@YF5q.SH_hull ly regs0 n res Nrange S).
Local Abbreviation lit_m1 := (@YF5q.lit_m1).
Local Abbreviation lit_enomem := (@YF5q.lit_enomem).
Local Abbreviation nores34 := (@YF5q.nores34).
Local Abbreviation core34 := (@YF5q.core34).
Local Abbreviation pru_MS := (@YF5q.pru_MS ly regs0 n res Nrange S).
Local Abbreviation grant_anon_shape := (@YF5q.grant_anon_shape).
Local Abbreviation Hcut_out := (@YF5q.Hcut_out).
Local Abbreviation slackS := ((ARg (@YF5q.slackS _)) mem0 md0 B S HARm HQT).
Local Abbreviation S_N_facts := (@YF5q.S_N_facts imgk).
Local Abbreviation S_N_ext64 := ((AR2 (AR0 (AR1 (@YF5q.S_N_ext64 _)))) S).
Local Abbreviation S_N_win64 := ((AR2 (AR0 (AR1 (@YF5q.S_N_win64 _)))) S).
Local Abbreviation nodeS := ((AR2 (AR0 ((AR4 (@YF5q.nodeS _ _)) md0))) B S HARm HQT).
Local Abbreviation S_VG := (@YF5r.S_VG imgk).
Local Abbreviation TQ := (@YF5r.TQ).
Local Abbreviation S_V_facts := (@YF5r.S_V_facts imgk).
Local Abbreviation ZQF := (@YF5r.ZQF imgk ly res).
Local Abbreviation ZQ := (@YF5r.ZQ imgk ly idx res).
Local Abbreviation QR_facts := ((AR9 (AR1 (@YF5r.QR_facts _))) LY IMG Hidx Hres S Hidx_def).
Local Abbreviation ZQ_of_ZQF := (@YF5r.ZQ_of_ZQF imgk ly idx res).
Local Abbreviation QR_not_WIN1T := ((AR6 (AR3 (@YF5r.QR_not_WIN1T _))) S Hidx_def).
Local Abbreviation ZQ_stableT := ((AR6 (AR3 (@YF5r.ZQ_stableT _))) S Hidx_def).
Local Abbreviation ZQ_rstable := ((AR6 (AR3 (@YF5r.ZQ_rstable _))) S Hidx_def).
Local Abbreviation ZQ_stableD := ((AR9 (AR1 (@YF5r.ZQ_stableD _))) LY IMG Hsp Hidx Hres S Hidx_def).
Local Abbreviation skel_apart_Q := ((AR6 (AR0 (AR1 (@YF5r.skel_apart_Q _)))) S Hidx_def Hres_def).
Local Abbreviation TQ_val := ((ARa (AR1 (@YF5r.TQ_val _))) Hidx Hres S Hidx_def).
Local Abbreviation nores50 := (@YF5r.nores50).
Local Abbreviation core50 := (@YF5r.core50).
Local Abbreviation pru17 := (@YF5r.pru17).
Local Abbreviation grant_piece_shape := (@YF5r.grant_piece_shape).
Local Abbreviation nodeV := (AR8 (AR6 (AR0 ((AR7 (@YF5r.nodeV _ _)) md0)))).
Local Abbreviation RZF := (@YF5r.RZF imgk ly res).
Local Abbreviation RZ := (@YF5r.RZ imgk ly idx res).
Local Abbreviation ZQF_rstable := ((AR6 (AR3 (@YF5r.ZQF_rstable _))) S Hidx_def).
Local Abbreviation segV := (AR8 (AR6 (AR0 (AR7 (@YF5r.segV _ _))))).
Local Abbreviation DCELLS := (@YF60.DCELLS imgk W mem0).
Local Abbreviation PZ := ((ARc (@YF60.PZ)) ch mb).
Local Abbreviation PZ_stable := (AR6 (AR9 ((ARc (@YF60.PZ_stable _)) ch))).
Local Abbreviation img_vis := (@YF60.img_vis imgk).
Local Abbreviation in_dimg := (@YF60.in_dimg imgk).
Local Abbreviation in_dimg_facts := ((ARh (AR3 (@YF60.in_dimg_facts _))) S).
Local Abbreviation val_mem_xfer_img := ((ARh (AR9 ((AR4 (@YF60.val_mem_xfer_img _)) n))) S).
Local Abbreviation dnewb := (@YF60.dnewb).
Local Abbreviation dnewb_sound := ((ARh (AR0 (AR1 (@YF60.dnewb_sound _)))) S).
Local Abbreviation pat_word := ((ARf (AR4 (@YF60.pat_word))) DPOST S).
Local Abbreviation D_1_ok := ((ARh (AR0 (AR4 (@YF60.D_1_ok _ _)))) DPOST B S TS HARm Hidx_def).
Local Abbreviation land15_lor240 := (@YF60.land15_lor240).
Local Abbreviation land15_lorc := (@YF60.land15_lorc).
Local Abbreviation at_S_tighten := (AR0 (AR7 (@YF60.at_S_tighten _))).
Local Abbreviation addzero_region_ok := ((AR1 (@YF60.addzero_region_ok)) res S).
Local Abbreviation addzero_regions_wf := (@YF60.addzero_regions_wf).
Local Abbreviation addzero_all_disjoint := (@YF60.addzero_all_disjoint).
Local Abbreviation addzero_pairwise := (@YF60.addzero_pairwise).
Local Abbreviation at_S_addzero := ((AR0 (AR7 (@YF60.at_S_addzero _))) S).
Local Abbreviation hexfact_ok := ((ARa (AR1 (@YF60.hexfact_ok _))) Hidx Hres S Hidx_def).
Local Abbreviation segD1_6 := ((AR6 (AR0 (AR7 (@YF60.segD1_6 _ _)))) S).
Local Abbreviation segD1_7 := ((AR6 (AR0 (AR7 (@YF60.segD1_7 _ _)))) S).
Local Abbreviation segD1_8 := ((AR6 (AR0 (AR7 (@YF60.segD1_8 _ _)))) S).
Local Abbreviation segD1_12 := (AR6 (AR0 (AR7 (@YF60.segD1_12 _ _)))).
Local Abbreviation dia_side := (@YF60.dia_side imgk).
Local Abbreviation diamond := (AR6 (AR0 (AR7 (@YF60.diamond _ _)))).
Local Abbreviation digits_6 := ((AR6 (AR0 (AR7 (@YF60.digits_6 _ _)))) S).
Local Abbreviation digits_7 := ((AR6 (AR0 (AR7 (@YF60.digits_7 _ _)))) S).
Local Abbreviation digits_8 := ((AR6 (AR0 (AR7 (@YF60.digits_8 _ _)))) S).
Local Abbreviation digits_12 := ((AR6 (AR0 (AR7 (@YF60.digits_12 _ _)))) S).
Local Abbreviation segEND_6 := (AR6 (AR0 (AR7 (@YF60.segEND_6 _ _)))).
Local Abbreviation segEND_7 := (AR6 (AR0 (AR7 (@YF60.segEND_7 _ _)))).
Local Abbreviation segEND_8 := (AR6 (AR0 (AR7 (@YF60.segEND_8 _ _)))).
Local Abbreviation segEND_12 := (AR6 (AR0 (AR7 (@YF60.segEND_12 _ _)))).
Local Abbreviation dieV := ((AR6 (AR0 (AR4 (@YF60.dieV _ _)))) DPOST B S TS HARm Hidx_def).
Local Ltac addr_tac :=
cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi];
rewrite ?EaT, ?EaC, ?EaTOP, ?EaSB, ?EaQ, ?EaMAP, ?EaQS, ?EaBSL, ?EaSM, ?EaPB, ?E2; ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, w64, ly_bot, kStackSpan, t_unwinding, t_cache, t_stats, TFX_IMG_END, UNW_STK, BST_SIZE, ASTACK, IFRAME, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *;
rewrite ?unsigned_lit_small by zlia; zlia.
Local Ltac denot_tac :=
cbn [sv_denot]; rewrite ?EaT, ?EaC, ?EaTOP, ?EaSB, ?EaQ, ?EaMAP, ?E2; unfold w64, ly_bot, kStackSpan in *;
first [ rewrite Z.add_0_r, Z_to_bv_bv_unsigned; img_refl
| rewrite Zbv_add_unsigned; f_equal; zlia
| rewrite unsigned_lit_small by zlia; f_equal; zlia
| img_refl ].
Local Ltac clearP := try clear Hmap_apart; try clear Hmap.
Local Ltac s_station HR ss' :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let H2 := fresh "HR" in
pose proof (at_S_eq Wx md X P ss ss' W' c' HR ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))) as H2; clear HR; rename H2 into HR end.
Local Ltac s_runP HR tbl tblok stop ss' HX HP :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let st := img_ev (snd (sym_run_toN_sh tfxsegs tbl FUEL stop ss)) in
eapply SRr_bind;
[ img_try (eapply (at_S_runP Wx tbl tblok stop md X P ss ss' st W' c' HR);
[ (img_case; vm_compute); img_refl | img_exact I | img_exact HX | (img_case; vm_compute); img_refl | img_exact HP | (img_case; vm_compute); img_refl ])
| img_try (clear HR; let W2 := fresh "W" in let c2 := fresh "c" in intros W2 c2 _ HR) ] end.
Local Ltac s_runM HR tbl tblok stop ss' HX HP :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let st := img_ev (snd (sym_run_toN_sh tfxsegs tbl FUEL stop ss)) in
eapply SRr_bind;
[ img_try (eapply (at_S_runM Wx tbl tblok stop md X P ss ss' st W' c' HR);
[ (img_case; vm_compute); img_refl | img_exact I | img_exact HX | (img_case; vm_compute); img_refl | img_exact HP | (img_case; vm_compute); img_refl ])
| img_try (clear HR; let W2 := fresh "W" in let c2 := fresh "c" in intros W2 c2 _ HR) ] end.
Local Ltac s_ecallP HR tbl tblok ss' HX HP :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
eapply (at_S_run_ecallP Wx tbl tblok 0x7ffffff0 md X P ss ss' W' c' HR);
[ img_try ((img_case; vm_compute); img_refl) | img_refl | img_try (img_exact HX) | img_try ((img_case; vm_compute); img_refl) | img_try (img_exact HP) | img_try ((img_case; vm_compute); img_refl) ] end.
Local Ltac s_ecallM HR tbl tblok ss' HX HP :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
eapply (at_S_run_ecallM Wx tbl tblok 0x7ffffff0 md X P ss ss' W' c' HR);
[ img_try ((img_case; vm_compute); img_refl) | img_refl | img_try (img_exact HX) | img_try ((img_case; vm_compute); img_refl) | img_try (img_exact HP) | img_try ((img_case; vm_compute); img_refl) ] end.
Local Ltac unfold_atoms := unfold aT, aC, aSB, aTOP, aLEN, aJ0, aR8, aQ, aRES, aNCH, aMS, aMAP, aEND, aSHB, aTL, aQS, aBSL, aJ4, aJ5, aJ6, aJ7, aJ8, aJ9, aI1, aI2, aI3, aSM, aUE, aND, aRL, aN8DS, aPBS.
Local Ltac pin_zevS := img_apply U_eq_by_zev; [img_refl | img_refl |]; cbn [zev zalu_raw zmd_raw]; unfold rho_of; try unfold_atoms.
Local Ltac s_pin HR r e :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let t := img_ev (sr_get (ss_regs ss) r) in
let HU := fresh "HU" in
assert (HU : U E0 e = U E0 t);
[ | img_try (let H2 := fresh "HR" in
pose proof (at_S_pin Wx md X P ss W' c' r e HR ltac:(intros XX; discriminate XX) ltac:((try img_inst; img_case; vm_compute); img_refl) ltac:((try img_inst; img_case; vm_compute); img_refl) ltac:(img_exact HU)) as H2;
clear HU HR; rename H2 into HR) ] end.
Local Ltac s_arm HR cnd tk a b :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let HB := fresh "HB" in
assert (HB : branch_taken cnd (sv_denot E0 a) (sv_denot E0 b) = tk);
[ | img_try (let H2 := fresh "HR" in
pose proof (at_S_arm Wx md X P ss W' c' cnd tk a b HR ltac:((try img_inst; img_case; vm_compute); img_refl) ltac:((try img_inst; img_case; vm_compute); img_refl) HB) as H2;
clear HB HR; rename H2 into HR) ] end.
Local Ltac s_forget HR k clob :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let H2 := fresh "HR" in
pose proof (at_S_forget Wx md X P ss W' c' k clob HR ltac:(img_try (unfold sHAV; (img_case; cbv); zlia)) ltac:(img_eqrefl)
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))) as H2;
clear HR; rename H2 into HR end.
Local Ltac s_noconds HR :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let H2 := fresh "HR" in pose proof (at_S_noconds Wx md X P ss W' c' HR) as H2; clear HR; rename H2 into HR end.
Local Ltac arm_zevS := rewrite ?branch_geu_U, ?branch_ltu_U, ?branch_eq_U, ?branch_ne_U;
rewrite !U_zev by (img_try ((img_case; vm_compute); img_refl)); cbn [zev zalu_raw zmd_raw]; unfold rho_of; try unfold_atoms.
Local Ltac U_zevS := rewrite U_zev by img_refl; cbn [zev zalu_raw zmd_raw]; unfold rho_of; try unfold_atoms.
Local Ltac s_armR HR cnd tk r1 r2 :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let a := img_ev (sr_get (ss_regs ss) r1) in
let b := img_ev (sr_get (ss_regs ss) r2) in
s_arm HR cnd tk a b end.
Local Ltac ladder_arith Z :=
let MF := fresh "MF" in let SF := fresh "SF" in let NRx := fresh "NRx" in
pose proof map_facts as MF; pose proof size_facts as SF; pose proof Nrange as NRx;
arm_zevS; rewrite ?EaSHB, ?EaMAP, ?EaEND, ?EaTL, ?EaUE, ?EaRL, ?EaN8D, ?EaND, ?EaMS; unfold w64;
clear - Z MF SF NRx;
destruct MF as (M1x & M2x & M3x & K4x & U5x & E6x & UE7x & E8x & UE9x & MTx & MUx & SM1x & SM2x & SM3x & PBx & SMAx);
destruct SF as (Z1x & Z2x & Z3x & Z4x & Z5x & Z6x & Z7x & Z8x & Z9x & Z10x & Z11x & Z12x & Z13x & Z14x);
unfold YF5k.SHBv, YF5k.Kv, YF5k.Uv, YF5k.SMv, YF5k.PBv, MALLOC_MAX,
kLowShadowBeg, kHighShadowEnd, TFX_IMG_END in *;
rewrite !unsigned_lit_small by zlia; zcanon_simp;
first [ rewrite (proj2 (Z.ltb_ge _ _)) by zlia | rewrite (proj2 (Z.ltb_lt _ _)) by zlia ]; img_refl.
Local Ltac s_join HR k clob SJ := s_forget HR k clob; s_noconds HR; s_station HR SJ; img_apply SRr_ret; img_exact HR.
Local Ltac s_ladder RUN HR tbl tblok STOP Sl Slo Sh Sh2 Sh3 Shi SJ k clob HX HP :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let HQ := fresh "HQ" in
assert (HQ : SRr tfxsegs W' c' (at_S Wx md X P SJ));
[ img_try (let MZ := fresh "MZ" in pose proof map_zoneN as MZ; destruct MZ as [ZLO|ZHI];
[ s_armR HR BC_GEU true (14%bv : bv 5) (10%bv : bv 5); [ladder_arith ZLO|];
RUN HR tbl tblok (0x5452c + D_2c4) Sl HX HP;
s_armR HR BC_GEU true (14%bv : bv 5) (11%bv : bv 5); [ladder_arith ZLO|];
RUN HR tbl tblok STOP Slo HX HP;
s_join HR k clob SJ
| s_armR HR BC_GEU false (14%bv : bv 5) (10%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok (0x54384 + D_2c4) Sh HX HP;
s_armR HR BC_LTU true (7%bv : bv 5) (10%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok (0x5452c + D_2c4) Sh2 HX HP;
s_armR HR BC_GEU false (14%bv : bv 5) (11%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok (0x5456c + D_2c4) Sh3 HX HP;
s_armR HR BC_GEU false (5%bv : bv 5) (11%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok STOP Shi HX HP;
s_join HR k clob SJ ])
| img_try (clear HR; eapply SRr_bind; [img_exact HQ | clear HQ; let W2 := fresh "WL" in let c2 := fresh "cL" in intros W2 c2 _ HR ]) ]
end.
Local Ltac s_ladderW RUN HR tbl tblok STOP Sl Slo Sh Sh2 Sh3a Sh3 Shi SJ k clob HX HP :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let HQ := fresh "HQ" in
assert (HQ : SRr tfxsegs W' c' (at_S Wx md X P SJ));
[ img_try (let MZ := fresh "MZ" in pose proof map_zoneN as MZ; destruct MZ as [ZLO|ZHI];
[ s_armR HR BC_GEU true (14%bv : bv 5) (10%bv : bv 5); [ladder_arith ZLO|];
RUN HR tbl tblok (0x5452c + D_2c4) Sl HX HP;
s_armR HR BC_GEU true (14%bv : bv 5) (11%bv : bv 5); [ladder_arith ZLO|];
RUN HR tbl tblok STOP Slo HX HP;
s_join HR k clob SJ
| s_armR HR BC_GEU false (14%bv : bv 5) (10%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok (0x54384 + D_2c4) Sh HX HP;
s_armR HR BC_LTU true (7%bv : bv 5) (10%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok (0x5452c + D_2c4) Sh2 HX HP;
s_armR HR BC_GEU false (14%bv : bv 5) (11%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok (0x54568 + D_2c4) Sh3a HX HP;
s_armR HR BC_LTU false (6%bv : bv 5) (11%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok (0x5456c + D_2c4) Sh3 HX HP;
s_armR HR BC_GEU false (5%bv : bv 5) (11%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok STOP Shi HX HP;
s_join HR k clob SJ ])
| img_try (clear HR; eapply SRr_bind; [img_exact HQ | clear HQ; let W2 := fresh "WL" in let c2 := fresh "cL" in intros W2 c2 _ HR ]) ]
end.
Local Ltac s_ladderM RUN HR tbl tblok STOP Slo Sh Sh2 Shi SJ k clob HX HP :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let HQ := fresh "HQ" in
assert (HQ : SRr tfxsegs W' c' (at_S Wx md X P SJ));
[ img_try (let MZ := fresh "MZ" in pose proof map_zoneN as MZ; destruct MZ as [ZLO|ZHI];
[ s_armR HR BC_GEU true (12%bv : bv 5) (22%bv : bv 5); [ladder_arith ZLO|];
RUN HR tbl tblok STOP Slo HX HP;
s_join HR k clob SJ
| s_armR HR BC_GEU false (12%bv : bv 5) (22%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok (0x31e3c + D_150) Sh HX HP;
s_armR HR BC_LTU false (17%bv : bv 5) (22%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok (0x31e40 + D_150) Sh2 HX HP;
s_armR HR BC_GEU false (16%bv : bv 5) (22%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok STOP Shi HX HP;
s_join HR k clob SJ ])
| img_try (clear HR; eapply SRr_bind; [img_exact HQ | clear HQ; let W2 := fresh "WL" in let c2 := fresh "cL" in intros W2 c2 _ HR ]) ]
end.
Variables (Wy : world tfxsegs) (md1 : Model).
Variable RX : (word -> option byte) -> Prop.
Hypothesis RXs : rstable RX.
Hypothesis RXt : pstable WIN1T RX.
Definition BCELLS : Prop :=
val_mem tfxsegs (mrestrict (w_H W) mem0) (0xa2e10 + D_10f0) 8 (0x5fd190 + D_10c0) /\ val_mem tfxsegs (mrestrict (w_H W) mem0) (0x5fd410 + D_10c0) 8 4096 /\
val_mem tfxsegs (mrestrict (w_H W) mem0) 0x2150c 2 0xff04 /\ val_mem tfxsegs (mrestrict (w_H W) mem0) 0x214a8 4 (0x6f924 + D_104c) /\
val_mem tfxsegs (mrestrict (w_H W) mem0) (0x13bddc + D_10c0) 1 1 /\ val_mem tfxsegs (mrestrict (w_H W) mem0) (0x13bdc3 + D_10c0) 1 1.
Hypothesis HBC : BCELLS.
Local Ltac s_runS HR tbl tblok stop ss' HX HP :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let st := img_ev (snd (sym_run_toN_sh tfxsegs tbl FUEL stop ss)) in
eapply SRr_bind;
[ img_try (eapply (at_S_runS Wx tbl tblok stop md X P ss ss' st W' c' HR);
[ (img_case; vm_compute); img_refl | img_exact I | img_exact HX | (img_case; vm_compute); img_refl | img_exact HP | (img_case; vm_compute); img_refl ])
| img_try (clear HR; let W2 := fresh "W" in let c2 := fresh "c" in intros W2 c2 _ HR) ] end.
Local Ltac s_ecallS HR tbl tblok ss' HX HP :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
eapply (at_S_run_ecallS Wx tbl tblok 0x7ffffff0 md X P ss ss' W' c' HR);
[ img_try ((img_case; vm_compute); img_refl) | img_refl | img_try (img_exact HX) | img_try ((img_case; vm_compute); img_refl) | img_try (img_exact HP) | img_try ((img_case; vm_compute); img_refl) ] end.
Definition PGBv : Z := (SMv + 768 + 4095) / 4096 * 4096.
Definition PGEv : Z := PBv / 4096 * 4096.
Lemma big_marks : 18446744073709551615 <= N8D / 8 ->
PBv = SMv + 768 + N8D / 8 /\ SMv mod 512 = 0 /\ PGBv mod 4096 = 0 /\ PGEv mod 4096 = 0 /\
SMv + 768 < PGBv /\ PGBv < SMv + 768 + 4096 /\ PGEv <= PBv /\ PBv < PGEv + 4096 /\ PGBv + 4096 <= PGEv /\
kLowShadowBeg + TFX_IMG_END / 8 <= SMv /\ PBv <= SMv + MSv / 8 /\ SMv + MSv / 8 <= kHighShadowEnd /\ PBv <= SHBv + UEv / 8.
Proof.
intros HB. pose proof map_facts as (M1 & M2 & M3 & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & SM3 & PB & _). pose proof map_zoneN as MZ.
pose proof shadow_marks as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9). pose proof user_marks as (B1 & B2 & B3 & B4 & B5).
pose proof size_facts as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & _).
clear - HB M3 SM1 SM2 SM3 PB A2 A3 A5 A6 B1 Z4 Z8 MZ. unfold PGBv, PGEv.
pose proof (Z.div_mod (SMv + 768 + 4095) 4096 ltac:(img_try (zlia))) as D1. pose proof (Z.mod_pos_bound (SMv + 768 + 4095) 4096 ltac:(img_try (zlia))) as R1.
pose proof (Z.div_mod PBv 4096 ltac:(img_try (zlia))) as D2. pose proof (Z.mod_pos_bound PBv 4096 ltac:(img_try (zlia))) as R2.
pose proof SM3 as SM3'. apply Z.mod_divide in SM3' as [u Hu]; [|img_try (zlia)].
assert (P1 : PGBv mod 4096 = 0) by (img_try (unfold PGBv; img_apply Z_mod_mult)). assert (P2 : PGEv mod 4096 = 0) by (img_try (unfold PGEv; img_apply Z_mod_mult)).
unfold PGBv, PGEv in *. set (q1 := (SMv + 768 + 4095) / 4096) in *. set (q2 := PBv / 4096) in *.
assert (X1 : SMv + 768 < q1 * 4096 < SMv + 768 + 4096) by (img_try (clear - D1 R1 Hu MZ; zlia)).
assert (X2 : q2 * 4096 <= PBv < q2 * 4096 + 4096) by (img_try (clear - D2 R2 MZ; zlia)).
clear D1 R1 D2 R2 Hu. unfold kHighShadowBeg, kHighShadowEnd, MALLOC_MAX in *.
repeat split; first [assumption | zlia].
Qed.
Lemma sm_bounds : 2148217856 <= SMv /\ SMv + 9216 <= SMv + MSv / 8 <= 17594333495296.
Proof.
pose proof map_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _). pose proof map_zoneN as MZ. pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & _).
clear - SM1 SM2 Z8 MZ. unfold kHighShadowBeg, kHighShadowEnd, MALLOC_MAX in *.
pose proof (Z.div_mod MSv 8 ltac:(img_try (zlia))). pose proof (Z.mod_pos_bound MSv 8 ltac:(img_try (zlia))). zlia.
Qed.
Lemma U_SHBT : U E0 SHBT = SMv + 768.
Proof.
pose proof sm_bounds as SMB. clear - SMB.
unfold SHBT. rewrite U_SOff. unfold aSM. rewrite EaSM. unfold w64. rewrite unsigned_lit_small by zlia. img_apply zcanon_id. unfold M64. zlia.
Qed.
Lemma U_SHET : 18446744073709551615 <= N8D / 8 -> U E0 SHET = PBv.
Proof.
intros HB. pose proof sm_bounds as SMB. pose proof (big_marks HB) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13). clear - SMB C1 C11 HB.
unfold SHET. rewrite U_SOff. unfold aPBS. rewrite EaPB. unfold w64. rewrite unsigned_lit_small by zlia. rewrite Z.add_0_r. img_apply zcanon_id. unfold M64. zlia.
Qed.
Lemma U_PGBT : 18446744073709551615 <= N8D / 8 -> U E0 PGBT = PGBv.
Proof.
intros HB. pose proof sm_bounds as SMB. pose proof (big_marks HB) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13). clear - SMB C3 C5 C6 C11 HB.
unfold PGBT. rewrite U_zev by img_refl. cbn [zev zalu_raw]. unfold rho_of. unfold aSM. rewrite EaSM. unfold w64.
rewrite unsigned_lit_small by zlia. rewrite (zcanon_id (SMv + 4863)) by (img_try (unfold M64; zlia)).
img_change (zcanon 18446744073709547520) with (2 ^ 64 - 2 ^ 12). rewrite land_neg_pow2_u64 by zlia. img_change (2 ^ 12) with 4096.
pose proof (Z.div_mod (SMv + 768 + 4095) 4096 ltac:(img_try (zlia))) as D1. pose proof (Z.mod_pos_bound (SMv + 768 + 4095) 4096 ltac:(img_try (zlia))) as R1.
replace (SMv + 4863) with (SMv + 768 + 4095) by zlia. unfold PGBv in *. rewrite zcanon_id; unfold M64; zlia.
Qed.
Lemma U_PGET : 18446744073709551615 <= N8D / 8 -> U E0 PGET = PGEv.
Proof.
intros HB. pose proof sm_bounds as SMB. pose proof (big_marks HB) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13). clear - SMB C1 C4 C7 C8 C11 HB.
unfold PGET. rewrite U_zev by img_refl. cbn [zev zalu_raw]. unfold rho_of. unfold aPBS. rewrite EaPB. unfold w64.
rewrite unsigned_lit_small by zlia. rewrite Z.add_0_r. rewrite (zcanon_id PBv) by (img_try (unfold M64; zlia)).
img_change (zcanon 18446744073709547520) with (2 ^ 64 - 2 ^ 12). rewrite land_neg_pow2_u64 by zlia. img_change (2 ^ 12) with 4096.
pose proof (Z.div_mod PBv 4096 ltac:(img_try (zlia))) as D1. pose proof (Z.mod_pos_bound PBv 4096 ltac:(img_try (zlia))) as R1.
unfold PGEv in *. rewrite zcanon_id; unfold M64; zlia.
Qed.
Lemma U_SHB_X : U E0 SHB_X = SMv + 768.
Proof.
pose proof map_facts as (M1 & M2 & M3 & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _). pose proof map_zoneN as MZ. pose proof shadow_marks as (_ & _ & _ & _ & _ & _ & A7 & _).
pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & _). clear - M1 M2 M3 SM1 SM2 A7 Z8 MZ.
unfold SHB_X. rewrite U_zev by img_refl. cbn [zev zalu_raw]. unfold rho_of. rewrite EaSHB, EaMAP. unfold w64, YF5k.SHBv in *.
ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kHighShadowBeg, kHighShadowEnd, MALLOC_MAX in *. rewrite !unsigned_lit_small by zlia.
zcanon_simp. land_lits. rewrite Z.shiftr_div_pow2 by zlia. img_change (2 ^ 3) with 8.
apply Z.mod_divide in M3 as [u Hu]; [|img_try (zlia)]. rewrite Hu in *. replace (u * 4096 + 6144) with ((u * 512 + 768) * 8) by zlia. rewrite Z_div_mult by zlia.
rewrite A7. replace (u * 4096) with ((u * 512) * 8) by zlia. rewrite Z_div_mult by zlia. zcanon_simp. zlia.
Qed.
Lemma U_SHE_X : U E0 SHE_X = PBv.
Proof.
pose proof map_facts as (M1 & M2 & M3 & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _ & PB & _). pose proof map_zoneN as MZ. pose proof shadow_marks as (_ & _ & _ & _ & _ & _ & A7 & _).
pose proof size_facts as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & _). pose proof Nrange as NR. pose proof user_marks as (B1 & _). clear - M1 M2 M3 SM1 SM2 PB A7 Z4 Z5 Z8 NR B1 MZ.
unfold SHE_X. rewrite U_zev by img_refl. cbn [zev zalu_raw]. unfold rho_of. rewrite EaSHB, EaMAP, EaN8D. unfold w64, YF5k.SHBv in *.
ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kHighShadowBeg, kHighShadowEnd, MALLOC_MAX in *. rewrite !unsigned_lit_small by zlia.
zcanon_simp. land_lits. rewrite Z.shiftr_div_pow2 by zlia. img_change (2 ^ 3) with 8.
apply Z.mod_divide in M3 as [u Hu]; [|img_try (zlia)]. apply Z.mod_divide in Z5 as [p Hp]; [|img_try (zlia)]. rewrite Hu, Hp in *.
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
Definition in_bimg {imgk : img} (x : Z) : Prop :=
((0xa2e10 + D_10f0) <= x < (0xa2e18 + D_10f0)) \/ ((0x5fd190 + D_10c0) <= x < (0x5fd198 + D_10c0)) \/ ((0x5fd410 + D_10c0) <= x < (0x5fd418 + D_10c0)) \/ (0x2150c <= x < 0x2150e) \/ (0x214a8 <= x < 0x214ac) \/
((0xa21a0 + D_10f0) <= x < (0xa21b0 + D_10f0)) \/ ((0x13bcdc + D_10c0) <= x < (0x13bce0 + D_10c0)) \/ ((0x13bddc + D_10c0) <= x < (0x13bddd + D_10c0)) \/ ((0x13bdc3 + D_10c0) <= x < (0x13bdc4 + D_10c0)).
Lemma in_bimg_facts : forall x, in_bimg x -> 0 <= x < 2 ^ 64 /\ find_segment tfxsegs x 1 <> None /\ ~ X x.
Proof.
intros x R. unfold in_bimg in R. pose proof high_facts as (F1 & _ & _ & _ & _ & _ & _ & _ & F9 & _). pose proof map_facts as (M1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & _). pose proof map_zoneN as MZ.
destruct Hsp as (S1' & _). pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7). pose proof BSLv_range as HB. pose proof Hres as [HRS _]. pose proof Hidx as HI.
pose proof blocks_facts as (NBhi & SBhi & _).
split; [img_try (clear - R MZ; zlia)|]. split.
- assert (SEG : forall y, 0x10000 <= y < (0x5ff000 + D_1000) -> find_segment tfxsegs y 1 <> None).
{ clear. intros y Hy. img_concrete; cbv delta [tfxsegs tfx_loaded_segments]; cbv beta iota;
cbn -[Z_to_bv bv_unsigned Z.leb Z.ltb Z.add] in *;
repeat match goal with |- context [((?x <=? y) && (y + 1 <=? ?z))%bool] => destruct (Z.leb_spec x y); destruct (Z.leb_spec (y + 1) z); cbn [andb] end;
try discriminate; exfalso; zlia. }
img_apply SEG. clear - R MZ. zlia.
- intros HXx. destruct (HXsub x HXx) as [HW | [HQ | HD]].
+ clear - R HW F1 F9 M1 SM1 S1' T7 HB HI MZ. unfold WIN, WINT, WINI, WINM in HW.
unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighShadowBeg, QSv, ASTACK, t_unwinding, TFX_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex in *.
try unfold Qb in *. try unfold T in *. try unfold sp0 in *. zlia.
+ unfold QR in HQ. clear - R HQ F9 HRS HI MZ. unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg in *. try unfold Qb in *. zlia.
+ unfold DX, DZONE in HD. clear - R HD S1' T7 NBhi SBhi MZ. unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASTACK, DEP_STK in *. try unfold sp0 in *. zlia.
Qed.
Lemma val_mem_xfer_bimg : forall (m : word -> option byte) a (w : nat) v,
val_mem tfxsegs (mrestrict (w_H W) mem0) a w v ->
(forall x : word, ~ X (bv_unsigned x) -> m x = mem0 x) ->
(forall i, 0 <= i < Z.of_nat w -> in_bimg (a + i)) ->
val_mem tfxsegs (mrestrict (w_H Wy) m) a w v.
Proof.
intros m a w v HV MEQ Hin k Hk. rewrite <- (HV k Hk). destruct (in_bimg_facts (a + Z.of_nat k) (Hin (Z.of_nat k) ltac:(img_try (zlia)))) as (Ra & Fs & Nw).
unfold mbyte, mrestrict. rewrite (img_vis Wy _ Ra Fs), (img_vis W _ Ra Fs). rewrite MEQ; [img_refl|]. rewrite unsigned_lit_small by img_exact Ra. img_exact Nw.
Qed.
Lemma can_word : forall m, exists w, val_mem tfxsegs (mrestrict (w_H Wy) m) (0x5fd190 + D_10c0) 8 w /\ 0 <= w < 2 ^ 64.
Proof.
clearP. intros m. destruct can_bytes as [bs Hbs]. destruct (img_word (w_H Wy) m (0x5fd190 + D_10c0) bs Hbs) as [w Hw].
exists (w mod 2 ^ 64). split; [img_try (img_exact (val_mem_mod8 _ _ _ Hw)) | img_try (img_apply Z.mod_pos_bound; zlia)].
Qed.
Theorem B_R_ok : forall (W' : world tfxsegs) c, at_S Wy md1 X (PSR Wy SH4 (PDX Wy RX z)) T_R W' c -> at_S Wy md1 X (PSR Wy SH4 (PDX Wy RX z)) B_R W' c.
Proof.
intros W' c HR. pose proof HBC as (C1 & C2 & C3 & C4 & C5 & C6).
pose proof (cell_lit (0xa21a0 + D_10f0) 8 1 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))) as G1. pose proof (cell_lit (0x13bcdc + D_10c0) 4 0 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))) as G2.
pose proof (cell_lit (0xa21a8 + D_10f0) 8 (0x13bcdc + D_10c0) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))) as G3.
pose proof map_facts as (M1 & M2 & M3 & _). pose proof map_zoneN as MZ. pose proof size_facts as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & _). pose proof Nrange as NR.
s_arm HR BC_LTU false USH_LEN (SLit 18446744073709551615).
{ clear - M1 M2 M3 Z8 Z4 Z5 NR Hbig MZ. ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, MALLOC_MAX in *. arm_zevS. unfold USH_LEN. cbn [zev zalu_raw]. unfold_atoms. rewrite EaMAP, EaN8D. unfold w64.
rewrite !unsigned_lit_small by zlia. zcanon_simp. land_lits. rewrite !Z.shiftr_div_pow2 by zlia. img_change (2 ^ 3) with 8.
apply Z.mod_divide in M3 as [u Hu]; [|img_try (zlia)]. apply Z.mod_divide in Z5 as [p Hp]; [|img_try (zlia)]. rewrite Hu, Hp in *.
replace (u * 4096 + 6136 + (p * 8 + 0)) with ((u * 512 + 767 + p) * 8) by zlia. replace (u * 4096 + 6144) with ((u * 512 + 768) * 8) by zlia.
rewrite !Z_div_mult in * by zlia. zcanon_simp. img_apply Z.ltb_ge. zlia. }
destruct HR as (EW & ms & mat & E' & Ec & HE & HS & MEQ & PRS & HPm).
destruct (can_word (ms_mem ms)) as (wc & Hwc & Rwc).
set (E'' := havoc E' aCAN [w64 wc]).
assert (HE'' : env_agree sHAV E0 E'').
{ destruct HE as [HE1 HE2]. split; [| img_try (unfold E'', havoc; cbn [ed]; img_exact HE2)]. intros k Hk. unfold E''. rewrite ew_havoc_old by (img_try (unfold aCAN, sHAV in *; zlia)). img_exact (HE1 k Hk). }
assert (AG : env_agree aCAN E' E'') by (img_try (split; [img_try (intros k Hk; unfold E''; img_apply ew_havoc_old; img_exact Hk) | img_refl])).
lazymatch type of HS with st_ok _ _ ?ss0 _ =>
assert (HS'' : st_ok tfxsegs E'' ss0 (restrict (w_H Wy) ms)) by (img_try (img_exact (st_ok_agree tfxsegs aCAN E' E'' ss0 _ HS AG ltac:((try img_inst; img_case; vm_compute); img_refl)))) end.
split; [img_try (img_exact EW)|]. exists ms, mat, E''. split; [img_try (img_exact Ec)|]. split; [img_try (img_exact HE'')|]. split; [| img_try (img_exact (conj MEQ (conj PRS HPm)))].
assert (X1 := val_mem_xfer_bimg (ms_mem ms) _ _ _ C1 MEQ ltac:(img_try (intros i Hi; unfold in_bimg; zlia))).
assert (X2 := val_mem_xfer_bimg (ms_mem ms) _ _ _ C2 MEQ ltac:(img_try (intros i Hi; unfold in_bimg; zlia))).
assert (X3 := val_mem_xfer_bimg (ms_mem ms) _ _ _ C3 MEQ ltac:(img_try (intros i Hi; unfold in_bimg; zlia))).
assert (X4 := val_mem_xfer_bimg (ms_mem ms) _ _ _ C4 MEQ ltac:(img_try (intros i Hi; unfold in_bimg; zlia))).
assert (X5 := val_mem_xfer_bimg (ms_mem ms) _ _ _ C5 MEQ ltac:(img_try (intros i Hi; unfold in_bimg; zlia))).
assert (X6 := val_mem_xfer_bimg (ms_mem ms) _ _ _ C6 MEQ ltac:(img_try (intros i Hi; unfold in_bimg; zlia))).
assert (Y1 := val_mem_xfer_bimg (ms_mem ms) _ _ _ G1 MEQ ltac:(img_try (intros i Hi; unfold in_bimg; zlia))).
assert (Y2 := val_mem_xfer_bimg (ms_mem ms) _ _ _ G2 MEQ ltac:(img_try (intros i Hi; unfold in_bimg; zlia))).
assert (Y3 := val_mem_xfer_bimg (ms_mem ms) _ _ _ G3 MEQ ltac:(img_try (intros i Hi; unfold in_bimg; zlia))).
Local Ltac raddB HS EE HEE RR lo hi :=
img_apply st_ok_add_region; [img_exact HS | (img_case; vm_compute); img_refl | |
img_apply all_disjoint_of_forall; intros r2 Hr2;
refine (dnewb_sound EE lo hi RR r2 HEE ltac:(img_eqrefl) ltac:(img_eqrefl) ltac:(img_eqrefl) ltac:(img_try (clear; zlia)) ltac:(img_try (clear; zlia)) ltac:(img_try (clear; zlia)) _);
lazymatch goal with |- dnewb _ _ _ = true =>
revert r2 Hr2; img_apply (proj1 (forallb_forall _ _)); (img_case; vm_compute); img_refl end ].
Local Ltac rlit RR XX :=
let hRR := lazymatch RR with ?f_ _ => f_ | _ => RR end in unfold hRR, lit8, lit4, lit1, region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict];
split; [img_try (clear; zlia)|]; split; [img_try (clear; zlia)|]; split; [img_try (intros o Ho; clear - Ho; zlia)|]; img_apply Forall_cons; [|img_try (img_apply Forall_nil)];
eapply chunk_ok_val; [img_refl | img_try (cbn; clear; zlia) | img_try (cbn; clear; zlia) | img_try (rewrite Z.add_0_l; img_exact XX)].
unfold B_R, BREG. cbn [fold_right].
assert (HS1 : st_ok tfxsegs E'' (addreg R_f2 B_0) (restrict (w_H Wy) ms)).
{ unfold addreg. raddB HS'' E'' HE'' R_f2 (0x13bdc3 + D_10c0) (0x13bdc4 + D_10c0). rlit R_f2 X6. }
assert (HS2 : st_ok tfxsegs E'' (addreg R_f1 (addreg R_f2 B_0)) (restrict (w_H Wy) ms)).
{ unfold addreg at 1. raddB HS1 E'' HE'' R_f1 (0x13bddc + D_10c0) (0x13bddd + D_10c0). rlit R_f1 X5. }
assert (HS3 : st_ok tfxsegs E'' (addreg R_g2 (addreg R_f1 (addreg R_f2 B_0))) (restrict (w_H Wy) ms)).
{ unfold addreg at 1. raddB HS2 E'' HE'' R_g2 (0x13bcdc + D_10c0) (0x13bce0 + D_10c0). rlit R_g2 Y2. }
assert (HS4 : st_ok tfxsegs E'' (addreg R_g3 (addreg R_g2 (addreg R_f1 (addreg R_f2 B_0)))) (restrict (w_H Wy) ms)).
{ unfold addreg at 1. raddB HS3 E'' HE'' R_g3 (0xa21a8 + D_10f0) (0xa21b0 + D_10f0). rlit R_g3 Y3. }
assert (HS5 : st_ok tfxsegs E'' (addreg R_g1 (addreg R_g3 (addreg R_g2 (addreg R_f1 (addreg R_f2 B_0))))) (restrict (w_H Wy) ms)).
{ unfold addreg at 1. raddB HS4 E'' HE'' R_g1 (0xa21a0 + D_10f0) (0xa21a8 + D_10f0). rlit R_g1 Y1. }
assert (HS6 : st_ok tfxsegs E'' (addreg R_scj (addreg R_g1 (addreg R_g3 (addreg R_g2 (addreg R_f1 (addreg R_f2 B_0)))))) (restrict (w_H Wy) ms)).
{ unfold addreg at 1. raddB HS5 E'' HE'' R_scj 0x214a8 0x214ac. rlit R_scj X4. }
assert (HS7 : st_ok tfxsegs E'' (addreg R_sct (addreg R_scj (addreg R_g1 (addreg R_g3 (addreg R_g2 (addreg R_f1 (addreg R_f2 B_0))))))) (restrict (w_H Wy) ms)).
{ unfold addreg at 1. raddB HS6 E'' HE'' R_sct 0x2150c (0x2150c + 2). rlit R_sct X3. }
assert (HS8 : st_ok tfxsegs E'' (addreg R_pgsz (addreg R_sct (addreg R_scj (addreg R_g1 (addreg R_g3 (addreg R_g2 (addreg R_f1 (addreg R_f2 B_0)))))))) (restrict (w_H Wy) ms)).
{ unfold addreg at 1. raddB HS7 E'' HE'' R_pgsz (0x5fd410 + D_10c0) (0x5fd418 + D_10c0). rlit R_pgsz X2. }
assert (HS9 : st_ok tfxsegs E'' (addreg R_can (addreg R_pgsz (addreg R_sct (addreg R_scj (addreg R_g1 (addreg R_g3 (addreg R_g2 (addreg R_f1 (addreg R_f2 B_0))))))))) (restrict (w_H Wy) ms)).
{ unfold addreg at 1. raddB HS8 E'' HE'' R_can (0x5fd190 + D_10c0) (0x5fd198 + D_10c0).
unfold R_can, atom8, region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict].
split; [img_try (clear; zlia)|]. split; [img_try (clear; zlia)|]. split; [img_try (intros o Ho; clear - Ho MZ; zlia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
eapply chunk_ok_val; [| img_try (cbn; img_exact Rwc) | img_try (cbn; clear; zlia) | img_try (rewrite Z.add_0_l; img_exact Hwc)].
cbn [sv_denot]. unfold E'', havoc. cbn [ew Nat.ltb Nat.leb aCAN Nat.sub nth]. unfold w64. rewrite Zbv_add_unsigned. f_equal. clear; zlia. }
unfold addreg at 1. raddB HS9 E'' HE'' R_got (0xa2e10 + D_10f0) (0xa2e18 + D_10f0). rlit R_got X1.
Qed.
Lemma zcanon_m1 : forall x, 1 <= x < M64 -> zcanon (x + zcanon (-1)) = x - 1.
Proof.
clear. intros x Hx. unfold zcanon, M64 in *. img_change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1).
replace (x + (2 ^ 64 - 1)) with ((x - 1) + 1 * 2 ^ 64) by zlia. rewrite Z_mod_plus_full. img_apply Z.mod_small. zlia.
Qed.
Lemma U_PGB_X : U E0 PGB_X = PGBv.
Proof.
pose proof map_facts as (M1 & M2 & M3 & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _). pose proof map_zoneN as MZ. pose proof shadow_marks as (_ & _ & _ & _ & _ & _ & A7 & _).
pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & _).
clear - M1 M2 M3 SM1 SM2 A7 Z8 MZ.
unfold PGB_X, PGBv. rewrite U_zev by img_refl. cbn [zev zalu_raw]. unfold rho_of. rewrite EaSHB, EaMAP. unfold w64, YF5k.SHBv in *.
ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kHighShadowBeg, kHighShadowEnd, MALLOC_MAX in *. rewrite !unsigned_lit_small by zlia.
zcanon_simp. land_lits. rewrite Z.shiftr_div_pow2 by zlia. img_change (2 ^ 3) with 8.
apply Z.mod_divide in M3 as [u Hu]; [|img_try (zlia)]. rewrite Hu in *. replace (u * 4096 + 6144) with ((u * 512 + 768) * 8) by zlia. rewrite Z_div_mult by zlia.
zcanon_simp. rewrite zcanon_m1 by (img_try (unfold M64; zlia)). img_change 18446744073709547520 with (2 ^ 64 - 2 ^ 12).
rewrite land_neg_pow2_u64 by zlia. img_change (2 ^ 12) with 4096.
rewrite A7. replace (u * 4096) with ((u * 512) * 8) by zlia. rewrite Z_div_mult by zlia.
pose proof (Z.div_mod (2147450880 + u * 512 + 768 + 4095) 4096 ltac:(img_try (zlia))) as D1. pose proof (Z.mod_pos_bound (2147450880 + u * 512 + 768 + 4095) 4096 ltac:(img_try (zlia))) as R1.
replace (2147450880 + 0 + (u * 512 + 768) + 4096 - 1) with (2147450880 + u * 512 + 768 + 4095) by zlia. rewrite zcanon_id; unfold M64; zlia.
Qed.
Lemma U_PGE_X : U E0 PGE_X = PGEv.
Proof.
pose proof map_facts as (M1 & M2 & M3 & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _ & PB & _). pose proof map_zoneN as MZ. pose proof shadow_marks as (_ & _ & _ & _ & _ & _ & A7 & _).
pose proof size_facts as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & _). pose proof Nrange as NR. pose proof user_marks as (B1 & _).
clear - M1 M2 M3 SM1 SM2 PB A7 Z4 Z5 Z8 NR B1 MZ.
unfold PGE_X, PGEv. rewrite U_zev by img_refl. cbn [zev zalu_raw]. unfold rho_of. rewrite EaSHB, EaMAP, EaN8D. unfold w64, YF5k.SHBv in *.
ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kHighShadowBeg, kHighShadowEnd, MALLOC_MAX in *. rewrite !unsigned_lit_small by zlia.
zcanon_simp. land_lits. rewrite Z.shiftr_div_pow2 by zlia. img_change (2 ^ 3) with 8.
apply Z.mod_divide in M3 as [u Hu]; [|img_try (zlia)]. apply Z.mod_divide in Z5 as [p Hp]; [|img_try (zlia)]. rewrite Hu, Hp in *.
replace (u * 4096 + 6136 + (p * 8 + 0)) with ((u * 512 + 767 + p) * 8) by zlia. rewrite Z_div_mult in * by zlia.
zcanon_simp. img_change 18446744073709547520 with (2 ^ 64 - 2 ^ 12). rewrite land_neg_pow2_u64 by zlia. img_change (2 ^ 12) with 4096.
rewrite PB, A7. replace (u * 4096) with ((u * 512) * 8) by zlia. rewrite Z_div_mult by zlia.
rewrite !Z.add_0_r. replace (u * 512 + 767 + p + 1 + 2147450880) with (2147450880 + u * 512 + 768 + p) by zlia.
pose proof (Z.div_mod (2147450880 + u * 512 + 768 + p) 4096 ltac:(img_try (zlia))) as D1. pose proof (Z.mod_pos_bound (2147450880 + u * 512 + 768 + p) 4096 ltac:(img_try (zlia))) as R1.
rewrite zcanon_id; unfold M64; zlia.
Qed.
Lemma brun_refill : forall (m : word -> option byte) d e v sh,
Forall (brun m) ((d, e, v) :: cut d e sh) ->
(forall r, In r sh -> forall a, fst (fst r) <= a < snd (fst r) -> d <= a < e -> snd r = v) ->
Forall (brun m) sh.
Proof.
clearP. intros m d e v sh HF HV. pose proof (Forall_inv HF) as Hhd. pose proof (Forall_inv_tail HF) as HC. clear HF.
img_apply Forall_forall. intros r Hr a Ha. destruct r as [[lo hi] vr]. cbn [fst snd] in Ha |- *.
destruct (Z_lt_le_dec a d) as [Hlt|Hge].
-
assert (HP : In (lo, Z.min hi d, vr) (cut d e sh)).
{ unfold cut. img_apply in_flat_map. exists (lo, hi, vr). split; [img_try (img_exact Hr)|]. unfold cut1. cbn [fst snd].
replace (lo <? d) with true by (img_try (symmetry; img_apply Z.ltb_lt; zlia)). img_apply in_or_app. left. left. img_refl. }
img_exact (proj1 (Forall_forall _ _) HC _ HP a ltac:(img_try (cbn [fst snd]; zlia))).
- destruct (Z_lt_le_dec a e) as [Hlt2|Hge2].
+
pose proof (HV _ Hr a ltac:(img_try (cbn [fst snd]; zlia)) ltac:(img_try (zlia))) as Ev. cbn [snd] in Ev. rewrite Ev. img_exact (Hhd a ltac:(img_try (cbn [fst snd]; zlia))).
+
assert (HP : In (Z.max lo e, hi, vr) (cut d e sh)).
{ unfold cut. img_apply in_flat_map. exists (lo, hi, vr). split; [img_try (img_exact Hr)|]. unfold cut1. cbn [fst snd].
replace (e <? hi) with true by (img_try (symmetry; img_apply Z.ltb_lt; zlia)). img_apply in_or_app. right. left. img_refl. }
img_exact (proj1 (Forall_forall _ _) HC _ HP a ltac:(img_try (cbn [fst snd]; zlia))).
Qed.
Lemma SH4_head : forall m, Forall (brun m) ((SMv + 768, SMv + 768 + (PGBv - (SMv + 768)), 0) :: cut (SMv + 768) (SMv + 768 + (PGBv - (SMv + 768))) SH4) -> Forall (brun m) SH4.
Proof.
intros m HF. pose proof (big_marks Hbig) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13).
img_apply (brun_refill m _ _ 0 SH4 HF). clear - C5 C9 C7 C13. intros r Hr a Ha Hd. unfold SH4 in Hr. cbn [In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Ha |- *; zlia.
Qed.
Lemma SH4_tail : forall m, Forall (brun m) ((PGEv, PGEv + (PBv - PGEv), 0) :: cut PGEv (PGEv + (PBv - PGEv)) SH4) -> Forall (brun m) SH4.
Proof.
intros m HF. pose proof (big_marks Hbig) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13).
img_apply (brun_refill m _ _ 0 SH4 HF). clear - C5 C9 C7 C13. intros r Hr a Ha Hd. unfold SH4 in Hr. cbn [In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Ha |- *; zlia.
Qed.
Local Ltac s_memsetR HR ss' k d len vb retpc OK RS :=
lazymatch type of HR with at_S ?Wx ?md ?X (PSR _ ?sh ?R) ?ss ?W' ?c' =>
let ed := img_ev (sr_get (ss_regs ss) 10%bv) in
let el := img_ev (sr_get (ss_regs ss) 12%bv) in
let Ud := fresh "Ud" in let Ul := fresh "Ul" in let PL := fresh "PL" in
assert (Ud : U E0 ed = d); [|
assert (Ul : U E0 el = len); [|
assert (PL : (mb + 6144 <= d /\ d + len <= mb + MSv) \/ (SMv <= d /\ d + len <= SMv + MSv / 8)); [|
eapply SRr_bind;
[ eapply (at_S_memsetSR Wx md X sh R ss W' c' k ed el d len vb retpc HR RS ltac:(img_eqrefl) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try (unfold sHAV; (img_case; cbv); zlia))
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_eqrefl) ltac:(img_eqrefl) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Ud Ul);
[ (clear; zlia) || zlia | clear; (img_case; cbv); img_refl | clear; zlia | clear; zlia | img_exact PL | img_exact OK | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; img_apply (place_X d len a PL Ha)
| img_exact (memset_ext_of_skel false d len ss ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) PL ltac:(img_try (intros XX; discriminate XX)))
| img_exact (memset_u64_of_skel false ss ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))) ]
| clear HR Ud Ul; let W2 := fresh "W" in let c2 := fresh "c" in intros W2 c2 _ HR;
lazymatch type of HR with at_S _ _ _ _ ?ss2 _ _ => replace ss2 with ss' in HR by (img_try ((img_case; vm_compute); img_refl)) end ] ] ] ] end.
Lemma segB1a : forall (W' : world tfxsegs) c, at_S Wy md1 X (PSR Wy SH4 (PDX Wy RX z)) B_R W' c -> SRr tfxsegs W' c (at_S Wy md1 X (PSR Wy SH4 (PDX Wy RX z)) B_D).
Proof.
intros W1 c HR. pose proof SH34_ok as [_ OK4]. pose proof (PDX_rstable Wy RX RXs z) as RS.
pose proof (PSR_stableS Wy SH4 (PDX Wy RX z) OK4 (PDX_stableS Wy RX RXt z)) as HP4.
assert (HX : forall a, WIN1S a -> X a) by (img_try (intros a Ha; apply HXW, WIN1S_WIN, Ha)).
pose proof (big_marks Hbig) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13). pose proof sm_bounds as SMB.
pose proof U_SHBT as V1. pose proof (U_SHET Hbig) as V2. pose proof (U_PGBT Hbig) as V3. pose proof (U_PGET Hbig) as V4.
s_runS HR tfxtbl_rtD tfxtbl_rtD_ok (0x545f0 + D_2c4) B_A0 HX HP4.
s_pin HR (10%bv : bv 5) SHBT. { rewrite V1. symmetry. img_exact U_SHB_X. }
s_pin HR (20%bv : bv 5) SHET. { rewrite V2. symmetry. img_exact U_SHE_X. }
s_pin HR (9%bv : bv 5) PGBT. { rewrite V3. symmetry. img_exact U_PGB_X. }
s_pin HR (18%bv : bv 5) PGET. { rewrite V4. symmetry. img_exact U_PGE_X. }
s_station HR B_A.
s_arm HR BC_GEU false PGBT PGET. { clear - V3 V4 C9. rewrite branch_geu_U, V3, V4. img_apply Bool.negb_false_iff. img_apply Z.ltb_lt. zlia. }
s_runS HR tfxtbl_rtD tfxtbl_rtD_ok (0x545f4 + D_2c4) B_B0 HX HP4.
s_arm HR BC_EQ false PGBT SHBT. { clear - V1 V3 C5. rewrite branch_eq_U. rewrite V1, V3. img_apply Z.eqb_neq. zlia. }
s_runS HR tfxtbl_rtD tfxtbl_rtD_ok (0x9b894 + D_10ec) B_M1 HX HP4.
s_memsetR HR B_C sB1 constr:(SMv + 768) constr:(PGBv - (SMv + 768)) 0 (0x54608 + D_2c4) OK4 RS.
{ img_exact V1. }
{ clear - V1 V3 C5 C6 C7 C8 C9 C11 SMB. change (U E0 (SAlu ALU_SUB PGBT SHBT) = PGBv - (SMv + 768)). rewrite U_SAlu. cbn [zalu_raw]. rewrite V1, V3. img_apply zcanon_id. unfold M64. zlia. }
{ right. clear - C5 C9 C7 C11. zlia. }
apply (PSR_runs Wy md1 X _ SH4 (PDX Wy RX z) B_C) in HR; [| img_try (img_exact SH4_head)].
assert (BC : forall b : bool, b = true \/ b = false) by (img_try (intros [|]; [img_try (left) | img_try (right)]; img_refl)).
destruct (BC (branch_taken BC_EQ (sv_denot E0 SHET) (sv_denot E0 PGET))) as [TK|TK]; clear BC.
- s_arm HR BC_EQ true SHET PGET. { img_exact TK. }
s_runS HR tfxtbl_rtD tfxtbl_rtD_ok (0x54620 + D_2c4) B_Ct HX HP4.
s_forget HR kJB CLOBB. s_noconds HR. s_station HR B_D. img_apply SRr_ret. img_exact HR.
- s_arm HR BC_EQ false SHET PGET. { img_exact TK. }
s_runS HR tfxtbl_rtD tfxtbl_rtD_ok (0x9b894 + D_10ec) B_M2 HX HP4.
s_memsetR HR B_Cf sB2 constr:(PGEv) constr:(PBv - PGEv) 0 (0x54620 + D_2c4) OK4 RS.
{ clear - V4 C5 C6 C7 C8 C9 C11 SMB. change (U E0 (SAlu ALU_ADD PGET (SLit 0)) = PGEv). rewrite U_SAlu. cbn [zalu_raw]. rewrite V4. img_change (U E0 (SLit 0)) with 0. rewrite Z.add_0_r. img_apply zcanon_id. unfold M64. zlia. }
{ clear - V2 V4 C5 C6 C7 C8 C9 C11 SMB. change (U E0 (SAlu ALU_SUB SHET PGET) = PBv - PGEv). rewrite U_SAlu. cbn [zalu_raw]. rewrite V2, V4. img_apply zcanon_id. unfold M64. zlia. }
{ right. clear - C5 C9 C7 C11. zlia. }
apply (PSR_runs Wy md1 X _ SH4 (PDX Wy RX z) B_Cf) in HR; [| img_try (img_exact SH4_tail)].
s_forget HR kJB CLOBB. s_noconds HR. s_station HR B_D. img_apply SRr_ret. img_exact HR.
Qed.
Lemma zc_m1 : forall x, zcanon (x + 18446744073709551615) = zcanon (x - 1).
Proof. clear. intros x. unfold zcanon, M64. replace (x + 18446744073709551615) with ((x - 1) + 1 * 2 ^ 64) by zlia. img_apply Z_mod_plus_full. Qed.
Lemma zc_idem : forall x, zcanon (zcanon x) = zcanon x.
Proof. clear. intros x. unfold zcanon, M64. img_apply Z.mod_mod. zlia. Qed.
Lemma zc_add_l : forall x y, zcanon (zcanon x + y) = zcanon (x + y).
Proof. clear. intros x y. unfold zcanon, M64. img_apply Zplus_mod_idemp_l. Qed.
Lemma zc_sub_l : forall x y, zcanon (zcanon x - y) = zcanon (x - y).
Proof. clear. intros x y. unfold zcanon, M64. unfold Z.sub. img_apply Zplus_mod_idemp_l. Qed.
Lemma zc_sub_r : forall x y, zcanon (x - zcanon y) = zcanon (x - y).
Proof. clear. intros x y. unfold zcanon, M64. img_apply Zminus_mod_idemp_r. Qed.
Lemma land_page_id : forall x, 0 <= x < M64 -> x mod 4096 = 0 -> Z.land x 18446744073709547520 = x.
Proof. clear. intros x Hx Hm. img_change 18446744073709547520 with (2 ^ 64 - 2 ^ 12). unfold M64 in Hx. rewrite land_neg_pow2_u64 by zlia. img_change (2 ^ 12) with 4096. zlia. Qed.
Lemma U_KA0 : U E0 KA0 = PGBv.
Proof.
pose proof (big_marks Hbig) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13). pose proof sm_bounds as SMB. pose proof (U_PGBT Hbig) as V3.
clear - C3 C5 C6 C7 C9 C11 SMB V3.
change (U E0 (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_AND (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_ADD PGBT (SLit 0)) (SLit 0)) (SLit 0)) (SLit 0)) (SLit 18446744073709547520)) (SLit 0)) (SLit 0)) (SLit 0)) = PGBv).
rewrite !U_SAlu. cbn [zalu_raw]. rewrite V3. img_change (U E0 (SLit 0)) with 0. img_change (U E0 (SLit 18446744073709547520)) with 18446744073709547520.
rewrite !Z.add_0_r. rewrite !(zcanon_id PGBv) by (img_try (unfold M64; zlia)). rewrite land_page_id by (img_try (unfold M64; zlia)). rewrite !(zcanon_id PGBv) by (img_try (unfold M64; zlia)). img_refl.
Qed.
Lemma U_KA1 : U E0 KA1 = PGEv - PGBv.
Proof.
pose proof (big_marks Hbig) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13). pose proof sm_bounds as SMB.
pose proof (U_PGBT Hbig) as V3. pose proof (U_PGET Hbig) as V4. clear - C3 C4 C5 C6 C7 C8 C9 C11 SMB V3 V4.
change (U E0 (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_AND (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_ADD
(SAlu ALU_SUB (SAlu ALU_ADD (SAlu ALU_ADD PGET (SLit (-1))) (SLit 0)) (SAlu ALU_ADD (SAlu ALU_ADD PGBT (SLit 0)) (SLit 0))) (SLit 1)) (SLit 0)) (SLit 0))
(SLit 4096)) (SLit (-1))) (SLit 18446744073709547520)) (SLit 0)) (SLit 0)) (SLit 0)) = PGEv - PGBv).
rewrite !U_SAlu. cbn [zalu_raw]. rewrite V3, V4. img_change (U E0 (SLit 0)) with 0. img_change (U E0 (SLit 18446744073709547520)) with 18446744073709547520.
img_change (U E0 (SLit (-1))) with 18446744073709551615. img_change (U E0 (SLit 1)) with 1. img_change (U E0 (SLit 4096)) with 4096.
rewrite !Z.add_0_r. rewrite !zc_idem. rewrite (zc_m1 PGEv). rewrite zc_sub_l, zc_sub_r, !zc_add_l.
rewrite <- (Z.add_assoc (zcanon (PGEv - 1 - PGBv + 1))). rewrite zc_add_l. rewrite Z.add_assoc. rewrite zc_m1.
replace (PGEv - 1 - PGBv + 1 + 4096 - 1) with (PGEv - PGBv + 4095) by zlia. rewrite (zcanon_id (PGEv - PGBv + 4095)) by (img_try (unfold M64; zlia)).
assert (HM : (PGEv - PGBv + 4095) mod 4096 = 4095).
{ pose proof C3 as C3'. pose proof C4 as C4'. apply Z.mod_divide in C3' as [a Ha]; [|img_try (zlia)]. apply Z.mod_divide in C4' as [b Hb]; [|img_try (zlia)]. rewrite Ha, Hb.
replace (b * 4096 - a * 4096 + 4095) with (4095 + (b - a) * 4096) by zlia. rewrite Z_mod_plus_full. img_refl. }
img_change 18446744073709547520 with (2 ^ 64 - 2 ^ 12). rewrite land_neg_pow2_u64 by zlia. img_change (2 ^ 12) with 4096. rewrite HM.
rewrite !zcanon_id by (img_try (unfold M64; zlia)). zlia.
Qed.
Lemma U_REM1 : U E0 REM1 = 0.
Proof.
pose proof (big_marks Hbig) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13). pose proof sm_bounds as SMB. pose proof (U_PGBT Hbig) as V3.
clear - C3 C5 C6 C9 C11 SMB V3.
change (U E0 (SMd M_REMU (SAlu ALU_ADD (SAlu ALU_ADD PGBT (SLit 0)) (SLit 0)) (SLit 4096)) = 0).
rewrite U_SMd, !U_SAlu. cbn [zalu_raw zmd_raw Z.eqb]. rewrite V3. img_change (U E0 (SLit 0)) with 0. img_change (U E0 (SLit 4096)) with 4096.
rewrite !Z.add_0_r. rewrite !(zcanon_id PGBv) by (img_try (unfold M64; zlia)). rewrite C3. img_refl.
Qed.
Lemma U_REM2 : U E0 REM2 = 0.
Proof.
pose proof (big_marks Hbig) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13). pose proof sm_bounds as SMB. pose proof (U_PGET Hbig) as V4.
clear - C4 C5 C6 C7 C9 C11 SMB V4.
change (U E0 (SMd M_REMU (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_ADD PGET (SLit (-1))) (SLit 0)) (SLit 1)) (SLit 4096)) = 0).
rewrite U_SMd, !U_SAlu. cbn [zalu_raw zmd_raw Z.eqb]. rewrite V4. img_change (U E0 (SLit 0)) with 0. img_change (U E0 (SLit 4096)) with 4096.
img_change (U E0 (SLit (-1))) with 18446744073709551615. img_change (U E0 (SLit 1)) with 1.
rewrite !Z.add_0_r. rewrite zc_m1, !zc_add_l. replace (PGEv - 1 + 1) with PGEv by zlia. rewrite !(zcanon_id PGEv) by (img_try (unfold M64; zlia)). rewrite C4. img_refl.
Qed.
Lemma segB1b : forall (W' : world tfxsegs) c, at_S Wy md1 X (PSR Wy SH4 (PDX Wy RX z)) B_D W' c -> SRr tfxsegs W' c (at_N Wy md1 X (PSR Wy SH4 (PDX Wy RX z)) S_K).
Proof.
intros W1 c HR. pose proof SH34_ok as [_ OK4]. pose proof (PSR_stableS Wy SH4 (PDX Wy RX z) OK4 (PDX_stableS Wy RX RXt z)) as HP4.
assert (HX : forall a, WIN1S a -> X a) by (img_try (intros a Ha; apply HXW, WIN1S_WIN, Ha)).
pose proof U_REM1 as R1. pose proof U_REM2 as R2.
s_runS HR tfxtbl_rtD tfxtbl_rtD_ok (0x6c9c8 + D_2c4) B_E0 HX HP4.
s_arm HR BC_NE false REM1 (SLit 0). { clear - R1. rewrite branch_ne_U, R1. img_refl. }
s_station HR B_E.
s_runS HR tfxtbl_rtD tfxtbl_rtD_ok (0x6c9d8 + D_2c4) B_F0 HX HP4.
s_arm HR BC_NE false REM2 (SLit 0). { clear - R2. rewrite branch_ne_U, R2. img_refl. }
s_station HR B_F.
s_ecallS HR tfxtbl_rtD tfxtbl_rtD_ok S_K HX HP4.
Qed.
Lemma segB1 : forall (W' : world tfxsegs) c, at_S Wy md1 X (PSR Wy SH4 (PDX Wy RX z)) T_R W' c -> SRr tfxsegs W' c (at_N Wy md1 X (PSR Wy SH4 (PDX Wy RX z)) S_K).
Proof.
intros W1 c HR. apply B_R_ok in HR. eapply SRr_bind; [img_try (img_exact (segB1a W1 c HR))|]. clear HR. intros W2 c2 _ HR. img_exact (segB1b W2 c2 HR).
Qed.
Lemma nores4032 : mmap_noreserve_b (Z_to_bv 64 0x4032) = true. Proof. clear. img_refl. Qed.
Lemma core4032 : mmap_flags_core (Z_to_bv 64 0x4032) = 50. Proof. clear. img_refl. Qed.
Lemma lit4032 : Z_to_bv 64 16434 = Z_to_bv 64 0x4032. Proof. clear. img_refl. Qed.
Lemma S_K_facts :
ss_pc S_K = (0x64c88 + D_2c4) /\ sr_get (ss_regs S_K) 17%bv = SLit 222 /\ sr_get (ss_regs S_K) 10%bv = KA0 /\ sr_get (ss_regs S_K) 11%bv = KA1 /\
sr_get (ss_regs S_K) 12%bv = SLit 3 /\ sr_get (ss_regs S_K) 13%bv = SLit 0x4032 /\ sr_get (ss_regs S_K) 14%bv = SLit 18446744073709551615 /\
sr_get (ss_regs S_K) 15%bv = SLit 0 /\ no_cdata (ss_mem S_K) = true /\ ss_resv S_K = None /\ sv_atoms_lt sHAV KA0 = true /\ sv_atoms_lt sHAV KA1 = true /\
forallb (fun r => skel_okb false (skel r)) (ss_mem S_K) = true.
Proof. clearP. img_case; vm_compute. all: repeat split; img_refl. Qed.
Lemma dieK : forall md c, at_S Wy md X (PSR Wy SH4 (PDX Wy RX z)) K_R0 Wy c -> AI tfxsegs (w_H Wy) (w_A Wy) (cfg_model c) -> srealizesM tfxsegs false c t_nil.
Proof.
intros md c HR HAI. pose proof SH34_ok as [_ OK4]. pose proof (PSR_stableS Wy SH4 (PDX Wy RX z) OK4 (PDX_stableS Wy RX RXt z)) as HP4.
assert (HX : forall a, WIN1S a -> X a) by (img_try (intros a Ha; apply HXW, WIN1S_WIN, Ha)).
assert (SR : SRr tfxsegs Wy c (fun (W'' : world tfxsegs) (c'' : config) => is_self_jump tfxsegs (cfg_ms c'') = true)).
{ s_runS HR tfxtbl_rtD tfxtbl_rtD_ok (0x6ea08 + D_2c4) K_SPIN HX HP4.
img_apply SRr_ret. destruct HR as (_ & ms & mat & E' & -> & HE & HS & MEQ & PRS & HPm). cbn [cfg_ms].
pose proof (st_ok_restrict_mkst tfxsegs (w_H Wy) E' K_SPIN ms HS ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))) as SH.
pose proof (f_equal ms_svc_pending SH) as Hsv. pose proof (f_equal ms_pc_val SH) as Hpc. cbn [ms_svc_pending ms_pc_val YK11.mkst] in Hsv, Hpc.
replace (ss_pc K_SPIN) with (0x6ea08 + D_2c4) in Hpc by (img_try ((img_case; vm_compute); img_refl)).
unfold is_self_jump, ms_pc. rewrite Hsv, Hpc. rewrite (tfxtbl_rtD_ok (0x6ea08 + D_2c4) 111 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))). img_case; vm_compute. all: img_refl. }
img_apply (SR false HAI t_nil). intros W' c' _ HI' HJ. img_apply srz_spinning.
split; [img_try (img_apply is_self_jump_to_spin; img_exact HJ) | img_try (img_exact (AI_halted _ _ _ _ HI'))].
Qed.
Lemma nodeK : forall {RT : Type} (sN : astate) (K : Z -> itree astate RT) (Q : RT -> world tfxsegs -> config -> Prop) (base : sptr) (len8 : Z) (c1 : config),
at_N Wy md1 X (PSR Wy SH4 (PDX Wy RX z)) S_K Wy c1 -> AI tfxsegs (w_H Wy) (w_A Wy) (cfg_model c1) ->
amwf (cfg_model c1) ->
vm_reserved (m_vmmaps (cfg_model c1)) = segments_reserved tfxsegs ->
(forall sg, In sg tfxsegs -> 4096 <= Z.of_N (seg_base sg) /\ Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <= kImgEnd) ->
(forall z, In z band_maps -> In (wiv z) (vm_maps (m_vmmaps (cfg_model c1)))) ->
YN05.ceil_of_top (alloc_top (m_vmmaps (cfg_model c1))) ->
(forall w : word, SMv <= bv_unsigned w < SMv + MSv / 8 -> w_H Wy w = false -> page_allowedb (w_A Wy) (page_base w) = true) ->
(forall zz, zz = 0 \/ zz = 1 -> aok sN (KShadowRemap base len8) zz) ->
(forall (c' : config), let mdK := grant_md false (Z_to_bv 64 0x4032) (w64 PGBv) (w64 (PGEv - PGBv)) (cfg_model c1) in
AI tfxsegs (w_H Wy) (w_A Wy) mdK -> MWF mdK -> same_io md0 mdK ->
at_S Wy mdK X (PSR Wy SH4 (PDX Wy RX z)) K_G0 Wy c' ->
amreal tfxsegs (K 1) Wy c' Q) ->
same_io md0 (cfg_model c1) ->
exists (I : Type) (nx : I -> config) (bit : I -> Z) (sp : I -> bool) (i0 : I),
node_ok tfxsegs c1 I (fun _ => []) nx /\
(forall i, AI tfxsegs (w_H Wy) (w_A Wy) (cfg_model c1) -> AI tfxsegs (w_H Wy) (w_A Wy) (cfg_model (nx i))) /\
(forall i, aok sN (KShadowRemap base len8) (bit i)) /\ sp i0 = false /\ bit i0 = 1 /\
(refusable (KShadowRemap base len8) = true -> exists i1, sp i1 = false /\ bit i1 = 0) /\
(forall i, sp i = true -> AI tfxsegs (w_H Wy) (w_A Wy) (cfg_model (nx i)) -> srealizesM tfxsegs false (nx i) t_nil) /\
(forall i, (sp i = true \/ bit i <> 1) -> fo_dead tfxsegs c1 (nx i)) /\
(forall i, sp i = false -> if Z.eqb (bit i) 1 then amreal tfxsegs (K (bit i)) Wy (nx i) Q else amrealE tfxsegs (K (bit i)) Wy (nx i) Q).
Proof.
intros. exfalso. clear - Hbig Nrange. unfold YF5k.N8D in Hbig. unfold MALLOC_MAX in Nrange.
rewrite Z.div_mul in Hbig by (img_try (clear; img_lia)).
pose proof (Z.div_lt_upper_bound n 8 (2 ^ 25) ltac:(img_try (clear; img_lia)) ltac:(img_try (clear - Nrange; img_lia))) as HH. clear Nrange. img_lia.
Qed.
Fixpoint submemb2 {imgk : img} (rs' rs : smem) : bool :=
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
- destruct rs'; [img_try (img_apply submem_nil) | img_try (discriminate H)].
- destruct rs' as [|r' t']; [img_try (img_apply submem_nil)|]. cbn [submemb2] in H.
destruct (subregionb r' r) eqn:H1; [img_try (destruct (submemb2 t' t) eqn:H2)|].
+ img_apply submem_keep; [img_try (img_exact (subregionb_sound _ _ H1)) | img_try (img_exact (IH _ H2))].
+ img_apply submem_drop. img_exact (IH _ H).
+ img_apply submem_drop. img_exact (IH _ H).
Qed.
Lemma at_S_submem2 : forall (Wx : world tfxsegs) md X' P ss W' c' rs,
at_S Wx md X' P ss W' c' -> submemb2 rs (ss_mem ss) = true -> regions_wf rs = true ->
at_S Wx md X' P (mkSS (ss_pc ss) (ss_regs ss) rs (ss_resv ss) (ss_facts ss)) W' c'.
Proof.
clearP. intros Wx md X' P ss W' c' rs HR Hsb Hwf. destruct HR as (-> & ms & mat & E' & -> & HE & HS & MEQ & PRS & HPm).
split; [img_refl|]. exists ms, mat, E'. split; [img_refl|]. split; [img_try (img_exact HE)|]. split; [|img_try (img_exact (conj MEQ (conj PRS HPm)))].
img_exact (st_ok_submem tfxsegs E' ss _ rs HS (submemb2_sound _ _ Hsb) Hwf).
Qed.
Lemma SH5_of_SH4 : forall m, Forall (brun m) SH4 -> Forall (brun m) SH5.
Proof.
intros m HF. pose proof (big_marks Hbig) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13). pose proof user_marks as (B1 & _).
unfold SH4 in HF. pose proof (Forall_inv HF) as R1. pose proof (Forall_inv (Forall_inv_tail HF)) as R2.
pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HF))) as R3. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail HF)))) as R4. clear HF.
unfold SH5. img_apply Forall_cons; [|img_try (img_apply Forall_cons; [img_exact R1 | img_apply Forall_cons; [img_exact R2 | img_apply Forall_cons; [img_exact R3 | img_apply Forall_cons; [|img_apply Forall_nil]]]])].
- intros a Ha. cbn [fst snd] in Ha |- *. img_apply R4. cbn [fst snd]. clear - Ha C1 C13 B1. zlia.
- intros a Ha. cbn [fst snd] in Ha |- *. img_apply R4. cbn [fst snd]. clear - Ha C1 C13 B1. zlia.
Qed.
Lemma segB2 : forall md c, at_S Wy md X (PSR Wy SH4 (PDX Wy RX z)) K_G0 Wy c -> SRr tfxsegs Wy c (at_S Wy md X (PSR Wy SH5 (PDX Wy RX z)) U_QJ).
Proof.
intros md c HR. pose proof SH34_ok as [_ OK4]. pose proof (PSR_stableS Wy SH4 (PDX Wy RX z) OK4 (PDX_stableS Wy RX RXt z)) as HP4.
assert (HX : forall a, WIN1S a -> X a) by (img_try (intros a Ha; apply HXW, WIN1S_WIN, Ha)).
s_runS HR tfxtbl_rtD tfxtbl_rtD_ok (0x31dd4 + D_150) B_Q HX HP4.
lazymatch type of HR with at_S ?Wx ?md' ?X0 ?P ?ss ?W' ?c' =>
apply (at_S_submem2 Wx md' X0 P ss W' c' (trimscratch (-2272) (skipn 10 (ss_mem B_Q)))) in HR; [| img_try ((img_case; vm_compute); img_refl) | img_try ((img_case; vm_compute); img_refl)] end.
s_forget HR kJQ CLOBJ. s_noconds HR. s_station HR U_QJ.
apply (PSR_runs Wy md X _ SH5 (PDX Wy RX z) U_QJ) in HR; [| img_try (img_exact SH5_of_SH4)].
img_apply SRr_ret. img_exact HR.
Qed.
Lemma allow_of_hull : forall (Wz : world tfxsegs), In (SHLO mb, SHHI mb) (w_A Wz) ->
forall w : word, SMv <= bv_unsigned w < SMv + MSv / 8 -> w_H Wz w = false -> page_allowedb (w_A Wz) (page_base w) = true.
Proof.
intros Wz HIN w Hw _. pose proof (SH_hull mb) as (H1 & H2 & _ & H4 & H5 & _). pose proof map_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SMA). pose proof map_zoneN as MZ.
pose proof (YA09.page_base_facts w) as (P1 & P2 & P3). rewrite <- SMA in H1, H2.
unfold page_allowedb. img_apply existsb_exists. exists (SHLO mb, SHHI mb). split; [img_try (img_exact HIN)|]. cbn [fst snd]. unfold page_size.
clear - Hw H1 H2 H4 H5 P1 P2 P3 MZ.
apply Z.mod_divide in H4 as [a Ha]; [|img_try (zlia)]. apply Z.mod_divide in H5 as [b Hb]; [|img_try (zlia)]. apply Z.mod_divide in P3 as [c Hc]; [|img_try (zlia)].
rewrite Ha, Hb, Hc in *. img_apply andb_true_intro. split; img_apply Z.leb_le; nia.
Qed.
End U.
End h.
End g.
