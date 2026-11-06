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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF64 YF3v YF3w YF3x YF41 YF6z YF0a YF7f YF7o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Set Printing Depth 50. Set Printing Width 180.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
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
pose proof (st_ok_forget2 k E ss ss' H ms clob HS eq_refl
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
eq_refl eq_refl ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))) as HS2; clear HS; rename HS2 into HS
end.
Section g. Context {imgk : img}.
Variables (W : world tfxsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (n : Z) (ch : list (Z * Z * Z)).
Variables (idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 : Z).
Variable mb : Z.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Let Qb : Z := ly_Q ly.
Local Abbreviation R8v := (@YF7f.R8v n).
Local Abbreviation N8D := (@YF7f.N8D n).
Local Abbreviation NDv := (@YF7f.NDv n).
Local Abbreviation MSv := (@YF7f.MSv n).
Local Abbreviation SHBv := (@YF7f.SHBv).
Local Abbreviation QSv := (@YF7f.QSv ly idx).
Local Abbreviation Kv := (@YF7f.Kv mb).
Local Abbreviation Uv := (@YF7f.Uv mb).
Local Abbreviation ENDv := (@YF7f.ENDv n mb).
Local Abbreviation TLv := (@YF7f.TLv n).
Local Abbreviation UEv := (@YF7f.UEv n mb).
Local Abbreviation RLv := (@YF7f.RLv n).
Local Abbreviation SMv := (@YF7f.SMv mb).
Local Abbreviation PBv := (@YF7f.PBv n mb).
Local Abbreviation LGv := (@YF7f.LGv n).
Local Abbreviation BSLv := (@YF7f.BSLv n imgk).
Local Abbreviation AR1 f := (f imgk ly regs0) (only parsing).
Local Abbreviation tr := ((AR1 (@YF7f.tr)) ch).
Local Abbreviation AR0 f := (f n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb) (only parsing).
Local Abbreviation XW := (AR0 (AR1 (@YF7f.XW))).
Local Abbreviation E0 := (AR0 (AR1 (@YF7f.E0))).
Local Abbreviation Er := (AR0 (AR1 (@YF7f.Er))).
Local Abbreviation E1 := (AR0 (AR1 (@YF7f.E1))).
Local Abbreviation E2 := (AR0 (AR1 (@YF7f.E2))).
Local Abbreviation E4 := (AR0 (AR1 (@YF7f.E4))).
Local Abbreviation E8 := (AR0 (AR1 (@YF7f.E8))).
Local Abbreviation E10 := (AR0 (AR1 (@YF7f.E10))).
Local Abbreviation EaT := (AR0 (AR1 (@YF7f.EaT))).
Local Abbreviation EaC := (AR0 (AR1 (@YF7f.EaC))).
Local Abbreviation EaSB := (AR0 (AR1 (@YF7f.EaSB))).
Local Abbreviation EaTOP := (AR0 (AR1 (@YF7f.EaTOP))).
Local Abbreviation EaR8 := (AR0 (AR1 (@YF7f.EaR8))).
Local Abbreviation EaQ := (AR0 (AR1 (@YF7f.EaQ))).
Local Abbreviation EaRES := (AR0 (AR1 (@YF7f.EaRES))).
Local Abbreviation EaNCH := (AR0 (AR1 (@YF7f.EaNCH))).
Local Abbreviation EaMS := (AR0 (AR1 (@YF7f.EaMS))).
Local Abbreviation EaMAP := (AR0 (AR1 (@YF7f.EaMAP))).
Local Abbreviation EaEND := (AR0 (AR1 (@YF7f.EaEND))).
Local Abbreviation EaSHB := (AR0 (AR1 (@YF7f.EaSHB))).
Local Abbreviation EaTL := (AR0 (AR1 (@YF7f.EaTL))).
Local Abbreviation EaQS := (AR0 (AR1 (@YF7f.EaQS))).
Local Abbreviation EaBSL := (AR0 (AR1 (@YF7f.EaBSL))).
Local Abbreviation EaSM := (AR0 (AR1 (@YF7f.EaSM))).
Local Abbreviation EaUE := (AR0 (AR1 (@YF7f.EaUE))).
Local Abbreviation EaND := (AR0 (AR1 (@YF7f.EaND))).
Local Abbreviation EaRL := (AR0 (AR1 (@YF7f.EaRL))).
Local Abbreviation EaN8D := (AR0 (AR1 (@YF7f.EaN8D))).
Local Abbreviation EaPB := (AR0 (AR1 (@YF7f.EaPB))).
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
Local Abbreviation mod0_of_mul := (@YF7f.mod0_of_mul).
Local Abbreviation size_facts := (@YF7f.size_facts n Nrange).
Local Abbreviation tr_length := ((AR1 (@YF7f.tr_length)) ch idx res Hidx).
Local Abbreviation AR6 f := (f idx res LY IMG Hidx Hres) (only parsing).
Local Abbreviation high_facts := (AR6 (AR1 (@YF7f.high_facts _))).
Local Abbreviation stack_ivs := (@YF7f.stack_ivs _ ly regs0 idx res LY Hsp Hidx Hres).
Local Abbreviation HCX := (@YF7f.HCX _ ly LY).
Hypothesis Hpres0 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem0 a.
Hypothesis Hmap : mb mod 4096 = 0 /\ mzone mb MSv.
Hypothesis Hmap_apart :
zdisjoint (mb, MSv) (T, kThreadObjSize) /\ zdisjoint (mb, MSv) (ly_C ly, kCtxMapSize) /\
zdisjoint (mb, MSv) (ly_prim ly, kPrimResvSize) /\ zdisjoint (mb, MSv) (Qb, kPtrArrayResv) /\
zdisjoint (mb, MSv) (ly_NB ly, kNodesBlockSize) /\ zdisjoint (mb, MSv) (ly_SB ly, kStoreBlockSize) /\
zdisjoint (mb, MSv) (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly).
Local Abbreviation AR3 f := (AR1 f n idx res mb) (only parsing).
Local Abbreviation map_facts := ((AR3 (@YF7f.map_facts _)) Nrange Hidx Hres Hmap).
Local Abbreviation map_zone := ((AR3 (@YF7f.map_zone _)) Nrange Hidx Hmap).
Local Abbreviation map_zoneN := ((AR3 (@YF7f.map_zoneN _)) Nrange Hidx Hres Hmap).
Local Abbreviation map_in_band := ((AR3 (@YF7f.map_in_band _)) Nrange Hidx Hmap).
Local Abbreviation map_off_img := (@YF7f.map_off_img _ imgk n mb Hmap).
Local Abbreviation WINT := (@YF7f.WINT ly).
Local Abbreviation WINI := (@YF7f.WINI n imgk).
Local Abbreviation WINM := (@YF7f.WINM ly n idx mb).
Local Abbreviation WIN := ((AR1 (@YF7f.WIN)) n idx mb).
Local Abbreviation WINN := (AR1 (@YF7f.WINN)).
Local Abbreviation WINP := ((AR1 (@YF7f.WINP)) n).
Local Abbreviation WINP_WIN := ((AR1 (@YF7f.WINP_WIN)) n idx mb).
Local Abbreviation WIN1P := ((AR1 (@YF7f.WIN1P)) n).
Local Abbreviation WIN1 := ((AR1 (@YF7f.WIN1)) n idx mb).
Local Abbreviation WIN1P_WINP := ((AR3 (@YF7f.WIN1P_WINP)) Hidx).
Local Abbreviation WIN1_WIN := ((AR3 (@YF7f.WIN1_WIN)) Hidx).
Local Abbreviation WIN1P_WIN1 := ((AR1 (@YF7f.WIN1P_WIN1)) n idx mb).
Local Abbreviation LGv_range := (@YF7f.LGv_range n Nrange).
Local Abbreviation BSLv_range := ((AR3 (@YF7f.BSLv_range)) Nrange Hidx).
Local Abbreviation WSKELP := (@YF7f.WSKELP imgk).
Local Abbreviation WSKEL1P := (@YF7f.WSKEL1P imgk).
Local Abbreviation WMAP := (@YF7f.WMAP).
Local Abbreviation WSKEL := (@YF7f.WSKEL imgk).
Local Abbreviation WSKEL1 := (@YF7f.WSKEL1 imgk).
Local Abbreviation win_sub := (@YF7f.win_sub).
Local Abbreviation win_sub_sound := (@YF7f.win_sub_sound ly regs0 idx res mb Hidx Hres).
Local Abbreviation in_win := (@YF7f.in_win).
Local Abbreviation AR2 f := (AR0 f LY IMG Nrange Hidx Hres) (only parsing).
Local Abbreviation WSKELP_WINP := (AR2 (AR1 (@YF7f.WSKELP_WINP _))).
Local Abbreviation WSKEL1P_WIN1P := (AR2 (AR1 (@YF7f.WSKEL1P_WIN1P _))).
Local Abbreviation WMAP_WINM := ((AR2 (AR1 (@YF7f.WMAP_WINM _))) Hmap).
Local Abbreviation WSKEL_WIN := ((AR2 (AR1 (@YF7f.WSKEL_WIN _))) Hmap).
Local Abbreviation WSKEL1_WIN1 := ((AR2 (AR1 (@YF7f.WSKEL1_WIN1 _))) Hmap).
Local Abbreviation windows_in := (@YF7f.windows_in ly regs0 idx res mb Hidx Hres).
Local Abbreviation windows_WINP := (AR2 (AR1 (@YF7f.windows_WINP _))).
Local Abbreviation windows_WIN1P := (AR2 (AR1 (@YF7f.windows_WIN1P _))).
Local Abbreviation windows_WIN := ((AR2 (AR1 (@YF7f.windows_WIN _))) Hmap).
Local Abbreviation windows_WIN1 := ((AR2 (AR1 (@YF7f.windows_WIN1 _))) Hmap).
Local Abbreviation frame_WIN1P := (AR2 (AR1 (@YF7f.frame_WIN1P _))).
Local Abbreviation frame_WIN1 := ((AR2 (AR1 (@YF7f.frame_WIN1 _))) Hmap).
Local Abbreviation AR4 f := (f LY IMG Hsp Nrange Hidx Hres) (only parsing).
Local Abbreviation WINP_not_high := (AR4 (AR3 (@YF7f.WINP_not_high _))).
Local Abbreviation WIN_not_high := ((AR4 (AR3 (@YF7f.WIN_not_high _))) Hmap).
Variables (mat0 : list word).
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 (0x53108 + D_2c4)) mem0 (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis U1 : tfx_unwind_spec.
Local Abbreviation all_disjoint_of_forall := (@YF7f.all_disjoint_of_forall).
Local Abbreviation img_rw_writable := ((AR1 (@YF7f.img_rw_writable)) idx res mb Hidx).
Local Abbreviation kept_of_frame := (@YF7f.kept_of_frame imgk W ly regs0 idx res mb Hidx).
Local Abbreviation SKEL_TAIL := (@YF7f.SKEL_TAIL imgk).
Local Abbreviation blocks_facts := (@YF7f.blocks_facts _ imgk ly LY IMG).
Local Abbreviation off_T := (AR6 (AR1 (@YF7f.off_T _))).
Local Abbreviation off_C := (AR6 (AR1 (@YF7f.off_C _))).
Local Abbreviation off_Q := (AR6 (AR1 (@YF7f.off_Q _))).
Local Abbreviation off_NB := (@YF7f.off_NB _ imgk ly LY IMG).
Local Abbreviation off_SB := (@YF7f.off_SB _ imgk ly LY IMG).
Local Abbreviation off_shadow := ((AR1 (@YF7f.off_shadow)) idx res mb Hidx).
Ltac off_by tac :=
first [ img_apply off_img_high; tac | img_apply off_T; tac | img_apply off_C; tac | img_apply off_Q; tac | img_apply off_NB; tac | img_apply off_SB; tac
| img_apply map_off_img; tac | img_apply off_shadow; tac
| unfold off_img; unfold TFX_IMG_LO; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; tac ].
Local Abbreviation DZONE := (@YF7f.DZONE imgk ly).
Variable DPOST : Z -> (word -> option byte) -> Prop.
Local Abbreviation DZONE_disj := ((AR4 (AR3 (@YF7f.DZONE_disj _))) Hmap Hmap_apart).
Local Abbreviation RFACTS := (AR1 (@YF7f.RFACTS)).
Local Abbreviation zone_lit := ((AR1 (@YF7f.zone_lit _)) LY IMG Hsp).
Local Abbreviation zone_irw := ((AR1 (@YF7f.zone_irw _)) LY IMG Hsp).
Local Abbreviation zone_T := ((AR1 (@YF7f.zone_T _)) idx res LY IMG Hsp Hidx Hres).
Local Abbreviation zone_C := ((AR1 (@YF7f.zone_C _)) idx res LY IMG Hsp Hidx Hres).
Local Abbreviation tail_ext_ok := (AR4 (AR0 (AR1 (@YF7f.tail_ext_ok _)))).
Local Abbreviation RFACTS_map := ((AR3 (@YF7f.RFACTS_map _)) LY IMG Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation AR5 f := (f imgk W ly regs0 mem0) (only parsing).
Local Abbreviation at_ST := (AR0 ((AR5 (@YF7f.at_ST _)) md0)).
Local Abbreviation memset_stretch := ((AR5 (@YF7f.memset_stretch _ _)) md0 n idx res mb Hsp Nrange Hidx Hres Hmap Hmap_apart mat0 DPOST).
Ltac clearM := try clear DPOST; try clear Hmap_apart; try clear Hmap.
Local Abbreviation AR7 f := (AR1 f mem0) (only parsing).
Local Abbreviation at_S := (AR0 (AR7 (@YF7f.at_S _))).
Local Abbreviation at_N := (AR0 (AR7 (@YF7f.at_N _))).
Local Abbreviation at_RETS := ((AR7 (@YF7f.at_RETS _)) ch).
Local Abbreviation pstable := (@YF7f.pstable).
Local Abbreviation stack_shaped := (@YF7f.stack_shaped).
Local Abbreviation window_present := ((AR1 (@YF7f.window_present)) idx res Hidx).
Local Abbreviation stack_present_of := ((AR0 (AR1 (@YF7f.stack_present_of _))) LY Hsp Hidx).
Local Abbreviation mid_not_WIN1P := (AR4 (AR3 (@YF7f.mid_not_WIN1P _))).
Local Abbreviation mid_not_WIN1 := ((AR4 (AR3 (@YF7f.mid_not_WIN1 _))) Hmap).
Local Abbreviation wins_ok := (@YF7f.wins_ok).
Local Abbreviation at_S_run_gen := ((AR0 (AR7 (@YF7f.at_S_run_gen _ _))) LY Hsp Hidx).
Local Abbreviation at_S_run_ecall_gen := ((AR0 (AR7 (@YF7f.at_S_run_ecall_gen _ _))) LY Hsp Hidx).
Local Abbreviation at_S_runP := (AR4 (AR0 (AR7 (@YF7f.at_S_runP _ _)))).
Local Abbreviation at_S_runM := ((AR4 (AR0 (AR7 (@YF7f.at_S_runM _ _)))) Hmap).
Local Abbreviation at_S_run_ecallP := (AR4 (AR0 (AR7 (@YF7f.at_S_run_ecallP _ _)))).
Local Abbreviation at_S_run_ecallM := ((AR4 (AR0 (AR7 (@YF7f.at_S_run_ecallM _ _)))) Hmap).
Local Abbreviation at_S_pin := (AR0 (AR7 (@YF7f.at_S_pin _))).
Local Abbreviation at_S_arm := (AR0 (AR7 (@YF7f.at_S_arm _))).
Local Abbreviation at_S_forget := (AR0 (AR7 (@YF7f.at_S_forget _))).
Local Abbreviation at_S_noconds := (AR0 (AR7 (@YF7f.at_S_noconds _))).
Local Abbreviation at_S_weaken := (AR0 (AR7 (@YF7f.at_S_weaken _))).
Local Abbreviation at_S_facts := (AR0 (AR7 (@YF7f.at_S_facts _))).
Local Abbreviation at_S_strengthen := (AR0 (AR7 (@YF7f.at_S_strengthen _))).
Local Abbreviation at_S_eq := (AR0 (AR7 (@YF7f.at_S_eq _))).
Local Abbreviation at_S_open := (AR0 (AR7 (@YF7f.at_S_open _))).
Local Abbreviation CSAVEDS := (@YF7f.CSAVEDS).
Local Abbreviation sv_denot_SOff0 := (@YF7f.sv_denot_SOff0).
Local Abbreviation at_S_ret := ((AR0 (AR7 (@YF7f.at_S_ret _))) Htp Hra Hsp Nrange Hidx Hres).
Local Abbreviation kept_of_frame2 := ((AR1 (@YF7f.kept_of_frame2)) idx res Hidx).
Local Abbreviation at_N_cont := ((AR0 (AR7 (@YF7f.at_N_cont _ _))) LY Hsp Hidx).
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
Local Abbreviation vis_present := ((AR5 (@YF7o.vis_present _)) idx res Hidx DPOST B S HARm).
Local Abbreviation in_thread_junk := (@YF7o.in_thread_junk ly B S).
Local Abbreviation in_sec_junk := (@YF7o.in_sec_junk ly B S).
Local Abbreviation in_as_junk := (@YF7o.in_as_junk ly B S).
Local Abbreviation junk_word := ((AR6 (AR5 (@YF7o.junk_word _))) DPOST B S HARm).
Local Abbreviation AR8 f := (f _ imgk W ly mem0 B S) (only parsing).
Local Abbreviation cell_sym := ((AR8 (@YF7o.cell_sym)) TS HARm).
Local Abbreviation cell_lit := ((AR8 (@YF7o.cell_lit)) TS HARm).
Local Abbreviation cell_state := ((AR8 (@YF7o.cell_state)) HARm).
Local Abbreviation In_acells_sec := (@YF7o.In_acells_sec ly B S).
Local Abbreviation sec_vals := (@YF7o.sec_vals _ imgk W ly mem0 idx res B S TS HARm Hidx_def Hres_def).
Local Abbreviation unwinding_val := ((AR8 (@YF7o.unwinding_val)) HARm).
Local Abbreviation rw_writable := ((AR1 (@YF7o.rw_writable)) idx res Hidx DPOST S).
Local Abbreviation val_mem_mod8 := ((AR5 (@YF7o.val_mem_mod8)) idx res Hidx DPOST S).
Local Abbreviation chunk_lit := (AR0 (AR5 (@YF7o.chunk_lit))).
Local Abbreviation chunk_lit_at := (AR0 (AR5 (@YF7o.chunk_lit_at))).
Local Abbreviation chunk_atom := ((AR0 (AR5 (@YF7o.chunk_atom))) Hidx DPOST S).
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
pose proof (at_S_forget Wx md X P ss W' c' k clob HR ltac:(img_try (unfold sHAV; (img_case; cbv); zlia)) eq_refl
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
unfold YF7f.SHBv, YF7f.Kv, YF7f.Uv, YF7f.SMv, YF7f.PBv, MALLOC_MAX,
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
Let m0 := mrestrict (w_H W) mem0.
Local Ltac reg_intro := unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
Local Ltac lit_region :=
reg_intro; split; [img_try (zlia)|]; split; [img_try (zlia)|]; split; [img_try (intros o Ho; zlia)|];
repeat (img_apply Forall_cons; [img_try (img_apply chunk_lit; [img_apply cell_lit; (img_case; vm_compute); img_refl | cbn; zlia | cbn; zlia]) |]); img_apply Forall_nil.
Local Ltac uoffs := unfold zone3, TFX_IMG_LO, kLowShadowBeg, o_sec, o_sec_chunks, o_sec_reserved, o_sec_n, o_sec_sorted, o_sec_stats, o_sec_mutex, o_comb_stats, TFX_INST, kPtrArrayResv, TFX_IMG_END in *.
Local Ltac junk_atom_chunk k j Hj :=
img_apply (chunk_atom _ _ 8 k 0 (j mod 2 ^ 64)); [img_try (rewrite Z.sub_0_r; img_apply Z_to_bv64_eq_mod; rewrite Z.mod_mod by zlia; img_refl)
| img_try (pose proof (Z.mod_pos_bound j (2 ^ 64)); zlia) | img_try (img_apply val_mem_mod8; first [img_exact Hj | rewrite Z.add_0_r; img_exact Hj]) | img_try (cbn; pose proof (Z.mod_pos_bound j (2 ^ 64)); zlia) | img_try (cbn; zlia)].
Lemma SREG0_ok : Forall (region_ok tfxsegs E0 m0) SREG0.
Proof.
pose proof high_facts as (hf1 & hf2 & hf3 & hf4 & hf5 & hf6 & hf7 & hf8 & hq1 & hq2 & hqa & hta & hsa & hca & hf9). pose proof size_facts as SZ.
pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). destruct Hsp as (S1 & S2 & S3 & S4).
ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kPtrArrayResv, t_cache, t_unwinding in hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hq1, hq2, T2, T4, T7.
pose proof tr_length as TL. pose proof (ts_inst B TS) as EI. pose proof sec_vals as (SV1 & SV2 & SV3).
unfold SREG0, REG0, lit1, lit4, lit8, lits8, atom8, atom8w, CTZ_TABLE, R_bsl.
cbn [firstn app map combine seq length Z.of_nat Pos.of_succ_nat Pos.succ fst snd Z.mul Z.add Pos.mul Pos.add].
unfold aSB, aSHB, aC, aT, aTOP, aJ0, aJ1, aJ2, aJ3, aJ4, aJ5, aJ6, aJ7, aJ8, aJ9, aI1, aI2, aI3, aQ, aRES, aNCH, aLEN, aR8.
img_apply Forall_cons.
{   img_apply (region_ok_stack tfxsegs E0 m0 2 sp0 (- ASTACK)); [img_try (rewrite E2; img_refl) | img_try (unfold ASTACK; zlia) | img_try (zlia) |].
intros a Ha. img_apply apresent_writable_off; [img_try (off_by ltac:(unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END, ASTACK in *; zlia)) | img_try (img_apply Hpres0; img_exact Ha)]. }
do 8 (img_apply Forall_cons; [img_try (lit_region)|]).
img_apply Forall_cons. {   reg_intro. split; [img_try (zlia)|]. split; [img_try (zlia)|]. split; [img_try (intros o Ho; zlia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply (chunk_atom 0 _ 8 34%nat 0 SB); [img_try (rewrite EaSB; unfold w64; f_equal; zlia) | img_try (unfold SB; zlia) | | img_try (unfold SB; cbn; zlia) | img_try (cbn; zlia)].
rewrite Z.add_0_l. replace (682872 + D_10c0) with (aeval B ly (AInst o_space)) by (img_try (cbn; rewrite (ts_inst B TS); img_refl)).
replace SB with (aeval B ly (ASp 0)) by (img_try (cbn; unfold SB; zlia)). img_apply cell_sym. img_case; vm_compute. all: img_refl. }
do 14 (img_apply Forall_cons; [img_try (lit_region)|]).
img_apply Forall_cons. {   reg_intro. split; [img_try (zlia)|]. split; [img_try (zlia)|]. split; [img_try (intros o Ho; zlia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply (chunk_atom 0 _ 8 47%nat 0 SHBv); [img_refl | img_try (unfold SHBv; zlia) | | img_try (unfold SHBv; cbn; zlia) | img_try (cbn; zlia)].
rewrite Z.add_0_l. img_apply cell_lit. img_case; vm_compute. all: img_refl. }
do 7 (img_apply Forall_cons; [img_try (lit_region)|]).
img_apply Forall_cons. {   reg_intro. split; [img_try (zlia)|]. split; [img_try (zlia)|]. split; [img_try (intros o Ho; zlia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply chunk_lit; [| img_try (cbn; zlia) | img_try (cbn; zlia)]. pose proof (cell_lit (0x5dd160 + D_10c0) 8 0 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))) as H8.
intros k Hk. rewrite (H8 k ltac:(img_try (zlia))). rewrite !le_byte_zero. img_refl. }
img_apply Forall_cons; [img_try (lit_region)|].
img_apply Forall_cons. {   reg_intro. unfold TFX_TP. split; [img_try (zlia)|]. split; [img_try (zlia)|]. split; [img_try (intros o Ho; zlia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply chunk_lit; [| img_try (unfold TFX_TSD; cbn; zlia) | img_try (cbn; zlia)].
replace ((6148432 + D_10c0) - 88) with (aeval B ly (ATp (-88))) by (img_try (cbn; rewrite (ts_tp B TS); img_refl)).
replace TFX_TSD with (aeval B ly (ATsd 0)) by (img_try (cbn; rewrite HTSD; unfold TFX_TSD; zlia)). img_apply cell_sym. img_case; vm_compute. all: img_refl. }
img_apply Forall_cons. {   reg_intro. unfold TFX_TSD. split; [img_try (zlia)|]. split; [img_try (zlia)|]. split; [img_try (intros o Ho; zlia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply (chunk_atom 0 _ 8 33%nat 0 (ly_C ly)); [img_try (rewrite EaC; unfold w64; f_equal; zlia) | img_try (zlia) | | img_try (cbn; zlia) | img_try (cbn; zlia)].
rewrite Z.add_0_l. replace (6284536 + D_10c0) with (aeval B ly (ATsd 0)) by (img_try (cbn; rewrite HTSD; img_refl)).
replace (ly_C ly) with (aeval B ly (AC 0)) by (img_try (cbn; zlia)). img_apply cell_sym. img_case; vm_compute. all: img_refl. }
img_apply Forall_cons. {   reg_intro. rewrite EaC. unfold w64. rewrite unsigned_lit_small by zlia.
split; [img_try (zlia)|]. split; [img_try (zlia)|]. split; [img_try (intros o Ho; zlia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_nil])].
- img_apply chunk_lit_at; [| img_try (cbn; zlia) | img_try (cbn; zlia)]. replace (ly_C ly + 8) with (aeval B ly (AC 8)) by img_refl. img_apply (cell_sym (AC 8) 4 (ANum 0)). img_case; vm_compute. all: img_refl.
- img_apply (chunk_atom _ _ 8 32%nat 0 T); [img_try (rewrite EaT; unfold w64; f_equal; zlia) | img_try (zlia) | | img_try (cbn; zlia) | img_try (cbn; zlia)].
replace (ly_C ly + 152) with (aeval B ly (AC 152)) by img_refl. replace T with (aeval B ly (AT 0)) by (img_try (cbn; unfold T; zlia)).
img_apply cell_sym. img_case; vm_compute. all: img_refl. }
img_apply Forall_cons. {   reg_intro. rewrite EaT. unfold w64. rewrite unsigned_lit_small by zlia.
split; [img_try (zlia)|]. split; [img_try (zlia)|]. split; [img_try (intros o Ho; zlia)|].
img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_cons; [|img_apply Forall_cons; [|img_apply Forall_nil]]])].
- img_apply (chunk_atom _ _ 8 33%nat 0 (ly_C ly)); [img_try (rewrite EaC; unfold w64; f_equal; zlia) | img_try (zlia) | | img_try (cbn; zlia) | img_try (cbn; zlia)].
replace (ly_T ly + 0) with (aeval B ly (AT 0)) by (img_try (cbn; zlia)). replace (ly_C ly) with (aeval B ly (AC 0)) by (img_try (cbn; zlia)). img_apply cell_sym. img_case; vm_compute. all: img_refl.
- img_apply (chunk_atom _ _ 8 35%nat 0 (ly_top ly)); [img_try (rewrite EaTOP; unfold w64; f_equal; zlia) | img_try (zlia) | | img_try (cbn; zlia) | img_try (cbn; zlia)].
replace (ly_T ly + 8) with (aeval B ly (AT 8)) by (img_try (cbn; zlia)). replace (ly_top ly) with (aeval B ly (ATop 0)) by (img_try (cbn; zlia)). img_apply cell_sym. img_case; vm_compute. all: img_refl.
- img_apply (chunk_atom _ _ 8 35%nat (- kStackSpan) (ly_top ly - kStackSpan)); [img_try (rewrite EaTOP; unfold w64; f_equal; zlia) | img_try (unfold kStackSpan; zlia) | | img_try (unfold kStackSpan; cbn; zlia) | img_try (cbn; zlia)].
replace (ly_T ly + 16) with (aeval B ly (AT 16)) by (img_try (cbn; zlia)). replace (ly_top ly - kStackSpan) with (aeval B ly (ATop (- kStackSpan))) by (img_try (cbn; zlia)).
img_apply cell_sym. img_case; vm_compute. all: img_refl.
- img_apply chunk_lit_at; [| img_try (cbn; zlia) | img_try (cbn; zlia)]. replace (ly_T ly + 40) with (aeval B ly (AT 40)) by (img_try (cbn; zlia)). img_apply (cell_sym (AT 40) 1 (ANum 0)). img_case; vm_compute. all: img_refl. }
img_apply Forall_cons. {   reg_intro. rewrite EaT. unfold w64. rewrite unsigned_lit_small by zlia.
split; [img_try (zlia)|]. split; [img_try (zlia)|]. split.
{ intros o Ho. img_apply apresent_writable_off; [img_try (off_by ltac:(unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; zlia)) |].
img_apply (vis_present (AT t_cache_stats) (t_stats - t_cache_stats)); [img_try (left; img_apply in_thread_junk; right; left; img_refl) | img_try (cbn; unfold t_cache_stats, t_stats, T in *; zlia) | img_try (off_by ltac:(unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; zlia)) ]. }
img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply (chunk_atom _ _ 8 37%nat 0 (j0 mod 2 ^ 64)); [img_try (rewrite Z.sub_0_r; img_apply Z_to_bv64_eq_mod; rewrite Z.mod_mod by zlia; img_refl)
| img_try (pose proof (Z.mod_pos_bound j0 (2 ^ 64)); zlia) | img_try (img_apply val_mem_mod8; img_exact Hj0) | img_try (cbn; pose proof (Z.mod_pos_bound j0 (2 ^ 64)); zlia) | img_try (cbn; zlia)]. }
img_apply Forall_cons. {   reg_intro. rewrite EaT. unfold w64. rewrite unsigned_lit_small by zlia. unfold t_unwinding.
split; [img_try (zlia)|]. split; [img_try (zlia)|]. split.
{ intros o Ho. img_apply apresent_writable_off; [img_try (off_by ltac:(unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; zlia)) |]. replace (ly_T ly + o) with (ly_T ly + 3168) by zlia.
pose proof unwinding_val as U.
eapply mbyte_off_apresent; [img_try (off_by ltac:(unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; zlia)) |]. unfold T, t_unwinding in U. rewrite <- (Z.add_0_r (ly_T ly + 3168)). img_exact (U 0%nat ltac:(img_try (zlia))). }
img_apply Forall_cons; [|img_try (img_apply Forall_nil)]. img_apply chunk_lit_at; [| img_try (cbn; zlia) | img_try (cbn; zlia)]. img_exact unwinding_val. }
img_apply Forall_cons. {   reg_intro. rewrite EaT. unfold w64. rewrite unsigned_lit_small by zlia.
split; [img_try (zlia)|]. split; [img_try (zlia)|]. split.
{ intros o Ho. img_apply apresent_writable_off; [img_try (off_by ltac:(unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; zlia)) |].
img_apply (vis_present (AT t_stats) (t_unwinding - t_stats)); [img_try (left; img_apply in_thread_junk; right; right; left; img_refl) | img_try (cbn; unfold t_stats, t_unwinding, T in *; zlia) | img_try (off_by ltac:(unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; zlia)) ]. }
img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_cons; [|img_apply Forall_nil]])].
- img_apply (chunk_atom _ _ 8 49%nat 0 (j1 mod 2 ^ 64)); [img_try (rewrite Z.sub_0_r; img_apply Z_to_bv64_eq_mod; rewrite Z.mod_mod by zlia; img_refl)
| img_try (pose proof (Z.mod_pos_bound j1 (2 ^ 64)); zlia) | img_try (img_apply val_mem_mod8; img_exact Hj1) | img_try (cbn; pose proof (Z.mod_pos_bound j1 (2 ^ 64)); zlia) | img_try (cbn; zlia)].
- img_apply (chunk_atom _ _ 8 50%nat 0 (j2 mod 2 ^ 64)); [img_try (rewrite Z.sub_0_r; img_apply Z_to_bv64_eq_mod; rewrite Z.mod_mod by zlia; img_refl)
| img_try (pose proof (Z.mod_pos_bound j2 (2 ^ 64)); zlia) | img_try (img_apply val_mem_mod8; img_exact Hj2) | img_try (cbn; pose proof (Z.mod_pos_bound j2 (2 ^ 64)); zlia) | img_try (cbn; zlia)].
- img_apply (chunk_atom _ _ 8 51%nat 0 (j3 mod 2 ^ 64)); [img_try (rewrite Z.sub_0_r; img_apply Z_to_bv64_eq_mod; rewrite Z.mod_mod by zlia; img_refl)
| img_try (pose proof (Z.mod_pos_bound j3 (2 ^ 64)); zlia) | img_try (img_apply val_mem_mod8; img_exact Hj3) | img_try (cbn; pose proof (Z.mod_pos_bound j3 (2 ^ 64)); zlia) | img_try (cbn; zlia)]. }
uoffs. cbn [Z.add Z.mul Z.sub Pos.add Pos.mul Pos.succ Pos.sub] in SV1, SV2, SV3, EI |- *.
img_apply Forall_cons. {   reg_intro. rewrite EaT. unfold w64. rewrite unsigned_lit_small by zlia.
split; [img_try (zlia)|]. split; [img_try (zlia)|]. split.
{ intros o Ho. img_apply apresent_writable_off; [img_try (off_by ltac:(unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; zlia)) |].
img_apply (vis_present (AT t_stats) (t_unwinding - t_stats)); [img_try (left; img_apply in_thread_junk; right; right; left; img_refl) | img_try (cbn; unfold t_stats, t_unwinding, T in *; zlia) | img_try (off_by ltac:(unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; zlia)) ]. }
img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_nil])].
- junk_atom_chunk 53%nat j4 Hj4.
- junk_atom_chunk 43%nat j5 Hj5. }
img_apply Forall_cons. {   reg_intro. rewrite EaT. unfold w64. rewrite unsigned_lit_small by zlia.
split; [img_try (zlia)|]. split; [img_try (zlia)|]. split.
{ intros o Ho. img_apply apresent_writable_off; [img_try (off_by ltac:(unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; zlia)) |].
img_apply (vis_present (AT t_stats) (t_unwinding - t_stats)); [img_try (left; img_apply in_thread_junk; right; right; left; img_refl) | img_try (cbn; unfold t_stats, t_unwinding, T in *; zlia) | img_try (off_by ltac:(unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; zlia)) ]. }
img_apply Forall_cons; [|img_try (img_apply Forall_nil)]. junk_atom_chunk 57%nat j9 Hj9. }
img_apply Forall_cons; [img_try (lit_region)|].
img_apply Forall_cons. {   reg_intro. split; [img_try (zlia)|]. split; [img_try (zlia)|]. split; [img_try (intros o Ho; zlia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply (chunk_atom 0 _ 8 39%nat 0 Qb); [img_try (rewrite EaQ; unfold w64; f_equal; zlia) | img_try (unfold Qb; zlia) | | img_try (unfold Qb; cbn; zlia) | img_try (cbn; zlia)].
rewrite Z.add_0_l. replace ((682840 + D_10c0) + 72) with (aeval B ly (AInst 72)) by (img_try (cbn; rewrite EI; img_refl)).
replace Qb with (aeval B ly (AQ 0)) by (img_try (cbn; unfold Qb; zlia)). img_apply cell_sym. img_case; vm_compute. all: img_refl. }
img_apply Forall_cons. {   reg_intro. split; [img_try (zlia)|]. split; [img_try (zlia)|]. split; [img_try (intros o Ho; zlia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply (chunk_atom 0 _ 8 39%nat 0 Qb); [img_try (rewrite EaQ; unfold w64; f_equal; zlia) | img_try (unfold Qb; zlia) | | img_try (unfold Qb; cbn; zlia) | img_try (cbn; zlia)].
rewrite Z.add_0_l. replace ((682840 + D_10c0) + 80) with (aeval B ly (AInst 80)) by (img_try (cbn; rewrite EI; img_refl)).
replace Qb with (aeval B ly (AQ 0)) by (img_try (cbn; unfold Qb; zlia)). img_apply cell_sym. img_case; vm_compute. all: img_refl. }
img_apply Forall_cons; [img_try (lit_region)|].
img_apply Forall_cons. {   reg_intro. split; [img_try (zlia)|]. split; [img_try (zlia)|]. split.
{ intros o Ho. img_apply rw_writable. zlia. }
img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply (chunk_atom 0 _ 8 40%nat 0 res); [img_try (rewrite EaRES; unfold w64; f_equal; zlia) | img_try (destruct Hres as [HR _]; unfold kMaxNumChunks in *; zlia) | img_try (rewrite Z.add_0_l; img_exact SV1) | img_try (cbn; destruct Hres as [HR _]; unfold kMaxNumChunks in *; zlia) | img_try (cbn; zlia)]. }
img_apply Forall_cons. {   reg_intro. split; [img_try (zlia)|]. split; [img_try (zlia)|]. split.
{ intros o Ho. img_apply rw_writable. zlia. }
img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply (chunk_atom 0 _ 8 41%nat 0 idx); [img_try (rewrite EaNCH; unfold w64; f_equal; zlia) | img_try (unfold kMaxNumChunks in *; zlia) | img_try (rewrite Z.add_0_l; img_exact SV2) | img_try (cbn; unfold kMaxNumChunks in *; zlia) | img_try (cbn; zlia)]. }
img_apply Forall_cons. {   reg_intro. split; [img_try (zlia)|]. split; [img_try (zlia)|]. split; [|img_try (img_apply Forall_nil)].
intros o Ho. img_apply rw_writable. zlia. }
img_apply Forall_cons. {   reg_intro. split; [img_try (zlia)|]. split; [img_try (zlia)|]. split.
{ intros o Ho. img_apply rw_writable. zlia. }
img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_cons; [|img_apply Forall_nil]])].
- junk_atom_chunk 58%nat i1 Hi1.
- junk_atom_chunk 59%nat i2 Hi2.
- junk_atom_chunk 60%nat i3 Hi3. }
img_apply Forall_cons. {   reg_intro. split; [img_try (zlia)|]. split; [img_try (zlia)|].
pose proof (cell_lit (0xa6e01 + D_10c0) 1 0 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))) as P1. pose proof (cell_lit (0xa6e02 + D_10c0) 2 0 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))) as P2.
assert (BY : forall k, (k < 4)%nat -> mbyte tfxsegs m0 (((682840 + D_10c0) + 680) + Z.of_nat k) = Some (Z_to_bv 8 0)).
{ intros [|[|[|[|k]]]] Hk; [| | | |img_try (zlia)].
- pose proof (SV3 0%nat ltac:(img_try (zlia))) as X. rewrite le_byte_zero in X. img_exact X.
- pose proof (P1 0%nat ltac:(img_try (zlia))) as X. rewrite le_byte_zero in X. img_exact X.
- pose proof (P2 0%nat ltac:(img_try (zlia))) as X. rewrite le_byte_zero in X. img_exact X.
- pose proof (P2 1%nat ltac:(img_try (zlia))) as X. rewrite le_byte_zero in X. img_exact X. }
split.
{ intros o Ho. img_apply rw_writable. zlia. }
img_apply Forall_cons; [|img_try (img_apply Forall_nil)]. img_apply chunk_lit; [| img_try (cbn; zlia) | img_try (cbn; zlia)].
intros k Hk. etransitivity; [img_try (img_exact (BY k Hk))|]. rewrite le_byte_zero. img_refl. }
img_apply Forall_cons. {   reg_intro. split; [img_try (zlia)|]. split; [img_try (zlia)|]. split.
{ intros o Ho. img_apply rw_writable. zlia. }
img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_nil])].
- junk_atom_chunk 44%nat j6 Hj6.
- junk_atom_chunk 54%nat j7 Hj7. }
img_apply Forall_cons; [img_try (lit_region)|]. img_apply Forall_cons; [img_try (lit_region)|]. img_apply Forall_cons; [img_try (lit_region)|]. img_apply Forall_cons; [img_try (lit_region)|].
img_apply Forall_cons. {
pose proof BSLv_range as HB. reg_intro. unfold aBSL. rewrite EaBSL. unfold w64. rewrite unsigned_lit_small by (img_try (clear - HB; unfold TFX_INST in *; zlia)).
split; [img_try (clear - HB; unfold TFX_INST in *; zlia)|]. split; [img_try (clear - HB; unfold TFX_INST in *; zlia)|]. split.
{ intros o Ho. img_apply rw_writable. clear - HB Ho. unfold TFX_INST in *. zlia. }
img_apply Forall_cons; [|img_try (img_apply Forall_nil)]. junk_atom_chunk 56%nat j8 Hj8. }
img_apply Forall_nil.
Qed.
End g.
End d.
