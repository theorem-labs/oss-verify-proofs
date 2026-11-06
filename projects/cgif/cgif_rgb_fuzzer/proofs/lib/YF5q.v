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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK0v YK13 YQ0k YA09 YG0b YF06 YF05 YG08.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF48 YF4b YF4c YF0h YF5t YF5u YF5v YF5f.
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
Local Abbreviation tr_length := ((AR1 (@YF5k.tr_length)) ch idx res Hidx).
Local Abbreviation AR7 f := (f idx res LY IMG Hidx Hres) (only parsing).
Local Abbreviation high_facts := (AR7 (AR1 (@YF5k.high_facts _))).
Local Abbreviation stack_ivs := (@YF5k.stack_ivs _ ly regs0 idx res LY Hsp Hidx Hres).
Local Abbreviation HCX := (@YF5k.HCX _ ly LY).
Hypothesis Hpres0 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem0 a.
Hypothesis Hmap : mb mod 4096 = 0 /\ mzone mb MSv.
Hypothesis Hmap_apart :
zdisjoint (mb, MSv) (T, kThreadObjSize) /\ zdisjoint (mb, MSv) (ly_C ly, kCtxMapSize) /\
zdisjoint (mb, MSv) (ly_prim ly, kPrimResvSize) /\ zdisjoint (mb, MSv) (Qb, kPtrArrayResv) /\
zdisjoint (mb, MSv) (ly_NB ly, kNodesBlockSize) /\ zdisjoint (mb, MSv) (ly_SB ly, kStoreBlockSize) /\
zdisjoint (mb, MSv) (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly).
Local Abbreviation AR4 f := (AR1 f n idx res mb) (only parsing).
Local Abbreviation ARa f := (f Nrange Hidx Hres) (only parsing).
Local Abbreviation map_facts := ((ARa (AR4 (@YF5k.map_facts _))) Hmap).
Local Abbreviation map_zone := ((AR4 (@YF5k.map_zone _)) Nrange Hidx Hmap).
Local Abbreviation map_zoneN := ((ARa (AR4 (@YF5k.map_zoneN _))) Hmap).
Local Abbreviation map_in_band := ((AR4 (@YF5k.map_in_band _)) Nrange Hidx Hmap).
Local Abbreviation map_off_img := (@YF5k.map_off_img _ imgk n mb Hmap).
Local Abbreviation WINT := (@YF5k.WINT ly).
Local Abbreviation WINI := (@YF5k.WINI n imgk).
Local Abbreviation WINM := (@YF5k.WINM ly n idx mb).
Local Abbreviation WIN := ((AR1 (@YF5k.WIN)) n idx mb).
Local Abbreviation WINN := (AR1 (@YF5k.WINN)).
Local Abbreviation WINP := ((AR1 (@YF5k.WINP)) n).
Local Abbreviation WINP_WIN := ((AR1 (@YF5k.WINP_WIN)) n idx mb).
Local Abbreviation WIN1P := ((AR1 (@YF5k.WIN1P)) n).
Local Abbreviation WIN1 := ((AR1 (@YF5k.WIN1)) n idx mb).
Local Abbreviation WIN1P_WINP := ((AR4 (@YF5k.WIN1P_WINP)) Hidx).
Local Abbreviation WIN1_WIN := ((AR4 (@YF5k.WIN1_WIN)) Hidx).
Local Abbreviation WIN1P_WIN1 := ((AR1 (@YF5k.WIN1P_WIN1)) n idx mb).
Local Abbreviation LGv_range := (@YF5k.LGv_range n Nrange).
Local Abbreviation BSLv_range := ((AR4 (@YF5k.BSLv_range)) Nrange Hidx).
Local Abbreviation WSKELP := (@YF5k.WSKELP imgk).
Local Abbreviation WSKEL1P := (@YF5k.WSKEL1P imgk).
Local Abbreviation WMAP := (@YF5k.WMAP).
Local Abbreviation WSKEL := (@YF5k.WSKEL imgk).
Local Abbreviation WSKEL1 := (@YF5k.WSKEL1 imgk).
Local Abbreviation win_sub := (@YF5k.win_sub).
Local Abbreviation ARb f := (f idx res mb) (only parsing).
Local Abbreviation win_sub_sound := ((ARb (@YF5k.win_sub_sound ly regs0)) Hidx Hres).
Local Abbreviation in_win := (@YF5k.in_win).
Local Abbreviation AR3 f := (AR0 f LY IMG Nrange Hidx Hres) (only parsing).
Local Abbreviation WSKELP_WINP := (AR3 (AR1 (@YF5k.WSKELP_WINP _))).
Local Abbreviation WSKEL1P_WIN1P := (AR3 (AR1 (@YF5k.WSKEL1P_WIN1P _))).
Local Abbreviation WMAP_WINM := ((AR3 (AR1 (@YF5k.WMAP_WINM _))) Hmap).
Local Abbreviation WSKEL_WIN := ((AR3 (AR1 (@YF5k.WSKEL_WIN _))) Hmap).
Local Abbreviation WSKEL1_WIN1 := ((AR3 (AR1 (@YF5k.WSKEL1_WIN1 _))) Hmap).
Local Abbreviation windows_in := ((ARb (@YF5k.windows_in ly regs0)) Hidx Hres).
Local Abbreviation windows_WINP := (AR3 (AR1 (@YF5k.windows_WINP _))).
Local Abbreviation windows_WIN1P := (AR3 (AR1 (@YF5k.windows_WIN1P _))).
Local Abbreviation windows_WIN := ((AR3 (AR1 (@YF5k.windows_WIN _))) Hmap).
Local Abbreviation windows_WIN1 := ((AR3 (AR1 (@YF5k.windows_WIN1 _))) Hmap).
Local Abbreviation frame_WIN1P := (AR3 (AR1 (@YF5k.frame_WIN1P _))).
Local Abbreviation frame_WIN1 := ((AR3 (AR1 (@YF5k.frame_WIN1 _))) Hmap).
Local Abbreviation AR2 f := (f LY IMG Hsp Nrange Hidx Hres) (only parsing).
Local Abbreviation WINP_not_high := (AR2 (AR4 (@YF5k.WINP_not_high _))).
Local Abbreviation WIN_not_high := ((AR2 (AR4 (@YF5k.WIN_not_high _))) Hmap).
Variables (mat0 : list word).
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 (0x53104 + D_2c4)) mem0 (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis U1 : tfx_unwind_spec.
Local Abbreviation all_disjoint_of_forall := (@YF5k.all_disjoint_of_forall).
Local Abbreviation img_rw_writable := ((ARb (AR1 (@YF5k.img_rw_writable))) Hidx).
Local Abbreviation AR9 f := (f imgk W ly) (only parsing).
Local Abbreviation kept_of_frame := ((ARb ((AR9 (@YF5k.kept_of_frame)) regs0)) Hidx).
Local Abbreviation SKEL_TAIL := (@YF5k.SKEL_TAIL imgk).
Local Abbreviation blocks_facts := (@YF5k.blocks_facts _ imgk ly LY IMG).
Local Abbreviation off_T := (AR7 (AR1 (@YF5k.off_T _))).
Local Abbreviation off_C := (AR7 (AR1 (@YF5k.off_C _))).
Local Abbreviation off_Q := (AR7 (AR1 (@YF5k.off_Q _))).
Local Abbreviation off_NB := (@YF5k.off_NB _ imgk ly LY IMG).
Local Abbreviation off_SB := (@YF5k.off_SB _ imgk ly LY IMG).
Local Abbreviation off_shadow := ((ARb (AR1 (@YF5k.off_shadow))) Hidx).
Ltac off_by tac :=
first [ img_apply off_img_high; tac | img_apply off_T; tac | img_apply off_C; tac | img_apply off_Q; tac | img_apply off_NB; tac | img_apply off_SB; tac
| img_apply map_off_img; tac | img_apply off_shadow; tac
| unfold off_img; unfold TFX_IMG_LO; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; tac ].
Local Abbreviation DZONE := (@YF5k.DZONE imgk ly).
Variable DPOST : Z -> (word -> option byte) -> Prop.
Local Abbreviation DZONE_disj := ((AR2 (AR4 (@YF5k.DZONE_disj _))) Hmap Hmap_apart).
Local Abbreviation RFACTS := (AR1 (@YF5k.RFACTS)).
Local Abbreviation zone_lit := ((AR1 (@YF5k.zone_lit _)) LY IMG Hsp).
Local Abbreviation zone_irw := ((AR1 (@YF5k.zone_irw _)) LY IMG Hsp).
Local Abbreviation zone_T := ((AR1 (@YF5k.zone_T _)) idx res LY IMG Hsp Hidx Hres).
Local Abbreviation zone_C := ((AR1 (@YF5k.zone_C _)) idx res LY IMG Hsp Hidx Hres).
Local Abbreviation tail_ext_ok := (AR2 (AR0 (AR1 (@YF5k.tail_ext_ok _)))).
Local Abbreviation RFACTS_map := ((ARa ((AR4 (@YF5k.RFACTS_map _)) LY IMG)) Hmap Hmap_apart).
Local Abbreviation AR5 f := (f imgk W ly regs0 mem0) (only parsing).
Local Abbreviation at_ST := (AR0 ((AR5 (@YF5k.at_ST _)) md0)).
Local Abbreviation memset_stretch := ((ARa ((ARb ((AR5 (@YF5k.memset_stretch _ _)) md0 n)) Hsp)) Hmap Hmap_apart mat0 DPOST).
Ltac clearM := try clear DPOST; try clear Hmap_apart; try clear Hmap.
Local Abbreviation AR8 f := (AR1 f mem0) (only parsing).
Local Abbreviation at_S := (AR0 (AR8 (@YF5k.at_S _))).
Local Abbreviation at_N := (AR0 (AR8 (@YF5k.at_N _))).
Local Abbreviation at_RETS := (@YF5k.at_RETS _ regs0 mem0 imgk).
Local Abbreviation pstable := (@YF5k.pstable).
Local Abbreviation stack_shaped := (@YF5k.stack_shaped).
Local Abbreviation window_present := ((AR1 (@YF5k.window_present)) idx res Hidx).
Local Abbreviation stack_present_of := ((AR0 (AR1 (@YF5k.stack_present_of _))) LY Hsp Hidx).
Local Abbreviation mid_not_WIN1P := (AR2 (AR4 (@YF5k.mid_not_WIN1P _))).
Local Abbreviation mid_not_WIN1 := ((AR2 (AR4 (@YF5k.mid_not_WIN1 _))) Hmap).
Local Abbreviation wins_ok := (@YF5k.wins_ok).
Local Abbreviation at_S_run_gen := ((AR0 (AR8 (@YF5k.at_S_run_gen _ _))) LY Hsp Hidx).
Local Abbreviation at_S_run_ecall_gen := ((AR0 (AR8 (@YF5k.at_S_run_ecall_gen _ _))) LY Hsp Hidx).
Local Abbreviation at_S_runP := (AR2 (AR0 (AR8 (@YF5k.at_S_runP _ _)))).
Local Abbreviation at_S_runM := ((AR2 (AR0 (AR8 (@YF5k.at_S_runM _ _)))) Hmap).
Local Abbreviation at_S_run_ecallP := (AR2 (AR0 (AR8 (@YF5k.at_S_run_ecallP _ _)))).
Local Abbreviation at_S_run_ecallM := ((AR2 (AR0 (AR8 (@YF5k.at_S_run_ecallM _ _)))) Hmap).
Local Abbreviation at_S_pin := (AR0 (AR8 (@YF5k.at_S_pin _))).
Local Abbreviation at_S_arm := (AR0 (AR8 (@YF5k.at_S_arm _))).
Local Abbreviation at_S_forget := (AR0 (AR8 (@YF5k.at_S_forget _))).
Local Abbreviation at_S_noconds := (AR0 (AR8 (@YF5k.at_S_noconds _))).
Local Abbreviation at_S_weaken := (AR0 (AR8 (@YF5k.at_S_weaken _))).
Local Abbreviation at_S_facts := (AR0 (AR8 (@YF5k.at_S_facts _))).
Local Abbreviation at_S_strengthen := (AR0 (AR8 (@YF5k.at_S_strengthen _))).
Local Abbreviation at_S_eq := (AR0 (AR8 (@YF5k.at_S_eq _))).
Local Abbreviation at_S_open := (AR0 (AR8 (@YF5k.at_S_open _))).
Local Abbreviation CSAVEDS := (@YF5k.CSAVEDS).
Local Abbreviation sv_denot_SOff0 := (@YF5k.sv_denot_SOff0).
Local Abbreviation at_S_ret := (ARa ((AR0 (AR8 (@YF5k.at_S_ret _))) Htp Hra Hsp)).
Local Abbreviation kept_of_frame2 := ((AR1 (@YF5k.kept_of_frame2)) idx res Hidx).
Local Abbreviation at_N_cont := ((AR0 (AR8 (@YF5k.at_N_cont _ _))) LY Hsp Hidx).
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
Local Abbreviation vis_present := ((AR5 (@YF5t.vis_present _)) idx res Hidx DPOST B S HARm).
Local Abbreviation in_thread_junk := (@YF5t.in_thread_junk ly B S).
Local Abbreviation in_sec_junk := (@YF5t.in_sec_junk ly B S).
Local Abbreviation in_as_junk := (@YF5t.in_as_junk ly B S).
Local Abbreviation junk_word := ((AR7 (AR5 (@YF5t.junk_word _))) DPOST B S HARm).
Local Abbreviation cell_sym := ((AR9 (@YF5t.cell_sym _)) mem0 B S TS HARm).
Local Abbreviation cell_lit := ((AR9 (@YF5t.cell_lit _)) mem0 B S TS HARm).
Local Abbreviation cell_state := ((AR9 (@YF5t.cell_state _)) mem0 B S HARm).
Local Abbreviation In_acells_sec := (@YF5t.In_acells_sec ly B S).
Local Abbreviation sec_vals := ((AR9 (@YF5t.sec_vals _)) mem0 idx res B S TS HARm Hidx_def Hres_def).
Local Abbreviation unwinding_val := ((AR9 (@YF5t.unwinding_val _)) mem0 B S HARm).
Local Abbreviation rw_writable := ((AR1 (@YF5t.rw_writable)) idx res Hidx DPOST S).
Local Abbreviation val_mem_mod8 := ((AR5 (@YF5t.val_mem_mod8)) idx res Hidx DPOST S).
Local Abbreviation chunk_lit := (AR0 (AR5 (@YF5t.chunk_lit))).
Local Abbreviation chunk_lit_at := (AR0 (AR5 (@YF5t.chunk_lit_at))).
Local Abbreviation chunk_atom := ((AR0 (AR5 (@YF5t.chunk_atom))) Hidx DPOST S).
Local Abbreviation AR6 f := (f DPOST B S TS HTSD HARm Hidx_def Hres_def Hj0 Hj1 Hj2 Hj3 Hj4 Hj5 Hj9 Hj6 Hj7 Hj8 Hi1 Hi2 Hi3) (only parsing).
Local Abbreviation SREG0_ok := (AR6 ((AR2 (AR0 (AR5 (@YF5u.SREG0_ok _)))) Hpres0)).
Local Abbreviation PAIRS_ok := ((AR2 (AR0 (AR5 (@YF5v.PAIRS_ok _)))) DPOST S).
Local Abbreviation FACTS_ok := ((ARa ((AR0 (AR5 (@YF5v.FACTS_ok _))) LY IMG Hn Hsp)) DPOST S).
Local Abbreviation SEED_ok := (AR6 ((ARa ((AR0 (AR5 (@YF5v.SEED_ok _ _))) LY IMG Hn Htp Hsp)) Hpres0)).
Local Abbreviation PBUF := ((AR9 (@YF5f.PBUF)) regs0 ch).
Local Abbreviation PBUF_stableP := (AR2 (ARb ((AR9 (@YF5f.PBUF_stableP _)) regs0 n ch))).
Local Abbreviation PBUF_stableM := ((AR2 (ARb ((AR9 (@YF5f.PBUF_stableM _)) regs0 n ch))) Hmap).
Local Abbreviation seg0 := (AR6 ((ARa ((AR0 ((AR5 (@YF5f.seg0 _ _)) md0)) LY IMG Hn Htp Hra4096 Hsp Hch)) Hpres0 mat0 U1)).
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
Definition SHLO (A : Z) : Z := shadow_addr A / 4096 * 4096.
Definition SHHI (A : Z) : Z := (shadow_addr A + MSv / 8 + 4095) / 4096 * 4096.
Lemma SH_hull : forall A, SHLO A <= shadow_addr A /\ shadow_addr A + MSv / 8 <= SHHI A /\ SHHI A - SHLO A <= MSv / 8 + 8192 /\
SHLO A mod 4096 = 0 /\ SHHI A mod 4096 = 0 /\ SHLO A <= SHHI A.
Proof.
clearP. intros A. pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & Z9 & _). unfold SHLO, SHHI.
pose proof (Z.div_mod (shadow_addr A) 4096 ltac:(img_try (zlia))) as D1. pose proof (Z.mod_pos_bound (shadow_addr A) 4096 ltac:(img_try (zlia))) as B1.
pose proof (Z.div_mod (shadow_addr A + MSv / 8 + 4095) 4096 ltac:(img_try (zlia))) as D2. pose proof (Z.mod_pos_bound (shadow_addr A + MSv / 8 + 4095) 4096 ltac:(img_try (zlia))) as B2.
repeat split; first [img_apply Z_mod_mult | zlia].
Qed.
Lemma lit_m1 : Z_to_bv 64 18446744073709551615 = Z_to_bv 64 (-1). Proof. clear. img_apply bv_eq. img_refl. Qed.
Lemma lit_enomem : Z_to_bv 64 ENOMEM_RETv = errno_ret ENOMEM. Proof. clear. unfold errno_ret, ENOMEM, ENOMEM_RETv. img_apply bv_eq. img_refl. Qed.
Lemma nores34 : mmap_noreserve_b (Z_to_bv 64 34) = false. Proof. clear. img_refl. Qed.
Lemma core34 : mmap_flags_core (Z_to_bv 64 34) = 34. Proof. clear. img_refl. Qed.
Lemma pru_MS : page_round_up_Z MSv = MSv.
Proof.
clearP. pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & Z9 & _). unfold page_round_up_Z, page_size.
apply Z.mod_divide in Z9 as [q Hq]; [|img_try (zlia)]. rewrite Hq. replace (q * 4096 + 4096 - 1) with (4095 + q * 4096) by zlia.
rewrite Z.div_add by zlia. img_change (4095 / 4096) with 0. zlia.
Qed.
Lemma grant_anon_shape : forall (a n : word) md,
vm_maps (m_vmmaps (grant_md true (Z_to_bv 64 34) a n md)) = (a, n) :: vm_maps (m_vmmaps md) /\
vm_reserved (m_vmmaps (grant_md true (Z_to_bv 64 34) a n md)) = vm_reserved (m_vmmaps md) /\
vm_limit (m_vmmaps (grant_md true (Z_to_bv 64 34) a n md)) = vm_limit (m_vmmaps md) /\
vm_mmap_base (m_vmmaps (grant_md true (Z_to_bv 64 34) a n md)) = vm_mmap_base (m_vmmaps md) /\
grant_md true (Z_to_bv 64 34) a n md = mmap_model a n md.
Proof. clear. intros a n md. unfold grant_md, with_mmap_backing, mmap_model. rewrite nores34. destruct md as [fd [maps lazy mat] io fs pr lim tm sg sc]. cbn. destruct maps; cbn. repeat split; img_refl. Qed.
Lemma Hcut_out : forall (Hh : word -> bool) lo hi (a : word), ~ (lo <= bv_unsigned a < hi) -> Hcut Hh lo hi a = Hh a.
Proof.
clear. intros Hh lo hi a Ha. unfold Hcut. destruct (Z.leb_spec lo (bv_unsigned a)); destruct (Z.ltb_spec (bv_unsigned a) hi); cbn [andb negb]; try (exfalso; zlia);
rewrite ?andb_true_r, ?andb_false_r; try img_refl; exfalso; img_apply Ha; zlia.
Qed.
Lemma slackS : forall md (Wx : world tfxsegs) k,
AR tfxsegs B ly S W mem0 md0 -> aregime S   -> ALedger tfxsegs ly S md0 -> vm_limit (m_vmmaps md) = vm_limit (m_vmmaps md0) ->
eager_used md <= eager_used md0 + k -> A_bytes (w_A Wx) <= A_bytes (w_A W) + k -> 0 <= k <= 2 ^ 30 ->
eager_used md + A_bytes (w_A Wx) + 2 ^ 36 <= vm_limit (m_vmmaps md).
Proof.
clearP. intros md Wx k HAR HREG L LIM EG AB Hk. pose proof (vm_budget_slack _ S (am_wf B ly S _ HARm) (aregime_to_mid S HREG) (qtight_qloose S HQT)) as VB. unfold VM_SLACK in VB.
pose proof (al_eager _ _ _ _ _ (am_wf B ly S _ HARm) L) as AE  . pose proof (al_limit _ _ _ _ L) as AL.
pose proof (proj1 (proj2 (proj2 HAR))) as [AB0 _]  .
rewrite LIM, AL. clear - VB AE EG AB Hk AB0. zlia.
Qed.
Lemma S_N_facts : ss_pc S_N = (0x64c88 + D_2c4) /\ sr_get (ss_regs S_N) 17%bv = SLit 222 /\ sr_get (ss_regs S_N) 10%bv = SLit 0 /\ sr_get (ss_regs S_N) 11%bv = SOff aMS 0 /\
sr_get (ss_regs S_N) 12%bv = SLit 3 /\ sr_get (ss_regs S_N) 13%bv = SLit 34 /\ sr_get (ss_regs S_N) 14%bv = SLit 18446744073709551615 /\ sr_get (ss_regs S_N) 15%bv = SLit 0 /\
no_cdata (ss_mem S_N) = true.
Proof. clear. img_case; vm_compute. all: repeat split; img_refl. Qed.
Lemma S_N_ext64 : forall (E' : env), env_agree sHAV E0 E' ->
forall r a, In r (ss_mem S_N) -> base_val E' (YQ0b.r_base r) + YQ0b.r_lo r <= a < base_val E' (YQ0b.r_base r) + YQ0b.r_hi r -> 0 <= a < 2 ^ 64.
Proof.
clearP. intros E' [HE _] r a Hr Ha. pose proof (lo_top ly LY) as (_ & _ & _ & T4 & _ & _ & T7). destruct Hsp as (S1 & _ & S3 & _). pose proof (u64_range (getr regs0 2)) as U2.
lazymatch type of Hr with In _ ?l =>
let m3 := img_ev (firstn 3 l) in let tl3 := img_ev (skipn 3 l) in
assert (SPLIT : In r m3 \/ In (skel r) SKEL_TAIL)
by (img_try (img_change l with (m3 ++ tl3) in Hr; apply in_app_iff in Hr as [Hr|Hr]; [img_try (left; img_exact Hr) | img_try (right)];
apply (in_map skel) in Hr; replace (map skel tl3) with SKEL_TAIL in Hr by ((img_case; vm_compute); img_refl); img_exact Hr)) end.
clear Hr. destruct SPLIT as [Hr|Hr].
- destruct Hr as [<-|[<-|[<-|[]]]]; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val] in Ha; rewrite (HE 2%nat ltac:(img_try (unfold sHAV; zlia))), E2 in Ha;
clear - Ha S1 S3 T4 T7 U2; unfold zone3, TFX_IMG_LO, kLowShadowBeg, ASTACK, IFRAME, kHighMemBeg, kHighMemEnd in *; try unfold sp0 in *; zlia.
- pose proof (tail_ext_ok E' r HE Hr) as (X1 & X2 & X3 & _). clear - Ha X2 X3. zlia.
Qed.
Lemma S_N_win64 : forall (E' : env) Hm, env_agree sHAV E0 E' -> mem_ok tfxsegs E' Hm (ss_mem S_N) ->
forall r a, In r (ss_mem S_N) -> base_val E' (YQ0b.r_base r) + YQ0b.r_wlo r <= a < base_val E' (YQ0b.r_base r) + YQ0b.r_whi r -> 0 <= a < 2 ^ 64.
Proof.
clearP. intros E' Hm HE (Hwf & _ & _) r a Hr Ha. pose proof (region_wf_facts r (regions_wf_In _ r Hwf Hr)) as (_ & WW & _).
img_apply (S_N_ext64 E' HE r a Hr). clear - Ha WW. zlia.
Qed.
Lemma nodeS : forall {RT : Type} (sN : astate) (K : Z -> itree astate RT) (Q : RT -> world tfxsegs -> config -> Prop) (c1 : config),
AR tfxsegs B ly S W mem0 md0 -> aregime S   ->
at_N W md0 WINP PBUF S_N W c1 -> AI tfxsegs (w_H W) (w_A W) (cfg_model c1) ->
(forall z, z = 0 \/ z = 1 -> aok sN (KMmapSec MSv) z) ->
(forall c', at_S W (cfg_model c1) WINP PBUF (resume S_N (SLit ENOMEM_RETv) (ss_mem S_N) (ss_facts S_N)) W c' ->
ALedger tfxsegs ly S (cfg_model c1) -> amwf (cfg_model c1) -> same_io md0 (cfg_model c1) ->
amrealE tfxsegs (K 0) W c' Q) ->
(forall (a : word) (W3 : world tfxsegs) (ms : machine_state) (E' : env),
let A := bv_unsigned a in let md2 := mmap_model a (w64 MSv) (cfg_model c1) in
grant_ok_na_pin (cfg_model c1) a MSv = true ->
ALedger tfxsegs ly S (cfg_model c1) -> amwf (cfg_model c1) ->
wle W W3 -> hsub (w_H W3) (w_H W) -> (forall x : word, w_H W x = false -> w_H W3 x = false) ->
w_A W3 = (SHLO A, SHHI A) :: (A, A + MSv) :: w_A W ->
(forall x : word, A <= bv_unsigned x < A + MSv -> w_H W3 x = false) ->
(forall x : word, SHLO A <= bv_unsigned x < SHHI A -> w_H W3 x = false) ->
(forall x : word, ~ (A <= bv_unsigned x < A + MSv) -> ~ (SHLO A <= bv_unsigned x < SHHI A) -> w_H W3 x = w_H W x) ->
AI tfxsegs (w_H W3) (w_A W3) md2 -> amwf md2 -> same_io md0 md2 -> eager_used md2 <= eager_used (cfg_model c1) + MSv ->
vm_maps (m_vmmaps md2) = (a, w64 MSv) :: vm_maps (m_vmmaps (cfg_model c1)) /\
vm_reserved (m_vmmaps md2) = vm_reserved (m_vmmaps (cfg_model c1)) /\
vm_limit (m_vmmaps md2) = vm_limit (m_vmmaps (cfg_model c1)) /\ vm_mmap_base (m_vmmaps md2) = vm_mmap_base (m_vmmaps (cfg_model c1)) ->
env_agree sHAV E0 E' -> st_ok_ecall tfxsegs E' S_N (restrict (w_H W) ms) ->
(forall x : word, ~ WINP (bv_unsigned x) -> ms_mem ms x = mem0 x) ->
(forall y, sp0 - ASTACK <= y < sp0 -> apresent (w_H W) (ms_mem ms) y) -> PBUF (ms_mem ms) ->
amreal tfxsegs (K 1) W3 (mkCfg (mkst (regupd (ms_regs ms) 10%bv a) (v_addi (Z_to_bv 64 (ss_pc S_N)) 4) (zfill a (w64 MSv) (ms_mem ms)) (seg_rom tfxsegs)) md2) Q) ->
same_io md0 (cfg_model c1) ->
exists (I : Type) (nx : I -> config) (bit : I -> Z) (sp : I -> bool) (i0 : I),
node_ok tfxsegs c1 I (fun _ => []) nx /\
(forall i, AI tfxsegs (w_H W) (w_A W) (cfg_model c1) -> AI tfxsegs (w_H W) (w_A W) (cfg_model (nx i))) /\
(forall i, aok sN (KMmapSec MSv) (bit i)) /\ sp i0 = false /\ bit i0 = 1 /\
(refusable (KMmapSec MSv) = true -> exists i1, sp i1 = false /\ bit i1 = 0) /\
(forall i, sp i = true -> AI tfxsegs (w_H W) (w_A W) (cfg_model (nx i)) -> srealizesM tfxsegs false (nx i) t_nil) /\
(forall i, (sp i = true \/ bit i <> 1) -> fo_dead tfxsegs c1 (nx i)) /\
(forall i, sp i = false -> if Z.eqb (bit i) 1 then amreal tfxsegs (K (bit i)) W (nx i) Q else amrealE tfxsegs (K (bit i)) W (nx i) Q).
Proof.
clearP. intros RT sN K Q c1 HAR Hev HN HAI Haok KEEP GRANT IO0.
pose proof size_facts as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & _).
pose proof HAR as (MA & L0 & BUD & MW & HS0).
destruct HN as (_ & ms & mat & E' & Ec & HE & HS & Hrv & MEQ & PRS & HPm).
set (mdN := with_vm_backing (m_vm_lazy md0) mat md0) in *.
assert (EcM : cfg_model c1 = mdN) by (img_try (rewrite Ec; img_refl)). rewrite EcM in *.
assert (LN : ALedger tfxsegs ly S mdN) by (img_try (img_exact (ALedger_same tfxsegs ly S md0 mdN L0 (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) (eager_used_wvb _ _)))).
assert (MWN : amwf mdN) by (img_try (img_exact (amwf_same md0 mdN (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) MW))).
assert (MWF0 : MWF mdN) by (img_try (img_apply (proj1 (amwf_MWF mdN)); img_exact (proj1 MWN))).
destruct (st_ok_ecall_shape_r tfxsegs (w_H W) E' S_N ms HS Hrv) as (regs & mem & Hms & Hregs & Hmem & HG).
assert (HEn : forall k, (k < sHAV)%nat -> ew E' k = ew E0 k) by (img_try (img_exact (proj1 HE))).
pose proof S_N_facts as (Hpc & H17 & H10 & H11 & H12 & H13 & H14 & H15 & Hnc).
assert (R17 : getr regs 17 = Z_to_bv 64 222) by (img_try (rewrite (Hregs 17%bv), H17; img_refl)).
assert (R10 : getr regs 10 = Z_to_bv 64 0) by (img_try (rewrite (Hregs 10%bv), H10; img_refl)).
assert (R11 : getr regs 11 = Z_to_bv 64 MSv).
{ rewrite (Hregs 11%bv), H11, sv_denot_SOff0. unfold aMS. rewrite (HEn 42%nat ltac:(img_try (unfold sHAV; zlia))). img_exact EaMS. }
assert (R12 : getr regs 12 = Z_to_bv 64 3) by (img_try (rewrite (Hregs 12%bv), H12; img_refl)).
assert (R13 : getr regs 13 = Z_to_bv 64 34) by (img_try (rewrite (Hregs 13%bv), H13; img_refl)).
assert (R14 : getr regs 14 = Z_to_bv 64 (-1)) by (img_try (rewrite (Hregs 14%bv), H14; cbn [sv_denot]; img_apply lit_m1)).
assert (R15 : getr regs 15 = Z_to_bv 64 0) by (img_try (rewrite (Hregs 15%bv), H15; img_refl)).
assert (MSB : 0 < MSv <= MALLOC_MAX + 4 * 4096) by (img_try (clear - Z8 Z1 Z2 Z3; unfold MALLOC_MAX in *; zlia)).
destruct (sec_grant_exists_AR B ly S _ mdN MSv HARm LN MWN ltac:(img_try (clear - MSB; unfold YF06.NOB, MALLOC_MAX in *; zlia))) as [a0 Ha0].
assert (SL0 : eager_used mdN + A_bytes (w_A W) + 2 ^ 36 <= vm_limit (m_vmmaps mdN)).
{ img_apply (slackS mdN W 0 HAR Hev L0); [img_try (unfold mdN; rewrite m_vmmaps_wvb; img_refl) | img_try (unfold mdN; rewrite eager_used_wvb; clear; zlia) | img_try (clear; zlia) | img_try (clear; zlia)]. }
assert (PER : forall a : word, grant_ok_na_pin mdN a MSv = true ->
(AI tfxsegs (w_H W) (w_A W) (grant_md true (Z_to_bv 64 34) a (w64 MSv) mdN) /\ MWF (grant_md true (Z_to_bv 64 34) a (w64 MSv) mdN)) /\
mmap_noreserve_backed_ok (Z_to_bv 64 34) mdN MSv = true /\
eager_used (grant_md true (Z_to_bv 64 34) a (w64 MSv) mdN) <= eager_used mdN + MSv /\
maps_nonempty (grant_md true (Z_to_bv 64 34) a (w64 MSv) mdN)).
{ intros a Ha. pose proof (YF48.grant_parts mdN a MSv Ha) as (Pal & Ppos & Pce & Prf & Ppl).
assert (CE : bv_unsigned a + page_round_up_Z MSv <= alloc_top (m_vmmaps mdN)) by (img_try (rewrite pru_MS; img_exact Pce)).
assert (PL' : region_free (vm_reserved (m_vmmaps mdN) ++ vm_maps (m_vmmaps mdN)) a (Z_to_bv 64 (page_round_up_Z MSv)) = true) by (img_try (rewrite pru_MS; img_exact Prf)).
assert (SL1 : eager_used mdN + A_bytes (w_A W) + page_round_up_Z MSv <= vm_limit (m_vmmaps mdN)) by (img_try (rewrite pru_MS; clear - SL0 MSB; unfold MALLOC_MAX in MSB; zlia)).
pose proof (commit_AI tfxsegs (w_H W) (w_A W) mdN true (Z_to_bv 64 34) a MSv HAI MWF0 nores34 ltac:(img_try (unfold page_size; img_exact Pal)) (proj1 MSB) CE PL' SL1) as [CG BUDg].
pose proof (commit_eager tfxsegs (w_H W) (w_A W) mdN true (Z_to_bv 64 34) a MSv HAI MWF0 nores34 ltac:(img_try (unfold page_size; img_exact Pal)) (proj1 MSB) CE PL' SL1) as EG.
pose proof (commit_nonempty true (Z_to_bv 64 34) a (Z_to_bv 64 (page_round_up_Z MSv)) mdN ltac:(img_try (rewrite pru_MS; unfold w64; rewrite unsigned_lit_small by (clear - MSB; unfold MALLOC_MAX in MSB; zlia); img_exact (proj1 MSB))) (proj2 MWN)) as NZg.
rewrite pru_MS in CG, BUDg, EG, NZg. fold (w64 MSv) in CG, EG, NZg. img_exact (conj CG (conj BUDg (conj EG NZg))). }
destruct (PER a0 Ha0) as (_ & BUD0 & _).
destruct (anon_node tfxsegs regs (Z_to_bv 64 (0x64c88 + D_2c4)) mem (seg_rom tfxsegs) mdN (Z_to_bv 64 34) MSv
(AI_halted _ _ _ _ HAI) R17 R10 R11 ltac:(img_try (clear - MSB; unfold MALLOC_MAX in MSB; zlia)) R12 R13 core34 R14 R15
ltac:(img_try (rewrite pru_MS; exists a0; img_exact Ha0)) ltac:(img_try (rewrite pru_MS; img_exact BUD0))) as (I & nx & bit & ga & i0 & iR & NODE & Bi0 & Bi1 & OUT).
rewrite pru_MS in OUT. fold (w64 MSv) in OUT.
assert (IOtr : forall m2, YG0b.same_io mdN m2 -> same_io md0 m2).
{ intros m2 (X1 & X2 & X3 & X4). destruct IO0 as (Y1 & Y2 & Y3 & Y4). unfold same_io. rewrite X1, X2, X3, X4. repeat split; assumption. }
exists I, nx, bit, (fun _ => false), i0.
split. { rewrite Ec, Hms, Hpc. img_exact NODE. }
split. { intros i _. destruct (OUT i) as (md_i & _ & _ & [[_ [-> ->]] | (_ & Hg & -> & ->)]); cbn [cfg_model];
[img_try (img_exact HAI) | img_try (img_exact (proj1 (proj1 (PER (ga i) Hg))))]. }
split. { intros i. img_apply Haok. destruct (OUT i) as (md_i & _ & _ & [[Bv _] | [Bv _]]); clear - Bv; zlia. }
split; [img_refl|]. split; [img_try (img_exact Bi0)|]. split; [img_try (intros _; exists iR; split; [img_refl | img_exact Bi1])|].
split; [img_try (intros i E; discriminate E)|].
split. { (* [comment removed for export] *)
intros i [E | Hb]; [discriminate E |].
destruct (OUT i) as (md_i & _ & _ & [[_ [NX _]] | (Bv & _ & _ & _)]); [| exfalso; exact (Hb Bv)].
destruct (OUT i0) as (md_0 & _ & _ & [[B0 _] | (_ & Hg0 & NX0 & _)]); [rewrite Bi0 in B0; discriminate B0 |].
assert (H222 : bv_unsigned (getr regs 17) = 222) by (img_try (rewrite R17; img_refl)).
assert (A0 : forall v : word, reg_get (regupd regs 10 v) (Z_to_bv 5 10) = v).
{ intros v. replace (Z_to_bv 5 10) with (10%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). img_apply regupd_same. }
rewrite Ec, Hms, Hpc.
img_apply (fo_dead_node tfxsegs (pend_at regs (Z_to_bv 64 (0x64c88 + D_2c4)) mem (seg_rom tfxsegs)) mdN (getr regs 17) I (fun _ => []) nx i0 i NODE eq_refl
(injected_family_off_mmap tfxsegs _ _ H222)).
- rewrite NX0. img_refl.
- rewrite NX0. cbn [cfg_ms ms_regs mkst]. rewrite A0, (refusal_b_mmap tfxsegs _ _ mdN _ H222).
img_exact (grant_na_pin_not_errno mdN (ga i0) MSv ltac:(img_try (clear - MSB; zlia)) Hg0).
- rewrite NX. img_refl.
- rewrite NX. cbn [cfg_ms ms_regs mkst]. rewrite A0. img_exact (mmap_enomem_refusal tfxsegs _ _ mdN H222). }
intros i _. destruct (OUT i) as (md_i & Hh_i & IO_i & [[Bv [NX MD]] | (Bv & Hg & NX & MD)]); rewrite Bv, NX; cbn [Z.eqb Pos.eqb]; rewrite MD in IO_i |- *.
-
img_apply KEEP; [| img_try (img_exact LN) | img_try (img_exact MWN) | img_try (img_exact IO0)].
pose proof (at_N_cont W W mdN WINP PBUF S_N (SLit ENOMEM_RETv) (errno_ret ENOMEM) (fun _ => False) mem ms E' HE HS Hrv MEQ PRS (hsub_refl _)
ltac:(img_try (cbn [sv_denot]; img_apply lit_enomem)) Hnc ltac:(img_try (intros x _; rewrite Hms; img_refl))
(fun r y Hr Hy => conj (fun f : False => f) (S_N_ext64 E' HE r y Hr Hy))
(fun r y Hr Hy => conj (fun f : False => f) (S_N_win64 E' _ HE Hmem r y Hr Hy))
(fun y _ (f : False) => f) ltac:(img_try (rewrite Hms in HPm; img_exact HPm))) as C.
rewrite Hms in C. cbn [ms_regs pend_at] in C. rewrite Hpc in C.
eapply at_S_weaken; [img_try (img_exact C) | img_try (intros y [Hy|[]]; img_exact Hy) | img_try (intros m Hm; img_exact Hm)].
-
set (a := ga i) in *. set (A := bv_unsigned a) in *.
destruct (PER a Hg) as ([AIg MWFg] & _ & EG & NZg).
pose proof (grant_anon_shape a (w64 MSv) mdN) as (SH1 & SH2 & SH3 & SH4 & SH5).
set (md2 := grant_md true (Z_to_bv 64 34) a (w64 MSv) mdN) in *.
pose proof (YF48.grant_parts mdN a MSv Hg) as (Pal & Ppos & Pce & Prf & Ppl).
fold A in Pal, Ppos, Pce.
pose proof (SH_hull A) as (U1' & U2 & U3 & U4 & U5 & U6).
assert (AL1 : A <= A + MSv) by (img_try (clear - MSB; zlia)).
assert (AL2 : A mod page_size = 0) by (img_try (unfold page_size; img_exact Pal)).
assert (AL3 : (A + MSv) mod page_size = 0).
{ unfold page_size. clear - Pal Z9. apply Z.mod_divide in Pal as [q' Hq]; [|img_try (zlia)]. apply Z.mod_divide in Z9 as [r' Hr]; [|img_try (zlia)]. rewrite Hq, Hr. img_apply Z.mod_divide; [img_try (zlia)|]. exists (q' + r'). zlia. }
destruct (allow_expose tfxsegs W md2 A (A + MSv) AL1 AL2 AL3 AIg ltac:(img_try (rewrite SH3; clear - EG SL0 MSB; unfold MALLOC_MAX in MSB; zlia)))
as (LE2 & A2 & AB2 & VIS2 & MON2 & AI2).
set (W2 := wallow tfxsegs W A (A + MSv) AL1 AL2 AL3) in *.
assert (SL2 : SHLO A mod page_size = 0) by (img_try (unfold page_size; img_exact U4)).
assert (SL3 : SHHI A mod page_size = 0) by (img_try (unfold page_size; img_exact U5)).
assert (BUD3 : eager_used md2 + A_bytes (w_A W2) + (SHHI A - SHLO A) <= vm_limit (m_vmmaps md2)).
{ rewrite SH3, AB2. assert (D8 : MSv / 8 <= MSv) by (img_try (img_apply Z.div_le_upper_bound; clear - MSB; zlia)). clear - EG SL0 MSB U3 D8. unfold MALLOC_MAX in MSB. zlia. }
destruct (allow_expose tfxsegs W2 md2 (SHLO A) (SHHI A) U6 SL2 SL3 AI2 BUD3)
as (LE3 & A3 & AB3 & VIS3 & MON3 & AI3).
set (W3 := wallow tfxsegs W2 (SHLO A) (SHHI A) U6 SL2 SL3) in *.
assert (MON : forall x : word, w_H W x = false -> w_H W3 x = false) by (img_try (intros x Hx; apply MON3, MON2, Hx)).
assert (SUB : hsub (w_H W3) (w_H W)).
{ intros x Hx. destruct (w_H W x) eqn:Ex; [img_refl|]. rewrite (MON x Ex) in Hx. discriminate Hx. }
eapply (amreal_world_le tfxsegs _ W W3); [img_try (img_exact (wle_trans _ _ _ _ LE2 LE3)) | img_try (intros _; img_exact AI3) |].
img_change (with_mmap_backing (Z_to_bv 64 34) a (w64 MSv) (mmap_model a (w64 MSv) mdN)) with md2.
pose proof (GRANT a W3 ms E' Hg LN MWN (wle_trans _ _ _ _ LE2 LE3) SUB MON) as G. cbv zeta in G. rewrite <- SH5 in G. fold md2 in G. fold A in G.
rewrite Hms in G. cbn [ms_regs ms_mem pend_at] in G. img_apply G; clear G.
+ rewrite A3, A2. img_refl.
+ intros x Hx. img_apply MON3. img_apply VIS2. img_exact Hx.
+ img_exact VIS3.
+ intros x N1 N2. unfold W3, W2, wallow. cbn [w_H]. rewrite (Hcut_out _ (SHLO A) (SHHI A) x) by img_exact N2. img_apply Hcut_out. img_exact N1.
+ img_exact AI3.
+ split; [img_try (img_apply (proj2 (amwf_MWF md2)); img_exact MWFg) | img_try (img_exact NZg)].
+ img_exact (IOtr _ IO_i).
+ img_exact EG.
+ rewrite SH1, SH2, SH3, SH4. repeat split; img_refl.
+ img_exact HE.
+ rewrite Hms in HS. img_exact HS.
+ intros x Hx. rewrite <- (MEQ x Hx), Hms. img_refl.
+ intros y Hy. rewrite Hms in PRS. img_exact (PRS y Hy).
+ rewrite Hms in HPm. img_exact HPm.
Qed.
End g.
End d.
