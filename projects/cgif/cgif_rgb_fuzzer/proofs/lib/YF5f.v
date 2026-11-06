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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF64 YF3v YF3w YF3x YF41 YF47 YF0a YF5k YF4b YF5t YF5u YF5v.
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
Local Abbreviation AR2 f := (f Nrange Hidx Hres) (only parsing).
Local Abbreviation AR3 f := (AR1 f n idx res mb) (only parsing).
Local Abbreviation ARb f := (AR2 f Hmap) (only parsing).
Local Abbreviation map_facts := (ARb (AR3 (@YF5k.map_facts _))).
Local Abbreviation map_zone := ((AR3 (@YF5k.map_zone _)) Nrange Hidx Hmap).
Local Abbreviation map_zoneN := (ARb (AR3 (@YF5k.map_zoneN _))).
Local Abbreviation map_in_band := ((AR3 (@YF5k.map_in_band _)) Nrange Hidx Hmap).
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
Local Abbreviation WIN1P_WINP := ((AR3 (@YF5k.WIN1P_WINP)) Hidx).
Local Abbreviation WIN1_WIN := ((AR3 (@YF5k.WIN1_WIN)) Hidx).
Local Abbreviation WIN1P_WIN1 := ((AR1 (@YF5k.WIN1P_WIN1)) n idx mb).
Local Abbreviation LGv_range := (@YF5k.LGv_range n Nrange).
Local Abbreviation BSLv_range := ((AR3 (@YF5k.BSLv_range)) Nrange Hidx).
Local Abbreviation WSKELP := (@YF5k.WSKELP imgk).
Local Abbreviation WSKEL1P := (@YF5k.WSKEL1P imgk).
Local Abbreviation WMAP := (@YF5k.WMAP).
Local Abbreviation WSKEL := (@YF5k.WSKEL imgk).
Local Abbreviation WSKEL1 := (@YF5k.WSKEL1 imgk).
Local Abbreviation win_sub := (@YF5k.win_sub).
Local Abbreviation win_sub_sound := (@YF5k.win_sub_sound ly regs0 idx res mb Hidx Hres).
Local Abbreviation in_win := (@YF5k.in_win).
Local Abbreviation AR5 f := (AR0 f LY IMG) (only parsing).
Local Abbreviation WSKELP_WINP := (AR2 (AR5 (AR1 (@YF5k.WSKELP_WINP _)))).
Local Abbreviation WSKEL1P_WIN1P := (AR2 (AR5 (AR1 (@YF5k.WSKEL1P_WIN1P _)))).
Local Abbreviation WMAP_WINM := (ARb (AR5 (AR1 (@YF5k.WMAP_WINM _)))).
Local Abbreviation WSKEL_WIN := (ARb (AR5 (AR1 (@YF5k.WSKEL_WIN _)))).
Local Abbreviation WSKEL1_WIN1 := (ARb (AR5 (AR1 (@YF5k.WSKEL1_WIN1 _)))).
Local Abbreviation windows_in := (@YF5k.windows_in ly regs0 idx res mb Hidx Hres).
Local Abbreviation windows_WINP := (AR2 (AR5 (AR1 (@YF5k.windows_WINP _)))).
Local Abbreviation windows_WIN1P := (AR2 (AR5 (AR1 (@YF5k.windows_WIN1P _)))).
Local Abbreviation windows_WIN := (ARb (AR5 (AR1 (@YF5k.windows_WIN _)))).
Local Abbreviation windows_WIN1 := (ARb (AR5 (AR1 (@YF5k.windows_WIN1 _)))).
Local Abbreviation frame_WIN1P := (AR2 (AR5 (AR1 (@YF5k.frame_WIN1P _)))).
Local Abbreviation frame_WIN1 := (ARb (AR5 (AR1 (@YF5k.frame_WIN1 _)))).
Local Abbreviation AR9 f := (f LY IMG Hsp) (only parsing).
Local Abbreviation WINP_not_high := (AR2 (AR9 (AR3 (@YF5k.WINP_not_high _)))).
Local Abbreviation WIN_not_high := (ARb (AR9 (AR3 (@YF5k.WIN_not_high _)))).
Variables (mat0 : list word).
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 (0x53104 + D_2c4)) mem0 (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis U1 : tfx_unwind_spec.
Local Abbreviation all_disjoint_of_forall := (@YF5k.all_disjoint_of_forall).
Local Abbreviation img_rw_writable := ((AR1 (@YF5k.img_rw_writable)) idx res mb Hidx).
Local Abbreviation kept_of_frame := (@YF5k.kept_of_frame imgk W ly regs0 idx res mb Hidx).
Local Abbreviation SKEL_TAIL := (@YF5k.SKEL_TAIL imgk).
Local Abbreviation blocks_facts := (@YF5k.blocks_facts _ imgk ly LY IMG).
Local Abbreviation off_T := (AR7 (AR1 (@YF5k.off_T _))).
Local Abbreviation off_C := (AR7 (AR1 (@YF5k.off_C _))).
Local Abbreviation off_Q := (AR7 (AR1 (@YF5k.off_Q _))).
Local Abbreviation off_NB := (@YF5k.off_NB _ imgk ly LY IMG).
Local Abbreviation off_SB := (@YF5k.off_SB _ imgk ly LY IMG).
Local Abbreviation off_shadow := ((AR1 (@YF5k.off_shadow)) idx res mb Hidx).
Ltac off_by tac :=
first [ img_apply off_img_high; tac | img_apply off_T; tac | img_apply off_C; tac | img_apply off_Q; tac | img_apply off_NB; tac | img_apply off_SB; tac
| img_apply map_off_img; tac | img_apply off_shadow; tac
| unfold off_img; unfold TFX_IMG_LO; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; tac ].
Local Abbreviation DZONE := (@YF5k.DZONE imgk ly).
Variable DPOST : Z -> (word -> option byte) -> Prop.
Local Abbreviation DZONE_disj := ((ARb (AR9 (AR3 (@YF5k.DZONE_disj _)))) Hmap_apart).
Local Abbreviation RFACTS := (AR1 (@YF5k.RFACTS)).
Local Abbreviation zone_lit := (AR9 (AR1 (@YF5k.zone_lit _))).
Local Abbreviation zone_irw := (AR9 (AR1 (@YF5k.zone_irw _))).
Local Abbreviation zone_T := ((AR9 ((AR1 (@YF5k.zone_T _)) idx res)) Hidx Hres).
Local Abbreviation zone_C := ((AR9 ((AR1 (@YF5k.zone_C _)) idx res)) Hidx Hres).
Local Abbreviation tail_ext_ok := (AR2 ((AR5 (AR1 (@YF5k.tail_ext_ok _))) Hsp)).
Local Abbreviation RFACTS_map := ((ARb ((AR3 (@YF5k.RFACTS_map _)) LY IMG)) Hmap_apart).
Local Abbreviation AR4 f := (f imgk W ly regs0 mem0) (only parsing).
Local Abbreviation at_ST := (AR0 ((AR4 (@YF5k.at_ST _)) md0)).
Local Abbreviation memset_stretch := ((ARb ((AR4 (@YF5k.memset_stretch _ _)) md0 n idx res mb Hsp)) Hmap_apart mat0 DPOST).
Ltac clearM := try clear DPOST; try clear Hmap_apart; try clear Hmap.
Local Abbreviation AR8 f := (AR1 f mem0) (only parsing).
Local Abbreviation at_S := (AR0 (AR8 (@YF5k.at_S _))).
Local Abbreviation at_N := (AR0 (AR8 (@YF5k.at_N _))).
Local Abbreviation at_RETS := (@YF5k.at_RETS _ regs0 mem0 imgk).
Local Abbreviation pstable := (@YF5k.pstable).
Local Abbreviation stack_shaped := (@YF5k.stack_shaped).
Local Abbreviation window_present := ((AR1 (@YF5k.window_present)) idx res Hidx).
Local Abbreviation stack_present_of := ((AR0 (AR1 (@YF5k.stack_present_of _))) LY Hsp Hidx).
Local Abbreviation mid_not_WIN1P := (AR2 (AR9 (AR3 (@YF5k.mid_not_WIN1P _)))).
Local Abbreviation mid_not_WIN1 := (ARb (AR9 (AR3 (@YF5k.mid_not_WIN1 _)))).
Local Abbreviation wins_ok := (@YF5k.wins_ok).
Local Abbreviation at_S_run_gen := ((AR0 (AR8 (@YF5k.at_S_run_gen _ _))) LY Hsp Hidx).
Local Abbreviation at_S_run_ecall_gen := ((AR0 (AR8 (@YF5k.at_S_run_ecall_gen _ _))) LY Hsp Hidx).
Local Abbreviation at_S_runP := (AR2 ((AR5 (AR8 (@YF5k.at_S_runP _ _))) Hsp)).
Local Abbreviation at_S_runM := (ARb ((AR5 (AR8 (@YF5k.at_S_runM _ _))) Hsp)).
Local Abbreviation at_S_run_ecallP := (AR2 ((AR5 (AR8 (@YF5k.at_S_run_ecallP _ _))) Hsp)).
Local Abbreviation at_S_run_ecallM := (ARb ((AR5 (AR8 (@YF5k.at_S_run_ecallM _ _))) Hsp)).
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
Local Abbreviation at_S_ret := (AR2 ((AR0 (AR8 (@YF5k.at_S_ret _))) Htp Hra Hsp)).
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
Local Abbreviation vis_present := ((AR4 (@YF5t.vis_present _)) idx res Hidx DPOST B S HARm).
Local Abbreviation in_thread_junk := (@YF5t.in_thread_junk ly B S).
Local Abbreviation in_sec_junk := (@YF5t.in_sec_junk ly B S).
Local Abbreviation in_as_junk := (@YF5t.in_as_junk ly B S).
Local Abbreviation junk_word := ((AR7 (AR4 (@YF5t.junk_word _))) DPOST B S HARm).
Local Abbreviation ARa f := (f _ imgk W ly mem0 B S) (only parsing).
Local Abbreviation cell_sym := ((ARa (@YF5t.cell_sym)) TS HARm).
Local Abbreviation cell_lit := ((ARa (@YF5t.cell_lit)) TS HARm).
Local Abbreviation cell_state := ((ARa (@YF5t.cell_state)) HARm).
Local Abbreviation In_acells_sec := (@YF5t.In_acells_sec ly B S).
Local Abbreviation sec_vals := (@YF5t.sec_vals _ imgk W ly mem0 idx res B S TS HARm Hidx_def Hres_def).
Local Abbreviation unwinding_val := ((ARa (@YF5t.unwinding_val)) HARm).
Local Abbreviation rw_writable := ((AR1 (@YF5t.rw_writable)) idx res Hidx DPOST S).
Local Abbreviation val_mem_mod8 := ((AR4 (@YF5t.val_mem_mod8)) idx res Hidx DPOST S).
Local Abbreviation chunk_lit := (AR0 (AR4 (@YF5t.chunk_lit))).
Local Abbreviation chunk_lit_at := (AR0 (AR4 (@YF5t.chunk_lit_at))).
Local Abbreviation chunk_atom := ((AR0 (AR4 (@YF5t.chunk_atom))) Hidx DPOST S).
Local Abbreviation AR6 f := (AR2 f Hpres0 DPOST B S TS HTSD HARm Hidx_def Hres_def Hj0 Hj1 Hj2 Hj3 Hj4 Hj5 Hj9 Hj6 Hj7 Hj8 Hi1 Hi2 Hi3) (only parsing).
Local Abbreviation SREG0_ok := (AR6 ((AR5 (AR4 (@YF5u.SREG0_ok _))) Hsp)).
Local Abbreviation PAIRS_ok := ((AR2 ((AR5 (AR4 (@YF5v.PAIRS_ok _))) Hsp)) DPOST S).
Local Abbreviation FACTS_ok := ((AR2 ((AR5 (AR4 (@YF5v.FACTS_ok _))) Hn Hsp)) DPOST S).
Local Abbreviation SEED_ok := (AR6 ((AR5 (AR4 (@YF5v.SEED_ok _ _))) Hn Htp Hsp)).
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
Definition PBUF (m : word -> option byte) : Prop :=
forall i, (i < length tr)%nat -> val_mem tfxsegs (mrestrict (w_H W) m) (sp0 - IFRAME + 16 + 8 * Z.of_nat i) 8 (nth i tr 0).
Lemma PBUF_stableP : pstable WIN1P PBUF.
Proof.
clearP. intros m m' FR HB i Hi. pose proof tr_length as LEN. pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7). destruct Hsp as (S1 & _).
pose proof (u64_range (getr regs0 2)) as U2.
eapply val_mem_frame; [|img_try (img_exact (HB i Hi))]. intros k Hk. img_apply FR.
rewrite unsigned_lit_small by (img_try (clear - Hi Hk LEN S1 T7 U2; numconst; unfold IFRAME, sp0 in *; zlia)).
img_apply mid_not_WIN1P. clear - Hi Hk LEN. unfold IFRAME. zlia.
Qed.
Lemma PBUF_stableM : pstable WIN1 PBUF.
Proof.
intros m m' FR HB i Hi. pose proof tr_length as LEN. pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7). destruct Hsp as (S1 & _).
pose proof (u64_range (getr regs0 2)) as U2.
eapply val_mem_frame; [|img_try (img_exact (HB i Hi))]. intros k Hk. img_apply FR.
rewrite unsigned_lit_small by (img_try (clear - Hi Hk LEN S1 T7 U2; numconst; unfold IFRAME, sp0 in *; zlia)).
img_apply mid_not_WIN1. clear - Hi Hk LEN. unfold IFRAME. zlia.
Qed.
Lemma seg0 : SRr tfxsegs W cfg0 (at_S W md0 WINP PBUF S_1).
Proof.
clearP. pose proof Hwx_tfa as Hwx. pose proof SEED_ok as HS.
pose proof Hsp as (Hlo & Hbot & Hhi & Hal).
pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
srr_run_to_sh tfxtbl_rtA_ok HS (0x5aea0 + D_2c4).
pose proof (st_ok_restrict_mkst tfxsegs (w_H W) E0 _ _ HS eq_refl) as Hshape; cbn [ss_pc] in Hshape.
rewrite Hshape.
eapply SRr_bind.
{ pose proof high_facts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15).
ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, ASAN_CEIL, kHighMemBeg, kHighMemEnd, kThreadObjSize, kPrimResvSize, kSpaceSize, kPtrArrayResv in F1, F2, F3, F4, F5, F6, F7, F8, F9, F10, T1, T2, T4, T7.
assert (U64 : forall r : bv 5, 0 <= bv_unsigned (getr regs0 r) < 2 ^ 64) by (img_try (intros r; img_apply u64_range)).
pose proof (U64 2%bv) as Usp.
rreg HS (2%bv : bv 5) R2. rewrite E2 in R2.
img_apply (U1 W ly (ms_regs ms) (ms_mem ms) _ (sp0 - 2128) (0x533a4 + D_2c4) sp0 (bv_unsigned (getr regs0 1)) (bv_unsigned (getr regs0 8)) ch LY IMG).
1:{ rreg HS (10%bv : bv 5) R10; rewrite R10, E2. unfold sp0. f_equal; zlia. }
1:{ rreg HS (11%bv : bv 5) R11; rewrite R11. img_refl. }
1:{ rreg HS (12%bv : bv 5) R12; rewrite R12, E2. unfold sp0. symmetry. img_apply Z_to_bv_bv_unsigned. }
1:{ rreg HS (13%bv : bv 5) R13; rewrite R13. img_refl. }
1:{ rreg HS (14%bv : bv 5) R14; rewrite R14. img_refl. }
1:{ rreg HS (15%bv : bv 5) R15; rewrite R15. img_refl. }
1:{ rreg HS (4%bv : bv 5) R4; rewrite R4. img_refl. }
1:{ rreg HS (1%bv : bv 5) R1; rewrite R1. img_apply ret_ok_even. img_refl. }
1:{ zlia. }
1:{ memv HS 1%nat 0%nat; [img_refl | img_refl | img_try (zlia)]. }
1:{ memv HS 6%nat 0%nat; [img_refl | img_refl | img_try (zlia)]. }
1:{ memv HS 7%nat 0%nat; [img_refl | img_refl | img_try (zlia)]. }
1:{ memv HS 34%nat 0%nat; [img_refl | img_refl | img_try (unfold TFX_TSD; zlia)]. }
1:{ memv HS 35%nat 0%nat; [img_refl | img_try (denot_tac) | img_try (zlia)]. }
1:{ memv HS 36%nat 1%nat; [img_try (addr_tac) | img_try (denot_tac) | img_try (zlia)]. }
1:{ memv HS 37%nat 3%nat; [img_try (addr_tac) | img_try (denot_tac) | img_try (zlia)]. }
1:{ memv HS 37%nat 1%nat; [img_try (addr_tac) | img_try (denot_tac) | img_try (zlia)]. }
1:{ memv HS 37%nat 2%nat; [img_try (addr_tac) | img_try (denot_tac) | img_try (zlia)]. }
1:{ memv HS 39%nat 0%nat; [img_try (addr_tac) | img_try (denot_tac) | img_try (zlia)]. }
1:{ eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 39 _ _ HS); [img_refl | img_try (addr_tac) | img_try (off_by ltac:(addr_tac)) ]. }
1:{ memv HS 21%nat 0%nat; [img_refl | img_refl | img_try (zlia)]. }
1:{ memv HS 22%nat 0%nat; [img_refl | img_refl | img_try (zlia)]. }
1:{ rewrite R2. rewrite unsigned_lit_small by addr_tac.
replace (bv_unsigned (getr regs0 2) + -2128) with (bv_unsigned (getr regs0 2) + (-133) * 16) by zlia.
rewrite Z_mod_plus_full. img_exact Hal. }
1:{ rewrite R2. rewrite unsigned_lit_small by addr_tac. addr_tac. }
1:{ intros a Ha. rewrite R2 in Ha. rewrite unsigned_lit_small in Ha by addr_tac.
eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 0 _ a HS); [img_refl | img_try (addr_tac) | img_try (off_by ltac:(addr_tac)) ]. }
1:{ unfold sp0. replace (bv_unsigned (getr regs0 2) - 2128) with (bv_unsigned (getr regs0 2) + (- 266) * 8) by zlia.
rewrite Z_mod_plus_full. img_apply (Znumtheory.Zdivide_mod). img_apply (Z.divide_trans _ 16); [img_try (exists 2; img_refl)|].
img_apply Znumtheory.Zmod_divide; [img_try (zlia) | img_try (img_exact Hal)]. }
1:{ addr_tac. }
1:{ right. rewrite R2. rewrite unsigned_lit_small by addr_tac. addr_tac. }
1:{ intros a Ha. eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 0 _ a HS); [img_refl | img_try (addr_tac) | img_try (off_by ltac:(addr_tac)) ]. }
1:{ addr_tac. }
1:{ rewrite R2. rewrite unsigned_lit_small by addr_tac. addr_tac. }
1:{ img_exact Hbot. }
1:{ img_exact Hhi. }
1:{ unfold sp0. img_apply (Znumtheory.Zdivide_mod). img_apply (Z.divide_trans _ 16); [img_try (exists 2; img_refl)|].
img_apply Znumtheory.Zmod_divide; [img_try (zlia) | img_try (img_exact Hal)]. }
1:{ img_apply val_mem_rdword; [img_try (img_apply u64_range)|]. memv HS 0%nat 11%nat;
[img_try (addr_tac) | img_try (cbn [sv_denot]; rewrite E1, Z.add_0_r; img_refl) | img_try (img_apply u64_range)]. }
1:{ img_apply val_mem_rdword; [img_try (img_apply u64_range)|]. memv HS 0%nat 10%nat;
[img_try (addr_tac) | img_try (cbn [sv_denot]; rewrite E8, Z.add_0_r; img_refl) | img_try (img_apply u64_range)]. }
1:{ img_exact Hra4096. }
destruct (sp0 + 16 <? ly_top ly) eqn:Hf0; [|img_try (img_exact Hch)].
destruct (bad_next sp0 (ly_top ly) (bv_unsigned (getr regs0 8))) eqn:Hb; [img_try (img_exact Hch)|].
destruct Hch as [H16 Hch']. split; [img_try (img_exact H16)|].
unfold bad_next in Hb. apply Bool.orb_false_iff in Hb as [Hb _]. apply Bool.orb_false_iff in Hb as [Hb1 Hb2].
apply Z.leb_gt in Hb1. apply Z.leb_gt in Hb2. apply Z.ltb_lt in Hf0.
eapply fpchain_ext2; [img_try (img_exact Hch') | img_try (zlia) |].
intros a va Ha1 Ha2 Hva. eapply rdword_ext; [|img_try (img_exact Hva)]. intros i Hi. img_apply aview_same.
img_apply (HF (Z_to_bv 64 (a + i))). intros Hw. rewrite unsigned_lit_small in Hw by zlia.
refine (WINP_not_high (a + i) _ (windows_WINP E0 (ss_mem S0) (a + i) (fun k _ => eq_refl) _ Hw)); [img_try (zlia) | img_try ((img_case; vm_compute); img_refl)]. }
intros W' c' Hle (-> & regs1 & mem1 & mat1 & -> & HP & Hfr & Hpr & Ht1 & Ht2 & Ht3). srr_norm_model.
rreg HS (2%bv : bv 5) R2. rewrite E2 in R2. rreg HS (1%bv : bv 5) R1.
assert (Usp : 0 <= bv_unsigned (getr regs0 2) < 2 ^ 64) by img_apply u64_range.
assert (Hfr' : forall x : word, ~ (sp0 - ASTACK <= bv_unsigned x < sp0) -> mem1 x = ms_mem ms x).
{ intros x Hx. rewrite R2 in Hfr. unfold UNW_STK, BST_SIZE in Hfr. rewrite unsigned_lit_small in Hfr by addr_tac.
img_apply Hfr; unfold sp0, ASTACK in *; zlia. }
jafter_call2 HS 80%nat regs1 (mrestrict (w_H W) mem1) HP (-64) (seq 0 57) HS1.
assert (Hfr'' : forall x : word, ~ (sp0 - ASTACK <= bv_unsigned x < sp0 - 64) -> mem1 x = ms_mem ms x).
{ intros x Hx. rewrite R2 in Hfr. unfold UNW_STK, BST_SIZE in Hfr. rewrite unsigned_lit_small in Hfr by addr_tac.
img_apply Hfr; unfold sp0, ASTACK in *; zlia. }
cbn [ms_mem restrict] in HS1.
lazymatch type of HS1 with Forall _ (?r0 :: ?tail) -> _ =>
assert (KEPT : Forall (region_kept tfxsegs E0 (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) mem1)) (r0 :: tail));
[ img_try (constructor;
[ eapply (kept_of_frame E0 _ _ (fun a => sp0 - ASTACK <= a < sp0 - 64) _ Hfr'' Hpr); cbn [base_val YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi];
rewrite E2; unfold zone3, TFX_IMG_LO, kLowShadowBeg, sp0, ASTACK, TFX_IMG_END, kHighMemBeg, kHighMemEnd in *; intros a Ha; cbn beta; [zlia | left; zlia]
| img_apply Forall_forall; intros r Hr;
apply (in_map skel) in Hr; replace (map skel tail) with SKEL_TAIL in Hr by ((img_case; vm_compute); img_refl);
pose proof (tail_ext_ok E0 r (fun k _ => eq_refl) Hr) as (X1 & X2 & X3 & X4 & X5 & X6);
eapply (kept_of_frame E0 _ _ (fun a => sp0 - ASTACK <= a < sp0) _ Hfr' Hpr); intros a Ha; cbn beta; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END in *;
[ clear - X1 X2 X3 Ha; zlia | clear - X4 Ha; zlia ] ])
| img_try (specialize (HS1 KEPT); clear KEPT) ]
end.
assert (PRES1 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem1 a).
{ intros a Ha. img_apply Hpr. eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 0 _ a HS); [img_refl | img_try (addr_tac) | img_try (off_by ltac:(addr_tac)) ]. }
set (En1 := havoc E0 80 (map (getr regs1) CLOB)) in HS1.
assert (HEn1 : forall k, (k < sHAV)%nat -> ew En1 k = ew E0 k) by (img_try (intros k Hk; (subst En1; cbv beta); img_apply ew_havoc_old; img_exact Hk)).
apply (st_ok_add_region _ _ _ (YQ0b.mkRegion (Some 2%nat) (- ASTACK) (- IFRAME) (- ASTACK) (- IFRAME) [])) in HS1;
[ | img_refl
| unfold YQ0b.region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem];
rewrite (HEn1 2%nat (ltHAV 2 eq_refl)), E2; unfold IFRAME;
split; [img_try (addr_tac)|]; split; [img_try (addr_tac)|]; split; [img_try (intros o Ho; img_apply apresent_writable_off; [off_by ltac:(addr_tac) | img_apply PRES1; addr_tac]) | img_try (constructor)]
| img_apply all_disjoint_of_forall; intros r' [<-|Hr'];
[ unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; unfold IFRAME; zlia
| apply (in_map skel) in Hr';
lazymatch type of Hr' with In _ (map skel ?tl) => replace (map skel tl) with SKEL_TAIL in Hr' by (img_try ((img_case; vm_compute); img_refl)) end;
pose proof (tail_ext_ok En1 r' HEn1 Hr') as (X1 & X2 & X3 & X4 & X5 & X6);
unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; rewrite (HEn1 2%nat (ltHAV 2 eq_refl)), E2;
unfold IFRAME, ASTACK in *; unfold sp0 in *; clear - X1; zlia ] ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1.
assert (OBJ0 : val_mem tfxsegs (mrestrict (w_H W) mem1) (sp0 - 2128) 8 (sp0 - 2112)).
{ eapply val_mem_frame; [img_try (intros k Hk; img_apply Hfr; rewrite ?R2, ?unsigned_lit_small by addr_tac; addr_tac)|].
memv HS 0%nat 2%nat; [img_try (addr_tac) | img_try (denot_tac) | img_try (addr_tac)]. }
assert (OBJ1 : val_mem tfxsegs (mrestrict (w_H W) mem1) (sp0 - 2120) 8 (Z.of_nat (length tr))).
{ replace (Z.of_nat (length tr)) with (Z.of_nat (length tr) + 2 ^ 32 * 0) by zlia.
pose proof tr_length as LEN.
img_apply val_mem_4_4; [img_try (zlia) | img_try (zlia) | |].
- eapply val_mem_addr; [img_try (img_exact Ht1) | img_try (addr_tac)].
- assert (Z8 : val_mem tfxsegs (mrestrict (w_H W) (ms_mem ms)) (sp0 - 2120) 8 0) by (img_try (memv HS 0%nat 1%nat; [img_try (addr_tac) | img_refl | img_try (zlia)])).
assert (Z4 : val_mem tfxsegs (mrestrict (w_H W) (ms_mem ms)) (sp0 - 2120 + 4) 4 0).
{ intros k Hk. replace (sp0 - 2120 + 4 + Z.of_nat k) with (sp0 - 2120 + Z.of_nat (4 + k)) by zlia.
rewrite (Z8 (4 + k)%nat ltac:(img_try (zlia))). rewrite !le_byte_zero. img_refl. }
eapply val_mem_frame; [img_try (intros k Hk; img_apply Hfr; rewrite ?R2, ?unsigned_lit_small by addr_tac; addr_tac)| img_try (img_exact Z4)]. }
apply (st_ok_add_region _ _ _ (YQ0b.mkRegion (Some 2%nat) (- 2128) (- 2112) 0 0
[YQ0b.mkChunk (- 2128) (CVal 8 (SOff 2 (- 2112))); YQ0b.mkChunk (- 2120) (CVal 8 (SOff aLEN 0))])) in HS1;
[ | img_refl
| unfold YQ0b.region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem];
rewrite (HEn1 2%nat (ltHAV 2 eq_refl)), E2;
split; [img_try (addr_tac)|]; split; [img_try (addr_tac)|]; split; [img_try (intros o Ho; zlia) |];
img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_nil])];
[ img_try (eapply (chunk_ok_val tfxsegs En1 _ _ (-2128) 8 (SOff 2 (-2112)) (sp0 - 2112));
[cbn [sv_denot]; rewrite (HEn1 2%nat (ltHAV 2 eq_refl)), E2; denot_tac | addr_tac | cbn; zlia | eapply val_mem_addr; [img_exact OBJ0 | addr_tac]])
| img_try (eapply (chunk_ok_val tfxsegs En1 _ _ (-2120) 8 (SOff aLEN 0) (Z.of_nat (length tr)));
[cbn [sv_denot]; rewrite (HEn1 aLEN (ltHAV aLEN eq_refl)); unfold aLEN; rewrite (eq_refl : ew E0 36 = w64 (Z.of_nat (length tr))); denot_tac
| pose proof tr_length; img_change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); zlia
| cbn; zlia | eapply val_mem_addr; [img_exact OBJ1 | addr_tac]]) ]
| img_apply all_disjoint_of_forall; intros r' [<-|[<-|Hr']];
[ unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; unfold IFRAME, ASTACK; zlia
| unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; zlia
| apply (in_map skel) in Hr';
lazymatch type of Hr' with In _ (map skel ?tl) => replace (map skel tl) with SKEL_TAIL in Hr' by (img_try ((img_case; vm_compute); img_refl)) end;
pose proof (tail_ext_ok En1 r' HEn1 Hr') as (X1 & X2 & X3 & X4 & X5 & X6);
unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; rewrite (HEn1 2%nat (ltHAV 2 eq_refl)), E2;
unfold IFRAME, ASTACK in *; unfold sp0 in *; clear - X1; zlia ] ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1.
rewrite <- (restrict_mkst_fx (w_H W)) in HS1. rewrite R1. clear HS. rename HS1 into HS.
lazymatch type of HS with st_ok _ _ ?ss _ => replace ss with S_1 in HS by (img_try ((img_case; vm_compute); img_refl)) end.
img_apply SRr_ret. split; [img_refl|].
lazymatch goal with |- context [mkCfg ?msf _] => exists msf, mat1, En1 end.
split; [img_refl|].
split. { split; [img_try (img_exact HEn1) | img_try ((subst En1; cbv beta); img_apply ed_havoc)]. }
split; [img_try (img_exact HS)|].
split. { intros x Hx. cbn [ms_mem mkst]. rewrite Hfr' by (img_try (intros Hs; img_apply Hx; left; img_exact Hs)). img_apply HF. intros Hw. img_apply Hx.
img_exact (windows_WINP E0 (ss_mem S0) _ (fun k _ => eq_refl) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Hw). }
split; [img_try (img_exact PRES1)|].
intros i Hi. cbn [ms_mem mkst]. img_exact (Ht2 i Hi).
Qed.
End g.
End d.
