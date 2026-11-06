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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK0k.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF4b YF4c YF4d YF4f YF5t YF5u YF5v YF5f YF5l YF5m YF5i YF5j YF5n YF5r.
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
Local Abbreviation ARc f := (AR1 f n idx mb) (only parsing).
Local Abbreviation WIN := (ARc (@YF5k.WIN)).
Local Abbreviation WINN := (AR1 (@YF5k.WINN)).
Local Abbreviation ARi f := (AR1 f n) (only parsing).
Local Abbreviation WINP := (ARi (@YF5k.WINP)).
Local Abbreviation WINP_WIN := (ARc (@YF5k.WINP_WIN)).
Local Abbreviation WIN1P := (ARi (@YF5k.WIN1P)).
Local Abbreviation WIN1 := (ARc (@YF5k.WIN1)).
Local Abbreviation WIN1P_WINP := ((AR3 (@YF5k.WIN1P_WINP)) Hidx).
Local Abbreviation WIN1_WIN := ((AR3 (@YF5k.WIN1_WIN)) Hidx).
Local Abbreviation WIN1P_WIN1 := (ARc (@YF5k.WIN1P_WIN1)).
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
Local Abbreviation WIN1N := (ARi (@YF5l.WIN1N)).
Local Abbreviation WINPN := (ARi (@YF5l.WINPN)).
Local Abbreviation WSKEL1N := (@YF5l.WSKEL1N imgk).
Local Abbreviation WIN1N_WINPN := ((AR3 (@YF5l.WIN1N_WINPN)) Hidx).
Local Abbreviation windows_WIN1N := (ARd (ARa (AR1 (@YF5l.windows_WIN1N _)))).
Local Abbreviation mid_not_WIN1N := (AR2 (AR3 (@YF5l.mid_not_WIN1N _))).
Local Abbreviation at_S_runN := (AR2 (AR0 (AR7 (@YF5l.at_S_runN _ _)))).
Local Abbreviation PBUF_stableN := (AR2 (AR9 ((ARg (@YF5l.PBUF_stableN _)) regs0 n ch))).
Local Abbreviation at_S_val := (AR0 (AR7 (@YF5l.at_S_val _))).
Local Abbreviation memset_stretchW := ((ARd ((AR4 (@YF5l.memset_stretchW _)) md0 n idx res Hsp)) mat0 DPOST S).
Local Abbreviation at_S_memset := ((ARd ((AR0 ((AR4 (@YF5l.at_S_memset _)) md0)) Hsp)) mat0 DPOST S).
Local Abbreviation WIN1T := (ARc (@YF5l.WIN1T)).
Local Abbreviation WIN1T_WIN := (AR5 (AR3 (@YF5l.WIN1T_WIN _))).
Local Abbreviation windows_WIN1T := (AR5 (ARa (AR1 (@YF5l.windows_WIN1T _)))).
Local Abbreviation WIN1T_WIN1_aux := (AR5 (AR3 (@YF5l.WIN1T_WIN1_aux _))).
Local Abbreviation mid_not_WIN1T := (ARh (AR3 (@YF5l.mid_not_WIN1T _))).
Local Abbreviation at_S_runT := (ARh (AR0 (AR7 (@YF5l.at_S_runT _ _)))).
Local Abbreviation at_S_run_ecallT := (ARh (AR0 (AR7 (@YF5l.at_S_run_ecallT _ _)))).
Local Abbreviation PBUFW := ((AR1 (@YF5l.PBUFW)) ch).
Local Abbreviation PBUFW_stableT := (ARh (AR9 ((ARi (@YF5l.PBUFW_stableT _)) ch))).
Local Abbreviation WIN1S := (ARc (@YF5m.WIN1S)).
Local Abbreviation WSKEL1S := (@YF5m.WSKEL1S imgk).
Local Abbreviation WIN1S_WIN1T := (ARc (@YF5m.WIN1S_WIN1T)).
Local Abbreviation WIN1S_WIN := (AR5 (AR3 (@YF5m.WIN1S_WIN _))).
Local Abbreviation windows_WIN1S := (AR5 (ARa (AR1 (@YF5m.windows_WIN1S _)))).
Local Abbreviation mid_not_WIN1S := (ARh (AR3 (@YF5m.mid_not_WIN1S _))).
Local Abbreviation at_S_runS := (ARh (AR0 (AR7 (@YF5m.at_S_runS _ _)))).
Local Abbreviation at_S_run_ecallS := (ARh (AR0 (AR7 (@YF5m.at_S_run_ecallS _ _)))).
Local Abbreviation brun := (@YF5m.brun).
Local Abbreviation run_ok := (@YF5m.run_ok n mb).
Local Abbreviation PS := ((ARi (@YF5m.PS)) ch mb).
Local Abbreviation runs_not_WIN1S := (AR6 (AR3 (@YF5m.runs_not_WIN1S _))).
Local Abbreviation runs_not_stack := ((AR5 ((AR3 (@YF5m.runs_not_stack _)) LY Hsp)) Hmap_apart).
Local Abbreviation PS_stable := (AR6 (AR9 ((ARi (@YF5m.PS_stable _)) ch))).
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
Local Abbreviation WIN1R := ((ARi (@YF5m.WIN1R)) mb).
Local Abbreviation WSKEL1R := (@YF5m.WSKEL1R imgk).
Local Abbreviation WIN1R_WIN1S := (ARc (@YF5m.WIN1R_WIN1S)).
Local Abbreviation WIN1R_WIN := (AR5 (AR3 (@YF5m.WIN1R_WIN _))).
Local Abbreviation windows_WIN1R := (AR5 (ARa (AR1 (@YF5m.windows_WIN1R _)))).
Local Abbreviation mid_not_WIN1R := (ARh (AR3 (@YF5m.mid_not_WIN1R _))).
Local Abbreviation at_S_runR := (ARh (AR0 (AR7 (@YF5m.at_S_runR _ _)))).
Local Abbreviation at_S_run_ecallR := (ARh (AR0 (AR7 (@YF5m.at_S_run_ecallR _ _)))).
Local Abbreviation PSR := ((ARi (@YF5m.PSR)) ch mb).
Local Abbreviation rstable := ((ARi (@YF5m.rstable)) mb).
Local Abbreviation rstable_true := ((ARi (@YF5m.rstable_true)) mb).
Local Abbreviation PSR_stable := (AR6 (AR9 ((ARi (@YF5m.PSR_stable _)) ch))).
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
Local Abbreviation place_WIN := (ARc (@YF5i.place_WIN)).
Local Abbreviation SH0 := (@YF5i.SH0 n mb).
Local Abbreviation SH1 := (@YF5i.SH1 n mb).
Local Abbreviation SH2 := (@YF5i.SH2 n mb).
Local Abbreviation SH_ok := (AR5 (AR3 (@YF5i.SH_ok _))).
Local Abbreviation segG1 := (AR8 ((AR6 (AR0 ((AR4 (@YF5i.segG1 _ _)) md0))) mat0)).
Local Abbreviation RX_stableS := (ARc (@YF5j.RX_stableS)).
Local Abbreviation rstable_and := ((ARi (@YF5j.rstable_and)) mb).
Local Abbreviation pstable_and := (@YF5j.pstable_and).
Local Abbreviation PSR_stableS' := (AR6 (AR9 ((ARi (@YF5j.PSR_stableS' _)) ch))).
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
Local Abbreviation PSR_stableS := (AR6 (AR9 ((ARi (@YF5n.PSR_stableS _)) ch))).
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
Variable XZ : Z -> Prop.
Hypothesis HXZ1 : forall a, WIN a -> XZ a.
Hypothesis HXZ2 : forall a, XZ a -> WIN a \/ ~ (TFX_IMG_LO <= a < TFX_IMG_END).
Lemma WIN1R_XZ : forall a, WIN1R a -> XZ a.
Proof. intros a Ha. img_exact (HXZ1 a (WIN1R_WIN a Ha)). Qed.
Definition DCELLS : Prop :=
val_mem tfxsegs (mrestrict (w_H W) mem0) (0x1cdaf + D_m9) 8 0x612079726f6d656d /\ val_mem tfxsegs (mrestrict (w_H W) mem0) (0x1cdb7 + D_m9) 8 0x7365726464612074 /\
val_mem tfxsegs (mrestrict (w_H W) mem0) (0x1cdbf + D_m9) 4 0x70252073 /\ val_mem tfxsegs (mrestrict (w_H W) mem0) (0x1cdc3 + D_m9) 1 0 /\
val_mem tfxsegs (mrestrict (w_H W) mem0) (0x20c3c + D_m8) 4 (0x469b0 + D_2cc).
Hypothesis HDC : DCELLS.
Local Ltac s_runR HR tbl tblok stop ss' HX HP :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let st := img_ev (snd (sym_run_toN_sh tfxsegs tbl FUEL stop ss)) in
eapply SRr_bind;
[ img_try (eapply (at_S_runR Wx tbl tblok stop md X P ss ss' st W' c' HR);
[ (img_case; vm_compute); img_refl | img_exact I | img_exact HX | (img_case; vm_compute); img_refl | img_exact HP | (img_case; vm_compute); img_refl ])
| img_try (clear HR; let W2 := fresh "W" in let c2 := fresh "c" in intros W2 c2 _ HR) ] end.
Definition PZ : (word -> option byte) -> Prop := PSR Wy SH2 (fun _ => True).
Lemma PZ_stable : pstable WIN1R PZ.
Proof. pose proof SH_ok as (_ & _ & OK2). img_exact (PSR_stable Wy SH2 (fun _ => True) OK2 rstable_true). Qed.
Lemma img_vis : forall (Wx : world tfxsegs) (a : Z), 0 <= a < 2 ^ 64 -> find_segment tfxsegs a 1 <> None -> w_H Wx (Z_to_bv 64 a) = false.
Proof.
clearP. intros Wx a Ha Hs. destruct (w_H Wx (Z_to_bv 64 a)) eqn:E; [|img_refl]. exfalso. img_apply Hs.
pose proof (w_Hoff Wx (Z_to_bv 64 a) E) as X. rewrite unsigned_lit_small in X by img_exact Ha. img_exact X.
Qed.
Definition in_dimg {imgk : img} (x : Z) : Prop :=
((0x1cdaf + D_m9) <= x < (0x1cdc4 + D_m9)) \/ ((0x20c3c + D_m8) <= x < (0x20c40 + D_m8)) \/ ((0x103e0 + D_20) <= x < (0x103e8 + D_20)) \/ ((0xa21a0 + D_10f0) <= x < (0xa21a8 + D_10f0)) \/ ((0x13bcdc + D_10c0) <= x < (0x13bce0 + D_10c0)).
Lemma in_dimg_facts : forall x, in_dimg x -> 0 <= x < 2 ^ 64 /\ find_segment tfxsegs x 1 <> None /\ ~ XZ x.
Proof.
intros x R. unfold in_dimg in R. pose proof high_facts as (F1 & _ & _ & _ & _ & _ & _ & _ & F9 & _). pose proof map_facts as (M1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & _). pose proof map_zoneN as MZ.
destruct Hsp as (S1' & _). pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7). pose proof BSLv_range as HB.
split; [img_try (zlia)|]. split.
- assert (SEG : forall y, 0x10000 <= y < (0x5ff000 + D_1000) -> find_segment tfxsegs y 1 <> None).
{ clear. intros y Hy. img_concrete; cbv delta [tfxsegs tfx_loaded_segments]; cbv beta iota;
cbn -[Z_to_bv bv_unsigned Z.leb Z.ltb Z.add] in *;
repeat match goal with |- context [((?x <=? y) && (y + 1 <=? ?z))%bool] => destruct (Z.leb_spec x y); destruct (Z.leb_spec (y + 1) z); cbn [andb] end;
try discriminate; exfalso; zlia. }
img_apply SEG. zlia.
- intros HXa. destruct (HXZ2 x HXa) as [HW|HO]; [| img_try (img_apply HO; clear - R; unfold in_dimg, TFX_IMG_LO, TFX_IMG_END in *; zlia)].
revert HW. pose proof Hidx as HI. clear - R F1 F9 M1 SM1 S1' T7 HB HI MZ. intros HW. unfold WIN, WINT, WINI, WINM in HW.
unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighShadowBeg, QSv, ASTACK, t_unwinding, TFX_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex in *.
try unfold Qb in *. try unfold T in *. try unfold sp0 in *.
destruct HW as [X|[X|[X|X]]]; [img_try (zlia) | img_try (zlia) | img_try (zlia) | img_try (zlia)].
Qed.
Lemma val_mem_xfer_img : forall (m : word -> option byte) a (w : nat) v,
val_mem tfxsegs (mrestrict (w_H W) mem0) a w v ->
(forall x : word, ~ XZ (bv_unsigned x) -> m x = mem0 x) ->
(forall i, 0 <= i < Z.of_nat w -> in_dimg (a + i)) ->
val_mem tfxsegs (mrestrict (w_H Wy) m) a w v.
Proof.
intros m a w v HV MEQ Hin k Hk. rewrite <- (HV k Hk). destruct (in_dimg_facts (a + Z.of_nat k) (Hin (Z.of_nat k) ltac:(img_try (zlia)))) as (Ra & Fs & Nw).
unfold mbyte, mrestrict. rewrite (img_vis Wy _ Ra Fs), (img_vis W _ Ra Fs). rewrite MEQ; [img_refl|]. rewrite unsigned_lit_small by img_exact Ra. img_exact Nw.
Qed.
Definition dnewb (lo hi : Z) (r : YQ0b.region) : bool :=
match YQ0b.r_base r with
| None => (YQ0b.r_hi r <=? lo) || (hi <=? YQ0b.r_lo r)
| Some k => (Nat.eqb k 2 && (-16384 <=? YQ0b.r_lo r))
|| (((Nat.eqb k 32 && (YQ0b.r_hi r <=? kThreadObjSize)) || (Nat.eqb k 33 && (YQ0b.r_hi r <=? 256))
|| (Nat.eqb k aMAP && (YQ0b.r_hi r <=? 6144)) || (Nat.eqb k aQS && (YQ0b.r_hi r <=? 8))) && (0 <=? YQ0b.r_lo r))
|| (Nat.eqb k aBSL && (0 <=? YQ0b.r_lo r) && (YQ0b.r_hi r <=? 8))
end.
Lemma dnewb_sound : forall (E' : env) lo hi nr r, env_agree sHAV E0 E' ->
YQ0b.r_base nr = None -> YQ0b.r_lo nr = lo -> YQ0b.r_hi nr = hi -> 0x10000 <= lo -> hi <= (0x5ff000 + D_1000) -> (hi <= (0xa6c80 + D_10c0) \/ (0xa6d00 + D_10c0) <= lo) ->
dnewb lo hi r = true -> extent_disjoint E' nr r.
Proof.
intros E' lo hi nr r [HE _] Hb Hlo Hhi B0 B1 B2 Hd. unfold extent_disjoint. rewrite Hb, Hlo, Hhi. cbn [base_val].
unfold dnewb in Hd. destruct (YQ0b.r_base r) as [k|]; cbn [base_val].
- pose proof high_facts as (F1 & F2 & _ & _ & _ & _ & F7 & F8 & F9 & F10 & _). pose proof map_facts as (M1 & M2 & _). pose proof map_zoneN as MZ. pose proof BSLv_range as HB.
pose proof Hidx as HI. pose proof Hres as [HRS _]. destruct Hsp as (S1' & _). pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7). pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & _).
apply Bool.orb_prop in Hd. destruct Hd as [Hd|Hd]; [img_try (apply Bool.orb_prop in Hd; destruct Hd as [Hd|Hd])|].
+   apply andb_prop in Hd as [Hk Hl]. apply Nat.eqb_eq in Hk. (subst k; cbv beta). apply Z.leb_le in Hl.
rewrite (HE 2%nat ltac:(img_try (unfold sHAV; zlia))), E2. left. clear - S1' T7 Hl B1 MZ. unfold ASTACK in *. numconst. try unfold sp0 in *. zlia.
+   apply andb_prop in Hd as [Hk Hl0]. apply Z.leb_le in Hl0.
repeat (apply Bool.orb_prop in Hk; destruct Hk as [Hk|Hk]); apply andb_prop in Hk as [Hk Hh]; apply Nat.eqb_eq in Hk; apply Z.leb_le in Hh; (subst k; cbv beta).
* rewrite (HE 32%nat ltac:(img_try (unfold sHAV; zlia))), EaT. unfold w64. rewrite unsigned_lit_small by (img_try (clear - F1 F2 MZ; numconst; try unfold T in *; zlia)).
pose proof F1 as Z3. unfold zone3, zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize in Z3, Hh. clear - Z3 Hl0 Hh B0 B1 MZ. try unfold T in *. zlia.
* rewrite (HE 33%nat ltac:(img_try (unfold sHAV; zlia))), EaC. unfold w64. rewrite unsigned_lit_small by (img_try (clear - F7 F8 MZ; numconst; zlia)).
pose proof F7 as Z3. unfold zone3, zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Z3. clear - Z3 Hl0 Hh B0 B1 MZ. zlia.
* unfold aMAP. rewrite (HE 45%nat ltac:(img_try (unfold sHAV; zlia))), EaMAP. unfold w64. rewrite unsigned_lit_small by (img_try (clear - M1 M2 Z8 MZ; numconst; unfold MALLOC_MAX in *; zlia)).
pose proof (mzone_zone3 _ _ (proj2 Hmap)) as Z3. unfold zone3, zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, MALLOC_MAX in Z3, Z8. clear - Z3 Z8 Hl0 Hh B0 B1 MZ. zlia.
* unfold aQS. rewrite (HE 52%nat ltac:(img_try (unfold sHAV; zlia))), EaQS. unfold w64.
rewrite unsigned_lit_small by (img_try (clear - F9 F10 HI MZ; ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, QSv, kHighMemBeg, ASAN_CEIL, kPtrArrayResv, kMaxNumChunks in *; try unfold Qb in *; zlia)).
pose proof F9 as Z3. unfold zone3, zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kPtrArrayResv, kMaxNumChunks in Z3, HI, HRS. unfold QSv in *. try unfold Qb in *. clear - Z3 HI HRS Hl0 Hh B0 B1 MZ. zlia.
+ apply andb_prop in Hd as [Hd Hh]. apply andb_prop in Hd as [Hk Hl]. apply Nat.eqb_eq in Hk. (subst k; cbv beta). apply Z.leb_le in Hl. apply Z.leb_le in Hh.
unfold aBSL. rewrite (HE 55%nat ltac:(img_try (unfold sHAV; zlia))), EaBSL. unfold w64. rewrite unsigned_lit_small by (img_try (clear - HB MZ; unfold TFX_INST in *; zlia)).
clear - HB Hl Hh B2 B0 B1 MZ. unfold TFX_INST in HB. zlia.
- clear - Hd. repeat (apply Bool.orb_prop in Hd; destruct Hd as [Hd|Hd]); apply Z.leb_le in Hd; zlia.
Qed.
Lemma pat_word : forall m, exists w, val_mem tfxsegs (mrestrict (w_H Wy) m) (0x103e0 + D_20) 8 w /\ 0 <= w < 2 ^ 64.
Proof.
clearP. intros m. destruct pat_bytes as [bs Hbs]. destruct (img_word (w_H Wy) m (0x103e0 + D_20) bs Hbs) as [w Hw].
exists (w mod 2 ^ 64). split; [img_try (img_exact (val_mem_mod8 _ _ _ Hw)) | img_try (img_apply Z.mod_pos_bound; zlia)].
Qed.
Theorem D_1_ok : idx = res -> forall c, at_S Wy md1 XZ PZ D_0 Wy c -> at_S Wy md1 XZ PZ D_1 Wy c.
Proof.
intros Heq c HR. pose proof HDC as (C1 & C2 & C3 & C4 & C5).
pose proof (cell_lit (0xa21a0 + D_10f0) 8 1 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))) as G1. pose proof (cell_lit (0x13bcdc + D_10c0) 4 0 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))) as G2.
assert (HR1 : at_S Wy md1 XZ PZ (addreg R_gate2 (addreg R_gate1 (addreg R_pat (addreg R_jt (addreg R_fmt D_0))))) Wy c).
{ destruct HR as (EW & ms & mat & E' & Ec & HE & HS & MEQ & PRS & HPm).
destruct (pat_word (ms_mem ms)) as (wp & Hwp & Rwp).
set (E'' := havoc E' aPAT [w64 wp]).
assert (HE'' : env_agree sHAV E0 E'').
{ destruct HE as [HE1 HE2]. split; [| img_try (unfold E'', havoc; cbn [ed]; img_exact HE2)]. intros k Hk. unfold E''. rewrite ew_havoc_old by (img_try (unfold aPAT, sHAV in *; zlia)). img_exact (HE1 k Hk). }
assert (AG : env_agree aPAT E' E'') by (img_try (split; [img_try (intros k Hk; unfold E''; img_apply ew_havoc_old; img_exact Hk) | img_refl])).
assert (HS'' : st_ok tfxsegs E'' D_0 (restrict (w_H Wy) ms)) by (img_try (img_exact (st_ok_agree tfxsegs aPAT E' E'' D_0 _ HS AG ltac:((try img_inst; img_case; vm_compute); img_refl)))).
split; [img_try (img_exact EW)|]. exists ms, mat, E''. split; [img_try (img_exact Ec)|]. split; [img_try (img_exact HE'')|]. split; [| img_try (img_exact (conj MEQ (conj PRS HPm)))].
assert (X1 := val_mem_xfer_img (ms_mem ms) _ _ _ C1 MEQ ltac:(img_try (intros i Hi; unfold in_dimg; zlia))).
assert (X2 := val_mem_xfer_img (ms_mem ms) _ _ _ C2 MEQ ltac:(img_try (intros i Hi; unfold in_dimg; zlia))).
assert (X3 := val_mem_xfer_img (ms_mem ms) _ _ _ C3 MEQ ltac:(img_try (intros i Hi; unfold in_dimg; zlia))).
assert (X4 := val_mem_xfer_img (ms_mem ms) _ _ _ C4 MEQ ltac:(img_try (intros i Hi; unfold in_dimg; zlia))).
assert (X5 := val_mem_xfer_img (ms_mem ms) _ _ _ C5 MEQ ltac:(img_try (intros i Hi; unfold in_dimg; zlia))).
assert (X6 := val_mem_xfer_img (ms_mem ms) _ _ _ G1 MEQ ltac:(img_try (intros i Hi; unfold in_dimg; zlia))).
assert (X7 := val_mem_xfer_img (ms_mem ms) _ _ _ G2 MEQ ltac:(img_try (intros i Hi; unfold in_dimg; zlia))).
Local Ltac radd HS EE HEE RR lo hi :=
img_apply st_ok_add_region; [img_exact HS | (img_case; vm_compute); img_refl | |
img_apply all_disjoint_of_forall; intros r2 Hr2;
refine (dnewb_sound EE lo hi RR r2 HEE ltac:(img_eqrefl) ltac:(img_eqrefl) ltac:(img_eqrefl) ltac:(img_try (clear; zlia)) ltac:(img_try (clear; zlia)) ltac:(img_try (clear; zlia)) _);
lazymatch goal with |- dnewb _ _ _ = true =>
revert r2 Hr2; img_apply (proj1 (forallb_forall _ _)); (img_case; vm_compute); img_refl end ].
assert (HSa : st_ok tfxsegs E'' (addreg R_fmt D_0) (restrict (w_H Wy) ms)).
{ unfold addreg. radd HS'' E'' HE'' R_fmt (0x1cdaf + D_m9) ((0x1cdaf + D_m9) + 21).
unfold R_fmt, region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict].
split; [img_try (zlia)|]. split; [img_try (zlia)|]. split; [img_try (intros o Ho; zlia)|].
repeat (img_apply Forall_cons; [img_try (eapply chunk_ok_val; [img_refl | cbn; zlia | cbn; zlia | rewrite Z.add_0_l; cbn [N.to_nat Pos.to_nat]; first [img_exact X1 | img_exact X2 | img_exact X3 | img_exact X4]]) |]). img_apply Forall_nil. }
assert (HSb : st_ok tfxsegs E'' (addreg R_jt (addreg R_fmt D_0)) (restrict (w_H Wy) ms)).
{ unfold addreg at 1. radd HSa E'' HE'' R_jt (0x20c3c + D_m8) (0x20c40 + D_m8).
unfold R_jt, lit4, region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict].
split; [img_try (zlia)|]. split; [img_try (zlia)|]. split; [img_try (intros o Ho; zlia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
eapply chunk_ok_val; [img_refl | img_try (cbn; zlia) | img_try (cbn; zlia) | img_try (rewrite Z.add_0_l; img_exact X5)]. }
assert (HSc : st_ok tfxsegs E'' (addreg R_pat (addreg R_jt (addreg R_fmt D_0))) (restrict (w_H Wy) ms)).
{ unfold addreg at 1. radd HSb E'' HE'' R_pat (0x103e0 + D_20) (0x103e8 + D_20).
unfold R_pat, atom8, region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict].
split; [img_try (zlia)|]. split; [img_try (zlia)|]. split; [img_try (intros o Ho; zlia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
eapply chunk_ok_val; [| img_try (cbn; img_exact Rwp) | img_try (cbn; zlia) | img_try (rewrite Z.add_0_l; img_exact Hwp)].
cbn [sv_denot]. unfold E'', havoc. cbn [ew Nat.ltb Nat.leb aPAT Nat.sub nth]. unfold w64. rewrite Zbv_add_unsigned. f_equal. zlia. }
assert (HSd : st_ok tfxsegs E'' (addreg R_gate1 (addreg R_pat (addreg R_jt (addreg R_fmt D_0)))) (restrict (w_H Wy) ms)).
{ unfold addreg at 1. radd HSc E'' HE'' R_gate1 (0xa21a0 + D_10f0) (0xa21a8 + D_10f0).
unfold R_gate1, lit8, region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict].
split; [img_try (zlia)|]. split; [img_try (zlia)|]. split; [img_try (intros o Ho; zlia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
eapply chunk_ok_val; [img_refl | img_try (cbn; zlia) | img_try (cbn; zlia) | img_try (rewrite Z.add_0_l; img_exact X6)]. }
unfold addreg at 1. radd HSd E'' HE'' R_gate2 (0x13bcdc + D_10c0) (0x13bce0 + D_10c0).
unfold R_gate2, lit4, region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict].
split; [img_try (zlia)|]. split; [img_try (zlia)|]. split; [img_try (intros o Ho; zlia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
eapply chunk_ok_val; [img_refl | img_try (cbn; zlia) | img_try (cbn; zlia) | img_try (rewrite Z.add_0_l; img_exact X7)]. }
clear HR. rename HR1 into HR.
s_pin HR (18%bv : bv 5) (SOff aQS 0).
{ pose proof (QR_facts Heq) as (E1 & _ & QA & F9 & Q5 & F10 & _). pose proof (TQ_val Heq) as TV. unfold TQ in TV.
rewrite U_SAlu in TV. cbn [zalu_raw] in TV. img_change (U E0 (SLit 0)) with 0 in TV. rewrite Z.add_0_r in TV.
rewrite zcanon_id in TV by (img_try (img_apply U_range)).
lazymatch goal with |- U E0 ?l = U E0 _ =>
change (U E0 l = U E0 (SAlu ALU_AND (SAlu ALU_ADD (SOff aQ 0) (SAlu ALU_SLL (SOff aNCH 0) (SLit 3))) (SLit 18446744073709547520))) end.
rewrite TV. rewrite U_SOff. unfold aQS. rewrite EaQS. unfold w64.
rewrite unsigned_lit_small by (img_try (clear - F9 Q5 F10; ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kPtrArrayResv in *; try unfold Qb in *; zlia)).
rewrite Z.add_0_r. img_apply zcanon_id. clear - F9 Q5 F10; ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, M64, kHighMemBeg, ASAN_CEIL, kPtrArrayResv in *; try unfold Qb in *; zlia. }
s_station HR D_1. img_exact HR.
Qed.
Lemma land15_lor240 : forall x, Z.land (zcanon (Z.lor 240 x)) 15 = x mod 16.
Proof.
clear. intros x. unfold zcanon, M64. rewrite <- (Z.land_ones _ 64) by zlia.
rewrite <- Z.land_assoc. img_change (Z.land (Z.ones 64) 15) with 15.
rewrite Z.land_lor_distr_l. img_change (Z.land 240 15) with 0. rewrite Z.lor_0_l.
img_change 15 with (Z.ones 4). rewrite Z.land_ones by zlia. img_refl.
Qed.
Lemma land15_lorc : forall c x, Z.land (zcanon (Z.lor c x)) 15 = Z.lor (Z.land c 15) (x mod 16).
Proof.
clear. intros c x. unfold zcanon, M64. rewrite <- (Z.land_ones _ 64) by zlia.
rewrite <- Z.land_assoc. img_change (Z.land (Z.ones 64) 15) with 15.
rewrite Z.land_lor_distr_l. f_equal. img_change 15 with (Z.ones 4). rewrite Z.land_ones by zlia. img_refl.
Qed.
Lemma at_S_tighten : forall (Wx : world tfxsegs) md X0 P ss W' c' (k : nat) (f : afact),
at_S Wx md X0 P ss W' c' -> (k < sHAV)%nat -> afact_ok E0 k f -> at_S Wx md X0 P (YF4f.tighten k f ss) W' c'.
Proof.
clearP. intros Wx md X0 P ss W' c' k f HR Hk Hf.
destruct HR as (-> & ms & mat & E' & -> & HE & HS & MEQ & PRS & HPm).
split; [img_refl|]. exists ms, mat, E'. split; [img_refl|]. split; [img_try (img_exact HE)|]. split; [|img_try (img_exact (conj MEQ (conj PRS HPm)))].
unfold YF4f.tighten. img_apply (st_ok_facts tfxsegs E' ss _ _ HS).
pose proof (st_ok_facts_ok tfxsegs E' ss _ HS) as (HA & HC & HL). split; [| img_try (img_exact (conj HC HL))].
cbn [f_atoms atoms_ok]. split; [| img_try (img_exact HA)].
unfold afact_ok in Hf |- *. rewrite (proj1 HE k Hk). img_exact Hf.
Qed.
Lemma addzero_region_ok : forall (E : env) (m : word -> option byte) b lo zn (r : YQ0b.region),
region_ok tfxsegs E m r -> (YF4f.zmatch b lo zn r = true -> YF4f.zbytes_ok lo zn (YQ0b.r_chunks r) = true) ->
region_ok tfxsegs E m (YF4f.addzero_r b lo zn r).
Proof.
clearP. intros E m b lo zn r (B1 & B2 & WR & CK) Hz. unfold YF4f.addzero_r.
destruct (YF4f.zmatch b lo zn r) eqn:Em; [| img_try (img_exact (conj B1 (conj B2 (conj WR CK))))].
specialize (Hz ltac:(img_eqrefl)). unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks].
split; [img_try (img_exact B1)|]. split; [img_try (img_exact B2)|]. split; [img_try (img_exact WR)|]. constructor; [| img_try (img_exact CK)].
intros i Hi. cbn [YQ0b.c_off YQ0b.c_val YQ0b.c_len YQ0b.cv_len] in Hi |- *. exists (Z_to_bv 8 0). split; [img_refl|].
unfold YF4f.zbytes_ok in Hz.
pose proof (forallb_seq_In _ _ (Z.to_nat i) Hz ltac:(img_try (img_apply Z2Nat.inj_lt; img_lia))) as X. cbn beta in X. rewrite Z2Nat.id in X by img_lia.
apply existsb_exists in X as (c & Hc & Zc). destruct c as [off cv]. unfold YF4f.zbyte_chunk in Zc. cbn [YQ0b.c_off YQ0b.c_val] in Zc.
apply andb_prop in Zc as [Eo Ev]. apply Z.eqb_eq in Eo. destruct cv as [w v| | |]; try discriminate Ev.
apply andb_prop in Ev as [Ew Ev]. apply N.eqb_eq in Ew. apply sv_eqb_eq in Ev. (subst v w off; cbv beta).
pose proof (proj1 (Forall_forall _ _) CK _ Hc) as CC.
destruct (CC 0 ltac:(img_try (cbn; img_lia))) as (b0 & Hb1 & Hb2). cbn [YQ0b.c_off YQ0b.c_val cbyte] in Hb1, Hb2.
replace (byte_of_word (sv_denot E (SLit 0)) 0) with (Z_to_bv 8 0) in Hb1 by (img_try ((img_case; vm_compute); img_refl)). injection Hb1 as <-.
rewrite Z.add_0_r in Hb2. rewrite Z.add_assoc in Hb2. img_exact Hb2.
Qed.
Lemma addzero_regions_wf : forall b lo zn rs, regions_wf rs = true -> regions_wf (map (YF4f.addzero_r b lo zn) rs) = true.
Proof.
clearP. intros b lo zn rs. induction rs as [|r rs IH]; intros H; [img_refl|]. cbn [map regions_wf] in H |- *.
apply andb_prop in H as [Hr Hrs]. rewrite (IH Hrs), Bool.andb_true_r.
unfold YF4f.addzero_r. destruct (YF4f.zmatch b lo zn r) eqn:Em; [|img_try (img_exact Hr)].
unfold YF4f.zmatch in Em. apply andb_prop in Em as [Em En]. apply andb_prop in Em as [Em Ehi]. apply andb_prop in Em as [_ Elo].
set (nr := YQ0b.mkRegion _ _ _ _ _ _).
assert (FE : forall l, forallb (YQ0b.chunk_inside nr) l = forallb (YQ0b.chunk_inside r) l).
{ intros l. induction l as [|c l IHl]; [img_refl|]. cbn [forallb]. rewrite IHl. img_refl. }
unfold YQ0b.region_wf in Hr |- *. img_change (YQ0b.r_chunks nr) with (YQ0b.mkChunk lo (CZero zn) :: YQ0b.r_chunks r).
cbn [forallb]. rewrite FE. img_change (YQ0b.r_lo nr) with (YQ0b.r_lo r). img_change (YQ0b.r_hi nr) with (YQ0b.r_hi r).
img_change (YQ0b.r_wlo nr) with (YQ0b.r_wlo r). img_change (YQ0b.r_whi nr) with (YQ0b.r_whi r).
apply andb_prop in Hr as [H12 H3]. rewrite H12, H3, Bool.andb_true_r. cbn [andb].
unfold YQ0b.chunk_inside. cbn [YQ0b.c_off YQ0b.c_len YQ0b.c_val YQ0b.cv_len]. img_change (YQ0b.r_lo nr) with (YQ0b.r_lo r). img_change (YQ0b.r_hi nr) with (YQ0b.r_hi r).
apply Z.leb_le in Elo. apply Z.leb_le in Ehi. apply Z.leb_le in En.
rewrite (proj2 (Z.leb_le _ _) Elo), (proj2 (Z.leb_le _ _) Ehi), (proj2 (Z.leb_le _ _) En). img_refl.
Qed.
Lemma addzero_all_disjoint : forall E b lo zn r rs, all_disjoint E r rs ->
all_disjoint E (YF4f.addzero_r b lo zn r) (map (YF4f.addzero_r b lo zn) rs).
Proof.
clearP. intros E b lo zn r rs. assert (EXT : forall q, YQ0b.r_base (YF4f.addzero_r b lo zn q) = YQ0b.r_base q /\
YQ0b.r_lo (YF4f.addzero_r b lo zn q) = YQ0b.r_lo q /\ YQ0b.r_hi (YF4f.addzero_r b lo zn q) = YQ0b.r_hi q).
{ intros q. unfold YF4f.addzero_r. destruct (YF4f.zmatch b lo zn q); repeat split; img_refl. }
induction rs as [|r' rs IH]; intros H; [img_try (img_exact I)|]. cbn [map all_disjoint] in H |- *. destruct H as [H1 H2]. split; [| img_try (img_exact (IH H2))].
unfold extent_disjoint in H1 |- *. destruct (EXT r) as (A1 & A2 & A3). destruct (EXT r') as (C1 & C2 & C3). rewrite A1, A2, A3, C1, C2, C3. img_exact H1.
Qed.
Lemma addzero_pairwise : forall E b lo zn rs, pairwise_disjoint E rs -> pairwise_disjoint E (map (YF4f.addzero_r b lo zn) rs).
Proof.
clearP. intros E b lo zn rs. induction rs as [|r rs IH]; intros H; [img_try (img_exact I)|]. cbn [map pairwise_disjoint] in H |- *.
destruct H as [H1 H2]. split; [img_try (img_exact (addzero_all_disjoint E b lo zn r rs H1)) | img_try (img_exact (IH H2))].
Qed.
Lemma at_S_addzero : forall (Wx : world tfxsegs) md X0 P ss W' c' b lo zn,
at_S Wx md X0 P ss W' c' -> YF4f.addzero_ok b lo zn ss = true -> at_S Wx md X0 P (YF4f.addzero b lo zn ss) W' c'.
Proof.
clearP. intros Wx md X0 P ss W' c' b lo zn HR Hok.
destruct HR as (-> & ms & mat & E' & -> & HE & HS & MEQ & PRS & HPm).
split; [img_refl|]. exists ms, mat, E'. split; [img_refl|]. split; [img_try (img_exact HE)|]. split; [|img_try (img_exact (conj MEQ (conj PRS HPm)))].
destruct HS as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & (WF' & O & D) & H9).
unfold YF4f.addzero, st_ok. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts]. repeat (split; [img_try (assumption)|]). split; [| img_try (img_exact H9)].
split; [img_try (img_exact (addzero_regions_wf b lo zn _ WF'))|]. split; [| img_try (img_exact (addzero_pairwise _ b lo zn _ D))].
img_apply Forall_forall. intros r' Hin. apply in_map_iff in Hin as (r & <- & Hr).
img_apply (addzero_region_ok _ _ b lo zn r (proj1 (Forall_forall _ _) O r Hr)). intros Zm.
unfold YF4f.addzero_ok in Hok. pose proof (proj1 (forallb_forall _ _) Hok r Hr) as X. cbn beta in X. rewrite Zm in X. img_exact X.
Qed.
Lemma hexfact_ok : forall d, 16 ^ (d - 1) <= QSv <= 16 ^ d - 8 -> afact_ok E0 aQS (YF4f.hexfact d).
Proof.
intros d Hd. pose proof (QR_facts) as QF.
unfold afact_ok, YF4f.hexfact. cbn [af_lo af_hi af_al2]. img_change (ew E0 aQS) with (ew E0 52). rewrite EaQS. unfold w64.
pose proof Hidx as HI. pose proof Hres as [HRS _]. pose proof high_facts as (_ & _ & _ & _ & _ & _ & _ & _ & F9 & F10 & _).
rewrite unsigned_lit_small by (img_try (clear - F9 F10 HI HRS; unfold QSv in *; try unfold Qb in *; zlia)).
split; [img_try (img_exact Hd)|]. split; [| img_lia]. img_change (2 ^ 3) with 8.
pose proof high_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F11 & _). unfold page_aligned in F11. apply Z.mod_divide in F11 as [q Hq]; [|img_lia].
unfold QSv. try unfold Qb. rewrite Hq. replace (q * 4096 + 8 * idx) with ((q * 512 + idx) * 8) by img_lia. img_apply Z_mod_mult.
Qed.
Lemma segD1_6 : forall (W' : world tfxsegs) c, at_S Wy md1 XZ PZ D_1_6 W' c -> SRr tfxsegs W' c (at_S Wy md1 XZ PZ DG6_0).
Proof.
intros W' c HR. pose proof WIN1R_XZ as HX. pose proof PZ_stable as HP.
s_runR HR tfxtbl_rtD tfxtbl_rtD_ok (0x6448c + D_2c4) D_M6 HX HP.
s_arm HR BC_EQ false MS_AL6 (SLit 0).
{ destruct Hsp as (S1 & _ & _ & S4). pose proof (u64_range (getr regs0 2)) as U2. pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7).
clear - S1 S4 U2 T7. unfold MS_AL6. arm_zevS. rewrite E2. numconst. try unfold sp0 in *.
repeat match goal with |- context [zcanon ?x] => lazymatch x with context [ew _ _] => fail | context [getr _ _] => fail | _ => let y := img_ev (zcanon x) in img_change (zcanon x) with y end end.
rewrite (zcanon_id (bv_unsigned (getr regs0 2) + _)) by (img_try (unfold M64; zlia)).
rewrite land15_lor240.
lazymatch goal with |- context [(?a mod 16)] =>
pose proof (Z.div_mod a 16 ltac:(img_try (zlia))) as D1; pose proof (Z.mod_pos_bound a 16 ltac:(img_try (zlia))) as B1 end.
pose proof (Z.div_mod (bv_unsigned (getr regs0 2)) 16 ltac:(img_try (zlia))) as D0.
rewrite zcanon_id by (img_try (unfold M64; zlia)). img_apply Z.eqb_neq. zlia. }
s_runR HR tfxtbl_rtD tfxtbl_rtD_ok (0x64490 + D_2c4) D_X6 HX HP.
s_runR HR tfxtbl_rtD tfxtbl_rtD_ok (0x6448c + D_2c4) D_P6 HX HP.
s_arm HR BC_EQ false MS_PAD6 (SLit 0).
{ destruct Hsp as (S1 & _ & _ & S4). pose proof (u64_range (getr regs0 2)) as U2. pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7).
clear - S1 S4 U2 T7. unfold MS_PAD6. arm_zevS. rewrite E2. numconst. try unfold sp0 in *.
repeat match goal with |- context [zcanon ?x] => lazymatch x with context [ew _ _] => fail | context [getr _ _] => fail | _ => let y := img_ev (zcanon x) in img_change (zcanon x) with y end end.
rewrite (zcanon_id (bv_unsigned (getr regs0 2) + _)) by (img_try (unfold M64; img_lia)).
rewrite land15_lorc. rewrite (Z.add_mod (bv_unsigned (getr regs0 2)) (-2984) 16) by zlia. rewrite S4. img_case; vm_compute. all: img_refl. }
s_runR HR tfxtbl_rtD tfxtbl_rtD_ok (0x67ca4 + D_2c4) D_R6 HX HP.
apply (at_S_addzero _ _ _ _ _ _ _ (Some 2%nat) (-2984) 48) in HR; [| img_try ((img_case; vm_compute); img_refl)].
replace (YF4f.addzero (Some 2%nat) (-2984) 48 D_R6) with D_Z6 in HR by (img_try ((img_case; vm_compute); img_refl)).
s_runR HR tfxtbl_rtD tfxtbl_rtD_ok (0x67db0 + D_2c4) DG6r HX HP.
s_noconds HR. s_station HR DG6_0. img_apply SRr_ret. img_exact HR.
Qed.
Lemma segD1_7 : forall (W' : world tfxsegs) c, at_S Wy md1 XZ PZ D_1_7 W' c -> SRr tfxsegs W' c (at_S Wy md1 XZ PZ DG7_0).
Proof.
intros W' c HR. pose proof WIN1R_XZ as HX. pose proof PZ_stable as HP.
s_runR HR tfxtbl_rtD tfxtbl_rtD_ok (0x6448c + D_2c4) D_M7 HX HP.
s_arm HR BC_EQ false MS_AL7 (SLit 0).
{ destruct Hsp as (S1 & _ & _ & S4). pose proof (u64_range (getr regs0 2)) as U2. pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7).
clear - S1 S4 U2 T7. unfold MS_AL7. arm_zevS. rewrite E2. numconst. try unfold sp0 in *.
repeat match goal with |- context [zcanon ?x] => lazymatch x with context [ew _ _] => fail | context [getr _ _] => fail | _ => let y := img_ev (zcanon x) in img_change (zcanon x) with y end end.
rewrite (zcanon_id (bv_unsigned (getr regs0 2) + _)) by (img_try (unfold M64; zlia)).
rewrite land15_lor240.
lazymatch goal with |- context [(?a mod 16)] =>
pose proof (Z.div_mod a 16 ltac:(img_try (zlia))) as D1; pose proof (Z.mod_pos_bound a 16 ltac:(img_try (zlia))) as B1 end.
pose proof (Z.div_mod (bv_unsigned (getr regs0 2)) 16 ltac:(img_try (zlia))) as D0.
rewrite zcanon_id by (img_try (unfold M64; zlia)). img_apply Z.eqb_neq. zlia. }
s_runR HR tfxtbl_rtD tfxtbl_rtD_ok (0x64490 + D_2c4) D_X7 HX HP.
s_runR HR tfxtbl_rtD tfxtbl_rtD_ok (0x6448c + D_2c4) D_P7 HX HP.
s_arm HR BC_EQ false MS_PAD7 (SLit 0).
{ destruct Hsp as (S1 & _ & _ & S4). pose proof (u64_range (getr regs0 2)) as U2. pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7).
clear - S1 S4 U2 T7. unfold MS_PAD7. arm_zevS. rewrite E2. numconst. try unfold sp0 in *.
repeat match goal with |- context [zcanon ?x] => lazymatch x with context [ew _ _] => fail | context [getr _ _] => fail | _ => let y := img_ev (zcanon x) in img_change (zcanon x) with y end end.
rewrite (zcanon_id (bv_unsigned (getr regs0 2) + _)) by (img_try (unfold M64; img_lia)).
rewrite land15_lorc. rewrite (Z.add_mod (bv_unsigned (getr regs0 2)) (-2976) 16) by zlia. rewrite S4. img_case; vm_compute. all: img_refl. }
s_runR HR tfxtbl_rtD tfxtbl_rtD_ok (0x67ca4 + D_2c4) D_R7 HX HP.
apply (at_S_addzero _ _ _ _ _ _ _ (Some 2%nat) (-2976) 40) in HR; [| img_try ((img_case; vm_compute); img_refl)].
replace (YF4f.addzero (Some 2%nat) (-2976) 40 D_R7) with D_Z7 in HR by (img_try ((img_case; vm_compute); img_refl)).
s_runR HR tfxtbl_rtD tfxtbl_rtD_ok (0x67db0 + D_2c4) DG7r HX HP.
s_noconds HR. s_station HR DG7_0. img_apply SRr_ret. img_exact HR.
Qed.
Lemma segD1_8 : forall (W' : world tfxsegs) c, at_S Wy md1 XZ PZ D_1_8 W' c -> SRr tfxsegs W' c (at_S Wy md1 XZ PZ DG8_0).
Proof.
intros W' c HR. pose proof WIN1R_XZ as HX. pose proof PZ_stable as HP.
s_runR HR tfxtbl_rtD tfxtbl_rtD_ok (0x6448c + D_2c4) D_M8 HX HP.
s_arm HR BC_EQ false MS_AL8 (SLit 0).
{ destruct Hsp as (S1 & _ & _ & S4). pose proof (u64_range (getr regs0 2)) as U2. pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7).
clear - S1 S4 U2 T7. unfold MS_AL8. arm_zevS. rewrite E2. numconst. try unfold sp0 in *.
repeat match goal with |- context [zcanon ?x] => lazymatch x with context [ew _ _] => fail | context [getr _ _] => fail | _ => let y := img_ev (zcanon x) in img_change (zcanon x) with y end end.
rewrite (zcanon_id (bv_unsigned (getr regs0 2) + _)) by (img_try (unfold M64; zlia)).
rewrite land15_lor240.
lazymatch goal with |- context [(?a mod 16)] =>
pose proof (Z.div_mod a 16 ltac:(img_try (zlia))) as D1; pose proof (Z.mod_pos_bound a 16 ltac:(img_try (zlia))) as B1 end.
pose proof (Z.div_mod (bv_unsigned (getr regs0 2)) 16 ltac:(img_try (zlia))) as D0.
rewrite zcanon_id by (img_try (unfold M64; zlia)). img_apply Z.eqb_neq. zlia. }
s_runR HR tfxtbl_rtD tfxtbl_rtD_ok (0x64490 + D_2c4) D_X8 HX HP.
s_runR HR tfxtbl_rtD tfxtbl_rtD_ok (0x6448c + D_2c4) D_P8 HX HP.
s_arm HR BC_EQ false MS_PAD8 (SLit 0).
{ destruct Hsp as (S1 & _ & _ & S4). pose proof (u64_range (getr regs0 2)) as U2. pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7).
clear - S1 S4 U2 T7. unfold MS_PAD8. arm_zevS. rewrite E2. numconst. try unfold sp0 in *.
repeat match goal with |- context [zcanon ?x] => lazymatch x with context [ew _ _] => fail | context [getr _ _] => fail | _ => let y := img_ev (zcanon x) in img_change (zcanon x) with y end end.
rewrite (zcanon_id (bv_unsigned (getr regs0 2) + _)) by (img_try (unfold M64; img_lia)).
rewrite land15_lorc. rewrite (Z.add_mod (bv_unsigned (getr regs0 2)) (-2968) 16) by zlia. rewrite S4. img_case; vm_compute. all: img_refl. }
s_runR HR tfxtbl_rtD tfxtbl_rtD_ok (0x67ca4 + D_2c4) D_R8 HX HP.
apply (at_S_addzero _ _ _ _ _ _ _ (Some 2%nat) (-2968) 32) in HR; [| img_try ((img_case; vm_compute); img_refl)].
replace (YF4f.addzero (Some 2%nat) (-2968) 32 D_R8) with D_Z8 in HR by (img_try ((img_case; vm_compute); img_refl)).
s_runR HR tfxtbl_rtD tfxtbl_rtD_ok (0x67db0 + D_2c4) DG8r HX HP.
s_noconds HR. s_station HR DG8_0. img_apply SRr_ret. img_exact HR.
Qed.
Lemma segD1_12 : forall (W' : world tfxsegs) c, at_S Wy md1 XZ PZ D_1_12 W' c -> SRr tfxsegs W' c (at_S Wy md1 XZ PZ DG12_0).
Proof.
intros W' c HR. pose proof WIN1R_XZ as HX. pose proof PZ_stable as HP.
s_runR HR tfxtbl_rtD tfxtbl_rtD_ok (0x6448c + D_2c4) D_M12 HX HP.
s_arm HR BC_EQ false MS_AL12 (SLit 0).
{ destruct Hsp as (S1 & _ & _ & S4). pose proof (u64_range (getr regs0 2)) as U2. pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7).
clear - S1 S4 U2 T7. unfold MS_AL12. arm_zevS. rewrite E2. numconst. try unfold sp0 in *.
repeat match goal with |- context [zcanon ?x] => lazymatch x with context [ew _ _] => fail | context [getr _ _] => fail | _ => let y := img_ev (zcanon x) in img_change (zcanon x) with y end end.
rewrite (zcanon_id (bv_unsigned (getr regs0 2) + _)) by (img_try (unfold M64; zlia)).
rewrite land15_lor240.
lazymatch goal with |- context [(?a mod 16)] =>
pose proof (Z.div_mod a 16 ltac:(img_try (zlia))) as D1; pose proof (Z.mod_pos_bound a 16 ltac:(img_try (zlia))) as B1 end.
pose proof (Z.div_mod (bv_unsigned (getr regs0 2)) 16 ltac:(img_try (zlia))) as D0.
rewrite zcanon_id by (img_try (unfold M64; zlia)). img_apply Z.eqb_neq. zlia. }
s_runR HR tfxtbl_rtD tfxtbl_rtD_ok (0x67db0 + D_2c4) DG12r HX HP.
s_noconds HR. s_station HR DG12_0. img_apply SRr_ret. img_exact HR.
Qed.
Definition dia_side {imgk : img} (k : nat) (tk : bool) (ss J : sstate) : Prop :=
let r := sym_run_toN_sh tfxsegs tfxtbl_rtD FUEL (0x67d88 + D_2c4) (arm BC_GEU tk (dia_lhs ss) (SLit 10) ss) in
(match snd r with RS_ecall => false | _ => true end
&& stack_shaped (fst r) && (match ss_resv (fst r) with None => true | Some _ => false end)
&& ss_atoms_lt k (fst r) && regions_wf (ss_mem (fst r)) && no_cdata (ss_mem (fst r)) && mem_atoms_lt k (ss_mem (fst r))) = true
/\ noconds (forget (fst r) k [16%bv]) = J.
Lemma diamond : forall (k : nat) (ss J : sstate),
(sHAV <= k)%nat -> sv_atoms_lt sHAV (dia_lhs ss) = true -> wins_ok WSKEL1R (ss_mem ss) = true ->
dia_side k true ss J -> dia_side k false ss J ->
forall (W' : world tfxsegs) c, at_S Wy md1 XZ PZ ss W' c -> SRr tfxsegs W' c (at_S Wy md1 XZ PZ J).
Proof.
intros k ss J Hk Hlhs Hwin HT HF W' c HR. pose proof WIN1R_XZ as HX. pose proof PZ_stable as HP.
assert (ARM : forall tk : bool, dia_side k tk ss J -> branch_taken BC_GEU (sv_denot E0 (dia_lhs ss)) (sv_denot E0 (SLit 10)) = tk ->
SRr tfxsegs W' c (at_S Wy md1 XZ PZ J)).
{ intros tk [CHK EQ] HB. unfold dia_side in CHK, EQ.
destruct (sym_run_toN_sh tfxsegs tfxtbl_rtD FUEL (0x67d88 + D_2c4) (arm BC_GEU tk (dia_lhs ss) (SLit 10) ss)) as [j st] eqn:RUN. cbn [fst snd] in CHK, EQ.
apply andb_prop in CHK as [CHK A7]. apply andb_prop in CHK as [CHK A6]. apply andb_prop in CHK as [CHK A5].
apply andb_prop in CHK as [CHK A4]. apply andb_prop in CHK as [CHK A3]. apply andb_prop in CHK as [A1 A2].
assert (Hst : match st with RS_ecall => False | _ => True end) by (img_try (destruct st; first [img_exact I | discriminate A1])).
assert (Hrv : ss_resv j = None) by (img_try (destruct (ss_resv j); [img_try (discriminate A3) | img_refl])).
pose proof (at_S_arm Wy md1 XZ PZ ss W' c BC_GEU tk (dia_lhs ss) (SLit 10) HR Hlhs ltac:(img_eqrefl) HB) as HR1.
eapply SRr_bind.
- img_exact (at_S_runR Wy tfxtbl_rtD tfxtbl_rtD_ok (0x67d88 + D_2c4) md1 XZ PZ _ j st W' c HR1 RUN Hst HX Hwin HP A2).
- intros W2 c2 _ HR2.
pose proof (at_S_forget Wy md1 XZ PZ j W2 c2 k [16%bv] HR2 Hk Hrv A4 A5 A6 A7 ltac:(img_eqrefl) ltac:(img_eqrefl)) as HR3.
img_apply SRr_ret. rewrite <- EQ. img_exact (at_S_noconds _ _ _ _ _ _ _ HR3). }
assert (BC : forall b : bool, b = true \/ b = false) by (img_try (intros [|]; [img_try (left) | img_try (right)]; img_refl)).
destruct (BC (branch_taken BC_GEU (sv_denot E0 (dia_lhs ss)) (sv_denot E0 (SLit 10)))) as [TK|TK]; [img_try (img_exact (ARM true HT TK)) | img_try (img_exact (ARM false HF TK))].
Qed.
Local Ltac s_dia HR k ss J :=
lazymatch type of HR with at_S _ _ _ _ _ ?W' ?c' =>
eapply SRr_bind;
[ img_try (eapply (diamond k ss J ltac:(unfold sHAV, aDIG; zlia) ltac:((try img_inst; img_case; vm_compute); img_refl) ltac:((try img_inst; img_case; vm_compute); img_refl)
ltac:(split; (img_case; vm_compute); img_refl) ltac:(split; (img_case; vm_compute); img_refl) W' c' HR))
| img_try (clear HR; let W2 := fresh "W" in let c2 := fresh "c" in intros W2 c2 _ HR) ] end.
Lemma digits_6 : forall (W' : world tfxsegs) c, at_S Wy md1 XZ PZ DG6_0 W' c -> SRr tfxsegs W' c (at_S Wy md1 XZ PZ DJ6_5).
Proof.
intros W' c HR. pose proof WIN1R_XZ as HX. pose proof PZ_stable as HP.
s_dia HR (aDIG + 0)%nat DG6_0 DJ6_0. s_runR HR tfxtbl_rtD tfxtbl_rtD_ok (0x67db0 + D_2c4) DG6_1 HX HP.
s_dia HR (aDIG + 1)%nat DG6_1 DJ6_1. s_runR HR tfxtbl_rtD tfxtbl_rtD_ok (0x67db0 + D_2c4) DG6_2 HX HP.
s_dia HR (aDIG + 2)%nat DG6_2 DJ6_2. s_runR HR tfxtbl_rtD tfxtbl_rtD_ok (0x67db0 + D_2c4) DG6_3 HX HP.
s_dia HR (aDIG + 3)%nat DG6_3 DJ6_3. s_runR HR tfxtbl_rtD tfxtbl_rtD_ok (0x67db0 + D_2c4) DG6_4 HX HP.
s_dia HR (aDIG + 4)%nat DG6_4 DJ6_4. s_runR HR tfxtbl_rtD tfxtbl_rtD_ok (0x67db0 + D_2c4) DG6_5 HX HP.
s_dia HR (aDIG + 5)%nat DG6_5 DJ6_5. img_apply SRr_ret. img_exact HR.
Qed.
Lemma digits_7 : forall (W' : world tfxsegs) c, at_S Wy md1 XZ PZ DG7_0 W' c -> SRr tfxsegs W' c (at_S Wy md1 XZ PZ DJ7_6).
Proof.
intros W' c HR. pose proof WIN1R_XZ as HX. pose proof PZ_stable as HP.
s_dia HR (aDIG + 0)%nat DG7_0 DJ7_0. s_runR HR tfxtbl_rtD tfxtbl_rtD_ok (0x67db0 + D_2c4) DG7_1 HX HP.
s_dia HR (aDIG + 1)%nat DG7_1 DJ7_1. s_runR HR tfxtbl_rtD tfxtbl_rtD_ok (0x67db0 + D_2c4) DG7_2 HX HP.
s_dia HR (aDIG + 2)%nat DG7_2 DJ7_2. s_runR HR tfxtbl_rtD tfxtbl_rtD_ok (0x67db0 + D_2c4) DG7_3 HX HP.
s_dia HR (aDIG + 3)%nat DG7_3 DJ7_3. s_runR HR tfxtbl_rtD tfxtbl_rtD_ok (0x67db0 + D_2c4) DG7_4 HX HP.
s_dia HR (aDIG + 4)%nat DG7_4 DJ7_4. s_runR HR tfxtbl_rtD tfxtbl_rtD_ok (0x67db0 + D_2c4) DG7_5 HX HP.
s_dia HR (aDIG + 5)%nat DG7_5 DJ7_5. s_runR HR tfxtbl_rtD tfxtbl_rtD_ok (0x67db0 + D_2c4) DG7_6 HX HP.
s_dia HR (aDIG + 6)%nat DG7_6 DJ7_6. img_apply SRr_ret. img_exact HR.
Qed.
Lemma digits_8 : forall (W' : world tfxsegs) c, at_S Wy md1 XZ PZ DG8_0 W' c -> SRr tfxsegs W' c (at_S Wy md1 XZ PZ DJ8_7).
Proof.
intros W' c HR. pose proof WIN1R_XZ as HX. pose proof PZ_stable as HP.
s_dia HR (aDIG + 0)%nat DG8_0 DJ8_0. s_runR HR tfxtbl_rtD tfxtbl_rtD_ok (0x67db0 + D_2c4) DG8_1 HX HP.
s_dia HR (aDIG + 1)%nat DG8_1 DJ8_1. s_runR HR tfxtbl_rtD tfxtbl_rtD_ok (0x67db0 + D_2c4) DG8_2 HX HP.
s_dia HR (aDIG + 2)%nat DG8_2 DJ8_2. s_runR HR tfxtbl_rtD tfxtbl_rtD_ok (0x67db0 + D_2c4) DG8_3 HX HP.
s_dia HR (aDIG + 3)%nat DG8_3 DJ8_3. s_runR HR tfxtbl_rtD tfxtbl_rtD_ok (0x67db0 + D_2c4) DG8_4 HX HP.
s_dia HR (aDIG + 4)%nat DG8_4 DJ8_4. s_runR HR tfxtbl_rtD tfxtbl_rtD_ok (0x67db0 + D_2c4) DG8_5 HX HP.
s_dia HR (aDIG + 5)%nat DG8_5 DJ8_5. s_runR HR tfxtbl_rtD tfxtbl_rtD_ok (0x67db0 + D_2c4) DG8_6 HX HP.
s_dia HR (aDIG + 6)%nat DG8_6 DJ8_6. s_runR HR tfxtbl_rtD tfxtbl_rtD_ok (0x67db0 + D_2c4) DG8_7 HX HP.
s_dia HR (aDIG + 7)%nat DG8_7 DJ8_7. img_apply SRr_ret. img_exact HR.
Qed.
Lemma digits_12 : forall (W' : world tfxsegs) c, at_S Wy md1 XZ PZ DG12_0 W' c -> SRr tfxsegs W' c (at_S Wy md1 XZ PZ DJ12_11).
Proof.
intros W' c HR. pose proof WIN1R_XZ as HX. pose proof PZ_stable as HP.
s_dia HR (aDIG + 0)%nat DG12_0 DJ12_0. s_runR HR tfxtbl_rtD tfxtbl_rtD_ok (0x67db0 + D_2c4) DG12_1 HX HP.
s_dia HR (aDIG + 1)%nat DG12_1 DJ12_1. s_runR HR tfxtbl_rtD tfxtbl_rtD_ok (0x67db0 + D_2c4) DG12_2 HX HP.
s_dia HR (aDIG + 2)%nat DG12_2 DJ12_2. s_runR HR tfxtbl_rtD tfxtbl_rtD_ok (0x67db0 + D_2c4) DG12_3 HX HP.
s_dia HR (aDIG + 3)%nat DG12_3 DJ12_3. s_runR HR tfxtbl_rtD tfxtbl_rtD_ok (0x67db0 + D_2c4) DG12_4 HX HP.
s_dia HR (aDIG + 4)%nat DG12_4 DJ12_4. s_runR HR tfxtbl_rtD tfxtbl_rtD_ok (0x67db0 + D_2c4) DG12_5 HX HP.
s_dia HR (aDIG + 5)%nat DG12_5 DJ12_5. s_runR HR tfxtbl_rtD tfxtbl_rtD_ok (0x67db0 + D_2c4) DG12_6 HX HP.
s_dia HR (aDIG + 6)%nat DG12_6 DJ12_6. s_runR HR tfxtbl_rtD tfxtbl_rtD_ok (0x67db0 + D_2c4) DG12_7 HX HP.
s_dia HR (aDIG + 7)%nat DG12_7 DJ12_7. s_runR HR tfxtbl_rtD tfxtbl_rtD_ok (0x67db0 + D_2c4) DG12_8 HX HP.
s_dia HR (aDIG + 8)%nat DG12_8 DJ12_8. s_runR HR tfxtbl_rtD tfxtbl_rtD_ok (0x67db0 + D_2c4) DG12_9 HX HP.
s_dia HR (aDIG + 9)%nat DG12_9 DJ12_9. s_runR HR tfxtbl_rtD tfxtbl_rtD_ok (0x67db0 + D_2c4) DG12_10 HX HP.
s_dia HR (aDIG + 10)%nat DG12_10 DJ12_10. s_runR HR tfxtbl_rtD tfxtbl_rtD_ok (0x67db0 + D_2c4) DG12_11 HX HP.
s_dia HR (aDIG + 11)%nat DG12_11 DJ12_11. img_apply SRr_ret. img_exact HR.
Qed.
Lemma segEND_6 : forall (W' : world tfxsegs) c, at_S Wy md1 XZ PZ DJ6_5 W' c ->
SRr tfxsegs W' c (fun (W'' : world tfxsegs) (c'' : config) => is_self_jump tfxsegs (cfg_ms c'') = true).
Proof.
intros W' c HR. pose proof WIN1R_XZ as HX. pose proof PZ_stable as HP.
s_runR HR tfxtbl_rtD tfxtbl_rtD_ok (0x60500 + D_2c4) D_END6 HX HP.
img_apply SRr_ret. destruct HR as (_ & ms & mat & E' & -> & HE & HS & MEQ & PRS & HPm). cbn [cfg_ms].
pose proof (st_ok_restrict_mkst tfxsegs (w_H Wy) E' D_END6 ms HS ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))) as SH.
pose proof (f_equal ms_svc_pending SH) as Hsv. pose proof (f_equal ms_pc_val SH) as Hpc. cbn [ms_svc_pending ms_pc_val YK11.mkst] in Hsv, Hpc.
replace (ss_pc D_END6) with (0x60500 + D_2c4) in Hpc by (img_try ((img_case; vm_compute); img_refl)).
unfold is_self_jump, ms_pc. rewrite Hsv, Hpc. rewrite (tfxtbl_rtD_ok (0x60500 + D_2c4) 111 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))). img_case; vm_compute. all: img_refl.
Qed.
Lemma segEND_7 : forall (W' : world tfxsegs) c, at_S Wy md1 XZ PZ DJ7_6 W' c ->
SRr tfxsegs W' c (fun (W'' : world tfxsegs) (c'' : config) => is_self_jump tfxsegs (cfg_ms c'') = true).
Proof.
intros W' c HR. pose proof WIN1R_XZ as HX. pose proof PZ_stable as HP.
s_runR HR tfxtbl_rtD tfxtbl_rtD_ok (0x60500 + D_2c4) D_END7 HX HP.
img_apply SRr_ret. destruct HR as (_ & ms & mat & E' & -> & HE & HS & MEQ & PRS & HPm). cbn [cfg_ms].
pose proof (st_ok_restrict_mkst tfxsegs (w_H Wy) E' D_END7 ms HS ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))) as SH.
pose proof (f_equal ms_svc_pending SH) as Hsv. pose proof (f_equal ms_pc_val SH) as Hpc. cbn [ms_svc_pending ms_pc_val YK11.mkst] in Hsv, Hpc.
replace (ss_pc D_END7) with (0x60500 + D_2c4) in Hpc by (img_try ((img_case; vm_compute); img_refl)).
unfold is_self_jump, ms_pc. rewrite Hsv, Hpc. rewrite (tfxtbl_rtD_ok (0x60500 + D_2c4) 111 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))). img_case; vm_compute. all: img_refl.
Qed.
Lemma segEND_8 : forall (W' : world tfxsegs) c, at_S Wy md1 XZ PZ DJ8_7 W' c ->
SRr tfxsegs W' c (fun (W'' : world tfxsegs) (c'' : config) => is_self_jump tfxsegs (cfg_ms c'') = true).
Proof.
intros W' c HR. pose proof WIN1R_XZ as HX. pose proof PZ_stable as HP.
s_runR HR tfxtbl_rtD tfxtbl_rtD_ok (0x60500 + D_2c4) D_END8 HX HP.
img_apply SRr_ret. destruct HR as (_ & ms & mat & E' & -> & HE & HS & MEQ & PRS & HPm). cbn [cfg_ms].
pose proof (st_ok_restrict_mkst tfxsegs (w_H Wy) E' D_END8 ms HS ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))) as SH.
pose proof (f_equal ms_svc_pending SH) as Hsv. pose proof (f_equal ms_pc_val SH) as Hpc. cbn [ms_svc_pending ms_pc_val YK11.mkst] in Hsv, Hpc.
replace (ss_pc D_END8) with (0x60500 + D_2c4) in Hpc by (img_try ((img_case; vm_compute); img_refl)).
unfold is_self_jump, ms_pc. rewrite Hsv, Hpc. rewrite (tfxtbl_rtD_ok (0x60500 + D_2c4) 111 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))). img_case; vm_compute. all: img_refl.
Qed.
Lemma segEND_12 : forall (W' : world tfxsegs) c, at_S Wy md1 XZ PZ DJ12_11 W' c ->
SRr tfxsegs W' c (fun (W'' : world tfxsegs) (c'' : config) => is_self_jump tfxsegs (cfg_ms c'') = true).
Proof.
intros W' c HR. pose proof WIN1R_XZ as HX. pose proof PZ_stable as HP.
s_runR HR tfxtbl_rtD tfxtbl_rtD_ok (0x60500 + D_2c4) D_END12 HX HP.
img_apply SRr_ret. destruct HR as (_ & ms & mat & E' & -> & HE & HS & MEQ & PRS & HPm). cbn [cfg_ms].
pose proof (st_ok_restrict_mkst tfxsegs (w_H Wy) E' D_END12 ms HS ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))) as SH.
pose proof (f_equal ms_svc_pending SH) as Hsv. pose proof (f_equal ms_pc_val SH) as Hpc. cbn [ms_svc_pending ms_pc_val YK11.mkst] in Hsv, Hpc.
replace (ss_pc D_END12) with (0x60500 + D_2c4) in Hpc by (img_try ((img_case; vm_compute); img_refl)).
unfold is_self_jump, ms_pc. rewrite Hsv, Hpc. rewrite (tfxtbl_rtD_ok (0x60500 + D_2c4) 111 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))). img_case; vm_compute. all: img_refl.
Qed.
Theorem dieV : idx = res -> forall c, at_S Wy md1 XZ PZ D_0 Wy c -> AI tfxsegs (w_H Wy) (w_A Wy) (cfg_model c) -> srealizesM tfxsegs false c t_nil.
Proof.
intros Heq c HR HAI.
assert (SR : SRr tfxsegs Wy c (fun (W'' : world tfxsegs) (c'' : config) => is_self_jump tfxsegs (cfg_ms c'') = true)).
{ apply (D_1_ok Heq) in HR.
pose proof (QR_facts Heq) as (E1 & _ & QA & F9 & Q5 & F10 & _). pose proof Hidx as HI. pose proof Hres as [HRS _].
assert (Q8 : QSv mod 8 = 0) by (img_try (clear - QA; apply Z.mod_divide in QA as [q Hq]; [|img_try (zlia)]; rewrite Hq; replace (q * 4096) with ((q * 512) * 8) by zlia; img_apply Z_mod_mult)).
apply Z.mod_divide in Q8 as [q8 Hq8]; [|img_try (zlia)].
assert (CASES : (16 ^ 5 <= QSv <= 16 ^ 6 - 8) \/ (16 ^ 6 <= QSv <= 16 ^ 7 - 8) \/ (16 ^ 7 <= QSv <= 16 ^ 8 - 8) \/ (16 ^ 11 <= QSv <= 16 ^ 12 - 8)).
{ clear - F9 Q5 F10 Hq8. ceil. unfold zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kPtrArrayResv in *. try unfold Qb in *.
img_change (16 ^ 5) with 1048576. img_change (16 ^ 6) with 16777216. img_change (16 ^ 7) with 268435456. img_change (16 ^ 8) with 4294967296.
img_change (16 ^ 11) with 17592186044416. img_change (16 ^ 12) with 281474976710656. zlia. }
destruct CASES as [C6|[C7|[C8|C12]]].
- apply (at_S_tighten _ _ _ _ _ _ _ aQS (YF4f.hexfact 6)) in HR; [| img_try (unfold aQS, sHAV; zlia) | img_try (img_exact (hexfact_ok 6 C6))].
replace (YF4f.tighten aQS (YF4f.hexfact 6) D_1) with D_1_6 in HR by (img_try ((img_case; vm_compute); img_refl)).
eapply SRr_bind; [img_try (img_exact (segD1_6 Wy c HR))|]. clear HR. intros W1 c1 _ HR.
eapply SRr_bind; [img_try (img_exact (digits_6 W1 c1 HR))|]. clear HR. intros W2 c2 _ HR. img_exact (segEND_6 W2 c2 HR).
- apply (at_S_tighten _ _ _ _ _ _ _ aQS (YF4f.hexfact 7)) in HR; [| img_try (unfold aQS, sHAV; zlia) | img_try (img_exact (hexfact_ok 7 C7))].
replace (YF4f.tighten aQS (YF4f.hexfact 7) D_1) with D_1_7 in HR by (img_try ((img_case; vm_compute); img_refl)).
eapply SRr_bind; [img_try (img_exact (segD1_7 Wy c HR))|]. clear HR. intros W1 c1 _ HR.
eapply SRr_bind; [img_try (img_exact (digits_7 W1 c1 HR))|]. clear HR. intros W2 c2 _ HR. img_exact (segEND_7 W2 c2 HR).
- apply (at_S_tighten _ _ _ _ _ _ _ aQS (YF4f.hexfact 8)) in HR; [| img_try (unfold aQS, sHAV; zlia) | img_try (img_exact (hexfact_ok 8 C8))].
replace (YF4f.tighten aQS (YF4f.hexfact 8) D_1) with D_1_8 in HR by (img_try ((img_case; vm_compute); img_refl)).
eapply SRr_bind; [img_try (img_exact (segD1_8 Wy c HR))|]. clear HR. intros W1 c1 _ HR.
eapply SRr_bind; [img_try (img_exact (digits_8 W1 c1 HR))|]. clear HR. intros W2 c2 _ HR. img_exact (segEND_8 W2 c2 HR).
- apply (at_S_tighten _ _ _ _ _ _ _ aQS (YF4f.hexfact 12)) in HR; [| img_try (unfold aQS, sHAV; zlia) | img_try (img_exact (hexfact_ok 12 C12))].
replace (YF4f.tighten aQS (YF4f.hexfact 12) D_1) with D_1_12 in HR by (img_try ((img_case; vm_compute); img_refl)).
eapply SRr_bind; [img_try (img_exact (segD1_12 Wy c HR))|]. clear HR. intros W1 c1 _ HR.
eapply SRr_bind; [img_try (img_exact (digits_12 W1 c1 HR))|]. clear HR. intros W2 c2 _ HR. img_exact (segEND_12 W2 c2 HR).
}
img_apply (SR false HAI t_nil). intros W' c' _ HI' HJ. img_apply srz_spinning.
split; [img_try (img_apply is_self_jump_to_spin; img_exact HJ) | img_try (img_exact (AI_halted _ _ _ _ HI'))].
Qed.
End h.
End g.
