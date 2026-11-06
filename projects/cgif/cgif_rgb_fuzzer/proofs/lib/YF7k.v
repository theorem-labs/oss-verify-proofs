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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF64 YF3v YF3w YF3x YF41 YF6z YF0a YF7f.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK0v YA09.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF71 YF72 YF0h YF7o YF7p YF7q YF7a YF7g YF7h YF7d YF7i YF7j.
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
Local Abbreviation ARf f := (f idx res Hidx) (only parsing).
Local Abbreviation tr_length := (ARf ((AR1 (@YF7f.tr_length)) ch)).
Local Abbreviation ARe f := (f idx res LY IMG Hidx Hres) (only parsing).
Local Abbreviation high_facts := (ARe (AR1 (@YF7f.high_facts _))).
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
Local Abbreviation AR4 f := (f Nrange Hidx Hres Hmap) (only parsing).
Local Abbreviation map_facts := (AR4 (AR3 (@YF7f.map_facts _))).
Local Abbreviation map_zone := ((AR3 (@YF7f.map_zone _)) Nrange Hidx Hmap).
Local Abbreviation map_zoneN := (AR4 (AR3 (@YF7f.map_zoneN _))).
Local Abbreviation map_in_band := ((AR3 (@YF7f.map_in_band _)) Nrange Hidx Hmap).
Local Abbreviation map_off_img := (@YF7f.map_off_img _ imgk n mb Hmap).
Local Abbreviation WINT := (@YF7f.WINT ly).
Local Abbreviation WINI := (@YF7f.WINI n imgk).
Local Abbreviation WINM := (@YF7f.WINM ly n idx mb).
Local Abbreviation ARc f := (AR1 f n idx mb) (only parsing).
Local Abbreviation WIN := (ARc (@YF7f.WIN)).
Local Abbreviation WINN := (AR1 (@YF7f.WINN)).
Local Abbreviation WINP := ((AR1 (@YF7f.WINP)) n).
Local Abbreviation WINP_WIN := (ARc (@YF7f.WINP_WIN)).
Local Abbreviation WIN1P := ((AR1 (@YF7f.WIN1P)) n).
Local Abbreviation WIN1 := (ARc (@YF7f.WIN1)).
Local Abbreviation WIN1P_WINP := ((AR3 (@YF7f.WIN1P_WINP)) Hidx).
Local Abbreviation WIN1_WIN := ((AR3 (@YF7f.WIN1_WIN)) Hidx).
Local Abbreviation WIN1P_WIN1 := (ARc (@YF7f.WIN1P_WIN1)).
Local Abbreviation LGv_range := (@YF7f.LGv_range n Nrange).
Local Abbreviation BSLv_range := ((AR3 (@YF7f.BSLv_range)) Nrange Hidx).
Local Abbreviation WSKELP := (@YF7f.WSKELP imgk).
Local Abbreviation WSKEL1P := (@YF7f.WSKEL1P imgk).
Local Abbreviation WMAP := (@YF7f.WMAP).
Local Abbreviation WSKEL := (@YF7f.WSKEL imgk).
Local Abbreviation WSKEL1 := (@YF7f.WSKEL1 imgk).
Local Abbreviation win_sub := (@YF7f.win_sub).
Local Abbreviation AR9 f := (f idx res mb) (only parsing).
Local Abbreviation win_sub_sound := ((AR9 (@YF7f.win_sub_sound ly regs0)) Hidx Hres).
Local Abbreviation in_win := (@YF7f.in_win).
Local Abbreviation AR7 f := (AR0 f LY IMG) (only parsing).
Local Abbreviation ARd f := (f Nrange Hidx Hres) (only parsing).
Local Abbreviation WSKELP_WINP := (ARd (AR7 (AR1 (@YF7f.WSKELP_WINP _)))).
Local Abbreviation WSKEL1P_WIN1P := (ARd (AR7 (AR1 (@YF7f.WSKEL1P_WIN1P _)))).
Local Abbreviation WMAP_WINM := (AR4 (AR7 (AR1 (@YF7f.WMAP_WINM _)))).
Local Abbreviation WSKEL_WIN := (AR4 (AR7 (AR1 (@YF7f.WSKEL_WIN _)))).
Local Abbreviation WSKEL1_WIN1 := (AR4 (AR7 (AR1 (@YF7f.WSKEL1_WIN1 _)))).
Local Abbreviation windows_in := ((AR9 (@YF7f.windows_in ly regs0)) Hidx Hres).
Local Abbreviation windows_WINP := (ARd (AR7 (AR1 (@YF7f.windows_WINP _)))).
Local Abbreviation windows_WIN1P := (ARd (AR7 (AR1 (@YF7f.windows_WIN1P _)))).
Local Abbreviation windows_WIN := (AR4 (AR7 (AR1 (@YF7f.windows_WIN _)))).
Local Abbreviation windows_WIN1 := (AR4 (AR7 (AR1 (@YF7f.windows_WIN1 _)))).
Local Abbreviation frame_WIN1P := (ARd (AR7 (AR1 (@YF7f.frame_WIN1P _)))).
Local Abbreviation frame_WIN1 := (AR4 (AR7 (AR1 (@YF7f.frame_WIN1 _)))).
Local Abbreviation AR2 f := (f LY IMG Hsp Nrange Hidx Hres) (only parsing).
Local Abbreviation WINP_not_high := (AR2 (AR3 (@YF7f.WINP_not_high _))).
Local Abbreviation ARh f := (AR2 f Hmap) (only parsing).
Local Abbreviation WIN_not_high := (ARh (AR3 (@YF7f.WIN_not_high _))).
Variables (mat0 : list word).
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 (0x53108 + D_2c4)) mem0 (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis U1 : tfx_unwind_spec.
Local Abbreviation all_disjoint_of_forall := (@YF7f.all_disjoint_of_forall).
Local Abbreviation img_rw_writable := ((AR9 (AR1 (@YF7f.img_rw_writable))) Hidx).
Local Abbreviation ARg f := (f imgk W ly) (only parsing).
Local Abbreviation kept_of_frame := ((AR9 ((ARg (@YF7f.kept_of_frame)) regs0)) Hidx).
Local Abbreviation SKEL_TAIL := (@YF7f.SKEL_TAIL imgk).
Local Abbreviation blocks_facts := (@YF7f.blocks_facts _ imgk ly LY IMG).
Local Abbreviation off_T := (ARe (AR1 (@YF7f.off_T _))).
Local Abbreviation off_C := (ARe (AR1 (@YF7f.off_C _))).
Local Abbreviation off_Q := (ARe (AR1 (@YF7f.off_Q _))).
Local Abbreviation off_NB := (@YF7f.off_NB _ imgk ly LY IMG).
Local Abbreviation off_SB := (@YF7f.off_SB _ imgk ly LY IMG).
Local Abbreviation off_shadow := ((AR9 (AR1 (@YF7f.off_shadow))) Hidx).
Ltac off_by tac :=
first [ img_apply off_img_high; tac | img_apply off_T; tac | img_apply off_C; tac | img_apply off_Q; tac | img_apply off_NB; tac | img_apply off_SB; tac
| img_apply map_off_img; tac | img_apply off_shadow; tac
| unfold off_img; unfold TFX_IMG_LO; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; tac ].
Local Abbreviation DZONE := (@YF7f.DZONE imgk ly).
Variable DPOST : Z -> (word -> option byte) -> Prop.
Local Abbreviation ARb f := (AR2 f Hmap Hmap_apart) (only parsing).
Local Abbreviation DZONE_disj := (ARb (AR3 (@YF7f.DZONE_disj _))).
Local Abbreviation RFACTS := (AR1 (@YF7f.RFACTS)).
Local Abbreviation zone_lit := ((AR1 (@YF7f.zone_lit _)) LY IMG Hsp).
Local Abbreviation zone_irw := ((AR1 (@YF7f.zone_irw _)) LY IMG Hsp).
Local Abbreviation zone_T := ((AR1 (@YF7f.zone_T _)) idx res LY IMG Hsp Hidx Hres).
Local Abbreviation zone_C := ((AR1 (@YF7f.zone_C _)) idx res LY IMG Hsp Hidx Hres).
Local Abbreviation tail_ext_ok := (AR2 (AR0 (AR1 (@YF7f.tail_ext_ok _)))).
Local Abbreviation RFACTS_map := ((AR4 ((AR3 (@YF7f.RFACTS_map _)) LY IMG)) Hmap_apart).
Local Abbreviation AR5 f := (f imgk W ly regs0 mem0) (only parsing).
Local Abbreviation at_ST := (AR0 ((AR5 (@YF7f.at_ST _)) md0)).
Local Abbreviation memset_stretch := ((AR4 ((AR9 ((AR5 (@YF7f.memset_stretch _ _)) md0 n)) Hsp)) Hmap_apart mat0 DPOST).
Ltac clearM := try clear DPOST; try clear Hmap_apart; try clear Hmap.
Local Abbreviation AR6 f := (AR1 f mem0) (only parsing).
Local Abbreviation at_S := (AR0 (AR6 (@YF7f.at_S _))).
Local Abbreviation at_N := (AR0 (AR6 (@YF7f.at_N _))).
Local Abbreviation at_RETS := ((AR6 (@YF7f.at_RETS _)) ch).
Local Abbreviation pstable := (@YF7f.pstable).
Local Abbreviation stack_shaped := (@YF7f.stack_shaped).
Local Abbreviation window_present := (ARf (AR1 (@YF7f.window_present))).
Local Abbreviation stack_present_of := ((AR0 (AR1 (@YF7f.stack_present_of _))) LY Hsp Hidx).
Local Abbreviation mid_not_WIN1P := (AR2 (AR3 (@YF7f.mid_not_WIN1P _))).
Local Abbreviation mid_not_WIN1 := (ARh (AR3 (@YF7f.mid_not_WIN1 _))).
Local Abbreviation wins_ok := (@YF7f.wins_ok).
Local Abbreviation at_S_run_gen := ((AR0 (AR6 (@YF7f.at_S_run_gen _ _))) LY Hsp Hidx).
Local Abbreviation at_S_run_ecall_gen := ((AR0 (AR6 (@YF7f.at_S_run_ecall_gen _ _))) LY Hsp Hidx).
Local Abbreviation at_S_runP := (AR2 (AR0 (AR6 (@YF7f.at_S_runP _ _)))).
Local Abbreviation at_S_runM := (ARh (AR0 (AR6 (@YF7f.at_S_runM _ _)))).
Local Abbreviation at_S_run_ecallP := (AR2 (AR0 (AR6 (@YF7f.at_S_run_ecallP _ _)))).
Local Abbreviation at_S_run_ecallM := (ARh (AR0 (AR6 (@YF7f.at_S_run_ecallM _ _)))).
Local Abbreviation at_S_pin := (AR0 (AR6 (@YF7f.at_S_pin _))).
Local Abbreviation at_S_arm := (AR0 (AR6 (@YF7f.at_S_arm _))).
Local Abbreviation at_S_forget := (AR0 (AR6 (@YF7f.at_S_forget _))).
Local Abbreviation at_S_noconds := (AR0 (AR6 (@YF7f.at_S_noconds _))).
Local Abbreviation at_S_weaken := (AR0 (AR6 (@YF7f.at_S_weaken _))).
Local Abbreviation at_S_facts := (AR0 (AR6 (@YF7f.at_S_facts _))).
Local Abbreviation at_S_strengthen := (AR0 (AR6 (@YF7f.at_S_strengthen _))).
Local Abbreviation at_S_eq := (AR0 (AR6 (@YF7f.at_S_eq _))).
Local Abbreviation at_S_open := (AR0 (AR6 (@YF7f.at_S_open _))).
Local Abbreviation CSAVEDS := (@YF7f.CSAVEDS).
Local Abbreviation sv_denot_SOff0 := (@YF7f.sv_denot_SOff0).
Local Abbreviation at_S_ret := (ARd ((AR0 (AR6 (@YF7f.at_S_ret _))) Htp Hra Hsp)).
Local Abbreviation kept_of_frame2 := (ARf (AR1 (@YF7f.kept_of_frame2))).
Local Abbreviation at_N_cont := ((AR0 (AR6 (@YF7f.at_N_cont _ _))) LY Hsp Hidx).
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
Local Abbreviation vis_present := ((ARf (AR5 (@YF7o.vis_present _))) DPOST B S HARm).
Local Abbreviation in_thread_junk := (@YF7o.in_thread_junk ly B S).
Local Abbreviation in_sec_junk := (@YF7o.in_sec_junk ly B S).
Local Abbreviation in_as_junk := (@YF7o.in_as_junk ly B S).
Local Abbreviation junk_word := ((ARe (AR5 (@YF7o.junk_word _))) DPOST B S HARm).
Local Abbreviation cell_sym := ((ARg (@YF7o.cell_sym _)) mem0 B S TS HARm).
Local Abbreviation cell_lit := ((ARg (@YF7o.cell_lit _)) mem0 B S TS HARm).
Local Abbreviation cell_state := ((ARg (@YF7o.cell_state _)) mem0 B S HARm).
Local Abbreviation In_acells_sec := (@YF7o.In_acells_sec ly B S).
Local Abbreviation sec_vals := ((ARg (@YF7o.sec_vals _)) mem0 idx res B S TS HARm Hidx_def Hres_def).
Local Abbreviation unwinding_val := ((ARg (@YF7o.unwinding_val _)) mem0 B S HARm).
Local Abbreviation rw_writable := ((ARf (AR1 (@YF7o.rw_writable))) DPOST S).
Local Abbreviation val_mem_mod8 := ((ARf (AR5 (@YF7o.val_mem_mod8))) DPOST S).
Local Abbreviation chunk_lit := (AR0 (AR5 (@YF7o.chunk_lit))).
Local Abbreviation chunk_lit_at := (AR0 (AR5 (@YF7o.chunk_lit_at))).
Local Abbreviation chunk_atom := ((AR0 (AR5 (@YF7o.chunk_atom))) Hidx DPOST S).
Local Abbreviation ARa f := (f DPOST B S TS HTSD HARm Hidx_def Hres_def Hj0 Hj1 Hj2 Hj3 Hj4 Hj5 Hj9 Hj6 Hj7 Hj8 Hi1 Hi2 Hi3) (only parsing).
Local Abbreviation SREG0_ok := (ARa ((AR2 (AR0 (AR5 (@YF7p.SREG0_ok _)))) Hpres0)).
Local Abbreviation PAIRS_ok := ((AR2 (AR0 (AR5 (@YF7q.PAIRS_ok _)))) DPOST S).
Local Abbreviation FACTS_ok := ((ARd ((AR7 (AR5 (@YF7q.FACTS_ok _))) Hn Hsp)) DPOST S).
Local Abbreviation SEED_ok := (ARa ((ARd ((AR7 (AR5 (@YF7q.SEED_ok _ _))) Hn Hsp)) Hpres0)).
Local Abbreviation PBUF := ((ARg (@YF7a.PBUF)) regs0 ch).
Local Abbreviation PBUF_stableP := (AR2 (AR9 ((ARg (@YF7a.PBUF_stableP _)) regs0 n ch))).
Local Abbreviation PBUF_stableM := (ARh (AR9 ((ARg (@YF7a.PBUF_stableM _)) regs0 n ch))).
Local Abbreviation seg0 := (ARa ((ARd ((AR7 ((AR5 (@YF7a.seg0 _ _)) md0)) Hn Htp Hra4096 Hsp Hch)) Hpres0 mat0 U1)).
Local Abbreviation appregs := (@YF7g.appregs).
Local Abbreviation st_ok_appregs := (@YF7g.st_ok_appregs _ imgk).
Local Abbreviation at_S_app := (AR0 (AR6 (@YF7g.at_S_app _))).
Local Abbreviation WIN1N := ((AR1 (@YF7g.WIN1N)) n).
Local Abbreviation WINPN := ((AR1 (@YF7g.WINPN)) n).
Local Abbreviation WSKEL1N := (@YF7g.WSKEL1N imgk).
Local Abbreviation WIN1N_WINPN := ((AR3 (@YF7g.WIN1N_WINPN)) Hidx).
Local Abbreviation windows_WIN1N := (ARd (AR7 (AR1 (@YF7g.windows_WIN1N _)))).
Local Abbreviation mid_not_WIN1N := (AR2 (AR3 (@YF7g.mid_not_WIN1N _))).
Local Abbreviation at_S_runN := (AR2 (AR0 (AR6 (@YF7g.at_S_runN _ _)))).
Local Abbreviation PBUF_stableN := (AR2 (AR9 ((ARg (@YF7g.PBUF_stableN _)) regs0 n ch))).
Local Abbreviation at_S_val := (AR0 (AR6 (@YF7g.at_S_val _))).
Local Abbreviation memset_stretchW := ((ARd ((AR5 (@YF7g.memset_stretchW _)) md0 n idx res Hsp)) mat0 DPOST S).
Local Abbreviation at_S_memset := ((ARd ((AR0 ((AR5 (@YF7g.at_S_memset _)) md0)) Hsp)) mat0 DPOST S).
Local Abbreviation WIN1T := (ARc (@YF7g.WIN1T)).
Local Abbreviation WIN1T_WIN := (AR4 (AR3 (@YF7g.WIN1T_WIN _))).
Local Abbreviation windows_WIN1T := (AR4 (AR7 (AR1 (@YF7g.windows_WIN1T _)))).
Local Abbreviation WIN1T_WIN1_aux := (AR4 (AR3 (@YF7g.WIN1T_WIN1_aux _))).
Local Abbreviation mid_not_WIN1T := (ARh (AR3 (@YF7g.mid_not_WIN1T _))).
Local Abbreviation at_S_runT := (ARh (AR0 (AR6 (@YF7g.at_S_runT _ _)))).
Local Abbreviation at_S_run_ecallT := (ARh (AR0 (AR6 (@YF7g.at_S_run_ecallT _ _)))).
Local Abbreviation PBUFW := ((AR1 (@YF7g.PBUFW)) ch).
Local Abbreviation ARi f := (AR1 f n ch) (only parsing).
Local Abbreviation PBUFW_stableT := (ARh (AR9 (ARi (@YF7g.PBUFW_stableT _)))).
Local Abbreviation WIN1S := (ARc (@YF7h.WIN1S)).
Local Abbreviation WSKEL1S := (@YF7h.WSKEL1S imgk).
Local Abbreviation WIN1S_WIN1T := (ARc (@YF7h.WIN1S_WIN1T)).
Local Abbreviation WIN1S_WIN := (AR4 (AR3 (@YF7h.WIN1S_WIN _))).
Local Abbreviation windows_WIN1S := (AR4 (AR7 (AR1 (@YF7h.windows_WIN1S _)))).
Local Abbreviation mid_not_WIN1S := (ARh (AR3 (@YF7h.mid_not_WIN1S _))).
Local Abbreviation at_S_runS := (ARh (AR0 (AR6 (@YF7h.at_S_runS _ _)))).
Local Abbreviation at_S_run_ecallS := (ARh (AR0 (AR6 (@YF7h.at_S_run_ecallS _ _)))).
Local Abbreviation brun := (@YF7h.brun).
Local Abbreviation run_ok := (@YF7h.run_ok n mb).
Local Abbreviation PS := ((ARi (@YF7h.PS)) mb).
Local Abbreviation runs_not_WIN1S := (ARb (AR3 (@YF7h.runs_not_WIN1S _))).
Local Abbreviation runs_not_stack := ((AR4 ((AR3 (@YF7h.runs_not_stack _)) LY Hsp)) Hmap_apart).
Local Abbreviation PS_stable := (ARb (AR9 (ARi (@YF7h.PS_stable _)))).
Local Abbreviation cut1 := (@YF7h.cut1).
Local Abbreviation cut := (@YF7h.cut).
Local Abbreviation cut_sound := ((AR4 (AR9 ((AR6 (@YF7h.cut_sound _)) n))) DPOST S).
Local Abbreviation cut_ok := ((AR9 (@YF7h.cut_ok ly regs0 mem0 n)) Hidx Hres DPOST S).
Local Abbreviation at_S_memsetS := ((AR4 ((AR0 ((AR5 (@YF7h.at_S_memsetS _ _)) md0)) LY Hsp)) Hmap_apart mat0 DPOST S).
Local Abbreviation skel_okb := (@YF7h.skel_okb imgk).
Local Abbreviation skel_cases := ((ARf (@YF7h.skel_cases imgk)) Hres S Hidx_def Hres_def).
Local Abbreviation AR8 f := (f DPOST S Hidx_def Hres_def) (only parsing).
Local Abbreviation skel_apart := (AR8 (ARb (AR0 (AR6 (@YF7h.skel_apart _))))).
Local Abbreviation skel_u64 := (AR8 (ARh (AR0 (AR6 (@YF7h.skel_u64 _))))).
Local Abbreviation memset_ext_of_skel := (AR8 (ARb (AR0 (AR6 (@YF7h.memset_ext_of_skel _))))).
Local Abbreviation memset_u64_of_skel := (AR8 (ARh (AR0 (AR6 (@YF7h.memset_u64_of_skel _))))).
Local Abbreviation WIN1R := ((AR1 (@YF7h.WIN1R)) n mb).
Local Abbreviation WSKEL1R := (@YF7h.WSKEL1R imgk).
Local Abbreviation WIN1R_WIN1S := (ARc (@YF7h.WIN1R_WIN1S)).
Local Abbreviation WIN1R_WIN := (AR4 (AR3 (@YF7h.WIN1R_WIN _))).
Local Abbreviation windows_WIN1R := (AR4 (AR7 (AR1 (@YF7h.windows_WIN1R _)))).
Local Abbreviation mid_not_WIN1R := (ARh (AR3 (@YF7h.mid_not_WIN1R _))).
Local Abbreviation at_S_runR := (ARh (AR0 (AR6 (@YF7h.at_S_runR _ _)))).
Local Abbreviation at_S_run_ecallR := (ARh (AR0 (AR6 (@YF7h.at_S_run_ecallR _ _)))).
Local Abbreviation PSR := ((ARi (@YF7h.PSR)) mb).
Local Abbreviation rstable := ((AR1 (@YF7h.rstable)) n mb).
Local Abbreviation rstable_true := ((AR1 (@YF7h.rstable_true)) n mb).
Local Abbreviation PSR_stable := (ARb (AR9 (ARi (@YF7h.PSR_stable _)))).
Local Abbreviation QSP := (@YF7h.QSP imgk ly idx).
Local Abbreviation QS_not_WIN1R := (ARb (AR3 (@YF7h.QS_not_WIN1R _))).
Local Abbreviation QSP_rstable := (ARb (AR3 (@YF7h.QSP_rstable _))).
Local Abbreviation at_S_memsetSR := ((AR4 ((AR0 ((AR5 (@YF7h.at_S_memsetSR _ _)) md0)) LY Hsp)) Hmap_apart mat0 DPOST S).
Local Abbreviation chunk_eqb := (@YF7h.chunk_eqb imgk).
Local Abbreviation chunk_eqb_eq := ((ARf (@YF7h.chunk_eqb_eq imgk)) Hres S Hidx_def Hres_def).
Local Abbreviation subregionb := (@YF7h.subregionb imgk).
Local Abbreviation subregionb_sound := (AR8 ((ARf (AR6 (@YF7h.subregionb_sound))) Hres)).
Local Abbreviation submemb := (@YF7h.submemb imgk).
Local Abbreviation submemb_sound := (AR8 ((ARf (AR6 (@YF7h.submemb_sound))) Hres)).
Local Abbreviation at_S_submem := (AR8 ((AR0 (AR6 (@YF7h.at_S_submem _))) Hidx Hres)).
Local Abbreviation at_S_addreg := (AR0 (AR6 (@YF7h.at_S_addreg _))).
Local Abbreviation PSR_runs := (AR0 (AR6 (@YF7d.PSR_runs _))).
Local Abbreviation place_WIN := (ARc (@YF7d.place_WIN)).
Local Abbreviation SH0 := (@YF7d.SH0 n mb).
Local Abbreviation SH1 := (@YF7d.SH1 n mb).
Local Abbreviation SH2 := (@YF7d.SH2 n mb).
Local Abbreviation SH_ok := (AR4 (AR3 (@YF7d.SH_ok _))).
Local Abbreviation segG1 := (AR8 ((ARb (AR0 ((AR5 (@YF7d.segG1 _ _)) md0))) mat0)).
Local Abbreviation QR := (@YF7i.QR ly res).
Local Abbreviation segT1 := ((AR4 ((AR7 (AR6 (@YF7i.segT1 _ _))) Hn Hsp)) Hmap_apart).
Local Abbreviation DX := (AR1 (@YF7i.DX)).
Local Abbreviation PD := (@YF7i.PD imgk ly mem0 DPOST).
Local Abbreviation PD_rstable := ((ARb (AR9 ((AR6 (@YF7i.PD_rstable _)) n))) DPOST).
Local Abbreviation PD_stableT := ((ARb (AR9 ((AR6 (@YF7i.PD_stableT _)) n))) DPOST).
Local Abbreviation PSR_stableS := (ARb (AR9 (ARi (@YF7i.PSR_stableS _)))).
Local Abbreviation PD_stableS := ((ARb (AR9 ((AR6 (@YF7i.PD_stableS _)) n))) DPOST).
Local Abbreviation PDX := (@YF7i.PDX imgk ly mem0 DPOST).
Local Abbreviation PDX_rstable := ((ARb (AR9 ((AR6 (@YF7i.PDX_rstable _)) n))) DPOST).
Local Abbreviation PDX_stableT := ((ARb (AR9 ((AR6 (@YF7i.PDX_stableT _)) n))) DPOST).
Local Abbreviation PDX_stableS := ((ARb (AR9 ((AR6 (@YF7i.PDX_stableS _)) n))) DPOST).
Local Abbreviation dx_okb := (@YF7i.dx_okb imgk).
Local Abbreviation skel_apart_DX := (AR8 (ARb (AR0 (AR6 (@YF7i.skel_apart_DX _))))).
Local Abbreviation skel_apart_stk := ((ARb (AR0 (AR1 (@YF7i.skel_apart_stk _)))) S Hidx_def Hres_def).
Local Abbreviation at_S_depot := (AR8 (ARb (AR0 (AR5 (@YF7i.at_S_depot _ _))))).
Local Abbreviation SH3 := (@YF7i.SH3 n mb).
Local Abbreviation SH4 := (@YF7i.SH4 n mb).
Local Abbreviation shadow_marks := (AR4 (AR3 (@YF7i.shadow_marks _))).
Local Abbreviation SH34_ok := (AR4 (AR3 (@YF7i.SH34_ok _))).
Local Abbreviation segT2b := (AR8 ((AR4 ((AR7 ((AR5 (@YF7i.segT2b _ _)) md0)) Hn Hsp)) Hmap_apart mat0)).
Local Abbreviation segT2 := (AR8 ((AR4 ((AR7 ((AR5 (@YF7i.segT2 _ _)) md0)) Hn Hsp)) Hmap_apart mat0)).
Local Abbreviation SH5 := (@YF7j.SH5 n mb).
Local Abbreviation SH6 := (@YF7j.SH6 n mb).
Local Abbreviation user_marks := (AR4 (AR3 (@YF7j.user_marks _))).
Local Abbreviation SH56_ok := (AR4 (AR3 (@YF7j.SH56_ok _))).
Local Abbreviation segU1 := (AR8 ((ARb (AR0 ((AR5 (@YF7j.segU1 _ _)) md0))) mat0)).
Local Abbreviation SH6_of_cut := (AR4 (AR3 (@YF7j.SH6_of_cut _))).
Local Abbreviation segUe := (AR8 ((AR4 ((AR7 ((AR5 (@YF7j.segUe _ _)) md0)) Hn Hsp)) Hmap_apart mat0)).
Local Abbreviation PT := ((ARi (@YF7j.PT)) mb).
Local Abbreviation run_okT := (@YF7j.run_okT n mb).
Local Abbreviation SH5o := (@YF7j.SH5o n mb).
Local Abbreviation SH6o := (@YF7j.SH6o n mb).
Local Abbreviation SH56o_ok := (AR4 (AR3 (@YF7j.SH56o_ok _))).
Local Abbreviation PT_stableT := (ARb (AR9 (ARi (@YF7j.PT_stableT _)))).
Local Abbreviation segUo := (AR8 ((AR4 ((AR7 ((AR5 (@YF7j.segUo _ _)) md0)) Hn Hsp)) Hmap_apart mat0)).
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
Definition E0_at (mb0 : Z) : env := @YF7f.E0 imgk ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb0.
Definition map_atom (k : nat) : bool := natin [aMAP; aEND; aSM; aUE; aPBS] k.
Lemma E0_at_other : forall mb0 k, (k < sHAV)%nat -> map_atom k = false -> ew (E0_at mb0) k = ew E0 k.
Proof.
clearP. intros mb0 k Hk Hm. unfold sHAV in Hk.
do 80 (destruct k as [|k]; [img_try (first [img_refl | discriminate Hm]) |]). exfalso. clear - Hk. zlia.
Qed.
Lemma ed_E0_at : forall mb0, ed (E0_at mb0) = ed E0.
Proof. clearP. intros; img_refl. Qed.
Lemma st_ok_ecall_agree_on : forall P (E E' : env) ss ms,
st_ok_ecall tfxsegs E ss ms -> env_agree_on P E E' -> ss_atoms_in P ss = true -> st_ok_ecall tfxsegs E' ss ms.
Proof.
clearP. intros P E E' ss ms (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) HA Hat.
unfold ss_atoms_in in Hat. apply andb_prop in Hat as [Hat Hrv]. apply andb_prop in Hat as [Hat HG]. apply andb_prop in Hat as [Hr Hm].
unfold st_ok_ecall. split; [img_try (img_exact H1)|]. split; [img_try (img_exact H2)|]. split.
{ rewrite H3. rewrite (sv_denot_agree_on P E E') by (img_try (try assumption; img_apply sr_get_atoms_in; img_exact Hr)). img_refl. }
split. { rewrite H4. destruct (ss_resv ss) as [a|]; cbn; [|img_refl]. rewrite (sv_denot_agree_on P E E') by assumption. img_refl. }
split; [img_try (img_exact H5)|]. split; [img_try (img_exact H6)|]. split; [img_try (eapply regs_ok_agree_on; eauto)|]. split; [img_try (eapply mem_ok_agree_on; eauto) | img_try (eapply facts_ok_agree_on; eauto)].
Qed.
Definition Esw (E' : env) : env := env_merge map_atom E0 E'.
Lemma Esw_agree : forall mb0 (E' : env), env_agree sHAV (E0_at mb0) E' -> env_agree sHAV E0 (Esw E').
Proof.
clearP. intros mb0 E' [HA HD]. split.
- intros k Hk. unfold Esw. destruct (map_atom k) eqn:Hm.
+ rewrite (ew_merge_in _ _ _ _ Hm). img_refl.
+ rewrite (ew_merge_out _ _ _ _ Hm), (HA k Hk). img_exact (E0_at_other mb0 k Hk Hm).
- unfold Esw. rewrite ed_merge, HD. img_apply ed_E0_at.
Qed.
Lemma Esw_on : forall E' : env, env_agree_on (fun k => negb (map_atom k)) E' (Esw E').
Proof. clearP. intros E' k Hk. unfold Esw. apply Bool.negb_true_iff in Hk. rewrite (ew_merge_out _ _ _ _ Hk). img_refl. Qed.
Lemma at_S_facts_atoms : forall (Wx : world tfxsegs) md X P ss W' c' (ats : list (nat * afact)),
at_S Wx md X P ss W' c' -> f_conds (ss_facts ss) = [] -> f_alias (ss_facts ss) = [] ->
atoms_ok E0 ats -> forallb (fun p => Nat.ltb (fst p) sHAV) ats = true ->
at_S Wx md X P (mkSS (ss_pc ss) (ss_regs ss) (ss_mem ss) (ss_resv ss) (mkFacts ats [] [])) W' c'.
Proof.
clearP. intros Wx md X P ss W' c' ats HR Hc Ha HOK Hlt. destruct HR as (-> & ms & mat & E' & -> & HE & HS & MEQ & PRS & HPm).
split; [img_refl|]. exists ms, mat, E'. split; [img_refl|]. split; [img_try (img_exact HE)|]. split; [|img_try (img_exact (conj MEQ (conj PRS HPm)))].
destruct HS as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9). unfold st_ok. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts].
repeat (split; [img_try (assumption)|]). split; [|img_try (split; [img_exact I | img_exact I])]. cbn [f_atoms].
clear - HOK Hlt HE. destruct HE as [HA _]. induction ats as [|[k f] l IH]; [img_try (img_exact I)|]. cbn [atoms_ok forallb fst] in HOK, Hlt |- *. apply andb_prop in Hlt as [Hk Hl]. destruct HOK as [Hf Hrest].
split; [|img_try (img_exact (IH Hrest Hl))]. unfold afact_ok in *. apply Nat.ltb_lt in Hk. rewrite (HA k Hk). img_exact Hf.
Qed.
Lemma atoms_ok_app : forall (E : env) l1 l2, atoms_ok E l1 -> atoms_ok E l2 -> atoms_ok E (l1 ++ l2).
Proof. clearP. intros E l1 l2 H1 H2. induction l1 as [|[k f] l IH]; [img_try (img_exact H2)|]. cbn in H1 |- *. destruct H1 as [Hf Hl]. split; [img_try (img_exact Hf) | img_try (img_exact (IH Hl))]. Qed.
Lemma FS2_ok : atoms_ok E0 (f_atoms FS2).
Proof.
pose proof FACTS_ok as F1. unfold FS2, FS in *. cbn [f_atoms] in *. unfold FS2_atoms. img_apply atoms_ok_app; [img_try (img_exact F1)|].
pose proof map_facts as (M1 & M2 & M3 & K4 & U5 & E6 & UE7 & E8 & UE9 & MT & MU & SM1 & SM2 & SM3 & PB & SMA). pose proof map_zoneN as MZ.
pose proof size_facts as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10 & Z11 & Z12 & Z13 & Z14). pose proof Nrange as NR. pose proof Hidx as HI.
pose proof BSLv_range as HB. pose proof high_facts as (_ & _ & _ & _ & _ & _ & _ & _ & F9 & F10 & F11 & _).
pose proof shadow_marks as (_ & A2 & A3 & _ & A5 & A6 & _). pose proof user_marks as (B1 & _ & _ & B4 & _).
clear - F1 M1 M2 M3 K4 U5 E6 UE7 E8 UE9 MT MU SM1 SM2 SM3 PB Z1 Z2 Z3 Z4 Z5 Z6 Z7 Z8 Z9 Z10 Z11 Z12 Z13 Z14 NR HI HB F9 F10 F11 A2 A3 A5 A6 B1 B4 MZ.
unfold MALLOC_MAX in *. ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighShadowBeg, kHighShadowEnd, ASAN_CEIL, kPtrArrayResv, kMaxNumChunks in *. unfold TFX_INST in HB |- *.
assert (AF : forall k X lo hi al, ew E0 k = w64 X -> 0 <= X < 2 ^ 64 -> lo <= X <= hi -> X mod 2 ^ al = 0 -> 0 <= al <= 64 -> afact_ok E0 k (mkAF lo hi al)).
{ clear. intros k X lo hi al HE HX HBd HM HA. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE. unfold w64. rewrite unsigned_lit_small by img_exact HX. repeat split; zlia. }
assert (M12 : mb mod 2 ^ 12 = 0) by (img_try (img_change (2 ^ 12) with 4096; img_exact M3)).
assert (E3 : ENDv mod 2 ^ 3 = 0) by (img_try (img_change (2 ^ 3) with 8; img_exact E8)). assert (UE3 : UEv mod 2 ^ 3 = 0) by (img_try (img_change (2 ^ 3) with 8; img_exact UE9)).
assert (TL3 : TLv mod 2 ^ 3 = 0) by (img_try (img_change (2 ^ 3) with 8; img_exact Z12)). assert (RL3 : RLv mod 2 ^ 3 = 0) by (img_try (img_change (2 ^ 3) with 8; img_exact Z14)).
assert (N83 : N8D mod 2 ^ 3 = 0) by (img_try (img_change (2 ^ 3) with 8; img_exact Z5)).
assert (QS3 : QSv mod 2 ^ 3 = 0).
{ unfold QSv. img_change (2 ^ 3) with 8. unfold page_aligned in F11. apply Z.mod_divide in F11 as [q Hq]; [|img_try (zlia)]. try unfold Qb. rewrite Hq.
replace (q * 4096 + 8 * idx) with ((q * 512 + idx) * 8) by zlia. img_apply Z_mod_mult. }
assert (BS3 : BSLv mod 2 ^ 3 = 0).
{ unfold YF7f.BSLv. img_change (2 ^ 3) with 8. unfold TFX_INST. replace ((682840 + D_10c0) + 168 + 8 * LGv) with (((85376 + D_218) + LGv) * 8) by zlia. img_apply Z_mod_mult. }
assert (SM9 : SMv mod 2 ^ 9 = 0) by (img_try (img_change (2 ^ 9) with 512; img_exact SM3)).
cbn [atoms_ok app fst snd]. unfold aMAP, aEND, aTL, aQS, aBSL, aSM, aUE, aRL, aN8DS, aPBS.
split; [img_try (img_apply (AF _ mb); [img_exact EaMAP | clear - M1 M2 Z8 MZ; zlia | clear - M1 M2 Z8 MZ; zlia | img_exact M12 | clear; zlia]) |].
split; [img_try (img_apply (AF _ ENDv); [img_exact EaEND | clear - M1 M2 Z8 Z1 E6 U5 MT Z11 MZ; unfold Uv in *; zlia | clear - M1 M2 Z8 Z1 E6 U5 MT Z11 MZ; unfold Uv in *; zlia | img_exact E3 | clear; zlia]) |].
split; [img_try (img_apply (AF _ TLv); [img_exact EaTL | clear - Z11 MZ; zlia | clear - Z11 MZ; zlia | img_exact TL3 | clear; zlia]) |].
split; [img_try (img_apply (AF _ QSv); [img_exact EaQS | clear - F9 F10 HI MZ; unfold QSv; try unfold Qb in *; zlia | clear - F9 F10 HI MZ; unfold QSv; try unfold Qb in *; zlia | img_exact QS3 | clear; zlia]) |].
split; [img_try (img_apply (AF _ BSLv); [img_exact EaBSL | clear - HB MZ; zlia | clear - HB MZ; zlia | img_exact BS3 | clear; zlia]) |].
split; [img_try (img_apply (AF _ SMv); [img_exact EaSM | clear - SM1 SM2 Z8 MZ; zlia | clear - SM1 SM2 Z8 MZ; zlia | img_exact SM9 | clear; zlia]) |].
split; [img_try (img_apply (AF _ UEv); [img_exact EaUE | clear - M1 M2 Z8 Z1 UE7 U5 MU Z13 MZ; unfold Uv in *; zlia | clear - M1 M2 Z8 Z1 UE7 U5 MU Z13 MZ; unfold Uv in *; zlia | img_exact UE3 | clear; zlia]) |].
split; [img_try (img_apply (AF _ RLv); [img_exact EaRL | clear - Z13 MZ; zlia | clear - Z13 MZ; zlia | img_exact RL3 | clear; zlia]) |].
split; [img_try (img_apply (AF _ N8D); [img_exact EaN8D | clear - Z4 NR MZ; zlia | clear - Z4 NR MZ; zlia | img_exact N83 | clear; zlia]) |].
split; [img_try (img_apply (AF _ PBv); [img_exact EaPB | clear - A2 A3 A5 A6 B1 B4 SM1 SM2 MZ; zlia | clear - A2 A3 A5 A6 B1 B4 SM1 SM2 MZ; zlia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r | clear; zlia]) | img_try (img_exact I)].
Qed.
Lemma at_S_addreg_cfg : forall (Wx : world tfxsegs) md X P ss W' c' r,
at_S Wx md X P ss W' c' -> YQ0b.region_wf r = true ->
(forall (E' : env) (ms : machine_state) mat,
c' = mkCfg ms (with_vm_backing (m_vm_lazy md) mat md) ->
env_agree sHAV E0 E' -> P (ms_mem ms) -> mem_ok tfxsegs E' (mrestrict (w_H Wx) (ms_mem ms)) (ss_mem ss) ->
region_ok tfxsegs E' (mrestrict (w_H Wx) (ms_mem ms)) r /\ (forall r2, In r2 (ss_mem ss) -> extent_disjoint E' r r2)) ->
at_S Wx md X P (addreg r ss) W' c'.
Proof.
clearP. intros Wx md X P ss W' c' r HR Hwf HOK. destruct HR as (-> & ms & mat & E' & -> & HE & HS & MEQ & PRS & HPm).
split; [img_refl|]. exists ms, mat, E'. split; [img_refl|]. split; [img_try (img_exact HE)|]. split; [|img_try (img_exact (conj MEQ (conj PRS HPm)))].
pose proof (st_ok_mem_ok tfxsegs E' ss _ HS) as HM. destruct (HOK E' ms mat eq_refl HE HPm HM) as [Hok Hx].
unfold addreg. img_apply st_ok_add_region; [img_try (img_exact HS) | img_try (img_exact Hwf) | img_try (img_exact Hok) | img_try (img_apply all_disjoint_of_forall; img_exact Hx)].
Qed.
Lemma S_N_apart : forall (E' : env), env_agree sHAV E0 E' ->
forall r a, In r (ss_mem S_N) -> base_val E' (YQ0b.r_base r) + YQ0b.r_lo r <= a < base_val E' (YQ0b.r_base r) + YQ0b.r_hi r ->
~ (mb <= a < mb + MSv) /\ 0 <= a < 2 ^ 64.
Proof.
intros E' [HE _] r a Hr Ha. pose proof (lo_top ly LY) as (_ & _ & _ & T4 & _ & _ & T7). destruct Hsp as (S1 & _ & S3 & _). pose proof (u64_range (getr regs0 2)) as U2.
destruct Hmap_apart as (_ & _ & _ & _ & _ & _ & MS). unfold zdisjoint in MS. cbn [fst snd] in MS.
lazymatch type of Hr with In _ ?l =>
let m3 := img_ev (firstn 3 l) in let tl3 := img_ev (skipn 3 l) in
assert (SPLIT : In r m3 \/ In (skel r) SKEL_TAIL)
by (img_try (img_change l with (m3 ++ tl3) in Hr; apply in_app_iff in Hr as [Hr|Hr]; [img_try (left; img_exact Hr) | img_try (right)];
apply (in_map skel) in Hr; replace (map skel tl3) with SKEL_TAIL in Hr by ((img_case; vm_compute); img_refl); img_exact Hr)) end.
clear Hr. destruct SPLIT as [Hr|Hr].
- destruct Hr as [<-|[<-|[<-|[]]]]; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val] in Ha; rewrite (HE 2%nat ltac:(img_try (unfold sHAV; zlia))), E2 in Ha;
clear - Ha MS S1 S3 T4 T7 U2; unfold zone3, TFX_IMG_LO, kLowShadowBeg, ASTACK, IFRAME, kHighMemBeg, kHighMemEnd in *; try unfold sp0 in *; zlia.
- pose proof (tail_ext_ok E' r HE Hr) as (X1 & X2 & X3 & X4 & X5 & X6).
pose proof (RFACTS_map _ _ 0 0 (conj X1 (conj X2 (conj X3 (conj (or_introl (Z.le_refl 0)) (conj X5 X6)))))) as [AM _]. clear - Ha X2 X3 AM. zlia.
Qed.
Lemma S_N_nomap : ss_atoms_in (fun k => negb (map_atom k)) S_N = true.
Proof. clearP. img_case; vm_compute. all: img_refl. Qed.
Lemma grant_cont : forall (mb0 : Z) (Wy : world tfxsegs) (md' : Model) (R : (word -> option byte) -> Prop) ms (E' : env),
env_agree sHAV (E0_at mb0) E' ->
st_ok_ecall tfxsegs E' S_N (restrict (w_H W) ms) ->
(forall x : word, ~ WINP (bv_unsigned x) -> ms_mem ms x = mem0 x) ->
(forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) (ms_mem ms) a) ->
PBUF (ms_mem ms) ->
hsub (w_H Wy) (w_H W) ->
(forall a, mb <= a < mb + MSv -> w_H Wy (w64 a) = false) ->
(forall a, SMv <= a < SMv + MSv / 8 -> w_H Wy (w64 a) = false /\ ms_mem ms (w64 a) = Some (Z_to_bv 8 0)) ->
R (zfill (w64 mb) (w64 MSv) (ms_mem ms)) ->
at_S Wy md' WIN (PSR Wy SH0 R) S_P0 Wy
(mkCfg (mkst (regupd (ms_regs ms) 10%bv (w64 mb)) (v_addi (Z_to_bv 64 (ss_pc S_N)) 4) (zfill (w64 mb) (w64 MSv) (ms_mem ms)) (seg_rom tfxsegs)) md').
Proof.
intros mb0 Wy md' R ms E' HE' HS MEQ PRS HB Hsub HMV HSV HR.
pose proof map_facts as (M1 & M2 & M3 & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _). pose proof map_zoneN as MZ. pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & _).
ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighShadowBeg, kHighShadowEnd, ASAN_CEIL in M1, M2, SM1, SM2. unfold MALLOC_MAX in Z8.
pose proof (Esw_agree mb0 E' HE') as HE. set (E'' := Esw E') in *.
assert (HS'' : st_ok_ecall tfxsegs E'' S_N (restrict (w_H W) ms)) by (img_try (img_exact (st_ok_ecall_agree_on _ E' E'' S_N _ HS (Esw_on E') S_N_nomap))).
assert (Umb : bv_unsigned (w64 mb) = mb) by (img_try (unfold w64; img_apply unsigned_lit_small; clear - M1 M2 Z8 MZ; zlia)).
assert (Ums : bv_unsigned (w64 MSv) = MSv) by (img_try (unfold w64; img_apply unsigned_lit_small; clear - Z8 MZ; zlia)).
assert (FRz : forall x : word, ~ (mb <= bv_unsigned x < mb + MSv) -> zfill (w64 mb) (w64 MSv) (ms_mem ms) x = ms_mem ms x).
{ intros x Hx. img_apply zfill_out. rewrite Umb, Ums. clear - Hx MZ. zlia. }
assert (ZIN : forall a, mb <= a < mb + MSv -> zfill (w64 mb) (w64 MSv) (ms_mem ms) (w64 a) = Some (Z_to_bv 8 0)).
{ intros a Ha. img_apply zfill_in. rewrite Umb, Ums. unfold w64. rewrite unsigned_lit_small by (img_try (clear - Ha M1 M2 Z8 MZ; zlia)). img_exact Ha. }
pose proof (at_N_cont W Wy md' WINP (PSR Wy SH0 R) S_N (SOff aMAP 0) (w64 mb) (fun a => mb <= a < mb + MSv) (zfill (w64 mb) (w64 MSv) (ms_mem ms)) ms E''
HE HS'' eq_refl MEQ PRS Hsub) as C.
assert (HeMAP : sv_denot E'' (SOff aMAP 0) = w64 mb).
{ rewrite sv_denot_SOff0. (subst E''; cbv beta). unfold Esw. rewrite (ew_merge_in map_atom E0 E' aMAP eq_refl). img_exact EaMAP. }
specialize (C HeMAP ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) FRz (S_N_apart E'' HE)).
assert (RWIN : forall r a, In r (ss_mem S_N) -> base_val E'' (YQ0b.r_base r) + YQ0b.r_wlo r <= a < base_val E'' (YQ0b.r_base r) + YQ0b.r_whi r -> ~ (mb <= a < mb + MSv) /\ 0 <= a < 2 ^ 64).
{ intros r a Hr Ha. destruct HS'' as (_ & _ & _ & _ & _ & _ & _ & (Hwf & _ & _) & _). pose proof (region_wf_facts r (regions_wf_In _ r Hwf Hr)) as (_ & WW & _). img_apply (S_N_apart E'' HE r a Hr). clear - Ha WW MZ. zlia. }
specialize (C RWIN). clear RWIN.
assert (STK : forall a, sp0 - ASTACK <= a < sp0 -> ~ (mb <= a < mb + MSv)).
{ intros a Ha Hm. destruct Hmap_apart as (_ & _ & _ & _ & _ & _ & MS). unfold zdisjoint in MS. cbn [fst snd] in MS.
pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7). destruct Hsp as (S1 & _ & S3 & _). clear - Ha Hm MS S1 S3 T7 MZ. unfold ASTACK in *. try unfold sp0 in *. zlia. }
specialize (C STK).
assert (PF : PSR Wy SH0 R (zfill (w64 mb) (w64 MSv) (ms_mem ms))).
{ split; [|img_try (img_exact HR)]. split; [|img_try (split; [|split])].
- intros i Hi. pose proof tr_length as LEN. pose proof (lo_top ly LY) as (_ & _ & _ & T4 & _ & _ & T7). destruct Hsp as (S1 & _ & S3 & _). pose proof (u64_range (getr regs0 2)) as U2.
intros kk Hkk. pose proof (HB i Hi kk Hkk) as X.
lazymatch goal with |- mbyte _ _ ?A = _ =>
assert (RNG : sp0 - ASTACK <= A < sp0) by (img_try (clear - Hi Hkk LEN MZ; unfold IFRAME, ASTACK; zlia));
destruct (PRS _ RNG) as [HhW _];
assert (HhY : w_H Wy (Z_to_bv 64 A) = false) by (img_try (destruct (w_H Wy (Z_to_bv 64 A)) eqn:Ey; [img_try (rewrite (Hsub _ Ey) in HhW; discriminate HhW) | img_refl]));
unfold mbyte, mrestrict in X |- *; rewrite HhW in X; rewrite HhY; rewrite (FRz (Z_to_bv 64 A)); [img_try (img_exact X)|];
rewrite unsigned_lit_small by (img_try (clear - RNG S1 S3 T4 T7 U2 MZ; unfold zone3, TFX_IMG_LO, kLowShadowBeg, IFRAME, ASTACK, kHighMemBeg, kHighMemEnd in *; try unfold sp0 in *; zlia));
img_apply STK; img_exact RNG
end.
- intros a Ha. split; [img_try (img_apply HMV; clear - Ha MZ; zlia)|]. exists (Z_to_bv 8 0). unfold w64 in ZIN. img_apply ZIN. clear - Ha MZ; zlia.
- intros a Ha. destruct (HSV a Ha) as [Hy Hz]. split; [img_try (img_exact Hy)|]. exists (Z_to_bv 8 0). unfold w64 in Hz, FRz |- *. rewrite FRz; [img_try (img_exact Hz)|].
rewrite unsigned_lit_small by (img_try (clear - Ha SM1 SM2 MZ; zlia)). clear - Ha M1 SM2 MZ. zlia.
- unfold SH0. img_apply Forall_cons; [|img_try (img_apply Forall_nil)]. intros a Ha. cbn [fst snd] in Ha. destruct (HSV a Ha) as [_ Hz]. unfold w64 in Hz, FRz |- *. rewrite FRz; [img_try (img_exact Hz)|].
rewrite unsigned_lit_small by (img_try (clear - Ha SM1 SM2 MZ; zlia)). clear - Ha M1 SM2 MZ. zlia. }
specialize (C PF). clear PF.
apply (at_S_weaken Wy md' _ WIN _ (PSR Wy SH0 R)) in C; [| img_try (intros a [Ha|Ha]; [img_exact (WINP_WIN a Ha) | unfold WIN, WINM; right; right; right; right; left; img_exact Ha]) | img_try (intros m Hm; img_exact Hm)].
apply at_S_noconds in C.
apply (at_S_facts_atoms Wy md' WIN _ _ Wy _ (f_atoms FS2)) in C; [| img_refl | img_refl | img_try (img_exact FS2_ok) | img_try ((img_case; vm_compute); img_refl)].
apply (at_S_addreg_cfg Wy md' WIN _ _ Wy _ R_map) in C; [| img_refl |].
2:{ intros E3 ms3 mat3 Hc HE3 [(HB3 & HM3 & HSH3 & HRs3) HQ3] HMok. pose proof (proj1 HE3) as HEn3.
assert (Hm3 : ms_mem ms3 = zfill (w64 mb) (w64 MSv) (ms_mem ms)) by (img_try (injection Hc as <- _; img_refl)).
rewrite Hm3 in *.
assert (BM : base_val E3 (Some aMAP) = mb) by (img_try (cbn [base_val]; unfold aMAP; rewrite (HEn3 45%nat ltac:(unfold sHAV; zlia)), EaMAP; img_exact Umb)).
split.
- unfold region_ok, R_map. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks]. rewrite BM.
split; [img_try (clear - M1 MZ; zlia)|]. split; [img_try (clear - M2 Z8 MZ; zlia)|]. split.
+ intros o Ho. img_apply apresent_writable_off; [img_try (off_by ltac:(clear - Ho M1 M2 Z8 MZ; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; zlia)) |]. split; [img_try (img_apply HMV; clear - Ho Z8 MZ; zlia)|].
exists (Z_to_bv 8 0). unfold w64 in ZIN. img_apply ZIN. clear - Ho Z8 MZ; zlia.
+ img_apply Forall_cons; [|img_try (img_apply Forall_nil)]. eapply chunk_ok_val; [img_refl | img_try (cbn; zlia) | img_try (cbn; zlia) |].
intros kk Hkk. destruct kk as [|kk]; [|img_try (cbn in Hkk; zlia)]. unfold mbyte, mrestrict. img_change (Z.of_nat 0) with 0. rewrite Z.add_0_r.
unfold w64 in HMV, ZIN |- *. rewrite (HMV (mb + 6129)) by (img_try (clear - Z8 MZ; zlia)). rewrite (ZIN (mb + 6129)) by (img_try (clear - Z8 MZ; zlia)). img_refl.
- intros r2 Hr2. unfold extent_disjoint, R_map. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi]. rewrite !BM.
pose proof (lo_top ly LY) as (_ & _ & _ & T4 & _ & _ & T7). destruct Hsp as (S1 & _ & S3 & _). pose proof (u64_range (getr regs0 2)) as U2.
destruct Hmap_apart as (_ & _ & _ & _ & _ & _ & MS). unfold zdisjoint in MS. cbn [fst snd] in MS.
lazymatch type of Hr2 with In _ ?l =>
let m3 := img_ev (firstn 3 l) in let tl3 := img_ev (skipn 3 l) in
assert (SPLIT : In r2 m3 \/ In (skel r2) SKEL_TAIL)
by (img_try (img_change l with (m3 ++ tl3) in Hr2; apply in_app_iff in Hr2 as [Hr2|Hr2]; [img_try (left; img_exact Hr2) | img_try (right)];
apply (in_map skel) in Hr2; replace (map skel tl3) with SKEL_TAIL in Hr2 by ((img_case; vm_compute); img_refl); img_exact Hr2)) end.
clear Hr2. destruct SPLIT as [Hr|Hr].
+ destruct Hr as [<-|[<-|[<-|[]]]]; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; rewrite (HEn3 2%nat ltac:(img_try (unfold sHAV; zlia))), E2;
clear - MS S1 S3 T4 T7 U2 Z8 MZ; unfold zone3, TFX_IMG_LO, kLowShadowBeg, ASTACK, IFRAME, kHighMemBeg, kHighMemEnd in *; try unfold sp0 in *; zlia.
+ pose proof (tail_ext_ok E3 r2 HEn3 Hr) as (X1 & X2 & X3 & X4 & X5 & X6).
pose proof (RFACTS_map _ _ 0 0 (conj X1 (conj X2 (conj X3 (conj (or_introl (Z.le_refl 0)) (conj X5 X6)))))) as [AM _]. clear - AM Z8 MZ. zlia. }
lazymatch type of C with at_S _ _ _ _ ?ss2 _ _ => replace ss2 with S_P0 in C by (img_try ((img_case; vm_compute); img_refl)) end.
img_exact C.
Qed.
End g.
End d.
