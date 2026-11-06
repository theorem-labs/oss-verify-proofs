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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK0v YK13 YQ0k YA05 YA09 YG0b YG0j.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF4b YF4c YF4d YF0h YF5t YF5u YF5v YF5f YF5l YF5m YF5i YF5j YF5n YF5q.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YA00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF48.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG0c.
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
pose proof (st_ok_forget2 k E ss ss' H ms clob HS eq_refl
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
eq_refl eq_refl ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))) as HS2; clear HS; rename HS2 into HS
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
Local Abbreviation ARg f := (f idx res Hidx) (only parsing).
Local Abbreviation tr_length := (ARg ((AR1 (@YF5k.tr_length)) ch)).
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
Local Abbreviation ARb f := (AR0 f LY IMG) (only parsing).
Local Abbreviation ARd f := (f Nrange Hidx Hres) (only parsing).
Local Abbreviation WSKELP_WINP := (ARd (ARb (AR1 (@YF5k.WSKELP_WINP _)))).
Local Abbreviation WSKEL1P_WIN1P := (ARd (ARb (AR1 (@YF5k.WSKEL1P_WIN1P _)))).
Local Abbreviation WMAP_WINM := (AR5 (ARb (AR1 (@YF5k.WMAP_WINM _)))).
Local Abbreviation WSKEL_WIN := (AR5 (ARb (AR1 (@YF5k.WSKEL_WIN _)))).
Local Abbreviation WSKEL1_WIN1 := (AR5 (ARb (AR1 (@YF5k.WSKEL1_WIN1 _)))).
Local Abbreviation windows_in := ((AR9 (@YF5k.windows_in ly regs0)) Hidx Hres).
Local Abbreviation windows_WINP := (ARd (ARb (AR1 (@YF5k.windows_WINP _)))).
Local Abbreviation windows_WIN1P := (ARd (ARb (AR1 (@YF5k.windows_WIN1P _)))).
Local Abbreviation windows_WIN := (AR5 (ARb (AR1 (@YF5k.windows_WIN _)))).
Local Abbreviation windows_WIN1 := (AR5 (ARb (AR1 (@YF5k.windows_WIN1 _)))).
Local Abbreviation frame_WIN1P := (ARd (ARb (AR1 (@YF5k.frame_WIN1P _)))).
Local Abbreviation frame_WIN1 := (AR5 (ARb (AR1 (@YF5k.frame_WIN1 _)))).
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
Local Abbreviation ARf f := (f imgk W ly) (only parsing).
Local Abbreviation kept_of_frame := ((AR9 ((ARf (@YF5k.kept_of_frame)) regs0)) Hidx).
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
Local Abbreviation AR7 f := (AR2 f Hmap Hmap_apart) (only parsing).
Local Abbreviation DZONE_disj := (AR7 (AR3 (@YF5k.DZONE_disj _))).
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
Local Abbreviation AR6 f := (AR1 f mem0) (only parsing).
Local Abbreviation at_S := (AR0 (AR6 (@YF5k.at_S _))).
Local Abbreviation at_N := (AR0 (AR6 (@YF5k.at_N _))).
Local Abbreviation at_RETS := (@YF5k.at_RETS _ regs0 mem0 imgk).
Local Abbreviation pstable := (@YF5k.pstable).
Local Abbreviation stack_shaped := (@YF5k.stack_shaped).
Local Abbreviation window_present := (ARg (AR1 (@YF5k.window_present))).
Local Abbreviation stack_present_of := ((AR0 (AR1 (@YF5k.stack_present_of _))) LY Hsp Hidx).
Local Abbreviation mid_not_WIN1P := (AR2 (AR3 (@YF5k.mid_not_WIN1P _))).
Local Abbreviation mid_not_WIN1 := (ARh (AR3 (@YF5k.mid_not_WIN1 _))).
Local Abbreviation wins_ok := (@YF5k.wins_ok).
Local Abbreviation at_S_run_gen := ((AR0 (AR6 (@YF5k.at_S_run_gen _ _))) LY Hsp Hidx).
Local Abbreviation at_S_run_ecall_gen := ((AR0 (AR6 (@YF5k.at_S_run_ecall_gen _ _))) LY Hsp Hidx).
Local Abbreviation at_S_runP := (AR2 (AR0 (AR6 (@YF5k.at_S_runP _ _)))).
Local Abbreviation at_S_runM := (ARh (AR0 (AR6 (@YF5k.at_S_runM _ _)))).
Local Abbreviation at_S_run_ecallP := (AR2 (AR0 (AR6 (@YF5k.at_S_run_ecallP _ _)))).
Local Abbreviation at_S_run_ecallM := (ARh (AR0 (AR6 (@YF5k.at_S_run_ecallM _ _)))).
Local Abbreviation at_S_pin := (AR0 (AR6 (@YF5k.at_S_pin _))).
Local Abbreviation at_S_arm := (AR0 (AR6 (@YF5k.at_S_arm _))).
Local Abbreviation at_S_forget := (AR0 (AR6 (@YF5k.at_S_forget _))).
Local Abbreviation at_S_noconds := (AR0 (AR6 (@YF5k.at_S_noconds _))).
Local Abbreviation at_S_weaken := (AR0 (AR6 (@YF5k.at_S_weaken _))).
Local Abbreviation at_S_facts := (AR0 (AR6 (@YF5k.at_S_facts _))).
Local Abbreviation at_S_strengthen := (AR0 (AR6 (@YF5k.at_S_strengthen _))).
Local Abbreviation at_S_eq := (AR0 (AR6 (@YF5k.at_S_eq _))).
Local Abbreviation at_S_open := (AR0 (AR6 (@YF5k.at_S_open _))).
Local Abbreviation CSAVEDS := (@YF5k.CSAVEDS).
Local Abbreviation sv_denot_SOff0 := (@YF5k.sv_denot_SOff0).
Local Abbreviation at_S_ret := (ARd ((AR0 (AR6 (@YF5k.at_S_ret _))) Htp Hra Hsp)).
Local Abbreviation kept_of_frame2 := (ARg (AR1 (@YF5k.kept_of_frame2))).
Local Abbreviation at_N_cont := ((AR0 (AR6 (@YF5k.at_N_cont _ _))) LY Hsp Hidx).
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
Local Abbreviation vis_present := ((ARg (AR4 (@YF5t.vis_present _))) DPOST B S HARm).
Local Abbreviation in_thread_junk := (@YF5t.in_thread_junk ly B S).
Local Abbreviation in_sec_junk := (@YF5t.in_sec_junk ly B S).
Local Abbreviation in_as_junk := (@YF5t.in_as_junk ly B S).
Local Abbreviation junk_word := ((ARe (AR4 (@YF5t.junk_word _))) DPOST B S HARm).
Local Abbreviation cell_sym := ((ARf (@YF5t.cell_sym _)) mem0 B S TS HARm).
Local Abbreviation cell_lit := ((ARf (@YF5t.cell_lit _)) mem0 B S TS HARm).
Local Abbreviation cell_state := ((ARf (@YF5t.cell_state _)) mem0 B S HARm).
Local Abbreviation In_acells_sec := (@YF5t.In_acells_sec ly B S).
Local Abbreviation sec_vals := ((ARf (@YF5t.sec_vals _)) mem0 idx res B S TS HARm Hidx_def Hres_def).
Local Abbreviation unwinding_val := ((ARf (@YF5t.unwinding_val _)) mem0 B S HARm).
Local Abbreviation rw_writable := ((ARg (AR1 (@YF5t.rw_writable))) DPOST S).
Local Abbreviation val_mem_mod8 := ((ARg (AR4 (@YF5t.val_mem_mod8))) DPOST S).
Local Abbreviation chunk_lit := (AR0 (AR4 (@YF5t.chunk_lit))).
Local Abbreviation chunk_lit_at := (AR0 (AR4 (@YF5t.chunk_lit_at))).
Local Abbreviation chunk_atom := ((AR0 (AR4 (@YF5t.chunk_atom))) Hidx DPOST S).
Local Abbreviation ARa f := (f DPOST B S TS HTSD HARm Hidx_def Hres_def Hj0 Hj1 Hj2 Hj3 Hj4 Hj5 Hj9 Hj6 Hj7 Hj8 Hi1 Hi2 Hi3) (only parsing).
Local Abbreviation SREG0_ok := (ARa ((AR2 (AR0 (AR4 (@YF5u.SREG0_ok _)))) Hpres0)).
Local Abbreviation PAIRS_ok := ((AR2 (AR0 (AR4 (@YF5v.PAIRS_ok _)))) DPOST S).
Local Abbreviation FACTS_ok := ((ARd ((ARb (AR4 (@YF5v.FACTS_ok _))) Hn Hsp)) DPOST S).
Local Abbreviation SEED_ok := (ARa ((ARd ((ARb (AR4 (@YF5v.SEED_ok _ _))) Hn Htp Hsp)) Hpres0)).
Local Abbreviation PBUF := ((ARf (@YF5f.PBUF)) regs0 ch).
Local Abbreviation PBUF_stableP := (AR2 (AR9 ((ARf (@YF5f.PBUF_stableP _)) regs0 n ch))).
Local Abbreviation PBUF_stableM := (ARh (AR9 ((ARf (@YF5f.PBUF_stableM _)) regs0 n ch))).
Local Abbreviation seg0 := (ARa ((ARd ((ARb ((AR4 (@YF5f.seg0 _ _)) md0)) Hn Htp Hra4096 Hsp Hch)) Hpres0 mat0 U1)).
Local Abbreviation appregs := (@YF5l.appregs).
Local Abbreviation st_ok_appregs := (@YF5l.st_ok_appregs _ imgk).
Local Abbreviation at_S_app := (AR0 (AR6 (@YF5l.at_S_app _))).
Local Abbreviation WIN1N := (ARi (@YF5l.WIN1N)).
Local Abbreviation WINPN := (ARi (@YF5l.WINPN)).
Local Abbreviation WSKEL1N := (@YF5l.WSKEL1N imgk).
Local Abbreviation WIN1N_WINPN := ((AR3 (@YF5l.WIN1N_WINPN)) Hidx).
Local Abbreviation windows_WIN1N := (ARd (ARb (AR1 (@YF5l.windows_WIN1N _)))).
Local Abbreviation mid_not_WIN1N := (AR2 (AR3 (@YF5l.mid_not_WIN1N _))).
Local Abbreviation at_S_runN := (AR2 (AR0 (AR6 (@YF5l.at_S_runN _ _)))).
Local Abbreviation PBUF_stableN := (AR2 (AR9 ((ARf (@YF5l.PBUF_stableN _)) regs0 n ch))).
Local Abbreviation at_S_val := (AR0 (AR6 (@YF5l.at_S_val _))).
Local Abbreviation memset_stretchW := ((ARd ((AR4 (@YF5l.memset_stretchW _)) md0 n idx res Hsp)) mat0 DPOST S).
Local Abbreviation at_S_memset := ((ARd ((AR0 ((AR4 (@YF5l.at_S_memset _)) md0)) Hsp)) mat0 DPOST S).
Local Abbreviation WIN1T := (ARc (@YF5l.WIN1T)).
Local Abbreviation WIN1T_WIN := (AR5 (AR3 (@YF5l.WIN1T_WIN _))).
Local Abbreviation windows_WIN1T := (AR5 (ARb (AR1 (@YF5l.windows_WIN1T _)))).
Local Abbreviation WIN1T_WIN1_aux := (AR5 (AR3 (@YF5l.WIN1T_WIN1_aux _))).
Local Abbreviation mid_not_WIN1T := (ARh (AR3 (@YF5l.mid_not_WIN1T _))).
Local Abbreviation at_S_runT := (ARh (AR0 (AR6 (@YF5l.at_S_runT _ _)))).
Local Abbreviation at_S_run_ecallT := (ARh (AR0 (AR6 (@YF5l.at_S_run_ecallT _ _)))).
Local Abbreviation PBUFW := ((AR1 (@YF5l.PBUFW)) ch).
Local Abbreviation PBUFW_stableT := (ARh (AR9 ((ARi (@YF5l.PBUFW_stableT _)) ch))).
Local Abbreviation WIN1S := (ARc (@YF5m.WIN1S)).
Local Abbreviation WSKEL1S := (@YF5m.WSKEL1S imgk).
Local Abbreviation WIN1S_WIN1T := (ARc (@YF5m.WIN1S_WIN1T)).
Local Abbreviation WIN1S_WIN := (AR5 (AR3 (@YF5m.WIN1S_WIN _))).
Local Abbreviation windows_WIN1S := (AR5 (ARb (AR1 (@YF5m.windows_WIN1S _)))).
Local Abbreviation mid_not_WIN1S := (ARh (AR3 (@YF5m.mid_not_WIN1S _))).
Local Abbreviation at_S_runS := (ARh (AR0 (AR6 (@YF5m.at_S_runS _ _)))).
Local Abbreviation at_S_run_ecallS := (ARh (AR0 (AR6 (@YF5m.at_S_run_ecallS _ _)))).
Local Abbreviation brun := (@YF5m.brun).
Local Abbreviation run_ok := (@YF5m.run_ok n mb).
Local Abbreviation PS := ((ARi (@YF5m.PS)) ch mb).
Local Abbreviation runs_not_WIN1S := (AR7 (AR3 (@YF5m.runs_not_WIN1S _))).
Local Abbreviation runs_not_stack := ((AR5 ((AR3 (@YF5m.runs_not_stack _)) LY Hsp)) Hmap_apart).
Local Abbreviation PS_stable := (AR7 (AR9 ((ARi (@YF5m.PS_stable _)) ch))).
Local Abbreviation cut1 := (@YF5m.cut1).
Local Abbreviation cut := (@YF5m.cut).
Local Abbreviation cut_sound := ((AR5 (AR9 ((AR6 (@YF5m.cut_sound _)) n))) DPOST S).
Local Abbreviation cut_ok := ((AR9 (@YF5m.cut_ok ly regs0 mem0 n)) Hidx Hres DPOST S).
Local Abbreviation at_S_memsetS := ((AR5 ((AR0 ((AR4 (@YF5m.at_S_memsetS _ _)) md0)) LY Hsp)) Hmap_apart mat0 DPOST S).
Local Abbreviation skel_okb := (@YF5m.skel_okb imgk).
Local Abbreviation skel_cases := ((ARg (@YF5m.skel_cases imgk)) Hres S Hidx_def Hres_def).
Local Abbreviation AR8 f := (f DPOST S Hidx_def Hres_def) (only parsing).
Local Abbreviation skel_apart := (AR8 (AR7 (AR0 (AR6 (@YF5m.skel_apart _))))).
Local Abbreviation skel_u64 := (AR8 (ARh (AR0 (AR6 (@YF5m.skel_u64 _))))).
Local Abbreviation memset_ext_of_skel := (AR8 (AR7 (AR0 (AR6 (@YF5m.memset_ext_of_skel _))))).
Local Abbreviation memset_u64_of_skel := (AR8 (ARh (AR0 (AR6 (@YF5m.memset_u64_of_skel _))))).
Local Abbreviation WIN1R := ((ARi (@YF5m.WIN1R)) mb).
Local Abbreviation WSKEL1R := (@YF5m.WSKEL1R imgk).
Local Abbreviation WIN1R_WIN1S := (ARc (@YF5m.WIN1R_WIN1S)).
Local Abbreviation WIN1R_WIN := (AR5 (AR3 (@YF5m.WIN1R_WIN _))).
Local Abbreviation windows_WIN1R := (AR5 (ARb (AR1 (@YF5m.windows_WIN1R _)))).
Local Abbreviation mid_not_WIN1R := (ARh (AR3 (@YF5m.mid_not_WIN1R _))).
Local Abbreviation at_S_runR := (ARh (AR0 (AR6 (@YF5m.at_S_runR _ _)))).
Local Abbreviation at_S_run_ecallR := (ARh (AR0 (AR6 (@YF5m.at_S_run_ecallR _ _)))).
Local Abbreviation PSR := ((ARi (@YF5m.PSR)) ch mb).
Local Abbreviation rstable := ((ARi (@YF5m.rstable)) mb).
Local Abbreviation rstable_true := ((ARi (@YF5m.rstable_true)) mb).
Local Abbreviation PSR_stable := (AR7 (AR9 ((ARi (@YF5m.PSR_stable _)) ch))).
Local Abbreviation QSP := (@YF5m.QSP imgk ly idx).
Local Abbreviation QS_not_WIN1R := (AR7 (AR3 (@YF5m.QS_not_WIN1R _))).
Local Abbreviation QSP_rstable := (AR7 (AR3 (@YF5m.QSP_rstable _))).
Local Abbreviation at_S_memsetSR := ((AR5 ((AR0 ((AR4 (@YF5m.at_S_memsetSR _ _)) md0)) LY Hsp)) Hmap_apart mat0 DPOST S).
Local Abbreviation chunk_eqb := (@YF5m.chunk_eqb imgk).
Local Abbreviation chunk_eqb_eq := ((ARg (@YF5m.chunk_eqb_eq imgk)) Hres S Hidx_def Hres_def).
Local Abbreviation subregionb := (@YF5m.subregionb imgk).
Local Abbreviation subregionb_sound := (AR8 ((ARg (AR6 (@YF5m.subregionb_sound))) Hres)).
Local Abbreviation submemb := (@YF5m.submemb imgk).
Local Abbreviation submemb_sound := (AR8 ((ARg (AR6 (@YF5m.submemb_sound))) Hres)).
Local Abbreviation at_S_submem := (AR8 ((AR0 (AR6 (@YF5m.at_S_submem _))) Hidx Hres)).
Local Abbreviation at_S_addreg := (AR0 (AR6 (@YF5m.at_S_addreg _))).
Local Abbreviation PSR_runs := (AR0 (AR6 (@YF5i.PSR_runs _))).
Local Abbreviation place_WIN := (ARc (@YF5i.place_WIN)).
Local Abbreviation SH0 := (@YF5i.SH0 n mb).
Local Abbreviation SH1 := (@YF5i.SH1 n mb).
Local Abbreviation SH2 := (@YF5i.SH2 n mb).
Local Abbreviation SH_ok := (AR5 (AR3 (@YF5i.SH_ok _))).
Local Abbreviation segG1 := (AR8 ((AR7 (AR0 ((AR4 (@YF5i.segG1 _ _)) md0))) mat0)).
Local Abbreviation RX_stableS := (ARc (@YF5j.RX_stableS)).
Local Abbreviation rstable_and := ((ARi (@YF5j.rstable_and)) mb).
Local Abbreviation pstable_and := (@YF5j.pstable_and).
Local Abbreviation PSR_stableS' := (AR7 (AR9 ((ARi (@YF5j.PSR_stableS' _)) ch))).
Local Abbreviation pairwise_disjoint_map := (@YF5j.pairwise_disjoint_map).
Local Abbreviation at_S_setchunks := (AR0 (AR6 (@YF5j.at_S_setchunks _))).
Local Abbreviation chunk_ok_CVal_eqv := (@YF5j.chunk_ok_CVal_eqv imgk).
Local Abbreviation RES2T_ne := ((AR0 (AR1 (@YF5j.RES2T_ne))) Hidx Hres).
Local Abbreviation RES2T_eq := ((AR0 (AR1 (@YF5j.RES2T_eq))) Hidx Hres).
Local Abbreviation sv_denot_eq_of_U := (AR0 (AR1 (@YF5j.sv_denot_eq_of_U))).
Local Abbreviation skel_apart_QS := (AR8 (AR7 (AR0 (AR6 (@YF5j.skel_apart_QS _))))).
Local Abbreviation QSPX := (@YF5j.QSPX imgk ly idx).
Local Abbreviation segNE := (AR8 (AR7 (AR0 (AR6 (@YF5j.segNE _ _))))).
Local Abbreviation segEQa := (AR7 (AR0 (AR6 (@YF5j.segEQa _ _)))).
Local Abbreviation zev_SAlu := (@YF5j.zev_SAlu).
Local Abbreviation zev_SLit := (@YF5j.zev_SLit).
Local Abbreviation zev_SOff := (@YF5j.zev_SOff).
Local Abbreviation segJ2 := (AR8 (AR7 (AR0 (AR6 (@YF5j.segJ2 _ _))))).
Local Abbreviation segJ := (AR8 (AR7 (AR0 (AR6 (@YF5j.segJ _ _))))).
Local Abbreviation QR := (@YF5n.QR ly res).
Local Abbreviation segT1 := ((AR5 ((ARb (AR6 (@YF5n.segT1 _ _))) Hn Hsp)) Hmap_apart).
Local Abbreviation DX := (AR1 (@YF5n.DX)).
Local Abbreviation PD := (@YF5n.PD imgk ly mem0 DPOST).
Local Abbreviation PD_rstable := ((AR7 (AR9 ((AR6 (@YF5n.PD_rstable _)) n))) DPOST).
Local Abbreviation PD_stableT := ((AR7 (AR9 ((AR6 (@YF5n.PD_stableT _)) n))) DPOST).
Local Abbreviation PSR_stableS := (AR7 (AR9 ((ARi (@YF5n.PSR_stableS _)) ch))).
Local Abbreviation PD_stableS := ((AR7 (AR9 ((AR6 (@YF5n.PD_stableS _)) n))) DPOST).
Local Abbreviation PDX := (@YF5n.PDX imgk ly mem0 DPOST).
Local Abbreviation PDX_rstable := ((AR7 (AR9 ((AR6 (@YF5n.PDX_rstable _)) n))) DPOST).
Local Abbreviation PDX_stableT := ((AR7 (AR9 ((AR6 (@YF5n.PDX_stableT _)) n))) DPOST).
Local Abbreviation PDX_stableS := ((AR7 (AR9 ((AR6 (@YF5n.PDX_stableS _)) n))) DPOST).
Local Abbreviation dx_okb := (@YF5n.dx_okb imgk).
Local Abbreviation skel_apart_DX := (AR8 (AR7 (AR0 (AR6 (@YF5n.skel_apart_DX _))))).
Local Abbreviation skel_apart_stk := ((AR7 (AR0 (AR1 (@YF5n.skel_apart_stk _)))) S Hidx_def Hres_def).
Local Abbreviation at_S_depot := (AR8 (AR7 (AR0 (AR4 (@YF5n.at_S_depot _ _))))).
Local Abbreviation SH3 := (@YF5n.SH3 n mb).
Local Abbreviation SH4 := (@YF5n.SH4 n mb).
Local Abbreviation shadow_marks := (AR5 (AR3 (@YF5n.shadow_marks _))).
Local Abbreviation SH34_ok := (AR5 (AR3 (@YF5n.SH34_ok _))).
Local Abbreviation segT2b := (AR8 ((AR5 ((ARb ((AR4 (@YF5n.segT2b _ _)) md0)) Hn Hsp)) Hmap_apart mat0)).
Local Abbreviation segT2 := (AR8 ((AR5 ((ARb ((AR4 (@YF5n.segT2 _ _)) md0)) Hn Hsp)) Hmap_apart mat0)).
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
Local Abbreviation slackS := ((ARf (@YF5q.slackS _)) mem0 md0 B S HARm HQT).
Local Abbreviation S_N_facts := (@YF5q.S_N_facts imgk).
Local Abbreviation S_N_ext64 := ((AR2 (AR0 (AR1 (@YF5q.S_N_ext64 _)))) S).
Local Abbreviation S_N_win64 := ((AR2 (AR0 (AR1 (@YF5q.S_N_win64 _)))) S).
Local Abbreviation nodeS := ((AR2 (AR0 ((AR4 (@YF5q.nodeS _ _)) md0))) B S HARm HQT).
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
Variables (Wy : world tfxsegs) (md1 : Model).
Definition S_VG {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (mkSS (0x64c8c + D_2c4) (ss_regs S_V) (ss_mem S_V) None (ss_facts S_V)))).
Definition TQ : sv := SAlu ALU_ADD (SAlu ALU_AND (SAlu ALU_ADD (SOff aQ 0) (SAlu ALU_SLL (SOff aNCH 0) (SLit 3))) (SLit 18446744073709547520)) (SLit 0).
Lemma S_V_facts : ss_pc S_V = (0x64c88 + D_2c4) /\ sr_get (ss_regs S_V) 17%bv = SLit 222 /\ sr_get (ss_regs S_V) 10%bv = TQ /\ sr_get (ss_regs S_V) 11%bv = SLit 131072 /\
sr_get (ss_regs S_V) 12%bv = SLit 3 /\ sr_get (ss_regs S_V) 13%bv = SLit 50 /\ sr_get (ss_regs S_V) 14%bv = SLit 18446744073709551615 /\ sr_get (ss_regs S_V) 15%bv = SLit 0 /\
no_cdata (ss_mem S_V) = true /\ resume S_V TQ (ss_mem S_V) (ss_facts S_V) = S_VG /\ sv_atoms_lt sHAV TQ = true.
Proof. clear. img_case; vm_compute. all: repeat split; img_refl. Qed.
Definition ZQF (Wz : world tfxsegs) (m : word -> option byte) : Prop :=
forall a, QR a -> w_H Wz (Z_to_bv 64 a) = false /\ m (Z_to_bv 64 a) = Some (Z_to_bv 8 0).
Definition ZQ (Wz : world tfxsegs) (m : word -> option byte) : Prop :=
idx = res -> forall a, QR a -> ~ (QSv <= a < QSv + 8) -> w_H Wz (Z_to_bv 64 a) = false /\ m (Z_to_bv 64 a) = Some (Z_to_bv 8 0).
Lemma QR_facts : idx = res -> QSv = Qb + 8 * res /\ QSv mod 131072 = Qb mod 131072 /\ QSv mod 4096 = 0 /\ (4096 <= Qb <= QSv /\ zone3cases Qb kPtrArrayResv) /\ QSv + 131072 <= Qb + kPtrArrayResv /\
Qb + kPtrArrayResv <= ASAN_CEIL /\ (forall a, QR a <-> QSv <= a < QSv + 131072).
Proof.
intros Heq. pose proof high_facts as (_ & _ & _ & _ & _ & _ & _ & _ & F9 & F10 & F11 & _). pose proof Hidx as HI. pose proof Hres as [HRS HRM].
unfold kMaxNumChunks, kPtrArrayEntriesPerCommit in *. unfold page_aligned in F11. unfold zone3 in F9.
assert (E1 : QSv = Qb + 8 * res) by (img_try (unfold QSv; try unfold Qb; rewrite Heq; img_refl)).
apply Z.mod_divide in HRM as [q Hq]; [|img_try (zlia)]. apply Z.mod_divide in F11 as [p Hp]; [|img_try (zlia)].
split; [img_try (img_exact E1)|]. split. { rewrite E1, Hq. replace (Qb + 8 * (q * 16384)) with (Qb + q * 131072) by zlia. rewrite Z.add_mod, Z_mod_mult, Z.add_0_r, Z.mod_mod by zlia. img_refl. }
split. { rewrite E1, Hq. try unfold Qb in *. rewrite Hp. replace (p * 4096 + 8 * (q * 16384)) with ((p + q * 32) * 4096) by zlia. img_apply Z_mod_mult. }
split; [img_try (split; [rewrite E1; zlia | img_exact (proj2 (proj2 F9))])|]. split; [img_try (rewrite E1; unfold kPtrArrayResv; zlia)|]. split; [img_try (img_exact F10)|].
intros a. unfold QR. rewrite E1. unfold kPtrArrayEntriesPerCommit, kPtrArrayResv. zlia.
Qed.
Lemma ZQ_of_ZQF : forall Wz m, ZQF Wz m -> ZQ Wz m.
Proof. clearP. intros Wz m H _ a Ha _. img_exact (H a Ha). Qed.
Lemma QR_not_WIN1T : idx = res -> forall a, QR a -> ~ (QSv <= a < QSv + 8) -> ~ WIN1T a.
Proof.
intros Heq a Ha Hs Hw. pose proof (QR_facts Heq) as (E1 & _ & _ & F9 & Q5 & F10 & EQ). apply EQ in Ha.
pose proof high_facts as (F1 & F2 & _ & _ & _ & _ & F7 & F8 & _ & _ & _ & _ & _ & _ & F15).
pose proof map_facts as (M1 & M2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _ & PB & _). pose proof map_zoneN as MZ. pose proof size_facts as (_ & _ & _ & Z4 & _ & _ & _ & Z8 & _).
pose proof BSLv_range as HB. destruct Hsp as (S1 & _ & S3 & _). pose proof (lo_stk_ceil ly LY) as SC.
destruct Hmap_apart as (_ & _ & _ & MQ & _). pose proof HCX as (_ & _ & QT & CQ). unfold zdisjoint in MQ, QT, CQ. cbn [fst snd] in MQ, QT, CQ.
pose proof Nrange as NR. pose proof shadow_marks as (_ & A2 & A3 & _ & _ & A6 & _). pose proof size_facts as (_ & _ & Z3 & Z4' & _).
assert (D1 : N8D / 8 <= R8v / 8) by (img_try (img_apply Z.div_le_mono; clear - Z3 Z4' MZ; zlia)).
pose proof Hidx as HI. pose proof Hres as [HRS _]. unfold kMaxNumChunks in HI, HRS.
unfold WIN1T in Hw. clear EQ. destruct Hw as [Hw|[Hw|[Hw|Hw]]].
- unfold WIN1P, WINT, WINI in Hw. clear - Ha Hw Q5 F9 F10 SC S1 QT HB E1 Heq HI HRS MZ.
ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kPtrArrayResv, kThreadObjSize, ASTACK, IFRAME, t_unwinding, TFX_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex in *.
try unfold T in *. try unfold Qb in *. try unfold sp0 in *. zlia.
- img_exact (Hs Hw).
- clear - Ha Hw MQ Z8 Q5 E1 Heq HI HRS MZ. unfold kPtrArrayResv, MALLOC_MAX in *. try unfold Qb in *. zlia.
- clear - Ha Hw PB A2 A3 A6 SM2 D1 F9 Q5 E1 Heq HI HRS MZ Z4. unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighShadowEnd, kPtrArrayResv in *. try unfold Qb in *. zlia.
Qed.
Lemma ZQ_stableT : forall Wz, pstable WIN1T (ZQ Wz).
Proof.
intros Wz m m' FR H Heq a Ha Hs. destruct (H Heq a Ha Hs) as [H1 H2]. split; [img_try (img_exact H1)|]. rewrite FR; [img_try (img_exact H2)|].
pose proof (QR_facts Heq) as (_ & _ & _ & F9 & Q5 & F10 & EQ). pose proof (proj1 (EQ a) Ha) as Ra.
rewrite unsigned_lit_small by (img_try (clear - Ra F9 F10 Q5; ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kPtrArrayResv in *; try unfold Qb in *; zlia)). img_exact (QR_not_WIN1T Heq a Ha Hs).
Qed.
Lemma ZQ_rstable : forall Wz, rstable (ZQ Wz).
Proof.
intros Wz. split.
- intros m m' FR. img_apply (ZQ_stableT Wz m m'). intros x Hx. img_apply FR. intros Hw. img_exact (Hx (WIN1S_WIN1T _ (WIN1R_WIN1S _ Hw))).
- intros m m' d len Hp FR H Heq a Ha Hs. destruct (H Heq a Ha Hs) as [H1 H2]. split; [img_try (img_exact H1)|]. rewrite FR; [img_try (img_exact H2)|].
pose proof (QR_facts Heq) as (_ & _ & _ & F9 & Q5 & F10 & EQ). pose proof (proj1 (EQ a) Ha) as Ra.
pose proof map_facts as (M1 & M2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _). pose proof map_zoneN as MZ. destruct Hmap_apart as (_ & _ & _ & MQ & _). unfold zdisjoint in MQ. cbn [fst snd] in MQ.
rewrite unsigned_lit_small by (img_try (clear - Ra F9 F10 Q5 MZ; ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kPtrArrayResv in *; try unfold Qb in *; zlia)).
clear - Hp Ra MQ F9 F10 Q5 M1 M2 SM1 SM2 MZ. ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kPtrArrayResv, kHighShadowBeg, kHighShadowEnd in *. try unfold Qb in *. zlia.
Qed.
Lemma ZQ_stableD : forall Wz, pstable DX (ZQ Wz).
Proof.
intros Wz m m' FR H Heq a Ha Hs. destruct (H Heq a Ha Hs) as [H1 H2]. split; [img_try (img_exact H1)|]. rewrite FR; [img_try (img_exact H2)|].
pose proof (QR_facts Heq) as (_ & _ & _ & F9 & Q5 & F10 & EQ). pose proof (proj1 (EQ a) Ha) as Ra.
rewrite unsigned_lit_small by (img_try (clear - Ra F9 F10 Q5; ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kPtrArrayResv in *; try unfold Qb in *; zlia)).
pose proof blocks_facts as (NBhi & SBhi & _ & _ & QNB & QSB & _). unfold zdisjoint in QNB, QSB. cbn [fst snd] in QNB, QSB.
destruct Hsp as (S1 & _ & S3 & _). pose proof (lo_stk_ceil ly LY) as SC.
intros [Hd|Hd]; revert Hd; clear - Ra F9 F10 Q5 QNB QSB S1 S3 SC; ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, DZONE, DEP_STK, ASTACK, kHighMemBeg, ASAN_CEIL, kPtrArrayResv, kNodesBlockSize, kStoreBlockSize in *; try unfold Qb in *; try unfold sp0 in *; zlia.
Qed.
Lemma skel_apart_Q : forall (E' : env) r, env_agree sHAV E0 E' -> skel_okb false (skel r) = true -> YQ0b.r_base r <> Some aQS ->
base_val E' (YQ0b.r_base r) + YQ0b.r_hi r <= Qb \/ Qb + kPtrArrayResv <= base_val E' (YQ0b.r_base r) + YQ0b.r_lo r \/ YQ0b.r_hi r <= YQ0b.r_lo r.
Proof.
intros E' r [HE _] Hs Hnq. destruct r as [b lo hi wlo whi cs]. unfold skel in Hs. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi] in *.
pose proof high_facts as (F1 & F2 & _ & _ & _ & _ & F7 & F8 & F9 & F10 & _ & _ & _ & _ & F15).
pose proof map_facts as (M1 & M2 & _). pose proof map_zoneN as MZ. pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & _). pose proof BSLv_range as HB.
destruct Hsp as (S1 & _ & S3 & _). pose proof (lo_stk_ceil ly LY) as SC.
destruct Hmap_apart as (_ & _ & _ & MQ & _). pose proof HCX as (_ & _ & QT & CQ). unfold zdisjoint in MQ, QT, CQ. cbn [fst snd] in MQ, QT, CQ.
pose proof (u64_range (getr regs0 2)) as U2.
destruct (skel_cases false b lo hi wlo whi Hs) as [(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|(Epb & -> & A1 & A2)]]]]]]]; cbn [base_val].
- clear - A1 A2 F9 MZ. unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg in *. try unfold Qb in *. zlia.
- rewrite (HE 2%nat ltac:(img_try (unfold sHAV; zlia))), E2. clear - A1 A2 S1 SC F10 U2 MZ. ceil; unfold ASTACK, ASAN_CEIL in *. try unfold Qb in *. try unfold sp0 in *. zlia.
- rewrite (HE 32%nat ltac:(img_try (unfold sHAV; zlia))), EaT. unfold w64. rewrite unsigned_lit_small by (img_try (clear - F1 F2 MZ; numconst; try unfold T in *; zlia)).
clear - A1 A2 QT MZ. unfold kThreadObjSize in *. try unfold T in *. try unfold Qb in *. zlia.
- rewrite (HE 33%nat ltac:(img_try (unfold sHAV; zlia))), EaC. unfold w64. rewrite unsigned_lit_small by (img_try (clear - F7 F8 MZ; ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; zlia)).
clear - A1 A2 CQ MZ. try unfold Qb in *. zlia.
- unfold aMAP. rewrite (HE 45%nat ltac:(img_try (unfold sHAV; zlia))), EaMAP. unfold w64. rewrite unsigned_lit_small by (img_try (clear - M1 M2 Z8 MZ; ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; zlia)).
clear - A1 A2 MQ Z8 MZ. unfold MALLOC_MAX in *. try unfold Qb in *. zlia.
- exfalso. img_apply Hnq. img_refl.
- unfold aBSL. rewrite (HE 55%nat ltac:(img_try (unfold sHAV; zlia))), EaBSL. unfold w64. rewrite unsigned_lit_small by (img_try (clear - HB MZ; unfold TFX_INST in *; zlia)).
clear - A1 A2 HB F9 MZ. unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, TFX_INST in *. try unfold Qb in *. zlia.
- discriminate Epb.
Qed.
Lemma TQ_val : idx = res -> U E0 TQ = QSv.
Proof.
intros Heq. pose proof (QR_facts Heq) as (E1 & _ & QA & F9 & Q5 & F10 & _). pose proof Hidx as HI. pose proof Hres as [HRS _].
ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kMaxNumChunks, kHighMemBeg, ASAN_CEIL, kPtrArrayResv in *.
assert (HQb : 0 <= Qb /\ Qb + 8388608 <= 140737479966720) by (img_try (clear - F9 F10; zlia)).
clear - Heq E1 QA Q5 HI HRS HQb.
unfold TQ. rewrite U_zev by img_refl. cbn [zev zalu_raw zmd_raw]. unfold rho_of. unfold_atoms. rewrite EaQ, EaNCH. unfold w64.
try unfold Qb in *. rewrite !unsigned_lit_small by (img_try (clear - HI HQb; zlia)).
rewrite !Z.add_0_r. rewrite (zcanon_id idx) by (img_try (unfold M64; clear - HI; zlia)). img_change (Z.land (zcanon 3) 63) with 3. rewrite Z.shiftl_mul_pow2 by (img_try (clear; zlia)). img_change (2 ^ 3) with 8.
rewrite (zcanon_id (idx * 8)) by (img_try (unfold M64; clear - HI; zlia)). rewrite (zcanon_id (ly_Q ly)) by (img_try (unfold M64; clear - HQb; zlia)).
rewrite (zcanon_id (ly_Q ly + idx * 8)) by (img_try (unfold M64; clear - HI HQb; zlia)). img_change (zcanon 18446744073709547520) with (2 ^ 64 - 2 ^ 12).
rewrite land_neg_pow2_u64 by (img_try (clear - HI HQb; zlia)). img_change (2 ^ 12) with 4096.
assert (MZ : (ly_Q ly + idx * 8) mod 4096 = 0) by (img_try (rewrite Heq, (Z.mul_comm res 8), <- E1; img_exact QA)).
rewrite MZ, Z.sub_0_r. rewrite (zcanon_id (ly_Q ly + idx * 8)) by (img_try (unfold M64; clear - HI HQb; zlia)). rewrite zcanon_id by (img_try (unfold M64; clear - HI HQb; zlia)). rewrite E1, Heq. zlia.
Qed.
Lemma nores50 : mmap_noreserve_b (Z_to_bv 64 50) = false. Proof. clear. img_refl. Qed.
Lemma core50 : mmap_flags_core (Z_to_bv 64 50) = 50. Proof. clear. img_refl. Qed.
Lemma pru17 : page_round_up_Z 131072 = 131072. Proof. clear. img_refl. Qed.
Lemma grant_piece_shape : forall (a k : word) md, let md' := grant_md false (Z_to_bv 64 50) a k md in
vm_maps (m_vmmaps md') = vm_maps (m_vmmaps md) /\ vm_reserved (m_vmmaps md') = vm_reserved (m_vmmaps md) /\
vm_limit (m_vmmaps md') = vm_limit (m_vmmaps md) /\ vm_mmap_base (m_vmmaps md') = vm_mmap_base (m_vmmaps md).
Proof.
clear. intros a k md. cbv zeta. unfold grant_md, fixedin_ok_model, fixedin_ok_vmmaps, with_mmap_replacement, with_mmap_backing. rewrite nores50. cbn.
destruct md as [fd [maps lazy mat] io fs pr lim tm sg sc]. cbn. destruct maps; cbn. repeat split; img_refl.
Qed.
Lemma nodeV : forall {RT : Type} (sN : astate) (K : Z -> itree astate RT) (Q : RT -> world tfxsegs -> config -> Prop)
(R : (word -> option byte) -> Prop) (c1 : config),
idx = res ->
at_N Wy md1 WIN (PSR Wy SH2 R) S_V Wy c1 -> AI tfxsegs (w_H Wy) (w_A Wy) (cfg_model c1) ->
(forall m m' : word -> option byte, (forall x : word, ~ QR (bv_unsigned x) -> m' x = m x) -> R m -> R m') ->
amwf (cfg_model c1) ->
vm_reserved (m_vmmaps (cfg_model c1)) = segments_reserved tfxsegs ->
(forall sg, In sg tfxsegs -> 4096 <= Z.of_N (seg_base sg) /\ Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <= kImgEnd) ->
In (wiv (Qb, kPtrArrayResv)) (vm_maps (m_vmmaps (cfg_model c1))) ->
eager_used (cfg_model c1) + A_bytes (w_A Wy) + 2 ^ 36 <= vm_limit (m_vmmaps (cfg_model c1)) ->
YN05.ceil_of_top (alloc_top (m_vmmaps (cfg_model c1))) ->
(forall z, z = 0 \/ z = 1 -> aok sN (KMapPtrArray (8 * idx) kPtrArrayCommit) z) ->
(forall c', at_S Wy (cfg_model c1) WIN (PSR Wy SH2 R) (resume S_V (SLit ENOMEM_RETv) (ss_mem S_V) (ss_facts S_V)) Wy c' ->
AI tfxsegs (w_H Wy) (w_A Wy) (cfg_model c') -> srealizesM tfxsegs false c' t_nil) ->
(forall c', let md3 := fixedin_destroyed_model (w64 QSv) (w64 131072) (cfg_model c1) in
at_S Wy md3 (fun a => WIN a \/ QR a) (PSR Wy SH2 R) (resume S_V (SLit ENOMEM_RETv) (ss_mem S_V) (ss_facts S_V)) Wy c' ->
AI tfxsegs (w_H Wy) (w_A Wy) (cfg_model c') -> srealizesM tfxsegs false c' t_nil) ->
(forall (W5 : world tfxsegs) (c' : config), let md5 := grant_md false (Z_to_bv 64 50) (w64 QSv) (w64 131072) (cfg_model c1) in
wle Wy W5 -> hsub (w_H W5) (w_H Wy) -> (forall x : word, w_H Wy x = false -> w_H W5 x = false) ->
w_A W5 = (QSv, QSv + 131072) :: w_A Wy ->
(forall x : word, QSv <= bv_unsigned x < QSv + 131072 -> w_H W5 x = false) ->
(forall x : word, ~ (QSv <= bv_unsigned x < QSv + 131072) -> w_H W5 x = w_H Wy x) ->
AI tfxsegs (w_H W5) (w_A W5) md5 -> amwf md5 -> same_io md0 md5 -> eager_used md5 <= eager_used (cfg_model c1) + 131072 ->
vm_maps (m_vmmaps md5) = vm_maps (m_vmmaps (cfg_model c1)) /\ vm_reserved (m_vmmaps md5) = vm_reserved (m_vmmaps (cfg_model c1)) /\
vm_limit (m_vmmaps md5) = vm_limit (m_vmmaps (cfg_model c1)) /\ vm_mmap_base (m_vmmaps md5) = vm_mmap_base (m_vmmaps (cfg_model c1)) ->
at_S W5 md5 (fun a => WIN a \/ QR a) (PSR W5 SH2 (fun m => R m /\ ZQF W5 m)) S_VG W5 c' ->
amreal tfxsegs (K 1) W5 c' Q) ->
same_io md0 (cfg_model c1) ->
exists (I : Type) (nx : I -> config) (bit : I -> Z) (sp : I -> bool) (i0 : I),
node_ok tfxsegs c1 I (fun _ => []) nx /\
(forall i, AI tfxsegs (w_H Wy) (w_A Wy) (cfg_model c1) -> AI tfxsegs (w_H Wy) (w_A Wy) (cfg_model (nx i))) /\
(forall i, aok sN (KMapPtrArray (8 * idx) kPtrArrayCommit) (bit i)) /\ sp i0 = false /\ bit i0 = 1 /\
(refusable (KMapPtrArray (8 * idx) kPtrArrayCommit) = true -> exists i1, sp i1 = false /\ bit i1 = 0) /\
(forall i, sp i = true -> AI tfxsegs (w_H Wy) (w_A Wy) (cfg_model (nx i)) -> srealizesM tfxsegs false (nx i) t_nil) /\
(forall i, (sp i = true \/ bit i <> 1) -> fo_dead tfxsegs c1 (nx i)) /\
(forall i, sp i = false -> if Z.eqb (bit i) 1 then amreal tfxsegs (K (bit i)) Wy (nx i) Q else amrealE tfxsegs (K (bit i)) Wy (nx i) Q).
Proof.
intros RT sN K Q R c1 Heq HN HAI RQ MW RSV IMGS INQ SL0 HTOP Haok DIE DIE3 GRANT IO0.
pose proof (QR_facts Heq) as (E1 & _ & QA & F9 & Q5 & F10 & EQR).
destruct HN as (_ & ms & mat & E' & Ec & HE & HS & Hrv & MEQ & PRS & HPm).
set (mdN := with_vm_backing (m_vm_lazy md1) mat md1) in *.
assert (EcM : cfg_model c1 = mdN) by (img_try (rewrite Ec; img_refl)). rewrite EcM in *.
assert (MWF0 : MWF mdN) by (img_try (img_apply (proj1 (amwf_MWF mdN)); img_exact (proj1 MW))).
destruct (st_ok_ecall_shape_r tfxsegs (w_H Wy) E' S_V ms HS Hrv) as (regs & mem & Hms & Hregs & Hmem & HG).
assert (HEn : forall k, (k < sHAV)%nat -> ew E' k = ew E0 k) by (img_try (img_exact (proj1 HE))).
pose proof S_V_facts as (Hpc & H17 & H10 & H11 & H12 & H13 & H14 & H15 & Hnc & Hres_g & Hatq).
assert (UQS : bv_unsigned (w64 QSv) = QSv) by (img_try (unfold w64; img_apply unsigned_lit_small; clear - F9 F10 Q5 E1; ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kPtrArrayResv in *; try unfold Qb in *; zlia)).
assert (Un : bv_unsigned (w64 131072) = 131072) by (img_try (unfold w64; img_apply unsigned_lit_small; clear; zlia)).
assert (R17 : getr regs 17 = Z_to_bv 64 222) by (img_try (rewrite (Hregs 17%bv), H17; img_refl)).
assert (R10 : getr regs 10 = w64 QSv).
{ rewrite (Hregs 10%bv), H10. unfold w64. rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E' TQ)). f_equal.
img_change (bv_unsigned (sv_denot E' TQ)) with (U E' TQ). rewrite (U_agree sHAV E0 E' TQ HE Hatq). img_exact (TQ_val Heq). }
assert (R11 : getr regs 11 = Z_to_bv 64 131072) by (img_try (rewrite (Hregs 11%bv), H11; img_refl)).
assert (R12 : getr regs 12 = Z_to_bv 64 3) by (img_try (rewrite (Hregs 12%bv), H12; img_refl)).
assert (R13 : getr regs 13 = Z_to_bv 64 50) by (img_try (rewrite (Hregs 13%bv), H13; img_refl)).
assert (R14 : getr regs 14 = Z_to_bv 64 (-1)) by (img_try (rewrite (Hregs 14%bv), H14; cbn [sv_denot]; img_apply lit_m1)).
assert (R15 : getr regs 15 = Z_to_bv 64 0) by (img_try (rewrite (Hregs 15%bv), H15; img_refl)).
assert (CEIL : bv_unsigned (w64 QSv) + page_round_up_Z 131072 <= alloc_ceiling).
{ rewrite UQS, pru17. clear - Q5 F10. ceil; unfold ASAN_CEIL, kPtrArrayResv in *. zlia. }
assert (CEILT : bv_unsigned (w64 QSv) + page_round_up_Z 131072 <= alloc_top (m_vmmaps mdN)).
{ eapply Z.le_trans; [img_try (img_exact CEIL) | img_try (img_apply YN05.ceil_le_top; img_exact HTOP)]. }
assert (PLACE : region_free (vm_reserved (m_vmmaps mdN)) (w64 QSv) (Z_to_bv 64 (page_round_up_Z 131072)) = true /\
map_contains (vm_maps (m_vmmaps mdN)) (w64 QSv) (Z_to_bv 64 (page_round_up_Z 131072)) = true).
{ rewrite pru17. split.
- rewrite RSV. pose proof high_facts as (_ & _ & _ & _ & _ & _ & _ & _ & F9z & _).
img_apply (tfx_region_free_reserved QSv 131072); [img_try (clear; zlia) | img_try (clear - F9 F10 Q5 E1; ceil; unfold ASAN_CEIL, kPtrArrayResv in *; try unfold Qb in *; zlia) |].
clear - F9z F9 Q5 E1. unfold zone3, zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kHighMemBeg, kPtrArrayResv in *. try unfold Qb in *. zlia.
- img_apply (YA09.map_contains_intro _ (w64 QSv) (w64 131072) (w64 Qb) (w64 kPtrArrayResv) INQ);
unfold w64; rewrite !unsigned_lit_small by (img_try (clear - F9 F10 Q5 E1; ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kPtrArrayResv in *; try unfold Qb in *; zlia));
clear - Q5 E1 Heq F9; unfold kPtrArrayResv in *; try unfold Qb in *; zlia. }
assert (SL1 : eager_used mdN + A_bytes (w_A Wy) + page_round_up_Z 131072 <= vm_limit (m_vmmaps mdN)) by (img_try (rewrite pru17; clear - SL0; zlia)).
assert (ALQ : bv_unsigned (w64 QSv) mod page_size = 0) by (img_try (rewrite UQS; unfold page_size; img_exact QA)).
pose proof (commit_AI tfxsegs (w_H Wy) (w_A Wy) mdN false (Z_to_bv 64 50) (w64 QSv) 131072 HAI MWF0 nores50 ALQ ltac:(img_try (clear; zlia)) CEILT PLACE SL1) as [CG BUD].
pose proof (commit_eager tfxsegs (w_H Wy) (w_A Wy) mdN false (Z_to_bv 64 50) (w64 QSv) 131072 HAI MWF0 nores50 ALQ ltac:(img_try (clear; zlia)) CEILT PLACE SL1) as EG.
pose proof (commit_nonempty false (Z_to_bv 64 50) (w64 QSv) (Z_to_bv 64 (page_round_up_Z 131072)) mdN ltac:(img_try (rewrite pru17; unfold w64 in Un; rewrite Un; clear; zlia)) (proj2 MW)) as NZg.
rewrite pru17 in CG, BUD, EG, NZg. fold (w64 131072) in CG, BUD, EG, NZg.
pose proof (destroyed_AI tfxsegs (w_H Wy) (w_A Wy) mdN (w64 QSv) 131072 HAI MWF0 ALQ ltac:(img_try (clear; zlia)) CEILT) as [CD _].
rewrite pru17 in CD. fold (w64 131072) in CD.
destruct (commit_node3 tfxsegs false regs (Z_to_bv 64 (0x64c88 + D_2c4)) mem (seg_rom tfxsegs) mdN (Z_to_bv 64 50) (w64 QSv) 131072
(AI_halted _ _ _ _ HAI) R17 R10 ALQ ltac:(img_try (rewrite UQS; clear - F9; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg in *; zlia))
R11 ltac:(img_try (clear; zlia)) CEILT R12 R13 core50 R14 R15 PLACE BUD) as (I & nx & bit & i0 & iR & NODE & Bi0 & Bi1 & _ & OUT).
rewrite pru17 in OUT. fold (w64 131072) in OUT.
assert (IOtr : forall m2, YG0b.same_io mdN m2 -> same_io md0 m2).
{ intros m2 (X1 & X2 & X3 & X4). destruct IO0 as (Y1 & Y2 & Y3 & Y4). unfold same_io. rewrite X1, X2, X3, X4. repeat split; assumption. }
exists I, nx, (fun i => if bit i =? 1 then 1 else 0), (fun i => negb (bit i =? 1)), i0.
split. { rewrite Ec, Hms, Hpc. img_exact NODE. }
split. { intros i _. destruct (OUT i) as (md_i & _ & _ & [[_ [-> ->]] | [(_ & -> & ->) | (_ & _ & -> & ->)]]); cbn [cfg_model]; [img_try (img_exact HAI) | img_try (img_exact (proj1 CG)) | img_try (img_exact (proj1 CD))]. }
split. { intros i. img_apply Haok. destruct (bit i =? 1); [img_try (right) | img_try (left)]; img_refl. }
split; [img_try (rewrite Bi0; img_refl)|]. split; [img_try (rewrite Bi0; img_refl)|]. split; [img_try (intros E; discriminate E)|].
assert (APQ0 : forall r y, In r (ss_mem S_V) -> base_val E' (YQ0b.r_base r) + YQ0b.r_lo r <= y < base_val E' (YQ0b.r_base r) + YQ0b.r_hi r -> ~ QR y /\ 0 <= y < 2 ^ 64).
{ intros r y Hr Hy.
pose proof (proj1 (forallb_forall _ _) (ltac:(img_eqrefl) : forallb (fun r => skel_okb false (skel r) && negb (obase_eqb (YQ0b.r_base r) (Some aQS))) (ss_mem S_V) = true) r Hr) as CK.
cbn beta in CK. apply andb_prop in CK as [CK1 CK2].
assert (NB : YQ0b.r_base r <> Some aQS) by (img_try (intros Eq; rewrite Eq in CK2; discriminate CK2)).
split; [| img_try (img_exact (skel_u64 E' false r y HE CK1 Hy))]. intros Hq. apply (proj1 (EQR y)) in Hq.
pose proof (skel_apart_Q E' r HE CK1 NB) as AP. clear - Hy Hq AP Q5 F9. zlia. }
split.
{
intros i Hspin HAIi. apply negb_true_iff in Hspin. apply Z.eqb_neq in Hspin.
destruct (OUT i) as (md_i & Hh_i & IO_i & [[Bv [NX MD]] | [(Bv & _) | (Bv & _ & NX & MD)]]); [| img_try (exfalso; img_exact (Hspin Bv)) |].
- rewrite NX in HAIi |- *. rewrite MD in HAIi |- *. cbn [cfg_model] in HAIi.
img_apply (DIE _); [| img_try (img_exact HAIi)].
pose proof (at_N_cont Wy Wy mdN WIN (PSR Wy SH2 R) S_V (SLit ENOMEM_RETv) (errno_ret ENOMEM) (fun _ => False) mem ms E' HE HS Hrv MEQ PRS (hsub_refl _)
ltac:(img_try (cbn [sv_denot]; img_apply lit_enomem)) Hnc ltac:(img_try (intros x _; rewrite Hms; img_refl))
(fun r y Hr Hy => conj (fun f : False => f) (skel_u64 E' false r y HE (proj1 (forallb_forall _ _) (ltac:(img_eqrefl) : forallb (fun r => skel_okb false (skel r)) (ss_mem S_V) = true) r Hr) Hy))
(fun r y Hr Hy => conj (fun f : False => f) (skel_u64 E' false r y HE (proj1 (forallb_forall _ _) (ltac:(img_eqrefl) : forallb (fun r => skel_okb false (skel r)) (ss_mem S_V) = true) r Hr)
ltac:(img_try (pose proof (region_wf_facts r (regions_wf_In _ r (proj1 Hmem) Hr)) as (_ & WW & _); clear - Hy WW; zlia))))
(fun y _ (f : False) => f) ltac:(img_try (rewrite Hms in HPm; img_exact HPm))) as C.
rewrite Hms in C. cbn [ms_regs pend_at] in C. rewrite Hpc in C.
eapply at_S_weaken; [img_try (img_exact C) | img_try (intros y [Hy|[]]; img_exact Hy) | img_try (intros m Hm; img_exact Hm)].
-
rewrite NX in HAIi |- *. rewrite MD in HAIi |- *. cbn [cfg_model] in HAIi.
img_apply (DIE3 _); [| img_try (img_exact HAIi)].
assert (FRu : forall x : word, ~ QR (bv_unsigned x) -> unfill (w64 QSv) (w64 131072) mem x = mem x).
{ intros x Hx. img_apply unfill_out. rewrite UQS, Un. pose proof (EQR (bv_unsigned x)) as EQx. clear - Hx EQx.
destruct (Z_lt_le_dec (bv_unsigned x) QSv); [img_try (left; zlia)|]. right. destruct (Z_lt_le_dec (bv_unsigned x) (QSv + 131072)); [img_try (exfalso; img_apply Hx; img_apply EQx; zlia) | img_try (zlia)]. }
pose proof (at_N_cont Wy Wy (fixedin_destroyed_model (w64 QSv) (w64 131072) mdN) WIN (PSR Wy SH2 R) S_V (SLit ENOMEM_RETv) (errno_ret ENOMEM) QR (unfill (w64 QSv) (w64 131072) mem) ms E'
HE HS Hrv MEQ PRS (hsub_refl _) ltac:(img_try (cbn [sv_denot]; img_apply lit_enomem)) Hnc ltac:(img_try (intros x Hx; rewrite Hms; cbn [ms_mem pend_at]; img_exact (FRu x Hx)))
APQ0
(fun r y Hr Hy => APQ0 r y Hr ltac:(img_try (pose proof (region_wf_facts r (regions_wf_In _ r (proj1 Hmem) Hr)) as (_ & WW & _); clear - Hy WW; zlia)))
ltac:(img_try (intros y Hy Hq; apply (proj1 (EQR y)) in Hq; destruct Hsp as (S1 & _ & S3 & _); pose proof (lo_stk_ceil ly LY) as SC;
clear - Hy Hq S1 S3 SC Q5 F10; ceil; unfold ASAN_CEIL, ASTACK, kPtrArrayResv in *; try unfold sp0 in *; try unfold Qb in *; zlia))) as C.
rewrite Hms in C. cbn [ms_regs ms_mem pend_at] in C. rewrite Hpc in C. img_apply C. clear C.
rewrite Hms in HPm. cbn [ms_mem pend_at] in HPm. destruct HPm as [(HB & HM & HSH & HRs) HR0].
pose proof map_facts as (M1 & M2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _). pose proof map_zoneN as MZ. destruct Hmap_apart as (_ & _ & _ & MQ & _). unfold zdisjoint in MQ. cbn [fst snd] in MQ.
assert (NQR : forall a, (mb + 6144 <= a < mb + MSv) \/ (SMv <= a < SMv + MSv / 8) -> ~ QR a /\ bv_unsigned (Z_to_bv 64 a) = a).
{ intros a Ha. split.
- intros Hq. apply (proj1 (EQR a)) in Hq. clear - Ha Hq MQ Q5 F9 F10 M1 M2 SM1 SM2 E1 Heq MZ. ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kPtrArrayResv, kHighShadowBeg, kHighShadowEnd in *. try unfold Qb in *. zlia.
- img_apply unsigned_lit_small. clear - Ha M1 M2 SM1 SM2 MZ. ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kHighShadowBeg, kHighShadowEnd in *. zlia. }
split; [img_try (split; [|split; [|split]])|].
+   intros j Hj. pose proof tr_length as LEN. pose proof (lo_top ly LY) as (_ & _ & _ & T4 & _ & _ & T7). destruct Hsp as (S1 & _ & S3 & _). pose proof (u64_range (getr regs0 2)) as U2.
pose proof (lo_stk_ceil ly LY) as SC.
intros kk Hkk. pose proof (HB j Hj kk Hkk) as X.
lazymatch goal with |- mbyte _ _ ?A = _ =>
assert (RNG : sp0 - ASTACK <= A < sp0) by (img_try (clear - Hj Hkk LEN MZ; unfold IFRAME, ASTACK; zlia));
unfold mbyte, mrestrict in X |- *; rewrite (FRu (Z_to_bv 64 A)); [img_try (img_exact X)|];
rewrite unsigned_lit_small by (img_try (clear - RNG S1 S3 T4 T7 U2 MZ; unfold zone3, TFX_IMG_LO, kLowShadowBeg, IFRAME, ASTACK, kHighMemBeg, kHighMemEnd in *; try unfold sp0 in *; zlia));
intros Hq; apply (proj1 (EQR _)) in Hq; clear - RNG Hq S1 SC Q5 F10 MZ; ceil; unfold ASAN_CEIL, ASTACK, kPtrArrayResv in *; try unfold sp0 in *; try unfold Qb in *; zlia
end.
+ intros a Ha. destruct (NQR a (or_introl Ha)) as [Nq Ua]. destruct (HM a Ha) as [Hh [b Hb]]. split; [img_try (img_exact Hh)|]. exists b. rewrite FRu; [img_try (img_exact Hb) | img_try (rewrite Ua; img_exact Nq)].
+ intros a Ha. destruct (NQR a (or_intror Ha)) as [Nq Ua]. destruct (HSH a Ha) as [Hh [b Hb]]. split; [img_try (img_exact Hh)|]. exists b. rewrite FRu; [img_try (img_exact Hb) | img_try (rewrite Ua; img_exact Nq)].
+ pose proof SH_ok as (_ & _ & OK2). img_apply Forall_forall. intros r Hr a Ha. pose proof (proj1 (Forall_forall _ _) OK2 r Hr) as RO.
assert (PL : (mb + 6144 <= a < mb + MSv) \/ (SMv <= a < SMv + MSv / 8)) by (img_try (unfold run_ok in RO; clear - RO Ha MZ; zlia)).
destruct (NQR a PL) as [Nq Ua]. unfold w64. rewrite FRu by (img_try (rewrite Ua; img_exact Nq)). img_exact (proj1 (Forall_forall _ _) HRs r Hr a Ha).
+ img_exact (RQ mem _ FRu HR0). }
split. { (* [comment removed for export] *)
destruct (OUT i0) as (md_0 & _ & _ & [[B0 _] | [(_ & NX0 & _) | (B0 & _)]]); [img_try (rewrite Bi0 in B0; discriminate B0) | | img_try (rewrite Bi0 in B0; discriminate B0)].
assert (H222 : bv_unsigned (getr regs 17) = 222) by (img_try (rewrite R17; img_refl)).
assert (A0 : forall v : word, reg_get (regupd regs 10 v) (Z_to_bv 5 10) = v).
{ intros v. replace (Z_to_bv 5 10) with (10%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). img_apply regupd_same. }
assert (LT0 : bv_unsigned (w64 QSv) < 2 ^ 64 - 4095).
{ pose proof (alloc_top_room (m_vmmaps mdN)) as ROOM. pose proof CEILT as CT. rewrite pru17 in CT.
clear - ROOM CT. unfold two_pow_64, stack_max_size in ROOM. zlia. }
assert (DEADi : forall i md_i mm, nx i = mkCfg (mkst (regupd regs 10 (errno_ret ENOMEM)) (v_addi (Z_to_bv 64 (0x64c88 + D_2c4)) 4) mm (seg_rom tfxsegs)) md_i ->
fo_dead tfxsegs c1 (nx i)).
{ intros i md_i mm NX. rewrite Ec, Hms, Hpc.
img_apply (fo_dead_node tfxsegs (pend_at regs (Z_to_bv 64 (0x64c88 + D_2c4)) mem (seg_rom tfxsegs)) mdN (getr regs 17) I (fun _ => []) nx i0 i NODE eq_refl
(injected_family_off_mmap tfxsegs _ _ H222)).
- rewrite NX0. img_refl.
- rewrite NX0. cbn [cfg_ms ms_regs mkst]. rewrite A0. img_exact (mmap_grant_not_refusal tfxsegs _ _ mdN (w64 QSv) H222 LT0).
- rewrite NX. img_refl.
- rewrite NX. cbn [cfg_ms ms_regs mkst]. rewrite A0. img_exact (mmap_enomem_refusal tfxsegs _ _ mdN H222). }
intros i Hd. cbv beta in Hd.
destruct (OUT i) as (md_i & _ & _ & [[_ [NX _]] | [(Bv & _) | (_ & _ & NX & _)]]);
[img_try (img_exact (DEADi _ _ _ NX)) | img_try (exfalso; rewrite Bv in Hd; destruct Hd as [Hd|Hd]; [discriminate Hd | img_exact (Hd eq_refl)]) | img_try (img_exact (DEADi _ _ _ NX))]. }
intros i Hspin. apply negb_false_iff in Hspin. apply Z.eqb_eq in Hspin.
destruct (OUT i) as (md_i & Hh_i & IO_i & [[Bv _] | [(Bv & NX & MD) | (Bv & _)]]); [img_try (rewrite Bv in Hspin; discriminate Hspin) | | img_try (rewrite Bv in Hspin; discriminate Hspin)].
rewrite Bv, NX. change (if 1 =? 1 then 1 else 0) with 1. cbn [Z.eqb Pos.eqb]. rewrite MD in IO_i |- *.
set (md5 := grant_md false (Z_to_bv 64 50) (w64 QSv) (w64 131072) mdN) in *.
pose proof (grant_piece_shape (w64 QSv) (w64 131072) mdN) as (SH1 & SH2' & SH3 & SH4). cbv zeta in SH1, SH2', SH3, SH4. fold md5 in SH1, SH2', SH3, SH4.
assert (AL1 : QSv <= QSv + 131072) by (img_try (clear; zlia)).
assert (AL2 : QSv mod page_size = 0) by (img_try (unfold page_size; img_exact QA)).
assert (AL3 : (QSv + 131072) mod page_size = 0).
{ unfold page_size. clear - QA. apply Z.mod_divide in QA as [q' Hq]; [|img_try (zlia)]. rewrite Hq. img_apply Z.mod_divide; [img_try (zlia)|]. exists (q' + 32). zlia. }
destruct (allow_expose tfxsegs Wy md5 QSv (QSv + 131072) AL1 AL2 AL3 (proj1 CG) ltac:(img_try (rewrite SH3; clear - EG SL0; zlia))) as (LE5 & A5 & AB5 & VIS5 & MON5 & AI5).
set (W5 := wallow tfxsegs Wy QSv (QSv + 131072) AL1 AL2 AL3) in *.
assert (SUB : hsub (w_H W5) (w_H Wy)).
{ intros x Hx. destruct (w_H Wy x) eqn:Ex; [img_refl|]. rewrite (MON5 x Ex) in Hx. discriminate Hx. }
eapply (amreal_world_le tfxsegs _ Wy W5); [img_try (img_exact LE5) | img_try (intros _; img_exact AI5) |].
img_apply (GRANT W5); [img_try (img_exact LE5) | img_try (img_exact SUB) | img_try (img_exact MON5) | img_try (img_exact A5) | img_try (img_exact VIS5)
| img_try (intros x Nx; unfold W5, wallow; cbn [w_H]; img_apply Hcut_out; img_exact Nx)
| img_try (img_exact AI5) | img_try (split; [img_apply (proj2 (amwf_MWF md5)); img_exact (proj2 CG) | img_exact NZg]) | img_try (img_exact (IOtr _ IO_i)) | img_try (img_exact EG)
| img_try (rewrite SH1, SH2', SH3, SH4; repeat split; img_refl) |].
assert (FRz : forall x : word, ~ QR (bv_unsigned x) -> zfill (w64 QSv) (w64 131072) mem x = mem x).
{ intros x Hx. img_apply zfill_out. rewrite UQS, Un. pose proof (EQR (bv_unsigned x)) as EQx. clear - Hx EQx.
destruct (Z_lt_le_dec (bv_unsigned x) QSv); [img_try (left; zlia)|]. right. destruct (Z_lt_le_dec (bv_unsigned x) (QSv + 131072)); [img_try (exfalso; img_apply Hx; img_apply EQx; zlia) | img_try (zlia)]. }
assert (APQ : forall r y, In r (ss_mem S_V) -> base_val E' (YQ0b.r_base r) + YQ0b.r_lo r <= y < base_val E' (YQ0b.r_base r) + YQ0b.r_hi r -> ~ QR y /\ 0 <= y < 2 ^ 64).
{ intros r y Hr Hy.
pose proof (proj1 (forallb_forall _ _) (ltac:(img_eqrefl) : forallb (fun r => skel_okb false (skel r) && negb (obase_eqb (YQ0b.r_base r) (Some aQS))) (ss_mem S_V) = true) r Hr) as CK.
cbn beta in CK. apply andb_prop in CK as [CK1 CK2].
assert (NB : YQ0b.r_base r <> Some aQS) by (img_try (intros Eq; rewrite Eq in CK2; discriminate CK2)).
split; [| img_try (img_exact (skel_u64 E' false r y HE CK1 Hy))]. intros Hq. apply (proj1 (EQR y)) in Hq.
pose proof (skel_apart_Q E' r HE CK1 NB) as AP. clear - Hy Hq AP Q5 F9. zlia. }
pose proof (at_N_cont Wy W5 md5 WIN (PSR W5 SH2 (fun m => R m /\ ZQF W5 m)) S_V TQ (w64 QSv) QR (zfill (w64 QSv) (w64 131072) mem) ms E'
HE HS Hrv MEQ PRS SUB ltac:(img_try (rewrite <- R10, (Hregs 10%bv), H10; img_refl)) Hnc ltac:(img_try (intros x Hx; rewrite Hms; cbn [ms_mem pend_at]; img_exact (FRz x Hx)))
APQ
(fun r y Hr Hy => APQ r y Hr ltac:(img_try (pose proof (region_wf_facts r (regions_wf_In _ r (proj1 Hmem) Hr)) as (_ & WW & _); clear - Hy WW; zlia)))
ltac:(img_try (intros y Hy Hq; apply (proj1 (EQR y)) in Hq; destruct Hsp as (S1 & _ & S3 & _); pose proof (lo_stk_ceil ly LY) as SC;
clear - Hy Hq S1 S3 SC Q5 F10; ceil; unfold ASAN_CEIL, ASTACK, kPtrArrayResv in *; try unfold sp0 in *; try unfold Qb in *; zlia))) as C.
rewrite Hms in C. cbn [ms_regs ms_mem pend_at] in C. rewrite Hpc, Hres_g in C. img_apply C. clear C.
rewrite Hms in HPm. cbn [ms_mem pend_at] in HPm. destruct HPm as [(HB & HM & HSH & HRs) HR0].
pose proof map_facts as (M1 & M2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _). pose proof map_zoneN as MZ. destruct Hmap_apart as (_ & _ & _ & MQ & _). unfold zdisjoint in MQ. cbn [fst snd] in MQ.
assert (NQR : forall a, (mb + 6144 <= a < mb + MSv) \/ (SMv <= a < SMv + MSv / 8) -> ~ QR a /\ bv_unsigned (Z_to_bv 64 a) = a).
{ intros a Ha. split.
- intros Hq. apply (proj1 (EQR a)) in Hq. clear - Ha Hq MQ Q5 F9 F10 M1 M2 SM1 SM2 E1 Heq MZ. ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kPtrArrayResv, kHighShadowBeg, kHighShadowEnd in *. try unfold Qb in *. zlia.
- img_apply unsigned_lit_small. clear - Ha M1 M2 SM1 SM2 MZ. ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kHighShadowBeg, kHighShadowEnd in *. zlia. }
split; [img_try (split; [|split; [|split]])|img_try (split)].
-   intros j Hj. pose proof tr_length as LEN. pose proof (lo_top ly LY) as (_ & _ & _ & T4 & _ & _ & T7). destruct Hsp as (S1 & _ & S3 & _). pose proof (u64_range (getr regs0 2)) as U2.
pose proof (lo_stk_ceil ly LY) as SC.
intros kk Hkk. pose proof (HB j Hj kk Hkk) as X.
lazymatch goal with |- mbyte _ _ ?A = _ =>
assert (RNG : sp0 - ASTACK <= A < sp0) by (img_try (clear - Hj Hkk LEN MZ; unfold IFRAME, ASTACK; zlia));
destruct (PRS _ RNG) as [HhW _];
assert (HhY : w_H W5 (Z_to_bv 64 A) = false) by (img_try (img_apply MON5; img_exact HhW));
unfold mbyte, mrestrict in X |- *; rewrite HhW in X; rewrite HhY; rewrite (FRz (Z_to_bv 64 A)); [img_try (img_exact X)|];
rewrite unsigned_lit_small by (img_try (clear - RNG S1 S3 T4 T7 U2 MZ; unfold zone3, TFX_IMG_LO, kLowShadowBeg, IFRAME, ASTACK, kHighMemBeg, kHighMemEnd in *; try unfold sp0 in *; zlia));
intros Hq; apply (proj1 (EQR _)) in Hq; clear - RNG Hq S1 SC Q5 F10 MZ; ceil; unfold ASAN_CEIL, ASTACK, kPtrArrayResv in *; try unfold sp0 in *; try unfold Qb in *; zlia
end.
- intros a Ha. destruct (NQR a (or_introl Ha)) as [Nq Ua]. destruct (HM a Ha) as [Hh [b Hb]]. split; [img_try (img_exact (MON5 _ Hh))|]. exists b. rewrite FRz; [img_try (img_exact Hb) | img_try (rewrite Ua; img_exact Nq)].
- intros a Ha. destruct (NQR a (or_intror Ha)) as [Nq Ua]. destruct (HSH a Ha) as [Hh [b Hb]]. split; [img_try (img_exact (MON5 _ Hh))|]. exists b. rewrite FRz; [img_try (img_exact Hb) | img_try (rewrite Ua; img_exact Nq)].
- pose proof SH_ok as (_ & _ & OK2). img_apply Forall_forall. intros r Hr a Ha. pose proof (proj1 (Forall_forall _ _) OK2 r Hr) as RO.
assert (PL : (mb + 6144 <= a < mb + MSv) \/ (SMv <= a < SMv + MSv / 8)) by (img_try (unfold run_ok in RO; clear - RO Ha MZ; zlia)).
destruct (NQR a PL) as [Nq Ua]. unfold w64. rewrite FRz by (img_try (rewrite Ua; img_exact Nq)). img_exact (proj1 (Forall_forall _ _) HRs r Hr a Ha).
- img_exact (RQ mem _ FRz HR0).
- intros a Hq. pose proof (proj1 (EQR a) Hq) as Ra.
assert (Ua : bv_unsigned (Z_to_bv 64 a) = a) by (img_try (img_apply unsigned_lit_small; clear - Ra F9 F10 Q5 E1 MZ; ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kPtrArrayResv in *; try unfold Qb in *; zlia)).
split; [img_try (img_apply VIS5; rewrite Ua; img_exact Ra)|]. img_apply zfill_in. rewrite UQS, Un, Ua. img_exact Ra.
Qed.
Local Ltac s_runS HR tbl tblok stop ss' HX HP :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let st := img_ev (snd (sym_run_toN_sh tfxsegs tbl FUEL stop ss)) in
eapply SRr_bind;
[ img_try (eapply (at_S_runS Wx tbl tblok stop md X P ss ss' st W' c' HR);
[ (img_case; vm_compute); img_refl | img_exact I | img_exact HX | (img_case; vm_compute); img_refl | img_exact HP | (img_case; vm_compute); img_refl ])
| img_try (clear HR; let W2 := fresh "W" in let c2 := fresh "c" in intros W2 c2 _ HR) ] end.
Definition RZF (R : (word -> option byte) -> Prop) (m : word -> option byte) : Prop := R m /\ ZQF Wy m.
Definition RZ (R : (word -> option byte) -> Prop) (m : word -> option byte) : Prop := R m /\ ZQ Wy m.
Lemma ZQF_rstable : idx = res -> rstable (ZQF Wy).
Proof.
intros Heq. pose proof (QR_facts Heq) as (E1 & _ & _ & F9 & Q5 & F10 & EQ).
pose proof map_facts as (M1 & M2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _). pose proof map_zoneN as MZ. destruct Hmap_apart as (_ & _ & _ & MQ & _). unfold zdisjoint in MQ. cbn [fst snd] in MQ.
assert (U64 : forall a, QR a -> bv_unsigned (Z_to_bv 64 a) = a).
{ intros a Ha. pose proof (proj1 (EQ a) Ha) as Ra. img_apply unsigned_lit_small. clear - Ra F9 F10 Q5 E1 MZ; ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kPtrArrayResv in *; try unfold Qb in *; zlia. }
split.
- intros m m' FR H a Ha. destruct (H a Ha) as [H1 H2]. split; [img_try (img_exact H1)|]. rewrite FR; [img_try (img_exact H2)|]. rewrite (U64 a Ha).
pose proof (proj1 (EQ a) Ha) as Ra. intros Hw. destruct Hw as [Hw|Hw].
+ destruct (Z_lt_le_dec a (QSv + 8)) as [Hl|Hg].
* img_exact (QS_not_WIN1R a ltac:(img_try (clear - Ra Hl MZ; zlia)) (or_introl Hw)).
* img_exact (QR_not_WIN1T Heq a Ha ltac:(img_try (clear - Hg MZ; zlia)) (or_introl Hw)).
+ pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & _). clear - Hw Ra MQ Q5 F9 Z8 MZ. unfold kPtrArrayResv, MALLOC_MAX in *. try unfold Qb in *. zlia.
- intros m m' d len Hp FR H a Ha. destruct (H a Ha) as [H1 H2]. split; [img_try (img_exact H1)|]. rewrite FR; [img_try (img_exact H2)|]. rewrite (U64 a Ha).
pose proof (proj1 (EQ a) Ha) as Ra. clear - Hp Ra MQ F9 F10 Q5 M1 M2 SM1 SM2 E1 Heq MZ. ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kPtrArrayResv, kHighShadowBeg, kHighShadowEnd in *. try unfold Qb in *. zlia.
Qed.
Local Ltac s_runR HR tbl tblok stop ss' HX HP :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let st := img_ev (snd (sym_run_toN_sh tfxsegs tbl FUEL stop ss)) in
eapply SRr_bind;
[ img_try (eapply (at_S_runR Wx tbl tblok stop md X P ss ss' st W' c' HR);
[ (img_case; vm_compute); img_refl | img_exact I | img_exact HX | (img_case; vm_compute); img_refl | img_exact HP | (img_case; vm_compute); img_refl ])
| img_try (clear HR; let W2 := fresh "W" in let c2 := fresh "c" in intros W2 c2 _ HR) ] end.
Lemma segV : forall (R : (word -> option byte) -> Prop), rstable R -> idx = res ->
forall c, at_S Wy md1 (fun a => WIN a \/ QR a) (PSR Wy SH2 (RZF R)) S_VG Wy c ->
SRr tfxsegs Wy c (at_S Wy md1 (fun a => WIN a \/ QR a) (PSR Wy SH2 (RZ R)) S_YJ).
Proof.
intros R RS Heq c HR. pose proof SH_ok as (OK0 & OK1 & OK2). pose proof (rstable_and _ _ RS (ZQF_rstable Heq)) as RS2.
pose proof (PSR_stable Wy SH2 (RZF R) OK2 RS2) as HP2.
assert (HX : forall a, WIN1R a -> WIN a \/ QR a) by (img_try (intros a Ha; left; img_exact (WIN1R_WIN a Ha))).
pose proof high_facts as (_ & _ & _ & _ & _ & _ & _ & _ & F9 & F10 & _). pose proof Hidx as HI. pose proof Hres as [HRS _].
ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kPtrArrayResv in F9, F10. unfold kMaxNumChunks in HI, HRS.
pose proof (QR_facts Heq) as (E1 & _ & _ & _ & Q5 & _ & EQR).
s_runR HR tfxtbl_rtC tfxtbl_rtC_ok (0x366f0 + D_150) S_V2 HX HP2.
s_runR HR tfxtbl_rtA tfxtbl_rtA_ok (0x3650c + D_150) S_V3 HX HP2.
s_pin HR (12%bv : bv 5) (SOff aQS 0).
{ clear - HI F9 F10. pin_zevS. rewrite EaQS, EaQ, EaNCH. unfold w64. unfold QSv in *. rewrite !unsigned_lit_small by (img_try (try unfold Qb in *; zlia)).
zcanon_simp. land_lits. rewrite Z.shiftl_mul_pow2 by zlia. img_change (2 ^ 3) with 8. zcanon_simp. try unfold Qb in *. zlia. }
lazymatch type of HR with at_S _ _ ?X0 _ ?ss _ _ =>
let rs1 := img_ev (setchunks (TFX_INST + o_sec_reserved) [YQ0b.mkChunk (TFX_INST + o_sec_reserved) (CVal 8 RES2T)] (ss_mem ss)) in
apply (at_S_setchunks Wy md1 X0 _ ss _ _ (TFX_INST + o_sec_reserved) [YQ0b.mkChunk (TFX_INST + o_sec_reserved) (CVal 8 RES2T)]) in HR;
[ img_try (img_change (setchunks (TFX_INST + o_sec_reserved) [YQ0b.mkChunk (TFX_INST + o_sec_reserved) (CVal 8 RES2T)] (ss_mem ss)) with rs1 in HR; cbn [ss_pc ss_regs ss_resv ss_facts] in HR) | img_try ((img_case; vm_compute); img_refl) | ] end.
2:{ intros E' m HE _ r Hr Hb Hl RO.
lazymatch type of Hr with In _ ?l =>
pose proof (proj1 (forallb_forall _ _) (ltac:(img_eqrefl) : forallb (fun r => negb (match YQ0b.r_base r with None => Z.eqb (YQ0b.r_lo r) (TFX_INST + o_sec_reserved) | Some _ => false end)
|| existsb (fun c => chunk_eqb c (YQ0b.mkChunk (TFX_INST + o_sec_reserved) (CVal 8 (SOff aRES 16384)))) (YQ0b.r_chunks r)) l = true) r Hr) as CK end.
cbn beta in CK. rewrite Hb, Hl, Z.eqb_refl in CK. cbn [negb orb] in CK.
destruct RO as (_ & _ & _ & RC). img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
apply existsb_exists in CK as (k0 & Hk0 & CK). apply chunk_eqb_eq in CK. (subst k0; cbv beta).
pose proof (proj1 (Forall_forall _ _) RC _ Hk0) as RC0. rewrite Hb in RC0. img_apply (chunk_ok_CVal_eqv E' _ _ _ _ RES2T (SOff aRES 16384)); [|img_try (img_exact RC0)].
img_apply (sv_denot_eq_of_U E' _ _ HE); [img_try ((img_case; vm_compute); img_refl) | img_try ((img_case; vm_compute); img_refl) | img_try (img_exact (RES2T_eq Heq))]. }
lazymatch type of HR with at_S _ _ ?X0 _ ?ss _ _ =>
let rs := img_ev (trimscratch (-2416) (ss_mem ss)) in
apply (at_S_submem Wy md1 X0 _ ss _ _ rs) in HR; [| img_try ((img_case; vm_compute); img_refl) | img_try ((img_case; vm_compute); img_refl)] end.
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
pose proof (at_S_forget Wx md X P ss W' c' sJY [1; 15; 17; 20]%bv HR ltac:(img_try (unfold sHAV, sJY; zlia)) eq_refl
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))) as HR2; clear HR; rename HR2 into HR end.
s_noconds HR.
lazymatch type of HR with at_S _ _ ?X0 _ _ _ _ =>
apply (at_S_addreg Wy md1 X0 _ _ _ _ R_qs) in HR; [| img_refl |] end.
2:{ intros E' m HE MEQ PRS [HP [HQ HZ]] HM. pose proof (proj1 HE) as HEn.
assert (BQ : base_val E' (Some aQS) = QSv).
{ cbn [base_val]. unfold aQS. rewrite (HEn 52%nat ltac:(img_try (unfold sHAV; zlia))), EaQS. unfold w64. img_apply unsigned_lit_small. clear - HI F9 F10. unfold QSv in *. try unfold Qb in *. zlia. }
split.
- unfold region_ok, R_qs. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks]. rewrite BQ.
split; [img_try (clear - HI F9; unfold QSv in *; try unfold Qb in *; zlia)|]. split; [img_try (clear - HI F9 F10; unfold QSv in *; try unfold Qb in *; zlia)|]. split; [|img_try (img_apply Forall_nil)].
intros o Ho. img_apply apresent_writable_off; [img_try (off_by ltac:(clear - Ho HI F9 F10; unfold zone3, TFX_IMG_LO, kLowShadowBeg, QSv, TFX_IMG_END in *; try unfold Qb in *; zlia)) |].
destruct (HZ (QSv + o) ltac:(img_try (img_apply (proj2 (EQR _)); clear - Ho; zlia))) as [Hh Hz]. split; [img_try (img_exact Hh) | img_try (exists (Z_to_bv 8 0); img_exact Hz)].
- intros r2 Hr2. unfold extent_disjoint, R_qs. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi]. rewrite !BQ.
lazymatch type of Hr2 with In _ ?l =>
pose proof (proj1 (forallb_forall _ _) (ltac:(img_eqrefl) : forallb (fun r => skel_okb false (skel r) && negb (obase_eqb (YQ0b.r_base r) (Some aQS))) l = true) r2 Hr2) as CK end.
cbn beta in CK. apply andb_prop in CK as [CK1 CK2].
assert (NB : YQ0b.r_base r2 <> Some aQS) by (img_try (intros Eq; rewrite Eq in CK2; discriminate CK2)).
pose proof (skel_apart_QS E' false r2 HE CK1 NB) as AP. clear - AP. zlia. }
replace (addreg R_qs _) with S_YJ in HR by (img_try (rewrite <- S_VY_join; (img_case; vm_compute); img_refl)).
img_apply SRr_ret. eapply at_S_weaken; [img_try (img_exact HR) | img_try (intros a Ha; img_exact Ha) | img_try (intros m [HP [HQ HZ]]; img_exact (conj HP (conj HQ (ZQ_of_ZQF Wy m HZ))))].
Qed.
End h.
End g.
