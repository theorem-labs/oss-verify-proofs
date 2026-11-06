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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF64 YF3v YF3w YF3x YF41 YF6z YF0a YF7f YF7o YF7p YF7q YF7a.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac img_fact_head C := lazymatch C with @D_m8 => idtac | @D_8 => idtac | @D_m9 => idtac | @D_10 => idtac | @D_18 => idtac | @D_20 => idtac | @D_30 => idtac | @D_m3c => idtac | @D_m3e => idtac | @D_m40 => idtac | @D_4e => idtac | @D_50 => idtac | @D_6c => idtac | @D_a0 => idtac | @D_150 => idtac | @D_200 => idtac | @D_218 => idtac | @D_21c => idtac | @D_21e => idtac | @D_220 => idtac | @D_270 => idtac | @D_274 => idtac | @D_280 => idtac | @D_2b4 => idtac | @D_2c4 => idtac | @D_2cc => idtac | @D_m3ac => idtac | @D_430 => idtac | @D_440 => idtac | @D_a2c => idtac | @D_1000 => idtac | @D_104c => idtac | @D_10c0 => idtac | @D_10e0 => idtac | @D_10e8 => idtac | @D_10ec => idtac | @D_10f0 => idtac | @D_1100 => idtac | @D_54c0 => idtac | @D_5680 => idtac | @D_m27b919177701d40 => idtac | @D_m10c55b69b38ab717 => idtac | @D_m261b33dfb1afee1d => idtac | @D_332fe4d8b3da5a5b => idtac | @D_558ab28b2f16c771 => idtac | @D_m5c6cf5c3c23d561f => idtac | @D_ma7775317fd2cb971 => idtac | @D_mcf6373b41df84414 => idtac | @tfxguard_start => idtac | @tfxmusl_text_start => idtac | @tfx_A_musl_memchr => idtac | @tfx_A_musl_memcmp => idtac | @tfx_A_musl_memcpy => idtac | @tfx_A_musl_memset => idtac | @tfx_A_musl_strnlen => idtac | @TFX_DEPOT => idtac | @TFX_ERRNO => idtac | @TFX_IAL_FLAG => idtac | @TFX_IAL_HI => idtac | @TFX_IAL_LO => idtac | @TFX_IAL_W => idtac | @TFX_INST => idtac | @TFX_MAIN => idtac | @TFX_MAIN_RA => idtac | @TFX_OOM => idtac | @TFX_STORE => idtac | @TFX_TP => idtac | @TFX_TSD => idtac end.
Ltac img_fact_used C := first [ lazymatch goal with |- context [C] => idtac end | match goal with H1 : context [C], H2 : context [C] |- _ => idtac end ].
Ltac img_prune_facts := repeat match goal with H : ?C ?k = _ |- _ => lazymatch type of k with img => img_fact_head C; tryif img_fact_used C then fail else clear H end end.
Ltac img_facts_full := lazymatch goal with k : img |- _ => let F := fresh "IMGF" in pose proof (P_facts k) as F end.
Ltac img_facts ::= lazymatch goal with k : img |- _ => let F := fresh "IMGF" in pose proof (P_facts k) as F; decompose [and] F; clear F; img_prune_facts end.
Ltac img_lia ::=
first [ (img_goal_has_k; first [ (img_facts; lia) | (img_facts_full; lia) ])
| lia
| (img_inst; lia)
| (try img_inst;
first [ (img_local; img_local_unfold; img_unfold_all; lia)
| (img_arith_rel; first [ (img_facts; lia) | (img_facts_full; lia)
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
Local Abbreviation AR7 f := (f idx res LY IMG Hidx Hres) (only parsing).
Local Abbreviation high_facts := (AR7 (AR1 (@YF7f.high_facts _))).
Local Abbreviation stack_ivs := (@YF7f.stack_ivs _ ly regs0 idx res LY Hsp Hidx Hres).
Local Abbreviation HCX := (@YF7f.HCX _ ly LY).
Hypothesis Hpres0 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem0 a.
Hypothesis Hmap : mb mod 4096 = 0 /\ mzone mb MSv.
Hypothesis Hmap_apart :
zdisjoint (mb, MSv) (T, kThreadObjSize) /\ zdisjoint (mb, MSv) (ly_C ly, kCtxMapSize) /\
zdisjoint (mb, MSv) (ly_prim ly, kPrimResvSize) /\ zdisjoint (mb, MSv) (Qb, kPtrArrayResv) /\
zdisjoint (mb, MSv) (ly_NB ly, kNodesBlockSize) /\ zdisjoint (mb, MSv) (ly_SB ly, kStoreBlockSize) /\
zdisjoint (mb, MSv) (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly).
Local Abbreviation AR4 f := (AR1 f n idx res mb) (only parsing).
Local Abbreviation ARa f := (f Nrange Hidx Hres) (only parsing).
Local Abbreviation map_facts := ((ARa (AR4 (@YF7f.map_facts _))) Hmap).
Local Abbreviation map_zone := ((AR4 (@YF7f.map_zone _)) Nrange Hidx Hmap).
Local Abbreviation map_zoneN := ((ARa (AR4 (@YF7f.map_zoneN _))) Hmap).
Local Abbreviation map_in_band := ((AR4 (@YF7f.map_in_band _)) Nrange Hidx Hmap).
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
Local Abbreviation WIN1P_WINP := ((AR4 (@YF7f.WIN1P_WINP)) Hidx).
Local Abbreviation WIN1_WIN := ((AR4 (@YF7f.WIN1_WIN)) Hidx).
Local Abbreviation WIN1P_WIN1 := ((AR1 (@YF7f.WIN1P_WIN1)) n idx mb).
Local Abbreviation LGv_range := (@YF7f.LGv_range n Nrange).
Local Abbreviation BSLv_range := ((AR4 (@YF7f.BSLv_range)) Nrange Hidx).
Local Abbreviation WSKELP := (@YF7f.WSKELP imgk).
Local Abbreviation WSKEL1P := (@YF7f.WSKEL1P imgk).
Local Abbreviation WMAP := (@YF7f.WMAP).
Local Abbreviation WSKEL := (@YF7f.WSKEL imgk).
Local Abbreviation WSKEL1 := (@YF7f.WSKEL1 imgk).
Local Abbreviation win_sub := (@YF7f.win_sub).
Local Abbreviation ARb f := (f idx res mb) (only parsing).
Local Abbreviation win_sub_sound := ((ARb (@YF7f.win_sub_sound ly regs0)) Hidx Hres).
Local Abbreviation in_win := (@YF7f.in_win).
Local Abbreviation AR3 f := (AR0 f LY IMG Nrange Hidx Hres) (only parsing).
Local Abbreviation WSKELP_WINP := (AR3 (AR1 (@YF7f.WSKELP_WINP _))).
Local Abbreviation WSKEL1P_WIN1P := (AR3 (AR1 (@YF7f.WSKEL1P_WIN1P _))).
Local Abbreviation WMAP_WINM := ((AR3 (AR1 (@YF7f.WMAP_WINM _))) Hmap).
Local Abbreviation WSKEL_WIN := ((AR3 (AR1 (@YF7f.WSKEL_WIN _))) Hmap).
Local Abbreviation WSKEL1_WIN1 := ((AR3 (AR1 (@YF7f.WSKEL1_WIN1 _))) Hmap).
Local Abbreviation windows_in := ((ARb (@YF7f.windows_in ly regs0)) Hidx Hres).
Local Abbreviation windows_WINP := (AR3 (AR1 (@YF7f.windows_WINP _))).
Local Abbreviation windows_WIN1P := (AR3 (AR1 (@YF7f.windows_WIN1P _))).
Local Abbreviation windows_WIN := ((AR3 (AR1 (@YF7f.windows_WIN _))) Hmap).
Local Abbreviation windows_WIN1 := ((AR3 (AR1 (@YF7f.windows_WIN1 _))) Hmap).
Local Abbreviation frame_WIN1P := (AR3 (AR1 (@YF7f.frame_WIN1P _))).
Local Abbreviation frame_WIN1 := ((AR3 (AR1 (@YF7f.frame_WIN1 _))) Hmap).
Local Abbreviation AR2 f := (f LY IMG Hsp Nrange Hidx Hres) (only parsing).
Local Abbreviation WINP_not_high := (AR2 (AR4 (@YF7f.WINP_not_high _))).
Local Abbreviation WIN_not_high := ((AR2 (AR4 (@YF7f.WIN_not_high _))) Hmap).
Variables (mat0 : list word).
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 (0x53108 + D_2c4)) mem0 (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis U1 : tfx_unwind_spec.
Local Abbreviation all_disjoint_of_forall := (@YF7f.all_disjoint_of_forall).
Local Abbreviation img_rw_writable := ((ARb (AR1 (@YF7f.img_rw_writable))) Hidx).
Local Abbreviation AR9 f := (f imgk W ly) (only parsing).
Local Abbreviation kept_of_frame := ((ARb ((AR9 (@YF7f.kept_of_frame)) regs0)) Hidx).
Local Abbreviation SKEL_TAIL := (@YF7f.SKEL_TAIL imgk).
Local Abbreviation blocks_facts := (@YF7f.blocks_facts _ imgk ly LY IMG).
Local Abbreviation off_T := (AR7 (AR1 (@YF7f.off_T _))).
Local Abbreviation off_C := (AR7 (AR1 (@YF7f.off_C _))).
Local Abbreviation off_Q := (AR7 (AR1 (@YF7f.off_Q _))).
Local Abbreviation off_NB := (@YF7f.off_NB _ imgk ly LY IMG).
Local Abbreviation off_SB := (@YF7f.off_SB _ imgk ly LY IMG).
Local Abbreviation off_shadow := ((ARb (AR1 (@YF7f.off_shadow))) Hidx).
Ltac off_by tac :=
first [ img_apply off_img_high; tac | img_apply off_T; tac | img_apply off_C; tac | img_apply off_Q; tac | img_apply off_NB; tac | img_apply off_SB; tac
| img_apply map_off_img; tac | img_apply off_shadow; tac
| unfold off_img; unfold TFX_IMG_LO; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; tac ].
Local Abbreviation DZONE := (@YF7f.DZONE imgk ly).
Variable DPOST : Z -> (word -> option byte) -> Prop.
Local Abbreviation DZONE_disj := ((AR2 (AR4 (@YF7f.DZONE_disj _))) Hmap Hmap_apart).
Local Abbreviation RFACTS := (AR1 (@YF7f.RFACTS)).
Local Abbreviation zone_lit := ((AR1 (@YF7f.zone_lit _)) LY IMG Hsp).
Local Abbreviation zone_irw := ((AR1 (@YF7f.zone_irw _)) LY IMG Hsp).
Local Abbreviation zone_T := ((AR1 (@YF7f.zone_T _)) idx res LY IMG Hsp Hidx Hres).
Local Abbreviation zone_C := ((AR1 (@YF7f.zone_C _)) idx res LY IMG Hsp Hidx Hres).
Local Abbreviation tail_ext_ok := (AR2 (AR0 (AR1 (@YF7f.tail_ext_ok _)))).
Local Abbreviation RFACTS_map := ((ARa ((AR4 (@YF7f.RFACTS_map _)) LY IMG)) Hmap Hmap_apart).
Local Abbreviation AR5 f := (f imgk W ly regs0 mem0) (only parsing).
Local Abbreviation at_ST := (AR0 ((AR5 (@YF7f.at_ST _)) md0)).
Local Abbreviation memset_stretch := ((ARa ((ARb ((AR5 (@YF7f.memset_stretch _ _)) md0 n)) Hsp)) Hmap Hmap_apart mat0 DPOST).
Ltac clearM := try clear DPOST; try clear Hmap_apart; try clear Hmap.
Local Abbreviation AR8 f := (AR1 f mem0) (only parsing).
Local Abbreviation at_S := (AR0 (AR8 (@YF7f.at_S _))).
Local Abbreviation at_N := (AR0 (AR8 (@YF7f.at_N _))).
Local Abbreviation at_RETS := ((AR8 (@YF7f.at_RETS _)) ch).
Local Abbreviation pstable := (@YF7f.pstable).
Local Abbreviation stack_shaped := (@YF7f.stack_shaped).
Local Abbreviation window_present := ((AR1 (@YF7f.window_present)) idx res Hidx).
Local Abbreviation stack_present_of := ((AR0 (AR1 (@YF7f.stack_present_of _))) LY Hsp Hidx).
Local Abbreviation mid_not_WIN1P := (AR2 (AR4 (@YF7f.mid_not_WIN1P _))).
Local Abbreviation mid_not_WIN1 := ((AR2 (AR4 (@YF7f.mid_not_WIN1 _))) Hmap).
Local Abbreviation wins_ok := (@YF7f.wins_ok).
Local Abbreviation at_S_run_gen := ((AR0 (AR8 (@YF7f.at_S_run_gen _ _))) LY Hsp Hidx).
Local Abbreviation at_S_run_ecall_gen := ((AR0 (AR8 (@YF7f.at_S_run_ecall_gen _ _))) LY Hsp Hidx).
Local Abbreviation at_S_runP := (AR2 (AR0 (AR8 (@YF7f.at_S_runP _ _)))).
Local Abbreviation at_S_runM := ((AR2 (AR0 (AR8 (@YF7f.at_S_runM _ _)))) Hmap).
Local Abbreviation at_S_run_ecallP := (AR2 (AR0 (AR8 (@YF7f.at_S_run_ecallP _ _)))).
Local Abbreviation at_S_run_ecallM := ((AR2 (AR0 (AR8 (@YF7f.at_S_run_ecallM _ _)))) Hmap).
Local Abbreviation at_S_pin := (AR0 (AR8 (@YF7f.at_S_pin _))).
Local Abbreviation at_S_arm := (AR0 (AR8 (@YF7f.at_S_arm _))).
Local Abbreviation at_S_forget := (AR0 (AR8 (@YF7f.at_S_forget _))).
Local Abbreviation at_S_noconds := (AR0 (AR8 (@YF7f.at_S_noconds _))).
Local Abbreviation at_S_weaken := (AR0 (AR8 (@YF7f.at_S_weaken _))).
Local Abbreviation at_S_facts := (AR0 (AR8 (@YF7f.at_S_facts _))).
Local Abbreviation at_S_strengthen := (AR0 (AR8 (@YF7f.at_S_strengthen _))).
Local Abbreviation at_S_eq := (AR0 (AR8 (@YF7f.at_S_eq _))).
Local Abbreviation at_S_open := (AR0 (AR8 (@YF7f.at_S_open _))).
Local Abbreviation CSAVEDS := (@YF7f.CSAVEDS).
Local Abbreviation sv_denot_SOff0 := (@YF7f.sv_denot_SOff0).
Local Abbreviation at_S_ret := (ARa ((AR0 (AR8 (@YF7f.at_S_ret _))) Htp Hra Hsp)).
Local Abbreviation kept_of_frame2 := ((AR1 (@YF7f.kept_of_frame2)) idx res Hidx).
Local Abbreviation at_N_cont := ((AR0 (AR8 (@YF7f.at_N_cont _ _))) LY Hsp Hidx).
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
Local Abbreviation junk_word := ((AR7 (AR5 (@YF7o.junk_word _))) DPOST B S HARm).
Local Abbreviation cell_sym := ((AR9 (@YF7o.cell_sym _)) mem0 B S TS HARm).
Local Abbreviation cell_lit := ((AR9 (@YF7o.cell_lit _)) mem0 B S TS HARm).
Local Abbreviation cell_state := ((AR9 (@YF7o.cell_state _)) mem0 B S HARm).
Local Abbreviation In_acells_sec := (@YF7o.In_acells_sec ly B S).
Local Abbreviation sec_vals := ((AR9 (@YF7o.sec_vals _)) mem0 idx res B S TS HARm Hidx_def Hres_def).
Local Abbreviation unwinding_val := ((AR9 (@YF7o.unwinding_val _)) mem0 B S HARm).
Local Abbreviation rw_writable := ((AR1 (@YF7o.rw_writable)) idx res Hidx DPOST S).
Local Abbreviation val_mem_mod8 := ((AR5 (@YF7o.val_mem_mod8)) idx res Hidx DPOST S).
Local Abbreviation chunk_lit := (AR0 (AR5 (@YF7o.chunk_lit))).
Local Abbreviation chunk_lit_at := (AR0 (AR5 (@YF7o.chunk_lit_at))).
Local Abbreviation chunk_atom := ((AR0 (AR5 (@YF7o.chunk_atom))) Hidx DPOST S).
Local Abbreviation AR6 f := (f DPOST B S TS HTSD HARm Hidx_def Hres_def Hj0 Hj1 Hj2 Hj3 Hj4 Hj5 Hj9 Hj6 Hj7 Hj8 Hi1 Hi2 Hi3) (only parsing).
Local Abbreviation SREG0_ok := (AR6 ((AR2 (AR0 (AR5 (@YF7p.SREG0_ok _)))) Hpres0)).
Local Abbreviation PAIRS_ok := ((AR2 (AR0 (AR5 (@YF7q.PAIRS_ok _)))) DPOST S).
Local Abbreviation FACTS_ok := ((ARa ((AR0 (AR5 (@YF7q.FACTS_ok _))) LY IMG Hn Hsp)) DPOST S).
Local Abbreviation SEED_ok := (AR6 ((ARa ((AR0 (AR5 (@YF7q.SEED_ok _ _))) LY IMG Hn Hsp)) Hpres0)).
Local Abbreviation PBUF := ((AR9 (@YF7a.PBUF)) regs0 ch).
Local Abbreviation PBUF_stableP := (AR2 (ARb ((AR9 (@YF7a.PBUF_stableP _)) regs0 n ch))).
Local Abbreviation PBUF_stableM := ((AR2 (ARb ((AR9 (@YF7a.PBUF_stableM _)) regs0 n ch))) Hmap).
Local Abbreviation seg0 := (AR6 ((ARa ((AR0 ((AR5 (@YF7a.seg0 _ _)) md0)) LY IMG Hn Htp Hra4096 Hsp Hch)) Hpres0 mat0 U1)).
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
Definition appregs (ss : sstate) (rs' : smem) : sstate := mkSS (ss_pc ss) (ss_regs ss) (ss_mem ss ++ rs') (ss_resv ss) (ss_facts ss).
Lemma st_ok_appregs : forall (E' : env) ss (ms : machine_state) rs',
st_ok tfxsegs E' ss ms -> regions_wf rs' = true -> Forall (region_ok tfxsegs E' (ms_mem ms)) rs' -> pairwise_disjoint E' rs' ->
(forall r1 r2, In r1 (ss_mem ss) -> In r2 rs' -> extent_disjoint E' r1 r2) ->
st_ok tfxsegs E' (appregs ss rs') ms.
Proof.
clearP. intros E' ss ms rs' (H1 & H2 & H3 & H4 & H5 & H6 & H7 & (Hwf & Hok & Hpd) & H9) Hwf' Hok' Hpd' Hx.
unfold st_ok, appregs; cbn. repeat (split; [img_try (assumption)|]). split; [|img_try (img_exact H9)]. split; [| img_try (split)].
- rewrite YQ0a.regions_wf_app, Hwf, Hwf'. img_refl.
- img_apply Forall_app. split; assumption.
- img_apply YQ0a.pairwise_disjoint_app; assumption.
Qed.
Lemma at_S_app : forall (Wx : world tfxsegs) md X P ss W' c' rs',
at_S Wx md X P ss W' c' -> regions_wf rs' = true ->
(forall (E' : env) (m : word -> option byte),
env_agree sHAV E0 E' -> (forall x : word, ~ X (bv_unsigned x) -> m x = mem0 x) ->
(forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H Wx) m a) -> P m -> mem_ok tfxsegs E' (mrestrict (w_H Wx) m) (ss_mem ss) ->
Forall (region_ok tfxsegs E' (mrestrict (w_H Wx) m)) rs' /\ pairwise_disjoint E' rs' /\
(forall r1 r2, In r1 (ss_mem ss) -> In r2 rs' -> extent_disjoint E' r1 r2)) ->
at_S Wx md X P (appregs ss rs') W' c'.
Proof.
clearP. intros Wx md X P ss W' c' rs' HR Hwf HOK. destruct HR as (-> & ms & mat & E' & -> & HE & HS & MEQ & PRS & HPm).
split; [img_refl|]. exists ms, mat, E'. split; [img_refl|]. split; [img_try (img_exact HE)|]. split; [|img_try (img_exact (conj MEQ (conj PRS HPm)))].
pose proof (st_ok_mem_ok tfxsegs E' ss _ HS) as HM.
destruct (HOK E' (ms_mem ms) HE MEQ PRS HPm HM) as (Hok & Hpd & Hx).
img_exact (st_ok_appregs E' ss _ rs' HS Hwf Hok Hpd Hx).
Qed.
Definition WIN1N (a : Z) : Prop := WIN1P a \/ (TFX_OOM <= a < TFX_OOM + 1) \/ (TFX_ERRNO <= a < TFX_ERRNO + 4).
Definition WINPN (a : Z) : Prop := WINP a \/ (TFX_OOM <= a < TFX_OOM + 1) \/ (TFX_ERRNO <= a < TFX_ERRNO + 4).
Definition WSKEL1N {imgk : img} : list (option nat * Z * Z) := WSKEL1P ++ [(None, TFX_OOM, TFX_OOM + 1); (None, TFX_ERRNO, TFX_ERRNO + 4)].
Lemma WIN1N_WINPN : forall a, WIN1N a -> WINPN a.
Proof. clearP. intros a [H|H]; [img_try (left; img_exact (WIN1P_WINP a H)) | img_try (right; img_exact H)]. Qed.
Lemma windows_WIN1N : forall (E : env) rs a,
(forall k, (k < sHAV)%nat -> ew E k = ew E0 k) -> wins_ok WSKEL1N rs = true -> in_wrange E rs a -> WIN1N a.
Proof.
clearP. intros E rs a HE. img_apply windows_in. intros t x Ht Hx. unfold WSKEL1N in Ht. apply in_app_iff in Ht as [Ht|Ht].
- left. img_exact (WSKEL1P_WIN1P E x t HE Ht Hx).
- right. unfold in_win in Hx. destruct Ht as [<-|[<-|[]]]; cbn [fst snd base_val] in Hx; [img_try (left) | img_try (right)]; img_exact Hx.
Qed.
Lemma mid_not_WIN1N : forall a, sp0 - IFRAME <= a < sp0 - 64 -> ~ WIN1N a.
Proof.
clearP. intros a Ha [Hw|Hw]; [img_try (img_exact (mid_not_WIN1P a Ha Hw))|].
pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7). destruct Hsp as (S1 & _). clear - Ha Hw T7 S1.
unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_OOM, TFX_ERRNO, kHighMemBeg, ASTACK, IFRAME in *. zlia.
Qed.
Lemma at_S_runN : forall (Wx : world tfxsegs) tbl (tblok : table_ok tfxsegs tbl) stop md X P ss ss' st W' c',
at_S Wx md X P ss W' c' ->
sym_run_toN_sh tfxsegs tbl FUEL stop ss = (ss', st) -> match st with RS_ecall => False | _ => True end ->
(forall a, WIN1N a -> X a) -> wins_ok WSKEL1N (ss_mem ss) = true -> pstable WIN1N P -> stack_shaped ss' = true ->
SRr tfxsegs W' c' (at_S Wx md X P ss').
Proof. clearP. img_exact (at_S_run_gen WSKEL1N WIN1N windows_WIN1N mid_not_WIN1N). Qed.
Lemma PBUF_stableN : pstable WIN1N PBUF.
Proof.
clearP. intros m m' FR HB i Hi. pose proof tr_length as LEN. pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7). destruct Hsp as (S1 & _).
pose proof (u64_range (getr regs0 2)) as U2.
eapply val_mem_frame; [|img_try (img_exact (HB i Hi))]. intros k Hk. img_apply FR.
rewrite unsigned_lit_small by (img_try (clear - Hi Hk LEN S1 T7 U2; numconst; unfold IFRAME, sp0 in *; zlia)).
img_apply mid_not_WIN1N. clear - Hi Hk LEN. unfold IFRAME. zlia.
Qed.
Lemma at_S_val : forall (Wx : world tfxsegs) md X P ss W' c' (i j : nat) (a : Z) (nn : BinNums.N) (v : Z),
at_S Wx md X P ss W' c' ->
(forall (E' : env) ms, env_agree sHAV E0 E' -> st_ok tfxsegs E' ss (restrict (w_H Wx) ms) -> val_mem tfxsegs (mrestrict (w_H Wx) (ms_mem ms)) a (N.to_nat nn) v) ->
at_S Wx md X (fun m => P m /\ val_mem tfxsegs (mrestrict (w_H Wx) m) a (N.to_nat nn) v) ss W' c'.
Proof. clearP. intros Wx md X P ss W' c' i j a nn v HR HV. img_exact (at_S_facts Wx md X P _ ss W' c' HR HV). Qed.
Lemma memset_stretchW : forall (Wx : world tfxsegs) (k : nat) (E : env) ss ms md (d len retpc : Z) (Q : world tfxsegs -> config -> Prop),
st_ok tfxsegs E ss (restrict (w_H Wx) ms) -> ss_resv ss = None -> ss_pc ss = tfx_A_musl_memset ->
ss_atoms_lt k ss = true -> no_cdata (ss_mem ss) = true ->
getr (ms_regs ms) 10 = Z_to_bv 64 d -> getr (ms_regs ms) 12 = Z_to_bv 64 len -> getr (ms_regs ms) 1 = Z_to_bv 64 retpc ->
0 <= len -> TFX_IMG_END <= d -> d + len < 2 ^ 64 -> retpc mod 4 = 0 -> 0 <= retpc < 2 ^ 64 ->
(forall a, d <= a < d + len -> apresent (w_H Wx) (ms_mem ms) a) ->
(forall r, In r (ss_mem ss) -> base_val E (YQ0b.r_base r) + YQ0b.r_hi r <= d \/ d + len <= base_val E (YQ0b.r_base r) + YQ0b.r_lo r
\/ YQ0b.r_hi r <= YQ0b.r_lo r) ->
(forall r a, In r (ss_mem ss) -> base_val E (YQ0b.r_base r) + YQ0b.r_lo r <= a < base_val E (YQ0b.r_base r) + YQ0b.r_hi r -> 0 <= a < 2 ^ 64) ->
(forall regs' mem' mat',
st_ok tfxsegs (havoc E k (map (getr regs') [11; 12; 13; 14; 15; 16]%bv))
(ss_after_stretch ss (ss_mem ss) k [11; 12; 13; 14; 15; 16]%bv retpc)
(restrict (w_H Wx) (mkst regs' (Z_to_bv 64 retpc) mem' (seg_rom tfxsegs))) ->
getr regs' 10 = Z_to_bv 64 d ->
(forall x : word, ~ (d <= bv_unsigned x < d + len) -> mem' x = ms_mem ms x) ->
(forall a, apresent (w_H Wx) (ms_mem ms) a -> apresent (w_H Wx) mem' a) ->
(forall x : word, d <= bv_unsigned x < d + len -> mem' x = Some (Z_to_bv 8 (bv_unsigned (getr (ms_regs ms) 11) mod 256))) ->
SRr tfxsegs Wx (mkCfg (mkst regs' (Z_to_bv 64 retpc) mem' (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
SRr tfxsegs Wx (mkCfg ms md) Q.
Proof.
clearP. intros Wx k E ss ms md d len retpc Q HS Hrv Hpc Hat Hnc H10 H12 H1 Hlen Hd Hdl Hrpc Hrpc' Hpres Hext Hext64 HK.
pose proof Hwx_tfa as Hwx.
pose proof (st_ok_restrict_mkst tfxsegs (w_H Wx) E _ _ HS Hrv) as Hshape. rewrite Hpc in Hshape. rewrite Hshape.
set (mr := mrestrict (w_H Wx) (ms_mem ms)).
assert (SOK : store_ok tfxsegs mr (Z_to_bv 64 d) (Z.to_nat len) = true).
{ img_apply store_ok_of_all; rewrite unsigned_lit_small by (img_try (unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END in *; zlia)); [img_try (zlia)|]. intros x Hx.
pose proof (apresent_writable (w_H Wx) (ms_mem ms) (bv_unsigned x) ltac:(img_try (pose proof (u64_range x); unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END in *; zlia)) (Hpres (bv_unsigned x) ltac:(img_try (zlia)))) as Hw.
unfold writable_at in Hw. rewrite Z_to_bv_bv_unsigned in Hw. img_exact Hw. }
destruct (tfx_memset (Z_to_bv 64 d) (getr (ms_regs ms) 11) (Z_to_bv 64 len) (Z.to_nat len) mr (seg_rom tfxsegs) (ms_regs ms)
H10 eq_refl H12 ltac:(img_try (rewrite unsigned_lit_small by (unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END in *; zlia); zlia)) SOK
ltac:(img_try (rewrite unsigned_lit_small by (unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END in *; zlia); zlia)))
as (regs' & Hms & H10' & Hfr).
set (bs := repeat (Z_to_bv 8 (bv_unsigned (getr (ms_regs ms) 11) mod 256)) (Z.to_nat len)) in Hms.
assert (Hlenbs : Z.of_nat (length bs) = len) by (img_try ((subst bs; cbv beta); rewrite repeat_length; zlia)).
eapply (SRr_msteps tfxsegs Hwx Wx _ _ md Q). { rewrite restrict_mkst_fx. img_exact Hms. }
intros model' Hsame Hcln. rewrite (same_but_materialized_wvb md model' Hsame).
rewrite H1. replace (v_jalr (Z_to_bv 64 retpc) 0) with (Z_to_bv 64 retpc).
2:{ unfold v_jalr, jalr_tgtZ. rewrite unsigned_lit_small by zlia. f_equal. rewrite Z.add_0_r.
img_change (-2) with (- 2 ^ 1). rewrite land_neg_pow2 by zlia. img_change (2 ^ 1) with 2.
replace (retpc mod 2) with 0; [img_try (zlia)|]. symmetry. img_apply Znumtheory.Zdivide_mod. img_apply (Z.divide_trans _ 4); [img_try (exists 2; img_refl)|].
img_apply Znumtheory.Zmod_divide; [img_try (zlia) | img_try (img_exact Hrpc)]. }
img_change (unrestrict (w_H Wx) (ms_mem ms) (mkst regs' (Z_to_bv 64 retpc) (wbytes mr (Z_to_bv 64 d) bs) (seg_rom tfxsegs)))
with (mkst regs' (Z_to_bv 64 retpc) (munrestrict (w_H Wx) (ms_mem ms) (wbytes mr (Z_to_bv 64 d) bs)) (seg_rom tfxsegs)).
set (m1 := wbytes mr (Z_to_bv 64 d) bs) in *. set (m1full := munrestrict (w_H Wx) (ms_mem ms) m1).
assert (Hm1 : mrestrict (w_H Wx) m1full = m1).
{ pose proof (f_equal ms_mem (restrict_unrestrict_clean (w_H Wx) (ms_mem ms) _ Hcln)) as Em. cbn [ms_mem restrict unrestrict mkst] in Em. img_exact Em. }
assert (FR1 : forall x : word, ~ (d <= bv_unsigned x < d + len) -> m1 x = mr x).
{ intros x Hx. (subst m1; cbv beta). destruct (Z_lt_le_dec (bv_unsigned x) d).
- img_apply wbytes_below; rewrite unsigned_lit_small by (img_try (unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END in *; zlia)); zlia.
- img_apply wbytes_above; rewrite unsigned_lit_small by (img_try (unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END in *; zlia)); zlia. }
assert (GR1 : mem_grows mr m1) by (img_try ((subst m1; cbv beta); img_apply wbytes_grows)).
img_apply (HK regs' m1full (m_vm_materialized model')).
- rewrite restrict_mkst_fx, Hm1.
unfold ss_atoms_lt in Hat. apply andb_prop in Hat as [Hat' Hrv']. apply andb_prop in Hat' as [Hat' HG]. apply andb_prop in Hat' as [Hr' Hm'].
img_apply (st_ok_after_stretch tfxsegs k E ss (restrict (w_H Wx) ms) regs' m1 (ss_mem ss) retpc [11; 12; 13; 14; 15; 16]%bv HS Hrv);
[ img_try (unfold ss_atoms_lt; rewrite Hr', Hm', HG, Hrv'; img_refl)
| img_try (img_exact (proj1 (st_ok_mem_ok tfxsegs E ss _ HS))) | img_try (img_exact Hnc) | img_try (img_exact Hm') | img_try (img_apply submem_refl) | img_refl | img_refl | | ].
+ intros r Hr. cbn [ms_regs restrict]. apply reg_in_false in Hr. cbn [In] in Hr.
destruct (base.decide (r = 10%bv)) as [->|N10]; [img_try (rewrite H10', H10; img_refl)|].
img_apply Hfr; intros ->; img_apply Hr; tauto.
+ img_apply Forall_forall. intros r Hr. cbn [ms_mem restrict]. fold mr. split.
* intros a Ha. unfold mbyte. rewrite (FR1 (Z_to_bv 64 a)); [img_refl|].
rewrite unsigned_lit_small by (img_try (img_exact (Hext64 r a Hr Ha))). destruct (Hext r Hr) as [X|[X|X]]; zlia.
* intros a Ha Hw. img_apply (writable_at_grows tfxsegs mr m1 a GR1 Hw).
- img_exact H10'.
- intros x Hx. (subst m1full; cbv beta). unfold munrestrict. destruct (w_H Wx x) eqn:Hh; [img_refl|].
rewrite (FR1 x Hx). (subst mr; cbv beta). unfold mrestrict. rewrite Hh. img_refl.
- intros a [Hh [b Hb]]. split; [img_try (img_exact Hh)|]. (subst m1full; cbv beta). unfold munrestrict. rewrite Hh.
assert (NN : m1 (Z_to_bv 64 a) <> None) by (img_try (img_apply GR1; (subst mr; cbv beta); unfold mrestrict; rewrite Hh, Hb; discriminate)).
destruct (m1 (Z_to_bv 64 a)) as [b'|]; [img_try (exists b'; img_refl) | img_try (exfalso; img_apply NN; img_refl)].
- intros x Hx. destruct (Hpres (bv_unsigned x) Hx) as [Hh _]. rewrite Z_to_bv_bv_unsigned in Hh.
(subst m1full; cbv beta). unfold munrestrict. rewrite Hh. (subst m1 bs; cbv beta). rewrite wbytes_repeat_spec by (img_try (rewrite unsigned_lit_small by (unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END in *; zlia); zlia)).
rewrite unsigned_lit_small by (img_try (unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END in *; zlia)).
replace ((d <=? bv_unsigned x) && (bv_unsigned x <? d + Z.of_nat (Z.to_nat len))) with true; [img_refl|].
symmetry. img_apply andb_true_intro. split; [img_try (img_apply Z.leb_le) | img_try (img_apply Z.ltb_lt)]; zlia.
Qed.
Lemma at_S_memset : forall (Wx : world tfxsegs) md X (P P' : (word -> option byte) -> Prop) ss W' c' (k : nat) (ed el : sv) (d len vb retpc : Z),
at_S Wx md X P ss W' c' -> ss_resv ss = None -> ss_pc ss = tfx_A_musl_memset -> (sHAV <= k)%nat ->
ss_atoms_lt k ss = true -> no_cdata (ss_mem ss) = true ->
sr_get (ss_regs ss) 10%bv = ed -> sr_get (ss_regs ss) 12%bv = el -> sr_get (ss_regs ss) 11%bv = SLit vb -> sr_get (ss_regs ss) 1%bv = SLit retpc ->
sv_atoms_lt sHAV ed = true -> sv_atoms_lt sHAV el = true -> U E0 ed = d -> U E0 el = len ->
0 <= len -> TFX_IMG_END <= d -> d + len < 2 ^ 64 -> retpc mod 4 = 0 -> 0 <= retpc < 2 ^ 64 -> 0 <= vb < 256 ->
(forall m, (forall x : word, ~ X (bv_unsigned x) -> m x = mem0 x) -> P m -> forall a, d <= a < d + len -> apresent (w_H Wx) m a) ->
(forall (E' : env), env_agree sHAV E0 E' ->
forall r, In r (ss_mem ss) -> base_val E' (YQ0b.r_base r) + YQ0b.r_hi r <= d \/ d + len <= base_val E' (YQ0b.r_base r) + YQ0b.r_lo r
\/ YQ0b.r_hi r <= YQ0b.r_lo r) ->
(forall (E' : env), env_agree sHAV E0 E' ->
forall r a, In r (ss_mem ss) -> base_val E' (YQ0b.r_base r) + YQ0b.r_lo r <= a < base_val E' (YQ0b.r_base r) + YQ0b.r_hi r -> 0 <= a < 2 ^ 64) ->
(forall m m' : word -> option byte,
(forall x : word, ~ X (bv_unsigned x) -> m x = mem0 x) -> P m ->
(forall x : word, ~ (d <= bv_unsigned x < d + len) -> m' x = m x) ->
(forall x : word, d <= bv_unsigned x < d + len -> m' x = Some (Z_to_bv 8 vb)) -> P' m') ->
SRr tfxsegs W' c' (at_S Wx md (fun a => X a \/ (d <= a < d + len)) P' (ss_after_stretch ss (ss_mem ss) k CLOB_MS retpc)).
Proof.
clearP. intros Wx md X P P' ss W' c' k ed el d len vb retpc HR Hrv Hpc Hk Hat Hnc H10 H12 H11 H1 Aed Ael Ud Ul Hlen Hd Hdl Hrpc Hrpc' Hvb HPR HEXT H64 HP'.
destruct HR as (-> & ms & mat & E' & -> & HE & HS & MEQ & PRS & HPm).
assert (R10 : getr (ms_regs ms) 10 = Z_to_bv 64 d).
{ rewrite (st_ok_reg_denot (w_H Wx) E' ss ms 10 HS), H10. rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E' ed)). f_equal.
img_change (bv_unsigned (sv_denot E' ed)) with (U E' ed). rewrite (U_agree sHAV E0 E' ed HE Aed). img_exact Ud. }
assert (R12 : getr (ms_regs ms) 12 = Z_to_bv 64 len).
{ rewrite (st_ok_reg_denot (w_H Wx) E' ss ms 12 HS), H12. rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E' el)). f_equal.
img_change (bv_unsigned (sv_denot E' el)) with (U E' el). rewrite (U_agree sHAV E0 E' el HE Ael). img_exact Ul. }
assert (R1 : getr (ms_regs ms) 1 = Z_to_bv 64 retpc) by (img_try (rewrite (st_ok_reg_denot (w_H Wx) E' ss ms 1 HS), H1; img_refl)).
assert (R11 : bv_unsigned (getr (ms_regs ms) 11) mod 256 = vb).
{ rewrite (st_ok_reg_denot (w_H Wx) E' ss ms 11 HS), H11. cbn [sv_denot]. rewrite unsigned_lit_small by zlia. img_apply Z.mod_small. zlia. }
eapply (memset_stretchW Wx k E' ss ms _ d len retpc _ HS Hrv Hpc Hat Hnc R10 R12 R1 Hlen Hd Hdl Hrpc Hrpc' (HPR _ MEQ HPm) (HEXT E' HE) (H64 E' HE)).
intros regs' mem' mat' HS' R10' FR PR FILL. rewrite R11 in FILL. rewrite wvb_collapse.
img_apply SRr_ret. split; [img_refl|]. exists (mkst regs' (Z_to_bv 64 retpc) mem' (seg_rom tfxsegs)), mat', (havoc E' k (map (getr regs') CLOB_MS)).
split; [img_refl|]. split; [img_try (img_exact (env_agree_havoc_ge sHAV k E0 E' _ Hk HE))|]. split; [img_try (img_exact HS')|].
split; [|img_try (split)].
- intros x Hx. cbn [ms_mem mkst]. rewrite (FR x) by (img_try (intros Hin; img_apply Hx; right; img_exact Hin)). img_apply MEQ. intros HX; img_apply Hx; left; img_exact HX.
- intros a Ha. cbn [ms_mem mkst]. img_apply PR. img_exact (PRS a Ha).
- cbn [ms_mem mkst]. img_exact (HP' _ _ MEQ HPm FR FILL).
Qed.
Definition WIN1T (a : Z) : Prop := WIN1P a \/ (QSv <= a < QSv + 8) \/ (mb <= a < mb + 6144) \/ (PBv <= a < PBv + 1).
Lemma WIN1T_WIN : forall a, WIN1T a -> WIN a.
Proof.
intros a [H|[H|[H|H]]]; [img_try (img_exact (WIN1_WIN a (or_introl H))) | | |]; unfold WIN, WINM; right; right; right; [img_try (left; img_exact H) | img_try (right) |].
- left. pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & _). clear - H Z8. zlia.
- right. pose proof map_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PB & _). pose proof map_zoneN as MZ. pose proof size_facts as (_ & _ & Z3 & Z4 & _ & _ & Z7 & _ & _ & Z10 & _).
pose proof Nrange as NR. rewrite PB in H. clear - H Z3 Z4 Z7 Z10 NR MZ.
assert (HND : 8 * (N8D / 8) <= N8D) by (img_try (img_apply Z.mul_div_le; zlia)).
assert (HM : N8D / 8 + 1024 <= MSv / 8) by (img_try (img_apply Z.div_le_lower_bound; zlia)).
pose proof (Z.div_pos N8D 8 ltac:(img_try (zlia)) ltac:(img_try (zlia))). zlia.
Qed.
Lemma windows_WIN1T : forall (E : env) rs a,
(forall k, (k < sHAV)%nat -> ew E k = ew E0 k) -> wins_ok WSKEL1 rs = true -> in_wrange E rs a -> WIN1T a.
Proof.
intros E rs a HE. img_apply windows_in. intros t x Ht Hx. unfold WSKEL1 in Ht. apply in_app_iff in Ht as [Ht|Ht].
- left. img_exact (WSKEL1P_WIN1P E x t HE Ht Hx).
- right. pose proof high_facts as (_ & _ & _ & _ & _ & _ & _ & _ & F9 & F10 & _).
pose proof map_facts as (M1 & M2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _ & PB & _). pose proof map_zoneN as MZ.
pose proof size_facts as (_ & _ & Z3 & Z4 & _ & _ & Z7 & Z8 & _ & Z10 & _). pose proof Hidx as HI. pose proof Nrange as NR.
unfold in_win in Hx. unfold WMAP in Ht. cbn [In] in Ht.
ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighShadowBeg, kHighShadowEnd, ASAN_CEIL, kPtrArrayResv, kMaxNumChunks, MALLOC_MAX, sHAV, aQS, aMAP, aPBS in *.
clear - HE Hx Ht F9 F10 M1 M2 SM1 SM2 PB Z3 Z4 Z7 Z8 Z10 HI NR MZ.
destruct Ht as [<-|[<-|[<-|[]]]]; cbn [fst snd base_val] in Hx; rewrite HE in Hx by zlia.
+ rewrite EaQS in Hx. unfold w64 in Hx. unfold QSv in *. rewrite unsigned_lit_small in Hx by zlia. left. zlia.
+ rewrite EaMAP in Hx. unfold w64 in Hx. rewrite unsigned_lit_small in Hx by zlia. right; left. zlia.
+ rewrite EaPB in Hx. unfold w64 in Hx. rewrite PB in Hx |- *.
assert (HND : 8 * (N8D / 8) <= N8D) by (img_try (img_apply Z.mul_div_le; zlia)).
assert (HM : N8D / 8 + 1024 <= MSv / 8) by (img_try (img_apply Z.div_le_lower_bound; zlia)).
pose proof (Z.div_pos N8D 8 ltac:(img_try (zlia)) ltac:(img_try (zlia))).
rewrite unsigned_lit_small in Hx by zlia. right; right. zlia.
Qed.
Lemma WIN1T_WIN1_aux : forall a, WIN1T a -> WIN1 a.
Proof.
intros a [H|H]; [img_try (left; img_exact H) | img_try (right)]. unfold WINM.
pose proof (WIN1T_WIN a (or_intror H)) as X. unfold WIN in X.
destruct H as [H|[H|H]]; [img_try (left; img_exact H) | img_try (right) |].
- left. pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & _). clear - H Z8. zlia.
- right. pose proof map_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PB & _). pose proof map_zoneN as MZ. pose proof size_facts as (_ & _ & Z3 & Z4 & _ & _ & Z7 & _ & _ & Z10 & _).
pose proof Nrange as NR. rewrite PB in H. clear - H Z3 Z4 Z7 Z10 NR MZ.
assert (HND : 8 * (N8D / 8) <= N8D) by (img_try (img_apply Z.mul_div_le; zlia)).
assert (HM : N8D / 8 + 1024 <= MSv / 8) by (img_try (img_apply Z.div_le_lower_bound; zlia)).
pose proof (Z.div_pos N8D 8 ltac:(img_try (zlia)) ltac:(img_try (zlia))). zlia.
Qed.
Lemma mid_not_WIN1T : forall a, sp0 - IFRAME <= a < sp0 - 64 -> ~ WIN1T a.
Proof. intros a Ha Hw. img_exact (mid_not_WIN1 a Ha (WIN1T_WIN1_aux a Hw)). Qed.
Lemma at_S_runT : forall (Wx : world tfxsegs) tbl (tblok : table_ok tfxsegs tbl) stop md X P ss ss' st W' c',
at_S Wx md X P ss W' c' ->
sym_run_toN_sh tfxsegs tbl FUEL stop ss = (ss', st) -> match st with RS_ecall => False | _ => True end ->
(forall a, WIN1T a -> X a) -> wins_ok WSKEL1 (ss_mem ss) = true -> pstable WIN1T P -> stack_shaped ss' = true ->
SRr tfxsegs W' c' (at_S Wx md X P ss').
Proof. img_exact (at_S_run_gen WSKEL1 WIN1T windows_WIN1T mid_not_WIN1T). Qed.
Lemma at_S_run_ecallT : forall (Wx : world tfxsegs) tbl (tblok : table_ok tfxsegs tbl) stop md X P ss ss' W' c',
at_S Wx md X P ss W' c' ->
sym_run_toN_sh tfxsegs tbl FUEL stop ss = (ss', RS_ecall) -> ss_resv ss' = None ->
(forall a, WIN1T a -> X a) -> wins_ok WSKEL1 (ss_mem ss) = true -> pstable WIN1T P -> stack_shaped ss' = true ->
SRr tfxsegs W' c' (at_N Wx md X P ss').
Proof. img_exact (at_S_run_ecall_gen WSKEL1 WIN1T windows_WIN1T mid_not_WIN1T). Qed.
Definition PBUFW (Wx : world tfxsegs) (m : word -> option byte) : Prop :=
forall i, (i < length tr)%nat -> val_mem tfxsegs (mrestrict (w_H Wx) m) (sp0 - IFRAME + 16 + 8 * Z.of_nat i) 8 (nth i tr 0).
Lemma PBUFW_stableT : forall Wx, pstable WIN1T (PBUFW Wx).
Proof.
intros Wx m m' FR HB i Hi. pose proof tr_length as LEN. pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7). destruct Hsp as (S1 & _).
pose proof (u64_range (getr regs0 2)) as U2.
eapply val_mem_frame; [|img_try (img_exact (HB i Hi))]. intros k Hk. img_apply FR.
rewrite unsigned_lit_small by (img_try (clear - Hi Hk LEN S1 T7 U2; numconst; unfold IFRAME, sp0 in *; zlia)).
img_apply mid_not_WIN1T. clear - Hi Hk LEN. unfold IFRAME. zlia.
Qed.
End h.
End g.
