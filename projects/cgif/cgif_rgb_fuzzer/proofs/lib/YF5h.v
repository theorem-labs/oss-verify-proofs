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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF64 YF3v YF3w YF3x YF41 YF47 YF0a YF5k YF4b YF4c YF5t YF5u YF5v YF5f YF5l YF49.
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
Local Abbreviation AR9 f := (f idx res LY IMG Hidx Hres) (only parsing).
Local Abbreviation high_facts := (AR9 (AR1 (@YF5k.high_facts _))).
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
Local Abbreviation AR8 f := (f Nrange Hidx Hres) (only parsing).
Local Abbreviation map_facts := ((AR8 (AR3 (@YF5k.map_facts _))) Hmap).
Local Abbreviation map_zone := ((AR3 (@YF5k.map_zone _)) Nrange Hidx Hmap).
Local Abbreviation map_zoneN := ((AR8 (AR3 (@YF5k.map_zoneN _))) Hmap).
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
Local Abbreviation ARa f := (f idx res mb) (only parsing).
Local Abbreviation win_sub_sound := ((ARa (@YF5k.win_sub_sound ly regs0)) Hidx Hres).
Local Abbreviation in_win := (@YF5k.in_win).
Local Abbreviation AR4 f := (AR0 f LY IMG Nrange Hidx Hres) (only parsing).
Local Abbreviation WSKELP_WINP := (AR4 (AR1 (@YF5k.WSKELP_WINP _))).
Local Abbreviation WSKEL1P_WIN1P := (AR4 (AR1 (@YF5k.WSKEL1P_WIN1P _))).
Local Abbreviation WMAP_WINM := ((AR4 (AR1 (@YF5k.WMAP_WINM _))) Hmap).
Local Abbreviation WSKEL_WIN := ((AR4 (AR1 (@YF5k.WSKEL_WIN _))) Hmap).
Local Abbreviation WSKEL1_WIN1 := ((AR4 (AR1 (@YF5k.WSKEL1_WIN1 _))) Hmap).
Local Abbreviation windows_in := ((ARa (@YF5k.windows_in ly regs0)) Hidx Hres).
Local Abbreviation windows_WINP := (AR4 (AR1 (@YF5k.windows_WINP _))).
Local Abbreviation windows_WIN1P := (AR4 (AR1 (@YF5k.windows_WIN1P _))).
Local Abbreviation windows_WIN := ((AR4 (AR1 (@YF5k.windows_WIN _))) Hmap).
Local Abbreviation windows_WIN1 := ((AR4 (AR1 (@YF5k.windows_WIN1 _))) Hmap).
Local Abbreviation frame_WIN1P := (AR4 (AR1 (@YF5k.frame_WIN1P _))).
Local Abbreviation frame_WIN1 := ((AR4 (AR1 (@YF5k.frame_WIN1 _))) Hmap).
Local Abbreviation AR2 f := (f LY IMG Hsp Nrange Hidx Hres) (only parsing).
Local Abbreviation WINP_not_high := (AR2 (AR3 (@YF5k.WINP_not_high _))).
Local Abbreviation WIN_not_high := ((AR2 (AR3 (@YF5k.WIN_not_high _))) Hmap).
Variables (mat0 : list word).
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 (0x53104 + D_2c4)) mem0 (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis U1 : tfx_unwind_spec.
Local Abbreviation all_disjoint_of_forall := (@YF5k.all_disjoint_of_forall).
Local Abbreviation img_rw_writable := ((ARa (AR1 (@YF5k.img_rw_writable))) Hidx).
Local Abbreviation AR5 f := (f imgk W ly regs0) (only parsing).
Local Abbreviation kept_of_frame := ((ARa (AR5 (@YF5k.kept_of_frame))) Hidx).
Local Abbreviation SKEL_TAIL := (@YF5k.SKEL_TAIL imgk).
Local Abbreviation blocks_facts := (@YF5k.blocks_facts _ imgk ly LY IMG).
Local Abbreviation off_T := (AR9 (AR1 (@YF5k.off_T _))).
Local Abbreviation off_C := (AR9 (AR1 (@YF5k.off_C _))).
Local Abbreviation off_Q := (AR9 (AR1 (@YF5k.off_Q _))).
Local Abbreviation off_NB := (@YF5k.off_NB _ imgk ly LY IMG).
Local Abbreviation off_SB := (@YF5k.off_SB _ imgk ly LY IMG).
Local Abbreviation off_shadow := ((ARa (AR1 (@YF5k.off_shadow))) Hidx).
Ltac off_by tac :=
first [ img_apply off_img_high; tac | img_apply off_T; tac | img_apply off_C; tac | img_apply off_Q; tac | img_apply off_NB; tac | img_apply off_SB; tac
| img_apply map_off_img; tac | img_apply off_shadow; tac
| unfold off_img; unfold TFX_IMG_LO; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; tac ].
Local Abbreviation DZONE := (@YF5k.DZONE imgk ly).
Variable DPOST : Z -> (word -> option byte) -> Prop.
Local Abbreviation DZONE_disj := ((AR2 (AR3 (@YF5k.DZONE_disj _))) Hmap Hmap_apart).
Local Abbreviation RFACTS := (AR1 (@YF5k.RFACTS)).
Local Abbreviation zone_lit := ((AR1 (@YF5k.zone_lit _)) LY IMG Hsp).
Local Abbreviation zone_irw := ((AR1 (@YF5k.zone_irw _)) LY IMG Hsp).
Local Abbreviation zone_T := ((AR1 (@YF5k.zone_T _)) idx res LY IMG Hsp Hidx Hres).
Local Abbreviation zone_C := ((AR1 (@YF5k.zone_C _)) idx res LY IMG Hsp Hidx Hres).
Local Abbreviation tail_ext_ok := (AR2 (AR0 (AR1 (@YF5k.tail_ext_ok _)))).
Local Abbreviation RFACTS_map := ((AR8 ((AR3 (@YF5k.RFACTS_map _)) LY IMG)) Hmap Hmap_apart).
Local Abbreviation ARc f := (AR5 f mem0) (only parsing).
Local Abbreviation at_ST := (AR0 ((ARc (@YF5k.at_ST _)) md0)).
Local Abbreviation memset_stretch := ((AR8 ((ARa ((ARc (@YF5k.memset_stretch _ _)) md0 n)) Hsp)) Hmap Hmap_apart mat0 DPOST).
Ltac clearM := try clear DPOST; try clear Hmap_apart; try clear Hmap.
Local Abbreviation AR7 f := (AR1 f mem0) (only parsing).
Local Abbreviation at_S := (AR0 (AR7 (@YF5k.at_S _))).
Local Abbreviation at_N := (AR0 (AR7 (@YF5k.at_N _))).
Local Abbreviation at_RETS := (@YF5k.at_RETS _ regs0 mem0 imgk).
Local Abbreviation pstable := (@YF5k.pstable).
Local Abbreviation stack_shaped := (@YF5k.stack_shaped).
Local Abbreviation window_present := ((AR1 (@YF5k.window_present)) idx res Hidx).
Local Abbreviation stack_present_of := ((AR0 (AR1 (@YF5k.stack_present_of _))) LY Hsp Hidx).
Local Abbreviation mid_not_WIN1P := (AR2 (AR3 (@YF5k.mid_not_WIN1P _))).
Local Abbreviation mid_not_WIN1 := ((AR2 (AR3 (@YF5k.mid_not_WIN1 _))) Hmap).
Local Abbreviation wins_ok := (@YF5k.wins_ok).
Local Abbreviation at_S_run_gen := ((AR0 (AR7 (@YF5k.at_S_run_gen _ _))) LY Hsp Hidx).
Local Abbreviation at_S_run_ecall_gen := ((AR0 (AR7 (@YF5k.at_S_run_ecall_gen _ _))) LY Hsp Hidx).
Local Abbreviation at_S_runP := (AR2 (AR0 (AR7 (@YF5k.at_S_runP _ _)))).
Local Abbreviation at_S_runM := ((AR2 (AR0 (AR7 (@YF5k.at_S_runM _ _)))) Hmap).
Local Abbreviation at_S_run_ecallP := (AR2 (AR0 (AR7 (@YF5k.at_S_run_ecallP _ _)))).
Local Abbreviation at_S_run_ecallM := ((AR2 (AR0 (AR7 (@YF5k.at_S_run_ecallM _ _)))) Hmap).
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
Local Abbreviation at_S_ret := (AR8 ((AR0 (AR7 (@YF5k.at_S_ret _))) Htp Hra Hsp)).
Local Abbreviation kept_of_frame2 := ((AR1 (@YF5k.kept_of_frame2)) idx res Hidx).
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
Local Abbreviation vis_present := ((ARc (@YF5t.vis_present _)) idx res Hidx DPOST B S HARm).
Local Abbreviation in_thread_junk := (@YF5t.in_thread_junk ly B S).
Local Abbreviation in_sec_junk := (@YF5t.in_sec_junk ly B S).
Local Abbreviation in_as_junk := (@YF5t.in_as_junk ly B S).
Local Abbreviation junk_word := ((AR9 (ARc (@YF5t.junk_word _))) DPOST B S HARm).
Local Abbreviation ARb f := (f _ imgk W ly mem0 B S) (only parsing).
Local Abbreviation cell_sym := ((ARb (@YF5t.cell_sym)) TS HARm).
Local Abbreviation cell_lit := ((ARb (@YF5t.cell_lit)) TS HARm).
Local Abbreviation cell_state := ((ARb (@YF5t.cell_state)) HARm).
Local Abbreviation In_acells_sec := (@YF5t.In_acells_sec ly B S).
Local Abbreviation sec_vals := (@YF5t.sec_vals _ imgk W ly mem0 idx res B S TS HARm Hidx_def Hres_def).
Local Abbreviation unwinding_val := ((ARb (@YF5t.unwinding_val)) HARm).
Local Abbreviation rw_writable := ((AR1 (@YF5t.rw_writable)) idx res Hidx DPOST S).
Local Abbreviation val_mem_mod8 := ((ARc (@YF5t.val_mem_mod8)) idx res Hidx DPOST S).
Local Abbreviation chunk_lit := (AR0 (ARc (@YF5t.chunk_lit))).
Local Abbreviation chunk_lit_at := (AR0 (ARc (@YF5t.chunk_lit_at))).
Local Abbreviation chunk_atom := ((AR0 (ARc (@YF5t.chunk_atom))) Hidx DPOST S).
Local Abbreviation AR6 f := (f DPOST B S TS HTSD HARm Hidx_def Hres_def Hj0 Hj1 Hj2 Hj3 Hj4 Hj5 Hj9 Hj6 Hj7 Hj8 Hi1 Hi2 Hi3) (only parsing).
Local Abbreviation SREG0_ok := (AR6 ((AR2 (AR0 (ARc (@YF5u.SREG0_ok _)))) Hpres0)).
Local Abbreviation PAIRS_ok := ((AR2 (AR0 (ARc (@YF5v.PAIRS_ok _)))) DPOST S).
Local Abbreviation FACTS_ok := ((AR8 ((AR0 (ARc (@YF5v.FACTS_ok _))) LY IMG Hn Hsp)) DPOST S).
Local Abbreviation SEED_ok := (AR6 ((AR8 ((AR0 (ARc (@YF5v.SEED_ok _ _))) LY IMG Hn Htp Hsp)) Hpres0)).
Local Abbreviation PBUF := ((AR5 (@YF5f.PBUF)) ch).
Local Abbreviation PBUF_stableP := (AR2 (ARa ((AR5 (@YF5f.PBUF_stableP _)) n ch))).
Local Abbreviation PBUF_stableM := ((AR2 (ARa ((AR5 (@YF5f.PBUF_stableM _)) n ch))) Hmap).
Local Abbreviation seg0 := (AR6 ((AR8 ((AR0 ((ARc (@YF5f.seg0 _ _)) md0)) LY IMG Hn Htp Hra4096 Hsp Hch)) Hpres0 mat0 U1)).
Local Abbreviation appregs := (@YF5l.appregs).
Local Abbreviation st_ok_appregs := (@YF5l.st_ok_appregs _ imgk).
Local Abbreviation at_S_app := (AR0 (AR7 (@YF5l.at_S_app _))).
Local Abbreviation WIN1N := ((AR1 (@YF5l.WIN1N)) n).
Local Abbreviation WINPN := ((AR1 (@YF5l.WINPN)) n).
Local Abbreviation WSKEL1N := (@YF5l.WSKEL1N imgk).
Local Abbreviation WIN1N_WINPN := ((AR3 (@YF5l.WIN1N_WINPN)) Hidx).
Local Abbreviation windows_WIN1N := (AR4 (AR1 (@YF5l.windows_WIN1N _))).
Local Abbreviation mid_not_WIN1N := (AR2 (AR3 (@YF5l.mid_not_WIN1N _))).
Local Abbreviation at_S_runN := (AR2 (AR0 (AR7 (@YF5l.at_S_runN _ _)))).
Local Abbreviation PBUF_stableN := (AR2 (ARa ((AR5 (@YF5l.PBUF_stableN _)) n ch))).
Local Abbreviation at_S_val := (AR0 (AR7 (@YF5l.at_S_val _))).
Local Abbreviation memset_stretchW := ((AR8 ((ARc (@YF5l.memset_stretchW _)) md0 n idx res Hsp)) mat0 DPOST S).
Local Abbreviation at_S_memset := ((AR8 ((AR0 ((ARc (@YF5l.at_S_memset _)) md0)) Hsp)) mat0 DPOST S).
Local Abbreviation WIN1T := ((AR1 (@YF5l.WIN1T)) n idx mb).
Local Abbreviation WIN1T_WIN := ((AR8 (AR3 (@YF5l.WIN1T_WIN _))) Hmap).
Local Abbreviation windows_WIN1T := ((AR4 (AR1 (@YF5l.windows_WIN1T _))) Hmap).
Local Abbreviation WIN1T_WIN1_aux := ((AR8 (AR3 (@YF5l.WIN1T_WIN1_aux _))) Hmap).
Local Abbreviation mid_not_WIN1T := ((AR2 (AR3 (@YF5l.mid_not_WIN1T _))) Hmap).
Local Abbreviation at_S_runT := ((AR2 (AR0 (AR7 (@YF5l.at_S_runT _ _)))) Hmap).
Local Abbreviation at_S_run_ecallT := ((AR2 (AR0 (AR7 (@YF5l.at_S_run_ecallT _ _)))) Hmap).
Local Abbreviation PBUFW := ((AR1 (@YF5l.PBUFW)) ch).
Local Abbreviation PBUFW_stableT := ((AR2 (ARa ((AR1 (@YF5l.PBUFW_stableT _)) n ch))) Hmap).
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
Local Ltac s_runN HR tbl tblok stop ss' HX HP :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let st := img_ev (snd (sym_run_toN_sh tfxsegs tbl FUEL stop ss)) in
eapply SRr_bind;
[ img_try (eapply (at_S_runN Wx tbl tblok stop md X P ss ss' st W' c' HR);
[ (img_case; vm_compute); img_refl | img_exact I | img_exact HX | (img_case; vm_compute); img_refl | img_exact HP | (img_case; vm_compute); img_refl ])
| img_try (clear HR; let W2 := fresh "W" in let c2 := fresh "c" in intros W2 c2 _ HR) ] end.
Definition PNULL (m : word -> option byte) : Prop :=
PBUF m /\ val_mem tfxsegs (mrestrict (w_H W) m) TFX_OOM 1 1 /\ val_mem tfxsegs (mrestrict (w_H W) m) TFX_ERRNO 4 12.
Definition PNULLX (m : word -> option byte) : Prop :=
PNULL m /\
(val_mem tfxsegs (mrestrict (w_H W) m) (T + t_unwinding) 1 0 /\ val_mem tfxsegs (mrestrict (w_H W) m) (TFX_INST + o_sec_reserved) 8 res /\
val_mem tfxsegs (mrestrict (w_H W) m) (TFX_INST + o_sec_n) 8 idx /\ val_mem tfxsegs (mrestrict (w_H W) m) (TFX_INST + o_sec_mutex) 4 0 /\
(forall a, WINT a -> apresent (w_H W) m a) /\ (forall a, WINI a -> aview tfxsegs (w_H W) m a <> None)).
Lemma tail_lits_apart : forall r, In (skel r) SKEL_TAIL -> YQ0b.r_base r = None ->
(YQ0b.r_hi r <= TFX_OOM \/ TFX_OOM + 2 <= YQ0b.r_lo r) /\ (YQ0b.r_hi r <= TFX_ERRNO \/ TFX_ERRNO + 4 <= YQ0b.r_lo r).
Proof.
clearP. intros r Hin Hb. destruct r as [bs lo hi wlo whi cs]. cbn [YQ0b.r_base] in Hb. (subst bs; cbv beta). unfold skel in Hin. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi] in *.
let sk := img_ev constr:(SKEL_TAIL) in img_change SKEL_TAIL with sk in Hin. cbn [In] in Hin. unfold TFX_OOM, TFX_ERRNO.
repeat match type of Hin with _ \/ _ => destruct Hin as [Hin|Hin]; [img_try (first [discriminate Hin | injection Hin as <- <- <- <-; clear; zlia]) |] | False => destruct Hin end.
Qed.
Lemma segR : forall W' c',
at_S W md0 WINP PBUF (resume S_N (SLit ENOMEM_RETv) (ss_mem S_N) (ss_facts S_N)) W' c' ->
SRr tfxsegs W' c' (at_RETS W (w64 0) md0 WINPN PNULLX).
Proof.
clearP. intros W1 c1 HR. pose proof PBUF_stableN as HP. pose proof WIN1N_WINPN as HX.
pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7). pose proof Hsp as (S1 & _ & S3 & _). pose proof (u64_range (getr regs0 2)) as U2.
pose proof high_facts as (F1 & F2 & _ & _ & _ & _ & F7 & F8 & _).
assert (OOM1 : val_mem tfxsegs (mrestrict (w_H W) mem0) (TFX_OOM + 1) 1 1) by (img_try (img_apply cell_lit; (img_case; vm_compute); img_refl)).
s_noconds HR.
apply (at_S_weaken W md0 WINP WINPN PBUF PBUF _ W1 c1) in HR; [| img_try (intros a Ha; left; img_exact Ha) | img_try (intros m Hm; img_exact Hm)].
apply (at_S_app W md0 WINPN PBUF _ W1 c1 NREGS) in HR; [| img_refl |].
2:{ intros E' m HE MEQ PRS HPm HM. pose proof (proj1 HE) as HEn.
assert (OOM1' : val_mem tfxsegs (mrestrict (w_H W) m) (TFX_OOM + 1) 1 1).
{ eapply val_mem_frame; [|img_try (img_exact OOM1)]. intros k Hk. img_apply MEQ. rewrite unsigned_lit_small by (img_try (unfold TFX_OOM; zlia)).
pose proof BSLv_range as HB. clear - Hk F1 F2 S1 T7 HB. unfold WINPN, WINP, WINT, WINI. numconst. unfold TFX_OOM, TFX_ERRNO, TFX_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex in *. try unfold T in *. zlia. }
split; [|img_try (split)].
- unfold NREGS. img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_cons; [|img_apply Forall_nil]])].
+ unfold region_ok, lit1. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
split; [img_try (unfold TFX_OOM; zlia)|]. split; [img_try (unfold TFX_OOM; zlia)|]. split; [img_try (intros o Ho; zlia)|].
img_apply Forall_cons; [|img_try (img_apply Forall_nil)]. eapply chunk_ok_val; [img_refl | img_try (cbn; zlia) | img_try (cbn; zlia) |]. rewrite Z.add_0_l. img_exact OOM1'.
+ unfold region_ok, oomR. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
split; [img_try (unfold TFX_OOM; zlia)|]. split; [img_try (unfold TFX_OOM; zlia)|]. split; [|img_try (img_apply Forall_nil)]. intros o Ho. rewrite Z.add_0_l. img_apply img_rw_writable. unfold TFX_OOM in *. zlia.
+ unfold region_ok, errR. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
split; [img_try (unfold TFX_ERRNO; zlia)|]. split; [img_try (unfold TFX_ERRNO; zlia)|]. split; [|img_try (img_apply Forall_nil)]. intros o Ho. rewrite Z.add_0_l. img_apply img_rw_writable. unfold TFX_ERRNO in *. zlia.
- unfold NREGS, lit1, oomR, errR. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. clear. unfold TFX_OOM, TFX_ERRNO. repeat split; zlia.
- intros r1 r2 Hr1 Hr2.
assert (B2 : base_val E' (Some 2%nat) = sp0) by (img_try (cbn [base_val]; rewrite (HEn 2%nat ltac:(unfold sHAV; zlia)), E2; img_refl)).
assert (L2' : YQ0b.r_base r2 = None /\ ((YQ0b.r_lo r2 = TFX_OOM + 1 /\ YQ0b.r_hi r2 = TFX_OOM + 2) \/ (YQ0b.r_lo r2 = TFX_OOM /\ YQ0b.r_hi r2 = TFX_OOM + 1) \/ (YQ0b.r_lo r2 = TFX_ERRNO /\ YQ0b.r_hi r2 = TFX_ERRNO + 4))).
{ unfold NREGS, lit1, oomR, errR in Hr2. destruct Hr2 as [<-|[<-|[<-|[]]]]; cbn; [img_try (split; [img_refl|left; zlia]) | img_try (split; [img_refl|right; left; zlia]) | img_try (split; [img_refl|right; right; zlia])]. }
destruct L2' as [Hb2 L2].
unfold extent_disjoint. rewrite Hb2. cbn [base_val].
lazymatch type of Hr1 with In _ ?l =>
let m3 := img_ev (firstn 3 l) in
let tl3 := img_ev (skipn 3 l) in
assert (SPLIT : In r1 m3 \/ In (skel r1) SKEL_TAIL)
by (img_try (img_change l with (m3 ++ tl3) in Hr1; apply in_app_iff in Hr1 as [Hr1|Hr1]; [img_try (left; img_exact Hr1) | img_try (right)];
apply (in_map skel) in Hr1; replace (map skel tl3) with SKEL_TAIL in Hr1 by ((img_case; vm_compute); img_refl); img_exact Hr1)) end.
clear Hr1. destruct SPLIT as [Hr1|Hr1].
+ destruct Hr1 as [<-|[<-|[<-|[]]]]; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi]; rewrite B2;
clear - L2 S1 T7 U2; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_OOM, TFX_ERRNO, kHighMemBeg, ASTACK, IFRAME in *; unfold sp0 in *; zlia.
+ pose proof (tail_ext_ok E' r1 HEn Hr1) as (X1 & X2 & X3 & X4 & X5 & X6).
destruct (YQ0b.r_base r1) as [b|] eqn:Eb.
*
clear X1 X2 X3 X4 X5 X6. destruct r1 as [bs lo hi wlo whi cs]. cbn [YQ0b.r_base] in Eb. (subst bs; cbv beta). unfold skel in Hr1.
cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi] in Hr1 |- *.
let sk := img_ev constr:(SKEL_TAIL) in img_change SKEL_TAIL with sk in Hr1. cbn [In] in Hr1.
repeat match type of Hr1 with _ \/ _ => destruct Hr1 as [Hr1|Hr1]; [img_try (first [discriminate Hr1 | injection Hr1 as <- <- <- <- <-]) |] | False => destruct Hr1 end.
all: pose proof BSLv_range as HB; cbn [base_val]; rewrite ?(HEn 32%nat ltac:(img_try (unfold sHAV; zlia))), ?(HEn 33%nat ltac:(img_try (unfold sHAV; zlia))), ?(HEn 55%nat ltac:(img_try (unfold sHAV; zlia))); rewrite ?EaT, ?EaC, ?EaBSL; unfold w64;
rewrite unsigned_lit_small by (img_try (clear - F1 F2 F7 F8 HB; numconst; unfold TFX_INST in *; try unfold T in *; zlia)); clear - L2 F1 F7 HB; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_OOM, TFX_ERRNO, kHighMemBeg, TFX_INST in *; try unfold T in *; zlia.
* pose proof (tail_lits_apart r1 Hr1 Eb) as [A1 A2]. cbn [base_val]. clear - L2 A1 A2. unfold TFX_OOM, TFX_ERRNO in *. zlia. }
s_station HR S_R0.
s_runN HR tfxtbl_rtC tfxtbl_rtC_ok (0x36350 + D_150) S_R1 HX HP.
s_runN HR tfxtbl_rtA tfxtbl_rtA_ok (0x53434 + D_2c4) S_RET HX HP.
apply (at_S_facts W md0 WINPN PBUF (fun m => (val_mem tfxsegs (mrestrict (w_H W) m) TFX_OOM 1 1 /\ val_mem tfxsegs (mrestrict (w_H W) m) TFX_ERRNO 4 12) /\
(val_mem tfxsegs (mrestrict (w_H W) m) (T + t_unwinding) 1 0 /\ val_mem tfxsegs (mrestrict (w_H W) m) (TFX_INST + o_sec_reserved) 8 res /\
val_mem tfxsegs (mrestrict (w_H W) m) (TFX_INST + o_sec_n) 8 idx /\ val_mem tfxsegs (mrestrict (w_H W) m) (TFX_INST + o_sec_mutex) 4 0 /\
(forall a, WINT a -> apresent (w_H W) m a) /\ (forall a, WINI a -> aview tfxsegs (w_H W) m a <> None))) S_RET) in HR.
2:{ intros E' ms HE HS. pose proof (proj1 HE) as HEn. pose proof Hidx as HI. pose proof Hres as [HRS _]. pose proof BSLv_range as HB.
assert (UT : bv_unsigned (ew E' 32) = T) by (img_try (rewrite (HEn 32%nat ltac:(unfold sHAV; zlia)), EaT; unfold w64; img_apply unsigned_lit_small; clear - F1 F2; ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize in *; try unfold T in *; zlia)).
assert (UBSL : bv_unsigned (ew E' 55) = BSLv) by (img_try (rewrite (HEn 55%nat ltac:(unfold sHAV; zlia)), EaBSL; unfold w64; img_apply unsigned_lit_small; unfold TFX_INST in *; zlia)).
split; [img_try (split; [memv HS 61%nat 0%nat; [img_refl | img_refl | zlia] | memv HS 62%nat 0%nat; [img_refl | img_refl | zlia]])|].
split; [img_try (memv HS 41%nat 0%nat; [cbn [base_val YQ0b.r_base]; rewrite UT; unfold t_unwinding; zlia | img_refl | zlia])|].
split; [img_try (memv HS 49%nat 0%nat; [cbn [base_val YQ0b.r_base]; img_refl | rewrite sv_denot_SOff0, (HEn 40%nat ltac:(unfold sHAV; zlia)), EaRES; img_refl | unfold kMaxNumChunks in *; zlia])|].
split; [img_try (memv HS 50%nat 0%nat; [cbn [base_val YQ0b.r_base]; img_refl | rewrite sv_denot_SOff0, (HEn 41%nat ltac:(unfold sHAV; zlia)), EaNCH; img_refl | unfold kMaxNumChunks in *; zlia])|].
split; [img_try (memv HS 53%nat 0%nat; [cbn [base_val YQ0b.r_base]; img_refl | img_refl | zlia])|].
split.
- intros a Hw. unfold WINT in Hw. destruct Hw as [Hw|[Hw|[Hw|Hw]]].
+ destruct (Z_lt_le_dec a (T + 2800)) as [H28|H28].
* eapply (st_ok_window_apresent_off (w_H W) E' _ _ 40%nat _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite UT; zlia) | img_try (off_by ltac:(unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; clear - Hw H28 F1 F2; ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize in *; try unfold T in *; zlia)) ].
* eapply (st_ok_window_apresent_off (w_H W) E' _ _ 42%nat _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite UT; zlia) | img_try (off_by ltac:(unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; clear - Hw H28 F1 F2; ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize in *; try unfold T in *; zlia)) ].
+ eapply (st_ok_window_apresent_off (w_H W) E' _ _ 43%nat _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite UT; zlia) | img_try (off_by ltac:(unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; clear - Hw F1 F2; ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize in *; try unfold T in *; zlia)) ].
+ eapply (st_ok_window_apresent_off (w_H W) E' _ _ 44%nat _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite UT; zlia) | img_try (off_by ltac:(unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; clear - Hw F1 F2; ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize in *; try unfold T in *; zlia)) ].
+ eapply (st_ok_window_apresent_off (w_H W) E' _ _ 41%nat _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite UT; unfold t_unwinding in *; zlia) | img_try (off_by ltac:(unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END, t_unwinding in *; clear - Hw F1 F2; ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize in *; try unfold T in *; zlia)) ].
- intros a Ha. assert (Ra : 0 <= a < 2 ^ 64) by (img_try (clear - Ha HB; unfold WINI, TFX_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex in *; zlia)).
img_apply (YF49.writable_visible (w_H W) (ms_mem ms) a Ra). unfold WINI in Ha.
destruct Ha as [Hw|[Hw|[Hw|[Hw|Hw]]]].
+ destruct (Z_lt_le_dec a (TFX_INST + 120)) as [A1|A1]; [|img_try (destruct (Z_lt_le_dec a (TFX_INST + 128)) as [A2|A2])].
* eapply (st_ok_window_writable (w_H W) E' _ _ 49%nat _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; unfold TFX_INST, o_sec_reserved in *; zlia)].
* eapply (st_ok_window_writable (w_H W) E' _ _ 50%nat _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; unfold TFX_INST in *; zlia)].
* eapply (st_ok_window_writable (w_H W) E' _ _ 51%nat _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; unfold TFX_INST, o_sec_sorted in *; zlia)].
+ eapply (st_ok_window_writable (w_H W) E' _ _ 52%nat _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; unfold TFX_INST, o_sec_stats in *; zlia)].
+ eapply (st_ok_window_writable (w_H W) E' _ _ 59%nat _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite UBSL; zlia)].
+ eapply (st_ok_window_writable (w_H W) E' _ _ 53%nat _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; unfold TFX_INST, o_sec_mutex in *; zlia)].
+ eapply (st_ok_window_writable (w_H W) E' _ _ 54%nat _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; zlia)]. }
apply (at_S_weaken W md0 WINPN WINPN _ PNULLX S_RET) in HR; [| img_try (intros a Ha; img_exact Ha) | img_try (intros m [H1 [H2 H3]]; img_exact (conj (conj H1 H2) H3))].
img_change (w64 0) with (sv_denot E0 (SLit 0)).
eapply (at_S_ret W md0 WINPN PNULLX S_RET _ _ (SLit 0) HR); [img_refl | img_refl | img_refl | img_refl | img_refl | img_refl |].
repeat constructor.
Qed.
End g.
End d.
