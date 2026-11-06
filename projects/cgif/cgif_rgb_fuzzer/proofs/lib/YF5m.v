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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF64 YF3v YF3w YF3x YF41 YF47 YF0a YF5k YF5t YF5u YF5v YF5f YF5l.
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
Definition WIN1S (a : Z) : Prop := WIN1P a \/ (QSv <= a < QSv + 8) \/ (mb <= a < mb + 6144).
Definition WSKEL1S {imgk : img} : list (option nat * Z * Z) := WSKEL1P ++ [(Some aQS, 0, 8); (Some aMAP, 0, 6144)].
Lemma WIN1S_WIN1T : forall a, WIN1S a -> WIN1T a.
Proof. clearP. intros a [H|[H|H]]; [img_try (left) | img_try (right; left) | img_try (right; right; left)]; img_exact H. Qed.
Lemma WIN1S_WIN : forall a, WIN1S a -> WIN a.
Proof. intros a H. img_exact (WIN1T_WIN a (WIN1S_WIN1T a H)). Qed.
Lemma windows_WIN1S : forall (E : env) rs a,
(forall k, (k < sHAV)%nat -> ew E k = ew E0 k) -> wins_ok WSKEL1S rs = true -> in_wrange E rs a -> WIN1S a.
Proof.
intros E rs a HE. img_apply windows_in. intros t x Ht Hx. unfold WSKEL1S in Ht. apply in_app_iff in Ht as [Ht|Ht].
- left. img_exact (WSKEL1P_WIN1P E x t HE Ht Hx).
- right. pose proof high_facts as (_ & _ & _ & _ & _ & _ & _ & _ & F9 & F10 & _).
pose proof map_facts as (M1 & M2 & _). pose proof map_zoneN as MZ. pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & _). pose proof Hidx as HI. pose proof Nrange as NR.
unfold in_win in Hx. cbn [In] in Ht.
ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kPtrArrayResv, kMaxNumChunks, MALLOC_MAX, sHAV, aQS, aMAP in *.
clear - HE Hx Ht F9 F10 M1 M2 Z8 HI NR MZ.
destruct Ht as [<-|[<-|[]]]; cbn [fst snd base_val] in Hx; rewrite HE in Hx by zlia.
+ rewrite EaQS in Hx. unfold w64 in Hx. unfold QSv in *. rewrite unsigned_lit_small in Hx by zlia. left. zlia.
+ rewrite EaMAP in Hx. unfold w64 in Hx. rewrite unsigned_lit_small in Hx by zlia. right. zlia.
Qed.
Lemma mid_not_WIN1S : forall a, sp0 - IFRAME <= a < sp0 - 64 -> ~ WIN1S a.
Proof. intros a Ha Hw. img_exact (mid_not_WIN1T a Ha (WIN1S_WIN1T a Hw)). Qed.
Lemma at_S_runS : forall (Wx : world tfxsegs) tbl (tblok : table_ok tfxsegs tbl) stop md X P ss ss' st W' c',
at_S Wx md X P ss W' c' ->
sym_run_toN_sh tfxsegs tbl FUEL stop ss = (ss', st) -> match st with RS_ecall => False | _ => True end ->
(forall a, WIN1S a -> X a) -> wins_ok WSKEL1S (ss_mem ss) = true -> pstable WIN1S P -> stack_shaped ss' = true ->
SRr tfxsegs W' c' (at_S Wx md X P ss').
Proof. img_exact (at_S_run_gen WSKEL1S WIN1S windows_WIN1S mid_not_WIN1S). Qed.
Lemma at_S_run_ecallS : forall (Wx : world tfxsegs) tbl (tblok : table_ok tfxsegs tbl) stop md X P ss ss' W' c',
at_S Wx md X P ss W' c' ->
sym_run_toN_sh tfxsegs tbl FUEL stop ss = (ss', RS_ecall) -> ss_resv ss' = None ->
(forall a, WIN1S a -> X a) -> wins_ok WSKEL1S (ss_mem ss) = true -> pstable WIN1S P -> stack_shaped ss' = true ->
SRr tfxsegs W' c' (at_N Wx md X P ss').
Proof. img_exact (at_S_run_ecall_gen WSKEL1S WIN1S windows_WIN1S mid_not_WIN1S). Qed.
Definition brun (m : word -> option byte) (r : Z * Z * Z) : Prop :=
forall a, fst (fst r) <= a < snd (fst r) -> m (w64 a) = Some (Z_to_bv 8 (snd r)).
Definition run_ok (r : Z * Z * Z) : Prop :=
(mb + 6144 <= fst (fst r) /\ snd (fst r) <= mb + MSv) \/ (SMv <= fst (fst r) /\ snd (fst r) <= SMv + MSv / 8).
Definition PS (Wy : world tfxsegs) (sh : list (Z * Z * Z)) (m : word -> option byte) : Prop :=
PBUFW Wy m /\
(forall a, mb + 6144 <= a < mb + MSv -> apresent (w_H Wy) m a) /\
(forall a, SMv <= a < SMv + MSv / 8 -> apresent (w_H Wy) m a) /\
Forall (brun m) sh.
Lemma runs_not_WIN1S : forall a, (mb + 6144 <= a < mb + MSv) \/ (SMv <= a < SMv + MSv / 8) -> ~ WIN1S a.
Proof.
intros a Ha Hw. pose proof high_facts as (F1 & F2 & _ & _ & _ & _ & _ & _ & F9 & F10 & _).
pose proof map_facts as (M1 & M2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _). pose proof map_zoneN as MZ. pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & _).
pose proof Hidx as HI. pose proof Nrange as NR. pose proof BSLv_range as HB. pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7). pose proof (lo_stk_ceil ly LY) as SC.
destruct Hsp as (S1 & _ & S3 & _). destruct Hmap_apart as (MT & _ & _ & MQ & _). unfold zdisjoint in MT, MQ. cbn [fst snd] in MT, MQ.
clear - Ha Hw F1 F2 F9 F10 M1 M2 SM1 SM2 Z8 HI NR HB T7 SC S1 S3 MT MQ MZ.
ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, WIN1S, WIN1P, WINT, WINI, QSv, kHighMemBeg, kHighShadowBeg, kHighShadowEnd, ASAN_CEIL, kThreadObjSize, kPtrArrayResv, kMaxNumChunks, MALLOC_MAX, ASTACK, IFRAME, t_unwinding, TFX_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex in *. unfold T, Qb in *. zlia.
Qed.
Lemma runs_not_stack : forall a, (mb + 6144 <= a < mb + MSv) \/ (SMv <= a < SMv + MSv / 8) -> ~ (sp0 - ASTACK <= a < sp0).
Proof.
intros a Ha Hs. pose proof map_facts as (M1 & M2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _). pose proof map_zoneN as MZ.
pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7). destruct Hsp as (S1 & _ & S3 & _).
destruct Hmap_apart as (_ & _ & _ & _ & _ & _ & MS). unfold zdisjoint in MS. cbn [fst snd] in MS.
clear - Ha Hs M1 M2 SM1 SM2 T7 S1 S3 MS MZ. ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighShadowBeg, kHighShadowEnd, ASAN_CEIL, ASTACK in *. zlia.
Qed.
Lemma PS_stable : forall Wy sh, Forall run_ok sh -> pstable WIN1S (PS Wy sh).
Proof.
intros Wy sh Hsh m m' FR (HB & HM & HSH & HR).
assert (U : forall a, (mb + 6144 <= a < mb + MSv) \/ (SMv <= a < SMv + MSv / 8) -> m' (w64 a) = m (w64 a)).
{ intros a Ha. pose proof map_facts as (M1 & M2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _). pose proof map_zoneN as MZ.
img_apply FR. unfold w64. rewrite unsigned_lit_small by (img_try (clear - Ha M1 M2 SM1 SM2 MZ; ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighShadowBeg, kHighShadowEnd, ASAN_CEIL in *; zlia)).
img_exact (runs_not_WIN1S a Ha). }
split; [img_try (img_exact (PBUFW_stableT Wy m m' (fun x Hx => FR x (fun Hw => Hx (WIN1S_WIN1T _ Hw))) HB))|].
split; [img_try (intros a Ha; img_apply (apresent_same (w_H Wy) m); [img_exact (U a (or_introl Ha)) | img_exact (HM a Ha)])|].
split; [img_try (intros a Ha; img_apply (apresent_same (w_H Wy) m); [img_exact (U a (or_intror Ha)) | img_exact (HSH a Ha)])|].
img_apply Forall_forall. intros r Hr a Ha. pose proof (proj1 (Forall_forall _ _) Hsh r Hr) as OK. pose proof (proj1 (Forall_forall _ _) HR r Hr a Ha) as V.
rewrite (U a); [img_try (img_exact V)|]. unfold run_ok in OK. clear - OK Ha. zlia.
Qed.
Definition cut1 (d e : Z) (r : Z * Z * Z) : list (Z * Z * Z) :=
let lo := fst (fst r) in let hi := snd (fst r) in let v := snd r in
(if lo <? d then [(lo, Z.min hi d, v)] else []) ++ (if e <? hi then [(Z.max lo e, hi, v)] else []).
Definition cut (d e : Z) (sh : list (Z * Z * Z)) : list (Z * Z * Z) := flat_map (cut1 d e) sh.
Lemma cut_sound : forall m m' d e sh,
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < e) -> m' (w64 a) = m (w64 a)) -> Forall run_ok sh -> Forall (brun m) sh -> Forall (brun m') (cut d e sh).
Proof.
intros m m' d e sh FR OK H. pose proof map_facts as (M1 & M2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _). pose proof map_zoneN as MZ.
unfold cut. img_apply Forall_flat_map. img_apply Forall_forall. intros r Hr.
pose proof (proj1 (Forall_forall _ _) H r Hr) as BR. pose proof (proj1 (Forall_forall _ _) OK r Hr) as RO. unfold run_ok in RO.
unfold cut1. destruct r as [[lo hi] v]. cbn [fst snd] in *.
assert (A64 : forall a, lo <= a < hi -> 0 <= a < 2 ^ 64) by (img_try (intros a Ha; clear - Ha RO M1 M2 SM1 SM2 MZ; ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighShadowBeg, kHighShadowEnd, ASAN_CEIL in *; zlia)).
clear M1 M2 SM1 SM2 RO. img_apply Forall_app. split.
- destruct (lo <? d) eqn:E1; [|img_try (img_apply Forall_nil)]. apply Z.ltb_lt in E1. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
intros a Ha. cbn [fst snd] in Ha. rewrite FR by (img_try (try img_apply A64; zlia)). img_apply BR. cbn [fst snd]. zlia.
- destruct (e <? hi) eqn:E2; [|img_try (img_apply Forall_nil)]. apply Z.ltb_lt in E2. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
intros a Ha. cbn [fst snd] in Ha. rewrite FR by (img_try (try img_apply A64; zlia)). img_apply BR. cbn [fst snd]. zlia.
Qed.
Lemma cut_ok : forall d e sh, Forall run_ok sh -> Forall run_ok (cut d e sh).
Proof.
clearP. intros d e sh H. unfold cut. img_apply Forall_flat_map. img_apply Forall_forall. intros r Hr.
pose proof (proj1 (Forall_forall _ _) H r Hr) as OK. unfold cut1, run_ok in *. destruct r as [[lo hi] v]. cbn [fst snd] in *.
img_apply Forall_app. split.
- destruct (lo <? d) eqn:E1; [|img_try (img_apply Forall_nil)]. apply Z.ltb_lt in E1. img_apply Forall_cons; [img_try (cbn [fst snd]; zlia) | img_try (img_apply Forall_nil)].
- destruct (e <? hi) eqn:E2; [|img_try (img_apply Forall_nil)]. apply Z.ltb_lt in E2. img_apply Forall_cons; [img_try (cbn [fst snd]; zlia) | img_try (img_apply Forall_nil)].
Qed.
Lemma at_S_memsetS : forall (Wy : world tfxsegs) md X sh ss W' c' (k : nat) (ed el : sv) (d len vb retpc : Z),
at_S Wy md X (PS Wy sh) ss W' c' -> ss_resv ss = None -> ss_pc ss = tfx_A_musl_memset -> (sHAV <= k)%nat ->
ss_atoms_lt k ss = true -> no_cdata (ss_mem ss) = true ->
sr_get (ss_regs ss) 10%bv = ed -> sr_get (ss_regs ss) 12%bv = el -> sr_get (ss_regs ss) 11%bv = SLit vb -> sr_get (ss_regs ss) 1%bv = SLit retpc ->
sv_atoms_lt sHAV ed = true -> sv_atoms_lt sHAV el = true -> U E0 ed = d -> U E0 el = len ->
0 <= len -> retpc mod 4 = 0 -> 0 <= retpc < 2 ^ 64 -> 0 <= vb < 256 ->
((mb + 6144 <= d /\ d + len <= mb + MSv) \/ (SMv <= d /\ d + len <= SMv + MSv / 8)) -> Forall run_ok sh ->
(forall a, d <= a < d + len -> X a) ->
(forall (E' : env), env_agree sHAV E0 E' ->
forall r, In r (ss_mem ss) -> base_val E' (YQ0b.r_base r) + YQ0b.r_hi r <= d \/ d + len <= base_val E' (YQ0b.r_base r) + YQ0b.r_lo r
\/ YQ0b.r_hi r <= YQ0b.r_lo r) ->
(forall (E' : env), env_agree sHAV E0 E' ->
forall r a, In r (ss_mem ss) -> base_val E' (YQ0b.r_base r) + YQ0b.r_lo r <= a < base_val E' (YQ0b.r_base r) + YQ0b.r_hi r -> 0 <= a < 2 ^ 64) ->
SRr tfxsegs W' c' (at_S Wy md X (PS Wy ((d, d + len, vb) :: cut d (d + len) sh)) (ss_after_stretch ss (ss_mem ss) k CLOB_MS retpc)).
Proof.
intros Wy md X sh ss W' c' k ed el d len vb retpc HR Hrv Hpc Hk Hat Hnc H10 H12 H11 H1 Aed Ael Ud Ul Hlen Hrpc Hrpc' Hvb Hplace Hsh HX HEXT H64.
pose proof map_facts as (M1 & M2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _). pose proof map_zoneN as MZ.
assert (Hd : TFX_IMG_END <= d /\ d + len < 2 ^ 64) by (img_try (clear - Hplace Hlen M1 M2 SM1 SM2 MZ; ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END, kHighMemBeg, kHighShadowBeg, kHighShadowEnd, ASAN_CEIL in *; zlia)).
eapply (SRr_mono tfxsegs W' c' _ _
(at_S_memset Wy md X (PS Wy sh) (PS Wy ((d, d + len, vb) :: cut d (d + len) sh)) ss W' c' k ed el d len vb retpc HR Hrv Hpc Hk Hat Hnc H10 H12 H11 H1 Aed Ael Ud Ul
Hlen (proj1 Hd) (proj2 Hd) Hrpc Hrpc' Hvb _ HEXT H64 _)).
{ intros W2 c2 _ HA. eapply at_S_weaken; [img_try (img_exact HA) | img_try (intros a [Ha|Ha]; [img_exact Ha | img_exact (HX a Ha)]) | img_try (intros m Hm; img_exact Hm)]. }
Unshelve.
- intros m MEQ (HB & HM & HSH & HRs) a Ha. destruct Hplace as [[P1 P2]|[P1 P2]]; [img_try (img_apply HM; zlia) | img_try (img_apply HSH; zlia)].
- intros m m' MEQ (HB & HM & HSH & HRs) FR FILL.
assert (FR' : forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + len) -> m' (w64 a) = m (w64 a)).
{ intros a Ha Hna. img_apply FR. unfold w64. rewrite unsigned_lit_small by img_exact Ha. img_exact Hna. }
assert (FILL' : forall a, d <= a < d + len -> m' (w64 a) = Some (Z_to_bv 8 vb)).
{ intros a Ha. img_apply FILL. unfold w64. rewrite unsigned_lit_small by (img_try (clear - Ha Hd Hplace M1 SM1 MZ; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END, kHighMemBeg, kHighShadowBeg in *; zlia)). img_exact Ha. }
assert (RP : forall a, (mb + 6144 <= a < mb + MSv) \/ (SMv <= a < SMv + MSv / 8) -> apresent (w_H Wy) m a -> apresent (w_H Wy) m' a).
{ intros a Hrng [Hh [b Hb]]. split; [img_try (img_exact Hh)|].
assert (A64 : 0 <= a < 2 ^ 64) by (img_try (clear - Hrng M1 M2 SM1 SM2 MZ; ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighShadowBeg, kHighShadowEnd, ASAN_CEIL in *; zlia)).
destruct (Z_lt_le_dec a d) as [L|GE].
- exists b. img_exact (eq_trans (FR' a A64 ltac:(img_try (zlia))) Hb).
- destruct (Z_lt_le_dec a (d + len)) as [L2|GE2]; [img_try (exists (Z_to_bv 8 vb); img_exact (FILL' a ltac:(zlia))) | img_try (exists b; img_exact (eq_trans (FR' a A64 ltac:(zlia)) Hb))]. }
split; [|img_try (split; [|split])].
+ intros i Hi. eapply val_mem_frame; [|img_try (img_exact (HB i Hi))]. intros kk Hkk. pose proof tr_length as LEN.
pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7). destruct Hsp as (S1 & _ & S3 & _). pose proof (u64_range (getr regs0 2)) as U2.
img_apply FR'; [img_try (clear - Hi Hkk LEN T7 S1 S3 U2 MZ; unfold zone3, TFX_IMG_LO, kLowShadowBeg, IFRAME, ASTACK, kHighMemBeg in *; unfold sp0 in *; zlia)|]. intros Hin.
img_apply (runs_not_stack (sp0 - IFRAME + 16 + 8 * Z.of_nat i + Z.of_nat kk)); [img_try (clear - Hin Hplace MZ; zlia) | img_try (clear - Hi Hkk LEN MZ; unfold IFRAME, ASTACK; zlia)].
+ intros a Ha. img_apply RP; [img_try (left; img_exact Ha) | img_try (img_exact (HM a Ha))].
+ intros a Ha. img_apply RP; [img_try (right; img_exact Ha) | img_try (img_exact (HSH a Ha))].
+ img_apply Forall_cons; [img_try (intros a Ha; cbn [fst snd] in Ha; img_exact (FILL' a Ha)) | img_try (img_exact (cut_sound m m' d (d + len) sh FR' Hsh HRs))].
Qed.
Definition skel_okb {imgk : img} (pb : bool) (s : option nat * Z * Z * Z * Z) : bool :=
match s with (b, lo, hi, _, _) =>
match b with
| None => (0 <=? lo) && (hi <=? (0x5ff000 + D_1000))
| Some k => (Nat.eqb k 2 && (- ASTACK <=? lo) && (hi <=? 0))
|| (Nat.eqb k 32 && (0 <=? lo) && (hi <=? kThreadObjSize))
|| (Nat.eqb k 33 && (0 <=? lo) && (hi <=? 256))
|| (Nat.eqb k aMAP && (0 <=? lo) && (hi <=? 6144))
|| (Nat.eqb k aQS && (0 <=? lo) && (hi <=? 8))
|| (Nat.eqb k aBSL && (0 <=? lo) && (hi <=? 8))
|| (pb && Nat.eqb k aPBS && (0 <=? lo) && (hi <=? 1))
end
end.
Lemma skel_cases : forall pb b lo hi wlo whi, skel_okb pb (b, lo, hi, wlo, whi) = true ->
(b = None /\ 0 <= lo /\ hi <= (0x5ff000 + D_1000)) \/ (b = Some 2%nat /\ - ASTACK <= lo /\ hi <= 0) \/ (b = Some 32%nat /\ 0 <= lo /\ hi <= kThreadObjSize) \/
(b = Some 33%nat /\ 0 <= lo /\ hi <= 256) \/ (b = Some aMAP /\ 0 <= lo /\ hi <= 6144) \/ (b = Some aQS /\ 0 <= lo /\ hi <= 8) \/
(b = Some aBSL /\ 0 <= lo /\ hi <= 8) \/ (pb = true /\ b = Some aPBS /\ 0 <= lo /\ hi <= 1).
Proof.
clearP. intros pb b lo hi wlo whi H. unfold skel_okb in H. destruct b as [k|].
- repeat (apply Bool.orb_prop in H; destruct H as [H|H]);
repeat (apply andb_prop in H; destruct H as [H ?HH]);
repeat match goal with X : (_ <=? _) = true |- _ => apply Z.leb_le in X | X : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in X; subst end.
all: first [ right; left; repeat split; assumption | right; right; left; repeat split; assumption | right; right; right; left; repeat split; assumption
| right; right; right; right; left; repeat split; assumption | right; right; right; right; right; left; repeat split; assumption
| right; right; right; right; right; right; left; repeat split; assumption
| right; right; right; right; right; right; right; repeat split; assumption ].
- apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. left. repeat split; assumption.
Qed.
Lemma skel_apart : forall (E' : env) (pb : bool) d len, env_agree sHAV E0 E' ->
((mb + 6144 <= d /\ d + len <= mb + MSv) \/ (SMv <= d /\ d + len <= SMv + MSv / 8)) ->
(pb = true -> d + len <= PBv \/ PBv + 1 <= d) ->
forall r, skel_okb pb (skel r) = true ->
base_val E' (YQ0b.r_base r) + YQ0b.r_hi r <= d \/ d + len <= base_val E' (YQ0b.r_base r) + YQ0b.r_lo r \/ YQ0b.r_hi r <= YQ0b.r_lo r.
Proof.
intros E' pb d len [HE _] Hplace Hpb r Hs. destruct r as [b lo hi wlo whi cs]. unfold skel in Hs. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi] in *.
pose proof high_facts as (F1 & F2 & _ & _ & _ & _ & F7 & F8 & F9 & F10 & _).
pose proof map_facts as (M1 & M2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _ & PB & _). pose proof map_zoneN as MZ. pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & _).
pose proof Hidx as HI. pose proof Nrange as NR. pose proof BSLv_range as HB. pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7). pose proof (lo_stk_ceil ly LY) as SC.
destruct Hsp as (S1 & _ & S3 & _). destruct Hmap_apart as (MT & MC & _ & MQ & _ & _ & MS). unfold zdisjoint in MT, MC, MQ, MS. cbn [fst snd] in MT, MC, MQ, MS.
pose proof (u64_range (getr regs0 2)) as U2.
destruct (Z_le_gt_dec hi lo) as [Hemp|Hne]; [img_try (right; right; img_exact Hemp)|].
destruct (skel_cases pb b lo hi wlo whi Hs) as [(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|(Epb & -> & A1 & A2)]]]]]]]; cbn [base_val].
- clear - Hplace A1 A2 M1 SM1 MZ. unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighShadowBeg in *. zlia.
- rewrite (HE 2%nat ltac:(img_try (unfold sHAV; zlia))), E2. pose proof (runs_not_stack) as RS.
destruct Hplace as [[P1 P2]|[P1 P2]].
+ clear - P1 P2 A1 A2 MS S1 S3 Hne U2 Z8 MZ. unfold ASTACK in *. unfold sp0 in *. destruct MS as [MS|MS]; [img_try (right; left; zlia) | img_try (left; zlia)].
+ right; left. clear - P1 P2 A1 A2 SM1 SM2 T7 S1 U2 MZ. unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighShadowEnd, kHighMemBeg, ASTACK in *. unfold sp0 in *. zlia.
- rewrite (HE 32%nat ltac:(img_try (unfold sHAV; zlia))), EaT. unfold w64. rewrite unsigned_lit_small by (img_try (clear - F1 F2 MZ; numconst; try unfold T in *; zlia)).
clear - Hplace A1 A2 MT F1 F2 M1 M2 SM1 SM2 Hne MZ. ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighShadowBeg, kHighShadowEnd, ASAN_CEIL, kThreadObjSize in *. try unfold T in *.
destruct Hplace as [[P1 P2]|[P1 P2]]; [img_try (destruct MT as [MT|MT]; [right; left; zlia | left; zlia]) | img_try (zlia) ].
- rewrite (HE 33%nat ltac:(img_try (unfold sHAV; zlia))), EaC. unfold w64. rewrite unsigned_lit_small by (img_try (clear - F7 F8 MZ; ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; zlia)).
clear - Hplace A1 A2 MC F7 F8 M1 M2 SM1 SM2 Hne MZ. ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighShadowBeg, kHighShadowEnd, ASAN_CEIL, kCtxMapSize in *.
destruct Hplace as [[P1 P2]|[P1 P2]]; [img_try (destruct MC as [MC|MC]; [right; left; zlia | left; zlia]) | img_try (zlia) ].
- unfold aMAP. rewrite (HE 45%nat ltac:(img_try (unfold sHAV; zlia))), EaMAP. unfold w64. rewrite unsigned_lit_small by (img_try (clear - M1 M2 Z8 MZ; ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; zlia)).
clear - Hplace A1 A2 M1 M2 SM1 SM2 Z8 Hne MZ. ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighShadowBeg, kHighShadowEnd, ASAN_CEIL in *. zlia.
- unfold aQS. rewrite (HE 52%nat ltac:(img_try (unfold sHAV; zlia))), EaQS. unfold w64. unfold QSv in *. rewrite unsigned_lit_small by (img_try (clear - F9 F10 HI MZ; ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kPtrArrayResv, kMaxNumChunks in *; try unfold Qb in *; zlia)).
clear - Hplace A1 A2 MQ F9 F10 HI M1 M2 SM1 SM2 Hne MZ. ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighShadowBeg, kHighShadowEnd, ASAN_CEIL, kPtrArrayResv, kMaxNumChunks in *. try unfold Qb in *.
destruct Hplace as [[P1 P2]|[P1 P2]]; [img_try (destruct MQ as [MQ|MQ]; [right; left; zlia | left; zlia]) | img_try (zlia) ].
- unfold aBSL. rewrite (HE 55%nat ltac:(img_try (unfold sHAV; zlia))), EaBSL. unfold w64. rewrite unsigned_lit_small by (img_try (clear - HB MZ; unfold TFX_INST in *; zlia)).
clear - Hplace A1 A2 HB M1 SM1 Hne MZ. unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighShadowBeg, TFX_INST in *. zlia.
- unfold aPBS. rewrite (HE 66%nat ltac:(img_try (unfold sHAV; zlia))), EaPB. unfold w64. rewrite PB in *.
pose proof size_facts as (_ & _ & Z3 & Z4 & _ & _ & Z7 & _ & _ & Z10 & _).
assert (HND : 8 * (N8D / 8) <= N8D) by (img_try (img_apply Z.mul_div_le; zlia)). assert (HM : N8D / 8 + 1024 <= MSv / 8) by (img_try (img_apply Z.div_le_lower_bound; zlia)).
pose proof (Z.div_pos N8D 8 ltac:(img_try (zlia)) ltac:(img_try (zlia))) as DP.
rewrite unsigned_lit_small by (img_try (clear - SM1 SM2 HND HM DP MZ; unfold kHighShadowBeg, kHighShadowEnd in *; zlia)).
specialize (Hpb Epb). clear - Hplace Hpb A1 A2 M1 M2 SM1 SM2 HND HM DP Hne MZ. ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighShadowBeg, kHighShadowEnd, ASAN_CEIL in *. zlia.
Qed.
Lemma skel_u64 : forall (E' : env) (pb : bool) r a, env_agree sHAV E0 E' -> skel_okb pb (skel r) = true ->
base_val E' (YQ0b.r_base r) + YQ0b.r_lo r <= a < base_val E' (YQ0b.r_base r) + YQ0b.r_hi r -> 0 <= a < 2 ^ 64.
Proof.
intros E' pb r a [HE _] Hs Ha. destruct r as [b lo hi wlo whi cs]. unfold skel in Hs. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi] in *.
pose proof high_facts as (F1 & F2 & _ & _ & _ & _ & F7 & F8 & F9 & F10 & _).
pose proof map_facts as (M1 & M2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _ & PB & _). pose proof map_zoneN as MZ. pose proof size_facts as (_ & _ & Z3 & Z4 & _ & _ & Z7 & Z8 & _ & Z10 & _).
pose proof Hidx as HI. pose proof Nrange as NR. pose proof BSLv_range as HB. pose proof (lo_top ly LY) as (_ & _ & _ & T4 & _ & _ & T7).
destruct Hsp as (S1 & _ & S3 & _). pose proof (u64_range (getr regs0 2)) as U2.
destruct (skel_cases pb b lo hi wlo whi Hs) as [(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|(Epb & -> & A1 & A2)]]]]]]]; cbn [base_val] in Ha.
- clear - Ha A1 A2 MZ. zlia.
- rewrite (HE 2%nat ltac:(img_try (unfold sHAV; zlia))), E2 in Ha. clear - Ha A1 A2 S1 S3 T4 T7 U2 MZ. unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASTACK in *. unfold sp0 in *. zlia.
- rewrite (HE 32%nat ltac:(img_try (unfold sHAV; zlia))), EaT in Ha. unfold w64 in Ha. rewrite unsigned_lit_small in Ha by (img_try (clear - F1 F2 MZ; numconst; try unfold T in *; zlia)).
clear - Ha A1 A2 F1 F2 MZ. ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize in *. try unfold T in *. zlia.
- rewrite (HE 33%nat ltac:(img_try (unfold sHAV; zlia))), EaC in Ha. unfold w64 in Ha. rewrite unsigned_lit_small in Ha by (img_try (clear - F7 F8 MZ; ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; zlia)).
clear - Ha A1 A2 F7 F8 MZ. ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. zlia.
- unfold aMAP in Ha. rewrite (HE 45%nat ltac:(img_try (unfold sHAV; zlia))), EaMAP in Ha. unfold w64 in Ha. rewrite unsigned_lit_small in Ha by (img_try (clear - M1 M2 Z8 MZ; ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; zlia)).
clear - Ha A1 A2 M1 M2 Z8 MZ. ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. zlia.
- unfold aQS in Ha. rewrite (HE 52%nat ltac:(img_try (unfold sHAV; zlia))), EaQS in Ha. unfold w64 in Ha. unfold QSv in *. rewrite unsigned_lit_small in Ha by (img_try (clear - F9 F10 HI MZ; ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kPtrArrayResv, kMaxNumChunks in *; try unfold Qb in *; zlia)).
clear - Ha A1 A2 F9 F10 HI MZ. ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kPtrArrayResv, kMaxNumChunks in *. try unfold Qb in *. zlia.
- unfold aBSL in Ha. rewrite (HE 55%nat ltac:(img_try (unfold sHAV; zlia))), EaBSL in Ha. unfold w64 in Ha. rewrite unsigned_lit_small in Ha by (img_try (clear - HB MZ; unfold TFX_INST in *; zlia)).
clear - Ha A1 A2 HB MZ. unfold TFX_INST in *. zlia.
- unfold aPBS in Ha. rewrite (HE 66%nat ltac:(img_try (unfold sHAV; zlia))), EaPB in Ha. unfold w64 in Ha. rewrite PB in Ha.
assert (HND : 8 * (N8D / 8) <= N8D) by (img_try (img_apply Z.mul_div_le; zlia)). assert (HM : N8D / 8 + 1024 <= MSv / 8) by (img_try (img_apply Z.div_le_lower_bound; zlia)).
pose proof (Z.div_pos N8D 8 ltac:(img_try (zlia)) ltac:(img_try (zlia))) as DP.
rewrite unsigned_lit_small in Ha by (img_try (clear - SM1 SM2 HND HM DP MZ; unfold kHighShadowBeg, kHighShadowEnd in *; zlia)).
clear - Ha A1 A2 SM1 SM2 HND HM DP MZ. unfold kHighShadowBeg, kHighShadowEnd in *. zlia.
Qed.
Lemma memset_ext_of_skel : forall (pb : bool) d len ss,
forallb (fun r => skel_okb pb (skel r)) (ss_mem ss) = true ->
((mb + 6144 <= d /\ d + len <= mb + MSv) \/ (SMv <= d /\ d + len <= SMv + MSv / 8)) ->
(pb = true -> d + len <= PBv \/ PBv + 1 <= d) ->
forall (E' : env), env_agree sHAV E0 E' ->
forall r, In r (ss_mem ss) -> base_val E' (YQ0b.r_base r) + YQ0b.r_hi r <= d \/ d + len <= base_val E' (YQ0b.r_base r) + YQ0b.r_lo r
\/ YQ0b.r_hi r <= YQ0b.r_lo r.
Proof. intros pb d len ss Hb Hplace Hpb E' HE r Hr. img_exact (skel_apart E' pb d len HE Hplace Hpb r (proj1 (forallb_forall _ _) Hb r Hr)). Qed.
Lemma memset_u64_of_skel : forall (pb : bool) ss,
forallb (fun r => skel_okb pb (skel r)) (ss_mem ss) = true ->
forall (E' : env), env_agree sHAV E0 E' ->
forall r a, In r (ss_mem ss) -> base_val E' (YQ0b.r_base r) + YQ0b.r_lo r <= a < base_val E' (YQ0b.r_base r) + YQ0b.r_hi r -> 0 <= a < 2 ^ 64.
Proof. intros pb ss Hb E' HE r a Hr Ha. img_exact (skel_u64 E' pb r a HE (proj1 (forallb_forall _ _) Hb r Hr) Ha). Qed.
Definition WIN1R (a : Z) : Prop := WIN1P a \/ (mb <= a < mb + 6144).
Definition WSKEL1R {imgk : img} : list (option nat * Z * Z) := WSKEL1P ++ [(Some aMAP, 0, 6144)].
Lemma WIN1R_WIN1S : forall a, WIN1R a -> WIN1S a.
Proof. clearP. intros a [H|H]; [img_try (left) | img_try (right; right)]; img_exact H. Qed.
Lemma WIN1R_WIN : forall a, WIN1R a -> WIN a.
Proof. intros a H. img_exact (WIN1S_WIN a (WIN1R_WIN1S a H)). Qed.
Lemma windows_WIN1R : forall (E : env) rs a,
(forall k, (k < sHAV)%nat -> ew E k = ew E0 k) -> wins_ok WSKEL1R rs = true -> in_wrange E rs a -> WIN1R a.
Proof.
intros E rs a HE. img_apply windows_in. intros t x Ht Hx. unfold WSKEL1R in Ht. apply in_app_iff in Ht as [Ht|Ht].
- left. img_exact (WSKEL1P_WIN1P E x t HE Ht Hx).
- right. pose proof map_facts as (M1 & M2 & _). pose proof map_zoneN as MZ. pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & _).
unfold in_win in Hx. cbn [In] in Ht. ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, sHAV, aMAP in *. clear - HE Hx Ht M1 M2 Z8 MZ.
destruct Ht as [<-|[]]; cbn [fst snd base_val] in Hx; rewrite HE in Hx by zlia.
rewrite EaMAP in Hx. unfold w64 in Hx. rewrite unsigned_lit_small in Hx by zlia. zlia.
Qed.
Lemma mid_not_WIN1R : forall a, sp0 - IFRAME <= a < sp0 - 64 -> ~ WIN1R a.
Proof. intros a Ha Hw. img_exact (mid_not_WIN1S a Ha (WIN1R_WIN1S a Hw)). Qed.
Lemma at_S_runR : forall (Wx : world tfxsegs) tbl (tblok : table_ok tfxsegs tbl) stop md X P ss ss' st W' c',
at_S Wx md X P ss W' c' ->
sym_run_toN_sh tfxsegs tbl FUEL stop ss = (ss', st) -> match st with RS_ecall => False | _ => True end ->
(forall a, WIN1R a -> X a) -> wins_ok WSKEL1R (ss_mem ss) = true -> pstable WIN1R P -> stack_shaped ss' = true ->
SRr tfxsegs W' c' (at_S Wx md X P ss').
Proof. img_exact (at_S_run_gen WSKEL1R WIN1R windows_WIN1R mid_not_WIN1R). Qed.
Lemma at_S_run_ecallR : forall (Wx : world tfxsegs) tbl (tblok : table_ok tfxsegs tbl) stop md X P ss ss' W' c',
at_S Wx md X P ss W' c' ->
sym_run_toN_sh tfxsegs tbl FUEL stop ss = (ss', RS_ecall) -> ss_resv ss' = None ->
(forall a, WIN1R a -> X a) -> wins_ok WSKEL1R (ss_mem ss) = true -> pstable WIN1R P -> stack_shaped ss' = true ->
SRr tfxsegs W' c' (at_N Wx md X P ss').
Proof. img_exact (at_S_run_ecall_gen WSKEL1R WIN1R windows_WIN1R mid_not_WIN1R). Qed.
Definition PSR (Wy : world tfxsegs) (sh : list (Z * Z * Z)) (R : (word -> option byte) -> Prop) (m : word -> option byte) : Prop := PS Wy sh m /\ R m.
Definition rstable (R : (word -> option byte) -> Prop) : Prop :=
pstable WIN1R R /\
(forall (m m' : word -> option byte) d len, ((mb + 6144 <= d /\ d + len <= mb + MSv) \/ (SMv <= d /\ d + len <= SMv + MSv / 8)) ->
(forall x : word, ~ (d <= bv_unsigned x < d + len) -> m' x = m x) -> R m -> R m').
Lemma rstable_true : rstable (fun _ => True).
Proof. clearP. split; [img_try (intros m m' _ _; img_exact I) | img_try (intros m m' d len _ _ _; img_exact I)]. Qed.
Lemma PSR_stable : forall Wy sh R, Forall run_ok sh -> rstable R -> pstable WIN1R (PSR Wy sh R).
Proof.
intros Wy sh R OK [RF _] m m' FR [HP HQ]. split.
- img_exact (PS_stable Wy sh OK m m' (fun x Hx => FR x (fun Hw => Hx (WIN1R_WIN1S _ Hw))) HP).
- img_exact (RF m m' FR HQ).
Qed.
Definition QSP (Wy : world tfxsegs) (m : word -> option byte) : Prop := forall a, QSv <= a < QSv + 8 -> apresent (w_H Wy) m a.
Lemma QS_not_WIN1R : forall a, QSv <= a < QSv + 8 -> ~ WIN1R a.
Proof.
intros a Ha Hw. pose proof high_facts as (F1 & F2 & _ & _ & _ & _ & _ & _ & F9 & F10 & _ & _ & _ & _ & F15).
pose proof map_facts as (M1 & M2 & _). pose proof map_zoneN as MZ. pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & _). pose proof Hidx as HI.
pose proof BSLv_range as HB. destruct Hsp as (S1 & _ & S3 & _).
destruct Hmap_apart as (_ & _ & _ & MQ & _). pose proof HCX as (_ & _ & QT & _). unfold zdisjoint in MQ, QT. cbn [fst snd] in MQ, QT.
ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, QSv, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kPtrArrayResv, kMaxNumChunks in *. unfold Qb in *.
destruct Hw as [[Hs|[Hs|[Ht|Hi]]]|Hm].
- destruct (F15 a) as (_ & _ & N3 & _); [img_try (clear - Hs S1 S3 MZ; unfold ASTACK, IFRAME in *; zlia) | img_try (clear - N3 Ha HI MZ; zlia)].
- destruct (F15 a) as (_ & _ & N3 & _); [img_try (clear - Hs S1 S3 MZ; unfold ASTACK, IFRAME in *; zlia) | img_try (clear - N3 Ha HI MZ; zlia)].
- clear - Ht Ha HI QT MZ. unfold WINT, t_unwinding in *. try unfold T in *. zlia.
- clear - Hi Ha HI HB F9 MZ. unfold WINI, TFX_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex in *. zlia.
- clear - Hm Ha HI MQ Z8 MZ. zlia.
Qed.
Lemma QSP_rstable : forall Wy, rstable (QSP Wy).
Proof.
intros Wy. pose proof high_facts as (_ & _ & _ & _ & _ & _ & _ & _ & F9 & F10 & _). pose proof Hidx as HI.
pose proof map_facts as (M1 & M2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _). pose proof map_zoneN as MZ. pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & _).
destruct Hmap_apart as (_ & _ & _ & MQ & _). unfold zdisjoint in MQ. cbn [fst snd] in MQ.
assert (U64 : forall a, QSv <= a < QSv + 8 -> bv_unsigned (Z_to_bv 64 a) = a).
{ intros a Ha. img_apply unsigned_lit_small. clear - Ha F9 F10 HI MZ. ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, QSv, kHighMemBeg, ASAN_CEIL, kPtrArrayResv, kMaxNumChunks in *. try unfold Qb in *. zlia. }
split.
- intros m m' FR HQ a Ha. img_apply (apresent_same (w_H Wy) m); [|img_try (img_exact (HQ a Ha))]. img_apply FR. rewrite (U64 a Ha). img_exact (QS_not_WIN1R a Ha).
- intros m m' d len Hplace FR HQ a Ha. img_apply (apresent_same (w_H Wy) m); [|img_try (img_exact (HQ a Ha))]. img_apply FR. rewrite (U64 a Ha). intros Hin.
clear - Ha Hin Hplace MQ HI F9 F10 M1 SM1 SM2 Z8 MZ. ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, QSv, kHighMemBeg, kHighShadowBeg, kHighShadowEnd, ASAN_CEIL, kPtrArrayResv, kMaxNumChunks in *. try unfold Qb in *. zlia.
Qed.
Lemma at_S_memsetSR : forall (Wy : world tfxsegs) md X sh R ss W' c' (k : nat) (ed el : sv) (d len vb retpc : Z),
at_S Wy md X (PSR Wy sh R) ss W' c' -> rstable R -> ss_resv ss = None -> ss_pc ss = tfx_A_musl_memset -> (sHAV <= k)%nat ->
ss_atoms_lt k ss = true -> no_cdata (ss_mem ss) = true ->
sr_get (ss_regs ss) 10%bv = ed -> sr_get (ss_regs ss) 12%bv = el -> sr_get (ss_regs ss) 11%bv = SLit vb -> sr_get (ss_regs ss) 1%bv = SLit retpc ->
sv_atoms_lt sHAV ed = true -> sv_atoms_lt sHAV el = true -> U E0 ed = d -> U E0 el = len ->
0 <= len -> retpc mod 4 = 0 -> 0 <= retpc < 2 ^ 64 -> 0 <= vb < 256 ->
((mb + 6144 <= d /\ d + len <= mb + MSv) \/ (SMv <= d /\ d + len <= SMv + MSv / 8)) -> Forall run_ok sh ->
(forall a, d <= a < d + len -> X a) ->
(forall (E' : env), env_agree sHAV E0 E' ->
forall r, In r (ss_mem ss) -> base_val E' (YQ0b.r_base r) + YQ0b.r_hi r <= d \/ d + len <= base_val E' (YQ0b.r_base r) + YQ0b.r_lo r
\/ YQ0b.r_hi r <= YQ0b.r_lo r) ->
(forall (E' : env), env_agree sHAV E0 E' ->
forall r a, In r (ss_mem ss) -> base_val E' (YQ0b.r_base r) + YQ0b.r_lo r <= a < base_val E' (YQ0b.r_base r) + YQ0b.r_hi r -> 0 <= a < 2 ^ 64) ->
SRr tfxsegs W' c' (at_S Wy md X (PSR Wy ((d, d + len, vb) :: cut d (d + len) sh) R) (ss_after_stretch ss (ss_mem ss) k CLOB_MS retpc)).
Proof.
intros Wy md X sh R ss W' c' k ed el d len vb retpc HR [_ RM] Hrv Hpc Hk Hat Hnc H10 H12 H11 H1 Aed Ael Ud Ul Hlen Hrpc Hrpc' Hvb Hplace Hsh HX HEXT H64.
pose proof map_facts as (M1 & M2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _). pose proof map_zoneN as MZ.
assert (Hd : TFX_IMG_END <= d /\ d + len < 2 ^ 64) by (img_try (clear - Hplace Hlen M1 M2 SM1 SM2 MZ; ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END, kHighMemBeg, kHighShadowBeg, kHighShadowEnd, ASAN_CEIL in *; zlia)).
eapply (SRr_mono tfxsegs W' c' _ _
(at_S_memset Wy md X (PSR Wy sh R) (PSR Wy ((d, d + len, vb) :: cut d (d + len) sh) R) ss W' c' k ed el d len vb retpc HR Hrv Hpc Hk Hat Hnc H10 H12 H11 H1 Aed Ael Ud Ul
Hlen (proj1 Hd) (proj2 Hd) Hrpc Hrpc' Hvb _ HEXT H64 _)).
{ intros W2 c2 _ HA. eapply at_S_weaken; [img_try (img_exact HA) | img_try (intros a [Ha|Ha]; [img_exact Ha | img_exact (HX a Ha)]) | img_try (intros m Hm; img_exact Hm)]. }
Unshelve.
- intros m MEQ [(HB & HM & HSH & HRs) HQ] a Ha. destruct Hplace as [[P1 P2]|[P1 P2]]; [img_try (img_apply HM; zlia) | img_try (img_apply HSH; zlia)].
- intros m m' MEQ [HP HQ] FR FILL. split; [|img_try (img_exact (RM m m' d len Hplace FR HQ))].
assert (FR' : forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + len) -> m' (w64 a) = m (w64 a)).
{ intros a Ha Hna. img_apply FR. unfold w64. rewrite unsigned_lit_small by img_exact Ha. img_exact Hna. }
assert (FILL' : forall a, d <= a < d + len -> m' (w64 a) = Some (Z_to_bv 8 vb)).
{ intros a Ha. img_apply FILL. unfold w64. rewrite unsigned_lit_small by (img_try (clear - Ha Hd Hplace M1 SM1 MZ; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END, kHighMemBeg, kHighShadowBeg in *; zlia)). img_exact Ha. }
destruct HP as (HB & HM & HSH & HRs).
assert (RP : forall a, (mb + 6144 <= a < mb + MSv) \/ (SMv <= a < SMv + MSv / 8) -> apresent (w_H Wy) m a -> apresent (w_H Wy) m' a).
{ intros a Hrng [Hh [b Hb]]. split; [img_try (img_exact Hh)|].
assert (A64 : 0 <= a < 2 ^ 64) by (img_try (clear - Hrng M1 M2 SM1 SM2 MZ; ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighShadowBeg, kHighShadowEnd, ASAN_CEIL in *; zlia)).
destruct (Z_lt_le_dec a d) as [L|GE].
- exists b. img_exact (eq_trans (FR' a A64 ltac:(img_try (zlia))) Hb).
- destruct (Z_lt_le_dec a (d + len)) as [L2|GE2]; [img_try (exists (Z_to_bv 8 vb); img_exact (FILL' a ltac:(zlia))) | img_try (exists b; img_exact (eq_trans (FR' a A64 ltac:(zlia)) Hb))]. }
split; [|img_try (split; [|split])].
+ intros i Hi. eapply val_mem_frame; [|img_try (img_exact (HB i Hi))]. intros kk Hkk. pose proof tr_length as LEN.
pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7). destruct Hsp as (S1 & _ & S3 & _). pose proof (u64_range (getr regs0 2)) as U2.
img_apply FR'; [img_try (clear - Hi Hkk LEN T7 S1 S3 U2 MZ; unfold zone3, TFX_IMG_LO, kLowShadowBeg, IFRAME, ASTACK, kHighMemBeg in *; unfold sp0 in *; zlia)|]. intros Hin.
img_apply (runs_not_stack (sp0 - IFRAME + 16 + 8 * Z.of_nat i + Z.of_nat kk)); [img_try (clear - Hin Hplace MZ; zlia) | img_try (clear - Hi Hkk LEN MZ; unfold IFRAME, ASTACK; zlia)].
+ intros a Ha. img_apply RP; [img_try (left; img_exact Ha) | img_try (img_exact (HM a Ha))].
+ intros a Ha. img_apply RP; [img_try (right; img_exact Ha) | img_try (img_exact (HSH a Ha))].
+ img_apply Forall_cons; [img_try (intros a Ha; cbn [fst snd] in Ha; img_exact (FILL' a Ha)) | img_try (img_exact (cut_sound m m' d (d + len) sh FR' Hsh HRs))].
Qed.
Definition chunk_eqb {imgk : img} (c c' : YQ0b.chunk) : bool :=
Z.eqb (YQ0b.c_off c) (YQ0b.c_off c') &&
match YQ0b.c_val c, YQ0b.c_val c' with
| CVal w v, CVal w' v' => N.eqb w w' && sv_eqb v v'
| CZero l, CZero l' => Z.eqb l l'
| CImg l, CImg l' => Z.eqb l l'
| CData d0 s0 l, CData d1 s1 l' => Nat.eqb d0 d1 && Z.eqb s0 s1 && Z.eqb l l'
| _, _ => false
end.
Lemma chunk_eqb_eq : forall c c', chunk_eqb c c' = true -> c = c'.
Proof.
clearP. intros [o v] [o' v'] H. unfold chunk_eqb in H. cbn [YQ0b.c_off YQ0b.c_val] in H. apply andb_prop in H as [Ho Hv]. apply Z.eqb_eq in Ho. (subst o'; cbv beta).
destruct v as [w x|l|l|d0 s0 l], v' as [w' x'|l'|l'|d1 s1 l']; try discriminate Hv.
- apply andb_prop in Hv as [Hw Hx]. apply N.eqb_eq in Hw. apply sv_eqb_eq in Hx. (subst; cbv beta). img_refl.
- apply Z.eqb_eq in Hv. (subst; cbv beta). img_refl.
- apply Z.eqb_eq in Hv. (subst; cbv beta). img_refl.
- apply andb_prop in Hv as [Hv Hl]. apply andb_prop in Hv as [Hd Hs]. apply Nat.eqb_eq in Hd. apply Z.eqb_eq in Hs. apply Z.eqb_eq in Hl. (subst; cbv beta). img_refl.
Qed.
Definition subregionb {imgk : img} (r' r : YQ0b.region) : bool :=
obase_eqb (YQ0b.r_base r') (YQ0b.r_base r) && (YQ0b.r_lo r <=? YQ0b.r_lo r') && (YQ0b.r_hi r' <=? YQ0b.r_hi r) &&
((YQ0b.r_whi r' <=? YQ0b.r_wlo r') || ((YQ0b.r_wlo r <=? YQ0b.r_wlo r') && (YQ0b.r_whi r' <=? YQ0b.r_whi r))) &&
forallb (fun c => existsb (chunk_eqb c) (YQ0b.r_chunks r)) (YQ0b.r_chunks r').
Lemma subregionb_sound : forall r' r, subregionb r' r = true -> subregion r' r.
Proof.
clearP. intros r' r H. unfold subregionb in H. repeat (apply andb_prop in H; destruct H as [H ?X]).
unfold subregion. split.
{ destruct (YQ0b.r_base r') as [x|], (YQ0b.r_base r) as [y|]; cbn in H; try discriminate H; [img_try (apply Nat.eqb_eq in H; (subst; cbv beta); img_refl) | img_refl]. }
apply Z.leb_le in X2. apply Z.leb_le in X1. split; [img_try (img_exact X2)|]. split; [img_try (img_exact X1)|]. split.
- apply Bool.orb_prop in X0 as [E|E]; [img_try (left; apply Z.leb_le in E; img_exact E) | img_try (right)]. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2. zlia.
- intros c Hc. pose proof (proj1 (forallb_forall _ _) X c Hc) as Y. apply existsb_exists in Y as (c' & Hc' & E). apply chunk_eqb_eq in E. (subst c'; cbv beta). img_exact Hc'.
Qed.
Fixpoint submemb {imgk : img} (rs' rs : smem) : bool :=
match rs', rs with
| [], _ => true
| r' :: t', r :: t => subregionb r' r && submemb t' t
| _ :: _, [] => false
end.
Lemma submemb_sound : forall rs' rs, submemb rs' rs = true -> submem rs' rs.
Proof.
clearP. intros rs'. induction rs' as [|r' t' IH]; intros rs H; [img_try (img_apply submem_nil)|]. destruct rs as [|r t]; [img_try (discriminate H)|].
cbn [submemb] in H. apply andb_prop in H as [H1 H2]. img_apply submem_keep; [img_try (img_exact (subregionb_sound _ _ H1)) | img_try (img_exact (IH t H2))].
Qed.
Lemma at_S_submem : forall (Wx : world tfxsegs) md X P ss W' c' rs,
at_S Wx md X P ss W' c' -> submemb rs (ss_mem ss) = true -> regions_wf rs = true ->
at_S Wx md X P (mkSS (ss_pc ss) (ss_regs ss) rs (ss_resv ss) (ss_facts ss)) W' c'.
Proof.
clearP. intros Wx md X P ss W' c' rs HR Hsb Hwf. destruct HR as (-> & ms & mat & E' & -> & HE & HS & MEQ & PRS & HPm).
split; [img_refl|]. exists ms, mat, E'. split; [img_refl|]. split; [img_try (img_exact HE)|]. split; [|img_try (img_exact (conj MEQ (conj PRS HPm)))].
img_exact (st_ok_submem tfxsegs E' ss _ rs HS (submemb_sound _ _ Hsb) Hwf).
Qed.
Lemma at_S_addreg : forall (Wx : world tfxsegs) md X P ss W' c' r,
at_S Wx md X P ss W' c' -> YQ0b.region_wf r = true ->
(forall (E' : env) (m : word -> option byte),
env_agree sHAV E0 E' -> (forall x : word, ~ X (bv_unsigned x) -> m x = mem0 x) ->
(forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H Wx) m a) -> P m -> mem_ok tfxsegs E' (mrestrict (w_H Wx) m) (ss_mem ss) ->
region_ok tfxsegs E' (mrestrict (w_H Wx) m) r /\ (forall r2, In r2 (ss_mem ss) -> extent_disjoint E' r r2)) ->
at_S Wx md X P (addreg r ss) W' c'.
Proof.
clearP. intros Wx md X P ss W' c' r HR Hwf HOK. destruct HR as (-> & ms & mat & E' & -> & HE & HS & MEQ & PRS & HPm).
split; [img_refl|]. exists ms, mat, E'. split; [img_refl|]. split; [img_try (img_exact HE)|]. split; [|img_try (img_exact (conj MEQ (conj PRS HPm)))].
pose proof (st_ok_mem_ok tfxsegs E' ss _ HS) as HM. destruct (HOK E' (ms_mem ms) HE MEQ PRS HPm HM) as [Hok Hx].
unfold addreg. img_apply st_ok_add_region; [img_try (img_exact HS) | img_try (img_exact Hwf) | img_try (img_exact Hok) | img_try (img_apply all_disjoint_of_forall; img_exact Hx)].
Qed.
End h.
End g.
