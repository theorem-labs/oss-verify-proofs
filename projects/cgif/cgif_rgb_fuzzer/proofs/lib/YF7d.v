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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF77.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP09.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF64 YF3v YF3w YF3x YF41 YF6z YF0a YF7f YF71 YF72 YF7o YF7p YF7q YF7a YF7g YF7h.
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
Local Abbreviation ARe f := (f idx res Hidx) (only parsing).
Local Abbreviation tr_length := (ARe ((AR1 (@YF7f.tr_length)) ch)).
Local Abbreviation ARc f := (f idx res LY IMG Hidx Hres) (only parsing).
Local Abbreviation high_facts := (ARc (AR1 (@YF7f.high_facts _))).
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
Local Abbreviation AR8 f := (f Nrange Hidx Hres) (only parsing).
Local Abbreviation map_facts := ((AR8 (AR3 (@YF7f.map_facts _))) Hmap).
Local Abbreviation map_zone := ((AR3 (@YF7f.map_zone _)) Nrange Hidx Hmap).
Local Abbreviation map_zoneN := ((AR8 (AR3 (@YF7f.map_zoneN _))) Hmap).
Local Abbreviation map_in_band := ((AR3 (@YF7f.map_in_band _)) Nrange Hidx Hmap).
Local Abbreviation map_off_img := (@YF7f.map_off_img _ imgk n mb Hmap).
Local Abbreviation WINT := (@YF7f.WINT ly).
Local Abbreviation WINI := (@YF7f.WINI n imgk).
Local Abbreviation WINM := (@YF7f.WINM ly n idx mb).
Local Abbreviation ARb f := (AR1 f n idx mb) (only parsing).
Local Abbreviation WIN := (ARb (@YF7f.WIN)).
Local Abbreviation WINN := (AR1 (@YF7f.WINN)).
Local Abbreviation WINP := ((AR1 (@YF7f.WINP)) n).
Local Abbreviation WINP_WIN := (ARb (@YF7f.WINP_WIN)).
Local Abbreviation WIN1P := ((AR1 (@YF7f.WIN1P)) n).
Local Abbreviation WIN1 := (ARb (@YF7f.WIN1)).
Local Abbreviation WIN1P_WINP := ((AR3 (@YF7f.WIN1P_WINP)) Hidx).
Local Abbreviation WIN1_WIN := ((AR3 (@YF7f.WIN1_WIN)) Hidx).
Local Abbreviation WIN1P_WIN1 := (ARb (@YF7f.WIN1P_WIN1)).
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
Local Abbreviation AR4 f := (AR0 f LY IMG Nrange Hidx Hres) (only parsing).
Local Abbreviation WSKELP_WINP := (AR4 (AR1 (@YF7f.WSKELP_WINP _))).
Local Abbreviation WSKEL1P_WIN1P := (AR4 (AR1 (@YF7f.WSKEL1P_WIN1P _))).
Local Abbreviation WMAP_WINM := ((AR4 (AR1 (@YF7f.WMAP_WINM _))) Hmap).
Local Abbreviation WSKEL_WIN := ((AR4 (AR1 (@YF7f.WSKEL_WIN _))) Hmap).
Local Abbreviation WSKEL1_WIN1 := ((AR4 (AR1 (@YF7f.WSKEL1_WIN1 _))) Hmap).
Local Abbreviation windows_in := ((AR9 (@YF7f.windows_in ly regs0)) Hidx Hres).
Local Abbreviation windows_WINP := (AR4 (AR1 (@YF7f.windows_WINP _))).
Local Abbreviation windows_WIN1P := (AR4 (AR1 (@YF7f.windows_WIN1P _))).
Local Abbreviation windows_WIN := ((AR4 (AR1 (@YF7f.windows_WIN _))) Hmap).
Local Abbreviation windows_WIN1 := ((AR4 (AR1 (@YF7f.windows_WIN1 _))) Hmap).
Local Abbreviation frame_WIN1P := (AR4 (AR1 (@YF7f.frame_WIN1P _))).
Local Abbreviation frame_WIN1 := ((AR4 (AR1 (@YF7f.frame_WIN1 _))) Hmap).
Local Abbreviation AR2 f := (f LY IMG Hsp Nrange Hidx Hres) (only parsing).
Local Abbreviation WINP_not_high := (AR2 (AR3 (@YF7f.WINP_not_high _))).
Local Abbreviation ARa f := (AR2 f Hmap) (only parsing).
Local Abbreviation WIN_not_high := (ARa (AR3 (@YF7f.WIN_not_high _))).
Variables (mat0 : list word).
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 (0x53108 + D_2c4)) mem0 (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis U1 : tfx_unwind_spec.
Local Abbreviation all_disjoint_of_forall := (@YF7f.all_disjoint_of_forall).
Local Abbreviation img_rw_writable := ((AR9 (AR1 (@YF7f.img_rw_writable))) Hidx).
Local Abbreviation ARf f := (f imgk W ly) (only parsing).
Local Abbreviation kept_of_frame := ((AR9 ((ARf (@YF7f.kept_of_frame)) regs0)) Hidx).
Local Abbreviation SKEL_TAIL := (@YF7f.SKEL_TAIL imgk).
Local Abbreviation blocks_facts := (@YF7f.blocks_facts _ imgk ly LY IMG).
Local Abbreviation off_T := (ARc (AR1 (@YF7f.off_T _))).
Local Abbreviation off_C := (ARc (AR1 (@YF7f.off_C _))).
Local Abbreviation off_Q := (ARc (AR1 (@YF7f.off_Q _))).
Local Abbreviation off_NB := (@YF7f.off_NB _ imgk ly LY IMG).
Local Abbreviation off_SB := (@YF7f.off_SB _ imgk ly LY IMG).
Local Abbreviation off_shadow := ((AR9 (AR1 (@YF7f.off_shadow))) Hidx).
Ltac off_by tac :=
first [ img_apply off_img_high; tac | img_apply off_T; tac | img_apply off_C; tac | img_apply off_Q; tac | img_apply off_NB; tac | img_apply off_SB; tac
| img_apply map_off_img; tac | img_apply off_shadow; tac
| unfold off_img; unfold TFX_IMG_LO; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; tac ].
Local Abbreviation DZONE := (@YF7f.DZONE imgk ly).
Variable DPOST : Z -> (word -> option byte) -> Prop.
Local Abbreviation DZONE_disj := ((ARa (AR3 (@YF7f.DZONE_disj _))) Hmap_apart).
Local Abbreviation RFACTS := (AR1 (@YF7f.RFACTS)).
Local Abbreviation zone_lit := ((AR1 (@YF7f.zone_lit _)) LY IMG Hsp).
Local Abbreviation zone_irw := ((AR1 (@YF7f.zone_irw _)) LY IMG Hsp).
Local Abbreviation zone_T := ((AR1 (@YF7f.zone_T _)) idx res LY IMG Hsp Hidx Hres).
Local Abbreviation zone_C := ((AR1 (@YF7f.zone_C _)) idx res LY IMG Hsp Hidx Hres).
Local Abbreviation tail_ext_ok := (AR2 (AR0 (AR1 (@YF7f.tail_ext_ok _)))).
Local Abbreviation RFACTS_map := ((AR8 ((AR3 (@YF7f.RFACTS_map _)) LY IMG)) Hmap Hmap_apart).
Local Abbreviation AR5 f := (f imgk W ly regs0 mem0) (only parsing).
Local Abbreviation at_ST := (AR0 ((AR5 (@YF7f.at_ST _)) md0)).
Local Abbreviation memset_stretch := ((AR8 ((AR9 ((AR5 (@YF7f.memset_stretch _ _)) md0 n)) Hsp)) Hmap Hmap_apart mat0 DPOST).
Ltac clearM := try clear DPOST; try clear Hmap_apart; try clear Hmap.
Local Abbreviation AR7 f := (AR1 f mem0) (only parsing).
Local Abbreviation at_S := (AR0 (AR7 (@YF7f.at_S _))).
Local Abbreviation at_N := (AR0 (AR7 (@YF7f.at_N _))).
Local Abbreviation at_RETS := ((AR7 (@YF7f.at_RETS _)) ch).
Local Abbreviation pstable := (@YF7f.pstable).
Local Abbreviation stack_shaped := (@YF7f.stack_shaped).
Local Abbreviation window_present := (ARe (AR1 (@YF7f.window_present))).
Local Abbreviation stack_present_of := ((AR0 (AR1 (@YF7f.stack_present_of _))) LY Hsp Hidx).
Local Abbreviation mid_not_WIN1P := (AR2 (AR3 (@YF7f.mid_not_WIN1P _))).
Local Abbreviation mid_not_WIN1 := (ARa (AR3 (@YF7f.mid_not_WIN1 _))).
Local Abbreviation wins_ok := (@YF7f.wins_ok).
Local Abbreviation at_S_run_gen := ((AR0 (AR7 (@YF7f.at_S_run_gen _ _))) LY Hsp Hidx).
Local Abbreviation at_S_run_ecall_gen := ((AR0 (AR7 (@YF7f.at_S_run_ecall_gen _ _))) LY Hsp Hidx).
Local Abbreviation at_S_runP := (AR2 (AR0 (AR7 (@YF7f.at_S_runP _ _)))).
Local Abbreviation at_S_runM := (ARa (AR0 (AR7 (@YF7f.at_S_runM _ _)))).
Local Abbreviation at_S_run_ecallP := (AR2 (AR0 (AR7 (@YF7f.at_S_run_ecallP _ _)))).
Local Abbreviation at_S_run_ecallM := (ARa (AR0 (AR7 (@YF7f.at_S_run_ecallM _ _)))).
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
Local Abbreviation at_S_ret := (AR8 ((AR0 (AR7 (@YF7f.at_S_ret _))) Htp Hra Hsp)).
Local Abbreviation kept_of_frame2 := (ARe (AR1 (@YF7f.kept_of_frame2))).
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
Local Abbreviation vis_present := ((ARe (AR5 (@YF7o.vis_present _))) DPOST B S HARm).
Local Abbreviation in_thread_junk := (@YF7o.in_thread_junk ly B S).
Local Abbreviation in_sec_junk := (@YF7o.in_sec_junk ly B S).
Local Abbreviation in_as_junk := (@YF7o.in_as_junk ly B S).
Local Abbreviation junk_word := ((ARc (AR5 (@YF7o.junk_word _))) DPOST B S HARm).
Local Abbreviation cell_sym := ((ARf (@YF7o.cell_sym _)) mem0 B S TS HARm).
Local Abbreviation cell_lit := ((ARf (@YF7o.cell_lit _)) mem0 B S TS HARm).
Local Abbreviation cell_state := ((ARf (@YF7o.cell_state _)) mem0 B S HARm).
Local Abbreviation In_acells_sec := (@YF7o.In_acells_sec ly B S).
Local Abbreviation sec_vals := ((ARf (@YF7o.sec_vals _)) mem0 idx res B S TS HARm Hidx_def Hres_def).
Local Abbreviation unwinding_val := ((ARf (@YF7o.unwinding_val _)) mem0 B S HARm).
Local Abbreviation rw_writable := ((ARe (AR1 (@YF7o.rw_writable))) DPOST S).
Local Abbreviation val_mem_mod8 := ((ARe (AR5 (@YF7o.val_mem_mod8))) DPOST S).
Local Abbreviation chunk_lit := (AR0 (AR5 (@YF7o.chunk_lit))).
Local Abbreviation chunk_lit_at := (AR0 (AR5 (@YF7o.chunk_lit_at))).
Local Abbreviation chunk_atom := ((AR0 (AR5 (@YF7o.chunk_atom))) Hidx DPOST S).
Local Abbreviation AR6 f := (f DPOST B S TS HTSD HARm Hidx_def Hres_def Hj0 Hj1 Hj2 Hj3 Hj4 Hj5 Hj9 Hj6 Hj7 Hj8 Hi1 Hi2 Hi3) (only parsing).
Local Abbreviation SREG0_ok := (AR6 ((AR2 (AR0 (AR5 (@YF7p.SREG0_ok _)))) Hpres0)).
Local Abbreviation PAIRS_ok := ((AR2 (AR0 (AR5 (@YF7q.PAIRS_ok _)))) DPOST S).
Local Abbreviation FACTS_ok := ((AR8 ((AR0 (AR5 (@YF7q.FACTS_ok _))) LY IMG Hn Hsp)) DPOST S).
Local Abbreviation SEED_ok := (AR6 ((AR8 ((AR0 (AR5 (@YF7q.SEED_ok _ _))) LY IMG Hn Hsp)) Hpres0)).
Local Abbreviation PBUF := ((ARf (@YF7a.PBUF)) regs0 ch).
Local Abbreviation PBUF_stableP := (AR2 (AR9 ((ARf (@YF7a.PBUF_stableP _)) regs0 n ch))).
Local Abbreviation PBUF_stableM := (ARa (AR9 ((ARf (@YF7a.PBUF_stableM _)) regs0 n ch))).
Local Abbreviation seg0 := (AR6 ((AR8 ((AR0 ((AR5 (@YF7a.seg0 _ _)) md0)) LY IMG Hn Htp Hra4096 Hsp Hch)) Hpres0 mat0 U1)).
Local Abbreviation appregs := (@YF7g.appregs).
Local Abbreviation st_ok_appregs := (@YF7g.st_ok_appregs _ imgk).
Local Abbreviation at_S_app := (AR0 (AR7 (@YF7g.at_S_app _))).
Local Abbreviation WIN1N := ((AR1 (@YF7g.WIN1N)) n).
Local Abbreviation WINPN := ((AR1 (@YF7g.WINPN)) n).
Local Abbreviation WSKEL1N := (@YF7g.WSKEL1N imgk).
Local Abbreviation WIN1N_WINPN := ((AR3 (@YF7g.WIN1N_WINPN)) Hidx).
Local Abbreviation windows_WIN1N := (AR4 (AR1 (@YF7g.windows_WIN1N _))).
Local Abbreviation mid_not_WIN1N := (AR2 (AR3 (@YF7g.mid_not_WIN1N _))).
Local Abbreviation at_S_runN := (AR2 (AR0 (AR7 (@YF7g.at_S_runN _ _)))).
Local Abbreviation PBUF_stableN := (AR2 (AR9 ((ARf (@YF7g.PBUF_stableN _)) regs0 n ch))).
Local Abbreviation at_S_val := (AR0 (AR7 (@YF7g.at_S_val _))).
Local Abbreviation memset_stretchW := ((AR8 ((AR5 (@YF7g.memset_stretchW _)) md0 n idx res Hsp)) mat0 DPOST S).
Local Abbreviation at_S_memset := ((AR8 ((AR0 ((AR5 (@YF7g.at_S_memset _)) md0)) Hsp)) mat0 DPOST S).
Local Abbreviation WIN1T := (ARb (@YF7g.WIN1T)).
Local Abbreviation WIN1T_WIN := ((AR8 (AR3 (@YF7g.WIN1T_WIN _))) Hmap).
Local Abbreviation windows_WIN1T := ((AR4 (AR1 (@YF7g.windows_WIN1T _))) Hmap).
Local Abbreviation WIN1T_WIN1_aux := ((AR8 (AR3 (@YF7g.WIN1T_WIN1_aux _))) Hmap).
Local Abbreviation mid_not_WIN1T := (ARa (AR3 (@YF7g.mid_not_WIN1T _))).
Local Abbreviation at_S_runT := (ARa (AR0 (AR7 (@YF7g.at_S_runT _ _)))).
Local Abbreviation at_S_run_ecallT := (ARa (AR0 (AR7 (@YF7g.at_S_run_ecallT _ _)))).
Local Abbreviation PBUFW := ((AR1 (@YF7g.PBUFW)) ch).
Local Abbreviation PBUFW_stableT := (ARa (AR9 ((AR1 (@YF7g.PBUFW_stableT _)) n ch))).
Local Abbreviation WIN1S := (ARb (@YF7h.WIN1S)).
Local Abbreviation WSKEL1S := (@YF7h.WSKEL1S imgk).
Local Abbreviation WIN1S_WIN1T := (ARb (@YF7h.WIN1S_WIN1T)).
Local Abbreviation WIN1S_WIN := ((AR8 (AR3 (@YF7h.WIN1S_WIN _))) Hmap).
Local Abbreviation windows_WIN1S := ((AR4 (AR1 (@YF7h.windows_WIN1S _))) Hmap).
Local Abbreviation mid_not_WIN1S := (ARa (AR3 (@YF7h.mid_not_WIN1S _))).
Local Abbreviation at_S_runS := (ARa (AR0 (AR7 (@YF7h.at_S_runS _ _)))).
Local Abbreviation at_S_run_ecallS := (ARa (AR0 (AR7 (@YF7h.at_S_run_ecallS _ _)))).
Local Abbreviation brun := (@YF7h.brun).
Local Abbreviation run_ok := (@YF7h.run_ok n mb).
Local Abbreviation PS := ((AR1 (@YF7h.PS)) n ch mb).
Local Abbreviation runs_not_WIN1S := ((ARa (AR3 (@YF7h.runs_not_WIN1S _))) Hmap_apart).
Local Abbreviation runs_not_stack := ((AR8 ((AR3 (@YF7h.runs_not_stack _)) LY Hsp)) Hmap Hmap_apart).
Local Abbreviation PS_stable := ((ARa (AR9 ((AR1 (@YF7h.PS_stable _)) n ch))) Hmap_apart).
Local Abbreviation cut1 := (@YF7h.cut1).
Local Abbreviation cut := (@YF7h.cut).
Local Abbreviation cut_sound := ((AR8 (AR9 ((AR7 (@YF7h.cut_sound _)) n))) Hmap DPOST S).
Local Abbreviation cut_ok := ((AR9 (@YF7h.cut_ok ly regs0 mem0 n)) Hidx Hres DPOST S).
Local Abbreviation at_S_memsetS := ((AR8 ((AR0 ((AR5 (@YF7h.at_S_memsetS _ _)) md0)) LY Hsp)) Hmap Hmap_apart mat0 DPOST S).
Local Abbreviation skel_okb := (@YF7h.skel_okb imgk).
Local Abbreviation skel_cases := ((ARe (@YF7h.skel_cases imgk)) Hres S Hidx_def Hres_def).
Local Abbreviation ARd f := (f DPOST S Hidx_def Hres_def) (only parsing).
Local Abbreviation skel_apart := (ARd ((ARa (AR0 (AR7 (@YF7h.skel_apart _)))) Hmap_apart)).
Local Abbreviation skel_u64 := (ARd (ARa (AR0 (AR7 (@YF7h.skel_u64 _))))).
Local Abbreviation memset_ext_of_skel := (ARd ((ARa (AR0 (AR7 (@YF7h.memset_ext_of_skel _)))) Hmap_apart)).
Local Abbreviation memset_u64_of_skel := (ARd (ARa (AR0 (AR7 (@YF7h.memset_u64_of_skel _))))).
Local Abbreviation WIN1R := ((AR1 (@YF7h.WIN1R)) n mb).
Local Abbreviation WSKEL1R := (@YF7h.WSKEL1R imgk).
Local Abbreviation WIN1R_WIN1S := (ARb (@YF7h.WIN1R_WIN1S)).
Local Abbreviation WIN1R_WIN := ((AR8 (AR3 (@YF7h.WIN1R_WIN _))) Hmap).
Local Abbreviation windows_WIN1R := ((AR4 (AR1 (@YF7h.windows_WIN1R _))) Hmap).
Local Abbreviation mid_not_WIN1R := (ARa (AR3 (@YF7h.mid_not_WIN1R _))).
Local Abbreviation at_S_runR := (ARa (AR0 (AR7 (@YF7h.at_S_runR _ _)))).
Local Abbreviation at_S_run_ecallR := (ARa (AR0 (AR7 (@YF7h.at_S_run_ecallR _ _)))).
Local Abbreviation PSR := ((AR1 (@YF7h.PSR)) n ch mb).
Local Abbreviation rstable := ((AR1 (@YF7h.rstable)) n mb).
Local Abbreviation rstable_true := ((AR1 (@YF7h.rstable_true)) n mb).
Local Abbreviation PSR_stable := ((ARa (AR9 ((AR1 (@YF7h.PSR_stable _)) n ch))) Hmap_apart).
Local Abbreviation QSP := (@YF7h.QSP imgk ly idx).
Local Abbreviation QS_not_WIN1R := ((ARa (AR3 (@YF7h.QS_not_WIN1R _))) Hmap_apart).
Local Abbreviation QSP_rstable := ((ARa (AR3 (@YF7h.QSP_rstable _))) Hmap_apart).
Local Abbreviation at_S_memsetSR := ((AR8 ((AR0 ((AR5 (@YF7h.at_S_memsetSR _ _)) md0)) LY Hsp)) Hmap Hmap_apart mat0 DPOST S).
Local Abbreviation chunk_eqb := (@YF7h.chunk_eqb imgk).
Local Abbreviation chunk_eqb_eq := ((ARe (@YF7h.chunk_eqb_eq imgk)) Hres S Hidx_def Hres_def).
Local Abbreviation subregionb := (@YF7h.subregionb imgk).
Local Abbreviation subregionb_sound := (ARd ((ARe (AR7 (@YF7h.subregionb_sound))) Hres)).
Local Abbreviation submemb := (@YF7h.submemb imgk).
Local Abbreviation submemb_sound := (ARd ((ARe (AR7 (@YF7h.submemb_sound))) Hres)).
Local Abbreviation at_S_submem := (ARd ((AR0 (AR7 (@YF7h.at_S_submem _))) Hidx Hres)).
Local Abbreviation at_S_addreg := (AR0 (AR7 (@YF7h.at_S_addreg _))).
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
Variables (Wy : world tfxsegs) (md1 : Model).
Local Ltac s_runR HR tbl tblok stop ss' HX HP :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let st := img_ev (snd (sym_run_toN_sh tfxsegs tbl FUEL stop ss)) in
eapply SRr_bind;
[ img_try (eapply (at_S_runR Wx tbl tblok stop md X P ss ss' st W' c' HR);
[ (img_case; vm_compute); img_refl | img_exact I | img_exact HX | (img_case; vm_compute); img_refl | img_exact HP | (img_case; vm_compute); img_refl ])
| img_try (clear HR; let W2 := fresh "W" in let c2 := fresh "c" in intros W2 c2 _ HR) ] end.
Lemma PSR_runs : forall md X sh sh' R ss W' c',
at_S Wy md X (PSR Wy sh R) ss W' c' -> (forall m, Forall (brun m) sh -> Forall (brun m) sh') -> at_S Wy md X (PSR Wy sh' R) ss W' c'.
Proof. clearP. intros md X sh sh' R ss W' c' HR Himp. eapply at_S_weaken; [img_try (img_exact HR) | img_try (intros a Ha; img_exact Ha) | img_try (intros m ((A & B' & C & D) & HQ); img_exact (conj (conj A (conj B' (conj C (Himp m D)))) HQ))]. Qed.
Lemma place_WIN : forall d len a, ((mb + 6144 <= d /\ d + len <= mb + MSv) \/ (SMv <= d /\ d + len <= SMv + MSv / 8)) -> d <= a < d + len -> WIN a.
Proof. intros d len a Hp Ha. unfold WIN, WINM. right; right; right. clear - Hp Ha. destruct Hp as [[P1 P2]|[P1 P2]]; [img_try (right; left; zlia) | img_try (right; right; zlia)]. Qed.
Local Ltac s_memset HR ss' k d len vb retpc OK RS :=
lazymatch type of HR with at_S ?Wx ?md ?X (PSR _ ?sh ?R) ?ss ?W' ?c' =>
let ed := img_ev (sr_get (ss_regs ss) 10%bv) in
let el := img_ev (sr_get (ss_regs ss) 12%bv) in
let Ud := fresh "Ud" in let Ul := fresh "Ul" in let PL := fresh "PL" in
assert (Ud : U E0 ed = d); [|
assert (Ul : U E0 el = len); [|
assert (PL : (mb + 6144 <= d /\ d + len <= mb + MSv) \/ (SMv <= d /\ d + len <= SMv + MSv / 8)); [|
eapply SRr_bind;
[ eapply (at_S_memsetSR Wx md X sh R ss W' c' k ed el d len vb retpc HR RS eq_refl ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try (unfold sHAV; (img_case; cbv); zlia))
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) eq_refl eq_refl ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Ud Ul);
[ (clear; zlia) || zlia | clear; (img_case; cbv); img_refl | clear; zlia | clear; zlia | img_exact PL | img_exact OK | intros a Ha; img_exact (place_WIN d len a PL Ha)
| img_exact (memset_ext_of_skel false d len ss ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) PL ltac:(img_try (intros XX; discriminate XX)))
| img_exact (memset_u64_of_skel false ss ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))) ]
| clear HR Ud Ul; let W2 := fresh "W" in let c2 := fresh "c" in intros W2 c2 _ HR;
lazymatch type of HR with at_S _ _ _ _ ?ss2 _ _ => replace ss2 with ss' in HR by (img_try ((img_case; vm_compute); img_refl)) end ] ] ] ] end.
Definition SH0 : list (Z * Z * Z) := [(SMv, SMv + MSv / 8, 0)].
Definition SH1 : list (Z * Z * Z) := [(SMv, SMv + 512, 250); (SMv + 512, SMv + MSv / 8, 0)].
Definition SH2 : list (Z * Z * Z) := [(SHBv + ENDv / 8, SMv + MSv / 8, 250); (SMv, SMv + 512, 250); (SMv + 512, SHBv + ENDv / 8, 0)].
Lemma SH_ok : Forall run_ok SH0 /\ Forall run_ok SH1 /\ Forall run_ok SH2.
Proof.
pose proof map_facts as (M1 & M2 & M3 & K4 & U5 & E6 & _ & _ & _ & MT & _ & SM1 & SM2 & _ & _ & SMA). pose proof map_zoneN as MZ. pose proof size_facts as (Z1 & _ & _ & _ & _ & _ & Z7 & Z8 & Z9 & Z10 & Z11 & _).
clear - M1 M2 M3 K4 U5 E6 MT SM1 SM2 Z1 Z7 Z8 Z9 Z10 Z11 MZ.
unfold SH0, SH1, SH2, run_ok. unfold YF7f.SMv, YF7f.SHBv in *.
assert (D1 : mb / 8 + 512 <= ENDv / 8) by (img_try (img_apply Z.div_le_lower_bound; [img_try (zlia)|]; pose proof (Z.mul_div_le mb 8 ltac:(zlia)); unfold Uv in *; zlia)).
assert (D2 : ENDv / 8 <= mb / 8 + MSv / 8).
{ rewrite <- Z.div_add by zlia. img_apply Z.div_le_mono; [img_try (zlia)|]. zlia. }
assert (D3 : 9216 <= MSv / 8) by (img_try (img_apply Z.div_le_lower_bound; zlia)).
repeat split; repeat (img_apply Forall_cons || img_apply Forall_nil); cbn [fst snd]; zlia.
Qed.
Lemma segG1 : forall (R : (word -> option byte) -> Prop), rstable R ->
forall c, at_S Wy md1 WIN (PSR Wy SH0 R) S_P0 Wy c -> SRr tfxsegs Wy c (at_S Wy md1 WIN (PSR Wy SH2 R) S_X).
Proof.
intros R RS c HR. pose proof WIN1R_WIN as HX. pose proof SH_ok as (OK0 & OK1 & OK2).
pose proof (PSR_stable Wy SH0 R OK0 RS) as HP0. pose proof (PSR_stable Wy SH1 R OK1 RS) as HP1. pose proof (PSR_stable Wy SH2 R OK2 RS) as HP2.
pose proof map_facts as (M1 & M2 & M3 & K4 & U5 & E6 & UE7 & E8 & UE9 & MT & MU & SM1 & SM2 & SM3 & PB & SMA). pose proof map_zoneN as MZ.
pose proof size_facts as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10 & Z11 & Z12 & Z13 & Z14). pose proof Nrange as NR. pose proof Hidx as HI.
unfold MALLOC_MAX in Z1, Z8, NR. ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kHighShadowBeg, kHighShadowEnd in M1, M2, SM1, SM2. unfold kMaxNumChunks in HI.
s_runR HR tfxtbl_rtC tfxtbl_rtC_ok (0x36350 + D_150) S_P1 HX HP0.
s_runR HR tfxtbl_rr tfxtbl_rr_ok (0x54344 + D_2c4) S_L1 HX HP0.
s_ladder s_runR HR tfxtbl_rr tfxtbl_rr_ok (0x9b894 + D_10ec) S_L1l S_L1lo S_L1h S_L1h2 S_L1h3 S_L1hi S_M1 sL1 CLOB_L HX HP0.
s_memset HR S_P2 sM1 constr:(SMv) 512 250 (0x363a8 + D_150) OK0 RS.
{ clear - M1 M2 Z8 MZ. U_zevS. rewrite (eq_refl : ew E0 47 = w64 SHBv), EaMAP. unfold w64, YF7f.SMv, YF7f.SHBv in *. rewrite !unsigned_lit_small by zlia.
zcanon_simp. land_lits. rewrite Z.shiftr_div_pow2 by zlia. img_change (2 ^ 3) with 8.
pose proof (Z.div_pos mb 8 ltac:(img_try (zlia)) ltac:(img_try (zlia))). pose proof (Z.div_lt_upper_bound mb 8 (2 ^ 61) ltac:(img_try (zlia)) ltac:(img_try (zlia))). zcanon_simp. zlia. }
{ clear - M1 M2 M3 Z8 MZ. U_zevS. rewrite EaMAP. unfold w64. rewrite !unsigned_lit_small by zlia.
zcanon_simp. land_lits. rewrite !Z.shiftr_div_pow2 by zlia. img_change (2 ^ 3) with 8.
apply Z.mod_divide in M3 as [q Hq]; [|img_try (zlia)]. rewrite Hq.
replace (q * 4096 + 4088) with ((q * 512 + 511) * 8) by zlia. replace (q * 4096 + 0) with ((q * 512) * 8) by zlia. rewrite !Z_div_mult by zlia.
zcanon_simp. zlia. }
{ right. clear - Z8 Z10 Z7 Z1 MZ. unfold YF7f.SMv. assert (9216 <= MSv / 8) by (img_try (img_apply Z.div_le_lower_bound; zlia)). zlia. }
apply (PSR_runs md1 WIN _ SH1 R S_P2) in HR.
2:{ intros m HF. pose proof (Forall_inv HF) as B1. pose proof (Forall_inv_tail HF) as B2'. clear HF.
unfold cut, SH0 in B2'. cbn [flat_map app] in B2'. unfold cut1 in B2'. cbn [fst snd] in B2'.
assert (E1 : (SMv <? SMv) = false) by (img_try (img_apply Z.ltb_irrefl)).
assert (E2 : (SMv + 512 <? SMv + MSv / 8) = true) by (img_try (img_apply Z.ltb_lt; clear - Z8 MZ; assert (9216 <= MSv / 8) by (img_apply Z.div_le_lower_bound; zlia); zlia)).
rewrite E1, E2 in B2'. cbn [app] in B2'. rewrite Z.max_r in B2' by zlia.
unfold SH1. img_apply Forall_cons; [img_try (img_exact B1)|]. img_exact B2'. }
s_pin HR (23%bv : bv 5) (SOff aEND 0).
{ clear - M1 M2 Z8 Z1 Z7 E8 K4 U5 E6 MZ. pin_zevS. rewrite EaEND, EaMAP, EaND. unfold w64. rewrite !unsigned_lit_small by zlia. zcanon_simp.
img_change (zcanon (-8)) with (2 ^ 64 - 8). rewrite land_m8_64 by zlia. unfold ENDv in *. rewrite Z.add_0_r. zcanon_simp. zlia. }
s_station HR S_P3.
s_runR HR tfxtbl_rr tfxtbl_rr_ok (0x363b4 + D_150) (runto (0x363b4 + D_150) S_P3) HX HP1.
s_pin HR (11%bv : bv 5) (SOff aTL 0).
{ clear - M1 M2 Z8 Z1 Z7 Z11 MT MZ. pin_zevS. rewrite EaTL, EaMS, EaMAP, EaEND. unfold w64. rewrite !unsigned_lit_small by zlia.
rewrite (zcanon_id (TLv + 0)), (zcanon_id (MSv + 0)), (zcanon_id (mb + 0)), (zcanon_id (ENDv + 0)), (zcanon_id (MSv + 0 + (mb + 0))) by (img_try (unfold M64; zlia)).
unfold zcanon, M64. rewrite Zmult_mod_idemp_r. rewrite Zplus_mod_idemp_r.
replace (MSv + 0 + (mb + 0) + (ENDv + 0) * -1) with (TLv + 0) by zlia. symmetry. img_apply Z.mod_small. zlia. }
s_station HR S_P4.
s_runR HR tfxtbl_rr tfxtbl_rr_ok (0x54344 + D_2c4) S_L2 HX HP1.
s_ladder s_runR HR tfxtbl_rr tfxtbl_rr_ok (0x9b894 + D_10ec) S_L2l S_L2lo S_L2h S_L2h2 S_L2h3 S_L2hi S_M2 sL2 CLOB_L HX HP1.
s_memset HR S_P5 sM2 constr:(SHBv + ENDv / 8) constr:(TLv / 8) 250 (0x363b8 + D_150) OK1 RS.
{ clear - M1 M2 Z8 E8 MT Z11 MZ. U_zevS. rewrite (eq_refl : ew E0 47 = w64 SHBv), EaEND. unfold w64, YF7f.SHBv in *. rewrite !unsigned_lit_small by zlia.
zcanon_simp. land_lits. rewrite Z.shiftr_div_pow2 by zlia. img_change (2 ^ 3) with 8.
pose proof (Z.div_pos ENDv 8 ltac:(img_try (zlia)) ltac:(img_try (zlia))). pose proof (Z.div_lt_upper_bound ENDv 8 (2 ^ 61) ltac:(img_try (zlia)) ltac:(img_try (zlia))). zcanon_simp. zlia. }
{ clear - M1 M2 Z8 E8 MT Z11 Z12 MZ. U_zevS. rewrite EaEND, EaTL. unfold w64. rewrite !unsigned_lit_small by zlia.
zcanon_simp. land_lits. rewrite !Z.shiftr_div_pow2 by zlia. img_change (2 ^ 3) with 8.
apply Z.mod_divide in E8 as [q Hq]; [|img_try (zlia)]. apply Z.mod_divide in Z12 as [t Ht]; [|img_try (zlia)]. rewrite Hq, Ht.
replace (q * 8 + -8 + (t * 8 + 0)) with ((q + t - 1) * 8) by zlia. replace (q * 8 + 0) with (q * 8) by zlia. rewrite !Z_div_mult by zlia.
zcanon_simp. zlia. }
{ right. clear - Z8 Z10 Z7 Z1 Z11 M1 M3 E8 MT K4 U5 E6 Z12 MZ. unfold YF7f.SMv, YF7f.SHBv.
apply Z.mod_divide in E8 as [q Hq]; [|img_try (zlia)]. apply Z.mod_divide in Z12 as [t Ht]; [|img_try (zlia)]. apply Z.mod_divide in M3 as [u Hu]; [|img_try (zlia)].
rewrite Ht, Z_div_mult by zlia. rewrite Hq, Z_div_mult by zlia.
replace mb with (u * 512 * 8) by zlia. rewrite Z_div_mult by zlia. replace MSv with ((q + t - u * 512) * 8) by zlia. rewrite Z_div_mult by zlia. unfold Uv in *. zlia. }
apply (PSR_runs md1 WIN _ SH2 R S_P5) in HR.
2:{ intros m HF. pose proof (Forall_inv HF) as B1. pose proof (Forall_inv_tail HF) as B2'. clear HF.
unfold cut, SH1 in B2'. cbn [flat_map app] in B2'. unfold cut1 in B2'. cbn [fst snd] in B2'.
assert (D1 : SMv + 512 < SHBv + ENDv / 8).
{ clear - M1 K4 U5 E6 Z1 Z7 MZ. unfold YF7f.SMv, YF7f.SHBv. assert (mb / 8 + 512 < ENDv / 8); [|img_try (zlia)].
assert (mb / 8 + 513 <= ENDv / 8); [|img_try (zlia)]. img_apply Z.div_le_lower_bound; [img_try (zlia)|]. pose proof (Z.mul_div_le mb 8 ltac:(img_try (zlia))). unfold Uv in *. zlia. }
assert (D2 : SHBv + ENDv / 8 + TLv / 8 = SMv + MSv / 8).
{ clear - M1 M3 E8 MT Z12 MZ. unfold YF7f.SMv, YF7f.SHBv. apply Z.mod_divide in E8 as [q Hq]; [|img_try (zlia)]. apply Z.mod_divide in Z12 as [t Ht]; [|img_try (zlia)].
apply Z.mod_divide in M3 as [u Hu]; [|img_try (zlia)]. rewrite Hq, Ht, !Z_div_mult by zlia.
replace mb with (u * 512 * 8) by zlia. rewrite Z_div_mult by zlia. replace MSv with ((q + t - u * 512) * 8) by zlia. rewrite Z_div_mult by zlia. zlia. }
assert (TL8 : 0 <= TLv / 8) by (img_try (clear - Z11 MZ; img_apply Z.div_pos; zlia)).
assert (E1 : (SMv <? SHBv + ENDv / 8) = true) by (img_try (clear - D1 MZ; img_apply Z.ltb_lt; zlia)).
assert (E2 : (SHBv + ENDv / 8 + TLv / 8 <? SMv + 512) = false) by (img_try (clear - D1 TL8 MZ; img_apply Z.ltb_ge; zlia)).
assert (E4 : (SHBv + ENDv / 8 + TLv / 8 <? SMv + MSv / 8) = false) by (img_try (clear - D2 MZ; img_apply Z.ltb_ge; zlia)).
assert (E5 : (SMv + 512 <? SHBv + ENDv / 8) = true) by (img_try (clear - D1 MZ; img_apply Z.ltb_lt; zlia)).
rewrite E1, E2, E4, E5 in B2'. cbn [app] in B2'. rewrite D2 in B1.
pose proof (Forall_inv B2') as C1. pose proof (Forall_inv (Forall_inv_tail B2')) as C2. clear B2'.
rewrite Z.min_l in C1 by (img_try (clear - D1 MZ; zlia)). rewrite Z.min_r in C2 by (img_try (clear - D2 TL8 MZ; zlia)).
unfold SH2. img_apply Forall_cons; [img_try (img_exact B1)|]. img_apply Forall_cons; [img_try (img_exact C1)|]. img_apply Forall_cons; [img_try (img_exact C2) | img_try (img_apply Forall_nil)]. }
s_runR HR tfxtbl_rr tfxtbl_rr_ok (0x363f0 + D_150) (runto (0x363f0 + D_150) S_P5) HX HP2.
s_arm HR BC_LTU false (SAlu ALU_ADD (SOff aMAP 4096) (SOff aND 0)) (SOff aMAP 0).
{ clear - M1 M2 Z8 Z1 Z7 Z10 MZ. arm_zevS. rewrite EaMAP, EaND. unfold w64. rewrite !unsigned_lit_small by zlia. zcanon_simp.
rewrite (proj2 (Z.ltb_ge _ _)); [img_refl | img_try (zlia)]. }
s_station HR S_P6.
s_runR HR tfxtbl_rr tfxtbl_rr_ok (0x363f4 + D_150) (runto (0x363f4 + D_150) S_P6) HX HP2.
s_arm HR BC_LTU false (SAlu ALU_ADD (SOff aMS 0) (SOff aMAP 0)) (SAlu ALU_ADD (SOff aMAP 4096) (SOff aND 0)).
{ clear - M1 M2 Z8 Z1 Z7 Z10 Z11 MT MZ. arm_zevS. rewrite EaMAP, EaND, EaMS. unfold w64. rewrite !unsigned_lit_small by zlia. zcanon_simp.
rewrite (proj2 (Z.ltb_ge _ _)); [img_refl | img_try (unfold ENDv in *; zlia)]. }
s_station HR S_P7.
s_runR HR tfxtbl_rr tfxtbl_rr_ok (0x36448 + D_150) (runto (0x36448 + D_150) S_P7) HX HP2.
s_arm HR BC_NE false (SAlu ALU_SRL (SOff aNCH 0) (SLit 20)) (SLit 0).
{ clear - HI MZ. arm_zevS. rewrite EaNCH. unfold w64. rewrite !unsigned_lit_small by zlia. zcanon_simp. land_lits.
rewrite Z.shiftr_div_pow2 by zlia. rewrite Z.add_0_r, (Z.div_small idx (2 ^ 20)) by zlia. img_refl. }
s_station HR S_P8.
s_runR HR tfxtbl_rr tfxtbl_rr_ok (0x364f4 + D_150) S_X HX HP2.
img_apply SRr_ret. img_exact HR.
Qed.
End h.
End g.
