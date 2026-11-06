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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF64 YF3v YF3w YF3x YF41 YF6z YF0a YF7f YF71 YF72 YF73 YF7o YF7p YF7q YF7a YF7g YF7h YF7d YF6w YF6y.
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
Local Abbreviation ARd f := (f idx res LY IMG Hidx Hres) (only parsing).
Local Abbreviation high_facts := (ARd (AR1 (@YF7f.high_facts _))).
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
Local Abbreviation AR8 f := (f Nrange Hidx Hres Hmap) (only parsing).
Local Abbreviation map_facts := (AR8 (AR3 (@YF7f.map_facts _))).
Local Abbreviation map_zone := ((AR3 (@YF7f.map_zone _)) Nrange Hidx Hmap).
Local Abbreviation map_zoneN := (AR8 (AR3 (@YF7f.map_zoneN _))).
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
Local Abbreviation off_T := (ARd (AR1 (@YF7f.off_T _))).
Local Abbreviation off_C := (ARd (AR1 (@YF7f.off_C _))).
Local Abbreviation off_Q := (ARd (AR1 (@YF7f.off_Q _))).
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
Local Abbreviation RFACTS_map := ((AR8 ((AR3 (@YF7f.RFACTS_map _)) LY IMG)) Hmap_apart).
Local Abbreviation AR5 f := (f imgk W ly regs0 mem0) (only parsing).
Local Abbreviation at_ST := (AR0 ((AR5 (@YF7f.at_ST _)) md0)).
Local Abbreviation memset_stretch := ((AR8 ((AR9 ((AR5 (@YF7f.memset_stretch _ _)) md0 n)) Hsp)) Hmap_apart mat0 DPOST).
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
Local Abbreviation at_S_ret := ((AR0 (AR7 (@YF7f.at_S_ret _))) Htp Hra Hsp Nrange Hidx Hres).
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
Local Abbreviation junk_word := ((ARd (AR5 (@YF7o.junk_word _))) DPOST B S HARm).
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
Local Abbreviation FACTS_ok := ((AR0 (AR5 (@YF7q.FACTS_ok _))) LY IMG Hn Hsp Nrange Hidx Hres DPOST S).
Local Abbreviation SEED_ok := (AR6 ((AR0 (AR5 (@YF7q.SEED_ok _ _))) LY IMG Hn Hsp Nrange Hidx Hres Hpres0)).
Local Abbreviation PBUF := ((ARf (@YF7a.PBUF)) regs0 ch).
Local Abbreviation PBUF_stableP := (AR2 (AR9 ((ARf (@YF7a.PBUF_stableP _)) regs0 n ch))).
Local Abbreviation PBUF_stableM := (ARa (AR9 ((ARf (@YF7a.PBUF_stableM _)) regs0 n ch))).
Local Abbreviation seg0 := (AR6 ((AR0 ((AR5 (@YF7a.seg0 _ _)) md0)) LY IMG Hn Htp Hra4096 Hsp Hch Nrange Hidx Hres Hpres0 mat0 U1)).
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
Local Abbreviation memset_stretchW := ((AR5 (@YF7g.memset_stretchW _)) md0 n idx res Hsp Nrange Hidx Hres mat0 DPOST S).
Local Abbreviation at_S_memset := ((AR0 ((AR5 (@YF7g.at_S_memset _)) md0)) Hsp Nrange Hidx Hres mat0 DPOST S).
Local Abbreviation WIN1T := (ARb (@YF7g.WIN1T)).
Local Abbreviation WIN1T_WIN := (AR8 (AR3 (@YF7g.WIN1T_WIN _))).
Local Abbreviation windows_WIN1T := ((AR4 (AR1 (@YF7g.windows_WIN1T _))) Hmap).
Local Abbreviation WIN1T_WIN1_aux := (AR8 (AR3 (@YF7g.WIN1T_WIN1_aux _))).
Local Abbreviation mid_not_WIN1T := (ARa (AR3 (@YF7g.mid_not_WIN1T _))).
Local Abbreviation at_S_runT := (ARa (AR0 (AR7 (@YF7g.at_S_runT _ _)))).
Local Abbreviation at_S_run_ecallT := (ARa (AR0 (AR7 (@YF7g.at_S_run_ecallT _ _)))).
Local Abbreviation PBUFW := ((AR1 (@YF7g.PBUFW)) ch).
Local Abbreviation PBUFW_stableT := (ARa (AR9 ((AR1 (@YF7g.PBUFW_stableT _)) n ch))).
Local Abbreviation WIN1S := (ARb (@YF7h.WIN1S)).
Local Abbreviation WSKEL1S := (@YF7h.WSKEL1S imgk).
Local Abbreviation WIN1S_WIN1T := (ARb (@YF7h.WIN1S_WIN1T)).
Local Abbreviation WIN1S_WIN := (AR8 (AR3 (@YF7h.WIN1S_WIN _))).
Local Abbreviation windows_WIN1S := ((AR4 (AR1 (@YF7h.windows_WIN1S _))) Hmap).
Local Abbreviation mid_not_WIN1S := (ARa (AR3 (@YF7h.mid_not_WIN1S _))).
Local Abbreviation at_S_runS := (ARa (AR0 (AR7 (@YF7h.at_S_runS _ _)))).
Local Abbreviation at_S_run_ecallS := (ARa (AR0 (AR7 (@YF7h.at_S_run_ecallS _ _)))).
Local Abbreviation brun := (@YF7h.brun).
Local Abbreviation run_ok := (@YF7h.run_ok n mb).
Local Abbreviation PS := ((AR1 (@YF7h.PS)) n ch mb).
Local Abbreviation runs_not_WIN1S := ((ARa (AR3 (@YF7h.runs_not_WIN1S _))) Hmap_apart).
Local Abbreviation runs_not_stack := ((AR8 ((AR3 (@YF7h.runs_not_stack _)) LY Hsp)) Hmap_apart).
Local Abbreviation PS_stable := ((ARa (AR9 ((AR1 (@YF7h.PS_stable _)) n ch))) Hmap_apart).
Local Abbreviation cut1 := (@YF7h.cut1).
Local Abbreviation cut := (@YF7h.cut).
Local Abbreviation cut_sound := ((AR8 (AR9 ((AR7 (@YF7h.cut_sound _)) n))) DPOST S).
Local Abbreviation cut_ok := ((AR9 (@YF7h.cut_ok ly regs0 mem0 n)) Hidx Hres DPOST S).
Local Abbreviation at_S_memsetS := ((AR8 ((AR0 ((AR5 (@YF7h.at_S_memsetS _ _)) md0)) LY Hsp)) Hmap_apart mat0 DPOST S).
Local Abbreviation skel_okb := (@YF7h.skel_okb imgk).
Local Abbreviation skel_cases := ((ARe (@YF7h.skel_cases imgk)) Hres S Hidx_def Hres_def).
Local Abbreviation ARc f := (f DPOST S Hidx_def Hres_def) (only parsing).
Local Abbreviation skel_apart := (ARc ((ARa (AR0 (AR7 (@YF7h.skel_apart _)))) Hmap_apart)).
Local Abbreviation skel_u64 := (ARc (ARa (AR0 (AR7 (@YF7h.skel_u64 _))))).
Local Abbreviation memset_ext_of_skel := (ARc ((ARa (AR0 (AR7 (@YF7h.memset_ext_of_skel _)))) Hmap_apart)).
Local Abbreviation memset_u64_of_skel := (ARc (ARa (AR0 (AR7 (@YF7h.memset_u64_of_skel _))))).
Local Abbreviation WIN1R := ((AR1 (@YF7h.WIN1R)) n mb).
Local Abbreviation WSKEL1R := (@YF7h.WSKEL1R imgk).
Local Abbreviation WIN1R_WIN1S := (ARb (@YF7h.WIN1R_WIN1S)).
Local Abbreviation WIN1R_WIN := (AR8 (AR3 (@YF7h.WIN1R_WIN _))).
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
Local Abbreviation at_S_memsetSR := ((AR8 ((AR0 ((AR5 (@YF7h.at_S_memsetSR _ _)) md0)) LY Hsp)) Hmap_apart mat0 DPOST S).
Local Abbreviation chunk_eqb := (@YF7h.chunk_eqb imgk).
Local Abbreviation chunk_eqb_eq := ((ARe (@YF7h.chunk_eqb_eq imgk)) Hres S Hidx_def Hres_def).
Local Abbreviation subregionb := (@YF7h.subregionb imgk).
Local Abbreviation subregionb_sound := (ARc ((ARe (AR7 (@YF7h.subregionb_sound))) Hres)).
Local Abbreviation submemb := (@YF7h.submemb imgk).
Local Abbreviation submemb_sound := (ARc ((ARe (AR7 (@YF7h.submemb_sound))) Hres)).
Local Abbreviation at_S_submem := (ARc ((AR0 (AR7 (@YF7h.at_S_submem _))) Hidx Hres)).
Local Abbreviation at_S_addreg := (AR0 (AR7 (@YF7h.at_S_addreg _))).
Local Abbreviation PSR_runs := (AR0 (AR7 (@YF7d.PSR_runs _))).
Local Abbreviation place_WIN := (ARb (@YF7d.place_WIN)).
Local Abbreviation SH0 := (@YF7d.SH0 n mb).
Local Abbreviation SH1 := (@YF7d.SH1 n mb).
Local Abbreviation SH2 := (@YF7d.SH2 n mb).
Local Abbreviation SH_ok := (AR8 (AR3 (@YF7d.SH_ok _))).
Local Abbreviation segG1 := (ARc ((ARa (AR0 ((AR5 (@YF7d.segG1 _ _)) md0))) Hmap_apart mat0)).
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
Variable RX : (word -> option byte) -> Prop.
Hypothesis RXs : rstable RX.
Hypothesis RXt : pstable WIN1T RX.
Lemma RX_stableS : pstable WIN1S RX.
Proof. intros m m' FR. img_apply (RXt m m'). intros x Hx. img_apply FR. intros Hw. img_exact (Hx (WIN1S_WIN1T _ Hw)). Qed.
Lemma rstable_and : forall R1 R2, rstable R1 -> rstable R2 -> rstable (fun m => R1 m /\ R2 m).
Proof.
clearP. intros R1 R2 [A1 B1] [A2 B2]. split.
- intros m m' FR [H1 H2]. split; [img_try (img_exact (A1 m m' FR H1)) | img_try (img_exact (A2 m m' FR H2))].
- intros m m' d len Hp FR [H1 H2]. split; [img_try (img_exact (B1 m m' d len Hp FR H1)) | img_try (img_exact (B2 m m' d len Hp FR H2))].
Qed.
Lemma pstable_and : forall (Xw : Z -> Prop) R1 R2, pstable Xw R1 -> pstable Xw R2 -> pstable Xw (fun m => R1 m /\ R2 m).
Proof. clearP. intros Xw R1 R2 A1 A2 m m' FR [H1 H2]. split; [img_try (img_exact (A1 m m' FR H1)) | img_try (img_exact (A2 m m' FR H2))]. Qed.
Lemma PSR_stableS' : forall sh R, Forall run_ok sh -> pstable WIN1S R -> pstable WIN1S (PSR Wy sh R).
Proof. intros sh R OK RS m m' FR [HP HQ]. split; [img_try (img_exact (PS_stable Wy sh OK m m' FR HP)) | img_try (img_exact (RS m m' FR HQ))]. Qed.
Lemma pairwise_disjoint_map : forall (E' : env) (f : YQ0b.region -> YQ0b.region) rs,
(forall r, YQ0b.r_base (f r) = YQ0b.r_base r /\ YQ0b.r_lo (f r) = YQ0b.r_lo r /\ YQ0b.r_hi (f r) = YQ0b.r_hi r) ->
pairwise_disjoint E' rs -> pairwise_disjoint E' (map f rs).
Proof.
clearP. intros E' f rs Hf. induction rs as [|r rs IH]; cbn; intros H; [img_try (img_exact I)|]. destruct H as [HA HP]. split; [|img_try (img_exact (IH HP))].
clear IH HP. induction rs as [|r2 rs IH2]; cbn in *; [img_try (img_exact I)|]. destruct HA as [HD HA]. split; [|img_try (img_exact (IH2 HA))].
unfold extent_disjoint in *. destruct (Hf r) as (-> & -> & ->). destruct (Hf r2) as (-> & -> & ->). img_exact HD.
Qed.
Lemma at_S_setchunks : forall (Wx : world tfxsegs) md X P ss W' c' lo cs,
at_S Wx md X P ss W' c' -> regions_wf (setchunks lo cs (ss_mem ss)) = true ->
(forall (E' : env) (m : word -> option byte), env_agree sHAV E0 E' -> P m ->
forall r, In r (ss_mem ss) -> YQ0b.r_base r = None -> YQ0b.r_lo r = lo ->
region_ok tfxsegs E' (mrestrict (w_H Wx) m) r -> Forall (YQ0b.chunk_ok tfxsegs E' (mrestrict (w_H Wx) m) (base_val E' None)) cs) ->
at_S Wx md X P (mkSS (ss_pc ss) (ss_regs ss) (setchunks lo cs (ss_mem ss)) (ss_resv ss) (ss_facts ss)) W' c'.
Proof.
clearP. intros Wx md X P ss W' c' lo cs HR Hwf HOK. destruct HR as (-> & ms & mat & E' & -> & HE & HS & MEQ & PRS & HPm).
split; [img_refl|]. exists ms, mat, E'. split; [img_refl|]. split; [img_try (img_exact HE)|]. split; [|img_try (img_exact (conj MEQ (conj PRS HPm)))].
destruct HS as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & (Hwf0 & Hok & Hpd) & H9). unfold st_ok; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts].
repeat (split; [img_try (assumption)|]). split; [| img_try (img_exact H9)]. split; [img_try (img_exact Hwf)|]. split.
- img_apply Forall_forall. intros r' Hr'. unfold setchunks in Hr'. apply in_map_iff in Hr' as (r & <- & Hr). pose proof (proj1 (Forall_forall _ _) Hok r Hr) as RO.
destruct (YQ0b.r_base r) as [b|] eqn:Eb; [img_try (img_exact RO)|]. destruct (Z.eqb_spec (YQ0b.r_lo r) lo) as [El|El]; [|img_try (img_exact RO)].
pose proof RO as (Q1 & Q2 & Q3 & Q4). unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks]. rewrite Eb in *.
split; [img_try (img_exact Q1)|]. split; [img_try (img_exact Q2)|]. split; [img_try (img_exact Q3)|]. cbn [restrict ms_mem] in *. img_exact (HOK E' (ms_mem ms) HE HPm r Hr Eb El RO).
- unfold setchunks. img_apply pairwise_disjoint_map; [|img_try (img_exact Hpd)]. intros [b lo0 hi0 wlo0 whi0 cs0]. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi].
destruct b; [img_try (repeat split; img_refl)|]. destruct (Z.eqb lo0 lo); repeat split; img_refl.
Qed.
Lemma chunk_ok_CVal_eqv : forall (E' : env) m base off w (v v' : sv),
sv_denot E' v = sv_denot E' v' -> YQ0b.chunk_ok tfxsegs E' m base (YQ0b.mkChunk off (CVal w v')) -> YQ0b.chunk_ok tfxsegs E' m base (YQ0b.mkChunk off (CVal w v)).
Proof. clearP. intros E' m base off w v v' Hv H i Hi. destruct (H i Hi) as (b & Hb & Hm). exists b. cbn [YQ0b.c_off YQ0b.c_val cbyte] in *. rewrite Hv. img_exact (conj Hb Hm). Qed.
Lemma RES2T_ne : idx <> res -> U E0 RES2T = U E0 (SOff aRES 0).
Proof.
intros Hne. pose proof Hidx as HI. pose proof Hres as [HRS _]. unfold kMaxNumChunks in HI, HRS. clear - Hne HI HRS.
unfold RES2T. pin_zevS. rewrite EaNCH, EaRES. unfold w64. rewrite !unsigned_lit_small by zlia. rewrite !Z.add_0_r.
rewrite !(zcanon_small res) by zlia. rewrite !(zcanon_small idx) by zlia. img_change (Z.land (zcanon 14) 63) with 14.
destruct (Z.ltb_spec idx res); [|img_try (exfalso; zlia)]. img_change (zcanon 1) with 1. img_change (Z.lxor 1 1) with 0. img_change (zcanon 0) with 0.
img_change (zcanon (Z.shiftl 0 14)) with 0. rewrite Z.add_0_r. img_apply zcanon_small. zlia.
Qed.
Lemma RES2T_eq : idx = res -> U E0 RES2T = U E0 (SOff aRES 16384).
Proof.
intros Heq. pose proof Hidx as HI. pose proof Hres as [HRS _]. unfold kMaxNumChunks in HI, HRS. clear - Heq HI HRS.
unfold RES2T. pin_zevS. rewrite EaNCH, EaRES. unfold w64. rewrite !unsigned_lit_small by zlia. rewrite !Z.add_0_r.
rewrite !(zcanon_small res) by zlia. rewrite !(zcanon_small idx) by zlia. img_change (Z.land (zcanon 14) 63) with 14.
destruct (Z.ltb_spec idx res); [img_try (exfalso; zlia)|]. img_change (zcanon 0) with 0. img_change (Z.lxor 0 1) with 1. img_change (zcanon 1) with 1.
img_change (zcanon (Z.shiftl 1 14)) with 16384. img_refl.
Qed.
Lemma sv_denot_eq_of_U : forall (E' : env) (a b : sv), env_agree sHAV E0 E' -> sv_atoms_lt sHAV a = true -> sv_atoms_lt sHAV b = true ->
U E0 a = U E0 b -> sv_denot E' a = sv_denot E' b.
Proof.
clearP. intros E' a b HE Ha Hb HU. rewrite (sv_denot_agree sHAV E0 E' a HE Ha), (sv_denot_agree sHAV E0 E' b HE Hb).
img_apply bv_eq. img_exact HU.
Qed.
Local Ltac s_runR HR tbl tblok stop ss' HX HP :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let st := img_ev (snd (sym_run_toN_sh tfxsegs tbl FUEL stop ss)) in
eapply SRr_bind;
[ img_try (eapply (at_S_runR Wx tbl tblok stop md X P ss ss' st W' c' HR);
[ (img_case; vm_compute); img_refl | img_exact I | img_exact HX | (img_case; vm_compute); img_refl | img_exact HP | (img_case; vm_compute); img_refl ])
| img_try (clear HR; let W2 := fresh "W" in let c2 := fresh "c" in intros W2 c2 _ HR) ] end.
Local Ltac s_runS HR tbl tblok stop ss' HX HP :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let st := img_ev (snd (sym_run_toN_sh tfxsegs tbl FUEL stop ss)) in
eapply SRr_bind;
[ img_try (eapply (at_S_runS Wx tbl tblok stop md X P ss ss' st W' c' HR);
[ (img_case; vm_compute); img_refl | img_exact I | img_exact HX | (img_case; vm_compute); img_refl | img_exact HP | (img_case; vm_compute); img_refl ])
| img_try (clear HR; let W2 := fresh "W" in let c2 := fresh "c" in intros W2 c2 _ HR) ] end.
Local Ltac s_ecallR HR tbl tblok ss' HX HP :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
eapply (at_S_run_ecallR Wx tbl tblok 0x7ffffff0 md X P ss ss' W' c' HR);
[ img_try ((img_case; vm_compute); img_refl) | img_refl | img_try (img_exact HX) | img_try ((img_case; vm_compute); img_refl) | img_try (img_exact HP) | img_try ((img_case; vm_compute); img_refl) ] end.
Lemma skel_apart_QS : forall (E' : env) (pb : bool) r, env_agree sHAV E0 E' -> skel_okb pb (skel r) = true -> YQ0b.r_base r <> Some aQS ->
base_val E' (YQ0b.r_base r) + YQ0b.r_hi r <= QSv \/ QSv + 8 <= base_val E' (YQ0b.r_base r) + YQ0b.r_lo r.
Proof.
intros E' pb r [HE _] Hs Hnq. destruct r as [b lo hi wlo whi cs]. unfold skel in Hs. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi] in *.
pose proof high_facts as (F1 & F2 & _ & _ & _ & _ & F7 & F8 & F9 & F10 & _ & _ & _ & _ & F15).
pose proof map_facts as (M1 & M2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _ & PB & _). pose proof map_zoneN as MZ. pose proof size_facts as (_ & _ & Z3 & Z4 & _ & _ & Z7 & Z8 & _ & Z10 & _).
pose proof Hidx as HI. pose proof Nrange as NR. pose proof BSLv_range as HB. destruct Hsp as (S1 & _ & S3 & _).
destruct Hmap_apart as (_ & _ & _ & MQ & _). pose proof HCX as (_ & _ & QT & CQ). unfold zdisjoint in MQ, QT, CQ. cbn [fst snd] in MQ, QT, CQ.
pose proof (u64_range (getr regs0 2)) as U2.
destruct (skel_cases pb b lo hi wlo whi Hs) as [(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|(Epb & -> & A1 & A2)]]]]]]]; cbn [base_val].
- clear - A1 A2 F9 HI MZ. unfold zone3, TFX_IMG_LO, kLowShadowBeg, QSv, kHighMemBeg in *. try unfold Qb in *. zlia.
- rewrite (HE 2%nat ltac:(img_try (unfold sHAV; zlia))), E2. pose proof stack_ivs as (_ & _ & _ & SQ).
clear - SQ A1 A2 HI U2 MZ. unfold QSv, ASTACK, kPtrArrayResv, kMaxNumChunks in *. try unfold Qb in *. try unfold sp0 in *.
destruct SQ as [SQ|SQ]; [img_try (right; zlia) | img_try (left; zlia)].
- rewrite (HE 32%nat ltac:(img_try (unfold sHAV; zlia))), EaT. unfold w64. rewrite unsigned_lit_small by (img_try (clear - F1 F2 MZ; numconst; try unfold T in *; zlia)).
clear - A1 A2 QT HI MZ. unfold QSv, kThreadObjSize, kPtrArrayResv, kMaxNumChunks in *. try unfold T in *. try unfold Qb in *. destruct QT as [QT|QT]; [img_try (right; zlia) | img_try (left; zlia)].
- rewrite (HE 33%nat ltac:(img_try (unfold sHAV; zlia))), EaC. unfold w64. rewrite unsigned_lit_small by (img_try (clear - F7 F8 MZ; ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; zlia)).
clear - A1 A2 CQ HI MZ. unfold QSv, kPtrArrayResv, kMaxNumChunks in *. try unfold Qb in *. destruct CQ as [CQ|CQ]; [img_try (left; zlia) | img_try (right; zlia)].
- unfold aMAP. rewrite (HE 45%nat ltac:(img_try (unfold sHAV; zlia))), EaMAP. unfold w64. rewrite unsigned_lit_small by (img_try (clear - M1 M2 Z8 MZ; ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; zlia)).
clear - A1 A2 MQ HI Z8 MZ. unfold QSv, kPtrArrayResv, kMaxNumChunks in *. try unfold Qb in *. destruct MQ as [MQ|MQ]; [img_try (left; zlia) | img_try (right; zlia)].
- exfalso. img_apply Hnq. img_refl.
- unfold aBSL. rewrite (HE 55%nat ltac:(img_try (unfold sHAV; zlia))), EaBSL. unfold w64. rewrite unsigned_lit_small by (img_try (clear - HB MZ; unfold TFX_INST in *; zlia)).
clear - A1 A2 HB F9 HI MZ. unfold zone3, TFX_IMG_LO, kLowShadowBeg, QSv, kHighMemBeg, TFX_INST in *. try unfold Qb in *. zlia.
- unfold aPBS. rewrite (HE 66%nat ltac:(img_try (unfold sHAV; zlia))), EaPB. unfold w64. rewrite PB in *.
assert (HND : 8 * (N8D / 8) <= N8D) by (img_try (img_apply Z.mul_div_le; zlia)). assert (HM : N8D / 8 + 1024 <= MSv / 8) by (img_try (img_apply Z.div_le_lower_bound; zlia)).
pose proof (Z.div_pos N8D 8 ltac:(img_try (zlia)) ltac:(img_try (zlia))) as DP.
rewrite unsigned_lit_small by (img_try (clear - SM1 SM2 HND HM DP MZ; unfold kHighShadowBeg, kHighShadowEnd in *; zlia)).
clear - A1 A2 SM1 SM2 HND HM DP F9 HI MZ. unfold zone3, TFX_IMG_LO, kLowShadowBeg, QSv, kHighShadowBeg, kHighShadowEnd, kHighMemBeg in *. try unfold Qb in *. zlia.
Qed.
Definition QSPX (m : word -> option byte) : Prop := QSP Wy m /\ RX m.
Lemma segNE : idx <> res -> forall c, at_S Wy md1 WIN (PSR Wy SH2 QSPX) S_X Wy c -> SRr tfxsegs Wy c (at_S Wy md1 WIN (PSR Wy SH2 RX) S_YJ).
Proof.
intros Hne c HR. pose proof WIN1R_WIN as HX. pose proof SH_ok as (OK0 & OK1 & OK2). pose proof (rstable_and _ _ (QSP_rstable Wy) RXs) as RS.
pose proof (PSR_stable Wy SH2 QSPX OK2 RS) as HP2.
pose proof high_facts as (_ & _ & _ & _ & _ & _ & _ & _ & F9 & F10 & _). pose proof Hidx as HI. pose proof Hres as [HRS _].
ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kPtrArrayResv in F9, F10. unfold kMaxNumChunks in HI, HRS.
s_arm HR BC_EQ false (SOff aNCH 0) (SOff aRES 0).
{ clear - Hne HI HRS. arm_zevS. rewrite EaNCH, EaRES. unfold w64. rewrite !unsigned_lit_small by zlia. zcanon_simp. img_apply Z.eqb_neq. zlia. }
s_runR HR tfxtbl_rr tfxtbl_rr_ok (0x3650c + D_150) S_Y0 HX HP2.
s_pin HR (12%bv : bv 5) (SOff aQS 0).
{ clear - HI F9 F10. pin_zevS. rewrite EaQS, EaQ, EaNCH. unfold w64. unfold QSv in *. rewrite !unsigned_lit_small by (img_try (try unfold Qb in *; zlia)).
zcanon_simp. land_lits. rewrite Z.shiftl_mul_pow2 by zlia. img_change (2 ^ 3) with 8. zcanon_simp. try unfold Qb in *. zlia. }
lazymatch type of HR with at_S _ _ _ _ ?ss _ _ =>
let rs1 := img_ev (setchunks (TFX_INST + o_sec_reserved) [YQ0b.mkChunk (TFX_INST + o_sec_reserved) (CVal 8 RES2T)] (ss_mem ss)) in
apply (at_S_setchunks Wy md1 WIN _ ss _ _ (TFX_INST + o_sec_reserved) [YQ0b.mkChunk (TFX_INST + o_sec_reserved) (CVal 8 RES2T)]) in HR;
[ img_try (img_change (setchunks (TFX_INST + o_sec_reserved) [YQ0b.mkChunk (TFX_INST + o_sec_reserved) (CVal 8 RES2T)] (ss_mem ss)) with rs1 in HR; cbn [ss_pc ss_regs ss_resv ss_facts] in HR) | img_try ((img_case; vm_compute); img_refl) | ] end.
2:{ intros E' m HE _ r Hr Hb Hl RO.
lazymatch type of Hr with In _ ?l =>
pose proof (proj1 (forallb_forall _ _) (ltac:(img_eqrefl) : forallb (fun r => negb (match YQ0b.r_base r with None => Z.eqb (YQ0b.r_lo r) (TFX_INST + o_sec_reserved) | Some _ => false end)
|| existsb (fun c => chunk_eqb c (YQ0b.mkChunk (TFX_INST + o_sec_reserved) (CVal 8 (SOff aRES 0)))) (YQ0b.r_chunks r)) l = true) r Hr) as CK end.
cbn beta in CK. rewrite Hb, Hl, Z.eqb_refl in CK. cbn [negb orb] in CK.
destruct RO as (_ & _ & _ & RC). img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
apply existsb_exists in CK as (k0 & Hk0 & CK). apply chunk_eqb_eq in CK. (subst k0; cbv beta).
pose proof (proj1 (Forall_forall _ _) RC _ Hk0) as RC0. rewrite Hb in RC0. img_apply (chunk_ok_CVal_eqv E' _ _ _ _ RES2T (SOff aRES 0)); [|img_try (img_exact RC0)].
img_apply (sv_denot_eq_of_U E' _ _ HE); [img_try ((img_case; vm_compute); img_refl) | img_try ((img_case; vm_compute); img_refl) | img_try (img_exact (RES2T_ne Hne))]. }
lazymatch type of HR with at_S _ _ _ _ ?ss _ _ =>
let rs := img_ev (trimscratch (-2480) (ss_mem ss)) in
apply (at_S_submem Wy md1 WIN _ ss _ _ rs) in HR; [| img_try ((img_case; vm_compute); img_refl) | img_try ((img_case; vm_compute); img_refl)] end.
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
pose proof (at_S_forget Wx md X P ss W' c' sJY [1; 15; 17; 20]%bv HR ltac:(img_try (unfold sHAV, sJY; zlia)) eq_refl
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))) as HR2; clear HR; rename HR2 into HR end.
s_noconds HR.
apply (at_S_addreg Wy md1 WIN _ _ _ _ R_qs) in HR; [| img_refl |].
2:{ intros E' m HE MEQ PRS [HP [HQ _]] HM. pose proof (proj1 HE) as HEn.
assert (BQ : base_val E' (Some aQS) = QSv).
{ cbn [base_val]. unfold aQS. rewrite (HEn 52%nat ltac:(img_try (unfold sHAV; zlia))), EaQS. unfold w64. img_apply unsigned_lit_small. clear - HI F9 F10. unfold QSv in *. try unfold Qb in *. zlia. }
split.
- unfold region_ok, R_qs. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks]. rewrite BQ.
split; [img_try (clear - HI F9; unfold QSv in *; try unfold Qb in *; zlia)|]. split; [img_try (clear - HI F9 F10; unfold QSv in *; try unfold Qb in *; zlia)|]. split; [|img_try (img_apply Forall_nil)].
intros o Ho. img_apply apresent_writable_off; [img_try (off_by ltac:(clear - Ho HI F9 F10; unfold zone3, TFX_IMG_LO, kLowShadowBeg, QSv, TFX_IMG_END in *; try unfold Qb in *; zlia)) |]. img_apply HQ. zlia.
- intros r2 Hr2. unfold extent_disjoint, R_qs. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi]. rewrite !BQ.
lazymatch type of Hr2 with In _ ?l =>
pose proof (proj1 (forallb_forall _ _) (ltac:(img_eqrefl) : forallb (fun r => skel_okb false (skel r) && negb (obase_eqb (YQ0b.r_base r) (Some aQS))) l = true) r2 Hr2) as CK end.
cbn beta in CK. apply andb_prop in CK as [CK1 CK2].
assert (NB : YQ0b.r_base r2 <> Some aQS) by (img_try (intros Eq; rewrite Eq in CK2; discriminate CK2)).
pose proof (skel_apart_QS E' false r2 HE CK1 NB) as AP. clear - AP. zlia. }
s_station HR S_YJ.
img_apply SRr_ret. eapply at_S_weaken; [img_try (img_exact HR) | img_try (intros a Ha; img_exact Ha) | img_try (intros m [HP [_ HQ]]; img_exact (conj HP HQ))].
Qed.
Lemma segEQa : forall (R : (word -> option byte) -> Prop), rstable R -> idx = res ->
forall c, at_S Wy md1 WIN (PSR Wy SH2 R) S_X Wy c -> SRr tfxsegs Wy c (at_N Wy md1 WIN (PSR Wy SH2 R) S_V).
Proof.
intros R RS Heq c HR. pose proof WIN1R_WIN as HX. pose proof SH_ok as (OK0 & OK1 & OK2). pose proof (PSR_stable Wy SH2 R OK2 RS) as HP2.
pose proof Hidx as HI. pose proof Hres as [HRS _]. unfold kMaxNumChunks in HI, HRS.
s_arm HR BC_EQ true (SOff aNCH 0) (SOff aRES 0).
{ clear - Heq HI HRS. arm_zevS. rewrite EaNCH, EaRES. unfold w64. rewrite !unsigned_lit_small by zlia. zcanon_simp. img_apply Z.eqb_eq. zlia. }
s_runR HR tfxtbl_rr tfxtbl_rr_ok (0x6ed20 + D_2c4) S_V0 HX HP2.
s_ecallR HR tfxtbl_rtC tfxtbl_rtC_ok S_V HX HP2.
Qed.
Lemma zev_SAlu : forall rho op a b, zev rho (SAlu op a b) = zcanon (zalu_raw 63 64 op (zev rho a) (zev rho b)).
Proof. clearP. intros; img_refl. Qed.
Lemma zev_SLit : forall rho z, zev rho (SLit z) = zcanon z.
Proof. clearP. intros; img_refl. Qed.
Lemma zev_SOff : forall rho a k, zev rho (SOff a k) = zcanon (rho a + k).
Proof. clearP. intros; img_refl. Qed.
Lemma segJ2 : forall (X : Z -> Prop), (forall a, WIN a -> X a) ->
forall W' c, at_S Wy md1 X (PSR Wy SH2 RX) S_ZJ W' c -> SRr tfxsegs W' c (at_S Wy md1 X (PSR Wy SH2 RX) S_TJ0).
Proof.
intros X HXW W1 c HR. pose proof SH_ok as (OK0 & OK1 & OK2). pose proof (PSR_stableS' SH2 RX OK2 RX_stableS) as HP2.
assert (HX : forall a, WIN1S a -> X a) by (img_try (intros a Ha; apply HXW, WIN1S_WIN, Ha)).
pose proof size_facts as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10 & Z11 & Z12 & Z13 & Z14). unfold MALLOC_MAX in Z1, Z8.
s_runS HR tfxtbl_rr tfxtbl_rr_ok (0x36548 + D_150) (runto (0x36548 + D_150) S_ZJ) HX HP2.
s_pin HR (11%bv : bv 5) (SOff aBSL (-104)).
{ pose proof BSLv_range as HB. clear - Z8 Z9 HB.
img_apply U_eq_by_zev; [img_refl | img_refl |].
lazymatch goal with |- _ = zev _ (SAlu ALU_ADD _ (SAlu ALU_SLL (SAlu ALU_XOR ?t19 _) _)) => img_change t19 with CLZ_TERM end.
rewrite zev_SOff, (zev_SAlu _ ALU_ADD), (zev_SAlu _ ALU_SLL), (zev_SAlu _ ALU_XOR), !zev_SLit, zev_CLZ_TERM. cbn [zalu_raw]. unfold rho_of.
unfold_atoms. rewrite EaBSL, EaMS. unfold w64. rewrite !unsigned_lit_small by (img_try (unfold TFX_INST in *; zlia)).
apply Z.mod_divide in Z9 as [p Hp]; [|img_try (zlia)].
replace MSv with (4096 * p) by zlia. try rewrite (zcanon_id 63) by (img_try (unfold M64; zlia)).
assert (LG : Z.lxor (clzS (4096 * p)) 63 = Z.log2 p + 12) by (img_try (img_apply clz_index; zlia)).
assert (LGR : 0 <= Z.log2 p + 12 <= 63) by (img_try (pose proof (Z.log2_nonneg p); assert (Z.log2 p <= Z.log2 (2 ^ 20)) by (img_apply Z.log2_le_mono; zlia); rewrite Z.log2_pow2 in * by zlia; zlia)).
rewrite (zcanon_id (Z.lxor (clzS (4096 * p)) 63)) by (img_try (rewrite LG; unfold M64; zlia)). rewrite LG.
unfold TFX_INST in *. zcanon_simp. land_lits. rewrite Z.shiftl_mul_pow2 by zlia. img_change (2 ^ 3) with 8.
unfold YF7f.BSLv, YF7f.LGv. rewrite Hp. rewrite Z.div_mul by zlia. unfold TFX_INST. zcanon_simp. zlia. }
s_station HR S_ZJ1.
lazymatch type of HR with at_S _ _ ?X0 _ ?ss _ _ =>
apply (at_S_setchunks Wy md1 X0 _ ss _ _ (TFX_INST + o_sec_mutex) MUTCH) in HR;
[ lazymatch type of HR with at_S _ _ _ _ ?ss2 _ _ => replace ss2 with S_ZJ1s in HR by (img_try ((img_case; vm_compute); img_refl)) end | (img_case; vm_compute); img_refl | ] end.
2:{ intros E' m HE _ r Hr Hb Hl RO.
lazymatch type of Hr with In _ ?l =>
pose proof (proj1 (forallb_forall _ _) (ltac:(img_eqrefl) : forallb (fun r => negb (match YQ0b.r_base r with None => Z.eqb (YQ0b.r_lo r) (TFX_INST + o_sec_mutex) | Some _ => false end)
|| existsb (fun c => chunk_eqb c (YQ0b.mkChunk (TFX_INST + o_sec_mutex) (CVal 4 (SLit 1)))) (YQ0b.r_chunks r)) l = true) r Hr) as CK end.
cbn beta in CK. rewrite Hb, Hl, Z.eqb_refl in CK. cbn [negb orb] in CK.
destruct RO as (_ & _ & _ & RC). apply existsb_exists in CK as (k0 & Hk0 & CK). apply chunk_eqb_eq in CK. (subst k0; cbv beta).
pose proof (proj1 (Forall_forall _ _) RC _ Hk0) as RC0. rewrite Hb in RC0. cbn [base_val] in RC0 |- *. unfold MUTCH.
repeat (img_apply Forall_cons; [|img_try (try img_apply Forall_nil)]);
intros i Hi; cbn in Hi; cbn [YQ0b.c_off YQ0b.c_val YQ0b.c_len cbyte].
- destruct (RC0 0 ltac:(img_try (cbn; zlia))) as (b & Hb1 & Hm1). cbn [YQ0b.c_off YQ0b.c_val cbyte] in Hb1, Hm1.
assert (i = 0) by zlia. (subst i; cbv beta). exists b. split; [| img_try (rewrite Z.add_0_r, <- (Z.add_0_r (0 + (TFX_INST + o_sec_mutex))); img_exact Hm1)].
rewrite <- Hb1. img_case; vm_compute. all: img_refl.
- destruct (RC0 1 ltac:(img_try (cbn; zlia))) as (b & Hb1 & Hm1). cbn [YQ0b.c_off YQ0b.c_val cbyte] in Hb1, Hm1.
assert (i = 0) by zlia. (subst i; cbv beta). exists b. split; [| img_try (rewrite Z.add_0_r, <- Z.add_assoc; img_exact Hm1)].
rewrite <- Hb1. img_case; vm_compute. all: img_refl.
- assert (Hcase : i = 0 \/ i = 1) by zlia. destruct Hcase as [-> | ->].
+ destruct (RC0 2 ltac:(img_try (cbn; zlia))) as (b & Hb1 & Hm1). cbn [YQ0b.c_off YQ0b.c_val cbyte] in Hb1, Hm1.
exists b. split; [| img_try (rewrite Z.add_0_r, <- Z.add_assoc; img_exact Hm1)]. rewrite <- Hb1. img_case; vm_compute. all: img_refl.
+ destruct (RC0 3 ltac:(img_try (cbn; zlia))) as (b & Hb1 & Hm1). cbn [YQ0b.c_off YQ0b.c_val cbyte] in Hb1, Hm1.
exists b. split; [| img_try (replace (0 + (TFX_INST + o_sec_mutex + 2) + 1) with (0 + (TFX_INST + o_sec_mutex) + 3) by zlia; img_exact Hm1)]. rewrite <- Hb1. img_case; vm_compute. all: img_refl. }
s_runS HR tfxtbl_rr tfxtbl_rr_ok (0x31be0 + D_150) S_TJ0 HX HP2.
img_apply SRr_ret; img_exact HR.
Qed.
Lemma segJ : forall (X : Z -> Prop), (forall a, WIN a -> X a) ->
forall c, at_S Wy md1 X (PSR Wy SH2 RX) S_YJ Wy c -> SRr tfxsegs Wy c (at_S Wy md1 X (PSR Wy SH2 RX) S_TJ0).
Proof.
intros X HXW c HR. pose proof SH_ok as (OK0 & OK1 & OK2). pose proof (PSR_stableS' SH2 RX OK2 RX_stableS) as HP2.
assert (HX : forall a, WIN1S a -> X a) by (img_try (intros a Ha; apply HXW, WIN1S_WIN, Ha)).
s_runS HR tfxtbl_rr tfxtbl_rr_ok (0x36538 + D_150) S_ZJ0 HX HP2.
assert (BC : forall b : bool, b = true \/ b = false) by (img_try (intros [|]; [img_try (left) | img_try (right)]; img_refl)).
destruct (BC (branch_taken BC_LTU (sv_denot E0 (SAlu ALU_ADD (SOff aMS 0) (SOff aI2 0))) (sv_denot E0 (SOff aI3 0)))) as [TK|TK]; clear BC.
- s_arm HR BC_LTU true (SAlu ALU_ADD (SOff aMS 0) (SOff aI2 0)) (SOff aI3 0). { img_exact TK. }
s_runS HR tfxtbl_rr tfxtbl_rr_ok (0x36540 + D_150) S_ZJt HX HP2.
lazymatch type of HR with at_S ?Wx ?md ?X0 ?P ?ss ?W' ?c' =>
pose proof (at_S_forget Wx md X0 P ss W' c' sMX [12]%bv HR ltac:(img_try (unfold sHAV, sMX; zlia)) eq_refl
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))) as HR2; clear HR; rename HR2 into HR end.
s_noconds HR. s_station HR S_ZJ. img_exact (segJ2 X HXW _ _ HR).
- s_arm HR BC_LTU false (SAlu ALU_ADD (SOff aMS 0) (SOff aI2 0)) (SOff aI3 0). { img_exact TK. }
s_runS HR tfxtbl_rr tfxtbl_rr_ok (0x36540 + D_150) S_ZJf HX HP2.
lazymatch type of HR with at_S ?Wx ?md ?X0 ?P ?ss ?W' ?c' =>
pose proof (at_S_forget Wx md X0 P ss W' c' sMX [12]%bv HR ltac:(img_try (unfold sHAV, sMX; zlia)) eq_refl
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))) as HR2; clear HR; rename HR2 into HR end.
s_noconds HR. s_station HR S_ZJ. img_exact (segJ2 X HXW _ _ HR).
Qed.
End h.
End g.
