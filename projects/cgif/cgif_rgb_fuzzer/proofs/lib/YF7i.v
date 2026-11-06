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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF64 YF3v YF3w YF3x YF41 YF6z YF0a YF7f YF71 YF72 YF73 YF7o YF7p YF7q YF7a YF7g YF7h YF7d YF7e.
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
Local Abbreviation ARb f := (f idx res mb) (only parsing).
Local Abbreviation win_sub_sound := ((ARb (@YF7f.win_sub_sound ly regs0)) Hidx Hres).
Local Abbreviation in_win := (@YF7f.in_win).
Local Abbreviation AR4 f := (AR0 f LY IMG Nrange Hidx Hres) (only parsing).
Local Abbreviation WSKELP_WINP := (AR4 (AR1 (@YF7f.WSKELP_WINP _))).
Local Abbreviation WSKEL1P_WIN1P := (AR4 (AR1 (@YF7f.WSKEL1P_WIN1P _))).
Local Abbreviation WMAP_WINM := ((AR4 (AR1 (@YF7f.WMAP_WINM _))) Hmap).
Local Abbreviation WSKEL_WIN := ((AR4 (AR1 (@YF7f.WSKEL_WIN _))) Hmap).
Local Abbreviation WSKEL1_WIN1 := ((AR4 (AR1 (@YF7f.WSKEL1_WIN1 _))) Hmap).
Local Abbreviation windows_in := ((ARb (@YF7f.windows_in ly regs0)) Hidx Hres).
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
Local Abbreviation img_rw_writable := ((ARb (AR1 (@YF7f.img_rw_writable))) Hidx).
Local Abbreviation ARf f := (f imgk W ly) (only parsing).
Local Abbreviation kept_of_frame := ((ARb ((ARf (@YF7f.kept_of_frame)) regs0)) Hidx).
Local Abbreviation SKEL_TAIL := (@YF7f.SKEL_TAIL imgk).
Local Abbreviation blocks_facts := (@YF7f.blocks_facts _ imgk ly LY IMG).
Local Abbreviation off_T := (ARd (AR1 (@YF7f.off_T _))).
Local Abbreviation off_C := (ARd (AR1 (@YF7f.off_C _))).
Local Abbreviation off_Q := (ARd (AR1 (@YF7f.off_Q _))).
Local Abbreviation off_NB := (@YF7f.off_NB _ imgk ly LY IMG).
Local Abbreviation off_SB := (@YF7f.off_SB _ imgk ly LY IMG).
Local Abbreviation off_shadow := ((ARb (AR1 (@YF7f.off_shadow))) Hidx).
Ltac off_by tac :=
first [ img_apply off_img_high; tac | img_apply off_T; tac | img_apply off_C; tac | img_apply off_Q; tac | img_apply off_NB; tac | img_apply off_SB; tac
| img_apply map_off_img; tac | img_apply off_shadow; tac
| unfold off_img; unfold TFX_IMG_LO; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; tac ].
Local Abbreviation DZONE := (@YF7f.DZONE imgk ly).
Variable DPOST : Z -> (word -> option byte) -> Prop.
Local Abbreviation ARg f := (ARa f Hmap_apart) (only parsing).
Local Abbreviation DZONE_disj := (ARg (AR3 (@YF7f.DZONE_disj _))).
Local Abbreviation RFACTS := (AR1 (@YF7f.RFACTS)).
Local Abbreviation zone_lit := ((AR1 (@YF7f.zone_lit _)) LY IMG Hsp).
Local Abbreviation zone_irw := ((AR1 (@YF7f.zone_irw _)) LY IMG Hsp).
Local Abbreviation zone_T := ((AR1 (@YF7f.zone_T _)) idx res LY IMG Hsp Hidx Hres).
Local Abbreviation zone_C := ((AR1 (@YF7f.zone_C _)) idx res LY IMG Hsp Hidx Hres).
Local Abbreviation tail_ext_ok := (AR2 (AR0 (AR1 (@YF7f.tail_ext_ok _)))).
Local Abbreviation RFACTS_map := ((AR8 ((AR3 (@YF7f.RFACTS_map _)) LY IMG)) Hmap_apart).
Local Abbreviation AR5 f := (f imgk W ly regs0 mem0) (only parsing).
Local Abbreviation at_ST := (AR0 ((AR5 (@YF7f.at_ST _)) md0)).
Local Abbreviation memset_stretch := ((AR8 ((ARb ((AR5 (@YF7f.memset_stretch _ _)) md0 n)) Hsp)) Hmap_apart mat0 DPOST).
Ltac clearM := try clear DPOST; try clear Hmap_apart; try clear Hmap.
Local Abbreviation AR6 f := (AR1 f mem0) (only parsing).
Local Abbreviation at_S := (AR0 (AR6 (@YF7f.at_S _))).
Local Abbreviation at_N := (AR0 (AR6 (@YF7f.at_N _))).
Local Abbreviation at_RETS := ((AR6 (@YF7f.at_RETS _)) ch).
Local Abbreviation pstable := (@YF7f.pstable).
Local Abbreviation stack_shaped := (@YF7f.stack_shaped).
Local Abbreviation window_present := (ARe (AR1 (@YF7f.window_present))).
Local Abbreviation stack_present_of := ((AR0 (AR1 (@YF7f.stack_present_of _))) LY Hsp Hidx).
Local Abbreviation mid_not_WIN1P := (AR2 (AR3 (@YF7f.mid_not_WIN1P _))).
Local Abbreviation mid_not_WIN1 := (ARa (AR3 (@YF7f.mid_not_WIN1 _))).
Local Abbreviation wins_ok := (@YF7f.wins_ok).
Local Abbreviation at_S_run_gen := ((AR0 (AR6 (@YF7f.at_S_run_gen _ _))) LY Hsp Hidx).
Local Abbreviation at_S_run_ecall_gen := ((AR0 (AR6 (@YF7f.at_S_run_ecall_gen _ _))) LY Hsp Hidx).
Local Abbreviation at_S_runP := (AR2 (AR0 (AR6 (@YF7f.at_S_runP _ _)))).
Local Abbreviation at_S_runM := (ARa (AR0 (AR6 (@YF7f.at_S_runM _ _)))).
Local Abbreviation at_S_run_ecallP := (AR2 (AR0 (AR6 (@YF7f.at_S_run_ecallP _ _)))).
Local Abbreviation at_S_run_ecallM := (ARa (AR0 (AR6 (@YF7f.at_S_run_ecallM _ _)))).
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
Local Abbreviation at_S_ret := ((AR0 (AR6 (@YF7f.at_S_ret _))) Htp Hra Hsp Nrange Hidx Hres).
Local Abbreviation kept_of_frame2 := (ARe (AR1 (@YF7f.kept_of_frame2))).
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
Local Abbreviation AR7 f := (f DPOST B S TS HTSD HARm Hidx_def Hres_def Hj0 Hj1 Hj2 Hj3 Hj4 Hj5 Hj9 Hj6 Hj7 Hj8 Hi1 Hi2 Hi3) (only parsing).
Local Abbreviation SREG0_ok := (AR7 ((AR2 (AR0 (AR5 (@YF7p.SREG0_ok _)))) Hpres0)).
Local Abbreviation PAIRS_ok := ((AR2 (AR0 (AR5 (@YF7q.PAIRS_ok _)))) DPOST S).
Local Abbreviation FACTS_ok := ((AR0 (AR5 (@YF7q.FACTS_ok _))) LY IMG Hn Hsp Nrange Hidx Hres DPOST S).
Local Abbreviation SEED_ok := (AR7 ((AR0 (AR5 (@YF7q.SEED_ok _ _))) LY IMG Hn Hsp Nrange Hidx Hres Hpres0)).
Local Abbreviation PBUF := ((ARf (@YF7a.PBUF)) regs0 ch).
Local Abbreviation PBUF_stableP := (AR2 (ARb ((ARf (@YF7a.PBUF_stableP _)) regs0 n ch))).
Local Abbreviation PBUF_stableM := (ARa (ARb ((ARf (@YF7a.PBUF_stableM _)) regs0 n ch))).
Local Abbreviation seg0 := (AR7 ((AR0 ((AR5 (@YF7a.seg0 _ _)) md0)) LY IMG Hn Htp Hra4096 Hsp Hch Nrange Hidx Hres Hpres0 mat0 U1)).
Local Abbreviation appregs := (@YF7g.appregs).
Local Abbreviation st_ok_appregs := (@YF7g.st_ok_appregs _ imgk).
Local Abbreviation at_S_app := (AR0 (AR6 (@YF7g.at_S_app _))).
Local Abbreviation WIN1N := ((AR1 (@YF7g.WIN1N)) n).
Local Abbreviation WINPN := ((AR1 (@YF7g.WINPN)) n).
Local Abbreviation WSKEL1N := (@YF7g.WSKEL1N imgk).
Local Abbreviation WIN1N_WINPN := ((AR3 (@YF7g.WIN1N_WINPN)) Hidx).
Local Abbreviation windows_WIN1N := (AR4 (AR1 (@YF7g.windows_WIN1N _))).
Local Abbreviation mid_not_WIN1N := (AR2 (AR3 (@YF7g.mid_not_WIN1N _))).
Local Abbreviation at_S_runN := (AR2 (AR0 (AR6 (@YF7g.at_S_runN _ _)))).
Local Abbreviation PBUF_stableN := (AR2 (ARb ((ARf (@YF7g.PBUF_stableN _)) regs0 n ch))).
Local Abbreviation at_S_val := (AR0 (AR6 (@YF7g.at_S_val _))).
Local Abbreviation memset_stretchW := ((AR5 (@YF7g.memset_stretchW _)) md0 n idx res Hsp Nrange Hidx Hres mat0 DPOST S).
Local Abbreviation at_S_memset := ((AR0 ((AR5 (@YF7g.at_S_memset _)) md0)) Hsp Nrange Hidx Hres mat0 DPOST S).
Local Abbreviation WIN1T := (ARc (@YF7g.WIN1T)).
Local Abbreviation WIN1T_WIN := (AR8 (AR3 (@YF7g.WIN1T_WIN _))).
Local Abbreviation windows_WIN1T := ((AR4 (AR1 (@YF7g.windows_WIN1T _))) Hmap).
Local Abbreviation WIN1T_WIN1_aux := (AR8 (AR3 (@YF7g.WIN1T_WIN1_aux _))).
Local Abbreviation mid_not_WIN1T := (ARa (AR3 (@YF7g.mid_not_WIN1T _))).
Local Abbreviation at_S_runT := (ARa (AR0 (AR6 (@YF7g.at_S_runT _ _)))).
Local Abbreviation at_S_run_ecallT := (ARa (AR0 (AR6 (@YF7g.at_S_run_ecallT _ _)))).
Local Abbreviation PBUFW := ((AR1 (@YF7g.PBUFW)) ch).
Local Abbreviation PBUFW_stableT := (ARa (ARb ((AR1 (@YF7g.PBUFW_stableT _)) n ch))).
Local Abbreviation WIN1S := (ARc (@YF7h.WIN1S)).
Local Abbreviation WSKEL1S := (@YF7h.WSKEL1S imgk).
Local Abbreviation WIN1S_WIN1T := (ARc (@YF7h.WIN1S_WIN1T)).
Local Abbreviation WIN1S_WIN := (AR8 (AR3 (@YF7h.WIN1S_WIN _))).
Local Abbreviation windows_WIN1S := ((AR4 (AR1 (@YF7h.windows_WIN1S _))) Hmap).
Local Abbreviation mid_not_WIN1S := (ARa (AR3 (@YF7h.mid_not_WIN1S _))).
Local Abbreviation at_S_runS := (ARa (AR0 (AR6 (@YF7h.at_S_runS _ _)))).
Local Abbreviation at_S_run_ecallS := (ARa (AR0 (AR6 (@YF7h.at_S_run_ecallS _ _)))).
Local Abbreviation brun := (@YF7h.brun).
Local Abbreviation run_ok := (@YF7h.run_ok n mb).
Local Abbreviation PS := ((AR1 (@YF7h.PS)) n ch mb).
Local Abbreviation runs_not_WIN1S := (ARg (AR3 (@YF7h.runs_not_WIN1S _))).
Local Abbreviation runs_not_stack := ((AR8 ((AR3 (@YF7h.runs_not_stack _)) LY Hsp)) Hmap_apart).
Local Abbreviation PS_stable := (ARg (ARb ((AR1 (@YF7h.PS_stable _)) n ch))).
Local Abbreviation cut1 := (@YF7h.cut1).
Local Abbreviation cut := (@YF7h.cut).
Local Abbreviation cut_sound := ((AR8 (ARb ((AR6 (@YF7h.cut_sound _)) n))) DPOST S).
Local Abbreviation cut_ok := ((ARb (@YF7h.cut_ok ly regs0 mem0 n)) Hidx Hres DPOST S).
Local Abbreviation at_S_memsetS := ((AR8 ((AR0 ((AR5 (@YF7h.at_S_memsetS _ _)) md0)) LY Hsp)) Hmap_apart mat0 DPOST S).
Local Abbreviation skel_okb := (@YF7h.skel_okb imgk).
Local Abbreviation skel_cases := ((ARe (@YF7h.skel_cases imgk)) Hres S Hidx_def Hres_def).
Local Abbreviation AR9 f := (f DPOST S Hidx_def Hres_def) (only parsing).
Local Abbreviation skel_apart := (AR9 (ARg (AR0 (AR6 (@YF7h.skel_apart _))))).
Local Abbreviation skel_u64 := (AR9 (ARa (AR0 (AR6 (@YF7h.skel_u64 _))))).
Local Abbreviation memset_ext_of_skel := (AR9 (ARg (AR0 (AR6 (@YF7h.memset_ext_of_skel _))))).
Local Abbreviation memset_u64_of_skel := (AR9 (ARa (AR0 (AR6 (@YF7h.memset_u64_of_skel _))))).
Local Abbreviation WIN1R := ((AR1 (@YF7h.WIN1R)) n mb).
Local Abbreviation WSKEL1R := (@YF7h.WSKEL1R imgk).
Local Abbreviation WIN1R_WIN1S := (ARc (@YF7h.WIN1R_WIN1S)).
Local Abbreviation WIN1R_WIN := (AR8 (AR3 (@YF7h.WIN1R_WIN _))).
Local Abbreviation windows_WIN1R := ((AR4 (AR1 (@YF7h.windows_WIN1R _))) Hmap).
Local Abbreviation mid_not_WIN1R := (ARa (AR3 (@YF7h.mid_not_WIN1R _))).
Local Abbreviation at_S_runR := (ARa (AR0 (AR6 (@YF7h.at_S_runR _ _)))).
Local Abbreviation at_S_run_ecallR := (ARa (AR0 (AR6 (@YF7h.at_S_run_ecallR _ _)))).
Local Abbreviation PSR := ((AR1 (@YF7h.PSR)) n ch mb).
Local Abbreviation rstable := ((AR1 (@YF7h.rstable)) n mb).
Local Abbreviation rstable_true := ((AR1 (@YF7h.rstable_true)) n mb).
Local Abbreviation PSR_stable := (ARg (ARb ((AR1 (@YF7h.PSR_stable _)) n ch))).
Local Abbreviation QSP := (@YF7h.QSP imgk ly idx).
Local Abbreviation QS_not_WIN1R := (ARg (AR3 (@YF7h.QS_not_WIN1R _))).
Local Abbreviation QSP_rstable := (ARg (AR3 (@YF7h.QSP_rstable _))).
Local Abbreviation at_S_memsetSR := ((AR8 ((AR0 ((AR5 (@YF7h.at_S_memsetSR _ _)) md0)) LY Hsp)) Hmap_apart mat0 DPOST S).
Local Abbreviation chunk_eqb := (@YF7h.chunk_eqb imgk).
Local Abbreviation chunk_eqb_eq := ((ARe (@YF7h.chunk_eqb_eq imgk)) Hres S Hidx_def Hres_def).
Local Abbreviation subregionb := (@YF7h.subregionb imgk).
Local Abbreviation subregionb_sound := (AR9 ((ARe (AR6 (@YF7h.subregionb_sound))) Hres)).
Local Abbreviation submemb := (@YF7h.submemb imgk).
Local Abbreviation submemb_sound := (AR9 ((ARe (AR6 (@YF7h.submemb_sound))) Hres)).
Local Abbreviation at_S_submem := (AR9 ((AR0 (AR6 (@YF7h.at_S_submem _))) Hidx Hres)).
Local Abbreviation at_S_addreg := (AR0 (AR6 (@YF7h.at_S_addreg _))).
Local Abbreviation PSR_runs := (AR0 (AR6 (@YF7d.PSR_runs _))).
Local Abbreviation place_WIN := (ARc (@YF7d.place_WIN)).
Local Abbreviation SH0 := (@YF7d.SH0 n mb).
Local Abbreviation SH1 := (@YF7d.SH1 n mb).
Local Abbreviation SH2 := (@YF7d.SH2 n mb).
Local Abbreviation SH_ok := (AR8 (AR3 (@YF7d.SH_ok _))).
Local Abbreviation segG1 := (AR9 ((ARg (AR0 ((AR5 (@YF7d.segG1 _ _)) md0))) mat0)).
Local Abbreviation RX_stableS := (ARc (@YF7e.RX_stableS)).
Local Abbreviation rstable_and := ((AR1 (@YF7e.rstable_and)) n mb).
Local Abbreviation pstable_and := (@YF7e.pstable_and).
Local Abbreviation PSR_stableS' := (ARg (ARb ((AR1 (@YF7e.PSR_stableS' _)) n ch))).
Local Abbreviation pairwise_disjoint_map := (@YF7e.pairwise_disjoint_map).
Local Abbreviation at_S_setchunks := (AR0 (AR6 (@YF7e.at_S_setchunks _))).
Local Abbreviation chunk_ok_CVal_eqv := (@YF7e.chunk_ok_CVal_eqv imgk).
Local Abbreviation RES2T_ne := ((AR0 (AR1 (@YF7e.RES2T_ne))) Hidx Hres).
Local Abbreviation RES2T_eq := ((AR0 (AR1 (@YF7e.RES2T_eq))) Hidx Hres).
Local Abbreviation sv_denot_eq_of_U := (AR0 (AR1 (@YF7e.sv_denot_eq_of_U))).
Local Abbreviation skel_apart_QS := (AR9 (ARg (AR0 (AR6 (@YF7e.skel_apart_QS _))))).
Local Abbreviation QSPX := (@YF7e.QSPX imgk ly idx).
Local Abbreviation segNE := (AR9 (ARg (AR0 (AR6 (@YF7e.segNE _ _))))).
Local Abbreviation segEQa := (ARg (AR0 (AR6 (@YF7e.segEQa _ _)))).
Local Abbreviation zev_SAlu := (@YF7e.zev_SAlu).
Local Abbreviation zev_SLit := (@YF7e.zev_SLit).
Local Abbreviation zev_SOff := (@YF7e.zev_SOff).
Local Abbreviation segJ2 := (AR9 (ARg (AR0 (AR6 (@YF7e.segJ2 _ _))))).
Local Abbreviation segJ := (AR9 (ARg (AR0 (AR6 (@YF7e.segJ _ _))))).
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
Definition QR (a : Z) : Prop := Qb + 8 * res <= a < Qb + 8 * res + 8 * kPtrArrayEntriesPerCommit /\ a < Qb + kPtrArrayResv.
Hypothesis D1w : forall (X : Z -> Prop) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model),
(forall a, X a -> WIN a \/ QR a) ->
getr regs 10 = Z_to_bv 64 (sp0 - IFRAME + 16) -> getr regs 11 = Z_to_bv 64 (Z.of_nat (length tr)) ->
getr regs 3 = getr regs0 3 -> getr regs 4 = Z_to_bv 64 TFX_TP -> getr regs 1 = Z_to_bv 64 (0x31cc8 + D_150) ->
bv_unsigned (getr regs 2) = sp0 - 2336 ->
PBUFW Wy mem -> (forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H Wy) mem a) ->
(forall x : word, ~ X (bv_unsigned x) -> mem x = mem0 x) ->
(forall k, 1 <= k < 4 -> aview tfxsegs (w_H Wy) mem (TFX_INST + o_sec_mutex + k) = Some 0) ->
SRr tfxsegs Wy (mkCfg (mkst regs (Z_to_bv 64 A_StackDepotPut) mem (seg_rom tfxsegs)) md)
(fun W' c' => W' = Wy /\ exists z regs' mem' mat,
c' = mkCfg (mkst regs' (Z_to_bv 64 (0x31cc8 + D_150)) mem' (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md) mat md) /\
regs_preserved regs regs' /\
(forall x : word, ~ (sp0 - 2336 - DEP_STK <= bv_unsigned x < sp0 - 2336) -> ~ DZONE (bv_unsigned x) -> mem' x = mem x) /\
(forall a, apresent (w_H Wy) mem a -> apresent (w_H Wy) mem' a) /\
DPOST z mem').
Local Ltac s_runS HR tbl tblok stop ss' HX HP :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let st := img_ev (snd (sym_run_toN_sh tfxsegs tbl FUEL stop ss)) in
eapply SRr_bind;
[ img_try (eapply (at_S_runS Wx tbl tblok stop md X P ss ss' st W' c' HR);
[ (img_case; vm_compute); img_refl | img_exact I | img_exact HX | (img_case; vm_compute); img_refl | img_exact HP | (img_case; vm_compute); img_refl ])
| img_try (clear HR; let W2 := fresh "W" in let c2 := fresh "c" in intros W2 c2 _ HR) ] end.
Lemma segT1 : forall (X : Z -> Prop), (forall a, WIN a -> X a) ->
forall c, at_S Wy md1 X (PSR Wy SH2 RX) S_TJ0 Wy c -> SRr tfxsegs Wy c (at_S Wy md1 X (PSR Wy SH2 RX) T_PD).
Proof.
intros X HXW c HR. pose proof SH_ok as (OK0 & OK1 & OK2). pose proof (PSR_stableS' Wy SH2 RX OK2 (RX_stableS RX RXt)) as HP2.
assert (HX : forall a, WIN1S a -> X a) by (img_try (intros a Ha; apply HXW, WIN1S_WIN, Ha)).
pose proof size_facts as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & _). pose proof Nrange as NR. pose proof map_facts as (M1 & M2 & _). pose proof map_zoneN as MZ.
unfold MALLOC_MAX in Z1, Z8, NR. ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in M1, M2.
s_arm HR BC_LTU false (SAlu ALU_ADD (SOff aMAP 4096) (SOff aND 0)) (SAlu ALU_ADD (SOff 10 6144) (SOff aMAP 0)).
{ clear - Z1 Z3 Z7 Z8 NR M1 M2 Hn MZ. arm_zevS. rewrite EaMAP, EaND, E10, Hn. unfold w64. rewrite !unsigned_lit_small by zlia. zcanon_simp.
img_apply Z.ltb_ge. zlia. }
s_station HR T_J.
s_runS HR tfxtbl_rr tfxtbl_rr_ok (0x31c08 + D_150) (runto (0x31c08 + D_150) T_J) HX HP2.
s_arm HR BC_NE false (SAlu ALU_SRL (SOff 10 0) (SLit 48)) (SLit 0).
{ clear - NR Hn MZ. arm_zevS. rewrite E10, Hn. unfold w64. rewrite !unsigned_lit_small by zlia. zcanon_simp. land_lits.
rewrite Z.shiftr_div_pow2 by zlia. rewrite Z.add_0_r, (Z.div_small n (2 ^ 48)) by zlia. img_refl. }
s_station HR T_K.
s_runS HR tfxtbl_rr tfxtbl_rr_ok (0x72fcc + D_2c4) T_PD HX HP2.
img_apply SRr_ret. img_exact HR.
Qed.
Definition DX (a : Z) : Prop := (sp0 - 2336 - DEP_STK <= a < sp0 - 2336) \/ DZONE a.
Hypothesis RXd : pstable DX RX.
Definition PD (z : Z) (m : word -> option byte) : Prop :=
exists memD, DPOST z memD /\ (forall a, DZONE a -> apresent (w_H Wy) mem0 a -> apresent (w_H Wy) memD a) /\
(forall x : word, DZONE (bv_unsigned x) -> m x = memD x).
Lemma PD_rstable : forall z, rstable (PD z).
Proof.
intros z. split.
- intros m m' FR (memD & D1' & D2 & D3). exists memD. split; [img_try (img_exact D1')|]. split; [img_try (img_exact D2)|]. intros x Hx. rewrite FR; [img_try (img_exact (D3 x Hx))|].
intros Hw. img_exact (proj1 (DZONE_disj _ Hx) (WIN1R_WIN _ Hw)).
- intros m m' d len Hplace FR (memD & D1' & D2 & D3). exists memD. split; [img_try (img_exact D1')|]. split; [img_try (img_exact D2)|]. intros x Hx. rewrite FR; [img_try (img_exact (D3 x Hx))|].
intros Hin. img_exact (proj1 (DZONE_disj _ Hx) (place_WIN d len _ Hplace Hin)).
Qed.
Lemma PD_stableT : forall z, pstable WIN1T (PD z).
Proof.
intros z m m' FR (memD & D1' & D2 & D3). exists memD. split; [img_try (img_exact D1')|]. split; [img_try (img_exact D2)|]. intros x Hx. rewrite FR; [img_try (img_exact (D3 x Hx))|].
intros Hw. img_exact (proj1 (DZONE_disj _ Hx) (WIN1T_WIN _ Hw)).
Qed.
Lemma PSR_stableS : forall sh R, Forall run_ok sh -> pstable WIN1S R -> pstable WIN1S (PSR Wy sh R).
Proof. intros sh R OK RS m m' FR [HP HQ]. split; [img_try (img_exact (PS_stable Wy sh OK m m' FR HP)) | img_try (img_exact (RS m m' FR HQ))]. Qed.
Lemma PD_stableS : forall z, pstable WIN1S (PD z).
Proof. intros z m m' FR. img_apply (PD_stableT z m m'). intros x Hx. img_apply FR. intros Hw. img_exact (Hx (WIN1S_WIN1T _ Hw)). Qed.
Definition PDX (z : Z) (m : word -> option byte) : Prop := PD z m /\ RX m.
Lemma PDX_rstable : forall z, rstable (PDX z).
Proof. intros z. img_exact (rstable_and _ _ (PD_rstable z) RXs). Qed.
Lemma PDX_stableT : forall z, pstable WIN1T (PDX z).
Proof. intros z. img_exact (pstable_and _ _ _ (PD_stableT z) RXt). Qed.
Lemma PDX_stableS : forall z, pstable WIN1S (PDX z).
Proof. intros z. img_exact (pstable_and _ _ _ (PD_stableS z) (RX_stableS RX RXt)). Qed.
Definition dx_okb {imgk : img} (s : option nat * Z * Z * Z * Z) : bool :=
match s with (b, lo, hi, _, _) =>
match b with
| Some 2%nat => (- 2336 <=? lo) && (hi <=? 0)
| None => (0 <=? lo) && (hi <=? (0x5ff000 + D_1000)) && ((hi <=? (0x17c088 + D_10c0)) || ((0x5cc810 + D_10c0) <=? lo))
| _ => skel_okb false s
end
end.
Lemma skel_apart_DX : forall (E' : env) r, env_agree sHAV E0 E' -> dx_okb (skel r) = true ->
(forall a, base_val E' (YQ0b.r_base r) + YQ0b.r_lo r <= a < base_val E' (YQ0b.r_base r) + YQ0b.r_hi r -> ~ DX a /\ 0 <= a < 2 ^ 64).
Proof.
intros E' r HE Hs a Ha.
assert (SK : skel_okb false (skel r) = true).
{ destruct r as [[k|] lo hi wlo whi cs]; unfold skel, dx_okb in Hs |- *; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi] in *;
[| img_try (apply andb_prop in Hs as [Hs _]; img_exact Hs)].
destruct k as [|[|[|k]]]; try img_exact Hs. unfold skel_okb. apply andb_prop in Hs as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
rewrite (proj2 (Z.leb_le (- ASTACK) lo)) by (img_try (unfold ASTACK; zlia)). rewrite (proj2 (Z.leb_le hi 0) H2). img_refl. }
split; [| img_try (img_exact (skel_u64 E' false r a HE SK Ha))].
destruct HE as [HEn _]. pose proof high_facts as (F1 & F2 & _ & _ & _ & _ & F7 & F8 & F9 & F10 & _).
pose proof map_facts as (M1 & M2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _ & PB & _). pose proof map_zoneN as MZ. pose proof size_facts as (_ & _ & Z3 & Z4 & _ & _ & Z7 & Z8 & _ & Z10 & _).
pose proof Hidx as HI. pose proof Nrange as NR. pose proof BSLv_range as HB. pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7). destruct Hsp as (S1 & _ & S3 & _).
pose proof blocks_facts as (NBhi & SBhi & TNB & TSB & QNB & QSB & NBS & SBS & CNB & CSB).
unfold zdisjoint in TNB, TSB, QNB, QSB, NBS, SBS, CNB, CSB. cbn [fst snd] in TNB, TSB, QNB, QSB, NBS, SBS, CNB, CSB.
destruct Hmap_apart as (_ & _ & _ & _ & MNB & MSB & _). unfold zdisjoint in MNB, MSB. cbn [fst snd] in MNB, MSB.
pose proof (u64_range (getr regs0 2)) as U2.
destruct r as [b lo hi wlo whi cs]. unfold skel in Hs, SK. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi] in *.
unfold zone3, TFX_IMG_LO, kLowShadowBeg, DX, DZONE, DEP_STK, kNodesBlockSize, kStoreBlockSize, kHighMemBeg in *.
destruct (skel_cases false b lo hi wlo whi SK) as [(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|(Epb & -> & A1 & A2)]]]]]]]; cbn [base_val] in Ha.
- unfold dx_okb in Hs. apply andb_prop in Hs as [_ H3]. apply Bool.orb_prop in H3 as [H3|H3]; apply Z.leb_le in H3;
clear - Ha A1 A2 H3 NBhi SBhi S1 T7 MZ; unfold ASTACK in *; try unfold sp0 in *; zlia.
- rewrite (HEn 2%nat ltac:(img_try (unfold sHAV; zlia))), E2 in Ha. unfold dx_okb in Hs. apply andb_prop in Hs as [H1 H2]. apply Z.leb_le in H1.
clear - Ha A1 A2 H1 NBS SBS S1 S3 T7 U2 MZ. unfold ASTACK in *. try unfold sp0 in *. zlia.
- rewrite (HEn 32%nat ltac:(img_try (unfold sHAV; zlia))), EaT in Ha. unfold w64 in Ha. rewrite unsigned_lit_small in Ha by (img_try (clear - F1 F2 MZ; numconst; try unfold T in *; zlia)).
pose proof stack_ivs as (DT & _). clear - Ha A1 A2 TNB TSB F1 F2 S1 S3 T7 U2 DT MZ. ceil; unfold kThreadObjSize, ASTACK, ASAN_CEIL in *. try unfold T in *. try unfold sp0 in *. zlia.
- rewrite (HEn 33%nat ltac:(img_try (unfold sHAV; zlia))), EaC in Ha. unfold w64 in Ha. rewrite unsigned_lit_small in Ha by (img_try (clear - F7 F8 MZ; ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; zlia)).
pose proof stack_ivs as (_ & _ & DC & _). clear - Ha A1 A2 CNB CSB F7 F8 S1 S3 T7 U2 DC MZ. ceil; unfold ASTACK, ASAN_CEIL in *. try unfold sp0 in *. zlia.
- unfold aMAP in Ha. rewrite (HEn 45%nat ltac:(img_try (unfold sHAV; zlia))), EaMAP in Ha. unfold w64 in Ha. rewrite unsigned_lit_small in Ha by (img_try (clear - M1 M2 Z8 MZ; ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; zlia)).
destruct Hmap_apart as (_ & _ & _ & _ & _ & _ & MS). unfold zdisjoint in MS. cbn [fst snd] in MS. clear - Ha A1 A2 MNB MSB M1 M2 Z8 S1 S3 T7 U2 MS MZ.
ceil; unfold ASTACK, ASAN_CEIL in *. try unfold sp0 in *. zlia.
- unfold aQS in Ha. rewrite (HEn 52%nat ltac:(img_try (unfold sHAV; zlia))), EaQS in Ha. unfold w64 in Ha. unfold QSv in *. rewrite unsigned_lit_small in Ha by (img_try (clear - F9 F10 HI MZ; ceil; unfold ASAN_CEIL, kPtrArrayResv, kMaxNumChunks in *; try unfold Qb in *; zlia)).
pose proof stack_ivs as (_ & _ & _ & SQ). clear - Ha A1 A2 QNB QSB F9 F10 HI S1 S3 T7 U2 SQ MZ. ceil; unfold ASTACK, ASAN_CEIL, kPtrArrayResv, kMaxNumChunks in *. try unfold Qb in *. try unfold sp0 in *. zlia.
- unfold aBSL in Ha. rewrite (HEn 55%nat ltac:(img_try (unfold sHAV; zlia))), EaBSL in Ha. unfold w64 in Ha. rewrite unsigned_lit_small in Ha by (img_try (clear - HB MZ; unfold TFX_INST in *; zlia)).
clear - Ha A1 A2 HB NBhi SBhi S1 T7 MZ. unfold TFX_INST, ASTACK in *. try unfold sp0 in *. zlia.
- discriminate Epb.
Qed.
Lemma skel_apart_stk : forall (E' : env) r, env_agree sHAV E0 E' -> dx_okb (skel r) = true -> YQ0b.r_lo r < YQ0b.r_hi r ->
base_val E' (YQ0b.r_base r) + YQ0b.r_hi r <= sp0 - ASTACK \/ sp0 - 2336 <= base_val E' (YQ0b.r_base r) + YQ0b.r_lo r.
Proof.
intros E' r HE Hs Hne.
assert (SK : skel_okb false (skel r) = true).
{ destruct r as [[k|] lo hi wlo whi cs]; unfold skel, dx_okb in Hs |- *; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi] in *;
[| img_try (apply andb_prop in Hs as [Hs _]; img_exact Hs)].
destruct k as [|[|[|k]]]; try img_exact Hs. unfold skel_okb. apply andb_prop in Hs as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
rewrite (proj2 (Z.leb_le (- ASTACK) lo)) by (img_try (unfold ASTACK; zlia)). rewrite (proj2 (Z.leb_le hi 0) H2). img_refl. }
destruct HE as [HEn _]. pose proof high_facts as (F1 & F2 & _ & _ & _ & _ & F7 & F8 & F9 & F10 & _).
pose proof map_facts as (M1 & M2 & _). pose proof map_zoneN as MZ. pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & _).
pose proof Hidx as HI. pose proof BSLv_range as HB. pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7). destruct Hsp as (S1 & _ & S3 & _).
pose proof stack_ivs as (DT & _ & DC & SQ). destruct Hmap_apart as (_ & _ & _ & _ & _ & _ & MS). unfold zdisjoint in MS. cbn [fst snd] in MS.
pose proof (u64_range (getr regs0 2)) as U2.
destruct r as [b lo hi wlo whi cs]. unfold skel in Hs, SK. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi] in *.
ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kPtrArrayResv, kMaxNumChunks in *.
destruct (skel_cases false b lo hi wlo whi SK) as [(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|(Epb & -> & A1 & A2)]]]]]]]; cbn [base_val].
- left. clear - A1 A2 S1 T7 MZ. unfold ASTACK in *. try unfold sp0 in *. zlia.
- right. rewrite (HEn 2%nat ltac:(img_try (unfold sHAV; zlia))), E2. unfold dx_okb in Hs. apply andb_prop in Hs as [H1 H2]. apply Z.leb_le in H1. clear - H1 MZ. try unfold sp0 in *. zlia.
- rewrite (HEn 32%nat ltac:(img_try (unfold sHAV; zlia))), EaT. unfold w64. rewrite unsigned_lit_small by (img_try (clear - F1 F2 MZ; numconst; try unfold T in *; zlia)).
clear - A1 A2 DT Hne MZ. unfold ASTACK, kThreadObjSize in *. try unfold T in *. try unfold sp0 in *. zlia.
- rewrite (HEn 33%nat ltac:(img_try (unfold sHAV; zlia))), EaC. unfold w64. rewrite unsigned_lit_small by (img_try (clear - F7 F8 MZ; zlia)).
clear - A1 A2 DC Hne MZ. unfold ASTACK in *. try unfold sp0 in *. zlia.
- unfold aMAP. rewrite (HEn 45%nat ltac:(img_try (unfold sHAV; zlia))), EaMAP. unfold w64. rewrite unsigned_lit_small by (img_try (clear - M1 M2 Z8 MZ; zlia)).
clear - A1 A2 MS M1 M2 Z8 S1 S3 Hne MZ. unfold ASTACK in *. try unfold sp0 in *. zlia.
- unfold aQS. rewrite (HEn 52%nat ltac:(img_try (unfold sHAV; zlia))), EaQS. unfold w64. unfold QSv in *. rewrite unsigned_lit_small by (img_try (clear - F9 F10 HI MZ; try unfold Qb in *; zlia)).
clear - A1 A2 SQ HI Hne MZ. unfold ASTACK, kPtrArrayResv, kMaxNumChunks in *. try unfold Qb in *. try unfold sp0 in *. zlia.
- unfold aBSL. rewrite (HEn 55%nat ltac:(img_try (unfold sHAV; zlia))), EaBSL. unfold w64. rewrite unsigned_lit_small by (img_try (clear - HB MZ; unfold TFX_INST in *; zlia)).
left. clear - A1 A2 HB S1 T7 MZ. unfold TFX_INST, ASTACK in *. try unfold sp0 in *. zlia.
- discriminate Epb.
Qed.
Lemma at_S_depot : forall (X : Z -> Prop), (forall a, X a -> WIN a \/ QR a) -> (forall a, WIN a -> X a) ->
forall c, at_S Wy md1 X (PSR Wy SH2 RX) T_PD Wy c ->
SRr tfxsegs Wy c (fun W2 c2 => exists z, at_S Wy md1 (fun a => X a \/ DX a) (PSR Wy SH2 (PDX z)) T_2 W2 c2).
Proof.
intros X HXQ HXW c HR. destruct HR as (EW & ms & mat & E' & -> & HE & HS & MEQ & PRS & HPm). clear EW. pose proof (proj1 HE) as HEn.
pose proof Hwx_tfa as Hwx. pose proof Hsp as (Hlo & Hbot & Hhi & Hal). pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
pose proof (u64_range (getr regs0 2)) as Usp.
pose proof (st_ok_restrict_mkst tfxsegs (w_H Wy) E' _ _ HS eq_refl) as Hshape. cbn [ss_pc] in Hshape.
lazymatch type of Hshape with _ = mkst _ (Z_to_bv 64 (ss_pc ?s)) _ _ => let p := img_ev (ss_pc s) in img_change (ss_pc s) with p in Hshape end. rewrite Hshape.
rreg HS (2%bv : bv 5) R2. rewrite (HEn 2%nat ltac:(img_try (unfold sHAV; zlia))), E2 in R2.
eapply SRr_mono.
{ img_apply (D1w X (ms_regs ms) (ms_mem ms) _ HXQ).
- rreg HS (10%bv : bv 5) R; rewrite R, (HEn 2%nat ltac:(img_try (unfold sHAV; zlia))), E2. unfold IFRAME, sp0. f_equal; zlia.
- rreg HS (11%bv : bv 5) R; rewrite R, (HEn 36%nat ltac:(img_try (unfold sHAV; zlia))). img_refl.
- rreg HS (3%bv : bv 5) R; rewrite R, (HEn 3%nat ltac:(img_try (unfold sHAV; zlia))). img_exact (Er 3 3%bv eq_refl).
- rreg HS (4%bv : bv 5) R; rewrite R. img_refl.
- rreg HS (1%bv : bv 5) R; rewrite R. img_refl.
- rewrite R2. clear - Hlo Hhi T4 T7 Usp. rewrite unsigned_lit_small by (img_try (unfold zone3, TFX_IMG_LO, kLowShadowBeg, ASTACK, kHighMemEnd, kHighMemBeg in *; unfold sp0 in *; zlia)). unfold sp0; zlia.
- img_exact (proj1 (proj1 HPm)).
- img_exact PRS.
- img_exact MEQ.
-
destruct (st_ok_mem_ok tfxsegs E' _ _ HS) as (_ & ROK & _).
set (RMUT := YQ0b.mkRegion None (TFX_INST + o_sec_mutex) (TFX_INST + o_sec_mutex + 4) (TFX_INST + o_sec_mutex) (TFX_INST + o_sec_mutex + 4)
[YQ0b.mkChunk (TFX_INST + o_sec_mutex) (CVal 1 (SLit 0)); YQ0b.mkChunk (TFX_INST + o_sec_mutex + 1) (CVal 1 (SLit 0));
YQ0b.mkChunk (TFX_INST + o_sec_mutex + 2) (CVal 2 (SLit 0))]).
assert (HIN : In RMUT (ss_mem T_PD)) by (img_try ((subst RMUT; cbv beta); (img_case; vm_compute); repeat (first [left; img_refl | right]))).
pose proof (proj1 (Forall_forall _ _) ROK RMUT HIN) as (_ & _ & _ & RC). (subst RMUT; cbv beta). cbn [YQ0b.r_chunks YQ0b.r_base base_val] in RC.
apply Forall_cons_iff in RC as [_ RC]. apply Forall_cons_iff in RC as [C1 RC]. apply Forall_cons_iff in RC as [C2 _].
intros k Hk. unfold aview. cbn [restrict ms_mem].
assert (Hcase : k = 1 \/ k = 2 \/ k = 3) by zlia. destruct Hcase as [-> | [-> | ->]].
+ destruct (C1 0 ltac:(img_try (cbn; zlia))) as (b & Hb & Hm). cbn [YQ0b.c_off YQ0b.c_val cbyte restrict ms_mem] in Hb, Hm.
replace (TFX_INST + o_sec_mutex + 1) with (0 + (TFX_INST + o_sec_mutex + 1) + 0) by zlia. rewrite Hm. rewrite <- Hb. img_case; vm_compute. all: img_refl.
+ destruct (C2 0 ltac:(img_try (cbn; zlia))) as (b & Hb & Hm). cbn [YQ0b.c_off YQ0b.c_val cbyte restrict ms_mem] in Hb, Hm.
replace (TFX_INST + o_sec_mutex + 2) with (0 + (TFX_INST + o_sec_mutex + 2) + 0) by zlia. rewrite Hm. rewrite <- Hb. img_case; vm_compute. all: img_refl.
+ destruct (C2 1 ltac:(img_try (cbn; zlia))) as (b & Hb & Hm). cbn [YQ0b.c_off YQ0b.c_val cbyte restrict ms_mem] in Hb, Hm.
replace (TFX_INST + o_sec_mutex + 3) with (0 + (TFX_INST + o_sec_mutex + 2) + 1) by zlia. rewrite Hm. rewrite <- Hb. img_case; vm_compute. all: img_refl. }
intros W' c' Hle (-> & z & regs2 & mem2 & mat2 & -> & HP & Hfr & Hpr & HDP). exists z.
set (mem := ms_mem ms) in *.
assert (Hfr' : forall x : word, ~ DX (bv_unsigned x) -> mem2 x = mem x) by (img_try (intros x Hx; img_apply Hfr; unfold DX in Hx; tauto)).
lazymatch type of HS with st_ok _ _ ?ss ?ms0 =>
let m := img_ev (ss_mem ss) in
lazymatch m with ?rq :: ?rm :: ?rb :: ?r1 :: ?rest =>
pose proof (st_ok_after_call tfxsegs sD1 E' ss ms0 regs2 (mrestrict (w_H Wy) mem2) (rq :: rm :: rb :: trim_lo r1 (-2336) :: rest) (0x31cc8 + D_150) HS eq_refl
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_try (img_apply submem_keep; [img_try (img_apply subregion_refl)|]; img_apply submem_keep; [img_try (img_apply subregion_refl)|]; img_apply submem_keep; [img_try (img_apply subregion_refl)|];
img_apply submem_keep; [img_try (img_apply subregion_trim_lo) | img_try (img_apply submem_refl)]))
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) HP) as HS1;
let rsv := img_ev (rq :: rm :: rb :: trim_lo r1 (-2336) :: rest) in
img_change (rq :: rm :: rb :: trim_lo r1 (-2336) :: rest) with rsv in HS1;
let ss2 := img_ev (ss_after_call ss rsv sD1 (0x31cc8 + D_150)) in
change (ss_after_call ss rsv sD1 (0x31cc8 + D_150)) with ss2 in HS1
end
end.
cbn [ms_mem restrict] in HS1. fold mem in HS1.
lazymatch type of HS1 with Forall _ ?rs -> _ =>
assert (KEPT : Forall (region_kept tfxsegs E' (mrestrict (w_H Wy) mem) (mrestrict (w_H Wy) mem2)) rs);
[ img_try (img_apply Forall_forall; intros r Hr;
pose proof (proj1 (forallb_forall _ _) (ltac:(img_eqrefl) : forallb (fun r => dx_okb (skel r)) rs = true) r Hr) as CK; cbn beta in CK;
img_apply (kept_of_frame2 (w_H Wy) E' mem mem2 DX r Hfr');
[ img_exact (skel_apart_DX E' r HE CK)
| intros a Ha; pose proof (region_wf_facts r (regions_wf_In rs r ltac:((try img_inst; img_case; vm_compute); img_refl) Hr)) as (_ & WW & _); img_apply (skel_apart_DX E' r HE CK); clear - Ha WW; zlia ])
| img_try (specialize (HS1 KEPT); clear KEPT) ]
end.
assert (PRES2 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H Wy) mem2 a) by (img_try (intros a Ha; apply Hpr, PRS, Ha)).
set (En3 := havoc E' sD1 (map (getr regs2) CLOB)) in HS1.
assert (HE3 : env_agree sHAV E0 En3) by (img_try (img_exact (env_agree_havoc_ge sHAV sD1 E0 E' _ ltac:(unfold sHAV, sD1; zlia) HE))).
pose proof (proj1 HE3) as HEn3.
apply (st_ok_add_region _ _ _ R_scr2) in HS1;
[ | img_refl
| unfold YQ0b.region_ok, R_scr2; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem];
rewrite (HEn3 2%nat ltac:(img_try (unfold sHAV; zlia))), E2;
split; [img_try (clear - Hlo T7; unfold zone3, TFX_IMG_LO, kLowShadowBeg, ASTACK, kHighMemBeg in *; unfold sp0 in *; zlia)|]; split; [img_try (clear - Usp; zlia)|]; split;
[ img_try (intros o Ho; img_apply apresent_writable_off; [off_by ltac:(clear - Ho Hlo T7 Usp; unfold zone3, TFX_IMG_LO, kLowShadowBeg, ASTACK, TFX_IMG_END, kHighMemBeg in *; unfold sp0 in *; zlia) | img_apply PRES2; clear - Ho; unfold ASTACK in *; zlia]) | img_try (constructor) ]
| img_apply all_disjoint_of_forall; intros r' Hr';
lazymatch type of Hr' with In _ ?l =>
pose proof (proj1 (forallb_forall _ _) (ltac:(img_eqrefl) : forallb (fun r => dx_okb (skel r) && (YQ0b.r_lo r <? YQ0b.r_hi r)) l = true) r' Hr') as CK; cbn beta in CK end;
apply andb_prop in CK as [CK1 CK2]; apply Z.ltb_lt in CK2;
unfold extent_disjoint, R_scr2; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; rewrite (HEn3 2%nat ltac:(img_try (unfold sHAV; zlia))), E2;
pose proof (skel_apart_stk En3 r' HE3 CK1 CK2) as AP; clear - AP; unfold sp0 in *; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1.
lazymatch type of HS1 with st_ok _ _ ?ss _ => replace ss with T_2 in HS1 by (img_try ((img_case; vm_compute); img_refl)) end.
split; [img_refl|]. exists (mkst regs2 (Z_to_bv 64 (0x31cc8 + D_150)) mem2 (seg_rom tfxsegs)), mat2, En3.
split; [img_try (rewrite wvb_collapse; img_refl)|]. split; [img_try (img_exact HE3)|]. split; [img_try (rewrite restrict_mkst_fx; img_exact HS1)|].
split. { intros x Hx. cbn [ms_mem mkst]. rewrite Hfr' by (img_try (intros Hd; img_apply Hx; right; img_exact Hd)). img_apply MEQ. intros HX'; img_apply Hx; left; img_exact HX'. }
split; [img_try (img_exact PRES2)|].
destruct HPm as [(HB & HM & HSH & HRs) HRX]. cbn [ms_mem mkst].
assert (NDX : forall a, (mb + 6144 <= a < mb + MSv) \/ (SMv <= a < SMv + MSv / 8) -> ~ DX a).
{ intros a Ha [Hs|Hd].
- img_apply (runs_not_stack a Ha). unfold DEP_STK, ASTACK in *. zlia.
- img_apply (proj1 (DZONE_disj a Hd)). img_apply (place_WIN a 1 a); [img_try (clear - Ha; zlia) | img_try (zlia)]. }
pose proof map_facts as (M1 & M2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _). pose proof map_zoneN as MZ.
assert (U64R : forall a, (mb + 6144 <= a < mb + MSv) \/ (SMv <= a < SMv + MSv / 8) -> bv_unsigned (Z_to_bv 64 a) = a).
{ intros a Ha. img_apply unsigned_lit_small. clear - Ha M1 M2 SM1 SM2 MZ. ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighShadowBeg, kHighShadowEnd, ASAN_CEIL in *. zlia. }
split; [img_try (split; [|split; [|split]])|].
- intros i Hi. eapply val_mem_frame; [|img_try (img_exact (HB i Hi))]. intros kk Hkk. img_apply Hfr'. pose proof tr_length as LEN.
rewrite unsigned_lit_small by (img_try (clear - Hi Hkk LEN Hlo Hhi T4 T7 MZ; unfold zone3, TFX_IMG_LO, kLowShadowBeg, IFRAME, ASTACK, kHighMemBeg, kHighMemEnd in *; unfold sp0 in *; zlia)).
intros [Hs|Hd]; [img_try (clear - Hs Hi Hkk LEN MZ; unfold IFRAME, DEP_STK in *; zlia)|].
img_apply (proj2 (DZONE_disj _ Hd)). clear - Hi Hkk LEN MZ. unfold IFRAME, ASTACK in *. zlia.
- intros a Ha. img_apply Hpr. img_exact (HM a Ha).
- intros a Ha. img_apply Hpr. img_exact (HSH a Ha).
- pose proof SH_ok as (_ & _ & OK2). img_apply Forall_forall. intros r Hr a Ha. pose proof (proj1 (Forall_forall _ _) OK2 r Hr) as RO.
assert (PL : (mb + 6144 <= a < mb + MSv) \/ (SMv <= a < SMv + MSv / 8)) by (img_try (unfold run_ok in RO; clear - RO Ha MZ; zlia)).
unfold w64. rewrite Hfr' by (img_try (rewrite (U64R a PL); img_exact (NDX a PL))). img_exact (proj1 (Forall_forall _ _) HRs r Hr a Ha).
- split; [| img_try (img_exact (RXd mem mem2 Hfr' HRX))].
exists mem2. split; [img_try (img_exact HDP)|]. split; [|img_try (intros x _; img_refl)].
intros a Hd Hp0. img_apply Hpr. img_apply (apresent_same (w_H Wy) mem0); [|img_try (img_exact Hp0)]. img_apply MEQ.
pose proof blocks_facts as (NBhi & SBhi & _ & _ & QNB & QSB & _). unfold zdisjoint in QNB, QSB. cbn [fst snd] in QNB, QSB.
pose proof high_facts as (_ & _ & _ & _ & _ & _ & _ & _ & F9 & F10 & _). pose proof Hres as [HRS _].
rewrite unsigned_lit_small by (img_try (clear - Hd NBhi SBhi MZ; unfold DZONE in *; numconst; zlia)).
intros HXa. destruct (HXQ a HXa) as [Hw|Hq]; [img_try (img_exact (proj1 (DZONE_disj a Hd) Hw))|].
unfold QR in Hq. pose proof Hidx as HI9. clear - Hd Hq QNB QSB F9 HRS HI9 MZ. unfold zone3, TFX_IMG_LO, kLowShadowBeg, DZONE, kHighMemBeg, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kMaxNumChunks, kPtrArrayEntriesPerCommit in *. try unfold Qb in *. zlia.
Qed.
Definition SH3 : list (Z * Z * Z) :=
[(SMv + 512, SMv + 768, 250); (SHBv + ENDv / 8, SMv + MSv / 8, 250); (SMv, SMv + 512, 250); (SMv + 768, SHBv + ENDv / 8, 0)].
Definition SH4 : list (Z * Z * Z) :=
[(SHBv + UEv / 8, SMv + MSv / 8, 250); (SMv + 512, SMv + 768, 250); (SMv, SMv + 512, 250); (SMv + 768, SHBv + UEv / 8, 0)].
Lemma shadow_marks :
SHBv + ENDv / 8 = SMv + 512 + NDv / 8 /\ SHBv + UEv / 8 = SMv + 768 + R8v / 8 /\ SMv + MSv / 8 = SHBv + UEv / 8 + RLv / 8 /\
NDv / 8 = R8v / 8 + 512 /\ 8065 <= R8v / 8 <= 2 ^ 25 /\ 256 <= RLv / 8 /\ SMv = SHBv + mb / 8 /\ MSv / 8 = NDv / 8 + 512 + TLv / 8 /\ 0 <= TLv / 8.
Proof.
pose proof map_facts as (M1 & M2 & M3 & K4 & U5 & E6 & UE7 & E8 & UE9 & MT & MU & SM1 & SM2 & SM3 & PB & SMA). pose proof map_zoneN as MZ.
pose proof size_facts as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10 & Z11 & Z12 & Z13 & Z14). unfold MALLOC_MAX in Z1, Z8.
clear - M1 M3 U5 E6 UE7 MT MU Z1 Z2 Z7 Z8 Z9 Z10 Z11 Z13 MZ. unfold YF7f.SMv, YF7f.SHBv.
rewrite E6, UE7 in *. rewrite U5 in *. rewrite Z7 in *.
replace RLv with (MSv - R8v - 6144) in * by zlia. replace TLv with (MSv - R8v - 8192) in * by zlia.
apply Z.mod_divide in M3 as [u Hu]; [|img_try (zlia)]. apply Z.mod_divide in Z2 as [q Hq]; [|img_try (zlia)]. apply Z.mod_divide in Z9 as [w Hw]; [|img_try (zlia)].
rewrite Hu, Hq, Hw in *.
replace (u * 4096 + 6144 + q * 8 + 2048) with ((u * 512 + 1024 + q) * 8) by zlia. replace (u * 4096 + 6144 + q * 8) with ((u * 512 + 768 + q) * 8) by zlia.
replace (w * 4096) with ((w * 512) * 8) by zlia. replace (q * 8 + 4096) with ((q + 512) * 8) by zlia.
replace ((w * 512) * 8 - q * 8 - 6144) with ((w * 512 - q - 768) * 8) by zlia. replace (u * 4096) with ((u * 512) * 8) by zlia.
replace ((w * 512) * 8 - q * 8 - 8192) with ((w * 512 - q - 1024) * 8) by zlia.
rewrite !Z_div_mult by zlia. repeat split; zlia.
Qed.
Lemma SH34_ok : Forall run_ok SH3 /\ Forall run_ok SH4.
Proof.
pose proof shadow_marks as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9). clear - A1 A2 A3 A4 A5 A6 A7 A8 A9.
unfold SH3, SH4, run_ok. repeat split; repeat (img_apply Forall_cons || img_apply Forall_nil); cbn [fst snd]; zlia.
Qed.
Section T2.
Variables (X : Z -> Prop) (z : Z).
Hypothesis HXW : forall a, WIN a -> X a.
Let place_X : forall d len a, ((mb + 6144 <= d /\ d + len <= mb + MSv) \/ (SMv <= d /\ d + len <= SMv + MSv / 8)) -> d <= a < d + len -> X a :=
fun d len a PL Ha => HXW a (place_WIN d len a PL Ha).
Local Ltac s_memsetR HR ss' k d len vb retpc OK RS :=
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
[ (clear; zlia) || zlia | clear; (img_case; cbv); img_refl | clear; zlia | clear; zlia | img_exact PL | img_exact OK | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; img_apply (place_X d len a PL Ha)
| img_exact (memset_ext_of_skel false d len ss ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) PL ltac:(img_try (intros XX; discriminate XX)))
| img_exact (memset_u64_of_skel false ss ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))) ]
| clear HR Ud Ul; let W2 := fresh "W" in let c2 := fresh "c" in intros W2 c2 _ HR;
lazymatch type of HR with at_S _ _ _ _ ?ss2 _ _ => replace ss2 with ss' in HR by (img_try ((img_case; vm_compute); img_refl)) end ] ] ] ] end.
Lemma segT2b : forall W' c, at_S Wy md1 X (PSR Wy SH2 (PDX z)) T_N W' c -> SRr tfxsegs W' c (at_S Wy md1 X (PSR Wy SH4 (PDX z)) T_R).
Proof.
intros W1 c HR. pose proof SH_ok as (_ & _ & OK2). pose proof SH34_ok as [OK3 OK4]. pose proof (PDX_rstable z) as RS.
pose proof (PSR_stableS SH2 (PDX z) OK2 (PDX_stableS z)) as HP2. pose proof (PSR_stableS SH3 (PDX z) OK3 (PDX_stableS z)) as HP3. pose proof (PSR_stableS SH4 (PDX z) OK4 (PDX_stableS z)) as HP4.
assert (HX : forall a, WIN1S a -> X a) by (img_try (intros a Ha; apply HXW, WIN1S_WIN, Ha)).
pose proof map_facts as (M1 & M2 & M3 & K4 & U5 & E6 & UE7 & E8 & UE9 & MT & MU & SM1 & SM2 & SM3 & PB & SMA). pose proof map_zoneN as MZ.
pose proof size_facts as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10 & Z11 & Z12 & Z13 & Z14). pose proof Nrange as NR.
unfold MALLOC_MAX in Z1, Z8, NR. ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kHighShadowBeg, kHighShadowEnd in M1, M2, SM1, SM2.
pose proof shadow_marks as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
s_runS HR tfxtbl_rr tfxtbl_rr_ok (0x54344 + D_2c4) T_L3 HX HP2.
s_ladder s_runS HR tfxtbl_rr tfxtbl_rr_ok (0x9b894 + D_10ec) T_L3l T_L3lo T_L3h T_L3h2 T_L3h3 T_L3hi T_M3 sL3 CLOB_L HX HP2.
s_memsetR HR T_P3 sM3 constr:(SMv + 512) 256 250 (0x31da0 + D_150) OK2 RS.
{ clear - M1 M2 M3 Z8 A7 MZ. U_zevS. rewrite (eq_refl : ew E0 47 = w64 SHBv), EaMAP. unfold w64, YF7f.SHBv in *. rewrite !unsigned_lit_small by zlia.
zcanon_simp. land_lits. rewrite Z.shiftr_div_pow2 by zlia. img_change (2 ^ 3) with 8.
apply Z.mod_divide in M3 as [u Hu]; [|img_try (zlia)]. rewrite Hu in *. replace (u * 4096 + 4096) with ((u * 512 + 512) * 8) by zlia. rewrite Z_div_mult by zlia.
rewrite A7. replace (u * 4096) with ((u * 512) * 8) by zlia. rewrite Z_div_mult by zlia. zcanon_simp. zlia. }
{ clear - M1 M2 M3 Z8 MZ. U_zevS. rewrite EaMAP. unfold w64. rewrite !unsigned_lit_small by zlia.
zcanon_simp. land_lits. rewrite !Z.shiftr_div_pow2 by zlia. img_change (2 ^ 3) with 8.
apply Z.mod_divide in M3 as [u Hu]; [|img_try (zlia)]. rewrite Hu.
replace (u * 4096 + 6136) with ((u * 512 + 767) * 8) by zlia. replace (u * 4096 + 4096) with ((u * 512 + 512) * 8) by zlia. rewrite !Z_div_mult by zlia.
zcanon_simp. zlia. }
{ right. clear - A1 A4 A5 A8 A9 MZ. zlia. }
apply (PSR_runs Wy md1 X _ SH3 (PDX z) T_P3) in HR.
2:{ intros m HF. pose proof (Forall_inv HF) as B1. pose proof (Forall_inv_tail HF) as B2'. clear HF.
unfold cut, SH2 in B2'. cbn [flat_map app] in B2'. unfold cut1 in B2'. cbn [fst snd] in B2'.
assert (G1 : (SHBv + ENDv / 8 <? SMv + 512) = false) by (img_try (clear - A1 A4 A5 MZ; img_apply Z.ltb_ge; zlia)).
assert (G2 : (SMv + 512 + 256 <? SMv + MSv / 8) = true) by (img_try (clear - A4 A5 A8 A9 MZ; img_apply Z.ltb_lt; zlia)).
assert (G3 : (SMv <? SMv + 512) = true) by (img_try (img_apply Z.ltb_lt; zlia)).
assert (G4 : (SMv + 512 + 256 <? SMv + 512) = false) by (img_try (img_apply Z.ltb_ge; zlia)).
assert (G5 : (SMv + 512 <? SMv + 512) = false) by (img_try (img_apply Z.ltb_irrefl)).
assert (G6 : (SMv + 512 + 256 <? SHBv + ENDv / 8) = true) by (img_try (clear - A1 A4 A5 MZ; img_apply Z.ltb_lt; zlia)).
rewrite G1, G2, G3, G4, G5, G6 in B2'. cbn [app] in B2'.
pose proof (Forall_inv B2') as C1. pose proof (Forall_inv (Forall_inv_tail B2')) as C2. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail B2'))) as C3. clear B2'.
rewrite Z.max_l in C1 by (img_try (clear - A1 A4 A5 MZ; zlia)). rewrite Z.min_l in C2 by zlia. rewrite Z.max_r in C3 by zlia.
replace (SMv + 512 + 256) with (SMv + 768) in B1 by zlia.
unfold SH3. img_apply Forall_cons; [img_try (img_exact B1)|]. img_apply Forall_cons; [img_try (img_exact C1)|]. img_apply Forall_cons; [img_try (img_exact C2)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
intros a Ha. img_apply C3. cbn [fst snd] in *. zlia. }
s_pin HR (22%bv : bv 5) (SOff aUE 0).
{ clear - M1 M2 M3 Z8 Z1 Z2 Z3 NR UE7 U5 Hn MZ. pin_zevS. rewrite EaUE, EaMAP, E10, Hn. unfold w64. rewrite !unsigned_lit_small by zlia. zcanon_simp.
img_change (zcanon (-8)) with (2 ^ 64 - 8). rewrite land_m8_64 by zlia. rewrite UE7, U5.
pose proof (Z.div_mod (n + 7) 8 ltac:(img_try (zlia))) as D8. pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(img_try (zlia))) as B8. unfold R8v in *.
apply Z.mod_divide in M3 as [u Hu]; [|img_try (zlia)].
replace ((n + 6151 + (mb + 0)) mod 8) with ((n + 7) mod 8); [img_try (zcanon_simp; zlia)|].
rewrite Hu. replace (n + 6151 + (u * 4096 + 0)) with ((n + 7) + (768 + u * 512) * 8) by zlia. rewrite Z_mod_plus_full. img_refl. }
s_pin HR (8%bv : bv 5) (SOff aMS (-4096)).
{ clear - Z1 Z7 Z8 Z9 Z10 MZ. pin_zevS. rewrite EaMS, EaND. unfold w64. rewrite !unsigned_lit_small by zlia. zcanon_simp.
img_change 18446744073709547520 with (2 ^ 64 - 2 ^ 12). rewrite land_neg_pow2_u64 by zlia. img_change (2 ^ 12) with 4096.
pose proof (Z.div_mod (NDv + 4095) 4096 ltac:(img_try (zlia))) as DM. pose proof (Z.mod_pos_bound (NDv + 4095) 4096 ltac:(img_try (zlia))) as MB.
unfold YF7f.MSv in *. zcanon_simp. zlia. }
s_station HR T_P4.
s_runS HR tfxtbl_rr tfxtbl_rr_ok (0x31db0 + D_150) (runto (0x31db0 + D_150) T_P4) HX HP3.
s_pin HR (11%bv : bv 5) (SOff aRL 0).
{ clear - M1 M2 Z8 Z1 Z13 MU UE7 U5 MZ. pin_zevS. rewrite EaRL, EaMS, EaMAP, EaUE. unfold w64. rewrite !unsigned_lit_small by zlia.
rewrite (zcanon_id (RLv + 0)), (zcanon_id (MSv + 0)), (zcanon_id (mb + 0)), (zcanon_id (UEv + 0)), (zcanon_id (MSv + 0 + (mb + 0))) by (img_try (unfold M64; zlia)).
unfold zcanon, M64. rewrite Zmult_mod_idemp_r. rewrite Zplus_mod_idemp_r.
replace (MSv + 0 + (mb + 0) + (UEv + 0) * 18446744073709551615) with ((RLv + 0) + UEv * 2 ^ 64) by zlia. rewrite Z_mod_plus_full. symmetry. img_apply Z.mod_small. zlia. }
s_station HR T_P5.
s_runS HR tfxtbl_rr tfxtbl_rr_ok (0x54344 + D_2c4) T_L4 HX HP3.
s_ladder s_runS HR tfxtbl_rr tfxtbl_rr_ok (0x9b894 + D_10ec) T_L4l T_L4lo T_L4h T_L4h2 T_L4h3 T_L4hi T_M4 sL4 CLOB_L HX HP3.
s_memsetR HR T_P6 sM4 constr:(SHBv + UEv / 8) constr:(RLv / 8) 250 (0x31db4 + D_150) OK3 RS.
{ clear - M1 M2 Z8 Z1 UE7 U5 A2 A7 A5 SM1 MZ. U_zevS. rewrite (eq_refl : ew E0 47 = w64 SHBv), EaUE. unfold w64, YF7f.SHBv in *. rewrite !unsigned_lit_small by zlia.
zcanon_simp. land_lits. rewrite Z.shiftr_div_pow2 by zlia. img_change (2 ^ 3) with 8.
pose proof (Z.div_pos UEv 8 ltac:(img_try (zlia)) ltac:(img_try (zlia))). pose proof (Z.div_lt_upper_bound UEv 8 (2 ^ 61) ltac:(img_try (zlia)) ltac:(img_try (zlia))). zcanon_simp. zlia. }
{ clear - M1 M2 Z8 Z1 Z13 Z14 UE7 UE9 U5 A2 A3 A5 A6 A7 MZ. U_zevS. rewrite EaUE, EaRL. unfold w64. rewrite !unsigned_lit_small by zlia.
zcanon_simp. land_lits. rewrite !Z.shiftr_div_pow2 by zlia. img_change (2 ^ 3) with 8.
apply Z.mod_divide in UE9 as [q Hq]; [|img_try (zlia)]. apply Z.mod_divide in Z14 as [t Ht]; [|img_try (zlia)]. rewrite Hq, Ht in *.
replace (q * 8 + -8 + (t * 8 + 0)) with ((q + t - 1) * 8) by zlia. replace (q * 8 + 0) with (q * 8) by zlia. rewrite !Z_div_mult in * by zlia.
zcanon_simp. zlia. }
{ right. clear - A2 A3 A5 A6 A4 A8 A9 MZ. zlia. }
apply (PSR_runs Wy md1 X _ SH4 (PDX z) T_P6) in HR.
2:{ intros m HF. pose proof (Forall_inv HF) as B1. pose proof (Forall_inv_tail HF) as B2'. clear HF.
unfold cut, SH3 in B2'. cbn [flat_map app] in B2'. unfold cut1 in B2'. cbn [fst snd] in B2'.
assert (G1 : (SMv + 512 <? SHBv + UEv / 8) = true) by (img_try (clear - A2 A5 MZ; img_apply Z.ltb_lt; zlia)).
assert (G2 : (SHBv + UEv / 8 + RLv / 8 <? SMv + 768) = false) by (img_try (clear - A2 A5 A6 MZ; img_apply Z.ltb_ge; zlia)).
assert (G3 : (SHBv + ENDv / 8 <? SHBv + UEv / 8) = false) by (img_try (clear - A1 A2 A4 MZ; img_apply Z.ltb_ge; zlia)).
assert (G4 : (SHBv + UEv / 8 + RLv / 8 <? SMv + MSv / 8) = false) by (img_try (clear - A3 MZ; img_apply Z.ltb_ge; zlia)).
assert (G5 : (SMv <? SHBv + UEv / 8) = true) by (img_try (clear - A2 A5 MZ; img_apply Z.ltb_lt; zlia)).
assert (G6 : (SHBv + UEv / 8 + RLv / 8 <? SMv + 512) = false) by (img_try (clear - A2 A5 A6 MZ; img_apply Z.ltb_ge; zlia)).
assert (G7 : (SMv + 768 <? SHBv + UEv / 8) = true) by (img_try (clear - A2 A5 MZ; img_apply Z.ltb_lt; zlia)).
assert (G8 : (SHBv + UEv / 8 + RLv / 8 <? SHBv + ENDv / 8) = false) by (img_try (clear - A1 A3 A4 A8 A9 MZ; img_apply Z.ltb_ge; zlia)).
rewrite G1, G2, G3, G4, G5, G6, G7, G8 in B2'. cbn [app] in B2'.
pose proof (Forall_inv B2') as C1. pose proof (Forall_inv (Forall_inv_tail B2')) as C2. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail B2'))) as C3. clear B2'.
rewrite Z.min_l in C1 by (img_try (clear - A2 A5 MZ; zlia)). rewrite Z.min_l in C2 by (img_try (clear - A2 A5 MZ; zlia)). rewrite Z.min_r in C3 by (img_try (clear - A1 A2 A4 MZ; zlia)).
rewrite <- A3 in B1. unfold SH4. img_apply Forall_cons; [img_try (img_exact B1)|]. img_apply Forall_cons; [img_try (img_exact C1)|]. img_apply Forall_cons; [img_try (img_exact C2)|]. img_apply Forall_cons; [img_try (img_exact C3) | img_try (img_apply Forall_nil)]. }
s_runS HR tfxtbl_rr tfxtbl_rr_ok (0x31dc0 + D_150) (runto (0x31dc0 + D_150) T_P6) HX HP4.
s_pin HR (22%bv : bv 5) (SOff aN8DS 0).
{ clear - NR Hn Z4 MZ. pin_zevS. rewrite EaN8D, E10, Hn. unfold w64. rewrite !unsigned_lit_small by zlia. zcanon_simp.
img_change (zcanon 281474976710648) with (2 ^ 48 - 8). rewrite land_m8_48 by zlia. unfold N8D in *.
pose proof (Z.div_mod n 8 ltac:(img_try (zlia))). pose proof (Z.mod_pos_bound n 8 ltac:(img_try (zlia))). rewrite Z.add_0_r. zcanon_simp. zlia. }
s_station HR T_P7.
s_runS HR tfxtbl_rr tfxtbl_rr_ok (0x54344 + D_2c4) T_L5 HX HP4.
s_ladderW s_runS HR tfxtbl_rr tfxtbl_rr_ok (0x54594 + D_2c4) T_L5l T_L5lo T_L5h T_L5h2 T_L5h3a T_L5h3 T_L5hi T_R sL5 CLOB_Lt HX HP4.
img_apply SRr_ret. img_exact HR.
Qed.
Lemma segT2 : forall W' c, at_S Wy md1 X (PSR Wy SH2 (PDX z)) T_2 W' c -> SRr tfxsegs W' c (at_S Wy md1 X (PSR Wy SH4 (PDX z)) T_R).
Proof.
intros W1 c HR. pose proof SH_ok as (_ & _ & OK2). pose proof (PSR_stableS SH2 (PDX z) OK2 (PDX_stableS z)) as HP2.
assert (HX : forall a, WIN1S a -> X a) by (img_try (intros a Ha; apply HXW, WIN1S_WIN, Ha)).
pose proof map_facts as (M1 & M2 & _). pose proof map_zoneN as MZ. pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & _).
ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in M1, M2. unfold MALLOC_MAX in Z8.
pose proof high_facts as (_ & _ & F3 & F4 & F5 & F6 & _). ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kSpaceSize, kPrimResvSize in F3, F4, F5, F6.
s_runS HR tfxtbl_rr tfxtbl_rr_ok (0x31cfc + D_150) T_M0 HX HP2.
destruct Hmap_apart as (_ & _ & MP & _). unfold zdisjoint in MP. cbn [fst snd] in MP. unfold kPrimResvSize in MP.
destruct MP as [MP|MP].
- s_arm HR BC_LTU true (SOff aMAP 4096) (SOff aSB 0).
{ clear - MP M1 M2 Z8 F3 F4 F5 F6 MZ. arm_zevS. rewrite EaMAP, EaSB. unfold w64. rewrite !unsigned_lit_small by (img_try (try unfold SB in *; zlia)). zcanon_simp. img_apply Z.ltb_lt. try unfold SB in *. zlia. }
s_runS HR tfxtbl_rr tfxtbl_rr_ok (0x31d34 + D_150) T_Ma HX HP2.
lazymatch type of HR with at_S ?Wx ?md ?X0 ?P ?ss ?W' ?c' =>
pose proof (at_S_forget Wx md X0 P ss W' c' sGA [11]%bv HR ltac:(img_try (unfold sHAV, sGA; zlia)) eq_refl
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))) as HR2; clear HR; rename HR2 into HR end.
s_noconds HR. s_station HR T_N. img_exact (segT2b _ _ HR).
- s_arm HR BC_LTU false (SOff aMAP 4096) (SOff aSB 0).
{ clear - MP M1 M2 Z8 F3 F4 F5 F6 MZ. arm_zevS. rewrite EaMAP, EaSB. unfold w64. rewrite !unsigned_lit_small by (img_try (try unfold SB in *; zlia)). zcanon_simp. img_apply Z.ltb_ge. try unfold SB in *. zlia. }
s_runS HR tfxtbl_rr tfxtbl_rr_ok (0x31d0c + D_150) (runto (0x31d0c + D_150) (arm BC_LTU false (SOff aMAP 4096) (SOff aSB 0) T_M0)) HX HP2.
s_arm HR BC_GEU true (SOff aMAP 4096) (SOff aSB 137438953472).
{ clear - MP M1 M2 Z8 F3 F4 F5 F6 MZ. arm_zevS. rewrite EaMAP, EaSB. unfold w64. rewrite !unsigned_lit_small by (img_try (try unfold SB in *; zlia)). zcanon_simp.
rewrite (proj2 (Z.ltb_ge _ _)); [img_refl|]. try unfold SB in *. zlia. }
s_runS HR tfxtbl_rr tfxtbl_rr_ok (0x31d34 + D_150) T_Mb HX HP2.
lazymatch type of HR with at_S ?Wx ?md ?X0 ?P ?ss ?W' ?c' =>
pose proof (at_S_forget Wx md X0 P ss W' c' sGA [11]%bv HR ltac:(img_try (unfold sHAV, sGA; zlia)) eq_refl
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))) as HR2; clear HR; rename HR2 into HR end.
s_noconds HR. s_station HR T_N. img_exact (segT2b _ _ HR).
Qed.
End T2.
End h.
End g.
