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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF64 YF3v YF3w YF3x YF41 YF6z YF0a YF7f YF48 YF49 YF71 YF72 YF73 YF74 YF0h YF7o YF7p YF7q YF7a YF7g YF7h YF7d YF7e YF7i YF7j YF7l YF7n.
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
Section b0. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
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
Section c0. Context {imgk : img}.
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
Local Abbreviation AR5 f := (f Nrange Hidx Hres Hmap) (only parsing).
Local Abbreviation map_facts := (AR5 (AR3 (@YF7f.map_facts _))).
Local Abbreviation map_zone := ((AR3 (@YF7f.map_zone _)) Nrange Hidx Hmap).
Local Abbreviation map_zoneN := (AR5 (AR3 (@YF7f.map_zoneN _))).
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
Local Abbreviation ARa f := (AR0 f LY IMG) (only parsing).
Local Abbreviation ARd f := (f Nrange Hidx Hres) (only parsing).
Local Abbreviation WSKELP_WINP := (ARd (ARa (AR1 (@YF7f.WSKELP_WINP _)))).
Local Abbreviation WSKEL1P_WIN1P := (ARd (ARa (AR1 (@YF7f.WSKEL1P_WIN1P _)))).
Local Abbreviation WMAP_WINM := (AR5 (ARa (AR1 (@YF7f.WMAP_WINM _)))).
Local Abbreviation WSKEL_WIN := (AR5 (ARa (AR1 (@YF7f.WSKEL_WIN _)))).
Local Abbreviation WSKEL1_WIN1 := (AR5 (ARa (AR1 (@YF7f.WSKEL1_WIN1 _)))).
Local Abbreviation windows_in := ((AR9 (@YF7f.windows_in ly regs0)) Hidx Hres).
Local Abbreviation windows_WINP := (ARd (ARa (AR1 (@YF7f.windows_WINP _)))).
Local Abbreviation windows_WIN1P := (ARd (ARa (AR1 (@YF7f.windows_WIN1P _)))).
Local Abbreviation windows_WIN := (AR5 (ARa (AR1 (@YF7f.windows_WIN _)))).
Local Abbreviation windows_WIN1 := (AR5 (ARa (AR1 (@YF7f.windows_WIN1 _)))).
Local Abbreviation frame_WIN1P := (ARd (ARa (AR1 (@YF7f.frame_WIN1P _)))).
Local Abbreviation frame_WIN1 := (AR5 (ARa (AR1 (@YF7f.frame_WIN1 _)))).
Local Abbreviation AR2 f := (f LY IMG Hsp Nrange Hidx Hres) (only parsing).
Local Abbreviation WINP_not_high := (AR2 (AR3 (@YF7f.WINP_not_high _))).
Local Abbreviation ARi f := (AR2 f Hmap) (only parsing).
Local Abbreviation WIN_not_high := (ARi (AR3 (@YF7f.WIN_not_high _))).
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
Local Abbreviation AR6 f := (AR2 f Hmap Hmap_apart) (only parsing).
Local Abbreviation DZONE_disj := (AR6 (AR3 (@YF7f.DZONE_disj _))).
Local Abbreviation RFACTS := (AR1 (@YF7f.RFACTS)).
Local Abbreviation zone_lit := ((AR1 (@YF7f.zone_lit _)) LY IMG Hsp).
Local Abbreviation zone_irw := ((AR1 (@YF7f.zone_irw _)) LY IMG Hsp).
Local Abbreviation zone_T := ((AR1 (@YF7f.zone_T _)) idx res LY IMG Hsp Hidx Hres).
Local Abbreviation zone_C := ((AR1 (@YF7f.zone_C _)) idx res LY IMG Hsp Hidx Hres).
Local Abbreviation tail_ext_ok := (AR2 (AR0 (AR1 (@YF7f.tail_ext_ok _)))).
Local Abbreviation RFACTS_map := ((AR5 ((AR3 (@YF7f.RFACTS_map _)) LY IMG)) Hmap_apart).
Local Abbreviation AR4 f := (f imgk W ly regs0 mem0) (only parsing).
Local Abbreviation at_ST := (AR0 ((AR4 (@YF7f.at_ST _)) md0)).
Local Abbreviation memset_stretch := ((AR5 ((AR9 ((AR4 (@YF7f.memset_stretch _ _)) md0 n)) Hsp)) Hmap_apart mat0 DPOST).
Ltac clearM := try clear DPOST; try clear Hmap_apart; try clear Hmap.
Local Abbreviation AR7 f := (AR1 f mem0) (only parsing).
Local Abbreviation at_S := (AR0 (AR7 (@YF7f.at_S _))).
Local Abbreviation at_N := (AR0 (AR7 (@YF7f.at_N _))).
Local Abbreviation at_RETS := ((AR7 (@YF7f.at_RETS _)) ch).
Local Abbreviation pstable := (@YF7f.pstable).
Local Abbreviation stack_shaped := (@YF7f.stack_shaped).
Local Abbreviation window_present := (ARf (AR1 (@YF7f.window_present))).
Local Abbreviation stack_present_of := ((AR0 (AR1 (@YF7f.stack_present_of _))) LY Hsp Hidx).
Local Abbreviation mid_not_WIN1P := (AR2 (AR3 (@YF7f.mid_not_WIN1P _))).
Local Abbreviation mid_not_WIN1 := (ARi (AR3 (@YF7f.mid_not_WIN1 _))).
Local Abbreviation wins_ok := (@YF7f.wins_ok).
Local Abbreviation at_S_run_gen := ((AR0 (AR7 (@YF7f.at_S_run_gen _ _))) LY Hsp Hidx).
Local Abbreviation at_S_run_ecall_gen := ((AR0 (AR7 (@YF7f.at_S_run_ecall_gen _ _))) LY Hsp Hidx).
Local Abbreviation at_S_runP := (AR2 (AR0 (AR7 (@YF7f.at_S_runP _ _)))).
Local Abbreviation at_S_runM := (ARi (AR0 (AR7 (@YF7f.at_S_runM _ _)))).
Local Abbreviation at_S_run_ecallP := (AR2 (AR0 (AR7 (@YF7f.at_S_run_ecallP _ _)))).
Local Abbreviation at_S_run_ecallM := (ARi (AR0 (AR7 (@YF7f.at_S_run_ecallM _ _)))).
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
Local Abbreviation at_S_ret := (ARd ((AR0 (AR7 (@YF7f.at_S_ret _))) Htp Hra Hsp)).
Local Abbreviation kept_of_frame2 := (ARf (AR1 (@YF7f.kept_of_frame2))).
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
Local Abbreviation vis_present := ((ARf (AR4 (@YF7o.vis_present _))) DPOST B S HARm).
Local Abbreviation in_thread_junk := (@YF7o.in_thread_junk ly B S).
Local Abbreviation in_sec_junk := (@YF7o.in_sec_junk ly B S).
Local Abbreviation in_as_junk := (@YF7o.in_as_junk ly B S).
Local Abbreviation junk_word := ((ARe (AR4 (@YF7o.junk_word _))) DPOST B S HARm).
Local Abbreviation cell_sym := ((ARg (@YF7o.cell_sym _)) mem0 B S TS HARm).
Local Abbreviation cell_lit := ((ARg (@YF7o.cell_lit _)) mem0 B S TS HARm).
Local Abbreviation cell_state := ((ARg (@YF7o.cell_state _)) mem0 B S HARm).
Local Abbreviation In_acells_sec := (@YF7o.In_acells_sec ly B S).
Local Abbreviation sec_vals := ((ARg (@YF7o.sec_vals _)) mem0 idx res B S TS HARm Hidx_def Hres_def).
Local Abbreviation unwinding_val := ((ARg (@YF7o.unwinding_val _)) mem0 B S HARm).
Local Abbreviation rw_writable := ((ARf (AR1 (@YF7o.rw_writable))) DPOST S).
Local Abbreviation val_mem_mod8 := ((ARf (AR4 (@YF7o.val_mem_mod8))) DPOST S).
Local Abbreviation chunk_lit := (AR0 (AR4 (@YF7o.chunk_lit))).
Local Abbreviation chunk_lit_at := (AR0 (AR4 (@YF7o.chunk_lit_at))).
Local Abbreviation chunk_atom := ((AR0 (AR4 (@YF7o.chunk_atom))) Hidx DPOST S).
Local Abbreviation ARb f := (f DPOST B S TS HTSD HARm Hidx_def Hres_def Hj0 Hj1 Hj2 Hj3 Hj4 Hj5 Hj9 Hj6 Hj7 Hj8 Hi1 Hi2 Hi3) (only parsing).
Local Abbreviation SREG0_ok := (ARb ((AR2 (AR0 (AR4 (@YF7p.SREG0_ok _)))) Hpres0)).
Local Abbreviation PAIRS_ok := ((AR2 (AR0 (AR4 (@YF7q.PAIRS_ok _)))) DPOST S).
Local Abbreviation FACTS_ok := ((ARd ((ARa (AR4 (@YF7q.FACTS_ok _))) Hn Hsp)) DPOST S).
Local Abbreviation SEED_ok := (ARb ((ARd ((ARa (AR4 (@YF7q.SEED_ok _ _))) Hn Hsp)) Hpres0)).
Local Abbreviation PBUF := ((ARg (@YF7a.PBUF)) regs0 ch).
Local Abbreviation PBUF_stableP := (AR2 (AR9 ((ARg (@YF7a.PBUF_stableP _)) regs0 n ch))).
Local Abbreviation PBUF_stableM := (ARi (AR9 ((ARg (@YF7a.PBUF_stableM _)) regs0 n ch))).
Local Abbreviation seg0 := (ARb ((ARd ((ARa ((AR4 (@YF7a.seg0 _ _)) md0)) Hn Htp Hra4096 Hsp Hch)) Hpres0 mat0 U1)).
Local Abbreviation appregs := (@YF7g.appregs).
Local Abbreviation st_ok_appregs := (@YF7g.st_ok_appregs _ imgk).
Local Abbreviation at_S_app := (AR0 (AR7 (@YF7g.at_S_app _))).
Local Abbreviation WIN1N := ((AR1 (@YF7g.WIN1N)) n).
Local Abbreviation WINPN := ((AR1 (@YF7g.WINPN)) n).
Local Abbreviation WSKEL1N := (@YF7g.WSKEL1N imgk).
Local Abbreviation WIN1N_WINPN := ((AR3 (@YF7g.WIN1N_WINPN)) Hidx).
Local Abbreviation windows_WIN1N := (ARd (ARa (AR1 (@YF7g.windows_WIN1N _)))).
Local Abbreviation mid_not_WIN1N := (AR2 (AR3 (@YF7g.mid_not_WIN1N _))).
Local Abbreviation at_S_runN := (AR2 (AR0 (AR7 (@YF7g.at_S_runN _ _)))).
Local Abbreviation PBUF_stableN := (AR2 (AR9 ((ARg (@YF7g.PBUF_stableN _)) regs0 n ch))).
Local Abbreviation at_S_val := (AR0 (AR7 (@YF7g.at_S_val _))).
Local Abbreviation memset_stretchW := ((ARd ((AR4 (@YF7g.memset_stretchW _)) md0 n idx res Hsp)) mat0 DPOST S).
Local Abbreviation at_S_memset := ((ARd ((AR0 ((AR4 (@YF7g.at_S_memset _)) md0)) Hsp)) mat0 DPOST S).
Local Abbreviation WIN1T := (ARc (@YF7g.WIN1T)).
Local Abbreviation WIN1T_WIN := (AR5 (AR3 (@YF7g.WIN1T_WIN _))).
Local Abbreviation windows_WIN1T := (AR5 (ARa (AR1 (@YF7g.windows_WIN1T _)))).
Local Abbreviation WIN1T_WIN1_aux := (AR5 (AR3 (@YF7g.WIN1T_WIN1_aux _))).
Local Abbreviation mid_not_WIN1T := (ARi (AR3 (@YF7g.mid_not_WIN1T _))).
Local Abbreviation at_S_runT := (ARi (AR0 (AR7 (@YF7g.at_S_runT _ _)))).
Local Abbreviation at_S_run_ecallT := (ARi (AR0 (AR7 (@YF7g.at_S_run_ecallT _ _)))).
Local Abbreviation PBUFW := ((AR1 (@YF7g.PBUFW)) ch).
Local Abbreviation ARh f := (AR1 f n ch) (only parsing).
Local Abbreviation PBUFW_stableT := (ARi (AR9 (ARh (@YF7g.PBUFW_stableT _)))).
Local Abbreviation WIN1S := (ARc (@YF7h.WIN1S)).
Local Abbreviation WSKEL1S := (@YF7h.WSKEL1S imgk).
Local Abbreviation WIN1S_WIN1T := (ARc (@YF7h.WIN1S_WIN1T)).
Local Abbreviation WIN1S_WIN := (AR5 (AR3 (@YF7h.WIN1S_WIN _))).
Local Abbreviation windows_WIN1S := (AR5 (ARa (AR1 (@YF7h.windows_WIN1S _)))).
Local Abbreviation mid_not_WIN1S := (ARi (AR3 (@YF7h.mid_not_WIN1S _))).
Local Abbreviation at_S_runS := (ARi (AR0 (AR7 (@YF7h.at_S_runS _ _)))).
Local Abbreviation at_S_run_ecallS := (ARi (AR0 (AR7 (@YF7h.at_S_run_ecallS _ _)))).
Local Abbreviation brun := (@YF7h.brun).
Local Abbreviation run_ok := (@YF7h.run_ok n mb).
Local Abbreviation PS := ((ARh (@YF7h.PS)) mb).
Local Abbreviation runs_not_WIN1S := (AR6 (AR3 (@YF7h.runs_not_WIN1S _))).
Local Abbreviation runs_not_stack := ((AR5 ((AR3 (@YF7h.runs_not_stack _)) LY Hsp)) Hmap_apart).
Local Abbreviation PS_stable := (AR6 (AR9 (ARh (@YF7h.PS_stable _)))).
Local Abbreviation cut1 := (@YF7h.cut1).
Local Abbreviation cut := (@YF7h.cut).
Local Abbreviation cut_sound := ((AR5 (AR9 ((AR7 (@YF7h.cut_sound _)) n))) DPOST S).
Local Abbreviation cut_ok := ((AR9 (@YF7h.cut_ok ly regs0 mem0 n)) Hidx Hres DPOST S).
Local Abbreviation at_S_memsetS := ((AR5 ((AR0 ((AR4 (@YF7h.at_S_memsetS _ _)) md0)) LY Hsp)) Hmap_apart mat0 DPOST S).
Local Abbreviation skel_okb := (@YF7h.skel_okb imgk).
Local Abbreviation skel_cases := ((ARf (@YF7h.skel_cases imgk)) Hres S Hidx_def Hres_def).
Local Abbreviation AR8 f := (f DPOST S Hidx_def Hres_def) (only parsing).
Local Abbreviation skel_apart := (AR8 (AR6 (AR0 (AR7 (@YF7h.skel_apart _))))).
Local Abbreviation skel_u64 := (AR8 (ARi (AR0 (AR7 (@YF7h.skel_u64 _))))).
Local Abbreviation memset_ext_of_skel := (AR8 (AR6 (AR0 (AR7 (@YF7h.memset_ext_of_skel _))))).
Local Abbreviation memset_u64_of_skel := (AR8 (ARi (AR0 (AR7 (@YF7h.memset_u64_of_skel _))))).
Local Abbreviation WIN1R := ((AR1 (@YF7h.WIN1R)) n mb).
Local Abbreviation WSKEL1R := (@YF7h.WSKEL1R imgk).
Local Abbreviation WIN1R_WIN1S := (ARc (@YF7h.WIN1R_WIN1S)).
Local Abbreviation WIN1R_WIN := (AR5 (AR3 (@YF7h.WIN1R_WIN _))).
Local Abbreviation windows_WIN1R := (AR5 (ARa (AR1 (@YF7h.windows_WIN1R _)))).
Local Abbreviation mid_not_WIN1R := (ARi (AR3 (@YF7h.mid_not_WIN1R _))).
Local Abbreviation at_S_runR := (ARi (AR0 (AR7 (@YF7h.at_S_runR _ _)))).
Local Abbreviation at_S_run_ecallR := (ARi (AR0 (AR7 (@YF7h.at_S_run_ecallR _ _)))).
Local Abbreviation PSR := ((ARh (@YF7h.PSR)) mb).
Local Abbreviation rstable := ((AR1 (@YF7h.rstable)) n mb).
Local Abbreviation rstable_true := ((AR1 (@YF7h.rstable_true)) n mb).
Local Abbreviation PSR_stable := (AR6 (AR9 (ARh (@YF7h.PSR_stable _)))).
Local Abbreviation QSP := (@YF7h.QSP imgk ly idx).
Local Abbreviation QS_not_WIN1R := (AR6 (AR3 (@YF7h.QS_not_WIN1R _))).
Local Abbreviation QSP_rstable := (AR6 (AR3 (@YF7h.QSP_rstable _))).
Local Abbreviation at_S_memsetSR := ((AR5 ((AR0 ((AR4 (@YF7h.at_S_memsetSR _ _)) md0)) LY Hsp)) Hmap_apart mat0 DPOST S).
Local Abbreviation chunk_eqb := (@YF7h.chunk_eqb imgk).
Local Abbreviation chunk_eqb_eq := ((ARf (@YF7h.chunk_eqb_eq imgk)) Hres S Hidx_def Hres_def).
Local Abbreviation subregionb := (@YF7h.subregionb imgk).
Local Abbreviation subregionb_sound := (AR8 ((ARf (AR7 (@YF7h.subregionb_sound))) Hres)).
Local Abbreviation submemb := (@YF7h.submemb imgk).
Local Abbreviation submemb_sound := (AR8 ((ARf (AR7 (@YF7h.submemb_sound))) Hres)).
Local Abbreviation at_S_submem := (AR8 ((AR0 (AR7 (@YF7h.at_S_submem _))) Hidx Hres)).
Local Abbreviation at_S_addreg := (AR0 (AR7 (@YF7h.at_S_addreg _))).
Local Abbreviation PSR_runs := (AR0 (AR7 (@YF7d.PSR_runs _))).
Local Abbreviation place_WIN := (ARc (@YF7d.place_WIN)).
Local Abbreviation SH0 := (@YF7d.SH0 n mb).
Local Abbreviation SH1 := (@YF7d.SH1 n mb).
Local Abbreviation SH2 := (@YF7d.SH2 n mb).
Local Abbreviation SH_ok := (AR5 (AR3 (@YF7d.SH_ok _))).
Local Abbreviation segG1 := (AR8 ((AR6 (AR0 ((AR4 (@YF7d.segG1 _ _)) md0))) mat0)).
Local Abbreviation RX_stableS := (ARc (@YF7e.RX_stableS)).
Local Abbreviation rstable_and := ((AR1 (@YF7e.rstable_and)) n mb).
Local Abbreviation pstable_and := (@YF7e.pstable_and).
Local Abbreviation PSR_stableS' := (AR6 (AR9 (ARh (@YF7e.PSR_stableS' _)))).
Local Abbreviation pairwise_disjoint_map := (@YF7e.pairwise_disjoint_map).
Local Abbreviation at_S_setchunks := (AR0 (AR7 (@YF7e.at_S_setchunks _))).
Local Abbreviation chunk_ok_CVal_eqv := (@YF7e.chunk_ok_CVal_eqv imgk).
Local Abbreviation RES2T_ne := ((AR0 (AR1 (@YF7e.RES2T_ne))) Hidx Hres).
Local Abbreviation RES2T_eq := ((AR0 (AR1 (@YF7e.RES2T_eq))) Hidx Hres).
Local Abbreviation sv_denot_eq_of_U := (AR0 (AR1 (@YF7e.sv_denot_eq_of_U))).
Local Abbreviation skel_apart_QS := (AR8 (AR6 (AR0 (AR7 (@YF7e.skel_apart_QS _))))).
Local Abbreviation QSPX := (@YF7e.QSPX imgk ly idx).
Local Abbreviation segNE := (AR8 (AR6 (AR0 (AR7 (@YF7e.segNE _ _))))).
Local Abbreviation segEQa := (AR6 (AR0 (AR7 (@YF7e.segEQa _ _)))).
Local Abbreviation zev_SAlu := (@YF7e.zev_SAlu).
Local Abbreviation zev_SLit := (@YF7e.zev_SLit).
Local Abbreviation zev_SOff := (@YF7e.zev_SOff).
Local Abbreviation segJ2 := (AR8 (AR6 (AR0 (AR7 (@YF7e.segJ2 _ _))))).
Local Abbreviation segJ := (AR8 (AR6 (AR0 (AR7 (@YF7e.segJ _ _))))).
Local Abbreviation QR := (@YF7i.QR ly res).
Local Abbreviation segT1 := ((AR5 ((ARa (AR7 (@YF7i.segT1 _ _))) Hn Hsp)) Hmap_apart).
Local Abbreviation DX := (AR1 (@YF7i.DX)).
Local Abbreviation PD := (@YF7i.PD imgk ly mem0 DPOST).
Local Abbreviation PD_rstable := ((AR6 (AR9 ((AR7 (@YF7i.PD_rstable _)) n))) DPOST).
Local Abbreviation PD_stableT := ((AR6 (AR9 ((AR7 (@YF7i.PD_stableT _)) n))) DPOST).
Local Abbreviation PSR_stableS := (AR6 (AR9 (ARh (@YF7i.PSR_stableS _)))).
Local Abbreviation PD_stableS := ((AR6 (AR9 ((AR7 (@YF7i.PD_stableS _)) n))) DPOST).
Local Abbreviation PDX := (@YF7i.PDX imgk ly mem0 DPOST).
Local Abbreviation PDX_rstable := ((AR6 (AR9 ((AR7 (@YF7i.PDX_rstable _)) n))) DPOST).
Local Abbreviation PDX_stableT := ((AR6 (AR9 ((AR7 (@YF7i.PDX_stableT _)) n))) DPOST).
Local Abbreviation PDX_stableS := ((AR6 (AR9 ((AR7 (@YF7i.PDX_stableS _)) n))) DPOST).
Local Abbreviation dx_okb := (@YF7i.dx_okb imgk).
Local Abbreviation skel_apart_DX := (AR8 (AR6 (AR0 (AR7 (@YF7i.skel_apart_DX _))))).
Local Abbreviation skel_apart_stk := ((AR6 (AR0 (AR1 (@YF7i.skel_apart_stk _)))) S Hidx_def Hres_def).
Local Abbreviation at_S_depot := (AR8 (AR6 (AR0 (AR4 (@YF7i.at_S_depot _ _))))).
Local Abbreviation SH3 := (@YF7i.SH3 n mb).
Local Abbreviation SH4 := (@YF7i.SH4 n mb).
Local Abbreviation shadow_marks := (AR5 (AR3 (@YF7i.shadow_marks _))).
Local Abbreviation SH34_ok := (AR5 (AR3 (@YF7i.SH34_ok _))).
Local Abbreviation segT2b := (AR8 ((AR5 ((ARa ((AR4 (@YF7i.segT2b _ _)) md0)) Hn Hsp)) Hmap_apart mat0)).
Local Abbreviation segT2 := (AR8 ((AR5 ((ARa ((AR4 (@YF7i.segT2 _ _)) md0)) Hn Hsp)) Hmap_apart mat0)).
Local Abbreviation SH5 := (@YF7j.SH5 n mb).
Local Abbreviation SH6 := (@YF7j.SH6 n mb).
Local Abbreviation user_marks := (AR5 (AR3 (@YF7j.user_marks _))).
Local Abbreviation SH56_ok := (AR5 (AR3 (@YF7j.SH56_ok _))).
Local Abbreviation segU1 := (AR8 ((AR6 (AR0 ((AR4 (@YF7j.segU1 _ _)) md0))) mat0)).
Local Abbreviation SH6_of_cut := (AR5 (AR3 (@YF7j.SH6_of_cut _))).
Local Abbreviation segUe := (AR8 ((AR5 ((ARa ((AR4 (@YF7j.segUe _ _)) md0)) Hn Hsp)) Hmap_apart mat0)).
Local Abbreviation PT := ((ARh (@YF7j.PT)) mb).
Local Abbreviation run_okT := (@YF7j.run_okT n mb).
Local Abbreviation SH5o := (@YF7j.SH5o n mb).
Local Abbreviation SH6o := (@YF7j.SH6o n mb).
Local Abbreviation SH56o_ok := (AR5 (AR3 (@YF7j.SH56o_ok _))).
Local Abbreviation PT_stableT := (AR6 (AR9 (ARh (@YF7j.PT_stableT _)))).
Local Abbreviation segUo := (AR8 ((AR5 ((ARa ((AR4 (@YF7j.segUo _ _)) md0)) Hn Hsp)) Hmap_apart mat0)).
Local Abbreviation SHLO := (@YF7l.SHLO).
Local Abbreviation SHHI := (@YF7l.SHHI n).
Local Abbreviation SH_hull := (@YF7l.SH_hull ly regs0 n res Nrange S).
Local Abbreviation lit_m1 := (@YF7l.lit_m1).
Local Abbreviation lit_enomem := (@YF7l.lit_enomem).
Local Abbreviation nores34 := (@YF7l.nores34).
Local Abbreviation core34 := (@YF7l.core34).
Local Abbreviation pru_MS := (@YF7l.pru_MS ly regs0 n res Nrange S).
Local Abbreviation grant_anon_shape := (@YF7l.grant_anon_shape).
Local Abbreviation Hcut_out := (@YF7l.Hcut_out).
Local Abbreviation slackS := ((ARg (@YF7l.slackS _)) mem0 md0 B S HARm HQT).
Local Abbreviation S_N_facts := (@YF7l.S_N_facts imgk).
Local Abbreviation S_N_ext64 := ((AR2 (AR0 (AR1 (@YF7l.S_N_ext64 _)))) S).
Local Abbreviation S_N_win64 := ((AR2 (AR0 (AR1 (@YF7l.S_N_win64 _)))) S).
Local Abbreviation nodeS := ((AR2 (AR0 ((AR4 (@YF7l.nodeS _ _)) md0))) B S HARm HQT).
Local Abbreviation CZI := (@YF7n.CZI imgk).
Local Abbreviation CZ := (@YF7n.CZ imgk ly).
Local Abbreviation abs_cell_okS := (@YF7n.abs_cell_okS imgk).
Local Abbreviation abs_cells_okS := (@YF7n.abs_cells_okS imgk).
Local Abbreviation MPAD := (@YF7n.MPAD imgk).
Local Abbreviation padb := (@YF7n.padb imgk).
Local Abbreviation const_cells_CZ := ((AR3 (@YF7n.const_cells_CZ)) Nrange Hidx B TS HTSD).
Local Abbreviation CZ_untouched := ((AR6 (AR9 ((AR7 (@YF7n.CZ_untouched _)) n))) DPOST S).
Local Abbreviation cell_holds_agree := ((ARf (@YF7n.cell_holds_agree ly regs0 mem0)) Hres DPOST B S).
Local Abbreviation aview_agreeW := (@YF7n.aview_agreeW imgk W).
Local Abbreviation rd_ext_Wy := (@YF7n.rd_ext_Wy imgk W).
Local Abbreviation depot_ids_bound := ((AR9 (AR7 (@YF7n.depot_ids_bound))) Hidx Hres DPOST B S TS).
Local Abbreviation depot_mem_ok_agree := ((AR9 (AR7 (@YF7n.depot_mem_ok_agree))) Hidx Hres DPOST B S TS).
Local Abbreviation depot_mem_ok_ext := (@YF7n.depot_mem_ok_ext ly B).
Local Abbreviation depot_at0 := ((AR5 ((AR9 ((AR4 (@YF7n.depot_at0 _)) n)) Hsp)) Hmap_apart DPOST B S HARm).
Local Abbreviation DPOSTS := ((AR1 (@YF7n.DPOSTS)) ch B S).
Local Abbreviation D1W_ok := ((AR6 (AR9 ((AR4 (@YF7n.D1W_ok _ _)) n ch))) DPOST B S TS HTSD HARm Hgp).
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
Local Open Scope am_scope.
Let rd0 : reader := aview tfxsegs (w_H W) mem0.
Let WF := am_wf B ly S rd0 HARm.
Definition lyF : alayout := set_ly_sec ly (rS S) mb.
Definition SFS (grow : bool) (z : Z) : astate := sfinal S n tr z MSv NDv grow.
Definition KSc : chunk := KS S n.
Lemma lyF_le : layout_le (length (st_secs S)) ly lyF.
Proof. clearP. unfold lyF, rS. img_apply set_ly_sec_le. Qed.
Lemma lyF_sec : ly_sec lyF (rS S) = mb.
Proof. clearP. unfold lyF, set_ly_sec. cbn. rewrite PeanoNat.Nat.eqb_refl. img_refl. Qed.
Lemma lyF_eqs : ly_prim lyF = ly_prim ly /\ ly_space lyF = ly_space ly /\ ly_Q lyF = Qb /\ ly_T lyF = T /\ ly_C lyF = ly_C ly /\ ly_F lyF = ly_F ly /\
ly_NB lyF = ly_NB ly /\ ly_SB lyF = ly_SB ly /\ ly_top lyF = ly_top ly /\ ly_stk_lo lyF = ly_stk_lo ly /\ ly_stk_hi lyF = ly_stk_hi ly /\
ly_tsd lyF = ly_tsd ly /\ ly_tr0 lyF = ly_tr0 ly /\ ly_extra lyF = ly_extra ly /\ ly_D lyF = ly_D ly /\ ly_vis0 lyF = ly_vis0 ly.
Proof. clearP. unfold lyF, set_ly_sec. cbn. repeat split; img_refl. Qed.
Lemma lyF_ok : layout_ok lyF.
Proof. unfold lyF. img_apply set_ly_sec_ok. img_exact LY. Qed.
Lemma sizes_model : needed_size n = NDv /\ sec_map_size n = MSv /\ req_size n = n /\ rz_size n = 2048 /\ from_primary n = false /\
ck_n KSc = n /\ ck_rz KSc = 2048 /\ ck_extent KSc = MSv - 4096 /\ ck_req KSc = n /\ ck_beg KSc = PSec (rS S) 4096 /\ ck_state KSc = CAllocated.
Proof.
clearP. pose proof Nrange as NR. unfold MALLOC_MAX in NR.
assert (RZ : rz_size n = 2048).
{ unfold rz_size, rz_log. rewrite (proj2 (Z.leb_gt n 48)), (proj2 (Z.leb_gt n 96)), (proj2 (Z.leb_gt n 448)), (proj2 (Z.leb_gt n 3968)),
(proj2 (Z.leb_gt n 16128)), (proj2 (Z.leb_gt n 32256)), (proj2 (Z.leb_gt n 64512)) by zlia. img_refl. }
assert (RS : req_size n = n) by (img_try (unfold req_size; destruct (Z.eqb_spec n 0); zlia)).
assert (R8 : rounded_size n = R8v) by (img_try (unfold rounded_size, round_up, R8v; rewrite Z.max_l by zlia; replace (n + 8 - 1) with (n + 7) by zlia; img_refl)).
assert (FP : from_primary n = false) by (img_try (unfold from_primary, needed_primary; rewrite R8, RZ; img_apply Z.leb_gt; unfold kMaxSize, R8v; pose proof (Z.div_mod (n+7) 8 ltac:(zlia)); pose proof (Z.mod_pos_bound (n+7) 8 ltac:(zlia)); zlia)).
assert (ND : needed_size n = NDv) by (img_try (unfold needed_size, needed_primary, NDv; rewrite FP, R8, RZ; zlia)).
assert (MS : sec_map_size n = MSv) by (img_try (unfold sec_map_size, round_up, MSv, kPage; rewrite ND; replace (NDv + 4096 - 1) with (NDv + 4095) by zlia; img_refl)).
unfold KSc, KS, ck_n, ck_rz, ck_extent, ck_req, ck_beg, ck_state. cbn [YG00.ck_req YG00.ck_beg YG00.ck_state].
rewrite RS, RZ, FP, MS. unfold kPage. repeat split; try img_refl; zlia.
Qed.
Lemma val_mem_cell : forall (Hh : word -> bool) mem e (w : nat) e' lyx,
val_mem tfxsegs (mrestrict Hh mem) (aeval B lyx e) w (aeval B lyx e') -> cell_holds B lyx (aview tfxsegs Hh mem) (ACell e w (AV e')).
Proof.
clearP. intros Hh mem e w e' lyx HV k Hk. cbn [c_at c_val c_w]. unfold aview. rewrite (HV k Hk). cbn [option_map].
rewrite <- le_byte_eq. rewrite unsigned_lit_small8; [img_refl|]. unfold YG0h.le_byte. img_apply Z.mod_pos_bound. zlia.
Qed.
Lemma le_byte_1_0 : forall x, 0 <= x < 256 -> YP0g.le_byte x 1 0 = x.
Proof.
clearP. intros x Hx. unfold YP0g.le_byte. img_change (2 ^ (8 * Z.of_nat 1)) with 256. img_change (8 * Z.of_nat 0)%Z with 0.
rewrite Z.shiftr_0_r, Z.mod_mod by zlia. img_apply Z.mod_small. img_exact Hx.
Qed.
Lemma find_chunk_at_app1 : forall lyx l1 l2 g k, find_chunk_at B lyx l1 g = Some k -> find_chunk_at B lyx (l1 ++ l2) g = Some k.
Proof.
clearP. intros lyx l1 l2 g k. induction l1 as [|k1 t IH]; intros H; [img_try (discriminate H)|]. cbn [find_chunk_at app] in *.
destruct ((ck_base B lyx k1 <=? g) && (g <? ck_base B lyx k1 + ck_extent k1)); [img_try (img_exact H) | img_try (img_exact (IH H))].
Qed.
Lemma find_chunk_at_app2 : forall lyx l1 l2 g, find_chunk_at B lyx l1 g = None -> find_chunk_at B lyx (l1 ++ l2) g = find_chunk_at B lyx l2 g.
Proof.
clearP. intros lyx l1 l2 g. induction l1 as [|k1 t IH]; intros H; [img_refl|]. cbn [find_chunk_at app] in *.
destruct ((ck_base B lyx k1 <=? g) && (g <? ck_base B lyx k1 + ck_extent k1)); [img_try (discriminate H) | img_try (img_exact (IH H))].
Qed.
Lemma In_combine_seq_app : forall {X : Type} (l0 : list X) (x : X) s p, In p (combine (seq s (length l0)) l0) -> In p (combine (seq s (length l0 + 1)) (l0 ++ [x])).
Proof.
clearP. intros X l0. induction l0 as [|y t IH]; intros x s p H; [img_try (destruct H)|]. cbn [length combine seq app Nat.add] in *.
destruct H as [H|H]; [img_try (left; img_exact H) | img_try (right)]. img_apply IH. img_exact H.
Qed.
Lemma combine_seq_last : forall {X : Type} (l0 : list X) (x : X) s, In ((s + length l0)%nat, x) (combine (seq s (length l0 + 1)) (l0 ++ [x])).
Proof.
clearP. intros X l0. induction l0 as [|y t IH]; intros x s; cbn [length combine seq app Nat.add].
- rewrite Nat.add_0_r. left. img_refl.
- right. replace (s + Datatypes.S (length t))%nat with (Datatypes.S s + length t)%nat by zlia. img_apply IH.
Qed.
Lemma in_combine_seq : forall {X : Type} (l : list X) s i x, In (i, x) (combine (seq s (length l)) l) -> nth_error l (i - s) = Some x /\ (s <= i < s + length l)%nat.
Proof.
clearP. intros X l. induction l as [|y t IH]; intros s i x H; [img_try (destruct H)|]. cbn [length seq combine] in H.
destruct H as [H|H].
- injection H as <- <-. rewrite Nat.sub_diag. cbn. split; [img_refl | img_try (zlia)].
- destruct (IH _ _ _ H) as [E R]. replace (i - s)%nat with (Datatypes.S (i - Datatypes.S s)) by zlia. cbn [nth_error length]. split; [img_try (img_exact E) | img_try (zlia)].
Qed.
Lemma combine_seq_in : forall {X : Type} (l : list X) s i x, nth_error l (i - s) = Some x -> (s <= i)%nat -> In (i, x) (combine (seq s (length l)) l).
Proof.
clearP. intros X l. induction l as [|y t IH]; intros s i x E Hs; [img_try (destruct (i - s)%nat; discriminate E)|]. cbn [length seq combine].
destruct (Nat.eq_dec i s) as [->|Hne].
- rewrite Nat.sub_diag in E. cbn in E. injection E as <-. left. img_refl.
- right. img_apply IH; [|img_try (zlia)]. replace (i - s)%nat with (Datatypes.S (i - Datatypes.S s)) in E by zlia. cbn in E. img_exact E.
Qed.
Lemma index_of_app_old : forall (l : list nat) (x r : nat) s, In r l -> index_of (l ++ [x]) r s = index_of l r s.
Proof.
clearP. induction l as [|y t IH]; intros x r s Hr; [img_try (destruct Hr)|]. cbn [index_of app]. destruct (Nat.eqb y r) eqn:E; [img_refl|].
destruct Hr as [->|Hr]; [img_try (rewrite Nat.eqb_refl in E; discriminate E)|]. img_exact (IH x r (Datatypes.S s) Hr).
Qed.
Lemma index_ofZ_app_old : forall (l : list nat) (x r : nat), In r l -> index_ofZ (l ++ [x]) r = index_ofZ l r.
Proof. clearP. intros l x r Hr. unfold index_ofZ. rewrite (index_of_app_old l x r 0 Hr). img_refl. Qed.
Lemma index_of_app_new : forall (l : list nat) (x : nat) s, ~ In x l -> index_of (l ++ [x]) x s = Some (s + length l)%nat.
Proof.
clearP. induction l as [|y t IH]; intros x s Hx; cbn [index_of app length].
- rewrite Nat.eqb_refl, Nat.add_0_r. img_refl.
- destruct (Nat.eqb_spec y x) as [E|E]; [img_try (exfalso; img_apply Hx; left; img_exact E)|]. rewrite (IH x (Datatypes.S s) ltac:(img_try (intros H; img_apply Hx; right; img_exact H))). f_equal. zlia.
Qed.
Lemma index_ofZ_app_new : forall (l : list nat) (x : nat), ~ In x l -> index_ofZ (l ++ [x]) x = Z.of_nat (length l).
Proof. clearP. intros l x Hx. unfold index_ofZ. rewrite (index_of_app_new l x 0 Hx). cbn [Nat.add]. img_refl. Qed.
Record fin_facts (grow : bool) (z : Z) (Wz : world tfxsegs) (regs' : bvmap 5 word) (mem' memD : word -> option byte) : Prop := mkFin {
f_AOK : aok S (KDepot tr) z;
f_DEPD : depot_mem_ok B ly (depot_after z tr S) (aview tfxsegs (w_H Wz) memD);
f_CSTD : Forall (cell_holds B ly (aview tfxsegs (w_H Wz) memD)) (as_const B ly);
f_PRD : forall a, DZONE a -> apresent (w_H Wz) mem0 a -> apresent (w_H Wz) memD a;
f_EQD : forall x : word, DZONE (bv_unsigned x) -> mem' x = memD x;
f_MEQF : forall x : word, ~ WIN (bv_unsigned x) -> ~ (grow = true /\ QR (bv_unsigned x)) -> ~ DX (bv_unsigned x) -> mem' x = mem0 x;
f_PRS : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H Wz) mem' a;
f_PRmap : forall a, mb <= a < mb + MSv -> apresent (w_H Wz) mem' a;
f_PRsh : forall a, SMv <= a < SMv + MSv / 8 -> apresent (w_H Wz) mem' a;
f_PRq : grow = true -> forall a, QR a -> apresent (w_H Wz) mem' a;
f_PRW : forall a, WINT a \/ (QSv <= a < QSv + 8) -> apresent (w_H Wz) mem' a;
f_VISW : forall a, WINI a -> aview tfxsegs (w_H Wz) mem' a <> None;
f_R10 : getr regs' 10 = w64 Uv;
f_RCS : MIDST_top regs0 (Z.of_nat (length tr)) (w_H Wz) regs' mem';
f_Vsh : forall x : word, (SMv <= bv_unsigned x < SMv + 768 \/ SHBv + UEv / 8 <= bv_unsigned x < SMv + MSv / 8) -> mem' x = Some (Z_to_bv 8 250);
f_Vzs : forall x : word, SMv + 768 <= bv_unsigned x < SMv + 768 + N8D / 8 -> mem' x = Some (Z_to_bv 8 0);
f_Vpb : n mod 8 <> 0 -> val_mem tfxsegs (mrestrict (w_H Wz) mem') PBv 1 (n mod 8);
f_Vunw : val_mem tfxsegs (mrestrict (w_H Wz) mem') (T + t_unwinding) 1 0;
f_Vres : val_mem tfxsegs (mrestrict (w_H Wz) mem') (TFX_INST + o_sec_reserved) 8 (if grow then res + kPtrArrayEntriesPerCommit else res);
f_Vnch : val_mem tfxsegs (mrestrict (w_H Wz) mem') (TFX_INST + o_sec_n) 8 (idx + 1);
f_Vmtx : val_mem tfxsegs (mrestrict (w_H Wz) mem') (TFX_INST + o_sec_mutex) 1 0;
f_Vpad : forall k, 1 <= k < 4 -> aview tfxsegs (w_H Wz) mem' (TFX_INST + o_sec_mutex + k) = Some 0;
f_Vslot : val_mem tfxsegs (mrestrict (w_H Wz) mem') QSv 8 mb;
f_Vh0 : val_mem tfxsegs (mrestrict (w_H Wz) mem') mb 8 mb;
f_Vh8 : val_mem tfxsegs (mrestrict (w_H Wz) mem') (mb + 8) 8 MSv;
f_Vh16 : val_mem tfxsegs (mrestrict (w_H Wz) mem') (mb + 16) 8 NDv;
f_Vh24 : val_mem tfxsegs (mrestrict (w_H Wz) mem') (mb + 24) 8 idx;
f_Vmag : val_mem tfxsegs (mrestrict (w_H Wz) mem') Kv 8 0xCC6E96B9CC6E96B9;
f_Vbk : val_mem tfxsegs (mrestrict (w_H Wz) mem') (Kv + 8) 8 (Uv - 16);
f_Vst : val_mem tfxsegs (mrestrict (w_H Wz) mem') (Uv - 16) 1 2;
f_Vb1 : val_mem tfxsegs (mrestrict (w_H Wz) mem') (Uv - 15) 1 17;
f_Vb2 : val_mem tfxsegs (mrestrict (w_H Wz) mem') (Uv - 14) 2 0;
f_Vn : val_mem tfxsegs (mrestrict (w_H Wz) mem') (Uv - 12) 4 n;
f_Vfill : forall x : word, Uv <= bv_unsigned x < Uv + 4096 -> mem' x = Some (Z_to_bv 8 190);
f_PBUF : PBUFW Wz mem' }.
Record wz_facts (grow : bool) (z : Z) (Wz : world tfxsegs) (mdf : Model) : Prop := mkWz {
w_MONf : forall x : word, w_H W x = false -> w_H Wz x = false;
w_VISmap : forall x : word, mb <= bv_unsigned x < mb + MSv -> w_H Wz x = false;
w_VISsh : forall x : word, SHLO mb <= bv_unsigned x < SHHI mb -> w_H Wz x = false;
w_VISq : grow = true -> forall x : word, QR (bv_unsigned x) -> w_H Wz x = false;
w_ABf : A_bytes (w_A Wz) = A_bytes (w_A W) + MSv + (SHHI mb - SHLO mb) + (if grow then 131072 else 0);
w_HINC : forall i, In i (w_A W) -> In i (w_A Wz);
w_AMAP : In (mb, mb + MSv) (w_A Wz);
w_AHULL : In (SHLO mb, SHHI mb) (w_A Wz);
w_LEDf : ALedger tfxsegs lyF (SFS grow z) mdf;
w_MWf : amwf mdf;
w_GAPART : Forall (zdisjoint (mb, MSv)) (static_extents ly ++ vis0_zones ly ++ sec_extents ly S) }.
Section d0.
Variables (grow : bool) (z : Z) (Wz : world tfxsegs) (mdf : Model) (regs' : bvmap 5 word) (mem' memD : word -> option byte).
Let rd' : reader := aview tfxsegs (w_H Wz) mem'.
Let rdD : reader := aview tfxsegs (w_H Wz) memD.
Let m' := mrestrict (w_H Wz) mem'.
Let SF : astate := SFS grow z.
Hypothesis HAR : AR tfxsegs B ly S W mem0 md0.
Hypothesis Hgrow : grow = true <-> idx = res.
Hypothesis MP : Wf (as_universe B) SF /\ qtight SF.
Hypothesis Htr : In tr (as_universe B).
Hypothesis HFIN : fin_facts grow z Wz regs' mem' memD.
Hypothesis HWZ : wz_facts grow z Wz mdf.
Let JUNK : forall ly1 ly2, as_junk B ly1 = as_junk B ly2 := fun ly1 ly2 => ts_junk_ly B TS ly2 ly1.
Let MONf := w_MONf _ _ _ _ HWZ. Let VISmap := w_VISmap _ _ _ _ HWZ. Let VISsh := w_VISsh _ _ _ _ HWZ. Let VISq := w_VISq _ _ _ _ HWZ.
Let ABf := w_ABf _ _ _ _ HWZ. Let HINC := w_HINC _ _ _ _ HWZ. Let AMAP := w_AMAP _ _ _ _ HWZ. Let AHULL := w_AHULL _ _ _ _ HWZ. Let LEDf := w_LEDf _ _ _ _ HWZ.
Let MWf := w_MWf _ _ _ _ HWZ. Let GAPART := w_GAPART _ _ _ _ HWZ.
Let AOK := f_AOK _ _ _ _ _ _ HFIN. Let DEPD : depot_mem_ok B ly (depot_after z tr S) rdD := f_DEPD _ _ _ _ _ _ HFIN.
Let CSTD : Forall (cell_holds B ly rdD) (as_const B ly) := f_CSTD _ _ _ _ _ _ HFIN.
Let PRD := f_PRD _ _ _ _ _ _ HFIN. Let EQD := f_EQD _ _ _ _ _ _ HFIN. Let MEQF := f_MEQF _ _ _ _ _ _ HFIN.
Let PRS := f_PRS _ _ _ _ _ _ HFIN. Let PRmap := f_PRmap _ _ _ _ _ _ HFIN. Let PRsh := f_PRsh _ _ _ _ _ _ HFIN. Let PRq := f_PRq _ _ _ _ _ _ HFIN. Let PRW := f_PRW _ _ _ _ _ _ HFIN.
Let VISW : forall a, WINI a -> rd' a <> None := f_VISW _ _ _ _ _ _ HFIN.
Let R10 := f_R10 _ _ _ _ _ _ HFIN. Let RCS := f_RCS _ _ _ _ _ _ HFIN.
Let Vsh := f_Vsh _ _ _ _ _ _ HFIN. Let Vzs := f_Vzs _ _ _ _ _ _ HFIN. Let Vpb : n mod 8 <> 0 -> val_mem tfxsegs m' PBv 1 (n mod 8) := f_Vpb _ _ _ _ _ _ HFIN.
Let Vunw : val_mem tfxsegs m' (T + t_unwinding) 1 0 := f_Vunw _ _ _ _ _ _ HFIN.
Let Vres : val_mem tfxsegs m' (TFX_INST + o_sec_reserved) 8 (if grow then res + kPtrArrayEntriesPerCommit else res) := f_Vres _ _ _ _ _ _ HFIN.
Let Vnch : val_mem tfxsegs m' (TFX_INST + o_sec_n) 8 (idx + 1) := f_Vnch _ _ _ _ _ _ HFIN.
Let Vmtx : val_mem tfxsegs m' (TFX_INST + o_sec_mutex) 1 0 := f_Vmtx _ _ _ _ _ _ HFIN.
Let Vpad : forall k, 1 <= k < 4 -> rd' (TFX_INST + o_sec_mutex + k) = Some 0 := f_Vpad _ _ _ _ _ _ HFIN.
Let Vslot : val_mem tfxsegs m' QSv 8 mb := f_Vslot _ _ _ _ _ _ HFIN.
Let Vh0 : val_mem tfxsegs m' mb 8 mb := f_Vh0 _ _ _ _ _ _ HFIN.
Let Vh8 : val_mem tfxsegs m' (mb + 8) 8 MSv := f_Vh8 _ _ _ _ _ _ HFIN.
Let Vh16 : val_mem tfxsegs m' (mb + 16) 8 NDv := f_Vh16 _ _ _ _ _ _ HFIN.
Let Vh24 : val_mem tfxsegs m' (mb + 24) 8 idx := f_Vh24 _ _ _ _ _ _ HFIN.
Let Vmag : val_mem tfxsegs m' Kv 8 0xCC6E96B9CC6E96B9 := f_Vmag _ _ _ _ _ _ HFIN.
Let Vbk : val_mem tfxsegs m' (Kv + 8) 8 (Uv - 16) := f_Vbk _ _ _ _ _ _ HFIN.
Let Vst : val_mem tfxsegs m' (Uv - 16) 1 2 := f_Vst _ _ _ _ _ _ HFIN.
Let Vb1 : val_mem tfxsegs m' (Uv - 15) 1 17 := f_Vb1 _ _ _ _ _ _ HFIN.
Let Vb2 : val_mem tfxsegs m' (Uv - 14) 2 0 := f_Vb2 _ _ _ _ _ _ HFIN.
Let Vn : val_mem tfxsegs m' (Uv - 12) 4 n := f_Vn _ _ _ _ _ _ HFIN.
Let Vfill := f_Vfill _ _ _ _ _ _ HFIN.
Let MA : ARm B ly S rd0 := proj1 HAR.
Definition XC (a : Z) : Prop :=
WINT a \/ WINI a \/ (QSv <= a < QSv + 8) \/ (mb <= a < mb + MSv) \/ (SMv <= a < SMv + MSv / 8) \/ DZONE a \/ (grow = true /\ QR a).
Lemma zr_dec : forall lo hi a : Z, (lo <= a < hi) \/ ~ (lo <= a < hi).
Proof. clear. intros lo hi a. zlia. Qed.
Lemma or_dec : forall A B : Prop, (A \/ ~ A) -> (B \/ ~ B) -> (A \/ B) \/ ~ (A \/ B).
Proof. clear. intros A B HA HB. tauto. Qed.
Lemma XC_dec : forall a, XC a \/ ~ XC a.
Proof.
clearP. intros a. unfold XC, WINT, WINI, DZONE, QR.
repeat (img_apply or_dec; [img_try (img_apply zr_dec)|]); repeat img_apply or_dec; try img_apply zr_dec.
destruct grow; [| img_try (right; intros [E _]; discriminate E)].
destruct (zr_dec (Qb + 8 * res) (Qb + 8 * res + 8 * kPtrArrayEntriesPerCommit) a) as [H1|H1]; [| img_try (right; intros [_ [H _]]; img_exact (H1 H))].
destruct (Z_lt_le_dec a (Qb + kPtrArrayResv)) as [H2|H2]; [img_try (left; split; [img_refl | split; [img_exact H1 | img_exact H2]]) | img_try (right; intros [_ [_ H]]; zlia)].
Qed.
Lemma AGREE0 : forall a, 0 <= a < 2 ^ 64 -> ~ XC a -> ~ (sp0 - ASTACK <= a < sp0) -> forall v, rd0 a = Some v -> rd' a = Some v.
Proof.
intros a Ra NX NS v Hv. unfold rd0, rd', aview, mbyte, mrestrict in *.
assert (Hm : mem' (Z_to_bv 64 a) = mem0 (Z_to_bv 64 a)).
{ img_apply MEQF; rewrite unsigned_lit_small by img_exact Ra.
- intros Hw. unfold WIN, WINM in Hw. destruct Hw as [Hw|[Hw|[Hw|Hw]]]; [img_try (img_exact (NS Hw)) | img_try (img_apply NX; left; img_exact Hw) | img_try (img_apply NX; right; left; img_exact Hw) |].
destruct Hw as [Hw|[Hw|Hw]]; img_apply NX; unfold XC; [img_try (right; right; left; img_exact Hw) | img_try (do 3 right; left; img_exact Hw) | img_try (do 4 right; left; img_exact Hw)].
- intros [Hg Hq]. img_apply NX. do 6 right. img_exact (conj Hg Hq).
- intros [Hs|Hd]; [img_try (img_apply NS; clear - Hs; unfold DEP_STK, ASTACK in *; zlia) | img_try (img_apply NX; do 5 right; left; img_exact Hd)]. }
rewrite Hm. destruct (w_H W (Z_to_bv 64 a)) eqn:Eh; [img_try (unfold seg_rom in Hv; rewrite (memory_read1_hidden tfxsegs (w_H W) (w_Hoff W) _ Eh) in Hv; discriminate Hv)|].
rewrite (MONf _ Eh). img_exact Hv.
Qed.
Lemma AGREED : forall a, 0 <= a < 2 ^ 64 -> DZONE a -> rd' a = rdD a.
Proof. clearP. intros a Ra Hd. unfold rd', rdD. img_apply aview_same. img_apply EQD. rewrite unsigned_lit_small by img_exact Ra. img_exact Hd. Qed.
Lemma AGX : forall a, aowned B ly S a -> ~ XC a -> forall v, rd0 a = Some v -> rd' a = Some v.
Proof.
intros a Ho Hx. pose proof (AR_owned_low_law_ok tfxsegs B ly S W mem0 md0 a HAR Ho) as Ra. ceil.
pose proof (AR_stack_law_ok tfxsegs B ly S W mem0 md0 a HAR) as NS. destruct Hsp as (S1 & S2 & S3 & S4).
img_apply AGREE0; [img_try (clear - Ra; zlia) | img_try (img_exact Hx) |]. intros Hs. img_apply NS; [|img_try (img_exact Ho)]. clear - Hs S1 S3. unfold sp0 in *. zlia.
Qed.

Lemma XC_where : forall a, XC a ->
(T <= a < T + kThreadObjSize /\ WINT a) \/ (0x10000 <= a < (0x5ff000 + D_1000) /\ (WINI a \/ (0x17c088 + D_10c0) <= a < (0x5cc810 + D_10c0))) \/ (Qb <= a < Qb + kPtrArrayResv) \/
(mb <= a < mb + MSv) \/ ((2148236800 + D_200) <= a < kHighShadowEnd /\ SMv <= a < SMv + MSv / 8) \/
(ly_NB ly <= a < ly_NB ly + kNodesBlockSize) \/ (ly_SB ly <= a < ly_SB ly + kStoreBlockSize).
Proof.
intros a Hx. pose proof map_facts as (M1 & M2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _). pose proof map_zoneN as MZ. pose proof Hidx as HI. pose proof Hres as [HRS _].
pose proof BSLv_range as HB. pose proof high_facts as (_ & _ & _ & _ & _ & _ & _ & _ & F9 & _).
unfold XC in Hx. destruct Hx as [Hw|[Hw|[Hw|[Hw|[Hw|[Hw|[_ Hw]]]]]]].
- left. split; [|img_try (img_exact Hw)]. unfold WINT, t_unwinding, kThreadObjSize in *. clear - Hw MZ. zlia.
- right; left. split; [|img_try (left; img_exact Hw)]. unfold WINI in Hw. clear - Hw HB MZ. unfold TFX_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex in *. zlia.
- do 2 right; left. unfold QSv in Hw. clear - Hw HI HRS MZ. unfold kPtrArrayResv, kMaxNumChunks in *. try unfold Qb in *. zlia.
- do 3 right; left. img_exact Hw.
- do 4 right; left. split; [| img_try (img_exact Hw)]. pose proof (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 map_facts))))))))))))))) as SMA.
rewrite SMA in Hw, SM2. unfold shadow_addr, SHADOW_OFF in *. clear - Hw M1 SM2 MZ. unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END in M1. assert (DD : (785920 + D_200) <= mb / 8) by (img_try (img_apply Z.div_le_lower_bound; zlia)). zlia.
- unfold DZONE in Hw. destruct Hw as [Hw|[Hw|Hw]]; [img_try (right; left; split; [clear - Hw MZ; zlia | right; img_exact Hw]) | img_try (do 5 right; left; img_exact Hw) | img_try (do 6 right; img_exact Hw)].
- do 2 right; left. unfold QR in Hw. clear - Hw HI HRS F9 MZ. unfold kPtrArrayEntriesPerCommit, kPtrArrayResv, kMaxNumChunks in *. try unfold Qb in *. zlia.
Qed.
Lemma Z_prim : forall a, ly_prim ly <= a < ly_prim ly + kPrimResvSize -> ~ XC a.
Proof.
intros a Ha Hx. apply XC_where in Hx. pose proof high_facts as (F1 & F2 & F3 & F4 & F5 & F6 & _).
pose proof blocks_facts as (NBhi & SBhi & _). destruct Hmap_apart as (_ & _ & MP3 & _). pose proof HCX as (CP & CT & QT & CQ).
pose proof (pairwise_ij _ _ 0 0 _ _ (lo_disj ly LY) eq_refl eq_refl) as PQ. pose proof (pairwise_ij _ _ 0 1 _ _ (lo_disj ly LY) eq_refl eq_refl) as PT.
pose proof (pairwise_ij _ _ 0 3 _ _ (lo_disj ly LY) eq_refl eq_refl) as PNB. pose proof (pairwise_ij _ _ 0 4 _ _ (lo_disj ly LY) eq_refl eq_refl) as PSB.
unfold zdisjoint in MP3, PQ, PT, PNB, PSB. cbn [fst snd] in MP3, PQ, PT, PNB, PSB.
clear - Ha Hx F3 F6 MP3 PQ PT PNB PSB. numconst. unfold kPtrArrayResv, kHighShadowBeg, kHighShadowEnd in *. try unfold T in *. try unfold Qb in *.
unfold WINT, WINI, DZONE in *. decompose [and or] Hx; clear Hx; zlia.
Qed.
Lemma Z_ext : forall (i : nat) e a, nth_error (owned_extents ly) i = Some e -> (i = 3 \/ i = 6 \/ i = 7)%nat -> fst e <= a < fst e + snd e -> ~ XC a.
Proof.
intros i e a He Hi Ha Hx. apply XC_where in Hx. pose proof (lo_app ly LY) as HIG. pose proof (lo_disj ly LY) as HD.
pose proof (Forall_nth' _ _ i _ HIG He) as IH. cbv beta in IH.
assert (He2 : nth_error (static_extents ly) i = Some e) by (img_try (unfold static_extents; rewrite nth_error_app1 by (cbn; zlia); img_exact He)).
pose proof (pairwise_ij _ _ i (9 - i - 1) _ _ HD He2 ltac:(img_try (destruct Hi as [-> |[-> | ->]]; img_refl))) as D9.
assert (SZ : 0 <= snd e) by (img_try (destruct Hi as [-> |[-> | ->]]; injection He as <-; cbn; unfold kFakeStackSize; zlia)).
pose proof (zone3_intro ly (fst e) (snd e) IMG SZ IH ltac:(img_try (destruct e; img_exact D9))) as Z3.
pose proof (zone3_apart_img _ _ a Z3) as EI. pose proof (zone3_apart_hsh _ _ a Z3) as EH. unfold zone3 in Z3. destruct Z3 as (E4096 & ECEIL & _).
unfold zone3, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kHighMemBeg in EI, EH.
assert (D : forall j e', nth_error (owned_extents ly) j = Some e' -> (j = 1 \/ j = 2 \/ j = 4 \/ j = 5)%nat -> zdisjoint e e').
{ intros j e' He' Hj. unfold static_extents in HD.
assert (HD' : pairwise zdisjoint (owned_extents ly)) by (img_try (apply (pairwise_app_inv zdisjoint (owned_extents ly) [_; _]) in HD; tauto)).
destruct (Nat.lt_ge_cases i j) as [L|L].
- replace j with (i + Datatypes.S (j - i - 1))%nat in He' by zlia. img_exact (pairwise_ij _ _ _ _ _ _ HD' He He').
- img_apply zdisjoint_sym. assert (j <> i) by (img_try (intros ->; zlia)). replace i with (j + Datatypes.S (i - j - 1))%nat in He by zlia. img_exact (pairwise_ij _ _ _ _ _ _ HD' He' He). }
pose proof (D 1%nat _ eq_refl ltac:(img_try (zlia))) as D1. pose proof (D 2%nat _ eq_refl ltac:(img_try (zlia))) as D2.
pose proof (D 4%nat _ eq_refl ltac:(img_try (zlia))) as D4. pose proof (D 5%nat _ eq_refl ltac:(img_try (zlia))) as D5.
unfold zdisjoint in D1, D2, D4, D5. cbn [fst snd] in D1, D2, D4, D5.
assert (DM : zdisjoint (mb, MSv) e).
{ img_apply (proj1 (Forall_forall _ _) GAPART e). img_apply in_app_iff. left. unfold static_extents. img_apply in_app_iff. left. eapply nth_error_In. img_exact He. }
pose proof map_facts as (M1 & M2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _). pose proof map_zoneN as MZ. pose proof blocks_facts as (NBhi & SBhi & _).
unfold zdisjoint in DM. cbn [fst snd] in DM.
clear - EI EH E4096 ECEIL Ha Hx D1 D2 D4 D5 DM M1 SM2 MZ. numconst. unfold kHighShadowBeg, kHighShadowEnd, kPtrArrayResv, WINT, WINI, DZONE in *. try unfold T in *. try unfold Qb in *.
decompose [and or] Hx; clear Hx; zlia.
Qed.
Lemma Z_sec : forall e a, In e (sec_extents ly S) -> fst e <= a < fst e + snd e -> ~ XC a.
Proof.
intros e a He Ha Hx. apply XC_where in Hx. pose proof (am_placed _ _ _ _ MA) as [PL PD]. pose proof (proj1 (Forall_forall _ _) PL e He) as (_ & HIA & _).
assert (D : forall e', In e' (owned_extents ly) -> zdisjoint e e').
{ intros e' He'. img_exact (pairwise_In zdisjoint _ e e' (sec_extents ly S) (static_extents ly) eq_refl PD He ltac:(img_try (unfold static_extents; img_apply in_app_iff; left; img_exact He'))). }
pose proof (D (ly_Q ly, kPtrArrayResv) ltac:(img_try (unfold owned_extents; cbn; tauto))) as DQ.
pose proof (D (ly_T ly, kThreadObjSize) ltac:(img_try (unfold owned_extents; cbn; tauto))) as DT.
pose proof (D (ly_NB ly, kNodesBlockSize) ltac:(img_try (unfold owned_extents; cbn; tauto))) as DNB.
pose proof (D (ly_SB ly, kStoreBlockSize) ltac:(img_try (unfold owned_extents; cbn; tauto))) as DSB.
assert (DM : zdisjoint (mb, MSv) e).
{ img_apply (proj1 (Forall_forall _ _) GAPART e). img_apply in_app_iff. right. img_apply in_app_iff. right. img_exact He. }
pose proof (pairwise_In zdisjoint _ e (ly_img ly) (sec_extents ly S) (static_extents ly) eq_refl PD He ltac:(img_try (unfold static_extents; img_apply in_app_iff; right; cbn; tauto))) as D9.
assert (SZ : 0 <= snd e) by (img_try (clear - Ha; zlia)).
pose proof (zone3_intro ly (fst e) (snd e) IMG SZ HIA ltac:(img_try (destruct e; img_exact D9))) as Z3.
pose proof (zone3_apart_img _ _ a Z3) as EI. pose proof (zone3_apart_hsh _ _ a Z3) as EH. unfold zone3 in Z3. destruct Z3 as (E4096 & ECEIL & _).
unfold zone3, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kHighMemBeg in EI, EH.
pose proof map_facts as (M1 & M2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _). pose proof map_zoneN as MZ. pose proof blocks_facts as (NBhi & SBhi & _).
unfold zdisjoint in DQ, DT, DNB, DSB, DM. cbn [fst snd] in DQ, DT, DNB, DSB, DM.
clear - EI EH E4096 ECEIL Ha Hx DQ DT DNB DSB DM M1 SM2 MZ. numconst. unfold kHighShadowBeg, kHighShadowEnd, kPtrArrayResv, WINT, WINI, DZONE in *. try unfold T in *. try unfold Qb in *.
decompose [and or] Hx; clear Hx; zlia.
Qed.
Lemma Z_T : forall a, T <= a < T + kThreadObjSize -> ~ WINT a -> ~ XC a.
Proof.
intros a Ha Hw Hx. apply XC_where in Hx. pose proof high_facts as (F1 & F2 & _). pose proof HCX as (_ & _ & QT & _). destruct Hmap_apart as (MT & _).
pose proof blocks_facts as (NBhi & SBhi & TNB & TSB & _). pose proof map_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _). pose proof map_zoneN as MZ.
unfold zdisjoint in QT, MT, TNB, TSB. cbn [fst snd] in QT, MT, TNB, TSB.
pose proof (zone3_apart_img _ _ a F1) as TI. pose proof (zone3_apart_hsh _ _ a F1) as TH. unfold zone3, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kHighMemBeg, kThreadObjSize in TI, TH.
clear - Ha Hw Hx TI TH QT MT TNB TSB SM2 MZ. numconst. unfold kHighShadowBeg, kHighShadowEnd, kPtrArrayResv in *. try unfold T in *. try unfold Qb in *.
decompose [and or] Hx; clear Hx; first [zlia | img_exact (Hw ltac:(img_try (assumption)))].
Qed.
Lemma Z_img : forall a, 0x10000 <= a < (0x5ff000 + D_1000) -> ~ WINI a -> ~ ((0x17c088 + D_10c0) <= a < (0x5cc810 + D_10c0)) -> ~ XC a.
Proof.
intros a Ha Hw Hd Hx. apply XC_where in Hx. pose proof high_facts as (F1 & _ & _ & _ & _ & _ & _ & _ & F9 & _).
pose proof blocks_facts as (NBhi & SBhi & _). pose proof map_facts as (M1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & _). pose proof map_zoneN as MZ.
pose proof (zone3_apart_img _ _ a F1) as TI. pose proof (zone3_apart_hsh _ _ a F1) as TH. pose proof (zone3_apart_img _ _ a F9) as QI. pose proof (zone3_apart_hsh _ _ a F9) as QH. pose proof (zone3_apart_img _ _ a NBhi) as NI. pose proof (zone3_apart_hsh _ _ a NBhi) as NH. pose proof (zone3_apart_img _ _ a SBhi) as BI. pose proof (zone3_apart_hsh _ _ a SBhi) as BH. pose proof (zone3_apart_img _ _ a (mzone_zone3 _ _ (proj2 Hmap))) as MI. pose proof (zone3_apart_hsh _ _ a (mzone_zone3 _ _ (proj2 Hmap))) as MH. unfold zone3, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kHighMemBeg, kThreadObjSize, kPtrArrayResv, kNodesBlockSize, kStoreBlockSize in TI, TH, QI, QH, NI, NH, BI, BH, MI, MH.
clear - Ha Hw Hd Hx TI QI NI BI MI SM1 MZ. numconst. unfold kHighShadowBeg in *. try unfold T in *. try unfold Qb in *.
decompose [and or] Hx; clear Hx; first [zlia | img_exact (Hw ltac:(img_try (assumption))) | img_exact (Hd ltac:(img_try (assumption)))].
Qed.
Lemma Z_Q : forall a, Qb <= a < Qb + kPtrArrayResv -> ~ (QSv <= a < QSv + 8) -> ~ (grow = true /\ QR a) -> ~ XC a.
Proof.
intros a Ha Hs Hq Hx. pose proof Hx as Hx0. apply XC_where in Hx. pose proof high_facts as (_ & _ & _ & _ & _ & _ & _ & _ & F9 & F10 & _).
pose proof HCX as (_ & _ & QT & _). destruct Hmap_apart as (_ & _ & _ & MQ & _).
pose proof blocks_facts as (NBhi & SBhi & _ & _ & QNB & QSB & _). pose proof map_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _). pose proof map_zoneN as MZ.
unfold zdisjoint in QT, MQ, QNB, QSB. cbn [fst snd] in QT, MQ, QNB, QSB.
pose proof BSLv_range as HB.
unfold XC in Hx0. destruct Hx0 as [Hw|[Hw|[Hw|[Hw|[Hw|[Hw|Hw]]]]]]; [| | img_try (img_exact (Hs Hw)) | | | | img_try (img_exact (Hq Hw))];
pose proof (zone3_apart_img _ _ a F9) as QI; pose proof (zone3_apart_hsh _ _ a F9) as QH; unfold zone3, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kHighMemBeg, kPtrArrayResv in QI, QH;
clear - Ha Hw QI QH F10 QT MQ QNB QSB SM2 HB MZ; unfold WINT, WINI, DZONE in *;
numconst; unfold kHighShadowBeg, kHighShadowEnd, kPtrArrayResv, t_unwinding, TFX_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex in *; try unfold T in *; try unfold Qb in *; zlia.
Qed.
Lemma Z_band : forall a, in_band_rw a -> ~ (SMv <= a < SMv + MSv / 8) -> ~ XC a.
Proof.
intros a Ha Hs Hx. apply XC_where in Hx. pose proof high_facts as (F1 & _ & _ & _ & _ & _ & _ & _ & F9 & _).
pose proof blocks_facts as (NBhi & SBhi & _). pose proof map_facts as (M1 & _). pose proof map_zoneN as MZ.
pose proof (zone3_apart_img _ _ a F1) as TI. pose proof (zone3_apart_hsh _ _ a F1) as TH. pose proof (zone3_apart_img _ _ a F9) as QI. pose proof (zone3_apart_hsh _ _ a F9) as QH. pose proof (zone3_apart_img _ _ a NBhi) as NI. pose proof (zone3_apart_hsh _ _ a NBhi) as NH. pose proof (zone3_apart_img _ _ a SBhi) as BI. pose proof (zone3_apart_hsh _ _ a SBhi) as BH. pose proof (zone3_apart_img _ _ a (mzone_zone3 _ _ (proj2 Hmap))) as MI. pose proof (zone3_apart_hsh _ _ a (mzone_zone3 _ _ (proj2 Hmap))) as MH. unfold zone3, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kHighMemBeg, kThreadObjSize, kPtrArrayResv, kNodesBlockSize, kStoreBlockSize in TI, TH, QI, QH, NI, NH, BI, BH, MI, MH.
unfold in_band_rw in Ha. clear - Ha Hs Hx TH QH NH BH MH MZ. numconst. unfold kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *. try unfold T in *. try unfold Qb in *.
decompose [and or] Hx; clear Hx; first [zlia | img_exact (Hs ltac:(img_try (split; assumption)))].
Qed.
Lemma apresent_word : forall (Hh : word -> bool) mem a, apresent Hh mem a <-> apresent Hh mem (bv_unsigned (Z_to_bv 64 a)).
Proof. clearP. intros Hh mem a. unfold apresent. rewrite Z_to_bv_bv_unsigned. split; intros H; img_exact H. Qed.
Lemma WINI_dec : forall a, WINI a \/ ~ WINI a.
Proof. clearP. intros a. unfold WINI. repeat (img_apply or_dec; [img_try (img_apply zr_dec)|]); img_apply zr_dec. Qed.
Lemma PRES_MONO : forall u, 0 <= u < 2 ^ 64 -> ~ WINI u -> apresent (w_H W) mem0 u -> apresent (w_H Wz) mem' u.
Proof.
{ intros u Ru NWI Hp.
assert (HpW : apresent (w_H Wz) mem0 u) by (img_try (destruct Hp as [Hh Hb]; split; [img_try (img_exact (MONf _ Hh)) | img_try (img_exact Hb)])).
destruct (zr_dec (0x17c088 + D_10c0) (0x5cc810 + D_10c0) u) as [D1|D1].
{ eapply apresent_same; [img_try (img_apply EQD) | img_try (img_apply PRD; [|img_exact HpW])]; [img_try (rewrite unsigned_lit_small by img_exact Ru)|]; unfold DZONE; left; img_exact D1. }
destruct (zr_dec (ly_NB ly) (ly_NB ly + kNodesBlockSize) u) as [D2|D2].
{ eapply apresent_same; [img_try (img_apply EQD) | img_try (img_apply PRD; [|img_exact HpW])]; [img_try (rewrite unsigned_lit_small by img_exact Ru)|]; unfold DZONE; right; left; img_exact D2. }
destruct (zr_dec (ly_SB ly) (ly_SB ly + kStoreBlockSize) u) as [D3|D3].
{ eapply apresent_same; [img_try (img_apply EQD) | img_try (img_apply PRD; [|img_exact HpW])]; [img_try (rewrite unsigned_lit_small by img_exact Ru)|]; unfold DZONE; right; right; img_exact D3. }
destruct (zr_dec (sp0 - ASTACK) sp0 u) as [D4|D4]; [img_try (img_apply PRS; img_exact D4)|].
destruct (zr_dec mb (mb + MSv) u) as [D5|D5]; [img_try (img_apply PRmap; img_exact D5)|].
destruct (zr_dec SMv (SMv + MSv / 8) u) as [D6|D6]; [img_try (img_apply PRsh; img_exact D6)|].
destruct (zr_dec QSv (QSv + 8) u) as [D7|D7]; [img_try (img_apply PRW; right; img_exact D7)|].
assert (DW : WINT u \/ ~ WINT u) by (img_try (clear; unfold WINT; zlia)).
destruct DW as [D8|D8]; [img_try (img_apply PRW; left; img_exact D8)|].
assert (D8' : ~ (WINT u \/ WINI u)) by (img_try (clear - D8 NWI; tauto)). clear D8. rename D8' into D8.
destruct grow eqn:Eg.
- destruct (zr_dec (Qb + 8 * res) (Qb + 8 * res + 8 * kPtrArrayEntriesPerCommit) u) as [D9|D9].
+ destruct (Z_lt_le_dec u (Qb + kPtrArrayResv)) as [D10|D10]; [img_try (img_apply (PRq eq_refl); unfold QR; img_exact (conj D9 D10))|].
eapply apresent_same; [|img_try (img_exact HpW)]. img_apply MEQF; rewrite unsigned_lit_small by img_exact Ru.
* unfold WIN, WINM. clear - D4 D5 D6 D7 D8. tauto.
* intros [_ [_ Hq]]. clear - Hq D10. zlia.
* unfold DX, DZONE. clear - D1 D2 D3 D4. unfold DEP_STK, ASTACK in *. intros [Hs|Hd]; [img_try (zlia) | img_try (tauto)].
+ eapply apresent_same; [|img_try (img_exact HpW)]. img_apply MEQF; rewrite unsigned_lit_small by img_exact Ru.
* unfold WIN, WINM. clear - D4 D5 D6 D7 D8. tauto.
* intros [_ [Hq _]]. img_exact (D9 Hq).
* unfold DX, DZONE. clear - D1 D2 D3 D4. unfold DEP_STK, ASTACK in *. intros [Hs|Hd]; [img_try (zlia) | img_try (tauto)].
- eapply apresent_same; [|img_try (img_exact HpW)]. img_apply MEQF; rewrite unsigned_lit_small by img_exact Ru.
+ unfold WIN, WINM. clear - D4 D5 D6 D7 D8. tauto.
+ intros [E _]. discriminate E.
+ unfold DX, DZONE. clear - D1 D2 D3 D4. unfold DEP_STK, ASTACK in *. intros [Hs|Hd]; [img_try (zlia) | img_try (tauto)]. }
Qed.
Lemma VIS_MONO : forall a, rd0 a <> None -> rd' a <> None.
Proof.
intros a0 HV0.
set (a := bv_unsigned (Z_to_bv 64 a0)).
assert (Ra : 0 <= a < 2 ^ 64) by (img_try (pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 a0)) as R; img_change (bv_modulus 64) with (2 ^ 64) in R; img_exact R)).
assert (Ex : Z_to_bv 64 a = Z_to_bv 64 a0) by (img_try ((subst a; cbv beta); img_apply Z_to_bv_bv_unsigned)).
assert (AV : forall (Hh : word -> bool) m, aview tfxsegs Hh m a0 = aview tfxsegs Hh m a) by (img_try (intros Hh m; unfold aview, mbyte, mrestrict; rewrite Ex; img_refl)).
unfold rd0 in HV0. rewrite AV in HV0. unfold rd'. rewrite AV. clearbody a. clear Ex AV a0. rename HV0 into HV.
destruct (WINI_dec a) as [HWI|NWI]; [img_try (img_exact (VISW a HWI))|].
unfold rd', rd0, aview, mbyte in *.
destruct (seg_rom tfxsegs (Z_to_bv 64 a)) as [r|] eqn:ER.
- destruct (mrestrict (w_H Wz) mem' (Z_to_bv 64 a)); cbn; discriminate.
- assert (Hp : apresent (w_H W) mem0 a).
{ unfold mrestrict in HV. unfold apresent. destruct (w_H W (Z_to_bv 64 a)); [img_try (exfalso; img_apply HV; img_refl)|].
split; [img_refl|]. destruct (mem0 (Z_to_bv 64 a)) as [b|]; [img_try (exists b; img_refl) | img_try (exfalso; img_apply HV; img_refl)]. }
destruct (PRES_MONO a Ra NWI Hp) as [Hh [b Hb]]. unfold mrestrict. rewrite Hh, Hb. cbn. discriminate.
Qed.
Lemma apresent_vis : forall a, apresent (w_H Wz) mem' a -> rd' a <> None.
Proof. clearP. intros a [Hh [b Hb]]. unfold rd', aview, mbyte, mrestrict. rewrite Hh, Hb. cbn. discriminate. Qed.
Lemma ZKEEP : forall g, g mod 8 = 0 -> in_app g 8 -> (g + 8 <= mb \/ mb + MSv <= g) ->
mem' (w64 (shadow_addr g)) = mem0 (w64 (shadow_addr g)).
Proof.
intros g Hg Happ HM. pose proof (shadow_addr_band_rw g Happ) as SBg. unfold in_band_rw in SBg. pose proof map_facts as (M1 & M2 & M3 & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _ & _ & SMA). pose proof map_zoneN as MZ.
pose proof high_facts as (F1 & _ & _ & _ & _ & _ & _ & _ & F9 & _). pose proof blocks_facts as (NBhi & SBhi & _).
destruct Hsp as (S1 & _). pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7). pose proof Hidx as HI. pose proof Hres as [HRS _].
assert (NS : ~ (SMv <= shadow_addr g < SMv + MSv / 8)).
{ rewrite SMA. unfold shadow_addr, SHADOW_OFF. apply Z.mod_divide in Hg as [q Hq]; [|img_try (zlia)]. apply Z.mod_divide in M3 as [p Hp]; [|img_try (zlia)].
pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & _ & Z9 & _). apply Z.mod_divide in Z9 as [u Hu]; [|img_try (zlia)].
rewrite Hq, Hp, Hu in *. replace (q * 8 / 8) with q by (img_try (symmetry; img_apply Z.div_mul; zlia)).
replace (p * 4096) with ((p * 512) * 8) by zlia. rewrite Z.div_mul by zlia. replace (u * 4096) with ((u * 512) * 8) by zlia. rewrite Z.div_mul by zlia.
clear - HM MZ. zlia. }
unfold w64. img_apply MEQF; rewrite unsigned_lit_small by (img_try (clear - SBg MZ; unfold kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in SBg; zlia)).
- intros HW. unfold WIN, WINT, WINI, WINM in HW. pose proof BSLv_range as HB.
pose proof (zone3_apart_hsh _ _ (shadow_addr g) F1) as TH. pose proof (zone3_apart_hsh _ _ (shadow_addr g) F9) as QH. pose proof (zone3_apart_hsh _ _ (shadow_addr g) (mzone_zone3 _ _ (proj2 Hmap))) as MH.
clear - HW NS SBg TH QH MH M1 S1 T7 HB HI HRS MZ. unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, ASTACK, t_unwinding, TFX_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex in *.
unfold QSv in *. try unfold sp0 in *. try unfold T in *. try unfold Qb in *. zlia.
- intros [_ Hq]. unfold QR in Hq. pose proof (zone3_apart_hsh _ _ (shadow_addr g) F9) as QH. clear - Hq SBg QH HI HRS MZ. unfold zone3, TFX_IMG_LO, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, kPtrArrayResv in *. try unfold Qb in *. zlia.
- intros [Hs|Hd]; [img_try (clear - Hs SBg S1 T7 MZ; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, DEP_STK, ASTACK in *; try unfold sp0 in *; zlia)|].
unfold DZONE in Hd. pose proof (zone3_apart_hsh _ _ (shadow_addr g) NBhi) as NH. pose proof (zone3_apart_hsh _ _ (shadow_addr g) SBhi) as BH.
clear - Hd SBg NH BH MZ. unfold zone3, TFX_IMG_LO, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, kNodesBlockSize, kStoreBlockSize in *. zlia.
Qed.
Lemma BANDKEEP : forall a, in_band_rw a -> mem0 (w64 a) <> None -> mem' (w64 a) <> None.
Proof.
intros a Ha Hm0. assert (Ra : 0 <= a < 2 ^ 64) by (img_try (clear - Ha; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha; zlia)).
destruct (zr_dec SMv (SMv + MSv / 8) a) as [D|D].
{ destruct (PRsh a D) as [_ [b Hb]]. unfold w64. rewrite Hb. discriminate. }
pose proof high_facts as (F1 & _ & _ & _ & _ & _ & _ & _ & F9 & _). pose proof blocks_facts as (NBhi & SBhi & _). pose proof map_facts as (M1 & _). pose proof map_zoneN as MZ.
destruct Hsp as (S1 & _). pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7). pose proof Hidx as HI. pose proof Hres as [HRS _]. pose proof BSLv_range as HB.
unfold w64. rewrite MEQF; [img_try (img_exact Hm0) | | |]; rewrite ?unsigned_lit_small by img_exact Ra.
- intros HW. unfold WIN, WINT, WINI, WINM in HW. unfold in_band_rw in Ha.
pose proof (zone3_apart_hsh _ _ a F1) as TH. pose proof (zone3_apart_hsh _ _ a F9) as QH. pose proof (zone3_apart_hsh _ _ a (mzone_zone3 _ _ (proj2 Hmap))) as MH.
clear - HW D Ha TH QH MH M1 S1 T7 HB HI HRS MZ.
unfold zone3, TFX_IMG_LO, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, ASTACK, t_unwinding, TFX_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex in *.
unfold QSv in *. try unfold sp0 in *. try unfold T in *. try unfold Qb in *. zlia.
- intros [_ Hq]. unfold QR in Hq. unfold in_band_rw in Ha. pose proof (zone3_apart_hsh _ _ a F9) as QH. clear - Hq Ha QH HI HRS MZ. unfold zone3, TFX_IMG_LO, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, kPtrArrayResv in *. try unfold Qb in *. zlia.
- unfold in_band_rw in Ha. intros [Hs|Hd]; [img_try (clear - Hs Ha S1 T7 MZ; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, DEP_STK, ASTACK in *; try unfold sp0 in *; zlia)|].
unfold DZONE in Hd. pose proof (zone3_apart_hsh _ _ a NBhi) as NH. pose proof (zone3_apart_hsh _ _ a SBhi) as BH.
clear - Hd Ha NH BH MZ. unfold zone3, TFX_IMG_LO, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, kNodesBlockSize, kStoreBlockSize in *. zlia.
Qed.
Lemma cell_holds_ext1 : forall (rd1 rd2 : reader) c,
(forall k v, 0 <= k < Z.max 1 (Z.of_nat (c_w c)) -> rd1 (aeval B ly (c_at c) + k) = Some v -> rd2 (aeval B ly (c_at c) + k) = Some v) ->
cell_holds B ly rd1 c -> cell_holds B ly rd2 c.
Proof.
clearP. intros rd1 rd2 c Hx Hc. unfold cell_holds in *. destruct (c_val c) as [e|m v].
- intros k Hk. img_apply Hx; [img_try (zlia) | img_try (img_exact (Hc k Hk))].
- destruct Hc as (b & Hb & Hm). exists b. split; [|img_try (img_exact Hm)]. rewrite <- (Z.add_0_r (aeval B ly (c_at c))). img_apply Hx; [img_try (zlia)|]. rewrite Z.add_0_r. img_exact Hb.
Qed.
Definition loc_ok (lo len : Z) : Prop := forall a, lo <= a < lo + len -> ~ XC a.
Lemma keep_cells : forall lst lo len, loc_ok lo len -> incl lst (acells B ly S) ->
Forall (fun c => lo <= aeval B ly (c_at c) /\ aeval B ly (c_at c) + Z.max 1 (Z.of_nat (c_w c)) <= lo + len) lst ->
Forall (cell_holds B ly rd') lst.
Proof.
intros lst lo len LOC INC RNG. img_apply Forall_forall. intros c Hc.
pose proof (proj1 (Forall_forall _ _) RNG c Hc) as [R1 R2]. cbv beta in R1, R2.
img_apply (cell_holds_ext1 rd0); [| img_try (img_exact (proj1 (Forall_forall _ _) (am_cells _ _ _ _ MA) c (INC c Hc)))].
intros k v Hk Hv. img_apply AGX; [| | img_try (img_exact Hv)].
- img_exact (proj1 (Forall_forall _ _) (acells_owned B ly S rd0 MA) c (INC c Hc) k Hk).
- img_apply LOC. zlia.
Qed.
Lemma keep_cell : forall c lo len, loc_ok lo len -> In c (acells B ly S) ->
lo <= aeval B ly (c_at c) -> aeval B ly (c_at c) + Z.max 1 (Z.of_nat (c_w c)) <= lo + len -> cell_holds B ly rd' c.
Proof.
intros c lo len LOC Hc R1 R2. img_exact (proj1 (Forall_forall _ _) (keep_cells [c] lo len LOC ltac:(img_try (intros x [<-|[]]; img_exact Hc)) ltac:(img_try (constructor; [img_try (split; assumption) | img_try (constructor)]))) c (or_introl eq_refl)).
Qed.
Lemma keep_cellX : forall c, In c (acells B ly S) -> (forall k, 0 <= k < Z.max 1 (Z.of_nat (c_w c)) -> ~ XC (aeval B ly (c_at c) + k)) -> cell_holds B ly rd' c.
Proof.
intros c Hc NX. img_apply (cell_holds_ext1 rd0); [| img_try (img_exact (proj1 (Forall_forall _ _) (am_cells _ _ _ _ MA) c Hc))].
intros k v Hk Hv. img_apply AGX; [img_try (img_exact (proj1 (Forall_forall _ _) (acells_owned B ly S rd0 MA) c Hc k Hk)) | img_try (img_exact (NX k Hk)) | img_try (img_exact Hv)].
Qed.
Lemma SF_parts :
(forall c, reg SF c = reg S c) /\ st_cache_inited SF = st_cache_inited S /\ (forall c, cache SF c = cache S c) /\
frames SF = frames S /\ st_qthread SF = st_qthread S /\ st_qglobal SF = st_qglobal S /\ st_fs SF = st_fs S /\
st_internal_inited SF = st_internal_inited S /\ st_sec_arr SF = st_sec_arr S ++ [rS S] /\
st_sec_reserved SF = (if grow then res + kPtrArrayEntriesPerCommit else res) /\ st_depot SF = st_depot (depot_after z tr S) /\
st_chunks SF = st_chunks S ++ [KSc] /\ st_secs SF = st_secs S ++ [mkSec MSv NDv true] /\ st_nev SF = st_nev S + 1 /\ st_regions SF = st_regions S.
Proof.
unfold SF, SFS, sfinal, resF, depF, KSc, reg, cache, frames. cbn. rewrite <- Hres_def.
repeat split; try img_refl. unfold depot_after. destruct (z =? 0); img_refl.
Qed.
Lemma rS_not_in_arr : ~ In (rS S) (st_sec_arr S).
Proof.
intros Hin. pose proof (proj1 (ws_arr_live _ (wf_secondary _ _ _ _ _ WF) (rS S)) Hin) as (sm & Hsm & _).
apply nth_error_lt in Hsm. unfold rS in Hsm. zlia.
Qed.
Lemma len_arr : Z.of_nat (length (st_sec_arr S)) = idx.
Proof. rewrite Hidx_def. img_refl. Qed.
Ltac fcons' := img_apply Forall_cons; [img_try (cbn; zlia)|].
Lemma val_mem_at : forall a a' (w : nat) x, a = a' -> val_mem tfxsegs m' a' w x -> val_mem tfxsegs m' a w x.
Proof. clearP. intros a a' w x -> H. img_exact H. Qed.
Lemma cells_regions : Forall (cell_holds B ly rd') (flat_map (region_cells SF) (zseq 1 31)).
Proof.
pose proof SF_parts as (Rreg & _). img_apply Forall_flat_map'. intros c Hc. apply zseq_In in Hc.
replace (region_cells SF c) with (region_cells S c) by (img_try (unfold region_cells; rewrite Rreg; img_refl)).
pose proof high_facts as (F1 & F2 & F3 & F4 & F5 & _).
img_apply (keep_cells _ (ly_space ly + kRegionInfoOff) 4096).
- intros a Ha. img_apply Z_prim; clear - Ha F3 F4 F5; unfold kRegionInfoOff in *; numconst; zlia.
- intros x Hx. unfold acells. img_apply in_app_iff. left. img_apply in_flat_map. exists c. split; [img_try (img_apply In_zseq; zlia) | img_try (img_exact Hx)].
- unfold region_cells, kRegionInfoOff. destruct (rg_mapped_user (reg S c) =? 0); repeat fcons'; img_apply Forall_nil.
Qed.
Lemma cells_caches : Forall (cell_holds B ly rd') (flat_map (cache_cells SF) (zseq 1 31)).
Proof.
pose proof SF_parts as (_ & Rinit & Rcache & _). img_apply Forall_flat_map'. intros c Hc. apply zseq_In in Hc.
replace (cache_cells SF c) with (cache_cells S c) by (img_try (unfold cache_cells; rewrite Rinit, (Rcache c); img_refl)).
img_apply (keep_cells _ (T + t_cache + 80 * c) 80).
- intros a Ha. img_apply Z_T; unfold WINT in *; unfold T in *; clear - Ha Hc; numconst; zlia.
- intros x Hx. unfold acells. img_apply in_app_iff. right. img_apply in_app_iff. left. img_apply in_flat_map. exists c. split; [img_try (img_apply In_zseq; zlia) | img_try (img_exact Hx)].
- unfold cache_cells. pose proof (wf_classes _ _ _ _ _ WF c ltac:(img_try (zlia))) as CL. pose proof (wr_cache _ _ _ _ _ _ CL) as WC.
pose proof (class_ok c ltac:(img_try (zlia))) as (_ & _ & _ & K4 & _). unfold T.
destruct (st_cache_inited S).
+ destruct WC as [PM PL]. unfold t_cache. repeat fcons'. img_apply Forall_forall. intros x Hx. apply in_map_iff in Hx as ([i vv] & <- & Hiv).
apply in_combine_l in Hiv. apply in_seq in Hiv. cbn. zlia.
+ unfold t_cache. repeat fcons'. img_apply Forall_nil.
Qed.
Lemma cells_chunks_old : Forall (cell_holds B ly rd') (flat_map chunk_cells (st_chunks S)).
Proof.
img_apply Forall_flat_map'. intros k Hk.
pose proof (chunk_facts B ly S rd0 k MA Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
pose proof (req_size_bounds (ck_req k) ltac:(img_try (zlia))) as (Q1 & Q2 & Q3).
img_apply (keep_cells _ (ck_base B ly k) (ck_rz k)).
- intros a Ha. destruct (extent_zone B ly S rd0 k MA Hk) as [[X1 X2]|(m & len & Hin & X1 & X2)].
+ img_apply Z_prim. clear - Ha X1 X2 G8 Q2. zlia.
+ img_apply (Z_sec (m, len)); [img_try (img_exact Hin) | img_try (cbn [fst snd]; clear - Ha X1 X2 G8 Q2; unfold kPage in *; zlia)].
- intros x Hx. unfold acells. do 2 (img_apply in_app_iff; right). img_apply in_app_iff; left. img_apply in_flat_map. exists k. split; [img_try (img_exact Hk) | img_try (img_exact Hx)].
- assert (EA : forall d, aeval B ly (aoff (sptr_exp (ck_beg k)) d) = ck_base B ly k + d).
{ intros d. unfold ck_base, sptr_addr. destruct (ck_beg k) as [|o|r o|c p]; try solve [destruct GG]; cbn; zlia. }
assert (EA2 : forall d d', aeval B ly (aoff (aoff (sptr_exp (ck_beg k)) d) d') = ck_base B ly k + d + d').
{ intros d d'. unfold ck_base, sptr_addr. destruct (ck_beg k) as [|o|r o|c p]; try solve [destruct GG]; cbn; zlia. }
assert (EA0 : aeval B ly (sptr_exp (ck_beg k)) = ck_base B ly k) by img_refl.
clear GG. unfold chunk_cells, kChunkHeaderSize. img_apply Forall_app. split.
+ repeat (img_apply Forall_cons; [img_try (cbn [c_at c_w z1 z2 z4 c1 c2 c4]; rewrite ?EA2, ?EA, ?EA0; cbn [Z.max Z.of_nat Pos.of_succ_nat Pos.succ]; zlia)|]). img_apply Forall_nil.
+ destruct (Z.eqb_spec (ck_rz k) 16); [img_try (img_apply Forall_nil)|].
assert (32 <= ck_rz k). { apply Z.mod_divide in G6 as [q Hq]; [|img_try (zlia)]. zlia. }
repeat (img_apply Forall_cons; [img_try (cbn [c_at c_w z8 c8]; rewrite ?EA2, ?EA, ?EA0; cbn [Z.max Z.of_nat Pos.of_succ_nat Pos.succ]; zlia)|]). img_apply Forall_nil.
Qed.
Lemma cells_chunks_new : Forall (cell_holds B lyF rd') (chunk_cells KSc).
Proof.
pose proof sizes_model as (ND & MS & RS & RZ & FP & KN & KR & KE & KQ & KB & KST). pose proof lyF_sec as LS.
unfold chunk_cells, hdr_state. rewrite KR, KN, KST, KB. unfold kChunkHeaderSize. cbn [sptr_exp app Z.eqb].
assert (EV : forall d, aeval B lyF (ASec (rS S) d) = mb + d) by (img_try (intros d; cbn [aeval aoff]; rewrite LS; img_refl)).
assert (EV2 : forall d d', aeval B lyF (aoff (ASec (rS S) d) d') = mb + d + d') by (img_try (intros d d'; cbn [aeval aoff]; rewrite LS; zlia)).
assert (EV3 : forall d d' d'', aeval B lyF (aoff (aoff (ASec (rS S) d) d') d'') = mb + d + d' + d'') by (img_try (intros d d' d''; cbn [aeval aoff]; rewrite LS; zlia)).
pose proof Vst as W1. pose proof Vb1 as W2. pose proof Vb2 as W3. pose proof Vn as W4. pose proof Vmag as W5. pose proof Vbk as W6. unfold Uv, Kv in W1, W2, W3, W4, W5, W6.
constructor. { img_apply val_mem_cell. rewrite EV2. cbn [aeval]. img_apply (val_mem_at _ (mb + 6144 - 16)); [img_try (zlia) | img_try (img_exact W1)]. }
constructor. { cbn [cell_holds c_at c_val c_w]. rewrite EV3. pose proof (W2 0%nat ltac:(img_try (zlia))) as X. rewrite Z.add_0_r in X. unfold m' in X.
exists 17. split; [|img_refl]. unfold rd', aview. replace (mb + 4096 + (2048 - 16) + 1) with (mb + 6144 - 15) by zlia. rewrite X. cbn [option_map].
rewrite le_byte_1_0 by zlia. rewrite unsigned_lit_small8 by zlia. img_refl. }
constructor. { img_apply val_mem_cell. rewrite EV3. cbn [aeval]. img_apply (val_mem_at _ (mb + 6144 - 14)); [img_try (zlia) | img_try (img_exact W3)]. }
constructor. { img_apply val_mem_cell. rewrite EV3. cbn [aeval]. img_apply (val_mem_at _ (mb + 6144 - 12)); [img_try (zlia) | img_try (img_exact W4)]. }
constructor. { img_apply val_mem_cell. rewrite EV. cbn [aeval]. img_apply (val_mem_at _ (mb + 4096)); [img_try (zlia) | img_try (img_exact W5)]. }
constructor. { img_apply val_mem_cell. rewrite !EV2. img_apply (val_mem_at _ (mb + 4096 + 8)); [img_try (zlia) |]. replace (mb + 4096 + (2048 - 16)) with (mb + 6144 - 16) by zlia. img_exact W6. }
img_apply Forall_nil.
Qed.
Lemma cells_sec_old_arr : Forall (cell_holds B ly rd') (map (fun ir => c8 (AQ (8 * Z.of_nat (fst ir))) (ASec (snd ir) 0)) (combine (seq 0 (length (st_sec_arr S))) (st_sec_arr S))).
Proof.
assert (INC : forall x, In x (sec_cells S) -> In x (acells B ly S)) by (img_try (intros x Hx; unfold acells; do 3 (img_apply in_app_iff; right); img_apply in_app_iff; left; img_exact Hx)).
img_apply Forall_forall. intros c Hc. pose proof Hc as Hc0. apply in_map_iff in Hc as ([i r] & <- & Hir). pose proof Hir as Hi. apply in_combine_l in Hi. apply in_seq in Hi.
img_apply keep_cellX; [img_try (img_apply INC; unfold sec_cells; do 3 right; img_apply in_app_iff; left; img_exact Hc0)|].
intros k Hk. cbn [c_at c_w c_val aeval c8 fst snd] in Hk |- *. pose proof len_arr as LA. pose proof Hres as [HRS _]. pose proof Hidx as HI.
img_apply Z_Q; [img_try (try unfold Qb; clear - Hk Hi LA HRS HI; unfold kPtrArrayResv, kMaxNumChunks in *; zlia) | img_try (unfold QSv; clear - Hk Hi LA; try unfold Qb; zlia) |].
intros [_ Hq]. unfold QR in Hq. clear - Hk Hi LA HRS Hq. try unfold Qb in *. zlia.
Qed.
Lemma cells_sec_old_hdr : Forall (cell_holds B ly rd') (flat_map (fun k => match ck_beg k with
| PSec r _ => [ c8 (ASec r 0) (ASec r 0); z8 (ASec r 8) (sec_map_size (ck_req k)); z8 (ASec r 16) (needed_size (ck_req k)); z8 (ASec r 24) (index_ofZ (st_sec_arr SF) r) ]
| _ => [] end) (st_chunks S)).
Proof.
pose proof SF_parts as (_ & _ & _ & _ & _ & _ & _ & _ & Rarr & _). rewrite Rarr.
assert (INC : forall x, In x (sec_cells S) -> In x (acells B ly S)) by (img_try (intros x Hx; unfold acells; do 3 (img_apply in_app_iff; right); img_apply in_app_iff; left; img_exact Hx)).
img_apply Forall_flat_map'. intros k Hk.
pose proof (chunk_facts B ly S rd0 k MA Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
destruct (ck_beg k) as [|o|r o|c' p] eqn:Eb; try img_apply Forall_nil. destruct GG as (_ & _ & Gbase & Gext & Gin & _).
assert (INr : In r (st_sec_arr S)) by (img_try (img_apply (proj2 (ws_arr_chunks _ (wf_secondary _ _ _ _ _ WF) r)); exists k; split; [img_try (img_exact Hk) | img_try (rewrite Eb; destruct (chunk_facts B ly S rd0 k MA Hk) as (_ & _ & _ & _ & _ & _ & _ & _ & GG'); rewrite Eb in GG'; destruct GG' as (-> & _); img_refl)])).
rewrite (index_ofZ_app_old _ _ _ INr).
pose proof (secondary_geometry (ck_req k) ltac:(img_try (zlia)) ltac:(img_try (destruct (chunk_facts B ly S rd0 k MA Hk) as (_ & _ & _ & _ & _ & _ & _ & _ & GG'); rewrite Eb in GG'; tauto))) as (_ & _ & SG & _).
img_apply (keep_cells _ (ly_sec ly r) (sec_map_size (ck_req k))).
- intros a Ha. img_apply (Z_sec (ly_sec ly r, sec_map_size (ck_req k))); [img_try (img_exact Gin) | img_try (cbn [fst snd]; img_exact Ha)].
- intros x Hx. img_apply INC. unfold sec_cells. do 3 right. img_apply in_app_iff. right. img_apply in_flat_map. exists k. rewrite Eb. split; [img_try (img_exact Hk) | img_try (img_exact Hx)].
- unfold kPage, kSecRz in *. pose proof (req_size_bounds (ck_req k) ltac:(img_try (zlia))) as (Q1 & Q2 & Q3).
repeat (img_apply Forall_cons; [img_try (cbn [c_at c_w aeval c8 z8]; zlia)|]). img_apply Forall_nil.
Qed.
Lemma cells_sec : Forall (cell_holds B lyF rd') (sec_cells SF).
Proof.
pose proof SF_parts as (_ & _ & _ & _ & _ & _ & _ & _ & Rarr & Rres & _ & Rck & _). pose proof (ts_inst B TS) as EI. pose proof len_arr as LA. pose proof lyF_sec as LS.
pose proof sizes_model as (ND & MS & RS & RZ & FP & KN & KR & KE & KQ & KB & KST). pose proof lyF_eqs as (_ & _ & EQ & _).
unfold sec_cells. rewrite Rres, Rarr, Rck.
constructor. { img_apply val_mem_cell. cbn [aeval]. rewrite EI. img_exact Vres. }
constructor. { img_apply val_mem_cell. cbn [aeval]. rewrite EI. rewrite length_app. cbn [length]. replace (Z.of_nat (length (st_sec_arr S) + 1)) with (idx + 1) by zlia. img_exact Vnch. }
constructor. { img_apply val_mem_cell. cbn [aeval]. rewrite EI. img_exact Vmtx. }
img_apply Forall_app. split.
- rewrite length_app. cbn [length]. img_apply Forall_forall. intros c Hc. apply in_map_iff in Hc as ([i r] & <- & Hir).
destruct (Nat.eq_dec i (length (st_sec_arr S))) as [->|Hne].
+   assert (Er : r = rS S).
{ replace (length (st_sec_arr S) + 1)%nat with (length (st_sec_arr S ++ [rS S])) in Hir by (img_try (rewrite length_app; img_refl)).
destruct (in_combine_seq _ _ _ _ Hir) as [E _]. rewrite Nat.sub_0_r, nth_error_app2 in E by zlia. rewrite Nat.sub_diag in E. cbn in E. injection E as <-. img_refl. }
(subst r; cbv beta). img_apply val_mem_cell. cbn [aeval fst snd]. rewrite EQ, LS, LA, Z.add_0_r. unfold QSv in Vslot. img_exact Vslot.
+   assert (Hold : In (i, r) (combine (seq 0 (length (st_sec_arr S))) (st_sec_arr S))).
{ replace (length (st_sec_arr S) + 1)%nat with (length (st_sec_arr S ++ [rS S])) in Hir by (img_try (rewrite length_app; img_refl)).
destruct (in_combine_seq _ _ _ _ Hir) as [E R]. rewrite length_app in R. cbn [length] in R. rewrite Nat.sub_0_r in E.
rewrite nth_error_app1 in E by zlia. img_apply combine_seq_in; [img_try (rewrite Nat.sub_0_r; img_exact E) | img_try (zlia)]. }
img_apply (cell_holds_le B ly lyF _ lyF_le rd'); [| img_try (img_exact (proj1 (Forall_forall _ _) cells_sec_old_arr _ ltac:(img_apply in_map_iff; exists (i, r); split; [img_refl | img_exact Hold])))].
split; cbn; [img_try (img_exact I)|]. apply in_combine_r in Hold.
pose proof (proj1 (ws_arr_live _ (wf_secondary _ _ _ _ _ WF) r) Hold) as (sm & Hsm & _). eapply nth_error_lt. img_exact Hsm.
- rewrite flat_map_app. img_apply Forall_app. split.
+ img_apply (Forall_cell_holds_le B ly lyF _ lyF_le rd'); [| img_try (img_exact cells_sec_old_hdr)].
img_apply Forall_flat_map'. intros k Hk. pose proof (YF49.chunk_lt S _ _ _ _ WF k Hk) as LT.
destruct (ck_beg k) as [|o|r o|c' p]; try img_apply Forall_nil. repeat (img_apply Forall_cons; [img_try (split; cbn; first [img_exact LT | img_exact I])|]). img_apply Forall_nil.
+ cbn [flat_map app]. rewrite KB. rewrite app_nil_r. rewrite KQ, ND, MS. rewrite (index_ofZ_app_new _ _ rS_not_in_arr), LA.
assert (EV : forall d, aeval B lyF (ASec (rS S) d) = mb + d) by (img_try (intros d; cbn [aeval aoff]; rewrite LS; img_refl)).
constructor. { img_apply val_mem_cell. rewrite !EV, Z.add_0_r. img_exact Vh0. }
constructor. { img_apply val_mem_cell. rewrite EV. cbn [aeval]. img_exact Vh8. }
constructor. { img_apply val_mem_cell. rewrite EV. cbn [aeval]. img_exact Vh16. }
constructor. { img_apply val_mem_cell. rewrite EV. cbn [aeval]. img_exact Vh24. }
img_apply Forall_nil.
Qed.
Lemma keep_batches : forall bl, incl bl (all_batches S) -> incl (batch_cells bl) (acells B ly S) -> Forall (cell_holds B ly rd') (batch_cells bl).
Proof.
induction bl as [|b t IH]; intros Hincl INC; [img_try (img_apply Forall_nil)|]. cbn [batch_cells].
pose proof (wq_batches _ (wf_quarantine _ _ _ _ _ WF)) as BL.
pose proof (proj1 (Forall_forall _ _) BL b (Hincl b (or_introl eq_refl))) as [L1 L2]. unfold kBatchSlots in L2.
assert (LOC : loc_ok (ly_space ly + b_self b) kBatchBytes).
{ pose proof (wf_classes _ _ _ _ _ WF kBatchClass ltac:(img_try (unfold kBatchClass; zlia))) as CL.
set (x := b_self b - region_off kBatchClass).
assert (INB : In x (batch_offs S kBatchClass)) by (img_try (rewrite batch_offs_24; img_apply in_map_iff; exists b; split; [img_refl | img_try (img_apply Hincl; left; img_refl)])).
pose proof (proj1 (Forall_forall _ _) (wr_elems _ _ _ _ _ _ CL) x ltac:(img_try (rewrite !in_app_iff; tauto))) as [X1 X2].
pose proof (wr_alloc _ _ _ _ _ _ CL) as AL. pose proof (mapped_user_bound (as_universe B) 0 0 0 S kBatchClass WF ltac:(img_try (unfold kBatchClass; zlia))) as MB.
pose proof (region_in_prim ly kBatchClass LY ltac:(img_try (unfold kBatchClass; zlia))) as (R1 & R2 & R3 & R4 & R5).
assert (CS : class_size kBatchClass = 8192) by img_refl. rewrite CS in X2.
assert (BX : ly_space ly + b_self b = region_base ly kBatchClass + x) by (img_try (unfold region_base; (subst x; cbv beta); zlia)).
intros a Ha. img_apply Z_prim. clear - Ha X1 X2 AL MB R1 R2 BX. unfold kBatchBytes, kUserMapSize, EV_MAX in *. zlia. }
img_apply Forall_cons; [img_try (img_apply (keep_cell _ _ _ LOC); [img_apply INC; left; img_refl | cbn; zlia | cbn; unfold kBatchBytes; zlia])|].
img_apply Forall_cons; [img_try (img_apply (keep_cell _ _ _ LOC); [img_apply INC; right; left; img_refl | cbn; zlia | cbn; unfold kBatchBytes; zlia])|].
img_apply Forall_cons; [img_try (img_apply (keep_cell _ _ _ LOC); [img_apply INC; right; right; left; img_refl | cbn; zlia | cbn; unfold kBatchBytes; zlia])|].
img_apply Forall_app. split.
- img_apply (keep_cells _ _ _ LOC).
+ intros y Hy. img_apply INC. do 3 right. img_apply in_app_iff. left. img_exact Hy.
+ img_apply Forall_forall. intros c Hc. apply in_map_iff in Hc as ([i k] & <- & Hik). apply in_combine_l in Hik. apply in_seq in Hik.
cbn. unfold kBatchBytes. zlia.
- img_apply IH; [img_try (intros y Hy; img_apply Hincl; right; img_exact Hy) | img_try (intros y Hy; img_apply INC; do 3 right; img_apply in_app_iff; right; img_exact Hy)].
Qed.
Lemma Z_quar : forall a, TFX_INST + o_quar <= a < (0x17c088 + D_10c0) -> ~ XC a.
Proof.
intros a Ha. pose proof BSLv_range as HB. img_apply Z_img; [img_try (clear - Ha; unfold TFX_INST, o_quar in *; zlia) | | img_try (clear - Ha; zlia)].
unfold WINI. clear - Ha HB. unfold TFX_INST, o_quar, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex in *. zlia.
Qed.
Lemma cells_quar : Forall (cell_holds B ly rd') (quar_cells SF).
Proof.
pose proof SF_parts as (_ & _ & _ & _ & Rqt & Rqg & _).
replace (quar_cells SF) with (quar_cells S) by (img_try (unfold quar_cells; rewrite Rqt, Rqg; img_refl)).
assert (INC : forall x, In x (quar_cells S) -> In x (acells B ly S)) by (img_try (intros x Hx; unfold acells; do 4 (img_apply in_app_iff; right); img_apply in_app_iff; left; img_exact Hx)).
pose proof (ts_inst B TS) as EI.
assert (LOCI : loc_ok (TFX_INST + o_quar) 400) by (img_try (intros a Ha; img_apply Z_quar; clear - Ha; unfold TFX_INST, o_quar in *; zlia)).
assert (LOCT : loc_ok (T + t_qc) 32) by (img_try (intros a Ha; img_apply Z_T; unfold WINT, t_qc, t_unwinding, kThreadObjSize in *; unfold T in *; clear - Ha; zlia)).
unfold quar_cells, qc_cells in *. unfold o_q_cmutex, o_q_rmutex, o_q_size, o_quar, t_qc in *.
img_apply Forall_cons; [img_try (img_apply (keep_cell _ _ _ LOCI); [img_apply INC; left; img_refl | cbn; rewrite EI; zlia | cbn; rewrite EI; zlia])|].
img_apply Forall_cons; [img_try (img_apply (keep_cell _ _ _ LOCI); [img_apply INC; right; left; img_refl | cbn; rewrite EI; zlia | cbn; rewrite EI; zlia])|].
img_apply Forall_app. split.
- do 4 (img_apply Forall_cons; [img_try (img_apply (keep_cell _ _ _ LOCT); [img_apply INC; right; right; img_apply in_app_iff; left; cbn; tauto | cbn; unfold T; zlia | cbn; unfold T; zlia])|]).
img_apply keep_batches; [img_try (intros b Hb; unfold all_batches; img_apply in_app_iff; left; img_exact Hb)|].
intros y Hy. img_apply INC. right; right. img_apply in_app_iff. left. do 4 right. img_exact Hy.
- do 4 (img_apply Forall_cons; [img_try (img_apply (keep_cell _ _ _ LOCI); [img_apply INC; right; right; img_apply in_app_iff; right; cbn; tauto | cbn; rewrite EI; zlia | cbn; rewrite EI; zlia])|]).
img_apply keep_batches; [img_try (intros b Hb; unfold all_batches; img_apply in_app_iff; right; img_exact Hb)|].
intros y Hy. img_apply INC. right; right. img_apply in_app_iff. right. do 4 right. img_exact Hy.
Qed.
Lemma cells_fs : Forall (cell_holds B ly rd') (fs_cells SF).
Proof.
pose proof SF_parts as (_ & _ & _ & _ & _ & _ & Rfs & _).
replace (fs_cells SF) with (fs_cells S) by (img_try (unfold fs_cells; rewrite Rfs; img_refl)).
img_apply (keep_cells _ (ly_F ly) kFakeStackSize).
- intros a Ha. img_apply (Z_ext 3 (ly_F ly, kFakeStackSize)); [img_refl | img_try (zlia) | img_try (cbn [fst snd]; img_exact Ha)].
- intros x Hx. unfold acells. do 5 (img_apply in_app_iff; right). img_apply in_app_iff. left. img_exact Hx.
- unfold fs_cells, kFakeStackSize. fcons'. fcons'. img_apply Forall_forall. intros c Hc. apply in_map_iff in Hc as ([i h] & <- & Hih).
apply in_combine_l in Hih. apply in_seq in Hih. cbn. zlia.
Qed.
Lemma DZONE64 : forall a, DZONE a -> 0 <= a < 2 ^ 64.
Proof.
intros a Ha. pose proof blocks_facts as (NBhi & SBhi & _). unfold DZONE in Ha.
clear - Ha NBhi SBhi. numconst. zlia.
Qed.
Lemma depot_final : depot_mem_ok B ly (depot_after z tr S) rd'.
Proof.
img_apply (depot_mem_ok_agree _ rdD).
- pose proof (wf_depot _ _ _ _ _ WF) as [ND INCL]. pose proof (depot_ids_bound S ND INCL). unfold depot_after. destruct (z =? 0); [img_try (zlia)|].
unfold depot_ids in *. cbn. rewrite length_app. cbn. zlia.
- intros a Ha. img_apply AGREED; [img_try (img_exact (DZONE64 a Ha)) | img_try (img_exact Ha)].
- img_exact DEPD.
Qed.
Lemma cells_depot : Forall (cell_holds B ly rd') (depot_cells ly SF).
Proof.
pose proof SF_parts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Rdep & _).
replace (depot_cells ly SF) with (depot_cells ly (depot_after z tr S)) by (img_try (unfold depot_cells, depot_ids, depot_frames; rewrite Rdep; img_refl)).
img_exact (proj1 depot_final).
Qed.
Lemma cells_ialloc : Forall (cell_holds B ly rd') (ialloc_cells B SF).
Proof.
pose proof SF_parts as (_ & _ & _ & _ & _ & _ & _ & Rii & _).
replace (ialloc_cells B SF) with (ialloc_cells B S) by (img_try (unfold ialloc_cells; rewrite Rii; img_refl)).
pose proof (ts_ial_lo B TS) as E1. pose proof (ts_ial_w B TS) as E2. pose proof (ts_ial_flag B TS) as E3.
img_apply (keep_cells _ (TFX_INST + o_quar) ((0x17c088 + D_10c0) - TFX_INST - o_quar)).
- intros a Ha. img_apply Z_quar. zlia.
- intros x Hx. unfold acells. do 7 (img_apply in_app_iff; right). img_apply in_app_iff. left. img_exact Hx.
- unfold ialloc_cells. rewrite E1, E2, E3. unfold TFX_IAL_LO, TFX_IAL_W, TFX_IAL_FLAG, TFX_INST, o_quar.
repeat (img_apply Forall_cons; [img_try (cbn; rewrite ?E1, ?E3; unfold TFX_IAL_LO, TFX_IAL_FLAG; zlia)|]). img_apply Forall_nil.
Qed.
Lemma cells_thread : Forall (cell_holds B ly rd') thread_cells.
Proof. unfold thread_cells. constructor; [|img_try (img_apply Forall_nil)]. img_apply val_mem_cell. cbn [aeval]. img_exact Vunw. Qed.
Lemma cells_final : Forall (cell_holds B lyF rd') (acells B lyF SF).
Proof.
pose proof (YF49.acells_lt B ly S _ _ _ _ WF) as LT. unfold acells in LT |- *.
pose proof lyF_eqs as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E13 & _).
assert (LIFT : forall l, incl l (flat_map (region_cells S) (zseq 1 31) ++ flat_map (cache_cells S) (zseq 1 31) ++ flat_map chunk_cells (st_chunks S) ++ sec_cells S ++
quar_cells S ++ fs_cells S ++ depot_cells ly S ++ ialloc_cells B S ++ thread_cells) ->
Forall (cell_holds B ly rd') l -> Forall (cell_holds B lyF rd') l).
{ intros l INC H. img_apply (Forall_cell_holds_le B ly lyF _ lyF_le rd'); [img_try (img_exact (incl_Forall INC LT)) | img_try (img_exact H)]. }
pose proof SF_parts as (Rreg & Rinit & Rcache & _ & Rqt & Rqg & Rfs & Rii & _ & _ & Rdep & Rck & _).
img_apply Forall_app; split.
{ img_apply LIFT; [| img_try (img_exact cells_regions)]. intros x Hx. img_apply in_app_iff. left. apply in_flat_map in Hx as (c & Hc & Hx). img_apply in_flat_map. exists c.
unfold region_cells in *. rewrite Rreg in Hx. img_exact (conj Hc Hx). }
img_apply Forall_app; split.
{ img_apply LIFT; [| img_try (img_exact cells_caches)]. intros x Hx. img_apply in_app_iff; right. img_apply in_app_iff; left. apply in_flat_map in Hx as (c & Hc & Hx). img_apply in_flat_map. exists c.
unfold cache_cells in *. rewrite Rinit, (Rcache c) in Hx. img_exact (conj Hc Hx). }
img_apply Forall_app; split.
{ rewrite Rck, flat_map_app. img_apply Forall_app; split.
- img_apply LIFT; [| img_try (img_exact cells_chunks_old)]. intros x Hx. do 2 (img_apply in_app_iff; right). img_apply in_app_iff; left. img_exact Hx.
- cbn [flat_map]. rewrite app_nil_r. img_exact cells_chunks_new. }
img_apply Forall_app; split; [img_try (img_exact cells_sec)|].
img_apply Forall_app; split.
{ img_apply LIFT; [| img_try (img_exact cells_quar)]. intros x Hx. do 4 (img_apply in_app_iff; right). img_apply in_app_iff; left. unfold quar_cells in *. rewrite Rqt, Rqg in Hx. img_exact Hx. }
img_apply Forall_app; split.
{ img_apply LIFT; [| img_try (img_exact cells_fs)]. intros x Hx. do 5 (img_apply in_app_iff; right). img_apply in_app_iff; left. unfold fs_cells in *. rewrite Rfs in Hx. img_exact Hx. }
img_apply Forall_app; split.
{
replace (depot_cells lyF SF) with (depot_cells ly SF) by (img_try (unfold depot_cells, depot_frames, depot_traces; rewrite E13; img_refl)).
img_apply (Forall_cell_holds_le B ly lyF _ lyF_le rd'); [| img_try (img_exact cells_depot)]. unfold depot_cells. repeat (img_apply Forall_cons; [img_try (split; cbn; img_exact I)|]). img_apply Forall_nil. }
img_apply Forall_app; split.
{ img_apply LIFT; [| img_try (img_exact cells_ialloc)]. intros x Hx. do 7 (img_apply in_app_iff; right). img_apply in_app_iff; left. unfold ialloc_cells in *. rewrite Rii in Hx. img_exact Hx. }
img_apply LIFT; [| img_try (img_exact cells_thread)]. intros x Hx. do 8 (img_apply in_app_iff; right). img_exact Hx.
Qed.
Lemma cell_holds_agree3 : forall (rd1 rd2 rd3 : reader) c,
(forall k, 0 <= k < Z.max 1 (Z.of_nat (c_w c)) ->
(forall v, rd1 (aeval B ly (c_at c) + k) = Some v -> rd3 (aeval B ly (c_at c) + k) = Some v) \/ rd3 (aeval B ly (c_at c) + k) = rd2 (aeval B ly (c_at c) + k)) ->
cell_holds B ly rd1 c -> cell_holds B ly rd2 c -> cell_holds B ly rd3 c.
Proof.
clearP. intros rd1 rd2 rd3 c He H1 H2. unfold cell_holds in *. destruct (c_val c) as [e|m vv].
- intros k Hk. destruct (He (Z.of_nat k) ltac:(img_try (zlia))) as [E|E]; [img_try (img_exact (E _ (H1 k Hk))) | img_try (rewrite E; img_exact (H2 k Hk))].
- destruct H1 as (b1 & Hb1 & Hm1). destruct H2 as (b2 & Hb2 & Hm2).
destruct (He 0 ltac:(img_try (zlia))) as [E|E]; rewrite Z.add_0_r in E; [img_try (exists b1; split; [img_exact (E _ Hb1) | img_exact Hm1]) | img_try (exists b2; rewrite E; tauto)].
Qed.
Lemma const_final : Forall (cell_holds B ly rd') (as_const B ly).
Proof.
img_apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) (am_const B ly S rd0 MA) c Hc) as HOLD.
pose proof (proj1 (Forall_forall _ _) CSTD c Hc) as HOLDD.
pose proof (const_cells_CZ c) as CCZ. destruct (padb c) eqn:Ep.
-
pose proof Hc as Hc'. rewrite (ts_const B TS ly) in Hc'. unfold Tfx_const in Hc'. apply in_app_iff in Hc' as [Hc'|Hc'].
{ exfalso. revert Ep Hc'. clear. intros Ep Hc'. unfold Tfx_const_sym in Hc'. cbn [In] in Hc'.
repeat match type of Hc' with _ \/ _ => destruct Hc' as [<-|Hc']; [img_try (discriminate Ep)|] | False => destruct Hc' end. }
pose proof (proj1 (forallb_forall _ _) (ltac:(img_eqrefl) : forallb (fun c => negb (padb c) || match c_val c with AV (ANum 0) => true | _ => false end) (Tfx_const_abs ++ Tfx_const_shadow) = true) c Hc') as CK.
cbn beta in CK. rewrite Ep in CK. cbn [negb orb] in CK.
unfold padb in Ep. unfold cell_holds. destruct (c_at c) eqn:Ea; try discriminate Ep. cbn [aeval] in CCZ |- *.
destruct (c_val c) as [e|mk vv]; [|img_try (discriminate CK)]. destruct e; try discriminate CK.
lazymatch goal with |- context [aeval _ _ (ANum ?zz)] => destruct zz; try discriminate CK end.
intros k Hk. cbn [aeval]. pose proof (CCZ (Z.of_nat k) Hc ltac:(img_try (zlia))) as Pk. unfold MPAD in Pk.
lazymatch goal with |- _ (?a + Z.of_nat k) = _ =>
replace (a + Z.of_nat k) with (TFX_INST + o_sec_mutex + (a + Z.of_nat k - (TFX_INST + o_sec_mutex))) by zlia end.
rewrite Vpad by zlia. f_equal. clear. unfold le_byte. rewrite Z.mod_0_l by (img_try (img_apply Z.pow_nonzero; zlia)). rewrite Z.shiftr_0_l. img_refl.
-
img_apply (cell_holds_agree3 rd0 rdD); [| img_try (img_exact HOLD) | img_try (img_exact HOLDD)].
assert (HmapD : zdisjoint (mb, MSv) (ly_D ly, 4096)).
{ img_apply (proj1 (Forall_forall _ _) GAPART). img_apply in_app_iff. left. unfold static_extents, owned_extents. img_apply in_app_iff. left. cbn. tauto. }
intros k Hk. pose proof (CZ_untouched HmapD _ (CCZ k Hc Hk)) as (Ra & N1 & N2 & N3 & N4 & N5).
destruct (zr_dec (0x17c088 + D_10c0) (0x5cc810 + D_10c0) (aeval B ly (c_at c) + k)) as [D|D].
+ right. img_apply AGREED; [img_try (img_exact Ra) | img_try (unfold DZONE; left; img_exact D)].
+ left. img_apply AGREE0; [img_try (img_exact Ra) | | img_try (intros Hs; img_apply N1; unfold WIN; left; img_exact Hs)].
intros HX. unfold XC in HX. unfold WIN, WINM in N1. unfold DZONE in HX. clear - HX N1 N2 N4 N5 D. tauto.
Qed.
Lemma CONSTlt : forall nn, Forall (YF49.cell_lt nn) (as_const B ly).
Proof.
intros nn. rewrite (ts_const B TS ly). clear. unfold Tfx_const, Tfx_const_sym, Tfx_const_abs, Tfx_const_shadow. cbn [app].
repeat (img_apply Forall_cons; [img_try (img_exact (conj I I))|]). img_apply Forall_nil.
Qed.
Lemma JUNKlt : forall nn lyx, Forall (fun r => YF49.asec_lt nn (fst r)) (as_junk B lyx).
Proof. intros nn lyx. img_apply Forall_forall. intros r Hr. destruct (ts_junk B TS lyx r Hr) as (zz & -> & _). img_exact I. Qed.
Lemma CONSTeq : forall ly1 ly2, as_const B ly1 = as_const B ly2.
Proof. intros ly1 ly2. rewrite !(ts_const B TS). img_refl. Qed.
Lemma MAF : ARm B lyF S rd0.
Proof.
img_exact (YF49.ARm_layout_le B ly lyF S rd0 MA lyF_le lyF_ok (CONSTeq lyF ly) (CONSTlt _) (JUNK lyF ly) (JUNKlt _ ly)).
Qed.
Lemma const_finalF : Forall (cell_holds B lyF rd') (as_const B lyF).
Proof. rewrite (CONSTeq lyF ly). img_exact (Forall_cell_holds_le B ly lyF _ lyF_le rd' _ (CONSTlt _) const_final). Qed.
Lemma fa_final : fa_entries_ok lyF rd' SF.
Proof.
pose proof SF_parts as (Rreg & _). pose proof lyF_eqs as (_ & E2 & _). intros c i vv Hc Hi HV k Hk. rewrite Rreg in Hi, HV.
unfold fa_base. rewrite E2. img_change (ly_space ly + region_off c + kFreeArrayOffset) with (fa_base ly c).
pose proof (wf_classes _ _ _ _ _ WF c Hc) as CL. pose proof (wr_fa_len _ _ _ _ _ _ CL) as FL. pose proof (wr_fa_bound _ _ _ _ _ _ CL) as FB.
img_apply AGX; [img_try (eapply own_fa; [img_exact MA | img_exact Hc | zlia]) | | img_try (img_exact (am_fa _ _ _ _ MA c i vv Hc Hi HV k Hk))].
pose proof (region_in_prim ly c LY Hc) as (R1 & R2 & _).
unfold fa_base, region_base, kFreeArrayOffset, kFreeArrayMax in *.
img_apply Z_prim; clear - Hk Hi FL FB R1 R2 Hc; zlia.
Qed.
Lemma flags_final : fs_flags_ok lyF rd' SF.
Proof.
pose proof SF_parts as (_ & _ & _ & Rfr & _). pose proof lyF_eqs as (_ & _ & _ & _ & _ & E6 & _). intros cid pos Hc Hp.
rewrite Rfr. unfold flag_addr. rewrite E6. pose proof (flag_off_bounds cid pos Hc Hp) as FB.
img_apply AGX; [img_try (unfold flag_addr, kFakeFlagsOff in *; eapply own_F_low; [img_exact MA | zlia]) | | img_try (img_exact (am_flags _ _ _ _ MA cid pos Hc Hp))].
img_apply (Z_ext 3 (ly_F ly, kFakeStackSize)); [img_refl | img_try (zlia) | img_try (cbn [fst snd])].
unfold flag_addr, kFakeFlagsOff, kFakeFramesOff, kFakeStackSize in *. zlia.
Qed.
Lemma zero_final : Forall (range_zero B lyF rd') (ialloc_zero B).
Proof.
pose proof (am_zero _ _ _ _ MA) as Mze. pose proof (am_syms _ _ _ _ MA) as Msy.
img_apply Forall_forall. intros r Hr i Hi.
assert (EV : aeval B lyF (fst r) = aeval B ly (fst r)) by (img_try (unfold ialloc_zero in Hr; destruct Hr as [<-|[<-|[]]]; img_refl)). rewrite EV.
img_apply AGX.
- pose proof (aso_ialloc _ Msy) as [I1 I2].
eapply (own_area B ly S rd0 (as_ialloc_lo B, as_ialloc_hi B - as_ialloc_lo B)); [img_try (img_exact MA) | img_try (cbn; tauto) |].
unfold ialloc_zero in Hr. cbn [fst snd]. destruct Hr as [<-|[<-|[]]]; cbn [fst snd aeval] in *; zlia.
- pose proof (ts_ial_lo B TS) as E1. pose proof (ts_ial_hi B TS) as E2'. pose proof (ts_ial_w B TS) as E3.
img_apply Z_quar. unfold ialloc_zero in Hr.
destruct Hr as [<-|[<-|[]]]; cbn [fst snd aeval] in *; rewrite ?E1, ?E2', ?E3 in *; unfold TFX_IAL_LO, TFX_IAL_HI, TFX_IAL_W, TFX_INST, o_quar in *; zlia.
- img_exact (proj1 (Forall_forall _ _) Mze r Hr i Hi).
Qed.
Lemma rd_byte : forall a v, 0 <= v < 256 -> w_H Wz (Z_to_bv 64 a) = false -> mem' (Z_to_bv 64 a) = Some (Z_to_bv 8 v) -> rd' a = Some v.
Proof. clearP. intros a v Hv Hh Hm. unfold rd', aview, mbyte, mrestrict. rewrite Hh, Hm. cbn [option_map]. rewrite unsigned_lit_small8 by img_exact Hv. img_refl. Qed.
Lemma sh_vis : forall a, SMv <= a < SMv + MSv / 8 -> w_H Wz (Z_to_bv 64 a) = false.
Proof.
intros a Ha. pose proof (SH_hull mb) as (H1 & H2 & _). pose proof map_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _ & _ & SMA). pose proof map_zoneN as MZ.
img_apply VISsh. rewrite unsigned_lit_small by (img_try (clear - Ha SM1 SM2 MZ; unfold kHighShadowBeg, kHighShadowEnd in *; zlia)). rewrite SMA in Ha. clear - Ha H1 H2 MZ. zlia.
Qed.
Lemma sh_map : forall j, shadow_addr (mb + 8 * j) = SMv + j.
Proof.
intros j. pose proof map_facts as (_ & _ & M3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SMA). pose proof map_zoneN as MZ. rewrite SMA. unfold shadow_addr.
apply Z.mod_divide in M3 as [p Hp]; [|img_try (zlia)]. rewrite Hp. replace (p * 4096 + 8 * j) with ((p * 512 + j) * 8) by zlia. replace (p * 4096) with ((p * 512) * 8) by zlia.
rewrite !Z.div_mul by zlia. zlia.
Qed.
Lemma sh_sep : forall g, g mod 8 = 0 -> (g + 8 <= mb \/ mb + MSv <= g) -> ~ (SMv <= shadow_addr g < SMv + MSv / 8).
Proof.
intros g Hg HM. pose proof map_facts as (M1 & M2 & M3 & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _ & _ & SMA). pose proof map_zoneN as MZ.
rewrite SMA. unfold shadow_addr, SHADOW_OFF. apply Z.mod_divide in Hg as [q Hq]; [|img_try (zlia)]. apply Z.mod_divide in M3 as [p Hp]; [|img_try (zlia)].
pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & _ & Z9 & _). apply Z.mod_divide in Z9 as [u Hu]; [|img_try (zlia)].
rewrite Hq, Hp, Hu in *. replace (q * 8 / 8) with q by (img_try (symmetry; img_apply Z.div_mul; zlia)).
replace (p * 4096) with ((p * 512) * 8) by zlia. rewrite Z.div_mul by zlia. replace (u * 4096) with ((u * 512) * 8) by zlia. rewrite Z.div_mul by zlia.
clear - HM MZ. zlia.
Qed.
Lemma in_rangesb_app : forall g l1 l2, in_rangesb g (l1 ++ l2) = (in_rangesb g l1 || in_rangesb g l2)%bool.
Proof. clear. intros g l1 l2. induction l1 as [|[lo len] t IH]; [img_refl|]. cbn [in_rangesb app]. rewrite IH, Bool.orb_assoc. img_refl. Qed.
Lemma ck_base_lyF : forall k, In k (st_chunks S) -> ck_base B lyF k = ck_base B ly k.
Proof. intros k Hk. unfold ck_base. img_apply (sptr_addr_le B ly lyF (length (st_secs S)) _ lyF_le). img_exact (YF49.chunk_lt S _ _ _ _ WF k Hk). Qed.
Lemma find_chunk_at_lyF : forall g, find_chunk_at B lyF (st_chunks S) g = find_chunk_at B ly (st_chunks S) g.
Proof.
intros g. assert (H : forall l, incl l (st_chunks S) -> find_chunk_at B lyF l g = find_chunk_at B ly l g).
{ induction l as [|k t IH]; intros INC; [img_refl|]. cbn [find_chunk_at]. rewrite (ck_base_lyF k (INC k (or_introl eq_refl))).
rewrite (IH (fun x Hx => INC x (or_intror Hx))). img_refl. }
img_apply H. intros k Hk. img_exact Hk.
Qed.
Lemma ck_base_new : ck_base B lyF KSc = Kv.
Proof. pose proof sizes_model as (_ & _ & _ & _ & _ & _ & _ & _ & _ & KB & _). unfold ck_base. rewrite KB. cbn [sptr_addr sptr_exp aeval]. rewrite lyF_sec. unfold Kv. img_refl. Qed.
Lemma FPR : fa_poison_ranges lyF SF = fa_poison_ranges ly S ++ [(mb, MSv)].
Proof.
pose proof SF_parts as (Rreg & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Rck & _). pose proof lyF_eqs as (_ & E2 & _).
pose proof sizes_model as (_ & MS & _ & _ & _ & _ & _ & _ & KQ & KB & _).
unfold fa_poison_ranges. rewrite Rck, flat_map_app, app_assoc.
pose proof (sec_extents_le ly lyF S _ _ _ _ lyF_le WF) as SE. unfold sec_extents in SE. rewrite SE.
replace (flat_map (fun k => match ck_beg k with PSec r _ => [(ly_sec lyF r, sec_map_size (ck_req k))] | _ => [] end) [KSc]) with [(mb, MSv)]
by (img_try (cbn [flat_map]; rewrite KB, KQ, MS, lyF_sec, app_nil_r; img_refl)).
f_equal; f_equal; try img_refl;
unfold reg in Rreg |- *; unfold region_base, fa_base; rewrite ?E2; img_apply flat_map_ext; intros c; rewrite ?Rreg; img_refl.
Qed.
Lemma shadow_final : shadow_ok B lyF rd' SF.
Proof.
pose proof SF_parts as (Rreg & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Rck & _).
pose proof sizes_model as (ND & MS & RS & RZ & FP & KN & KR & KE & KQ & KB & KST).
pose proof map_facts as (M1 & M2 & M3 & M4 & M5 & _ & M7 & _ & _ & _ & _ & SM1 & SM2 & _ & PB & SMA). pose proof map_zoneN as MZ.
pose proof size_facts as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & _). pose proof high_facts as (F1 & F2 & F3 & F4 & F5 & F6 & _).
destruct Hmap_apart as (_ & _ & MP3 & _).
assert (C8 : ASAN_CEIL mod 8 = 0) by (img_try (pose proof (proj2 (@YG0h.ASAN_CEIL_range _)) as CM; clear - CM MZ; apply Z.mod_divide in CM as [q Hq]; [|img_try (zlia)]; rewrite Hq; replace (q * 4096) with ((q * 512) * 8) by zlia; img_apply Z.mod_mul; zlia)).
assert (M8 : MSv mod 8 = 0) by (img_try (clear - Z9 MZ; apply Z.mod_divide in Z9 as [u Hu]; [|img_try (zlia)]; rewrite Hu; replace (u * 4096) with ((u * 512) * 8) by zlia; img_apply Z.mod_mul; zlia)).
pose proof (Z.div_mod MSv 8 ltac:(img_try (zlia))) as DM8.
intros g vv Hg8 HV. unfold ashadow in HV. rewrite Rck in HV.
destruct (find_chunk_at B ly (st_chunks S) g) as [k0|] eqn:F0.
-
pose proof F0 as F0'. rewrite <- find_chunk_at_lyF in F0'. rewrite (find_chunk_at_app1 lyF _ _ _ _ F0') in HV.
pose proof F0 as F0c. apply find_chunk_at_In in F0c as [Hk0 Hg0]. rewrite (ck_base_lyF k0 Hk0) in HV.
assert (A0 : ashadow B ly S g = Some vv) by (img_try (unfold ashadow; rewrite F0; img_exact HV)).
pose proof (chunk_facts B ly S rd0 k0 MA Hk0) as (C1 & C2 & _).
img_apply AGX; [img_try (img_exact (ashadow_owned B ly S rd0 g vv MA A0)) | | img_try (img_exact (am_shadow _ _ _ _ MA g vv Hg8 A0))].
img_apply Z_band; [img_try (rewrite <- (Zplus_minus (ck_base B ly k0) g); img_apply (shadow_addr_in_band _ _ _ C1); clear - Hg0 MZ; zlia)|].
img_apply sh_sep; [img_try (img_exact Hg8)|]. destruct (extent_zone B ly S rd0 k0 MA Hk0) as [[X1 X2]|(m & len & Hin & X1 & X2)].
+ unfold zdisjoint in MP3. cbn [fst snd] in MP3. apply Z.mod_divide in Hg8 as [q Hq]; [|img_try (zlia)]. apply Z.mod_divide in M3 as [p Hp]; [|img_try (zlia)]. clear - Hg0 X1 X2 MP3 Hq Hp MZ. zlia.
+ pose proof (proj1 (Forall_forall _ _) GAPART (m, len) ltac:(img_try (img_apply in_app_iff; right; img_apply in_app_iff; right; img_exact Hin))) as D. unfold zdisjoint in D. cbn [fst snd] in D.
apply Z.mod_divide in Hg8 as [q Hq]; [|img_try (zlia)]. apply Z.mod_divide in M3 as [p Hp]; [|img_try (zlia)]. clear - Hg0 X1 X2 D Hq Hp MZ. unfold kPage in *. zlia.
- pose proof F0 as F0'. rewrite <- find_chunk_at_lyF in F0'. rewrite (find_chunk_at_app2 lyF _ _ _ F0') in HV. cbn [find_chunk_at] in HV.
rewrite ck_base_new, KE in HV.
destruct (andb (Kv <=? g) (g <? Kv + (MSv - 4096))) eqn:CK.
+
apply andb_prop in CK as [CK1 CK2]. apply Z.leb_le in CK1. apply Z.ltb_lt in CK2.
injection HV as HV'. cbn beta iota in HV'. rewrite ck_base_new in HV'. unfold chunk_granule in HV'. rewrite KR, KN, KST in HV'. img_change (2048 / 8) with 256 in HV'.
set (j := (g - Kv) / 8) in HV'.
assert (Hgj : g = mb + 8 * (512 + j)).
{ (subst j; cbv beta). rewrite M4 in *. pose proof (Z.div_mod (g - (mb + 4096)) 8 ltac:(img_try (zlia))) as D1. apply Z.mod_divide in M3 as [p Hp]; [|img_try (zlia)]. apply Z.mod_divide in Hg8 as [q Hq]; [|img_try (zlia)].
assert ((g - (mb + 4096)) mod 8 = 0) by (img_try (rewrite Hq, Hp; replace (q * 8 - (p * 4096 + 4096)) with ((q - 512 * p - 512) * 8) by zlia; img_apply Z.mod_mul; zlia)). zlia. }
pose proof (sh_map (512 + j)) as SA. rewrite <- Hgj in SA. rewrite SA.
assert (Jhi : j < MSv / 8 - 512) by (img_try (clear - CK2 Hgj M4 DM8 M8 MZ; zlia)).
assert (N8 : N8D / 8 = n / 8) by (img_try (unfold N8D; img_apply Z.div_mul; zlia)).
assert (R8 : R8v / 8 = (n + 7) / 8) by (img_try (unfold R8v; img_apply Z.div_mul; zlia)).
pose proof (Z.div_mod n 8 ltac:(img_try (zlia))) as DM. pose proof (Z.mod_pos_bound n 8 ltac:(img_try (zlia))) as MB.
pose proof (Z.div_mod (n + 7) 8 ltac:(img_try (zlia))) as DM7. pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(img_try (zlia))) as MB7.
assert (VIS : w_H Wz (Z_to_bv 64 (SMv + (512 + j))) = false) by (img_try (img_apply sh_vis; clear - Jhi CK1 Hgj M4 MZ; zlia)).
assert (R64 : 0 <= SMv + (512 + j) < 2 ^ 64) by (img_try (clear - Jhi CK1 Hgj M4 SM1 SM2 MZ; unfold kHighShadowBeg, kHighShadowEnd in *; zlia)).
revert HV'. destruct (Z.ltb_spec j 256) as [J1|J1]; intros HV'; cbn beta iota in HV'.
*
(subst vv; cbv beta). img_apply rd_byte; [img_try (unfold shHeapLeftRz; zlia) | img_try (img_exact VIS) |]. img_apply Vsh. rewrite unsigned_lit_small by img_exact R64. left. clear - J1 CK1 Hgj M4 MZ. zlia.
* revert HV'. destruct (Z.ltb_spec j (256 + n / 8)) as [J2|J2]; intros HV'; cbn beta iota in HV'.
--
(subst vv; cbv beta). img_apply rd_byte; [img_try (unfold shAddressable; zlia) | img_try (img_exact VIS) |]. img_apply Vzs. rewrite unsigned_lit_small by img_exact R64. clear - J1 J2 N8 MZ. zlia.
-- revert HV'. destruct (andb (j =? 256 + n / 8) (negb (n mod 8 =? 0))) eqn:PJ; intros HV'; cbn beta iota in HV'.
++
apply andb_prop in PJ as [PJ1 PJ2]. apply Z.eqb_eq in PJ1. apply Bool.negb_true_iff in PJ2. apply Z.eqb_neq in PJ2. (subst vv; cbv beta).
pose proof (Vpb PJ2 0%nat ltac:(img_try (zlia))) as X. rewrite Z.add_0_r in X. unfold m' in X.
assert (EP : PBv = SMv + (512 + j)) by (img_try (clear - PB PJ1 N8 MZ; zlia)).
unfold rd', aview. rewrite <- EP, X. cbn [option_map]. rewrite le_byte_1_0 by zlia. rewrite unsigned_lit_small8 by zlia. img_refl.
++
(subst vv; cbv beta). img_apply rd_byte; [img_try (unfold shHeapLeftRz; zlia) | img_try (img_exact VIS) |]. img_apply Vsh. rewrite unsigned_lit_small by img_exact R64. right.
unfold UEv, SHBv. unfold SMv, SHBv in Jhi |- *. apply Z.mod_divide in M3 as [p Hp]; [|img_try (zlia)].
assert (EU : (mb + 6144 + R8v) / 8 = mb / 8 + 768 + R8v / 8).
{ rewrite Hp. apply Z.mod_divide in Z2 as [r8 Hr8]; [|img_try (zlia)]. rewrite Hr8. replace (p * 4096 + 6144 + r8 * 8) with ((p * 512 + 768 + r8) * 8) by zlia.
replace (p * 4096) with ((p * 512) * 8) by zlia. rewrite !Z.div_mul by zlia. zlia. }
rewrite EU, R8. apply Bool.andb_false_iff in PJ.
destruct PJ as [PJ|PJ]; [img_try (apply Z.eqb_neq in PJ) | img_try (apply Bool.negb_false_iff in PJ; apply Z.eqb_eq in PJ)]; clear - J1 J2 PJ Jhi DM MB DM7 MB7 MZ; split; try zlia.
all: assert (n / 8 + 1 <= j) by zlia; assert ((n + 7) / 8 <= n / 8 + 1) by zlia; zlia.
+
rewrite FPR, in_rangesb_app in HV.
destruct (in_rangesb g (fa_poison_ranges ly S)) eqn:IR.
* cbn [orb] in HV. assert (A0 : ashadow B ly S g = Some vv) by (img_try (unfold ashadow; rewrite F0, IR; img_exact HV)).
apply in_rangesb_true in IR as (lo & len & Hin & Hglo).
img_apply AGX; [img_try (img_exact (ashadow_owned B ly S rd0 g vv MA A0)) | | img_try (img_exact (am_shadow _ _ _ _ MA g vv Hg8 A0))].
assert (GZ : (ly_prim ly <= g /\ g + 8 <= ly_prim ly + kPrimResvSize) \/ In (lo, len) (sec_extents ly S)).
{ unfold fa_poison_ranges in Hin. apply in_app_iff in Hin as [Hin|Hin].
- left. apply in_flat_map in Hin as (c & Hc & Hin). apply zseq_In in Hc.
pose proof (region_in_prim ly c LY ltac:(img_try (zlia))) as (R1 & R2 & R3 & R4 & R5).
pose proof (wf_classes _ _ _ _ _ WF c ltac:(img_try (zlia))) as CL. pose proof (wr_alloc _ _ _ _ _ _ CL) as A1. pose proof (wr_fa _ _ _ _ _ _ CL) as [A2 _].
pose proof (wr_fa_bound _ _ _ _ _ _ CL) as A3. pose proof (mapped_user_bound (as_universe B) 0 0 0 S c WF ltac:(img_try (zlia))) as MB.
pose proof (lo_prim_al ly LY) as PA. unfold page_aligned in PA. apply Z.mod_divide in PA as [pp Hpp]; [|img_try (zlia)]. apply Z.mod_divide in Hg8 as [q Hq]; [|img_try (zlia)].
unfold kUserMapSize, EV_MAX, kFreeArrayMax, kPrimResvSize in *. unfold fa_base, kFreeArrayOffset in Hin. unfold region_base in *.
destruct Hin as [E|[E|[]]]; injection E as <- <-; clear - Hglo R1 R2 A1 A2 A3 MB Hpp Hq MZ; zlia.
- right. apply in_flat_map in Hin as (k & Hk & Hin). unfold sec_extents. img_apply in_flat_map. exists k. img_exact (conj Hk Hin). }
assert (GB : in_band_rw (shadow_addr g)).
{ destruct GZ as [[X1 X2]|Hin'].
- assert (HPA : in_app (ly_prim ly) kPrimResvSize) by (img_try (unfold in_app; clear - F3 F6 MZ; zlia)).
rewrite <- (Zplus_minus (ly_prim ly) g). img_apply (shadow_addr_in_band _ _ _ HPA). clear - X1 X2 MZ. zlia.
- pose proof (am_placed _ _ _ _ MA) as [PL _]. pose proof (proj1 (Forall_forall _ _) PL (lo, len) Hin') as (_ & HIA & _). cbn [fst snd] in HIA.
rewrite <- (Zplus_minus lo g). img_apply (shadow_addr_in_band _ _ _ HIA). clear - Hglo MZ. zlia. }
img_apply Z_band; [img_try (img_exact GB)|]. img_apply sh_sep; [img_try (img_exact Hg8)|].
destruct GZ as [[X1 X2]|Hin'].
-- unfold zdisjoint in MP3. cbn [fst snd] in MP3. clear - X1 X2 MP3 MZ. zlia.
-- pose proof (proj1 (Forall_forall _ _) GAPART (lo, len) ltac:(img_try (img_apply in_app_iff; right; img_apply in_app_iff; right; img_exact Hin'))) as D. unfold zdisjoint in D. cbn [fst snd] in D.
apply Z.mod_divide in Hg8 as [q Hq]; [|img_try (zlia)]. apply Z.mod_divide in M3 as [p Hp]; [|img_try (zlia)]. clear - Hglo D Hq Hp MZ. zlia.
* cbn [orb in_rangesb] in HV. rewrite Bool.orb_false_r in HV.
destruct (andb (mb <=? g) (g <? mb + MSv)) eqn:IM; [|img_try (discriminate HV)]. injection HV as <-.
apply andb_prop in IM as [IM1 IM2]. apply Z.leb_le in IM1. apply Z.ltb_lt in IM2.
apply Bool.andb_false_iff in CK. rewrite M4 in CK.
assert (GH : g < mb + 4096) by (img_try (destruct CK as [CK|CK]; [img_try (apply Z.leb_gt in CK) | img_try (apply Z.ltb_ge in CK)]; clear - CK IM1 IM2 MZ; zlia)).
set (j := (g - mb) / 8).
assert (Hgj : g = mb + 8 * j).
{ (subst j; cbv beta). pose proof (Z.div_mod (g - mb) 8 ltac:(img_try (zlia))) as D1. apply Z.mod_divide in M3 as [p Hp]; [|img_try (zlia)]. apply Z.mod_divide in Hg8 as [q Hq]; [|img_try (zlia)].
assert ((g - mb) mod 8 = 0) by (img_try (rewrite Hq, Hp; replace (q * 8 - p * 4096) with ((q - 512 * p) * 8) by zlia; img_apply Z.mod_mul; zlia)). zlia. }
rewrite Hgj, sh_map. img_apply rd_byte; [img_try (unfold shHeapLeftRz; zlia) | img_try (img_apply sh_vis; clear - IM1 GH Hgj Z8 DM8 M8 MZ; zlia) |].
img_apply Vsh. rewrite unsigned_lit_small by (img_try (clear - IM1 GH Hgj SM1 SM2 Z8 MZ; unfold kHighShadowBeg, kHighShadowEnd in *; zlia)). left. clear - IM1 GH Hgj MZ. zlia.
Qed.
Lemma Z_lowsh : forall a, 2147459072 <= a < (2148236800 + D_200) -> ~ XC a.
Proof.
intros a Ha Hx. apply XC_where in Hx. pose proof high_facts as (F1 & _ & _ & _ & _ & _ & _ & _ & F9 & _).
pose proof blocks_facts as (NBhi & SBhi & _). pose proof map_facts as (M1 & _). pose proof map_zoneN as MZ.
pose proof (zone3_apart_img _ _ a F1) as TI. pose proof (zone3_apart_hsh _ _ a F1) as TH. pose proof (zone3_apart_img _ _ a F9) as QI. pose proof (zone3_apart_hsh _ _ a F9) as QH. pose proof (zone3_apart_img _ _ a NBhi) as NI. pose proof (zone3_apart_hsh _ _ a NBhi) as NH. pose proof (zone3_apart_img _ _ a SBhi) as BI. pose proof (zone3_apart_hsh _ _ a SBhi) as BH. pose proof (zone3_apart_img _ _ a (mzone_zone3 _ _ (proj2 Hmap))) as MI. pose proof (zone3_apart_hsh _ _ a (mzone_zone3 _ _ (proj2 Hmap))) as MH. unfold zone3, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kHighMemBeg, kThreadObjSize, kPtrArrayResv, kNodesBlockSize, kStoreBlockSize in TI, TH, QI, QH, NI, NH, BI, BH, MI, MH.
clear - Ha Hx TH QH NH BH MH MZ. numconst. unfold kHighShadowBeg, kHighShadowEnd in *. try unfold T in *. try unfold Qb in *.
decompose [and or] Hx; clear Hx; zlia.
Qed.
Lemma zshadow_final : zshadow_ok B lyF rd'.
Proof.
pose proof lyF_eqs as (_ & _ & _ & _ & _ & _ & _ & _ & _ & E10 & E11 & _).
unfold zshadow_ok. replace (zero_shadow_ranges B lyF) with (zero_shadow_ranges B ly) by (img_try (unfold zero_shadow_ranges; rewrite E10, E11; img_refl)).
img_apply Forall_forall. intros r Hr i Hi. unfold shadow_of_addr. img_change (SHADOW_OFF + fst r / 8) with (shadow_addr (fst r)).
img_apply AGX; [img_try (eapply own_shadow_zero; [img_exact MA | img_exact Hr | img_exact Hi]) | | img_try (img_exact (proj1 (Forall_forall _ _) (am_zshadow _ _ _ _ MA) r Hr i Hi))].
pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). pose proof (lo_stk_ceil ly LY) as SC. pose proof map_facts as (M1 & M2 & M3 & _). pose proof map_zoneN as MZ.
unfold zero_shadow_ranges in Hr. destruct Hr as [<-|Hr].
-
cbn [fst snd] in *.
pose proof (Z.div_mod (ly_stk_lo ly) 8 ltac:(img_try (zlia))) as D1. pose proof (Z.div_mod (ly_stk_hi ly - ly_stk_lo ly) 8 ltac:(img_try (zlia))) as D2.
pose proof (Z.mod_pos_bound (ly_stk_hi ly - ly_stk_lo ly) 8 ltac:(img_try (zlia))) as B2.
assert (A8 : ly_stk_lo ly mod 8 = 0) by (img_try (unfold page_aligned in T5; apply Z.mod_divide in T5 as [q Hq]; [|img_try (zlia)]; rewrite Hq; replace (q * 4096) with (q * 512 * 8) by zlia; img_apply Z.mod_mul; zlia)).
img_apply Z_band.
+ unfold in_band_rw, shadow_addr. clear - Hi T1 T2 T4 T7 D1 D2 B2 A8 SC MZ. numconst. unfold SHADOW_OFF, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd. zlia.
+ apply Z.mod_divide in A8 as [q Hq]; [|img_try (zlia)].
pose proof (sh_sep (ly_stk_lo ly + 8 * i) ltac:(img_try (rewrite Hq; replace (q * 8 + 8 * i) with ((q + i) * 8) by zlia; img_apply Z.mod_mul; zlia)) ltac:(img_try (right; clear - Hi SC M2 D1 D2 B2 MZ; numconst; zlia))) as NS.
unfold shadow_addr in NS |- *. rewrite Hq in NS |- *. replace (q * 8 + 8 * i) with ((q + i) * 8) in NS by zlia. replace (q * 8) with (q * 8) by zlia.
rewrite Z.div_mul in NS by zlia. replace (q * 8 / 8) with q by (img_try (symmetry; img_apply Z.div_mul; zlia)). clear - NS MZ. zlia.
-
pose proof (proj1 (Forall_forall _ _) (aso_zshadow _ (am_syms _ _ _ _ MA)) r Hr) as (Z1 & Z2 & Z3 & Z4 & Z5).
assert (RI : 0x10000 <= fst r /\ fst r + snd r <= (0x5ff000 + D_1000)).
{ rewrite (ts_zsh B TS) in Hr. unfold Tfx_zero_shadow in Hr. cbn [In] in Hr. clear - Hr MZ.
destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd]; zlia. }
img_apply Z_lowsh. unfold shadow_addr. unfold kLowMemEnd in Z5.
pose proof (Z.div_mod (fst r) 8 ltac:(img_try (zlia))) as D1. pose proof (Z.div_mod (snd r) 8 ltac:(img_try (zlia))) as D2. pose proof (Z.mod_pos_bound (fst r) 8 ltac:(img_try (zlia))) as B1.
clear - Hi Z1 Z2 Z3 Z4 Z5 RI D1 D2 B1 MZ. unfold SHADOW_OFF. zlia.
Qed.
Lemma SEF : sec_extents lyF SF = sec_extents ly S ++ [(mb, MSv)].
Proof.
pose proof SF_parts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Rck & _). pose proof sizes_model as (_ & MS & _ & _ & _ & _ & _ & _ & KQ & KB & _).
unfold sec_extents at 1. rewrite Rck, flat_map_app. pose proof (sec_extents_le ly lyF S _ _ _ _ lyF_le WF) as SE. unfold sec_extents in SE at 1. rewrite SE.
cbn [flat_map]. rewrite KB, KQ, MS, lyF_sec, app_nil_r. img_refl.
Qed.
Lemma staticF : static_extents lyF = static_extents ly /\ vis0_zones lyF = vis0_zones ly /\ core_extents lyF = core_extents ly /\ owned_extents lyF = owned_extents ly.
Proof. clearP. unfold lyF, set_ly_sec, static_extents, vis0_zones, core_extents, owned_extents. cbn. repeat split; img_refl. Qed.
Lemma placed_finalG : Forall (zdisjoint (mb, MSv)) (static_extents ly ++ vis0_zones ly ++ sec_extents ly S) -> sec_placed lyF SF.
Proof.
clear GAPART. intros GAPART.
pose proof (am_placed _ _ _ _ MA) as [PL PD]. pose proof map_facts as (M1 & M2 & M3 & _). pose proof map_zoneN as MZ. pose proof staticF as (ES & _).
unfold sec_placed. rewrite SEF, ES. split.
- img_apply Forall_app. split; [img_try (img_exact PL)|]. constructor; [|img_try (img_apply Forall_nil)]. cbn [fst snd]. unfold page_aligned, in_app.
clear - M1 M2 M3 MZ. ceil. unfold zone3, TFX_IMG_LO, ASAN_CEIL, kLowShadowBeg, kHighMemBeg, TFX_IMG_END in *. repeat split; zlia.
- apply pairwise_app_inv in PD as (P1 & P2 & P3). img_apply pairwise_app; [img_try (img_apply pairwise_app; [img_exact P1 | cbn; split; [img_apply Forall_nil | img_exact I] |]) | img_try (img_exact P2) |].
+ intros x y Hx [<-|[]]. img_apply zdisjoint_sym. img_apply (proj1 (Forall_forall _ _) GAPART). rewrite !in_app_iff. right; right. img_exact Hx.
+ intros x y Hx Hy. apply in_app_iff in Hx as [Hx|[<-|[]]]; [img_try (img_exact (P3 x y Hx Hy))|].
img_apply (proj1 (Forall_forall _ _) GAPART). rewrite !in_app_iff. left. img_exact Hy.
Qed.
Lemma placed_final : sec_placed lyF SF.
Proof. img_exact (placed_finalG GAPART). Qed.
Lemma vis_old : forall lst, incl lst (ajunk B ly S) \/ incl lst (aareas S) \/ incl lst (aclient S) -> Forall (range_vis B lyF rd') lst.
Proof.
intros lst H. img_apply (Forall_range_vis_le B ly lyF _ lyF_le rd').
- destruct H as [H|[H|H]]; (eapply incl_Forall; [img_try (img_exact H)|]);
[img_try (img_exact (YF49.ajunk_lt B ly S _ _ _ _ WF (JUNKlt _ ly))) | img_try (img_exact (YF49.aareas_lt S _ _ _ _ WF)) | img_try (img_exact (YF49.aclient_lt S _ _ _ _ WF))].
- img_apply (Forall_range_vis_keep B ly rd0 rd' lst VIS_MONO).
destruct H as [H|[H|H]]; (eapply incl_Forall; [img_try (img_exact H)|]); [img_try (img_exact (am_junk _ _ _ _ MA)) | img_try (img_exact (am_areas _ _ _ _ MA)) | img_try (img_exact (am_client _ _ _ _ MA))].
Qed.
Lemma vis_map : forall e len, mb <= aeval B lyF e -> aeval B lyF e + len <= mb + MSv -> range_vis B lyF rd' (e, len).
Proof. intros e len H1 H2 i Hi. cbn [fst snd] in Hi |- *. img_apply apresent_vis. img_apply PRmap. clear - H1 H2 Hi. zlia. Qed.
Lemma resF_facts : Z.of_nat (length (st_sec_arr S)) + 1 <= (if grow then res + kPtrArrayEntriesPerCommit else res) <= kPtrArrayEntriesPerCommit /\
(grow = false -> idx < res).
Proof.
pose proof SF_parts as (_ & _ & _ & _ & _ & _ & _ & _ & Rarr & Rres & _).
pose proof (ws_reserved _ (wf_secondary _ _ _ _ _ (proj1 MP))) as WR. rewrite Rarr, Rres, length_app in WR. cbn [length] in WR.
pose proof len_arr as LA. pose proof Hres as [HRS _]. split; [img_try (zlia)|]. intros Hg. destruct (Z.eq_dec idx res) as [E|NE]; [|img_try (zlia)].
exfalso. pose proof (proj2 Hgrow E) as Hg'. rewrite Hg in Hg'. discriminate Hg'.
Qed.
Lemma vis_junk : Forall (range_vis B lyF rd') (ajunk B lyF SF).
Proof.
pose proof SF_parts as (Rreg & Rinit & Rcache & Rfr & Rqt & Rqg & Rfs & Rii & Rarr & Rres & Rdep & Rck & _).
pose proof sizes_model as (ND & MS & RS & RZ & FP & KN & KR & KE & KQ & KB & KST). pose proof lyF_sec as LS. pose proof lyF_eqs as (_ & _ & EQ & _).
pose proof size_facts as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10 & _). pose proof len_arr as LA. pose proof resF_facts as [RF1 RF2].
pose proof high_facts as (_ & _ & _ & _ & _ & _ & _ & _ & F9 & F10 & _).
assert (EV2 : forall d d', aeval B lyF (aoff (ASec (rS S) d) d') = mb + d + d') by (img_try (intros d d'; cbn [aeval aoff]; rewrite LS; zlia)).
unfold ajunk. rewrite Rck.
img_apply Forall_cons. { refine (proj1 (Forall_forall _ _) (vis_old [_] _) _ (or_introl eq_refl)). left. intros x [<-|[]]. unfold ajunk. left. img_refl. }
img_apply Forall_cons. { refine (proj1 (Forall_forall _ _) (vis_old [_] _) _ (or_introl eq_refl)). left. intros x [<-|[]]. unfold ajunk. right; left. img_refl. }
img_apply Forall_app; split; [img_try (img_apply vis_old; left; intros x Hx; unfold ajunk; do 2 right; img_apply in_app_iff; left; img_exact Hx)|].
img_apply Forall_app; split.
{ replace (flat_map (cache_junk SF) (zseq 1 31)) with (flat_map (cache_junk S) (zseq 1 31)) by (img_try (img_apply flat_map_ext; intros c; unfold cache_junk; rewrite Rinit, (Rcache c); img_refl)).
img_apply vis_old. left. intros x Hx. unfold ajunk. do 2 right. img_apply in_app_iff; right. img_apply in_app_iff; left. img_exact Hx. }
img_apply Forall_app; split.
{ rewrite flat_map_app. img_apply Forall_app; split.
- img_apply vis_old. left. intros x Hx. unfold ajunk. do 2 right. do 2 (img_apply in_app_iff; right). img_apply in_app_iff; left. img_exact Hx.
- cbn [flat_map]. rewrite app_nil_r. unfold chunk_junk. rewrite KR, KN, KST, KB, KE. unfold kChunkHeaderSize. cbn [sptr_exp app Z.eqb Pos.eqb].
repeat (img_apply Forall_cons; [img_try (img_apply vis_map; rewrite EV2; clear - Z1 Z3 Z7 Z10; zlia)|]). img_apply Forall_nil. }
img_apply Forall_app; split.
{ unfold sec_junk. rewrite Rarr, Rres, Rck, flat_map_app, length_app. cbn [length].
img_apply Forall_cons. { refine (proj1 (Forall_forall _ _) (vis_old [_] _) _ (or_introl eq_refl)). left. intros x [<-|[]]. unfold ajunk. do 2 right. do 3 (img_apply in_app_iff; right). img_apply in_app_iff; left. unfold sec_junk. left. img_refl. }
img_apply Forall_cons. { refine (proj1 (Forall_forall _ _) (vis_old [_] _) _ (or_introl eq_refl)). left. intros x [<-|[]]. unfold ajunk. do 2 right. do 3 (img_apply in_app_iff; right). img_apply in_app_iff; left. unfold sec_junk. right; left. img_refl. }
img_apply Forall_cons.
{
intros i Hi. cbn [fst snd aeval] in Hi |- *. rewrite EQ. replace (Z.of_nat (length (st_sec_arr S) + 1)) with (idx + 1) in Hi |- * by zlia.
destruct (Z_lt_le_dec (Qb + 8 * (idx + 1) + i) (Qb + 8 * res)) as [LO|HI].
- pose proof (proj1 (Forall_forall _ _) (am_junk _ _ _ _ MA) (AQ (8 * Z.of_nat (length (st_sec_arr S))), 8 * (st_sec_reserved S - Z.of_nat (length (st_sec_arr S))))
ltac:(img_try (unfold ajunk; do 2 right; do 3 (img_apply in_app_iff; right); img_apply in_app_iff; left; unfold sec_junk; do 2 right; left; img_refl))) as RV.
specialize (RV (8 + i)). cbn [fst snd aeval] in RV. rewrite <- Hres_def, LA in RV. img_apply VIS_MONO.
replace (Qb + 8 * (idx + 1) + i) with (ly_Q ly + 8 * idx + (8 + i)) by (img_try (unfold Qb; zlia)). img_apply RV. clear - Hi LO. unfold Qb in *. zlia.
- img_apply apresent_vis. destruct grow eqn:Eg; [| img_try (pose proof (RF2 eq_refl); exfalso; clear - Hi HI RF1 H; zlia)].
img_apply (PRq eq_refl). unfold QR. clear - Hi HI RF1 F9 F10. unfold kPtrArrayEntriesPerCommit, kPtrArrayResv in *. try unfold Qb in *. zlia. }
img_apply Forall_app; split.
- img_apply vis_old. left. intros x Hx. unfold ajunk. do 2 right. do 3 (img_apply in_app_iff; right). img_apply in_app_iff; left. unfold sec_junk. do 3 right. img_exact Hx.
- cbn [flat_map]. rewrite KB, app_nil_r. constructor; [|img_try (img_apply Forall_nil)]. img_apply vis_map; cbn [aeval]; rewrite LS; unfold kPage; clear - Z8; zlia. }
img_apply Forall_app; split.
{ img_apply vis_old. left. intros x Hx. unfold ajunk. do 2 right. do 4 (img_apply in_app_iff; right). img_apply in_app_iff; left.
unfold quar_junk, all_batches in *. rewrite Rqt, Rqg in Hx. img_exact Hx. }
img_apply Forall_app; split; [img_try (img_apply vis_old; left; intros x Hx; unfold ajunk; do 2 right; do 5 (img_apply in_app_iff; right); img_apply in_app_iff; left; img_exact Hx)|].
img_apply Forall_app; split; [img_try (img_apply vis_old; left; intros x Hx; unfold ajunk; do 2 right; do 6 (img_apply in_app_iff; right); img_apply in_app_iff; left; img_exact Hx)|].
rewrite (JUNK lyF ly). img_apply vis_old. left. intros x Hx. unfold ajunk. do 2 right. do 6 (img_apply in_app_iff; right). img_apply in_app_iff; right. img_exact Hx.
Qed.
Lemma vis_areas : Forall (range_vis B lyF rd') (aareas SF).
Proof.
pose proof SF_parts as (Rreg & Rinit & Rcache & Rfr & Rqt & Rqg & Rfs & Rii & Rarr & Rres & Rdep & Rck & _).
pose proof sizes_model as (ND & MS & RS & RZ & FP & KN & KR & KE & KQ & KB & KST). pose proof lyF_sec as LS. pose proof lyF_eqs as (_ & _ & EQ & _).
pose proof resF_facts as [RF1 RF2]. pose proof high_facts as (_ & _ & _ & _ & _ & _ & _ & _ & F9 & F10 & _). pose proof len_arr as LA.
unfold aareas. rewrite Rres, Rck, flat_map_app.
img_apply Forall_app; split.
{ unfold reg in Rreg |- *.
img_apply vis_old. right; left. intros x Hx. unfold aareas. img_apply in_app_iff. left. img_exact Hx. }
img_apply Forall_cons.
{ intros i Hi. cbn [fst snd aeval] in Hi |- *. rewrite EQ.
destruct (Z_lt_le_dec i (8 * res)) as [LO|HI].
- pose proof (proj1 (Forall_forall _ _) (am_areas _ _ _ _ MA) (AQ 0, 8 * st_sec_reserved S) ltac:(img_try (unfold aareas; img_apply in_app_iff; right; left; img_refl))) as RV.
specialize (RV i). cbn [fst snd aeval] in RV. rewrite <- Hres_def in RV. img_apply VIS_MONO. img_apply RV. clear - Hi LO. zlia.
- img_apply apresent_vis. destruct grow eqn:Eg; [| img_try (exfalso; clear - Hi HI; zlia)].
img_apply (PRq eq_refl). unfold QR. clear - Hi HI RF1 F9 F10 LA. unfold kPtrArrayEntriesPerCommit, kPtrArrayResv in *. try unfold Qb in *. zlia. }
img_apply Forall_app; split.
{ img_apply Forall_app; split.
- img_apply vis_old. right; left. intros x Hx. unfold aareas. img_apply in_app_iff; right. img_apply in_app_iff; right. img_apply in_app_iff; left. img_exact Hx.
- cbn [flat_map]. rewrite KB, KQ, MS, app_nil_r. constructor; [|img_try (img_apply Forall_nil)]. img_apply vis_map; cbn [aeval]; rewrite LS; zlia. }
img_apply vis_old. right; left. intros x Hx. unfold aareas. img_apply in_app_iff; right. img_apply in_app_iff; right. img_apply in_app_iff; right. img_exact Hx.
Qed.
Lemma vis_client : Forall (range_vis B lyF rd') (aclient SF).
Proof.
pose proof SF_parts as (Rreg & Rinit & Rcache & Rfr & Rqt & Rqg & Rfs & Rii & Rarr & Rres & Rdep & Rck & _).
pose proof sizes_model as (ND & MS & RS & RZ & FP & KN & KR & KE & KQ & KB & KST). pose proof lyF_sec as LS.
pose proof size_facts as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10 & _).
unfold aclient. rewrite Rfr, Rck, flat_map_app.
img_apply Forall_app; split; [img_try (img_apply Forall_app; split)|].
- img_apply vis_old. do 2 right. intros x Hx. unfold aclient. img_apply in_app_iff. left. img_exact Hx.
- cbn [flat_map]. rewrite app_nil_r. unfold chunk_user. rewrite KST, KN. unfold ck_user. rewrite KB. img_change (YG00.ck_rz KSc) with (ck_rz KSc). rewrite KR. cbn [padd sptr_exp].
constructor; [|img_try (img_apply Forall_nil)]. img_apply vis_map; cbn [aeval]; rewrite LS; clear - Z1 Z3 Z7 Z10; zlia.
- img_apply vis_old. do 2 right. intros x Hx. unfold aclient. img_apply in_app_iff. right. img_exact Hx.
Qed.
Lemma depot_okF : forall s1 s2 (rd : reader), st_depot s1 = st_depot s2 -> depot_ok B ly rd s1 -> depot_ok B lyF rd s2.
Proof.
clearP. intros s1 s2 rd E. pose proof lyF_eqs as (_ & _ & _ & _ & _ & _ & E7 & _ & _ & _ & _ & _ & E13 & _).
unfold depot_ok, depot_ids, depot_traces. rewrite E, E7, E13. img_exact (fun H => H).
Qed.
Lemma ARm_final : ARm B lyF SF rd'.
Proof.
pose proof MAF as MF. destruct MF as [_ Mun Msy Mly _ _ Mcow _ _ _ _ _ _ _ _ _ _ Mts Msi].
pose proof SF_parts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Rdep & _).
constructor.
- img_exact (proj1 MP).
- img_exact Mun.
- img_exact Msy.
- img_exact Mly.
- img_exact placed_final.
- img_exact const_finalF.
- img_exact Mcow.
- img_exact cells_final.
- img_exact fa_final.
- img_exact flags_final.
- img_apply (depot_okF (depot_after z tr S)); [img_try (rewrite Rdep; unfold depot_after; destruct (z =? 0); img_refl) | img_try (img_exact (proj1 (proj2 depot_final)))].
- img_exact shadow_final.
- img_exact zshadow_final.
- img_exact vis_junk.
- img_exact vis_areas.
- img_exact vis_client.
- img_exact zero_final.
- img_exact Mts.
-   img_exact Msi.
Qed.
Lemma ahs_final : ahs B lyF SF (w_H Wz) mem'.
Proof.
pose proof HAR as (_ & _ & _ & _ & [HS0 HZ0]). pose proof SF_parts as (_ & _ & _ & Rfr & _ & _ & _ & _ & _ & _ & _ & Rck & _).
pose proof staticF as (ES & EV0 & _). pose proof lyF_eqs as (_ & _ & _ & _ & _ & E6 & _ & _ & _ & _ & _ & _ & _ & _ & _ & E16).
split.
- intros a Ha NC HV. img_apply (BANDKEEP a Ha). img_apply (HS0 a Ha).
+ intros CL. img_apply NC. destruct CL as [(k & Hk & Hst & Hr) | (cp & Hcp & Hr)].
* left. exists k. split; [img_try (rewrite Rck; img_apply in_app_iff; left; img_exact Hk) | img_try (split; [img_exact Hst|])].
unfold ck_user. rewrite (sptr_addr_le B ly lyF (length (st_secs S)) _ lyF_le (YF49.padd_lt S _ _ (YF49.chunk_lt S _ _ _ _ WF k Hk))). img_exact Hr.
* right. exists cp. split; [unfold frames in Hcp |- *; cbn; img_exact Hcp|]. unfold frame_addr in Hr |- *. rewrite E6. img_exact Hr.
+ destruct HV as [Hh|Hv]; [img_try (left) | img_try (right)].
* destruct (w_H W (YG0u.w64 a)) eqn:E; [img_refl|]. rewrite (MONf _ E) in Hh. discriminate Hh.
* unfold in_vis0 in Hv |- *. rewrite E16 in Hv. img_exact Hv.
- intros g Hg Happ HF.
unfold hfree in HF. rewrite SEF, ES, EV0 in HF. rewrite !app_assoc in HF. apply Forall_app in HF as [HF1 HF2].
pose proof (Forall_inv HF2) as X. cbn [fst snd] in X.
assert (HF0 : hfree ly S g) by (img_try (unfold hfree; rewrite !app_assoc; img_exact HF1)). rewrite <- (HZ0 g Hg Happ HF0). img_exact (ZKEEP g Hg Happ X).
Qed.
Lemma sec_live_final : sec_live_bytes SF = sec_live_bytes S + MSv.
Proof.
pose proof SF_parts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Rck & _). pose proof sizes_model as (_ & MS & _ & _ & _ & _ & _ & _ & KQ & KB & _).
unfold sec_live_bytes. rewrite Rck, fold_right_app. cbn [fold_right]. rewrite KB, KQ, MS.
assert (G : forall l a, fold_right (fun k acc => match ck_beg k with PSec _ _ => sec_map_size (ck_req k) + acc | _ => acc end) a l =
fold_right (fun k acc => match ck_beg k with PSec _ _ => sec_map_size (ck_req k) + acc | _ => acc end) 0 l + a).
{ clear. induction l as [|k t IH]; intros a; cbn [fold_right]; [img_try (zlia)|]. rewrite (IH a), (IH 0). destruct (ck_beg k); zlia. }
rewrite G. zlia.
Qed.
Theorem AR_transport : AR tfxsegs B lyF SF Wz mem' mdf.
Proof.
pose proof HAR as (_ & _ & BUD & _ & _). pose proof SF_parts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Rsecs & Rnev & _).
split; [img_try (img_exact ARm_final)|]. split; [img_try (img_exact LEDf)|]. split; [|img_try (split; [img_exact MWf | img_exact ahs_final])].
pose proof (SH_hull mb) as (_ & _ & H3 & _). pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & Z9 & _).
pose proof (Z.div_mod MSv 8 ltac:(img_try (zlia))) as DM8. pose proof (Z.mod_pos_bound MSv 8 ltac:(img_try (zlia))) as MB8.
pose proof ABf as AB. pose proof sec_live_final as SLF. pose proof HINC as HINC'. pose proof AMAP as AMAP'. pose proof AHULL as AHULL'. pose proof SEF as SEF'.
destruct BUD as [BUD PIN]; split;
[ unfold abudget, sec_hulls in BUD |- *; rewrite Rnev, Rsecs, sec_hulls_app1, SLF, AB; cbn [sm_len]  ; clear - BUD H3 Z8 DM8 MB8; unfold EV_A, MALLOC_MAX in *; destruct grow; zlia
| intros e He; rewrite SEF' in He; apply in_app_iff in He as [He|[He|[]]];
[ img_try (split; [img_exact (HINC' _ (proj1 (PIN e He))) | img_exact (HINC' _ (proj2 (PIN e He)))])
| img_try (rewrite <- He; split; [cbn [fst snd]; img_exact AMAP' | unfold YG0u.shull; cbn [fst snd]; img_exact AHULL']) ] ].
Qed.
End d0.
Definition S_AR_final {imgk : img} := AR_transport.
End c0.
End b0.
