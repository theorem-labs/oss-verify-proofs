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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK0v YK13 YQ0k YA05 YA09 YG0b YG0j YG0l.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF48 YF49 YF70 YF71 YF72 YF73 YF74 YF0h YF7o YF7p YF7q YF7a YF7b YF7c YF7g YF7h YF7d YF7e YF7i YF7j YF7k YF7l YF7m YF7n YF7r YF7s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF05.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF75 YF76 YF7u YF40.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YA00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF48.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG0i.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
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
Local Abbreviation ARg f := (f idx res Hidx) (only parsing).
Local Abbreviation tr_length := (ARg ((AR1 (@YF7f.tr_length)) ch)).
Local Abbreviation ARh f := (f idx res LY IMG Hidx Hres) (only parsing).
Local Abbreviation high_facts := (ARh (AR1 (@YF7f.high_facts _))).
Local Abbreviation stack_ivs := (@YF7f.stack_ivs _ ly regs0 idx res LY Hsp Hidx Hres).
Local Abbreviation HCX := (@YF7f.HCX _ ly LY).
Hypothesis Hpres0 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem0 a.
Hypothesis Hmap : mb mod 4096 = 0 /\ mzone mb MSv.
Hypothesis Hmap_apart :
zdisjoint (mb, MSv) (T, kThreadObjSize) /\ zdisjoint (mb, MSv) (ly_C ly, kCtxMapSize) /\
zdisjoint (mb, MSv) (ly_prim ly, kPrimResvSize) /\ zdisjoint (mb, MSv) (Qb, kPtrArrayResv) /\
zdisjoint (mb, MSv) (ly_NB ly, kNodesBlockSize) /\ zdisjoint (mb, MSv) (ly_SB ly, kStoreBlockSize) /\
zdisjoint (mb, MSv) (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly).
Local Abbreviation AR4 f := (f n idx res mb) (only parsing).
Local Abbreviation AR5 f := (f Nrange Hidx Hres Hmap) (only parsing).
Local Abbreviation map_facts := (AR5 (AR4 (AR1 (@YF7f.map_facts _)))).
Local Abbreviation map_zone := ((AR4 (AR1 (@YF7f.map_zone _))) Nrange Hidx Hmap).
Local Abbreviation map_zoneN := (AR5 (AR4 (AR1 (@YF7f.map_zoneN _)))).
Local Abbreviation map_in_band := ((AR4 (AR1 (@YF7f.map_in_band _))) Nrange Hidx Hmap).
Local Abbreviation map_off_img := (@YF7f.map_off_img _ imgk n mb Hmap).
Local Abbreviation WINT := (@YF7f.WINT ly).
Local Abbreviation WINI := (@YF7f.WINI n imgk).
Local Abbreviation WINM := (@YF7f.WINM ly n idx mb).
Local Abbreviation ARf f := (AR1 f n idx mb) (only parsing).
Local Abbreviation WIN := (ARf (@YF7f.WIN)).
Local Abbreviation WINN := (AR1 (@YF7f.WINN)).
Local Abbreviation ARp f := (AR1 f n) (only parsing).
Local Abbreviation WINP := (ARp (@YF7f.WINP)).
Local Abbreviation WINP_WIN := (ARf (@YF7f.WINP_WIN)).
Local Abbreviation WIN1P := (ARp (@YF7f.WIN1P)).
Local Abbreviation WIN1 := (ARf (@YF7f.WIN1)).
Local Abbreviation WIN1P_WINP := ((AR4 (AR1 (@YF7f.WIN1P_WINP))) Hidx).
Local Abbreviation WIN1_WIN := ((AR4 (AR1 (@YF7f.WIN1_WIN))) Hidx).
Local Abbreviation WIN1P_WIN1 := (ARf (@YF7f.WIN1P_WIN1)).
Local Abbreviation LGv_range := (@YF7f.LGv_range n Nrange).
Local Abbreviation BSLv_range := ((AR4 (AR1 (@YF7f.BSLv_range))) Nrange Hidx).
Local Abbreviation WSKELP := (@YF7f.WSKELP imgk).
Local Abbreviation WSKEL1P := (@YF7f.WSKEL1P imgk).
Local Abbreviation WMAP := (@YF7f.WMAP).
Local Abbreviation WSKEL := (@YF7f.WSKEL imgk).
Local Abbreviation WSKEL1 := (@YF7f.WSKEL1 imgk).
Local Abbreviation win_sub := (@YF7f.win_sub).
Local Abbreviation ARk f := (f idx res mb Hidx) (only parsing).
Local Abbreviation win_sub_sound := ((ARk (@YF7f.win_sub_sound ly regs0)) Hres).
Local Abbreviation in_win := (@YF7f.in_win).
Local Abbreviation ARa f := (AR0 f LY IMG) (only parsing).
Local Abbreviation ARd f := (f Nrange Hidx Hres) (only parsing).
Local Abbreviation WSKELP_WINP := (ARd (ARa (AR1 (@YF7f.WSKELP_WINP _)))).
Local Abbreviation WSKEL1P_WIN1P := (ARd (ARa (AR1 (@YF7f.WSKEL1P_WIN1P _)))).
Local Abbreviation WMAP_WINM := (AR5 (ARa (AR1 (@YF7f.WMAP_WINM _)))).
Local Abbreviation WSKEL_WIN := (AR5 (ARa (AR1 (@YF7f.WSKEL_WIN _)))).
Local Abbreviation WSKEL1_WIN1 := (AR5 (ARa (AR1 (@YF7f.WSKEL1_WIN1 _)))).
Local Abbreviation windows_in := ((ARk (@YF7f.windows_in ly regs0)) Hres).
Local Abbreviation windows_WINP := (ARd (ARa (AR1 (@YF7f.windows_WINP _)))).
Local Abbreviation windows_WIN1P := (ARd (ARa (AR1 (@YF7f.windows_WIN1P _)))).
Local Abbreviation windows_WIN := (AR5 (ARa (AR1 (@YF7f.windows_WIN _)))).
Local Abbreviation windows_WIN1 := (AR5 (ARa (AR1 (@YF7f.windows_WIN1 _)))).
Local Abbreviation frame_WIN1P := (ARd (ARa (AR1 (@YF7f.frame_WIN1P _)))).
Local Abbreviation frame_WIN1 := (AR5 (ARa (AR1 (@YF7f.frame_WIN1 _)))).
Local Abbreviation AR2 f := (f LY IMG Hsp Nrange Hidx Hres) (only parsing).
Local Abbreviation WINP_not_high := (AR2 (AR4 (AR1 (@YF7f.WINP_not_high _)))).
Local Abbreviation ARj f := (AR2 f Hmap) (only parsing).
Local Abbreviation WIN_not_high := (ARj (AR4 (AR1 (@YF7f.WIN_not_high _)))).
Variables (mat0 : list word).
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 (0x53108 + D_2c4)) mem0 (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis U1 : tfx_unwind_spec.
Local Abbreviation all_disjoint_of_forall := (@YF7f.all_disjoint_of_forall).
Local Abbreviation img_rw_writable := (ARk (AR1 (@YF7f.img_rw_writable))).
Local Abbreviation ARe f := (f imgk W ly) (only parsing).
Local Abbreviation kept_of_frame := (ARk ((ARe (@YF7f.kept_of_frame)) regs0)).
Local Abbreviation SKEL_TAIL := (@YF7f.SKEL_TAIL imgk).
Local Abbreviation blocks_facts := (@YF7f.blocks_facts _ imgk ly LY IMG).
Local Abbreviation off_T := (ARh (AR1 (@YF7f.off_T _))).
Local Abbreviation off_C := (ARh (AR1 (@YF7f.off_C _))).
Local Abbreviation off_Q := (ARh (AR1 (@YF7f.off_Q _))).
Local Abbreviation off_NB := (@YF7f.off_NB _ imgk ly LY IMG).
Local Abbreviation off_SB := (@YF7f.off_SB _ imgk ly LY IMG).
Local Abbreviation off_shadow := (ARk (AR1 (@YF7f.off_shadow))).
Ltac off_by tac :=
first [ img_apply off_img_high; tac | img_apply off_T; tac | img_apply off_C; tac | img_apply off_Q; tac | img_apply off_NB; tac | img_apply off_SB; tac
| img_apply map_off_img; tac | img_apply off_shadow; tac
| unfold off_img; unfold TFX_IMG_LO; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; tac ].
Local Abbreviation DZONE := (@YF7f.DZONE imgk ly).
Variable DPOST : Z -> (word -> option byte) -> Prop.
Local Abbreviation AR6 f := (AR2 f Hmap Hmap_apart) (only parsing).
Local Abbreviation DZONE_disj := (AR6 (AR4 (AR1 (@YF7f.DZONE_disj _)))).
Local Abbreviation RFACTS := (AR1 (@YF7f.RFACTS)).
Local Abbreviation zone_lit := ((AR1 (@YF7f.zone_lit _)) LY IMG Hsp).
Local Abbreviation zone_irw := ((AR1 (@YF7f.zone_irw _)) LY IMG Hsp).
Local Abbreviation zone_T := ((AR1 (@YF7f.zone_T _)) idx res LY IMG Hsp Hidx Hres).
Local Abbreviation zone_C := ((AR1 (@YF7f.zone_C _)) idx res LY IMG Hsp Hidx Hres).
Local Abbreviation tail_ext_ok := (AR2 (AR0 (AR1 (@YF7f.tail_ext_ok _)))).
Local Abbreviation RFACTS_map := ((AR5 ((AR4 (AR1 (@YF7f.RFACTS_map _))) LY IMG)) Hmap_apart).
Local Abbreviation AR3 f := (f imgk W ly regs0 mem0) (only parsing).
Local Abbreviation ARi f := (AR3 f md0) (only parsing).
Local Abbreviation at_ST := (AR0 (ARi (@YF7f.at_ST _))).
Local Abbreviation memset_stretch := ((AR5 ((AR4 (ARi (@YF7f.memset_stretch _ _))) Hsp)) Hmap_apart mat0 DPOST).
Ltac clearM := try clear DPOST; try clear Hmap_apart; try clear Hmap.
Local Abbreviation AR8 f := (AR1 f mem0) (only parsing).
Local Abbreviation at_S := (AR0 (AR8 (@YF7f.at_S _))).
Local Abbreviation at_N := (AR0 (AR8 (@YF7f.at_N _))).
Local Abbreviation at_RETS := ((AR8 (@YF7f.at_RETS _)) ch).
Local Abbreviation pstable := (@YF7f.pstable).
Local Abbreviation stack_shaped := (@YF7f.stack_shaped).
Local Abbreviation window_present := (ARg (AR1 (@YF7f.window_present))).
Local Abbreviation stack_present_of := ((AR0 (AR1 (@YF7f.stack_present_of _))) LY Hsp Hidx).
Local Abbreviation mid_not_WIN1P := (AR2 (AR4 (AR1 (@YF7f.mid_not_WIN1P _)))).
Local Abbreviation mid_not_WIN1 := (ARj (AR4 (AR1 (@YF7f.mid_not_WIN1 _)))).
Local Abbreviation wins_ok := (@YF7f.wins_ok).
Local Abbreviation at_S_run_gen := ((AR0 (AR8 (@YF7f.at_S_run_gen _ _))) LY Hsp Hidx).
Local Abbreviation at_S_run_ecall_gen := ((AR0 (AR8 (@YF7f.at_S_run_ecall_gen _ _))) LY Hsp Hidx).
Local Abbreviation at_S_runP := (AR2 (AR0 (AR8 (@YF7f.at_S_runP _ _)))).
Local Abbreviation at_S_runM := (ARj (AR0 (AR8 (@YF7f.at_S_runM _ _)))).
Local Abbreviation at_S_run_ecallP := (AR2 (AR0 (AR8 (@YF7f.at_S_run_ecallP _ _)))).
Local Abbreviation at_S_run_ecallM := (ARj (AR0 (AR8 (@YF7f.at_S_run_ecallM _ _)))).
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
Local Abbreviation at_S_ret := (ARd ((AR0 (AR8 (@YF7f.at_S_ret _))) Htp Hra Hsp)).
Local Abbreviation kept_of_frame2 := (ARg (AR1 (@YF7f.kept_of_frame2))).
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
Local Abbreviation ARb f := (f DPOST B S) (only parsing).
Local Abbreviation vis_present := ((ARb (ARg (AR3 (@YF7o.vis_present _)))) HARm).
Local Abbreviation in_thread_junk := (@YF7o.in_thread_junk ly B S).
Local Abbreviation in_sec_junk := (@YF7o.in_sec_junk ly B S).
Local Abbreviation in_as_junk := (@YF7o.in_as_junk ly B S).
Local Abbreviation junk_word := ((ARb (ARh (AR3 (@YF7o.junk_word _)))) HARm).
Local Abbreviation cell_sym := ((ARe (@YF7o.cell_sym _)) mem0 B S TS HARm).
Local Abbreviation cell_lit := ((ARe (@YF7o.cell_lit _)) mem0 B S TS HARm).
Local Abbreviation ARo f := (f B S HARm) (only parsing).
Local Abbreviation cell_state := (ARo ((ARe (@YF7o.cell_state _)) mem0)).
Local Abbreviation In_acells_sec := (@YF7o.In_acells_sec ly B S).
Local Abbreviation sec_vals := ((ARe (@YF7o.sec_vals _)) mem0 idx res B S TS HARm Hidx_def Hres_def).
Local Abbreviation unwinding_val := (ARo ((ARe (@YF7o.unwinding_val _)) mem0)).
Local Abbreviation rw_writable := ((ARg (AR1 (@YF7o.rw_writable))) DPOST S).
Local Abbreviation val_mem_mod8 := ((ARg (AR3 (@YF7o.val_mem_mod8))) DPOST S).
Local Abbreviation chunk_lit := (AR0 (AR3 (@YF7o.chunk_lit))).
Local Abbreviation chunk_lit_at := (AR0 (AR3 (@YF7o.chunk_lit_at))).
Local Abbreviation chunk_atom := ((AR0 (AR3 (@YF7o.chunk_atom))) Hidx DPOST S).
Local Abbreviation ARc f := (ARb f TS HTSD HARm Hidx_def Hres_def Hj0 Hj1 Hj2 Hj3 Hj4 Hj5 Hj9 Hj6 Hj7 Hj8 Hi1 Hi2 Hi3) (only parsing).
Local Abbreviation SREG0_ok := (ARc ((AR2 (AR0 (AR3 (@YF7p.SREG0_ok _)))) Hpres0)).
Local Abbreviation PAIRS_ok := ((AR2 (AR0 (AR3 (@YF7q.PAIRS_ok _)))) DPOST S).
Local Abbreviation ARl f := (ARa f Hn Hsp) (only parsing).
Local Abbreviation FACTS_ok := ((ARd (ARl (AR3 (@YF7q.FACTS_ok _)))) DPOST S).
Local Abbreviation SEED_ok := (ARc ((ARd (ARl (AR3 (@YF7q.SEED_ok _ _)))) Hpres0)).
Local Abbreviation PBUF := ((ARe (@YF7a.PBUF)) regs0 ch).
Local Abbreviation AR9 f := (f n ch idx res mb) (only parsing).
Local Abbreviation PBUF_stableP := (AR2 (AR9 ((ARe (@YF7a.PBUF_stableP _)) regs0))).
Local Abbreviation PBUF_stableM := (ARj (AR9 ((ARe (@YF7a.PBUF_stableM _)) regs0))).
Local Abbreviation seg0 := (ARc ((ARd ((ARa (ARi (@YF7a.seg0 _ _))) Hn Htp Hra4096 Hsp Hch)) Hpres0 mat0 U1)).
Local Abbreviation seg1 := (ARd (ARl (ARi (@YF7b.seg1 _ _)))).
Local Abbreviation PNULL := ((ARe (@YF7c.PNULL)) regs0 ch).
Local Abbreviation PNULLX := ((ARe (@YF7c.PNULLX)) regs0 n ch idx res).
Local Abbreviation tail_lits_apart := (@YF7c.tail_lits_apart imgk).
Local Abbreviation segR := ((ARb (ARd ((ARa (ARi (@YF7c.segR _ _))) Htp Hra Hsp))) TS HARm).
Local Abbreviation appregs := (@YF7g.appregs).
Local Abbreviation st_ok_appregs := (@YF7g.st_ok_appregs _ imgk).
Local Abbreviation at_S_app := (AR0 (AR8 (@YF7g.at_S_app _))).
Local Abbreviation WIN1N := (ARp (@YF7g.WIN1N)).
Local Abbreviation WINPN := (ARp (@YF7g.WINPN)).
Local Abbreviation WSKEL1N := (@YF7g.WSKEL1N imgk).
Local Abbreviation WIN1N_WINPN := ((AR4 (AR1 (@YF7g.WIN1N_WINPN))) Hidx).
Local Abbreviation windows_WIN1N := (ARd (ARa (AR1 (@YF7g.windows_WIN1N _)))).
Local Abbreviation mid_not_WIN1N := (AR2 (AR4 (AR1 (@YF7g.mid_not_WIN1N _)))).
Local Abbreviation at_S_runN := (AR2 (AR0 (AR8 (@YF7g.at_S_runN _ _)))).
Local Abbreviation PBUF_stableN := (AR2 (AR9 ((ARe (@YF7g.PBUF_stableN _)) regs0))).
Local Abbreviation at_S_val := (AR0 (AR8 (@YF7g.at_S_val _))).
Local Abbreviation memset_stretchW := ((ARd ((ARi (@YF7g.memset_stretchW _)) n idx res Hsp)) mat0 DPOST S).
Local Abbreviation at_S_memset := ((ARd ((AR0 (ARi (@YF7g.at_S_memset _))) Hsp)) mat0 DPOST S).
Local Abbreviation WIN1T := (ARf (@YF7g.WIN1T)).
Local Abbreviation WIN1T_WIN := (AR5 (AR4 (AR1 (@YF7g.WIN1T_WIN _)))).
Local Abbreviation windows_WIN1T := (AR5 (ARa (AR1 (@YF7g.windows_WIN1T _)))).
Local Abbreviation WIN1T_WIN1_aux := (AR5 (AR4 (AR1 (@YF7g.WIN1T_WIN1_aux _)))).
Local Abbreviation mid_not_WIN1T := (ARj (AR4 (AR1 (@YF7g.mid_not_WIN1T _)))).
Local Abbreviation at_S_runT := (ARj (AR0 (AR8 (@YF7g.at_S_runT _ _)))).
Local Abbreviation at_S_run_ecallT := (ARj (AR0 (AR8 (@YF7g.at_S_run_ecallT _ _)))).
Local Abbreviation PBUFW := ((AR1 (@YF7g.PBUFW)) ch).
Local Abbreviation PBUFW_stableT := (ARj (AR9 (AR1 (@YF7g.PBUFW_stableT _)))).
Local Abbreviation WIN1S := (ARf (@YF7h.WIN1S)).
Local Abbreviation WSKEL1S := (@YF7h.WSKEL1S imgk).
Local Abbreviation WIN1S_WIN1T := (ARf (@YF7h.WIN1S_WIN1T)).
Local Abbreviation WIN1S_WIN := (AR5 (AR4 (AR1 (@YF7h.WIN1S_WIN _)))).
Local Abbreviation windows_WIN1S := (AR5 (ARa (AR1 (@YF7h.windows_WIN1S _)))).
Local Abbreviation mid_not_WIN1S := (ARj (AR4 (AR1 (@YF7h.mid_not_WIN1S _)))).
Local Abbreviation at_S_runS := (ARj (AR0 (AR8 (@YF7h.at_S_runS _ _)))).
Local Abbreviation at_S_run_ecallS := (ARj (AR0 (AR8 (@YF7h.at_S_run_ecallS _ _)))).
Local Abbreviation brun := (@YF7h.brun).
Local Abbreviation run_ok := (@YF7h.run_ok n mb).
Local Abbreviation PS := ((ARp (@YF7h.PS)) ch mb).
Local Abbreviation runs_not_WIN1S := (AR6 (AR4 (AR1 (@YF7h.runs_not_WIN1S _)))).
Local Abbreviation runs_not_stack := ((AR5 ((AR4 (AR1 (@YF7h.runs_not_stack _))) LY Hsp)) Hmap_apart).
Local Abbreviation PS_stable := (AR6 (AR9 (AR1 (@YF7h.PS_stable _)))).
Local Abbreviation cut1 := (@YF7h.cut1).
Local Abbreviation cut := (@YF7h.cut).
Local Abbreviation cut_sound := ((AR5 (AR4 (AR8 (@YF7h.cut_sound _)))) DPOST S).
Local Abbreviation cut_ok := ((AR4 (@YF7h.cut_ok ly regs0 mem0)) Hidx Hres DPOST S).
Local Abbreviation at_S_memsetS := ((AR5 ((AR0 (ARi (@YF7h.at_S_memsetS _ _))) LY Hsp)) Hmap_apart mat0 DPOST S).
Local Abbreviation skel_okb := (@YF7h.skel_okb imgk).
Local Abbreviation skel_cases := ((ARg (@YF7h.skel_cases imgk)) Hres S Hidx_def Hres_def).
Local Abbreviation AR7 f := (f DPOST S Hidx_def Hres_def) (only parsing).
Local Abbreviation skel_apart := (AR7 (AR6 (AR0 (AR8 (@YF7h.skel_apart _))))).
Local Abbreviation skel_u64 := (AR7 (ARj (AR0 (AR8 (@YF7h.skel_u64 _))))).
Local Abbreviation memset_ext_of_skel := (AR7 (AR6 (AR0 (AR8 (@YF7h.memset_ext_of_skel _))))).
Local Abbreviation memset_u64_of_skel := (AR7 (ARj (AR0 (AR8 (@YF7h.memset_u64_of_skel _))))).
Local Abbreviation WIN1R := ((ARp (@YF7h.WIN1R)) mb).
Local Abbreviation WSKEL1R := (@YF7h.WSKEL1R imgk).
Local Abbreviation WIN1R_WIN1S := (ARf (@YF7h.WIN1R_WIN1S)).
Local Abbreviation WIN1R_WIN := (AR5 (AR4 (AR1 (@YF7h.WIN1R_WIN _)))).
Local Abbreviation windows_WIN1R := (AR5 (ARa (AR1 (@YF7h.windows_WIN1R _)))).
Local Abbreviation mid_not_WIN1R := (ARj (AR4 (AR1 (@YF7h.mid_not_WIN1R _)))).
Local Abbreviation at_S_runR := (ARj (AR0 (AR8 (@YF7h.at_S_runR _ _)))).
Local Abbreviation at_S_run_ecallR := (ARj (AR0 (AR8 (@YF7h.at_S_run_ecallR _ _)))).
Local Abbreviation PSR := ((ARp (@YF7h.PSR)) ch mb).
Local Abbreviation rstable := ((ARp (@YF7h.rstable)) mb).
Local Abbreviation rstable_true := ((ARp (@YF7h.rstable_true)) mb).
Local Abbreviation PSR_stable := (AR6 (AR9 (AR1 (@YF7h.PSR_stable _)))).
Local Abbreviation QSP := (@YF7h.QSP imgk ly idx).
Local Abbreviation QS_not_WIN1R := (AR6 (AR4 (AR1 (@YF7h.QS_not_WIN1R _)))).
Local Abbreviation QSP_rstable := (AR6 (AR4 (AR1 (@YF7h.QSP_rstable _)))).
Local Abbreviation at_S_memsetSR := ((AR5 ((AR0 (ARi (@YF7h.at_S_memsetSR _ _))) LY Hsp)) Hmap_apart mat0 DPOST S).
Local Abbreviation chunk_eqb := (@YF7h.chunk_eqb imgk).
Local Abbreviation chunk_eqb_eq := ((ARg (@YF7h.chunk_eqb_eq imgk)) Hres S Hidx_def Hres_def).
Local Abbreviation subregionb := (@YF7h.subregionb imgk).
Local Abbreviation subregionb_sound := (AR7 ((ARg (AR8 (@YF7h.subregionb_sound))) Hres)).
Local Abbreviation submemb := (@YF7h.submemb imgk).
Local Abbreviation submemb_sound := (AR7 ((ARg (AR8 (@YF7h.submemb_sound))) Hres)).
Local Abbreviation at_S_submem := (AR7 ((AR0 (AR8 (@YF7h.at_S_submem _))) Hidx Hres)).
Local Abbreviation at_S_addreg := (AR0 (AR8 (@YF7h.at_S_addreg _))).
Local Abbreviation PSR_runs := (AR0 (AR8 (@YF7d.PSR_runs _))).
Local Abbreviation place_WIN := (ARf (@YF7d.place_WIN)).
Local Abbreviation SH0 := (@YF7d.SH0 n mb).
Local Abbreviation SH1 := (@YF7d.SH1 n mb).
Local Abbreviation SH2 := (@YF7d.SH2 n mb).
Local Abbreviation SH_ok := (AR5 (AR4 (AR1 (@YF7d.SH_ok _)))).
Local Abbreviation segG1 := (AR7 ((AR6 (AR0 (ARi (@YF7d.segG1 _ _)))) mat0)).
Local Abbreviation RX_stableS := (ARf (@YF7e.RX_stableS)).
Local Abbreviation rstable_and := ((ARp (@YF7e.rstable_and)) mb).
Local Abbreviation pstable_and := (@YF7e.pstable_and).
Local Abbreviation PSR_stableS' := (AR6 (AR9 (AR1 (@YF7e.PSR_stableS' _)))).
Local Abbreviation pairwise_disjoint_map := (@YF7e.pairwise_disjoint_map).
Local Abbreviation at_S_setchunks := (AR0 (AR8 (@YF7e.at_S_setchunks _))).
Local Abbreviation chunk_ok_CVal_eqv := (@YF7e.chunk_ok_CVal_eqv imgk).
Local Abbreviation RES2T_ne := ((AR0 (AR1 (@YF7e.RES2T_ne))) Hidx Hres).
Local Abbreviation RES2T_eq := ((AR0 (AR1 (@YF7e.RES2T_eq))) Hidx Hres).
Local Abbreviation sv_denot_eq_of_U := (AR0 (AR1 (@YF7e.sv_denot_eq_of_U))).
Local Abbreviation skel_apart_QS := (AR7 (AR6 (AR0 (AR8 (@YF7e.skel_apart_QS _))))).
Local Abbreviation QSPX := (@YF7e.QSPX imgk ly idx).
Local Abbreviation segNE := (AR7 (AR6 (AR0 (AR8 (@YF7e.segNE _ _))))).
Local Abbreviation segEQa := (AR6 (AR0 (AR8 (@YF7e.segEQa _ _)))).
Local Abbreviation zev_SAlu := (@YF7e.zev_SAlu).
Local Abbreviation zev_SLit := (@YF7e.zev_SLit).
Local Abbreviation zev_SOff := (@YF7e.zev_SOff).
Local Abbreviation segJ2 := (AR7 (AR6 (AR0 (AR8 (@YF7e.segJ2 _ _))))).
Local Abbreviation segJ := (AR7 (AR6 (AR0 (AR8 (@YF7e.segJ _ _))))).
Local Abbreviation QR := (@YF7i.QR ly res).
Local Abbreviation segT1 := ((AR5 (ARl (AR8 (@YF7i.segT1 _ _)))) Hmap_apart).
Local Abbreviation DX := (AR1 (@YF7i.DX)).
Local Abbreviation PD := (@YF7i.PD imgk ly mem0 DPOST).
Local Abbreviation PD_rstable := ((AR6 (AR4 (AR8 (@YF7i.PD_rstable _)))) DPOST).
Local Abbreviation PD_stableT := ((AR6 (AR4 (AR8 (@YF7i.PD_stableT _)))) DPOST).
Local Abbreviation PSR_stableS := (AR6 (AR9 (AR1 (@YF7i.PSR_stableS _)))).
Local Abbreviation PD_stableS := ((AR6 (AR4 (AR8 (@YF7i.PD_stableS _)))) DPOST).
Local Abbreviation PDX := (@YF7i.PDX imgk ly mem0 DPOST).
Local Abbreviation PDX_rstable := ((AR6 (AR4 (AR8 (@YF7i.PDX_rstable _)))) DPOST).
Local Abbreviation PDX_stableT := ((AR6 (AR4 (AR8 (@YF7i.PDX_stableT _)))) DPOST).
Local Abbreviation PDX_stableS := ((AR6 (AR4 (AR8 (@YF7i.PDX_stableS _)))) DPOST).
Local Abbreviation dx_okb := (@YF7i.dx_okb imgk).
Local Abbreviation skel_apart_DX := (AR7 (AR6 (AR0 (AR8 (@YF7i.skel_apart_DX _))))).
Local Abbreviation skel_apart_stk := ((AR6 (AR0 (AR1 (@YF7i.skel_apart_stk _)))) S Hidx_def Hres_def).
Local Abbreviation at_S_depot := (AR7 (AR6 (AR0 (AR3 (@YF7i.at_S_depot _ _))))).
Local Abbreviation SH3 := (@YF7i.SH3 n mb).
Local Abbreviation SH4 := (@YF7i.SH4 n mb).
Local Abbreviation shadow_marks := (AR5 (AR4 (AR1 (@YF7i.shadow_marks _)))).
Local Abbreviation SH34_ok := (AR5 (AR4 (AR1 (@YF7i.SH34_ok _)))).
Local Abbreviation segT2b := (AR7 ((AR5 (ARl (ARi (@YF7i.segT2b _ _)))) Hmap_apart mat0)).
Local Abbreviation segT2 := (AR7 ((AR5 (ARl (ARi (@YF7i.segT2 _ _)))) Hmap_apart mat0)).
Local Abbreviation SH5 := (@YF7j.SH5 n mb).
Local Abbreviation SH6 := (@YF7j.SH6 n mb).
Local Abbreviation user_marks := (AR5 (AR4 (AR1 (@YF7j.user_marks _)))).
Local Abbreviation SH56_ok := (AR5 (AR4 (AR1 (@YF7j.SH56_ok _)))).
Local Abbreviation segU1 := (AR7 ((AR6 (AR0 (ARi (@YF7j.segU1 _ _)))) mat0)).
Local Abbreviation SH6_of_cut := (AR5 (AR4 (AR1 (@YF7j.SH6_of_cut _)))).
Local Abbreviation segUe := (AR7 ((AR5 (ARl (ARi (@YF7j.segUe _ _)))) Hmap_apart mat0)).
Local Abbreviation PT := ((ARp (@YF7j.PT)) ch mb).
Local Abbreviation run_okT := (@YF7j.run_okT n mb).
Local Abbreviation SH5o := (@YF7j.SH5o n mb).
Local Abbreviation SH6o := (@YF7j.SH6o n mb).
Local Abbreviation SH56o_ok := (AR5 (AR4 (AR1 (@YF7j.SH56o_ok _)))).
Local Abbreviation PT_stableT := (AR6 (AR9 (AR1 (@YF7j.PT_stableT _)))).
Local Abbreviation segUo := (AR7 ((AR5 (ARl (ARi (@YF7j.segUo _ _)))) Hmap_apart mat0)).
Local Abbreviation E0_at := ((ARp (@YF7k.E0_at)) ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3).
Local Abbreviation map_atom := (@YF7k.map_atom).
Local Abbreviation E0_at_other := (AR0 (AR1 (@YF7k.E0_at_other))).
Local Abbreviation ed_E0_at := (AR0 (AR1 (@YF7k.ed_E0_at))).
Local Abbreviation st_ok_ecall_agree_on := (@YF7k.st_ok_ecall_agree_on _ imgk).
Local Abbreviation Esw := (AR0 (AR1 (@YF7k.Esw))).
Local Abbreviation Esw_agree := (AR0 (AR1 (@YF7k.Esw_agree))).
Local Abbreviation Esw_on := (AR0 (AR1 (@YF7k.Esw_on))).
Local Abbreviation at_S_facts_atoms := (AR0 (AR8 (@YF7k.at_S_facts_atoms _))).
Local Abbreviation atoms_ok_app := (@YF7k.atoms_ok_app).
Local Abbreviation FS2_ok := ((AR5 (ARl (AR3 (@YF7k.FS2_ok _)))) DPOST S).
Local Abbreviation at_S_addreg_cfg := (AR0 (AR8 (@YF7k.at_S_addreg_cfg _))).
Local Abbreviation S_N_apart := ((AR6 (AR0 (AR1 (@YF7k.S_N_apart _)))) S).
Local Abbreviation S_N_nomap := (@YF7k.S_N_nomap imgk).
Local Abbreviation grant_cont := ((AR5 (ARl (AR3 (@YF7k.grant_cont _ _)))) Hmap_apart DPOST S).
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
Local Abbreviation slackS := ((ARo ((ARe (@YF7l.slackS _)) mem0 md0)) HQT).
Local Abbreviation S_N_facts := (@YF7l.S_N_facts imgk).
Local Abbreviation S_N_ext64 := ((AR2 (AR0 (AR1 (@YF7l.S_N_ext64 _)))) S).
Local Abbreviation S_N_win64 := ((AR2 (AR0 (AR1 (@YF7l.S_N_win64 _)))) S).
Local Abbreviation nodeS := ((ARo (AR2 (AR0 (ARi (@YF7l.nodeS _ _))))) HQT).
Local Abbreviation S_VG := (@YF7m.S_VG imgk).
Local Abbreviation TQ := (@YF7m.TQ).
Local Abbreviation S_V_facts := (@YF7m.S_V_facts imgk).
Local Abbreviation ZQF := (@YF7m.ZQF imgk ly res).
Local Abbreviation ZQ := (@YF7m.ZQ imgk ly idx res).
Local Abbreviation QR_facts := ((AR1 (@YF7m.QR_facts _)) idx res mb LY IMG Hidx Hres S Hidx_def).
Local Abbreviation ZQ_of_ZQF := (@YF7m.ZQ_of_ZQF imgk ly idx res).
Local Abbreviation QR_not_WIN1T := ((AR6 (AR4 (AR1 (@YF7m.QR_not_WIN1T _)))) S Hidx_def).
Local Abbreviation ZQ_stableT := ((AR6 (AR4 (AR1 (@YF7m.ZQ_stableT _)))) S Hidx_def).
Local Abbreviation ZQ_rstable := ((AR6 (AR4 (AR1 (@YF7m.ZQ_rstable _)))) S Hidx_def).
Local Abbreviation ZQ_stableD := ((AR1 (@YF7m.ZQ_stableD _)) idx res mb LY IMG Hsp Hidx Hres S Hidx_def).
Local Abbreviation skel_apart_Q := ((AR6 (AR0 (AR1 (@YF7m.skel_apart_Q _)))) S Hidx_def Hres_def).
Local Abbreviation TQ_val := ((ARa (AR1 (@YF7m.TQ_val _))) Hidx Hres S Hidx_def).
Local Abbreviation nores50 := (@YF7m.nores50).
Local Abbreviation core50 := (@YF7m.core50).
Local Abbreviation pru17 := (@YF7m.pru17).
Local Abbreviation grant_piece_shape := (@YF7m.grant_piece_shape).
Local Abbreviation nodeV := (AR7 (AR6 (AR0 ((AR8 (@YF7m.nodeV _ _)) md0)))).
Local Abbreviation RZF := (@YF7m.RZF imgk ly res).
Local Abbreviation RZ := (@YF7m.RZ imgk ly idx res).
Local Abbreviation ZQF_rstable := ((AR6 (AR4 (AR1 (@YF7m.ZQF_rstable _)))) S Hidx_def).
Local Abbreviation segV := (AR7 (AR6 (AR0 (AR8 (@YF7m.segV _ _))))).
Local Abbreviation CZI := (@YF7n.CZI imgk).
Local Abbreviation CZ := (@YF7n.CZ imgk ly).
Local Abbreviation abs_cell_okS := (@YF7n.abs_cell_okS imgk).
Local Abbreviation abs_cells_okS := (@YF7n.abs_cells_okS imgk).
Local Abbreviation MPAD := (@YF7n.MPAD imgk).
Local Abbreviation padb := (@YF7n.padb imgk).
Local Abbreviation const_cells_CZ := ((AR4 (AR1 (@YF7n.const_cells_CZ))) Nrange Hidx B TS HTSD).
Local Abbreviation CZ_untouched := ((AR6 (AR4 (AR8 (@YF7n.CZ_untouched _)))) DPOST S).
Local Abbreviation cell_holds_agree := (ARb ((ARg (@YF7n.cell_holds_agree ly regs0 mem0)) Hres)).
Local Abbreviation aview_agreeW := (@YF7n.aview_agreeW imgk W).
Local Abbreviation rd_ext_Wy := (@YF7n.rd_ext_Wy imgk W).
Local Abbreviation depot_ids_bound := ((ARb ((ARk (AR8 (@YF7n.depot_ids_bound))) Hres)) TS).
Local Abbreviation depot_mem_ok_agree := ((ARb ((ARk (AR8 (@YF7n.depot_mem_ok_agree))) Hres)) TS).
Local Abbreviation depot_mem_ok_ext := (@YF7n.depot_mem_ok_ext ly B).
Local Abbreviation depot_at0 := ((ARb ((AR5 ((AR4 (AR3 (@YF7n.depot_at0 _))) Hsp)) Hmap_apart)) HARm).
Local Abbreviation DPOSTS := ((AR1 (@YF7n.DPOSTS)) ch B S).
Local Abbreviation D1W_ok := ((ARb (AR6 (AR9 (AR3 (@YF7n.D1W_ok _ _))))) TS HTSD HARm Hgp).
Local Abbreviation lyF := (@YF7r.lyF ly mb S).
Local Abbreviation SFS := ((ARp (@YF7r.SFS)) ch S).
Local Abbreviation KSc := (@YF7r.KSc n S).
Local Abbreviation lyF_le := (@YF7r.lyF_le ly mb S).
Local Abbreviation lyF_sec := (@YF7r.lyF_sec ly mb S).
Local Abbreviation lyF_eqs := (@YF7r.lyF_eqs ly mb S).
Local Abbreviation lyF_ok := (@YF7r.lyF_ok _ ly mb LY S).
Local Abbreviation sizes_model := (@YF7r.sizes_model ly regs0 n res Nrange S).
Local Abbreviation val_mem_cell := ((AR1 (@YF7r.val_mem_cell)) res B S).
Local Abbreviation ARn f := (f ly regs0 res S) (only parsing).
Local Abbreviation le_byte_1_0 := (ARn (@YF7r.le_byte_1_0)).
Local Abbreviation find_chunk_at_app1 := (@YF7r.find_chunk_at_app1 B).
Local Abbreviation find_chunk_at_app2 := (@YF7r.find_chunk_at_app2 B).
Local Abbreviation In_combine_seq_app := (@YF7r.In_combine_seq_app).
Local Abbreviation combine_seq_last := (ARn (@YF7r.combine_seq_last)).
Local Abbreviation in_combine_seq := (ARn (@YF7r.in_combine_seq)).
Local Abbreviation combine_seq_in := (ARn (@YF7r.combine_seq_in)).
Local Abbreviation index_of_app_old := (@YF7r.index_of_app_old).
Local Abbreviation index_ofZ_app_old := (@YF7r.index_ofZ_app_old).
Local Abbreviation index_of_app_new := (ARn (@YF7r.index_of_app_new)).
Local Abbreviation index_ofZ_app_new := (ARn (@YF7r.index_ofZ_app_new)).
Local Abbreviation fin_facts := ((AR9 (AR8 (@YF7r.fin_facts))) B S).
Local Abbreviation wz_facts := ((ARe (@YF7r.wz_facts _)) regs0 n ch res mb S).
Local Abbreviation S_AR_final := ((ARb (AR6 (AR9 (ARi (@YF7r.S_AR_final _))))) TS HTSD HARm Hidx_def Hres_def imgk).
Local Abbreviation SF_parts := ((ARp (@YF7r.SF_parts)) ch res S Hres_def).
Local Abbreviation rS_not_in_arr := (ARo ((AR3 (@YF7r.rS_not_in_arr _)) n res mb)).
Local Abbreviation len_arr := (@YF7r.len_arr idx S Hidx_def).
Local Abbreviation ck_base_new := (@YF7r.ck_base_new ly regs0 n res mb Nrange B S).
Local Abbreviation SEF := ((ARo ((AR3 (@YF7r.SEF _)) n ch res mb Nrange)) Hres_def).
Local Abbreviation staticF := (@YF7r.staticF ly mb S).
Local Abbreviation placed_finalG := ((ARo (AR5 (AR9 (ARi (@YF7r.placed_finalG _))))) Hres_def).
Local Abbreviation sec_live_final := ((ARp (@YF7r.sec_live_final)) ch res mb Nrange S Hres_def).
Local Abbreviation FQ := (AR4 (@YF7s.FQ imgk ly)).
Local Abbreviation OWN_T := ((ARb (ARd ((AR3 (@YF7s.OWN_T _)) n idx res Hsp))) HARm).
Local Abbreviation OWN_I := ((ARb (ARd ((AR4 (AR3 (@YF7s.OWN_I _))) Hsp))) TS HARm).
Local Abbreviation OWN_Q := ((ARb (ARd ((AR3 (@YF7s.OWN_Q _)) n idx res Hsp))) HARm).
Local Abbreviation OWN_D := ((ARb (ARd ((AR3 (@YF7s.OWN_D _)) n idx res Hsp))) TS HARm).
Local Abbreviation band_core := (@YF7s.band_core ly B S).
Local Abbreviation OWN_SH := ((ARb ((AR5 ((AR4 (AR3 (@YF7s.OWN_SH _))) Hsp)) Hmap_apart)) HARm).
Local Abbreviation OWN_BANDhid := (ARo ((ARe (@YF7s.OWN_BANDhid _)) mem0 md0 LY)).
Local Abbreviation NEWOWN := ((ARb ((AR5 ((AR9 (AR3 (@YF7s.NEWOWN _))) Hsp)) Hmap_apart)) HARm Hres_def).
Local Abbreviation fin_pack := (ARb (AR0 (AR8 (@YF7s.fin_pack)))).
Local Abbreviation fin_post := ((AR9 (AR8 (@YF7s.fin_post _))) B S).
Local Abbreviation finE := ((ARb (AR5 ((ARa (AR8 (@YF7s.finE _ _))) Hn Htp Hra Hsp))) Hidx_def).
Local Abbreviation finO := ((ARb (AR5 ((ARa (AR8 (@YF7s.finO _ _))) Hn Htp Hra Hsp))) Hidx_def).
Local Abbreviation LEAF_S := ((ARb (AR6 (AR9 (ARi (@YF7s.LEAF_S _ _))))) TS HTSD HARm Hidx_def Hres_def).
Local Abbreviation BCELLS := (@YF7u.BCELLS imgk W mem0).
Local Abbreviation PGBv := (@YF7u.PGBv mb).
Local Abbreviation PGEv := (@YF7u.PGEv n mb).
Local Abbreviation big_marks := (AR5 (AR4 (AR1 (@YF7u.big_marks _)))).
Local Abbreviation sm_bounds := (AR5 (AR4 (AR1 (@YF7u.sm_bounds _)))).
Local Abbreviation U_SHBT := (AR5 (AR0 (AR1 (@YF7u.U_SHBT _)))).
Local Abbreviation U_SHET := (AR5 (AR0 (AR1 (@YF7u.U_SHET _)))).
Local Abbreviation U_PGBT := (AR5 (AR0 (AR1 (@YF7u.U_PGBT _)))).
Local Abbreviation U_PGET := (AR5 (AR0 (AR1 (@YF7u.U_PGET _)))).
Local Abbreviation U_SHB_X := (AR5 (AR0 (AR1 (@YF7u.U_SHB_X _)))).
Local Abbreviation U_SHE_X := (AR5 (AR0 (AR1 (@YF7u.U_SHE_X _)))).
Local Abbreviation in_bimg := (@YF7u.in_bimg imgk).
Local Abbreviation in_bimg_facts := (ARj (AR4 (AR1 (@YF7u.in_bimg_facts _)))).
Local Abbreviation val_mem_xfer_bimg := ((ARj (AR4 (AR3 (@YF7u.val_mem_xfer_bimg _)))) S).
Local Abbreviation can_word := ((ARg ((AR3 (@YF7u.can_word)) n)) DPOST S).
Local Abbreviation B_R_ok := ((ARb (ARj (AR0 (AR3 (@YF7u.B_R_ok _ _))))) TS HARm).
Local Abbreviation zcanon_m1 := (@YF7u.zcanon_m1).
Local Abbreviation U_PGB_X := (AR5 (AR0 (AR1 (@YF7u.U_PGB_X _)))).
Local Abbreviation U_PGE_X := (AR5 (AR0 (AR1 (@YF7u.U_PGE_X _)))).
Local Abbreviation brun_refill := (@YF7u.brun_refill ly regs0 n idx res Hres S Hidx_def).
Local Abbreviation SH4_head := ((AR5 (AR4 (AR1 (@YF7u.SH4_head _)))) S Hidx_def).
Local Abbreviation SH4_tail := ((AR5 (AR4 (AR1 (@YF7u.SH4_tail _)))) S Hidx_def).
Local Abbreviation segB1a := (AR7 ((AR6 (AR0 (ARi (@YF7u.segB1a _ _)))) mat0)).
Local Abbreviation zc_m1 := (@YF7u.zc_m1).
Local Abbreviation zc_idem := (@YF7u.zc_idem).
Local Abbreviation zc_add_l := (@YF7u.zc_add_l).
Local Abbreviation zc_sub_l := (@YF7u.zc_sub_l).
Local Abbreviation zc_sub_r := (@YF7u.zc_sub_r).
Local Abbreviation land_page_id := (@YF7u.land_page_id).
Local Abbreviation U_KA0 := (AR5 (AR0 (AR1 (@YF7u.U_KA0 _)))).
Local Abbreviation U_KA1 := (AR5 (AR0 (AR1 (@YF7u.U_KA1 _)))).
Local Abbreviation U_REM1 := (AR5 (AR0 (AR1 (@YF7u.U_REM1 _)))).
Local Abbreviation U_REM2 := (AR5 (AR0 (AR1 (@YF7u.U_REM2 _)))).
Local Abbreviation segB1b := ((AR6 (AR0 (AR8 (@YF7u.segB1b _ _)))) DPOST).
Local Abbreviation segB1 := ((ARb ((AR6 (AR0 (ARi (@YF7u.segB1 _ _)))) mat0)) TS HARm Hidx_def Hres_def).
Local Abbreviation nores4032 := (@YF7u.nores4032).
Local Abbreviation core4032 := (@YF7u.core4032).
Local Abbreviation lit4032 := (@YF7u.lit4032).
Local Abbreviation S_K_facts := (@YF7u.S_K_facts imgk).
Local Abbreviation dieK := ((AR6 (AR0 (AR8 (@YF7u.dieK _ _)))) DPOST).
Local Abbreviation nodeK := (AR7 (AR6 (AR0 ((AR8 (@YF7u.nodeK _ _)) md0)))).
Local Abbreviation submemb2 := (@YF7u.submemb2 imgk).
Local Abbreviation submemb2_sound := (AR7 ((ARg (AR8 (@YF7u.submemb2_sound))) Hres)).
Local Abbreviation at_S_submem2 := (AR7 ((AR0 (AR8 (@YF7u.at_S_submem2 _))) Hidx Hres)).
Local Abbreviation SH5_of_SH4 := (AR5 (AR4 (AR1 (@YF7u.SH5_of_SH4 _)))).
Local Abbreviation segB2 := (AR7 (AR6 (AR0 (AR8 (@YF7u.segB2 _ _))))).
Local Abbreviation allow_of_hull := ((AR5 (AR4 (AR1 (@YF7u.allow_of_hull _)))) S).
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
Let rd0 : reader := aview tfxsegs (w_H W) mem0.
Let WF := am_wf B ly S rd0 HARm.
Definition S1 : astate := set_nev (st_nev S + 1) S.
Definition QLEAF (r : sptr * astate) (W' : world tfxsegs) (c' : config) : Prop :=
Wf (as_universe B) (snd r) /\ qtight (snd r) -> mid_leaf B ly S W regs0 mem0 md0 n tr r W' c'.
Local Open Scope am_scope.
Definition sec_body : M (option sptr) :=
s <- YG00.get ;;
mcheck (Z.of_nat (length (st_sec_arr s)) <? kMaxNumChunks) 220984 ;;
YG00.put (set_secs (st_secs s ++ [mkSec (sec_map_size n) (needed_size n) true]) s) ;;
(if Z.of_nat (length (st_sec_arr s)) =? st_sec_reserved s then
z2 <- askz (KMapPtrArray (8 * Z.of_nat (length (st_sec_arr s))) kPtrArrayCommit) ;;
if aGranted z2 then YG00.modify (fun s0 => set_sec_reserved (st_sec_reserved s0 + kPtrArrayEntriesPerCommit) s0) else spin 391172
else YG00.ret tt) ;;
YG00.modify (fun s0 => set_sec_arr (st_sec_arr s0 ++ [length (st_secs s)]) s0) ;;
YG00.ret (Some (PSec (length (st_secs s)) kPage)).
Definition KSEC (z : Z) : itree astate (sptr * astate) := (ob <- (if z =? 0 then YG00.ret None else sec_body) ;; malloc_K n tr ob) S1.
Lemma malloc_secondary_eq : forall s, from_primary n = false ->
malloc n tr s = (tick ;; mcheck (n <? kMaxAllowedMalloc - kPage) 202196 ;; ob <- sec_alloc n ;; malloc_K n tr ob) s.
Proof. clearP. intros s FP. unfold malloc, malloc_K. rewrite FP. img_refl. Qed.
Lemma sec_ask_eq : forall (Wx : world tfxsegs) c Q,
amreal tfxsegs ((ob <- sec_alloc n ;; malloc_K n tr ob) S1) Wx c Q = amreal tfxsegs (IAsk (KMmapSec (sec_map_size n)) S1 KSEC) Wx c Q.
Proof. clearP. intros Wx c Q. img_refl. Qed.
Lemma at_S_wvb : forall (Wx : world tfxsegs) md mat X P ss W' c',
at_S Wx (with_vm_backing (m_vm_lazy md) mat md) X P ss W' c' -> at_S Wx md X P ss W' c'.
Proof. clear. intros Wx md mat X P ss W' c' (-> & ms & mat' & E' & -> & HE & HS & MEQ & PRS & HP). split; [img_refl|]. exists ms, mat', E'. rewrite wvb_collapse. split; [img_refl|]. repeat (split; [img_try (assumption)|]). img_exact HP. Qed.
Lemma aowned_tick : forall a, aowned B ly S1 a <-> aowned B ly S a.
Proof. clear. intros a. unfold S1, aowned, aclient_byte, sec_extents, frames. cbn. tauto. Qed.
Lemma errno_not_owned : AR tfxsegs B ly S W mem0 md0 -> forall a, TFX_ERRNO <= a < TFX_ERRNO + 4 -> ~ aowned B ly S a.
Proof.
clearP. intros HAR a Ha O.
assert (IMGa : in_img tfxsegs a).
{ unfold in_img. img_case; cbv delta [tfxsegs tfx_loaded_segments]; cbv beta iota; (eexists; split; [do 3 right; left; reflexivity|]); cbn; unfold TFX_ERRNO in Ha; img_lia. }
apply (proj1 (AR_owned_image_law_ok tfxsegs B ly S W mem0 md0 a HAR IMGa)) in O.
rewrite (ts_owned B TS) in O. unfold Tfx_owned_static in O. apply Exists_exists in O as (r & Hr & [X1 X2]). cbn [In] in Hr. unfold TFX_ERRNO in Ha.
repeat match type of Hr with _ \/ _ => destruct Hr as [<-|Hr]; [img_try (cbn [fst snd] in X1, X2; zlia)|] | False => destruct Hr end.
Qed.
Lemma oom_owned : aowned B ly S TFX_OOM.
Proof. clearP. img_apply (own_area B ly S _ (as_oom_byte B, 1) TFX_OOM HARm); [img_try (unfold asyms_areas; cbn; tauto)|]. cbn [fst snd]. rewrite (ts_oom B TS). zlia. Qed.
Lemma val_mem_aview : forall (Hh : word -> bool) m a (w : nat) v k, val_mem tfxsegs (mrestrict Hh m) a w v -> (k < w)%nat ->
aview tfxsegs Hh m (a + Z.of_nat k) = Some (YG0h.le_byte v w k).
Proof.
clear. intros Hh m a w v k Hv Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. img_change (YG0h.le_byte v w k) with (YP0g.le_byte v w k). f_equal.
img_apply unsigned_lit_small8. unfold YP0g.le_byte. img_apply Z.mod_pos_bound. zlia.
Qed.
Theorem refuseS : forall (mat : list word) c',
AR tfxsegs B ly S W mem0 md0 -> aregime S   ->
at_S W (with_vm_backing (m_vm_lazy md0) mat md0) WINP PBUF (resume S_N (SLit ENOMEM_RETv) (ss_mem S_N) (ss_facts S_N)) W c' ->
amreal tfxsegs (KSEC 0) W c' QLEAF.
Proof.
clearP. intros mat c' HAR Hev HR. img_change (amreal tfxsegs (KSEC 0) W c' QLEAF) with (SRr tfxsegs W c' (QLEAF (PNull, S1))).
apply at_S_wvb in HR. eapply SRr_mono; [img_try (img_exact (segR _ _ HR))|].
intros W2 c2 _ (-> & regs' & mem' & mat2 & -> & R10 & RCS & MEQ & PRS & ((HB & VOOM & VERR) & (Vunw & Vres & Vnch & Vmtx & PRT & VISI))) [WF1 QT1]. cbn [fst snd] in WF1, QT1.
pose proof Hsp as (S1' & S2' & S3' & S4'). pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). pose proof BSLv_range as HB'.
pose proof high_facts as (F1 & F2 & _ & _ & _ & _ & _ & _ & F9 & F10 & _). pose proof (ts_inst B TS) as EI.
set (md' := with_vm_backing (m_vm_lazy md0) mat2 md0).
assert (NW : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - ASTACK <= a < sp0) -> ~ WINT a -> ~ WINI a -> a <> TFX_OOM -> ~ (TFX_ERRNO <= a < TFX_ERRNO + 4) ->
mem' (Z_to_bv 64 a) = mem0 (Z_to_bv 64 a)).
{ intros a Ra N1 N2 N3 N4 N5. img_apply MEQ. rewrite unsigned_lit_small by img_exact Ra. unfold WINPN, WINP. clear - N1 N2 N3 N4 N5. intros [[X|[X|X]]|[X|X]]; try tauto; zlia. }
assert (ARF : AR tfxsegs B ly S W mem' md').
{ img_apply (YF70.AR_snull B ly S W mem0 mem' md0 md' BSLv HB' TS HAR).
-
intros a Ra Ho NX. img_apply aview_same. img_apply NW; [img_try (img_exact Ra) | | | | |].
+ intros ST. img_exact (AR_stack_law_ok tfxsegs B ly S W mem0 md0 a HAR ltac:(img_try (clear - ST S1' S3'; unfold ASTACK in *; try unfold sp0 in *; zlia)) Ho).
+ intros X. img_apply NX. unfold YF70.XN. unfold WINT, t_unwinding in X. unfold T in X. clear - X. zlia.
+ intros X. img_apply NX. unfold YF70.XN. unfold WINI in X. clear - X. zlia.
+ intros ->. img_apply NX. unfold YF70.XN. left. zlia.
+ intros X. img_exact (errno_not_owned HAR a X Ho).
-
intros a0 HV0. set (a := bv_unsigned (Z_to_bv 64 a0)).
assert (Ra : 0 <= a < 2 ^ 64) by (img_try (pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 a0)) as R; img_change (bv_modulus 64) with (2 ^ 64) in R; img_exact R)).
assert (Ex : Z_to_bv 64 a = Z_to_bv 64 a0) by (img_try ((subst a; cbv beta); img_apply Z_to_bv_bv_unsigned)).
assert (AV : forall (Hh : word -> bool) m, aview tfxsegs Hh m a0 = aview tfxsegs Hh m a) by (img_try (intros Hh m; unfold aview, mbyte, mrestrict; rewrite Ex; img_refl)).
rewrite AV in HV0 |- *. clearbody a. clear Ex AV a0.
assert (PRES : forall u, apresent (w_H W) mem' u -> aview tfxsegs (w_H W) mem' u <> None) by (img_try (clear; intros u [Hh [b Hb]]; unfold aview, mbyte, mrestrict; rewrite Hh, Hb; cbn; discriminate)).
assert (VAL : forall u base (w : nat) v, val_mem tfxsegs (mrestrict (w_H W) mem') base w v -> base <= u < base + Z.of_nat w -> aview tfxsegs (w_H W) mem' u <> None).
{ clear. intros u base w v HV Hu. replace u with (base + Z.of_nat (Z.to_nat (u - base))) by zlia. rewrite (val_mem_aview (w_H W) mem' base w v (Z.to_nat (u - base)) HV ltac:(img_try (zlia))). discriminate. }
destruct (zr_dec (sp0 - ASTACK) sp0 a) as [D1|D1]; [img_try (img_apply PRES; img_apply PRS; img_exact D1)|].
assert (DT : WINT a \/ ~ WINT a) by (img_try (clear; unfold WINT; zlia)). destruct DT as [D2|D2]; [img_try (img_apply PRES; img_apply PRT; img_exact D2)|].
assert (DI : WINI a \/ ~ WINI a) by (img_try (clear; unfold WINI; zlia)). destruct DI as [D3|D3]; [img_try (img_exact (VISI a D3))|].
destruct (Z.eq_dec a TFX_OOM) as [->|D4]; [img_try (img_apply (VAL _ _ _ _ VOOM); cbn; zlia)|].
destruct (zr_dec TFX_ERRNO (TFX_ERRNO + 4) a) as [D5|D5]; [img_try (img_exact (VERR a D5))|].
rewrite (aview_same (w_H W) mem0 mem' a (NW a Ra D1 D2 D3 D4 D5)). img_exact HV0.
-   pose proof (val_mem_aview _ _ _ _ _ 0%nat Vunw ltac:(img_try (zlia))) as X. rewrite Z.add_0_r in X. unfold T in X. img_exact X.
- intros k Hk. rewrite <- Hres_def. img_exact (val_mem_aview _ _ _ _ _ k Vres Hk).
- intros k Hk. rewrite <- Hidx_def. img_exact (val_mem_aview _ _ _ _ _ k Vnch Hk).
- intros k Hk. replace k with (Z.of_nat (Z.to_nat k)) by zlia. rewrite (val_mem_aview _ _ _ _ _ (Z.to_nat k) Vmtx ltac:(img_try (zlia))). f_equal.
clear - Hk. unfold YG0h.le_byte. rewrite Z.shiftr_0_l. img_refl.
- unfold md'. img_apply m_vmmaps_wvb.
- unfold md'. img_apply m_vm_lazy_wvb.
- unfold md'. img_apply eager_used_wvb.
-   intros a Ha _. unfold YG0u.w64. img_apply NW.
+ clear - Ha. unfold kHighShadowBeg, kHighShadowEnd in Ha. zlia.
+ clear - Ha S1' T7. unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, ASTACK in *. try unfold sp0 in *. zlia.
+ clear - Ha F1. unfold zone3, TFX_IMG_LO, kLowShadowBeg, WINT, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, t_unwinding in *. try unfold T in *. zlia.
+ clear - Ha HB'. unfold WINI, kHighShadowBeg, kHighShadowEnd, TFX_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex in *. zlia.
+ clear - Ha. unfold kHighShadowBeg, kHighShadowEnd, TFX_OOM in *. zlia.
+ clear - Ha. unfold kHighShadowBeg, kHighShadowEnd, TFX_ERRNO in *. zlia. }
exists ly, regs', mem', md'.
split. { img_refl. }
split. { intros i Hi. replace (spZ regs0 - 2120 + 8 * Z.of_nat i) with (sp0 - IFRAME + 16 + 8 * Z.of_nat i) by (img_try (unfold IFRAME, spZ, sp0; clear; zlia)). img_exact (HB i Hi). }
split; [| img_try (split; [rewrite R10; cbn [fst sptr_addr sptr_exp aeval]; img_refl | img_exact QT1])].
split; [img_try (img_exact (AR_tick B ly S W mem' md' ARF Hev))|].
split; [img_try (img_apply layout_le_refl)|].
split; [img_try (img_apply wle_refl)|].
split; [img_try (img_exact RCS)|].
split; [img_try (unfold md'; img_apply YG0b.same_io_with_vm_backing)|].
split; [| img_try (img_exact PRS)].
intros a Ra NO NO' NS NE. img_apply aview_same. img_apply NW; [img_try (img_exact Ra) | | | | |].
- intros ST. img_apply NS. unfold ascratch, spZ. left. img_exact ST.
- intros X. img_exact (NO (OWN_T a X)).
- intros X. img_exact (NO (OWN_I a X)).
- intros ->. img_exact (NO oom_owned).
- intros X. img_apply NS. unfold ascratch. right. rewrite (ts_errno B TS). img_exact X.
Qed.
Local Ltac step HR e :=
eapply SRr_bind; [img_try (img_exact e) | img_try (clear HR; let W2 := fresh "W" in let c2 := fresh "c" in intros W2 c2 _ HR)].
Section l.
Variables (W3 : world tfxsegs) (mat : list word) (ms : machine_state) (E' : env) (mb0 : Z).
Let mdN : Model := with_vm_backing (m_vm_lazy md0) mat md0.
Let md2 : Model := mmap_model (w64 mb) (w64 MSv) mdN.
Let ccont : config := mkCfg (mkst (regupd (ms_regs ms) 10%bv (w64 mb)) (v_addi (Z_to_bv 64 (ss_pc S_N)) 4) (zfill (w64 mb) (w64 MSv) (ms_mem ms)) (seg_rom tfxsegs)) md2.
Hypothesis HAR : AR tfxsegs B ly S W mem0 md0.
Hypothesis Hev : aregime S.
Hypothesis Htr : In tr (as_universe B).
Hypothesis D1 : tfx_depot_spec B.
Hypothesis HBC : BCELLS.
Hypothesis HDP : forall z m, DPOST z m <-> DPOSTS W3 z m.
Hypothesis GOK : grant_ok_na_pin mdN (w64 mb) MSv = true.
Hypothesis LE3 : wle W W3.
Hypothesis SUB3 : hsub (w_H W3) (w_H W).
Hypothesis MON3 : forall x : word, w_H W x = false -> w_H W3 x = false.
Hypothesis A3 : w_A W3 = (SHLO mb, SHHI mb) :: (mb, mb + MSv) :: w_A W.
Hypothesis VISM3 : forall x : word, mb <= bv_unsigned x < mb + MSv -> w_H W3 x = false.
Hypothesis VISH3 : forall x : word, SHLO mb <= bv_unsigned x < SHHI mb -> w_H W3 x = false.
Hypothesis OUT3 : forall x : word, ~ (mb <= bv_unsigned x < mb + MSv) -> ~ (SHLO mb <= bv_unsigned x < SHHI mb) -> w_H W3 x = w_H W x.
Hypothesis AI2 : AI tfxsegs (w_H W3) (w_A W3) md2.
Hypothesis MW2 : amwf md2.
Hypothesis IO2 : same_io md0 md2.
Hypothesis EG2 : eager_used md2 <= eager_used mdN + MSv.
Hypothesis VM2 : vm_maps (m_vmmaps md2) = (w64 mb, w64 MSv) :: vm_maps (m_vmmaps mdN) /\ vm_reserved (m_vmmaps md2) = vm_reserved (m_vmmaps mdN) /\
vm_limit (m_vmmaps md2) = vm_limit (m_vmmaps mdN) /\ vm_mmap_base (m_vmmaps md2) = vm_mmap_base (m_vmmaps mdN).
Hypothesis HE' : env_agree sHAV (E0_at mb0) E'.
Hypothesis HS : st_ok_ecall tfxsegs E' S_N (restrict (w_H W) ms).
Hypothesis MEQ : forall x : word, ~ WINP (bv_unsigned x) -> ms_mem ms x = mem0 x.
Hypothesis PRS : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) (ms_mem ms) a.
Hypothesis HB : PBUF (ms_mem ms).
Let MA : ARm B ly S rd0 := proj1 HAR.
Lemma LN : ALedger tfxsegs ly S mdN.
Proof. img_exact (ALedger_same tfxsegs ly S md0 mdN (proj1 (proj2 HAR)) (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) (eager_used_wvb _ _)). Qed.
Lemma MWN : amwf mdN.
Proof. img_exact (amwf_same md0 mdN (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) (proj1 (proj2 (proj2 (proj2 HAR))))). Qed.
Lemma MSB : 0 < MSv <= MALLOC_MAX + 4 * 4096.
Proof. clearP. pose proof size_facts as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & _). clear - Z8 Z1 Z2 Z3. unfold MALLOC_MAX in *. zlia. Qed.
Lemma Umb : bv_unsigned (w64 mb) = mb.
Proof. pose proof map_facts as (M1 & M2 & _). pose proof map_zoneN as MZ. pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & _). unfold w64. img_apply unsigned_lit_small. clear - M1 M2 Z8 MZ. ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. zlia. Qed.
Lemma GAP : Forall (zdisjoint (mb, MSv)) (static_extents ly ++ vis0_zones ly ++ sec_extents ly S).
Proof.
pose proof (YF48.grant_apart B ly S rd0 mdN (w64 mb) MSv MA LN MSB ltac:(img_try (pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & _ & Z9 & _); img_exact Z9)) GOK) as X.
rewrite Umb in X. img_exact X.
Qed.
Lemma SHZ : forall a, SMv <= a < SMv + MSv / 8 -> w_H W3 (w64 a) = false /\ ms_mem ms (w64 a) = Some (Z_to_bv 8 0).
Proof.
intros a Ha. pose proof map_facts as (M1 & M2 & M3 & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _ & _ & SMA). pose proof map_zoneN as MZ. pose proof (SH_hull mb) as (H1 & H2 & _).
pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & Z9 & _).
assert (Ra : 0 <= a < 2 ^ 64) by (img_try (clear - Ha SM1 SM2 MZ; unfold kHighShadowBeg, kHighShadowEnd in *; zlia)).
split; [img_try (img_apply VISH3; unfold w64; rewrite unsigned_lit_small by img_exact Ra; rewrite SMA in Ha; clear - Ha H1 H2 MZ; zlia)|].
set (g := mb + 8 * (a - SMv)).
assert (Hg : shadow_addr g = a).
{ (subst g; cbv beta). rewrite SMA. unfold shadow_addr. apply Z.mod_divide in M3 as [p Hp]; [|img_try (zlia)]. rewrite Hp.
replace (p * 4096) with (p * 512 * 8) by zlia. rewrite (Z.div_mul (p * 512) 8) by zlia.
replace (p * 512 * 8 + 8 * (a - (SHADOW_OFF + p * 512))) with ((p * 512 + (a - (SHADOW_OFF + p * 512))) * 8) by zlia.
rewrite Z.div_mul by zlia. zlia. }
rewrite <- Hg. unfold w64. rewrite MEQ.
- pose proof (Z.div_mod MSv 8 ltac:(img_try (zlia))) as DM8. assert (M8 : MSv mod 8 = 0) by (img_try (clear - Z9 MZ; apply Z.mod_divide in Z9 as [u Hu]; [|img_try (zlia)]; rewrite Hu; replace (u * 4096) with ((u * 512) * 8) by zlia; img_apply Z.mod_mul; zlia)).
apply (YF48.grant_shadow_zero B ly S rd0 mdN (w64 mb) MSv MA LN MSB Z9 GOK mem0 g (proj2 (proj2 (proj2 (proj2 (proj2 HAR)))))).
+ (subst g; cbv beta). img_apply Z.mod_divide; [img_try (zlia)|]. apply Z.mod_divide in M3 as [p Hp]; [|img_try (zlia)]. exists (p * 512 + (a - SMv)). zlia.
+ rewrite Umb. (subst g; cbv beta). clear - Ha MZ. zlia.
+ rewrite Umb. (subst g; cbv beta). clear - Ha DM8 M8 MZ. zlia.
- rewrite unsigned_lit_small by (img_try (rewrite Hg; img_exact Ra)). rewrite Hg. intros Hw. unfold WINP, WINT, WINI in Hw. pose proof BSLv_range as HBS. pose proof high_facts as (F1 & _).
destruct Hsp as (S1' & _). pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7).
clear - Hw Ha SM1 SM2 F1 S1' T7 HBS MZ. unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, ASTACK, t_unwinding, TFX_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex in *.
try unfold sp0 in *. try unfold T in *. zlia.
Qed.
Lemma VISM : forall a, mb <= a < mb + MSv -> w_H W3 (w64 a) = false.
Proof. intros a Ha. pose proof map_facts as (M1 & M2 & _). pose proof map_zoneN as MZ. img_apply VISM3. unfold w64. rewrite unsigned_lit_small; [img_try (img_exact Ha) | img_try (clear - Ha M1 M2 MZ; ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; zlia)]. Qed.
Lemma WZ3 : forall z mat', ALedger tfxsegs lyF (SFS false z) md2 -> wz_facts false z W3 (with_vm_backing (m_vm_lazy md2) mat' md2).
Proof.
intros z mat' L2. pose proof (SH_hull mb) as (H1 & H2 & H3 & _). constructor.
- img_exact MON3.
- img_exact VISM3.
- img_exact VISH3.
- intros E; discriminate E.
- rewrite A3. cbn [A_bytes fst snd]. zlia.
- intros i Hi. rewrite A3. cbn. right; right. img_exact Hi.
- rewrite A3. cbn. right; left. img_refl.
- rewrite A3. cbn. left. img_refl.
- img_exact (ALedger_same tfxsegs lyF (SFS false z) md2 _ L2 (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) (eager_used_wvb _ _)).
- img_exact (amwf_same md2 _ (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) MW2).
- img_exact GAP.
Qed.
Lemma LED0 : forall z, ALedger tfxsegs lyF (SFS false z) md2.
Proof.
intros z. pose proof (SF_parts false z) as (Rreg & _ & _ & _ & _ & _ & _ & _ & Rarr & Rres & _ & Rck & Rsecs & Rnev & Rregs).
pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & Z9 & _).
assert (UMS : bv_unsigned (w64 MSv) = MSv) by (img_try (unfold w64; img_apply unsigned_lit_small; clear - Z8; unfold MALLOC_MAX in Z8; zlia)).
unfold md2. img_apply (YG0l.ALedger_anon tfxsegs (as_universe B) 0 0 0 ly S (SFS false z) mdN (w64 mb) (w64 MSv) (rS S) mb LY WF (am_placed _ _ _ _ MA) MWN LN).
- rewrite UMS. img_exact GOK.
- img_exact Hev.
- rewrite UMS. img_exact MSB.
- rewrite UMS. img_exact Z9.
- intros c Hc. img_exact (Rreg c).
- unfold prim_committed. rewrite Rregs. img_refl.
- rewrite Umb, UMS. img_exact (SEF false z).
- img_exact Rnev.
- rewrite Rres, <- Hres_def. img_refl.
Qed.
Lemma COV_Q : forall mdV, amwf mdV -> idx = res ->
forall x, ~ (ly_Q ly <= x < ly_Q ly + kPtrArrayResv) ->
YK0h.covered (vm_noaccess (m_vmmaps (grant_md false (Z_to_bv 64 50) (w64 QSv) (w64 131072) mdV)) ++ m_vm_lazy (grant_md false (Z_to_bv 64 50) (w64 QSv) (w64 131072) mdV)) x
= YK0h.covered (vm_noaccess (m_vmmaps mdV) ++ m_vm_lazy mdV) x.
Proof.
intros mdV [(W1 & W2 & W3' & _ & W5) _] Heq x Hx.     pose proof (QR_facts Heq) as (E1 & _ & QA & F9 & Q5 & F10 & EQR).
assert (UQa : bv_unsigned (w64 QSv) = QSv) by (img_try (unfold w64; img_apply unsigned_lit_small; clear - F9 Q5 F10; ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kPtrArrayResv in *; try unfold Qb in *; zlia)).
assert (UQb : bv_unsigned (w64 131072) = 131072) by (img_try (unfold w64; img_apply unsigned_lit_small; zlia)).
img_apply (YG0l.cov_grant_md false (Z_to_bv 64 50) (w64 QSv) (w64 131072) mdV x).
- unfold YK0h.model_ivs_wf. split; [|img_try (split; [|split; [|img_exact W5]])]; intros q Hq; [img_try (img_exact (W1 q Hq)) | img_try (img_exact (W2 q Hq)) | img_try (img_exact (W3' q Hq))].
- rewrite UQa, UQb. clear - F9 Q5 F10. ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kPtrArrayResv in *. try unfold Qb in *. zlia.
- rewrite UQa, UQb. intros Hin. img_apply Hx. clear - Hin F9 Q5. unfold kPtrArrayResv in *. try unfold Qb in *. zlia.
Qed.
Lemma grant50_isp : forall (a k : word) md, vm_init_sp (m_vmmaps (grant_md false (Z_to_bv 64 50) a k md)) = vm_init_sp (m_vmmaps md).
Proof.
clear. intros a k md. unfold grant_md, fixedin_ok_model, fixedin_ok_vmmaps, with_mmap_replacement, with_mmap_backing. rewrite YF7m.nores50. cbn.
destruct md as [fd [maps lazy mat] io fs pr lim tm sg sc]. cbn. destruct maps; cbn; img_refl.
Qed.
Lemma LED1 : forall z mdV md5, idx = res -> ALedger tfxsegs lyF (SFS false z) mdV ->
vm_maps (m_vmmaps md5) = vm_maps (m_vmmaps mdV) -> vm_reserved (m_vmmaps md5) = vm_reserved (m_vmmaps mdV) ->
vm_limit (m_vmmaps md5) = vm_limit (m_vmmaps mdV) -> vm_mmap_base (m_vmmaps md5) = vm_mmap_base (m_vmmaps mdV) ->
vm_init_sp (m_vmmaps md5) = vm_init_sp (m_vmmaps mdV) ->
(forall x, ~ (ly_Q ly <= x < ly_Q ly + kPtrArrayResv) ->
YK0h.covered (vm_noaccess (m_vmmaps md5) ++ m_vm_lazy md5) x = YK0h.covered (vm_noaccess (m_vmmaps mdV) ++ m_vm_lazy mdV) x) ->
eager_used md5 <= eager_used mdV + 131072 ->
(forall lo n, region_free (vm_noaccess (m_vmmaps mdV)) lo n = true -> region_free (vm_noaccess (m_vmmaps md5)) lo n = true) ->
ALedger tfxsegs lyF (SFS true z) md5.
Proof.
intros z mdV md5 Heq LV VM RES LIM MMB ISP COV EG NAF.
pose proof (SF_parts false z) as (Rreg0 & _ & _ & _ & _ & _ & _ & _ & _ & Rres0 & _ & _ & _ & Rnev0 & Rregs0).
pose proof (SF_parts true z) as (Rreg1 & _ & _ & _ & _ & _ & _ & _ & _ & Rres1 & _ & _ & _ & Rnev1 & Rregs1).
pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & Z9 & _).
img_apply (YG0l.ALedger_qcommit' tfxsegs lyF (SFS false z) (SFS true z) mdV md5).
- img_exact lyF_ok.
- rewrite (SEF false z). img_apply Forall_app. split; [img_try (img_exact (YG08.sec_extents_sizes64P _ 0 0 0 ly S WF))|]. constructor; [|img_try (constructor)]. cbn [snd]. clear - Z8 Z9. unfold MALLOC_MAX in Z8. zlia.
- img_exact (placed_finalG false z HAR GAP).
- img_exact LV.
- img_exact VM.
- img_exact RES.
- img_exact LIM.
- img_exact MMB.
- img_exact ISP.
- intros x Hx. img_apply COV. img_exact Hx.
- clear - EG. unfold kPtrArrayEntriesPerCommit. zlia.
- intros c Hc. rewrite (Rreg1 c), (Rreg0 c). img_refl.
- rewrite (SEF true z), (SEF false z). img_refl.
- unfold prim_committed. rewrite Rregs1, Rregs0. img_refl.
- rewrite Rnev1, Rnev0. img_refl.
- rewrite Rres1, Rres0. img_refl.
- img_exact NAF.
Qed.
Definition KDEP (s : astate) (beg : sptr) (z : Z) : itree astate (sptr * astate) :=
((if z =? 0 then YG00.ret tt
else (s' <- YG00.get ;;
mcheck (depot_ids s' + 1 <? kDepotIdsPerBlock) 469424 ;;
mcheck (kStartFramesMax + depot_frames s' + Z.of_nat (length tr) + 1 <? kStoreFramesPerBlock) 460444 ;;
YG00.put (set_depot (st_depot s' ++ [tr]) s'))) ;;
(let k := mkChunk beg n CAllocated in
(if needs_remap (ck_n k) then z <- askz (KShadowRemap (ck_user k) (8 * (ck_n k / 8))) ;; if aGranted z then YG00.ret tt else spin 449796 else YG00.ret tt) ;;
YG00.modify (fun s0 => set_chunks (upd_chunk (st_chunks s0) k) s0) ;;
YG00.ret (ck_user k))) s.
Lemma malloc_K_some : forall beg s (Wx : world tfxsegs) c Q,
amreal tfxsegs (malloc_K n tr (Some beg) s) Wx c Q = SRr tfxsegs Wx c (fun W1 c1 => exists z, aok s (KDepot tr) z /\ amreal tfxsegs (KDEP s beg z) W1 c1 Q).
Proof. clearP. intros. img_refl. Qed.
Lemma NR : N8D / 8 < 18446744073709551615 -> needs_remap (ck_n (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated)) = false.
Proof.
intros Hsmall. pose proof sizes_model as (_ & _ & RS & _). unfold ck_n, needs_remap. cbn [YG00.ck_req]. rewrite RS. img_apply Z.leb_gt.
clear - Hsmall Nrange. unfold N8D, kClearShadowMmapThreshold in *. rewrite Z.div_mul in Hsmall by zlia. zlia.
Qed.
Lemma NRb : 18446744073709551615 <= N8D / 8 -> needs_remap (ck_n (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated)) = true.
Proof.
intros Hbig. pose proof sizes_model as (_ & _ & RS & _). unfold ck_n, needs_remap. cbn [YG00.ck_req]. rewrite RS. img_apply Z.leb_le.
clear - Hbig Nrange. unfold N8D, kClearShadowMmapThreshold in *. rewrite Z.div_mul in Hbig by zlia. zlia.
Qed.

Lemma TAILg : N8D / 8 < 18446744073709551615 -> forall (grow : bool) (Wz : world tfxsegs) (mdz : Model) (RX : (word -> option byte) -> Prop) (Xd : Z -> Prop) z c4 s4,
(grow = true <-> idx = res) -> rstable RX -> pstable WIN1T RX -> (grow = true -> forall m, RX m -> ZQ Wz m) ->
(forall a, WIN a -> Xd a) -> (forall a, Xd a -> WIN a \/ (grow = true /\ QR a) \/ DX a) ->
wle W Wz -> same_io md0 mdz -> (forall mat', wz_facts grow z Wz (with_vm_backing (m_vm_lazy mdz) mat' mdz)) ->
(forall x : word, ~ (mb <= bv_unsigned x < mb + MSv) -> ~ (SHLO mb <= bv_unsigned x < SHHI mb) ->
~ (grow = true /\ QSv <= bv_unsigned x < QSv + 131072) -> w_H Wz x = w_H W x) ->
(forall zz m, DPOST zz m -> DPOSTS Wz zz m) ->
at_S Wz mdz Xd (PSR Wz SH2 (PDX Wz RX z)) T_2 Wz c4 ->
st_depot s4 = st_depot (depot_after z tr S) -> st_chunks s4 = st_chunks S -> st_secs s4 = st_secs S ++ [mkSec (sec_map_size n) (needed_size n) true] ->
st_sec_arr s4 = st_sec_arr S ++ [length (st_secs S)] ->
st_sec_reserved s4 = (if grow then st_sec_reserved S + kPtrArrayEntriesPerCommit else st_sec_reserved S) -> st_regions s4 = st_regions S ->
st_nev s4 = st_nev S + 1 -> st_cache_inited s4 = st_cache_inited S -> st_cache s4 = st_cache S -> st_qthread s4 = st_qthread S ->
st_qglobal s4 = st_qglobal S -> st_fs s4 = st_fs S -> st_internal_inited s4 = st_internal_inited S ->
amreal tfxsegs ((YG00.ret tt ;;
(YG00.modify (fun s0 => set_chunks (upd_chunk (st_chunks s0) (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated)) s0) ;;
YG00.ret (ck_user (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated)))) s4) Wz c4 QLEAF.
Proof.
intros Hsmall grow Wz mdz RX Xd z c4 s4 Hgrow RXs RXt HRXQ HXW HXsub LEz IOz HWZ HOUT HDPz HR D4 C4 SE4 A4 R4 RG4 N4 CI4 CA4 QT4 QG4 FS4 II4.
pose proof sizes_model as (ND & MS & RS & RZ & FP & KN & KR & KE & KQ & KB & KST).
eapply amreal_pure; [img_refl|]. eapply amreal_pure; [img_refl|]. cbn [amreal].
assert (LEAF : forall W' c', fin_post Wz mdz grow z W' c' ->
QLEAF (ck_user (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated), set_chunks (upd_chunk (st_chunks s4) (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated)) s4) W' c').
{ intros W' c' (-> & regs' & mem' & mat' & memD' & -> & HF) MP.
assert (EQS : set_chunks (upd_chunk (st_chunks s4) (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated)) s4 = SFS grow z).
{ pose proof (YF49.upd_chunk_fresh (st_chunks S) (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated)
(YF49.KS_fresh S (as_universe B) 0 0 0 WF)) as UF.
clear HR. destruct s4; cbn in *. (subst; cbv beta). unfold SFS, YF49.sfinal, YF49.depF, YF49.resF, YF49.KS, YF49.rS. cbn. cbn in UF. rewrite UF.
rewrite MS, ND. unfold depot_after. destruct grow; destruct (z =? 0); img_refl. }
rewrite EQS in MP |- *. img_change (ck_user (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated)) with (ck_user KSc).
img_exact (LEAF_S grow z Wz mdz HAR Hgrow LEz IOz HWZ HOUT regs' mem' memD' mat' MP HF). }
assert (HDPOST : forall zz m, DPOST zz m -> aok S (KDepot tr) zz /\ depot_mem_ok B ly (depot_after zz tr S) (aview tfxsegs (w_H Wz) m) /\ Forall (cell_holds B ly (aview tfxsegs (w_H Wz) m)) (as_const B ly)).
{ intros zz m Hd. img_exact (HDPz zz m Hd). }
step HR (segT2 Wz mdz RX RXs RXt Xd z HXW _ _ HR). pose proof (proj1 HR) as EW. (subst W0; cbv beta).
step HR (segU1 Wz mdz RX RXs RXt Xd z HXW Hsmall _ _ HR). pose proof (proj1 HR) as EW. (subst W0; cbv beta).
destruct (Z.eq_dec (n mod 8) 0) as [H8|H8].
- step HR (segUe Wz mdz RX RXs RXt Xd z HXW H8 _ _ HR). pose proof (proj1 HR) as EW. (subst W0; cbv beta).
eapply SRr_mono; [img_try (img_exact (finE Wz mdz Xd RX grow z Hgrow HXsub HRXQ HDPOST H8 _ _ HR))|].
intros W' c' _ HP. img_exact (LEAF W' c' HP).
- step HR (segUo Wz mdz RX RXs RXt Xd z HXW H8 _ _ HR). pose proof (proj1 HR) as EW. (subst W0; cbv beta).
eapply SRr_mono; [img_try (img_exact (finO Wz mdz Xd RX grow z Hgrow HXsub HRXQ HDPOST H8 _ _ HR))|].
intros W' c' _ HP. img_exact (LEAF W' c' HP).
Qed.
Lemma SRr_with_AI : forall (Wx : world tfxsegs) cx (Q : world tfxsegs -> config -> Prop),
SRr tfxsegs Wx cx Q -> SRr tfxsegs Wx cx (fun W' c' => AI tfxsegs (w_H W') (w_A W') (cfg_model c') /\ Q W' c').
Proof. clear. intros Wx cx Q H b HI T HK. img_apply (H b HI T). intros W' c' Hle HI' HQ. img_exact (HK W' c' Hle HI' (conj HI' HQ)). Qed.
Lemma amreal_askV : forall (q : kreq) (sN : astate) (Kc : Z -> itree astate (sptr * astate)) (Wx : world tfxsegs) (cx : config)
(Q : sptr * astate -> world tfxsegs -> config -> Prop),
match q with KDepot _ => False | _ => True end ->
SRr tfxsegs Wx cx (fun W1 c1 => exists (I : Type) (nx : I -> config) (bit : I -> Z) (sp : I -> bool) (i0 : I),
node_ok tfxsegs c1 I (fun _ => []) nx /\
(forall i, AI tfxsegs (w_H W1) (w_A W1) (cfg_model c1) -> AI tfxsegs (w_H W1) (w_A W1) (cfg_model (nx i))) /\
(forall i, aok sN q (bit i)) /\ sp i0 = false /\ bit i0 = 1 /\
(refusable q = true -> exists i1, sp i1 = false /\ bit i1 = 0) /\
(forall i, sp i = true -> AI tfxsegs (w_H W1) (w_A W1) (cfg_model (nx i)) -> srealizesM tfxsegs false (nx i) t_nil) /\
(forall i, (sp i = true \/ bit i <> 1) -> fo_dead tfxsegs c1 (nx i)) /\
(forall i, sp i = false -> if Z.eqb (bit i) 1 then amreal tfxsegs (Kc (bit i)) W1 (nx i) Q else amrealE tfxsegs (Kc (bit i)) W1 (nx i) Q)) ->
amreal tfxsegs (IAsk q sN Kc) Wx cx Q.
Proof. clear. intros q sN Kc Wx cx Q Hq H. destruct q; try (destruct Hq); cbn [amreal]; img_exact H. Qed.
Lemma same_io_wvb : forall md mat', same_io md0 md -> same_io md0 (with_vm_backing (m_vm_lazy md) mat' md).
Proof. clear. intros md mat' (X1 & X2 & X3 & X4). unfold same_io in *. rewrite <- X1, <- X2, <- X3, <- X4. repeat split; img_refl. Qed.
Lemma TAILgB : 18446744073709551615 <= N8D / 8 -> forall (grow : bool) (Wz : world tfxsegs) (mdz : Model) (RX : (word -> option byte) -> Prop) (Xd : Z -> Prop) z c4 s4,
(grow = true <-> idx = res) -> rstable RX -> pstable WIN1T RX -> (grow = true -> forall m, RX m -> ZQ Wz m) ->
(forall a, WIN a -> Xd a) -> (forall a, Xd a -> WIN a \/ (grow = true /\ QR a) \/ DX a) ->
wle W Wz -> same_io md0 mdz -> (forall mat', wz_facts grow z Wz (with_vm_backing (m_vm_lazy mdz) mat' mdz)) ->
(forall x : word, ~ (mb <= bv_unsigned x < mb + MSv) -> ~ (SHLO mb <= bv_unsigned x < SHHI mb) ->
~ (grow = true /\ QSv <= bv_unsigned x < QSv + 131072) -> w_H Wz x = w_H W x) ->
(forall zz m, DPOST zz m -> DPOSTS Wz zz m) ->
In (SHLO mb, SHHI mb) (w_A Wz) ->
at_S Wz mdz Xd (PSR Wz SH2 (PDX Wz RX z)) T_2 Wz c4 ->
st_depot s4 = st_depot (depot_after z tr S) -> st_chunks s4 = st_chunks S -> st_secs s4 = st_secs S ++ [mkSec (sec_map_size n) (needed_size n) true] ->
st_sec_arr s4 = st_sec_arr S ++ [length (st_secs S)] ->
st_sec_reserved s4 = (if grow then st_sec_reserved S + kPtrArrayEntriesPerCommit else st_sec_reserved S) -> st_regions s4 = st_regions S ->
st_nev s4 = st_nev S + 1 -> st_cache_inited s4 = st_cache_inited S -> st_cache s4 = st_cache S -> st_qthread s4 = st_qthread S ->
st_qglobal s4 = st_qglobal S -> st_fs s4 = st_fs S -> st_internal_inited s4 = st_internal_inited S ->
amreal tfxsegs (((z' <- askz (KShadowRemap (ck_user (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated))
(8 * (ck_n (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated) / 8))) ;;
(if aGranted z' then YG00.ret tt else spin 449796)) ;;
(YG00.modify (fun s0 => set_chunks (upd_chunk (st_chunks s0) (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated)) s0) ;;
YG00.ret (ck_user (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated)))) s4) Wz c4 QLEAF.
Proof.
intros Hbig. exfalso. clear - Hbig Nrange. unfold YF7f.N8D in Hbig. unfold MALLOC_MAX in Nrange.
rewrite Z.div_mul in Hbig by (img_try (clear; img_lia)).
pose proof (Z.div_lt_upper_bound n 8 (2 ^ 25) ltac:(img_try (clear; img_lia)) ltac:(img_try (clear - Nrange; img_lia))) as HH. clear Nrange. img_lia.
Qed.
Lemma after_depot : forall (grow : bool) (Wz : world tfxsegs) (mdz : Model) (RX : (word -> option byte) -> Prop) (Xd : Z -> Prop) z c4 s3,
(grow = true <-> idx = res) -> rstable RX -> pstable WIN1T RX -> (grow = true -> forall m, RX m -> ZQ Wz m) ->
(forall a, WIN a -> Xd a) -> (forall a, Xd a -> WIN a \/ (grow = true /\ QR a) \/ DX a) ->
wle W Wz -> same_io md0 mdz -> (forall mat', wz_facts grow z Wz (with_vm_backing (m_vm_lazy mdz) mat' mdz)) ->
(forall x : word, ~ (mb <= bv_unsigned x < mb + MSv) -> ~ (SHLO mb <= bv_unsigned x < SHHI mb) ->
~ (grow = true /\ QSv <= bv_unsigned x < QSv + 131072) -> w_H Wz x = w_H W x) ->
(forall zz m, DPOST zz m -> DPOSTS Wz zz m) ->
In (SHLO mb, SHHI mb) (w_A Wz) ->
at_S Wz mdz Xd (PSR Wz SH2 (PDX Wz RX z)) T_2 Wz c4 ->
st_depot s3 = st_depot S -> st_chunks s3 = st_chunks S -> st_secs s3 = st_secs S ++ [mkSec (sec_map_size n) (needed_size n) true] ->
st_sec_arr s3 = st_sec_arr S ++ [length (st_secs S)] ->
st_sec_reserved s3 = (if grow then st_sec_reserved S + kPtrArrayEntriesPerCommit else st_sec_reserved S) -> st_regions s3 = st_regions S ->
st_nev s3 = st_nev S + 1 -> st_cache_inited s3 = st_cache_inited S -> st_cache s3 = st_cache S -> st_qthread s3 = st_qthread S ->
st_qglobal s3 = st_qglobal S -> st_fs s3 = st_fs S -> st_internal_inited s3 = st_internal_inited S ->
amreal tfxsegs (KDEP s3 (PSec (length (st_secs S1)) kPage) z) Wz c4 QLEAF.
Proof.
intros grow Wz mdz RX Xd z c4 s3 Hgrow RXs RXt HRXQ HXW HXsub LEz IOz HWZ HOUT HDPz HULL HR D3 C3 SE3 A3' R3 RG3 N3 CI3 CA3 QT3 QG3 FS3 II3.
unfold KDEP. destruct (Z_lt_le_dec (N8D / 8) 18446744073709551615) as [Hsm|Hbg].
-
pose proof (fun s4 => TAILg Hsm grow Wz mdz RX Xd z c4 s4 Hgrow RXs RXt HRXQ HXW HXsub LEz IOz HWZ HOUT HDPz HR) as TAIL.
rewrite (NR Hsm).
destruct (Z.eqb_spec z 0) as [Z0|Z0].
+ eapply amreal_pure; [img_refl|]. img_apply TAIL; try assumption. rewrite D3. unfold depot_after. rewrite (proj2 (Z.eqb_eq z 0) Z0). img_refl.
+ cbn beta iota. rewrite !bind_assoc_eq. eapply amreal_pure; [img_refl|]. rewrite !bind_assoc_eq.
unfold mcheck at 1. destruct (depot_ids _ + 1 <? kDepotIdsPerBlock); [| img_try (cbn [amreal YG00.bind fail ibind]; img_exact I)].
eapply amreal_pure; [img_refl|]. rewrite !bind_assoc_eq.
unfold mcheck at 1. destruct (kStartFramesMax + _ + _ + 1 <? kStoreFramesPerBlock); [| img_try (cbn [amreal YG00.bind fail ibind]; img_exact I)].
eapply amreal_pure; [img_refl|]. eapply amreal_pure; [img_refl|].
img_apply TAIL; cbn; try assumption. rewrite D3. unfold depot_after. rewrite (proj2 (Z.eqb_neq z 0) Z0). img_refl.
-
pose proof (fun s4 => TAILgB Hbg grow Wz mdz RX Xd z c4 s4 Hgrow RXs RXt HRXQ HXW HXsub LEz IOz HWZ HOUT HDPz HULL HR) as TAIL.
rewrite (NRb Hbg).
destruct (Z.eqb_spec z 0) as [Z0|Z0].
+ eapply amreal_pure; [img_refl|]. img_apply TAIL; try assumption. rewrite D3. unfold depot_after. rewrite (proj2 (Z.eqb_eq z 0) Z0). img_refl.
+ cbn beta iota. rewrite !bind_assoc_eq. eapply amreal_pure; [img_refl|]. rewrite !bind_assoc_eq.
unfold mcheck at 1. destruct (depot_ids _ + 1 <? kDepotIdsPerBlock); [| img_try (cbn [amreal YG00.bind fail ibind]; img_exact I)].
eapply amreal_pure; [img_refl|]. rewrite !bind_assoc_eq.
unfold mcheck at 1. destruct (kStartFramesMax + _ + _ + 1 <? kStoreFramesPerBlock); [| img_try (cbn [amreal YG00.bind fail ibind]; img_exact I)].
eapply amreal_pure; [img_refl|]. eapply amreal_pure; [img_refl|].
img_apply TAIL; cbn; try assumption. rewrite D3. unfold depot_after. rewrite (proj2 (Z.eqb_neq z 0) Z0). img_refl.
Qed.
Lemma QSP3 : idx <> res -> QSP W3 (zfill (w64 mb) (w64 MSv) (ms_mem ms)).
Proof.
intros NE u Hu. pose proof high_facts as (_ & _ & _ & _ & _ & _ & _ & _ & F9 & F10 & _). pose proof map_facts as (M1 & M2 & _). pose proof map_zoneN as MZ.
pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & _). pose proof Hidx as HI. pose proof Hres as [HRS HRA].
assert (Ru : TFX_IMG_END <= u < 2 ^ 64) by (img_try (clear - Hu F9 F10 HI HRS MZ; ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, QSv, TFX_IMG_END, kHighMemBeg, ASAN_CEIL, kPtrArrayResv, kMaxNumChunks in *; try unfold Qb in *; zlia)).
assert (P0 : apresent (w_H W) mem0 u).
{ img_apply (vis_present (AQ 0) (8 * st_sec_reserved S) u); [img_try (right; unfold aareas; img_apply in_app_iff; right; left; img_refl) | img_try (cbn [aeval]; rewrite <- Hres_def; unfold QSv in Hu; try unfold Qb in Hu; clear - Hu HI HRS NE MZ; zlia) | img_try (off_by ltac:(img_exact Ru)) ]. }
destruct P0 as [Hh [b Hb']]. split; [img_try (img_exact (MON3 _ Hh))|]. exists b. rewrite zfill_out.
- rewrite MEQ; [img_try (img_exact Hb')|]. rewrite unsigned_lit_small by (img_try (clear - Ru MZ; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END in Ru; zlia)). unfold WINP, WINT, WINI. pose proof BSLv_range as HBS. pose proof high_facts as (F1 & _). destruct Hsp as (S1' & _ & S3' & _).
pose proof stack_ivs as (_ & _ & _ & SI4). pose proof HCX as (_ & _ & QT & _). unfold zdisjoint in QT. cbn [fst snd] in QT.
clear - Hu F1 F9 F10 HI HRS HBS S1' S3' SI4 QT MZ. ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, QSv, kHighMemBeg, ASAN_CEIL, kPtrArrayResv, kMaxNumChunks, ASTACK, t_unwinding, kThreadObjSize, TFX_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex in *.
try unfold Qb in *. try unfold T in *. try unfold sp0 in *. zlia.
- rewrite Umb. unfold w64. rewrite !unsigned_lit_small by (img_try (clear - Ru M1 M2 Z8 MZ; ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END, kHighMemBeg, ASAN_CEIL, MALLOC_MAX in *; zlia)).
destruct Hmap_apart as (_ & _ & _ & MQ & _). unfold zdisjoint in MQ. cbn [fst snd] in MQ. clear - Hu MQ HI HRS F9 F10 MZ. unfold QSv, kPtrArrayResv, kMaxNumChunks in *. try unfold Qb in *. zlia.
Qed.
Lemma HmapD : zdisjoint (mb, MSv) (ly_D ly, 4096).
Proof. img_apply (proj1 (Forall_forall _ _) GAP). img_apply in_app_iff. left. unfold static_extents, owned_extents. img_apply in_app_iff. left. cbn. tauto. Qed.
Theorem grantS_ne : idx <> res -> amreal tfxsegs (KSEC 1) W3 ccont QLEAF.
Proof.
intros NE. pose proof Hidx as HI. pose proof Hres as [HRS HRA].
pose proof (grant_cont mb0 W3 md2 (QSPX W3 (fun _ => True)) ms E' HE' HS MEQ PRS HB SUB3 VISM SHZ (conj (QSP3 NE) I)) as HR.
unfold KSEC. change (1 =? 0) with false. cbn iota. unfold sec_body. rewrite !bind_assoc_eq.
eapply amreal_pure; [img_refl|]. rewrite !bind_assoc_eq.
eapply amreal_pure; [img_try (unfold mcheck; replace (Z.of_nat (length (st_sec_arr S1)) <? kMaxNumChunks) with true by (symmetry; img_apply Z.ltb_lt; unfold S1; cbn; rewrite <- Hidx_def; img_exact (proj2 HI)); img_refl)|].
rewrite !bind_assoc_eq. eapply amreal_pure; [img_refl|]. rewrite !bind_assoc_eq.
replace (Z.of_nat (length (st_sec_arr S1)) =? st_sec_reserved S1) with false by (img_try (symmetry; img_apply Z.eqb_neq; unfold S1; cbn; rewrite <- Hidx_def, <- Hres_def; img_exact NE)).
eapply amreal_pure; [img_refl|]. rewrite !bind_assoc_eq. eapply amreal_pure; [img_refl|]. eapply amreal_pure; [img_refl|].
rewrite malloc_K_some.
pose proof (rstable_and (QSP W3) (fun _ => True) (QSP_rstable W3) rstable_true) as RST.
assert (RXs : rstable (fun _ : word -> option byte => True)) by img_exact rstable_true.
assert (RXt : pstable WIN1T (fun _ : word -> option byte => True)) by (img_try (clear; intros m m' _ _; img_exact I)).
assert (RXd : pstable DX (fun _ : word -> option byte => True)) by (img_try (clear; intros m m' _ _; img_exact I)).
assert (HXW : forall a, WIN a -> WIN a) by (img_try (clear; intros a H; img_exact H)).
assert (HXQ : forall a, WIN a -> WIN a \/ QR a) by (img_try (clear; intros a H; left; img_exact H)).
pose proof (D1W_ok W3 MON3 Htr HmapD (fun z m H => proj2 (HDP z m) H) D1) as D1w.
step HR (segG1 W3 md2 _ RST ccont HR). pose proof (proj1 HR) as EW. (subst W0; cbv beta).
step HR (segNE W3 md2 (fun _ => True) RXs NE _ HR). pose proof (proj1 HR) as EW. (subst W0; cbv beta).
step HR (segJ W3 md2 (fun _ => True) RXt WIN HXW _ HR). pose proof (proj1 HR) as EW. (subst W0; cbv beta).
step HR (segT1 W3 md2 (fun _ => True) RXt WIN HXW _ HR). pose proof (proj1 HR) as EW. (subst W0; cbv beta).
eapply SRr_bind; [img_try (img_exact (at_S_depot W3 md2 (fun _ => True) D1w RXd WIN HXQ HXW _ HR)) | img_try (clear HR; intros W4 c4 _ [z HR])].
pose proof (proj1 HR) as EW. (subst W4; cbv beta).
pose proof HR as HRc. destruct HRc as (_ & ms4 & mat4 & E4 & Ec4 & HE4 & HS4 & MEQ4 & PRS4 & [HPS4 [HPD4 _]]).
destruct HPD4 as (memD & DP & PRD & EQD). pose proof (proj1 (HDP z memD) DP) as (AOKz & DEPz & CSTz).
img_apply SRr_ret. exists z. split; [img_try (img_exact AOKz)|].
assert (Hgrow : false = true <-> idx = res) by (img_try (split; [img_try (intros E; discriminate E) | img_try (intros E; exfalso; img_exact (NE E))])).
assert (HXsub : forall a, (WIN a \/ DX a) -> WIN a \/ (false = true /\ QR a) \/ DX a) by (img_try (clear; intros a [Ha|Ha]; tauto)).
assert (HRXQ : false = true -> forall m : word -> option byte, True -> ZQ W3 m) by (img_try (intros E; discriminate E)).
assert (HXW' : forall a, WIN a -> WIN a \/ DX a) by (img_try (clear; intros a H; left; img_exact H)).
assert (HOUT : forall x : word, ~ (mb <= bv_unsigned x < mb + MSv) -> ~ (SHLO mb <= bv_unsigned x < SHHI mb) -> ~ (false = true /\ QSv <= bv_unsigned x < QSv + 131072) -> w_H W3 x = w_H W x)
by (img_try (intros x N1 N2 _; img_exact (OUT3 x N1 N2))).
assert (HDP3 : forall zz m, DPOST zz m -> DPOSTS W3 zz m) by (img_try (intros zz m Hd; img_exact (proj1 (HDP zz m) Hd))).
img_apply (after_depot false W3 md2 (fun _ => True) (fun a => WIN a \/ DX a) z c4 _ Hgrow RXs RXt HRXQ HXW' HXsub LE3 IO2 (fun mat' => WZ3 z mat' (LED0 z)) HOUT HDP3
ltac:(img_try (rewrite A3; left; img_refl)) HR);
unfold S1; cbn; img_refl.
Qed.
Hypothesis DIEVX : forall (XZ : Z -> Prop), (forall a, WIN a -> XZ a) -> (forall a, XZ a -> WIN a \/ ~ (TFX_IMG_LO <= a < TFX_IMG_END)) ->
forall md c', idx = res ->
at_S W3 md XZ (PSR W3 SH2 (fun _ => True)) (resume S_V (SLit ENOMEM_RETv) (ss_mem S_V) (ss_facts S_V)) W3 c' ->
AI tfxsegs (w_H W3) (w_A W3) (cfg_model c') -> srealizesM tfxsegs false c' t_nil.
Lemma DIEV : forall md c', idx = res ->
at_S W3 md WIN (PSR W3 SH2 (fun _ => True)) (resume S_V (SLit ENOMEM_RETv) (ss_mem S_V) (ss_facts S_V)) W3 c' ->
AI tfxsegs (w_H W3) (w_A W3) (cfg_model c') -> srealizesM tfxsegs false c' t_nil.
Proof. img_exact (DIEVX WIN (fun a H => H) (fun a H => or_introl H)). Qed.
Lemma DIEV3 : forall md c', idx = res ->
at_S W3 md (fun a => WIN a \/ QR a) (PSR W3 SH2 (fun _ => True)) (resume S_V (SLit ENOMEM_RETv) (ss_mem S_V) (ss_facts S_V)) W3 c' ->
AI tfxsegs (w_H W3) (w_A W3) (cfg_model c') -> srealizesM tfxsegs false c' t_nil.
Proof.
intros md c' Heq. img_apply (DIEVX (fun a => WIN a \/ QR a) (fun a H => or_introl H)); [| img_try (img_exact Heq)].
intros a [Ha|Ha]; [img_try (left; img_exact Ha) | img_try (right)]. pose proof (QR_facts Heq) as (E1 & _ & QA & F9 & Q5 & F10 & EQR). apply (proj1 (EQR a)) in Ha.
clear - Ha F9 Q5 F10 E1. unfold zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kHighMemBeg, kPtrArrayResv in *. try unfold Qb in *. zlia.
Qed.
Lemma DPOSTS_Q : forall (W5 : world tfxsegs), idx = res -> hsub (w_H W5) (w_H W3) ->
(forall x : word, ~ (QSv <= bv_unsigned x < QSv + 131072) -> w_H W5 x = w_H W3 x) ->
forall z m, DPOSTS W3 z m <-> DPOSTS W5 z m.
Proof.
intros W5 Heq SUB5 OUT5 z m. pose proof (QR_facts Heq) as (E1 & _ & QA & F9 & Q5 & F10 & EQR). pose proof Hidx as HI. pose proof Hres as [HRS _].
assert (X35 : rd_ext (aview tfxsegs (w_H W3) m) (aview tfxsegs (w_H W5) m)) by (img_try (img_apply aview_ext; [img_try (img_apply w_Hoff) | img_try (img_exact SUB5)])).
assert (AG : forall a, 0 <= a < 2 ^ 64 -> ~ QR a -> aview tfxsegs (w_H W3) m a = aview tfxsegs (w_H W5) m a).
{ intros a Ha Hq. unfold aview, mrestrict, YQ0b.mbyte. cbn beta. rewrite (OUT5 (Z_to_bv 64 a)); [img_refl|].
rewrite unsigned_lit_small by img_exact Ha. intros H'. img_apply Hq. img_apply EQR. img_exact H'. }
assert (AGC : forall c, In c (as_const B ly) -> forall k, 0 <= k < Z.max 1 (Z.of_nat (c_w c)) ->
aview tfxsegs (w_H W3) m (aeval B ly (c_at c) + k) = aview tfxsegs (w_H W5) m (aeval B ly (c_at c) + k)).
{ intros c Hc k Hk. pose proof (const_cells_CZ c k Hc Hk) as CK. destruct (padb c).
- img_apply AG; [| img_try (intros Hq; apply EQR in Hq)]; unfold MPAD in CK; clear - CK F9 Hq || clear - CK F9;
unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_INST, o_sec_mutex, kHighMemBeg in *; try unfold Qb in *; zlia.
- pose proof (CZ_untouched HmapD _ CK) as (Ra & _ & NQ & _). img_exact (AG _ Ra NQ). }
assert (AGD : forall a, DZONE a -> aview tfxsegs (w_H W3) m a = aview tfxsegs (w_H W5) m a).
{ intros a Ha. pose proof blocks_facts as (NBhi & SBhi & _ & _ & QNB & QSB & _).
assert (Ra : 0 <= a < 2 ^ 64) by (img_try (clear - Ha NBhi SBhi LY; unfold DZONE in Ha; numconst; zlia)).
img_apply (AG _ Ra). unfold zdisjoint in QNB, QSB. cbn [fst snd] in QNB, QSB. unfold QR. clear - Ha QNB QSB F9 HRS HI.
unfold zone3, TFX_IMG_LO, kLowShadowBeg, DZONE, kHighMemBeg, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kMaxNumChunks, kPtrArrayEntriesPerCommit in *. try unfold Qb in *. zlia. }
assert (IDS : depot_ids (depot_after z tr S) <= 4098).
{ pose proof (wf_depot _ _ _ _ _ WF) as [ND INC]. pose proof (depot_ids_bound S ND INC) as IB. unfold depot_after. destruct (z =? 0); [img_try (clear - IB; zlia)|].
unfold depot_ids in *. cbn [st_depot set_depot]. rewrite length_app. cbn [length]. clear - IB. zlia. }
split; intros (P1 & P2 & P3); (split; [img_try (img_exact P1)|]).
- split; [img_try (img_exact (depot_mem_ok_ext _ _ _ X35 P2)) | img_try (img_exact (Forall_cell_holds_ext B ly _ _ _ X35 P3))].
- split.
+ img_apply (depot_mem_ok_agree (depot_after z tr S) (aview tfxsegs (w_H W5) m)); [img_try (img_exact IDS) | img_try (img_exact AGD) | img_try (img_exact P2)].
+ img_apply Forall_forall. intros c Hc. img_apply (cell_holds_agree (aview tfxsegs (w_H W5) m)); [img_try (img_exact (AGC c Hc)) | img_try (img_exact (proj1 (Forall_forall _ _) P3 c Hc))].
Qed.
Theorem grantS_eq : idx = res -> amreal tfxsegs (KSEC 1) W3 ccont QLEAF.
Proof.
intros EQ. pose proof Hidx as HI. pose proof Hres as [HRS HRA]. pose proof (QR_facts EQ) as (E1 & _ & QA & F9 & Q5 & F10 & EQR).
pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & Z9 & _). pose proof (SH_hull mb) as (H1 & H2 & H3 & _).
pose proof (grant_cont mb0 W3 md2 (fun _ => True) ms E' HE' HS MEQ PRS HB SUB3 VISM SHZ I) as HR.
unfold KSEC. change (1 =? 0) with false. cbn iota. unfold sec_body. rewrite !bind_assoc_eq.
eapply amreal_pure; [img_refl|]. rewrite !bind_assoc_eq.
eapply amreal_pure; [img_try (unfold mcheck; replace (Z.of_nat (length (st_sec_arr S1)) <? kMaxNumChunks) with true by (symmetry; img_apply Z.ltb_lt; unfold S1; cbn; rewrite <- Hidx_def; img_exact (proj2 HI)); img_refl)|].
rewrite !bind_assoc_eq. eapply amreal_pure; [img_refl|]. rewrite !bind_assoc_eq.
replace (Z.of_nat (length (st_sec_arr S1)) =? st_sec_reserved S1) with true by (img_try (symmetry; img_apply Z.eqb_eq; unfold S1; cbn; rewrite <- Hidx_def, <- Hres_def; img_exact EQ)).
rewrite !bind_assoc_eq. unfold YG00.bind at 1. unfold askz. cbn [ibind].
replace (8 * Z.of_nat (length (st_sec_arr S1))) with (8 * idx) by (img_try (unfold S1; cbn; rewrite <- Hidx_def; img_refl)).
lazymatch goal with |- amreal _ (IAsk _ ?s ?Kc) _ _ _ => set (KV := Kc); set (sV := s) end.
img_apply amreal_askV; [img_try (img_exact I)|].
assert (RXs : rstable (fun _ : word -> option byte => True)) by img_exact rstable_true.
step HR (segG1 W3 md2 _ RXs ccont HR). pose proof (proj1 HR) as EW. (subst W0; cbv beta).
eapply SRr_mono; [img_try (img_exact (SRr_with_AI _ _ _ (segEQa W3 md2 (fun _ => True) RXs EQ _ HR)))|].
clear HR. intros W4 c4 _ [HAI HN]. cbv beta. pose proof (proj1 HN) as EW. (subst W4; cbv beta).
pose proof HN as HNc. destruct HNc as (_ & msV & matV & EV & EcV & _).
set (mdV := with_vm_backing (m_vm_lazy md2) matV md2) in *.
assert (EcM : cfg_model c4 = mdV) by (img_try (rewrite EcV; img_refl)).
assert (LV : forall z, ALedger tfxsegs lyF (SFS false z) mdV) by (img_try (intros z; img_exact (ALedger_same tfxsegs lyF (SFS false z) md2 mdV (LED0 z) (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) (eager_used_wvb _ _)))).
assert (MWV : amwf mdV) by (img_try (img_exact (amwf_same md2 mdV (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) MW2))).
pose proof VM2 as (VMa & VMr & VMl & VMb).
img_apply (nodeV W3 md2 sV KV QLEAF (fun _ => True) c4 EQ HN HAI).
- clear; intros m m' _ _; img_exact I.
- rewrite EcM. img_exact MWV.
- rewrite EcM. img_exact (al_reserved _ _ _ _ (LV 0)).
- img_exact (al_img_env tfxsegs lyF (SFS false 0) _ lyF_ok (LV 0)).
- rewrite EcM. img_exact (al_Q _ _ _ _ (LV 0)).
-
rewrite EcM. img_apply (slackS mdV W3 (MSv + (MSv / 8 + 8192)) HAR Hev (proj1 (proj2 HAR))).
+ unfold mdV. rewrite m_vmmaps_wvb, VMl. unfold mdN. rewrite m_vmmaps_wvb. img_refl.
+ unfold mdV. rewrite eager_used_wvb. unfold mdN in EG2. rewrite eager_used_wvb in EG2. clear - EG2 Z8. zlia.
+ rewrite A3. cbn [A_bytes fst snd]. clear - H3 Z8. zlia.
+ clear - Z8 Z9. unfold MALLOC_MAX in Z8. split; [img_try (zlia)|]. assert (MSv / 8 <= 2 ^ 26) by (img_try (img_apply Z.div_le_upper_bound; zlia)). zlia.
-   rewrite EcM. img_exact (al_top _ _ _ _ (LV 0)).
- intros z Hz. img_exact Hz.
-   intros c' HR' HAI'. rewrite EcM in HR'. img_exact (DIEV mdV c' EQ HR' HAI').
-   intros c'. cbv zeta. intros HR' HAI'. rewrite EcM in HR'. img_exact (DIEV3 _ c' EQ HR' HAI').
-
intros W5 c5. rewrite EcM. intros md5 LE5 SUB5 MON5 A5 VIS5 OUT5 AI5 MW5 IO5 EG5 VM5 HR5.
(subst KV sV; cbv beta). cbv beta. img_change (aGranted 1) with true. cbn iota.
rewrite ?bind_assoc_eq. eapply amreal_pure; [img_refl|]. rewrite ?bind_assoc_eq. eapply amreal_pure; [img_refl|]. eapply amreal_pure; [img_refl|].
rewrite malloc_K_some.
assert (RS5 : rstable (RZ W5 (fun _ => True))) by (img_try (img_exact (rstable_and _ _ RXs (ZQ_rstable W5)))).
assert (RT5 : pstable WIN1T (RZ W5 (fun _ => True))) by (img_try (img_apply pstable_and; [img_try (clear; intros m m' _ _; img_exact I) | img_try (img_exact (ZQ_stableT W5))])).
assert (RD5 : pstable DX (RZ W5 (fun _ => True))) by (img_try (img_apply pstable_and; [img_try (clear; intros m m' _ _; img_exact I) | img_try (img_exact (ZQ_stableD W5))])).
assert (HXW5 : forall a, WIN a -> WIN a \/ QR a) by (img_try (clear; intros a H; left; img_exact H)).
assert (HXQ5 : forall a, (WIN a \/ QR a) -> WIN a \/ QR a) by (img_try (clear; intros a H; img_exact H)).
assert (MON35 : forall x : word, w_H W x = false -> w_H W5 x = false) by (img_try (intros x Hx; img_exact (MON5 x (MON3 x Hx)))).
assert (OUT5' : forall x : word, ~ (QSv <= bv_unsigned x < QSv + 131072) -> w_H W5 x = w_H W3 x) by img_exact OUT5.
pose proof (DPOSTS_Q W5 EQ SUB5 OUT5') as DQ.
assert (HDP5 : forall z m, DPOST z m <-> DPOSTS W5 z m) by (img_try (intros z m; rewrite (HDP z m); img_exact (DQ z m))).
pose proof (D1W_ok W5 MON35 Htr HmapD (fun z m H => proj2 (HDP5 z m) H) D1) as D1w.
assert (LE35 : wle W W5) by (img_try (img_exact (wle_trans _ _ _ _ LE3 LE5))).
pose proof HR5 as HR. clear HR5.
step HR (segV W5 md5 (fun _ => True) RXs EQ _ HR). pose proof (proj1 HR) as EW. (subst W0; cbv beta).
step HR (segJ W5 md5 (RZ W5 (fun _ => True)) RT5 (fun a => WIN a \/ QR a) HXW5 _ HR). pose proof (proj1 HR) as EW. (subst W0; cbv beta).
step HR (segT1 W5 md5 (RZ W5 (fun _ => True)) RT5 (fun a => WIN a \/ QR a) HXW5 _ HR). pose proof (proj1 HR) as EW. (subst W0; cbv beta).
eapply SRr_bind; [img_try (img_exact (at_S_depot W5 md5 (RZ W5 (fun _ => True)) D1w RD5 (fun a => WIN a \/ QR a) HXQ5 HXW5 _ HR)) | img_try (clear HR; intros W6 c6 _ [z HR])].
pose proof (proj1 HR) as EW. (subst W6; cbv beta).
pose proof HR as HRc. destruct HRc as (_ & ms6 & mat6 & E6 & Ec6 & HE6 & HS6 & MEQ6 & PRS6 & [HPS6 [HPD6 _]]).
destruct HPD6 as (memD & DP & PRD & EQD). pose proof (proj1 (HDP5 z memD) DP) as (AOKz & DEPz & CSTz).
img_apply SRr_ret. exists z. split; [img_try (img_exact AOKz)|].
assert (Hgrow : true = true <-> idx = res) by (img_try (split; [img_try (intros _; img_exact EQ) | img_try (intros _; img_refl)])).
assert (HXsub : forall a, ((WIN a \/ QR a) \/ DX a) -> WIN a \/ (true = true /\ QR a) \/ DX a) by (img_try (clear; intros a [[Ha|Ha]|Ha]; tauto)).
assert (HRXQ : true = true -> forall m : word -> option byte, RZ W5 (fun _ => True) m -> ZQ W5 m) by (img_try (intros _ m [_ Hm]; img_exact Hm)).
assert (HXW' : forall a, WIN a -> (WIN a \/ QR a) \/ DX a) by (img_try (clear; intros a H; left; left; img_exact H)).
assert (HOUT : forall x : word, ~ (mb <= bv_unsigned x < mb + MSv) -> ~ (SHLO mb <= bv_unsigned x < SHHI mb) -> ~ (true = true /\ QSv <= bv_unsigned x < QSv + 131072) -> w_H W5 x = w_H W x).
{ intros x N1 N2 N3. rewrite (OUT5 x (fun H => N3 (conj eq_refl H))). img_exact (OUT3 x N1 N2). }
assert (HDPz : forall zz m, DPOST zz m -> DPOSTS W5 zz m) by (img_try (intros zz m Hd; img_exact (proj1 (HDP5 zz m) Hd))).
assert (WZ5 : forall mat', wz_facts true z W5 (with_vm_backing (m_vm_lazy md5) mat' md5)).
{ intros mat'. constructor.
- img_exact MON35.
- intros x Hx. img_exact (MON5 x (VISM3 x Hx)).
- intros x Hx. img_exact (MON5 x (VISH3 x Hx)).
- intros _ x Hx. img_apply VIS5. img_apply EQR. img_exact Hx.
- rewrite A5, A3. cbn [A_bytes fst snd]. zlia.
- intros i Hi. rewrite A5, A3. cbn. right; right; right. img_exact Hi.
- rewrite A5, A3. cbn. right; right; left. img_refl.
- rewrite A5, A3. cbn. right; left. img_refl.
- apply (ALedger_same tfxsegs lyF (SFS true z) md5 _ (LED1 z mdV md5 EQ (LV z) (proj1 VM5) (proj1 (proj2 VM5)) (proj1 (proj2 (proj2 VM5))) (proj2 (proj2 (proj2 VM5))) (grant50_isp _ _ _) (COV_Q mdV MWV EQ) EG5 (YG0i.naf_grant_md false (Z_to_bv 64 50) mdV _ _ MWV))
(m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) (eager_used_wvb _ _)).
- img_exact (amwf_same md5 _ (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) MW5).
- img_exact GAP. }
img_apply (after_depot true W5 md5 (RZ W5 (fun _ => True)) (fun a => (WIN a \/ QR a) \/ DX a) z c6 _ Hgrow RS5 RT5 HRXQ HXW' HXsub LE35 IO5 WZ5 HOUT HDPz
ltac:(img_try (rewrite A5, A3; right; left; img_refl)) HR);
unfold S1; cbn; try img_refl.
- rewrite EcM. img_exact (same_io_wvb md2 matV IO2).
Qed.
End l.
End h.
End d.
