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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF64 YF3v YF3w YF3x YF41 YF47 YF0a YF5k YF48 YF49 YF4b YF4c YF4d YF4e YF0h YF5t YF5u YF5v YF5f YF5l YF5m YF5i YF5j YF5n YF5o YF5q YF5s YF5r YF5w.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG0b.
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
Local Abbreviation ARg f := (f idx res Hidx) (only parsing).
Local Abbreviation tr_length := (ARg ((AR1 (@YF5k.tr_length)) ch)).
Local Abbreviation ARf f := (f idx res LY IMG Hidx Hres) (only parsing).
Local Abbreviation high_facts := (ARf (AR1 (@YF5k.high_facts _))).
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
Local Abbreviation ARc f := (AR1 f n) (only parsing).
Local Abbreviation ARh f := (ARc f idx mb) (only parsing).
Local Abbreviation WIN := (ARh (@YF5k.WIN)).
Local Abbreviation WINN := (AR1 (@YF5k.WINN)).
Local Abbreviation WINP := (ARc (@YF5k.WINP)).
Local Abbreviation WINP_WIN := (ARh (@YF5k.WINP_WIN)).
Local Abbreviation WIN1P := (ARc (@YF5k.WIN1P)).
Local Abbreviation WIN1 := (ARh (@YF5k.WIN1)).
Local Abbreviation WIN1P_WINP := ((AR3 (@YF5k.WIN1P_WINP)) Hidx).
Local Abbreviation WIN1_WIN := ((AR3 (@YF5k.WIN1_WIN)) Hidx).
Local Abbreviation WIN1P_WIN1 := (ARh (@YF5k.WIN1P_WIN1)).
Local Abbreviation LGv_range := (@YF5k.LGv_range n Nrange).
Local Abbreviation BSLv_range := ((AR3 (@YF5k.BSLv_range)) Nrange Hidx).
Local Abbreviation WSKELP := (@YF5k.WSKELP imgk).
Local Abbreviation WSKEL1P := (@YF5k.WSKEL1P imgk).
Local Abbreviation WMAP := (@YF5k.WMAP).
Local Abbreviation WSKEL := (@YF5k.WSKEL imgk).
Local Abbreviation WSKEL1 := (@YF5k.WSKEL1 imgk).
Local Abbreviation win_sub := (@YF5k.win_sub).
Local Abbreviation AR7 f := (f idx res mb) (only parsing).
Local Abbreviation win_sub_sound := ((AR7 (@YF5k.win_sub_sound ly regs0)) Hidx Hres).
Local Abbreviation in_win := (@YF5k.in_win).
Local Abbreviation ARa f := (AR0 f LY IMG) (only parsing).
Local Abbreviation ARd f := (f Nrange Hidx Hres) (only parsing).
Local Abbreviation WSKELP_WINP := (ARd (ARa (AR1 (@YF5k.WSKELP_WINP _)))).
Local Abbreviation WSKEL1P_WIN1P := (ARd (ARa (AR1 (@YF5k.WSKEL1P_WIN1P _)))).
Local Abbreviation WMAP_WINM := (AR5 (ARa (AR1 (@YF5k.WMAP_WINM _)))).
Local Abbreviation WSKEL_WIN := (AR5 (ARa (AR1 (@YF5k.WSKEL_WIN _)))).
Local Abbreviation WSKEL1_WIN1 := (AR5 (ARa (AR1 (@YF5k.WSKEL1_WIN1 _)))).
Local Abbreviation windows_in := ((AR7 (@YF5k.windows_in ly regs0)) Hidx Hres).
Local Abbreviation windows_WINP := (ARd (ARa (AR1 (@YF5k.windows_WINP _)))).
Local Abbreviation windows_WIN1P := (ARd (ARa (AR1 (@YF5k.windows_WIN1P _)))).
Local Abbreviation windows_WIN := (AR5 (ARa (AR1 (@YF5k.windows_WIN _)))).
Local Abbreviation windows_WIN1 := (AR5 (ARa (AR1 (@YF5k.windows_WIN1 _)))).
Local Abbreviation frame_WIN1P := (ARd (ARa (AR1 (@YF5k.frame_WIN1P _)))).
Local Abbreviation frame_WIN1 := (AR5 (ARa (AR1 (@YF5k.frame_WIN1 _)))).
Local Abbreviation AR2 f := (f LY IMG Hsp Nrange Hidx Hres) (only parsing).
Local Abbreviation WINP_not_high := (AR2 (AR3 (@YF5k.WINP_not_high _))).
Local Abbreviation ARj f := (AR2 f Hmap) (only parsing).
Local Abbreviation WIN_not_high := (ARj (AR3 (@YF5k.WIN_not_high _))).
Variables (mat0 : list word).
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 (0x53104 + D_2c4)) mem0 (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis U1 : tfx_unwind_spec.
Local Abbreviation all_disjoint_of_forall := (@YF5k.all_disjoint_of_forall).
Local Abbreviation img_rw_writable := ((AR7 (AR1 (@YF5k.img_rw_writable))) Hidx).
Local Abbreviation ARe f := (f imgk W ly) (only parsing).
Local Abbreviation kept_of_frame := ((AR7 ((ARe (@YF5k.kept_of_frame)) regs0)) Hidx).
Local Abbreviation SKEL_TAIL := (@YF5k.SKEL_TAIL imgk).
Local Abbreviation blocks_facts := (@YF5k.blocks_facts _ imgk ly LY IMG).
Local Abbreviation off_T := (ARf (AR1 (@YF5k.off_T _))).
Local Abbreviation off_C := (ARf (AR1 (@YF5k.off_C _))).
Local Abbreviation off_Q := (ARf (AR1 (@YF5k.off_Q _))).
Local Abbreviation off_NB := (@YF5k.off_NB _ imgk ly LY IMG).
Local Abbreviation off_SB := (@YF5k.off_SB _ imgk ly LY IMG).
Local Abbreviation off_shadow := ((AR7 (AR1 (@YF5k.off_shadow))) Hidx).
Ltac off_by tac :=
first [ img_apply off_img_high; tac | img_apply off_T; tac | img_apply off_C; tac | img_apply off_Q; tac | img_apply off_NB; tac | img_apply off_SB; tac
| img_apply map_off_img; tac | img_apply off_shadow; tac
| unfold off_img; unfold TFX_IMG_LO; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; tac ].
Local Abbreviation DZONE := (@YF5k.DZONE imgk ly).
Variable DPOST : Z -> (word -> option byte) -> Prop.
Local Abbreviation AR6 f := (AR2 f Hmap Hmap_apart) (only parsing).
Local Abbreviation DZONE_disj := (AR6 (AR3 (@YF5k.DZONE_disj _))).
Local Abbreviation RFACTS := (AR1 (@YF5k.RFACTS)).
Local Abbreviation zone_lit := ((AR1 (@YF5k.zone_lit _)) LY IMG Hsp).
Local Abbreviation zone_irw := ((AR1 (@YF5k.zone_irw _)) LY IMG Hsp).
Local Abbreviation zone_T := ((AR1 (@YF5k.zone_T _)) idx res LY IMG Hsp Hidx Hres).
Local Abbreviation zone_C := ((AR1 (@YF5k.zone_C _)) idx res LY IMG Hsp Hidx Hres).
Local Abbreviation tail_ext_ok := (AR2 (AR0 (AR1 (@YF5k.tail_ext_ok _)))).
Local Abbreviation RFACTS_map := ((AR5 ((AR3 (@YF5k.RFACTS_map _)) LY IMG)) Hmap_apart).
Local Abbreviation AR4 f := (f imgk W ly regs0 mem0) (only parsing).
Local Abbreviation ARl f := (AR4 f md0) (only parsing).
Local Abbreviation at_ST := (AR0 (ARl (@YF5k.at_ST _))).
Local Abbreviation memset_stretch := ((AR5 ((AR7 ((ARl (@YF5k.memset_stretch _ _)) n)) Hsp)) Hmap_apart mat0 DPOST).
Ltac clearM := try clear DPOST; try clear Hmap_apart; try clear Hmap.
Local Abbreviation AR9 f := (AR1 f mem0) (only parsing).
Local Abbreviation at_S := (AR0 (AR9 (@YF5k.at_S _))).
Local Abbreviation at_N := (AR0 (AR9 (@YF5k.at_N _))).
Local Abbreviation at_RETS := (@YF5k.at_RETS _ regs0 mem0 imgk).
Local Abbreviation pstable := (@YF5k.pstable).
Local Abbreviation stack_shaped := (@YF5k.stack_shaped).
Local Abbreviation window_present := (ARg (AR1 (@YF5k.window_present))).
Local Abbreviation stack_present_of := ((AR0 (AR1 (@YF5k.stack_present_of _))) LY Hsp Hidx).
Local Abbreviation mid_not_WIN1P := (AR2 (AR3 (@YF5k.mid_not_WIN1P _))).
Local Abbreviation mid_not_WIN1 := (ARj (AR3 (@YF5k.mid_not_WIN1 _))).
Local Abbreviation wins_ok := (@YF5k.wins_ok).
Local Abbreviation at_S_run_gen := ((AR0 (AR9 (@YF5k.at_S_run_gen _ _))) LY Hsp Hidx).
Local Abbreviation at_S_run_ecall_gen := ((AR0 (AR9 (@YF5k.at_S_run_ecall_gen _ _))) LY Hsp Hidx).
Local Abbreviation at_S_runP := (AR2 (AR0 (AR9 (@YF5k.at_S_runP _ _)))).
Local Abbreviation at_S_runM := (ARj (AR0 (AR9 (@YF5k.at_S_runM _ _)))).
Local Abbreviation at_S_run_ecallP := (AR2 (AR0 (AR9 (@YF5k.at_S_run_ecallP _ _)))).
Local Abbreviation at_S_run_ecallM := (ARj (AR0 (AR9 (@YF5k.at_S_run_ecallM _ _)))).
Local Abbreviation at_S_pin := (AR0 (AR9 (@YF5k.at_S_pin _))).
Local Abbreviation at_S_arm := (AR0 (AR9 (@YF5k.at_S_arm _))).
Local Abbreviation at_S_forget := (AR0 (AR9 (@YF5k.at_S_forget _))).
Local Abbreviation at_S_noconds := (AR0 (AR9 (@YF5k.at_S_noconds _))).
Local Abbreviation at_S_weaken := (AR0 (AR9 (@YF5k.at_S_weaken _))).
Local Abbreviation at_S_facts := (AR0 (AR9 (@YF5k.at_S_facts _))).
Local Abbreviation at_S_strengthen := (AR0 (AR9 (@YF5k.at_S_strengthen _))).
Local Abbreviation at_S_eq := (AR0 (AR9 (@YF5k.at_S_eq _))).
Local Abbreviation at_S_open := (AR0 (AR9 (@YF5k.at_S_open _))).
Local Abbreviation CSAVEDS := (@YF5k.CSAVEDS).
Local Abbreviation sv_denot_SOff0 := (@YF5k.sv_denot_SOff0).
Local Abbreviation at_S_ret := (ARd ((AR0 (AR9 (@YF5k.at_S_ret _))) Htp Hra Hsp)).
Local Abbreviation kept_of_frame2 := (ARg (AR1 (@YF5k.kept_of_frame2))).
Local Abbreviation at_N_cont := ((AR0 (AR9 (@YF5k.at_N_cont _ _))) LY Hsp Hidx).
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
Local Abbreviation ARi f := (f B S HARm) (only parsing).
Local Abbreviation vis_present := (ARi ((ARg (AR4 (@YF5t.vis_present _))) DPOST)).
Local Abbreviation in_thread_junk := (@YF5t.in_thread_junk ly B S).
Local Abbreviation in_sec_junk := (@YF5t.in_sec_junk ly B S).
Local Abbreviation in_as_junk := (@YF5t.in_as_junk ly B S).
Local Abbreviation junk_word := (ARi ((ARf (AR4 (@YF5t.junk_word _))) DPOST)).
Local Abbreviation cell_sym := ((ARe (@YF5t.cell_sym _)) mem0 B S TS HARm).
Local Abbreviation cell_lit := ((ARe (@YF5t.cell_lit _)) mem0 B S TS HARm).
Local Abbreviation cell_state := (ARi ((ARe (@YF5t.cell_state _)) mem0)).
Local Abbreviation In_acells_sec := (@YF5t.In_acells_sec ly B S).
Local Abbreviation sec_vals := ((ARe (@YF5t.sec_vals _)) mem0 idx res B S TS HARm Hidx_def Hres_def).
Local Abbreviation unwinding_val := (ARi ((ARe (@YF5t.unwinding_val _)) mem0)).
Local Abbreviation rw_writable := ((ARg (AR1 (@YF5t.rw_writable))) DPOST S).
Local Abbreviation val_mem_mod8 := ((ARg (AR4 (@YF5t.val_mem_mod8))) DPOST S).
Local Abbreviation chunk_lit := (AR0 (AR4 (@YF5t.chunk_lit))).
Local Abbreviation chunk_lit_at := (AR0 (AR4 (@YF5t.chunk_lit_at))).
Local Abbreviation chunk_atom := ((AR0 (AR4 (@YF5t.chunk_atom))) Hidx DPOST S).
Local Abbreviation ARb f := (f DPOST B S TS HTSD HARm Hidx_def Hres_def Hj0 Hj1 Hj2 Hj3 Hj4 Hj5 Hj9 Hj6 Hj7 Hj8 Hi1 Hi2 Hi3) (only parsing).
Local Abbreviation SREG0_ok := (ARb ((AR2 (AR0 (AR4 (@YF5u.SREG0_ok _)))) Hpres0)).
Local Abbreviation PAIRS_ok := ((AR2 (AR0 (AR4 (@YF5v.PAIRS_ok _)))) DPOST S).
Local Abbreviation FACTS_ok := ((ARd ((ARa (AR4 (@YF5v.FACTS_ok _))) Hn Hsp)) DPOST S).
Local Abbreviation SEED_ok := (ARb ((ARd ((ARa (AR4 (@YF5v.SEED_ok _ _))) Hn Htp Hsp)) Hpres0)).
Local Abbreviation PBUF := ((ARe (@YF5f.PBUF)) regs0 ch).
Local Abbreviation PBUF_stableP := (AR2 (AR7 ((ARe (@YF5f.PBUF_stableP _)) regs0 n ch))).
Local Abbreviation PBUF_stableM := (ARj (AR7 ((ARe (@YF5f.PBUF_stableM _)) regs0 n ch))).
Local Abbreviation seg0 := (ARb ((ARd ((ARa (ARl (@YF5f.seg0 _ _))) Hn Htp Hra4096 Hsp Hch)) Hpres0 mat0 U1)).
Local Abbreviation appregs := (@YF5l.appregs).
Local Abbreviation st_ok_appregs := (@YF5l.st_ok_appregs _ imgk).
Local Abbreviation at_S_app := (AR0 (AR9 (@YF5l.at_S_app _))).
Local Abbreviation WIN1N := (ARc (@YF5l.WIN1N)).
Local Abbreviation WINPN := (ARc (@YF5l.WINPN)).
Local Abbreviation WSKEL1N := (@YF5l.WSKEL1N imgk).
Local Abbreviation WIN1N_WINPN := ((AR3 (@YF5l.WIN1N_WINPN)) Hidx).
Local Abbreviation windows_WIN1N := (ARd (ARa (AR1 (@YF5l.windows_WIN1N _)))).
Local Abbreviation mid_not_WIN1N := (AR2 (AR3 (@YF5l.mid_not_WIN1N _))).
Local Abbreviation at_S_runN := (AR2 (AR0 (AR9 (@YF5l.at_S_runN _ _)))).
Local Abbreviation PBUF_stableN := (AR2 (AR7 ((ARe (@YF5l.PBUF_stableN _)) regs0 n ch))).
Local Abbreviation at_S_val := (AR0 (AR9 (@YF5l.at_S_val _))).
Local Abbreviation memset_stretchW := ((ARd ((ARl (@YF5l.memset_stretchW _)) n idx res Hsp)) mat0 DPOST S).
Local Abbreviation at_S_memset := ((ARd ((AR0 (ARl (@YF5l.at_S_memset _))) Hsp)) mat0 DPOST S).
Local Abbreviation WIN1T := (ARh (@YF5l.WIN1T)).
Local Abbreviation WIN1T_WIN := (AR5 (AR3 (@YF5l.WIN1T_WIN _))).
Local Abbreviation windows_WIN1T := (AR5 (ARa (AR1 (@YF5l.windows_WIN1T _)))).
Local Abbreviation WIN1T_WIN1_aux := (AR5 (AR3 (@YF5l.WIN1T_WIN1_aux _))).
Local Abbreviation mid_not_WIN1T := (ARj (AR3 (@YF5l.mid_not_WIN1T _))).
Local Abbreviation at_S_runT := (ARj (AR0 (AR9 (@YF5l.at_S_runT _ _)))).
Local Abbreviation at_S_run_ecallT := (ARj (AR0 (AR9 (@YF5l.at_S_run_ecallT _ _)))).
Local Abbreviation PBUFW := ((AR1 (@YF5l.PBUFW)) ch).
Local Abbreviation PBUFW_stableT := (ARj (AR7 ((ARc (@YF5l.PBUFW_stableT _)) ch))).
Local Abbreviation WIN1S := (ARh (@YF5m.WIN1S)).
Local Abbreviation WSKEL1S := (@YF5m.WSKEL1S imgk).
Local Abbreviation WIN1S_WIN1T := (ARh (@YF5m.WIN1S_WIN1T)).
Local Abbreviation WIN1S_WIN := (AR5 (AR3 (@YF5m.WIN1S_WIN _))).
Local Abbreviation windows_WIN1S := (AR5 (ARa (AR1 (@YF5m.windows_WIN1S _)))).
Local Abbreviation mid_not_WIN1S := (ARj (AR3 (@YF5m.mid_not_WIN1S _))).
Local Abbreviation at_S_runS := (ARj (AR0 (AR9 (@YF5m.at_S_runS _ _)))).
Local Abbreviation at_S_run_ecallS := (ARj (AR0 (AR9 (@YF5m.at_S_run_ecallS _ _)))).
Local Abbreviation brun := (@YF5m.brun).
Local Abbreviation run_ok := (@YF5m.run_ok n mb).
Local Abbreviation PS := ((ARc (@YF5m.PS)) ch mb).
Local Abbreviation runs_not_WIN1S := (AR6 (AR3 (@YF5m.runs_not_WIN1S _))).
Local Abbreviation runs_not_stack := ((AR5 ((AR3 (@YF5m.runs_not_stack _)) LY Hsp)) Hmap_apart).
Local Abbreviation PS_stable := (AR6 (AR7 ((ARc (@YF5m.PS_stable _)) ch))).
Local Abbreviation cut1 := (@YF5m.cut1).
Local Abbreviation cut := (@YF5m.cut).
Local Abbreviation cut_sound := ((AR5 (AR7 ((AR9 (@YF5m.cut_sound _)) n))) DPOST S).
Local Abbreviation cut_ok := ((AR7 (@YF5m.cut_ok ly regs0 mem0 n)) Hidx Hres DPOST S).
Local Abbreviation at_S_memsetS := ((AR5 ((AR0 (ARl (@YF5m.at_S_memsetS _ _))) LY Hsp)) Hmap_apart mat0 DPOST S).
Local Abbreviation skel_okb := (@YF5m.skel_okb imgk).
Local Abbreviation skel_cases := ((ARg (@YF5m.skel_cases imgk)) Hres S Hidx_def Hres_def).
Local Abbreviation AR8 f := (f DPOST S Hidx_def Hres_def) (only parsing).
Local Abbreviation skel_apart := (AR8 (AR6 (AR0 (AR9 (@YF5m.skel_apart _))))).
Local Abbreviation skel_u64 := (AR8 (ARj (AR0 (AR9 (@YF5m.skel_u64 _))))).
Local Abbreviation memset_ext_of_skel := (AR8 (AR6 (AR0 (AR9 (@YF5m.memset_ext_of_skel _))))).
Local Abbreviation memset_u64_of_skel := (AR8 (ARj (AR0 (AR9 (@YF5m.memset_u64_of_skel _))))).
Local Abbreviation WIN1R := ((ARc (@YF5m.WIN1R)) mb).
Local Abbreviation WSKEL1R := (@YF5m.WSKEL1R imgk).
Local Abbreviation WIN1R_WIN1S := (ARh (@YF5m.WIN1R_WIN1S)).
Local Abbreviation WIN1R_WIN := (AR5 (AR3 (@YF5m.WIN1R_WIN _))).
Local Abbreviation windows_WIN1R := (AR5 (ARa (AR1 (@YF5m.windows_WIN1R _)))).
Local Abbreviation mid_not_WIN1R := (ARj (AR3 (@YF5m.mid_not_WIN1R _))).
Local Abbreviation at_S_runR := (ARj (AR0 (AR9 (@YF5m.at_S_runR _ _)))).
Local Abbreviation at_S_run_ecallR := (ARj (AR0 (AR9 (@YF5m.at_S_run_ecallR _ _)))).
Local Abbreviation PSR := ((ARc (@YF5m.PSR)) ch mb).
Local Abbreviation rstable := ((ARc (@YF5m.rstable)) mb).
Local Abbreviation rstable_true := ((ARc (@YF5m.rstable_true)) mb).
Local Abbreviation PSR_stable := (AR6 (AR7 ((ARc (@YF5m.PSR_stable _)) ch))).
Local Abbreviation QSP := (@YF5m.QSP imgk ly idx).
Local Abbreviation QS_not_WIN1R := (AR6 (AR3 (@YF5m.QS_not_WIN1R _))).
Local Abbreviation QSP_rstable := (AR6 (AR3 (@YF5m.QSP_rstable _))).
Local Abbreviation at_S_memsetSR := ((AR5 ((AR0 (ARl (@YF5m.at_S_memsetSR _ _))) LY Hsp)) Hmap_apart mat0 DPOST S).
Local Abbreviation chunk_eqb := (@YF5m.chunk_eqb imgk).
Local Abbreviation chunk_eqb_eq := ((ARg (@YF5m.chunk_eqb_eq imgk)) Hres S Hidx_def Hres_def).
Local Abbreviation subregionb := (@YF5m.subregionb imgk).
Local Abbreviation subregionb_sound := (AR8 ((ARg (AR9 (@YF5m.subregionb_sound))) Hres)).
Local Abbreviation submemb := (@YF5m.submemb imgk).
Local Abbreviation submemb_sound := (AR8 ((ARg (AR9 (@YF5m.submemb_sound))) Hres)).
Local Abbreviation at_S_submem := (AR8 ((AR0 (AR9 (@YF5m.at_S_submem _))) Hidx Hres)).
Local Abbreviation at_S_addreg := (AR0 (AR9 (@YF5m.at_S_addreg _))).
Local Abbreviation PSR_runs := (AR0 (AR9 (@YF5i.PSR_runs _))).
Local Abbreviation place_WIN := (ARh (@YF5i.place_WIN)).
Local Abbreviation SH0 := (@YF5i.SH0 n mb).
Local Abbreviation SH1 := (@YF5i.SH1 n mb).
Local Abbreviation SH2 := (@YF5i.SH2 n mb).
Local Abbreviation SH_ok := (AR5 (AR3 (@YF5i.SH_ok _))).
Local Abbreviation segG1 := (AR8 ((AR6 (AR0 (ARl (@YF5i.segG1 _ _)))) mat0)).
Local Abbreviation RX_stableS := (ARh (@YF5j.RX_stableS)).
Local Abbreviation rstable_and := ((ARc (@YF5j.rstable_and)) mb).
Local Abbreviation pstable_and := (@YF5j.pstable_and).
Local Abbreviation PSR_stableS' := (AR6 (AR7 ((ARc (@YF5j.PSR_stableS' _)) ch))).
Local Abbreviation pairwise_disjoint_map := (@YF5j.pairwise_disjoint_map).
Local Abbreviation at_S_setchunks := (AR0 (AR9 (@YF5j.at_S_setchunks _))).
Local Abbreviation chunk_ok_CVal_eqv := (@YF5j.chunk_ok_CVal_eqv imgk).
Local Abbreviation RES2T_ne := ((AR0 (AR1 (@YF5j.RES2T_ne))) Hidx Hres).
Local Abbreviation RES2T_eq := ((AR0 (AR1 (@YF5j.RES2T_eq))) Hidx Hres).
Local Abbreviation sv_denot_eq_of_U := (AR0 (AR1 (@YF5j.sv_denot_eq_of_U))).
Local Abbreviation skel_apart_QS := (AR8 (AR6 (AR0 (AR9 (@YF5j.skel_apart_QS _))))).
Local Abbreviation QSPX := (@YF5j.QSPX imgk ly idx).
Local Abbreviation segNE := (AR8 (AR6 (AR0 (AR9 (@YF5j.segNE _ _))))).
Local Abbreviation segEQa := (AR6 (AR0 (AR9 (@YF5j.segEQa _ _)))).
Local Abbreviation zev_SAlu := (@YF5j.zev_SAlu).
Local Abbreviation zev_SLit := (@YF5j.zev_SLit).
Local Abbreviation zev_SOff := (@YF5j.zev_SOff).
Local Abbreviation segJ2 := (AR8 (AR6 (AR0 (AR9 (@YF5j.segJ2 _ _))))).
Local Abbreviation segJ := (AR8 (AR6 (AR0 (AR9 (@YF5j.segJ _ _))))).
Local Abbreviation QR := (@YF5n.QR ly res).
Local Abbreviation segT1 := ((AR5 ((ARa (AR9 (@YF5n.segT1 _ _))) Hn Hsp)) Hmap_apart).
Local Abbreviation DX := (AR1 (@YF5n.DX)).
Local Abbreviation PD := (@YF5n.PD imgk ly mem0 DPOST).
Local Abbreviation PD_rstable := ((AR6 (AR7 ((AR9 (@YF5n.PD_rstable _)) n))) DPOST).
Local Abbreviation PD_stableT := ((AR6 (AR7 ((AR9 (@YF5n.PD_stableT _)) n))) DPOST).
Local Abbreviation PSR_stableS := (AR6 (AR7 ((ARc (@YF5n.PSR_stableS _)) ch))).
Local Abbreviation PD_stableS := ((AR6 (AR7 ((AR9 (@YF5n.PD_stableS _)) n))) DPOST).
Local Abbreviation PDX := (@YF5n.PDX imgk ly mem0 DPOST).
Local Abbreviation PDX_rstable := ((AR6 (AR7 ((AR9 (@YF5n.PDX_rstable _)) n))) DPOST).
Local Abbreviation PDX_stableT := ((AR6 (AR7 ((AR9 (@YF5n.PDX_stableT _)) n))) DPOST).
Local Abbreviation PDX_stableS := ((AR6 (AR7 ((AR9 (@YF5n.PDX_stableS _)) n))) DPOST).
Local Abbreviation dx_okb := (@YF5n.dx_okb imgk).
Local Abbreviation skel_apart_DX := (AR8 (AR6 (AR0 (AR9 (@YF5n.skel_apart_DX _))))).
Local Abbreviation skel_apart_stk := ((AR6 (AR0 (AR1 (@YF5n.skel_apart_stk _)))) S Hidx_def Hres_def).
Local Abbreviation at_S_depot := (AR8 (AR6 (AR0 (AR4 (@YF5n.at_S_depot _ _))))).
Local Abbreviation SH3 := (@YF5n.SH3 n mb).
Local Abbreviation SH4 := (@YF5n.SH4 n mb).
Local Abbreviation shadow_marks := (AR5 (AR3 (@YF5n.shadow_marks _))).
Local Abbreviation SH34_ok := (AR5 (AR3 (@YF5n.SH34_ok _))).
Local Abbreviation segT2b := (AR8 ((AR5 ((ARa (ARl (@YF5n.segT2b _ _))) Hn Hsp)) Hmap_apart mat0)).
Local Abbreviation segT2 := (AR8 ((AR5 ((ARa (ARl (@YF5n.segT2 _ _))) Hn Hsp)) Hmap_apart mat0)).
Local Abbreviation SH5 := (@YF5o.SH5 n mb).
Local Abbreviation SH6 := (@YF5o.SH6 n mb).
Local Abbreviation user_marks := (AR5 (AR3 (@YF5o.user_marks _))).
Local Abbreviation SH56_ok := (AR5 (AR3 (@YF5o.SH56_ok _))).
Local Abbreviation segU1 := (AR8 ((AR6 (AR0 (ARl (@YF5o.segU1 _ _)))) mat0)).
Local Abbreviation SH6_of_cut := (AR5 (AR3 (@YF5o.SH6_of_cut _))).
Local Abbreviation segUe := (AR8 ((AR5 ((ARa (ARl (@YF5o.segUe _ _))) Hn Hsp)) Hmap_apart mat0)).
Local Abbreviation PT := ((ARc (@YF5o.PT)) ch mb).
Local Abbreviation run_okT := (@YF5o.run_okT n mb).
Local Abbreviation SH5o := (@YF5o.SH5o n mb).
Local Abbreviation SH6o := (@YF5o.SH6o n mb).
Local Abbreviation SH56o_ok := (AR5 (AR3 (@YF5o.SH56o_ok _))).
Local Abbreviation PT_stableT := (AR6 (AR7 ((ARc (@YF5o.PT_stableT _)) ch))).
Local Abbreviation segUo := (AR8 ((AR5 ((ARa (ARl (@YF5o.segUo _ _))) Hn Hsp)) Hmap_apart mat0)).
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
Local Abbreviation slackS := ((ARi ((ARe (@YF5q.slackS _)) mem0 md0)) HQT).
Local Abbreviation S_N_facts := (@YF5q.S_N_facts imgk).
Local Abbreviation S_N_ext64 := ((AR2 (AR0 (AR1 (@YF5q.S_N_ext64 _)))) S).
Local Abbreviation S_N_win64 := ((AR2 (AR0 (AR1 (@YF5q.S_N_win64 _)))) S).
Local Abbreviation nodeS := ((ARi (AR2 (AR0 (ARl (@YF5q.nodeS _ _))))) HQT).
Local Abbreviation CZI := (@YF5s.CZI imgk).
Local Abbreviation CZ := (@YF5s.CZ imgk ly).
Local Abbreviation abs_cell_okS := (@YF5s.abs_cell_okS imgk).
Local Abbreviation abs_cells_okS := (@YF5s.abs_cells_okS imgk).
Local Abbreviation MPAD := (@YF5s.MPAD imgk).
Local Abbreviation padb := (@YF5s.padb imgk).
Local Abbreviation const_cells_CZ := ((AR3 (@YF5s.const_cells_CZ)) Nrange Hidx B TS HTSD).
Local Abbreviation CZ_untouched := ((AR6 (AR7 ((AR9 (@YF5s.CZ_untouched _)) n))) DPOST S).
Local Abbreviation cell_holds_agree := ((ARg (@YF5s.cell_holds_agree ly regs0 mem0)) Hres DPOST B S).
Local Abbreviation aview_agreeW := (@YF5s.aview_agreeW imgk W).
Local Abbreviation rd_ext_Wy := (@YF5s.rd_ext_Wy imgk W).
Local Abbreviation depot_ids_bound := ((AR7 (AR9 (@YF5s.depot_ids_bound))) Hidx Hres DPOST B S TS).
Local Abbreviation depot_mem_ok_agree := ((AR7 (AR9 (@YF5s.depot_mem_ok_agree))) Hidx Hres DPOST B S TS).
Local Abbreviation depot_mem_ok_ext := (@YF5s.depot_mem_ok_ext ly B).
Local Abbreviation depot_at0 := (ARi ((AR5 ((AR7 ((AR4 (@YF5s.depot_at0 _)) n)) Hsp)) Hmap_apart DPOST)).
Local Abbreviation DPOSTS := ((AR1 (@YF5s.DPOSTS)) ch B S).
Local Abbreviation D1W_ok := ((AR6 (AR7 ((AR4 (@YF5s.D1W_ok _ _)) n ch))) DPOST B S TS HTSD HARm Hgp).
Local Abbreviation S_VG := (@YF5r.S_VG imgk).
Local Abbreviation TQ := (@YF5r.TQ).
Local Abbreviation S_V_facts := (@YF5r.S_V_facts imgk).
Local Abbreviation ZQF := (@YF5r.ZQF imgk ly res).
Local Abbreviation ZQ := (@YF5r.ZQ imgk ly idx res).
Local Abbreviation QR_facts := ((AR7 (AR1 (@YF5r.QR_facts _))) LY IMG Hidx Hres S Hidx_def).
Local Abbreviation ZQ_of_ZQF := (@YF5r.ZQ_of_ZQF imgk ly idx res).
Local Abbreviation QR_not_WIN1T := ((AR6 (AR3 (@YF5r.QR_not_WIN1T _))) S Hidx_def).
Local Abbreviation ZQ_stableT := ((AR6 (AR3 (@YF5r.ZQ_stableT _))) S Hidx_def).
Local Abbreviation ZQ_rstable := ((AR6 (AR3 (@YF5r.ZQ_rstable _))) S Hidx_def).
Local Abbreviation ZQ_stableD := ((AR7 (AR1 (@YF5r.ZQ_stableD _))) LY IMG Hsp Hidx Hres S Hidx_def).
Local Abbreviation skel_apart_Q := ((AR6 (AR0 (AR1 (@YF5r.skel_apart_Q _)))) S Hidx_def Hres_def).
Local Abbreviation TQ_val := ((ARa (AR1 (@YF5r.TQ_val _))) Hidx Hres S Hidx_def).
Local Abbreviation nores50 := (@YF5r.nores50).
Local Abbreviation core50 := (@YF5r.core50).
Local Abbreviation pru17 := (@YF5r.pru17).
Local Abbreviation grant_piece_shape := (@YF5r.grant_piece_shape).
Local Abbreviation nodeV := (AR8 (AR6 (AR0 ((AR9 (@YF5r.nodeV _ _)) md0)))).
Local Abbreviation RZF := (@YF5r.RZF imgk ly res).
Local Abbreviation RZ := (@YF5r.RZ imgk ly idx res).
Local Abbreviation ZQF_rstable := ((AR6 (AR3 (@YF5r.ZQF_rstable _))) S Hidx_def).
Local Abbreviation segV := (AR8 (AR6 (AR0 (AR9 (@YF5r.segV _ _))))).
Local Abbreviation lyF := (@YF5w.lyF ly mb S).
Local Abbreviation SFS := ((ARc (@YF5w.SFS)) ch S).
Local Abbreviation KSc := (@YF5w.KSc n S).
Local Abbreviation lyF_le := (@YF5w.lyF_le ly mb S).
Local Abbreviation lyF_sec := (@YF5w.lyF_sec ly mb S).
Local Abbreviation lyF_eqs := (@YF5w.lyF_eqs ly mb S).
Local Abbreviation lyF_ok := (@YF5w.lyF_ok _ ly mb LY S).
Local Abbreviation sizes_model := (@YF5w.sizes_model ly regs0 n res Nrange S).
Local Abbreviation val_mem_cell := ((AR1 (@YF5w.val_mem_cell)) res B S).
Local Abbreviation ARk f := (f ly regs0 res S) (only parsing).
Local Abbreviation le_byte_1_0 := (ARk (@YF5w.le_byte_1_0)).
Local Abbreviation find_chunk_at_app1 := (@YF5w.find_chunk_at_app1 B).
Local Abbreviation find_chunk_at_app2 := (@YF5w.find_chunk_at_app2 B).
Local Abbreviation In_combine_seq_app := (@YF5w.In_combine_seq_app).
Local Abbreviation combine_seq_last := (ARk (@YF5w.combine_seq_last)).
Local Abbreviation in_combine_seq := (ARk (@YF5w.in_combine_seq)).
Local Abbreviation combine_seq_in := (ARk (@YF5w.combine_seq_in)).
Local Abbreviation index_of_app_old := (@YF5w.index_of_app_old).
Local Abbreviation index_ofZ_app_old := (@YF5w.index_ofZ_app_old).
Local Abbreviation index_of_app_new := (ARk (@YF5w.index_of_app_new)).
Local Abbreviation index_ofZ_app_new := (ARk (@YF5w.index_ofZ_app_new)).
Local Abbreviation fin_facts := ((AR7 ((AR9 (@YF5w.fin_facts)) n ch)) B S).
Local Abbreviation wz_facts := ((ARe (@YF5w.wz_facts _)) regs0 n ch res mb S).
Local Abbreviation S_AR_final := ((AR6 (AR7 ((ARl (@YF5w.S_AR_final _)) n ch))) DPOST B S TS HTSD HARm Hidx_def Hres_def imgk).
Local Abbreviation SF_parts := ((ARc (@YF5w.SF_parts)) ch res S Hres_def).
Local Abbreviation rS_not_in_arr := (ARi ((AR4 (@YF5w.rS_not_in_arr _)) n res mb)).
Local Abbreviation len_arr := (@YF5w.len_arr idx S Hidx_def).
Local Abbreviation ck_base_new := (@YF5w.ck_base_new ly regs0 n res mb Nrange B S).
Local Abbreviation SEF := ((ARi ((AR4 (@YF5w.SEF _)) n ch res mb Nrange)) Hres_def).
Local Abbreviation staticF := (@YF5w.staticF ly mb S).
Local Abbreviation placed_finalG := ((ARi (AR5 (AR7 ((ARl (@YF5w.placed_finalG _)) n ch)))) Hres_def).
Local Abbreviation sec_live_final := ((ARc (@YF5w.sec_live_final)) ch res mb Nrange S Hres_def).
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
Let rd0 : reader := aview tfxsegs (w_H W) mem0.
Let WF := am_wf B ly S rd0 HARm.
Definition FQ (Wz : world tfxsegs) (grow : bool) (m : word -> option byte) : Prop :=
let mr := mrestrict (w_H Wz) m in
val_mem tfxsegs mr QSv 8 mb /\ val_mem tfxsegs mr mb 8 mb /\ val_mem tfxsegs mr (mb + 8) 8 MSv /\ val_mem tfxsegs mr (mb + 16) 8 NDv /\ val_mem tfxsegs mr (mb + 24) 8 idx /\
val_mem tfxsegs mr Kv 8 0xCC6E96B9CC6E96B9 /\ val_mem tfxsegs mr (Kv + 8) 8 (Uv - 16) /\ val_mem tfxsegs mr (Uv - 16) 1 2 /\ val_mem tfxsegs mr (Uv - 15) 1 17 /\
val_mem tfxsegs mr (Uv - 14) 2 0 /\ val_mem tfxsegs mr (Uv - 12) 4 n /\ val_mem tfxsegs mr (T + t_unwinding) 1 0 /\
val_mem tfxsegs mr (TFX_INST + o_sec_reserved) 8 (if grow then res + kPtrArrayEntriesPerCommit else res) /\ val_mem tfxsegs mr (TFX_INST + o_sec_n) 8 (idx + 1) /\
val_mem tfxsegs mr (TFX_INST + o_sec_mutex) 1 0 /\ val_mem tfxsegs mr (TFX_INST + o_sec_mutex + 1) 1 0 /\ val_mem tfxsegs mr (TFX_INST + o_sec_mutex + 2) 2 0 /\
(forall a, WINT a \/ (QSv <= a < QSv + 8) \/ (mb <= a < mb + 6144) -> apresent (w_H Wz) m a) /\
(forall a, WINI a -> aview tfxsegs (w_H Wz) m a <> None).
Section h.
Variables (Wz : world tfxsegs) (mdl : Model) (X : Z -> Prop) (RX : (word -> option byte) -> Prop) (grow : bool) (z : Z).
Hypothesis Hgrow : grow = true <-> idx = res.
Hypothesis HXsub : forall a, X a -> WIN a \/ (grow = true /\ QR a) \/ DX a.
Hypothesis HRXQ : grow = true -> forall m, RX m -> ZQ Wz m.
Hypothesis HDPOST : forall zz m, DPOST zz m ->
aok S (KDepot tr) zz /\ depot_mem_ok B ly (depot_after zz tr S) (aview tfxsegs (w_H Wz) m) /\ Forall (cell_holds B ly (aview tfxsegs (w_H Wz) m)) (as_const B ly).
Lemma srl32_n : Z.shiftr n 32 = 0.
Proof. clearP. pose proof Nrange as NR. unfold MALLOC_MAX in NR. rewrite Z.shiftr_div_pow2 by zlia. img_apply Z.div_small. zlia. Qed.
Lemma FQ_e : forall (E' : env) ms, env_agree sHAV E0 E' -> st_ok tfxsegs E' Ue_RET (restrict (w_H Wz) ms) -> FQ Wz grow (ms_mem ms).
Proof.
intros E' ms HE HS. pose proof (proj1 HE) as HEn.
pose proof map_facts as (M1 & M2 & M3 & M4 & M5 & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _). pose proof map_zoneN as MZ. pose proof size_facts as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & _).
pose proof high_facts as (F1 & F2 & _ & _ & _ & _ & _ & _ & F9 & F10 & _). pose proof Hidx as HI. pose proof Hres as [HRS _]. pose proof Nrange as NR. pose proof BSLv_range as HB.
ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kHighShadowBeg, kHighShadowEnd, kPtrArrayResv, kMaxNumChunks, MALLOC_MAX, kThreadObjSize in *.
assert (UQS : bv_unsigned (ew E' 52) = QSv) by (img_try (rewrite (HEn 52%nat ltac:(unfold sHAV; zlia)), EaQS; unfold w64; img_apply unsigned_lit_small; unfold QSv; try unfold Qb; zlia)).
assert (UMAP : bv_unsigned (ew E' 45) = mb) by (img_try (rewrite (HEn 45%nat ltac:(unfold sHAV; zlia)), EaMAP; unfold w64; img_apply unsigned_lit_small; zlia)).
assert (UT : bv_unsigned (ew E' 32) = T) by (img_try (rewrite (HEn 32%nat ltac:(unfold sHAV; zlia)), EaT; unfold w64; img_apply unsigned_lit_small; try unfold T; zlia)).
assert (UBSL : bv_unsigned (ew E' 55) = BSLv) by (img_try (rewrite (HEn 55%nat ltac:(unfold sHAV; zlia)), EaBSL; unfold w64; img_apply unsigned_lit_small; unfold TFX_INST in *; zlia)).
unfold FQ. cbv zeta.
split. { memv HS 1%nat 0%nat; [img_try (cbn [base_val YQ0b.r_base]; rewrite UQS; zlia) | img_try (rewrite sv_denot_SOff0, (HEn 45%nat ltac:(unfold sHAV; zlia)), EaMAP; img_refl) | img_try (zlia)]. }
split. { memv HS 2%nat 10%nat; [img_try (cbn [base_val YQ0b.r_base]; rewrite UMAP; zlia) | img_try (rewrite sv_denot_SOff0, (HEn 45%nat ltac:(unfold sHAV; zlia)), EaMAP; img_refl) | img_try (zlia)]. }
split. { memv HS 2%nat 9%nat; [img_try (cbn [base_val YQ0b.r_base]; rewrite UMAP; zlia) | img_try (rewrite sv_denot_SOff0, (HEn 42%nat ltac:(unfold sHAV; zlia)), EaMS; img_refl) | img_try (zlia)]. }
split. { memv HS 2%nat 8%nat; [img_try (cbn [base_val YQ0b.r_base]; rewrite UMAP; zlia) | img_try (rewrite sv_denot_SOff0, (HEn 63%nat ltac:(unfold sHAV; zlia)), EaND; img_refl) | img_try (unfold NDv, R8v in *; zlia)]. }
split. { memv HS 2%nat 7%nat; [img_try (cbn [base_val YQ0b.r_base]; rewrite UMAP; zlia) | img_try (rewrite sv_denot_SOff0, (HEn 41%nat ltac:(unfold sHAV; zlia)), EaNCH; img_refl) | img_try (zlia)]. }
split. { memv HS 2%nat 0%nat; [img_try (cbn [base_val YQ0b.r_base]; rewrite UMAP; unfold Kv; zlia) | img_refl | img_try (zlia)]. }
split. { memv HS 2%nat 1%nat; [img_try (cbn [base_val YQ0b.r_base]; rewrite UMAP; unfold Kv; zlia) | | img_try (unfold Uv; zlia)].
cbn [sv_denot]. rewrite (HEn 45%nat ltac:(img_try (unfold sHAV; zlia))), EaMAP. unfold w64, Uv. rewrite Zbv_add_unsigned. f_equal. zlia. }
split. { memv HS 2%nat 2%nat; [img_try (cbn [base_val YQ0b.r_base]; rewrite UMAP; unfold Uv; zlia) | img_refl | img_try (zlia)]. }
split. { memv HS 2%nat 3%nat; [img_try (cbn [base_val YQ0b.r_base]; rewrite UMAP; unfold Uv; zlia) | img_refl | img_try (zlia)]. }
split. { memv HS 2%nat 6%nat; [img_try (cbn [base_val YQ0b.r_base]; rewrite UMAP; unfold Uv; zlia) | | img_try (zlia)].
lazymatch goal with |- sv_denot ?E ?t = _ => rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E t)); f_equal; img_change (bv_unsigned (sv_denot E t)) with (U E t); rewrite (U_zev E t eq_refl) end.
cbn [zev zalu_raw]. unfold rho_of. rewrite (HEn 10%nat ltac:(img_try (unfold sHAV; zlia))), E10, Hn. unfold w64. rewrite unsigned_lit_small by zlia.
rewrite Z.add_0_r, (zcanon_small n) by zlia. img_change (Z.land (zcanon 32) 63) with 32. rewrite srl32_n. img_refl. }
split. { memv HS 2%nat 5%nat; [img_try (cbn [base_val YQ0b.r_base]; rewrite UMAP; unfold Uv; zlia) | img_try (cbn [sv_denot]; rewrite (HEn 10%nat ltac:(unfold sHAV; zlia)), E10, Hn; unfold w64; rewrite ?Zbv_add_unsigned, ?Z.add_0_r; first [img_refl | f_equal; zlia]) | img_try (zlia)]. }
split. { memv HS 44%nat 0%nat; [img_try (cbn [base_val YQ0b.r_base]; rewrite UT; unfold t_unwinding; zlia) | img_refl | img_try (zlia)]. }
split. { memv HS 52%nat 0%nat; [img_try (cbn [base_val YQ0b.r_base]; img_refl) | | img_try (destruct grow; unfold kPtrArrayEntriesPerCommit; zlia)].
img_change (SAlu ALU_ADD (SOff 40 0) (SAlu ALU_SLL (SAlu ALU_XOR (SAlu ALU_SLTU (SOff 41 0) (SOff 40 0)) (SLit 1)) (SLit 14))) with RES2T.
rewrite (sv_denot_agree sHAV E0 E' RES2T HE ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))).
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E0 RES2T)). f_equal. img_change (bv_unsigned (sv_denot E0 RES2T)) with (U E0 RES2T).
destruct grow.
- rewrite (RES2T_eq (proj1 Hgrow eq_refl)). rewrite U_SOff. unfold aRES. rewrite EaRES. unfold w64. rewrite unsigned_lit_small by zlia. img_apply zcanon_small. unfold kPtrArrayEntriesPerCommit. zlia.
- assert (NE : idx <> res) by (img_try (intros E; pose proof (proj2 Hgrow E) as XX; discriminate XX)).
rewrite (RES2T_ne NE). rewrite U_SOff. unfold aRES. rewrite EaRES. unfold w64. rewrite unsigned_lit_small by zlia. rewrite Z.add_0_r. img_apply zcanon_small. zlia. }
split. { memv HS 53%nat 0%nat; [img_try (cbn [base_val YQ0b.r_base]; img_refl) | img_try (cbn [sv_denot]; rewrite (HEn 41%nat ltac:(unfold sHAV; zlia)), EaNCH; unfold w64; rewrite ?Zbv_add_unsigned; first [img_refl | f_equal; zlia]) | img_try (zlia)]. }
split. { memv HS 56%nat 0%nat; [img_try (cbn [base_val YQ0b.r_base]; img_refl) | img_refl | img_try (zlia)]. }
split. { memv HS 56%nat 1%nat; [img_try (cbn [base_val YQ0b.r_base]; img_refl) | img_refl | img_try (zlia)]. }
split. { memv HS 56%nat 2%nat; [img_try (cbn [base_val YQ0b.r_base]; img_refl) | img_refl | img_try (zlia)]. }
split.
{ intros a Ha. destruct Ha as [Hw|[Hq|Hm]].
- unfold WINT in Hw. destruct Hw as [Hw|[Hw|[Hw|Hw]]].
+ destruct (Z_lt_le_dec a (T + 2800)) as [H28|H28].
* eapply (st_ok_window_apresent_off (w_H Wz) E' _ _ 43%nat _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite UT; zlia) | img_try (off_by ltac:(unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; try unfold T in *; zlia)) ].
* eapply (st_ok_window_apresent_off (w_H Wz) E' _ _ 45%nat _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite UT; zlia) | img_try (off_by ltac:(unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; try unfold T in *; zlia)) ].
+ eapply (st_ok_window_apresent_off (w_H Wz) E' _ _ 46%nat _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite UT; zlia) | img_try (off_by ltac:(unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; try unfold T in *; zlia)) ].
+ eapply (st_ok_window_apresent_off (w_H Wz) E' _ _ 47%nat _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite UT; zlia) | img_try (off_by ltac:(unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; try unfold T in *; zlia)) ].
+ eapply (st_ok_window_apresent_off (w_H Wz) E' _ _ 44%nat _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite UT; unfold t_unwinding in *; zlia) | img_try (off_by ltac:(unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END, t_unwinding in *; try unfold T in *; zlia)) ].
- eapply (st_ok_window_apresent_off (w_H Wz) E' _ _ 1%nat _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite UQS; zlia) | img_try (off_by ltac:(unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; unfold QSv in *; try unfold Qb in *; zlia)) ].
- eapply (st_ok_window_apresent_off (w_H Wz) E' _ _ 2%nat _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite UMAP; zlia) | img_try (off_by ltac:(unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; zlia)) ]. }
{ intros a Ha. assert (Ra : 0 <= a < 2 ^ 64) by (img_try (clear - Ha HB MZ; unfold WINI, TFX_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex in *; zlia)).
img_apply (writable_visible (w_H Wz) (ms_mem ms) a Ra). unfold WINI in Ha.
destruct Ha as [Hw|[Hw|[Hw|[Hw|Hw]]]].
- destruct (Z_lt_le_dec a (TFX_INST + 120)) as [A1|A1]; [|img_try (destruct (Z_lt_le_dec a (TFX_INST + 128)) as [A2|A2])].
+ eapply (st_ok_window_writable (w_H Wz) E' _ _ 52%nat _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; unfold TFX_INST, o_sec_reserved in *; zlia)].
+ eapply (st_ok_window_writable (w_H Wz) E' _ _ 53%nat _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; unfold TFX_INST in *; zlia)].
+ eapply (st_ok_window_writable (w_H Wz) E' _ _ 54%nat _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; unfold TFX_INST, o_sec_sorted in *; zlia)].
- eapply (st_ok_window_writable (w_H Wz) E' _ _ 55%nat _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; unfold TFX_INST, o_sec_stats in *; zlia)].
- eapply (st_ok_window_writable (w_H Wz) E' _ _ 62%nat _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite UBSL; zlia)].
- eapply (st_ok_window_writable (w_H Wz) E' _ _ 56%nat _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; unfold TFX_INST, o_sec_mutex in *; zlia)].
- eapply (st_ok_window_writable (w_H Wz) E' _ _ 57%nat _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; zlia)]. }
Qed.
Lemma FQ_o : n mod 8 <> 0 -> forall (E' : env) ms, env_agree sHAV E0 E' -> st_ok tfxsegs E' Uo_RET (restrict (w_H Wz) ms) ->
FQ Wz grow (ms_mem ms) /\ val_mem tfxsegs (mrestrict (w_H Wz) (ms_mem ms)) PBv 1 (n mod 8) /\ apresent (w_H Wz) (ms_mem ms) PBv.
Proof.
intros H8 E' ms HE HS. pose proof (proj1 HE) as HEn.
pose proof map_facts as (M1 & M2 & M3 & M4 & M5 & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _). pose proof map_zoneN as MZ. pose proof size_facts as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & _).
pose proof high_facts as (F1 & F2 & _ & _ & _ & _ & _ & _ & F9 & F10 & _). pose proof Hidx as HI. pose proof Hres as [HRS _]. pose proof Nrange as NR. pose proof BSLv_range as HB.
ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kHighShadowBeg, kHighShadowEnd, kPtrArrayResv, kMaxNumChunks, MALLOC_MAX, kThreadObjSize in *.
assert (UQS : bv_unsigned (ew E' 52) = QSv) by (img_try (rewrite (HEn 52%nat ltac:(unfold sHAV; zlia)), EaQS; unfold w64; img_apply unsigned_lit_small; unfold QSv; try unfold Qb; zlia)).
assert (UMAP : bv_unsigned (ew E' 45) = mb) by (img_try (rewrite (HEn 45%nat ltac:(unfold sHAV; zlia)), EaMAP; unfold w64; img_apply unsigned_lit_small; zlia)).
assert (UT : bv_unsigned (ew E' 32) = T) by (img_try (rewrite (HEn 32%nat ltac:(unfold sHAV; zlia)), EaT; unfold w64; img_apply unsigned_lit_small; try unfold T; zlia)).
assert (UBSL : bv_unsigned (ew E' 55) = BSLv) by (img_try (rewrite (HEn 55%nat ltac:(unfold sHAV; zlia)), EaBSL; unfold w64; img_apply unsigned_lit_small; unfold TFX_INST in *; zlia)).
assert (UPB : bv_unsigned (ew E' 66) = PBv).
{ rewrite (HEn 66%nat ltac:(img_try (unfold sHAV; zlia))), EaPB. unfold w64. img_apply unsigned_lit_small. pose proof map_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PB & _).
pose proof (Z.div_mod N8D 8 ltac:(img_try (zlia))) as DM8. pose proof (Z.mod_pos_bound N8D 8 ltac:(img_try (zlia))) as MB8. pose proof (Z.div_mod MSv 8 ltac:(img_try (zlia))) as DM8'. pose proof (Z.mod_pos_bound MSv 8 ltac:(img_try (zlia))) as MB8'. clear - PB SM1 SM2 Z4 Z8 DM8 MB8 DM8' MB8' NR MZ. zlia. }
split; [| img_try (split)].
2:{ memv HS 0%nat 0%nat; [img_try (cbn [base_val YQ0b.r_base]; rewrite UPB; zlia) | | img_try (pose proof (Z.mod_pos_bound n 8 ltac:(zlia)); zlia)].
lazymatch goal with |- sv_denot ?E ?t = _ => rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E t)); f_equal; img_change (bv_unsigned (sv_denot E t)) with (U E t); rewrite (U_zev E t eq_refl) end.
cbn [zev zalu_raw]. unfold rho_of. rewrite (HEn 10%nat ltac:(img_try (unfold sHAV; zlia))), E10, Hn. unfold w64. rewrite unsigned_lit_small by zlia.
rewrite Z.add_0_r, (zcanon_small n) by zlia. img_change (zcanon 7) with (Z.ones 3). rewrite Z.land_ones by zlia. img_change (2 ^ 3) with 8.
img_apply zcanon_small. pose proof (Z.mod_pos_bound n 8 ltac:(img_try (zlia))). zlia. }
2:{ pose proof map_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PB & _).
pose proof (Z.div_mod N8D 8 ltac:(img_try (zlia))) as DM8. pose proof (Z.mod_pos_bound N8D 8 ltac:(img_try (zlia))) as MB8. pose proof (Z.div_mod MSv 8 ltac:(img_try (zlia))) as DM8'. pose proof (Z.mod_pos_bound MSv 8 ltac:(img_try (zlia))) as MB8'.
eapply (st_ok_window_apresent_off (w_H Wz) E' _ _ 0%nat _ PBv HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite UPB; zlia) | img_try (off_by ltac:(unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; clear - PB SM1 SM2 Z4 Z8 DM8 MB8 DM8' MB8' NR MZ; zlia)) ]. }
unfold FQ. cbv zeta.
split. { memv HS 2%nat 0%nat; [img_try (cbn [base_val YQ0b.r_base]; rewrite UQS; zlia) | img_try (rewrite sv_denot_SOff0, (HEn 45%nat ltac:(unfold sHAV; zlia)), EaMAP; img_refl) | img_try (zlia)]. }
split. { memv HS 3%nat 10%nat; [img_try (cbn [base_val YQ0b.r_base]; rewrite UMAP; zlia) | img_try (rewrite sv_denot_SOff0, (HEn 45%nat ltac:(unfold sHAV; zlia)), EaMAP; img_refl) | img_try (zlia)]. }
split. { memv HS 3%nat 9%nat; [img_try (cbn [base_val YQ0b.r_base]; rewrite UMAP; zlia) | img_try (rewrite sv_denot_SOff0, (HEn 42%nat ltac:(unfold sHAV; zlia)), EaMS; img_refl) | img_try (zlia)]. }
split. { memv HS 3%nat 8%nat; [img_try (cbn [base_val YQ0b.r_base]; rewrite UMAP; zlia) | img_try (rewrite sv_denot_SOff0, (HEn 63%nat ltac:(unfold sHAV; zlia)), EaND; img_refl) | img_try (unfold NDv, R8v in *; zlia)]. }
split. { memv HS 3%nat 7%nat; [img_try (cbn [base_val YQ0b.r_base]; rewrite UMAP; zlia) | img_try (rewrite sv_denot_SOff0, (HEn 41%nat ltac:(unfold sHAV; zlia)), EaNCH; img_refl) | img_try (zlia)]. }
split. { memv HS 3%nat 0%nat; [img_try (cbn [base_val YQ0b.r_base]; rewrite UMAP; unfold Kv; zlia) | img_refl | img_try (zlia)]. }
split. { memv HS 3%nat 1%nat; [img_try (cbn [base_val YQ0b.r_base]; rewrite UMAP; unfold Kv; zlia) | | img_try (unfold Uv; zlia)].
cbn [sv_denot]. rewrite (HEn 45%nat ltac:(img_try (unfold sHAV; zlia))), EaMAP. unfold w64, Uv. rewrite Zbv_add_unsigned. f_equal. zlia. }
split. { memv HS 3%nat 2%nat; [img_try (cbn [base_val YQ0b.r_base]; rewrite UMAP; unfold Uv; zlia) | img_refl | img_try (zlia)]. }
split. { memv HS 3%nat 3%nat; [img_try (cbn [base_val YQ0b.r_base]; rewrite UMAP; unfold Uv; zlia) | img_refl | img_try (zlia)]. }
split. { memv HS 3%nat 6%nat; [img_try (cbn [base_val YQ0b.r_base]; rewrite UMAP; unfold Uv; zlia) | | img_try (zlia)].
lazymatch goal with |- sv_denot ?E ?t = _ => rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E t)); f_equal; img_change (bv_unsigned (sv_denot E t)) with (U E t); rewrite (U_zev E t eq_refl) end.
cbn [zev zalu_raw]. unfold rho_of. rewrite (HEn 10%nat ltac:(img_try (unfold sHAV; zlia))), E10, Hn. unfold w64. rewrite unsigned_lit_small by zlia.
rewrite Z.add_0_r, (zcanon_small n) by zlia. img_change (Z.land (zcanon 32) 63) with 32. rewrite srl32_n. img_refl. }
split. { memv HS 3%nat 5%nat; [img_try (cbn [base_val YQ0b.r_base]; rewrite UMAP; unfold Uv; zlia) | img_try (cbn [sv_denot]; rewrite (HEn 10%nat ltac:(unfold sHAV; zlia)), E10, Hn; unfold w64; rewrite ?Zbv_add_unsigned, ?Z.add_0_r; first [img_refl | f_equal; zlia]) | img_try (zlia)]. }
split. { memv HS 45%nat 0%nat; [img_try (cbn [base_val YQ0b.r_base]; rewrite UT; unfold t_unwinding; zlia) | img_refl | img_try (zlia)]. }
split. { memv HS 53%nat 0%nat; [img_try (cbn [base_val YQ0b.r_base]; img_refl) | | img_try (destruct grow; unfold kPtrArrayEntriesPerCommit; zlia)].
img_change (SAlu ALU_ADD (SOff 40 0) (SAlu ALU_SLL (SAlu ALU_XOR (SAlu ALU_SLTU (SOff 41 0) (SOff 40 0)) (SLit 1)) (SLit 14))) with RES2T.
rewrite (sv_denot_agree sHAV E0 E' RES2T HE ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))).
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E0 RES2T)). f_equal. img_change (bv_unsigned (sv_denot E0 RES2T)) with (U E0 RES2T).
destruct grow.
- rewrite (RES2T_eq (proj1 Hgrow eq_refl)). rewrite U_SOff. unfold aRES. rewrite EaRES. unfold w64. rewrite unsigned_lit_small by zlia. img_apply zcanon_small. unfold kPtrArrayEntriesPerCommit. zlia.
- assert (NE : idx <> res) by (img_try (intros E; pose proof (proj2 Hgrow E) as XX; discriminate XX)).
rewrite (RES2T_ne NE). rewrite U_SOff. unfold aRES. rewrite EaRES. unfold w64. rewrite unsigned_lit_small by zlia. rewrite Z.add_0_r. img_apply zcanon_small. zlia. }
split. { memv HS 54%nat 0%nat; [img_try (cbn [base_val YQ0b.r_base]; img_refl) | img_try (cbn [sv_denot]; rewrite (HEn 41%nat ltac:(unfold sHAV; zlia)), EaNCH; unfold w64; rewrite ?Zbv_add_unsigned; first [img_refl | f_equal; zlia]) | img_try (zlia)]. }
split. { memv HS 57%nat 0%nat; [img_try (cbn [base_val YQ0b.r_base]; img_refl) | img_refl | img_try (zlia)]. }
split. { memv HS 57%nat 1%nat; [img_try (cbn [base_val YQ0b.r_base]; img_refl) | img_refl | img_try (zlia)]. }
split. { memv HS 57%nat 2%nat; [img_try (cbn [base_val YQ0b.r_base]; img_refl) | img_refl | img_try (zlia)]. }
split.
{ intros a Ha. destruct Ha as [Hw|[Hq|Hm]].
- unfold WINT in Hw. destruct Hw as [Hw|[Hw|[Hw|Hw]]].
+ destruct (Z_lt_le_dec a (T + 2800)) as [H28|H28].
* eapply (st_ok_window_apresent_off (w_H Wz) E' _ _ 44%nat _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite UT; zlia) | img_try (off_by ltac:(unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; try unfold T in *; zlia)) ].
* eapply (st_ok_window_apresent_off (w_H Wz) E' _ _ 46%nat _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite UT; zlia) | img_try (off_by ltac:(unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; try unfold T in *; zlia)) ].
+ eapply (st_ok_window_apresent_off (w_H Wz) E' _ _ 47%nat _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite UT; zlia) | img_try (off_by ltac:(unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; try unfold T in *; zlia)) ].
+ eapply (st_ok_window_apresent_off (w_H Wz) E' _ _ 48%nat _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite UT; zlia) | img_try (off_by ltac:(unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; try unfold T in *; zlia)) ].
+ eapply (st_ok_window_apresent_off (w_H Wz) E' _ _ 45%nat _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite UT; unfold t_unwinding in *; zlia) | img_try (off_by ltac:(unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END, t_unwinding in *; try unfold T in *; zlia)) ].
- eapply (st_ok_window_apresent_off (w_H Wz) E' _ _ 2%nat _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite UQS; zlia) | img_try (off_by ltac:(unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; unfold QSv in *; try unfold Qb in *; zlia)) ].
- eapply (st_ok_window_apresent_off (w_H Wz) E' _ _ 3%nat _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite UMAP; zlia) | img_try (off_by ltac:(unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; zlia)) ]. }
{ intros a Ha. assert (Ra : 0 <= a < 2 ^ 64) by (img_try (clear - Ha HB MZ; unfold WINI, TFX_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex in *; zlia)).
img_apply (writable_visible (w_H Wz) (ms_mem ms) a Ra). unfold WINI in Ha.
destruct Ha as [Hw|[Hw|[Hw|[Hw|Hw]]]].
- destruct (Z_lt_le_dec a (TFX_INST + 120)) as [A1|A1]; [|img_try (destruct (Z_lt_le_dec a (TFX_INST + 128)) as [A2|A2])].
+ eapply (st_ok_window_writable (w_H Wz) E' _ _ 53%nat _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; unfold TFX_INST, o_sec_reserved in *; zlia)].
+ eapply (st_ok_window_writable (w_H Wz) E' _ _ 54%nat _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; unfold TFX_INST in *; zlia)].
+ eapply (st_ok_window_writable (w_H Wz) E' _ _ 55%nat _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; unfold TFX_INST, o_sec_sorted in *; zlia)].
- eapply (st_ok_window_writable (w_H Wz) E' _ _ 56%nat _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; unfold TFX_INST, o_sec_stats in *; zlia)].
- eapply (st_ok_window_writable (w_H Wz) E' _ _ 63%nat _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite UBSL; zlia)].
- eapply (st_ok_window_writable (w_H Wz) E' _ _ 57%nat _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; unfold TFX_INST, o_sec_mutex in *; zlia)].
- eapply (st_ok_window_writable (w_H Wz) E' _ _ 58%nat _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; zlia)]. }
Qed.
Local Ltac run_byte HR x :=
rewrite <- (Z_to_bv_bv_unsigned 64 x); img_apply HR; cbn [fst snd].
Lemma fin_pack : forall (odd : bool) regs' mem' memD,
(odd = true <-> n mod 8 <> 0) ->
getr regs' 10 = sv_denot E0 (SOff aMAP 6144) ->
(forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs0 r) ->
(forall x : word, ~ X (bv_unsigned x) -> mem' x = mem0 x) ->
(forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H Wz) mem' a) ->
(forall a, mb + 6144 <= a < mb + MSv -> apresent (w_H Wz) mem' a) ->
(forall a, SMv <= a < SMv + MSv / 8 -> (odd = true -> a <> PBv) -> apresent (w_H Wz) mem' a) ->
Forall (brun mem') (if odd then SH6o else SH6) ->
DPOST z memD -> (forall a, DZONE a -> apresent (w_H Wz) mem0 a -> apresent (w_H Wz) memD a) -> (forall x : word, DZONE (bv_unsigned x) -> mem' x = memD x) ->
RX mem' -> FQ Wz grow mem' ->
(odd = true -> val_mem tfxsegs (mrestrict (w_H Wz) mem') PBv 1 (n mod 8) /\ apresent (w_H Wz) mem' PBv) ->
fin_facts grow z Wz regs' mem' memD.
Proof.
intros odd regs' mem' memD Hodd R10 RCS MEQ PRS HM HSH HRUN DP PRD EQD HRX FQm HPB.
destruct FQm as (Qslot & Qh0 & Qh8 & Qh16 & Qh24 & Qmag & Qbk & Qst & Qb1 & Qb2 & Qn & Qunw & Qres & Qnch & Qmtx & Qp1 & Qp2 & QPR & QVISW).
destruct (HDPOST z memD DP) as (AOK & DEPD & CSTD).
assert (RUNS : brun mem' (Uv, Uv + 4096, 190) /\ brun mem' (SMv + 768, SMv + 768 + N8D / 8, 0) /\ brun mem' (SHBv + UEv / 8, SMv + MSv / 8, 250) /\
brun mem' (SMv + 512, SMv + 768, 250) /\ brun mem' (SMv, SMv + 512, 250)).
{ destruct odd; unfold SH6o, SH5o, SH6, SH5 in HRUN;
apply Forall_cons_iff in HRUN as [R0 HRUN]; apply Forall_cons_iff in HRUN as [R1 HRUN]; apply Forall_cons_iff in HRUN as [R2 HRUN];
apply Forall_cons_iff in HRUN as [R3 HRUN]; apply Forall_cons_iff in HRUN as [R4 _]; img_exact (conj R0 (conj R1 (conj R2 (conj R3 R4)))). }
destruct RUNS as (Rfill & Rzs & Rrt & Rhd & Rpg).
constructor.
- img_exact AOK.
- img_exact DEPD.
- img_exact CSTD.
- img_exact PRD.
- img_exact EQD.
- intros x N1 N2 N3. img_apply MEQ. intros HXx. destruct (HXsub _ HXx) as [Hw|[Hw|Hw]]; [img_try (img_exact (N1 Hw)) | img_try (img_exact (N2 Hw)) | img_try (img_exact (N3 Hw))].
- img_exact PRS.
- intros a Ha. destruct (Z_lt_le_dec a (mb + 6144)) as [Hl|Hl]; [img_try (img_apply QPR; right; right; zlia) | img_try (img_apply HM; zlia)].
- intros a Ha. destruct odd.
+ destruct (Z.eq_dec a PBv) as [->|Hne]; [img_try (img_exact (proj2 (HPB eq_refl))) | img_try (img_apply HSH; [img_exact Ha | intros _; img_exact Hne])].
+ img_apply HSH; [img_try (img_exact Ha) | img_try (intros E; discriminate E)].
- intros Hg a Hqa. destruct (zr_dec QSv (QSv + 8) a) as [Hs|Hs]; [img_try (img_apply QPR; right; left; img_exact Hs)|].
destruct (HRXQ Hg _ HRX (proj1 Hgrow Hg) a Hqa Hs) as [Hh Hm]. split; [img_try (img_exact Hh) | img_try (eexists; img_exact Hm)].
- intros a [Hw|Hs]; img_apply QPR; [img_try (left; img_exact Hw) | img_try (right; left; img_exact Hs)].
- img_exact QVISW.
- rewrite R10. cbn [sv_denot]. unfold aMAP. rewrite EaMAP. unfold w64, Uv. rewrite Zbv_add_unsigned; first [img_refl | f_equal; zlia].
- img_exact RCS.
- intros x [Hx|Hx].
+ destruct (Z_lt_le_dec (bv_unsigned x) (SMv + 512)) as [Hl|Hl]; [img_try (run_byte Rpg x; zlia) | img_try (run_byte Rhd x; zlia)].
+ run_byte Rrt x; img_exact Hx.
- intros x Hx. run_byte Rzs x; img_exact Hx.
- intros H8. img_exact (proj1 (HPB (proj2 Hodd H8))).
- img_exact Qunw.
- img_exact Qres.
- img_exact Qnch.
- img_exact Qmtx.
- intros k Hk. unfold aview.
assert (K : k = 1 \/ k = 2 \/ k = 3) by zlia. destruct K as [->|[->| ->]].
+ pose proof (Qp1 0%nat ltac:(img_try (zlia))) as Xb. rewrite Z.add_0_r in Xb. rewrite Xb. img_refl.
+ pose proof (Qp2 0%nat ltac:(img_try (zlia))) as Xb. rewrite Z.add_0_r in Xb. replace (TFX_INST + o_sec_mutex + 2) with (TFX_INST + o_sec_mutex + 2) by zlia. rewrite Xb. img_refl.
+ pose proof (Qp2 1%nat ltac:(img_try (zlia))) as Xb. replace (TFX_INST + o_sec_mutex + 3) with (TFX_INST + o_sec_mutex + 2 + Z.of_nat 1) by zlia. rewrite Xb. img_refl.
- img_exact Qslot.
- img_exact Qh0.
- img_exact Qh8.
- img_exact Qh16.
- img_exact Qh24.
- img_exact Qmag.
- img_exact Qbk.
- img_exact Qst.
- img_exact Qb1.
- img_exact Qb2.
- img_exact Qn.
- intros x Hx. run_byte Rfill x; img_exact Hx.
Qed.
Definition fin_post (W2 : world tfxsegs) (c2 : config) : Prop :=
W2 = Wz /\ exists regs' mem' mat memD,
c2 = mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy mdl) mat mdl) /\ fin_facts grow z Wz regs' mem' memD.
Lemma finE : n mod 8 = 0 -> forall W' c', at_S Wz mdl X (PSR Wz SH6 (PDX Wz RX z)) Ue_RET W' c' -> SRr tfxsegs W' c' fin_post.
Proof.
intros H8 W' c' HR.
apply (at_S_facts Wz mdl X _ (FQ Wz grow) Ue_RET) in HR; [| img_try (intros E' ms HE HS; img_exact (FQ_e E' ms HE HS))].
eapply SRr_mono; [img_try (eapply (at_S_ret Wz mdl X _ Ue_RET _ _ (SOff aMAP 6144) HR); [img_refl | img_refl | img_refl | img_refl | img_refl | img_refl | repeat constructor]) |].
intros W2 c2 _ (-> & regs' & mem' & mat & -> & R10 & RCS & MEQ & PRS & (((HB & HM & HSH & HRUN) & ((memD & DP & PRD & EQD) & HRX)) & FQm)).
split; [img_refl|]. exists regs', mem', mat, memD. split; [img_refl|].
img_apply (fin_pack false); try assumption.
- split; [img_try (intros E; discriminate E) | img_try (intros H; exfalso; img_exact (H H8))].
- intros a Ha _. img_exact (HSH a Ha).
- intros E; discriminate E.
Qed.
Lemma finO : n mod 8 <> 0 -> forall W' c', at_S Wz mdl X (PT Wz SH6o (PDX Wz RX z)) Uo_RET W' c' -> SRr tfxsegs W' c' fin_post.
Proof.
intros H8 W' c' HR.
apply (at_S_facts Wz mdl X _ (fun m => FQ Wz grow m /\ val_mem tfxsegs (mrestrict (w_H Wz) m) PBv 1 (n mod 8) /\ apresent (w_H Wz) m PBv) Uo_RET) in HR;
[| img_try (intros E' ms HE HS; img_exact (FQ_o H8 E' ms HE HS))].
eapply SRr_mono; [img_try (eapply (at_S_ret Wz mdl X _ Uo_RET _ _ (SOff aMAP 6144) HR); [img_refl | img_refl | img_refl | img_refl | img_refl | img_refl | repeat constructor]) |].
intros W2 c2 _ (-> & regs' & mem' & mat & -> & R10 & RCS & MEQ & PRS & ((HB & HM & HSH & HRUN & ((memD & DP & PRD & EQD) & HRX)) & (FQm & QPB & QPBp))).
split; [img_refl|]. exists regs', mem', mat, memD. split; [img_refl|].
img_apply (fin_pack true); try assumption.
- split; [img_try (intros _; img_exact H8) | img_refl].
- intros a Ha Hne. img_exact (HSH a Ha (Hne eq_refl)).
- intros _. img_exact (conj QPB QPBp).
Qed.
End h.
Lemma OWN_T : forall a, WINT a -> aowned B ly S a.
Proof.
clearP. intros a Hw. img_apply (own_core B ly S rd0 (ly_T ly, kThreadObjSize) a HARm); [img_try (unfold core_extents; cbn; tauto)|].
cbn [fst snd]. unfold WINT, t_unwinding, kThreadObjSize in *. unfold T in Hw. clear - Hw. zlia.
Qed.
Lemma OWN_I : forall a, WINI a -> aowned B ly S a.
Proof.
clearP. intros a Hw. pose proof BSLv_range as HB. img_apply (own_static B ly S rd0 a HARm). rewrite (ts_owned B TS). unfold Tfx_owned_static. img_apply Exists_exists.
exists ((0xa6b58 + D_10c0), (0x5cc810 + D_10c0) - (0xa6b58 + D_10c0)). split; [img_try (cbn; tauto)|]. unfold in_zr. cbn [fst snd].
unfold WINI, TFX_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex in *. clear - Hw HB. zlia.
Qed.
Lemma OWN_Q : forall a, Qb <= a < Qb + kPtrArrayResv -> aowned B ly S a.
Proof. clearP. intros a Ha. img_apply (own_core B ly S rd0 (ly_Q ly, kPtrArrayResv) a HARm); [img_try (unfold core_extents; cbn; tauto) | img_try (cbn [fst snd]; unfold Qb in Ha; img_exact Ha)]. Qed.
Lemma OWN_D : forall a, DZONE a -> aowned B ly S a.
Proof.
clearP. intros a Hd. unfold DZONE in Hd. destruct Hd as [Hd|[Hd|Hd]].
- img_apply (own_static B ly S rd0 a HARm). rewrite (ts_owned B TS). unfold Tfx_owned_static. img_apply Exists_exists.
exists ((0xa6b58 + D_10c0), (0x5cc810 + D_10c0) - (0xa6b58 + D_10c0)). split; [img_try (cbn; tauto)|]. unfold in_zr. cbn [fst snd]. clear - Hd. zlia.
- img_apply (own_core B ly S rd0 (ly_NB ly, kNodesBlockSize) a HARm); [img_try (unfold core_extents; cbn; tauto) | img_try (cbn [fst snd]; img_exact Hd)].
- img_apply (own_core B ly S rd0 (ly_SB ly, kStoreBlockSize) a HARm); [img_try (unfold core_extents; cbn; tauto) | img_try (cbn [fst snd]; img_exact Hd)].
Qed.
Lemma band_core : forall a, (2147450880 <= a < kLowShadowEnd) \/ (kHighShadowBeg <= a < kHighShadowEnd) ->
Exists (fun r => in_zr a (shadow_addr (fst r), (snd r + 7) / 8)) (static_extents ly ++ sec_extents ly S ++ zero_shadow_ranges B ly ++ as_owned_static B ++ [hm_zone; lm_zone]).
Proof.
clearP. intros a Ha. img_apply Exists_exists. pose proof hm_zone_shadow as [E1 E2].
destruct Ha as [LO|HI].
- exists lm_zone. split; [img_try (repeat (img_apply in_app_iff; right); right; left; img_refl)|].
unfold in_zr, lm_zone, shadow_addr, SHADOW_OFF. cbn [fst snd]. clear - LO. unfold kLowMemEnd, kLowShadowBeg, kLowShadowEnd in *.
repeat match goal with |- context[(?x + 7) / 8] => let v := img_ev ((x + 7) / 8) in img_change ((x + 7) / 8) with v end. img_change (0 / 8) with 0. zlia.
- exists hm_zone. split; [img_try (repeat (img_apply in_app_iff; right); left; img_refl)|].
unfold in_zr. cbn [fst snd] in *. rewrite E1. rewrite E1 in E2. clear - HI E2. zlia.
Qed.
Lemma OWN_SH : Forall (zdisjoint (mb, MSv)) (static_extents ly ++ vis0_zones ly ++ sec_extents ly S) ->
forall a, SMv <= a < SMv + MSv / 8 -> aowned B ly S a.
Proof.
intros GAP a Ha. pose proof map_facts as (M1 & M2 & M3 & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _ & _ & SMA). pose proof map_zoneN as MZ. pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & Z9 & _).
split; [img_try (do 4 right; img_apply band_core; clear - Ha MZ; unfold kLowShadowEnd, kHighShadowBeg, kHighShadowEnd; zlia)|].
pose proof (Z.div_mod MSv 8 ltac:(img_try (zlia))) as DM8. assert (M8 : MSv mod 8 = 0) by (img_try (clear - Z9 MZ; apply Z.mod_divide in Z9 as [u Hu]; [|img_try (zlia)]; rewrite Hu; replace (u * 4096) with ((u * 512) * 8) by zlia; img_apply Z.mod_mul; zlia)).
eapply (nc_shadow B ly S rd0 a mb MSv HARm).
- apply Z.mod_divide in M3 as [p Hp]; [|img_try (zlia)]. rewrite Hp. replace (p * 4096) with ((p * 512) * 8) by zlia. img_apply Z.mod_mul. zlia.
- clear - M1 MZ. unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg in M1. zlia.
- clear - M2 MZ. ceil; unfold ASAN_CEIL, kHighMemEnd in *. zlia.
- img_apply (proj1 (Forall_forall _ _) GAP). img_apply in_app_iff. left. unfold static_extents, owned_extents. img_apply in_app_iff. left. cbn. tauto.
- rewrite <- SMA. replace ((MSv + 7) / 8) with (MSv / 8); [img_try (clear - Ha MZ; zlia)|].
clear - M8 Z8 MZ. apply Z.mod_divide in M8 as [u Hu]; [|img_try (zlia)]. rewrite Hu. rewrite Z.div_mul by zlia. rewrite Z.div_add_l by zlia. img_change (7 / 8) with 0. zlia.
Qed.
Lemma OWN_BANDhid : AR tfxsegs B ly S W mem0 md0 -> forall a, (2147450880 <= a < kLowShadowEnd) \/ (kHighShadowBeg <= a < kHighShadowEnd) -> w_H W (Z_to_bv 64 a) = true -> aowned B ly S a.
Proof.
intros HAR a Ha Hh. split; [img_try (do 4 right; img_apply band_core; img_exact Ha)|].
assert (HB : in_band_rw a) by (img_try (clear - Ha; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *; zlia)).
intros C. img_apply (client_band_vis B ly S rd0 a HARm HB C). unfold rd0. img_apply aview_band_hidden; [img_try (img_exact (al_img_env tfxsegs ly S _ LY (proj1 (proj2 HAR)))) | img_try (img_exact HB) | img_try (img_exact Hh)].
Qed.
Lemma NEWOWN : forall (grow : bool) (z : Z),
Forall (zdisjoint (mb, MSv)) (static_extents ly ++ vis0_zones ly ++ sec_extents ly S) ->
forall a, mb <= a < mb + MSv -> ~ (Uv <= a < Uv + n) -> aowned B lyF (SFS grow z) a.
Proof.
intros grow z GAP a Ha Hnu. pose proof map_facts as (M1 & M2 & M3 & _). pose proof map_zoneN as MZ. pose proof (SF_parts grow z) as (_ & _ & _ & Rfr & _ & _ & _ & _ & _ & _ & _ & Rck & _).
pose proof sizes_model as (ND & MS & RS & RZ & FP & KN & KR & KE & KQ & KB & KST). destruct Hmap_apart as (_ & _ & MP3 & _).
split.
- do 3 right. left. rewrite (SEF grow z). img_apply Exists_exists. exists (mb, MSv). split; [img_try (img_apply in_app_iff; right; left; img_refl) | img_try (unfold in_zr; cbn [fst snd]; img_exact Ha)].
- intros [(k & Hk & Hst & Hr)|(cp & Hcp & Hr)].
+ rewrite Rck in Hk. apply in_app_iff in Hk as [Hk|[<-|[]]].
*
unfold ck_user in Hr. rewrite (sptr_addr_le B ly lyF (length (st_secs S)) _ lyF_le (YF49.padd_lt S _ _ (YF49.chunk_lt S _ _ _ _ WF k Hk))) in Hr.
fold (ck_user k) in Hr. pose proof (chunk_facts B ly S rd0 k HARm Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _). rewrite G4 in Hr. unfold ck_n in Hr.
destruct (extent_zone B ly S rd0 k HARm Hk) as [[X1 X2]|(m & len & Hin & X1 & X2)].
-- unfold zdisjoint in MP3. cbn [fst snd] in MP3. clear - Ha Hr X1 X2 MP3 G8 G5 MZ. zlia.
-- pose proof (proj1 (Forall_forall _ _) GAP (m, len) ltac:(img_try (img_apply in_app_iff; right; img_apply in_app_iff; right; img_exact Hin))) as D. unfold zdisjoint in D. cbn [fst snd] in D.
clear - Ha Hr X1 X2 D G8 G5 MZ. unfold kPage in *. zlia.
*
img_apply Hnu. unfold ck_user in Hr. cbn [YG00.ck_beg KSc YF49.KS padd sptr_addr sptr_exp aeval] in Hr.
img_change (YG00.ck_rz (YF49.KS S n)) with (ck_rz KSc) in Hr. rewrite KR, KN, lyF_sec in Hr. unfold Uv. unfold kPage in Hr. clear - Hr MZ. zlia.
+
unfold frames in Hcp, Rfr. rewrite Rfr in Hcp. destruct cp as [cid pos]. cbn [fst snd] in Hr.
pose proof (frame_facts B ly S rd0 cid pos HARm Hcp) as (C1 & C2 & F1 & F2 & FA & P1 & P2 & P3 & P4 & _). pose proof (Z.mul_nonneg_nonneg cid (2 ^ 20) ltac:(img_try (zlia)) ltac:(img_try (zlia))).
pose proof lyF_eqs as (_ & _ & _ & _ & _ & E6 & _). unfold frame_addr, in_zr in Hr. rewrite E6 in Hr. cbn [fst snd] in Hr.
pose proof (proj1 (Forall_forall _ _) GAP (ly_F ly, kFakeStackSize) ltac:(img_try (img_apply in_app_iff; left; unfold static_extents, owned_extents; img_apply in_app_iff; left; cbn; tauto))) as D.
unfold zdisjoint in D. cbn [fst snd] in D.
destruct Hr as [Hr|Hr].
* clear - Ha Hr D P1 P2 C1 H MZ. unfold kFakeFramesOff in *. zlia.
* pose proof (shadow_range_below (ly_F ly + fs_frame_off cid pos) (fs_frame_bytes cid) ltac:(img_try (clear - F1 P1 H MZ; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kFakeFramesOff in *; zlia)) ltac:(img_try (clear - P4 MZ; zlia)) ltac:(img_try (clear - F1 P2 MZ; ceil; unfold zone3, TFX_IMG_LO, in_app, ASAN_CEIL, kHighMemEnd, kLowShadowBeg, kHighMemBeg, kFakeStackSize in *; zlia))) as SBel.
pose proof (Z.div_pos (ly_F ly + fs_frame_off cid pos) 8 ltac:(img_try (clear - F1 P1 H MZ; unfold in_app, kFakeFramesOff in *; zlia)) ltac:(img_try (zlia))) as SB0.
clear - Ha Hr SBel SB0 M1 MZ. unfold shadow_addr, SHADOW_OFF, zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg in *. zlia.
Qed.
Section l.
Variables (grow : bool) (z : Z) (Wz : world tfxsegs) (mdl : Model).
Hypothesis HAR : AR tfxsegs B ly S W mem0 md0.
Hypothesis Hgrow : grow = true <-> idx = res.
Hypothesis LEz : wle W Wz.
Hypothesis IOz : same_io md0 mdl.
Hypothesis HWZ : forall mat, wz_facts grow z Wz (with_vm_backing (m_vm_lazy mdl) mat mdl).
Hypothesis HOUT : forall x : word, ~ (mb <= bv_unsigned x < mb + MSv) -> ~ (SHLO mb <= bv_unsigned x < SHHI mb) ->
~ (grow = true /\ QSv <= bv_unsigned x < QSv + 131072) -> w_H Wz x = w_H W x.
Theorem LEAF_S : forall regs' mem' memD mat,
Wf (as_universe B) (SFS grow z) /\ qtight (SFS grow z) ->
fin_facts grow z Wz regs' mem' memD ->
malloc_leaf tfxsegs B ly S W regs0 mem0 md0 n (ck_user KSc, SFS grow z) Wz
(mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy mdl) mat mdl)).
Proof.
intros regs' mem' memD mat MP HF. set (mdf := with_vm_backing (m_vm_lazy mdl) mat mdl).
pose proof (HWZ mat) as HW. fold mdf in HW.
pose proof map_facts as (M1 & M2 & M3 & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _ & _ & SMA). pose proof map_zoneN as MZ. pose proof size_facts as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & _).
pose proof sizes_model as (ND & MS & RS & RZ & FP & KN & KR & KE & KQ & KB & KST). pose proof high_facts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & _).
pose proof Hidx as HI. pose proof Hres as [HRS _]. destruct Hsp as (S1 & S2 & S3 & S4). pose proof (SH_hull mb) as (H1 & H2 & H3 & _).
pose proof HW as [MONf _ _ _ _ _ _ _ _ _ GAP]. pose proof blocks_facts as (NBhi & SBhi & _).
pose proof HF as [_ _ _ _ _ fMEQF fPRS _ _ _ _ _ fR10 fRCS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _].
exists lyF, regs', mem', mdf.
split. { unfold cfg_at, raZ, YG0d.w64. rewrite Z_to_bv_bv_unsigned. img_refl. }
split; [| img_try (split; [| img_exact (proj2 MP)])].
2:{ rewrite fR10. cbn [fst]. unfold ck_user. cbn [YG00.ck_beg KSc YF49.KS padd sptr_addr sptr_exp aeval].
img_change (YG00.ck_rz (YF49.KS S n)) with (ck_rz KSc). rewrite KR, lyF_sec. unfold Uv, YG0d.w64, w64, kPage. f_equal; zlia. }
split; [img_try (img_exact (S_AR_final grow z Wz mdf regs' mem' memD HAR Hgrow MP HF HW))|].
split; [img_try (img_exact lyF_le)|].
split; [img_try (img_exact LEz)|].
split. { intros r Hr. img_apply fRCS. unfold acallee_saved in Hr.
assert (H18 : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by zlia.
clear - H18 MZ.
assert (E5 : forall k : Z, 0 <= k < 32 -> forall b : bv 5, bv_unsigned b = k -> Z_to_bv 5 k = b) by (img_try (intros k Hk b Hb; img_apply bv_eq; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; img_change (2 ^ Z.of_N 5) with 32; rewrite Z.mod_small by zlia; symmetry; img_exact Hb)).
destruct H18 as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
[ img_try (rewrite (E5 2 ltac:(zlia) 2%bv eq_refl)) | img_try (rewrite (E5 3 ltac:(zlia) 3%bv eq_refl)) | img_try (rewrite (E5 4 ltac:(zlia) 4%bv eq_refl))
| img_try (rewrite (E5 8 ltac:(zlia) 8%bv eq_refl)) | img_try (rewrite (E5 9 ltac:(zlia) 9%bv eq_refl)) | img_try (rewrite (E5 18 ltac:(zlia) 18%bv eq_refl))
| img_try (rewrite (E5 19 ltac:(zlia) 19%bv eq_refl)) | img_try (rewrite (E5 20 ltac:(zlia) 20%bv eq_refl)) | img_try (rewrite (E5 21 ltac:(zlia) 21%bv eq_refl))
| img_try (rewrite (E5 22 ltac:(zlia) 22%bv eq_refl)) | img_try (rewrite (E5 23 ltac:(zlia) 23%bv eq_refl)) | img_try (rewrite (E5 24 ltac:(zlia) 24%bv eq_refl))
| img_try (rewrite (E5 25 ltac:(zlia) 25%bv eq_refl)) | img_try (rewrite (E5 26 ltac:(zlia) 26%bv eq_refl)) | img_try (rewrite (E5 27 ltac:(zlia) 27%bv eq_refl)) ];
cbn [In]; tauto. }
split. { unfold mdf. eapply YG0b.same_io_trans; [img_try (img_exact IOz) | img_try (img_apply YG0b.same_io_with_vm_backing)]. }
split; [| img_try (img_exact fPRS)].
intros a Ra NO NO' NS NE. cbn [fst] in NE.
assert (NE' : ~ (Uv <= a < Uv + n)).
{ intros Hu. img_apply NE. split; [img_try (discriminate)|]. unfold ck_user. cbn [YG00.ck_beg KSc YF49.KS padd sptr_addr sptr_exp aeval].
img_change (YG00.ck_rz (YF49.KS S n)) with (ck_rz KSc). rewrite KR, RS, lyF_sec. unfold Uv in Hu. unfold kPage. clear - Hu MZ. zlia. }
assert (NST : ~ (sp0 - ASTACK <= a < sp0)) by (img_try (intros Hs; img_apply NS; unfold ascratch, spZ; left; img_exact Hs)).
set (x := Z_to_bv 64 a). assert (Ux : bv_unsigned x = a) by (img_try ((subst x; cbv beta); img_apply unsigned_lit_small; img_exact Ra)).
assert (MEQa : mem' x = mem0 x).
{ img_apply fMEQF; rewrite Ux.
- intros Hw. unfold WIN, WINM in Hw. destruct Hw as [Hw|[Hw|[Hw|[Hw|[Hw|Hw]]]]].
+ img_exact (NST Hw).
+ img_exact (NO (OWN_T a Hw)).
+ img_exact (NO (OWN_I a Hw)).
+ apply NO, OWN_Q. unfold QSv in Hw. clear - Hw HI HRS MZ. unfold Qb in *. unfold kPtrArrayResv, kMaxNumChunks in *. zlia.
+ img_exact (NO' (NEWOWN grow z GAP a Hw NE')).
+ img_exact (NO (OWN_SH GAP a Hw)).
- intros [_ Hq]. apply NO, OWN_Q. unfold QR in Hq. clear - Hq HRS HI MZ. unfold Qb in *. unfold kPtrArrayEntriesPerCommit, kPtrArrayResv, kMaxNumChunks in *. zlia.
- intros [Hs|Hd]; [img_try (img_apply NST; clear - Hs MZ; unfold DEP_STK, ASTACK in *; zlia) | img_try (img_exact (NO (OWN_D a Hd)))]. }
destruct (w_H W x) eqn:EhW.
-
destruct (w_H Wz x) eqn:EhZ.
+ unfold aview, mbyte, mrestrict. (subst x; cbv beta). rewrite EhW, EhZ. img_refl.
+ exfalso. destruct (zr_dec mb (mb + MSv) a) as [D1|D1]; [img_try (img_exact (NO' (NEWOWN grow z GAP a D1 NE')))|].
destruct (zr_dec (SHLO mb) (SHHI mb) a) as [D2|D2].
{ img_apply NO. img_apply (OWN_BANDhid HAR a); [| img_try ((subst x; cbv beta); img_exact EhW)]. clear - D2 H1 H2 SM1 SM2 H3 M1 M2 M3 Z8 SMA MZ.
unfold SHLO, SHHI, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *.
pose proof (Z.div_mod (shadow_addr mb) 4096 ltac:(img_try (zlia))). pose proof (Z.mod_pos_bound (shadow_addr mb) 4096 ltac:(img_try (zlia))).
pose proof (Z.div_mod (shadow_addr mb + MSv / 8 + 4095) 4096 ltac:(img_try (zlia))). pose proof (Z.mod_pos_bound (shadow_addr mb + MSv / 8 + 4095) 4096 ltac:(img_try (zlia))).
pose proof (Z.div_mod MSv 8 ltac:(img_try (zlia))). pose proof (Z.mod_pos_bound MSv 8 ltac:(img_try (zlia))). zlia. }
destruct grow eqn:Eg.
* destruct (zr_dec QSv (QSv + 131072) a) as [D3|D3].
{ apply NO, OWN_Q. pose proof (proj1 Hgrow eq_refl) as EIR. pose proof (ws_reserved _ (wf_secondary _ _ _ _ _ (proj1 MP))) as WR.
pose proof (SF_parts true z) as (_ & _ & _ & _ & _ & _ & _ & _ & Rarr & Rres & _). rewrite Rarr, Rres in WR.
unfold QSv in D3. clear - D3 HI HRS EIR WR MZ. unfold kPtrArrayResv, kMaxNumChunks, kPtrArrayEntriesPerCommit in *. zlia. }
rewrite (HOUT x) in EhZ; [img_try (congruence) | img_try (rewrite Ux; img_exact D1) | img_try (rewrite Ux; img_exact D2) | img_try (rewrite Ux; intros [_ Hq]; img_exact (D3 Hq))].
* rewrite (HOUT x) in EhZ; [img_try (congruence) | img_try (rewrite Ux; img_exact D1) | img_try (rewrite Ux; img_exact D2) | img_try (intros [E _]; discriminate E)].
-
pose proof (MONf x EhW) as EhZ. unfold aview, mbyte, mrestrict. (subst x; cbv beta). rewrite EhW, EhZ, MEQa. img_refl.
Qed.
End l.
End g.
End d.
