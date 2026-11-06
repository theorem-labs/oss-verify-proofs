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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF64 YF3v YF3w YF3x YF41 YF47 YF0a YF5k YF4b YF4c YF4d YF4e YF5t YF5u YF5v YF5f YF5l YF5m YF5i YF5j YF5n.
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
Local Abbreviation ARf f := (f idx res Hidx) (only parsing).
Local Abbreviation tr_length := (ARf ((AR1 (@YF5k.tr_length)) ch)).
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
Local Abbreviation ARg f := (f imgk W ly) (only parsing).
Local Abbreviation kept_of_frame := ((AR9 ((ARg (@YF5k.kept_of_frame)) regs0)) Hidx).
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
Local Abbreviation window_present := (ARf (AR1 (@YF5k.window_present))).
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
Local Abbreviation kept_of_frame2 := (ARf (AR1 (@YF5k.kept_of_frame2))).
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
Local Abbreviation vis_present := ((ARf (AR4 (@YF5t.vis_present _))) DPOST B S HARm).
Local Abbreviation in_thread_junk := (@YF5t.in_thread_junk ly B S).
Local Abbreviation in_sec_junk := (@YF5t.in_sec_junk ly B S).
Local Abbreviation in_as_junk := (@YF5t.in_as_junk ly B S).
Local Abbreviation junk_word := ((ARe (AR4 (@YF5t.junk_word _))) DPOST B S HARm).
Local Abbreviation cell_sym := ((ARg (@YF5t.cell_sym _)) mem0 B S TS HARm).
Local Abbreviation cell_lit := ((ARg (@YF5t.cell_lit _)) mem0 B S TS HARm).
Local Abbreviation cell_state := ((ARg (@YF5t.cell_state _)) mem0 B S HARm).
Local Abbreviation In_acells_sec := (@YF5t.In_acells_sec ly B S).
Local Abbreviation sec_vals := ((ARg (@YF5t.sec_vals _)) mem0 idx res B S TS HARm Hidx_def Hres_def).
Local Abbreviation unwinding_val := ((ARg (@YF5t.unwinding_val _)) mem0 B S HARm).
Local Abbreviation rw_writable := ((ARf (AR1 (@YF5t.rw_writable))) DPOST S).
Local Abbreviation val_mem_mod8 := ((ARf (AR4 (@YF5t.val_mem_mod8))) DPOST S).
Local Abbreviation chunk_lit := (AR0 (AR4 (@YF5t.chunk_lit))).
Local Abbreviation chunk_lit_at := (AR0 (AR4 (@YF5t.chunk_lit_at))).
Local Abbreviation chunk_atom := ((AR0 (AR4 (@YF5t.chunk_atom))) Hidx DPOST S).
Local Abbreviation ARa f := (f DPOST B S TS HTSD HARm Hidx_def Hres_def Hj0 Hj1 Hj2 Hj3 Hj4 Hj5 Hj9 Hj6 Hj7 Hj8 Hi1 Hi2 Hi3) (only parsing).
Local Abbreviation SREG0_ok := (ARa ((AR2 (AR0 (AR4 (@YF5u.SREG0_ok _)))) Hpres0)).
Local Abbreviation PAIRS_ok := ((AR2 (AR0 (AR4 (@YF5v.PAIRS_ok _)))) DPOST S).
Local Abbreviation FACTS_ok := ((ARd ((ARb (AR4 (@YF5v.FACTS_ok _))) Hn Hsp)) DPOST S).
Local Abbreviation SEED_ok := (ARa ((ARd ((ARb (AR4 (@YF5v.SEED_ok _ _))) Hn Htp Hsp)) Hpres0)).
Local Abbreviation PBUF := ((ARg (@YF5f.PBUF)) regs0 ch).
Local Abbreviation PBUF_stableP := (AR2 (AR9 ((ARg (@YF5f.PBUF_stableP _)) regs0 n ch))).
Local Abbreviation PBUF_stableM := (ARh (AR9 ((ARg (@YF5f.PBUF_stableM _)) regs0 n ch))).
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
Local Abbreviation PBUF_stableN := (AR2 (AR9 ((ARg (@YF5l.PBUF_stableN _)) regs0 n ch))).
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
Local Abbreviation skel_cases := ((ARf (@YF5m.skel_cases imgk)) Hres S Hidx_def Hres_def).
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
Local Abbreviation chunk_eqb_eq := ((ARf (@YF5m.chunk_eqb_eq imgk)) Hres S Hidx_def Hres_def).
Local Abbreviation subregionb := (@YF5m.subregionb imgk).
Local Abbreviation subregionb_sound := (AR8 ((ARf (AR6 (@YF5m.subregionb_sound))) Hres)).
Local Abbreviation submemb := (@YF5m.submemb imgk).
Local Abbreviation submemb_sound := (AR8 ((ARf (AR6 (@YF5m.submemb_sound))) Hres)).
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
Variable RX : (word -> option byte) -> Prop.
Hypothesis RXs : rstable RX.
Hypothesis RXt : pstable WIN1T RX.
Local Ltac s_runS HR tbl tblok stop ss' HX HP :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let st := img_ev (snd (sym_run_toN_sh tfxsegs tbl FUEL stop ss)) in
eapply SRr_bind;
[ img_try (eapply (at_S_runS Wx tbl tblok stop md X P ss ss' st W' c' HR);
[ (img_case; vm_compute); img_refl | img_exact I | img_exact HX | (img_case; vm_compute); img_refl | img_exact HP | (img_case; vm_compute); img_refl ])
| img_try (clear HR; let W2 := fresh "W" in let c2 := fresh "c" in intros W2 c2 _ HR) ] end.
Local Ltac s_runT HR tbl tblok stop ss' HX HP :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let st := img_ev (snd (sym_run_toN_sh tfxsegs tbl FUEL stop ss)) in
eapply SRr_bind;
[ img_try (eapply (at_S_runT Wx tbl tblok stop md X P ss ss' st W' c' HR);
[ (img_case; vm_compute); img_refl | img_exact I | img_exact HX | (img_case; vm_compute); img_refl | img_exact HP | (img_case; vm_compute); img_refl ])
| img_try (clear HR; let W2 := fresh "W" in let c2 := fresh "c" in intros W2 c2 _ HR) ] end.
Definition SH5 : list (Z * Z * Z) :=
[(SMv + 768, SMv + 768 + N8D / 8, 0); (SHBv + UEv / 8, SMv + MSv / 8, 250); (SMv + 512, SMv + 768, 250); (SMv, SMv + 512, 250); (SMv + 768 + N8D / 8, SHBv + UEv / 8, 0)].
Definition SH6 : list (Z * Z * Z) := (Uv, Uv + 4096, 190) :: SH5.
Lemma user_marks : 8064 <= N8D / 8 <= R8v / 8 /\ (n mod 8 = 0 -> N8D / 8 = R8v / 8) /\ (n mod 8 <> 0 -> N8D / 8 + 1 = R8v / 8) /\ PBv = SMv + 768 + N8D / 8 /\ Uv = mb + 6144.
Proof.
pose proof map_facts as (_ & _ & _ & _ & U5 & _ & _ & _ & _ & _ & _ & _ & _ & _ & PB & _). pose proof map_zoneN as MZ.
pose proof size_facts as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & _). pose proof Nrange as NR. unfold MALLOC_MAX in Z1, NR. clear - U5 PB Z1 Z2 Z3 Z4 Z5 Z6 NR MZ.
apply Z.mod_divide in Z2 as [q Hq]; [|img_try (zlia)]. apply Z.mod_divide in Z5 as [p Hp]; [|img_try (zlia)]. rewrite Hq, Hp in *. rewrite !Z_div_mult by zlia.
unfold R8v, N8D in *. pose proof (Z.div_mod n 8 ltac:(img_try (zlia))) as D1. pose proof (Z.mod_pos_bound n 8 ltac:(img_try (zlia))) as B1.
pose proof (Z.div_mod (n + 7) 8 ltac:(img_try (zlia))) as D2. pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(img_try (zlia))) as B2.
repeat split; try zlia; intros H8; nia.
Qed.
Lemma SH56_ok : Forall run_ok SH5 /\ Forall run_ok SH6.
Proof.
pose proof shadow_marks as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9). pose proof user_marks as (B1 & _ & _ & _ & B5).
pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & _). clear - A1 A2 A3 A4 A5 A6 A7 A8 A9 B1 B5 Z8.
unfold SH5, SH6, run_ok. repeat split; repeat (img_apply Forall_cons || img_apply Forall_nil); cbn [fst snd]; zlia.
Qed.
Section U.
Variables (X : Z -> Prop) (z : Z).
Hypothesis HXW : forall a, WIN a -> X a.
Hypothesis Hsmall : N8D / 8 < 18446744073709551615.
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
Lemma segU1 : forall W' c, at_S Wy md1 X (PSR Wy SH4 (PDX Wy RX z)) T_R W' c -> SRr tfxsegs W' c (at_S Wy md1 X (PSR Wy SH5 (PDX Wy RX z)) U_QJ).
Proof.
intros W1 c HR. pose proof SH34_ok as [_ OK4]. pose proof SH56_ok as [OK5 _]. pose proof (PDX_rstable Wy RX RXs z) as RS.
pose proof (PSR_stableS Wy SH4 (PDX Wy RX z) OK4 (PDX_stableS Wy RX RXt z)) as HP4. pose proof (PSR_stableS Wy SH5 (PDX Wy RX z) OK5 (PDX_stableS Wy RX RXt z)) as HP5.
assert (HX : forall a, WIN1S a -> X a) by (img_try (intros a Ha; apply HXW, WIN1S_WIN, Ha)).
pose proof map_facts as (M1 & M2 & M3 & _). pose proof map_zoneN as MZ. ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in M1, M2.
pose proof size_facts as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & _). pose proof Nrange as NR. unfold MALLOC_MAX in Z1, Z8, NR.
pose proof shadow_marks as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9). pose proof user_marks as (B1 & B2 & B3 & B4 & B5).
s_arm HR BC_LTU true USH_LEN (SLit 18446744073709551615).
{ clear - M1 M2 M3 Z8 Z4 Z5 NR Hsmall MZ. arm_zevS. unfold USH_LEN. cbn [zev zalu_raw]. unfold_atoms. rewrite EaMAP, EaN8D. unfold w64. rewrite !unsigned_lit_small by zlia.
zcanon_simp. land_lits. rewrite !Z.shiftr_div_pow2 by zlia. img_change (2 ^ 3) with 8.
apply Z.mod_divide in M3 as [u Hu]; [|img_try (zlia)]. apply Z.mod_divide in Z5 as [p Hp]; [|img_try (zlia)]. rewrite Hu, Hp in *.
replace (u * 4096 + 6136 + (p * 8 + 0)) with ((u * 512 + 767 + p) * 8) by zlia. replace (u * 4096 + 6144) with ((u * 512 + 768) * 8) by zlia.
rewrite !Z_div_mult in * by zlia. zcanon_simp. img_apply Z.ltb_lt. zlia. }
s_runS HR tfxtbl_rtA tfxtbl_rtA_ok (0x9b894 + D_10ec) U_M5 HX HP4.
s_memsetR HR U_Q sM5 constr:(SMv + 768) constr:(N8D / 8) 0 (0x31dd4 + D_150) OK4 RS.
{ clear - M1 M2 M3 Z8 A7 MZ. U_zevS. rewrite (eq_refl : ew E0 47 = w64 SHBv), EaMAP. unfold w64, YF5k.SHBv in *. rewrite !unsigned_lit_small by zlia.
zcanon_simp. land_lits. rewrite Z.shiftr_div_pow2 by zlia. img_change (2 ^ 3) with 8.
apply Z.mod_divide in M3 as [u Hu]; [|img_try (zlia)]. rewrite Hu in *. replace (u * 4096 + 6144) with ((u * 512 + 768) * 8) by zlia. rewrite Z_div_mult by zlia.
rewrite A7. replace (u * 4096) with ((u * 512) * 8) by zlia. rewrite Z_div_mult by zlia. zcanon_simp. zlia. }
{ clear - M1 M2 M3 Z8 Z4 Z5 NR MZ. U_zevS. unfold USH_LEN. cbn [zev zalu_raw]. unfold_atoms. rewrite EaMAP, EaN8D. unfold w64. rewrite !unsigned_lit_small by zlia.
zcanon_simp. land_lits. rewrite !Z.shiftr_div_pow2 by zlia. img_change (2 ^ 3) with 8.
apply Z.mod_divide in M3 as [u Hu]; [|img_try (zlia)]. apply Z.mod_divide in Z5 as [p Hp]; [|img_try (zlia)]. rewrite Hu, Hp in *.
replace (u * 4096 + 6136 + (p * 8 + 0)) with ((u * 512 + 767 + p) * 8) by zlia. replace (u * 4096 + 6144) with ((u * 512 + 768) * 8) by zlia.
rewrite !Z_div_mult in * by zlia. zcanon_simp. zlia. }
{ right. clear - A2 A3 A5 A6 B1 MZ. zlia. }
apply (PSR_runs Wy md1 X _ SH5 (PDX Wy RX z) U_Q) in HR.
2:{ intros m HF. pose proof (Forall_inv HF) as C0. pose proof (Forall_inv_tail HF) as B2'. clear HF.
unfold cut, SH4 in B2'. cbn [flat_map app] in B2'. unfold cut1 in B2'. cbn [fst snd] in B2'.
assert (G1 : (SHBv + UEv / 8 <? SMv + 768) = false) by (img_try (clear - A2 A5 MZ; img_apply Z.ltb_ge; zlia)).
assert (G2 : (SMv + 768 + N8D / 8 <? SMv + MSv / 8) = true) by (img_try (clear - A2 A3 A5 A6 B1 MZ; img_apply Z.ltb_lt; zlia)).
assert (G3 : (SMv + 512 <? SMv + 768) = true) by (img_try (img_apply Z.ltb_lt; zlia)).
assert (G4 : (SMv + 768 + N8D / 8 <? SMv + 768) = false) by (img_try (clear - B1 MZ; img_apply Z.ltb_ge; zlia)).
assert (G5 : (SMv <? SMv + 768) = true) by (img_try (img_apply Z.ltb_lt; zlia)).
assert (G6 : (SMv + 768 + N8D / 8 <? SMv + 512) = false) by (img_try (clear - B1 MZ; img_apply Z.ltb_ge; zlia)).
assert (G7 : (SMv + 768 <? SMv + 768) = false) by (img_try (img_apply Z.ltb_irrefl)).
rewrite G1, G2, G3, G4, G5, G6, G7 in B2'. cbn [app] in B2'.
pose proof (Forall_inv B2') as C1. pose proof (Forall_inv (Forall_inv_tail B2')) as C2. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail B2'))) as C3.
pose proof (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail B2'))) as C4'. clear B2'.
rewrite Z.max_l in C1 by (img_try (clear - A2 A5 B1 MZ; zlia)). rewrite Z.min_l in C2 by zlia. rewrite Z.min_l in C3 by zlia.
unfold SH5. img_apply Forall_cons; [img_try (img_exact C0)|]. img_apply Forall_cons; [img_try (img_exact C1)|]. img_apply Forall_cons; [img_try (img_exact C2)|]. img_apply Forall_cons; [img_try (img_exact C3)|].
img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
destruct (SMv + 768 + N8D / 8 <? SHBv + UEv / 8) eqn:G8; cbn [app] in C4'.
- pose proof (Forall_inv C4') as C4. rewrite Z.max_r in C4 by (img_try (clear - B1 MZ; zlia)). img_exact C4.
- apply Z.ltb_ge in G8. intros a Ha. cbn [fst snd] in Ha. exfalso. clear - G8 Ha MZ. zlia. }
lazymatch type of HR with at_S ?Wx ?md ?X0 ?P ?ss ?W' ?c' =>
apply (at_S_submem Wx md X0 P ss W' c' (trimscratch (-2272) (ss_mem U_Q))) in HR; [| img_try ((img_case; vm_compute); img_refl) | img_try ((img_case; vm_compute); img_refl)] end.
s_forget HR kJQ CLOBJ. s_noconds HR. s_station HR U_QJ.
img_apply SRr_ret. img_exact HR.
Qed.
Lemma SH6_of_cut : forall m, Forall (brun m) ((Uv, Uv + 4096, 190) :: cut Uv (Uv + 4096) SH5) -> Forall (brun m) SH6.
Proof.
intros m HF. pose proof (Forall_inv HF) as C0. pose proof (Forall_inv_tail HF) as B'. clear HF.
pose proof shadow_marks as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9). pose proof user_marks as (B1 & _ & _ & _ & B5).
pose proof map_facts as (M1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _). pose proof map_zoneN as MZ. pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & _).
unfold cut, SH5 in B'. cbn [flat_map app] in B'. unfold cut1 in B'. cbn [fst snd] in B'.
destruct MZ as [ZLO|ZHI].
-
assert (BOT : Uv + 4096 < SMv) by (img_try (clear - ZLO B5 Z8; unfold MALLOC_MAX in *; zlia)).
assert (G1 : forall x, SMv <= x -> (x <? Uv) = false) by (img_try (intros x Hx; img_apply Z.ltb_ge; clear - Hx BOT; zlia)).
assert (G2 : forall x, SMv <= x -> (Uv + 4096 <? x) = true) by (img_try (intros x Hx; img_apply Z.ltb_lt; clear - Hx BOT; zlia)).
rewrite !G1 in B' by (img_try (clear - A1 A2 A3 A4 A5 A6 A7 A8 A9 B1; zlia)). rewrite !G2 in B' by (img_try (clear - A1 A2 A3 A4 A5 A6 A7 A8 A9 B1; zlia)). cbn [app] in B'.
rewrite !Z.max_l in B' by (img_try (clear - A1 A2 A3 A4 A5 A6 A7 A8 A9 B1 BOT; zlia)).
unfold SH6, SH5. img_apply Forall_cons; [img_try (img_exact C0) | img_try (img_exact B')].
-
assert (TOP : SMv + MSv / 8 < Uv) by (img_try (clear - ZHI B5; zlia)).
assert (G1 : forall x, x <= SMv + MSv / 8 -> (x <? Uv) = true) by (img_try (intros x Hx; img_apply Z.ltb_lt; clear - Hx TOP; zlia)).
assert (G2 : forall x, x <= SMv + MSv / 8 -> (Uv + 4096 <? x) = false) by (img_try (intros x Hx; img_apply Z.ltb_ge; clear - Hx TOP; zlia)).
rewrite !G1 in B' by (img_try (clear - A1 A2 A3 A4 A5 A6 A7 A8 A9 B1; zlia)). rewrite !G2 in B' by (img_try (clear - A1 A2 A3 A4 A5 A6 A7 A8 A9 B1; zlia)). cbn [app] in B'.
rewrite !Z.min_l in B' by (img_try (clear - A1 A2 A3 A4 A5 A6 A7 A8 A9 B1 TOP; zlia)).
unfold SH6, SH5. img_apply Forall_cons; [img_try (img_exact C0) | img_try (img_exact B')].
Qed.
Lemma segUe : n mod 8 = 0 -> forall W' c, at_S Wy md1 X (PSR Wy SH5 (PDX Wy RX z)) U_QJ W' c -> SRr tfxsegs W' c (at_S Wy md1 X (PSR Wy SH6 (PDX Wy RX z)) Ue_RET).
Proof.
intros H8 W1 c HR. pose proof SH56_ok as [OK5 OK6]. pose proof (PDX_rstable Wy RX RXs z) as RS.
pose proof (PSR_stableS Wy SH5 (PDX Wy RX z) OK5 (PDX_stableS Wy RX RXt z)) as HP5. pose proof (PSR_stableS Wy SH6 (PDX Wy RX z) OK6 (PDX_stableS Wy RX RXt z)) as HP6.
assert (HX : forall a, WIN1S a -> X a) by (img_try (intros a Ha; apply HXW, WIN1S_WIN, Ha)).
pose proof map_facts as (M1 & M2 & M3 & _). pose proof map_zoneN as MZ. ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in M1, M2.
pose proof size_facts as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & _). pose proof Nrange as NR. unfold MALLOC_MAX in Z1, Z8, NR.
pose proof user_marks as (B1 & B2 & B3 & B4 & B5).
s_arm HR BC_EQ true (SOff 10 0) (SOff aN8DS 0).
{ clear - H8 NR Hn Z4 Z6 MZ. arm_zevS. rewrite E10, Hn, EaN8D. unfold w64. rewrite !unsigned_lit_small by zlia. zcanon_simp. img_apply Z.eqb_eq.
unfold N8D in *. pose proof (Z.div_mod n 8 ltac:(img_try (zlia))). zlia. }
s_runS HR tfxtbl_rtA tfxtbl_rtA_ok (0x9b894 + D_10ec) Ue_MF HX HP5.
s_memsetR HR (ss_after_stretch Ue_MF (ss_mem Ue_MF) sMF CLOB_MS (0x31ffc + D_150)) sMF constr:(Uv) 4096 190 (0x31ffc + D_150) OK5 RS.
{ clear - M1 M2 Z8 B5 MZ. U_zevS. rewrite EaMAP. unfold w64. rewrite !unsigned_lit_small by zlia. zcanon_simp. zlia. }
{ clear. U_zevS. img_refl. }
{ left. clear - Z8 B5 MZ. zlia. }
apply (PSR_runs Wy md1 X _ SH6 (PDX Wy RX z)) in HR; [|img_try (img_exact SH6_of_cut)].
s_runS HR tfxtbl_rtA tfxtbl_rtA_ok (0x32024 + D_150) (runto (0x32024 + D_150) (ss_after_stretch Ue_MF (ss_mem Ue_MF) sMF CLOB_MS (0x31ffc + D_150))) HX HP6.
s_arm HR BC_EQ false (SOff aMAP 6128) (SOff aMAP 4096).
{ clear - M1 M2 Z8 MZ. arm_zevS. rewrite EaMAP. unfold w64. rewrite !unsigned_lit_small by zlia. zcanon_simp. img_apply Z.eqb_neq. zlia. }
s_runS HR tfxtbl_rtA tfxtbl_rtA_ok (0x3202c + D_150) (runto (0x3202c + D_150) (arm BC_EQ false (SOff aMAP 6128) (SOff aMAP 4096) (runto (0x32024 + D_150) (ss_after_stretch Ue_MF (ss_mem Ue_MF) sMF CLOB_MS (0x31ffc + D_150))))) HX HP6.
s_arm HR BC_LTU false (SOff aMAP 6128) (SOff aMAP 4112).
{ clear - M1 M2 Z8 MZ. arm_zevS. rewrite EaMAP. unfold w64. rewrite !unsigned_lit_small by zlia. zcanon_simp. img_apply Z.ltb_ge. zlia. }
s_runS HR tfxtbl_rtA tfxtbl_rtA_ok (0x53434 + D_2c4) Ue_RET HX HP6.
img_apply SRr_ret. img_exact HR.
Qed.
Definition PT (sh : list (Z * Z * Z)) (R : (word -> option byte) -> Prop) (m : word -> option byte) : Prop :=
PBUFW Wy m /\ (forall a, mb + 6144 <= a < mb + MSv -> apresent (w_H Wy) m a) /\
(forall a, SMv <= a < SMv + MSv / 8 -> a <> PBv -> apresent (w_H Wy) m a) /\ Forall (brun m) sh /\ R m.
Definition run_okT (r : Z * Z * Z) : Prop := run_ok r /\ (snd (fst r) <= PBv \/ PBv + 1 <= fst (fst r)).
Definition SH5o : list (Z * Z * Z) :=
[(SMv + 768, SMv + 768 + N8D / 8, 0); (SHBv + UEv / 8, SMv + MSv / 8, 250); (SMv + 512, SMv + 768, 250); (SMv, SMv + 512, 250); (PBv + 1, SHBv + UEv / 8, 0)].
Definition SH6o : list (Z * Z * Z) := (Uv, Uv + 4096, 190) :: SH5o.
Lemma SH56o_ok : n mod 8 <> 0 -> Forall run_okT SH5o /\ Forall run_okT SH6o.
Proof.
intros H8. pose proof shadow_marks as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9). pose proof user_marks as (B1 & _ & B3 & B4 & B5). specialize (B3 H8).
pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & _). pose proof map_facts as (M1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _). pose proof map_zoneN as MZ.
unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg in M1. unfold kHighShadowEnd in SM2. clear - A1 A2 A3 A4 A5 A6 A7 A8 A9 B1 B3 B4 B5 Z8 M1 SM2 MZ.
unfold SH5o, SH6o, run_okT, run_ok. repeat split; repeat (img_apply Forall_cons || img_apply Forall_nil); cbn [fst snd]; zlia.
Qed.
Lemma PT_stableT : forall sh R, Forall run_okT sh -> pstable WIN1T R -> pstable WIN1T (PT sh R).
Proof.
intros sh R OK RS m m' FR (HB & HM & HSH & HR' & HQ).
pose proof map_facts as (M1 & M2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _). pose proof map_zoneN as MZ.
assert (U : forall a, (mb + 6144 <= a < mb + MSv) \/ (SMv <= a < SMv + MSv / 8) -> a <> PBv -> m' (w64 a) = m (w64 a)).
{ intros a Ha Hne. img_apply FR. unfold w64. rewrite unsigned_lit_small by (img_try (clear - Ha M1 M2 SM1 SM2 MZ; ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighShadowBeg, kHighShadowEnd, ASAN_CEIL in *; zlia)).
intros [Hw|[Hw|[Hw|Hw]]]; [img_try (img_exact (runs_not_WIN1S a Ha (or_introl Hw))) | img_try (img_exact (runs_not_WIN1S a Ha (or_intror (or_introl Hw)))) | img_try (img_exact (runs_not_WIN1S a Ha (or_intror (or_intror Hw)))) | img_try (clear - Hw Hne MZ; zlia)]. }
split; [img_try (img_exact (PBUFW_stableT Wy m m' FR HB))|].
pose proof user_marks as (B1 & _ & _ & B4 & _). pose proof shadow_marks as (_ & A2 & A3 & _ & _ & A6 & _).
split; [img_try (intros a Ha; img_apply (apresent_same (w_H Wy) m); [img_apply (U a (or_introl Ha)); clear - Ha B4 B1 A2 A3 A6 M1 SM2 MZ; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighShadowEnd in *; zlia | img_exact (HM a Ha)])|].
split; [img_try (intros a Ha Hne; img_apply (apresent_same (w_H Wy) m); [img_exact (U a (or_intror Ha) Hne) | img_exact (HSH a Ha Hne)])|].
split; [|img_try (img_exact (RS m m' FR HQ))].
img_apply Forall_forall. intros r Hr a Ha. pose proof (proj1 (Forall_forall _ _) OK r Hr) as [RO RP]. pose proof (proj1 (Forall_forall _ _) HR' r Hr a Ha) as V.
rewrite (U a); [img_try (img_exact V) | img_try (unfold run_ok in RO; clear - RO Ha MZ; zlia) | img_try (clear - RP Ha MZ; zlia)].
Qed.
Lemma segUo : n mod 8 <> 0 -> forall W' c, at_S Wy md1 X (PSR Wy SH5 (PDX Wy RX z)) U_QJ W' c -> SRr tfxsegs W' c (at_S Wy md1 X (PT SH6o (PDX Wy RX z)) Uo_RET).
Proof.
intros H8 W1 c HR. pose proof SH56_ok as [OK5 _]. pose proof (SH56o_ok H8) as [OK5o OK6o].
pose proof (PSR_stableS Wy SH5 (PDX Wy RX z) OK5 (PDX_stableS Wy RX RXt z)) as HP5.
pose proof (PT_stableT SH5o (PDX Wy RX z) OK5o (PDX_stableT Wy RX RXt z)) as HT5. pose proof (PT_stableT SH6o (PDX Wy RX z) OK6o (PDX_stableT Wy RX RXt z)) as HT6.
assert (HX : forall a, WIN1S a -> X a) by (img_try (intros a Ha; apply HXW, WIN1S_WIN, Ha)).
assert (HXT : forall a, WIN1T a -> X a) by (img_try (intros a Ha; apply HXW, WIN1T_WIN, Ha)).
pose proof map_facts as (M1 & M2 & M3 & K4 & U5 & E6 & UE7 & E8 & UE9 & MT & MU & SM1 & SM2 & SM3 & PB & SMA). pose proof map_zoneN as MZ. ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in M1, M2. unfold kHighShadowBeg, kHighShadowEnd in SM1, SM2.
pose proof size_facts as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & _). pose proof Nrange as NR. unfold MALLOC_MAX in Z1, Z8, NR.
pose proof user_marks as (B1 & B2 & B3 & B4 & B5). specialize (B3 H8). pose proof shadow_marks as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
assert (PLfill : (mb + 6144 <= Uv /\ Uv + 4096 <= mb + MSv) \/ (SMv <= Uv /\ Uv + 4096 <= SMv + MSv / 8)) by (img_try (left; clear - B5 Z8 MZ; zlia)).
s_arm HR BC_EQ false (SOff 10 0) (SOff aN8DS 0).
{ clear - H8 NR Hn Z4 Z6 MZ. arm_zevS. rewrite E10, Hn, EaN8D. unfold w64. rewrite !unsigned_lit_small by zlia. zcanon_simp. img_apply Z.eqb_neq.
unfold N8D in *. pose proof (Z.div_mod n 8 ltac:(img_try (zlia))). zlia. }
s_runS HR tfxtbl_rtA tfxtbl_rtA_ok (0x31e00 + D_150) Uo_L6 HX HP5.
s_ladderM s_runS HR tfxtbl_rtA tfxtbl_rtA_ok (0x31e64 + D_150) Uo_L6lo Uo_L6h Uo_L6h2 Uo_L6hi Uo_P0 sL6 CLOB_L6 HX HP5.
s_pin HR (10%bv : bv 5) (SOff aPBS 0).
{ clear - M1 M2 M3 Z8 Z4 Z5 NR A7 B4 MZ. pin_zevS. rewrite EaPB, (eq_refl : ew E0 47 = w64 SHBv), EaMAP, EaN8D. unfold w64, YF5k.SHBv in *.
rewrite B4 in *. rewrite A7 in *. rewrite !unsigned_lit_small by zlia.
zcanon_simp. land_lits. rewrite Z.shiftr_div_pow2 by zlia. img_change (2 ^ 3) with 8.
apply Z.mod_divide in M3 as [u Hu]; [|img_try (zlia)]. apply Z.mod_divide in Z5 as [p Hp]; [|img_try (zlia)]. rewrite Hu, Hp in *.
replace (u * 4096 + 6144 + (p * 8 + 0)) with ((u * 512 + 768 + p) * 8) by zlia. replace (u * 4096) with ((u * 512) * 8) by zlia. rewrite !Z_div_mult in * by zlia.
zcanon_simp. zlia. }
apply (at_S_addreg Wy md1 X _ _ _ _ R_pbS) in HR; [| img_refl |].
2:{ intros E' m HE MEQ PRS [(HB & HM & HSH & HRs) HQ] HMok. pose proof (proj1 HE) as HEn.
assert (BP : base_val E' (Some aPBS) = PBv).
{ cbn [base_val]. unfold aPBS. rewrite (HEn 66%nat ltac:(img_try (unfold sHAV; zlia))), EaPB. unfold w64. img_apply unsigned_lit_small. clear - B4 B1 A2 A5 A3 A6 SM1 SM2 MZ. zlia. }
split.
- unfold region_ok, R_pbS. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks]. rewrite BP.
split; [img_try (clear - B4 B1 SM1 MZ; zlia)|]. split; [img_try (clear - B4 B1 A2 A3 A5 A6 SM2 MZ; zlia)|]. split; [|img_try (img_apply Forall_nil)].
intros o Ho. img_apply apresent_writable_off; [img_try (off_by ltac:(clear - Ho B4 B1 SM1 A2 A3 A5 A6 SM2 MZ; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; zlia)) |]. img_apply HSH. clear - Ho B4 B1 A2 A3 A5 A6 MZ. zlia.
- intros r2 Hr2. unfold extent_disjoint, R_pbS. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi]. rewrite !BP.
lazymatch type of Hr2 with In _ ?l =>
pose proof (proj1 (forallb_forall _ _) (ltac:(img_eqrefl) : forallb (fun r => skel_okb false (skel r) && (YQ0b.r_lo r <? YQ0b.r_hi r)) l = true) r2 Hr2) as CK end.
cbn beta in CK. apply andb_prop in CK as [CK1 CK2]. apply Z.ltb_lt in CK2.
pose proof (skel_apart E' false PBv 1 HE ltac:(img_try (right; clear - B4 B1 A2 A3 A5 A6 MZ; zlia)) ltac:(img_try (intros XX; discriminate XX)) r2 CK1) as AP. clear - AP CK2 MZ. zlia. }
s_station HR Uo_P.
apply (at_S_weaken Wy md1 X X _ (PT SH5o (PDX Wy RX z)) Uo_P) in HR; [| img_try (intros a Ha; img_exact Ha) |].
2:{ intros m [(HB & HM & HSH & HRs) HQ]. split; [img_try (img_exact HB)|]. split; [img_try (img_exact HM)|]. split; [img_try (intros a Ha _; img_exact (HSH a Ha))|]. split; [|img_try (img_exact HQ)].
unfold SH5o. unfold SH5 in HRs.
pose proof (Forall_inv HRs) as C1. pose proof (Forall_inv (Forall_inv_tail HRs)) as C2. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HRs))) as C3.
pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail HRs)))) as C4. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail HRs))))) as C5.
repeat (img_apply Forall_cons); [img_try (img_exact C1) | img_try (img_exact C2) | img_try (img_exact C3) | img_try (img_exact C4) | | img_try (img_apply Forall_nil)].
intros a Ha. img_apply C5. cbn [fst snd] in *. clear - Ha B4 MZ. zlia. }
s_runT HR tfxtbl_rtA tfxtbl_rtA_ok (0x9b894 + D_10ec) Uo_MF HXT HT5.
lazymatch type of HR with at_S ?Wx ?md ?X0 ?P ?ss ?W' ?c' =>
eapply SRr_bind;
[ img_try (eapply (at_S_memset Wx md X0 P (PT SH6o (PDX Wy RX z)) ss W' c' sMF (SOff aMAP 6144) (SLit 4096) Uv 4096 190 (0x31ffc + D_150) HR eq_refl ltac:((try img_inst; img_case; vm_compute); img_refl) ltac:(unfold sHAV, sMF; zlia)
ltac:((try img_inst; img_case; vm_compute); img_refl) ltac:((try img_inst; img_case; vm_compute); img_refl) ltac:((try img_inst; img_case; vm_compute); img_refl) ltac:((try img_inst; img_case; vm_compute); img_refl) ltac:((try img_inst; img_case; vm_compute); img_refl) ltac:((try img_inst; img_case; vm_compute); img_refl)
ltac:((try img_inst; img_case; vm_compute); img_refl) ltac:((try img_inst; img_case; vm_compute); img_refl)))
| img_try (clear HR; intros W3 c3 _ HR) ] end.
{ clear - M1 M2 Z8 B5 MZ. U_zevS. rewrite EaMAP. unfold w64. rewrite !unsigned_lit_small by zlia. zcanon_simp. zlia. }
{ clear. U_zevS. img_refl. }
{ clear; zlia. }
{ clear - M1 B5 MZ. unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END. zlia. }
{ clear - M2 Z8 B5 MZ. zlia. }
{ clear; (img_case; cbv); img_refl. }
{ clear; zlia. }
{ clear; zlia. }
{ intros m MEQ (HB & HM & HSH & HRs & HQ) a Ha. img_apply HM. clear - Ha B5 Z8 MZ. zlia. }
{ refine (memset_ext_of_skel true Uv 4096 Uo_MF ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) PLfill _); intros _; clear - B1 B4 B5 M1 SM2 A2 A3 A5 A6 MZ; zlia. }
{ img_exact (memset_u64_of_skel true Uo_MF ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))). }
{ intros m m' MEQ (HB & HM & HSH & HRs & HQ) FR FILL.
assert (FR' : forall a, 0 <= a < 2 ^ 64 -> ~ (Uv <= a < Uv + 4096) -> m' (w64 a) = m (w64 a)).
{ intros a Ha Hna. img_apply FR. unfold w64. rewrite unsigned_lit_small by img_exact Ha. img_exact Hna. }
assert (TOP : SMv + MSv / 8 < Uv \/ Uv + 4096 < SMv) by (img_try (clear - B5 Z8 MZ; unfold MALLOC_MAX in *; zlia)).
split; [|img_try (split; [|split; [|split]])].
- intros i Hi. eapply val_mem_frame; [|img_try (img_exact (HB i Hi))]. intros kk Hkk. pose proof tr_length as LEN.
pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7). destruct Hsp as (S1 & _ & S3 & _). pose proof (u64_range (getr regs0 2)) as U2.
img_apply FR'; [img_try (clear - Hi Hkk LEN T7 S1 S3 U2 MZ; unfold zone3, TFX_IMG_LO, kLowShadowBeg, IFRAME, ASTACK, kHighMemBeg in *; unfold sp0 in *; zlia)|]. intros Hin.
img_apply (runs_not_stack (sp0 - IFRAME + 16 + 8 * Z.of_nat i + Z.of_nat kk)); [img_try (left; clear - Hin B5 Z8 MZ; zlia) | img_try (clear - Hi Hkk LEN MZ; unfold IFRAME, ASTACK; zlia)].
- intros a Ha. destruct (HM a Ha) as [Hh [b Hb]]. split; [img_try (img_exact Hh)|].
destruct (Z_lt_le_dec a (Uv + 4096)) as [L|GE].
+ exists (Z_to_bv 8 190). img_apply FILL. unfold w64. rewrite unsigned_lit_small by (img_try (clear - Ha M1 M2 Z8 MZ; zlia)). clear - Ha L B5 MZ; zlia.
+ exists b. rewrite <- Hb. img_apply (FR' a); clear - Ha GE M1 M2 Z8 MZ; zlia.
- intros a Ha Hne. destruct (HSH a Ha Hne) as [Hh [b Hb]]. split; [img_try (img_exact Hh)|]. exists b. rewrite <- Hb. img_apply (FR' a); [img_try (clear - Ha SM1 SM2 MZ; zlia) | img_try (clear - Ha TOP MZ; zlia)].
- unfold SH6o. img_apply Forall_cons.
+ intros a Ha. cbn [fst snd] in Ha. img_apply FILL. unfold w64. rewrite unsigned_lit_small by (img_try (clear - Ha M1 M2 Z8 B5 MZ; zlia)). img_exact Ha.
+ img_apply Forall_forall. intros r Hr a Ha. pose proof (proj1 (Forall_forall _ _) OK5o r Hr) as [RO _].
rewrite FR'; [img_try (img_exact (proj1 (Forall_forall _ _) HRs r Hr a Ha)) | img_try (unfold run_ok in RO; clear - RO Ha M1 M2 SM1 SM2 Z8 MZ; zlia) |].
unfold run_ok in RO. unfold SH5o in Hr. cbn [In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd] in Ha; clear - Ha TOP B1 B4 A2 A3 A5 A6 MZ; zlia.
- destruct HQ as [(memD & D1' & D2 & D3) HRX]. split; [| img_try (img_exact (proj2 RXs m m' Uv 4096 PLfill FR HRX))].
exists memD. split; [img_try (img_exact D1')|]. split; [img_try (img_exact D2)|]. intros x Hx. rewrite FR; [img_try (img_exact (D3 x Hx))|].
intros Hin. img_exact (proj1 (DZONE_disj _ Hx) (place_WIN Uv 4096 _ PLfill Hin)). }
apply (at_S_weaken Wy md1 _ X _ (PT SH6o (PDX Wy RX z))) in HR; [| img_try (intros a [Ha|Ha]; [img_exact Ha | img_exact (HXW a (place_WIN Uv 4096 a PLfill Ha))]) | img_try (intros m Hm; img_exact Hm)].
lazymatch type of HR with at_S _ _ _ _ ?ss2 _ _ => replace ss2 with (ss_after_stretch Uo_MF (ss_mem Uo_MF) sMF CLOB_MS (0x31ffc + D_150)) in HR by (img_try ((img_case; vm_compute); img_refl)) end.
s_runT HR tfxtbl_rtA tfxtbl_rtA_ok (0x32024 + D_150) (runto (0x32024 + D_150) (ss_after_stretch Uo_MF (ss_mem Uo_MF) sMF CLOB_MS (0x31ffc + D_150))) HXT HT6.
s_arm HR BC_EQ false (SOff aMAP 6128) (SOff aMAP 4096).
{ clear - M1 M2 Z8 MZ. arm_zevS. rewrite EaMAP. unfold w64. rewrite !unsigned_lit_small by zlia. zcanon_simp. img_apply Z.eqb_neq. zlia. }
s_runT HR tfxtbl_rtA tfxtbl_rtA_ok (0x3202c + D_150) (runto (0x3202c + D_150) (arm BC_EQ false (SOff aMAP 6128) (SOff aMAP 4096) (runto (0x32024 + D_150) (ss_after_stretch Uo_MF (ss_mem Uo_MF) sMF CLOB_MS (0x31ffc + D_150))))) HXT HT6.
s_arm HR BC_LTU false (SOff aMAP 6128) (SOff aMAP 4112).
{ clear - M1 M2 Z8 MZ. arm_zevS. rewrite EaMAP. unfold w64. rewrite !unsigned_lit_small by zlia. zcanon_simp. img_apply Z.ltb_ge. zlia. }
s_runT HR tfxtbl_rtA tfxtbl_rtA_ok (0x53434 + D_2c4) Uo_RET HXT HT6.
img_apply SRr_ret. img_exact HR.
Qed.
End U.
End h.
End g.
