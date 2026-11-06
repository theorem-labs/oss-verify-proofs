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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF64 YF3v YF4q YF3w YF3l YF41.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Set Printing Depth 50. Set Printing Width 180.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Ltac zlia := first [ img_lia | ceil; unfold zone3, zone3cases, off_img, in_app, app_addr, in_band_rw, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPrimResvSize, kSpaceSize in *; img_lia ].
Ltac zcanon_simp :=
repeat match goal with
| |- context [zcanon ?x] =>
lazymatch x with
| context [zcanon _] => fail
| context [Z.shiftl _ _] => fail | context [Z.shiftr _ _] => fail | context [Z.land _ _] => fail
| context [Z.lor _ _] => fail | context [Z.lxor _ _] => fail
| _ => rewrite (zcanon_id x) by (img_try (unfold M64; img_lia))
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
ltac:(img_try ((img_case; vm_compute); img_refl)) ltac:(img_try ((img_case; vm_compute); img_refl)) ltac:(img_try ((img_case; vm_compute); img_refl)) ltac:(img_try ((img_case; vm_compute); img_refl))
eq_refl eq_refl ltac:(img_try ((img_case; vm_compute); img_refl))) as HS2; clear HS; rename HS2 into HS
end.
Section e. Context {imgk : img}.
Variables (W : world tfxsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (n : Z) (ch : list (Z * Z * Z)).
Variables (cl cnt v csz j0 jb j1 j2 j3 j4 : Z).
Variable kz : Z.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Local Abbreviation RZ := (@YF4q.RZ kz).
Local Abbreviation R8v := (@YF4q.R8v n).
Local Abbreviation N8D := (@YF4q.N8D n).
Local Abbreviation Pv := (@YF4q.Pv ly cl).
Local Abbreviation PVv := (@YF4q.PVv ly cl cnt).
Local Abbreviation Kv := (@YF4q.Kv ly cl v).
Local Abbreviation SHBv := (@YF4q.SHBv).
Local Abbreviation SKv := (@YF4q.SKv ly cl v).
Local Abbreviation SSLOTv := (@YF4q.SSLOTv ly cl).
Local Abbreviation AR6 f := (f n cl v kz) (only parsing).
Local Abbreviation PBv := (AR6 (@YF4q.PBv ly)).
Local Abbreviation Uv := (@YF4q.Uv ly cl v kz).
Local Abbreviation SUv := (@YF4q.SUv ly cl v kz).
Local Abbreviation FILv := (@YF4q.FILv n).
Local Abbreviation NDv := (@YF4q.NDv n kz).
Local Abbreviation AR2 f := (f imgk ly regs0) (only parsing).
Local Abbreviation tr := ((AR2 (@YF4q.tr)) ch).
Local Abbreviation AR0 f := (f n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz) (only parsing).
Local Abbreviation XW := (AR0 (AR2 (@YF4q.XW))).
Local Abbreviation E0 := (AR0 (AR2 (@YF4q.E0))).
Local Abbreviation EaT := (AR0 (AR2 (@YF4q.EaT))).
Local Abbreviation EaC := (AR0 (AR2 (@YF4q.EaC))).
Local Abbreviation EaSB := (AR0 (AR2 (@YF4q.EaSB))).
Local Abbreviation EaTOP := (AR0 (AR2 (@YF4q.EaTOP))).
Local Abbreviation Er := (AR0 (AR2 (@YF4q.Er))).
Local Abbreviation E2 := (AR0 (AR2 (@YF4q.E2))).
Local Abbreviation E1 := (AR0 (AR2 (@YF4q.E1))).
Local Abbreviation E8 := (AR0 (AR2 (@YF4q.E8))).
Local Abbreviation E10 := (AR0 (AR2 (@YF4q.E10))).
Local Abbreviation E4 := (AR0 (AR2 (@YF4q.E4))).
Local Abbreviation EaP := (AR0 (AR2 (@YF4q.EaP))).
Local Abbreviation EaK := (AR0 (AR2 (@YF4q.EaK))).
Local Abbreviation EaSK := (AR0 (AR2 (@YF4q.EaSK))).
Local Abbreviation EaSSLOT := (AR0 (AR2 (@YF4q.EaSSLOT))).
Local Abbreviation EaPB := (AR0 (AR2 (@YF4q.EaPB))).
Local Abbreviation EaPV := (AR0 (AR2 (@YF4q.EaPV))).
Local Abbreviation EaKL := (AR0 (AR2 (@YF4q.EaKL))).
Local Abbreviation EaRZ := (AR0 (AR2 (@YF4q.EaRZ))).
Local Abbreviation EaU := (AR0 (AR2 (@YF4q.EaU))).
Local Abbreviation EaSU := (AR0 (AR2 (@YF4q.EaSU))).
Local Abbreviation EaFIL := (AR0 (AR2 (@YF4q.EaFIL))).
Local Abbreviation EaND := (AR0 (AR2 (@YF4q.EaND))).
Local Abbreviation WINT := (@YF4q.WINT ly cl).
Local Abbreviation PBW := (AR6 (@YF4q.PBW ly)).
Local Abbreviation WIN := (AR6 (@YF4q.WIN ly regs0)).
Local Abbreviation win_in_WIN := (AR6 (@YF4q.win_in_WIN ly regs0)).
Hypotheses (Hcl : 1 <= cl <= 31) (Hv : 0 <= v /\ 16 * v + 2 ^ 16 <= 2 ^ 32) (Hcnt : 1 <= cnt <= 16) (Hjb : 0 <= jb <= 255).
Hypothesis Hv2 : v mod 2 = 0.
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
Local Abbreviation HCdisj := (@YF4q.HCdisj _ ly regs0 v Hv LY).
Local Abbreviation DZONE := (@YF4q.DZONE imgk ly).
Variable DPOST : Z -> (word -> option byte) -> Prop.
Local Abbreviation HC_NB := (@YF4q.HC_NB _ ly LY).
Hypothesis HKpres : forall a, Kv <= a < Kv + RZ + R8v -> apresent (w_H W) mem0 a.
Hypothesis HSKpres : forall a, SKv <= a < SKv + (RZ + R8v) / 8 -> apresent (w_H W) mem0 a.
Hypothesis HPB250 : n mod 8 <> 0 -> val_mem tfxsegs (mrestrict (w_H W) mem0) PBv 1 250.
Local Abbreviation HCX := (@YF4q.HCX _ ly LY).
Local Abbreviation tr_length := ((AR2 (@YF4q.tr_length)) mem0 n ch v kz DPOST).
Local Abbreviation AR5 f := (f ly regs0 mem0) (only parsing).
Local Abbreviation Kv_range := ((AR6 (AR5 (@YF4q.Kv_range))) Hcl Hv Hv2 DPOST).
Local Abbreviation AR7 f := (AR2 f mem0 n v kz Hv LY IMG DPOST) (only parsing).
Local Abbreviation high_facts := (AR7 (@YF4q.high_facts _)).
Local Abbreviation blocks_facts := (@YF4q.blocks_facts _ imgk ly LY IMG).
Local Abbreviation off_T := (AR7 (@YF4q.off_T _)).
Local Abbreviation off_C := (AR7 (@YF4q.off_C _)).
Local Abbreviation off_NB := (@YF4q.off_NB _ imgk ly LY IMG).
Local Abbreviation off_SB := (@YF4q.off_SB _ imgk ly LY IMG).
Ltac off_by tac :=
first [ img_apply off_img_high; tac
| img_apply off_T; unfold kThreadObjSize; tac
| img_apply off_C; tac
| img_apply off_NB; unfold kNodesBlockSize; tac
| img_apply off_SB; unfold kStoreBlockSize; tac
| unfold off_img; unfold TFX_IMG_LO; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; tac ].
Hypothesis Hkz : 1 <= kz <= 6.
Hypothesis Nrange : rz_lo kz <= n <= rz_hi kz.
Local Abbreviation kz_cases := (@YF4q.kz_cases kz Hkz).
Local Abbreviation RZ_facts := (@YF4q.RZ_facts n kz Hkz Nrange).
Local Abbreviation RZ_num := (@YF4q.RZ_num n kz Hkz Nrange).
Ltac numconst ::= (ceil; unfold zone3, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize,
t_cache, t_unwinding, t_stats, ASTACK, TFX_IMG_END, TFX_IMG_LO, kLowShadowBeg, UNW_STK, BST_SIZE, DEP_STK in * ); try pose proof RZ_num as RZN.
Local Abbreviation AR3 f := (f Hcl Hv Hcnt Hv2 LY IMG DPOST Hkz Nrange) (only parsing).
Local Abbreviation derived_ranges := (AR3 ((AR2 (@YF4q.derived_ranges _)) mem0 n cl cnt v kz)).
Hypothesis Hcl_def : cl = class_id (R8v + RZ).
Local Abbreviation NDv_facts := ((AR5 (@YF4q.NDv_facts)) n v kz DPOST Hkz Nrange).
Local Abbreviation CL_hi_E := ((AR0 ((AR2 (@YF4q.CL_hi_E)) mem0)) DPOST Hkz Nrange Hcl_def).
Local Abbreviation CL_lo_E := ((AR0 ((AR2 (@YF4q.CL_lo_E)) mem0)) DPOST Hkz Nrange Hcl_def).
Local Abbreviation WIN1 := (AR6 (@YF4q.WIN1 ly regs0)).
Local Abbreviation WIN1_WIN := ((AR6 (AR5 (@YF4q.WIN1_WIN))) DPOST).
Local Abbreviation AR4 f := (f n cl cnt v jb kz Hcl Hv Hcnt Hjb Hsp DPOST Hkz Nrange) (only parsing).
Local Abbreviation WIN_odd := (AR4 (AR5 (@YF4q.WIN_odd))).
Local Abbreviation WIN1_odd := (AR4 (AR5 (@YF4q.WIN1_odd))).
Local Abbreviation WSKEL := (@YF4q.WSKEL).
Local Abbreviation WSKEL1 := (@YF4q.WSKEL1).
Local Abbreviation win_sub := (@YF4q.win_sub).
Local Abbreviation win_sub_sound := ((AR5 (@YF4q.win_sub_sound)) n v kz Hv DPOST).
Local Abbreviation WSKEL_WIN := (AR3 (AR0 ((AR2 (@YF4q.WSKEL_WIN _)) mem0))).
Local Abbreviation WSKEL1_WIN1 := (AR3 (AR0 ((AR2 (@YF4q.WSKEL1_WIN1 _)) mem0))).
Local Abbreviation windows_WIN := (AR3 (AR0 ((AR2 (@YF4q.windows_WIN _)) mem0))).
Local Abbreviation windows_WIN1 := (AR3 (AR0 ((AR2 (@YF4q.windows_WIN1 _)) mem0))).
Local Abbreviation frame_WIN1 := (AR3 (AR0 ((AR2 (@YF4q.frame_WIN1 _)) mem0))).
Local Abbreviation AR1 f := (f _ imgk ly regs0 mem0 n cl cnt v kz Hcl Hv Hcnt Hv2 LY IMG Hsp DPOST Hkz Nrange) (only parsing).
Local Abbreviation WIN_not_high := (AR1 (@YF4q.WIN_not_high)).
Variables (mat0 : list word).
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 (0x53104 + D_2c4)) mem0 (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis U1 : tfx_unwind_spec.
Hypothesis SEED : st_ok tfxsegs E0 SS0 (restrict (w_H W) (mkst regs0 (w64 (0x53104 + D_2c4)) mem0 (seg_rom tfxsegs))).
Local Abbreviation all_disjoint_of_forall := (@YF4q.all_disjoint_of_forall).
Local Abbreviation kept_of_frame := ((AR5 (@YF4q.kept_of_frame imgk W)) n v kz DPOST).
Local Abbreviation SKEL_TAIL := (@YF4q.SKEL_TAIL imgk).
Local Abbreviation stack_ivs := ((AR5 (@YF4q.stack_ivs _)) n v kz Hv LY Hsp DPOST).
Local Abbreviation stack_ivs2 := ((AR5 (@YF4q.stack_ivs2 _)) n v kz Hv LY Hsp DPOST).
Local Abbreviation DZONE_disj := (AR1 (@YF4q.DZONE_disj)).
Local Abbreviation RFACTS := (AR6 (AR2 (@YF4q.RFACTS))).
Local Abbreviation zone_lit := (AR1 (@YF4q.zone_lit)).
Local Abbreviation zone_T := (AR1 (@YF4q.zone_T)).
Local Abbreviation zone_C := (AR1 (@YF4q.zone_C)).
Local Abbreviation zone_K := (AR1 (@YF4q.zone_K)).
Local Abbreviation zone_SH := (AR1 (@YF4q.zone_SH)).
Local Abbreviation tail_ext_ok := ((AR0 ((AR2 (@YF4q.tail_ext_ok _)) mem0)) Hcl Hv Hcnt Hv2 LY IMG Hsp DPOST Hkz Nrange).
Local Abbreviation at_ST := (AR0 ((AR5 (@YF4q.at_ST _ imgk W)) md0)).
Local Abbreviation at_ST2 := ((AR0 ((AR5 (@YF4q.at_ST2 _ imgk W)) md0)) DPOST).
Local Abbreviation at_S2 := ((AR0 ((AR5 (@YF4q.at_S2 _ imgk W)) md0)) DPOST).
Local Abbreviation at_RET := ((AR5 (@YF4q.at_RET _ imgk W)) md0 n cl cnt v jb kz DPOST).
Ltac frame_acc HE :=
match goal with
| MEQ : (forall x : word, ~ WIN1 ?odd (bv_unsigned x) -> ?m1 x = ?mb x), HFx : frame_of ?E ?rs ?m1 ?m2 |- _ =>
let MEQ' := fresh "MEQ" in
assert (MEQ' : forall x : word, ~ WIN1 odd (bv_unsigned x) -> m2 x = mb x)
by (img_try (intros x Hx; transitivity (m1 x); [img_try (img_exact (frame_WIN1 odd E rs m1 m2 HE ltac:((img_case; vm_compute); img_refl) HFx x Hx)) | img_try (img_exact (MEQ x Hx))]));
clear MEQ HFx; rename MEQ' into MEQ
end.
Local Abbreviation memset_stretch := ((AR4 ((AR5 (@YF4q.memset_stretch _ imgk W)) md0)) mat0).
Variables (B : asyms) (S : astate) (l : list Z) (off : Z).
Hypothesis TS : TfxSyms B.
Hypothesis HTSD : ly_tsd ly = TFX_TSD.
Hypothesis HARm : ARm B ly S (aview tfxsegs (w_H W) mem0).
Hypothesis Hgp : getr regs0 3 = w64 (as_gp B).
Hypothesis Hpres0 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem0 a.
Hypothesis Hinited : st_cache_inited S = true.
Hypothesis Hcache : pc_chunks (cache S cl) = l ++ [off].
Hypothesis Hcl_class : cl = chunk_class n.
Hypothesis Hcnt_def : cnt = Z.of_nat (length (l ++ [off])).
Hypothesis Hoff_def : off = 16 * v.
Hypothesis Hcsz_def : csz = class_size cl.
Hypothesis Hj0 : val_mem tfxsegs (mrestrict (w_H W) mem0) (T + 2784) 8 j0.
Hypothesis Hj1 : val_mem tfxsegs (mrestrict (w_H W) mem0) (T + 2800) 8 j1.
Hypothesis Hj2 : val_mem tfxsegs (mrestrict (w_H W) mem0) (T + 2808) 8 j2.
Hypothesis Hj3 : val_mem tfxsegs (mrestrict (w_H W) mem0) (T + 2816) 8 j3.
Hypothesis Hj4 : val_mem tfxsegs (mrestrict (w_H W) mem0) SSLOTv 8 j4.
Hypothesis Hjb_def : val_mem tfxsegs (mrestrict (w_H W) mem0) (Kv + RZ - 15) 1 jb.
Hypothesis HQT : qtight S.
Local Abbreviation casek_sizes := (@YF4q.casek_sizes n kz Hkz Nrange).
Local Abbreviation Kv_is_sptr := (@YF4q.Kv_is_sptr ly cl v Hcl B off Hoff_def).
Local Ltac addr_tac :=
cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi];
rewrite ?EaT, ?EaC, ?EaTOP, ?EaSB, ?E2; ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, w64, ly_bot, kStackSpan, t_unwinding, t_cache, t_stats, TFX_IMG_END, UNW_STK, BST_SIZE, ASTACK, IFRAME, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *;
rewrite ?unsigned_lit_small by zlia; zlia.
Local Ltac denot_tac :=
cbn [sv_denot]; rewrite ?EaT, ?EaC, ?EaTOP, ?EaSB, ?E2; unfold w64, ly_bot, kStackSpan in *;
first [ rewrite Z.add_0_r, Z_to_bv_bv_unsigned; img_refl
| rewrite Zbv_add_unsigned; f_equal; zlia
| rewrite unsigned_lit_small by zlia; f_equal; zlia
| img_refl ].
Hypothesis SEEDM : st_ok tfxsegs E0 MS0 (restrict (w_H W) (mkst regs0 (w64 (0x53104 + D_2c4)) mem0 (seg_rom tfxsegs))).
Definition WINM (a : Z) : Prop := (sp0 - ASTACK <= a < sp0) \/ (T + t_unwinding <= a < T + t_unwinding + 1).
Definition WINM1 (a : Z) : Prop :=
(sp0 - ASTACK <= a < sp0 - IFRAME) \/ (sp0 - 64 <= a < sp0) \/ (T + t_unwinding <= a < T + t_unwinding + 1).
Lemma WINM1_WINM : forall a, WINM1 a -> WINM a.
Proof. intros a H. unfold WINM1, WINM, IFRAME, ASTACK in *. zlia. Qed.

Definition WSKELM : list (option nat * Z * Z) := [(Some 2%nat, - ASTACK, 0); (Some 32%nat, t_unwinding, t_unwinding + 1)].
Definition WSKELM1 : list (option nat * Z * Z) := [(Some 2%nat, - ASTACK, - IFRAME); (Some 2%nat, -64, 0); (Some 32%nat, t_unwinding, t_unwinding + 1)].
Lemma WSKELM_WINM : forall (E : env) a t,
(forall k, (k < aHAV)%nat -> ew E k = ew E0 k) -> In t WSKELM ->
base_val E (fst (fst t)) + snd (fst t) <= a < base_val E (fst (fst t)) + snd t -> WINM a.
Proof.
intros E a t HE Hin Hr. pose proof derived_ranges as DR. pose proof high_facts as HF'.
unfold WSKELM in Hin. cbn [In] in Hin. unfold WINM.
ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, t_cache, t_unwinding, kThreadObjSize, aHAV in *.
repeat match type of Hin with _ \/ _ => destruct Hin as [<-|Hin] | False => destruct Hin end;
cbn [fst snd base_val] in Hr; rewrite HE in Hr by zlia; rewrite ?E2, ?EaT in Hr; unfold w64 in Hr; rewrite ?unsigned_lit_small in Hr by zlia;
unfold sp0 in *; zlia.
Qed.
Lemma WSKELM1_WINM1 : forall (E : env) a t,
(forall k, (k < aHAV)%nat -> ew E k = ew E0 k) -> In t WSKELM1 ->
base_val E (fst (fst t)) + snd (fst t) <= a < base_val E (fst (fst t)) + snd t -> WINM1 a.
Proof.
intros E a t HE Hin Hr. pose proof derived_ranges as DR. pose proof high_facts as HF'.
unfold WSKELM1 in Hin. cbn [In] in Hin. unfold WINM1.
ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, t_cache, t_unwinding, kThreadObjSize, aHAV, IFRAME in *.
repeat match type of Hin with _ \/ _ => destruct Hin as [<-|Hin] | False => destruct Hin end;
cbn [fst snd base_val] in Hr; rewrite HE in Hr by zlia; rewrite ?E2, ?EaT in Hr; unfold w64 in Hr; rewrite ?unsigned_lit_small in Hr by zlia;
unfold sp0 in *; zlia.
Qed.
Lemma windows_WINM : forall (E : env) rs a,
(forall k, (k < aHAV)%nat -> ew E k = ew E0 k) ->
forallb (fun t => existsb (win_sub t) WSKELM || (snd t <=? snd (fst t))) (windows rs) = true ->
in_wrange E rs a -> WINM a.
Proof.
intros E rs a HE Hb Hw. destruct (in_wrange_windows E rs a Hw) as (b & lo & hi & Hin & Hr).
pose proof (proj1 (forallb_forall _ _) Hb _ Hin) as Ht. cbn beta in Ht. apply Bool.orb_prop in Ht as [Ht|Ht].
- apply existsb_exists in Ht as (u & Hinu & Hsub). img_exact (WSKELM_WINM E a u HE Hinu (win_sub_sound E a _ u Hsub Hr)).
- cbn [fst snd] in Ht. apply Z.leb_le in Ht. zlia.
Qed.
Lemma windows_WINM1 : forall (E : env) rs a,
(forall k, (k < aHAV)%nat -> ew E k = ew E0 k) ->
forallb (fun t => existsb (win_sub t) WSKELM1 || (snd t <=? snd (fst t))) (windows rs) = true ->
in_wrange E rs a -> WINM1 a.
Proof.
intros E rs a HE Hb Hw. destruct (in_wrange_windows E rs a Hw) as (b & lo & hi & Hin & Hr).
pose proof (proj1 (forallb_forall _ _) Hb _ Hin) as Ht. cbn beta in Ht. apply Bool.orb_prop in Ht as [Ht|Ht].
- apply existsb_exists in Ht as (u & Hinu & Hsub). img_exact (WSKELM1_WINM1 E a u HE Hinu (win_sub_sound E a _ u Hsub Hr)).
- cbn [fst snd] in Ht. apply Z.leb_le in Ht. zlia.
Qed.
Lemma frame_WINM1 : forall (E : env) rs (m m' : word -> option byte),
(forall k, (k < aHAV)%nat -> ew E k = ew E0 k) ->
forallb (fun t => existsb (win_sub t) WSKELM1 || (snd t <=? snd (fst t))) (windows rs) = true ->
frame_of E rs m m' -> forall x : word, ~ WINM1 (bv_unsigned x) -> m' x = m x.
Proof. intros E rs m m' HE Hb HF x Hx. img_apply HF. intros Hw. img_apply Hx. img_exact (windows_WINM1 E rs _ HE Hb Hw). Qed.
Definition at_STM (ss : sstate) (W' : world tfxsegs) (c' : config) : Prop :=
W' = W /\ exists ms mat (E' : env),
c' = mkCfg ms (with_vm_backing (m_vm_lazy md0) mat md0) /\
(forall k, (k < aHAV)%nat -> ew E' k = ew E0 k) /\
st_ok tfxsegs E' ss (restrict (w_H W) ms) /\
(forall x : word, ~ WINM (bv_unsigned x) -> ms_mem ms x = mem0 x) /\
(forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) (ms_mem ms) a) /\
(forall i, (i < length tr)%nat -> val_mem tfxsegs (mrestrict (w_H W) (ms_mem ms)) (sp0 - IFRAME + 16 + 8 * Z.of_nat i) 8 (nth i tr 0)).

Ltac frame_accM HE :=
match goal with
| MEQ : (forall x : word, ~ WINM1 (bv_unsigned x) -> ?m1 x = ?mb x), HFx : frame_of ?E ?rs ?m1 ?m2 |- _ =>
let MEQ' := fresh "MEQ" in
assert (MEQ' : forall x : word, ~ WINM1 (bv_unsigned x) -> m2 x = mb x)
by (img_try (intros x Hx; transitivity (m1 x); [img_try (img_exact (frame_WINM1 E rs m1 m2 HE ltac:((img_case; vm_compute); img_refl) HFx x Hx)) | img_try (img_exact (MEQ x Hx))]));
clear MEQ HFx; rename MEQ' into MEQ
end.
Local Ltac close_ST En HEn HS memB MEQ MEQW PRESW BUFW :=
img_apply SRr_ret; split; [img_refl|];
lazymatch goal with |- context [mkCfg ?msf (with_vm_backing _ ?matf _)] => exists msf, matf, En end;
split; [img_refl|]; split; [img_try (img_exact HEn)|]; split; [img_try (img_exact HS)|];
pose proof derived_ranges as DR'; pose proof high_facts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9); pose proof Kv_range as HKR;
pose proof (lo_top ly LY) as (T1' & T2' & T3' & T4' & T5' & T6' & T7'); pose proof Hsp as (Hlo_ & Hbot_ & Hhi_ & Hal_);
split; [|img_try (split)];
[ img_try (intros x Hx; rewrite (MEQ x) by (intros H1; apply Hx, WINM1_WINM, H1); apply MEQW, Hx)
| img_try (intros a Ha; destruct (Z_lt_le_dec a (sp0 - IFRAME)) as [Hlo'|Hge];
[ eapply (st_ok_window_apresent_off (w_H W) En _ _ 1 _ a HS); [img_refl | cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite (HEn 2%nat (ltHAV 2 eq_refl)), E2; addr_tac | off_by ltac:(addr_tac) ]
| destruct (Z_lt_le_dec a (sp0 - 64)) as [Hmid|Htop'];
[ img_apply (apresent_same (w_H W) memB);
[ img_apply MEQ; assert (Hx : ly_stk_lo ly <= a < ly_stk_hi ly) by (clear - Hge Hmid Hlo_ Hhi_; unfold IFRAME, ASTACK in *; zlia);
destruct (F9 a Hx) as [N1 N2]; pose proof (HCdisj a Hx) as HC;
clear - Hge Hmid DR' HKR N1 N2 HC T7' T4' Hlo_ Hhi_ F1 F2 F3 F4 F5 F6 F7 F8;
unfold WINM1, IFRAME in *; numconst; rewrite unsigned_lit_small by zlia; zlia
| img_apply PRESW; unfold IFRAME in *; zlia ]
| eapply (st_ok_window_apresent_off (w_H W) En _ _ 2 _ a HS); [img_refl | cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite (HEn 2%nat (ltHAV 2 eq_refl)), E2; addr_tac | off_by ltac:(addr_tac) ] ] ])
| img_try (intros i Hi; pose proof tr_length as LEN;
eapply val_mem_frame; [|eapply val_mem_addr; [img_exact (BUFW i Hi) | clear - Hi LEN Hlo_ Hhi_ T4' T7'; addr_tac]];
intros k Hk; img_apply MEQ;
assert (Hx : ly_stk_lo ly <= sp0 - IFRAME + 16 + 8 * Z.of_nat i + Z.of_nat k < ly_stk_hi ly) by (clear - Hi Hk LEN Hlo_ Hhi_; unfold IFRAME, ASTACK in *; zlia);
destruct (F9 _ Hx) as [N1 N2]; pose proof (HCdisj _ Hx) as HC;
clear - Hi Hk LEN DR' HKR N1 N2 HC T7' T4' Hlo_ Hhi_ F1 F2 F3 F4 F5 F6 F7 F8;
unfold WINM1, IFRAME in *; numconst; rewrite unsigned_lit_small by zlia; zlia) ].
Definition SKEL_TAILM {imgk : img} : list (option nat * Z * Z * Z * Z) := skeleton (tl MREG0).
Lemma tail_ext_okM : forall (E : env) r,
(forall k, (k < aHAV)%nat -> ew E k = ew E0 k) -> In (skel r) SKEL_TAILM ->
let b := base_val E (YQ0b.r_base r) in
(b + YQ0b.r_hi r <= sp0 - ASTACK \/ sp0 <= b + YQ0b.r_lo r) /\ 0 <= b + YQ0b.r_lo r /\ b + YQ0b.r_hi r <= 2 ^ 64 /\
(YQ0b.r_whi r <= YQ0b.r_wlo r \/ (TFX_IMG_END <= b + YQ0b.r_wlo r /\ b + YQ0b.r_whi r <= 2 ^ 64) \/ (0 <= b + YQ0b.r_wlo r /\ b + YQ0b.r_whi r <= TFX_IMG_LO)) /\
((b + YQ0b.r_hi r <= (0x17c088 + D_10c0) \/ (0x5cc810 + D_10c0) <= b + YQ0b.r_lo r) /\
(b + YQ0b.r_hi r <= ly_NB ly \/ ly_NB ly + kNodesBlockSize <= b + YQ0b.r_lo r) /\
(b + YQ0b.r_hi r <= ly_SB ly \/ ly_SB ly + kStoreBlockSize <= b + YQ0b.r_lo r)) /\
((b + YQ0b.r_hi r <= SUv \/ PBv <= b + YQ0b.r_lo r) /\ (b + YQ0b.r_hi r <= Kv + RZ \/ Kv + RZ + 4096 <= b + YQ0b.r_lo r) /\
(b + YQ0b.r_hi r <= PBv \/ PBv + 1 <= b + YQ0b.r_lo r)).
Proof.
intros E r HE Hin. pose proof derived_ranges as DR. pose proof high_facts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & _).
destruct r as [bs lo hi wlo whi cs]. unfold skel in Hin. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi].
let sk := img_ev constr:(SKEL_TAILM) in img_change SKEL_TAILM with sk in Hin. cbn [In] in Hin.
repeat match type of Hin with _ \/ _ => destruct Hin as [Hin|Hin]; [img_try (injection Hin as <- <- <- <- <-)|] | False => destruct Hin end.
all: cbn [base_val].
all: rewrite ?HE by (img_try (clear - HE; (img_case; cbv); zlia)); rewrite ?E2, ?EaT, ?EaC, ?EaP, ?EaK, ?EaU, ?EaSK, ?EaSSLOT, ?EaPB, ?EaPV; unfold w64;
rewrite ?unsigned_lit_small by (img_try (clear - DR F1 F2 F3 F4 F5 F6 F7 F8; numconst; try unfold T in *; zlia)).
all: lazymatch goal with |- (?b + ?hi' <= ?s \/ ?s' <= ?b' + ?lo') /\ ?B /\ ?C /\ (?whi' <= ?wlo' \/ ?D) /\ ?R =>
enough (RF : (b + hi' <= s \/ s' <= b' + lo') /\ B /\ C /\ (b + whi' <= b + wlo' \/ D) /\ R) by (img_try (clear - RF; destruct RF as (X1 & X2 & X3 & X4 & X5); refine (conj X1 (conj X2 (conj X3 (conj _ X5)))); clear - X4; unfold TFX_IMG_LO, TFX_IMG_END in *; zlia)) end.
all: first [ img_apply zone_lit; clear - DR; numconst; unfold TFX_TSD, TFX_TP; zlia
| img_apply zone_SH; clear - DR; numconst; zlia
| img_apply zone_K; clear - DR; numconst; zlia
| img_apply zone_T; clear - DR F1 F2; numconst; try unfold T in *; zlia
| img_apply zone_C; clear - DR F7 F8; numconst; zlia
].
Qed.
Local Ltac ladder_close HS HEn1 EnKL :=
srr_run_to_sh tfxtbl_rtA_ok HS (0x31a8c + D_150); frame_accM HEn1;
apply (st_ok_pin_regU _ _ _ 19%bv (SOff aKL 0)) in HS;
[ | img_try (intros X; discriminate)
| img_try (pin_zev; unfold aKL; rewrite (HEn1 57%nat (ltHAV 57 eq_refl)), EaKL; unfold w64; rewrite unsigned_lit_small by zlia; rewrite !zcanon_id by (unfold M64; zlia); zlia) ];
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS;
apply (YQ04.st_ok_prune tfxsegs _ _ _ [] []) in HS;
lazymatch type of HS with st_ok _ _ ?ss _ => replace ss with MS_L in HS by (img_try ((img_case; vm_compute); img_refl)) end.
Lemma missA : SRr tfxsegs W cfg0 (at_STM MS_L).
Proof.
pose proof Hwx_tfa as Hwx. pose proof SEEDM as HS.
pose proof Hsp as (Hlo & Hbot & Hhi & Hal).
pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
srr_run_to_sh tfxtbl_rtA_ok HS (0x5aea0 + D_2c4).
pose proof (st_ok_restrict_mkst tfxsegs (w_H W) E0 _ _ HS eq_refl) as Hshape; cbn [ss_pc] in Hshape.
rewrite Hshape.
eapply SRr_bind.
{ pose proof high_facts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, ASAN_CEIL, kHighMemBeg, kHighMemEnd, kThreadObjSize, kPrimResvSize, kSpaceSize in F1, F2, F3, F4, F5, F6, F7, F8, T1, T2, T4, T7.
assert (U64 : forall r : bv 5, 0 <= bv_unsigned (getr regs0 r) < 2 ^ 64) by (img_try (intros r; img_apply u64_range)).
pose proof (U64 2%bv) as Usp.
rreg HS (2%bv : bv 5) R2. rewrite E2 in R2.
img_apply (U1 W ly (ms_regs ms) (ms_mem ms) _ (sp0 - 2128) (0x533a4 + D_2c4) sp0 (bv_unsigned (getr regs0 1)) (bv_unsigned (getr regs0 8)) ch LY IMG).
1:{ rreg HS (10%bv : bv 5) R10; rewrite R10, E2. unfold sp0. f_equal; zlia. }
1:{ rreg HS (11%bv : bv 5) R11; rewrite R11. img_refl. }
1:{ rreg HS (12%bv : bv 5) R12; rewrite R12, E2. unfold sp0. symmetry. img_apply Z_to_bv_bv_unsigned. }
1:{ rreg HS (13%bv : bv 5) R13; rewrite R13. img_refl. }
1:{ rreg HS (14%bv : bv 5) R14; rewrite R14. img_refl. }
1:{ rreg HS (15%bv : bv 5) R15; rewrite R15. img_refl. }
1:{ rreg HS (4%bv : bv 5) R4; rewrite R4. img_refl. }
1:{ rreg HS (1%bv : bv 5) R1; rewrite R1. img_apply ret_ok_even. img_refl. }
1:{ zlia. }
1:{ memv HS 1%nat 0%nat; [img_refl | img_refl | img_try (zlia)]. }
1:{ memv HS 6%nat 0%nat; [img_refl | img_refl | img_try (zlia)]. }
1:{ memv HS 7%nat 0%nat; [img_refl | img_refl | img_try (zlia)]. }
1:{ memv HS 34%nat 0%nat; [img_refl | img_refl | img_try (unfold TFX_TSD; zlia)]. }
1:{ memv HS 35%nat 0%nat; [img_refl | img_try (denot_tac) | img_try (zlia)]. }
1:{ memv HS 36%nat 1%nat; [img_try (addr_tac) | img_try (denot_tac) | img_try (zlia)]. }
1:{ memv HS 37%nat 3%nat; [img_try (addr_tac) | img_try (denot_tac) | img_try (zlia)]. }
1:{ memv HS 37%nat 1%nat; [img_try (addr_tac) | img_try (denot_tac) | img_try (zlia)]. }
1:{ memv HS 37%nat 2%nat; [img_try (addr_tac) | img_try (denot_tac) | img_try (zlia)]. }
1:{ memv HS 39%nat 0%nat; [img_try (addr_tac) | img_try (denot_tac) | img_try (zlia)]. }
1:{ eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 39 _ _ HS); [img_refl | img_try (addr_tac) | img_try (off_by ltac:(addr_tac)) ]. }
1:{ memv HS 21%nat 0%nat; [img_refl | img_refl | img_try (zlia)]. }
1:{ memv HS 22%nat 0%nat; [img_refl | img_refl | img_try (zlia)]. }
1:{ rewrite R2. rewrite unsigned_lit_small by addr_tac.
replace (bv_unsigned (getr regs0 2) + -2128) with (bv_unsigned (getr regs0 2) + (-133) * 16) by zlia.
rewrite Z_mod_plus_full. img_exact Hal. }
1:{ rewrite R2. rewrite unsigned_lit_small by addr_tac. addr_tac. }
1:{ intros a Ha. rewrite R2 in Ha. rewrite unsigned_lit_small in Ha by addr_tac.
eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 0 _ a HS); [img_refl | img_try (addr_tac) | img_try (off_by ltac:(addr_tac)) ]. }
1:{ unfold sp0. replace (bv_unsigned (getr regs0 2) - 2128) with (bv_unsigned (getr regs0 2) + (- 266) * 8) by zlia.
rewrite Z_mod_plus_full. img_apply (Znumtheory.Zdivide_mod). img_apply (Z.divide_trans _ 16); [img_try (exists 2; img_refl)|].
img_apply Znumtheory.Zmod_divide; [img_try (zlia) | img_try (img_exact Hal)]. }
1:{ addr_tac. }
1:{ right. rewrite R2. rewrite unsigned_lit_small by addr_tac. addr_tac. }
1:{ intros a Ha. eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 0 _ a HS); [img_refl | img_try (addr_tac) | img_try (off_by ltac:(addr_tac)) ]. }
1:{ addr_tac. }
1:{ rewrite R2. rewrite unsigned_lit_small by addr_tac. addr_tac. }
1:{ img_exact Hbot. }
1:{ img_exact Hhi. }
1:{ unfold sp0. img_apply (Znumtheory.Zdivide_mod). img_apply (Z.divide_trans _ 16); [img_try (exists 2; img_refl)|].
img_apply Znumtheory.Zmod_divide; [img_try (zlia) | img_try (img_exact Hal)]. }
1:{ img_apply val_mem_rdword; [img_try (img_apply u64_range)|]. memv HS 0%nat 11%nat;
[img_try (addr_tac) | img_try (cbn [sv_denot]; rewrite E1, Z.add_0_r; img_refl) | img_try (img_apply u64_range)]. }
1:{ img_apply val_mem_rdword; [img_try (img_apply u64_range)|]. memv HS 0%nat 10%nat;
[img_try (addr_tac) | img_try (cbn [sv_denot]; rewrite E8, Z.add_0_r; img_refl) | img_try (img_apply u64_range)]. }
1:{ img_exact Hra4096. }
destruct (sp0 + 16 <? ly_top ly) eqn:Hf0; [|img_try (img_exact Hch)].
destruct (bad_next sp0 (ly_top ly) (bv_unsigned (getr regs0 8))) eqn:Hb; [img_try (img_exact Hch)|].
destruct Hch as [H16 Hch']. split; [img_try (img_exact H16)|].
unfold bad_next in Hb. apply Bool.orb_false_iff in Hb as [Hb _]. apply Bool.orb_false_iff in Hb as [Hb1 Hb2].
apply Z.leb_gt in Hb1. apply Z.leb_gt in Hb2. apply Z.ltb_lt in Hf0.
eapply fpchain_ext2; [img_try (img_exact Hch') | img_try (zlia) |].
intros a va Ha1 Ha2 Hva. eapply rdword_ext; [|img_try (img_exact Hva)]. intros i Hi. img_apply aview_same.
img_apply (HF (Z_to_bv 64 (a + i))). intros Hw. rewrite unsigned_lit_small in Hw by zlia.
refine (WIN_not_high false (a + i) _ (windows_WIN false E0 (ss_mem MS0) (a + i) (fun k _ => eq_refl) _ Hw)); [img_try (zlia) | img_try ((img_case; vm_compute); img_refl)]. }
intros W' c' Hle (-> & regs1 & mem1 & mat1 & -> & HP & Hfr & Hpr & Ht1 & Ht2 & Ht3). srr_norm_model.
rreg HS (2%bv : bv 5) R2. rewrite E2 in R2. rreg HS (1%bv : bv 5) R1.
assert (Usp : 0 <= bv_unsigned (getr regs0 2) < 2 ^ 64) by img_apply u64_range.
assert (Hfr' : forall x : word, ~ (sp0 - ASTACK <= bv_unsigned x < sp0) -> mem1 x = ms_mem ms x).
{ intros x Hx. rewrite R2 in Hfr. unfold UNW_STK, BST_SIZE in Hfr. rewrite unsigned_lit_small in Hfr by addr_tac.
img_apply Hfr; unfold sp0, ASTACK in *; zlia. }
jafter_call2 HS 64%nat regs1 (mrestrict (w_H W) mem1) HP (-64) (seq 0 48) HS1.
assert (Hfr'' : forall x : word, ~ (sp0 - ASTACK <= bv_unsigned x < sp0 - 64) -> mem1 x = ms_mem ms x).
{ intros x Hx. rewrite R2 in Hfr. unfold UNW_STK, BST_SIZE in Hfr. rewrite unsigned_lit_small in Hfr by addr_tac.
img_apply Hfr; unfold sp0, ASTACK in *; zlia. }
cbn [ms_mem restrict] in HS1.
lazymatch type of HS1 with Forall _ (?r0 :: ?tail) -> _ =>
assert (KEPT : Forall (region_kept tfxsegs E0 (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) mem1)) (r0 :: tail));
[ img_try (constructor;
[ eapply (kept_of_frame E0 _ _ (fun a => sp0 - ASTACK <= a < sp0 - 64) _ Hfr'' Hpr); cbn [base_val YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi];
rewrite E2; unfold zone3, TFX_IMG_LO, kLowShadowBeg, sp0, ASTACK, TFX_IMG_END, kHighMemBeg, kHighMemEnd in *; intros a Ha; cbn beta; zlia
| img_apply Forall_forall; intros r Hr;
apply (in_map skel) in Hr; replace (map skel tail) with SKEL_TAILM in Hr by ((img_case; vm_compute); img_refl);
pose proof (tail_ext_okM E0 r (fun k _ => eq_refl) Hr) as (X1 & X2 & X3 & X4 & X5 & X6);
eapply (kept_of_frame E0 _ _ (fun a => sp0 - ASTACK <= a < sp0) _ Hfr' Hpr); intros a Ha; cbn beta; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END in *; zlia ])
| img_try (specialize (HS1 KEPT); clear KEPT) ]
end.
assert (PRES1 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem1 a).
{ intros a Ha. img_apply Hpr. eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 0 _ a HS); [img_refl | img_try (addr_tac) | img_try (off_by ltac:(addr_tac)) ]. }
set (En1 := havoc E0 64 (map (getr regs1) CLOB)) in HS1.
assert (HEn1 : forall k, (k < aHAV)%nat -> ew En1 k = ew E0 k) by (img_try (intros k Hk; (subst En1; cbv beta); img_apply ew_havoc_old; img_exact Hk)).
apply (st_ok_add_region _ _ _ (YQ0b.mkRegion (Some 2%nat) (- ASTACK) (- IFRAME) (- ASTACK) (- IFRAME) [])) in HS1;
[ | img_refl
| unfold YQ0b.region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem];
rewrite (HEn1 2%nat (ltHAV 2 eq_refl)), E2; unfold IFRAME;
split; [img_try (addr_tac)|]; split; [img_try (addr_tac)|]; split; [img_try (intros o Ho; img_apply apresent_writable_off; [off_by ltac:(addr_tac) | img_apply PRES1; addr_tac]) | img_try (constructor)]
| img_apply all_disjoint_of_forall; intros r' [<-|Hr'];
[ unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; unfold IFRAME; zlia
| apply (in_map skel) in Hr';
lazymatch type of Hr' with In _ (map skel ?tl) => replace (map skel tl) with SKEL_TAILM in Hr' by (img_try ((img_case; vm_compute); img_refl)) end;
pose proof (tail_ext_okM En1 r' HEn1 Hr') as (X1 & X2 & X3 & X4 & X5 & X6);
unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; rewrite (HEn1 2%nat (ltHAV 2 eq_refl)), E2;
unfold IFRAME, ASTACK, sp0 in *; zlia ] ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1.
assert (OBJ0 : val_mem tfxsegs (mrestrict (w_H W) mem1) (sp0 - 2128) 8 (sp0 - 2112)).
{ eapply val_mem_frame; [img_try (intros k Hk; img_apply Hfr; rewrite ?R2, ?unsigned_lit_small by addr_tac; addr_tac)|].
memv HS 0%nat 2%nat; [img_try (addr_tac) | img_try (denot_tac) | img_try (addr_tac)]. }
assert (OBJ1 : val_mem tfxsegs (mrestrict (w_H W) mem1) (sp0 - 2120) 8 (Z.of_nat (length tr))).
{ replace (Z.of_nat (length tr)) with (Z.of_nat (length tr) + 2 ^ 32 * 0) by zlia.
pose proof tr_length as LEN.
img_apply val_mem_4_4; [img_try (zlia) | img_try (zlia) | |].
- eapply val_mem_addr; [img_try (img_exact Ht1) | img_try (addr_tac)].
- assert (Z8 : val_mem tfxsegs (mrestrict (w_H W) (ms_mem ms)) (sp0 - 2120) 8 0) by (img_try (memv HS 0%nat 1%nat; [img_try (addr_tac) | img_refl | img_try (zlia)])).
assert (Z4 : val_mem tfxsegs (mrestrict (w_H W) (ms_mem ms)) (sp0 - 2120 + 4) 4 0).
{ intros k Hk. replace (sp0 - 2120 + 4 + Z.of_nat k) with (sp0 - 2120 + Z.of_nat (4 + k)) by zlia.
rewrite (Z8 (4 + k)%nat ltac:(img_try (zlia))). rewrite !le_byte_zero. img_refl. }
eapply val_mem_frame; [img_try (intros k Hk; img_apply Hfr; rewrite ?R2, ?unsigned_lit_small by addr_tac; addr_tac)| img_try (img_exact Z4)]. }
apply (st_ok_add_region _ _ _ (YQ0b.mkRegion (Some 2%nat) (- 2128) (- 2112) 0 0
[YQ0b.mkChunk (- 2128) (CVal 8 (SOff 2 (- 2112))); YQ0b.mkChunk (- 2120) (CVal 8 (SOff aLEN 0))])) in HS1;
[ | img_refl
| unfold YQ0b.region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem];
rewrite (HEn1 2%nat (ltHAV 2 eq_refl)), E2;
split; [img_try (addr_tac)|]; split; [img_try (addr_tac)|]; split; [img_try (intros o Ho; zlia) |];
img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_nil])];
[ img_try (eapply (chunk_ok_val tfxsegs En1 _ _ (-2128) 8 (SOff 2 (-2112)) (sp0 - 2112));
[cbn [sv_denot]; rewrite (HEn1 2%nat (ltHAV 2 eq_refl)), E2; denot_tac | addr_tac | cbn; zlia | eapply val_mem_addr; [img_exact OBJ0 | addr_tac]])
| img_try (eapply (chunk_ok_val tfxsegs En1 _ _ (-2120) 8 (SOff aLEN 0) (Z.of_nat (length tr)));
[cbn [sv_denot]; rewrite (HEn1 aLEN (ltHAV aLEN eq_refl)); unfold aLEN; rewrite (eq_refl : ew E0 36 = w64 (Z.of_nat (length tr))); denot_tac
| pose proof tr_length; img_change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); zlia
| cbn; zlia | eapply val_mem_addr; [img_exact OBJ1 | addr_tac]]) ]
| img_apply all_disjoint_of_forall; intros r' [<-|[<-|Hr']];
[ unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; unfold IFRAME, ASTACK; zlia
| unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; zlia
| apply (in_map skel) in Hr';
lazymatch type of Hr' with In _ (map skel ?tl) => replace (map skel tl) with SKEL_TAILM in Hr' by (img_try ((img_case; vm_compute); img_refl)) end;
pose proof (tail_ext_okM En1 r' HEn1 Hr') as (X1 & X2 & X3 & X4 & X5 & X6);
unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; rewrite (HEn1 2%nat (ltHAV 2 eq_refl)), E2;
unfold IFRAME, ASTACK, sp0 in *; zlia ] ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1.
rewrite <- (restrict_mkst_fx (w_H W)) in HS1. rewrite R1. clear HS. rename HS1 into HS.
assert (MEQ : forall x : word, ~ WINM1 (bv_unsigned x) -> mem1 x = mem1 x) by (img_try (intros; img_refl)).
assert (MEQ0 : forall x : word, ~ WINM (bv_unsigned x) -> mem1 x = mem0 x).
{ intros x Hx. rewrite Hfr' by (img_try (unfold WINM in Hx; tauto)). img_apply HF. intros Hw. img_apply Hx.
img_exact (windows_WINM E0 (ss_mem MS0) _ (fun k _ => eq_refl) ltac:(img_try ((img_case; vm_compute); img_refl)) Hw). }
clear HF HFr Hfr Hfr' Hfr''.
rename MEQ0 into MEQW. rename PRES1 into PRESW. rename Ht2 into BUFW.
srr_run_sh tfxtbl_rtA_ok HS. frame_accM HEn1.
pose proof RZ_facts as (_ & _ & _ & _ & _ & NR). pose proof kz_cases as KC.
assert (En10 : U En1 (SOff 10 0) = n).
{ clear - HEn1 Hn NR KC. rewrite U_zev by img_refl. cbn [zev]. unfold rho_of. rewrite (HEn1 10%nat (ltHAV 10 eq_refl)), E10, Hn. unfold w64.
rewrite unsigned_lit_small by (img_try (destruct KC as [->|[->|[->|[->|[->| ->]]]]]; cbn in NR; zlia)). rewrite Z.add_0_r. img_apply zcanon_id. unfold M64.
destruct KC as [->|[->|[->|[->|[->| ->]]]]]; cbn in NR; zlia. }
assert (EnKL : U En1 (SOff aKL 0) = kz).
{ clear - HEn1 Hkz. rewrite U_zev by img_refl. cbn [zev]. unfold rho_of, aKL. rewrite (HEn1 57%nat (ltHAV 57 eq_refl)), EaKL. unfold w64.
rewrite unsigned_lit_small by zlia. rewrite Z.add_0_r. img_apply zcanon_id. unfold M64. zlia. }
srr_branch_sh tfxtbl_rtA_ok HS.
2:{   rewrite branch_geu_U, En10, U_lit in Hc by zlia.
assert (K1 : kz = 1) by (img_try (clear - Hc NR KC; apply Bool.negb_false_iff in Hc; apply Z.ltb_lt in Hc;
destruct KC as [->|[->|[->|[->|[->| ->]]]]]; cbn in NR; zlia)).
ladder_close HS HEn1 EnKL. close_ST En1 HEn1 HS mem1 MEQ MEQW PRESW BUFW. }
rewrite branch_geu_U, En10, (U_lit En1 97) in Hc by zlia. apply Bool.negb_true_iff in Hc. apply Z.ltb_ge in Hc. rename Hc into Hc1.
srr_run_sh tfxtbl_rtA_ok HS. frame_accM HEn1.
srr_branch_sh tfxtbl_rtA_ok HS.
2:{ rewrite branch_geu_U, En10, (U_lit En1 449) in Hc by zlia.
assert (K2 : kz = 2) by (img_try (clear - Hc Hc1 NR KC; apply Bool.negb_false_iff in Hc; apply Z.ltb_lt in Hc; destruct KC as [->|[->|[->|[->|[->| ->]]]]]; cbn in NR; zlia)).
ladder_close HS HEn1 EnKL. close_ST En1 HEn1 HS mem1 MEQ MEQW PRESW BUFW. }
rewrite branch_geu_U, En10, (U_lit En1 449) in Hc by zlia. apply Bool.negb_true_iff in Hc. apply Z.ltb_ge in Hc. rename Hc into Hc2.
srr_run_sh tfxtbl_rtA_ok HS. frame_accM HEn1.
srr_branch_sh tfxtbl_rtA_ok HS.
2:{ rewrite branch_geu_U, En10, (U_lit En1 3969) in Hc by zlia.
assert (K3 : kz = 3) by (img_try (clear - Hc Hc2 NR KC; apply Bool.negb_false_iff in Hc; apply Z.ltb_lt in Hc; destruct KC as [->|[->|[->|[->|[->| ->]]]]]; cbn in NR; zlia)).
ladder_close HS HEn1 EnKL. close_ST En1 HEn1 HS mem1 MEQ MEQW PRESW BUFW. }
rewrite branch_geu_U, En10, (U_lit En1 3969) in Hc by zlia. apply Bool.negb_true_iff in Hc. apply Z.ltb_ge in Hc. rename Hc into Hc3.
srr_run_sh tfxtbl_rtA_ok HS. frame_accM HEn1.
srr_branch_sh tfxtbl_rtA_ok HS.
2:{ rewrite branch_geu_U, En10, (U_lit En1 16129) in Hc by zlia.
assert (K4 : kz = 4) by (img_try (clear - Hc Hc3 NR KC; apply Bool.negb_false_iff in Hc; apply Z.ltb_lt in Hc; destruct KC as [->|[->|[->|[->|[->| ->]]]]]; cbn in NR; zlia)).
ladder_close HS HEn1 EnKL. close_ST En1 HEn1 HS mem1 MEQ MEQW PRESW BUFW. }
rewrite branch_geu_U, En10, (U_lit En1 16129) in Hc by zlia. apply Bool.negb_true_iff in Hc. apply Z.ltb_ge in Hc. rename Hc into Hc4.
srr_run_sh tfxtbl_rtA_ok HS. frame_accM HEn1.
srr_branch_sh tfxtbl_rtA_ok HS.
2:{ rewrite branch_geu_U, En10, (U_lit En1 32257) in Hc by zlia.
assert (K5 : kz = 5) by (img_try (clear - Hc Hc4 NR KC; apply Bool.negb_false_iff in Hc; apply Z.ltb_lt in Hc; destruct KC as [->|[->|[->|[->|[->| ->]]]]]; cbn in NR; zlia)).
ladder_close HS HEn1 EnKL. close_ST En1 HEn1 HS mem1 MEQ MEQW PRESW BUFW. }
rewrite branch_geu_U, En10, (U_lit En1 32257) in Hc by zlia. apply Bool.negb_true_iff in Hc. apply Z.ltb_ge in Hc. rename Hc into Hc5.
assert (K6 : kz = 6) by (img_try (clear - Hc5 NR KC; destruct KC as [->|[->|[->|[->|[->| ->]]]]]; cbn in NR; zlia)).
ladder_close HS HEn1 EnKL. close_ST En1 HEn1 HS mem1 MEQ MEQW PRESW BUFW.
Qed.
Local Ltac class_close HS HEn CLV CLT :=
apply (st_ok_pin_regU _ _ _ 8%bv (SOff aCL 0)) in HS;
[ | intros X; discriminate
| lazymatch goal with |- U ?E _ = U _ (sr_get ?sr ?r) => let t := img_ev (sr_get sr r) in img_change (sr_get sr r) with t end;
lazymatch goal with |- U ?E _ = U _ ?t => replace t with CLT by (img_try ((img_case; vm_compute); img_refl)) end;
img_apply U_eq_by_zev; [img_refl | img_try (clear; (img_case; vm_compute); img_refl) |]; rewrite CLV;
cbn [zev]; unfold rho_of, aCL; rewrite (HEn 39%nat (ltHAV 39 eq_refl)), (eq_refl : ew E0 39 = w64 cl); unfold w64;
rewrite unsigned_lit_small by zlia; rewrite Z.add_0_r; img_apply zcanon_id; unfold M64; zlia ];
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS;
forget_regs HS 80%nat ([5; 6; 12; 14; 15; 16; 17]%bv : list (bv 5));
apply (YQ04.st_ok_prune tfxsegs _ _ _ [] []) in HS;
lazymatch type of HS with st_ok _ _ ?ss _ => replace ss with MS_E in HS by (img_try ((img_case; vm_compute); img_refl)) end.
Lemma missB : forall W0 c, at_STM MS_L W0 c -> SRr tfxsegs W0 c (at_STM MS_E).
Proof.
intros W0 c (-> & ms & mat & En & -> & HEn & HS & MEQW & PRESW & BUFW). pose proof Hwx_tfa as Hwx.
pose proof Hsp as (Hlo & Hbot & Hhi & Hal). pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
pose proof derived_ranges as DR. pose proof high_facts as LF. pose proof RZ_facts as (RF1 & RF2 & RF3 & RF4 & RF5 & RF6). pose proof NDv_facts as (ND1 & ND2 & ND3 & ND4 & ND5).
ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, t_cache, t_unwinding in DR, LF.
pose proof (st_ok_restrict_mkst tfxsegs (w_H W) En _ _ HS eq_refl) as Hshape; cbn [ss_pc] in Hshape;
lazymatch type of Hshape with _ = mkst _ (Z_to_bv 64 (ss_pc ?s)) _ _ => let p := img_ev (ss_pc s) in img_change (ss_pc s) with p in Hshape | _ => idtac end.
rewrite Hshape in HS. rewrite Hshape. set (mem1 := ms_mem ms) in *.
assert (MEQ : forall x : word, ~ WINM1 (bv_unsigned x) -> mem1 x = mem1 x) by (img_try (intros; img_refl)).
srr_run_sh tfxtbl_rtA_ok HS. frame_accM HEn.
assert (ZR8 : zev (rho_of En) (SAlu ALU_AND (SOff 10 7) (SLit 18446744073709551608)) = R8v).
{ clear - HEn Hn RF4.
cbn [zev zalu_raw]. unfold rho_of. rewrite (HEn 10%nat (ltHAV 10 eq_refl)), E10, Hn. unfold w64. rewrite unsigned_lit_small by zlia.
rewrite (zcanon_id (n + 7)) by (img_try (unfold M64; zlia)). rewrite (zcanon_id 18446744073709551608) by (img_try (unfold M64; zlia)).
img_change 18446744073709551608 with (2 ^ 64 - 8). rewrite land_m8_64 by zlia. unfold R8v.
pose proof (Z.div_mod (n + 7) 8 ltac:(img_try (zlia))). pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(img_try (zlia))). rewrite zcanon_id; unfold M64; zlia. }
apply (st_ok_pin_regU _ _ _ 10%bv (SOff aR8 0)) in HS. 2:{ intros X; discriminate. }
2:{ clear - HEn ZR8 DR. img_apply U_eq_by_zev; [img_refl | img_refl |]. cbn [sr_get ss_regs nth]. unfold aR8.
change (zev (rho_of En) (SOff 38 0) = zcanon (zalu_raw 63 64 ALU_ADD (zev (rho_of En) (SAlu ALU_AND (SOff 10 7) (SLit 18446744073709551608))) (zev (rho_of En) (SLit 0)))).
rewrite ZR8. cbn [zev zalu_raw]. unfold rho_of. rewrite (HEn 38%nat (ltHAV 38 eq_refl)), (eq_refl : ew E0 38 = w64 R8v). unfold w64.
rewrite unsigned_lit_small by zlia. zcanon_simp. zlia. }
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
apply (st_ok_pin_regU _ _ _ 11%bv (SLit 0)) in HS. 2:{ intros X; discriminate. }
2:{ clear - HEn ZR8 DR. img_apply U_eq_by_zev; [img_refl | img_refl |]. cbn [sr_get ss_regs nth].
change (zev (rho_of En) (SLit 0) = zcanon (zalu_raw 63 64 ALU_AND (zcanon (zalu_raw 63 64 ALU_ADD (zev (rho_of En) (SAlu ALU_AND (SOff 10 7) (SLit 18446744073709551608))) (zev (rho_of En) (SLit 0)))) (zev (rho_of En) (SLit 7)))).
rewrite ZR8. cbn [zev zalu_raw]. zcanon_simp. rewrite Z.add_0_r, land_7_mod by zlia. replace (R8v mod 8) with 0 by zlia. img_refl. }
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_to_sh tfxtbl_rtA_ok HS (0x31b08 + D_150). frame_accM HEn.
apply (st_ok_pin_regU _ _ _ 20%bv (SOff aRZ 0)) in HS. 2:{ intros X; discriminate. }
2:{ pose proof kz_cases as KC. clear - HEn KC. pin_zev. unfold aRZ, aKL. rewrite (HEn 58%nat (ltHAV 58 eq_refl)), (HEn 57%nat (ltHAV 57 eq_refl)), EaRZ, EaKL.
unfold w64, RZ, rz_of. destruct KC as [->|[->|[->|[->|[->| ->]]]]]; (img_case; vm_compute); img_refl. }
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_to_sh tfxtbl_rtA_ok HS (0x31b18 + D_150). frame_accM HEn.
apply (st_ok_pin_regU _ _ _ 19%bv (SOff aND 0)) in HS. 2:{ intros X; discriminate. }
2:{ clear - HEn ND1 ND5 RF1 DR. pin_zev. unfold aND, aR8, aRZ. rewrite (HEn 63%nat (ltHAV 63 eq_refl)), (HEn 38%nat (ltHAV 38 eq_refl)), (HEn 58%nat (ltHAV 58 eq_refl)), EaND, EaRZ,
(eq_refl : ew E0 38 = w64 R8v). unfold w64. rewrite !unsigned_lit_small by zlia. zcanon_simp. zlia. }
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_sh tfxtbl_rtA_ok HS. frame_accM HEn.
srr_branch_sh tfxtbl_rtA_ok HS.
2:{ exfalso. clear - Hc HEn ND5. rewrite branch_geu_U in Hc. apply Bool.negb_false_iff in Hc. apply Z.ltb_lt in Hc. revert Hc.
rewrite !U_zev by img_refl. cbn [zev zalu_raw]. unfold rho_of, aND.
rewrite (HEn 63%nat (ltHAV 63 eq_refl)), EaND. unfold w64. rewrite unsigned_lit_small by zlia.
rewrite (zcanon_id (NDv + 0)) by (img_try (unfold M64; zlia)). img_change (zcanon (-1)) with (2 ^ 64 - 1). rewrite lxor_ones64 by zlia.
zcanon_simp. zlia. }
clear Hc.
srr_run_sh tfxtbl_rtA_ok HS. frame_accM HEn.
srr_branch_sh tfxtbl_rtA_ok HS.
-
rewrite branch_ltu_U, (U_lit En 512) in Hc by zlia. apply Z.ltb_lt in Hc.
assert (EN : U En (SOff 63 0) = NDv) by (img_try (clear - HEn ND5; img_apply U_atom; [img_try (rewrite (HEn 63%nat (ltHAV 63 eq_refl)); img_exact EaND) | img_try (zlia)])). rewrite EN in Hc.
assert (K3 : 3 <= kz) by (img_try (clear - Hc ND4 Hkz; zlia)).
srr_run_to_sh tfxtbl_rtA_ok HS (0x36150 + D_150). frame_accM HEn.
class_close HS HEn (CL_hi_E En HEn K3) CL_hi.
lazymatch type of HS with st_ok _ ?E2 _ _ => set (EnE := E2) in HS end.
assert (HEnE : forall j, (j < aHAV)%nat -> ew EnE j = ew E0 j) by (img_try (intros j Hj; (subst EnE; cbv beta); unfold aHAV in Hj; rewrite ew_havoc_old by zlia; img_apply HEn; img_exact Hj)).
close_ST EnE HEnE HS mem1 MEQ MEQW PRESW BUFW.
-
rewrite branch_ltu_U, (U_lit En 512) in Hc by zlia. apply Z.ltb_ge in Hc.
assert (EN : U En (SOff 63 0) = NDv) by (img_try (clear - HEn ND5; img_apply U_atom; [img_try (rewrite (HEn 63%nat (ltHAV 63 eq_refl)); img_exact EaND) | img_try (zlia)])). rewrite EN in Hc.
assert (K2 : kz <= 2) by (img_try (clear - Hc ND3 Hkz; pose proof kz_cases as KC; destruct KC as [->|[->|[->|[->|[->| ->]]]]]; cbn in ND3; zlia)).
srr_run_to_sh tfxtbl_rtA_ok HS (0x36150 + D_150). frame_accM HEn.
class_close HS HEn (CL_lo_E En HEn K2) CL_lo.
lazymatch type of HS with st_ok _ ?E2 _ _ => set (EnE := E2) in HS end.
assert (HEnE : forall j, (j < aHAV)%nat -> ew EnE j = ew E0 j) by (img_try (intros j Hj; (subst EnE; cbv beta); unfold aHAV in Hj; rewrite ew_havoc_old by zlia; img_apply HEn; img_exact Hj)).
close_ST EnE HEnE HS mem1 MEQ MEQW PRESW BUFW.
Qed.
Lemma missC : forall W0 c, at_STM MS_E W0 c -> SRr tfxsegs W0 c (at_STM MS_CALL).
Proof.
intros W0 c (-> & ms & mat & En & -> & HEn & HS & MEQW & PRESW & BUFW). pose proof Hwx_tfa as Hwx.
pose proof Hsp as (Hlo & Hbot & Hhi & Hal). pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
pose proof derived_ranges as DR. pose proof high_facts as LF. pose proof RZ_facts as (RF1 & RF2 & RF3 & RF4 & RF5 & RF6). pose proof NDv_facts as (ND1 & ND2 & ND3 & ND4 & ND5).
ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, t_cache, t_unwinding in DR, LF.
pose proof (st_ok_restrict_mkst tfxsegs (w_H W) En _ _ HS eq_refl) as Hshape; cbn [ss_pc] in Hshape;
lazymatch type of Hshape with _ = mkst _ (Z_to_bv 64 (ss_pc ?s)) _ _ => let p := img_ev (ss_pc s) in img_change (ss_pc s) with p in Hshape | _ => idtac end.
rewrite Hshape in HS. rewrite Hshape. set (mem1 := ms_mem ms) in *.
assert (MEQ : forall x : word, ~ WINM1 (bv_unsigned x) -> mem1 x = mem1 x) by (img_try (intros; img_refl)).
srr_run_sh tfxtbl_rtA_ok HS. frame_accM HEn.
apply (st_ok_pin_regU _ _ _ 9%bv (SOff aP 0)) in HS;
[ | img_try (intros X; discriminate)
| img_try (clear - T SB HEn DR LF Hcl Hcnt Hv Hn; pin_zev; unfold aP;
rewrite (HEn 40%nat (ltHAV 40 eq_refl)), (HEn 32%nat (ltHAV 32 eq_refl)), (HEn 39%nat (ltHAV 39 eq_refl)), EaP, EaT, (eq_refl : ew E0 39 = w64 cl);
unfold w64; rewrite !unsigned_lit_small by (unfold Pv, t_cache in *; zlia); unfold Pv, t_cache in *; zcanon_simp; zlia) ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_to_sh tfxtbl_rtA_ok HS (0x3670c + D_150). frame_accM HEn.
close_ST En HEn HS mem1 MEQ MEQW PRESW BUFW.
Qed.
Lemma miss1 : SRr tfxsegs W cfg0 (at_STM MS_CALL).
Proof.
eapply SRr_bind; [img_try (img_exact missA)|]. intros W1 c1 _ H1.
eapply SRr_bind; [img_try (img_exact (missB W1 c1 H1))|]. intros W2 c2 _ H2. img_exact (missC W2 c2 H2).
Qed.
End e.
End d.
