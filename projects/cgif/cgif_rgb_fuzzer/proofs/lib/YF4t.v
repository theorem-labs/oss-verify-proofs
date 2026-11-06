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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF64 YF3v YF4q YF3w YF41.
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
Definition WINN {imgk : img} (a : Z) : Prop :=
(sp0 - ASTACK <= a < sp0 - IFRAME) \/ (sp0 - 64 <= a < sp0) \/ (TFX_OOM <= a < TFX_OOM + 1) \/ (TFX_ERRNO <= a < TFX_ERRNO + 4).
Definition WSKELN {imgk : img} : list (option nat * Z * Z) :=
[(Some 2%nat, - ASTACK, - IFRAME); (Some 2%nat, -64, 0); (None, TFX_OOM, TFX_OOM + 1); (None, TFX_ERRNO, TFX_ERRNO + 4)].
Lemma WSKELN_WINN : forall (E : env) a t,
(forall k, (k < aHAV)%nat -> ew E k = ew E0 k) -> In t WSKELN ->
base_val E (fst (fst t)) + snd (fst t) <= a < base_val E (fst (fst t)) + snd t -> WINN a.
Proof.
intros E a t HE Hin Hr. unfold WSKELN in Hin. cbn [In] in Hin. unfold WINN. unfold aHAV, IFRAME, ASTACK in *.
repeat match type of Hin with _ \/ _ => destruct Hin as [<-|Hin] | False => destruct Hin end;
cbn [fst snd base_val] in Hr; rewrite ?HE in Hr by zlia; rewrite ?E2 in Hr; unfold sp0 in *; zlia.
Qed.
Lemma windows_WINN : forall (E : env) rs a,
(forall k, (k < aHAV)%nat -> ew E k = ew E0 k) ->
forallb (fun t => existsb (win_sub t) WSKELN || (snd t <=? snd (fst t))) (windows rs) = true ->
in_wrange E rs a -> WINN a.
Proof.
intros E rs a HE Hb Hw. destruct (in_wrange_windows E rs a Hw) as (b & lo & hi & Hin & Hr).
pose proof (proj1 (forallb_forall _ _) Hb _ Hin) as Ht. cbn beta in Ht. apply Bool.orb_prop in Ht as [Ht|Ht].
- apply existsb_exists in Ht as (u & Hinu & Hsub). img_exact (WSKELN_WINN E a u HE Hinu (win_sub_sound E a _ u Hsub Hr)).
- cbn [fst snd] in Ht. apply Z.leb_le in Ht. zlia.
Qed.
Definition at_STN (ss : sstate) (W' : world tfxsegs) (c' : config) : Prop :=
W' = W /\ exists ms mat (E' : env),
c' = mkCfg ms (with_vm_backing (m_vm_lazy md0) mat md0) /\
(forall k, (k < aHAV)%nat -> ew E' k = ew E0 k) /\
st_ok tfxsegs E' ss (restrict (w_H W) ms) /\
ms_mem ms = mem0 /\
(forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) (ms_mem ms) a).
Definition at_RETN (W' : world tfxsegs) (c' : config) : Prop :=
W' = W /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md0) mat md0) /\
getr regs' 10 = Z_to_bv 64 0 /\
(forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs0 r) /\
(forall x : word, ~ WINN (bv_unsigned x) -> mem' x = mem0 x) /\
(forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem' a) /\
val_mem tfxsegs (mrestrict (w_H W) mem') TFX_OOM 1 1 /\ val_mem tfxsegs (mrestrict (w_H W) mem') TFX_ERRNO 4 12.
Lemma segN : forall W0 c, at_STN MS_N0 W0 c -> SRr tfxsegs W0 c at_RETN.
Proof.
intros W0 c (-> & ms & mat & En & -> & HEn & HS & MEM0 & PRESW). pose proof Hwx_tfa as Hwx.
pose proof Hsp as (Hlo & Hbot & Hhi & Hal). pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
assert (Usp : 0 <= bv_unsigned (getr regs0 2) < 2 ^ 64) by img_apply u64_range.
pose proof (st_ok_restrict_mkst tfxsegs (w_H W) En _ _ HS eq_refl) as Hshape; cbn [ss_pc] in Hshape;
lazymatch type of Hshape with _ = mkst _ (Z_to_bv 64 (ss_pc ?s)) _ _ => let p := img_ev (ss_pc s) in img_change (ss_pc s) with p in Hshape | _ => idtac end.
rewrite Hshape in HS. rewrite Hshape. cbn [ms_mem] in MEM0, PRESW. set (mem1 := ms_mem ms) in *.
srr_run_to_sh tfxtbl_rtA_ok HS (0x53434 + D_2c4).
match type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msZ end.
lazymatch type of HF with frame_of ?E ?rs ?ma ?mb =>
assert (MEQ : forall x : word, ~ WINN (bv_unsigned x) -> mb x = ma x)
by (img_try (intros x Hx; img_apply HF; intros Hw; img_apply Hx; img_exact (windows_WINN E rs (bv_unsigned x) HEn ltac:((img_case; vm_compute); img_refl) Hw)))
end. clear HF HFr.
eapply (SRr_ret_at tfxsegs tfxtbl_rtA tfxtbl_rtA_ok Hwx W En); [img_try (img_exact HS) | img_refl | img_try ((img_case; vm_compute); img_refl) |].
intros matZ.
rreg HS (1%bv : bv 5) RZ1. rewrite (HEn 1%nat (ltHAV 1 eq_refl)), E1 in RZ1. rewrite RZ1. unfold YK0s.ret_ok in Hra. rewrite Hra.
split; [img_refl|]. exists (ms_regs msZ), (ms_mem msZ), matZ. split; [img_refl|].
split. { rreg HS (10%bv : bv 5) R. img_exact R. }
split. { intros r Hr. cbn [In] in Hr.
repeat match type of Hr with _ \/ _ => destruct Hr as [<-|Hr] | False => destruct Hr end;
lazymatch goal with |- getr _ ?r = _ =>
let R := fresh "R" in rreg HS r R; rewrite R;
first [ let k := img_ev (Z.to_nat (bv_unsigned r)) in rewrite (HEn k (ltHAV k eq_refl)); img_exact (Er k r eq_refl)
| symmetry; img_exact Htp ] end. }
split. { intros x Hx. rewrite (MEQ x Hx). (subst mem1; cbv beta). rewrite MEM0. img_refl. }
split. { pose proof high_facts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
intros a Ha. assert (Ha' : TFX_IMG_END <= a < 2 ^ 64) by (img_try (clear - Ha Hlo T7 Usp; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END, ASTACK, kHighMemBeg in *; unfold sp0 in *; zlia)).
destruct (Z_lt_le_dec a (sp0 - IFRAME)) as [Hlo'|Hge].
- eapply (st_ok_window_apresent_off (w_H W) En _ _ 1 _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite (HEn 2%nat (ltHAV 2 eq_refl)), E2; clear - Ha Hlo'; unfold IFRAME, ASTACK in *; unfold sp0 in *; zlia) | img_try (off_by ltac:(img_exact Ha')) ].
- destruct (Z_lt_le_dec a (sp0 - 64)) as [Hmid|Htop'].
+ img_apply (apresent_same (w_H W) mem1); [| img_try (img_apply PRESW; img_exact Ha)]. img_apply MEQ. rewrite unsigned_lit_small by (img_try (clear - Ha'; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END in *; zlia)).
clear - Hge Hmid Ha'. unfold zone3, TFX_IMG_LO, kLowShadowBeg, WINN, IFRAME, TFX_OOM, TFX_ERRNO, TFX_IMG_END in *. zlia.
+ eapply (st_ok_window_apresent_off (w_H W) En _ _ 2 _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite (HEn 2%nat (ltHAV 2 eq_refl)), E2; clear - Ha Htop'; unfold sp0 in *; zlia) | img_try (off_by ltac:(img_exact Ha')) ]. }
split. { memv HS 4%nat 0%nat; [img_refl | img_refl | img_try (zlia)]. }
memv HS 5%nat 0%nat; [img_refl | img_refl | img_try (zlia)].
Qed.
End e.
End d.
