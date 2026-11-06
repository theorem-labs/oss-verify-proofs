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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF64 YF3v YF3y YF54 YF3w YF3x YF3z.
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
Ltac zlia := first [ img_lia | ceil; unfold zone3, zone3cases, in_app, app_addr, in_band_rw, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, ASAN_CEIL in *; img_lia ].
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
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Local Abbreviation RZ := (@YF54.RZ).
Local Abbreviation NPv := (@YF54.NPv n).
Local Abbreviation R8v := (@YF54.R8v n).
Local Abbreviation N8D := (@YF54.N8D n).
Local Abbreviation Pv := (@YF54.Pv ly cl).
Local Abbreviation PVv := (@YF54.PVv ly cl cnt).
Local Abbreviation Kv := (@YF54.Kv ly cl v).
Local Abbreviation SHBv := (@YF54.SHBv).
Local Abbreviation SKv := (@YF54.SKv ly cl v).
Local Abbreviation SSLOTv := (@YF54.SSLOTv ly cl).
Local Abbreviation AR7 f := (f n cl v) (only parsing).
Local Abbreviation PBv := (AR7 (@YF54.PBv ly)).
Local Abbreviation Uv := (@YF54.Uv ly cl v).
Local Abbreviation SUv := (@YF54.SUv ly cl v).
Local Abbreviation FILv := (@YF54.FILv n).
Local Abbreviation NDv := (@YF54.NDv n).
Local Abbreviation AR2 f := (f imgk ly regs0) (only parsing).
Local Abbreviation tr := ((AR2 (@YF54.tr)) ch).
Local Abbreviation AR0 f := (f n ch cl cnt v csz j0 jb j1 j2 j3 j4) (only parsing).
Local Abbreviation XW := (AR0 (AR2 (@YF54.XW))).
Local Abbreviation E0 := (AR0 (AR2 (@YF54.E0))).
Local Abbreviation EaT := (AR0 (AR2 (@YF54.EaT))).
Local Abbreviation EaC := (AR0 (AR2 (@YF54.EaC))).
Local Abbreviation EaSB := (AR0 (AR2 (@YF54.EaSB))).
Local Abbreviation EaTOP := (AR0 (AR2 (@YF54.EaTOP))).
Local Abbreviation Er := (AR0 (AR2 (@YF54.Er))).
Local Abbreviation E2 := (AR0 (AR2 (@YF54.E2))).
Local Abbreviation E1 := (AR0 (AR2 (@YF54.E1))).
Local Abbreviation E8 := (AR0 (AR2 (@YF54.E8))).
Local Abbreviation E10 := (AR0 (AR2 (@YF54.E10))).
Local Abbreviation E4 := (AR0 (AR2 (@YF54.E4))).
Local Abbreviation EaP := (AR0 (AR2 (@YF54.EaP))).
Local Abbreviation EaR8 := (AR0 (AR2 (@YF54.EaR8))).
Local Abbreviation EaK := (AR0 (AR2 (@YF54.EaK))).
Local Abbreviation EaSK := (AR0 (AR2 (@YF54.EaSK))).
Local Abbreviation EaSSLOT := (AR0 (AR2 (@YF54.EaSSLOT))).
Local Abbreviation EaPB := (AR0 (AR2 (@YF54.EaPB))).
Local Abbreviation EaPV := (AR0 (AR2 (@YF54.EaPV))).
Local Abbreviation EaRZ := (AR0 (AR2 (@YF54.EaRZ))).
Local Abbreviation EaU := (AR0 (AR2 (@YF54.EaU))).
Local Abbreviation EaSU := (AR0 (AR2 (@YF54.EaSU))).
Local Abbreviation EaFIL := (AR0 (AR2 (@YF54.EaFIL))).
Local Abbreviation EaNP := (AR0 (AR2 (@YF54.EaNP))).
Local Abbreviation EaND := (AR0 (AR2 (@YF54.EaND))).
Local Abbreviation WINT := (@YF54.WINT ly cl).
Local Abbreviation PBW := (AR7 (@YF54.PBW ly)).
Local Abbreviation WIN := (AR7 (@YF54.WIN ly regs0)).
Local Abbreviation win_in_WIN := (AR7 (@YF54.win_in_WIN ly regs0)).
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
Local Abbreviation HCdisj := (@YF54.HCdisj _ ly regs0 v Hv LY).
Local Abbreviation DZONE := (@YF54.DZONE imgk ly).
Variable DPOST : Z -> (word -> option byte) -> Prop.
Local Abbreviation HC_NB := (@YF54.HC_NB _ ly LY).
Hypothesis HKpres : forall a, Kv <= a < Kv + RZ + R8v -> apresent (w_H W) mem0 a.
Hypothesis HSKpres : forall a, SKv <= a < SKv + (RZ + R8v) / 8 -> apresent (w_H W) mem0 a.
Hypothesis HPB250 : NPv mod 8 <> 0 -> val_mem tfxsegs (mrestrict (w_H W) mem0) PBv 1 250.
Local Abbreviation HCX := (@YF54.HCX _ ly LY).
Local Abbreviation tr_length := ((AR2 (@YF54.tr_length)) mem0 n ch v DPOST).
Local Abbreviation AR4 f := (f ly regs0 mem0) (only parsing).
Local Abbreviation Kv_range := ((AR7 (AR4 (@YF54.Kv_range))) Hcl Hv Hv2 DPOST).
Local Abbreviation AR6 f := (AR2 f mem0 n v Hv LY IMG DPOST) (only parsing).
Local Abbreviation high_facts := (AR6 (@YF54.high_facts _)).
Local Abbreviation blocks_facts := (@YF54.blocks_facts _ imgk ly LY IMG).
Local Abbreviation off_T := (AR6 (@YF54.off_T _)).
Local Abbreviation off_C := (AR6 (@YF54.off_C _)).
Local Abbreviation off_NB := (@YF54.off_NB _ imgk ly LY IMG).
Local Abbreviation off_SB := (@YF54.off_SB _ imgk ly LY IMG).
Ltac off_by tac :=
first [ img_apply off_img_high; tac
| img_apply off_T; unfold kThreadObjSize; tac
| img_apply off_C; tac
| img_apply off_NB; unfold kNodesBlockSize; tac
| img_apply off_SB; unfold kStoreBlockSize; tac
| unfold off_img; unfold TFX_IMG_LO; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; tac ].
Hypothesis Nrange : 0 <= n <= 48.
Local Abbreviation K0_facts := (@YF54.K0_facts n Nrange).
Local Abbreviation RZ_num := (@YF54.RZ_num n Nrange).
Ltac numconst ::= (ceil; unfold zone3, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize,
t_cache, t_unwinding, t_stats, ASTACK, TFX_IMG_END, TFX_IMG_LO, kLowShadowBeg, UNW_STK, BST_SIZE, DEP_STK in * ); try pose proof RZ_num as RZN.
Local Abbreviation AR3 f := (f Hcl Hv Hcnt Hv2 LY IMG DPOST Nrange) (only parsing).
Local Abbreviation derived_ranges := (AR3 ((AR2 (@YF54.derived_ranges _)) mem0 n cl cnt v)).
Hypothesis Hcl_def : cl = class_id (R8v + RZ).
Local Abbreviation CLk := (@YF54.CLk).
Local Abbreviation CLk_E := ((AR0 ((AR2 (@YF54.CLk_E)) mem0)) DPOST Nrange Hcl_def).
Local Abbreviation WIN1 := (AR7 (@YF54.WIN1 ly regs0)).
Local Abbreviation WIN1_WIN := ((AR7 (AR4 (@YF54.WIN1_WIN))) DPOST).
Local Abbreviation AR5 f := (f n cl cnt v jb Hcl Hv Hcnt Hjb Hsp DPOST Nrange) (only parsing).
Local Abbreviation WIN_odd := (AR5 (AR4 (@YF54.WIN_odd))).
Local Abbreviation WIN1_odd := (AR5 (AR4 (@YF54.WIN1_odd))).
Local Abbreviation WSKEL := (@YF54.WSKEL).
Local Abbreviation WSKEL1 := (@YF54.WSKEL1).
Local Abbreviation win_sub := (@YF54.win_sub).
Local Abbreviation win_sub_sound := ((AR4 (@YF54.win_sub_sound)) n v Hv DPOST).
Local Abbreviation WSKEL_WIN := (AR3 (AR0 ((AR2 (@YF54.WSKEL_WIN _)) mem0))).
Local Abbreviation WSKEL1_WIN1 := (AR3 (AR0 ((AR2 (@YF54.WSKEL1_WIN1 _)) mem0))).
Local Abbreviation windows_WIN := (AR3 (AR0 ((AR2 (@YF54.windows_WIN _)) mem0))).
Local Abbreviation windows_WIN1 := (AR3 (AR0 ((AR2 (@YF54.windows_WIN1 _)) mem0))).
Local Abbreviation frame_WIN1 := (AR3 (AR0 ((AR2 (@YF54.frame_WIN1 _)) mem0))).
Local Abbreviation AR1 f := (f _ imgk ly regs0 mem0 n cl cnt v Hcl Hv Hcnt Hv2 LY IMG Hsp DPOST Nrange) (only parsing).
Local Abbreviation WIN_not_high := (AR1 (@YF54.WIN_not_high)).
Variables (mat0 : list word).
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 (0x53104 + D_2c4)) mem0 (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis U1 : tfx_unwind_spec.
Hypothesis SEED : st_ok tfxsegs E0 SS0K (restrict (w_H W) (mkst regs0 (w64 (0x53104 + D_2c4)) mem0 (seg_rom tfxsegs))).
Local Abbreviation all_disjoint_of_forall := (@YF54.all_disjoint_of_forall).
Local Abbreviation kept_of_frame := ((AR4 (@YF54.kept_of_frame imgk W)) n v DPOST).
Local Abbreviation SKEL_TAIL := (@YF54.SKEL_TAIL imgk).
Local Abbreviation stack_ivs := ((AR4 (@YF54.stack_ivs _)) n v Hv LY Hsp DPOST).
Local Abbreviation stack_ivs2 := ((AR4 (@YF54.stack_ivs2 _)) n v Hv LY Hsp DPOST).
Local Abbreviation DZONE_disj := (AR1 (@YF54.DZONE_disj)).
Local Abbreviation RFACTS := (AR7 (AR2 (@YF54.RFACTS))).
Local Abbreviation zone_lit := (AR1 (@YF54.zone_lit)).
Local Abbreviation zone_T := (AR1 (@YF54.zone_T)).
Local Abbreviation zone_C := (AR1 (@YF54.zone_C)).
Local Abbreviation zone_K := (AR1 (@YF54.zone_K)).
Local Abbreviation zone_SH := (AR1 (@YF54.zone_SH)).
Local Abbreviation tail_ext_ok := ((AR0 ((AR2 (@YF54.tail_ext_ok _)) mem0)) Hcl Hv Hcnt Hv2 LY IMG Hsp DPOST Nrange).
Local Abbreviation at_ST := (AR0 ((AR4 (@YF54.at_ST _ imgk W)) md0)).
Local Abbreviation at_ST2 := ((AR0 ((AR4 (@YF54.at_ST2 _ imgk W)) md0)) DPOST).
Local Abbreviation at_S2 := ((AR0 ((AR4 (@YF54.at_S2 _ imgk W)) md0)) DPOST).
Local Abbreviation at_RET := ((AR4 (@YF54.at_RET _ imgk W)) md0 n cl cnt v jb DPOST).
Ltac frame_acc HE :=
match goal with
| MEQ : (forall x : word, ~ WIN1 ?odd (bv_unsigned x) -> ?m1 x = ?mb x), HFx : frame_of ?E ?rs ?m1 ?m2 |- _ =>
let MEQ' := fresh "MEQ" in
assert (MEQ' : forall x : word, ~ WIN1 odd (bv_unsigned x) -> m2 x = mb x)
by (img_try (intros x Hx; transitivity (m1 x); [img_try (img_exact (frame_WIN1 odd E rs m1 m2 HE ltac:((img_case; vm_compute); img_refl) HFx x Hx)) | img_try (img_exact (MEQ x Hx))]));
clear MEQ HFx; rename MEQ' into MEQ
end.
Local Abbreviation memset_stretch := ((AR5 ((AR4 (@YF54.memset_stretch _ imgk W)) md0)) mat0).
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
Local Abbreviation case0_sizes := (@YF54.case0_sizes n Nrange).
Local Abbreviation Kv_is_sptr := (@YF54.Kv_is_sptr ly cl v Hcl B off Hoff_def).
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
Hypothesis D1w : forall (regs : bvmap 5 word) (mem : word -> option byte) (md : Model),
getr regs 10 = Z_to_bv 64 (sp0 - IFRAME + 16) -> getr regs 11 = Z_to_bv 64 (Z.of_nat (length tr)) ->
getr regs 3 = getr regs0 3 -> getr regs 4 = Z_to_bv 64 TFX_TP -> getr regs 1 = Z_to_bv 64 (0x31cc8 + D_150) ->
bv_unsigned (getr regs 2) = sp0 - 2272 ->
(forall i, (i < length tr)%nat -> val_mem tfxsegs (mrestrict (w_H W) mem) (sp0 - IFRAME + 16 + 8 * Z.of_nat i) 8 (nth i tr 0)) ->
(forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem a) ->
(forall x : word, ~ WIN false (bv_unsigned x) -> mem x = mem0 x) ->
SRr tfxsegs W (mkCfg (mkst regs (Z_to_bv 64 A_StackDepotPut) mem (seg_rom tfxsegs)) md)
(fun W' c' => W' = W /\ exists z regs' mem' mat,
c' = mkCfg (mkst regs' (Z_to_bv 64 (0x31cc8 + D_150)) mem' (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md) mat md) /\
regs_preserved regs regs' /\
(forall x : word, ~ (sp0 - 2272 - DEP_STK <= bv_unsigned x < sp0 - 2272) -> ~ DZONE (bv_unsigned x) -> mem' x = mem x) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
DPOST z mem').
Lemma segD : forall W0 c, at_ST KS_PD W0 c -> SRr tfxsegs W0 c (fun W' c' => exists z, at_ST2 KS_PD z W' c').
Proof.
intros W0 c (-> & ms & mat & En & -> & HEn & HS & MEQ0 & PRES & BUF). pose proof Hwx_tfa as Hwx.
pose proof Hsp as (Hlo & Hbot & Hhi & Hal). pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd in T2, T4, T7.
assert (Usp : 0 <= bv_unsigned (getr regs0 2) < 2 ^ 64) by img_apply u64_range.
pose proof (st_ok_restrict_mkst tfxsegs (w_H W) En _ _ HS eq_refl) as Hshape; cbn [ss_pc] in Hshape;
lazymatch type of Hshape with _ = mkst _ (Z_to_bv 64 (ss_pc ?s)) _ _ => let p := img_ev (ss_pc s) in img_change (ss_pc s) with p in Hshape | _ => idtac end. rewrite Hshape.
rreg HS (2%bv : bv 5) R2. rewrite (HEn 2%nat (ltHAV 2 eq_refl)), E2 in R2.
eapply SRr_mono.
{ img_apply (D1w (ms_regs ms) (ms_mem ms)).
- rreg HS (10%bv : bv 5) R; rewrite R, (HEn 2%nat (ltHAV 2 eq_refl)), E2. unfold IFRAME, sp0. f_equal; zlia.
- rreg HS (11%bv : bv 5) R; rewrite R, (HEn 36%nat (ltHAV 36 eq_refl)). img_refl.
- rreg HS (3%bv : bv 5) R; rewrite R, (HEn 3%nat (ltHAV 3 eq_refl)). img_exact (Er 3 3%bv eq_refl).
- rreg HS (4%bv : bv 5) R; rewrite R. img_refl.
- rreg HS (1%bv : bv 5) R; rewrite R. img_refl.
- rewrite R2. clear - cfg0 sp0 T SB Hlo Hhi T4 T7. rewrite unsigned_lit_small by addr_tac. unfold sp0; zlia.
- img_exact BUF.
- img_exact PRES.
- img_exact MEQ0. }
intros W' c' Hle (-> & z & regs2 & mem2 & mat2 & -> & HP & Hfr & Hpr & HDP). exists z.
split; [img_refl|]. exists ms, mat2, En, regs2, mem2.
split; [img_try (rewrite wvb_collapse; img_refl)|].
split; [img_try (img_exact HEn)|]. split; [img_try (img_exact HS)|]. split; [img_try (img_exact MEQ0)|]. split; [img_try (img_exact PRES)|]. split; [img_try (img_exact BUF)|].
split; [img_try (img_exact HP)|]. split; [img_try (img_exact Hfr)|]. split; [img_try (img_exact Hpr)|]. img_exact HDP.
Qed.
Local Ltac stack_pres En HEn HS PCH PRESB :=
intros a Ha; pose proof Hsp as (Hlo_ & Hbot_ & Hhi_ & Hal_); pose proof (lo_top ly LY) as (T1' & T2' & T3' & T4' & T5' & T6' & T7');
assert (Ra : 0 <= a < 2 ^ 64) by (img_try (clear - Ha Hlo_ Hhi_ T4' T7'; addr_tac));
destruct (Z_lt_le_dec a (sp0 - 2272)) as [H1|H1];
[ img_try (eapply (st_ok_window_apresent_off (w_H W) En _ _ 0 _ a HS); [img_refl | clear - Ha Ra H1 Hlo_ Hhi_ T4' T7' HEn; cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite (HEn 2%nat (ltHAV 2 eq_refl)), E2; addr_tac | off_by ltac:(addr_tac) ])
| img_try (destruct (Z_lt_le_dec a (sp0 - 2128)) as [H2|H2];
[ eapply (st_ok_window_apresent_off (w_H W) En _ _ 2 _ a HS); [img_refl | clear - Ha Ra H1 H2 Hlo_ Hhi_ T4' T7' HEn; cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite (HEn 2%nat (ltHAV 2 eq_refl)), E2; addr_tac | off_by ltac:(addr_tac) ]
| destruct (Z_lt_le_dec a (sp0 - 64)) as [H3|H3];
[ img_apply PCH; [| img_exact Ra | img_apply PRESB; zlia];
pose proof derived_ranges as DR'; pose proof high_facts as LF'; pose proof stack_ivs as SI; pose proof Kv_range as HKR_;
clear - H2 H3 DR' LF' SI HKR_ Hlo_ T7'; unfold WIN1, WINT, PBW, IFRAME; numconst; zlia
| eapply (st_ok_window_apresent_off (w_H W) En _ _ 3 _ a HS); [img_refl | clear - Ha Ra H1 H2 H3 Hlo_ Hhi_ T4' T7' HEn; cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite (HEn 2%nat (ltHAV 2 eq_refl)), E2; addr_tac | off_by ltac:(addr_tac) ] ] ]) ].
Local Ltac stack_pres_odd En HEn HS PCH PRESB :=
intros a Ha; pose proof Hsp as (Hlo_ & Hbot_ & Hhi_ & Hal_); pose proof (lo_top ly LY) as (T1' & T2' & T3' & T4' & T5' & T6' & T7');
assert (Ra : 0 <= a < 2 ^ 64) by (img_try (clear - Ha Hlo_ Hhi_ T4' T7'; addr_tac));
destruct (Z_lt_le_dec a (sp0 - 2272)) as [H1|H1];
[ img_try (eapply (st_ok_window_apresent_off (w_H W) En _ _ 1 _ a HS); [img_refl | clear - Ha Ra H1 Hlo_ Hhi_ T4' T7' HEn; cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite (HEn 2%nat (ltHAV 2 eq_refl)), E2; addr_tac | off_by ltac:(addr_tac) ])
| img_try (destruct (Z_lt_le_dec a (sp0 - 2128)) as [H2|H2];
[ eapply (st_ok_window_apresent_off (w_H W) En _ _ 3 _ a HS); [img_refl | clear - Ha Ra H1 H2 Hlo_ Hhi_ T4' T7' HEn; cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite (HEn 2%nat (ltHAV 2 eq_refl)), E2; addr_tac | off_by ltac:(addr_tac) ]
| destruct (Z_lt_le_dec a (sp0 - 64)) as [H3|H3];
[ img_apply PCH; [| img_exact Ra | img_apply PRESB; zlia];
pose proof derived_ranges as DR'; pose proof high_facts as LF'; pose proof stack_ivs as SI; pose proof Kv_range as HKR_;
clear - H2 H3 DR' LF' SI HKR_ Hlo_ T7'; unfold WIN1, WINT, PBW, IFRAME; numconst; zlia
| eapply (st_ok_window_apresent_off (w_H W) En _ _ 4 _ a HS); [img_refl | clear - Ha Ra H1 H2 H3 Hlo_ Hhi_ T4' T7' HEn; cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite (HEn 2%nat (ltHAV 2 eq_refl)), E2; addr_tac | off_by ltac:(addr_tac) ] ] ]) ].
Local Ltac join_close HS :=
lazymatch type of HS with st_ok _ ?E ?ss ?ms0 =>
let rs := img_ev (R_scr2 :: tl (ss_mem ss)) in
pose proof (st_ok_submem tfxsegs E ss ms0 rs HS
ltac:(img_try (let m := img_ev (ss_mem ss) in img_change (ss_mem ss) with m;
img_apply submem_keep; [ img_try (unfold subregion; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks];
split; [img_refl|]; split; [zlia|]; split; [zlia|]; split; [right; zlia|]; intros cc Hcc; destruct Hcc)
| img_try (img_apply submem_refl) ]))
ltac:(img_try ((img_case; vm_compute); img_refl))) as HSJ;
clear HS; rename HSJ into HS; cbn [ss_pc ss_regs ss_resv ss_facts] in HS
end;
forget_regs HS 139%nat ([1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28]%bv : list (bv 5));
apply (YQ04.st_ok_prune tfxsegs _ _ _ [] []) in HS;
lazymatch type of HS with st_ok _ _ ?ss _ => replace ss with KS_Q in HS by (img_try ((img_case; vm_compute); img_refl)) end.
Lemma seg2aK : forall z W0 c, at_ST2 KS_PD z W0 c -> SRr tfxsegs W0 c (at_S2 false KS_Q z).
Proof.
intros z W0 c (-> & ms & mat & En & regs2 & mem2 & -> & HEn & HS & MEQ0 & PRES & BUF & HP & Hfr & Hpr & HDP). pose proof Hwx_tfa as Hwx.
pose proof Hsp as (Hlo & Hbot & Hhi & Hal). pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
pose proof derived_ranges as DR. pose proof high_facts as LF. pose proof K0_facts as (_ & NR & NPr & NP0 & NP1 & R8r & R8m & NPR8 & _ & N8r & N8m & NPN8 & _).
ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, t_cache, t_unwinding in DR, LF.
assert (Usp : 0 <= bv_unsigned (getr regs0 2) < 2 ^ 64) by img_apply u64_range.
pose proof (st_ok_restrict_mkst tfxsegs (w_H W) En _ _ HS eq_refl) as Hshape; cbn [ss_pc] in Hshape;
lazymatch type of Hshape with _ = mkst _ (Z_to_bv 64 (ss_pc ?s)) _ _ => let p := img_ev (ss_pc s) in img_change (ss_pc s) with p in Hshape | _ => idtac end.
rreg HS (2%bv : bv 5) R2. rewrite (HEn 2%nat (ltHAV 2 eq_refl)), E2 in R2.
set (XD := fun a : Z => (sp0 - 2272 - DEP_STK <= a < sp0 - 2272) \/ DZONE a).
assert (Hfr' : forall x : word, ~ XD (bv_unsigned x) -> mem2 x = ms_mem ms x).
{ intros x Hx. (subst XD; cbv beta). img_apply Hfr; [img_try (unfold sp0 in *; zlia) | img_try (tauto)]. }
pose proof (DZONE_disj false) as DZD0.
assert (PRD2 : forall a, DZONE a -> apresent (w_H W) mem0 a -> apresent (w_H W) mem2 a).
{ intros a Ha Hp. img_apply Hpr. img_apply (apresent_same (w_H W) mem0); [|img_try (img_exact Hp)]. img_apply MEQ0.
destruct (DZD0 a Ha) as (N0 & _). pose proof blocks_facts as (NBhi & SBhi & _).
rewrite unsigned_lit_small; [img_try (img_exact N0)|]. clear - Ha NBhi SBhi LY; unfold DZONE in Ha.
numconst. zlia.   }
lazymatch type of HS with st_ok _ _ ?ss ?ms0 =>
let m := img_ev (ss_mem ss) in
lazymatch m with ?r0 :: ?r1 :: ?rest =>
pose proof (st_ok_after_call tfxsegs 117 En ss ms0 regs2 (mrestrict (w_H W) mem2) (r0 :: trim_lo r1 (-2272) :: rest) (0x31cc8 + D_150) HS eq_refl
ltac:(img_try ((img_case; vm_compute); img_refl)) ltac:(img_try ((img_case; vm_compute); img_refl)) ltac:(img_try ((img_case; vm_compute); img_refl)) ltac:(img_try ((img_case; vm_compute); img_refl))
ltac:(img_try (img_apply submem_keep; [img_try (img_apply subregion_refl)|]; img_apply submem_keep; [img_try (img_apply subregion_trim_lo) | img_try (img_apply submem_refl)]))
ltac:(img_try ((img_case; vm_compute); img_refl)) HP) as HS1;
let rsv := img_ev (r0 :: trim_lo r1 (-2272) :: rest) in
img_change (r0 :: trim_lo r1 (-2272) :: rest) with rsv in HS1;
let ss2 := img_ev (ss_after_call ss rsv 117 (0x31cc8 + D_150)) in
change (ss_after_call ss rsv 117 (0x31cc8 + D_150)) with ss2 in HS1
end
end.
cbn [ms_mem restrict] in HS1.
lazymatch type of HS1 with Forall _ (?r0 :: ?r1 :: ?r2 :: ?tail) -> _ =>
assert (KEPT : Forall (region_kept tfxsegs En (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) mem2)) (r0 :: r1 :: r2 :: tail));
[ img_try (pose proof (DZONE_disj false) as DZD;
constructor; [|constructor; [|constructor]];
[ eapply (kept_of_frame En _ _ XD _ Hfr' Hpr); cbn [base_val YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi];
clear - HEn XD DZD Hlo Hhi T4 T7; rewrite (HEn 2%nat (ltHAV 2 eq_refl)), E2; (subst XD; cbv beta); intros a Ha; cbn beta;
[ split; [ intros [Hs|Hd]; [unfold DEP_STK in Hs; zlia | img_exact (proj2 (proj2 (proj2 (DZD a Hd))) ltac:(unfold ASTACK; zlia))]
| unfold zone3, TFX_IMG_LO, kLowShadowBeg, ASTACK, kHighMemBeg, kHighMemEnd in *; zlia ]
| unfold zone3, TFX_IMG_LO, kLowShadowBeg, ASTACK, TFX_IMG_END, kHighMemBeg, kHighMemEnd in *; zlia ]
| eapply (kept_of_frame En _ _ XD _ Hfr' Hpr); cbn [base_val YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi];
clear - HEn XD DZD Hlo Hhi T4 T7; rewrite (HEn 2%nat (ltHAV 2 eq_refl)), E2; (subst XD; cbv beta); intros a Ha; cbn beta;
[ split; [ intros [Hs|Hd]; [unfold DEP_STK in Hs; zlia | img_exact (proj2 (proj2 (proj2 (DZD a Hd))) ltac:(unfold ASTACK; zlia))]
| unfold zone3, TFX_IMG_LO, kLowShadowBeg, ASTACK, kHighMemBeg, kHighMemEnd in *; zlia ]
| unfold zone3, TFX_IMG_LO, kLowShadowBeg, ASTACK, TFX_IMG_END, kHighMemBeg, kHighMemEnd in *; zlia ]
| eapply (kept_of_frame En _ _ XD _ Hfr' Hpr); cbn [base_val YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi];
clear - HEn XD DZD Hlo Hhi T4 T7; rewrite (HEn 2%nat (ltHAV 2 eq_refl)), E2; (subst XD; cbv beta); intros a Ha; cbn beta;
[ split; [ intros [Hs|Hd]; [unfold DEP_STK in Hs; zlia | img_exact (proj2 (proj2 (proj2 (DZD a Hd))) ltac:(unfold ASTACK; zlia))]
| unfold zone3, TFX_IMG_LO, kLowShadowBeg, ASTACK, kHighMemBeg, kHighMemEnd in *; zlia ]
| unfold zone3, TFX_IMG_LO, kLowShadowBeg, ASTACK, TFX_IMG_END, kHighMemBeg, kHighMemEnd in *; zlia ]
| img_apply Forall_forall; intros r Hr;
apply (in_map skel) in Hr; replace (map skel tail) with SKEL_TAIL in Hr by ((img_case; vm_compute); img_refl);
pose proof (tail_ext_ok En r HEn Hr) as (X1 & X2 & X3 & X4 & X5 & X6);
eapply (kept_of_frame En _ _ XD _ Hfr' Hpr); clear - XD X1 X2 X3 X4 X5 X6; intros a Ha; (subst XD; cbv beta); cbn beta;
[ split; [ intros [Hs|Hd]; [unfold DEP_STK, ASTACK in *; zlia | unfold DZONE in Hd; numconst; zlia] | zlia ]
| numconst; zlia ] ])
| img_try (specialize (HS1 KEPT); clear KEPT) ]
end.
assert (PRES2 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem2 a) by (img_try (intros a Ha; apply Hpr, PRES, Ha)).
set (En3 := havoc En 117 (map (getr regs2) CLOB)) in HS1.
assert (HEn3 : forall k, (k < aHAV)%nat -> ew En3 k = ew E0 k) by (img_try (intros k Hk; (subst En3; cbv beta); unfold aHAV in Hk; rewrite ew_havoc_old by zlia; img_apply HEn; img_exact Hk)).
apply (st_ok_add_region _ _ _ (YQ0b.mkRegion (Some 2%nat) (- ASTACK) (- 2272) (- ASTACK) (- 2272) [])) in HS1;
[ | img_refl
| unfold YQ0b.region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem];
rewrite (HEn3 2%nat (ltHAV 2 eq_refl)), E2;
split; [img_try (addr_tac)|]; split; [img_try (addr_tac)|]; split; [img_try (intros o Ho; img_apply apresent_writable_off; [off_by ltac:(addr_tac) | img_apply PRES2; addr_tac]) | img_try (constructor)]
| img_apply all_disjoint_of_forall; intros r' [<-|[<-|[<-|Hr']]];
[ unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; unfold ASTACK; zlia
| unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; unfold ASTACK; zlia
| unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; unfold ASTACK; zlia
| apply (in_map skel) in Hr';
lazymatch type of Hr' with In _ (map skel ?tl) => replace (map skel tl) with SKEL_TAIL in Hr' by (img_try ((img_case; vm_compute); img_refl)) end;
pose proof (tail_ext_ok En3 r' HEn3 Hr') as (X1 & X2 & X3 & X4 & X5 & X6);
unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; rewrite (HEn3 2%nat (ltHAV 2 eq_refl)), E2;
unfold ASTACK, sp0 in *; zlia ] ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1.
rewrite <- (restrict_mkst_fx (w_H W)) in HS1. clear HS. rename HS1 into HS.
assert (MEQ : forall x : word, ~ WIN1 false (bv_unsigned x) -> mem2 x = mem2 x) by (img_try (intros; img_refl)).
srr_run_sh tfxtbl_rtA_ok HS. frame_acc HEn3.
apply (st_ok_pin_regU _ _ _ 10%bv (SOff aSK 0)) in HS. 2:{ intros X; discriminate. }
2:{ clear - HEn3 DR LF Hcl Hcnt Hv. pin_zev. unfold aSK.
rewrite (HEn3 48%nat (ltHAV 48 eq_refl)), (HEn3 47%nat (ltHAV 47 eq_refl)), (HEn3 45%nat (ltHAV 45 eq_refl)), EaSK, EaK, (eq_refl : ew E0 47 = w64 SHBv).
unfold w64. unfold SKv, SHBv in *. rewrite !unsigned_lit_small by zlia. zcanon_simp.
land_lits. rewrite Z.shiftr_div_pow2 by zlia. img_change (2 ^ 3) with 8.
pose proof (div8_bounds Kv ltac:(img_try (zlia))). zcanon_simp. zlia. }
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_sh tfxtbl_rtA_ok HS. frame_acc HEn3.
apply (st_ok_pin_regU _ _ _ 22%bv (SOff aN8D 0)) in HS. 2:{ intros X; discriminate. }
2:{ clear - HEn3 DR LF Hcl Hcnt Hv NPr. pin_zev. unfold aN8D, aNP.
rewrite (HEn3 55%nat (ltHAV 55 eq_refl)), (HEn3 62%nat (ltHAV 62 eq_refl)), (eq_refl : ew E0 55 = w64 N8D), EaNP.
unfold w64. unfold N8D in *. rewrite !unsigned_lit_small by zlia. zcanon_simp.
img_change 281474976710648 with (2 ^ 48 - 8). rewrite land_m8_48 by zlia.
pose proof (div8_bounds NPv ltac:(img_try (zlia))). pose proof (Z.div_mod NPv 8 ltac:(img_try (zlia))). zcanon_simp. zlia. }
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
assert (EN8 : U En3 (SOff 55 0) = N8D) by (img_try (clear - HEn3 DR; img_apply U_atom; [img_try (rewrite (HEn3 55%nat (ltHAV 55 eq_refl)); img_refl) | img_try (zlia)])).
srr_branch_sh tfxtbl_rtA_ok HS.
{
rewrite branch_eq_U, EN8, (U_lit En3 0) in Hc by zlia. apply Z.eqb_eq in Hc.
srr_run_to_sh tfxtbl_rtA_ok HS (0x31dd4 + D_150). frame_acc HEn3.
join_close HS.
lazymatch type of HS with st_ok _ ?E2 _ _ => set (EnS := E2) in HS end.
assert (HEnS : forall j, (j < aHAV)%nat -> ew EnS j = ew E0 j) by (img_try (intros j Hj; (subst EnS; cbv beta); unfold aHAV in Hj; rewrite ew_havoc_old by zlia; img_apply HEn3; img_exact Hj)).
match type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msS end.
assert (CH2 : forall x : word, ~ WIN1 false (bv_unsigned x) -> ~ (SUv <= bv_unsigned x < SUv + N8D / 8) -> ms_mem msS x = mem2 x).
{ intros x NA NB. img_exact (MEQ x NA). }
assert (PCH2 : forall a, ~ WIN1 false a -> 0 <= a < 2 ^ 64 -> apresent (w_H W) mem2 a -> apresent (w_H W) (ms_mem msS) a).
{ intros a NA Ra Hp. img_apply (apresent_same (w_H W) mem2); [img_try (img_apply MEQ; rewrite unsigned_lit_small by img_exact Ra; img_exact NA)|]. img_exact Hp. }
pose proof (DZONE_disj false) as DZDo.
img_apply SRr_ret. split; [img_refl|]. lazymatch goal with |- context [mkCfg ?msf (with_vm_backing _ ?matf _)] => exists msf, matf, EnS, mem2 end. split; [img_refl|]. split; [img_try (img_exact HEnS)|]. split; [img_try (img_exact HS)|]. split; [img_try (img_exact HDP)|]. split; [img_try (img_exact PRD2)|].
split. { intros x Hd. destruct (DZDo _ Hd) as (D0 & D2 & D3 & D4). img_apply CH2; [img_try (intros H1; apply D0, WIN1_WIN, H1) | img_try (img_exact D3)]. }
split. { intros x NA ND NB. rewrite (CH2 x) by (img_try (try img_exact NB; intros H1; apply NA, WIN1_WIN, H1)).
rewrite Hfr' by (img_try ((subst XD; cbv beta); cbn beta; intros [H1|H1]; [img_try (img_apply NA; unfold WIN; left; clear - H1; numconst; zlia) | img_try (img_exact (ND H1))])).
img_apply MEQ0. img_exact NA. }
split. { stack_pres EnS HEnS HS PCH2 PRES2. }
split. { intros x Hx. exfalso. clear - Hx Hc N8r. rewrite Hc in Hx. img_change (0 / 8) with 0 in Hx. zlia. }
intros HH; discriminate HH. }
rewrite branch_eq_U, EN8, (U_lit En3 0) in Hc by zlia. apply Z.eqb_neq in Hc.
srr_run_sh tfxtbl_rtA_ok HS. frame_acc HEn3.
assert (E16 : Kv = 16 * (Kv / 16)) by (img_try (clear - DR; pose proof (Z.div_mod Kv 16 ltac:(zlia)); zlia)).
assert (EN8' : N8D = 8 * (N8D / 8)) by (img_try (clear - DR; pose proof (Z.div_mod N8D 8 ltac:(zlia)); zlia)).
assert (EK8 : Kv / 8 = 2 * (Kv / 16)) by (img_try (clear - E16 DR; rewrite E16 at 1; replace (16 * (Kv / 16)) with ((2 * (Kv / 16)) * 8) by zlia; img_apply Z.div_mul; zlia)).
assert (EU8 : (Kv + 16) / 8 = 2 * (Kv / 16) + 2) by (img_try (clear - E16 DR; replace (Kv + 16) with ((2 * (Kv / 16) + 2) * 8) by zlia; img_apply Z.div_mul; zlia)).
assert (EP8 : (Kv + 8 + N8D) / 8 = N8D / 8 + 2 * (Kv / 16) + 1) by (img_try (clear - E16 EN8' DR; replace (Kv + 8 + N8D) with ((N8D / 8 + 2 * (Kv / 16) + 1) * 8) by zlia; img_apply Z.div_mul; zlia)).
apply (st_ok_pin_regU _ _ _ 8%bv (SOff aCNT8 0)) in HS. 2:{ intros X; discriminate. }
2:{ clear - HEn3 DR E16 EN8' EK8 EU8 EP8. pin_zev. unfold aCNT8, aN8D, aK.
rewrite (HEn3 56%nat (ltHAV 56 eq_refl)), (HEn3 45%nat (ltHAV 45 eq_refl)), (HEn3 55%nat (ltHAV 55 eq_refl)), EaK, (eq_refl : ew E0 56 = w64 (N8D / 8)), (eq_refl : ew E0 55 = w64 N8D).
unfold w64. rewrite !unsigned_lit_small by zlia. zcanon_simp. land_lits. rewrite !Z.shiftr_div_pow2 by zlia. img_change (2 ^ 3) with 8.
zcanon_simp. rewrite ?EP8, ?EU8. zcanon_simp. zlia. }
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
apply (st_ok_pin_regU _ _ _ 10%bv (SOff aSK 2)) in HS. 2:{ intros X; discriminate. }
2:{ clear - HEn3 DR E16 EK8 EU8. pin_zev. unfold aSK, aSHB, aK.
rewrite (HEn3 48%nat (ltHAV 48 eq_refl)), (HEn3 47%nat (ltHAV 47 eq_refl)), (HEn3 45%nat (ltHAV 45 eq_refl)), EaSK, EaK, (eq_refl : ew E0 47 = w64 SHBv).
unfold w64. unfold SUv, SKv, SHBv in *. rewrite !unsigned_lit_small by zlia. zcanon_simp. land_lits. rewrite !Z.shiftr_div_pow2 by zlia. img_change (2 ^ 3) with 8.
zcanon_simp. rewrite ?EU8, ?EK8 in *. zcanon_simp. zlia. }
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_sh tfxtbl_rtA_ok HS. frame_acc HEn3.
match type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msM end.
assert (SHPRES : forall a, SUv <= a < SUv + N8D / 8 -> apresent (w_H W) (ms_mem msM) a).
{ intros a Ha.
assert (NW : ~ WIN false a) by (img_try (clear - Ha DR LF Hlo T7; unfold WIN, WINT, PBW, IFRAME in *; numconst; zlia)).
assert (Ra : 0 <= a < 2 ^ 64) by (img_try (clear - Ha DR; numconst; zlia)).
img_apply (apresent_same (w_H W) mem2); [img_try (img_apply MEQ; rewrite unsigned_lit_small by img_exact Ra; intros H1; apply NW, WIN1_WIN, H1)|].
img_apply Hpr. img_apply (apresent_same (w_H W) mem0); [img_try (img_apply MEQ0; rewrite unsigned_lit_small by img_exact Ra; img_exact NW)|].
img_apply HSKpres. clear - Ha DR. pose proof (Z.div_le_mono N8D R8v 8 ltac:(img_try (zlia)) ltac:(img_try (zlia))). replace (RZ + R8v) with (2 * 8 + R8v) by zlia. rewrite Z.div_add_l by zlia. zlia. }
rreg HS (11%bv : bv 5) RA1m1.
eapply (memset_stretch 133 En3 _ _ _ SUv (N8D / 8) (0x31dd4 + D_150));
[ img_try (img_exact HS) | img_refl | img_refl | img_try ((img_case; vm_compute); img_refl) | img_try ((img_case; vm_compute); img_refl)
| img_try (rreg HS (10%bv : bv 5) R; rewrite R, (HEn3 48%nat (ltHAV 48 eq_refl)), EaSK; unfold w64; rewrite ?Zbv_add_unsigned, ?Z.add_0_r; f_equal; clear - DR; zlia)
| img_try (rreg HS (12%bv : bv 5) R; rewrite R, (HEn3 56%nat (ltHAV 56 eq_refl)); img_refl)
| img_try (rreg HS (1%bv : bv 5) R; rewrite R; img_refl)
| img_try (clear - DR; zlia) | img_try (clear - DR; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; zlia) | img_try (clear - DR; numconst; zlia) | img_refl | img_try (clear; zlia)
| img_try (img_exact SHPRES)
| img_try (intros r Hr) | img_try (intros r a Hr) | img_try (intros r a Hr) | ].
1-3: cbn [ss_mem] in Hr; destruct Hr as [<-|[<-|[<-|[<-|Hr]]]];
[ cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi base_val]; clear - DR LF Hlo T7 Hhi T2 T4 Usp HEn3; rewrite (HEn3 2%nat (ltHAV 2 eq_refl)), E2; numconst; zlia
| cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi base_val]; clear - DR LF Hlo T7 Hhi T2 T4 Usp HEn3; rewrite (HEn3 2%nat (ltHAV 2 eq_refl)), E2; numconst; zlia
| cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi base_val]; clear - DR LF Hlo T7 Hhi T2 T4 Usp HEn3; rewrite (HEn3 2%nat (ltHAV 2 eq_refl)), E2; numconst; zlia
| cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi base_val]; clear - DR LF Hlo T7 Hhi T2 T4 Usp HEn3; rewrite (HEn3 2%nat (ltHAV 2 eq_refl)), E2; numconst; zlia
| apply (in_map skel) in Hr;
lazymatch type of Hr with In _ (map skel ?tl) => replace (map skel tl) with SKEL_TAIL in Hr by (img_try ((img_case; vm_compute); img_refl)) end;
pose proof (tail_ext_ok En3 r HEn3 Hr) as (X1 & X2 & X3 & X4 & X5 & X6); clear - DR LF X1 X2 X3 X4 X5 X6; numconst; zlia ].
intros regs3 mem3 mat3 HS3 H10c Hfr3 Hpr3 Hin3. clear HS. rename HS3 into HS.
lazymatch type of HS with st_ok _ ?E ?ss _ => set (En4 := E) in HS; let ss' := img_ev constr:(ss) in img_change ss with ss' in HS end.
assert (HEn4 : forall k, (k < aHAV)%nat -> ew En4 k = ew E0 k) by (img_try (intros k Hk; (subst En4; cbv beta); unfold aHAV in Hk; rewrite ew_havoc_old by zlia; img_apply HEn3; img_exact Hk)).
assert (MEQ3 : forall x : word, ~ WIN1 false (bv_unsigned x) -> mem3 x = mem3 x) by (img_try (intros; img_refl)).
rename MEQ into MEQ2. rename MEQ3 into MEQ.
join_close HS.
lazymatch type of HS with st_ok _ ?E2 _ _ => set (EnS := E2) in HS end.
assert (HEnS : forall j, (j < aHAV)%nat -> ew EnS j = ew E0 j) by (img_try (intros j Hj; (subst EnS; cbv beta); unfold aHAV in Hj; rewrite ew_havoc_old by zlia; img_apply HEn4; img_exact Hj)).
assert (CH2 : forall x : word, ~ WIN1 false (bv_unsigned x) -> ~ (SUv <= bv_unsigned x < SUv + N8D / 8) -> mem3 x = mem2 x).
{ intros x NA NB. rewrite (Hfr3 x NB). img_apply MEQ2. img_exact NA. }
assert (PCH2 : forall a, ~ WIN1 false a -> 0 <= a < 2 ^ 64 -> apresent (w_H W) mem2 a -> apresent (w_H W) mem3 a).
{ intros a NA Ra Hp. img_apply Hpr3. img_apply (apresent_same (w_H W) mem2); [img_try (img_apply MEQ2; rewrite unsigned_lit_small by img_exact Ra; img_exact NA)|]. img_exact Hp. }
pose proof (DZONE_disj false) as DZDo.
img_apply SRr_ret. split; [img_refl|]. lazymatch goal with |- context [mkCfg ?msf (with_vm_backing _ ?matf _)] => exists msf, matf, EnS, mem2 end. split; [img_refl|]. split; [img_try (img_exact HEnS)|]. split; [img_try (img_exact HS)|]. split; [img_try (img_exact HDP)|]. split; [img_try (img_exact PRD2)|].
cbn [ms_mem mkst].
split. { intros x Hd. destruct (DZDo _ Hd) as (D0 & D2 & D3 & D4). img_apply CH2; [img_try (intros H1; apply D0, WIN1_WIN, H1) | img_try (img_exact D3)]. }
split. { intros x NA ND NB. cbn [ms_mem mkst]. etransitivity; [img_try (img_apply CH2; [intros H1; apply NA, WIN1_WIN, H1 | img_exact NB]) |].
rewrite Hfr' by (img_try ((subst XD; cbv beta); cbn beta; intros [H1|H1]; [img_try (img_apply NA; unfold WIN; left; clear - H1; numconst; zlia) | img_try (img_exact (ND H1))])).
img_apply MEQ0. img_exact NA. }
split. { stack_pres EnS HEnS HS PCH2 PRES2. }
split. { intros x Hx. cbn [ms_mem mkst]. rewrite (Hin3 x Hx), RA1m1. img_refl. }
intros HH; discriminate HH.
Qed.
Local Ltac close2b EnW HEnW HS MEQ EQD M0 PRS SRZ PBVt memD HDP PRD2 :=
img_apply SRr_ret; split; [img_refl|];
lazymatch goal with |- context [mkCfg ?msf (with_vm_backing _ ?matf _)] => exists msf, matf, EnW, memD end;
split; [img_refl|]; split; [img_try (img_exact HEnW)|]; split; [img_try (img_exact HS)|]; split; [img_try (img_exact HDP)|]; split; [img_try (img_exact PRD2)|];
pose proof (DZONE_disj true) as DZDo;
split; [ img_try (intros x Hd; destruct (DZDo _ Hd) as (D0 & D2 & D3 & D4); rewrite (MEQ x) by (intros H1; apply D0, WIN1_WIN, H1); apply EQD, Hd) |];
split; [ img_try (intros x NA ND NB; rewrite (MEQ x) by (intros H1; apply NA, WIN1_WIN, H1); img_apply M0; [intros H1; img_apply NA; first [img_exact H1 | img_apply WIN_odd; img_exact H1] | img_exact ND | img_exact NB]) |];
split; [| img_try (split; [ intros x Hx; pose proof Kv_range as HKR; pose proof derived_ranges as DR'; pose proof high_facts as LF'; pose proof Hsp as (Hlo_ & _); pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7_);
rewrite (MEQ x) by (pose proof stack_ivs as SI; clear - Hx DR' LF' HKR Hlo_ T7_ SI; unfold WIN1, WINT, PBW, IFRAME; numconst; zlia); apply SRZ, Hx
| PBVt ]) ].
Local Ltac sslot_pin HS En HEn :=
apply (st_ok_pin_regU _ _ _ 10%bv (SOff aSSLOT 0)) in HS;
[ | intros X; discriminate
| lazymatch goal with |- U ?E _ = U _ (sr_get ?sr ?r) => let t := img_ev (sr_get sr r) in img_change (sr_get sr r) with t end;
lazymatch goal with |- U ?E _ = U _ ?t => img_change t with SSLOT_term end;
img_apply U_eq_by_zev; [img_refl | img_try (clear; (img_case; vm_compute); img_refl) |];
change (zev (rho_of En) (SOff aSSLOT 0) = zcanon (zalu_raw 63 64 ALU_ADD (zev (rho_of En) (SOff aT 2912)) (zcanon (zalu_raw 63 64 ALU_SLL (zev (rho_of En) CLk) (zev (rho_of En) (SLit 3))))));
rewrite (CLk_E En HEn); pose proof derived_ranges as DR'; pose proof high_facts as LF'; clear - HEn Hcl DR' LF';
cbn [zev zalu_raw]; unfold rho_of, aSSLOT, aT; rewrite (HEn 52%nat (ltHAV 52 eq_refl)), (HEn 32%nat (ltHAV 32 eq_refl)), EaSSLOT, EaT;
unfold w64; unfold SSLOTv in *; numconst; rewrite !unsigned_lit_small by zlia; zcanon_simp; land_lits; rewrite ?Z.shiftl_mul_pow2 by zlia;
img_change (2 ^ 3) with 8; zcanon_simp; zlia ];
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
Lemma seg2b_odd : NPv mod 8 <> 0 -> forall z W0 c, at_S2 false KS_Q z W0 c -> SRr tfxsegs W0 c (at_S2 true KS_To z).
Proof.
intros H8 z W0 c (-> & ms & mat & En & mem2 & -> & HEn & HS & HDP & PRD2 & EQD & M0 & PRS & SRZ & PBV). pose proof Hwx_tfa as Hwx.
pose proof Hsp as (Hlo & Hbot & Hhi & Hal). pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
pose proof derived_ranges as DR. pose proof high_facts as LF. pose proof K0_facts as (_ & NR & NPr & NP0 & NP1 & R8r & R8m & NPR8 & _ & N8r & N8m & NPN8 & _).
ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, t_cache, t_unwinding in DR, LF.
assert (Usp : 0 <= bv_unsigned (getr regs0 2) < 2 ^ 64) by img_apply u64_range.
pose proof (st_ok_restrict_mkst tfxsegs (w_H W) En _ _ HS eq_refl) as Hshape; cbn [ss_pc] in Hshape;
lazymatch type of Hshape with _ = mkst _ (Z_to_bv 64 (ss_pc ?s)) _ _ => let p := img_ev (ss_pc s) in img_change (ss_pc s) with p in Hshape | _ => idtac end.
rewrite Hshape in HS. rewrite Hshape. set (mem1 := ms_mem ms) in *.
assert (MEQ : forall x : word, ~ WIN1 false (bv_unsigned x) -> mem1 x = mem1 x) by (img_try (intros; img_refl)).
assert (ENP : U En (SOff 62 0) = NPv) by (img_try (clear - HEn NPr; img_apply U_atom; [img_try (rewrite (HEn 62%nat (ltHAV 62 eq_refl)); img_exact EaNP) | img_try (zlia)])).
assert (EN8 : U En (SOff 55 0) = N8D) by (img_try (clear - HEn DR; img_apply U_atom; [img_try (rewrite (HEn 55%nat (ltHAV 55 eq_refl)); img_refl) | img_try (zlia)])).
srr_branch_sh tfxtbl_rtA_ok HS.
-
exfalso. clear - Hc ENP EN8 H8 NPr DR. rewrite branch_eq_U, ENP, EN8 in Hc. apply Z.eqb_eq in Hc. img_apply H8.
pose proof (Z.div_mod NPv 8 ltac:(img_try (zlia))). zlia.
- clear Hc. srr_run_sh tfxtbl_rtA_ok HS. frame_acc HEn.
apply (st_ok_pin_regU _ _ _ 10%bv (SOff aPB 0)) in HS. 2:{ intros X; discriminate. }
2:{ clear - HEn DR LF. pin_zev. unfold aPB, aSHB, aN8D, aK.
rewrite (HEn 54%nat (ltHAV 54 eq_refl)), (HEn 47%nat (ltHAV 47 eq_refl)), (HEn 45%nat (ltHAV 45 eq_refl)), (HEn 55%nat (ltHAV 55 eq_refl)), EaPB, EaK,
(eq_refl : ew E0 47 = w64 SHBv), (eq_refl : ew E0 55 = w64 N8D).
unfold w64. unfold PBv, SHBv in *. numconst. rewrite !unsigned_lit_small by zlia. zcanon_simp. land_lits. rewrite !Z.shiftr_div_pow2 by zlia.
img_change (2 ^ 3) with 8. replace (Kv + 16 + N8D) with (Kv + RZ + N8D) by zlia. zcanon_simp. zlia. }
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
pose proof H8 as E8.
assert (R8odd : N8D + 8 <= R8v).
{ clear - NPr NPR8 R8m N8r N8m NPN8 E8 DR. destruct (Z.eq_dec N8D NPv) as [Ee|Ne]; [img_try (exfalso; img_apply E8; rewrite <- Ee; img_exact N8m)|].
apply Z.mod_divide in R8m as [q Hq]; [|img_try (zlia)]. apply Z.mod_divide in N8m as [r Hr]; [|img_try (zlia)]. zlia. }
match type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msP end.
assert (NPB : ~ WIN1 false PBv) by (img_try (pose proof stack_ivs as SI; clear - DR LF Hlo T7 SI; unfold WIN1, WINT, PBW, IFRAME; numconst; zlia)).
assert (RPB : 0 <= PBv < 2 ^ 64) by (img_try (clear - DR; numconst; zlia)).
assert (NDZ : ~ DZONE PBv) by (img_try (pose proof blocks_facts as (NBhi & SBhi & _); clear - DR NBhi SBhi; unfold DZONE; numconst; zlia)).
assert (MPB : ms_mem msP (Z_to_bv 64 PBv) = mem0 (Z_to_bv 64 PBv)).
{ rewrite (MEQ (Z_to_bv 64 PBv)) by (img_try (rewrite unsigned_lit_small by img_exact RPB; img_exact NPB)).
img_apply M0; rewrite unsigned_lit_small by img_exact RPB; [img_try (pose proof stack_ivs as SI; clear - DR LF Hlo T7 SI; unfold WIN, WINT, PBW; numconst; zlia) | img_try (img_exact NDZ) | img_try (clear - DR; zlia)]. }
assert (PPB : apresent (w_H W) (ms_mem msP) PBv).
{ img_apply (apresent_same (w_H W) mem0 _ _ MPB). img_apply HSKpres. clear - DR R8odd.
pose proof (Z.div_le_mono (N8D + 8) R8v 8 ltac:(img_try (zlia)) R8odd) as X. replace (RZ + R8v) with (2 * 8 + R8v) by zlia. rewrite Z.div_add_l by zlia.
replace (N8D + 8) with ((N8D / 8 + 1) * 8) in X by zlia. rewrite Z.div_mul in X by zlia. zlia. }
apply (st_ok_add_region _ _ _ (YQ0b.mkRegion (Some aPB) 0 1 0 1 [YQ0b.mkChunk 0 (CVal 1 (SLit 250))])) in HS;
[ | img_refl
| unfold YQ0b.region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem];
unfold aPB; rewrite (HEn 54%nat (ltHAV 54 eq_refl)), EaPB; unfold w64; rewrite unsigned_lit_small by img_exact RPB;
split; [img_try (zlia)|]; split; [img_try (zlia)|]; split;
[ img_try (intros o Ho; replace (PBv + o) with PBv by zlia; img_apply apresent_writable_off; [off_by ltac:(clear - DR; numconst; zlia) | img_exact PPB])
| img_try (img_apply Forall_cons; [|img_apply Forall_nil];
eapply (chunk_ok_val tfxsegs En _ _ 0 1 (SLit 250) 250); [img_refl | cbn; zlia | cbn; zlia |];
rewrite Z.add_0_r; eapply (val_mem_frame (w_H W) mem0); [| img_exact (HPB250 E8)]; intros k Hk; replace (PBv + Z.of_nat k) with PBv by zlia; img_exact MPB) ]
| img_apply all_disjoint_of_forall; intros r' Hr';
cbn [ss_mem] in Hr'; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
unfold aPB; rewrite (HEn 54%nat (ltHAV 54 eq_refl)), EaPB; unfold w64; rewrite unsigned_lit_small by img_exact RPB;
destruct Hr' as [<-|[<-|[<-|[<-|Hr']]]];
[ cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; rewrite (HEn 2%nat (ltHAV 2 eq_refl)), E2; pose proof stack_ivs as SI; clear - DR LF Hlo T7 SI; numconst; unfold sp0 in *; zlia
| cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; rewrite (HEn 2%nat (ltHAV 2 eq_refl)), E2; pose proof stack_ivs as SI; clear - DR LF Hlo T7 SI; numconst; unfold sp0 in *; zlia
| cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; rewrite (HEn 2%nat (ltHAV 2 eq_refl)), E2; pose proof stack_ivs as SI; clear - DR LF Hlo T7 SI; numconst; unfold sp0 in *; zlia
| cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; rewrite (HEn 2%nat (ltHAV 2 eq_refl)), E2; pose proof stack_ivs as SI; clear - DR LF Hlo T7 SI; numconst; unfold sp0 in *; zlia
| apply (in_map skel) in Hr';
lazymatch type of Hr' with In _ (map skel ?tl) => replace (map skel tl) with SKEL_TAIL in Hr' by (img_try ((img_case; vm_compute); img_refl)) end;
pose proof (tail_ext_ok En r' HEn Hr') as (X1 & X2 & X3 & X4 & X5 & X6 & X7); clear - X7; zlia ] ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
assert (MEQ' : forall x : word, ~ WIN1 true (bv_unsigned x) -> ms_mem msP x = mem1 x) by (img_try (intros x Hx; img_apply MEQ; intros Hw; apply Hx, WIN1_odd, Hw)).
clear MEQ. rename MEQ' into MEQ.
srr_run_sh tfxtbl_rtA_ok HS. frame_acc HEn.
sslot_pin HS En HEn.
lazymatch type of HS with st_ok _ _ ?ss _ => replace ss with KS_To in HS by (img_try ((img_case; vm_compute); img_refl)) end.
close2b En HEn HS MEQ EQD M0 PRS SRZ ltac:(img_try (idtac)) mem2 HDP PRD2.
+ match type of HS with st_ok _ _ _ (restrict _ ?msx) => assert (PCH : forall a, ~ WIN1 true a -> 0 <= a < 2 ^ 64 -> apresent (w_H W) mem1 a -> apresent (w_H W) (ms_mem msx) a)
by (img_try (intros a NA Ra Hp; img_apply (apresent_same (w_H W) mem1); [img_try (img_apply MEQ; rewrite unsigned_lit_small by img_exact Ra; img_exact NA) | img_try (img_exact Hp)])) end.
stack_pres_odd En HEn HS PCH PRS.
+ intros _. pose proof (Z.mod_pos_bound NPv 8 ltac:(img_try (zlia))) as M8.
memv HS 0%nat 0%nat; [img_try (cbn [base_val YQ0b.r_base]; rewrite (HEn 54%nat (ltHAV 54 eq_refl)), EaPB; unfold w64; rewrite unsigned_lit_small by (clear - DR LF; numconst; zlia); zlia) | | img_try (zlia)].
lazymatch goal with |- sv_denot ?E ?t = _ =>
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E t)); f_equal; img_change (bv_unsigned (sv_denot E t)) with (U E t); rewrite (U_zev E t eq_refl) end.
cbn [zev zalu_raw]. unfold rho_of. rewrite (HEn 62%nat (ltHAV 62 eq_refl)), EaNP. unfold w64. rewrite unsigned_lit_small by zlia.
zcanon_simp. rewrite land_7_mod by zlia. zcanon_simp. rewrite Z.add_0_r. img_refl.
Qed.
Lemma seg2c_odd : NPv mod 8 <> 0 -> forall z W0 c, at_S2 true KS_To z W0 c -> SRr tfxsegs W0 c (at_RET true z).
Proof.
intros H8 z W0 c (-> & ms & mat & En & mem2 & -> & HEn & HS & HDP & PRD2 & EQD & M0 & PRS & SRZ & PBV). pose proof Hwx_tfa as Hwx.
pose proof Hsp as (Hlo & Hbot & Hhi & Hal). pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
pose proof derived_ranges as DR. pose proof high_facts as LF. pose proof K0_facts as (_ & NR & NPr & NP0 & NP1 & R8r & R8m & NPR8 & _ & N8r & N8m & NPN8 & _).
ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, t_cache, t_unwinding in DR, LF.
assert (Usp : 0 <= bv_unsigned (getr regs0 2) < 2 ^ 64) by img_apply u64_range.
pose proof (st_ok_restrict_mkst tfxsegs (w_H W) En _ _ HS eq_refl) as Hshape; cbn [ss_pc] in Hshape;
lazymatch type of Hshape with _ = mkst _ (Z_to_bv 64 (ss_pc ?s)) _ _ => let p := img_ev (ss_pc s) in img_change (ss_pc s) with p in Hshape | _ => idtac end.
assert (PBV1 : true = true -> val_mem tfxsegs (mrestrict (w_H W) (ms_mem ms)) PBv 1 (NPv mod 8)) by img_exact PBV.
assert (EUv : Uv = Kv + 16) by (img_try (clear - DR; zlia)).
rewrite Hshape in HS. rewrite Hshape. set (mem1 := ms_mem ms) in *.
assert (MEQ : forall x : word, ~ WIN1 true (bv_unsigned x) -> mem1 x = mem1 x) by (img_try (intros; img_refl)).
srr_run_sh tfxtbl_rtA_ok HS. frame_acc HEn.
match type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msF end.
pose proof Kv_range as HKR. pose proof blocks_facts as (_ & _ & _ & _ & _ & _ & _ & _ & PT). unfold zdisjoint in PT. cbn [fst snd] in PT.
assert (UPRES : forall a, Uv <= a < Uv + FILv -> apresent (w_H W) (ms_mem msF) a).
{ intros a Ha. pose proof high_facts as (_ & _ & _ & _ & _ & _ & _ & _ & F9).
assert (Ra : 0 <= a < 2 ^ 64) by (img_try (clear - Ha DR; numconst; zlia)).
assert (NS : ~ (sp0 - ASTACK <= a < sp0)).
{ intros Hs. destruct (F9 a) as [N1' N2']; [img_try (clear - Hs Hlo Hhi T2; numconst; zlia)|]. img_apply N2'. clear - Ha HKR LF DR. numconst. zlia. }
assert (NW : ~ WIN true a) by (img_try (clear - Ha NS DR LF Hlo T7 HKR PT; unfold WIN, WINT, PBW, IFRAME in *; numconst; zlia)).
assert (ND : ~ DZONE a).
{ pose proof blocks_facts as BF. clear - Ha DR LF Hlo T7 BF HKR. unfold zdisjoint in BF. cbn [fst snd] in BF. unfold DZONE. numconst. zlia. }
img_apply (apresent_same (w_H W) mem1). { img_apply MEQ. rewrite unsigned_lit_small by img_exact Ra. intros H1; apply NW, WIN1_WIN, H1. }
img_apply (apresent_same (w_H W) mem0). { img_apply M0; rewrite unsigned_lit_small by img_exact Ra; [img_try (img_exact NW) | img_try (img_exact ND) | img_try (clear - Ha DR; numconst; zlia)]. }
img_apply HKpres. clear - Ha DR. numconst. zlia. }
rreg HS (11%bv : bv 5) RA1m2.
eapply (memset_stretch 152 En _ _ _ Uv FILv (0x31ffc + D_150));
[ img_try (img_exact HS) | img_refl | img_refl | img_try ((img_case; vm_compute); img_refl) | img_try ((img_case; vm_compute); img_refl)
| img_try (rreg HS (10%bv : bv 5) R; rewrite R, (HEn 45%nat (ltHAV 45 eq_refl)), EaK, EUv; unfold w64; rewrite ?Zbv_add_unsigned, ?Z.add_0_r; img_refl)
| img_try (rreg HS (12%bv : bv 5) R; rewrite R, (HEn 62%nat (ltHAV 62 eq_refl)), EaFIL; unfold w64; rewrite ?Zbv_add_unsigned, ?Z.add_0_r; img_refl)
| img_try (rreg HS (1%bv : bv 5) R; rewrite R; img_refl)
| img_try (clear - DR; zlia) | img_try (clear - DR; numconst; zlia) | img_try (clear - DR; numconst; zlia) | img_refl | img_try (clear; zlia)
| img_try (img_exact UPRES)
| img_try (intros r Hr) | img_try (intros r a Hr) | img_try (intros r a Hr) | ].
1-3: cbn [ss_mem] in Hr; destruct Hr as [<-|[<-|[<-|[<-|[<-|Hr]]]]];
[ cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi base_val]; clear - DR HKR HEn; unfold aPB;
rewrite (HEn 54%nat (ltHAV 54 eq_refl)), EaPB; unfold w64; rewrite unsigned_lit_small by (img_try (numconst; zlia)); numconst; zlia
| cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi base_val]; pose proof stack_ivs as SI; clear - DR LF Hlo T7 Hhi T2 T4 Usp HKR SI HEn; rewrite (HEn 2%nat (ltHAV 2 eq_refl)), E2; numconst; unfold sp0 in *; zlia
| cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi base_val]; pose proof stack_ivs as SI; clear - DR LF Hlo T7 Hhi T2 T4 Usp HKR SI HEn; rewrite (HEn 2%nat (ltHAV 2 eq_refl)), E2; numconst; unfold sp0 in *; zlia
| cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi base_val]; pose proof stack_ivs as SI; clear - DR LF Hlo T7 Hhi T2 T4 Usp HKR SI HEn; rewrite (HEn 2%nat (ltHAV 2 eq_refl)), E2; numconst; unfold sp0 in *; zlia
| cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi base_val]; pose proof stack_ivs as SI; clear - DR LF Hlo T7 Hhi T2 T4 Usp HKR SI HEn; rewrite (HEn 2%nat (ltHAV 2 eq_refl)), E2; numconst; unfold sp0 in *; zlia
| apply (in_map skel) in Hr;
lazymatch type of Hr with In _ (map skel ?tl) => replace (map skel tl) with SKEL_TAIL in Hr by (img_try ((img_case; vm_compute); img_refl)) end;
pose proof (tail_ext_ok En r HEn Hr) as (X1 & X2 & X3 & X4 & X5 & X6); clear - DR LF X1 X2 X3 X4 X5 X6; numconst; zlia ].
intros regs4 mem4 mat4 HS4 H10d Hfr4 Hpr4 Hin4. clear HS. rename HS4 into HS.
lazymatch type of HS with st_ok _ ?E ?ss _ => set (En5 := E) in HS; let ss' := img_ev constr:(ss) in img_change ss with ss' in HS end.
assert (HEn5 : forall k, (k < aHAV)%nat -> ew En5 k = ew E0 k) by (img_try (intros k Hk; (subst En5; cbv beta); unfold aHAV in Hk; rewrite ew_havoc_old by zlia; img_apply HEn; img_exact Hk)).
assert (MEQ4 : forall x : word, ~ WIN1 true (bv_unsigned x) -> mem4 x = mem4 x) by (img_try (intros; img_refl)).
rename MEQ into MEQ3. rename MEQ4 into MEQ.
srr_run_sh tfxtbl_rtA_ok HS. frame_acc HEn5.
eapply (SRr_ret_at tfxsegs tfxtbl_rtA tfxtbl_rtA_ok Hwx W En5); [img_try (img_exact HS) | img_refl | img_try ((img_case; vm_compute); img_refl) |].
intros matZ. match type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msZ end.
rreg HS (1%bv : bv 5) RZ1. rewrite (HEn5 1%nat (ltHAV 1 eq_refl)), E1 in RZ1. rewrite RZ1. unfold YK0s.ret_ok in Hra. rewrite Hra.
pose proof (DZONE_disj true) as DZD.
assert (CH1 : forall x : word, ~ WIN1 true (bv_unsigned x) -> ~ (Uv <= bv_unsigned x < Uv + FILv) -> ms_mem msZ x = mem1 x).
{ intros x N1' N2'. rewrite (MEQ x N1'), (Hfr4 x N2'), (MEQ3 x N1'). img_refl. }
assert (PCH1 : forall a, ~ WIN1 true a -> 0 <= a < 2 ^ 64 -> apresent (w_H W) mem1 a -> apresent (w_H W) (ms_mem msZ) a).
{ intros a N1' Ra Hp. img_apply (apresent_same (w_H W) mem4); [img_try (img_apply MEQ; rewrite unsigned_lit_small by img_exact Ra; img_exact N1')|].
img_apply Hpr4. img_apply (apresent_same (w_H W) mem1); [img_try (img_apply MEQ3; rewrite unsigned_lit_small by img_exact Ra; img_exact N1')|]. img_exact Hp. }
split; [img_refl|]. exists (ms_regs msZ), (ms_mem msZ), matZ. split; [img_refl|].
split. { rreg HS (10%bv : bv 5) R; rewrite R, (HEn5 45%nat (ltHAV 45 eq_refl)), EaK. unfold w64. rewrite ?Zbv_add_unsigned, ?Z.add_0_r. first [img_refl | f_equal; clear - DR; zlia]. }
split. { intros r Hr. cbn [In] in Hr.
repeat match type of Hr with _ \/ _ => destruct Hr as [<-|Hr] | False => destruct Hr end;
lazymatch goal with |- getr _ ?r = _ =>
let R := fresh "R" in rreg HS r R; rewrite R;
let k := img_ev (Z.to_nat (bv_unsigned r)) in
first [ rewrite (HEn5 k (ltHAV k eq_refl)); symmetry; img_exact (Er k r eq_refl) | symmetry; img_exact Htp ] end. }
split. { exists mem2. split; [img_try (img_exact HDP)|]. split; [img_try (img_exact PRD2)|].
intros x Hx. destruct (DZD _ Hx) as (N0 & N2' & N3 & N4). rewrite CH1; [img_try (apply EQD, Hx) | img_try (intros H1; apply N0, WIN1_WIN, H1) |].
clear - N2' DR. zlia. }
split. { intros x N0 ND N2' N3. rewrite CH1; [img_try (img_apply M0; assumption) | img_try (intros H1; apply N0, WIN1_WIN, H1) | img_try (clear - N2' DR; zlia)]. }
split. {   stack_pres_odd En5 HEn5 HS PCH1 PRS. }
split. {   intros a Ha.
assert (Ra : 0 <= a < 2 ^ 64) by (img_try (clear - Ha DR LF HKR; unfold WINT, PBW in Ha; numconst; destruct Ha as [Ha|[Ha|[_ Ha]]]; zlia)).
destruct Ha as [Hw|[Hk|Hpb]].
- unfold WINT in Hw. destruct Hw as [Hw|[Hw|[Hw|Hw]]].
+ eapply (st_ok_window_apresent_off (w_H W) En5 _ _ 46%nat _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite (HEn5 40%nat (ltHAV 40 eq_refl)), EaP; unfold w64; rewrite unsigned_lit_small by (clear - DR LF; numconst; zlia); zlia) | img_try (off_by ltac:(clear - Hw DR LF; numconst; zlia)) ].
+ destruct (Z_lt_le_dec a (T + 2800)) as [H28|H28].
* eapply (st_ok_window_apresent_off (w_H W) En5 _ _ 42%nat _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite (HEn5 32%nat (ltHAV 32 eq_refl)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - DR LF; numconst; zlia); unfold T in *; zlia) | img_try (off_by ltac:(clear - Hw DR LF; numconst; zlia)) ].
* eapply (st_ok_window_apresent_off (w_H W) En5 _ _ 44%nat _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite (HEn5 32%nat (ltHAV 32 eq_refl)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - DR LF; numconst; zlia); unfold T in *; zlia) | img_try (off_by ltac:(clear - Hw H28 DR LF; numconst; zlia)) ].
+ eapply (st_ok_window_apresent_off (w_H W) En5 _ _ 45%nat _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite (HEn5 52%nat (ltHAV 52 eq_refl)), EaSSLOT; unfold w64; rewrite unsigned_lit_small by (clear - DR LF; numconst; zlia); zlia) | img_try (off_by ltac:(clear - Hw DR LF; numconst; zlia)) ].
+ eapply (st_ok_window_apresent_off (w_H W) En5 _ _ 43%nat _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite (HEn5 32%nat (ltHAV 32 eq_refl)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - DR LF; numconst; zlia); unfold T in *; numconst; zlia) | img_try (off_by ltac:(clear - Hw DR LF; numconst; zlia)) ].
- destruct (Z_lt_le_dec a (Kv + 16)) as [H1|H1].
+ eapply (st_ok_window_apresent_off (w_H W) En5 _ _ 49%nat _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite (HEn5 45%nat (ltHAV 45 eq_refl)), EaK; unfold w64; rewrite unsigned_lit_small by (clear - DR LF; numconst; zlia); zlia) | img_try (off_by ltac:(clear - Hk H1 DR LF HKR; numconst; zlia)) ].
+
split. { destruct (HKpres a ltac:(img_try (clear - Hk H1 DR; numconst; zlia))) as [Hh _]. img_exact Hh. }
exists (Z_to_bv 8 190).
pose proof (Hin4 (Z_to_bv 64 a)) as Hi. rewrite unsigned_lit_small in Hi by img_exact Ra. rewrite RA1m2, unsigned_lit_small in Hi by zlia.
rewrite (MEQ (Z_to_bv 64 a)); [img_try (img_exact (Hi ltac:(clear - Hk H1 DR EUv; zlia)))|].
rewrite unsigned_lit_small by img_exact Ra. pose proof stack_ivs as SI. clear - Hk H1 DR LF HKR Hlo T7 SI PT. unfold WIN1, WINT, PBW, IFRAME. numconst. zlia.
- destruct Hpb as [_ Hpb]. eapply (st_ok_window_apresent_off (w_H W) En5 _ _ 0%nat _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; unfold aPB; rewrite (HEn5 54%nat (ltHAV 54 eq_refl)), EaPB; unfold w64; rewrite unsigned_lit_small by (clear - DR; numconst; zlia); zlia) | img_try (off_by ltac:(clear - Hpb DR; numconst; zlia)) ]. }
cbv zeta.
assert (RK : 0 <= Kv /\ Kv + 2 ^ 16 < 2 ^ 64) by (img_try (clear - DR; numconst; zlia)).
split. { memv HS 49%nat 0%nat; [img_try (cbn [base_val YQ0b.r_base]; rewrite (HEn5 45%nat (ltHAV 45 eq_refl)), EaK; unfold w64; rewrite unsigned_lit_small by (clear - DR; numconst; zlia); clear - DR; zlia) | img_refl | img_try (zlia)]. }
split. { pose proof (hdr_byte1_ok jb Hjb) as [B1 B2].
memv HS 49%nat 1%nat; [img_try (cbn [base_val YQ0b.r_base]; rewrite (HEn5 45%nat (ltHAV 45 eq_refl)), EaK; unfold w64; rewrite unsigned_lit_small by (clear - DR; numconst; zlia); clear - DR; zlia) | | img_try (zlia)].
lazymatch goal with |- sv_denot ?E ?t = _ =>
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E t)); f_equal; img_change (bv_unsigned (sv_denot E t)) with (U E t); rewrite (U_zev E t eq_refl) end.
cbn [zev zalu_raw]. unfold rho_of. rewrite (HEn5 46%nat (ltHAV 46 eq_refl)), (eq_refl : ew E0 46 = w64 jb). unfold w64. rewrite unsigned_lit_small by zlia.
unfold hdr_byte1. img_refl. }
split. { memv HS 49%nat 4%nat; [img_try (cbn [base_val YQ0b.r_base]; rewrite (HEn5 45%nat (ltHAV 45 eq_refl)), EaK; unfold w64; rewrite unsigned_lit_small by (clear - DR; numconst; zlia); clear - DR; zlia) | | img_try (zlia)].
lazymatch goal with |- sv_denot ?E ?t = _ =>
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E t)); f_equal; img_change (bv_unsigned (sv_denot E t)) with (U E t); rewrite (U_zev E t eq_refl) end.
cbn [zev zalu_raw]. unfold rho_of. rewrite (HEn5 62%nat (ltHAV 62 eq_refl)), EaNP. unfold w64. rewrite unsigned_lit_small by zlia.
zcanon_simp. land_lits. rewrite Z.shiftr_div_pow2 by zlia. rewrite Z.div_small by zlia. img_refl. }
split. { memv HS 49%nat 3%nat; [img_try (cbn [base_val YQ0b.r_base]; rewrite (HEn5 45%nat (ltHAV 45 eq_refl)), EaK; unfold w64; rewrite unsigned_lit_small by (clear - DR; numconst; zlia); clear - DR; zlia)
| img_try (cbn [sv_denot]; rewrite (HEn5 62%nat (ltHAV 62 eq_refl)), EaNP; unfold w64; rewrite ?Zbv_add_unsigned, ?Z.add_0_r; f_equal; zlia) | img_try (zlia)]. }
split. { memv HS 46%nat 0%nat; [img_try (cbn [base_val YQ0b.r_base]; rewrite (HEn5 40%nat (ltHAV 40 eq_refl)), EaP; unfold w64; rewrite unsigned_lit_small by (clear - DR LF; numconst; zlia); zlia)
| img_try (cbn [sv_denot]; rewrite (HEn5 41%nat (ltHAV 41 eq_refl)), (eq_refl : ew E0 41 = w64 cnt); unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia) | img_try (zlia)]. }
split. { memv HS 43%nat 0%nat; [img_try (cbn [base_val YQ0b.r_base]; rewrite (HEn5 32%nat (ltHAV 32 eq_refl)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - DR LF; numconst; zlia); unfold T; numconst; zlia) | img_refl | img_try (zlia)]. }
split. {   intros x Hx. pose proof (u64_range x) as Rx.
assert (N1' : ~ WIN1 true (bv_unsigned x)).
{ pose proof stack_ivs as SI. clear - Hx DR LF HKR Hlo T7 SI. unfold WIN1, WINT, PBW, IFRAME. numconst. zlia. }
rewrite (CH1 x N1') by (img_try (clear - Hx DR LF HKR; numconst; zlia)). apply SRZ, Hx. }
split. {   intros _.
pose proof (Z.mod_pos_bound NPv 8 ltac:(img_try (zlia))) as M8.
memv HS 0%nat 0%nat; [img_try (cbn [base_val YQ0b.r_base]; rewrite (HEn5 54%nat (ltHAV 54 eq_refl)), EaPB; unfold w64; rewrite unsigned_lit_small by (clear - DR LF; numconst; zlia); zlia) | | img_try (zlia)].
lazymatch goal with |- sv_denot ?E ?t = _ =>
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E t)); f_equal; img_change (bv_unsigned (sv_denot E t)) with (U E t); rewrite (U_zev E t eq_refl) end.
cbn [zev zalu_raw]. unfold rho_of. rewrite (HEn5 62%nat (ltHAV 62 eq_refl)), EaNP. unfold w64. rewrite unsigned_lit_small by zlia.
zcanon_simp. rewrite land_7_mod by zlia. zcanon_simp. rewrite Z.add_0_r. img_refl. }
intros x Hx. pose proof (u64_range x) as Rx.
assert (N1' : ~ WIN1 true (bv_unsigned x)).
{ pose proof stack_ivs as SI. clear - Hx DR LF HKR Hlo T7 SI PT. unfold WIN1, WINT, PBW, IFRAME. numconst. zlia. }
rewrite (MEQ x N1'), (Hin4 x Hx), RA1m2. img_refl.
Qed.
End e.
End d.
