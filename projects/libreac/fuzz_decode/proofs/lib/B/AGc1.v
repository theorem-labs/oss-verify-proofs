(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/AGc1.v at 95e6f1d72b6 (sha256 a84ec689c6e4) into lib/B (libreac/fuzz_decode image B, fuzz_decode.asan-ubsan), with its module paths changed and its image numerals moved to fuzz_decode.asan-ubsan (pin sha256 5d05689fd5b1) by symbol + offset (alreloc 9b786608301; KEEP, regenerated and resolved values per proofs/libreac/fuzz_decode/provenance/alloc-reloc/B/resolve.txt). *)
(* The can_fill = 0 arm of the frame-generic Allocate walk, g path (n in 49..64512).
   Ported from proofs/cgif/cgif_file_fuzzer/lib/YFhy.v..YFjg.v (cgif_file's released malloc walk, same image): the
   same scripts, with the caller's frame made abstract; the cf = 0 arm reuses the cf = 1 tail after 0x31978.
   Each lemma starts where the cf = 1 proof splits on can_fill (AGiq.seg2b_even / AGir.seg2b_odd start at
   at_S2 SS_Se / SS_So): the run to 0x31930 and its SSLOT pin, the test at 0x31940 (cf = 0 takes it), then the
   cf = 1 tail from 0x31978 (AGiq.seg2c_even / AGir.seg2c_odd after the memset) to Allocate's ret. *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import YB1v YB1q YF0l YF0m YF0x YFl0.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YO0a. From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import YB1w YE3d YFhy AGhy AGis AGhz AGi0 AGho AGc0.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Set Printing Depth 50. Set Printing Width 180.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Ltac zlia := first [ lia | ceil; unfold zone3, zone3cases, in_app, app_addr, in_band_rw, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, ASAN_CEIL in *; lia ].
Ltac zcanon_simp :=
repeat match goal with
| |- context [zcanon ?x] =>
lazymatch x with
| context [zcanon _] => fail
| context [Z.shiftl _ _] => fail | context [Z.shiftr _ _] => fail | context [Z.land _ _] => fail
| context [Z.lor _ _] => fail | context [Z.lxor _ _] => fail
| _ => rewrite (zcanon_id x) by (unfold M64; lia)
end
end.
Ltac is_zlit a := lazymatch a with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.
Ltac land_lits :=
repeat match goal with
| |- context [Z.land ?a ?b] => is_zlit a; is_zlit b; let c := eval vm_compute in (Z.land a b) in change (Z.land a b) with c
end.
Ltac numconst := ceil; unfold zone3, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize,
t_cache, t_unwinding, t_stats, AFSTACK, TFIB_IMG_END, TFIB_IMG_LO, kLowShadowBeg, UNW_STK, BST_SIZE, DEP_STK in *.
Ltac pin_zev :=
lazymatch goal with |- U _ _ = U _ (sr_get ?sr ?r) => let t := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with t end;
apply U_eq_by_zev; [reflexivity | reflexivity |]; cbn [zev zalu_raw zmd_raw]; unfold rho_of.
Ltac memv HS i j :=
lazymatch goal with |- val_mem _ _ ?a ?n ?v =>
let nn := lazymatch n with 1%nat => constr:(1%N) | 2%nat => constr:(2%N) | 4%nat => constr:(4%N) | _ => constr:(8%N) end in
lazymatch type of HS with st_ok _ ?E ?ss (restrict ?H ?ms) =>
eapply (chunk_val_at H E ss ms i j _ _ nn _ v a HS);
[ reflexivity | reflexivity | cbn [base_val YP09.r_base]
| | lazymatch goal with |- _ <= _ < ?p => let q := eval vm_compute in p in change p with q end
| cbn; lia ]
end
end.
Section e.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (n : Z) (tr : list Z).
Variables (cl cnt v csz j0 jb j1 j2 j3 j4 : Z).
Variable kz : Z.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let SOv : Z := bv_unsigned (getr regs0 13).
Let BPv : Z := bv_unsigned (getr regs0 12).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Local Abbreviation RZ := (@AGis.RZ kz).
Local Abbreviation R8v := (@AGis.R8v n).
Local Abbreviation N8D := (@AGis.N8D n).
Local Abbreviation Pv := (@AGis.Pv ly cl).
Local Abbreviation Kv := (@AGis.Kv ly cl v).
Local Abbreviation SKv := (@AGis.SKv ly cl v).
Local Abbreviation SSLOTv := (@AGis.SSLOTv ly cl).
Local Abbreviation PBv := (@AGis.PBv ly n cl v kz).
Local Abbreviation Uv := (@AGis.Uv ly cl v kz).
Local Abbreviation SUv := (@AGis.SUv ly cl v kz).
Local Abbreviation E0 := (@AGis.E0 ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaT := (@AGis.EaT ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaC := (@AGis.EaC ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaSB := (@AGis.EaSB ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaTOP := (@AGis.EaTOP ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation Er := (@AGis.Er ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation E2 := (@AGis.E2 ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation E1 := (@AGis.E1 ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation E10 := (@AGis.E10 ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaP := (@AGis.EaP ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaK := (@AGis.EaK ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaSSLOT := (@AGis.EaSSLOT ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaPB := (@AGis.EaPB ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation EaU := (@AGis.EaU ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz).
Local Abbreviation WINT := (@AGis.WINT ly cl).
Local Abbreviation PBW := (@AGis.PBW ly n cl v kz).
Local Abbreviation WIN := (@AGis.WIN ly regs0 n cl v kz).
Hypotheses (Hcl : 1 <= cl <= 31) (Hv : 0 <= v /\ 16 * v + 2 ^ 16 <= 2 ^ 32) (Hcnt : 1 <= cnt <= 16) (Hjb : 0 <= jb <= 255).
Hypothesis Hv2 : v mod 2 = 0.
Hypothesis LY : layout_ok ly.
Hypothesis IMG : img_cover ly.
Hypothesis Hn : getr regs0 10 = w64 n.
Hypothesis Htp : getr regs0 4 = w64 TFIB_TP.
Hypothesis Hra : YK0s.ret_ok (getr regs0 1).
Hypothesis Hra4096 : 4096 <= bv_unsigned (getr regs0 1).
Hypothesis Hsp : ly_stk_lo ly + AFSTACK <= sp0 /\ ly_bot ly < sp0 /\ sp0 <= ly_stk_hi ly /\ sp0 mod 16 = 0.
Hypothesis Htrlen : (1 <= length tr <= 30)%nat.
Hypothesis Hso : sp0 <= SOv /\ SOv + 16 <= ly_stk_hi ly /\ SOv mod 8 = 0.
Hypothesis Hbp : sp0 <= BPv /\ BPv + 8 * 30 <= ly_stk_hi ly /\ BPv mod 8 = 0.
(* The allocator instance (atom aINST = register 11 of the virtual regs0) lies in the image, below the depot. *)
Hypothesis Hinst : TFIB_IMG_LO <= bv_unsigned (getr regs0 11) /\ bv_unsigned (getr regs0 11) + 0xe60 <= 0x173208.
Local Abbreviation DZONE := (@AGis.DZONE ly).
Variable DPOST : Z -> (word -> option byte) -> Prop.
Hypothesis HKpres : forall a, Kv <= a < Kv + RZ + R8v -> apresent (w_H W) mem0 a.
Local Abbreviation Kv_range := (@AGis.Kv_range ly regs0 mem0 n tr cl v kz Hcl Hv Hv2 Htrlen DPOST).
Local Abbreviation high_facts := (@AGis.high_facts _ ly regs0 mem0 n tr v kz Hv LY IMG Htrlen DPOST).
Local Abbreviation blocks_facts := (@AGis.blocks_facts _ ly LY IMG).
Local Abbreviation off_T := (@AGis.off_T _ ly regs0 mem0 n tr v kz Hv LY IMG Htrlen DPOST).
Local Abbreviation off_C := (@AGis.off_C _ ly regs0 mem0 n tr v kz Hv LY IMG Htrlen DPOST).
Local Abbreviation off_NB := (@AGis.off_NB _ ly LY IMG).
Local Abbreviation off_SB := (@AGis.off_SB _ ly LY IMG).
Ltac off_by tac :=
first [ apply off_img_high; tac
| apply off_T; unfold kThreadObjSize; tac
| apply off_C; tac
| apply off_NB; unfold kNodesBlockSize; tac
| apply off_SB; unfold kStoreBlockSize; tac
| unfold off_img; unfold TFIB_IMG_LO; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; tac ].
Hypothesis Hkz : 1 <= kz <= 6.
Hypothesis Nrange : rz_lo kz <= n <= rz_hi kz.
Local Abbreviation RZ_facts := (@AGis.RZ_facts n kz Hkz Nrange).
Local Abbreviation RZ_num := (@AGis.RZ_num n kz Hkz Nrange).
Ltac numconst ::= (ceil; unfold zone3, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize,
t_cache, t_unwinding, t_stats, AFSTACK, TFIB_IMG_END, TFIB_IMG_LO, kLowShadowBeg, UNW_STK, BST_SIZE, DEP_STK in * ); try pose proof RZ_num as RZN.
Local Abbreviation derived_ranges := (@AGis.derived_ranges _ ly regs0 mem0 n tr cl cnt v kz Hcl Hv Hcnt Hv2 LY IMG Htrlen DPOST Hkz Nrange).
Local Abbreviation WIN1 := (@AGis.WIN1 ly regs0 n cl v kz).
Local Abbreviation WIN1_WIN := (@AGis.WIN1_WIN ly regs0 mem0 n tr cl v kz Htrlen DPOST).
Local Abbreviation frame_WIN1 := (@AGis.frame_WIN1 _ ly regs0 mem0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz Hcl Hv Hcnt Hv2 LY IMG Htrlen DPOST Hkz Nrange).
Local Abbreviation stack_ivs := (@AGis.stack_ivs _ ly regs0 mem0 n tr v kz Hv LY Hsp Htrlen Hbp DPOST).
Local Abbreviation DZONE_disj := (@AGis.DZONE_disj _ ly regs0 mem0 n tr cl cnt v kz Hcl Hv Hcnt Hv2 LY IMG Hsp Htrlen Hso Hbp DPOST Hkz Nrange).
Local Abbreviation at_S2 := (@AGis.at_S2 _ W ly regs0 mem0 md0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz DPOST).
Local Abbreviation at_RET0 := (@AGc0.at_RET0 _ W ly regs0 mem0 md0 n cl cnt v jb kz DPOST).
Ltac frame_acc HE :=
match goal with
| MEQ : (forall x : word, ~ WIN1 ?odd (bv_unsigned x) -> ?m1 x = ?mb x), HFx : frame_of ?E ?rs ?m1 ?m2 |- _ =>
let MEQ' := fresh "MEQ" in
assert (MEQ' : forall x : word, ~ WIN1 odd (bv_unsigned x) -> m2 x = mb x)
by (intros x Hx; transitivity (m1 x); [exact (frame_WIN1 odd E rs m1 m2 HE ltac:(vm_compute; reflexivity) HFx x Hx) | exact (MEQ x Hx)]);
clear MEQ HFx; rename MEQ' into MEQ
end.
Local Ltac addr_tac :=
cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi];
rewrite ?EaT, ?EaC, ?EaTOP, ?EaSB, ?E2; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, w64, ly_bot, kStackSpan, t_unwinding, t_cache, t_stats, TFIB_IMG_END, UNW_STK, BST_SIZE, AFSTACK, IFRAME, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *;
rewrite ?unsigned_lit_small by zlia; zlia.
(* The scratch window below Allocate's entry sp covers the whole stack part (regions 0 / 2, odd: 1 / 3). *)
Local Ltac stack_pres En HEn HS :=
intros a Ha; pose proof Hsp as (Hlo_ & Hbot_ & Hhi_ & Hal_); pose proof (lo_top ly LY) as (T1' & T2' & T3' & T4' & T5' & T6' & T7');
assert (Ra : 0 <= a < 2 ^ 64) by (clear - Ha Hlo_ Hhi_ T4' T7'; addr_tac);
destruct (Z_lt_le_dec a (sp0 - 128)) as [H1|H1];
[ eapply (st_ok_window_apresent_off (w_H W) En _ _ 0 _ a HS); [reflexivity | clear - Ha Ra H1 Hlo_ Hhi_ T4' T7' HEn; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn 2%nat (ltHAV 2 eq_refl)), E2; addr_tac | off_by ltac:(addr_tac)]
| eapply (st_ok_window_apresent_off (w_H W) En _ _ 2 _ a HS); [reflexivity | clear - Ha Ra H1 Hlo_ Hhi_ T4' T7' HEn; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn 2%nat (ltHAV 2 eq_refl)), E2; addr_tac | off_by ltac:(addr_tac)] ].
Local Ltac stack_pres_odd En HEn HS :=
intros a Ha; pose proof Hsp as (Hlo_ & Hbot_ & Hhi_ & Hal_); pose proof (lo_top ly LY) as (T1' & T2' & T3' & T4' & T5' & T6' & T7');
assert (Ra : 0 <= a < 2 ^ 64) by (clear - Ha Hlo_ Hhi_ T4' T7'; addr_tac);
destruct (Z_lt_le_dec a (sp0 - 128)) as [H1|H1];
[ eapply (st_ok_window_apresent_off (w_H W) En _ _ 1 _ a HS); [reflexivity | clear - Ha Ra H1 Hlo_ Hhi_ T4' T7' HEn; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn 2%nat (ltHAV 2 eq_refl)), E2; addr_tac | off_by ltac:(addr_tac)]
| eapply (st_ok_window_apresent_off (w_H W) En _ _ 3 _ a HS); [reflexivity | clear - Ha Ra H1 Hlo_ Hhi_ T4' T7' HEn; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn 2%nat (ltHAV 2 eq_refl)), E2; addr_tac | off_by ltac:(addr_tac)] ].
(* From at_S2 SS_Se / SS_So to the can_fill test at 0x31940 (AGi0.st_T, then the test): the SSLOT pin at 0x31930. *)
Local Ltac sslot_pin HS HEn DR LF :=
apply (st_ok_pin_regU _ _ _ 10%bv (SOff aSSLOT 0)) in HS;
[ | intros X; discriminate
| clear - T SB HEn DR LF Hcl Hcnt Hv Hn; pin_zev; unfold aSSLOT;
rewrite (HEn 52%nat (ltHAV 52 eq_refl)), (HEn 32%nat (ltHAV 32 eq_refl)), (HEn 39%nat (ltHAV 39 eq_refl)), EaSSLOT, EaT, (eq_refl : ew E0 39 = w64 cl);
unfold w64; unfold SSLOTv in *; numconst; rewrite !unsigned_lit_small by zlia; zcanon_simp; land_lits; rewrite ?Z.shiftl_mul_pow2 by zlia;
change (2 ^ 3) with 8; zcanon_simp; zlia ];
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
(* can_fill (atom 15) is tested at 0x31940; this is the cf = 0 arm (AGi0.st_V0), which jumps to 0x31978. *)
Lemma seg2cf0_even : getr regs0 15 = w64 0 -> n mod 8 = 0 -> forall z W0 c, at_S2 false SS_Se z W0 c -> SRr tfibsegs W0 c (at_RET0 false z).
Proof.
intros Hcf0 H8 z W0 c (-> & ms & mat & En & mem2 & -> & HEn & HS & HDP & PRD2 & EQD & M0 & PRS & SRZ & PBV). pose proof Hwx_tfa as Hwx.
pose proof Hsp as (Hlo & Hbot & Hhi & Hal). pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
pose proof derived_ranges as DR. pose proof high_facts as LF. pose proof RZ_facts as (RF1 & RF2 & RF3 & RF4 & RF5 & RF6).
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, t_cache, t_unwinding in DR, LF.
assert (Usp : 0 <= bv_unsigned (getr regs0 2) < 2 ^ 64) by apply u64_range.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) En _ _ HS eq_refl) as Hshape; cbn [ss_pc] in Hshape;
lazymatch type of Hshape with _ = mkst _ (Z_to_bv 64 (ss_pc ?s)) _ _ => let p := eval vm_compute in (ss_pc s) in change (ss_pc s) with p in Hshape | _ => idtac end.
rewrite Hshape in HS. rewrite Hshape. set (mem1 := ms_mem ms) in *.
assert (MEQ : forall x : word, ~ WIN1 false (bv_unsigned x) -> mem1 x = mem1 x) by (intros; reflexivity).
srr_run_sh tfibtbl_rtA_ok HS. frame_acc HEn.
sslot_pin HS HEn DR LF.
srr_run_sh tfibtbl_rtA_ok HS. frame_acc HEn.
assert (En15 : U En (SOff 15 0) = 0) by (clear - HEn Hcf0; apply U_atom; [rewrite (HEn 15%nat (ltHAV 15 eq_refl)), (Er 15 15%bv eq_refl); exact Hcf0 | zlia]).
srr_branch_sh tfibtbl_rtA_ok HS.
2:{ exfalso. clear - Hc En15. rewrite branch_eq_U, En15, (U_lit En 0) in Hc by zlia. first [discriminate Hc | apply Z.eqb_neq in Hc; zlia]. }
clear Hc. srr_run_sh tfibtbl_rtA_ok HS. frame_acc HEn.
pose proof Kv_range as HKR. pose proof blocks_facts as (_ & _ & _ & _ & _ & _ & _ & _ & PT). unfold zdisjoint in PT. cbn [fst snd] in PT.
assert (EU : U En (SOff 60 (-16)) = Uv - 16).
{ clear - HEn DR. rewrite U_SOff, (HEn 60%nat (ltHAV 60 eq_refl)), EaU. unfold w64. rewrite unsigned_lit_small by zlia. apply zcanon_id. unfold M64. zlia. }
assert (EK : U En (SOff 45 0) = Kv) by (clear - HEn DR; apply U_atom; [rewrite (HEn 45%nat (ltHAV 45 eq_refl)); exact EaK | zlia]).
assert (EK16 : U En (SOff 45 16) = Kv + 16).
{ clear - HEn DR. rewrite U_SOff, (HEn 45%nat (ltHAV 45 eq_refl)), EaK. unfold w64. rewrite unsigned_lit_small by zlia. apply zcanon_id. unfold M64. zlia. }
srr_branch_sh tfibtbl_rtA_ok HS.
{ exfalso. clear - Hc EU EK DR. rewrite branch_eq_U, EU, EK in Hc. apply Z.eqb_eq in Hc. zlia. }
clear Hc. srr_run_sh tfibtbl_rtA_ok HS. frame_acc HEn.
srr_branch_sh tfibtbl_rtA_ok HS.
{ exfalso. clear - Hc EU EK16 DR. rewrite branch_ltu_U, EU, EK16 in Hc. apply Z.ltb_lt in Hc. zlia. }
clear Hc. srr_run_sh tfibtbl_rtA_ok HS. frame_acc HEn.
eapply (SRr_ret_at tfibsegs tfibtbl_rtA tfibtbl_rtA_ok Hwx W En); [exact HS | reflexivity | vm_compute; reflexivity |].
intros matZ. match type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msZ end.
rreg HS (1%bv : bv 5) RZ1. rewrite (HEn 1%nat (ltHAV 1 eq_refl)), E1 in RZ1. rewrite RZ1. unfold YK0s.ret_ok in Hra. rewrite Hra.
pose proof (DZONE_disj false) as DZD.
assert (PCH1 : forall a, ~ WIN1 false a -> 0 <= a < 2 ^ 64 -> apresent (w_H W) mem1 a -> apresent (w_H W) (ms_mem msZ) a).
{ intros a N1' Ra Hp. apply (apresent_same (w_H W) mem1); [apply MEQ; rewrite unsigned_lit_small by exact Ra; exact N1' | exact Hp]. }
split; [reflexivity|]. exists (ms_regs msZ), (ms_mem msZ), matZ. split; [reflexivity|].
split. { rreg HS (10%bv : bv 5) R; rewrite R, (HEn 60%nat (ltHAV 60 eq_refl)), EaU. unfold w64. rewrite ?Zbv_add_unsigned, ?Z.add_0_r. first [reflexivity | f_equal; clear - DR; zlia]. }
split. { intros r Hr. cbn [In] in Hr.
repeat match type of Hr with _ \/ _ => destruct Hr as [<-|Hr] | False => destruct Hr end;
lazymatch goal with |- getr _ ?r = _ =>
let R := fresh "R" in rreg HS r R; rewrite R;
let k := eval cbv in (Z.to_nat (bv_unsigned r)) in
first [ rewrite (HEn k (ltHAV k eq_refl)); symmetry; exact (Er k r eq_refl) | symmetry; exact Htp ] end. }
split. { exists mem2. split; [exact HDP|]. split; [exact PRD2|].
intros x Hx. destruct (DZD _ Hx) as (N0 & N2' & N3 & N4). rewrite (MEQ x) by (intros H1; apply N0, WIN1_WIN, H1). apply EQD, Hx. }
split. { intros x N0 ND N2' N3. rewrite (MEQ x) by (intros H1; apply N0, WIN1_WIN, H1). apply M0; assumption. }
split. { stack_pres En HEn HS. }
split. { intros a Ha.
assert (Ra : 0 <= a < 2 ^ 64) by (clear - Ha DR LF HKR; unfold WINT, PBW in Ha; numconst; destruct Ha as [Ha|[Ha|[_ Ha]]]; zlia).
destruct Ha as [Hw|[Hk|Hpb]].
- unfold WINT in Hw. destruct Hw as [Hw|[Hw|[Hw|Hw]]].
+ eapply (st_ok_window_apresent_off (w_H W) En _ _ 45%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn 40%nat (ltHAV 40 eq_refl)), EaP; unfold w64; rewrite unsigned_lit_small by (clear - DR LF; numconst; zlia); zlia | off_by ltac:(clear - Hw DR LF; numconst; zlia)].
+ destruct (Z_lt_le_dec a (T + 2800)) as [H28|H28].
* eapply (st_ok_window_apresent_off (w_H W) En _ _ 41%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn 32%nat (ltHAV 32 eq_refl)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - DR LF; numconst; zlia); unfold T in *; zlia | off_by ltac:(clear - Hw DR LF; numconst; zlia)].
* eapply (st_ok_window_apresent_off (w_H W) En _ _ 43%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn 32%nat (ltHAV 32 eq_refl)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - DR LF; numconst; zlia); unfold T in *; zlia | off_by ltac:(clear - Hw H28 DR LF; numconst; zlia)].
+ eapply (st_ok_window_apresent_off (w_H W) En _ _ 44%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn 52%nat (ltHAV 52 eq_refl)), EaSSLOT; unfold w64; rewrite unsigned_lit_small by (clear - DR LF; numconst; zlia); zlia | off_by ltac:(clear - Hw DR LF; numconst; zlia)].
+ eapply (st_ok_window_apresent_off (w_H W) En _ _ 42%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn 32%nat (ltHAV 32 eq_refl)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - DR LF; numconst; zlia); unfold T in *; numconst; zlia | off_by ltac:(clear - Hw DR LF; numconst; zlia)].
- destruct (Z_lt_le_dec a (Kv + 16)) as [H1|H1].
+ eapply (st_ok_window_apresent_off (w_H W) En _ _ 48%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn 45%nat (ltHAV 45 eq_refl)), EaK; unfold w64; rewrite unsigned_lit_small by (clear - DR LF; numconst; zlia); zlia | off_by ltac:(clear - Hk H1 DR LF HKR; numconst; zlia)].
+ destruct (Z_lt_le_dec a (Uv - 16)) as [H2|H2]; [|destruct (Z_lt_le_dec a Uv) as [H3|H3]].
*
apply PCH1; [pose proof stack_ivs as SI; clear - Hk H1 H2 DR LF HKR Hlo T7 PT SI; unfold WIN1, WINT, PBW, IFRAME; numconst; zlia | exact Ra |].
apply (apresent_same (w_H W) mem0); [apply M0; rewrite unsigned_lit_small by exact Ra | apply HKpres; clear - Hk H1 H2 DR; numconst; zlia].
-- pose proof stack_ivs as SI; clear - Hk H1 H2 DR LF HKR Hlo T7 PT SI; unfold WIN, WINT, PBW; numconst; zlia.
-- pose proof blocks_facts as BF. clear - Hk H1 H2 DR LF HKR Hlo T7 BF; unfold zdisjoint in BF; cbn [fst snd] in BF; unfold DZONE; numconst; zlia.
-- clear - Hk H1 H2 DR; numconst; zlia.
* eapply (st_ok_window_apresent_off (w_H W) En _ _ 49%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn 60%nat (ltHAV 60 eq_refl)), EaU; unfold w64; rewrite unsigned_lit_small by (clear - DR LF; numconst; zlia); zlia | off_by ltac:(clear - Hk H2 H3 DR LF HKR; numconst; zlia)].
*
apply PCH1; [pose proof stack_ivs as SI; clear - Hk H3 DR LF HKR Hlo T7 PT SI; unfold WIN1, WINT, PBW, IFRAME; numconst; zlia | exact Ra |].
apply (apresent_same (w_H W) mem0); [apply M0; rewrite unsigned_lit_small by exact Ra | apply HKpres; clear - Hk H3 DR; numconst; zlia].
-- pose proof stack_ivs as SI; clear - Hk H3 DR LF HKR Hlo T7 PT SI; unfold WIN, WINT, PBW; numconst; zlia.
-- pose proof blocks_facts as BF. clear - Hk H3 DR LF HKR Hlo T7 BF; unfold zdisjoint in BF; cbn [fst snd] in BF; unfold DZONE; numconst; zlia.
-- clear - Hk H3 DR; numconst; zlia.
- destruct Hpb as [Hpb _]. discriminate Hpb. }
cbv zeta.
assert (RK : 0 <= Kv /\ Kv + 2 ^ 16 < 2 ^ 64) by (clear - DR; numconst; zlia).
split. { memv HS 48%nat 0%nat; [cbn [base_val YP09.r_base]; rewrite (HEn 45%nat (ltHAV 45 eq_refl)), EaK; unfold w64; rewrite unsigned_lit_small by zlia; zlia | reflexivity | zlia]. }
split. { memv HS 48%nat 1%nat; [cbn [base_val YP09.r_base]; rewrite (HEn 45%nat (ltHAV 45 eq_refl)), EaK; unfold w64; rewrite unsigned_lit_small by zlia; zlia
| cbn [sv_denot]; rewrite (HEn 60%nat (ltHAV 60 eq_refl)), EaU; unfold w64; rewrite Zbv_add_unsigned; f_equal; clear - DR; zlia | clear - DR; numconst; zlia]. }
split. { memv HS 49%nat 0%nat; [cbn [base_val YP09.r_base]; rewrite (HEn 60%nat (ltHAV 60 eq_refl)), EaU; unfold w64; rewrite unsigned_lit_small by (clear - DR; numconst; zlia); clear - DR; zlia | reflexivity | zlia]. }
split. { pose proof (hdr_byte1_ok jb Hjb) as [B1 B2].
memv HS 49%nat 1%nat; [cbn [base_val YP09.r_base]; rewrite (HEn 60%nat (ltHAV 60 eq_refl)), EaU; unfold w64; rewrite unsigned_lit_small by (clear - DR; numconst; zlia); clear - DR; zlia | | zlia].
lazymatch goal with |- sv_denot ?E ?t = _ =>
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E t)); f_equal; change (bv_unsigned (sv_denot E t)) with (U E t); rewrite (U_zev E t eq_refl) end.
cbn [zev zalu_raw]. unfold rho_of. rewrite (HEn 46%nat (ltHAV 46 eq_refl)), (eq_refl : ew E0 46 = w64 jb). unfold w64. rewrite unsigned_lit_small by zlia.
unfold hdr_byte1. reflexivity. }
split. { memv HS 49%nat 4%nat; [cbn [base_val YP09.r_base]; rewrite (HEn 60%nat (ltHAV 60 eq_refl)), EaU; unfold w64; rewrite unsigned_lit_small by (clear - DR; numconst; zlia); clear - DR; zlia | | zlia].
lazymatch goal with |- sv_denot ?E ?t = _ =>
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E t)); f_equal; change (bv_unsigned (sv_denot E t)) with (U E t); rewrite (U_zev E t eq_refl) end.
cbn [zev zalu_raw]. unfold rho_of. rewrite (HEn 10%nat (ltHAV 10 eq_refl)), E10, Hn. unfold w64. rewrite unsigned_lit_small by zlia.
zcanon_simp. land_lits. rewrite Z.shiftr_div_pow2 by zlia. rewrite Z.div_small by zlia. reflexivity. }
split. { memv HS 49%nat 3%nat; [cbn [base_val YP09.r_base]; rewrite (HEn 60%nat (ltHAV 60 eq_refl)), EaU; unfold w64; rewrite unsigned_lit_small by (clear - DR; numconst; zlia); clear - DR; zlia
| cbn [sv_denot]; rewrite (HEn 10%nat (ltHAV 10 eq_refl)), E10, Hn; unfold w64; rewrite ?Zbv_add_unsigned, ?Z.add_0_r; f_equal; zlia | zlia]. }
split. { memv HS 45%nat 0%nat; [cbn [base_val YP09.r_base]; rewrite (HEn 40%nat (ltHAV 40 eq_refl)), EaP; unfold w64; rewrite unsigned_lit_small by (clear - DR LF; numconst; zlia); zlia
| cbn [sv_denot]; rewrite (HEn 41%nat (ltHAV 41 eq_refl)), (eq_refl : ew E0 41 = w64 cnt); unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia | zlia]. }
split. { memv HS 42%nat 0%nat; [cbn [base_val YP09.r_base]; rewrite (HEn 32%nat (ltHAV 32 eq_refl)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - DR LF; numconst; zlia); unfold T; numconst; zlia | reflexivity | zlia]. }
split. { intros x Hx. pose proof (u64_range x) as Rx.
assert (N1' : ~ WIN1 false (bv_unsigned x)).
{ pose proof stack_ivs as SI. clear - Hx DR LF HKR Hlo T7 SI. unfold WIN1, WINT, PBW, IFRAME. numconst. zlia. }
rewrite (MEQ x N1'). apply SRZ, Hx. }
split. { intros HH; discriminate HH. }
(* The block keeps its contents: it lies outside every write window of the run. *)
intros x Hx. pose proof (u64_range x) as Rx.
assert (N1' : ~ WIN1 false (bv_unsigned x)).
{ pose proof stack_ivs as SI. clear - Hx DR LF HKR Hlo T7 SI PT. unfold WIN1, WINT, PBW, IFRAME. numconst. zlia. }
rewrite (MEQ x N1'). apply M0.
- pose proof stack_ivs as SI. clear - Hx DR LF HKR Hlo T7 SI PT. unfold WIN, WINT, PBW. numconst. zlia.
- pose proof blocks_facts as BF. clear - Hx DR LF Hlo T7 BF HKR. unfold zdisjoint in BF. cbn [fst snd] in BF. unfold DZONE. numconst. zlia.
- clear - Hx DR. numconst. zlia.
Qed.
Lemma seg2cf0_odd : getr regs0 15 = w64 0 -> n mod 8 <> 0 -> forall z W0 c, at_S2 true SS_So z W0 c -> SRr tfibsegs W0 c (at_RET0 true z).
Proof.
intros Hcf0 H8 z W0 c (-> & ms & mat & En & mem2 & -> & HEn & HS & HDP & PRD2 & EQD & M0 & PRS & SRZ & PBV). pose proof Hwx_tfa as Hwx.
pose proof Hsp as (Hlo & Hbot & Hhi & Hal). pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
pose proof derived_ranges as DR. pose proof high_facts as LF. pose proof RZ_facts as (RF1 & RF2 & RF3 & RF4 & RF5 & RF6).
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, t_cache, t_unwinding in DR, LF.
assert (Usp : 0 <= bv_unsigned (getr regs0 2) < 2 ^ 64) by apply u64_range.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) En _ _ HS eq_refl) as Hshape; cbn [ss_pc] in Hshape;
lazymatch type of Hshape with _ = mkst _ (Z_to_bv 64 (ss_pc ?s)) _ _ => let p := eval vm_compute in (ss_pc s) in change (ss_pc s) with p in Hshape | _ => idtac end.
rewrite Hshape in HS. rewrite Hshape. set (mem1 := ms_mem ms) in *.
assert (MEQ : forall x : word, ~ WIN1 true (bv_unsigned x) -> mem1 x = mem1 x) by (intros; reflexivity).
srr_run_sh tfibtbl_rtA_ok HS. frame_acc HEn.
sslot_pin HS HEn DR LF.
srr_run_sh tfibtbl_rtA_ok HS. frame_acc HEn.
assert (En15 : U En (SOff 15 0) = 0) by (clear - HEn Hcf0; apply U_atom; [rewrite (HEn 15%nat (ltHAV 15 eq_refl)), (Er 15 15%bv eq_refl); exact Hcf0 | zlia]).
srr_branch_sh tfibtbl_rtA_ok HS.
2:{ exfalso. clear - Hc En15. rewrite branch_eq_U, En15, (U_lit En 0) in Hc by zlia. first [discriminate Hc | apply Z.eqb_neq in Hc; zlia]. }
clear Hc. srr_run_sh tfibtbl_rtA_ok HS. frame_acc HEn.
pose proof Kv_range as HKR. pose proof blocks_facts as (_ & _ & _ & _ & _ & _ & _ & _ & PT). unfold zdisjoint in PT. cbn [fst snd] in PT.
assert (EU : U En (SOff 60 (-16)) = Uv - 16).
{ clear - HEn DR. rewrite U_SOff, (HEn 60%nat (ltHAV 60 eq_refl)), EaU. unfold w64. rewrite unsigned_lit_small by zlia. apply zcanon_id. unfold M64. zlia. }
assert (EK : U En (SOff 45 0) = Kv) by (clear - HEn DR; apply U_atom; [rewrite (HEn 45%nat (ltHAV 45 eq_refl)); exact EaK | zlia]).
assert (EK16 : U En (SOff 45 16) = Kv + 16).
{ clear - HEn DR. rewrite U_SOff, (HEn 45%nat (ltHAV 45 eq_refl)), EaK. unfold w64. rewrite unsigned_lit_small by zlia. apply zcanon_id. unfold M64. zlia. }
srr_branch_sh tfibtbl_rtA_ok HS.
{ exfalso. clear - Hc EU EK DR. rewrite branch_eq_U, EU, EK in Hc. apply Z.eqb_eq in Hc. zlia. }
clear Hc. srr_run_sh tfibtbl_rtA_ok HS. frame_acc HEn.
srr_branch_sh tfibtbl_rtA_ok HS.
{ exfalso. clear - Hc EU EK16 DR. rewrite branch_ltu_U, EU, EK16 in Hc. apply Z.ltb_lt in Hc. zlia. }
clear Hc. srr_run_sh tfibtbl_rtA_ok HS. frame_acc HEn.
eapply (SRr_ret_at tfibsegs tfibtbl_rtA tfibtbl_rtA_ok Hwx W En); [exact HS | reflexivity | vm_compute; reflexivity |].
intros matZ. match type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msZ end.
rreg HS (1%bv : bv 5) RZ1. rewrite (HEn 1%nat (ltHAV 1 eq_refl)), E1 in RZ1. rewrite RZ1. unfold YK0s.ret_ok in Hra. rewrite Hra.
pose proof (DZONE_disj true) as DZD.
assert (PCH1 : forall a, ~ WIN1 true a -> 0 <= a < 2 ^ 64 -> apresent (w_H W) mem1 a -> apresent (w_H W) (ms_mem msZ) a).
{ intros a N1' Ra Hp. apply (apresent_same (w_H W) mem1); [apply MEQ; rewrite unsigned_lit_small by exact Ra; exact N1' | exact Hp]. }
split; [reflexivity|]. exists (ms_regs msZ), (ms_mem msZ), matZ. split; [reflexivity|].
split. { rreg HS (10%bv : bv 5) R; rewrite R, (HEn 60%nat (ltHAV 60 eq_refl)), EaU. unfold w64. rewrite ?Zbv_add_unsigned, ?Z.add_0_r. first [reflexivity | f_equal; clear - DR; zlia]. }
split. { intros r Hr. cbn [In] in Hr.
repeat match type of Hr with _ \/ _ => destruct Hr as [<-|Hr] | False => destruct Hr end;
lazymatch goal with |- getr _ ?r = _ =>
let R := fresh "R" in rreg HS r R; rewrite R;
let k := eval cbv in (Z.to_nat (bv_unsigned r)) in
first [ rewrite (HEn k (ltHAV k eq_refl)); symmetry; exact (Er k r eq_refl) | symmetry; exact Htp ] end. }
split. { exists mem2. split; [exact HDP|]. split; [exact PRD2|].
intros x Hx. destruct (DZD _ Hx) as (N0 & N2' & N3 & N4). rewrite (MEQ x) by (intros H1; apply N0, WIN1_WIN, H1). apply EQD, Hx. }
split. { intros x N0 ND N2' N3. rewrite (MEQ x) by (intros H1; apply N0, WIN1_WIN, H1). apply M0; assumption. }
split. { stack_pres_odd En HEn HS. }
split. { intros a Ha.
assert (Ra : 0 <= a < 2 ^ 64) by (clear - Ha DR LF HKR; unfold WINT, PBW in Ha; numconst; destruct Ha as [Ha|[Ha|[_ Ha]]]; zlia).
destruct Ha as [Hw|[Hk|Hpb]].
- unfold WINT in Hw. destruct Hw as [Hw|[Hw|[Hw|Hw]]].
+ eapply (st_ok_window_apresent_off (w_H W) En _ _ 46%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn 40%nat (ltHAV 40 eq_refl)), EaP; unfold w64; rewrite unsigned_lit_small by (clear - DR LF; numconst; zlia); zlia | off_by ltac:(clear - Hw DR LF; numconst; zlia)].
+ destruct (Z_lt_le_dec a (T + 2800)) as [H28|H28].
* eapply (st_ok_window_apresent_off (w_H W) En _ _ 42%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn 32%nat (ltHAV 32 eq_refl)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - DR LF; numconst; zlia); unfold T in *; zlia | off_by ltac:(clear - Hw DR LF; numconst; zlia)].
* eapply (st_ok_window_apresent_off (w_H W) En _ _ 44%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn 32%nat (ltHAV 32 eq_refl)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - DR LF; numconst; zlia); unfold T in *; zlia | off_by ltac:(clear - Hw H28 DR LF; numconst; zlia)].
+ eapply (st_ok_window_apresent_off (w_H W) En _ _ 45%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn 52%nat (ltHAV 52 eq_refl)), EaSSLOT; unfold w64; rewrite unsigned_lit_small by (clear - DR LF; numconst; zlia); zlia | off_by ltac:(clear - Hw DR LF; numconst; zlia)].
+ eapply (st_ok_window_apresent_off (w_H W) En _ _ 43%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn 32%nat (ltHAV 32 eq_refl)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - DR LF; numconst; zlia); unfold T in *; numconst; zlia | off_by ltac:(clear - Hw DR LF; numconst; zlia)].
- destruct (Z_lt_le_dec a (Kv + 16)) as [H1|H1].
+ eapply (st_ok_window_apresent_off (w_H W) En _ _ 49%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn 45%nat (ltHAV 45 eq_refl)), EaK; unfold w64; rewrite unsigned_lit_small by (clear - DR LF; numconst; zlia); zlia | off_by ltac:(clear - Hk H1 DR LF HKR; numconst; zlia)].
+ destruct (Z_lt_le_dec a (Uv - 16)) as [H2|H2]; [|destruct (Z_lt_le_dec a Uv) as [H3|H3]].
*
apply PCH1; [pose proof stack_ivs as SI; clear - Hk H1 H2 DR LF HKR Hlo T7 PT SI; unfold WIN1, WINT, PBW, IFRAME; numconst; zlia | exact Ra |].
apply (apresent_same (w_H W) mem0); [apply M0; rewrite unsigned_lit_small by exact Ra | apply HKpres; clear - Hk H1 H2 DR; numconst; zlia].
-- pose proof stack_ivs as SI; clear - Hk H1 H2 DR LF HKR Hlo T7 PT SI; unfold WIN, WINT, PBW; numconst; zlia.
-- pose proof blocks_facts as BF. clear - Hk H1 H2 DR LF HKR Hlo T7 BF; unfold zdisjoint in BF; cbn [fst snd] in BF; unfold DZONE; numconst; zlia.
-- clear - Hk H1 H2 DR; numconst; zlia.
* eapply (st_ok_window_apresent_off (w_H W) En _ _ 50%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn 60%nat (ltHAV 60 eq_refl)), EaU; unfold w64; rewrite unsigned_lit_small by (clear - DR LF; numconst; zlia); zlia | off_by ltac:(clear - Hk H2 H3 DR LF HKR; numconst; zlia)].
*
apply PCH1; [pose proof stack_ivs as SI; clear - Hk H3 DR LF HKR Hlo T7 PT SI; unfold WIN1, WINT, PBW, IFRAME; numconst; zlia | exact Ra |].
apply (apresent_same (w_H W) mem0); [apply M0; rewrite unsigned_lit_small by exact Ra | apply HKpres; clear - Hk H3 DR; numconst; zlia].
-- pose proof stack_ivs as SI; clear - Hk H3 DR LF HKR Hlo T7 PT SI; unfold WIN, WINT, PBW; numconst; zlia.
-- pose proof blocks_facts as BF. clear - Hk H3 DR LF HKR Hlo T7 BF; unfold zdisjoint in BF; cbn [fst snd] in BF; unfold DZONE; numconst; zlia.
-- clear - Hk H3 DR; numconst; zlia.
- destruct Hpb as [_ Hpb]. eapply (st_ok_window_apresent_off (w_H W) En _ _ 0%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; unfold aPB; rewrite (HEn 54%nat (ltHAV 54 eq_refl)), EaPB; unfold w64; rewrite unsigned_lit_small by (clear - DR; numconst; zlia); zlia | off_by ltac:(clear - Hpb DR; numconst; zlia)]. }
cbv zeta.
assert (RK : 0 <= Kv /\ Kv + 2 ^ 16 < 2 ^ 64) by (clear - DR; numconst; zlia).
split. { memv HS 49%nat 0%nat; [cbn [base_val YP09.r_base]; rewrite (HEn 45%nat (ltHAV 45 eq_refl)), EaK; unfold w64; rewrite unsigned_lit_small by zlia; zlia | reflexivity | zlia]. }
split. { memv HS 49%nat 1%nat; [cbn [base_val YP09.r_base]; rewrite (HEn 45%nat (ltHAV 45 eq_refl)), EaK; unfold w64; rewrite unsigned_lit_small by zlia; zlia
| cbn [sv_denot]; rewrite (HEn 60%nat (ltHAV 60 eq_refl)), EaU; unfold w64; rewrite Zbv_add_unsigned; f_equal; clear - DR; zlia | clear - DR; numconst; zlia]. }
split. { memv HS 50%nat 0%nat; [cbn [base_val YP09.r_base]; rewrite (HEn 60%nat (ltHAV 60 eq_refl)), EaU; unfold w64; rewrite unsigned_lit_small by (clear - DR; numconst; zlia); clear - DR; zlia | reflexivity | zlia]. }
split. { pose proof (hdr_byte1_ok jb Hjb) as [B1 B2].
memv HS 50%nat 1%nat; [cbn [base_val YP09.r_base]; rewrite (HEn 60%nat (ltHAV 60 eq_refl)), EaU; unfold w64; rewrite unsigned_lit_small by (clear - DR; numconst; zlia); clear - DR; zlia | | zlia].
lazymatch goal with |- sv_denot ?E ?t = _ =>
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E t)); f_equal; change (bv_unsigned (sv_denot E t)) with (U E t); rewrite (U_zev E t eq_refl) end.
cbn [zev zalu_raw]. unfold rho_of. rewrite (HEn 46%nat (ltHAV 46 eq_refl)), (eq_refl : ew E0 46 = w64 jb). unfold w64. rewrite unsigned_lit_small by zlia.
unfold hdr_byte1. reflexivity. }
split. { memv HS 50%nat 4%nat; [cbn [base_val YP09.r_base]; rewrite (HEn 60%nat (ltHAV 60 eq_refl)), EaU; unfold w64; rewrite unsigned_lit_small by (clear - DR; numconst; zlia); clear - DR; zlia | | zlia].
lazymatch goal with |- sv_denot ?E ?t = _ =>
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E t)); f_equal; change (bv_unsigned (sv_denot E t)) with (U E t); rewrite (U_zev E t eq_refl) end.
cbn [zev zalu_raw]. unfold rho_of. rewrite (HEn 10%nat (ltHAV 10 eq_refl)), E10, Hn. unfold w64. rewrite unsigned_lit_small by zlia.
zcanon_simp. land_lits. rewrite Z.shiftr_div_pow2 by zlia. rewrite Z.div_small by zlia. reflexivity. }
split. { memv HS 50%nat 3%nat; [cbn [base_val YP09.r_base]; rewrite (HEn 60%nat (ltHAV 60 eq_refl)), EaU; unfold w64; rewrite unsigned_lit_small by (clear - DR; numconst; zlia); clear - DR; zlia
| cbn [sv_denot]; rewrite (HEn 10%nat (ltHAV 10 eq_refl)), E10, Hn; unfold w64; rewrite ?Zbv_add_unsigned, ?Z.add_0_r; f_equal; zlia | zlia]. }
split. { memv HS 46%nat 0%nat; [cbn [base_val YP09.r_base]; rewrite (HEn 40%nat (ltHAV 40 eq_refl)), EaP; unfold w64; rewrite unsigned_lit_small by (clear - DR LF; numconst; zlia); zlia
| cbn [sv_denot]; rewrite (HEn 41%nat (ltHAV 41 eq_refl)), (eq_refl : ew E0 41 = w64 cnt); unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia | zlia]. }
split. { memv HS 43%nat 0%nat; [cbn [base_val YP09.r_base]; rewrite (HEn 32%nat (ltHAV 32 eq_refl)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - DR LF; numconst; zlia); unfold T; numconst; zlia | reflexivity | zlia]. }
split. { intros x Hx. pose proof (u64_range x) as Rx.
assert (N1' : ~ WIN1 true (bv_unsigned x)).
{ pose proof stack_ivs as SI. clear - Hx DR LF HKR Hlo T7 SI. unfold WIN1, WINT, PBW, IFRAME. numconst. zlia. }
rewrite (MEQ x N1'). apply SRZ, Hx. }
split. { intros _.
pose proof (Z.mod_pos_bound n 8 ltac:(zlia)) as M8.
memv HS 0%nat 0%nat; [cbn [base_val YP09.r_base]; rewrite (HEn 54%nat (ltHAV 54 eq_refl)), EaPB; unfold w64; rewrite unsigned_lit_small by (clear - DR LF; numconst; zlia); zlia | | zlia].
lazymatch goal with |- sv_denot ?E ?t = _ =>
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E t)); f_equal; change (bv_unsigned (sv_denot E t)) with (U E t); rewrite (U_zev E t eq_refl) end.
cbn [zev zalu_raw]. unfold rho_of. rewrite (HEn 10%nat (ltHAV 10 eq_refl)), E10, Hn. unfold w64. rewrite unsigned_lit_small by zlia.
zcanon_simp. rewrite land_7_mod by zlia. zcanon_simp. rewrite Z.add_0_r. reflexivity. }
(* The block keeps its contents: it lies outside every write window of the run. *)
intros x Hx. pose proof (u64_range x) as Rx.
assert (N1' : ~ WIN1 true (bv_unsigned x)).
{ pose proof stack_ivs as SI. clear - Hx DR LF HKR Hlo T7 SI PT. unfold WIN1, WINT, PBW, IFRAME. numconst. zlia. }
rewrite (MEQ x N1'). apply M0.
- pose proof stack_ivs as SI. clear - Hx DR LF HKR Hlo T7 SI PT. unfold WIN, WINT, PBW. numconst. zlia.
- pose proof blocks_facts as BF. clear - Hx DR LF Hlo T7 BF HKR. unfold zdisjoint in BF. cbn [fst snd] in BF. unfold DZONE. numconst. zlia.
- clear - Hx DR. numconst. zlia.
Qed.
End e.
End d.
