(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI08 YI0n YI0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0y YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC81 YC4b YC4b.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC9g.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC93.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC1i.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC88 YC5d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Ltac getAM4 := lazymatch goal with A : amalloc04_rule _ _ _ |- _ => A end.
Ltac malloc_siteX HS HJ nval a0tac AG Usp Rctx Hom HSZ MOK :=
let Bv := getB in let L := getLAWS in let T := getTL in let M := getML in let AM := getAM4 in
let HUL := getHUL in let ENV := getENV in
let Rra := fresh "Rra" in let Rsp := fresh "Rsp" in let Rgp := fresh "Rgp" in let Rtp := fresh "Rtp" in let Rs0 := fresh "Rs0" in
prreg HS (1%bv : bv 5) Rra; prreg HS (2%bv : bv 5) Rsp; prreg HS (3%bv : bv 5) Rgp; prreg HS (4%bv : bv 5) Rtp; prreg HS (8%bv : bv 5) Rs0;
pmkst HS; ppcs;
ppcs;
lazymatch type of Usp with _ = ?spv =>
lazymatch type of Rctx with _ = w64 ?ctxv =>
lazymatch type of HJ with ajournal _ _ ?STK ?sp0 ?FP ?ly ?S ?W0 ?mem0 ?md0 ?own ?lyc ?Sc ?Wc (ms_mem ?msX) ?mdc ?kk =>
lazymatch type of Rra with _ = Z_to_bv 64 ?ra =>
let Hnev := fresh "Hnev" in pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & _);
eapply SRr_bind;
[ eapply (AM Wc (ms_regs msX) (ms_mem msX) STK sp0 FP ly S W0 mem0 md0 own
lyc Sc mdc kk nval (spv - 320 - sp0) (Z_to_bv 64 ra) [] HJ);
[ first [ a0tac | match goal with |- ?g => idtac "MSFAIL" g end ]
| first [ exact (proj1 HSZ) | match goal with |- ?g => idtac "MSFAIL" g end ]
| first [ exact (proj2 HSZ) | match goal with |- ?g => idtac "MSFAIL" g end ]
| first [ unfold spZ; rewrite Rsp, ?(AG 2%nat) by lia; rewrite Usp, unsigned_lit_small by lia; lia | match goal with |- ?g => idtac "MSFAIL" g end ]
| first [ exact Hom | match goal with |- ?g => idtac "MSFAIL" g end ]
| first [ lia | match goal with |- ?g => idtac "MSFAIL" g end ]
| first [ lia | match goal with |- ?g => idtac "MSFAIL" g end ]
| first [ rewrite Rgp, ?(AG 3%nat) by lia; lazymatch goal with H : ew _ 3%nat = Z_to_bv 64 (as_gp _) |- _ => rewrite H; reflexivity end | match goal with |- ?g => idtac "MSFAIL" g end ]
| first [ rewrite Rtp, ?(AG 4%nat) by lia; lazymatch goal with H : ew _ 4%nat = Z_to_bv 64 (as_tp _) |- _ => rewrite H; reflexivity end | match goal with |- ?g => idtac "MSFAIL" g end ]
| first [ exact Rra | match goal with |- ?g => idtac "MSFAIL" g end ]
| first [ apply ret_ok_codeptr_v; [lazymatch goal with |- _ <= ?k < _ => try unfold k end; lia | reflexivity] | match goal with |- ?g => idtac "MSFAIL" g end ]
| first [ match goal with H1 : st_nev ?Sb + LZW_EV <= EV_MAX, H2 : LZW_EV = 19 |- _ => clear - Hnev H1 H2; lia end | match goal with |- ?g => idtac "MSFAIL" g end ]
| first [ apply (achain_chain_pre lyc _ (spv - 320) ctxv [] _ (achain_low lyc _ (spv - 320) ctxv ltac:(lia)));
[ unfold spZ; rewrite Rsp, ?(AG 2%nat) by lia; rewrite Usp, unsigned_lit_small by lia; lia
| unfold s0Z; rewrite Rs0, Rctx; apply unsigned_lit_small; lia
| unfold raZ; rewrite Rra, unsigned_lit_small by lia; lia ] | match goal with |- ?g => idtac "MSFAIL" g end ]
| first [ rewrite call_trace_nil; unfold raZ; rewrite Rra, unsigned_lit_small by lia; try rewrite (proj2 (Z.eqb_neq _ _)) by (pose proof (pal_rt_below Bv T); lia);
hul_tac | match goal with |- ?g => idtac "MSFAIL" g end ]
| first [ exact MOK | match goal with |- ?g => idtac "MSFAIL meter" g end ] ]
| clear Rra Rsp Rgp Rtp Rs0 Hnev ] end end end end.
Ltac mresX Hnz Ebl HK Hres :=
lazymatch type of HK with acall_kept ?sg ?Bq ?lyc ?Sc ?Wc ?memT ?W2 ?mem2 ?slo ?shi (fun a => ?res <= a < _) =>
lazymatch type of Ebl with ablocks _ ?ly ?S = _ =>
pose proof (@or_intror (res = 0 /\ ablocks Bq ly S = ablocks Bq lyc Sc /\ acall_kept sg Bq lyc Sc Wc memT W2 mem2 slo shi (fun _ => False)) _
(conj Hnz (conj Ebl HK))) as Hres end end.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg lib_asan3_1_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_1_listing PI) (@pa_relro_lo _ lib_asan3_1_listing PI) (@pa_relro_hi _ lib_asan3_1_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_1_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_1_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_1_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_1_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Section e.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Variable MT : ameter_ops.
Hypothesis MLAW : ameter_laws MT.
Hypothesis AMALLOC4 : amalloc04_rule SEGS B MT.
Hypothesis AMEMSET : aintrin_realizes SEGS B OSet (SIGMA AS_asan_memset).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_1) (PI := PI).
Hypothesis HUL : forall t, In t (lzw_traces (as_code B) BASE) -> In t (as_universe B).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_asan3_1 PI.
Definition tpro_okX (STK sp0 : Z) (FP : list (Z * Z)) (lyc : alayout) (Sc : astate) (W : world SEGS)
(memc : word -> option byte) (mdc : Model) (own : list (Z * Z))
(regs : bvmap 5 word) (pR nP img idl icl : Z) (macc : Z) : world SEGS -> config -> Prop :=
fun W6 c6 => exists ly6 S6 regs6 mem6 md6 (ctx ti lm lc li tm ld : Z),
let m6 := mrestrict (w_H W6) mem6 in let sp := spZ regs - 320 in
let tabs := lzw_tabs ti lm lc li tm ld nP idl in
c6 = mkCfg (mkst regs6 (Z_to_bv 64 (BASE + PC_INIT)) mem6 (seg_rom SEGS)) md6 /\
ajournal SEGS B STK sp0 FP lyc Sc W memc mdc own ly6 S6 W6 mem6 md6 7 /\
spZ regs6 = sp /\ getr regs6 3 = getr regs 3 /\ getr regs6 4 = getr regs 4 /\
getr regs6 8 = w64 ctx /\ getr regs6 22 = alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 ctx) (Z_to_bv 64 3)) (Z_to_bv 64 SB) /\
getr regs6 20 = w64 (ctx + 8) /\ getr regs6 19 = w64 (ctx + 16) /\ getr regs6 18 = w64 (ctx + 24) /\ getr regs6 9 = w64 (ctx + 32) /\
getr regs6 27 = w64 SB /\ getr regs6 21 = w64 2 /\ getr regs6 25 = w64 idl /\
getr regs6 26 = alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 (ctx + 8)) (Z_to_bv 64 3)) (Z_to_bv 64 SB) /\
getr regs6 1 = w64 (ctx + 40) /\ getr regs6 10 = w64 ld /\
tlzw_frame m6 (spZ regs) regs /\
val_mem SEGS m6 (sp + 208) 8 (ctx + 40) /\ val_mem SEGS m6 (sp + 200) 8 (shadow_word (ctx + 16)) /\ val_mem SEGS m6 (sp + 192) 8 (shadow_word (ctx + 24)) /\
val_mem SEGS m6 (sp + 184) 8 (2 * idl * idl) /\ val_mem SEGS m6 (sp + 176) 8 icl /\ val_mem SEGS m6 (sp + 168) 8 (2 * idl) /\
val_mem SEGS m6 (sp + 160) 8 (shadow_word (ctx + 32)) /\ val_mem SEGS m6 (sp + 152) 8 pR /\ val_mem SEGS m6 (sp + 144) 8 (ctx + 56) /\
val_mem SEGS m6 (sp + 136) 8 (shadow_word (ctx + 56)) /\ val_mem SEGS m6 (sp + 128) 8 (shadow_word (ctx + 40)) /\
val_mem SEGS m6 (sp + 120) 8 (ctx + 48) /\ val_mem SEGS m6 (sp + 112) 8 (shadow_word (ctx + 48)) /\
val_mem SEGS m6 ctx 8 ti /\ val_mem SEGS m6 (ctx + 8) 8 lm /\ val_mem SEGS m6 (ctx + 16) 8 lc /\
val_mem SEGS m6 (ctx + 24) 8 li /\ val_mem SEGS m6 (ctx + 32) 8 tm /\ val_mem SEGS m6 (ctx + 40) 8 ld /\
val_mem SEGS m6 (ctx + 48) 8 img /\ val_mem SEGS m6 (ctx + 56) 4 nP /\
Permutation (ablocks B ly6 S6) (tabs ++ (ctx, 72) :: ablocks B lyc Sc) /\
(forall b, In b ((ctx, 72) :: tabs) ->
4096 <= fst b /\ 0 <= snd b /\ aftok FP (ablocks B lyc Sc) b /\
forall blc lyq i, In b blc -> 0 <= i < req_size (snd b) -> awr_byte STK sp0 FP (ablocks B lyc Sc) blc lyq own (fst b + i)) /\
frames S6 = frames Sc /\
mo_le MT Sc S6 macc.
Lemma tlzw_pro9X : forall E W6 (regs6 : bvmap 5 word) mem6 md6 STK sp0 FP lyc Sc W memc mdc own ly6 S6
(regs : bvmap 5 word) (pR nP img idl icl bi Li ctx ti lm lc li : Z) (T acc : Z),
st_ok_pi SEGS VAL E ss_pro9_c (restrict (w_H W6) (mkst regs6 (Z_to_bv 64 (BASE + 0x154c)) mem6 (seg_rom SEGS))) -> img_env VAL A_LIM E ->
ajournal SEGS B STK sp0 FP lyc Sc W memc mdc own ly6 S6 W6 mem6 md6 5 ->
(forall n (rr : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) ->
ew E 32%nat = w64 SB -> ew E 37%nat = w64 ctx -> ew E 69%nat = w64 ti -> ew E 85%nat = w64 lm -> ew E 101%nat = w64 lc -> ew E 117%nat = w64 li ->
YK0s.ret_ok (getr regs 1) -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 10 = w64 pR -> getr regs 11 = w64 nP -> getr regs 12 = w64 img -> getr regs 13 = w64 idl -> getr regs 14 = w64 icl ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - LZW_TSTK -> spZ regs <= sp0 ->
pR mod 8 = 0 -> 0 <= pR -> pR + 16 <= 2 ^ 63 ->
1 <= nP <= 100000000 -> 2 <= idl <= 256 -> 0 <= icl <= 12 ->
In (bi, Li) (ablocks B lyc Sc) -> bi <= img -> img + nP <= bi + req_size Li ->
st_nev Sc + LZW_EV <= EV_MAX -> blocks_bytes Sc + 2 ^ 29 <= LIVE_MAX ->
Permutation (ablocks B ly6 S6)
(tnz [(0, 2 * (lzw_MR nP idl + nP + 2)); (ti, 2 * idl * idl); (lm, 8192); (lc, 4096); (li, 8192); (0, 4098 * idl)] ++ (ctx, 72) :: ablocks B lyc Sc) ->
tok_inv STK sp0 FP (ablocks B lyc Sc) own
((ctx, 72) :: tnz [(0, 2 * (lzw_MR nP idl + nP + 2)); (ti, 2 * idl * idl); (lm, 8192); (lc, 4096); (li, 8192); (0, 4098 * idl)]) ->
4096 <= ti -> ti + req_size (2 * idl * idl) <= alloc_ceiling ->
4096 <= lm < 2 ^ 64 -> 4096 <= lc < 2 ^ 64 -> 4096 <= li < 2 ^ 64 ->
blocks_bytes S6 <= blocks_bytes Sc + (72 + 2 * idl * idl + 8192 + 4096 + 8192) -> frames S6 = frames Sc ->
mo_ok MT Sc T -> mo_le MT Sc S6 acc -> 0 <= acc ->
acc + mo_malloc MT (4098 * idl) + mo_malloc MT (2 * (lzw_MR nP idl + nP + 2)) <= T ->
SRr SEGS W6 (mkCfg (mkst regs6 (Z_to_bv 64 (BASE + 0x154c)) mem6 (seg_rom SEGS)) md6)
(tpro_okX STK sp0 FP lyc Sc W memc mdc own regs pR nP img idl icl
(acc + mo_malloc MT (4098 * idl) + mo_malloc MT (2 * (lzw_MR nP idl + nP + 2)))).
Proof.
intros E W6 regs6 mem6 md6 STK sp0 FP lyc Sc W memc mdc own ly6 S6 regs pR nP img idl icl bi Li ctx ti lm lc li T acc
HS HEI HJ6 EE E32 Rctx Rti Rlm Rlc Rli Hra0 Hgp Htp G10 G11 G12 G13 G14 Hal16 Hwlo Hwhi HpR8 HpR0 HpR63 HnP Hidl Hicl Hbi Hbi1 Hbi2 Hev Hlive
HB6 TOK6 Hti4096 Hticeil Hlm Hlc Hli HBB6 Hfrs6 HT MACC Hacc0 HaccT.
pose proof (mo_malloc_nonneg MT MLAW (4098 * idl) ltac:(lia)) as Mc6.
pose proof (mo_malloc_nonneg MT MLAW (2 * (lzw_MR nP idl + nP + 2)) ltac:(pose proof (maxres_bounds idl nP Hidl ltac:(lia)); unfold lzw_MR; lia)) as Mc7.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HJ6 as (HAR6 & Hly6 & _ & _ & _ & _ & Hnev6 & _ & _ & _ & _ & _ & _ & Hpres & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) & _).
pose proof Hly6 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HTS : LZW_TSTK = 336 + ASTACK) by reflexivity.
assert (ASTACK = 16384) as Has by reflexivity. assert (HEV : LZW_EV = 19) by reflexivity.
assert (HMM : MALLOC_MAX = 2 ^ 28) by reflexivity.
pose proof (req_size_pos' (2 * idl * idl) ltac:(lia)) as Hrq.
assert (Htisz : 8 <= 2 * idl * idl <= 131072) by (clear - Hidl; nia).
assert (Hin6 : forall b, In b (tnz [(0, 2 * (lzw_MR nP idl + nP + 2)); (ti, 2 * idl * idl); (lm, 8192); (lc, 4096); (li, 8192); (0, 4098 * idl)] ++ (ctx, 72) :: ablocks B lyc Sc) ->
In b (ablocks B ly6 S6)) by (intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact HB6 | exact Hb]).
assert (Hctx6 : In (ctx, 72) (ablocks B ly6 S6)) by (apply Hin6; apply in_app_iff; right; left; reflexivity).
assert (Hbi6 : In (bi, Li) (ablocks B ly6 S6)) by (apply Hin6; apply in_app_iff; right; right; exact Hbi).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bi Li HAR6 Hbi6) as (Hbi16 & Hbi4096 & Hbiceil & Hbih_ia & _ & _). pose proof (proj1 Hbih_ia) as Hbih.
pose proof (blk_off_imgP _ _ _ _ _ _ bi Li HAR6 Hbi6) as Hbih_img.
destruct (al_blocks _ _ LAWS _ _ _ _ _ ctx 72 HAR6 Hctx6) as (Hc16 & Hc4096 & Hcceil & Hchigh_ia & Hcpres & _). pose proof (proj1 Hchigh_ia) as Hchigh.
pose proof (blk_off_imgP _ _ _ _ _ _ ctx 72 HAR6 Hctx6) as Hchigh_img.
change (req_size 72) with 72 in Hcceil, Hcpres.
assert (Actx : forall blc lyq i, In (ctx, 72) blc -> 0 <= i < 72 -> awr_byte STK sp0 FP (ablocks B lyc Sc) blc lyq own (ctx + i)).
{ intros blc lyq i Hin Hi. apply (TOK6 (ctx, 72) ltac:(left; reflexivity)); [exact Hin | cbn [snd]; change (req_size 72) with 72; lia]. }
assert (E3 : ew E 3 = Z_to_bv 64 (as_gp B)) by (rewrite (EE 3%nat 3%bv ltac:(lia) eq_refl); exact Hgp).
assert (E4 : ew E 4 = Z_to_bv 64 (as_tp B)) by (rewrite (EE 4%nat 4%bv ltac:(lia) eq_refl); exact Htp).
assert (E10 : ew E 10 = Z_to_bv 64 pR) by (rewrite (EE 10%nat 10%bv ltac:(lia) eq_refl); exact G10).
assert (E11 : ew E 11 = Z_to_bv 64 nP) by (rewrite (EE 11%nat 11%bv ltac:(lia) eq_refl); exact G11).
assert (E12 : ew E 12 = Z_to_bv 64 img) by (rewrite (EE 12%nat 12%bv ltac:(lia) eq_refl); exact G12).
assert (E13 : ew E 13 = Z_to_bv 64 idl) by (rewrite (EE 13%nat 13%bv ltac:(lia) eq_refl); exact G13).
assert (E14 : ew E 14 = Z_to_bv 64 icl) by (rewrite (EE 14%nat 14%bv ltac:(lia) eq_refl); exact G14).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv ltac:(lia) eq_refl); reflexivity).
set (sp := spZ regs) in *.
assert (Hom : (sp - 320 - sp0) mod 16 = 0).
{ pose proof (Z.div_mod sp0 16 ltac:(lia)) as D0. pose proof (Z.div_mod sp 16 ltac:(lia)) as D1.
rewrite Hsp0al, Z.add_0_r in D0. rewrite Hal16, Z.add_0_r in D1.
replace (sp - 320 - sp0) with ((sp / 16 - 20 - sp0 / 16) * 16) by lia. apply Z_mod_mult. }
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by (intros; reflexivity).
assert (EE' : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr).
{ intros n rr Hn. apply EE; [|exact Hn]. pose proof (bv_unsigned_in_range 5 rr) as Hr. change (bv_modulus 5) with 32 in Hr. lia. }
clear EE. rename EE' into EE.
reshok HS.
paj_run_tok RUN HS HJ6 SHOK Bspan; [obl_ctx HJ6 Hctx6 AG Rctx E32 .. | awr2 Actx Hctx6 AG Rctx Usp |].
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK Bspan.
{
exfalso. rewrite branch_eq_U, (U_atom _ 85 lm), U_SLit in Hc by (first [eatom AG Rlm | lia]). change (zcanon 0) with 0 in Hc.
destruct (Z.eqb_spec lm 0); [lia | discriminate]. }
rewrite branch_eq_U, (U_atom _ 85 lm), U_SLit in Hc by (first [eatom AG Rlm | lia]). change (zcanon 0) with 0 in Hc.
assert (Hlm1 : lm <> 0) by (destruct (Z.eqb_spec lm 0); [discriminate | assumption]). clear Hc.
paj_run_tok RUN HS HJ6 SHOK Bspan; [obl_ctx HJ6 Hctx6 AG Rctx E32 .. | awr2 Actx Hctx6 AG Rctx Usp |]. clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK Bspan.
{
exfalso. rewrite branch_eq_U, (U_atom _ 101 lc), U_SLit in Hc by (first [eatom AG Rlc | lia]). change (zcanon 0) with 0 in Hc.
destruct (Z.eqb_spec lc 0); [lia | discriminate]. }
rewrite branch_eq_U, (U_atom _ 101 lc), U_SLit in Hc by (first [eatom AG Rlc | lia]). change (zcanon 0) with 0 in Hc.
assert (Hlc1 : lc <> 0) by (destruct (Z.eqb_spec lc 0); [discriminate | assumption]). clear Hc.
paj_run_tok RUN HS HJ6 SHOK Bspan; [obl_ctx HJ6 Hctx6 AG Rctx E32 .. | awr2 Actx Hctx6 AG Rctx Usp |]. clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK Bspan.
{
exfalso. rewrite branch_eq_U, (U_atom _ 117 li), U_SLit in Hc by (first [eatom AG Rli | lia]). change (zcanon 0) with 0 in Hc.
destruct (Z.eqb_spec li 0); [lia | discriminate]. }
rewrite branch_eq_U, (U_atom _ 117 li), U_SLit in Hc by (first [eatom AG Rli | lia]). change (zcanon 0) with 0 in Hc.
assert (Hli1 : li <> 0) by (destruct (Z.eqb_spec li 0); [discriminate | assumption]). clear Hc.
paj_run_tok RUN HS HJ6 SHOK Bspan; [obl_ctx HJ6 Hctx6 AG Rctx E32 .. | awr2 Actx Hctx6 AG Rctx Usp |]. clear HF HFr HG.
rregU HS (10%bv : bv 5) (4098 * idl) ltac:(apply (U_tmsz _ 13 idl); [eatom AG E13 | exact Hidl]) Ra0.
assert (HSZ6 : 0 <= 4098 * idl < MALLOC_MAX /\ blocks_bytes S6 + 4098 * idl <= LIVE_MAX) by (clear - HMM HBB6 Hlive Htisz Hidl; rewrite HMM; unfold LIVE_MAX in *; lia).
pose proof (mok_station MT Sc S6 T acc _ MLAW HT MACC Mc6 ltac:(lia)) as MOK6.
malloc_siteX HS HJ6 (4098 * idl) ltac:(exact Ra0) AG Usp Rctx Hom HSZ6 MOK6. clear Ra0.
cbv beta. intros W7 c7 Hwle7 (ly7 & S7 & regs7 & mem7 & md7 & tm & -> & HJ7 & HP7 & Ha07 & Hfrs7 & Hnz7 & Ebl7 & HK7' & MLE7).
mresX Hnz7 Ebl7 HK7' Hres7. pose proof (mle_station MT Sc S6 S7 _ _ MLAW MACC MLE7) as MACC7.
assert (HBB7 : blocks_bytes S7 <= blocks_bytes Sc + (72 + 2 * idl * idl + 8192 + 4096 + 8192 + 4098 * idl)) by (pose proof (blocks_bytes_after_malloc B _ _ _ _ _ _ _ _ Hres7 ltac:(lia)); lia).
destruct (mres_kept B _ _ _ _ _ _ _ _ _ _ _ _ Hres7) as (HK7 & Hsub7 & Htm_in).
pose proof (mres_range B LAWS _ _ _ _ _ _ _ _ _ _ _ (proj1 HJ7) Hres7) as Hrr7.
assert (Hctx7 : In (ctx, 72) (ablocks B ly7 S7)) by (apply Hsub7; exact Hctx6).
pose proof (perm_tab_update _ _ _ [(0, 2 * (lzw_MR nP idl + nP + 2)); (ti, 2 * idl * idl); (lm, 8192); (lc, 4096); (li, 8192)] _ tm _ _ _ HB6 Hres7) as HB7. cbn [app] in HB7.
assert (TOK7 : tok_inv STK sp0 FP (ablocks B lyc Sc) own
((ctx, 72) :: tnz [(0, 2 * (lzw_MR nP idl + nP + 2)); (ti, 2 * idl * idl); (lm, 8192); (lc, 4096); (li, 8192); (tm, 4098 * idl)])).
{ intros b [<- | Hb]; [apply TOK6; left; reflexivity|].
destruct (in_tnz_update [(0, 2 * (lzw_MR nP idl + nP + 2)); (ti, 2 * idl * idl); (lm, 8192); (lc, 4096); (li, 8192)] _ tm _ b Hb) as [-> | Hb']; [| apply TOK6; right; exact Hb'].
cbn [fst snd]. destruct Hres7 as [(Hz0 & _ & _) | (Hnz & Ebl & _)].
{ exfalso. clear - Hz0 Hnz7. lia. }
split; [exact Hnz|]. split; [lia|]. split; [exact (aftok_new_block SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ tm _ HJ6 (proj1 HJ7) Ebl ltac:(lia))|].
intros blc lyq i Hin Hi. exact (awr_new_block SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ tm _ blc i lyq HJ6 (proj1 HJ7) Ebl ltac:(lia) Hin Hi). }
reseat HS HJ7 HP7 [0%nat; 1%nat] AG ltac:(first [kept_malloc HK7 HJ7 AG Usp | kept_ctx_m HK7 HJ7 Hctx7 Hctx6 Rctx AG Hres7]).
prreg HS (10%bv : bv 5) Rtm. rewrite Ha07 in Rtm. symmetry in Rtm.
destruct Hrr7 as [Htm0 | (Htm4096 & Htmh & Htmceil & Htm16 & Htm7)].
{   exfalso. clear - Htm0 Hnz7. lia. }
pose proof (req_size_pos0 (4098 * idl) ltac:(lia)) as Hrq7.
lazymatch type of Rtm with ew ?Ex ?nx = _ =>
pose proof (st_ok_pi_add_fact Ex _ _ nx (PTR 4) HS
ltac:(clear HS; idtac; unfold afact_ok, PTR; cbn [af_lo af_hi af_al2]; rewrite Rtm, unsigned_lit_small by lia;
change (2 ^ 4) with 16; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS. reshok HS.
paj_run_tok RUN HS HJ7 SHOK Bspan;
[obl_ctx HJ7 Hctx7 AG Rctx E32 .. | awr2 Actx Hctx7 AG Rctx Usp |].
clear HF HFr HG.
pose proof (maxres_bounds idl nP Hidl ltac:(lia)) as [HMR1 HMR2].
assert (HMRle : 0 <= lzw_MR nP idl <= nP) by (clear - HMR1 HMR2 Hidl HnP; unfold lzw_MR in *; nia).
rregU HS (10%bv : bv 5) (2 * (lzw_MR nP idl + nP + 2))
ltac:(unfold lzw_MR; apply (U_ldsz _ 13 11 idl nP); [eatom AG E13 | eatom AG E11 | exact Hidl | exact HnP]) Ra0.
assert (HMRb : 3838 * lzw_MR nP idl <= nP) by (clear - HMR1 HMR2 Hidl HnP; unfold lzw_MR in *; nia).
assert (HSZ7 : 0 <= 2 * (lzw_MR nP idl + nP + 2) < MALLOC_MAX /\ blocks_bytes S7 + 2 * (lzw_MR nP idl + nP + 2) <= LIVE_MAX) by (clear - HMM HBB7 Hlive Htisz Hidl HnP HMRb HMRle; rewrite HMM; unfold LIVE_MAX in *; lia).
pose proof (mok_station MT Sc S7 T _ _ MLAW HT MACC7 Mc7 ltac:(lia)) as MOK7.
malloc_siteX HS HJ7 (2 * (lzw_MR nP idl + nP + 2)) ltac:(exact Ra0) AG Usp Rctx Hom HSZ7 MOK7. clear Ra0.
cbv beta. intros W8 c8 Hwle8 (ly8 & S8 & regs8 & mem8 & md8 & ld & -> & HJ8 & HP8 & Ha08 & Hfrs8 & Hnz8 & Ebl8 & HK8' & MLE8).
mresX Hnz8 Ebl8 HK8' Hres8. pose proof (mle_station MT Sc S7 S8 _ _ MLAW MACC7 MLE8) as MACC8.
destruct (mres_kept B _ _ _ _ _ _ _ _ _ _ _ _ Hres8) as (HK8 & Hsub8 & Hld_in).
pose proof (mres_range B LAWS _ _ _ _ _ _ _ _ _ _ _ (proj1 HJ8) Hres8) as Hrr8.
assert (Hctx8 : In (ctx, 72) (ablocks B ly8 S8)) by (apply Hsub8; exact Hctx7).
pose proof (perm_tab_update _ _ _ [] _ ld _ _ _ HB7 Hres8) as HB8. cbn [app] in HB8.
assert (TOK8 : tok_inv STK sp0 FP (ablocks B lyc Sc) own
((ctx, 72) :: tnz [(ld, 2 * (lzw_MR nP idl + nP + 2)); (ti, 2 * idl * idl); (lm, 8192); (lc, 4096); (li, 8192); (tm, 4098 * idl)])).
{ intros b [<- | Hb]; [apply TOK7; left; reflexivity|].
destruct (in_tnz_update [] _ ld _ b Hb) as [-> | Hb']; [| apply TOK7; right; exact Hb'].
cbn [fst snd]. destruct Hres8 as [(Hz0 & _ & _) | (Hnz & Ebl & _)].
{ exfalso. clear - Hz0 Hnz8. lia. }
split; [exact Hnz|]. split; [lia|]. split; [exact (aftok_new_block SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ld _ HJ7 (proj1 HJ8) Ebl ltac:(lia))|].
intros blc lyq i Hin Hi. exact (awr_new_block SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ld _ blc i lyq HJ7 (proj1 HJ8) Ebl ltac:(lia) Hin Hi). }
reseat HS HJ8 HP8 [0%nat; 1%nat] AG ltac:(first [kept_malloc HK8 HJ8 AG Usp | kept_ctx_m HK8 HJ8 Hctx8 Hctx7 Rctx AG Hres8]).
prreg HS (10%bv : bv 5) Rld. rewrite Ha08 in Rld. symmetry in Rld.
destruct Hrr8 as [Hld0 | (Hld4096 & Hldh & Hldceil & Hld16 & Hld8)].
{   exfalso. clear - Hld0 Hnz8. lia. }
pose proof (req_size_pos0 (2 * (lzw_MR nP idl + nP + 2)) ltac:(lia)) as Hrq8.
lazymatch type of Rld with ew ?Ex ?nx = _ =>
pose proof (st_ok_pi_add_fact Ex _ _ nx (PTR 4) HS
ltac:(clear HS; idtac; unfold afact_ok, PTR; cbn [af_lo af_hi af_al2]; rewrite Rld, unsigned_lit_small by lia;
change (2 ^ 4) with 16; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS. reshok HS.
paj_run_to_tok RUNTO HS HJ8 SHOK Bspan PC_INIT; [obl_ctx HJ8 Hctx8 AG Rctx E32 .. | awr2 Actx Hctx8 AG Rctx Usp |].
clear HF HFr HG.
prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4. prreg HS (8%bv : bv 5) R8. prreg HS (9%bv : bv 5) R9.
prreg HS (10%bv : bv 5) R10. prreg HS (18%bv : bv 5) R18. prreg HS (19%bv : bv 5) R19. prreg HS (20%bv : bv 5) R20. prreg HS (21%bv : bv 5) R21.
prreg HS (22%bv : bv 5) R22. prreg HS (25%bv : bv 5) R25. prreg HS (26%bv : bv 5) R26. prreg HS (27%bv : bv 5) R27. prreg HS (1%bv : bv 5) R1.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict (w_H ?Wx) ?msx) =>
assert (HFR : tlzw_frame (mrestrict (w_H Wx) (ms_mem msx)) sp regs) by (frame_tac HS 1%nat AG EE) | st_ok _ _ _ (restrict (w_H ?Wx) ?msx) =>
assert (HFR : tlzw_frame (mrestrict (w_H Wx) (ms_mem msx)) sp regs) by (frame_tac HS 1%nat AG EE)  end.
assert (Htabs : tnz [(ld, 2 * (lzw_MR nP idl + nP + 2)); (ti, 2 * idl * idl); (lm, 8192); (lc, 4096); (li, 8192); (tm, 4098 * idl)]
= lzw_tabs ti lm lc li tm ld nP idl).
{ unfold lzw_tabs. rewrite !tnz_cons_nz by lia. reflexivity. }
rewrite Htabs in HB8, TOK8.
pmkst HS.
apply SRr_ret.
lazymatch goal with |- tpro_okX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (mkCfg (mkst ?rg _ ?m _) ?mdx) =>
exists ly8, S8, rg, m, mdx, ctx, ti, lm, lc, li, tm, ld end.
cbv beta zeta.
split; [reflexivity|]. split; [exact HJ8|].
split; [fold sp; unfold spZ; rewrite R2, ?(AG 2%nat) by lia; rewrite Usp, unsigned_lit_small by lia; lia|].
split; [rewrite R3, ?(AG 3%nat) by lia; exact (EE 3%nat 3%bv eq_refl)|].
split; [rewrite R4, ?(AG 4%nat) by lia; exact (EE 4%nat 4%bv eq_refl)|].
split; [rewrite R8; exact Rctx|].
split; [rewrite R22, Rctx, ?(AG 32%nat) by lia; rewrite E32; reflexivity|].
split; [rewrite R20, Rctx, unsigned_lit_small by lia; reflexivity|].
split; [rewrite R19, Rctx, unsigned_lit_small by lia; reflexivity|].
split; [rewrite R18, Rctx, unsigned_lit_small by lia; reflexivity|].
split; [rewrite R9, Rctx, unsigned_lit_small by lia; reflexivity|].
split; [rewrite R27, ?(AG 32%nat) by lia; exact E32|].
split; [exact R21|].
split; [rewrite R25, ?(AG 13%nat) by lia; exact E13|].
split; [rewrite R26, Rctx, ?(AG 32%nat) by lia; rewrite E32, unsigned_lit_small by lia; reflexivity|].
split; [rewrite R1, Rctx, unsigned_lit_small by lia; reflexivity|].
split; [rewrite R10; exact Rld|].
split; [exact HFR|].
do 13 (split; [slot_tac HS 1%nat Usp AG Rctx|]).
do 8 (split; [ctx_field HS 0%nat Rctx AG|]).
split; [exact HB8|]. split; [exact TOK8|].
split; [rewrite Hfrs8, Hfrs7; exact Hfrs6|].
exact MACC8.
Qed.
End e.
End d.
End c.
