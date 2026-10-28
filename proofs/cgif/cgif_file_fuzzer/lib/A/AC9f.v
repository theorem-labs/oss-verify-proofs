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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC81 YC4b.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8a AC93 AC9g.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section e.
Context {PI : PAImg lib_asan3_1_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_1_listing PI) (@pa_relro_lo _ lib_asan3_1_listing PI) (@pa_relro_hi _ lib_asan3_1_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_1_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_1_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_1_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_1_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Section f.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMALLOC : amalloc_realizes SEGS B.
Hypothesis AFREE : afree_realizes SEGS B.
Hypothesis AMEMSET : aintrin_realizes SEGS B OSet (SIGMA AS_asan_memset).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_1) (PI := PI).
Hypothesis HUL : forall t, In t (lzw_traces (as_code B) BASE) -> In t (as_universe B).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_asan3_1 PI.
Variable CTX : list (list Z).
Hypothesis HUCTX : forall c, In c CTX ->
In (firstn kUnwindMax (pc_malloc_ra0 (as_code B)
:: flat_map (fun ra => if ra =? pc_malloc_ra0 (as_code B) then [] else [ra]) ((BASE + 0x14a4) :: tl c))) (as_universe B).
Lemma tlzw_pro : forall W STK sp0 FP lyc Sc memc mdc own (regs : bvmap 5 word) (pR nP img idl icl bi Li : Z) ch,
ajournal SEGS B STK sp0 FP lyc Sc W memc mdc own lyc Sc W memc mdc 0 ->
YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 10 = w64 pR -> getr regs 11 = w64 nP -> getr regs 12 = w64 img -> getr regs 13 = w64 idl -> getr regs 14 = w64 icl ->
achain lyc (aview SEGS (w_H W) memc) (spZ regs) (s0Z regs) ch -> In (raZ regs :: spine ch) CTX ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - LZW_TSTK -> spZ regs <= sp0 ->
pR mod 8 = 0 -> 0 <= pR -> pR + 16 <= 2 ^ 63 ->
1 <= nP <= 100000000 -> 2 <= idl <= 256 -> 0 <= icl <= 12 ->
In (bi, Li) (ablocks B lyc Sc) -> bi <= img -> img + nP <= bi + req_size Li ->
st_nev Sc + LZW_EV <= EV_MAX -> blocks_bytes Sc + 2 ^ 29 <= LIVE_MAX ->
SRr SEGS W (cfg_at SEGS (BASE + A_LZW) regs memc mdc)
(fun W' c' => tpro_fail B STK sp0 FP lyc Sc W memc mdc own regs W' c' \/
tpro_ok B STK sp0 FP lyc Sc W memc mdc own regs pR nP img idl icl W' c').
Proof.
intros W STK sp0 FP lyc Sc memc mdc own regs pR nP img idl icl bi Li ch
HJ Hra0 Hra4 Hgp Htp G10 G11 G12 G13 G14 Hch Hctx Hal16 Hwlo Hwhi HpR8 HpR0 HpR63 HnP Hidl Hicl Hbi Hbi1 Hbi2 Hev Hlive.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HJ as (HAR & Hly0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) & _).
pose proof Hly0 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HTS : LZW_TSTK = 336 + ASTACK) by reflexivity.
assert (ASTACK = 16384) as Has by reflexivity. assert (HEV : LZW_EV = 19) by reflexivity.
assert (HMM : MALLOC_MAX = 2 ^ 28) by reflexivity.
destruct (al_blocks _ _ LAWS _ _ _ _ _ bi Li HAR Hbi) as (Hbi16 & Hbi4096 & Hbiceil & Hbih_ia & _ & _). pose proof (proj1 Hbih_ia) as Hbih.
pose proof (blk_off_imgP _ _ _ _ _ _ bi Li HAR Hbi) as Hbih_img.
pose proof (tlzw_entry B TL LAWS W STK sp0 FP lyc Sc W memc mdc own lyc Sc memc mdc 0 regs pR nP img idl icl bi Li HJ G10 G11 G12 G13 G14
Hal16 Hwlo Hwhi HpR8 HpR0 HpR63 HnP Hidl Hicl Hbi Hbi1 Hbi2) as HS.
remember (Eimg (Ereg regs [Z_to_bv 64 SB])) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) by (intros n rr Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (exact (EE 2%nat 2%bv eq_refl)).
assert (E8 : ew E 8 = getr regs 8) by (exact (EE 8%nat 8%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 pR) by (rewrite (EE 10%nat 10%bv eq_refl); exact G10).
assert (E11 : ew E 11 = Z_to_bv 64 nP) by (rewrite (EE 11%nat 11%bv eq_refl); exact G11).
assert (E12 : ew E 12 = Z_to_bv 64 img) by (rewrite (EE 12%nat 12%bv eq_refl); exact G12).
assert (E13 : ew E 13 = Z_to_bv 64 idl) by (rewrite (EE 13%nat 13%bv eq_refl); exact G13).
assert (E14 : ew E 14 = Z_to_bv 64 icl) by (rewrite (EE 14%nat 14%bv eq_refl); exact G14).
assert (E3 : ew E 3 = Z_to_bv 64 (as_gp B)) by (rewrite (EE 3%nat 3%bv eq_refl); exact Hgp).
assert (E4 : ew E 4 = Z_to_bv 64 (as_tp B)) by (rewrite (EE 4%nat 4%bv eq_refl); exact Htp).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
clear HE. unfold cfg_at.
shok_auto SHOK (SOff 32 0) E (mrestrict (w_H W) memc).
set (sp := spZ regs) in *.
paj_run_tok RUN HS HJ SHOK Bspan.
{ eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (sp - sp0)); [reflexivity | rewrite Usp; lia | cbn; lia | cbn; lia | awr_ok_tac]. }
assert (Hom : (sp - 320 - sp0) mod 16 = 0).
{ pose proof (Z.div_mod sp0 16 ltac:(lia)) as D0. pose proof (Z.div_mod sp 16 ltac:(lia)) as D1.
rewrite Hsp0al, Z.add_0_r in D0. rewrite Hal16, Z.add_0_r in D1.
replace (sp - 320 - sp0) with ((sp / 16 - 20 - sp0 / 16) * 16) by lia. apply Z_mod_mult. }
prreg HS (10%bv : bv 5) Ra0. prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp.
prreg HS (4%bv : bv 5) Rtp. prreg HS (8%bv : bv 5) Rs0.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msX) =>
assert (Hch1 : achain lyc (aview SEGS (w_H W) (ms_mem msX)) sp (s0Z regs) ch) | st_ok _ _ _ (restrict _ ?msX) =>
assert (Hch1 : achain lyc (aview SEGS (w_H W) (ms_mem msX)) sp (s0Z regs) ch)  end.
{ eapply (achain_kept lyc _ _ sp (s0Z regs) ch sp Hch); [lia | lia |].
eapply (aview_kept_frame _ _ _ _ _ sp HFr); [lia|].
intros a Ha (rg & Hin & Hrg). cbn in Hin.
destruct Hin as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg; rewrite ?Usp in Hrg; lia. }
clear HF HFr HG.
pmkst HS.
ppcs.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_malloc_at SEGS B LAWS Hsegs errno_low ML AMALLOC _ (ms_regs msX) (ms_mem msX) STK sp0 FP lyc Sc W memc mdc own
lyc Sc _ 0 72 (sp - 320 - sp0) (Z_to_bv 64 (BASE + 0x14a4)) ch HJ) end.
- exact Ra0.
- rewrite HMM. lia.
- unfold LIVE_MAX in *. lia.
- unfold spZ. rewrite Rsp, Usp, unsigned_lit_small by lia. lia.
- exact Hom.
- lia.
- lia.
- rewrite Rgp, E3. reflexivity.
- rewrite Rtp, E4. reflexivity.
- exact Rra.
- apply ret_ok_codeptr_v; [lazymatch goal with |- _ <= ?k < _ => try unfold k end; lia | reflexivity].
- lia.
- apply (achain_chain_pre lyc _ sp (s0Z regs) ch _ Hch1);
[ unfold spZ; rewrite Rsp, Usp, unsigned_lit_small by lia; lia
| unfold s0Z; rewrite Rs0, E8; reflexivity
| unfold raZ; rewrite Rra, unsigned_lit_small by lia; lia ].
- rewrite call_trace_of_spine. unfold raZ. rewrite Rra, unsigned_lit_small by lia. exact (HUCTX (raZ regs :: spine ch) Hctx). }
cbv beta. intros W1 c1 Hwle1 (ly1 & S1 & regs1 & mem1 & md1 & ctx & -> & HJ1 & HP1 & Ha01 & Hfrs1 & Hres1).
clear Ra0 Rra Rsp Rgp Rtp Rs0.
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by (intros; reflexivity).
destruct Hres1 as [(Hres0 & Ebl1 & HK1) | (Hres4096 & Ebl1 & HK1)].
{
reseat HS HJ1 HP1 [0%nat] AG ltac:(kept_malloc HK1 HJ1 AG Usp).
pose proof (st_ok_pi_pin_reg' _ _ _ (10%bv : bv 5) 0 HS ltac:(cbn [ms_regs restrict mkst]; rewrite Ha01, Hres0; reflexivity) eq_refl) as HS3.
norm_ss HS3. clear HS. rename HS3 into HS. reshok HS.
paj_run_to_tok RUNTO HS HJ1 SHOK Bspan 0x21c8.
{ eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (sp - sp0));
[reflexivity | cbn [ew ewset Nat.eqb]; rewrite ?(AG 2%nat) by lia; rewrite Usp; lia | cbn; lia | cbn; lia | awr_ok_tac]. }
idtac "AT LEAVE".
prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4. prreg HS (21%bv : bv 5) R21.
assert (HFR : tlzw_frame (mrestrict (w_H W1) _) sp regs) by (frame_tac HS 0%nat AG EE).
pmkst HS.
eapply SRr_mono.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (tlzw_leave B LAWS W1 (ms_regs msX) (ms_mem msX) _ regs STK sp0 FP lyc Sc W memc mdc own ly1 S1 (0 + 1) 2 HJ1) end.
- fold sp. unfold spZ. rewrite R2, ?(AG 2%nat) by lia. rewrite Usp, unsigned_lit_small by lia. lia.
- exact Hwhi.
- exact Hwlo.
- exact Hal16.
- rewrite R3, ?(AG 3%nat) by lia. exact (EE 3%nat 3%bv eq_refl).
- rewrite R4, ?(AG 4%nat) by lia. exact (EE 4%nat 4%bv eq_refl).
- exact R21.
- lia.
- exact Hra0.
- exact HFR. }
cbv beta. intros W2 c2 _ (-> & regs2 & md2 & -> & HJ2 & HP2 & Ha02).
left. lazymatch goal with |- tpro_fail _ _ _ _ _ _ _ _ _ _ _ _ (mkCfg (mkst _ _ ?m _) _) => exists ly1, S1, regs2, m, md2 end.
split; [reflexivity|].
split; [eapply ajournal_mono_k; [exact HJ2 | rewrite HEV; lia]|].
split; [exact HP2|]. split; [exact Ha02|]. split; [exact Hfrs1|]. rewrite Ebl1. apply Permutation_refl. }
assert (Hctx1 : In (ctx, 72) (ablocks B ly1 S1)) by (rewrite Ebl1; apply in_app_iff; right; left; reflexivity).
pose proof (proj1 HJ1) as HAR1.
destruct (al_blocks _ _ LAWS _ _ _ _ _ ctx 72 HAR1 Hctx1) as (Hc16 & Hc4096 & Hcceil & Hchigh_ia & Hcpres & _). pose proof (proj1 Hchigh_ia) as Hchigh.
pose proof (blk_off_imgP _ _ _ _ _ _ ctx 72 HAR1 Hctx1) as Hchigh_img.
change (req_size 72) with 72 in Hcceil, Hcpres.
pose proof (aftok_new_block SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ctx 72 HJ HAR1 Ebl1 ltac:(lia)) as Tctx.
assert (Actx : forall blc lyq i, In (ctx, 72) blc -> 0 <= i < 72 -> awr_byte STK sp0 FP (ablocks B lyc Sc) blc lyq own (ctx + i)).
{ intros blc lyq i Hin Hi. exact (awr_new_block SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ctx 72 blc i lyq HJ HAR1 Ebl1 ltac:(lia) Hin ltac:(change (req_size 72) with 72; lia)). }
assert (HB1 : Permutation (ablocks B ly1 S1)
(tnz [(0, 2 * (lzw_MR nP idl + nP + 2)); (0, 2 * idl * idl); (0, 8192); (0, 4096); (0, 8192); (0, 4098 * idl)] ++ (ctx, 72) :: ablocks B lyc Sc)).
{ cbn [tnz List.filter fst Z.eqb negb app]. rewrite Ebl1. apply Permutation_sym. apply Permutation_cons_append. }
assert (TOK1 : forall b, In b ((ctx, 72) :: tnz [(0, 2 * (lzw_MR nP idl + nP + 2)); (0, 2 * idl * idl); (0, 8192); (0, 4096); (0, 8192); (0, 4098 * idl)]) ->
4096 <= fst b /\ 0 <= snd b /\ aftok FP (ablocks B lyc Sc) b /\
forall blc lyq i, In b blc -> 0 <= i < req_size (snd b) -> awr_byte STK sp0 FP (ablocks B lyc Sc) blc lyq own (fst b + i)).
{ cbn [tnz List.filter fst Z.eqb negb app]. intros b [<- | []]. cbn [fst snd]. split; [lia|]. split; [lia|]. split; [exact Tctx|].
intros blc lyq i Hin Hi. apply Actx; [exact Hin | change (req_size 72) with 72 in Hi; lia]. }
reseat HS HJ1 HP1 [0%nat] AG ltac:(kept_malloc HK1 HJ1 AG Usp).
prreg HS (10%bv : bv 5) Rctx. rewrite Ha01 in Rctx. symmetry in Rctx.
lazymatch type of Rctx with ew ?Ex ?nx = _ =>
pose proof (st_ok_pi_add_fact Ex _ _ nx (PTR 4) HS
ltac:(unfold afact_ok, PTR; cbn [af_lo af_hi af_al2]; rewrite Rctx, unsigned_lit_small by lia;
change (2 ^ 4) with 16; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg; idtac; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_region Ex _ _ (YP09.mkRegion (Some nx) 0 72 0 72 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite Rctx, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|constructor];
intros o Ho; apply (apresent_writable SEGS); apply (proj1 (Hcpres (ctx + o) ltac:(lia))))
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite Rctx, unsigned_lit_small by lia; rewrite ?(AG 2%nat) by lia; rewrite Usp; split; [lia | exact I])) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS. reshok HS.
paj_run_tok RUN HS HJ1 SHOK Bspan.
{ eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ _ ctx); [reflexivity | cbn [ew ewset Nat.eqb]; rewrite Rctx; apply unsigned_lit_small; lia
| cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; replace a with (ctx + (a - ctx)) by lia; apply Actx; [exact Hctx1 | lia] |].
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (sp - sp0));
[reflexivity | cbn [ew ewset Nat.eqb]; rewrite ?(AG 2%nat) by lia; rewrite Usp; lia | cbn; lia | cbn; lia | awr_ok_tac]. }
clear HF HFr HG.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
pmkst HS.
idtac.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_intrin_at SEGS B LAWS Hsegs OSet (SIGMA AS_asan_memset) AMEMSET _ (ms_regs msX) (ms_mem msX) STK sp0 FP lyc Sc W memc mdc own
ly1 S1 _ (0 + 1) ctx 0 72 (sp - 320 - sp0) (Z_to_bv 64 (BASE + 0x14bc)) HJ1) end.
- first [rewrite Ra0, Rctx; reflexivity | rewrite Ra0, Rctx, unsigned_lit_small by lia; reflexivity | match goal with |- ?g => idtac "MEMSET-A0" g end].
- exact Ra1.
- exact Ra2.
- lia.
- lia.
- ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *. lia.
- fold sp. unfold spZ. rewrite Rsp, ?(AG 2%nat) by lia. rewrite Usp, unsigned_lit_small by lia. lia.
- exact Hom.
- lia.
- unfold ESTACK. lia.
- rewrite Rgp, ?(AG 3%nat) by lia. rewrite E3. reflexivity.
- rewrite Rtp, ?(AG 4%nat) by lia. rewrite E4. reflexivity.
- exact Rra.
- apply ret_ok_codeptr_v; [lazymatch goal with |- _ <= ?k < _ => try unfold k end; lia | reflexivity].
- intros a Ha. split; [replace a with (ctx + (a - ctx)) by lia; apply Actx; [exact Hctx1 | lia] | unfold ESTACK; lia].
- eapply (amem_range_of_block SEGS B LAWS ly1 S1 _ _ _ ctx 72 ctx 72 (proj1 HJ1) Hctx1); change (req_size 72) with 72; lia.
- eapply (range_addressable_of_block SEGS B LAWS ly1 S1 _ _ _ ctx 72 ctx 72 (proj1 HJ1) Hctx1); change (req_size 72) with 72; lia.
- intros _. eapply (shadow_hull_vis_of_block SEGS B LAWS ly1 S1 _ _ _ ctx 72 ctx 72 (proj1 HJ1) Hctx1); change (req_size 72) with 72; lia.
- exact I. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha02 & Heff & Hfr & Hpres2).
clear Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp.
reseat HS HJ2 HP2 [1%nat] AG ltac:(kept_intrin Hfr Hpres2 AG Usp).
assert (Hz : forall off, 0 <= off -> off + 8 <= 72 -> val_mem SEGS (mrestrict (w_H W1) mem2) (ctx + off) 8 0).
{ intros off H1 H2. apply val_mem_zero8. intros i Hi. replace (ctx + off + i) with (ctx + (off + i)) by lia.
rewrite (Heff (off + i)) by lia. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ ctx 72 (proj1 HJ2) Hctx1) as (_ & _ & _ & _ & Hcpres2 & _). change (req_size 72) with 72 in Hcpres2.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
pose proof (st_ok_pi_add_region Ex _ _
(YP09.mkRegion (Some 37%nat) 0 72 0 72
(map (fun off => YP09.mkChunk off (CVal 8 (SLit 0))) [0; 8; 16; 24; 32; 40; 48; 56; 64])) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst map];
rewrite Rctx, unsigned_lit_small by lia; split; [lia|]; split; [lia|];
split; [intros o Ho; apply (apresent_writable SEGS); apply (proj1 (Hcpres2 (ctx + o) ltac:(lia)))|];
repeat (apply Forall_cons; [apply (chunk_ok_val SEGS Ex _ ctx _ 8 (SLit 0) 0); [reflexivity | zside | zside | apply Hz; lia] |]);
apply Forall_nil)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite Rctx, unsigned_lit_small by lia; rewrite ?(AG 2%nat) by lia; rewrite Usp; split; [lia | exact I])) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ex _ _ =>
pose proof (st_ok_pi_add_region Ex _ _
(YP09.mkRegion (Some 37%nat) 0 72 0 72
(map (fun off => YP09.mkChunk off (CVal 8 (SLit 0))) [0; 8; 16; 24; 32; 40; 48; 56; 64])) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst map];
rewrite Rctx, unsigned_lit_small by lia; split; [lia|]; split; [lia|];
split; [intros o Ho; apply (apresent_writable SEGS); apply (proj1 (Hcpres2 (ctx + o) ltac:(lia)))|];
repeat (apply Forall_cons; [apply (chunk_ok_val SEGS Ex _ ctx _ 8 (SLit 0) 0); [reflexivity | zside | zside | apply Hz; lia] |]);
apply Forall_nil)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite Rctx, unsigned_lit_small by lia; rewrite ?(AG 2%nat) by lia; rewrite Usp; split; [lia | exact I])) as HS3;
clear HS; rename HS3 into HS  end.
norm_ss HS. reshok HS.
paj_run_tok RUN HS HJ2 SHOK Bspan.
{ eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ _ ctx); [reflexivity | cbn [ew ewset Nat.eqb]; rewrite Rctx; apply unsigned_lit_small; lia
| cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; replace a with (ctx + (a - ctx)) by lia; apply Actx; [exact Hctx1 | lia] |].
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (sp - sp0));
[reflexivity | cbn [ew ewset Nat.eqb]; rewrite ?(AG 2%nat) by lia; rewrite Usp; lia | cbn; lia | cbn; lia | awr_ok_tac]. }
assert (HBB1 : blocks_bytes S1 <= blocks_bytes Sc + 72) by (rewrite (blocks_bytes_bsum B ly1 S1), (blocks_bytes_bsum B lyc Sc), Ebl1, bsum_app; cbn; lia).
clear HF HFr HG.
rregU HS (10%bv : bv 5) (2 * idl * idl) ltac:(apply (U_tisz _ 13 idl); [eatom AG E13 | exact Hidl]) Ra0.
assert (Htisz : 8 <= 2 * idl * idl <= 131072) by (clear - Hidl; nia).
assert (HSZ2 : 0 <= 2 * idl * idl < MALLOC_MAX /\ blocks_bytes S1 + 2 * idl * idl <= LIVE_MAX) by (clear - HMM HBB1 Hlive Htisz; rewrite HMM; unfold LIVE_MAX in *; lia).
malloc_site HS HJ2 (2 * idl * idl) ltac:(exact Ra0) AG Usp Rctx Hom HSZ2.
cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & ti & -> & HJ3 & HP3 & Ha03 & Hfrs3 & Hres3). clear Ra0.
assert (HBB3 : blocks_bytes S3 <= blocks_bytes Sc + (72 + 2 * idl * idl)) by (pose proof (blocks_bytes_after_malloc B _ _ _ _ _ _ _ _ Hres3 ltac:(lia)); lia).
assert (Hctx3 : In (ctx, 72) (ablocks B ly3 S3)).
{ destruct Hres3 as [(_ & -> & _) | (_ & -> & _)]; [exact Hctx1 | apply in_app_iff; left; exact Hctx1]. }
pose proof (perm_tab_update _ _ _ [(0, 2 * (lzw_MR nP idl + nP + 2))] _ ti _ _ _ HB1 Hres3) as HB3. cbn [app] in HB3.
assert (TOK3 : forall b, In b ((ctx, 72) :: tnz [(0, 2 * (lzw_MR nP idl + nP + 2)); (ti, 2 * idl * idl); (0, 8192); (0, 4096); (0, 8192); (0, 4098 * idl)]) ->
4096 <= fst b /\ 0 <= snd b /\ aftok FP (ablocks B lyc Sc) b /\
forall blc lyq i, In b blc -> 0 <= i < req_size (snd b) -> awr_byte STK sp0 FP (ablocks B lyc Sc) blc lyq own (fst b + i)).
{ intros b [<- | Hb]; [apply TOK1; left; reflexivity|].
destruct (in_tnz_update [(0, 2 * (lzw_MR nP idl + nP + 2))] _ ti _ b Hb) as [-> | Hb']; [| apply TOK1; right; exact Hb'].
cbn [fst snd]. destruct Hres3 as [(Hz0 & _ & _) | (Hnz & Ebl & _)].
{ exfalso. subst ti. exact (tnz_fst_nz _ _ Hb eq_refl). }
split; [exact Hnz|]. split; [lia|]. split; [exact (aftok_new_block SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ti _ HJ2 (proj1 HJ3) Ebl ltac:(lia))|].
intros blc lyq i Hin Hi. exact (awr_new_block SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ti _ blc i lyq HJ2 (proj1 HJ3) Ebl ltac:(lia) Hin Hi). }
destruct Hres3 as [(Hti0 & Ebl3 & HK3) | (Hti4096 & Ebl3 & HK3)].
{
reseat HS HJ3 HP3 [0%nat; 1%nat] AG ltac:(first [kept_malloc HK3 HJ3 AG Usp | kept_ctx HK3 HJ3 Hctx3 Hctx1 Rctx AG Ebl3]).
pose proof (st_ok_pi_pin_reg' _ _ _ (10%bv : bv 5) 0 HS ltac:(cbn [ms_regs restrict mkst]; rewrite Ha03, Hti0; reflexivity) eq_refl) as HS3.
norm_ss HS3. clear HS. rename HS3 into HS. reshok HS.
subst ti.
paj_run_to_tok RUNTO HS HJ3 SHOK Bspan 0x2138; [obl_ctx HJ3 Hctx3 AG Rctx E32 | awr2 Actx Hctx3 AG Rctx Usp |].
clear HF HFr HG.
to_clean HS HJ3 HB3 TOK3 AG EE Usp Rctx E32 0 0 0 0 0 0 1%nat 0%nat. }
destruct (mres_range B LAWS _ _ _ _ _ _ _ _ _ True _ (proj1 HJ3) (or_intror (conj Hti4096 (conj Ebl3 HK3)))) as [? | (_ & Htih & Hticeil & Hti16 & Hti3)]; [lia|].
reseat HS HJ3 HP3 [0%nat; 1%nat] AG ltac:(first [kept_malloc HK3 HJ3 AG Usp | kept_ctx HK3 HJ3 Hctx3 Hctx1 Rctx AG Ebl3]).
prreg HS (10%bv : bv 5) Rti. rewrite Ha03 in Rti. symmetry in Rti.
lazymatch type of Rti with ew ?Ex ?nx = _ =>
pose proof (req_size_pos' (2 * idl * idl) ltac:(lia)) as Hrq;
pose proof (st_ok_pi_add_fact Ex _ _ nx (PTR 4) HS
ltac:(clear HS; idtac; unfold afact_ok, PTR; cbn [af_lo af_hi af_al2]; rewrite Rti, unsigned_lit_small by lia;
change (2 ^ 4) with 16; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS. reshok HS.
paj_run_tok RUN HS HJ3 SHOK Bspan; [obl_ctx HJ3 Hctx3 AG Rctx E32 | awr2 Actx Hctx3 AG Rctx Usp |].
clear HF HFr HG.
prreg HS (10%bv : bv 5) Ra0.
assert (HSZ3 : 0 <= 8192 < MALLOC_MAX /\ blocks_bytes S3 + 8192 <= LIVE_MAX) by (clear - HMM HBB3 Hlive Htisz; rewrite HMM; unfold LIVE_MAX in *; lia).
malloc_site HS HJ3 8192 ltac:(exact Ra0) AG Usp Rctx Hom HSZ3. clear Ra0.
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & lm & -> & HJ4 & HP4 & Ha04 & Hfrs4 & Hres4).
assert (HBB4 : blocks_bytes S4 <= blocks_bytes Sc + (72 + 2 * idl * idl + 8192)) by (pose proof (blocks_bytes_after_malloc B _ _ _ _ _ _ _ _ Hres4 ltac:(lia)); lia).
destruct (mres_kept B _ _ _ _ _ _ _ _ _ _ _ _ Hres4) as (HK4 & Hsub4 & Hlm_in).
pose proof (mres_range B LAWS _ _ _ _ _ _ _ _ _ _ _ (proj1 HJ4) Hres4) as Hrr4.
assert (Hctx4 : In (ctx, 72) (ablocks B ly4 S4)) by (apply Hsub4; exact Hctx3).
pose proof (perm_tab_update _ _ _ [(0, 2 * (lzw_MR nP idl + nP + 2)); (ti, 2 * idl * idl)] _ lm _ _ _ HB3 Hres4) as HB4. cbn [app] in HB4.
assert (TOK4 : forall b, In b ((ctx, 72) :: tnz [(0, 2 * (lzw_MR nP idl + nP + 2)); (ti, 2 * idl * idl); (lm, 8192); (0, 4096); (0, 8192); (0, 4098 * idl)]) ->
4096 <= fst b /\ 0 <= snd b /\ aftok FP (ablocks B lyc Sc) b /\
forall blc lyq i, In b blc -> 0 <= i < req_size (snd b) -> awr_byte STK sp0 FP (ablocks B lyc Sc) blc lyq own (fst b + i)).
{ intros b [<- | Hb]; [apply TOK3; left; reflexivity|].
destruct (in_tnz_update [(0, 2 * (lzw_MR nP idl + nP + 2)); (ti, 2 * idl * idl)] _ lm _ b Hb) as [-> | Hb']; [| apply TOK3; right; exact Hb'].
cbn [fst snd]. destruct Hres4 as [(Hz0 & _ & _) | (Hnz & Ebl & _)].
{ exfalso. subst lm. exact (tnz_fst_nz _ _ Hb eq_refl). }
split; [exact Hnz|]. split; [lia|]. split; [exact (aftok_new_block SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lm _ HJ3 (proj1 HJ4) Ebl ltac:(lia))|].
intros blc lyq i Hin Hi. exact (awr_new_block SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lm _ blc i lyq HJ3 (proj1 HJ4) Ebl ltac:(lia) Hin Hi). }
reseat HS HJ4 HP4 [0%nat; 1%nat] AG ltac:(first [kept_malloc HK4 HJ4 AG Usp | kept_ctx_m HK4 HJ4 Hctx4 Hctx3 Rctx AG Hres4]).
prreg HS (10%bv : bv 5) Rlm. rewrite Ha04 in Rlm. symmetry in Rlm.
reshok HS.
paj_run_tok RUN HS HJ4 SHOK Bspan; [obl_ctx HJ4 Hctx4 AG Rctx E32 | awr2 Actx Hctx4 AG Rctx Usp |].
clear HF HFr HG.
prreg HS (10%bv : bv 5) Ra0.
assert (HSZ4 : 0 <= 4096 < MALLOC_MAX /\ blocks_bytes S4 + 4096 <= LIVE_MAX) by (clear - HMM HBB4 Hlive Htisz; rewrite HMM; unfold LIVE_MAX in *; lia).
malloc_site HS HJ4 4096 ltac:(exact Ra0) AG Usp Rctx Hom HSZ4. clear Ra0.
cbv beta. intros W5 c5 Hwle5 (ly5 & S5 & regs5 & mem5 & md5 & lc & -> & HJ5 & HP5 & Ha05 & Hfrs5 & Hres5).
assert (HBB5 : blocks_bytes S5 <= blocks_bytes Sc + (72 + 2 * idl * idl + 8192 + 4096)) by (pose proof (blocks_bytes_after_malloc B _ _ _ _ _ _ _ _ Hres5 ltac:(lia)); lia).
destruct (mres_kept B _ _ _ _ _ _ _ _ _ _ _ _ Hres5) as (HK5 & Hsub5 & Hlc_in).
pose proof (mres_range B LAWS _ _ _ _ _ _ _ _ _ _ _ (proj1 HJ5) Hres5) as Hrr5.
assert (Hctx5 : In (ctx, 72) (ablocks B ly5 S5)) by (apply Hsub5; exact Hctx4).
pose proof (perm_tab_update _ _ _ [(0, 2 * (lzw_MR nP idl + nP + 2)); (ti, 2 * idl * idl); (lm, 8192)] _ lc _ _ _ HB4 Hres5) as HB5. cbn [app] in HB5.
assert (TOK5 : forall b, In b ((ctx, 72) :: tnz [(0, 2 * (lzw_MR nP idl + nP + 2)); (ti, 2 * idl * idl); (lm, 8192); (lc, 4096); (0, 8192); (0, 4098 * idl)]) ->
4096 <= fst b /\ 0 <= snd b /\ aftok FP (ablocks B lyc Sc) b /\
forall blc lyq i, In b blc -> 0 <= i < req_size (snd b) -> awr_byte STK sp0 FP (ablocks B lyc Sc) blc lyq own (fst b + i)).
{ intros b [<- | Hb]; [apply TOK4; left; reflexivity|].
destruct (in_tnz_update [(0, 2 * (lzw_MR nP idl + nP + 2)); (ti, 2 * idl * idl); (lm, 8192)] _ lc _ b Hb) as [-> | Hb']; [| apply TOK4; right; exact Hb'].
cbn [fst snd]. destruct Hres5 as [(Hz0 & _ & _) | (Hnz & Ebl & _)].
{ exfalso. subst lc. exact (tnz_fst_nz _ _ Hb eq_refl). }
split; [exact Hnz|]. split; [lia|]. split; [exact (aftok_new_block SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lc _ HJ4 (proj1 HJ5) Ebl ltac:(lia))|].
intros blc lyq i Hin Hi. exact (awr_new_block SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lc _ blc i lyq HJ4 (proj1 HJ5) Ebl ltac:(lia) Hin Hi). }
reseat HS HJ5 HP5 [0%nat; 1%nat] AG ltac:(first [kept_malloc HK5 HJ5 AG Usp | kept_ctx_m HK5 HJ5 Hctx5 Hctx4 Rctx AG Hres5]).
prreg HS (10%bv : bv 5) Rlc. rewrite Ha05 in Rlc. symmetry in Rlc.
reshok HS.
paj_run_tok RUN HS HJ5 SHOK Bspan; [obl_ctx HJ5 Hctx5 AG Rctx E32 | awr2 Actx Hctx5 AG Rctx Usp |].
clear HF HFr HG.
prreg HS (10%bv : bv 5) Ra0.
assert (HSZ5 : 0 <= 8192 < MALLOC_MAX /\ blocks_bytes S5 + 8192 <= LIVE_MAX) by (clear - HMM HBB5 Hlive Htisz; rewrite HMM; unfold LIVE_MAX in *; lia).
malloc_site HS HJ5 8192 ltac:(exact Ra0) AG Usp Rctx Hom HSZ5. clear Ra0.
cbv beta. intros W6 c6 Hwle6 (ly6 & S6 & regs6 & mem6 & md6 & li & -> & HJ6 & HP6 & Ha06 & Hfrs6 & Hres6).
assert (HBB6 : blocks_bytes S6 <= blocks_bytes Sc + (72 + 2 * idl * idl + 8192 + 4096 + 8192)) by (pose proof (blocks_bytes_after_malloc B _ _ _ _ _ _ _ _ Hres6 ltac:(lia)); lia).
destruct (mres_kept B _ _ _ _ _ _ _ _ _ _ _ _ Hres6) as (HK6 & Hsub6 & Hli_in).
pose proof (mres_range B LAWS _ _ _ _ _ _ _ _ _ _ _ (proj1 HJ6) Hres6) as Hrr6.
assert (Hctx6 : In (ctx, 72) (ablocks B ly6 S6)) by (apply Hsub6; exact Hctx5).
pose proof (perm_tab_update _ _ _ [(0, 2 * (lzw_MR nP idl + nP + 2)); (ti, 2 * idl * idl); (lm, 8192); (lc, 4096)] _ li _ _ _ HB5 Hres6) as HB6. cbn [app] in HB6.
assert (TOK6 : forall b, In b ((ctx, 72) :: tnz [(0, 2 * (lzw_MR nP idl + nP + 2)); (ti, 2 * idl * idl); (lm, 8192); (lc, 4096); (li, 8192); (0, 4098 * idl)]) ->
4096 <= fst b /\ 0 <= snd b /\ aftok FP (ablocks B lyc Sc) b /\
forall blc lyq i, In b blc -> 0 <= i < req_size (snd b) -> awr_byte STK sp0 FP (ablocks B lyc Sc) blc lyq own (fst b + i)).
{ intros b [<- | Hb]; [apply TOK5; left; reflexivity|].
destruct (in_tnz_update [(0, 2 * (lzw_MR nP idl + nP + 2)); (ti, 2 * idl * idl); (lm, 8192); (lc, 4096)] _ li _ b Hb) as [-> | Hb']; [| apply TOK5; right; exact Hb'].
cbn [fst snd]. destruct Hres6 as [(Hz0 & _ & _) | (Hnz & Ebl & _)].
{ exfalso. subst li. exact (tnz_fst_nz _ _ Hb eq_refl). }
split; [exact Hnz|]. split; [lia|]. split; [exact (aftok_new_block SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ li _ HJ5 (proj1 HJ6) Ebl ltac:(lia))|].
intros blc lyq i Hin Hi. exact (awr_new_block SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ li _ blc i lyq HJ5 (proj1 HJ6) Ebl ltac:(lia) Hin Hi). }
reseat HS HJ6 HP6 [0%nat; 1%nat] AG ltac:(first [kept_malloc HK6 HJ6 AG Usp | kept_ctx_m HK6 HJ6 Hctx6 Hctx5 Rctx AG Hres6]).
prreg HS (10%bv : bv 5) Rli. rewrite Ha06 in Rli. symmetry in Rli.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
eapply (tlzw_pro9 B TL LAWS ML AMALLOC AFREE HUL Ex W6 regs6 mem6 md6 STK sp0 FP lyc Sc W memc mdc own ly6 S6 regs pR nP img idl icl bi Li ctx ti lm lc li) | st_ok _ ?Ex _ _ =>
eapply (tlzw_pro9 B TL LAWS ML AMALLOC AFREE HUL Ex W6 regs6 mem6 md6 STK sp0 FP lyc Sc W memc mdc own ly6 S6 regs pR nP img idl icl bi Li ctx ti lm lc li)  end.
- exact HS.
- assumption.
- exact HJ6.
- intros n rr Hn Hrr. rewrite (AG n) by lia. apply EE. exact Hrr.
- rewrite (AG 32%nat) by lia. exact E32.
- exact Rctx. - exact Rti. - exact Rlm. - exact Rlc. - exact Rli.
- exact Hra0. - exact Hgp. - exact Htp. - exact G10. - exact G11. - exact G12. - exact G13. - exact G14.
- exact Hal16. - exact Hwlo. - exact Hwhi. - exact HpR8. - exact HpR0. - exact HpR63. - exact HnP. - exact Hidl. - exact Hicl.
- exact Hbi. - exact Hbi1. - exact Hbi2. - exact Hev. - exact Hlive.
- exact HB6.
- exact TOK6.
- exact Hti4096.
- exact Hticeil.
- clear - Hrr4 C1 C3. destruct Hrr4 as [-> | (H1 & H2 & H3 & _)]; [left; reflexivity | right]. pose proof (req_size_pos' 8192 ltac:(lia)). lia.
- clear - Hrr5 C1 C3. destruct Hrr5 as [-> | (H1 & H2 & H3 & _)]; [left; reflexivity | right]. pose proof (req_size_pos' 4096 ltac:(lia)). lia.
- clear - Hrr6 C1 C3. destruct Hrr6 as [-> | (H1 & H2 & H3 & _)]; [left; reflexivity | right]. pose proof (req_size_pos' 8192 ltac:(lia)). lia.
- exact HBB6.
- rewrite Hfrs6, Hfrs5, Hfrs4, Hfrs3. exact Hfrs1.
Qed.
End f.
End e.
End d.
