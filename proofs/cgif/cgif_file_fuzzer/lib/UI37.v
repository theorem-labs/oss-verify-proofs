(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YM06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YN32 YK0w.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 UN3b UN3c
YI06 UI5b YI09 YI08 YI0t YI0r YI0o YI0s YI6a UI3n UI3o UI3p UI3k.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI0u UI30 UI3g UI3e UIZ2.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition ss_tinit : sstate :=
tlzw_ss0 TPC_INIT sr_atoms true [] [] [] [].
Definition ss_tinit_c : sstate := Eval vm_compute in ss_tinit.
Lemma arr16_u16s_t : forall mem base l, arr16 ubs0segs mem base l -> u16s l.
Proof using. intros mem base l H. unfold u16s. apply Forall_nth_Z. intros j Hj. exact (proj2 (H j Hj)). Qed.
Definition tinit_np_region : YP09.region := YP09.mkRegion (Some 8%nat) 56 60 0 0 [mkChunk 56 (CVal 4 (SOff 39%nat 0))].
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Hypothesis RESET : reset_specV API.
Lemma tlzw_init_runV :
forall cx STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) (memc : word -> option byte) (TM0 : list Z) (PIX : list Z),
tcx_ok cx -> tcx_ranges cx -> tcx_seps cx -> tcx_blocks cx (blocks Lc Ac) -> tcx_win STK sp0 cx ->
tcx_wtok STK sp0 FP (blocks L A) cx ->
journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc ->
tlzw_regs_fix regs cx -> gen_at memc cx 0 0 0 ->
arr16 ubs0segs memc (y_tm cx) TM0 -> length TM0 = Z.to_nat (2049 * y_idl cx) ->
garr8 ubs0segs memc (y_img cx) PIX -> length PIX = Z.to_nat (y_nP cx) ->
SR ubs0segs (mkCfg (mkst regs (Z_to_bv 64 TPC_INIT) memc (seg_rom ubs0segs)) mdc)
(fun c' => exists regsH memH,
c' = mkCfg (mkst regsH (Z_to_bv 64 TPC_HEAD) memH (seg_rom ubs0segs)) mdc /\
journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac memH mdc /\
tlzw_regs_fix regsH cx /\
gen_at memH cx 1 (y_idl cx + 2) 1 /\
ttables_at memH cx (lzw_init (y_idl cx) TM0) /\ lzw_inv (y_idl cx) (y_nP cx) (lzw_init (y_idl cx) TM0) /\
getr regsH 11 = Z_to_bv 64 (y_nP cx) /\ getr regsH 22 = Z_to_bv 64 0 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ rd_written cx 0 a -> ~ (y_sp cx - RESET_STK <= a < y_sp cx) ->
(alloc_ceiling <= a \/ exists b m, In (b, m) (blocks Lc Ac) /\ b <= a < b + m) ->
mbyte ubs0segs memH a = mbyte ubs0segs memc a) /\
vtabs_at memH cx PIX (mkLV (repeat 0 4096) [y_idl cx]) /\ vinv cx PIX (lzw_init (y_idl cx) TM0) (mkLV (repeat 0 4096) [y_idl cx])).
Proof using IMG LAWS RESET.
intros cx STK sp0 FP L A mem md Lc Ac mdc regs memc TM0 PIX HCX HRG HSEP HBL HWIN HWT HJ HFX HGA ATM LenTM GPIX LenPIX.
pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof HJ as (HH & _ & _ & _ & _ & (_ & _ & Hceil & _ & _) & _).
pose proof HCX as (Hidl & HnP & HMR & HMR0 & Hicl & Hal16 & Hsplo & Hsphi & HpR1 & HpR2 & HpR3 & HpR8 & Hbi1 & Hbi2 & Hbi3 & Hbi4 & Hgp).
pose proof HRG as ((Rti1 & Rti2 & Rti3 & Rti4) & (Rlm1 & Rlm2 & Rlm3 & _) & (Rlc1 & Rlc2 & Rlc3 & _) & (Rli1 & Rli2 & Rli3 & _) &
(Rtm1 & Rtm2 & Rtm3 & Rtm4) & (Rld1 & Rld2 & Rld3 & Rld4) & (Rg1 & Rg2 & Rg3 & _) & _).
pose proof HBL as [HBt HBi]. destruct HWIN as [W1 W2].
pose proof HFX as (F2 & F8 & F20 & F21 & F18 & F19 & F9 & F4 & F3).
unfold y_tisz, y_tmsz, y_cap, cap in *. cbn [fst snd] in Rti1, Rti2, Rti3, Rti4, Rtm1, Rtm2, Rtm3, Rtm4, Rld1, Rld2, Rld3, Rld4.
assert (Htisz : 8 <= 2 * y_idl cx * y_idl cx <= 131072) by (apply ttisz_range; exact Hidl).
pose proof HGA as (V0 & V8 & V16 & V24 & V32 & V40 & V48 & V56 & V60 & V64 & V66).
remember (@nil word) as more eqn:Hmore.
remember (Ereg regs (tcx_extra cx 0 0 0 ++ more)) as E eqn:HE0.
pose proof (TE_sp regs cx 0 0 0 more HFX) as HE2. pose proof (TE_g regs cx 0 0 0 more HFX) as HE8.
pose proof (TE_idl regs cx 0 0 0 more HFX) as HE20.
pose proof (TE_nP regs cx 0 0 0 more) as HE39. pose proof (TE_lp regs cx 0 0 0 more) as HE41.
rewrite <- HE0 in HE2, HE8, HE20, HE39, HE41.
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HS : st_ok ubs0segs E ss_tinit_c (mkst regs (Z_to_bv 64 TPC_INIT) memc (seg_rom ubs0segs))).
{ change ss_tinit_c with ss_tinit. unfold ss_tinit. rewrite HE0.
apply (tlzw_st_ok0 cx regs 0 0 0 more memc TPC_INIT true); rewrite <- ?HE0.
- exact HCX.
- exact HRG.
- exact HFX.
- exact HGA.
- intros _ a Ha. apply (present_writable ubs0_msyms). replace a with (y_g cx + (a - y_g cx)) by lia.
apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ (y_g cx) 72 (a - y_g cx) HH ltac:(apply HBt; cbv; tauto) ltac:(lia))).
- lia.
- lia.
- lia.
- vm_compute; reflexivity.
- apply Forall_nil.
- exact I.
- exact I.
- exact I.
- exact I.
- exact I. }
change memc with (ms_mem (mkst regs (Z_to_bv 64 TPC_INIT) memc (seg_rom ubs0segs))) in HJ.
pose proof (HWT (y_g cx, 72) ltac:(cbv; tauto)) as Wg.
jrun_to LAWS ubs0tbl_ok HS HJ ubs0_A_resetDict.
{ wr_norm.
eapply (wr_ok_cons_gen _ _ _ _ _ _ _ _ 8 (y_g cx)); [reflexivity | rewrite HE8; apply unsigned_lit_small; lia | |].
{ cbn [r_wlo r_whi gen_region]. intros a Ha. replace a with (y_g cx + (a - y_g cx)) by lia.
apply (Wg (blocks Lc Ac)); [apply HBt; cbv; tauto | cbn [snd]; lia]. }
apply wr_ok_nil. }
lazymatch goal with HF1 : frame_of _ _ _ ?m' |- _ =>
assert (M1 : forall a, 0 <= a < 2 ^ 64 -> ~ (y_g cx + 60 <= a < y_g cx + 68) ->
mbyte ubs0segs m' a = mbyte ubs0segs (ms_mem (mkst regs (Z_to_bv 64 TPC_INIT) memc (seg_rom ubs0segs))) a)
by (intros a Ha Hn1; eapply (tframe_mbyte_list E _ _ _ [(y_g cx + 60, y_g cx + 68)] a HF1 Ha);
[ repeat (apply Forall2_cons; [right; cbn [fst snd r_base r_wlo r_whi gen_region base_val]; rewrite ?HE8, ?unsigned_lit_small by lia; lia|]); apply Forall2_nil
| cbn; tauto ]);
clear HF1
end.
cbn [ms_mem mkst] in M1.
lazymatch type of HS with st_ok _ _ _ ?ms1 =>
assert (U60 : val_mem ubs0segs (ms_mem ms1) (y_g cx + 60) 4 0)
end.
{ pose proof (tst_ok_region_nth E _ _ 0 _ HS eq_refl) as HRg.
assert (G8 : bv_unsigned (ew E 8) = y_g cx) by (rewrite HE8; apply unsigned_lit_small; lia).
change 4%nat with (N.to_nat 4). eapply (tval_mem_of_chunk E _ _ 8%nat (y_g cx) 60 4); [exact HRg | reflexivity | cbv; tauto | exact G8 | | cbn; lia | cbn; lia].
cbn [sv_denot]. rewrite ?HE41, ?Z.add_0_r, ?unsigned_lit_small by lia. reflexivity. }
Local Ltac vm1 M1 V := intros k Hk; rewrite M1; [apply V; exact Hk | cbn in Hk; lia | cbn in Hk; lia].
lazymatch type of HS with st_ok _ _ _ ?ms1 =>
assert (U0 : val_mem ubs0segs (ms_mem ms1) (y_g cx) 8 (y_ti cx)) by vm1 M1 V0;
assert (U8 : val_mem ubs0segs (ms_mem ms1) (y_g cx + 8) 8 (y_lm cx)) by vm1 M1 V8;
assert (U16 : val_mem ubs0segs (ms_mem ms1) (y_g cx + 16) 8 (y_lc cx)) by vm1 M1 V16;
assert (U24 : val_mem ubs0segs (ms_mem ms1) (y_g cx + 24) 8 (y_li cx)) by vm1 M1 V24;
assert (U40 : val_mem ubs0segs (ms_mem ms1) (y_g cx + 40) 8 (y_ld cx)) by vm1 M1 V40
end.
jreg HS (10%bv:reg) as C10. jreg HS (11%bv:reg) as C11. jreg HS (1%bv:reg) as C1. jreg HS (2%bv:reg) as C2. jreg HS (4%bv:reg) as C4.
lazymatch type of HS with st_ok _ _ _ ?ms1 =>
assert (Hspc : spZ (ms_regs ms1) = y_sp cx) by (unfold spZ; first [rewrite C2 | rewrite <- C2]; rewrite HE2; apply unsigned_lit_small; lia)
end.
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_bind.
{ eapply (RESET Lc Ac _ _ _ (y_g cx) (y_ti cx) (y_lm cx) (y_lc cx) (y_li cx) (y_ld cx) (2 * (y_nP cx + 2 + y_MR cx)) (y_idl cx) 0).
- eapply fn_pre_of_journal; [exact HJ | | | | | |].
+ first [rewrite C1 | rewrite <- C1]. apply ret_ok_even. vm_compute. reflexivity.
+ rewrite Hspc. exact Hal16.
+ unfold RESET_STK. lia.
+ rewrite Hspc. unfold RESET_STK. lia.
+ rewrite Hspc. lia.
+ first [rewrite C4 | rewrite <- C4]. rewrite (HE 4%nat (4%bv:reg) eq_refl). exact F4.
- first [rewrite C10 | rewrite <- C10]. exact HE8.
- first [rewrite C11 | rewrite <- C11]. exact HE20.
- lia.
- lia.
- lia.
- apply HBt. cbv [tcx_tabs In]. tauto.
- apply HBt. cbv [tcx_tabs y_tisz In]. tauto.
- apply HBt. cbv [tcx_tabs In]. tauto.
- apply HBt. cbv [tcx_tabs In]. tauto.
- apply HBt. cbv [tcx_tabs In]. tauto.
- apply HBt. cbv [tcx_tabs y_cap cap In]. tauto.
- apply tcx_nodup; assumption.
- exact U0.
- exact U8.
- exact U16.
- exact U24.
- exact U40.
- exact U60. }
cbv beta. intros c' (regs9 & mem9 & -> & HJc & HPc & W60 & W64 & W66 & WLD & Z1 & Z2 & Z3 & Z4).
rewrite Z.mul_0_r, Z.add_0_r in WLD.
first [rewrite C1 | rewrite <- C1].
assert (HJ2 : journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac mem9 mdc).
{ eapply (journal_sub_gen _ _ LAWS); [exact HJ | exact HJc | rewrite Hspc; unfold RESET_STK; lia | rewrite Hspc; lia |].
intros a Ha. exact (rd_fp_sub cx STK sp0 FP L A Lc Ac 0 HRG HBL HWT Hceil ltac:(lia) ltac:(unfold y_cap, cap; lia) a Ha). }
assert (KB : forall b n i, In (b, n) (blocks Lc Ac) -> 0 <= i < n -> ~ rd_written cx 0 (b + i) ->
mbyte ubs0segs mem9 (b + i) = mbyte ubs0segs memc (b + i)).
{ intros b n i Hb Hi Hnw.
destruct (heap_blocks _ _ LAWS _ _ _ _ b n i HH Hb Hi) as (_ & Hb1 & Hb2 & _).
rewrite <- (M1 (b + i) ltac:(lia) ltac:(intros Hg; apply Hnw; left; exact Hg)).
exact (journal_blocks_kept _ _ _ _ _ _ _ _ _ _ _ _ _ HJc b n i Hb Hb Hi (fun Hf => Hnw (rd_fp_written cx 0 _ Hf))). }
assert (KH : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (y_sp cx - RESET_STK <= a < y_sp cx) -> mbyte ubs0segs mem9 a = mbyte ubs0segs memc a).
{ intros a Ha Hna. rewrite <- (M1 a ltac:(lia) ltac:(lia)).
exact (proj1 (journal_high_kept _ _ _ _ _ _ _ _ _ _ _ _ _ HJc a ltac:(lia) ltac:(rewrite Hspc; exact Hna))). }
assert (FR9 : forall a, 0 <= a < 2 ^ 64 -> ~ rd_written cx 0 a -> ~ (y_sp cx - RESET_STK <= a < y_sp cx) ->
(alloc_ceiling <= a \/ exists b m, In (b, m) (blocks Lc Ac) /\ b <= a < b + m) ->
mbyte ubs0segs mem9 a = mbyte ubs0segs memc a).
{ intros a Ha Hnw Hns [Hhi | (b & m & Hb & Hr)]; [apply KH; [lia | exact Hns]|].
replace a with (b + (a - b)) by lia. apply (KB b m); [exact Hb | lia | replace (b + (a - b)) with a by lia; exact Hnw]. }
assert (G56 : val_mem ubs0segs mem9 (y_g cx + 56) 4 (y_nP cx)).
{ intros k Hk. replace (y_g cx + 56 + Z.of_nat k) with (y_g cx + (56 + Z.of_nat k)) by lia.
rewrite (KB (y_g cx) 72); [| apply HBt; cbv [tcx_tabs In]; tauto | cbn in Hk; lia |].
- replace (y_g cx + (56 + Z.of_nat k)) with (y_g cx + 56 + Z.of_nat k) by lia. apply V56. exact Hk.
- unfold rd_written, y_tisz. rsep HSEP 0%nat 6%nat. rsep HSEP 1%nat 6%nat. rsep HSEP 2%nat 6%nat. rsep HSEP 3%nat 6%nat. rsep HSEP 5%nat 6%nat.
cbn in Hk. lia. }
jafter_call_keep HS 44%nat regs9 mem9 HPc (@nil nat) HS2.
specialize (HS2 ltac:(constructor)). clear HS HJ. rename HS2 into HS. rename HJ2 into HJ.
lazymatch type of HS with st_ok ?segs ?E1 ?ss1 ?ms1 =>
pose proof (st_ok_add_region' segs E1 ss1 ms1 tinit_np_region HS ltac:(vm_compute; reflexivity)) as HS2 end.
match type of HS2 with ?P -> ?Q -> _ => assert (HRo : P); [| assert (HRd : Q); [| specialize (HS2 HRo HRd); clear HRo HRd HS]] end.
{ unfold region_ok, tinit_np_region. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val ms_mem mkst].
ew_havoc. rewrite HE8, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
eapply chunk_ok_val; [ cbn [sv_denot]; ew_havoc; rewrite HE39, unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity | cbn; lia | cbn; lia | exact G56 ]. }
{ cbn [all_disjoint ss_mem]. exact I. }
lazymatch type of HS2 with st_ok _ _ ?ss2 _ => let v := eval vm_compute in ss2 in change ss2 with v in HS2 end.
rename HS2 into HS.
lazymatch type of HS with st_ok _ _ _ ?msx => change mem9 with (ms_mem msx) in HJ end.
jrun_to LAWS ubs0tbl_ok HS HJ TPC_HEAD; [first [apply wr_ok_nil | wr_ok_tac]|].
lazymatch goal with HF1 : frame_of _ _ _ _ |- _ => pose proof (tframe_of_ro' _ _ _ _ HF1 ltac:(vm_compute; reflexivity)) as Hm3; clear HF1 end.
cbn [ms_mem mkst] in Hm3.
lazymatch type of HS with st_ok _ _ _ ?msx =>
assert (MF : forall a, mbyte ubs0segs (ms_mem msx) a = mbyte ubs0segs mem9 a) by (intros a; apply tmbyte_eq_of1; apply Hm3)
end.
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc]. apply SR_ret.
lazymatch type of HS with st_ok _ _ _ ?msx => exists (ms_regs msx), (ms_mem msx) end.
split; [reflexivity|]. split; [exact HJ|].
lazymatch type of HS with st_ok _ ?E4 ?ss4 ?ms4 =>
assert (QF : forall r, In r TREGS_FIXL -> getr (ms_regs ms4) r = getr regs r)
by (pose proof (regs_kept_of_st_ok _ _ _ _ regs (tcx_extra cx 0 0 0 ++ more) TREGS_FIXL HS
ltac:(rewrite HE0; repeat (apply env_agree_havoc_ge; [cbv; lia|]); apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HK; exact HK)
end.
split; [apply (tlzw_regs_fix_kept regs); [exact HFX | exact QF]|].
assert (GK : forall a, y_g cx <= a < y_g cx + 60 -> mbyte ubs0segs mem9 a = mbyte ubs0segs memc a).
{ intros a Ha. replace a with (y_g cx + (a - y_g cx)) by lia. apply (KB (y_g cx) 72); [apply HBt; cbv [tcx_tabs In]; tauto | lia |].
unfold rd_written, y_tisz. rsep HSEP 0%nat 6%nat. rsep HSEP 1%nat 6%nat. rsep HSEP 2%nat 6%nat. rsep HSEP 3%nat 6%nat. rsep HSEP 5%nat 6%nat. lia. }
split.
{ unfold gen_at. repeat split.
- intros k Hk. rewrite MF, GK; [apply V0; exact Hk | cbn in Hk; lia].
- intros k Hk. rewrite MF, GK; [apply V8; exact Hk | cbn in Hk; lia].
- intros k Hk. rewrite MF, GK; [apply V16; exact Hk | cbn in Hk; lia].
- intros k Hk. rewrite MF, GK; [apply V24; exact Hk | cbn in Hk; lia].
- intros k Hk. rewrite MF, GK; [apply V32; exact Hk | cbn in Hk; lia].
- intros k Hk. rewrite MF, GK; [apply V40; exact Hk | cbn in Hk; lia].
- intros k Hk. rewrite MF, GK; [apply V48; exact Hk | cbn in Hk; lia].
- intros k Hk. rewrite MF, GK; [apply V56; exact Hk | cbn in Hk; lia].
- intros k Hk. rewrite MF. apply W60. exact Hk.
- intros k Hk. rewrite MF. apply W64. exact Hk.
- intros k Hk. rewrite MF. apply W66. exact Hk. }
split.
{ unfold ttables_at. cbn [la_TI la_LM la_LI la_TM lzw_init].
split; [|split; [|split]].
- apply arr16_zeros. intros a Ha. rewrite Z2Nat.id in Ha by nia. rewrite MF. replace a with (y_ti cx + (a - y_ti cx)) by lia. apply Z1. nia.
- apply arr16_zeros. intros a Ha. change (Z.of_nat 4096) with 4096 in Ha. rewrite MF. replace a with (y_lm cx + (a - y_lm cx)) by lia. apply Z2. lia.
- apply arr16_zeros. intros a Ha. change (Z.of_nat 4096) with 4096 in Ha. rewrite MF. replace a with (y_li cx + (a - y_li cx)) by lia. apply Z4. lia.
- eapply arr16_frame; [exact ATM|]. intros a Ha. rewrite LenTM, Z2Nat.id in Ha by lia. rewrite MF.
replace a with (y_tm cx + (a - y_tm cx)) by lia. apply (KB (y_tm cx) (4098 * y_idl cx)); [apply HBt; cbv [tcx_tabs y_tmsz In]; tauto | lia |].
unfold rd_written, y_tisz. rsep HSEP 0%nat 4%nat. rsep HSEP 1%nat 4%nat. rsep HSEP 2%nat 4%nat. rsep HSEP 3%nat 4%nat.
rsep HSEP 4%nat 5%nat. rsep HSEP 4%nat 6%nat. lia. }
split. { apply inv_init; [exact Hidl | lia | exact LenTM | eapply arr16_u16s_t; exact ATM]. }
split; [treg_val HS (11%bv:reg)|]. split; [treg_val HS (22%bv:reg)|].
assert (FRH : forall a, 0 <= a < 2 ^ 64 -> ~ rd_written cx 0 a -> ~ (y_sp cx - RESET_STK <= a < y_sp cx) ->
(alloc_ceiling <= a \/ exists b m, In (b, m) (blocks Lc Ac) /\ b <= a < b + m) ->
mbyte ubs0segs ltac:(lazymatch type of HS with st_ok _ _ _ ?msx => exact (ms_mem msx) end) a = mbyte ubs0segs memc a)
by (intros a Ha Hnw Hns Hin; rewrite MF; exact (FR9 a Ha Hnw Hns Hin)).
split; [exact FRH|].
split; [| split; [reflexivity | split; [exact LenPIX | reflexivity]]].
lazymatch type of HS with st_ok _ _ _ ?msx =>
eapply (vtabs_init memc (ms_mem msx) cx PIX (fun a => ~ (y_img cx <= a < y_img cx + y_nP cx)) (y_idl cx) GPIX LenPIX ltac:(lia)) end.
- intros a Ha HW. apply FRH; [exact Ha | | | right; exists (y_bi cx), (y_Li cx); split; [exact HBi | lia]].
+ unfold rd_written, y_tisz. rsep HSEP 0%nat 7%nat. rsep HSEP 1%nat 7%nat. rsep HSEP 2%nat 7%nat. rsep HSEP 3%nat 7%nat.
rsep HSEP 5%nat 7%nat. rsep HSEP 6%nat 7%nat.
destruct (Z_lt_le_dec a (y_img cx)); [exfalso; apply HW; lia|]. destruct (Z_lt_le_dec a (y_img cx + y_nP cx)); [lia | exfalso; apply HW; lia].
+ destruct (Z_lt_le_dec a (y_img cx)); [exfalso; apply HW; lia|]. destruct (Z_lt_le_dec a (y_img cx + y_nP cx)); [|exfalso; apply HW; lia].
unfold RESET_STK. lia.
- intros a Ha. split; [lia|]. intros H. exact (H Ha).
- intros a Ha. rewrite MF. replace a with (y_lc cx + (a - y_lc cx)) by lia. apply Z3. lia.
- intros k Hk. rewrite MF. apply WLD. exact Hk.
- lia.
Qed.
End S.
End b.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
