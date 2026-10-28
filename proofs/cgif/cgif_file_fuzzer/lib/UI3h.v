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
YI06 UI5b YI09 YI08 YI0t YI0r YI0o YI0s YI6a UI3n UI3o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI0u UI30 UI3g UIZ2.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Hypothesis RESET : reset_specV API.
Lemma trst_segV : forall cx STK sp0 FP L A mem md Lc Ac mdc regs memc X s' PIX V1,
tcx_ok cx -> tcx_ranges cx -> tcx_seps cx -> tcx_blocks cx (blocks Lc Ac) -> tcx_win STK sp0 cx ->
tcx_wtok STK sp0 FP (blocks L A) cx ->
journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc ->
trst_pre cx X s' regs memc ->
vtabs_at memc cx PIX V1 -> length PIX = Z.to_nat (y_nP cx) -> Z.of_nat (length (v_LD V1)) = la_lp X + 1 ->
SR ubs0segs (mkCfg (mkst regs (Z_to_bv 64 TPC_RST) memc (seg_rom ubs0segs)) mdc)
(fun c' => exists regs' mem' X',
c' = mkCfg (mkst regs' (Z_to_bv 64 TPC_TAIL) mem' (seg_rom ubs0segs)) mdc /\
journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac mem' mdc /\ tabove_eq cx memc mem' /\
ttail_post cx X regs' mem' X' /\ la_s X' = s' /\ X' = st_reset (y_idl cx) X (s' - 1) /\
vtabs_at mem' cx PIX (mkLV (repeat 0 4096) (v_LD V1 ++ [y_idl cx]))).
Proof using IMG LAWS RESET.
intros cx STK sp0 FP L A mem md Lc Ac mdc regs memc X s' PIX V1 HCX HRG HSEP HBL HWIN HWT HJ HPRE HVT LenPIX LenLD.
destruct X as [TI LM LI TM s lp0 dp mp Cn R].
destruct HPRE as (HFX & HGA & HT & HI & Hdp4096 & H22 & Hs').
cbn [la_TI la_LM la_LI la_TM la_s la_lp la_dp la_mp] in *.
pose proof HI as (LenTI & LenLM & LenLI & LenTM & BTI & BLI & BLM & UTM & ATMrows & Hdp' & Hmp & HA & HR0 & HRC & HCn & Hlpx & Hs0).
pose proof (lp_head_bound (y_idl cx) (y_nP cx) (y_MR cx) (mkLA TI LM LI TM s lp0 dp mp Cn R)
ltac:(unfold lzw_par; destruct HCX as (Hidl_ & HnP_ & HMR_ & HMR0_ & _); assert (y_MR cx * 3838 <= y_MR cx * (4094 - y_idl cx)) by (apply Z.mul_le_mono_nonneg_l; lia); lia)
HI ltac:(cbn [la_s]; lia)) as Hlpb.
cbn [la_lp] in Hlpb. unfold cap in Hlpb.
destruct HT as (ATI & ALM & ALI & ATM).
set (lp := lp0 + 1) in *.
assert (Hlp0 : 0 <= lp) by lia. assert (Hlpc : lp < y_cap cx) by (unfold y_cap, cap; lia). assert (Hlpm : lp <= 134217726).
{ destruct HCX as (Hidl_ & HnP_ & HMR_ & HMR0_ & _). assert (y_MR cx * 3838 <= y_MR cx * (4094 - y_idl cx)) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
assert (Hmpb : 1 <= mp <= 2047) by (pose proof (mp_bound (y_idl cx) (y_nP cx) (mkLA TI LM LI TM s lp0 dp mp Cn R) ltac:(destruct HCX as (Hidl_ & _); lia) HI) as Hq; cbn [la_mp] in Hq; lia).
pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof HJ as (HH & _ & _ & _ & _ & (_ & _ & Hceil & _ & _) & _).
pose proof HCX as (Hidl & HnP & HMR & HMR0 & Hicl & Hal16 & Hsplo & Hsphi & HpR1 & HpR2 & HpR3 & HpR8 & Hbi1 & Hbi2 & Hbi3 & Hbi4 & Hgp).
pose proof HRG as ((Rti1 & Rti2 & Rti3 & Rti4) & (Rlm1 & Rlm2 & Rlm3 & _) & (Rlc1 & Rlc2 & Rlc3 & _) & (Rli1 & Rli2 & Rli3 & _) &
(Rtm1 & Rtm2 & Rtm3 & Rtm4) & (Rld1 & Rld2 & Rld3 & Rld4) & (Rg1 & Rg2 & Rg3 & _) & _).
pose proof HBL as [HBt HBi]. destruct HWIN as [W1 W2].
pose proof HFX as (F2 & F8 & F20 & F21 & F18 & F19 & F9 & F4 & F3).
unfold y_tisz, y_tmsz, y_cap, cap in *. cbn [fst snd] in Rti1, Rti2, Rti3, Rti4, Rtm1, Rtm2, Rtm3, Rtm4, Rld1, Rld2, Rld3, Rld4.
assert (Htisz : 8 <= 2 * y_idl cx * y_idl cx <= 131072) by (apply ttisz_range; exact Hidl).
remember (@nil word) as more eqn:Hmore.
remember (Ereg regs (tcx_extra cx lp dp mp ++ more)) as E eqn:HE0.
pose proof (TE_sp regs cx lp dp mp more HFX) as HE2. pose proof (TE_g regs cx lp dp mp more HFX) as HE8.
pose proof (TE_idl regs cx lp dp mp more HFX) as HE20.
rewrite <- HE0 in HE2, HE8, HE20.
assert (HE22 : ew E 22 = Z_to_bv 64 s') by (rewrite HE0, (TE_reg regs _ _ _ _ more 22%bv 22) by reflexivity; exact H22).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HS : st_ok ubs0segs E ss_trst (mkst regs (Z_to_bv 64 TPC_RST) memc (seg_rom ubs0segs))).
{ unfold ss_trst, tlzw_ss. rewrite HE0.
apply (tlzw_st_ok cx regs lp dp mp more memc TPC_RST false); rewrite <- ?HE0.
- exact HCX.
- exact HRG.
- exact HFX.
- exact HGA.
- intros X0. discriminate X0.
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
change memc with (ms_mem (mkst regs (Z_to_bv 64 TPC_RST) memc (seg_rom ubs0segs))) in HJ.
jrun_to LAWS ubs0tbl_ok HS HJ ubs0_A_resetDict; [wr_ok_tac|].
lazymatch goal with HF1 : frame_of _ _ _ _ |- _ => pose proof (tframe_of_ro' _ _ _ _ HF1 ltac:(vm_compute; reflexivity)) as Hm1; clear HF1 end.
cbn [ms_mem mkst] in Hm1.
lazymatch type of HS with st_ok _ _ _ ?ms1 =>
assert (M1 : forall a, mbyte ubs0segs (ms_mem ms1) a = mbyte ubs0segs memc a) by (intros a; apply tmbyte_eq_of1; apply Hm1);
pose proof (gen_at_eq _ _ _ _ _ _ HGA Hm1) as (V0 & V8 & V16 & V24 & V32 & V40 & V48 & V56 & V60 & V64 & V66)
end.
jreg HS (10%bv:reg) as C10. jreg HS (11%bv:reg) as C11. jreg HS (1%bv:reg) as C1. jreg HS (2%bv:reg) as C2. jreg HS (4%bv:reg) as C4.
lazymatch type of HS with st_ok _ _ _ ?ms1 =>
assert (Hspc : spZ (ms_regs ms1) = y_sp cx) by (unfold spZ; first [rewrite C2 | rewrite <- C2]; rewrite HE2; apply unsigned_lit_small; lia)
end.
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_bind.
{ eapply (RESET Lc Ac _ _ _ (y_g cx) (y_ti cx) (y_lm cx) (y_lc cx) (y_li cx) (y_ld cx) (2 * (y_nP cx + 2 + y_MR cx)) (y_idl cx) lp).
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
- exact V0.
- exact V8.
- exact V16.
- exact V24.
- exact V40.
- exact V60. }
cbv beta. intros c' (regs9 & mem9 & -> & HJc & HPc & W60 & W64 & W66 & WLD & Z1 & Z2 & Z3 & Z4).
first [rewrite C1 | rewrite <- C1].
assert (HJ2 : journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac mem9 mdc).
{ eapply (journal_sub_gen _ _ LAWS); [exact HJ | exact HJc | rewrite Hspc; unfold RESET_STK; lia | rewrite Hspc; lia |].
intros a Ha. exact (rd_fp_sub cx STK sp0 FP L A Lc Ac lp HRG HBL HWT Hceil Hlp0 ltac:(unfold y_cap, cap; lia) a Ha). }
assert (KB : forall b n i, In (b, n) (blocks Lc Ac) -> 0 <= i < n -> ~ rd_written cx lp (b + i) ->
mbyte ubs0segs mem9 (b + i) = mbyte ubs0segs memc (b + i)).
{ intros b n i Hb Hi Hnw. rewrite <- M1.
exact (journal_blocks_kept _ _ _ _ _ _ _ _ _ _ _ _ _ HJc b n i Hb Hb Hi (fun Hf => Hnw (rd_fp_written cx lp _ Hf))). }
assert (KH : forall a, y_sp cx + 8 <= a < 2 ^ 64 -> mbyte ubs0segs mem9 a = mbyte ubs0segs memc a).
{ intros a Ha. rewrite <- M1.
exact (proj1 (journal_high_kept _ _ _ _ _ _ _ _ _ _ _ _ _ HJc a ltac:(lia) ltac:(rewrite Hspc; unfold RESET_STK; lia))). }
jafter_call_keep HS 44%nat regs9 mem9 HPc (@nil nat) HS2.
specialize (HS2 ltac:(constructor)). clear HS HJ. rename HS2 into HS. rename HJ2 into HJ.
lazymatch type of HS with st_ok _ _ _ ?msx => change mem9 with (ms_mem msx) in HJ end.
jrun_to LAWS ubs0tbl_ok HS HJ TPC_TAIL; [first [apply wr_ok_nil | wr_ok_tac]|].
lazymatch goal with HF1 : frame_of _ _ _ _ |- _ => pose proof (tframe_of_ro' _ _ _ _ HF1 ltac:(vm_compute; reflexivity)) as Hm3; clear HF1 end.
cbn [ms_mem mkst] in Hm3.
lazymatch type of HS with st_ok _ _ _ ?msx =>
assert (MF : forall a, mbyte ubs0segs (ms_mem msx) a = mbyte ubs0segs mem9 a) by (intros a; apply tmbyte_eq_of1; apply Hm3)
end.
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc]. apply SR_ret.
lazymatch type of HS with st_ok _ _ _ ?msx =>
exists (ms_regs msx), (ms_mem msx), (st_reset (y_idl cx) (mkLA TI LM LI TM s lp0 dp mp Cn R) (s' - 1)) end.
split; [reflexivity|]. split; [exact HJ|].
split.
{ intros a Ha. rewrite MF. apply KH. exact Ha. }
pose proof (inv_reset (y_idl cx) (y_nP cx) Hidl _ (s' - 1) HI ltac:(cbn [la_dp]; exact Hdp4096) ltac:(cbn [la_s]; lia)) as HI'.
cbn [st_reset] in HI'.
unfold ttail_post. cbn [st_reset la_lp la_dp la_mp la_s la_TI la_LM la_LI la_TM].
split.
2:{ split; [lia|]. split; [reflexivity|].
lazymatch type of HS with st_ok _ _ _ ?msx =>
eapply (vtabs_reset memc (ms_mem msx) cx PIX V1 (fun a => ~ (y_img cx <= a < y_img cx + y_nP cx) /\ ~ (y_ld cx <= a < y_ld cx + 2 * lp))
(y_idl cx) HVT LenPIX ltac:(lia)) end.
- intros a Ha HW. rewrite MF.
assert (Hc : (y_img cx <= a < y_img cx + y_nP cx) \/ (y_ld cx <= a < y_ld cx + 2 * lp)).
{ destruct (Z_lt_le_dec a (y_img cx)); destruct (Z_lt_le_dec a (y_img cx + y_nP cx));
destruct (Z_lt_le_dec a (y_ld cx)); destruct (Z_lt_le_dec a (y_ld cx + 2 * lp));
first [left; lia | right; lia | exfalso; apply HW; split; lia]. }
destruct Hc as [Hc|Hc].
+ replace a with (y_bi cx + (a - y_bi cx)) by lia. apply (KB (y_bi cx) (y_Li cx)); [exact HBi | lia |].
unfold rd_written, y_tisz. rsep HSEP 0%nat 7%nat. rsep HSEP 1%nat 7%nat. rsep HSEP 2%nat 7%nat. rsep HSEP 3%nat 7%nat.
rsep HSEP 5%nat 7%nat. rsep HSEP 6%nat 7%nat. lia.
+ replace a with (y_ld cx + (a - y_ld cx)) by lia. apply (KB (y_ld cx) (2 * (y_nP cx + 2 + y_MR cx))); [apply HBt; cbv [tcx_tabs y_cap cap In]; tauto | lia |].
unfold rd_written, y_tisz. rsep HSEP 0%nat 5%nat. rsep HSEP 1%nat 5%nat. rsep HSEP 2%nat 5%nat. rsep HSEP 3%nat 5%nat. rsep HSEP 5%nat 6%nat. lia.
- intros a Ha. split; [lia|]. intros [H1 _]. exact (H1 Ha).
- rewrite LenLD. intros a Ha. split; [lia|]. intros [_ H2]. exact (H2 Ha).
- intros a Ha. rewrite MF. replace a with (y_lc cx + (a - y_lc cx)) by lia. apply Z3. lia.
- rewrite LenLD. intros k Hk. rewrite MF. apply WLD. exact Hk.
- lia. }
lazymatch type of HS with st_ok _ ?E4 ?ss4 ?ms4 =>
assert (QF : forall r, In r TREGS_FIXL -> getr (ms_regs ms4) r = getr regs r)
by (pose proof (regs_kept_of_st_ok _ _ _ _ regs (tcx_extra cx lp dp mp ++ more) TREGS_FIXL HS
ltac:(rewrite HE0; repeat (apply env_agree_havoc_ge; [cbv; lia|]); apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HK; exact HK)
end.
split; [apply (tlzw_regs_fix_kept regs); [exact HFX | exact QF]|].
split.
{ replace (lp0 + 2) with (lp + 1) by (subst lp; lia).
lazymatch type of HS with st_ok _ _ _ ?msx =>
assert (GK : forall a, y_g cx <= a < y_g cx + 60 -> mbyte ubs0segs (ms_mem msx) a = mbyte ubs0segs memc a)
end.
{ intros a Ha. rewrite MF. replace a with (y_g cx + (a - y_g cx)) by lia. apply (KB (y_g cx) 72); [apply HBt; cbv [tcx_tabs In]; tauto | lia |].
unfold rd_written, y_tisz. rsep HSEP 0%nat 6%nat. rsep HSEP 1%nat 6%nat. rsep HSEP 2%nat 6%nat. rsep HSEP 3%nat 6%nat. rsep HSEP 5%nat 6%nat. lia. }
destruct HGA as (U0 & U8 & U16 & U24 & U32 & U40 & U48 & U56 & _ & _ & _).
unfold gen_at. repeat split.
- intros k Hk. rewrite GK; [apply U0; exact Hk | cbn in Hk; lia].
- intros k Hk. rewrite GK; [apply U8; exact Hk | cbn in Hk; lia].
- intros k Hk. rewrite GK; [apply U16; exact Hk | cbn in Hk; lia].
- intros k Hk. rewrite GK; [apply U24; exact Hk | cbn in Hk; lia].
- intros k Hk. rewrite GK; [apply U32; exact Hk | cbn in Hk; lia].
- intros k Hk. rewrite GK; [apply U40; exact Hk | cbn in Hk; lia].
- intros k Hk. rewrite GK; [apply U48; exact Hk | cbn in Hk; lia].
- intros k Hk. rewrite GK; [apply U56; exact Hk | cbn in Hk; lia].
- intros k Hk. rewrite MF. apply W60. exact Hk.
- intros k Hk. rewrite MF. apply W64. exact Hk.
- intros k Hk. rewrite MF. apply W66. exact Hk. }
split.
{ unfold ttables_at. cbn [la_TI la_LM la_LI la_TM].
split; [|split; [|split]].
- apply arr16_zeros. intros a Ha. rewrite Z2Nat.id in Ha by nia. rewrite MF. replace a with (y_ti cx + (a - y_ti cx)) by lia. apply Z1. nia.
- apply arr16_zeros. intros a Ha. change (Z.of_nat 4096) with 4096 in Ha. rewrite MF. replace a with (y_lm cx + (a - y_lm cx)) by lia. apply Z2. lia.
- apply arr16_zeros. intros a Ha. change (Z.of_nat 4096) with 4096 in Ha. rewrite MF. replace a with (y_li cx + (a - y_li cx)) by lia. apply Z4. lia.
- eapply arr16_frame; [exact ATM|]. intros a Ha. rewrite LenTM, Z2Nat.id in Ha by lia. rewrite MF.
replace a with (y_tm cx + (a - y_tm cx)) by lia. apply (KB (y_tm cx) (4098 * y_idl cx)); [apply HBt; cbv [tcx_tabs y_tmsz In]; tauto | lia |].
unfold rd_written, y_tisz. rsep HSEP 0%nat 4%nat. rsep HSEP 1%nat 4%nat. rsep HSEP 2%nat 4%nat. rsep HSEP 3%nat 4%nat.
rsep HSEP 4%nat 5%nat. rsep HSEP 4%nat 6%nat. lia. }
split; [exact HI'|].
split; [treg_val HS (22%bv:reg)|].
lia.
Qed.
End S.
End b.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
