(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI08 YI0t YI0m YI0n YI0s.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0d.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCbw.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI10 YC4a YC8i YC80 YC1f YC1g YC81 YC4b YC44.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC8a YC93 YC9g YC95 YC91 YC99 YC92 YC9h.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC8g.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section e.
Context {PI : PAImg lib_both3_1_listing}.
Context {RO : YC8g.ro_below_ofl (@pa_segs _ lib_both3_1_listing PI) (@pa_relro_lo _ lib_both3_1_listing PI) (@pa_relro_hi _ lib_both3_1_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_1_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_1_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_1_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_1_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Definition A_RST_RET : Z := 0x1e84.
Definition rctx_after : YP09.region :=
YP09.mkRegion (Some 8%nat) 0 72 0 0
(rctx_chunks false ++ [YP09.mkChunk 60 (CVal 4 (SOff 41 1)); YP09.mkChunk 64 (CVal 2 (SOff 25 2)); YP09.mkChunk 66 (CVal 2 (SLit 1))]).
Lemma region_kept_direct' : forall E H (m m2 : word -> option byte) n b lo hi wlo whi cs,
bv_unsigned (ew E n) = b ->
(forall a, b + lo <= a < b + hi -> mbyte SEGS (mrestrict H m2) a = mbyte SEGS (mrestrict H m) a) ->
(forall a, b + wlo <= a < b + whi -> writable_at SEGS (mrestrict H m2) a) ->
region_kept SEGS E (mrestrict H m) (mrestrict H m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E H m m2 n b lo hi wlo whi cs Hn Hb Hw.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha; [apply Hb; exact Ha | intros _; apply Hw; exact Ha].
Qed.
Section S.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis AMEMSET : aintrin_realizes SEGS B OSet (SIGMA AS_asan_memset).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_both3_1) (PI := PI).
Hypothesis HUL : forall t, In t (lzw_traces (as_code B) BASE) -> In t (as_universe B).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_both3_1 PI.
Definition tmiss_tail_post cx lyc Sc W memc mdc ly7 S7 W7 memT X s1 : world SEGS -> config -> Prop :=
fun W' c' => W' = W7 /\ exists regs' mem' md' X',
c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + atail_pc cx X')) mem' (seg_rom SEGS)) md' /\
ajournal SEGS B LZW_TSTK (z_sp cx) [] lyc Sc W memc mdc [] ly7 S7 W7 mem' md' 7 /\
aabove_eq cx (mrestrict (w_H W7) memT) (mrestrict (w_H W7) mem') /\
atail_post cx X regs' (mrestrict (w_H W7) mem') X' /\ la_s X' = s1.
Local Ltac sep HSEP i j := septac HSEP i j; lia.
Lemma trst_seg : forall cx lyc Sc W memc mdc ly7 S7 W7 (regs : bvmap 5 word) memT mdT (regs0 : bvmap 5 word) X s',
acx_ok cx -> acx_ranges cx -> acx_seps cx -> acx_blk (ablocks B ly7 S7) cx -> acx_tok cx (ablocks B lyc Sc) ->
ajournal SEGS B LZW_TSTK (z_sp cx) [] lyc Sc W memc mdc [] ly7 S7 W7 memT mdT 7 ->
alzw_slots (mrestrict (w_H W7) memT) cx -> alzw_sslots (mrestrict (w_H W7) memT) cx -> tlzw_frame (mrestrict (w_H W7) memT) (z_sp cx) regs0 ->
arst_pre cx X s' regs (mrestrict (w_H W7) memT) -> z_gp cx = as_gp B -> z_tp cx = as_tp B ->
SRr SEGS W7 (mkCfg (mkst regs (Z_to_bv 64 (BASE + PC_RST)) memT (seg_rom SEGS)) mdT)
(tmiss_tail_post cx lyc Sc W memc mdc ly7 S7 W7 memT X s').
Proof.
intros cx lyc Sc W memc mdc ly7 S7 W7 regs memT mdT regs0 X s' HCX HRG HSEP HBL HTOK HJ HSL HSS HFR (HFX & HG & HT & HI & Hdp & H26 & Hs') Hzgp Hztp.
pose proof HBL as (HBg & HBi & HBt).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HJ as (HAR & _). pose proof (alzw_regs_core_of_fix _ _ HFX) as HFC.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HTS : LZW_TSTK = 304 + ASTACK) by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
destruct X as [TI LM LI TM s lp dp mp Cn R]. cbn [la_TI la_LM la_LI la_TM la_s la_lp la_dp la_mp] in *.
pose proof HCX as (Hidl & HnP & HMR & HMR0 & Hicl & Hal16 & Hsplo & Hsphi & HpR0 & HpR47 & HpR8 & Hgp & Htp & EMR).
pose proof HRG as (HR & Hbi0 & Hbi1 & Hbi2 & Hbi3). cbn [ranges acx_tabs lzw_tabs app] in HR.
destruct HR as ((Rld1 & Rld2 & Rld3 & Rld4) & (Rti1 & Rti2 & Rti3 & Rti4) & (Rlm1 & Rlm2 & Rlm3 & _) & (Rlc1 & Rlc2 & Rlc3 & _) & (Rli1 & Rli2 & Rli3 & _) &
(Rtm1 & Rtm2 & Rtm3 & Rtm4) & (Rg1 & Rg2 & Rg3 & _) & _).
assert (Actx : forall blc lyq i, In (z_ctx cx, 72) blc -> 0 <= i < 72 -> awr_byte LZW_TSTK (z_sp cx) [] (ablocks B lyc Sc) blc lyq [] (z_ctx cx + i)).
{ intros blc lyq i Hb Hi. apply (HTOK (z_ctx cx, 72) ltac:(left; reflexivity)); [exact Hb | cbn [snd]; change (req_size 72) with 72; lia]. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ (z_ctx cx) 72 HAR HBg) as (_ & _ & _ & _ & Hcpres & _). change (req_size 72) with 72 in Hcpres.
pose proof HI as (LenTI & LenLM & LenLI & LenTM & BTI & BLI & BLM & UTM & ATMrows & Hdp' & Hmp & HA & HR0 & HRC & HCn & Hlp & Hs0).
pose proof (countA_nonneg LI LM) as HA0.
pose proof (maxres_bounds (z_idl cx) (z_nP cx) Hidl ltac:(lia)) as [HMR1 HMR2].
assert (EMR' : lzw_MR (z_nP cx) (z_idl cx) = z_MR cx) by (symmetry; exact EMR). unfold lzw_MR in EMR'. unfold lzw_MR in Rld1, Rld2, Rld4. rewrite EMR' in *.
assert (HMRle : z_MR cx <= 26055).
{ assert (z_MR cx * 3838 <= z_MR cx * (4094 - z_idl cx)) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
pose proof (lp_head_bound (z_idl cx) (z_nP cx) (z_MR cx) (mkLA TI LM LI TM s lp dp mp Cn R) ltac:(unfold lzw_par; lia) HI ltac:(cbn [la_s]; lia)) as Hlpb.
cbn [la_lp] in Hlpb. unfold cap in Hlpb.
destruct HT as (ATI & ALM & ALI & ATM).
assert (Htisz : 8 <= z_tisz cx <= 131072) by (unfold z_tisz; clear - Hidl; split; [nia|nia]).
unfold z_tisz, z_tmsz in *.
rewrite ?C1, ?C2, ?C3, ?C4, ?HTS, ?Has in *. clear C2 C3 C4 HTS Has.
remember (Eimg (Ereg regs (acx_extra cx (lp + 1) dp mp regs0 ++ []))) as E eqn:HE0. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
pose proof (AE_sp regs cx (lp + 1) dp mp regs0 [] HFC) as HE2. pose proof (AE_ctx regs cx (lp + 1) dp mp regs0 [] HFC) as HE8.
pose proof (AE_SB regs cx (lp + 1) dp mp regs0 [] HFC) as HE21. pose proof (AE_idl regs cx (lp + 1) dp mp regs0 [] HFC) as HE25.
pose proof (AE_gp regs cx (lp + 1) dp mp regs0 [] HFC) as HE3. pose proof (AE_tp regs cx (lp + 1) dp mp regs0 [] HFC) as HE4.
pose proof (AE_ti regs cx (lp + 1) dp mp regs0 []) as HE32. pose proof (AE_lm regs cx (lp + 1) dp mp regs0 []) as HE33.
pose proof (AE_lc regs cx (lp + 1) dp mp regs0 []) as HE34. pose proof (AE_li regs cx (lp + 1) dp mp regs0 []) as HE35.
pose proof (AE_tm regs cx (lp + 1) dp mp regs0 []) as HE36. pose proof (AE_ld regs cx (lp + 1) dp mp regs0 []) as HE37.
pose proof (AE_img regs cx (lp + 1) dp mp regs0 []) as HE38. pose proof (AE_nP regs cx (lp + 1) dp mp regs0 []) as HE39.
pose proof (AE_lp regs cx (lp + 1) dp mp regs0 []) as HE41.
rewrite <- HE0 in HE2, HE8, HE21, HE25, HE3, HE4, HE32, HE33, HE34, HE35, HE36, HE37, HE38, HE39, HE41.
assert (HE26 : ew E 24 = Z_to_bv 64 s') by (rewrite HE0, (AE_reg regs _ _ _ _ _ [] 24%bv 24) by reflexivity; exact H26).
assert (HS1 : st_ok_pi SEGS VAL E (alzw_ss PC_RST asr_fix false false [] [] [] []) (mkst regs (Z_to_bv 64 (BASE + PC_RST)) (mrestrict (w_H W7) memT) (seg_rom SEGS))).
{ rewrite HE0. apply (alzw_st_ok cx regs regs0 (lp + 1) dp mp [] (mrestrict (w_H W7) memT) PC_RST asr_fix false false); rewrite <- ?HE0.
- exact HCX. - exact HRG. - exact HFC. - exact HG. - exact HSL. - exact HSS. - exact HFR.
- intros X0; discriminate X0. - intros X0; discriminate X0.
- lia. - lia. - lia.
- rewrite HE0. apply (regs_ok_fix regs cx); [exact HFX | lia | lia].
- vm_compute; reflexivity.
- apply Forall_nil.
- exact I. - exact I. - exact I. - exact I. - exact I. - exact I. }
idtac "SEED OK".
cbn [alzw_ss] in HS1. rewrite <- restrict_mkst_fx in HS1. rename HS1 into HS.
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by (intros; reflexivity).
shok_auto SHOK (SOff 23 0) E (mrestrict (w_H W7) (ms_mem (mkst regs (Z_to_bv 64 (BASE + PC_RST)) memT (seg_rom SEGS)))).
change memT with (ms_mem (mkst regs (Z_to_bv 64 (BASE + PC_RST)) memT (seg_rom SEGS))) in HJ.
Local Ltac oblkA AG HJ HB HEn HE21 v :=
let L := getLAWS in
lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff ?n ?c)) ?len =>
first [ rewrite (U_atom_off Ex n v c); [| cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; rewrite ?AG by lia; exact HEn | lia | lia]
| rewrite (U_atom Ex n v); [| cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; rewrite ?AG by lia; exact HEn | lia] ];
eapply (obl_of_block SEGS _ L _ _ _ _ _ Ex (SOff 23 0) _ len _ _ (proj1 HJ) HB);
[ rewrite (U_atom Ex 23 SB); [reflexivity | cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; rewrite ?AG by lia; exact HE21 | unfold SB; lia]
| lia
| try change (req_size 72) with 72; first [ lia | match goal with |- _ <= _ + req_size ?nn => pose proof (req_size_pos nn ltac:(lia)); lia end ] ]
end.
Local Ltac awr_ro := cbn [ss_mem]; repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
Local Ltac mem_unch HF :=
lazymatch type of HF with frame_of _ _ ?m0 (ms_mem ?msx) =>
let EQM := fresh "EQM" in
assert (EQM : ms_mem msx = m0)
by (apply functional_extensionality; intros x; apply HF; intros (rg & Hin & Hrg); cbn in Hin;
repeat (destruct Hin as [<-|Hin]; [cbn in Hrg; lia|]); destruct Hin);
cbn [ms_mem ms_regs mkst] in EQM; rewrite <- EQM in *; clear EQM HF;
try match goal with H : frame_of _ _ _ _ |- _ => clear H end; try match goal with H : mem_grows _ _ |- _ => clear H end
end.
paj_run_to_tok RUNTO HS HJ SHOK Bspan A_rd; try (oblkA AG HJ HBg HE8 HE21 (z_ctx cx)); [ awr_ro | ].
mem_unch HF.
idtac "RUN1 OK".
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (1%bv : bv 5) Rra.
pose proof HG as (V0 & V8 & V16 & V24 & V32 & V40 & V48 & V56 & V60 & V64 & V66).
lazymatch type of HS with st_ok_pi _ _ ?E1 ?ss1 ?ms1 =>
assert (HFXA : alzw_regs_fix (ms_regs ms1) cx)
by (eapply (alzw_regs_fix_after E E1 ss1 ms1 _ _ _ HS);
[vm_compute; reflexivity | intros nn Hnn; rewrite ?ew_ewset_other by lia; apply AG; lia | exact HE0 | exact HFC | lia | lia]) | st_ok _ ?E1 ?ss1 ?ms1 =>
assert (HFXA : alzw_regs_fix (ms_regs ms1) cx)
by (eapply (alzw_regs_fix_after E E1 ss1 ms1 _ _ _ HS);
[vm_compute; reflexivity | intros nn Hnn; rewrite ?ew_ewset_other by lia; apply AG; lia | exact HE0 | exact HFC | lia | lia])  end.
rewrite (st_ok_restrict_mkst SEGS _ _ _ _ HS eq_refl). cbn [ss_pc ms_regs ms_mem].
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rX _ ?mX _) _) _ =>
eapply (tard_run B TL LAWS AMEMSET cx lyc Sc W memc mdc ly7 S7 W7 rX mX _ (lp + 1) TM (Z_to_bv 64 (BASE + A_RST_RET))
HCX HRG HSEP HBL HTOK HJ Hzgp Hztp HFXA (agen_ptrs_of_at _ _ _ _ _ HG) V60 ATM LenTM) end.
- rewrite Ra0. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?AG by lia. rewrite HE8. reflexivity.
- rewrite Ra1. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?AG by lia. rewrite HE25. reflexivity.
- exact Rra.
- apply ret_ok_codeptr_v; [lazymatch goal with |- _ <= ?k < _ => try unfold k end; lia | reflexivity].
- lia. - unfold z_cap, cap; lia. - lia. }
cbv beta. clear Ra0 Ra1 Rra HFXA.
intros W8 c8 _ (-> & regs7 & mem7 & md7 & -> & HJ7 & HFX7 & HPR7 & H26' & HG7 & ATM7 & ZTI & ZLM & ZLC & ZLI & HK7).
idtac "CALL OK".
assert (HTS : LZW_TSTK = 304 + 16384) by reflexivity. rewrite HTS in HJ7. clear HTS.
lazymatch type of HK7 with forall a, _ -> _ -> _ = mbyte _ ?mq a =>
assert (HAE : aabove_eq cx mq (mrestrict (w_H W7) mem7))
by (intros a Ha; apply HK7; [lia|]; unfold rd_written, z_tisz; clear - Ha Rg2 Rld2 Rti2 Rlm2 Rlc2 Rli2 Hsplo HnP HMR0 Hlpb; lia) end.
reseat HS HJ7 HPR7 [1]%nat AG
ltac:(eapply region_kept_direct';
[ cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; try rewrite (AG 2%nat) by lia; rewrite HE2; apply unsigned_lit_small; lia
| intros a Ha; cbn in Ha; apply HK7; [lia|]; unfold rd_written, z_tisz; clear - Ha Rg2 Rld2 Rti2 Rlm2 Rlc2 Rli2 Hsplo HnP HMR0 Hlpb; lia
| intros a Ha; cbn in Ha; lia ]).
idtac "RESEAT OK".
lazymatch type of AG with forall n, _ -> ew ?Ev n = _ =>
assert (HEv8 : ew Ev 8 = Z_to_bv 64 (z_ctx cx)) by (rewrite (AG 8%nat) by lia; exact HE8);
assert (HEv2 : ew Ev 2 = Z_to_bv 64 (z_sp cx - 304)) by (rewrite (AG 2%nat) by lia; exact HE2);
assert (HEv21 : ew Ev 23 = Z_to_bv 64 SB) by (rewrite (AG 23%nat) by lia; exact HE21);
assert (HEv25 : ew Ev 25 = Z_to_bv 64 (z_idl cx)) by (rewrite (AG 25%nat) by lia; exact HE25);
assert (HEv26 : ew Ev 24 = Z_to_bv 64 s') by (rewrite (AG 24%nat) by lia; exact HE26);
assert (HEv32 : ew Ev 32 = Z_to_bv 64 (z_ti cx)) by (rewrite (AG 32%nat) by lia; exact HE32)
end.
pose proof HG7 as (W0 & W8 & W16 & W24 & W32 & W40 & W48 & W56 & W60 & W64 & W66).
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
pose proof (st_ok_pi_add_region Ex _ _ rctx_after HS eq_refl
ltac:(unfold region_ok, rctx_after; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app rctx_chunks];
rewrite HEv8, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
let ack S HE := (eapply chunk_ok_val; [ cbn [sv_denot]; rewrite HE, unsigned_lit_small by lia; rewrite ?Z.add_0_r; reflexivity | cbn; lia | cbn; apply Z.le_refl || lia
| first [exact S | rewrite Z.add_0_r; exact S | match type of S with val_mem _ _ _ _ ?v => match goal with |- val_mem _ _ _ _ ?v' => replace v' with v by lia; exact S end end] ]) in
let lck S := (eapply chunk_ok_val; [ reflexivity | cbn; lia | cbn; lia | exact S ]) in
constructor; [ack W0 HEv32|]; constructor; [ack W8 HE33|]; constructor; [ack W16 HE34|]; constructor; [ack W24 HE35|];
constructor; [ack W32 HE36|]; constructor; [ack W40 HE37|]; constructor; [ack W48 HE38|]; constructor; [ack W56 HE39|];
constructor; [ack W60 HE41|]; constructor; [ack W64 HEv25|]; constructor; [lck W66|]; constructor)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, rctx_after; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite HEv8, HEv2, !unsigned_lit_small by lia; split; [lia | exact I])) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ex _ _ =>
pose proof (st_ok_pi_add_region Ex _ _ rctx_after HS eq_refl
ltac:(unfold region_ok, rctx_after; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app rctx_chunks];
rewrite HEv8, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
let ack S HE := (eapply chunk_ok_val; [ cbn [sv_denot]; rewrite HE, unsigned_lit_small by lia; rewrite ?Z.add_0_r; reflexivity | cbn; lia | cbn; apply Z.le_refl || lia
| first [exact S | rewrite Z.add_0_r; exact S | match type of S with val_mem _ _ _ _ ?v => match goal with |- val_mem _ _ _ _ ?v' => replace v' with v by lia; exact S end end] ]) in
let lck S := (eapply chunk_ok_val; [ reflexivity | cbn; lia | cbn; lia | exact S ]) in
constructor; [ack W0 HEv32|]; constructor; [ack W8 HE33|]; constructor; [ack W16 HE34|]; constructor; [ack W24 HE35|];
constructor; [ack W32 HE36|]; constructor; [ack W40 HE37|]; constructor; [ack W48 HE38|]; constructor; [ack W56 HE39|];
constructor; [ack W60 HE41|]; constructor; [ack W64 HEv25|]; constructor; [lck W66|]; constructor)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, rctx_after; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite HEv8, HEv2, !unsigned_lit_small by lia; split; [lia | exact I])) as HS3;
clear HS; rename HS3 into HS  end.
norm_ss HS. reshok_bx HS 23%nat.
idtac "CTX OK".
pose proof (inv_reset (z_idl cx) (z_nP cx) Hidl _ (s' - 1) HI ltac:(cbn [la_dp]; exact Hdp) ltac:(cbn [la_s]; lia)) as HI'.
cbn [st_reset] in HI'. replace (s' - 1 + 1) with s' in HI' by lia.
paj_run_tok RUN HS HJ7 SHOK Bspan; try (oblkA AG HJ7 HBg HE8 HE21 (z_ctx cx)); [ awr_ro | ].
mem_unch HF.
idtac "RUN2 OK".
Local Ltac finish HS HJ HAE HI' HE0 HFC AG ATM7 ZTI ZLM ZLI HG7 TM s' lp Cn R cx :=
pmkst HS; ppcs;
apply SRr_ret; split; [reflexivity|];
lazymatch goal with |- exists regs' mem' md' X', mkCfg (mkst ?rg _ ?mm _) ?mdx = _ /\ _ =>
exists rg, mm, mdx, (mkLA (repeat 0 (Z.to_nat (z_idl cx * z_idl cx))) (repeat 0 4096) (repeat 0 4096) TM s' (lp + 2) (z_idl cx + 2) 1 (Cn + 1) (R + 1)) end;
split; [| split; [exact HJ|]; split; [exact HAE|]; split; [|reflexivity] ];
[ unfold atail_pc; cbn [la_s];
first [ replace (s' <? z_nP cx) with true by (symmetry; apply Z.ltb_lt; lia) | replace (s' <? z_nP cx) with false by (symmetry; apply Z.ltb_ge; lia) ];
reflexivity
| unfold atail_post; cbn [la_lp la_dp la_mp la_s la_TI la_LM la_LI la_TM];
split; [ split; [ lazymatch type of HS with st_ok_pi _ _ ?E1 ?ss1 ?ms1 =>
eapply (alzw_regs_fix_after _ E1 ss1 ms1 _ _ _ HS);
[vm_compute; reflexivity | intros nn Hnn; rewrite ?ew_ewset_other by lia; apply AG; lia | exact HE0 | exact HFC | lia | lia] | st_ok _ ?E1 ?ss1 ?ms1 =>
eapply (alzw_regs_fix_after _ E1 ss1 ms1 _ _ _ HS);
[vm_compute; reflexivity | intros nn Hnn; rewrite ?ew_ewset_other by lia; apply AG; lia | exact HE0 | exact HFC | lia | lia]  end
| aregv HS (15%bv : bv 5) ] |];
split; [ replace (lp + 2) with (lp + 1 + 1) by lia; exact HG7 |];
split; [ split; [|split; [|split]];
[ apply arr16_zeros_aview; intros a Ha; rewrite Z2Nat.id in Ha by lia; apply ZTI; [lia | unfold in_rng, z_tisz; lia]
| apply arr16_zeros_aview; intros a Ha; cbn in Ha; apply ZLM; [lia | unfold in_rng; lia]
| apply arr16_zeros_aview; intros a Ha; cbn in Ha; apply ZLI; [lia | unfold in_rng; lia]
| exact ATM7 ] |];
split; [exact HI'|]; split; [aregv HS (24%bv : bv 5) | lia] ].
psrr_branch_tok RUN BR HS SHOK Bspan.
{
aUcond Hc.
paj_run_to_tok RUNTO HS HJ7 SHOK Bspan PC_HEAD; try (oblkA AG HJ7 HBg HE8 HE21 (z_ctx cx)); [ awr_ro | ].
mem_unch HF.
finish HS HJ7 HAE HI' HE0 HFC AG ATM7 ZTI ZLM ZLI HG7 TM s' lp Cn R cx. }
aUcond Hc.
paj_run_to_tok RUNTO HS HJ7 SHOK Bspan PC_EPI; try (oblkA AG HJ7 HBg HE8 HE21 (z_ctx cx)); [ awr_ro | ].
mem_unch HF.
finish HS HJ7 HAE HI' HE0 HFC AG ATM7 ZTI ZLM ZLI HG7 TM s' lp Cn R cx.
Qed.
End S.
End e.
End d.
