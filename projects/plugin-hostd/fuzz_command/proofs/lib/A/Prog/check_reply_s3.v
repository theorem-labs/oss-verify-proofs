(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the third segment of check_reply's walk (fuzz_command.asan, 0x86d78), from the
   return of sup_reply_code (0x86f18) to the snprintf call (0x86f98), the strlen call (0x86f68) or the shape join
   (0x86fcc), ported from proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v..ACh8.v, AChc.v and ACke.v (cgif_close) at
   c8557374ad2e.

   The walk seeds the mid-walk state at 0x86f18 (check_reply_sd.v cr_seed, the frame's shadow read-only) and adds
   the harness's words: the fields w->w and w->n at w + 16 and w + 24 (base atom 19 = s3 = w, chunk values atoms 40
   and 41), with the shadow entry (19, 16, 28). `bltz a0` splits on the code:
   - code < 0: one run to the snprintf call (s5 = code, s3 = a0 = F + 32, a1 = 32, a2 = "resp %d", a3 = code);
   - code >= 0: check #6 (0x86f28, load4 at w + 24: a token whose slow block needs [w + 24, w + 28), inside the
     entry), `lw a0` = n, and `beqz a0` splits on n: n = 0 runs to the join with a0 = "resp 0" (0x210e0); n <> 0
     adds the first slot of w->w (base atom 40, chunk value atom 42) with the shadow entry (40, 0, 8) and runs
     checks #7 (0x86f44) and #8 (0x86f58), both covered, to the strlen call with s3 = a0 = w->w[0].
   No step stores, so the mid-walk invariant carries over by the run's frame_of (only the frame header [F, F + 32)
   is a writable window). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString RtFormat RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import check_reply_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaRun PaShadow PaStep CmdSyms
  CmdList CmdPa PaJournal CmdPaLib PaLibG PaLibH PaLibF PaDenot PaSB PaCall CmdBase CmdRep CmdObj CmdRo CmdZsh
  CmdRecBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import sup_reply_code_c check_reply_answer_c
  rec_code_declared_c rec_shape_of_c syntax_reply_matches_c check_reply_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import check_reply_k check_reply_m check_reply_sd
  check_reply_t.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* the harness's words w->w (w + 16) and w->n (w + 24), on s3 = w *)
Definition s3_wregion : YP09.region :=
YP09.mkRegion (Some 19%nat) 16 28 0 0 [YP09.mkChunk 16 (CVal 8 (SOff 40 0)); YP09.mkChunk 24 (CVal 4 (SOff 41 0))].
(* the first slot of w->w *)
Definition s3_wwregion : YP09.region := YP09.mkRegion (Some 40%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 42 0))].

(* discharge a lemma's Section hypotheses from the context *)
Ltac s3_hyps H := repeat lazymatch type of H with
  forall _ : ?A, _ => lazymatch type of A with Prop => specialize (H ltac:(assumption)) end end.
(* the walk's only writable region is the frame header [F, F + 32) of the owned frame (1, pos) *)
Ltac s3_awr E36u pos :=
lazymatch goal with |- awr_ok ?sg ?bb ?Ev ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyv ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok sg bb Ev rs' stk spx fp b0 bc fr lyv own) end;
repeat first
[ apply awr_ok_nil
| apply awr_ok_cons_ro; [cbn; lia|]
| eapply awr_ok_cons_gen; [reflexivity | exact E36u
  | intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; left; exists 1%Z, pos;
    split; [left; reflexivity | left; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 1) with 128; lia] | ] ].
(* cr_regs_at at a stop of a run from the seed: the kept registers still denote the seed's atoms *)
Ltac s3_regs_tac HS G2 G3 G4 G8 G27 R2 R3 R4 R8 R27 E32 E33 E36 E38 :=
unfold cr_regs_at; cbv zeta;
repeat match goal with |- _ /\ _ => split end;
rewrite (st_ok_pi_restrict_reg (w_H _) _ _ _ _ HS); cbn [ms_regs];
lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ => let e := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with e end;
first
[ exact (denot_s10 _ E33 E32)
| cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
  first
  [ rewrite G2; exact R2 | rewrite G3; exact R3 | rewrite G4; exact R4 | rewrite G8; exact R8 | rewrite G27; exact R27
  | rewrite E36; reflexivity | rewrite E38; reflexivity | rewrite E32; reflexivity
  | rewrite E33, unsigned_lit_small by lia; reflexivity | rewrite E33; reflexivity ] ].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Lemma s3_val_mem_of_aval : forall H mem a n v, aval_mem (aview SEGS H mem) a n v -> val_mem SEGS (mrestrict H mem) a n v.
Proof.
intros H mem a n v Hv k Hk. specialize (Hv k Hk). unfold aview in Hv.
destruct (mbyte SEGS (mrestrict H mem) (a + Z.of_nat k)) as [b|]; cbn in Hv; [|discriminate].
injection Hv as Hv. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned.
unfold YO0f.le_byte. unfold YG0f.le_byte in Hv. rewrite <- Hv. symmetry. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.
Lemma s3_val_mem_mod64 : forall m a v, val_mem SEGS m a 8 v -> val_mem SEGS m a 8 (v mod 2 ^ 64).
Proof.
intros m a v H k Hk. rewrite (H k Hk). unfold YO0f.le_byte. change (8 * Z.of_nat 8) with 64. rewrite Z.mod_mod by lia.
reflexivity.
Qed.
(* bltz on an atom that holds a signed 64-bit value *)
Lemma s3_branch_lt0 : forall E n c, ew E n = Z_to_bv 64 c -> -2 ^ 63 <= c < 2 ^ 63 ->
branch_taken BC_LT (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = (c <? 0).
Proof.
intros E n c H Hc. cbn [sv_denot]. rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned.
cbn [branch_taken]. try unfold bv_lts. rewrite !Z_to_bv_signed.
rewrite !bv_swrap_small by (change (bv_half_modulus 64) with (2 ^ 63); lia). reflexivity.
Qed.
(* sup_reply_code's value is a C int *)
Lemma s3_code_range : forall v, -2 ^ 31 <= c_code v < 2 ^ 31.
Proof.
intros v. unfold c_code, reply_code_a, atoi_a. destruct (list_eq_dec _ _ _); [|lia].
unfold bv_swrap. match goal with |- context [bv_wrap 32 ?y] => pose proof (bv_wrap_in_range 32 y) end.
change (bv_half_modulus 32) with (2 ^ 31) in *. change (bv_modulus 32) with (2 ^ 32) in *. lia.
Qed.

Section e.
Variable B : asyms.
Variables RLO RHI : Z.
Context {RO : ro_below_ofl SEGS RLO RHI}.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HB : CmdBSyms B.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a.
Hypothesis IMG : cmd_img_facts SEGS B.
Hypothesis CMD_RO_AT : forall ly S W mem md, AR SEGS B ly S W mem md ->
  arodata_okP SEGS RLO RHI B (aview SEGS (w_H W) mem) -> cmd_ro_ok (aview SEGS (w_H W) mem).
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS. Let BR := paj_branch.

(* the mid-walk invariant at a later memory that agrees with this one outside the frame header [F, F + 32) *)
Lemma s3_mid_kept : forall v lyc Sc Wc memc mdc mem' md' pos,
cr_cx B RLO RHI v -> cr_mid B v lyc Sc Wc memc mdc pos ->
ajournal SEGS B CHECK_REPLY_STK (c_sp v) [] (c_ly v) (c_S v) (c_W v) (c_mem v) (c_md v) [(1, pos)] lyc Sc Wc mem' md' 0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (frame_addr lyc 1 pos <= a < frame_addr lyc 1 pos + 32) -> rdW Wc mem' a = rdW Wc memc a) ->
cr_mid B v lyc Sc Wc mem' md' pos.
Proof.
intros v lyc Sc Wc memc mdc mem' md' pos CX MID HJ' UN.
pose proof CX as (HPRE & _).
pose proof HPRE as (HAR0 & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof MID as (HJ & HPerm & VFL & VSH & VSV & VREP & VSZ).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hfin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 pos HAR Hfin) as (HF4096 & HFceil & HFapp).
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR Hfin) as HFimg.
pose proof alloc_ceiling_value as Cc.
assert (HSTK : CHECK_REPLY_STK = 12464) by reflexivity.
change (fs_frame_bytes 1) with 128 in *.
pose proof (Z.div_mod (frame_addr lyc 1 pos) 8 ltac:(lia)) as HFd8. pose proof (Z.mod_pos_bound (frame_addr lyc 1 pos) 8 ltac:(lia)) as HFm8.
unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in HFapp. unfold off_img in HFimg.
assert (K : forall a n val, val_mem SEGS (mrestrict (w_H Wc) memc) a n val -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  a + Z.of_nat n <= frame_addr lyc 1 pos \/ frame_addr lyc 1 pos + 32 <= a -> val_mem SEGS (mrestrict (w_H Wc) mem') a n val).
{ intros a n val Hv Ha Hb Hd. apply (val_mem_kept SEGS (w_H Wc) (w_H Wc) memc mem' a n val); [|exact Hv].
  intros k Hk. apply UN; lia. }
split; [exact HJ'|]. split; [exact HPerm|].
split; [apply K; [exact VFL | lia | try change (Z.of_nat 8) with 8; lia | right; lia]|].
split; [intros i Hi; apply K; [exact (VSH i Hi) | unfold SHADOW_OFF; lia | try change (Z.of_nat 1) with 1; unfold SHADOW_OFF; lia
  | try change (Z.of_nat 1) with 1; unfold SHADOW_OFF; lia]|].
split.
{ intros j r Hj. assert (Hj12 : (j < 12)%nat).
  { apply (proj1 (nth_error_Some cr_saved_regs j)). rewrite Hj. discriminate. }
  apply K; [exact (VSV j r Hj) | unfold c_sp in *; lia | try change (Z.of_nat 8) with 8; unfold c_sp in *; lia
  | try change (Z.of_nat 8) with 8; unfold c_sp in *; lia]. }
split; [apply K; [exact VREP | | | ]; try change (Z.of_nat 8) with 8; unfold A_G_REC, OFF_REPLY; lia|].
apply K; [exact VSZ | | | ]; try change (Z.of_nat 8) with 8; unfold A_G_REC, OFF_REPLY_SIZE; lia.
Qed.

Theorem cr_s3 : CR_SNP_stmt B RLO RHI -> CR_STRLEN_stmt B RLO RHI -> CR_JOIN_stmt B RLO RHI -> CR_CODE_stmt B RLO RHI.
Proof.
intros SNP STRL JOIN v lyc Sc Wc regs1 memc mdc pos CX MID RA R19 R10 LS HFRM.
pose proof CX as (HPRE & Hfr7 & HROD & HGOT & HROK & HROI & HVO & HGRD & H10 & HREC & Hn1 & Hry & Hno0 & Hrep & Htr
  & Hans & Hta & Hw8 & Hspw & HWRA & Hww & Hnv & Hn & HN0 & HAOK & HRY & HFL & HERR & HEV & HWHI).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof MID as (HJ & HPerm & VFL & VSH & VSV & VREP & VSZ).
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _).
pose proof RA as (R2 & R3 & R4 & R8 & R9 & R18 & R23 & R22 & R24 & R25 & R20 & R26 & R27).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_value as Cc.
assert (HSTK : CHECK_REPLY_STK = 12464) by reflexivity.
assert (Hfin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 pos HAR Hfin) as (HF4096 & HFceil & HFapp).
change (fs_frame_bytes 1) with 128 in *.
set (sp0 := c_sp v) in *. set (F := frame_addr lyc 1 pos) in *.
pose proof (Z.div_mod F 8 ltac:(lia)) as HFd8. pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as HFm8.
unfold c_sp in sp0. fold sp0 in Hstk, Hal16, Hslo, Hshi, Hbot, Htop, Hspw, Hpres0.
(* the reply block: the numbers the seed needs *)
pose proof (cr_reply_block B RLO RHI) as RB. s3_hyps RB. destruct (RB v CX) as (m & Hrin & Hrm & _). clear RB.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hrin) as (Hr16 & Hr4096 & Hrceil & _).
pose proof (req_size_pos0 m ltac:(unfold c_nr in Hrm; lia)) as [Hrq0 Hrq].
assert (Hnr : c_nr v + 1 <= 8194).
{ destruct HREC as (Q & (_ & _ & _ & _ & _ & Hrepl & _) & _). unfold areply_at in Hrepl. rewrite Hry in Hrepl.
  destruct (l_reply Q) as [[rp rn]|]; [|destruct Hrepl].
  destruct Hrepl as (_ & _ & _ & _ & _ & _ & _ & Hrlen). rewrite length_app in Hrlen. cbn [length] in Hrlen.
  unfold c_nr, LMAX in *. lia. }
pose proof (cr_seed B RLO RHI LAWS v lyc Sc Wc regs1 memc mdc pos CR_RET_SRC false CX MID RA
  ltac:(lia) Hr16 ltac:(unfold c_nr in *; lia) Hnr) as HS.
set (E := crM regs1 v lyc pos) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold crM; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r) by (intros; subst E; apply crM_reg; assumption).
assert (EX : forall j, (j < 23)%nat -> ew E (32 + j) = nth j (crM_extra v lyc pos) (Z_to_bv 64 0)) by (intros; subst E; apply crM_extra_nth; lia).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 4%nat ltac:(lia)) as E36. pose proof (EX 6%nat ltac:(lia)) as E38. pose proof (EX 7%nat ltac:(lia)) as E39.
pose proof (EX 8%nat ltac:(lia)) as E40. pose proof (EX 9%nat ltac:(lia)) as E41. pose proof (EX 10%nat ltac:(lia)) as E42.
cbn [Nat.add nth crM_extra map app] in E32, E33, E36, E38, E39, E40, E41, E42. fold F in E36, E38.
assert (E19 : ew E 19 = Z_to_bv 64 (c_w v)) by (rewrite (EE 19%nat 19%bv eq_refl); exact R19).
assert (E10 : ew E 10 = Z_to_bv 64 (c_code v)) by (rewrite (EE 10%nat 10%bv eq_refl); exact R10).
assert (VB : forall k z, ew E k = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> base_val E (Some k) = z).
{ intros k z Hk Hz. cbn [base_val]. rewrite Hk. apply unsigned_lit_small. exact Hz. }
assert (Hw46 : 2 ^ 46 <= c_w v /\ c_w v + 32 <= 2 ^ 47) by (unfold c_sp in *; lia).
(* the words' facts at this state *)
pose proof (cr_words_facts B RLO RHI) as WF. s3_hyps WF.
destruct (WF v lyc Sc Wc memc mdc pos CX MID) as (_ & WRA & WWW & WWN & WWB). clear WF.
unfold WORDS_W, WORDS_N in WRA, WWW, WWN.
(* s3 = w: an atom fact (for the shadow entry) and the words region *)
assert (HF19 : afact_ok E 19 (mkAF (2 ^ 46) (2 ^ 47 - 32) 3)).
{ unfold afact_ok; cbn [af_lo af_hi af_al2]. rewrite E19, unsigned_lit_small by lia. change (2 ^ 3) with 8. lia. }
pose proof (st_ok_pi_add_fact E _ _ 19 _ HS HF19) as HS1. clear HS.
assert (HRW : region_ok SEGS E (mrestrict (w_H Wc) memc) s3_wregion).
{ unfold region_ok, s3_wregion; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite (VB 19%nat (c_w v) E19) by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor; [|constructor]].
  - apply (chunk_ok_val SEGS E _ (c_w v) 16 8 (SOff 40 0) (c_ww v mod 2 ^ 64));
    [cbn [sv_denot]; rewrite E40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | apply Z.mod_pos_bound; lia | zside |].
    apply s3_val_mem_mod64. apply s3_val_mem_of_aval. exact WWW.
  - apply (chunk_ok_val SEGS E _ (c_w v) 24 4 (SOff 41 0) (c_n v));
    [cbn [sv_denot]; rewrite E41, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    apply s3_val_mem_of_aval. exact WWN. }
assert (HDW : all_disjoint E s3_wregion (cr_regions_mid false)).
{ apply all_disjoint_of_extents. unfold cr_regions_mid, cr_stkm, cr_grecm, cr_frh, cr_frt, cr_frs, s3_wregion, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB 19%nat (c_w v) E19) by lia. rewrite (VB 33%nat 0x5e3740 E33) by lia. rewrite (VB 36%nat F E36) by lia.
  rewrite (VB 38%nat (SBc + F / 8) E38) by (pose proof (Z.div_pos F 8); pose proof (Z.div_le_upper_bound F 8 (2 ^ 47) ltac:(lia) ltac:(lia)); unfold SBc; lia).
  rewrite (VB 8%nat sp0 ltac:(rewrite (EE 8%nat 8%bv eq_refl); exact R8)) by lia.
  cbn [zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold SBc. repeat split; lia. }
pose proof (st_ok_pi_add_region E _ _ s3_wregion HS1 eq_refl HRW HDW) as HS. clear HS1.
lazymatch type of HS with st_ok_pi ?sg ?vl ?Ev ?s ?mm => let s' := eval vm_compute in s in change (st_ok_pi sg vl Ev s' mm) in HS end.
assert (HBx : U E crBx = SHADOW_OFF) by (unfold crBx; rewrite (U_atom E 32 SBc E32) by (unfold SBc; lia); reflexivity).
assert (U19 : U E (SOff 19 0) = c_w v) by (apply U_atom; [exact E19 | lia]).
assert (U33 : U E (SOff 33 0) = 0x5e3740) by (apply U_atom; [exact E33 | lia]).
pose proof (cr_grec_addressable B) as GA. s3_hyps GA.
pose proof (GA lyc Sc Wc memc mdc (A_G_REC + 928) 16 HAR ltac:(unfold A_G_REC; lia) ltac:(unfold A_G_REC; lia)) as GRA. clear GA.
shok_auto_with SHOK crBx E (mrestrict (w_H Wc) memc) [mkSHE 33 928 944; mkSHE 19 16 28]
  ltac:(first
  [ apply (shent_ok_of_range SEGS (w_H Wc) memc E crBx 33 (A_G_REC + 928) 16 0x5e3740 928 944 GRA HBx U33);
    unfold A_G_REC, SHADOW_OFF; [lia | lia | intros x Hx; cbn [Z.min Z.max] in Hx; lia]
  | apply (shent_ok_of_range SEGS (w_H Wc) memc E crBx 19 (c_w v + 16) 12 (c_w v) 16 28 WRA HBx U19);
    [lia | lia | intros x Hx; cbn [Z.min Z.max] in Hx; unfold SHADOW_OFF; lia] ]).
assert (E36u : bv_unsigned (ew E 36) = F) by (rewrite E36; apply unsigned_lit_small; lia).
psrr_branch_tok RUN BR HS SHOK crSpan.
- (* bltz taken: the refusal (0x86f7c .. 0x86f94) *)
  rewrite (s3_branch_lt0 E 10 (c_code v) E10) in Hc by (pose proof (s3_code_range v); lia).
  apply Z.ltb_lt in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK crSpan CR_SNPRINTF.
  { s3_awr E36u pos. }
  lazymatch goal with |- SRr _ _ (mkCfg _ ?md0) _ => set (mdv := md0) in *; clearbody mdv end.
  pmkst HS.
  pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => F <= a < F + 32) HFr
    ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
      repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?E36u in Hrr; cbv beta; lia|]);
      destruct Hin)) as UN.
  prreg HS (19%bv : bv 5) Q19. prreg HS (21%bv : bv 5) Q21. prreg HS (10%bv : bv 5) Q10.
  prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12. prreg HS (13%bv : bv 5) Q13.
  apply (SNP v lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv pos CX).
  + apply (s3_mid_kept v lyc Sc Wc memc mdc (ms_mem ms) mdv pos CX MID HJ). exact UN.
  + s3_regs_tac HS (EE 2%nat 2%bv eq_refl) (EE 3%nat 3%bv eq_refl) (EE 4%nat 4%bv eq_refl) (EE 8%nat 8%bv eq_refl)
      (EE 27%nat 27%bv eq_refl) R2 R3 R4 R8 R27 E32 E33 E36 E38.
  + exact Hc.
  + rewrite Q19, E36u. reflexivity.
  + rewrite Q21. exact E10.
  + rewrite Q10, E36u. reflexivity.
  + rewrite Q11. reflexivity.
  + rewrite Q12, <- (Z_to_bv_bv_unsigned _ (ew E 252)), (HEI 252%nat ltac:(unfold A_TEXT, A_LIM; lia)).
    change 252%nat with (A_OBJ 11). rewrite (HVO 11%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)). reflexivity.
  + rewrite Q13. exact E10.
  + exact LS.
  + exact HFRM.
- (* bltz not taken: the shape (0x86f1c): check #6 (w + 24, token with its slow block), lw n, beqz *)
  rewrite (s3_branch_lt0 E 10 (c_code v) E10) in Hc by (pose proof (s3_code_range v); lia).
  apply Z.ltb_ge in Hc. rename Hc into Hc0.
  paj_run_tok RUN HS HJ SHOK crSpan.
  { s3_awr E36u pos. }
  lazymatch goal with |- SRr _ _ (mkCfg _ ?md0) _ => set (mdv1 := md0) in *; clearbody mdv1 end.
  pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => F <= a < F + 32) HFr
    ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
      repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?E36u in Hrr; cbv beta; lia|]);
      destruct Hin)) as UN1.
  clear HF HFr HG.
  lazymatch type of HS with st_ok_pi _ _ ?E1 _ (restrict _ ?ms1) => set (E2 := E1) in *; set (mem1 := ms_mem ms1) in * end.
  assert (OLD2 : forall n, (n < 1024)%nat -> ew E2 n = ew E n)
    by (intros nn Hnn; unfold E2; rewrite !ew_ewset_other by lia; reflexivity).
  assert (E41b : ew E2 41 = Z_to_bv 64 (c_n v)) by (rewrite OLD2 by lia; exact E41).
  assert (E36u2 : bv_unsigned (ew E2 36) = F) by (rewrite OLD2 by lia; exact E36u).
  psrr_branch_tok RUN BR HS SHOK crSpan.
  + (* beqz taken: no word; a0 = mod-host's "resp 0" (0x210e0), to the join *)
    rewrite branch_eq_U, (U_atom E2 41 (c_n v) E41b) in Hc by lia.
    replace (U E2 (SLit 0)) with 0 in Hc by reflexivity. apply Z.eqb_eq in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK crSpan CR_JOIN.
    { s3_awr E36u2 pos. }
    lazymatch goal with |- SRr _ _ (mkCfg _ ?md0) _ => set (mdv2 := md0) in *; clearbody mdv2 end.
    pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => F <= a < F + 32) HFr
      ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?E36u2 in Hrr; cbv beta; lia|]);
        destruct Hin)) as UN2.
    clear HF HFr HG.
    pmkst HS.
    lazymatch type of HS with st_ok_pi _ _ ?E1 _ _ => set (E3 := E1) in * end.
    assert (OLD3 : forall n, (n < 1024)%nat -> ew E3 n = ew E n)
      by (intros nn Hnn; unfold E3; rewrite ?ew_ewset_other by lia; apply OLD2; exact Hnn).
    lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ ?mm _) _) _ =>
      assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ (frame_addr lyc 1 pos <= a < frame_addr lyc 1 pos + 32) ->
        rdW Wc mm a = rdW Wc memc a) by (intros a Ha Hna; rewrite (UN2 a Ha Hna); exact (UN1 a Ha Hna)) end.
    prreg HS (10%bv : bv 5) Q10.
    assert (MID2 := s3_mid_kept v lyc Sc Wc memc mdc _ mdv2 pos CX MID HJ UN).
    apply (JOIN v lyc Sc Wc _ _ mdv2 pos 0x210e0 CX MID2).
    * s3_regs_tac HS (eq_trans (OLD3 2%nat ltac:(lia)) (EE 2%nat 2%bv eq_refl))
        (eq_trans (OLD3 3%nat ltac:(lia)) (EE 3%nat 3%bv eq_refl)) (eq_trans (OLD3 4%nat ltac:(lia)) (EE 4%nat 4%bv eq_refl))
        (eq_trans (OLD3 8%nat ltac:(lia)) (EE 8%nat 8%bv eq_refl)) (eq_trans (OLD3 27%nat ltac:(lia)) (EE 27%nat 27%bv eq_refl))
        R2 R3 R4 R8 R27 (eq_trans (OLD3 32%nat ltac:(lia)) E32) (eq_trans (OLD3 33%nat ltac:(lia)) E33)
        (eq_trans (OLD3 36%nat ltac:(lia)) E36) (eq_trans (OLD3 38%nat ltac:(lia)) E38).
    * exact Hc0.
    * rewrite Q10, (OLD3 254%nat ltac:(lia)), <- (Z_to_bv_bv_unsigned _ (ew E 254)), (HEI 254%nat ltac:(unfold A_TEXT, A_LIM; lia)).
      change 254%nat with (A_OBJ 13). rewrite (HVO 13%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)). reflexivity.
    * lia.
    * replace (shape_strA (c_n v) (c_w0 v)) with REC_MOD_HOST_SHAPE by (unfold shape_strA; rewrite Hc; reflexivity).
      pose proof (cr_lit0_arg B RLO RHI) as L0. s3_hyps L0. exact (L0 v lyc Sc Wc _ mdv2 pos CX MID2).
    * exact LS.
  + (* beqz not taken: a word; check #7 (w + 16), ld w->w, check #8 (w->w[0]), ld s3 = w->w[0], to strlen *)
    rewrite branch_eq_U, (U_atom E2 41 (c_n v) E41b) in Hc by lia.
    replace (U E2 (SLit 0)) with 0 in Hc by reflexivity. apply Z.eqb_neq in Hc.
    destruct (WWB Hc) as ((q1 & k1 & Hq1 & Hq1a & Hq1b) & HV & _).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hq1) as (Hq16 & Hq4096 & Hqceil & Hqapp & _ & _ & Hqn).
    pose proof (req_size_pos0 k1 ltac:(lia)) as [Hkq0 Hkq].
    pose proof (blk_off_imgP B) as BO. s3_hyps BO. pose proof (BO _ _ _ _ _ _ _ HAR Hq1) as Hqimg. clear BO.
    unfold off_img in Hqimg.
    pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ 1 pos HAR Hq1 Hfin) as Hqf.
    unfold zdisjoint in Hqf; cbn [fst snd] in Hqf. change (fs_frame_bytes 1) with 128 in Hqf. fold F in Hqf.
    unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Hqapp.
    assert (Eww : c_ww v mod 2 ^ 64 = c_ww v) by (apply Z.mod_small; lia).
    assert (E40b : ew E2 40 = Z_to_bv 64 (c_ww v)) by (rewrite OLD2, E40, Eww by lia; reflexivity).
    assert (E42b : ew E2 42 = Z_to_bv 64 (c_p0 v mod 2 ^ 64)) by (rewrite OLD2 by lia; exact E42).
    assert (VB2 : forall k z, (k < 1024)%nat -> ew E k = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> base_val E2 (Some k) = z).
    { intros k z Hk Hkz Hz. cbn [base_val]. rewrite OLD2, Hkz by exact Hk. apply unsigned_lit_small. exact Hz. }
    assert (HF40 : afact_ok E2 40 (mkAF 4096 140737479966720 0)).
    { unfold afact_ok; cbn [af_lo af_hi af_al2]. rewrite E40b, unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r. lia. }
    pose proof (st_ok_pi_add_fact E2 _ _ 40 _ HS HF40) as HS1. clear HS.
    assert (HRWW : region_ok SEGS E2 (mrestrict (w_H Wc) mem1) s3_wwregion).
    { unfold region_ok, s3_wwregion; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      cbn [base_val]. rewrite E40b, unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E2 _ (c_ww v) 0 8 (SOff 42 0) (c_p0 v mod 2 ^ 64));
      [cbn [sv_denot]; rewrite E42b, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | apply Z.mod_pos_bound; lia | zside |].
      rewrite Z.add_0_r. apply s3_val_mem_mod64.
      apply (val_mem_kept SEGS (w_H Wc) (w_H Wc) memc mem1 (c_ww v) 8 (c_p0 v)); [|apply s3_val_mem_of_aval; exact HV].
      intros k Hk. apply UN1; [change (Z.of_nat 8) with 8 in Hk; lia|]. cbv beta. change (Z.of_nat 8) with 8 in Hk. lia. }
    lazymatch type of HS1 with st_ok_pi _ _ _ ?s _ => let r := eval vm_compute in (ss_mem s) in
      assert (HDWW : all_disjoint E2 s3_wwregion r) end.
    { apply all_disjoint_of_extents. unfold s3_wwregion, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
      rewrite (VB2 40%nat (c_ww v) ltac:(lia) ltac:(rewrite E40, Eww; reflexivity)) by lia.
      rewrite (VB2 19%nat (c_w v) ltac:(lia) E19) by lia. rewrite (VB2 33%nat 0x5e3740 ltac:(lia) E33) by lia.
      rewrite (VB2 36%nat F ltac:(lia) E36) by lia.
      rewrite (VB2 38%nat (SBc + F / 8) ltac:(lia) E38) by (unfold SBc; lia).
      rewrite (VB2 8%nat sp0 ltac:(lia) ltac:(rewrite (EE 8%nat 8%bv eq_refl); exact R8)) by lia.
      cbn [zall_disjoint]. unfold zdisj. cbn [fst snd].
      unfold SBc. repeat split; lia. }
    pose proof (st_ok_pi_add_region E2 _ _ s3_wwregion HS1 eq_refl HRWW HDWW) as HS. clear HS1.
    lazymatch type of HS with st_ok_pi ?sg ?vl ?Ev ?s ?mm => let s' := eval vm_compute in s in change (st_ok_pi sg vl Ev s' mm) in HS end.
    assert (HBx2 : U E2 crBx = SHADOW_OFF)
      by (unfold crBx; rewrite (U_atom E2 32 SBc ltac:(rewrite OLD2 by lia; exact E32)) by (unfold SBc; lia); reflexivity).
    assert (U40 : U E2 (SOff 40 0) = c_ww v) by (apply U_atom; [exact E40b | lia]).
    assert (RAw : range_addressable (rdW Wc mem1) SHADOW_OFF (c_ww v) 8)
      by exact (range_addressable_of_block SEGS B LAWS lyc Sc Wc mem1 mdv1 q1 k1 (c_ww v) 8 (proj1 HJ) Hq1 ltac:(lia) ltac:(lia)).
    lazymatch type of SHOK with sh_ok _ _ ?SH _ _ =>
      assert (SHOK2 : sh_ok SEGS crBx (mkSHE 40 0 8 :: SH) E2 (mrestrict (w_H Wc) mem1)) end.
    { apply Forall_cons; [|exact SHOK].
      apply (shent_ok_of_range SEGS (w_H Wc) mem1 E2 crBx 40 (c_ww v) 8 (c_ww v) 0 8 RAw HBx2 U40);
      [lia | lia | intros x Hx; cbn [Z.min Z.max] in Hx; unfold SHADOW_OFF; lia]. }
    clear SHOK.
    assert (E36u3 := E36u2).
    paj_run_to_tok RUNTO HS HJ SHOK2 crSpan CR_STRLEN.
    { s3_awr E36u3 pos. }
    lazymatch goal with |- SRr _ _ (mkCfg _ ?md0) _ => set (mdv2 := md0) in *; clearbody mdv2 end.
    pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => F <= a < F + 32) HFr
      ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?E36u3 in Hrr; cbv beta; lia|]);
        destruct Hin)) as UN2.
    clear HF HFr HG.
    pmkst HS.
    lazymatch type of HS with st_ok_pi _ _ ?E1 _ _ => set (E3 := E1) in * end.
    assert (OLD3 : forall n, (n < 1024)%nat -> ew E3 n = ew E n)
      by (intros nn Hnn; unfold E3; rewrite ?ew_ewset_other by lia; apply OLD2; exact Hnn).
    lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ ?mm _) _) _ =>
      assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ (frame_addr lyc 1 pos <= a < frame_addr lyc 1 pos + 32) ->
        rdW Wc mm a = rdW Wc memc a) by (intros a Ha Hna; rewrite (UN2 a Ha Hna); exact (UN1 a Ha Hna)) end.
    prreg HS (19%bv : bv 5) Q19. prreg HS (10%bv : bv 5) Q10.
    assert (MID2 := s3_mid_kept v lyc Sc Wc memc mdc _ mdv2 pos CX MID HJ UN).
    apply (STRL v lyc Sc Wc _ _ mdv2 pos CX MID2).
    * s3_regs_tac HS (eq_trans (OLD3 2%nat ltac:(lia)) (EE 2%nat 2%bv eq_refl))
        (eq_trans (OLD3 3%nat ltac:(lia)) (EE 3%nat 3%bv eq_refl)) (eq_trans (OLD3 4%nat ltac:(lia)) (EE 4%nat 4%bv eq_refl))
        (eq_trans (OLD3 8%nat ltac:(lia)) (EE 8%nat 8%bv eq_refl)) (eq_trans (OLD3 27%nat ltac:(lia)) (EE 27%nat 27%bv eq_refl))
        R2 R3 R4 R8 R27 (eq_trans (OLD3 32%nat ltac:(lia)) E32) (eq_trans (OLD3 33%nat ltac:(lia)) E33)
        (eq_trans (OLD3 36%nat ltac:(lia)) E36) (eq_trans (OLD3 38%nat ltac:(lia)) E38).
    * exact Hc0.
    * exact Hc.
    * rewrite Q19, (OLD3 42%nat ltac:(lia)). exact E42.
    * rewrite Q10, (OLD3 42%nat ltac:(lia)). exact E42.
    * exact LS.
Qed.

End e.
End f.
End d.
