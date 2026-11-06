(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: segment 8 of check_reply's walk (fuzz_command.asan, 0x86d78): the epilogue
   from 0x86ff8 to the return, after proofs/cgif/cgif_file_fuzzer/lib/A/ACh2.v (the return and the contract's post,
   lines 259-290) and A/AChd.v (the leaf return).

   The walk seeds the mid-walk state (check_reply_sd.v cr_seed) with the frame's shadow writable, adds the frame's
   flag cell (atom 37) as a writable region, and runs to the `ret` at 0x870d4 with one plain run that ends the
   frame (PaLibF.v aj_flag_store_pi): shadow bytes 4..7 = 0xf8, frame + 0 = 0x45e0360e, `beqz s2` not taken (the
   frame is at or above 4096), the 16 shadow bytes = 0xf5, the flag byte = 0 (`ld a0,120(s2); sb zero,0(a0)`), the
   callee-saved registers loaded back from below sp0, sp = s0 - 128 + 128. The return is apost_baseF at this
   segment's FP state through PaFx.v's apost_baseF_of_base (the epilogue changes no FP state). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString RtFormat RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaRun PaShadow PaStep CmdSyms
  CmdList CmdPa PaJournal CmdPaLib PaLibG PaLibH PaLibF PaDenot PaSB PaCall CmdBase CmdRep CmdObj CmdRo PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import check_reply_c check_reply_k check_reply_m check_reply_sd.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the frame's flag cell, written by the epilogue *)
Definition cr_flagr : YP09.region := YP09.mkRegion (Some 37%nat) 0 1 0 1 [].
(* the state at 0x86ff8: the mid-walk state with the frame's shadow writable and the flag cell *)
Definition ss_epi : sstate := mkSS CR_EPI sr_mid (cr_flagr :: cr_regions_mid true) None cr_facts_mid.

(* two values whose 8 little-endian bytes agree are equal mod 2^64 *)
Lemma s8_le_byte8 : forall x y, (forall k, (k < 8)%nat -> le_byte x 8 k = le_byte y 8 k) -> x mod 2 ^ 64 = y mod 2 ^ 64.
Proof.
intros x y H. apply Z.bits_inj'. intros i Hi.
destruct (Z.lt_ge_cases i 64) as [Hi64 | Hi64].
- pose proof (Z.div_mod i 8 ltac:(lia)) as Di. pose proof (Z.mod_pos_bound i 8 ltac:(lia)) as Mi.
  assert (Hq : 0 <= i / 8 < 8) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  pose proof (H (Z.to_nat (i / 8)) ltac:(lia)) as Hb. unfold le_byte in Hb.
  rewrite Z2Nat.id in Hb by lia.
  replace (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in Hb by reflexivity. change 256 with (2 ^ 8) in Hb.
  apply (f_equal (fun z => Z.testbit z (i mod 8))) in Hb.
  rewrite !Z.mod_pow2_bits_low in Hb by lia.
  rewrite !Z.shiftr_spec in Hb by lia.
  replace (i mod 8 + 8 * (i / 8)) with i in Hb by lia. exact Hb.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

(* x + 1 <= lo or lo + n <= x, for an x that no address of [lo, lo + n) equals *)
Lemma s8_sep1 : forall x lo n, (forall a, lo <= a < lo + n -> x <> a) -> x + 1 <= lo \/ lo + n <= x.
Proof.
intros x lo n H. destruct (Z_lt_le_dec x lo) as [h | h]; [left; lia|].
destruct (Z_lt_le_dec x (lo + n)) as [h' | h']; [exfalso; exact (H x ltac:(lia) eq_refl) | right; lia].
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variables RLO RHI : Z.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Let RUNF := aj_flag_store_pi B LAWS ML ASF FFL.
Let RET := paj_ret_at (PL := PL_cmd) (PI := PI).

(* the reply block's address and size as cr_seed takes them: g_rec.reply is the start of a live block that holds
   the reply and its NUL, |reply| + 1 <= LMAX + 2 *)
Lemma cr_s8_nums : forall v, cr_cx B RLO RHI v ->
4096 <= c_p v /\ c_p v mod 16 = 0 /\ c_p v + c_nr v + 1 <= 140737479966720 /\ c_nr v + 1 <= 8194.
Proof.
intros v HCX.
pose proof HCX as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & HREP & _ & HRR & _ & HREPV & _).
destruct HREP as (Q & (_ & _ & _ & _ & _ & HRP & _) & _).
rewrite HRR in HRP. unfold areply_at in HRP. destruct (l_reply Q) as [[p m]|]; [|cbn in HRP; contradiction].
destruct HRP as (P1 & _ & _ & _ & P5 & P6 & _ & P8). cbn [fst snd] in *.
pose proof HPRE as (HAR & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ p m HAR P5) as (Hp16 & Hp4096 & Hpceil & _ & _ & _ & Hm).
pose proof (req_size_pos m (proj1 Hm)) as [_ Hr].
pose proof asan_consts as (C1 & _).
assert (Ep : c_p v = p).
{ unfold c_p. assert (Hpm : p mod 2 ^ 64 = p) by (apply Z.mod_small; lia).
  rewrite <- Hpm. apply s8_le_byte8. intros k Hk.
  pose proof (HREPV k Hk) as E1. pose proof (P1 k Hk) as E2. rewrite E1 in E2. injection E2 as E. exact E. }
rewrite length_app in P6, P8. cbn [length] in P6, P8. unfold c_nr, LMAX in *. rewrite Ep. lia.
Qed.

Lemma cr_s8 : CR_EPI_stmt B RLO RHI.
Proof.
intros v lyc Sc Wc regs1 memc mdc pos CX MID RA LS.
pose proof pa_segs_low as Hsegs.
destruct (cr_s8_nums v CX) as (Hp4096 & Hp16 & Hphi & Hnr).
pose proof (cr_seed B RLO RHI LAWS v lyc Sc Wc regs1 memc mdc pos CR_EPI true CX MID RA Hp4096 Hp16 Hphi Hnr) as HS.
pose proof CX as (HPRE & _).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof MID as (HJ & HPerm & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
pose proof RA as (R2 & R3 & R4 & R8 & R9 & R18 & R23 & R22 & R24 & R25 & R20 & R26 & R27).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTK : CHECK_REPLY_STK = 12464) by reflexivity.
assert (HSB : SBc = 2147450880) by reflexivity.
assert (Hfin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 pos HAR Hfin) as (HFal & _ & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 pos HAR Hfin) as (HF4096 & HFceil & _).
destruct (FFL _ _ _ _ _ 1 pos HAR Hfin) as (HFLp & HFLo & _ & HFL4096 & HFLz & HFLc).
change (fs_frame_bytes 1) with 128 in HFpres, HFSpres, HFceil. change (128 / 8) with 16 in HFSpres.
pose proof (Z.div_pos (frame_addr lyc 1 pos) 8 ltac:(lia) ltac:(lia)) as HF8lo.
pose proof (Z.div_le_upper_bound (frame_addr lyc 1 pos) 8 (2 ^ 47) ltac:(lia) ltac:(lia)) as HF8hi.
assert (Hsp0 : alloc_ceiling + 12464 <= c_sp v <= 2 ^ 47) by (unfold c_sp; lia).
(* the environment *)
remember (crM regs1 v lyc pos) as E eqn:HE in HS.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; unfold crM; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r) by (intros; rewrite HE; apply crM_reg; assumption).
assert (EX : forall j, (j < 23)%nat -> ew E (32 + j) = nth j (crM_extra v lyc pos) (Z_to_bv 64 0)) by (intros; rewrite HE; apply crM_extra_nth; assumption).
pose proof (EX 4%nat ltac:(lia)) as E36. pose proof (EX 5%nat ltac:(lia)) as E37. pose proof (EX 6%nat ltac:(lia)) as E38.
cbn [Nat.add nth crM_extra map app] in E36, E37, E38.
assert (E43 : ew E 43 = getr (c_regs v) (1%bv : bv 5)) by (change 43%nat with (32 + 11)%nat; rewrite EX by lia; reflexivity).
assert (U8 : bv_unsigned (ew E 8) = c_sp v) by (rewrite (EE 8%nat 8%bv eq_refl), R8; unfold w64; apply unsigned_lit_small; lia).
assert (U36 : bv_unsigned (ew E 36) = frame_addr lyc 1 pos) by (rewrite E36; apply unsigned_lit_small; lia).
assert (U37 : bv_unsigned (ew E 37) = flag_addr lyc 1 pos) by (rewrite E37; apply unsigned_lit_small; lia).
assert (U38 : bv_unsigned (ew E 38) = SBc + frame_addr lyc 1 pos / 8) by (rewrite E38; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = 0x5e3740) by (change 33%nat with (32 + 1)%nat; rewrite (EX 1%nat ltac:(lia)); cbn [nth crM_extra map app]; apply unsigned_lit_small; lia).
(* the flag cell is outside the frame and its shadow (it is the runtime's) *)
assert (NF : forall a, frame_addr lyc 1 pos <= a < frame_addr lyc 1 pos + 128 -> flag_addr lyc 1 pos <> a)
by (intros a Ha Heq; apply (proj2 (HFpres a Ha)); rewrite <- Heq; exact HFLo).
assert (NS : forall a, SBc + frame_addr lyc 1 pos / 8 <= a < SBc + frame_addr lyc 1 pos / 8 + 16 -> flag_addr lyc 1 pos <> a).
{ intros a Ha Heq. apply (proj2 (HFSpres (a - (SBc + frame_addr lyc 1 pos / 8)) ltac:(lia))).
  unfold shadow_addr. rewrite <- SBc_SHADOW_OFF.
  replace (SBc + frame_addr lyc 1 pos / 8 + (a - (SBc + frame_addr lyc 1 pos / 8))) with a by lia.
  rewrite <- Heq. exact HFLo. }
pose proof (s8_sep1 _ _ _ NF) as SF. pose proof (s8_sep1 _ _ _ NS) as SS.
destruct HFLz as [HFLimg _]. unfold off_img in HFLimg.
(* the flag cell as a writable region *)
assert (HS2 : st_ok_pi SEGS VAL E ss_epi (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + CR_EPI)) memc (seg_rom SEGS)))).
{ apply (st_ok_pi_add_region E _ _ cr_flagr HS eq_refl).
  - unfold region_ok, cr_flagr. rewrite restrict_mkst_fx.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem].
    rewrite U37. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. replace (flag_addr lyc 1 pos + o) with (flag_addr lyc 1 pos) by lia.
    apply (apresent_writable SEGS). exact HFLp.
  - change (ss_mem (ss_mid CR_EPI true)) with (cr_regions_mid true).
    unfold cr_regions_mid, cr_stkm, cr_grecm, cr_frh, cr_frt, cr_frs, cr_flagr. cbn [all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U8, U33, U36, U37, U38.
    repeat split; first [exact I | lia]. }
clear HS.
unfold cr_at.
paj_run_flag_sh RUNF HS2 HJ.
- lia.
- intros a (r & Hr & Ha).
  change (ss_mem ss_epi) with [cr_flagr; cr_stkm; cr_grecm; cr_frh; cr_frt; cr_frs true] in Hr.
  destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]];
  unfold cr_flagr, cr_stkm, cr_grecm, cr_frh, cr_frt, cr_frs in Ha;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; try lia.
  + left. unfold awr_byte. right; right; right; left. exists 1, pos. split; [left; reflexivity|].
    left. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes 1) with 128. rewrite U36 in Ha. lia.
  + left. unfold awr_byte. right; right; right; left. exists 1, pos. split; [left; reflexivity|].
    right. unfold in_zr, shadow_addr. cbn [fst snd]. change (fs_frame_bytes 1 / 8) with 16.
    rewrite <- SBc_SHADOW_OFF. rewrite U38 in Ha. lia.
- intros msr HSr. unfold st_ok_pi in HSr.
  pose proof (st_ok_mem_ok SEGS E _ msr HSr) as (_ & HOK & _).
  unfold abs_ss, setpc in HOK. cbn [ss_mem] in HOK.
  apply Forall_inv in HOK. destruct HOK as (_ & _ & _ & HC). apply Forall_inv in HC.
  destruct (HC 0 ltac:(split; [lia | cbv; reflexivity])) as (b & Hb1 & Hb2).
  cbn [base_val YP09.r_base YP09.c_off] in Hb2. rewrite U37 in Hb2.
  replace (flag_addr lyc 1 pos + 0 + 0) with (flag_addr lyc 1 pos) in Hb2 by lia. rewrite Hb2.
  cbn [YP09.cbyte YP09.c_val sv_denot] in Hb1. injection Hb1 as <-. vm_compute. reflexivity.
- prreg HS2 (1%bv : bv 5) Q1.
  eapply (RET Wc _ _ _ _ _ HS2 eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'. unfold CR_POST. apply (apost_baseF_of_base SEGS). unfold apost_base.
  lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists lyc, (stack_free_state 1 pos Sc), r, m, d end.
  split; [cbn [ms_regs]; rewrite Q1, E43, Hra; reflexivity|].
  split; [eapply (ajournal_mono_k SEGS B); [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ | cbv [EV_CHECK_REPLY]; lia]|].
  split; [| split; [unfold ablocks; rewrite blocks_stack_free_state; exact HPerm|]].
  2: { destruct LS as (Ely & fS & ES). split; [exact Ely|].
       exists (st_fs (stack_free_state 1 pos Sc)). rewrite ES. reflexivity. }
  unfold aregs_preserved. intros r Hr.
  assert (Hcases : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27 \/ False)
  by (unfold acallee_saved in Hr; lia).
  clear Hr.
  repeat (destruct Hcases as [-> | Hcases]); [..| destruct Hcases];
  (rewrite (st_ok_pi_restrict_reg (w_H Wc) E _ _ _ HS2); cbn [ms_regs];
   lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ => let e := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with e end;
   cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned).
  all: try (lazymatch goal with |- ew _ ?n = getr _ (Z_to_bv 5 ?rr) =>
    let j := eval compute in (n - 32)%nat in change n with (32 + j)%nat; rewrite (EX j) by lia; reflexivity end).
  all: first
  [ rewrite (EE 8%nat 8%bv eq_refl), R8; replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity);
    unfold w64, c_sp, spZ; apply Z_to_bv_bv_unsigned
  | rewrite (EE 3%nat 3%bv eq_refl), R3; replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity);
    rewrite Hgp; reflexivity
  | rewrite (EE 4%nat 4%bv eq_refl), R4; replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity);
    rewrite Htp; reflexivity
  | rewrite (EE 27%nat 27%bv eq_refl), R27; replace (Z_to_bv 5 27) with (27%bv : bv 5) by (apply bv_eq; reflexivity);
    reflexivity ].
Qed.
End e.
End f.
End d.
