(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: segment F of LLVMFuzzerTestOneInput's ASan walk (plugin-hostd/fuzz_command, 0x86974 .. 0x8699c): the three frees of the words blocks and the latch back to the loop head or out to the second rec_clear, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACbk.v (pb_wcb: run, branch, exit) and A/ACh6.v (a segment statement proved from the statements of the points it leaves to). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import ACfn AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaSB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdRecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_clear_c send_message_c check_reply_c check_arity_c check_words_c check_refusal_c check_round_trip_c
verbs_receive_c LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_defs
LLVMFuzzerTestOneInput_s01 LLVMFuzzerTestOneInput_s70.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require SlotSpec HarnessProps.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs StrFun.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Local Open Scope Z_scope.

Lemma ltf_perm_shift : forall {X} (a b c : list X), Permutation (a ++ b ++ c) (c ++ a ++ b).
Proof. intros X a b c. rewrite (app_assoc a b c). apply Permutation_app_comm. Qed.
Lemma ltf_sub32 : forall m, (32 - Datatypes.S m = 31 - m)%nat.
Proof. intros m. lia. Qed.

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
Variable MT : ameter_ops.
(* the per-binary record and the walk hypotheses, with cgif's names *)
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
Hypothesis IMG : cmd_img_facts SEGS B.
Hypothesis SIGP : cmd_sig_prog.
(* the runtime entry this segment reaches: the statement's own hypothesis, word for word *)
Hypothesis AFREE4 : afree04_rule SEGS B MT.
Let UNOWNED := cmd_prog_unowned SEGS B LAWS HB IMG.

(* ---- the budget of the three frees ---- *)
Lemma ltf_free_le_U : mo_free MT <= LT_U MT.
Proof. unfold LT_U. pose proof (mo_malloc_nonneg MT MTL 32784 ltac:(lia)). lia. Qed.

Lemma ltf_bud_pre : forall cx ly S (W : world SEGS) mem md own k acc rem,
  lt_base B MT cx ->
  ajournal SEGS B LTOI_STK (x_sp0 cx) cmd_PG (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) own ly S W mem md k ->
  lt_bud MT cx S k acc rem -> 1 <= rem ->
  st_nev S < EV_MAX /\ mo_ok MT S (mo_free MT).
Proof.
intros cx ly S W mem md own k acc rem HBASE HJ HBUD Hrem.
pose proof HBASE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hev & _ & MOK0 & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & Hk & _).
pose proof HBUD as (Hk0 & Hrem0 & Hkr & Hmle & Hacc & Hax).
pose proof ltf_free_le_U as HU. pose proof LT_U_nonneg MT MTL as HU0.
assert (Hrle : acc + mo_free MT <= XM_LTOI MT (x_pl cx)).
{ assert (Hm : 1 * LT_U MT <= rem * LT_U MT) by (apply Z.mul_le_mono_nonneg_r; lia). lia. }
split; [lia|].
apply (mo_ok_step MT MTL (x_S cx) S acc (mo_free MT)); [|exact Hmle].
apply (mo_ok_le MT MTL (x_S cx) (acc + mo_free MT) (XM_LTOI MT (x_pl cx)) MOK0). lia.
Qed.

Lemma ltf_bud_step : forall cx S S2 k acc rem,
  lt_bud MT cx S k acc rem -> mo_le MT S S2 (mo_free MT) -> 1 <= rem ->
  lt_bud MT cx S2 (k + 1) (acc + mo_free MT) (rem - 1).
Proof.
intros cx S S2 k acc rem HBUD HLE Hrem.
pose proof HBUD as (Hk0 & Hrem0 & Hkr & Hmle & Hacc & Hax).
pose proof ltf_free_le_U as HU. pose proof LT_U_nonneg MT MTL as HU0.
pose proof (mo_free_nonneg MT MTL) as HF0.
assert (Hmul : (rem - 1) * LT_U MT = rem * LT_U MT - LT_U MT) by ring.
split; [lia|]. split; [lia|]. split; [lia|].
split; [exact (mo_le_trans MT MTL (x_S cx) S S2 acc (mo_free MT) Hmle HLE)|].
split; [lia | lia].
Qed.

Lemma ltf_bud_eq : forall cx S k acc X Y, lt_bud MT cx S k acc X -> X = Y -> lt_bud MT cx S k acc Y.
Proof. intros cx S k acc X Y H <-. exact H. Qed.

(* ---- what the three frees leave of the recorder and the frame ---- *)
Lemma ltf_exit_mem : forall cx O R q wb ly S (W : world SEGS) mem ly3 S3 (W3 : world SEGS) mem3,
  lt_slots cx (rdW W mem) -> lt_saved cx (rdW W mem) ->
  lt_rec B cx ly S W mem R O q wb ->
  Permutation (ablocks B ly3 S3) (O ++ x_bl0 B cx) ->
  ltf_keep B cx O (rdW W mem) (rdW W3 mem3) ->
  lt_slots cx (rdW W3 mem3) /\ lt_saved cx (rdW W3 mem3) /\ lt_rec B cx ly3 S3 W3 mem3 R O q [].
Proof.
intros cx O R q wb ly S W mem ly3 S3 W3 mem3 HSL HSAV HREC HPERM HK.
pose proof HREC as (HRREP & HSPILL & HCALLS & HQV & HQR & _).
assert (HKblk : forall pn, In pn O -> In pn (ablocks B ly3 S3)).
{ intros pn Hpn. apply (Permutation_in _ (Permutation_sym HPERM)). apply in_or_app. left. exact Hpn. }
split.
{ intros o v Ho. rewrite (rdword_ext (rdW W mem) (rdW W3 mem3)); [exact (HSL o v Ho)|].
  intros kk Hkk. apply HK. right. left.
  assert (Ho80 : 0 <= o <= 80).
  { unfold LT_SLOTS in Ho. cbn [In] in Ho.
    repeat (destruct Ho as [Hq | Ho]; [injection Hq as <- <-; lia|]). destruct Ho. }
  unfold x_sp1, x_sp0, LT_FRAME in *. lia. }
split.
{ intros i rr Hi. rewrite (rdword_ext (rdW W mem) (rdW W3 mem3)); [exact (HSAV i rr Hi)|].
  intros kk Hkk. apply HK. right. left.
  assert (Hi13 : (i < length LT_SAVED)%nat) by (apply (proj1 (nth_error_Some LT_SAVED i)); rewrite Hi; discriminate).
  change (length LT_SAVED) with 13%nat in Hi13.
  assert (Hiz : 1 <= Z.of_nat (Datatypes.S i) <= 13) by (rewrite Nat2Z.inj_succ; lia).
  unfold x_sp1, x_sp0, LT_FRAME in *. lia. }
split.
{ destruct HRREP as (Q & HA & HO).
  exists Q. split; [|exact HO].
  apply (ltf_arep_ext (ablocks B ly S) (ablocks B ly3 S3) (rdW W mem) (rdW W3 mem3) R Q O HA);
    [ intros pn Hpn; apply HO; exact Hpn
    | intros pn Hpn; apply HKblk; apply HO; exact Hpn
    | intros x Hx; apply HK; left; exact Hx ]. }
split; [exact HSPILL|]. split; [exact HCALLS|].
split.
{ apply (ltf_aval_ext (rdW W mem) (rdW W3 mem3)); [|exact HQV].
  intros i Hi. apply HK. left. left. apply ltf_PG_quit. cbn in Hi. lia. }
split; [exact HQR|].
rewrite app_nil_r. exact HPERM.
Qed.

(* every address the segment reads is a machine address *)
Lemma ltf_bnd : forall cx O ly S (W : world SEGS) mem md,
  lt_base B MT cx -> AR SEGS B ly S W mem md ->
  (forall pn, In pn O -> In pn (ablocks B ly S)) ->
  forall a, ltf_rk O a \/ (x_sp1 cx <= a < x_sp0 cx) \/
            (exists b n, In (b, n) (x_bl0 B cx) /\ b <= a < b + req_size n) -> 0 <= a < 2 ^ 64.
Proof.
intros cx O ly S W mem md HBASE HAR HO a Ha.
pose proof HBASE as (HPRE0 & _).
pose proof HPRE0 as (HAR0 & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & _).
destruct Ha as [[Hfp | (b & mm & Hb & Hrg)] | [Hs | (b & mm & Hb & Hrg)]].
- destruct (UNOWNED a Hfp) as (Himg & _). pose proof (pa_img_range a Himg). lia.
- destruct (al_blocks _ _ LAWS ly S W mem md b mm HAR (HO _ Hb)) as (_ & Hb4 & Hbc & _). lia.
- unfold x_sp1, x_sp0, LTOI_STK, LLVMF_STK, LT_FRAME in *. lia.
- destruct (al_blocks _ _ LAWS (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) b mm HAR0 Hb)
    as (_ & Hb4 & Hbc & _). lia.
Qed.

(* reading a register of a symbolic state without reducing its symbolic value *)
Ltac ltf_reg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  end.

(* ---- the segment: 0x86974 .. 0x8699c; its continuations at every FP state (the defs' LTA_LH and LTA_Z),
   applied at the ambient fx, which the free wrapper keeps ---- *)
Theorem lt_seg_F : forall m, LTA_LH B MT (Datatypes.S m) -> LTA_Z B MT -> LT_F_stmt B MT m.
Proof.
intros m HLH HZ.
pose proof (paj_run B LAWS) as RUN. pose proof (paj_run_to B LAWS) as RUNTO.
pose proof (paj_branch (PI := PI)) as BR.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBok.
pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_value as [_ HAC].
unfold LT_F_stmt.
intros cx ly S W regs mem md k acc r Rh R2 O2 q2 text copy arr
  HBASE Hfrm HBODY Hr H19 H20 H26 H27 H24 H23 H25.
cbv zeta. intros HREC HBUD.
pose proof HBODY as (HFRAME & HSLOTS & R8 & R9 & R18 & R22 & Hm32 & Hn & Hpblk).
pose proof HFRAME as (HJ & Hsp & Hgp & Htp & HSAV).
pose proof HREC as (HRREP & HSPILL & HCALLS & HQV & HQR & HPERM0).
pose proof HBASE as (HPRE0 & _).
pose proof (ev_from_nonneg (31 - m) R2 (x_rest cx (lt_r' (x_pl cx) (x_n cx) r))) as HEV0.
pose proof (lt_len_range (x_pl cx) (x_n cx) r ltac:(lia)) as HLR.
assert (Hhdr : 0 < SlotSpec.hdr_n r <= r) by (unfold SlotSpec.hdr_n; lia).
assert (Hrb : 0 <= lt_r' (x_pl cx) (x_n cx) r <= r - SlotSpec.hdr_n r) by (unfold lt_r'; lia).
(* the payload's block, for the bound on x_p *)
destruct (al_blocks _ _ LAWS (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) (x_p cx) (x_n cx)
  (proj1 HPRE0) Hpblk) as (_ & Hp4096 & Hpceil & _).
pose proof (req_size_pos (x_n cx) ltac:(lia)) as [_ Hrq].
(* the three blocks, in the order the three frees take them *)
set (L0 := StrFun.strnlen_res (Z.of_nat (length (lt_D (x_pl cx) (x_n cx) r))) (lt_D (x_pl cx) (x_n cx) r)) in *.
assert (Ewb : lt_wblocks (lt_D (x_pl cx) (x_n cx) r) text copy arr
              = [(text, L0 + 1); (copy, L0 + 1); (arr, SlotSpec.arr_size L0)]) by reflexivity.
rewrite Ewb in HPERM0.
assert (HP1 : Permutation (ablocks B ly S)
          ([(text, L0 + 1); (copy, L0 + 1); (arr, SlotSpec.arr_size L0)] ++ (O2 ++ x_bl0 B cx)))
  by (eapply Permutation_trans; [exact HPERM0 | apply ltf_perm_shift]).
assert (HPT0 : ltf_pt B cx O2 [(text, L0 + 1); (copy, L0 + 1); (arr, SlotSpec.arr_size L0)]
                 regs ly S W regs mem md k (rdW W mem)).
{ split; [exact HJ|]. split; [exact HP1|]. split; [apply ltf_keep_refl | intros rr Hrr; reflexivity]. }
destruct (ltf_bud_pre cx ly S W mem md [] k acc _ HBASE HJ HBUD ltac:(lia)) as [Hnev1 MOK1].
unfold LO_RTRA.
(* 0x86974, 0x8697c, 0x86984: free(text), free(copy), free(arr) *)
apply (ltf_free B MT LAWS TL AFREE4 UNOWNED cx O2 text (L0 + 1) _ regs ly S W regs mem md k (rdW W mem)
  1168 24%bv _ HBASE (or_introl (conj eq_refl eq_refl)) HPT0 Hsp Hgp Htp R8 H24 Hnev1 MOK1).
intros ly1 S1 W1 regs1 mem1 md1 HPT1 MLE1.
change (1168 + 8) with 1176.
pose proof (ltf_bud_step cx S S1 k acc _ HBUD MLE1 ltac:(lia)) as HBUD1.
pose proof HPT1 as (HJ1 & _ & _ & _).
destruct (ltf_bud_pre cx ly1 S1 W1 mem1 md1 [] (k + 1) _ _ HBASE HJ1 HBUD1 ltac:(lia)) as [Hnev2 MOK2].
apply (ltf_free B MT LAWS TL AFREE4 UNOWNED cx O2 copy (L0 + 1) _ regs ly1 S1 W1 regs1 mem1 md1 (k + 1)
  (rdW W mem) 1176 23%bv _ HBASE (or_intror (or_introl (conj eq_refl eq_refl))) HPT1 Hsp Hgp Htp R8 H23
  Hnev2 MOK2).
intros ly2 S2 W2 regs2 mem2 md2 HPT2 MLE2.
change (1176 + 8) with 1184.
pose proof (ltf_bud_step cx S1 S2 (k + 1) _ _ HBUD1 MLE2 ltac:(lia)) as HBUD2.
pose proof HPT2 as (HJ2 & _ & _ & _).
destruct (ltf_bud_pre cx ly2 S2 W2 mem2 md2 [] (k + 1 + 1) _ _ HBASE HJ2 HBUD2 ltac:(lia)) as [Hnev3 MOK3].
apply (ltf_free B MT LAWS TL AFREE4 UNOWNED cx O2 arr (SlotSpec.arr_size L0) _ regs ly2 S2 W2 regs2 mem2 md2
  (k + 1 + 1) (rdW W mem) 1184 25%bv _ HBASE (or_intror (or_intror (conj eq_refl eq_refl))) HPT2
  Hsp Hgp Htp R8 H25 Hnev3 MOK3).
intros ly3 S3 W3 regs3 mem3 md3 HPT3 MLE3.
change (1184 + 8) with 1192.
pose proof (ltf_bud_step cx S2 S3 (k + 1 + 1) _ _ HBUD2 MLE3 ltac:(lia)) as HBUD3.
pose proof HPT3 as (HJ3 & HPERM3 & HK3 & HPR3).
cbn [app] in HPERM3.
(* what the three frees left *)
assert (HOsub : forall pn, In pn O2 -> In pn (ablocks B ly3 S3))
  by (intros pn Hpn; apply (Permutation_in _ (Permutation_sym HPERM3)); apply in_or_app; left; exact Hpn).
pose proof (ltf_bnd cx O2 ly3 S3 W3 mem3 md3 HBASE (proj1 HJ3) HOsub) as HBND3.
(* the registers the frees kept *)
assert (R3_2 : getr regs3 2 = getr regs 2)
  by exact (ltf_pres_get regs regs3 2 2%bv HPR3 ltac:(unfold acallee_saved; lia) ltac:(vm_compute; reflexivity)).
assert (R3_3 : getr regs3 3 = getr regs 3)
  by exact (ltf_pres_get regs regs3 3 3%bv HPR3 ltac:(unfold acallee_saved; lia) ltac:(vm_compute; reflexivity)).
assert (R3_4 : getr regs3 4 = getr regs 4)
  by exact (ltf_pres_get regs regs3 4 4%bv HPR3 ltac:(unfold acallee_saved; lia) ltac:(vm_compute; reflexivity)).
assert (R3_8 : getr regs3 8 = getr regs 8)
  by exact (ltf_pres_get regs regs3 8 8%bv HPR3 ltac:(unfold acallee_saved; lia) ltac:(vm_compute; reflexivity)).
assert (R3_9 : getr regs3 9 = getr regs 9)
  by exact (ltf_pres_get regs regs3 9 9%bv HPR3 ltac:(unfold acallee_saved; lia) ltac:(vm_compute; reflexivity)).
assert (R3_18 : getr regs3 18 = getr regs 18)
  by exact (ltf_pres_get regs regs3 18 18%bv HPR3 ltac:(unfold acallee_saved; lia) ltac:(vm_compute; reflexivity)).
assert (R3_19 : getr regs3 19 = getr regs 19)
  by exact (ltf_pres_get regs regs3 19 19%bv HPR3 ltac:(unfold acallee_saved; lia) ltac:(vm_compute; reflexivity)).
assert (R3_20 : getr regs3 20 = getr regs 20)
  by exact (ltf_pres_get regs regs3 20 20%bv HPR3 ltac:(unfold acallee_saved; lia) ltac:(vm_compute; reflexivity)).
assert (R3_22 : getr regs3 22 = getr regs 22)
  by exact (ltf_pres_get regs regs3 22 22%bv HPR3 ltac:(unfold acallee_saved; lia) ltac:(vm_compute; reflexivity)).
assert (R3_26 : getr regs3 26 = getr regs 26)
  by exact (ltf_pres_get regs regs3 26 26%bv HPR3 ltac:(unfold acallee_saved; lia) ltac:(vm_compute; reflexivity)).
assert (R3_27 : getr regs3 27 = getr regs 27)
  by exact (ltf_pres_get regs regs3 27 27%bv HPR3 ltac:(unfold acallee_saved; lia) ltac:(vm_compute; reflexivity)).
(* 0x8698c: the seed of the latch *)
destruct (ltf_seed W3 regs3 mem3 1192) as (HS & SHOK & HEI & HAE & EEo).
remember (ltf_E regs3) as E eqn:HE.
assert (E2 : ew E 2 = getr regs3 2) by (apply EEo; reflexivity).
assert (E3 : ew E 3 = getr regs3 3) by (apply EEo; reflexivity).
assert (E4 : ew E 4 = getr regs3 4) by (apply EEo; reflexivity).
assert (E8 : ew E 8 = getr regs3 8) by (apply EEo; reflexivity).
assert (E9 : ew E 9 = getr regs3 9) by (apply EEo; reflexivity).
assert (E18 : ew E 18 = getr regs3 18) by (apply EEo; reflexivity).
assert (E19 : ew E 19 = getr regs3 19) by (apply EEo; reflexivity).
assert (E20 : ew E 20 = getr regs3 20) by (apply EEo; reflexivity).
assert (E22 : ew E 22 = getr regs3 22) by (apply EEo; reflexivity).
assert (E26 : ew E 26 = getr regs3 26) by (apply EEo; reflexivity).
assert (E27 : ew E 27 = getr regs3 27) by (apply EEo; reflexivity).
clear HE.
assert (EV26 : ew E 26 = Z_to_bv 64 (lt_r' (x_pl cx) (x_n cx) r)) by exact (eq_trans E26 (eq_trans R3_26 H26)).
assert (EV27 : ew E 27 = Z_to_bv 64 (Z.of_nat m)) by exact (eq_trans E27 (eq_trans R3_27 H27)).
assert (EV19 : ew E 19 = Z_to_bv 64 (lt_len (x_pl cx) (x_n cx) r)) by exact (eq_trans E19 (eq_trans R3_19 H19)).
assert (EV20 : ew E 20 = Z_to_bv 64 (x_p cx + (x_n cx - r) + SlotSpec.hdr_n r))
  by exact (eq_trans E20 (eq_trans R3_20 H20)).
unfold ltf_ss in HS, SHOK.
(* 0x8698c: beqz s10 *)
psrr_branch_tok RUN BR HS SHOK ltf_Bspan.
- (* no byte left: 0x86a0c calls rec_clear for the last time *)
  assert (HR0 : lt_r' (x_pl cx) (x_n cx) r = 0).
  { rewrite branch_eq_U in Hc. apply Z.eqb_eq in Hc.
    rewrite (U_atom E 26 _ EV26 ltac:(lia)), (U_lit E 0 ltac:(lia)) in Hc. exact Hc. }
  paj_run_tok RUN HS HJ3 SHOK ltf_Bspan; try solve [apply awr_ok_nil].
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv := d) in *; clearbody mdv end.
  pmkst HS.
  rewrite (SIGP CS_rec_clear ltac:(unfold cmd_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
  replace (cmd_af CS_rec_clear) with AF_rec_clear by (vm_compute; reflexivity).
  prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3.
  prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9.
  lazymatch goal with
  | HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ ?m1) |- _ =>
    assert (KEEPF : forall a, 0 <= a < 2 ^ 64 -> rdW W3 m1 a = rdW W3 mem3 a)
      by (intros a Ha; apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) HFr);
          [ intros b wlo whi a' Hin' Hrr'; vm_compute in Hin'; destruct Hin' | exact Ha | intros Hff; destruct Hff ])
  end.
  lazymatch goal with
  | |- SRr _ _ (mkCfg (mkst ?rX _ ?mX _) _) _ =>
    assert (HKf : ltf_keep B cx O2 (rdW W mem) (rdW W3 mX))
      by (apply (ltf_keep_trans B cx O2 _ (rdW W3 mem3)); [exact HK3 | intros a Ha; exact (KEEPF a (HBND3 a Ha))]);
    destruct (ltf_exit_mem cx O2 R2 q2 _ ly S W mem ly3 S3 W3 mX HSLOTS HSAV HREC HPERM3 HKf)
      as (HSL3 & HSAV3 & HREC3);
    apply (HZ fx cx ly3 S3 W3 rX mX mdv (k + 1 + 1 + 1) (acc + mo_free MT + mo_free MT + mo_free MT) R2 O2 q2)
  end.
  + exact HBASE.
  + exact Hfrm.
  + split; [exact HJ3|].
    split; [transitivity (spZ regs); [unfold spZ; f_equal; exact (eq_trans P2 (eq_trans E2 R3_2)) | exact Hsp]|].
    split; [exact (eq_trans P3 (eq_trans E3 (eq_trans R3_3 Hgp)))|].
    split; [exact (eq_trans P4 (eq_trans E4 (eq_trans R3_4 Htp))) | exact HSAV3].
  + exact P1.
  + exact (eq_trans P9 (eq_trans E9 (eq_trans R3_9 R9))).
  + left. exact (eq_trans P8 (eq_trans E8 (eq_trans R3_8 R8))).
  + exact HREC3.
  + apply (ltf_bud_eq cx S3 _ _ _ _ HBUD3).
    unfold x_rest. rewrite HR0.
    replace (lt_rest (x_pl cx) (x_n cx) 0) with (@nil byte).
    * rewrite ev_from_nil. ring.
    * unfold lt_rest. pose proof HBASE as (_ & _ & _ & _ & _ & _ & _ & Hlen & _).
      rewrite skipn_all2; [reflexivity | lia].
- (* a byte is left: 0x86990 .. 0x86998 compute the next cursor and the next pass *)
  assert (HRnz : lt_r' (x_pl cx) (x_n cx) r <> 0).
  { intros HR0. rewrite branch_eq_U in Hc. apply Z.eqb_neq in Hc. apply Hc.
    rewrite (U_atom E 26 _ EV26 ltac:(lia)), (U_lit E 0 ltac:(lia)). exact HR0. }
  clear Hc.
  paj_run_tok RUN HS HJ3 SHOK ltf_Bspan; try solve [apply awr_ok_nil].
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv := d) in *; clearbody mdv end.
  (* the two registers the latch computed, before the state is seeded again *)
  ltf_reg HS (10%bv : bv 5) Q10. ltf_reg HS (21%bv : bv 5) Q21.
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18.
  prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20. prreg HS (22%bv : bv 5) Q22.
  prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27. ltf_reg HS (11%bv : bv 5) Q11.
  rewrite (ltf_addw1 E 27 m EV27 Hm32) in Q10.
  rewrite (ltf_add_atoms E 19 20 _ _ EV19 EV20 ltac:(lia) ltac:(lia) ltac:(lia)) in Q21.
  lazymatch goal with
  | HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ ?m1) |- _ =>
    assert (KEEPF : forall a, 0 <= a < 2 ^ 64 -> rdW W3 m1 a = rdW W3 mem3 a)
      by (intros a Ha; apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) HFr);
          [ intros b wlo whi a' Hin' Hrr'; vm_compute in Hin'; destruct Hin' | exact Ha | intros Hff; destruct Hff ])
  end.
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end.
  pmkst HS. clear HS SHOK HEI HAE EEo.
  (* 0x86998: the latch, from a fresh seed *)
  lazymatch goal with
  | |- SRr _ _ (mkCfg (mkst ?rB _ ?mB _) _) _ =>
    assert (HKf : ltf_keep B cx O2 (rdW W mem) (rdW W3 mB))
      by (apply (ltf_keep_trans B cx O2 _ (rdW W3 mem3)); [exact HK3 | intros a Ha; exact (KEEPF a (HBND3 a Ha))]);
    destruct (ltf_seed W3 rB mB 1208) as (HS & SHOK & HEI & HAE & EEo);
    remember (ltf_E rB) as E' eqn:HE'
  end.
  clear HE'.
  assert (F2 : ew E' 2 = getr regs3 2) by exact (eq_trans (EEo 2%nat 2%bv eq_refl) (eq_trans Q2 E2)).
  assert (F3 : ew E' 3 = getr regs3 3) by exact (eq_trans (EEo 3%nat 3%bv eq_refl) (eq_trans Q3 E3)).
  assert (F4 : ew E' 4 = getr regs3 4) by exact (eq_trans (EEo 4%nat 4%bv eq_refl) (eq_trans Q4 E4)).
  assert (F8 : ew E' 8 = getr regs3 8) by exact (eq_trans (EEo 8%nat 8%bv eq_refl) (eq_trans Q8 E8)).
  assert (F9 : ew E' 9 = getr regs3 9) by exact (eq_trans (EEo 9%nat 9%bv eq_refl) (eq_trans Q9 E9)).
  assert (F18 : ew E' 18 = getr regs3 18) by exact (eq_trans (EEo 18%nat 18%bv eq_refl) (eq_trans Q18 E18)).
  assert (F22 : ew E' 22 = getr regs3 22) by exact (eq_trans (EEo 22%nat 22%bv eq_refl) (eq_trans Q22 E22)).
  assert (F26 : ew E' 26 = getr regs3 26) by exact (eq_trans (EEo 26%nat 26%bv eq_refl) (eq_trans Q26 E26)).
  assert (F27 : ew E' 27 = Z_to_bv 64 (Z.of_nat m)) by exact (eq_trans (EEo 27%nat 27%bv eq_refl) (eq_trans Q27 EV27)).
  assert (F10 : ew E' 10 = Z_to_bv 64 (Z.of_nat (Datatypes.S m))) by exact (eq_trans (EEo 10%nat 10%bv eq_refl) Q10).
  assert (F21 : ew E' 21 = Z_to_bv 64 (lt_len (x_pl cx) (x_n cx) r + (x_p cx + (x_n cx - r) + SlotSpec.hdr_n r)))
    by exact (eq_trans (EEo 21%nat 21%bv eq_refl) Q21).
  assert (F11 : ew E' 11 = Z_to_bv 64 31) by exact (eq_trans (EEo 11%nat 11%bv eq_refl) Q11).
  unfold ltf_ss in HS, SHOK.
  psrr_branch_tok RUN BR HS SHOK ltf_Bspan.
  + (* the pass is not the last: back to the head of pass m + 1 *)
    assert (Hm31 : (m < 31)%nat).
    { rewrite branch_ltu_U in Hc. apply Z.ltb_lt in Hc.
      rewrite (U_atom E' 27 _ F27 ltac:(lia)), (U_atom E' 11 _ F11 ltac:(lia)) in Hc. lia. }
    paj_run_to_tok RUNTO HS HJ3 SHOK ltf_Bspan 272; try solve [apply awr_ok_nil].
    lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv2 := d) in *; clearbody mdv2 end.
    pmkst HS.
    prreg HS (2%bv : bv 5) N2. prreg HS (3%bv : bv 5) N3. prreg HS (4%bv : bv 5) N4.
    prreg HS (8%bv : bv 5) N8. prreg HS (9%bv : bv 5) N9. prreg HS (10%bv : bv 5) N10.
    prreg HS (18%bv : bv 5) N18. prreg HS (21%bv : bv 5) N21. prreg HS (22%bv : bv 5) N22.
    prreg HS (26%bv : bv 5) N26.
    lazymatch goal with
    | HFr : frame_of _ _ (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
      assert (KEEPL : forall a, 0 <= a < 2 ^ 64 -> rdW W3 m2 a = rdW W3 m1 a)
        by (intros a Ha; apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) HFr);
            [ intros b wlo whi a' Hin' Hrr'; vm_compute in Hin'; destruct Hin' | exact Ha | intros Hff; destruct Hff ])
    end.
    lazymatch goal with
    | |- SRr _ _ (mkCfg (mkst ?rL _ ?mL _) _) _ =>
      assert (HKl : ltf_keep B cx O2 (rdW W mem) (rdW W3 mL))
        by (eapply (ltf_keep_trans B cx O2 _ (rdW W3 _)); [exact HKf | intros a Ha; exact (KEEPL a (HBND3 a Ha))]);
      destruct (ltf_exit_mem cx O2 R2 q2 _ ly S W mem ly3 S3 W3 mL HSLOTS HSAV HREC HPERM3 HKl)
        as (HSLL & HSAVL & HRECL);
      apply (HLH fx cx ly3 S3 W3 rL mL mdv2 (k + 1 + 1 + 1) (acc + mo_free MT + mo_free MT + mo_free MT)
               (lt_r' (x_pl cx) (x_n cx) r) R2 O2 q2)
    end.
    * exact HBASE.
    * exact Hfrm.
    * split.
      { split; [exact HJ3|].
        split; [transitivity (spZ regs); [unfold spZ; f_equal; exact (eq_trans N2 (eq_trans F2 R3_2)) | exact Hsp]|].
        split; [exact (eq_trans N3 (eq_trans F3 (eq_trans R3_3 Hgp)))|].
        split; [exact (eq_trans N4 (eq_trans F4 (eq_trans R3_4 Htp))) | exact HSAVL]. }
      split; [exact HSLL|].
      split; [exact (eq_trans N8 (eq_trans F8 (eq_trans R3_8 R8)))|].
      split; [exact (eq_trans N9 (eq_trans F9 (eq_trans R3_9 R9)))|].
      split; [exact (eq_trans N18 (eq_trans F18 (eq_trans R3_18 R18)))|].
      split; [exact (eq_trans N22 (eq_trans F22 (eq_trans R3_22 R22)))|].
      split; [lia|]. split; [lia | exact Hpblk].
    * lia.
    * etransitivity; [exact N21|]. etransitivity; [exact F21|]. unfold w64, lt_r'. f_equal. ring.
    * exact (eq_trans N26 (eq_trans F26 (eq_trans R3_26 H26))).
    * exact (eq_trans N10 F10).
    * exact HRECL.
    * apply (ltf_bud_eq cx S3 _ _ _ _ HBUD3). rewrite ltf_sub32. unfold x_rest. ring.
  + (* the last pass: 0x8699c falls through to 0x86a0c *)
    assert (Hm31 : m = 31%nat).
    { rewrite branch_ltu_U in Hc. apply Z.ltb_ge in Hc.
      rewrite (U_atom E' 27 _ F27 ltac:(lia)), (U_atom E' 11 _ F11 ltac:(lia)) in Hc. lia. }
    paj_run_tok RUN HS HJ3 SHOK ltf_Bspan; try solve [apply awr_ok_nil].
    lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv2 := d) in *; clearbody mdv2 end.
    pmkst HS.
    rewrite (SIGP CS_rec_clear ltac:(unfold cmd_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
    replace (cmd_af CS_rec_clear) with AF_rec_clear by (vm_compute; reflexivity).
    prreg HS (1%bv : bv 5) M1. prreg HS (2%bv : bv 5) M2. prreg HS (3%bv : bv 5) M3.
    prreg HS (4%bv : bv 5) M4. prreg HS (8%bv : bv 5) M8. prreg HS (9%bv : bv 5) M9.
    lazymatch goal with
    | HFr : frame_of _ _ (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
      assert (KEEPL : forall a, 0 <= a < 2 ^ 64 -> rdW W3 m2 a = rdW W3 m1 a)
        by (intros a Ha; apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) HFr);
            [ intros b wlo whi a' Hin' Hrr'; vm_compute in Hin'; destruct Hin' | exact Ha | intros Hff; destruct Hff ])
    end.
    lazymatch goal with
    | |- SRr _ _ (mkCfg (mkst ?rL _ ?mL _) _) _ =>
      assert (HKl : ltf_keep B cx O2 (rdW W mem) (rdW W3 mL))
        by (eapply (ltf_keep_trans B cx O2 _ (rdW W3 _)); [exact HKf | intros a Ha; exact (KEEPL a (HBND3 a Ha))]);
      destruct (ltf_exit_mem cx O2 R2 q2 _ ly S W mem ly3 S3 W3 mL HSLOTS HSAV HREC HPERM3 HKl)
        as (HSLL & HSAVL & HRECL);
      apply (HZ fx cx ly3 S3 W3 rL mL mdv2 (k + 1 + 1 + 1) (acc + mo_free MT + mo_free MT + mo_free MT) R2 O2 q2)
    end.
    * exact HBASE.
    * exact Hfrm.
    * split; [exact HJ3|].
      split; [transitivity (spZ regs); [unfold spZ; f_equal; exact (eq_trans M2 (eq_trans F2 R3_2)) | exact Hsp]|].
      split; [exact (eq_trans M3 (eq_trans F3 (eq_trans R3_3 Hgp)))|].
      split; [exact (eq_trans M4 (eq_trans F4 (eq_trans R3_4 Htp))) | exact HSAVL].
    * exact M1.
    * exact (eq_trans M9 (eq_trans F9 (eq_trans R3_9 R9))).
    * left. exact (eq_trans M8 (eq_trans F8 (eq_trans R3_8 R8))).
    * exact HRECL.
    * apply (ltf_bud_eq cx S3 _ _ _ _ HBUD3). rewrite Hm31. cbn [Nat.sub].
      rewrite ev_from_O. ring.
Qed.

End e.
End f.
End d.
