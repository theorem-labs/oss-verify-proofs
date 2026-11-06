(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan walk of check_refusal (plugin-hostd/fuzz_command, 0x87f08, 52 instructions), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACbk.v (pb_wcb: entry, branch, return) and A/ACh2.v:122-290 (a program call through cl_callS and back). *)
(* Modified by Theorem Labs, 2026-10: ported from lib/A/Prog/check_refusal.v (the A walk) to fuzz_command.asan-ubsan (image B, check_refusal at 0x88204, 53 instructions; sup_reply_code at 0x8a398): module paths and the B image's addresses. B's code is A's up to pc-relative offsets plus one `unimp` at 0x882b0 after `jal abort`, which no walk reaches; check_refusal has no UBSan trap branch. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YO0b YO0c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdChk CmdRecBase CmdRecImg PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaSB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdAddr PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import sup_reply_code_c check_refusal_c check_refusal_s1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* the code the ASan build computes for a reply lies in the int range: the atoi wrapper truncates to 32 bits *)
Lemma cr_rc_range : forall s, -2^31 <= reply_code_a s < 2^31.
Proof.
intros s. unfold reply_code_a. destruct (list_eq_dec Z.eq_dec _ _); [|lia].
unfold atoi_a, bv_swrap, bv_wrap.
assert (Hm : bv_modulus 32 = 2 ^ 32) by reflexivity. assert (Hh : bv_half_modulus 32 = 2 ^ 31) by reflexivity.
rewrite Hm, Hh.
match goal with |- context [(?z + 2 ^ 31) mod 2 ^ 32] => pose proof (Z.mod_pos_bound (z + 2 ^ 31) (2 ^ 32) ltac:(lia)) end.
lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the callee's statement, never restated, at every FP state (statement pass 4) *)
Hypothesis HSUP_REPLY_CODE : forall fx0 : YK11.FPState, @tsup_reply_code_spec fx0 rc SK PI B MT.
(* the per-binary facts, with the names of a Theorem Labs lane's RULING-STMT.md section 1 *)
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis SIGP : cmd_sig_prog.
(* the record's facts are the lemmas of lib/B/Prog/CmdRecBase.v (cmd_addressable_chk) and CmdRecImg.v
   (cmd_heap_tail_vis, cmd_prog_unowned); the image facts IMG close at assembly by cmd_img_facts_tfib, and the
   read-only range is in the image by its field cif_relro_img *)
Hypothesis IMG : cmd_img_facts SEGS B.
Let RRO : forall a, RLO <= a < RHI -> in_img SEGS a := cif_relro_img SEGS B IMG.
Let errno_low := pal_env B TL.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_cmd) (PI := PI).

(* g_quitting's GOT word is an image byte of the read-only range, outside the runtime-owned statics and the errno
   cell (the record pins both lists, CmdBSyms' ts_owned and ts_errno) *)
Lemma cr_got_unowned : forall a, 0xa6be0 <= a < 0xa6be8 ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros a Ha. split; [apply RRO; unfold CMD_RLO, CMD_RHI; lia|]. split.
- rewrite (ts_owned B HB). intros HE. apply Exists_exists in HE as ([lo n] & Hin & Hz). unfold in_zr in Hz. cbn [fst snd] in Hz.
  assert (HF : forallb (fun r => (fst r + snd r <=? 0xa6be0) || (0xa6be8 <=? fst r)) Tfib_owned_static = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in HF. specialize (HF _ Hin). cbn [fst snd] in HF.
  apply orb_true_iff in HF as [HF|HF]; apply Z.leb_le in HF; lia.
- rewrite (ts_errno B HB). unfold TFIB_ERRNO. lia.
Qed.
Lemma cr_PG_rec : forall a, A_G_REC + 928 <= a < A_G_REC + 952 -> inFP cmd_PG a.
Proof. intros a Ha. exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity | cbn [fst snd]; lia]. Qed.
Lemma cr_PG_quit : forall a, A_G_QUITTING <= a < A_G_QUITTING + 4 -> inFP cmd_PG a.
Proof. intros a Ha. exists (A_G_QUITTING, A_G_QUITTING + 4). split; [right; right; left; reflexivity | cbn [fst snd]; lia]. Qed.

Theorem tcheck_refusal_spec_holds : tcheck_refusal_spec B MT.
Proof.
unfold tcheck_refusal_spec.
intros ly S W regs mem md before reply state quit y HPRE HROD HRO HOBJ H10 Rb Hrep Rrep Hst Rst Hq Rq HyN HyS HREF HEV.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_value as [_ HAC].
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & HQT).
assert (WS : CHECK_REFUSAL_STK = 32 + 12288) by reflexivity.
assert (WS1 : SUP_REPLY_CODE_STK = 12288) by reflexivity.
rewrite WS in Hstk, Hpres.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (proj1 errno_low) as [Herr0 Herr1].
assert (ZCHK : forall ly0 S0 (W0 : world SEGS) mem0 md0, AR SEGS B ly0 S0 W0 mem0 md0 ->
  range_addressable (rdW W0 mem0) SHADOW_OFF A_G_REC 960 /\ range_addressable (rdW W0 mem0) SHADOW_OFF A_G_QUITTING 4).
{ intros ly0 S0 W0 mem0 md0 HAR0. split.
  - exact (cmd_addressable_chk SEGS B LAWS HB ly0 S0 W0 mem0 md0 A_G_REC 960 HAR0 ltac:(vm_compute; reflexivity)).
  - exact (cmd_addressable_chk SEGS B LAWS HB ly0 S0 W0 mem0 md0 A_G_QUITTING 4 HAR0 ltac:(vm_compute; reflexivity)). }
destruct (ZCHK ly S W mem md HAR) as [ZREC ZQ].
destruct (cr_got_of_ro (rdW W mem) HRO) as [G2 G6].
destruct (cr_entry B LAWS TL HOBJ W regs mem ly S md reply state quit HAR Hstk Hpres G2 G6 Hrep Rrep Hst Rst Hq Rq ZREC ZQ)
  as [HS SHOK].
pose proof (ajournal_init_na SEGS B CHECK_REFUSAL_STK [] ly S W regs mem md HPRE) as HJ.
assert (EL : forall n, (n < A_TEXT)%nat -> ew (cr_E regs reply state quit) n = ew (Ereg regs (cr_extra reply state quit)) n)
  by (intros n Hn; unfold cr_E; apply Eimg_low; exact Hn).
assert (HED : ed (cr_E regs reply state quit) = ed (Ereg regs (cr_extra reply state quit))) by reflexivity.
assert (HEI : img_env VAL A_LIM (cr_E regs reply state quit)) by (unfold cr_E; apply Eimg_env).
remember (cr_E regs reply state quit) as E eqn:HE.
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr).
{ intros n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite EL by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (E1 : ew E 1 = getr regs 1) by (apply EEo; reflexivity).
assert (E2 : ew E 2 = getr regs 2) by (apply EEo; reflexivity).
assert (E3 : ew E 3 = getr regs 3) by (apply EEo; reflexivity).
assert (E4 : ew E 4 = getr regs 4) by (apply EEo; reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 before) by (rewrite (EEo 10%nat 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 CR_SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 A_G_QUITTING) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 reply) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 state) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 quit) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (cr_extra reply state quit)) E).
{ split; [intros n Hn; rewrite EL by (unfold A_TEXT; lia); reflexivity | exact HED]. }
clear HE EL HED.
unfold cfg_at, w64.
(* 0x88204 .. 0x88248: the frame, the shadow base, g_rec's address, the check on g_rec.reply (its shadow is 0 by the
   shadow entry, so the check and its error path vanish), s0 := before, a0 := g_rec.reply, then beqz a0 *)
paj_run_tok RUN HS HJ SHOK CRspan.
{ awr_ok_tac. exact Usp. }
lazymatch goal with Hfr : frame_of E _ (mrestrict _ _) (mrestrict _ _) |- _ =>
assert (KEEP0 : cr_kept (rdW W mem) (rdW W (ms_mem ms)) (spZ regs - (32 + 12288)) (spZ regs))
by (intros a Ha Hn; apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => spZ regs - (32 + 12288) <= a < spZ regs) Hfr);
  [ intros b wlo whi a' Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq0 | Hin]; [injection Hq0 as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp in Hrr; lia|]);
    destruct Hin
  | exact Ha | exact Hn ]) end.
clear HF HFr HG. rename ms into ms1.
psrr_branch_tok RUN BR HS SHOK CRspan.
- (* no reply: 0x88290 .. 0x882a4 restore and return *)
  paj_run_tok RUN HS HJ SHOK CRspan.
  { awr_ok_tac. exact Usp. }
  prreg HS (1%bv : bv 5) F1.
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'. unfold apost_base.
  lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly, S, r, m, d end.
  split; [rewrite F1, E1; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
  split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|].
  split; [eapply (aregs_preserved_of_st_ok SEGS _ E _ _ regs (cr_extra reply state quit) HS); [exact HAE | vm_compute; reflexivity]|].
  split; [apply Permutation_refl | split; reflexivity].
- (* a reply: 0x8824c calls sup_reply_code on it *)
  assert (Hrnz : reply <> 0).
  { rewrite branch_eq_U in Hc. apply Z.eqb_neq in Hc. rewrite (U_atom E 34 reply E34 Rrep), U_lit in Hc by lia. exact Hc. }
  clear Hc. destruct y as [x|]; [|exfalso; exact (Hrnz (HyN eq_refl))].
  destruct (HyS x eq_refl) as (_ & HBLK & HSTR).
  pose proof HBLK as (p & k & Hpk & Hpx & Hxk).
  destruct (al_blocks _ _ LAWS ly S W mem md p k HAR Hpk) as (Hp16 & Hp4096 & Hpceil & Hpapp & Hppres & _ & Hkr).
  pose proof (req_size_pos k ltac:(lia)) as [_ Hreq].
  pose proof (cmd_heap_tail_vis SEGS B LAWS HB ly S W mem md p k (reply + Z.of_nat (length x)) HAR Hpk ltac:(lia)) as HTAIL.
  paj_run_tok RUN HS HJ SHOK CRspan.
  { awr_ok_tac. exact Usp. }
  pmkst HS.
  prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (10%bv : bv 5) P10.
  lazymatch goal with Hfr : frame_of E _ (mrestrict _ _) (mrestrict _ _) |- _ =>
  assert (KEEP1 : cr_kept (rdW W mem) (rdW W (ms_mem ms)) (spZ regs - (32 + 12288)) (spZ regs))
  by (intros a Ha Hn; rewrite (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => spZ regs - (32 + 12288) <= a < spZ regs) Hfr);
    [ exact (KEEP0 a Ha Hn)
    | intros b wlo whi a' Hin Hrr; vm_compute in Hin;
      repeat (destruct Hin as [Hq0 | Hin]; [injection Hq0 as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp in Hrr; lia|]);
      destruct Hin
    | exact Ha | exact Hn ]) end.
  assert (HspT : spZ (ms_regs ms) = spZ regs + -32).
  { unfold spZ at 1. rewrite P2, Usp. rewrite unsigned_lit_small by lia. reflexivity. }
  assert (P3' : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite P3, E3; exact Hgp).
  assert (P4' : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite P4, E4; exact Htp).
  assert (P10' : getr (ms_regs ms) 10 = w64 reply) by (rewrite P10, E34; reflexivity).
  assert (HraT : YK0s.ret_ok (getr (ms_regs ms) 1)) by (rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]).
  assert (Hra4T : 4096 <= bv_unsigned (getr (ms_regs ms) 1)) by (rewrite P1, unsigned_lit_small by lia; lia).
  assert (Hlen0 : reply + Z.of_nat (length x) + 1 <= spZ regs - (32 + 12288)) by lia.
  assert (Htail0 : reply + Z.of_nat (length x) - (reply + Z.of_nat (length x)) mod 8 + 8 <= spZ regs - (32 + 12288)).
  { assert (Hxe : 0 <= reply + Z.of_nat (length x) < alloc_ceiling) by lia.
    pose proof (tail_below _ _ Hxe HAC). lia. }
  rewrite (SIGP CS_sup_reply_code ltac:(unfold cmd_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
  replace (cmd_af CS_sup_reply_code) with AF_sup_reply_code by (vm_compute; reflexivity).
  eapply SRr_bind.
  { eapply (cl_callS_na B LAWS W (ms_regs ms) (ms_mem ms) _ CHECK_REFUSAL_STK (spZ regs) [] ly S W mem md [] ly S _ 0
      SUP_REPLY_CODE_STK [] EV_SUP_REPLY_CODE (-32) (getr (ms_regs ms) 1)
      (fun ly2 S2 W2 regs2 mem2 md2 => getr regs2 10 = w64 (reply_code_a x) /\ Permutation (ablocks B ly2 S2) (ablocks B ly S)
         /\ ly2 = ly /\ S2 = S)
      HJ HspT); [reflexivity | lia | rewrite WS1; lia | rewrite WS, WS1; lia | exact P3' | exact P4' | reflexivity
      | exact HraT | exact Hra4T | | ].
    - intros HPRE1. eapply SRr_mono.
      + apply (HSUP_REPLY_CODE fx ly S W (ms_regs ms) (ms_mem ms) _ reply x HPRE1).
        * intros a Hro Ho He.
          assert (Hia : in_img SEGS a) by (destruct Hro as [(s0 & Hs & _ & Hr) | Hr]; [exists s0; split; [exact Hs | exact Hr] | exact (RRO a Hr)]).
          pose proof (pa_img_range a Hia) as Hra0.
          rewrite (KEEP1 a) by lia. exact (HROD a Hro Ho He).
        * exact P10'.
        * exact Rrep.
        * exact HBLK.
        * exact (cr_astr_kept _ _ _ _ reply x KEEP1 HSTR ltac:(lia) Hlen0 ltac:(lia)).
        * intros a Ha. rewrite (KEEP1 a) by lia. exact (HTAIL a Ha).
        * exact (cr_ro_ok_kept _ _ _ _ KEEP1 ltac:(lia) ltac:(lia) HRO).
        * exact HOBJ.
        * exact HEV.
      + cbv beta. unfold apost_base. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & HQ3).
        exists ly3, S3, regs3, mem3, md3. split; [reflexivity|]. split; [exact HJ3|]. split; [exact HP3 | exact HQ3].
    - intros a (r & Hr & _). destruct Hr. }
  cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HJc3 & HP3 & HQa & HPerm3 & Hly3 & HS3e).
  subst ly3 S3.
  pose proof (proj1 HJ3) as HAR3.
  pose proof HJc3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Gimg & _).
  assert (KIMG : forall a, (A_G_REC + 928 <= a < A_G_REC + 952 \/ 0xa6be0 <= a < 0xa6be8 \/ A_G_QUITTING <= a < A_G_QUITTING + 4) ->
    mbyte SEGS (mrestrict (w_H W3) mem3) a = mbyte SEGS (mrestrict (w_H W) (ms_mem ms)) a).
  { intros a Ha.
    assert (HU : in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4))
      by (destruct Ha as [Ha | [Ha | Ha]];
          [exact (cmd_prog_unowned SEGS B LAWS HB IMG a (cr_PG_rec a Ha)) | exact (cr_got_unowned a Ha)
          | exact (cmd_prog_unowned SEGS B LAWS HB IMG a (cr_PG_quit a Ha))]).
    destruct HU as (Hi & Ho & He). apply (mbyte_of_aview SEGS).
    apply Gimg; [exact Hi | exact Ho | exact He | apply fp_spares_closed; [exact sink_closed_nil | intros (r & Hr & _); destruct Hr]]. }
  (* back at 0x88250 *)
  jafter_call_keep_pi HS 40%nat regs3 (mrestrict (w_H W3) mem3) HP3 [0; 1; 2; 3]%nat HS3.
  match type of HS3 with ?t -> _ => assert (HRK : t); [|specialize (HS3 HRK); clear HRK] end.
  { cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | | apply Forall_nil].
    - eapply (region_kept_stack_sub SEGS B); [exact HJc3 | exact HJ3 | exact Usp | lia | rewrite WS; lia | lia | lia | lia |].
      intros a _ (r & Hr & _). destruct Hr.
    - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; intros a Ha; [|lia].
      change 285%nat with (A_OBJ 44) in Ha.
      rewrite (cr_ew_obj HOBJ E 44 0x5e32c0 HEI ltac:(vm_compute; lia) eq_refl ltac:(unfold A_OBJ, A_LIM; lia)) in Ha.
      rewrite unsigned_lit_small in Ha by lia. apply KIMG. unfold A_G_REC. lia.
    - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; intros a Ha; [|lia].
      change 247%nat with (A_OBJ 6) in Ha.
      rewrite (cr_ew_obj HOBJ E 6 0xa6be0 HEI ltac:(vm_compute; lia) eq_refl ltac:(unfold A_OBJ, A_LIM; lia)) in Ha.
      rewrite unsigned_lit_small in Ha by lia. apply KIMG. lia.
    - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; intros a Ha; [|lia].
      rewrite E33 in Ha. rewrite unsigned_lit_small in Ha by (unfold A_G_QUITTING; lia). apply KIMG. lia. }
  clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
  assert (A44 : ew (havoc E 40 (map (getr regs3) CLOB)) 44 = getr regs3 10) by reflexivity.
  remember (havoc E 40 (map (getr regs3) CLOB)) as Ec eqn:HEc.
  assert (HEIc : img_env VAL A_LIM Ec) by (rewrite HEc; apply img_env_havoc; [first [exact HEI0 | exact HEI] | cbv; lia]).
  assert (OLD3 : forall n, (n < 40)%nat -> ew Ec n = ew E n) by (intros n Hn; rewrite HEc; apply YN3v.ew_havoc_old; exact Hn).
  assert (HAE3 : env_agree 32 (Ereg regs (cr_extra reply state quit)) Ec).
  { destruct HAE as [HA1 HA2]. split; [intros n Hn; rewrite OLD3 by lia; exact (HA1 n Hn) | rewrite HEc; exact HA2]. }
  clear HEc.
  assert (Usp3 : bv_unsigned (ew Ec 2) = spZ regs) by (rewrite OLD3 by lia; exact Usp).
  destruct (ZCHK ly S W3 mem3 md3 HAR3) as [ZREC3 ZQ3].
  assert (SHOK3 : sh_ok SEGS CRx cr_SH Ec (mrestrict (w_H W3) mem3)).
  { unfold sh_ok, cr_SH. constructor; [|constructor; [|constructor]].
    - apply (shent_ok_of_range SEGS (w_H W3) mem3 Ec CRx (A_OBJ 44) A_G_REC 960 A_G_REC 0 960 ZREC3).
      + unfold U, CRx. cbn [sv_denot]. rewrite OLD3, E32, Z.add_0_r, Z_to_bv_bv_unsigned by lia. rewrite unsigned_lit_small by (unfold CR_SB; lia). reflexivity.
      + unfold U. cbn [sv_denot]. rewrite (cr_ew_obj HOBJ Ec 44 0x5e32c0 HEIc ltac:(vm_compute; lia) eq_refl ltac:(unfold A_OBJ, A_LIM; lia)).
        rewrite Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small by lia. reflexivity.
      + lia. + lia.
      + intros z Hz. unfold A_G_REC, SHADOW_OFF in *. cbn in Hz. lia.
    - apply (shent_ok_of_range SEGS (w_H W3) mem3 Ec CRx 33 A_G_QUITTING 4 A_G_QUITTING 0 4 ZQ3).
      + unfold U, CRx. cbn [sv_denot]. rewrite OLD3, E32, Z.add_0_r, Z_to_bv_bv_unsigned by lia. rewrite unsigned_lit_small by (unfold CR_SB; lia). reflexivity.
      + unfold U. cbn [sv_denot]. rewrite OLD3, E33, Z.add_0_r, Z_to_bv_bv_unsigned by lia. rewrite unsigned_lit_small by (unfold A_G_QUITTING; lia). reflexivity.
      + lia. + lia.
      + intros z Hz. unfold A_G_QUITTING, SHADOW_OFF in *. cbn in Hz. lia. }
  rewrite P1.
  pose proof (cr_rc_range x) as Rrc.
  (* 0x88250: bgez a0 on the reply's code *)
  psrr_branch_tok RUN BR HS SHOK3 CRspan.
  + (* the code is not negative: 0x88290 .. 0x882a4 restore and return *)
    paj_run_tok RUN HS HJ3 SHOK3 CRspan.
    { awr_ok_tac. exact Usp3. }
    prreg HS (1%bv : bv 5) F1.
    eapply (RET W3 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
    intros mat'. unfold apost_base.
    lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly, S, r, m, d end.
    split; [rewrite F1, OLD3, E1 by lia; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
    split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ3|].
    split; [eapply (aregs_preserved_of_st_ok SEGS _ Ec _ _ regs (cr_extra reply state quit) HS); [exact HAE3 | vm_compute; reflexivity]|].
    split; [exact HPerm3 | split; reflexivity].
  + (* the code is negative: the message was refused, so state = before and quit = 0 (the caller's premise) *)
    assert (Hneg : reply_code_a x < 0).
    { rewrite YO0c.branch_ge in Hc. apply negb_false_iff in Hc. apply Z.ltb_lt in Hc.
      cbn [sv_denot] in Hc. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, A44, HQa in Hc. unfold w64 in Hc.
      rewrite !YO0c.lit64_unsigned in Hc. unfold YO0b.s64 in Hc.
      destruct (Z_lt_le_dec (reply_code_a x) 0) as [Hl|Hl]; [exact Hl|exfalso].
      rewrite (Z.mod_small (reply_code_a x)) in Hc by lia. rewrite Z.mod_0_l in Hc by lia.
      destruct (Z.ltb_spec (reply_code_a x) (2 ^ 63)); destruct (Z.ltb_spec 0 (2 ^ 63)); lia. }
    clear Hc. destruct (HREF x eq_refl Hneg) as [Hsb Hq0].
    (* 0x88254 .. 0x8826c: the check on g_rec.state vanishes (shadow entry); a0 := state, then bne a0, s0 *)
    paj_run_tok RUN HS HJ3 SHOK3 CRspan.
    { awr_ok_tac. exact Usp3. }
    psrr_branch_tok RUN BR HS SHOK3 CRspan.
    * (* state <> before: the abort edge; refuted by the caller's premise *)
      exfalso. rewrite branch_ne_U in Hc. apply negb_true_iff in Hc. apply Z.eqb_neq in Hc. apply Hc.
      rewrite (U_atom _ 35 state ltac:(cbn [ew ewset Nat.eqb]; rewrite OLD3 by lia; exact E35) Rst).
      rewrite (U_atom _ 10 before ltac:(cbn [ew ewset Nat.eqb]; rewrite OLD3 by lia; exact E10) Rb). exact Hsb.
    * (* 0x88270 .. 0x8828c: g_quitting through its GOT word; its check passes through the slow block 0x882b4 .. 0x882bc
         (the shadow entry covers its 4 bytes); a0 := quit, then bnez a0 *)
      clear Hc. paj_run_tok RUN HS HJ3 SHOK3 CRspan.
      { awr_ok_tac. exact Usp3. }
      psrr_branch_tok RUN BR HS SHOK3 CRspan.
      -- (* quit <> 0: the abort edge; refuted by the caller's premise *)
         exfalso. rewrite branch_ne_U in Hc. apply negb_true_iff in Hc. apply Z.eqb_neq in Hc. apply Hc.
         lazymatch goal with |- U ?E4 _ = _ =>
           assert (Hz : ew E4 36 = Z_to_bv 64 0) by (cbn [ew ewset Nat.eqb]; rewrite OLD3 by lia; rewrite E36, Hq0; reflexivity) end.
         unfold U. cbn [sv_denot]. rewrite Hz. vm_compute. reflexivity.
      -- (* 0x88290 .. 0x882a4 restore and return *)
         paj_run_tok RUN HS HJ3 SHOK3 CRspan.
         { awr_ok_tac. exact Usp3. }
         prreg HS (1%bv : bv 5) F1.
         lazymatch type of HS with st_ok_pi _ _ ?E4 _ _ =>
           assert (HAE4 : env_agree 32 (Ereg regs (cr_extra reply state quit)) E4) end.
         { destruct HAE3 as [HA1 HA2]. split.
           - intros n Hn. cbn [ew ewset].
             repeat match goal with |- context [Nat.eqb ?a ?b] => destruct (Nat.eqb_spec a b); [lia|] end.
             exact (HA1 n Hn).
           - cbn [ed ewset]. exact HA2. }
         eapply (RET W3 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
         intros mat'. unfold apost_base.
         lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly, S, r, m, d end.
         split; [rewrite F1; cbn [ew ewset Nat.eqb]; rewrite OLD3, E1 by lia; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
         split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ3|].
         split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs (cr_extra reply state quit) HS); [exact HAE4 | vm_compute; reflexivity]|].
         split; [exact HPerm3 | split; reflexivity].
Qed.
End e.
End f.
End d.
