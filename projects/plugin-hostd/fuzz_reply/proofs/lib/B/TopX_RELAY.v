(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-31 (a Theorem Labs lane, for a Theorem Labs lane's B W1 rows and a Theorem Labs lane's ReplyBTop): two callee
   contracts of image B's top_x at its W1 relation, the ReplyBTop rows
     RSRC_x : relay_source (0x85d28) at fr_B0 + AF_fr_relay_source  (W_LLVMFuzzerTestOneInput_top_x.v Hypothesis RSRC_x)
     RRDS_x : relay_reads  (0x864e8) at fr_B0 + AF_fr_relay_reads   (the drain arm's RRDS_x, the same shape)
   PROVED at top_x's relation ARX (W_LLVMFuzzerTestOneInput_top_x.v:177-179: ARcf /\ Hp = [] /\ arodata_ok_cf, restated
   here verbatim as ARX_rl so that this file does not build top_x; k3's `exact` at top_x's ARX is by unfolding).
   Image A has no twin: A inlines relay_source and relay_reads (W_relay_src_c.v header).  The proofs are the GENERIC
   walks of lib/B/W_relay_src_c.v (a Theorem Labs lane, a working branch 44e1c0f0315):
   pb_relay_source_x_fr / pb_relay_reads_x_fr, over any ARx with AR_laws_x, Hp = [] in every ARx state and (for
   relay_reads) asyms_ok B in every ARx state, at B's pin from TfibB's two shadow cells.  At ARX_rl: the laws are
   top_x's ARX_laws proof (copied below), Hp = [] its second conjunct, asyms_ok ARcf's amc_syms.  The W1 conjunct needs
   no lift: it is part of the relation the generic walks carry (AR_laws_x's frame law keeps it, ReplyKeptAroB).
   rule 24: proves no function (kind: instance of proved generic walks). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_kit_x W_journal_x W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YD2l YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import CfImgB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG0ncf YGcallcf YG0lawscf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyKeptAroB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_relay_src_c.
Import ListNotations.
Open Scope Z_scope.

Module RSC := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.W_relay_src_c.

Section topx_relay. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Existing Instance tfib_sink_head.

(* W_LLVMFuzzerTestOneInput_top_x.v:177-179, verbatim *)
Definition ARX_rl : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop :=
  fun ly S Hp W mem md => ARcf (ci := CfImg_B) (cp := CfParams_reply) segs TfibB ly S Hp W mem md /\ Hp = [] /\
    @YG0dcf.arodata_ok_cf CfImg_B segs TfibB mem.

(* W_LLVMFuzzerTestOneInput_top_x.v:180-191's ARX_laws, at ARX_rl *)
Lemma ARX_rl_laws : AR_laws_x segs TfibB ARX_rl (@cf_head CfParams_reply).
Proof.
  apply (AR_laws_x_iff segs TfibB (fun ly S Hp W mem md =>
           (ARcf (ci := CfImg_B) (cp := CfParams_reply) segs TfibB ly S Hp W mem md /\ Hp = []) /\
           @YG0dcf.arodata_ok_cf CfImg_B segs TfibB mem)).
  { intros ly S Hp W mem md. unfold ARX_rl. split.
    - intros ((H1 & H2) & H3). exact (conj H1 (conj H2 H3)).
    - intros (H1 & H2 & H3). exact (conj (conj H1 H2) H3). }
  apply (AR_laws_x_and_mem segs TfibB _ (@YG0dcf.arodata_ok_cf CfImg_B segs TfibB) ReplyKeptAroB.arodata_kept_B).
  apply AR_laws_x_and_hp.
  exact (AR_laws_x_cf (cp := CfParams_reply) segs TfibB (AR_laws_ok_cf (cp := CfParams_reply) segs TfibB)).
Qed.

Lemma ARX_rl_hp0 : forall ly S Hp (W : world segs) mem md, ARX_rl ly S Hp W mem md -> Hp = [].
Proof. intros ly S Hp W mem md H. exact (proj1 (proj2 H)). Qed.

Lemma ARX_rl_syms : forall ly S Hp (W : world segs) mem md, ARX_rl ly S Hp W mem md -> asyms_ok TfibB.
Proof. intros ly S Hp W mem md H. exact (amc_syms _ _ _ _ _ (proj1 (proj1 H))). Qed.

Lemma TfibB_got_shadow : as_got_shadow TfibB = 0x9df50. Proof. vm_compute. reflexivity. Qed.
Lemma TfibB_shadow_cell : as_shadow_cell TfibB = 0xa6638. Proof. vm_compute. reflexivity. Qed.

(* RSRC_x (top_x's Hypothesis RSRC_x; ReplyBTop.v:102) *)
Theorem topx_RSRC_x : forall W ly S Hp (regs : bvmap 5 word) mem md ch T es fd,
  afn_pre_x segs TfibB ARX_rl RSRC_STK ly S Hp W regs mem md ch ->
  getr regs 10 = w64 fd -> 0 <= fd < 2 ^ 32 ->
  arelay_at TfibB fr_RG ly S W mem T es -> rom_view segs W mem ->
  SRr segs W (cfg_at segs (fr_B0 + AF_fr_relay_source) regs mem md)
    (aleafx_post_x TfibB [] ARX_rl RSRC_STK regs ly S Hp W mem md
      (fun a0 =>
         (exists j e, nth_error es j = Some e /\ re_fd e = fd /\
            (forall i e', (i < j)%nat -> nth_error es i = Some e' -> re_fd e' <> fd) /\
            a0 = w64 (T + AENT * Z.of_nat j)) \/
         ((forall e, In e es -> re_fd e <> fd) /\ a0 = w64 0))).
Proof.
  exact (RSC.pb_relay_source_x_fr TfibB [] ARX_rl (@cf_head CfParams_reply) ARX_rl_laws ARX_rl_hp0
           TfibB_got_shadow TfibB_shadow_cell).
Qed.

(* RRDS_x (ReplyBTop.v:108) *)
Theorem topx_RRDS_x : forall W ly S Hp (regs : bvmap 5 word) mem md ch T es HA h,
  afn_pre_x segs TfibB ARX_rl RRDS_STK ly S Hp W regs mem md ch ->
  getr regs 10 = w64 HA -> 0 < HA -> HA mod 8 = 0 -> azs TfibB HA 4 ->
  asrc_at TfibB ly S W mem HA h ->
  arelay_at TfibB fr_RG ly S W mem T es -> rom_view segs W mem ->
  SRr segs W (cfg_at segs (fr_B0 + AF_fr_relay_reads) regs mem md)
    (aleafx_post_x TfibB [] ARX_rl RRDS_STK regs ly S Hp W mem md
      (fun a0 =>
         (exists j e, nth_error es j = Some e /\ re_fd e = hs_fd h /\
            (forall i e', (i < j)%nat -> nth_error es i = Some e' -> re_fd e' <> hs_fd h) /\
            a0 = w64 (if re_eof e =? 0 then 1 else 0)) \/
         ((forall e, In e es -> re_fd e <> hs_fd h) /\ a0 = w64 0))).
Proof.
  exact (RSC.pb_relay_reads_x_fr TfibB [] ARX_rl (@cf_head CfParams_reply) ARX_rl_laws ARX_rl_hp0 ARX_rl_syms
           TfibB_got_shadow TfibB_shadow_cell).
Qed.

End topx_relay.

(* ReplyBTop's forms: the RunCeil first, then the FPState *)
Theorem topx_RSRC_x_all : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  forall W ly S Hp (regs : bvmap 5 word) mem md ch T es fd,
  afn_pre_x (@pa_segs rc fr_prog_listing (@PB_fr rc)) TfibB (@ARX_rl rc) RSRC_STK ly S Hp W regs mem md ch ->
  getr regs 10 = w64 fd -> 0 <= fd < 2 ^ 32 ->
  arelay_at (PI := @PB_fr rc) TfibB fr_RG ly S W mem T es -> rom_view (@pa_segs rc fr_prog_listing (@PB_fr rc)) W mem ->
  SRr (@pa_segs rc fr_prog_listing (@PB_fr rc)) W
    (@cfg_at fx (@pa_segs rc fr_prog_listing (@PB_fr rc)) (fr_B0 + AF_fr_relay_source) regs mem md)
    (@aleafx_post_x fx rc tfib_sink_head (@PB_fr rc) TfibB [] (@ARX_rl rc) RSRC_STK regs ly S Hp W mem md
      (fun a0 =>
         (exists j e, nth_error es j = Some e /\ re_fd e = fd /\
            (forall i e', (i < j)%nat -> nth_error es i = Some e' -> re_fd e' <> fd) /\
            a0 = w64 (T + AENT * Z.of_nat j)) \/
         ((forall e, In e es -> re_fd e <> fd) /\ a0 = w64 0))).
Proof. intros rc fx. exact (@topx_RSRC_x fx rc). Qed.

Theorem topx_RRDS_x_all : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  forall W ly S Hp (regs : bvmap 5 word) mem md ch T es HA h,
  afn_pre_x (@pa_segs rc fr_prog_listing (@PB_fr rc)) TfibB (@ARX_rl rc) RRDS_STK ly S Hp W regs mem md ch ->
  getr regs 10 = w64 HA -> 0 < HA -> HA mod 8 = 0 -> azs TfibB HA 4 ->
  asrc_at (PI := @PB_fr rc) TfibB ly S W mem HA h ->
  arelay_at (PI := @PB_fr rc) TfibB fr_RG ly S W mem T es -> rom_view (@pa_segs rc fr_prog_listing (@PB_fr rc)) W mem ->
  SRr (@pa_segs rc fr_prog_listing (@PB_fr rc)) W
    (@cfg_at fx (@pa_segs rc fr_prog_listing (@PB_fr rc)) (fr_B0 + AF_fr_relay_reads) regs mem md)
    (@aleafx_post_x fx rc tfib_sink_head (@PB_fr rc) TfibB [] (@ARX_rl rc) RRDS_STK regs ly S Hp W mem md
      (fun a0 =>
         (exists j e, nth_error es j = Some e /\ re_fd e = hs_fd h /\
            (forall i e', (i < j)%nat -> nth_error es i = Some e' -> re_fd e' <> hs_fd h) /\
            a0 = w64 (if re_eof e =? 0 then 1 else 0)) \/
         ((forall e, In e es -> re_fd e <> hs_fd h) /\ a0 = w64 0))).
Proof. intros rc fx. exact (@topx_RRDS_x fx rc). Qed.
