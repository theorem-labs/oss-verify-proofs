(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC85.v for libreac/fuzz_boxreg's program walk (as fuzz_identity's lib/A/Prog/YC85.v, ea5560a967b, carries it): the listing's names are bsym; module paths changed. No image numeral occurs in this file. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/Prog/YC85.v, with its module paths and module names changed; 313 of its 404 lines of code are new or changed and 320 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputFree.v, with its module paths and module names changed; 306 of its 362 lines of code are new or changed and 348 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A: the premises of text_of's contract (lib/A/Prog/text_of_c.v,
   `text_of_acontract`, link_amem.v's aleaf_alloc_rd at TEXT_OF_AK = 16448, EV 1, SIDE []) at the body's three
   text_of sites, built from what the walk's interface carries (lib/A/Prog/LLVMFuzzerTestOneInputDefs.v). The sites
   (listing (internal path) (internal record, sha256 e84d6f0c6974)):
     0x82e24 (+0x650, op_decide)  a0 = s1 + 0x118 (the cursor), a1 = s1 + 0x130
     0x82e34 (+0x660, op_decide)  a0 = s1 + 0x118,              a1 = s1 + 0x128
     0x837d8 (+0x1004, op_write)  a0 = s1 + 0x118,              a1 = s1 + 0x130
   with sp = s1 (the realigned stack pointer, lf_sp1) and s0 = the entry sp.

   lf_text_of_pre gives, at such a call, the three things the contract asks beside the allocator-side premises (the
   live-byte room, the meter, the chain and its context, LedPre, which the arm states from lf_jbk / lf_base and
   lib/A/Prog/LLVMFuzzerTestOneInputFree.v lf_site_chain):
   - apre: the journal, gx_ok, arodata_okP, the return, gp / tp, the window [sp - 16448, sp) inside the journal's
     window (sp >= sp0 - 432, LLVMF_STK = 32768), the event room from lf_base's EV_LIB, the write set's bytes (the
     cursor and the slot) in the journal's own window and off the read-only set;
   - the read set's `akb`: the input bytes [c0, c0 + c1) left at the cursor lie in the payload block, a block of
     every state of the call (lib/A/Prog/LLVMFuzzerTestOneInputKpre.v lf_input_block);
   - text_of_apre: the cursor and the slot in the real frame (zero shadow: the stack row), the payload's bytes,
     shadow, band and placement (a heap block below alloc_ceiling), the unwinder's words under the slot (a cursor
     word: a heap pointer or a count below 2 ^ 26, both below the slot), and the texts table: its shadow and its
     eleven entries by computation over the pin (Kpre.v kp_img_b), each with the W3 clause below.

   Named Section hypotheses:
   - TXO_RO: text_of_ro of each texts entry, its string and NUL (|s| + 1 bytes, text_of_c.v since W3's fix
     3d6bbe064f03): true of the image, the instance discharges it by computation.
   - TXO_TR: text_of_traces B, the malloc trace's wild prefix in the universe (lib/A/ACejUniv.v Tfib_univ_wild at
     the instance).
   - LAWS, TB, HSEGS: the image instance (AR_laws, PcapSyms B, pa_segs = tfibsegs), as Kpre.v takes them.

   Proves no function (kind: segment lemma of LLVMFuzzerTestOneInput's walk). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YI00 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 YO09 YGwildCount YImgTop.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AMemFile AMemFileSink LinkWildRoom.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalk LinkWalkSide BoxBase.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkEntry LinkEntryA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import text_of_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputKpre.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputFree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* every texts string is shorter than 320 bytes *)
Lemma txo_texts_short :
  forallb (fun i => Nat.ltb (length (snd (nth i KP_TEXTS (0, [])))) 320) (seq 0 11) = true.
Proof. vm_compute. reflexivity. Qed.

(* a present byte reads as itself *)
Lemma txo_mbyte_present : forall segs H (mem : word -> option byte) a,
  apresent H mem a -> exists b, mbyte segs (mrestrict H mem) a = Some b.
Proof.
  intros segs H mem a (Hh & b & Hb). exists b. unfold mbyte, mrestrict. rewrite Hh, Hb. reflexivity.
Qed.

Lemma txo_aview_present : forall segs H (mem : word -> option byte) a, apresent H mem a -> aview segs H mem a <> None.
Proof.
  intros segs H mem a Hp. destruct (txo_mbyte_present segs H mem a Hp) as (b & Hb).
  unfold aview. rewrite Hb. cbn. discriminate.
Qed.

(* n present bytes from a, as an abuf *)
Lemma txo_abuf_present : forall segs H (mem : word -> option byte) a n,
  0 <= a -> a + n <= 2 ^ 64 -> 0 <= n -> (forall i, 0 <= i < n -> apresent H mem (a + i)) ->
  abuf segs (mrestrict H mem) a n.
Proof.
  intros segs H mem a n H0 H1 Hn Hp. exists (abytes_of segs (mrestrict H mem) a (Z.to_nat n)).
  split; [rewrite abytes_of_length; lia|]. split.
  - apply abytes_of_abytes; [lia | lia |]. intros i Hi.
    exact (txo_mbyte_present segs H mem (a + Z.of_nat i) (Hp (Z.of_nat i) ltac:(lia))).
  - intros i Hi. rewrite abytes_of_length in Hi. apply (apresent_writable segs). apply Hp. lia.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.

Section b.
Context {PI : PAImg link_listing}.
#[local] Abbreviation SEGS := (pa_segs).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variable MS : amemfile_syms.
Variable la_nul : Z.
Variable LF_CTX : list (list Z).
Variables LF_MO_SET LF_MO_OP LF_MO_END : Z.

Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : pa_segs = tfibsegs.
(* text_of_c.v's table clause at each texts entry: the string and its NUL are read-only image bytes *)
Hypothesis TXO_RO : forall i, (i < 11)%nat ->
  text_of_ro SEGS PCAP_RLO PCAP_RHI B (fst (nth i KP_TEXTS (0, [])))
    (Z.of_nat (length (snd (nth i KP_TEXTS (0, [])))) + 1).
Hypothesis TXO_TR : text_of_traces B.
(* the meter is trivial at the instance (MT_OK, `fun _ _ => I` at YCbp.ameter_triv) *)
Hypothesis MT_OK : forall S m, mo_ok MT S m.
(* text_of's contract at the running FP state (the text_of walk) *)
Hypothesis TXO_C : forall fy : YK11.FPState, text_of_acontract (fx := fy) SK SEGS PCAP_RLO PCAP_RHI B MT LF_CTX.

#[local] Notation BASEF cx := (lf_base SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx).
#[local] Notation JRN cx fp ly S W mem mdl k :=
  (ajournal_gx SEGS B G_HARNESS 0 [] LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx))
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(LF_CID, fp)] ly S W mem mdl k).

(* The real-stack row's shadow is zero at every AR state (YG0n.v zero_shadow_ranges, first row), so the shadow
   hull of a stack range is visible: text_of asks it of *own (help bb9e0a6c020c: its check +0x264 runs after the
   malloc at +0x22c). *)
Lemma txo_stack_hull : forall ly S rd p n, ARm B ly S rd -> ly_stk_lo ly <= p -> 0 < n -> p + n <= ly_stk_hi ly ->
  shadow_hull_vis rd p n.
Proof.
  intros ly S rd p n M Hlo Hn Hhi s Hs.
  pose proof (proj1 (Forall_forall _ _) (am_zshadow B ly S _ M) (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly)
    ltac:(unfold zero_shadow_ranges; left; reflexivity)) as HZ.
  cbn [fst snd] in HZ. unfold zero_shadow, shadow_of_addr in HZ.
  pose proof (am_layout B ly S _ M) as LO. destruct (lo_top _ LO) as (_ & _ & _ & _ & Pl & Ph & _).
  unfold page_aligned in Pl, Ph.
  unfold shadow_addr in Hs.
  replace s with (SHADOW_OFF + ly_stk_lo ly / 8 + (s - SHADOW_OFF - ly_stk_lo ly / 8)) by lia.
  rewrite HZ; [discriminate|].
  clear HZ. unfold SHADOW_OFF in *. Z.div_mod_to_equations. lia.
Qed.

(* a range of the real stack below 2^47 is application memory (high memory): text_of asks it of the cursor and
   of *own (help bb9e0a6c020c, amem_range for each instrumented check's shadow entry) *)
Lemma txo_stack_amem : forall ly S rd p n, ARm B ly S rd -> ly_stk_lo ly <= p -> p + n <= kHighMemEnd - 1 ->
  amem_range p n.
Proof.
  intros ly S rd p n M Hlo Hhi.
  pose proof (am_layout B ly S _ M) as LO. pose proof (lo_top _ LO) as (Lbot & Ltop & _ & Lhi & Lplo & Lphi & Lbeg).
  right. unfold kHighMemBeg, kHighMemEnd in *. lia.
Qed.

Lemma lf_text_of_pre : forall cx fp ly S (W : world SEGS) mem mdl k (regs : bvmap 5 word) P N o,
  BASEF cx -> JRN cx fp ly S W mem mdl k ->
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W) mem) ->
  abytes SEGS (rdW W mem) (c_p cx) (c_pl cx) ->
  rdword (aview SEGS (w_H W) mem) (lf_sp1 cx + LS_P) = Some P ->
  rdword (aview SEGS (w_H W) mem) (lf_sp1 cx + LS_N) = Some N ->
  (exists q, 0 <= q <= c_n cx /\ P = c_p cx + q /\ N = c_n cx - q) ->
  (o = LS_T128 \/ o = LS_T130) ->
  spZ regs = lf_sp1 cx -> aarg regs 0 = lf_sp1 cx + LS_P -> aarg regs 1 = lf_sp1 cx + o ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  k + 1 <= EV_LIB ->
  apre SK SEGS PCAP_RLO PCAP_RHI B TEXT_OF_AK 1 [] (text_of_awr regs (rdW W mem)) G_HARNESS 0 [] LLVMF_STK
    (spZ (c_regs cx)) (amf_harness_fp (c_T cx)) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(LF_CID, fp)]
    ly S W mem mdl k regs /\
  (forall a, text_of_ard SEGS regs (rdW W mem) a -> akb SEGS B ly S (spZ regs - TEXT_OF_AK) (spZ regs) a) /\
  text_of_apre SEGS PCAP_RLO PCAP_RHI B regs (rdW W mem).
Proof.
  intros cx fp ly S W mem mdl k regs P N o HB HJ HRO Hpl HP HN (q & Hq & EP & EN) Ho Hsp Ha0 Ha1 Hgp Htp Hret Hra4 Hk.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly S W mem mdl k
    HB HJ) as (H16 & Hceil & Hslo & Hshi & H47 & Hwin & HAR).
  pose proof HAR as (M & _).
  pose proof HB as (HPRE & _ & HGX & _).
  pose proof HPRE as (_ & _ & _ & _ & Hpn & Hlen & _ & _ & Hnev & _).
  set (sp0 := spZ (c_regs cx)) in *.
  assert (Hs1 : sp0 - 416 - 16 <= lf_sp1 cx <= sp0 - 416 /\ lf_sp1 cx mod 32 = 0).
  { unfold lf_sp1. pose proof (lf_sp1_range sp0 ltac:(unfold LF_MFRAME, LLVMF_STK in *; lia) H16) as (R & R32 & _).
    unfold LF_MFRAME in R. split; [exact R | exact R32]. }
  destruct Hs1 as (Hs1 & Hs32).
  assert (HK : TEXT_OF_AK = 16448) by reflexivity.
  assert (HEV : EV_LIB = 196) by reflexivity.
  pose proof (kp_rdword_range _ _ _ (kp_aview_range SEGS (w_H W) mem) HP) as RP.
  pose proof (kp_rdword_range _ _ _ (kp_aview_range SEGS (w_H W) mem) HN) as RN.
  pose proof (val_mem_of_rdword SEGS (w_H W) mem _ _ HP) as VP.
  pose proof (val_mem_of_rdword SEGS (w_H W) mem _ _ HN) as VN.
  assert (Hos : lf_sp1 cx + LS_P + 16 <= lf_sp1 cx + o /\ o + 8 <= 0x138) by (unfold LS_P, LS_T128, LS_T130 in *; lia).
  unfold LS_P, LS_N, LS_T128, LS_T130, LLVMF_STK in *.
  (* the payload: where it is *)
  assert (Hpay : 0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly S) /\ c_p cx + c_n cx <= alloc_ceiling /\
                 c_n cx = req_size (c_n cx)).
  { intros Hnp.
    pose proof (lf_input_block SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS
      cx fp ly S W mem mdl k HB HJ Hnp) as Hin.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & Hb4096 & Hbceil & _).
    assert (Rn : req_size (c_n cx) = c_n cx) by (unfold req_size; destruct (c_n cx =? 0) eqn:E; [lia | reflexivity]).
    rewrite Rn in Hbceil. split; [exact Hin|]. split; [exact Hbceil | symmetry; exact Rn]. }
  assert (HPlow : P + N <= alloc_ceiling /\ 0 <= P).
  { destruct (Z.eq_dec (c_n cx) 0) as [Hn0 | Hn0].
    - destruct Hpn as [(_ & Hpe) | (Hnp & _)]; [|lia]. subst P N. rewrite Hpe. unfold A_EMPTY. lia.
    - destruct (Hpay ltac:(unfold c_n in *; lia)) as (_ & Hb & _). subst P N. lia. }
  split; [|split].
  (* ---- apre ---- *)
  - unfold apre. split; [exact HJ|]. split; [exact HGX|]. split; [exact HRO|]. split; [exact Hret|].
    split; [exact Hra4|]. split; [exact Hgp|]. split; [exact Htp|].
    split; [rewrite Hsp; rewrite <- (Z.mod_mod (lf_sp1 cx) 16) by lia;
            replace (lf_sp1 cx mod 16) with ((lf_sp1 cx mod 32) mod 16)
              by (rewrite Zmod_mod_mod_div_mul by lia; reflexivity) || (pose proof (Z.div_mod (lf_sp1 cx) 32); lia);
            rewrite Hs32; reflexivity|].
    split; [rewrite Hsp; lia|]. split; [rewrite Hsp; lia|].
    split; [lia|]. split; [apply Forall_nil|].
    split.
    + intros a (r & Hr & Hra). unfold text_of_awr in Hr.
      destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Hra; rewrite ?Ha0, ?Ha1 in Hra; unfold ajw;
        left; (split; [unfold awr_byte; left; lia | lia]).
    + intros a (r & Hr & Hra) Hro. unfold text_of_awr in Hr.
      assert (Ha : sp0 - 32768 <= a < sp0) by (destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Hra;
                                               rewrite ?Ha0, ?Ha1 in Hra; lia).
      destruct Hro as [(sg & Hin & _ & Hsg) | Hrw].
      * assert (Hi : in_img SEGS a) by (exists sg; split; [exact Hin | exact Hsg]).
        pose proof (pa_segs_low a Hi). unfold kLowMemEnd in *. lia.
      * unfold PCAP_RLO, PCAP_RHI in Hrw. lia.
  (* ---- the read set ---- *)
  - intros a (c0 & c1 & H0 & H1 & R0 & R1 & Ha).
    rewrite Ha0 in H0, H1.
    replace (lf_sp1 cx + 280 + 8) with (lf_sp1 cx + 288) in H1 by lia.
    pose proof (kp_vm8_mod _ _ _ _ _ H0 VP) as E0. pose proof (kp_vm8_mod _ _ _ _ _ H1 VN) as E1.
    rewrite !Z.mod_small in E0 by lia. rewrite !Z.mod_small in E1 by lia. subst c0 c1.
    unfold rd_ivl in Ha. right; left.
    destruct (Hpay ltac:(unfold c_n in *; lia)) as (Hin & _ & Rn).
    exists (c_p cx), (c_n cx). split; [exact Hin | lia].
  (* ---- text_of_apre ---- *)
  - exists P, N, (skipn (Z.to_nat q) (c_pl cx)).
    rewrite Ha0, Ha1.
    replace (lf_sp1 cx + 280 + 8) with (lf_sp1 cx + 288) by lia.
    split; [exact VP|]. split; [exact VN|]. split; [exact RP|]. split; [exact RN|].
    split; [apply txo_abuf_present; [lia | lia | lia | intros i Hi; apply Hwin; lia]|].
    split; [rewrite Z.add_mod by lia; rewrite <- (Z.mod_mod (lf_sp1 cx) 8) by lia;
            replace (lf_sp1 cx mod 8) with ((lf_sp1 cx mod 32) mod 8)
              by (rewrite Zmod_mod_mod_div_mul by lia; reflexivity) || (pose proof (Z.div_mod (lf_sp1 cx) 32); lia);
            rewrite Hs32; reflexivity|].
    split; [rewrite ard_aview; apply (kp_stack_ra B ly S _ _ _ M); lia|].
    split; [apply (txo_stack_amem ly S _ _ _ M); unfold kHighMemEnd in *; lia|].
    split; [unfold apart_frame; right; lia|].
    split; [apply txo_abuf_present; [lia | lia | lia | intros i Hi; apply Hwin; lia]|].
    split; [rewrite ard_aview; apply (kp_stack_ra B ly S _ _ _ M); lia|].
    split; [apply (txo_stack_amem ly S _ _ _ M); unfold kHighMemEnd in *; lia|].
    split; [rewrite ard_aview; apply (txo_stack_hull ly S _ _ _ M); lia|].
    split; [unfold apart_frame; right; lia|].
    split; [unfold apart; right; lia|].
    split; [unfold apart; rewrite (ts_errno B TB); unfold TFIB_ERRNO; left; lia|].
    split.
    { destruct Hpl as (Hp0 & Hpe & Hpb).
      split; [lia|]. rewrite length_skipn. split; [unfold c_n in *; lia|].
      intros i Hi. try rewrite length_skipn in Hi. rewrite lw_nth_error_skipn.
      replace (P + Z.of_nat i) with (c_p cx + Z.of_nat (Z.to_nat q + i)) by lia.
      apply Hpb. unfold c_n in *. lia. }
    split; [rewrite length_skipn; unfold c_n in *; lia|].
    split.
    { rewrite ard_aview. destruct (Z.eq_dec (c_n cx) 0) as [Hn0 | Hn0].
      - intros x Hx. lia.
      - destruct (Hpay ltac:(unfold c_n in *; lia)) as (Hin & _ & Rn).
        eapply range_addressable_of_block; [eassumption | eassumption | exact Hin | lia | lia]. }
    split.
    { intros HNp. destruct (Hpay ltac:(lia)) as (Hin & Hbc & Rn).
      split; [rewrite ard_aview; eapply shadow_hull_vis_of_block; [eassumption | eassumption | exact Hin | lia | lia | lia]|].
      split; [eapply amem_range_of_block; [eassumption | eassumption | exact Hin | lia | lia]|].
      split; [unfold apart_frame; left; lia|].
      split; [unfold apart; left; lia|]. split; [unfold apart; left; lia|]. lia. }
    split; [intros i Hi; rewrite ard_aview; apply txo_aview_present; apply Hwin; lia|].
    split.
    { intros w Hw Rw.
      destruct Ho as [-> | ->].
      - replace (lf_sp1 cx + 296 - 16) with (lf_sp1 cx + 280) in Hw by lia.
        pose proof (kp_vm8_mod _ _ _ _ _ Hw VP) as Ew. rewrite !Z.mod_small in Ew by lia. lia.
      - replace (lf_sp1 cx + 304 - 16) with (lf_sp1 cx + 288) in Hw by lia.
        pose proof (kp_vm8_mod _ _ _ _ _ Hw VN) as Ew. rewrite !Z.mod_small in Ew by lia.
        destruct HPRE as (_ & _ & _ & _ & Hpn' & _). subst N.
        destruct Hpn' as [(Hn0 & _) | (Hn26 & _)]; unfold c_n in *; lia. }
    pose proof (kp_img_here B TB HSEGS) as KI. unfold kp_img_b in KI.
    repeat match type of KI with (_ && _)%bool = true => apply andb_prop in KI as [KI ?] end.
    match goal with H : kp_ra_b LA_TEXTS _ = true |- _ => rename H into KTxr end.
    match goal with H : forallb _ (seq 0 11) = true |- _ => rename H into KTx end.
    pose proof (eq_refl (as_owned_static B)) as Hown. pose proof (eq_refl (as_errno B)) as Herr.
    split; [rewrite ard_aview; exact (kp_ra B TB ly S _ _ _ M KTxr)|].
    split; [unfold apart, LA_TEXTS, TEXTS_N; right; lia|].
    split; [unfold apart, LA_TEXTS, TEXTS_N; right; lia|].
    split; [|exact TXO_TR].
    intros i Hi. unfold TEXTS_N in Hi.
    pose proof (kp_forallb_seq _ _ KTx (Z.to_nat i) ltac:(lia)) as Hx.
    cbv beta zeta in Hx. apply andb_prop in Hx as [Hw Hs].
    pose proof (kp_forallb_seq _ _ txo_texts_short (Z.to_nat i) ltac:(lia)) as Hsh.
    cbv beta in Hsh. apply Nat.ltb_lt in Hsh.
    pose proof (TXO_RO (Z.to_nat i) ltac:(lia)) as Hro.
    set (e := nth (Z.to_nat i) KP_TEXTS (0, [])) in *.
    rewrite Z2Nat.id in Hw by lia.
    destruct (kp_kstr_acstr B (w_H W) mem (fst e) (snd e) HRO Hs) as (Hcs & Hq0 & Hql).
    exists (fst e), (map (Z_to_bv 8) (snd e)). rewrite length_map.
    split; [exact (kp_val_mem8 SEGS _ _ B (w_H W) mem _ _ Hown Herr HRO Hw)|].
    split; [unfold LA_G_NL in Hql; lia|].
    split; [exact Hcs|].
    split; [lia|].
    split; [exact Hro|].
    split; unfold apart, LA_G_NL in *; right; lia.
Qed.

(* the whole text_of call at a site, from what a cut of the body carries: the contract applied, its post as the
   contract states it *)
Lemma lf_text_of_call : forall (fy : YK11.FPState) cx fp k2 ev wl lv ly S (W : world SEGS) mem mdl
    (regs : bvmap 5 word) P N o rao,
  @lf_base fx rc SK PI B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx ->
  JRN cx fp ly S W mem mdl k2 ->
  k2 <= ev -> ev + 1 <= EV_LIB ->
  blocks_bytes S <= blocks_bytes (c_S cx) + lv -> lv + TEXT_OF_LIVE <= LIVE_LIB ->
  (length (wild_part (as_universe B) (st_depot S)) <=
     length (wild_part (as_universe B) (st_depot (c_S cx))) + wl)%nat -> (wl + 1 <= LINK_WILD_PER_CALL)%nat ->
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W) mem) ->
  abytes SEGS (rdW W mem) (c_p cx) (c_pl cx) ->
  rdword (aview SEGS (w_H W) mem) (spZ (c_regs cx) - 8) = Some (raZ (c_regs cx)) ->
  rdword (aview SEGS (w_H W) mem) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx)) ->
  rdword (aview SEGS (w_H W) mem) (lf_sp1 cx + LS_P) = Some P ->
  rdword (aview SEGS (w_H W) mem) (lf_sp1 cx + LS_N) = Some N ->
  (exists q, 0 <= q <= c_n cx /\ P = c_p cx + q /\ N = c_n cx - q) ->
  (o = LS_T128 \/ o = LS_T130) ->
  spZ regs = lf_sp1 cx -> s0Z regs = spZ (c_regs cx) ->
  aarg regs 0 = lf_sp1 cx + LS_P -> aarg regs 1 = lf_sp1 cx + o ->
  getr regs 3 = getr (c_regs cx) 3 -> getr regs 4 = getr (c_regs cx) 4 ->
  pa_val A_TEXT = link_text -> getr regs 1 = Z_to_bv 64 (link_text + rao) -> In rao LF_TEXT_OF_SITES ->
  SRr SEGS W (cfg_at (fx := fy) SEGS TEXT_OF_A regs mem mdl)
    (apost (fx := fy) SK SEGS B TEXT_OF_AK 1 (fun a => inFP (text_of_awr regs (rdW W mem)) a) G_HARNESS 0 []
       LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx)) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
       [(LF_CID, fp)] ly S W mem mdl k2 regs
       (fun ly2 S2 W2 regs2 mem2 md2 =>
          mo_le MT S S2 (mo_malloc MT TEXT_OF_LIVE) /\ text_of_ledpost B S S2 /\
          text_of_apostA SEGS PCAP_RLO PCAP_RHI B regs (rdW W mem) regs2 (rdW W2 mem2)
            (ablocks B ly S) (ablocks B ly2 S2))).
Proof.
  intros fy cx fp k2 ev wl lv ly S W mem mdl regs P N o rao HB HJ Hkev Hev Hbb Hlv Hwl Hwl1 HRO Hpl H8 H16 HP HN
    Hq Ho Hsp Hs0 Ha0 Ha1 R3 R4 HBASE R1 Hsite.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof HB as (HPRE & _ & HGX & _).
  pose proof HPRE as (HAFN & _ & _ & _ & _ & _ & _ & _ & _ & Hlive & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hwr).
  pose proof HAFN as (_ & _ & _ & HGP & HTP & _).
  destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly S W mem mdl k2
    HB HJ) as (H16s & Hceil & Hslo & Hshi & H47 & Hwin & HAR).
  assert (Hs1 : spZ (c_regs cx) - 416 - 16 <= lf_sp1 cx <= spZ (c_regs cx) - 416).
  { unfold lf_sp1. pose proof (lf_sp1_range (spZ (c_regs cx)) ltac:(unfold LF_MFRAME, LLVMF_STK in *; lia) H16s)
      as (R & _). unfold LF_MFRAME in R. exact R. }
  assert (Hra : raZ regs = link_text + rao).
  { unfold raZ. rewrite R1. apply unsigned_lit_small.
    unfold LF_TEXT_OF_SITES, AF_LLVMFuzzerTestOneInput, link_text in *. cbn in Hsite. lia. }
  assert (Hret : YK0s.ret_ok (getr regs 1)).
  { rewrite R1, <- HBASE. apply ret_ok_codeptr_v.
    - unfold LF_TEXT_OF_SITES, AF_LLVMFuzzerTestOneInput in Hsite. cbn in Hsite. lia.
    - unfold LF_TEXT_OF_SITES, AF_LLVMFuzzerTestOneInput in Hsite. cbn in Hsite.
      destruct Hsite as [<- | [<- | [<- | []]]]; reflexivity. }
  assert (Hra4 : 4096 <= raZ regs) by (rewrite Hra; unfold link_text, LF_TEXT_OF_SITES, AF_LLVMFuzzerTestOneInput in *;
    cbn in Hsite; lia).
  destruct (lf_text_of_pre cx fp ly S W mem mdl k2 regs P N o HB HJ HRO Hpl HP HN Hq Ho Hsp Ha0 Ha1
    ltac:(rewrite R3; exact HGP) ltac:(rewrite R4; exact HTP) Hret Hra4 ltac:(lia)) as (HAPRE & HRD & HTPRE).
  destruct (lf_site_chain SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END
    cx [(LF_CID, fp)] ly S W mem mdl k2 regs HB HJ H8 H16 ltac:(unfold LLVMF_STK in *; lia) Hs0 Hra4)
    as (_ & HCH).
  assert (HCTX : In (raZ regs :: spine (lf_chain cx)) LF_CTX).
  { apply (lf_site_ctx SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx regs HB).
    rewrite Hra, <- HBASE. replace (pa_val A_TEXT + rao - pa_val A_TEXT) with rao by lia.
    unfold LF_ALLOC_SITES. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hsite. }
  apply (TXO_C fy G_HARNESS 0 [] LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx)) (c_ly cx) (c_S cx) (c_W cx)
    (c_mem cx) (c_md cx) [(LF_CID, fp)] ly S W mem mdl k2 regs (lf_chain cx) HAPRE HRD).
  - pose proof LF_LIVE_HELD_room as LR. unfold TEXT_OF_LIVE, LF_LIVE_HELD in *. lia.
  - apply MT_OK.
  - exact HCH.
  - exact HCTX.
  - unfold text_of_ledpre. unfold link_wild_room, LINK_WILD_PER_CALL in *. lia.
  - exact HTPRE.
Qed.

End b.
End a.

(* TXO_RO is true of the image: Kpre.v's checks hold each texts string and its NUL as read-only image bytes, off
   the runtime's owned statics and errno *)
Section t. Context {rc : YM05.RunCeil}. Context {PI : PAImg link_listing}.
Local Open Scope Z_scope.
Lemma lf_txo_ro : forall (B : asyms), pa_segs = tfibsegs -> PcapSyms B ->
  forall i, (i < 11)%nat ->
  text_of_ro pa_segs PCAP_RLO PCAP_RHI B (fst (nth i KP_TEXTS (0, [])))
    (Z.of_nat (length (snd (nth i KP_TEXTS (0, [])))) + 1).
Proof.
  intros B HSEGS TB i Hi.
  pose proof (kp_img_here B TB HSEGS) as KI. unfold kp_img_b in KI.
  repeat match type of KI with (_ && _)%bool = true => apply andb_prop in KI as [KI ?] end.
  match goal with H : forallb _ (seq 0 11) = true |- _ => rename H into KTx end.
  pose proof (kp_forallb_seq _ _ KTx i Hi) as Hx. cbv beta zeta in Hx. apply andb_prop in Hx as [_ Hs].
  unfold kp_kstr_b in Hs.
  repeat match type of Hs with (_ && _)%bool = true => apply andb_prop in Hs as [Hs ?] end.
  match goal with H : kp_bytes_b _ _ _ _ (_ ++ [0]) = true |- _ => rename H into Hby end.
  intros j Hj.
  assert (Hjl : Nat.lt (Z.to_nat j) (length (snd (nth i KP_TEXTS (0, [])) ++ [0])))
    by (rewrite length_app; cbn [length]; lia).
  pose proof (kp_bytes_inroP _ _ _ _ _ Hby (Z.to_nat j) Hjl) as Hro.
  pose proof (kp_forallb_seq _ _ Hby (Z.to_nat j) Hjl) as Hy. cbv beta in Hy.
  apply andb_prop in Hy as [Hy _]. unfold kp_ro_b in Hy.
  apply andb_prop in Hy as [Hy Herr]. apply andb_prop in Hy as [_ Hown].
  rewrite Z2Nat.id in Hro, Hown, Herr by lia.
  set (x := fst (nth i KP_TEXTS (0, [])) + j) in *.
  split; [exact Hro|]. split.
  - intros HE. apply Exists_exists in HE as (r & Hr & Hz). unfold in_zr in Hz.
    apply negb_true_iff in Hown.
    assert (Hx : existsb (fun r => (fst r <=? x) && (x <? fst r + snd r)) (as_owned_static B) = true)
      by (apply existsb_exists; exists r; split; [exact Hr|];
          apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    rewrite Hx in Hown. discriminate.
  - intros He. apply negb_true_iff in Herr.
    assert (Ht : ((as_errno B <=? x) && (x <? as_errno B + 4))%bool = true)
      by (apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    rewrite Ht in Herr. discriminate.
Qed.
End t.
