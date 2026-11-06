(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC85.v for libreac/fuzz_boxreg's program walk (as fuzz_identity's lib/A/Prog/YC85.v, ea5560a967b, carries it): the listing's names are bsym; module paths changed. No image numeral occurs in this file. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/Prog/YC85.v, with its module paths and module names changed; 313 of its 404 lines of code are new or changed and 320 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputFree.v, with its module names changed; 279 of its 330 lines of code are new or changed and 353 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A (fuzz_link.asan, the PUBLISHED pin, sha256 059dae63e07c...): the call of
   mark_quietly (0x883d4) at op_refused's site 0x831f8 (ra 0x831fc) and op_mark's 0x8347c (ra 0x83480), applied:
   `lf_mq_open_call` (g_sink = 0: the opening arm `mark_quietly_acontract_open`, aleaf_alloc_fx_sk, MO :=
   mo_malloc MT AMF_BLOCK, CTX := LF_CTX, LedPre := True, LedPost := the wild count not growing) and
   `lf_mq_again_call` (g_sink = the kept FILE: `mark_quietly_acontract_again`, aleaf_fx), each from what a cut of the
   loop carries (Mq.v for the Pres and the read set, Dec.v lf_apre_at for the journal premises, Free.v
   lf_site_chain / lf_site_ctx for the allocator's frame chain), to the contract's post as the contract states it.
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AMemFile AMemFileSink LinkWildRoom AF0m AB1v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalk LinkWalkSide BoxBase.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkEntry LinkEntryA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputKpre LLVMFuzzerTestOneInputKeep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputFree LLVMFuzzerTestOneInputDec.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputArmR LLVMFuzzerTestOneInputArmK.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputMb LLVMFuzzerTestOneInputMq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
  model_decide_c remember_c reac_code_emit_c reac_served_mark_c mark_quietly_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* the opening arm's ledger post: the wild count does not grow (mark_quietly's walk's theorem, settled 18:15Z) *)
Definition mq_ledpost (B : asyms) (Sc S2 : astate) : Prop :=
  (length (wild_part (as_universe B) (st_depot S2)) <= length (wild_part (as_universe B) (st_depot Sc)))%nat.

(* blocks placed apart are distinct *)
Lemma mq_pw_nodup : forall (g : Z * Z -> Z * Z) (l : list (Z * Z)),
  YG0f.pairwise YG0f.zdisjoint (map g l) -> (forall x, In x l -> 0 < snd (g x)) -> List.NoDup l.
Proof.
  intros g. induction l as [|x l IH]; intros Hp Hpos; [constructor|].
  cbn [map YG0f.pairwise] in Hp. destruct Hp as (Hf & Hp). constructor.
  - intros Hin. pose proof (proj1 (Forall_forall _ _) Hf (g x) (in_map g l x Hin)) as D.
    unfold YG0f.zdisjoint in D. pose proof (Hpos x (or_introl eq_refl)). lia.
  - apply IH; [exact Hp | intros y Hy; apply Hpos; right; exact Hy].
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
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
Hypothesis MT_OK : forall S m, mo_ok MT S m.
(* mark_quietly's two arms, as proved (mark_quietly_aproof_open at MO := mo_malloc MT AMF_BLOCK,
   CTX := LF_CTX; mark_quietly_aproof_again) *)
Hypothesis MQO : forall fx0 : YK11.FPState,
  @mark_quietly_acontract_open fx0 rc SK pa_segs PCAP_RLO PCAP_RHI B MT (mo_malloc MT AMF_BLOCK) LF_CTX
    (fun _ => True) (mq_ledpost B).
Hypothesis MQA : forall fx0 : YK11.FPState,
  @mark_quietly_acontract_again fx0 rc SK pa_segs PCAP_RLO PCAP_RHI B.

#[local] Notation BASEF cx := (lf_base SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx).
#[local] Notation JRN cx fp ly S W mem mdl k :=
  (ajournal_gx SEGS B G_HARNESS 0 [] LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx))
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(LF_CID, fp)] ly S W mem mdl k).

Lemma mq_side_room : forall S fp, frames S = [(LF_CID, fp)] -> aside_room S MARK_QUIETLY_ASIDE.
Proof. intros S fp Hfr. apply (ar_side_room S fp); [exact Hfr | vm_compute; reflexivity]. Qed.

(* the opening arm's write set: g_nl's head, the marks block (or nothing), the four FILE globals *)
Lemma mq_awr_open_ok : forall cx fp ly S (regs : bvmap 5 word) m mk,
  In (mk, MK_SIZE) (ablocks B ly S) -> ~ In (mk, MK_SIZE) (ablocks B (c_ly cx) (c_S cx)) -> off_img mk MK_SIZE -> 0 < mk ->
  (aarg regs 0 = 0 \/ aarg regs 0 = mk) ->
  (forall a, inFP (mark_quietly_awr_open regs m) a ->
     ajw B G_HARNESS 0 [] LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx)) (c_ly cx) (c_S cx) ly S
       [(LF_CID, fp)] a) /\
  (forall a, inFP (mark_quietly_awr_open regs m) a -> ~ in_roP SEGS PCAP_RLO PCAP_RHI a).
Proof.
  intros cx fp ly S regs m mk Hin Hout Hmkt Hmk0 Ha0.
  assert (HG : forall a, (LA_G_NL <= a < LA_G_NL + NK_N_SENT + 4 \/ LA_G_SINK <= a < LA_G_SINK + 8 \/
                          LA_G_SAID <= a < LA_G_SAID + SAID_SIZE \/ LA_G_SAY <= a < LA_G_SAY + 8 \/
                          LA_OFL_HEAD <= a < LA_OFL_HEAD + 8) -> inG G_HARNESS a).
  { intros a Ha. unfold inG, G_HARNESS.
    unfold NK_N_SENT, LA_G_SINK, LA_G_SAID, SAID_SIZE, LA_G_SAY, LA_OFL_HEAD, LA_G_NL in Ha.
    destruct Ha as [Ha | [Ha | [Ha | [Ha | Ha]]]];
      repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd];
                     unfold LA_G_NL, LA_G_NAMES, LA_LONG_ALIAS, LA_G_SINK, LA_G_SAID, LA_G_SAY, LA_OFL_HEAD; lia
                   | apply Exists_cons_tl ]. }
  assert (HM : forall a, inFP (mark_quietly_awr_open regs m) a ->
             inG G_HARNESS a \/ (aarg regs 0 = mk /\ mk <= a < mk + MK_SIZE)).
  { intros a (r & Hr & Ha). unfold mark_quietly_awr_open in Hr. cbn [In] in Hr.
    destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]; cbn [fst snd] in Ha;
      try (left; apply HG; lia).
    unfold aivl in Ha. destruct Ha0 as [E | E]; rewrite E in Ha; cbn [fst snd] in Ha.
    - cbn in Ha. lia.
    - right. split; [exact E|]. destruct (Z.eqb_spec mk 0); lia. }
  split.
  - intros a Ha. destruct (HM a Ha) as [Hg | (_ & Hb)].
    + exact (ar_ajw_G B cx fp ly S a Hg).
    + exact (ar_ajw_blk B cx fp ly S mk MK_SIZE a Hin Hout Hb).
  - intros a Ha Hro. destruct (HM a Ha) as [Hg | (_ & Hb)].
    + exact (ar_not_ro_G HSEGS a Hg Hro).
    + pose proof (lf_roP_bounds a Hro). unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP, MK_SIZE in *. lia.
Qed.

(* the later arm's write set: the same with the kept FILE block in place of the three FILE heads *)
Lemma mq_awr_again_ok : forall cx fp ly S (regs : bvmap 5 word) m mk sink,
  In (mk, MK_SIZE) (ablocks B ly S) -> ~ In (mk, MK_SIZE) (ablocks B (c_ly cx) (c_S cx)) -> off_img mk MK_SIZE -> 0 < mk ->
  (aarg regs 0 = 0 \/ aarg regs 0 = mk) ->
  In (sink, AMF_BLOCK) (ablocks B ly S) ->
  (In (sink, AMF_BLOCK) (c_T cx) \/ ~ In (sink, AMF_BLOCK) (ablocks B (c_ly cx) (c_S cx))) ->
  (sink + AMF_BLOCK <= 0x10000 \/ YImgTop.IMG_TOP <= sink) ->
  (forall a, inFP (mark_quietly_awr_again sink regs m) a ->
     ajw B G_HARNESS 0 [] LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx)) (c_ly cx) (c_S cx) ly S
       [(LF_CID, fp)] a) /\
  (forall a, inFP (mark_quietly_awr_again sink regs m) a -> ~ in_roP SEGS PCAP_RLO PCAP_RHI a).
Proof.
  intros cx fp ly S regs m mk sink Hin Hout Hmkt Hmk0 Ha0 Hsin HsT Hsimg.
  assert (HG : forall a, (LA_G_NL <= a < LA_G_NL + NK_N_SENT + 4 \/ LA_G_SAID <= a < LA_G_SAID + SAID_SIZE) ->
                 inG G_HARNESS a).
  { intros a Ha. unfold inG, G_HARNESS. unfold NK_N_SENT, LA_G_SAID, SAID_SIZE, LA_G_NL in Ha.
    destruct Ha as [Ha | Ha];
      repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd];
                     unfold LA_G_NL, LA_G_NAMES, LA_LONG_ALIAS, LA_G_SINK, LA_G_SAID, LA_G_SAY, LA_OFL_HEAD; lia
                   | apply Exists_cons_tl ]. }
  assert (HM : forall a, inFP (mark_quietly_awr_again sink regs m) a ->
             inG G_HARNESS a \/ (aarg regs 0 = mk /\ mk <= a < mk + MK_SIZE) \/ (sink <= a < sink + AMF_BLOCK)).
  { intros a (r & Hr & Ha). unfold mark_quietly_awr_again in Hr. cbn [In] in Hr.
    destruct Hr as [<- | [<- | [<- | [<- | []]]]]; cbn [fst snd] in Ha.
    - left. apply HG. lia.
    - unfold aivl in Ha. destruct Ha0 as [E | E]; rewrite E in Ha; cbn [fst snd] in Ha.
      + cbn in Ha. lia.
      + right; left. split; [exact E|]. destruct (Z.eqb_spec mk 0); lia.
    - left. apply HG. lia.
    - right; right. unfold aivl in Ha. cbn [fst snd] in Ha. destruct (Z.eqb_spec sink 0); lia. }
  split.
  - intros a Ha. destruct (HM a Ha) as [Hg | [(_ & Hb) | Hb]].
    + exact (ar_ajw_G B cx fp ly S a Hg).
    + exact (ar_ajw_blk B cx fp ly S mk MK_SIZE a Hin Hout Hb).
    + destruct HsT as [HsT | HsT].
      * left. split; [|lia]. right; left. split.
        -- apply (amf_harness_fp_in (c_T cx) sink AMF_BLOCK a HsT). lia.
        -- exists sink, AMF_BLOCK. split; [exact Hsin|]. change (req_size AMF_BLOCK) with AMF_BLOCK. lia.
      * exact (ar_ajw_blk B cx fp ly S sink AMF_BLOCK a Hsin HsT Hb).
  - intros a Ha Hro. pose proof (lf_roP_bounds a Hro) as Hlo.
    destruct (HM a Ha) as [Hg | [(_ & Hb) | Hb]].
    + exact (ar_not_ro_G HSEGS a Hg Hro).
    + unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP, MK_SIZE in *. lia.
    + destruct Hsimg as [Hs | Hs]; [|lia].
      destruct Hro as [(s & Hs1 & _ & Hr) | Hr].
      * assert (Hi : in_img SEGS a) by (exists s; split; [exact Hs1 | exact Hr]).
        pose proof (pa_img_range a Hi). lia.
      * unfold PCAP_RLO in Hr. lia.
Qed.


(* the facts of a mark site's call that both arms ask: ra, the window, gp / tp, the chain and its context *)
Lemma mq_site_facts : forall cx fp ly S (W : world SEGS) mem mdl k (regs : bvmap 5 word) rao,
  BASEF cx -> JRN cx fp ly S W mem mdl k ->
  rdword (aview SEGS (w_H W) mem) (spZ (c_regs cx) - 8) = Some (raZ (c_regs cx)) ->
  rdword (aview SEGS (w_H W) mem) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx)) ->
  spZ regs = lf_sp1 cx -> s0Z regs = spZ (c_regs cx) ->
  pa_val A_TEXT = link_text -> getr regs 1 = Z_to_bv 64 (link_text + rao) -> In rao LF_MARK_SITES ->
  YK0s.ret_ok (getr regs 1) /\ 4096 <= raZ regs /\
  alloc_ceiling <= spZ regs - MARK_QUIETLY_AK /\
  achain ly (aview SEGS (w_H W) mem) (spZ regs) (s0Z regs) (lf_chain cx) /\
  In (raZ regs :: spine (lf_chain cx)) LF_CTX.
Proof.
  intros cx fp ly S W mem mdl k regs rao HB HJ H8 H16 Hsp Hs0 HBASE R1 Hsite.
  pose proof asan_consts as ((C1a & C1b) & _).
  destruct (ar_sp1_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly S W mem mdl k
    HB HJ) as (Hs1 & _ & Hceil & _).
  assert (Hra : raZ regs = link_text + rao).
  { unfold raZ. rewrite R1. apply unsigned_lit_small.
    unfold LF_MARK_SITES, AF_LLVMFuzzerTestOneInput, link_text in *. cbn in Hsite. lia. }
  assert (Hret : YK0s.ret_ok (getr regs 1)).
  { rewrite R1, <- HBASE. apply ret_ok_codeptr_v.
    - unfold LF_MARK_SITES, AF_LLVMFuzzerTestOneInput in Hsite. cbn in Hsite. lia.
    - unfold LF_MARK_SITES, AF_LLVMFuzzerTestOneInput in Hsite. cbn in Hsite.
      destruct Hsite as [<- | [<- | []]]; reflexivity. }
  assert (Hra4 : 4096 <= raZ regs) by (rewrite Hra; unfold link_text, LF_MARK_SITES, AF_LLVMFuzzerTestOneInput in *;
    cbn in Hsite; lia).
  destruct (lf_site_chain SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END
    cx [(LF_CID, fp)] ly S W mem mdl k regs HB HJ H8 H16 ltac:(unfold LLVMF_STK in *; lia) Hs0 Hra4)
    as (_ & HCH).
  assert (HCTX : In (raZ regs :: spine (lf_chain cx)) LF_CTX).
  { apply (lf_site_ctx SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx regs HB).
    rewrite Hra, <- HBASE. replace (pa_val A_TEXT + rao - pa_val A_TEXT) with rao by lia.
    unfold LF_ALLOC_SITES. repeat (apply in_or_app; right). exact Hsite. }
  split; [exact Hret|]. split; [exact Hra4|]. split; [|split; [exact HCH | exact HCTX]].
  rewrite Hsp. assert (HAK : MARK_QUIETLY_AK = 24608) by reflexivity. unfold LLVMF_STK in *. lia.
Qed.

(* the opening call: g_sink = 0, the kept set empty *)
Lemma lf_mq_open_call : forall (fy : YK11.FPState) cx fp k2 ly S (W : world SEGS) mem mdl
    (regs : bvmap 5 word) md mk kbs mbs gbs rao nm,
  @lf_base fx rc SK PI B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx ->
  JRN cx fp ly S W mem mdl k2 -> frames S = [(LF_CID, fp)] ->
  YK0o.frm_zero (@YK11.fp_csr fy) -> k2 + 1 <= EV_LIB ->
  lf_bl B cx [(md, MD_SIZE); (mk, MK_SIZE)] [] ly S ->
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W) mem) ->
  lf_blocks B cx md mk [] ly S (rdW W mem) -> lf_data_nm cx md mk kbs mbs gbs (rdW W mem) ->
  amf_heads SEGS link_amf (rdW W mem) 0 -> amf_env SEGS link_amf (rdW W mem) ->
  nk_opened kbs + 2 < 2 ^ 31 ->
  rdword (aview SEGS (w_H W) mem) (spZ (c_regs cx) - 8) = Some (raZ (c_regs cx)) ->
  rdword (aview SEGS (w_H W) mem) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx)) ->
  spZ regs = lf_sp1 cx -> s0Z regs = spZ (c_regs cx) ->
  getr regs 3 = getr (c_regs cx) 3 -> getr regs 4 = getr (c_regs cx) 4 ->
  pa_val A_TEXT = link_text -> getr regs 1 = Z_to_bv 64 (link_text + rao) -> In rao LF_MARK_SITES ->
  (aarg regs 0 = 0 \/ aarg regs 0 = mk) -> aarg regs 1 < alloc_ceiling ->
  astr_arg SEGS (rdW W mem) (aarg regs 1) nm ->
  amk_name_ok SEGS B regs MARK_QUIETLY_AK 0 0 (rdW W mem) nm ->
  (forall s, nm = Some s -> aarg regs 1 + Z.of_nat (length s) + 8 <= LA_G_SINK) ->
  (forall a, aarg regs 1 <> 0 -> forall s, acstr_at SEGS (rdW W mem) (aarg regs 1) s ->
     aarg regs 1 <= a <= aarg regs 1 + Z.of_nat (length s) ->
     akb SEGS B ly S (spZ regs - MARK_QUIETLY_AK) (spZ regs) a) ->
  SRr SEGS W (cfg_at (fx := fy) SEGS MARK_QUIETLY_A regs mem mdl)
    (apostF (fx := fy) SK SEGS B MARK_QUIETLY_AK 1 (fun a => inFP (mark_quietly_awr_open regs (rdW W mem)) a)
       G_HARNESS 0 [] LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx)) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx)
       (c_md cx) [(LF_CID, fp)] ly S W mem mdl k2 regs
       (fun ly2 S2 W2 regs2 mem2 md2 =>
          mo_le MT S S2 (mo_malloc MT AMF_BLOCK) /\ mq_ledpost B S S2 /\
          mark_quietly_aposta_open SEGS regs (rdW W mem) regs2 (rdW W2 mem2) (ablocks B ly S) (ablocks B ly2 S2))).
Proof.
  intros fy cx fp k2 ly S W mem mdl regs md mk kbs mbs gbs rao nm HB HJ Hfr Hfrm Hev Hbl HRO HBL HD Hh Henv Hop
    H8 H16 Hsp Hs0 R3 R4 HBASE R1 Hsite Ha0 Ha1 Hnm Hnok Hnlo Hnakb.
  pose proof HB as (HPRE & _ & HGX & _).
  pose proof HPRE as (HAFN & _ & _ & _ & _ & _ & _ & _ & _ & Hlive & _).
  destruct (ar_gp_tp SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx HB) as (HGP & HTP).
  destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly S W mem mdl k2
    HB HJ) as (_ & _ & _ & _ & _ & _ & HAR).
  destruct (mq_site_facts cx fp ly S W mem mdl k2 regs rao HB HJ H8 H16 Hsp Hs0 HBASE R1 Hsite)
    as (Hret & Hra4 & HK & HCH & HCTX).
  pose proof HBL as (Hmdin & Hmkin & Hmdc & Hmkc & _ & _ & _ & _ & _ & Hmkt & _).
  pose proof HD as (Hnl & _ & Htab & _ & _ & _ & _ & _ & _ & _ & Hifp & _).
  destruct (mq_awr_open_ok cx fp ly S regs (rdW W mem) mk Hmkin Hmkc Hmkt
    ltac:(destruct (al_blocks _ _ LAWS _ _ _ _ _ mk MK_SIZE HAR Hmkin) as (_ & H4 & _); lia) Ha0) as (HW & HR).
  apply (MQO fy G_HARNESS 0 [] LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx)) (c_ly cx) (c_S cx) (c_W cx)
    (c_mem cx) (c_md cx) [(LF_CID, fp)] ly S W mem mdl k2 regs (lf_chain cx)).
  - exact (lf_apre_at SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly S W mem mdl k2 regs
      MARK_QUIETLY_AK 1 MARK_QUIETLY_ASIDE _ HB HJ HRO Hsp ltac:(rewrite R3; exact HGP) ltac:(rewrite R4; exact HTP)
      Hret Hra4 ltac:(vm_compute; split; discriminate) ltac:(lia) Hev (mq_side_room S fp Hfr) HW HR).
  - exact (amf_harness_fp_sink_open (c_T cx)).
  - exact (mq_ard_akb B TB HSEGS ly S W mem mdl kbs regs ly S (spZ regs - MARK_QUIETLY_AK) (spZ regs) HAR HRO HGX Hnl
      Htab Hifp Hnakb).
  - destruct (lf_bl_bytes B cx _ _ ly S Hbl) as (D & HT & Hbb).
    assert (HD0 : D = []) by (destruct D; [reflexivity | destruct (c_T cx); discriminate]).
    subst D. cbn [bsum fold_right fst snd] in Hbb. unfold LIVE_LIB, MD_SIZE, MK_SIZE, AMF_BLOCK in *. lia.
  - apply MT_OK.
  - exact HCH.
  - exact HCTX.
  - exact I.
  - exact Hfrm.
  - exact (lf_mq_pre_open B LAWS TB HSEGS cx ly S W mem mdl md mk kbs mbs gbs regs nm HAR HRO HBL HD Hh Henv
      Hop HK Ha0 Ha1 Hnm Hnok Hnlo).
Qed.

(* a later call: g_sink = the kept FILE *)
Lemma lf_mq_again_call : forall (fy : YK11.FPState) cx fp k2 ly S (W : world SEGS) mem mdl
    (regs : bvmap 5 word) md mk kbs mbs gbs rao nm sink,
  @lf_base fx rc SK PI B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx ->
  JRN cx fp ly S W mem mdl k2 -> frames S = [(LF_CID, fp)] ->
  YK0o.frm_zero (@YK11.fp_csr fy) -> k2 <= EV_LIB ->
  lf_bl B cx [(md, MD_SIZE); (mk, MK_SIZE)] [(sink, AMF_BLOCK)] ly S ->
  incl [(sink, AMF_BLOCK)] (ablocks B ly S) ->
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W) mem) ->
  lf_blocks B cx md mk [(sink, AMF_BLOCK)] ly S (rdW W mem) -> lf_data_nm cx md mk kbs mbs gbs (rdW W mem) ->
  amf_heads SEGS link_amf (rdW W mem) sink -> amemfile_at SEGS link_amf (rdW W mem) sink ->
  nk_opened kbs + 2 < 2 ^ 31 ->
  rdword (aview SEGS (w_H W) mem) (spZ (c_regs cx) - 8) = Some (raZ (c_regs cx)) ->
  rdword (aview SEGS (w_H W) mem) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx)) ->
  spZ regs = lf_sp1 cx -> s0Z regs = spZ (c_regs cx) ->
  getr regs 3 = getr (c_regs cx) 3 -> getr regs 4 = getr (c_regs cx) 4 ->
  pa_val A_TEXT = link_text -> getr regs 1 = Z_to_bv 64 (link_text + rao) -> In rao LF_MARK_SITES ->
  (aarg regs 0 = 0 \/ aarg regs 0 = mk) ->
  astr_arg SEGS (rdW W mem) (aarg regs 1) nm ->
  amk_name_ok SEGS B regs MARK_QUIETLY_AK sink AMF_BLOCK (rdW W mem) nm ->
  (forall s, nm = Some s -> aarg regs 1 + Z.of_nat (length s) + 8 <= LA_G_SINK) ->
  (forall a, aarg regs 1 <> 0 -> forall s, acstr_at SEGS (rdW W mem) (aarg regs 1) s ->
     aarg regs 1 <= a <= aarg regs 1 + Z.of_nat (length s) ->
     akb SEGS B ly S (spZ regs - MARK_QUIETLY_AK) (spZ regs) a) ->
  SRr SEGS W (cfg_at (fx := fy) SEGS MARK_QUIETLY_A regs mem mdl)
    (apostF (fx := fy) SK SEGS B MARK_QUIETLY_AK 0
       (fun a => inFP (mark_quietly_awr_again sink regs (rdW W mem)) a)
       G_HARNESS 0 [] LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx)) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx)
       (c_md cx) [(LF_CID, fp)] ly S W mem mdl k2 regs
       (fun ly2 S2 W2 regs2 mem2 md2 =>
          S2 = set_fs (st_fs S2) S /\ Permutation (ablocks B ly2 S2) (ablocks B ly S) /\
          mark_quietly_apost_again SEGS sink regs (rdW W mem) regs2 (rdW W2 mem2))).
Proof.
  intros fy cx fp k2 ly S W mem mdl regs md mk kbs mbs gbs rao nm sink HB HJ Hfr Hfrm Hev Hbl Hinc HRO HBL HD Hh Hf
    Hop H8 H16 Hsp Hs0 R3 R4 HBASE R1 Hsite Ha0 Hnm Hnok Hnlo Hnakb.
  pose proof HB as (HPRE & _ & HGX & _).
  destruct (ar_gp_tp SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx HB) as (HGP & HTP).
  destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly S W mem mdl k2
    HB HJ) as (_ & _ & _ & _ & _ & _ & HAR).
  destruct (mq_site_facts cx fp ly S W mem mdl k2 regs rao HB HJ H8 H16 Hsp Hs0 HBASE R1 Hsite)
    as (Hret & Hra4 & HK & HCH & HCTX).
  pose proof HBL as (Hmdin & Hmkin & Hmdc & Hmkc & _ & _ & _ & _ & _ & Hmkt & _).
  pose proof HD as (Hnl & _ & Htab & _ & _ & _ & _ & _ & _ & _ & Hifp & _).
  assert (Hsin : In (sink, AMF_BLOCK) (ablocks B ly S)) by (apply Hinc; left; reflexivity).
  assert (HsT : In (sink, AMF_BLOCK) (c_T cx) \/ ~ In (sink, AMF_BLOCK) (ablocks B (c_ly cx) (c_S cx))).
  { destruct Hbl as (D & HT & HP).
    destruct (c_T cx) as [|t0 [|t1 tr]] eqn:EcT.
    - right. cbn [app] in HT. subst D. intros Hc.
      destruct (al_sep _ _ LAWS _ _ _ _ _ HAR) as (Hsep & _).
      apply YG0s.pairwise_app_inv in Hsep as (Hsep & _ & _).
      assert (ND : List.NoDup (ablocks B ly S)).
      { apply (mq_pw_nodup (fun b => (fst b, req_size (snd b))) _ Hsep).
        intros x Hx. cbn [snd]. unfold req_size. destruct (Z.eqb_spec (snd x) 0); [lia|].
        destruct (al_blocks _ _ LAWS _ _ _ _ _ (fst x) (snd x) HAR ltac:(destruct x; exact Hx)) as (_ & _ & _ & _ & _ & _ & Hn).
        lia. }
      pose proof (Permutation_NoDup HP ND) as ND'.
      apply NoDup_app_remove_l in ND'. cbn [app] in ND'. apply List.NoDup_cons_iff in ND' as (Hn & _).
      exact (Hn (in_or_app [] _ _ (or_intror Hc))).
    - left. cbn [app] in HT. injection HT as Ht0 HD0. subst t0. left. reflexivity.
    - cbn [app] in HT. discriminate HT. }
  destruct (blk_off_imgP B ly S W mem mdl sink AMF_BLOCK HAR Hsin) as [Hoff | Hoff];
    change (req_size AMF_BLOCK) with AMF_BLOCK in Hoff; unfold YImgTop.IMG_LO in Hoff.
  all: assert (Hsimg : sink + AMF_BLOCK <= 0x10000 \/ YImgTop.IMG_TOP <= sink) by lia.
  all: destruct (mq_awr_again_ok cx fp ly S regs (rdW W mem) mk sink Hmkin Hmkc Hmkt
    ltac:(destruct (al_blocks _ _ LAWS _ _ _ _ _ mk MK_SIZE HAR Hmkin) as (_ & H4 & _); lia) Ha0 Hsin HsT Hsimg) as (HW & HR).
  all: apply (MQA fy sink G_HARNESS 0 [] LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx)) (c_ly cx) (c_S cx)
         (c_W cx) (c_mem cx) (c_md cx) [(LF_CID, fp)] ly S W mem mdl k2 regs);
    [ exact (lf_apre_at SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly S W mem mdl k2
        regs MARK_QUIETLY_AK 0 MARK_QUIETLY_ASIDE _ HB HJ HRO Hsp ltac:(rewrite R3; exact HGP)
        ltac:(rewrite R4; exact HTP) Hret Hra4 ltac:(vm_compute; split; discriminate) ltac:(lia) ltac:(lia)
        (mq_side_room S fp Hfr) HW HR)
    | exact (mq_ard_akb B TB HSEGS ly S W mem mdl kbs regs ly S (spZ regs - MARK_QUIETLY_AK) (spZ regs) HAR HRO HGX
        Hnl Htab Hifp Hnakb)
    | exact Hfrm
    | exact (lf_mq_pre_again B LAWS TB HSEGS cx ly S W mem mdl md mk kbs mbs gbs regs nm sink HAR HRO HBL
        HD Hinc Hh Hf Hop HK Ha0 Hnm Hnok Hnlo) ].
Qed.

End a.
