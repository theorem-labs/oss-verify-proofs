(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACer.v, with its module paths and module names changed; 1338 of its 1373 lines of code are new or changed and 261 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_K.v; 1536 of its 1692 lines of code are new or changed and 1217 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_write_value.v, with its module names changed; 222 of its 422 lines of code are new or changed and 1492 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/ZZwv_cps.v; 300 of its 371 lines of code are new or changed and 351 lines of the source are left out. *)
(* write_value's CONTAINER arms (fs.asan image A, write_value 0x83d84): the two CALL SITES whose callee is `put` of
   a read-only literal - the object's key separator (':' / ': ', return 0x84068) and the item loop's comma
   (',', return 0x83ffc). Each lemma runs the engine segment out of the previous resume point (ZZwv_runs2), applies
   put's contract at the call registers (its premises from ZZwv_call3.wvc_callpre, the invariant's writer facts and
   the model lemmas of ZZwv_comp), and lands the loop invariant at the return point with ZZwv_step.wvc_ret_inv.
   Rule 24: no function proved here (these are call-site steps inside write_value's container arms; the lane's
   lookup for write_value is recorded in (internal path), CHECKER CONFIRM a Theorem Labs lane). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat
FSH_Fn_writer FSH_Fn_alloc FSW_K FSW_K3 FSW_ret FSW_rres FSW_writer_tbl FSW_writer_model FSW_writer_kit
FSH_Fn_reader FSW_rd FSupoisonStack FSW_pj ZZwv_defs ZZwv_inv ZZwv_kit ZZwv_comp ZZwv_tree ZZwv_call ZZwv_call2
ZZwv_call3 ZZwv_res ZZwv_ret ZZwv_runs2 ZZwv_step.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require AF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec WriterApp WriterValue PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the three read-only literals these two sites put (FSH_Rt.FS_RO_STRS) ---- *)
Lemma wvc_in_colon : In (WVC_COLON, [58]) FS_RO_STRS.
Proof. unfold FS_RO_STRS, WVC_COLON. cbn [In]. repeat (first [left; reflexivity | right]). Qed.
Lemma wvc_in_colon_sp : In (WVC_COLON_SP, [58; 32]) FS_RO_STRS.
Proof. unfold FS_RO_STRS, WVC_COLON_SP. cbn [In]. repeat (first [left; reflexivity | right]). Qed.
Lemma wvc_in_comma : In (WVC_COMMA, [44]) FS_RO_STRS.
Proof. unfold FS_RO_STRS, WVC_COMMA. cbn [In]. repeat (first [left; reflexivity | right]). Qed.

Section A. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Hypothesis HSS : FsShadowSyms B.
(* the arm instance: its fixed data and the entry state *)
Variable F : wvc_fix.
Variables (ly0 : alayout) (S0 : astate) (U0 : list (Z * Z)) (W0 : world tfibsegs) (mem0 : word -> option byte)
  (md0 : Model) (regs0 : bvmap 5 word).
(* the entry facts the arms' callers discharge once *)
Hypothesis HE_sp16 : wf_sp F mod 16 = 0.
Hypothesis HE_ot16 : wf_ot F mod 16 = 0.
Hypothesis HE_oot : wf_o F + 32 <= wf_ot F.
Hypothesis HE_o8 : wf_o F mod 8 = 0.
Hypothesis HE_top : wf_ot F <= ly_top ly0.
Hypothesis HE_top47 : ly_top ly0 <= 2 ^ 47.
Hypothesis HE_lo : alloc_ceiling + STK_write_value (wf_m F) <= wf_sp F.
Hypothesis HE_gp : YK11.getr regs0 3%bv = w64 (as_gp B).
Hypothesis HE_tp : YK11.getr regs0 4%bv = w64 (as_tp B).
Hypothesis HE_cap0 : 0 <= wf_cap0 F.
Hypothesis HE_capl : wf_cap0 F <= wf_live F.
Hypothesis HE_cnt0 : 0 <= wf_cnt0 F.
Hypothesis HE_p : 0 <= wf_p F < alloc_ceiling.
Hypothesis HE_d : 0 <= wf_d F.
Hypothesis HE_dd : wf_d F + Z.of_nat (PjTree.depth (wf_t F)) <= 2 ^ 31 - 1.
Hypothesis HE_room : Z.of_nat (length (wf_text0 F)) + Z.of_nat (length (concat (wvc_WP F))) + 1 <= WMAX.
Hypothesis HE_bud : wbudget_pre S0 (wf_cap0 F) (wf_cnt0 F) (wf_live F) (WriterApp.putN (wvc_st0 F) (wvc_WP F)).
Hypothesis HE_frl : Z.of_nat (length (frames S0)) <= FRL_CRT_CALLEE.
Hypothesis HE_foot : forall x, wf_o F <= x < wf_ot F -> ~ PjStruct.pj_foot (wf_v F) (wf_D F) x.
Hypothesis HE_plain : jv_plain (wf_t F).
Hypothesis HE_ty :
  (wf_ty F = 5 /\ exists items, wf_t F = PjTree.JArr items /\ wf_n F = Z.of_nat (length items) /\ wf_keys F = 0) \/
  (wf_ty F = 6 /\ exists members, wf_t F = PjTree.JObj members /\ wf_n F = Z.of_nat (length members)).
Hypothesis HE_hdr : exists num capn,
  PjStruct.pj_hdr tfibsegs (rdW W0 mem0) (wf_v F) (wf_ty F) num (wf_str F) (wf_kids F) (wf_keys F) (wf_n F) capn.
Hypothesis HE_n : 0 <= wf_n F < 2 ^ 54.
Hypothesis HE_kk : 0 <= wf_kids F /\ wf_kids F + 56 * wf_n F <= alloc_ceiling /\
                   0 <= wf_keys F /\ wf_keys F + 8 * wf_n F <= alloc_ceiling.

(* membership in a short concrete register list *)
Local Ltac wvc_inq := cbn [In]; repeat (first [left; reflexivity | right]).

(* ---- the separator literal of this arm: its table entry, its length and where it lives ---- *)
Lemma wvc_sep_str :
  In (wvc_sep (wf_p F), WriterValue.wsep (negb (wf_p F =? 0))) FS_RO_STRS /\
  Z.of_nat (length (WriterValue.wsep (negb (wf_p F =? 0)))) = wvc_seplen (wf_p F) /\
  wvc_sep (wf_p F) + Z.of_nat (length (WriterValue.wsep (negb (wf_p F =? 0)))) < SHADOW_OFF.
Proof.
unfold wvc_sep, wvc_seplen, WriterValue.wsep.
destruct (wf_p F =? 0); cbn [negb length].
- split; [exact wvc_in_colon|]. split; [reflexivity|].
  unfold WVC_COLON, SHADOW_OFF. cbn [length Z.of_nat]. lia.
- split; [exact wvc_in_colon_sp|]. split; [reflexivity|].
  unfold WVC_COLON_SP, SHADOW_OFF. cbn [length Z.of_nat]. lia.
Qed.

(* ---- a read-only literal's bytes on the MACHINE's own memory at an ARU state (ZZwv_inv.wvc_lit_pre reads the
   unpoisoned memory, which below SHADOW_OFF is the machine's: ZZwv_kit.zwk_j_mrestrict_low) ---- *)
Lemma wvc_lit_raw : forall ly S U (W : world tfibsegs) mem mdC SA (LB : list Z),
  fs_img_facts tfibsegs B ->
  ARU tfibsegs B ly S U W mem mdC ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) mem) ->
  In (SA, LB) FS_RO_STRS -> SA + Z.of_nat (length LB) < SHADOW_OFF ->
  zbytes_at tfibsegs W mem SA LB /\ WriterSpec.bytes_ok LB /\
  4096 <= SA /\ SA + Z.of_nat (length LB) <= alloc_ceiling.
Proof.
intros ly S U W mem mdC SA LB IMG HARU HRO Hin Hhi.
destruct (wvc_lit_pre B ly S U W (unpoison U mem) mdC SA LB 0 IMG (proj1 HARU)
  (proj1 (zwk_j_arodata_unpoison B ly S U W mem mdC HARU) HRO) Hin) as (HZ & HBO & _ & H4096 & Hceil).
split; [|split; [exact HBO | split; [exact H4096 | exact Hceil]]].
unfold zbytes_at in HZ |- *. apply (garr8_frame tfibsegs _ _ SA LB HZ).
intros a Ha. unfold mbyte.
rewrite (zwk_j_mrestrict_low B ly S U W mem mdC (w_H W) a HARU ltac:(lia)). reflexivity.
Qed.

(* ================= one call of `put` of a read-only literal, from the facts at the call =================
   The caller has already run the engine segment out of the previous resume point, so the state here is the callee's
   entry: the journal from the arm's entry at the call memory, ARU, the arm's writer facts, the frame chunks and the
   call registers. The step discharges put's contract and hands back the loop invariant at the return point r2. *)
Lemma wvc_put_step : forall SA (LB : list Z) Pd Rest i2 r2 ly S U (W : world tfibsegs)
    memC mdC (regsC R0 : bvmap 5 word) ke key buf (Q : world tfibsegs -> config -> Prop),
  put_spec B tfibsegs -> fs_img_facts tfibsegs B ->
  In (SA, LB) FS_RO_STRS -> SA + Z.of_nat (length LB) < SHADOW_OFF ->
  wvc_WP F = Pd ++ [LB] ++ Rest ->
  ajournal tfibsegs B (wvc_STK F) (wf_ot F) (wvc_FP F) ly0 S0 W0 (unpoison U0 mem0) md0 []
    ly S W (unpoison U memC) mdC (wevk (wf_cap0 F) (wvc_stP F Pd)) ->
  ARU tfibsegs B ly S U W memC mdC ->
  wvc_sem B F ly0 S0 U0 W0 mem0 regs0 ly S U W memC buf (wvc_stP F Pd) ->
  Forall (YP09.chunk_ok tfibsegs (wvc_E F regs0 R0 ke key) (rdW W memC) (wf_sp F - WVC_F)) (wvc_csL (wf_p F)) ->
  YK11.getr R0 9%bv = w64 (wf_v F) ->
  4096 <= r2 < 2 ^ 64 -> YK0s.ret_ok (Z_to_bv 64 r2) ->
  YK11.getr regsC 1%bv = w64 r2 ->
  YK11.getr regsC 10%bv = w64 (wf_o F) -> YK11.getr regsC 11%bv = w64 SA ->
  YK11.getr regsC 12%bv = w64 (Z.of_nat (length LB)) ->
  spZ regsC = wf_sp F - WVC_F ->
  YK11.getr regsC 8%bv = w64 (wf_o F) -> YK11.getr regsC 9%bv = w64 (wf_v F) ->
  YK11.getr regsC 19%bv = w64 (wf_p F) -> YK11.getr regsC 21%bv = w64 i2 ->
  YK11.getr regsC 25%bv = w64 (56 * i2) -> YK11.getr regsC 22%bv = w64 (8 * i2) ->
  YK11.getr regsC 3%bv = YK11.getr regs0 3%bv -> YK11.getr regsC 4%bv = YK11.getr regs0 4%bv ->
  YK11.getr regsC 18%bv = w64 ((wf_v F + 40) / 8 + SHADOW_OFF) ->
  YK11.getr regsC 20%bv = w64 (wf_v F + 40) -> YK11.getr regsC 23%bv = w64 (wf_v F + 24) ->
  YK11.getr regsC 24%bv = w64 (wf_d F + 1) ->
  YK11.getr regsC 26%bv = w64 ((wf_v F + 24) / 8 + SHADOW_OFF) ->
  YK11.getr regsC 27%bv = w64 (wf_v F / 8 + SHADOW_OFF) ->
  0 <= i2 < wf_n F ->
  (forall ly' S' U' (W' : world tfibsegs) regs' mem' md' buf' key',
     wvc_inv B F r2 i2 (wf_keys F + 8 * i2) key' (Pd ++ [LB]) ly0 S0 U0 W0 mem0 md0 regs0
       W' (mkst regs' (Z_to_bv 64 r2) mem' (seg_rom tfibsegs)) md' ly' S' U' buf' ->
     SRr tfibsegs W' (cfg_at tfibsegs r2 regs' mem' md') Q) ->
  SRr tfibsegs W (cfg_at tfibsegs A_put regsC memC mdC) Q.
Proof.
intros SA LB Pd Rest i2 r2 ly S U W memC mdC regsC R0 ke key buf Q HPUT IMG Hin Hhi HWP HJ HARU HSEM HCH HR09
  Hr2 Hret Hc1 Hc10 Hc11 Hc12 Hsp Hc8 Hc9 Hc19 Hc21 Hc25 Hc22 Hc3 Hc4 Hc18 Hc20 Hc23 Hc24 Hc26 Hc27 Hi2 K.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HWF : WVC_F = 176) by reflexivity.
pose proof (wvc_stk (wf_m F)) as (HSF & HSP & _).
assert (HSKp : 0 <= STK_put) by (vm_compute; discriminate).
pose proof (wvc_sem_o_sp B F ly0 S0 U0 W0 mem0 regs0 ly S U W memC buf _ HSEM) as Hosp.
pose proof (proj1 HARU) as HAR.
(* the journal's layout and frames clauses *)
pose proof HJ as (_ & Hly & _ & _ & _ & Hfrs & Hnev & _).
assert (Etop : ly_top ly = ly_top ly0)
  by (destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & E & _); exact E).
(* the arm's writer facts at the call *)
pose proof HSEM as (HOUT & HGL & HHD & HUS & HBS & HBK & HCNT & HWK & HN & HPO & HNB & HUL & HD & HROOT & HBIN &
  HB0 & HRO & H8 & HC & HU0).
destruct HGL as (peak & Hpk & HGLOB).
pose proof HOUT as (Ho8 & Ho0 & Hotop & _ & Hbuf64 & Hcap64 & _).
pose proof HBK as (HcapW & Hbb & Hcntle).
pose proof (wv_cap_mono (wvc_st0 F) Pd HE_cap0) as Hcapmono.
assert (Hspot : wf_sp F <= wf_ot F) by lia.
assert (Hot47 : wf_ot F <= 2 ^ 47) by lia.
(* the literal's bytes at the call memory *)
destruct (wvc_lit_raw ly S U W memC mdC SA LB IMG HARU HRO Hin Hhi) as (HZB & HBOK & H4096 & Hsceil).
(* case 1 of the chain clause: the saved-ra slot at offset 168 of the frame *)
assert (HC1 : wf_o F = wf_sp F + 8 ->
  rdword (aview tfibsegs (w_H W) (unpoison U memC)) (wf_sp F - 8) = Some (raZ regs0)).
{ intros _.
  assert (Hin168 : In (YP09.mkChunk 168 (CVal 8 (SOff (xatom 17) 0))) (wvc_csL (wf_p F))).
  { unfold wvc_csL. apply in_or_app. right. unfold wvc_cs0. right.
    apply in_map_iff. exists 12%nat. split; [reflexivity | apply in_seq; lia]. }
  pose proof (proj1 (Forall_forall _ _) HCH _ Hin168) as HCK.
  assert (Hden : sv_denot (wvc_E F regs0 R0 ke key) (SOff (xatom 17) 0) = Z_to_bv 64 (raZ regs0)).
  { rewrite fsw_SOff0, (wvc_E_x F regs0 R0 ke key 17%nat).
    cbn [wvc_xs wvc_saved map app nth].
    unfold raZ. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  pose proof (val_of_chunk_ok tfibsegs (wvc_E F regs0 R0 ke key) (rdW W memC) (wf_sp F - WVC_F) 168 8
    (SOff (xatom 17) 0) (raZ regs0) HCK Hden
    ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply u64_range) ltac:(cbn; lia)) as HVM.
  cbn [N.to_nat] in HVM.
  replace (wf_sp F - WVC_F + 168) with (wf_sp F - 8) in HVM by lia.
  pose proof (AF0x.val_mem_rdword (w_H W) memC (wf_sp F - 8) (raZ regs0) (u64_range _) HVM) as HRD.
  assert (HEQ : rdword (aview tfibsegs (w_H W) (unpoison U memC)) (wf_sp F - 8)
              = rdword (aview tfibsegs (w_H W) memC) (wf_sp F - 8)).
  { apply rdword_ext. intros k Hk. apply aview_unpoison_out.
    apply (zwk_p_stack_not_ush B ly S U W memC mdC); [exact HARU | lia]. }
  rewrite HEQ. exact HRD. }
(* the callee's fpreU, the one-node chain at o and the window presence *)
destruct (wvc_callpre B F ly0 S0 U0 W0 mem0 md0 regs0 ly S U W memC mdC _ buf (wvc_stP F Pd) regsC STK_put
  HJ HARU HSEM HC1 Hsp HE_sp16 HE_ot16 Hspot HSKp HSP
  ltac:(rewrite Hc1; exact Hret)
  ltac:(unfold raZ; rewrite Hc1; unfold w64; rewrite unsigned_lit_small by lia; lia)
  ltac:(rewrite Hc3; exact HE_gp) ltac:(rewrite Hc4; exact HE_tp)
  ltac:(unfold s0Z; rewrite Hc8; unfold w64; rewrite unsigned_lit_small by lia; reflexivity)
  HE_oot ltac:(rewrite Etop; exact HE_top) HE_o8 ltac:(lia)) as (ch & Hch & HPRE & HCHAIN & HPRESENT).
(* the call *)
eapply SRr_bind.
{ apply (HPUT ly S U W regsC memC mdC ch (wf_ot F) (wf_o F) SA (Z.of_nat (length LB)) buf
    (WriterApp.w_cap (wvc_stP F Pd)) (WriterApp.w_failed (wvc_stP F Pd)) (WriterApp.w_text (wvc_stP F Pd)) LB
    (wf_live F + WriterApp.w_cap (wvc_stP F Pd) - wf_cap0 F) peak
    (WriterApp.w_cnt (wvc_stP F Pd)) (WriterApp.w_fail (wvc_stP F Pd)) HPRE HHD).
  - rewrite Hfrs. cbn [app]. unfold FRL_CRT_CALLEE in *. lia.
  - exact Hc10.
  - exact Hc11.
  - exact Hc12.
  - exact HOUT.
  - exact HGLOB.
  - exact HU0.
  - lia.
  - exact HE_oot.
  - exact HE_ot16.
  - rewrite Etop. exact HE_top.
  - exact HCHAIN.
  - exact HPRESENT.
  - exact HZB.
  - right; right; right. exists LB. split; [exact Hin | apply Nat.le_succ_diag_r].
  - reflexivity.
  - exact HBOK.
  - split; [lia | lia].
  - left. lia.
  - (* room: the pieces of this call are a middle slice of the arm's pieces *)
    pose proof (wv_room_mid (wvc_st0 F) Pd ([LB] ++ Rest)) as HR.
    rewrite <- HWP in HR. change (WriterApp.w_text (wvc_st0 F)) with (wf_text0 F) in HR.
    assert (HL : (length LB <= length (concat ([LB] ++ Rest)))%nat)
      by (cbn [app concat]; rewrite length_app; lia).
    pose proof HE_room as HRM. unfold wvc_stP. lia.
  - exact HcapW.
  - lia.
  - (* budget: the entry's budget, split at this call *)
    pose proof HE_bud as HBUD0. rewrite HWP in HBUD0.
    pose proof (wv_budget_pre_mid S0 S (wf_cap0 F) (wf_cnt0 F) (wf_live F) (wf_failed0 F) (wf_text0 F)
      (wf_fail0 F) Pd ([LB] ++ Rest) HE_cap0 HBUD0 Hnev Hbb HCNT) as HMID.
    pose proof (wv_budget_pre_prefix S (WriterApp.w_cap (wvc_stP F Pd)) (WriterApp.w_cnt (wvc_stP F Pd))
      (wf_live F - wf_cap0 F + WriterApp.w_cap (wvc_stP F Pd))
      (WriterApp.w_failed (wvc_stP F Pd)) (WriterApp.w_text (wvc_stP F Pd)) (WriterApp.w_fail (wvc_stP F Pd))
      [LB] Rest ltac:(lia) HMID) as HPRE2.
    rewrite WriterApp.putN_cons, WriterApp.putN_nil in HPRE2.
    destruct HPRE2 as (A1 & A2 & A3 & A4).
    split; [exact A1|]. split; [exact A2|]. split; [lia | exact A4]. }
(* the post: the callee's pieces are this call's slice *)
cbv beta. intros W' c' Hle (st' & buf' & U' & Est & HUS' & HWPOST).
assert (Estc : st' = WriterApp.putN (wv_rst (wvc_stP F Pd)) [LB])
  by (rewrite Est, WriterApp.putN_cons, WriterApp.putN_nil; reflexivity).
rewrite Estc in HWPOST.
unfold wpost, fpostU in HWPOST.
destruct HWPOST as (ly' & S'' & regs' & mem' & md' & Ec & HJc & OK' & PO' & HP &
  (HOUT' & HBK' & HBS' & HWK' & HGL' & _)).
(* the loop invariant at the return point *)
destruct (wvc_ret_inv B HSS F ly0 S0 U0 W0 mem0 md0 regs0 HE_sp16 HE_oot HE_top HE_top47 HE_lo HE_cap0 HE_cnt0
  HE_p HE_d HE_dd HE_bud HE_ty HE_hdr HE_n HE_kk
  r2 i2 Pd [LB] Rest ly S U W memC mdC buf regsC R0 ke key STK_put peak ly' S'' U' W' regs' mem' md' buf'
  HWP HJ HARU HSEM Hpk HCH HR09 Hsp Hc8 Hc9 Hc19 Hc21 Hc25 Hc22 Hc3 Hc4 Hc18 Hc20 Hc23 Hc24 Hc26 Hc27 Hi2
  HJc OK' PO' HP HSKp HSP HUS' HOUT' HBK' HBS' HWK' HGL') as (key' & HINV').
rewrite Ec, Hc1.
exact (K ly' S'' U' W' regs' mem' md' buf' key' HINV').
Qed.

(* ================= (1) the key's put_string returned: the put of ':' / ': ' (return 0x84068) ================= *)
Lemma wvc_key_sep : forall i ke key Pd Rest ly S U (W : world tfibsegs) ms mdc buf
    (Q : world tfibsegs -> config -> Prop),
  put_spec B tfibsegs -> fs_img_facts tfibsegs B ->
  wf_ty F = 6 ->
  wvc_WP F = Pd ++ [WriterValue.wsep (negb (wf_p F =? 0))] ++ Rest ->
  wvc_inv B F WVC_R_KEY i ke key Pd ly0 S0 U0 W0 mem0 md0 regs0 W ms mdc ly S U buf ->
  (forall ly' S' U' (W' : world tfibsegs) regs' mem' md' buf' key',
     wvc_inv B F WVC_R_SEP i ke key' (Pd ++ [WriterValue.wsep (negb (wf_p F =? 0))])
       ly0 S0 U0 W0 mem0 md0 regs0
       W' (mkst regs' (Z_to_bv 64 WVC_R_SEP) mem' (seg_rom tfibsegs)) md' ly' S' U' buf' ->
     SRr tfibsegs W' (cfg_at tfibsegs WVC_R_SEP regs' mem' md') Q) ->
  SRr tfibsegs W (mkCfg ms mdc) Q.
Proof.
intros i ke key Pd Rest ly S U W ms mdc buf Q HPUT IMG Hty HWP HINV K.
unfold wvc_inv in HINV. cbv zeta in HINV.
destruct HINV as (HAT & HSEM & R8 & R9 & R19 & R21 & R25 & R3 & R4 & R18 & R20 & R22 & R23 & R24 & R26 & R27 &
  Hsp & Hi & Eke).
pose proof (wvc_stk (wf_m F)) as (HSF & _).
pose proof (wvc_sem_o_sp B F ly0 S0 U0 W0 mem0 regs0 ly S U W (ms_mem ms) buf _ HSEM) as Hosp.
destruct wvc_sep_str as (Hin & Hlen & Hhi).
rewrite Hty in HAT.
eapply (wvc_seg_key B W ms mdc _ _ _ _ (wf_sp F)).
- exact HAT.
- rewrite (ew_Ereg_nat (ms_regs ms) _ 2%nat 2%bv eq_refl). exact Hsp.
- lia.
- unfold wvc_STK. lia.
- intros ms' mdc' Ems' HJ' HARU' HFR HCH' G1 G10 G11 G12 G2 GK.
  assert (Ecfg : mkCfg ms' mdc' = cfg_at tfibsegs A_put (ms_regs ms') (ms_mem ms') mdc')
    by (unfold cfg_at; rewrite <- Ems'; reflexivity).
  rewrite Ecfg.
  assert (HSEM' : wvc_sem B F ly0 S0 U0 W0 mem0 regs0 ly S U W (ms_mem ms') buf (wvc_stP F Pd)).
  { apply (wvc_sem_run B F ly0 S0 U0 W0 mem0 regs0 ly S U W (ms_mem ms) (ms_mem ms') mdc' buf _ HSEM HARU' HFR);
      [lia | lia | lia]. }
  apply (wvc_put_step (wvc_sep (wf_p F)) (WriterValue.wsep (negb (wf_p F =? 0))) Pd Rest i WVC_R_SEP
    ly S U W (ms_mem ms') mdc' (ms_regs ms') (ms_regs ms) ke key buf Q HPUT IMG Hin ltac:(lia) HWP
    HJ' HARU' HSEM' HCH' R9);
    [ unfold WVC_R_SEP; lia
    | unfold YK0s.ret_ok, WVC_R_SEP; apply bv_eq; vm_compute; reflexivity
    | exact G1
    | rewrite G10, (ew_Ereg_nat (ms_regs ms) _ 8%nat 8%bv eq_refl); exact R8
    | exact G11
    | rewrite Hlen; exact G12
    | unfold spZ; rewrite G2; exact Hsp
    | rewrite (GK 8%bv ltac:(wvc_inq)); exact R8
    | rewrite (GK 9%bv ltac:(wvc_inq)); exact R9
    | rewrite (GK 19%bv ltac:(wvc_inq)); exact R19
    | rewrite (GK 21%bv ltac:(wvc_inq)); exact R21
    | rewrite (GK 25%bv ltac:(wvc_inq)); exact R25
    | rewrite (GK 22%bv ltac:(wvc_inq)); exact R22
    | rewrite (GK 3%bv ltac:(wvc_inq)); exact R3
    | rewrite (GK 4%bv ltac:(wvc_inq)); exact R4
    | rewrite (GK 18%bv ltac:(wvc_inq)); exact R18
    | rewrite (GK 20%bv ltac:(wvc_inq)); exact R20
    | rewrite (GK 23%bv ltac:(wvc_inq)); exact R23
    | rewrite (GK 24%bv ltac:(wvc_inq)); exact R24
    | rewrite (GK 26%bv ltac:(wvc_inq)); exact R26
    | rewrite (GK 27%bv ltac:(wvc_inq)); exact R27
    | exact Hi
    | ].
  intros ly' S' U' W' regs' mem' md' buf' key' HINV2.
  apply (K ly' S' U' W' regs' mem' md' buf' key'). rewrite Eke. exact HINV2.
Qed.

(* ================= (2) the item's write_value returned, another item follows: the put of ',' (0x83ffc) ========= *)
Lemma wvc_item_comma : forall i ke key Pd Rest ly S U (W : world tfibsegs) ms mdc buf
    (Q : world tfibsegs -> config -> Prop),
  put_spec B tfibsegs -> fs_img_facts tfibsegs B ->
  i + 1 < wf_n F ->
  wvc_WP F = Pd ++ [[44]] ++ Rest ->
  wvc_inv B F WVC_R_ITEM i ke key Pd ly0 S0 U0 W0 mem0 md0 regs0 W ms mdc ly S U buf ->
  (forall ly' S' U' (W' : world tfibsegs) regs' mem' md' buf' key',
     wvc_inv B F WVC_R_COMMA (i + 1) (wf_keys F + 8 * (i + 1)) key' (Pd ++ [[44]])
       ly0 S0 U0 W0 mem0 md0 regs0
       W' (mkst regs' (Z_to_bv 64 WVC_R_COMMA) mem' (seg_rom tfibsegs)) md' ly' S' U' buf' ->
     SRr tfibsegs W' (cfg_at tfibsegs WVC_R_COMMA regs' mem' md') Q) ->
  SRr tfibsegs W (mkCfg ms mdc) Q.
Proof.
intros i ke key Pd Rest ly S U W ms mdc buf Q HPUT IMG Hin1 HWP HINV K.
unfold wvc_inv in HINV. cbv zeta in HINV.
destruct HINV as (HAT & HSEM & R8 & R9 & R19 & R21 & R25 & R3 & R4 & R18 & R20 & R22 & R23 & R24 & R26 & R27 &
  Hsp & Hi & Eke).
pose proof (wvc_stk (wf_m F)) as (HSF & _).
pose proof (wvc_sem_o_sp B F ly0 S0 U0 W0 mem0 regs0 ly S U W (ms_mem ms) buf _ HSEM) as Hosp.
pose proof HE_kk as (Hk1 & Hk2 & Hk3 & Hk4).
eapply (wvc_seg_item_next B W ms mdc _ _ _ i (wf_n F) (wf_keys F) _ _ (wf_sp F)).
- exact HAT.
- destruct HE_ty as [(Hty & _) | (Hty & _)]; [left | right]; exact Hty.
- rewrite (ew_Ereg_nat (ms_regs ms) _ 21%nat 21%bv eq_refl). exact R21.
- rewrite (ew_Ereg_nat (ms_regs ms) _ 25%nat 25%bv eq_refl). exact R25.
- rewrite fsw_ew_xatom. cbn [wvc_xs wvc_saved map app nth]. reflexivity.
- rewrite fsw_ew_xatom. cbn [wvc_xs wvc_saved map app nth]. reflexivity.
- rewrite fsw_ew_xatom. cbn [wvc_xs wvc_saved map app nth]. rewrite Eke. reflexivity.
- lia.
- exact Hin1.
- lia.
- exact Hk3.
- exact Hk4.
- rewrite (ew_Ereg_nat (ms_regs ms) _ 2%nat 2%bv eq_refl). exact Hsp.
- lia.
- unfold wvc_STK. lia.
- intros ms' mdc' Ems' HJ' HARU' HFR HCH' G1 G10 G11 G12 G21 G22 G25 G2 GK.
  assert (Ecfg : mkCfg ms' mdc' = cfg_at tfibsegs A_put (ms_regs ms') (ms_mem ms') mdc')
    by (unfold cfg_at; rewrite <- Ems'; reflexivity).
  rewrite Ecfg.
  assert (HSEM' : wvc_sem B F ly0 S0 U0 W0 mem0 regs0 ly S U W (ms_mem ms') buf (wvc_stP F Pd)).
  { apply (wvc_sem_run B F ly0 S0 U0 W0 mem0 regs0 ly S U W (ms_mem ms) (ms_mem ms') mdc' buf _ HSEM HARU' HFR);
      [lia | lia | lia]. }
  apply (wvc_put_step WVC_COMMA [44] Pd Rest (i + 1) WVC_R_COMMA
    ly S U W (ms_mem ms') mdc' (ms_regs ms') (ms_regs ms) ke key buf Q HPUT IMG wvc_in_comma
    ltac:(unfold WVC_COMMA, SHADOW_OFF; cbn [length Z.of_nat]; lia) HWP
    HJ' HARU' HSEM' HCH' R9);
    [ unfold WVC_R_COMMA; lia
    | unfold YK0s.ret_ok, WVC_R_COMMA; apply bv_eq; vm_compute; reflexivity
    | exact G1
    | rewrite G10, (ew_Ereg_nat (ms_regs ms) _ 8%nat 8%bv eq_refl); exact R8
    | exact G11
    | cbn [length Z.of_nat]; exact G12
    | unfold spZ; rewrite G2; exact Hsp
    | rewrite (GK 8%bv ltac:(wvc_inq)); exact R8
    | rewrite (GK 9%bv ltac:(wvc_inq)); exact R9
    | rewrite (GK 19%bv ltac:(wvc_inq)); exact R19
    | exact G21
    | exact G25
    | exact G22
    | rewrite (GK 3%bv ltac:(wvc_inq)); exact R3
    | rewrite (GK 4%bv ltac:(wvc_inq)); exact R4
    | rewrite (GK 18%bv ltac:(wvc_inq)); exact R18
    | rewrite (GK 20%bv ltac:(wvc_inq)); exact R20
    | rewrite (GK 23%bv ltac:(wvc_inq)); exact R23
    | rewrite (GK 24%bv ltac:(wvc_inq)); exact R24
    | rewrite (GK 26%bv ltac:(wvc_inq)); exact R26
    | rewrite (GK 27%bv ltac:(wvc_inq)); exact R27
    | lia
    | ].
  intros ly' S' U' W' regs' mem' md' buf' key' HINV2.
  exact (K ly' S' U' W' regs' mem' md' buf' key' HINV2).
Qed.

End A.
