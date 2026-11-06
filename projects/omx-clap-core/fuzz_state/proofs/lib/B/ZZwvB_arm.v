(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACer.v, with its module paths and module names changed; 1338 of its 1373 lines of code are new or changed and 261 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_K.v; 1536 of its 1692 lines of code are new or changed and 1217 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_write_value.v, with its module names changed; 222 of its 422 lines of code are new or changed and 1492 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/ZZwv_cps.v, with its module paths and module names changed; 614 of its 685 lines of code are new or changed and 351 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: the CALL GLUE of the lib/B (fs.asan-ubsan) container arms of write_value:
   the four call steps of the item loop (put of a literal, indent, put_string of an object key, the recursive
   write_value of an item), each from the facts the engine run of ZZwvB_runs1 / ZZwvB_runs2 left at the call to the
   loop invariant (ZZwvB_inv.wvc_inv) at the callee's return address, through ZZwvB_call3.wvc_callpre (the callee's
   fpreU and the one-node frame chain at s0 = o) and ZZwvB_step.wvc_ret_inv (the return).
   Image A has no twin of this file: its container arms are unproved (wv_arr / wv_obj are hypotheses of
   lib/A/FSW_write_value.v); the pieces it does have are mirrored in ZZwvB_*.v with A's names.
   rule 24: proves no function (kind: segment lemma) - call steps of the container arms of write_value B.
   Rule 24 (proof-index, a Theorem Labs lane, unpiped): write_value has RELEASED proofs for fs's PLAIN and UBSAN
   builds only (lib/Prog, lib/U/Prog), none for an ASan image; 0x84010 is not in the released set. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSPstat FSW_K FSW_K3 FSW_rres FSW_ret FSW_rd FSW_pj FSH_Fn_writer
FSW_write_value_entry ZZwvB_defs ZZwvB_comp ZZwvB_kit ZZwvB_tree ZZwvB_inv ZZwvB_call ZZwvB_call2 ZZwvB_call3
ZZwvB_ret ZZwvB_res ZZwvB_runs1 ZZwvB_runs2 ZZwvB_step.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require FSH_Fn_reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec WriterApp WriterValue PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance
   resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

Section A. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis HSS : FsShadowSyms B.
Hypothesis IMG : fs_img_facts tfibsegs B.
Hypothesis HPUT : put_spec B tfibsegs.
Hypothesis HPS : put_string_spec B tfibsegs.
Hypothesis HIND : indent_spec B tfibsegs.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
(* ================= the pieces the arm writes, by point of the loop ================= *)
(* the first put's piece, the closing put's piece *)
Definition wvc_POPEN (F : wvc_fix) : list (list Z) := [if wf_ty F =? 6 then [123] else [91]].
Definition wvc_PCLOSE (F : wvc_fix) : list (list Z) := [if wf_ty F =? 6 then [125] else [93]].
Definition wvc_pp (F : wvc_fix) : bool := negb (wf_p F =? 0).
(* the pieces at the per-item resume points, for the two arms (ZZwvB_tree's wv_items / wv_mems) *)
Definition wvc_PIND_arr (F : wvc_fix) (items : list PjTree.jv) (j : nat) : list (list Z) :=
  wvc_POPEN F ++ wv_items (wvc_pp F) (wf_d F) 0%nat (firstn j items)
  ++ WriterValue.wcomma j ++ WriterValue.wind (wvc_pp F) (wf_d F + 1).
Definition wvc_PITEM_arr (F : wvc_fix) (items : list PjTree.jv) (j : nat) : list (list Z) :=
  wvc_POPEN F ++ wv_items (wvc_pp F) (wf_d F) 0%nat (firstn (S j) items).
Definition wvc_PIND_obj (F : wvc_fix) (ms : list (list Z * PjTree.jv)) (j : nat) : list (list Z) :=
  wvc_POPEN F ++ wv_mems (wvc_pp F) (wf_d F) 0%nat (firstn j ms)
  ++ WriterValue.wcomma j ++ WriterValue.wind (wvc_pp F) (wf_d F + 1).
Definition wvc_PKEY_obj (F : wvc_fix) (ms : list (list Z * PjTree.jv)) (j : nat) (nm : list Z) : list (list Z) :=
  wvc_PIND_obj F ms j ++ WriterSpec.spieces nm.
Definition wvc_PSEP_obj (F : wvc_fix) (ms : list (list Z * PjTree.jv)) (j : nat) (nm : list Z) : list (list Z) :=
  wvc_PKEY_obj F ms j nm ++ [WriterValue.wsep (wvc_pp F)].
Definition wvc_PITEM_obj (F : wvc_fix) (ms : list (list Z * PjTree.jv)) (j : nat) : list (list Z) :=
  wvc_POPEN F ++ wv_mems (wvc_pp F) (wf_d F) 0%nat (firstn (S j) ms).

(* ---- the loop's return addresses (MEASURED, ZZwvB_defs.WV_CONT_RAS): each is an even code address above 4096,
   which is what a callee's fpreU asks of ra (YK0s.ret_ok and 4096 <= raZ) ---- *)
Lemma wvc_ras_ok : forall r, In r WV_CONT_RAS -> 4096 <= r < 2 ^ 64 /\ r mod 2 = 0.
Proof.
intros r Hin. unfold WV_CONT_RAS in Hin. cbn [In] in Hin.
repeat (destruct Hin as [<- | Hin]; [split; [split|]; vm_compute; first [reflexivity | discriminate]|]).
destruct Hin.
Qed.

(* ---- every read-only string of FS_RO_STRS lies in fs's image, far below the shadow band: the literals the arms
   put are .rodata bytes, where the machine memory and the UNPOISONED one agree ---- *)
Lemma wvc_ro_low : forall p, In p FS_RO_STRS ->
  4096 <= fst p /\ fst p + Z.of_nat (length (snd p)) + 8 <= SHADOW_OFF.
Proof.
intros p Hin. unfold FS_RO_STRS in Hin. cbn [In] in Hin.
repeat (destruct Hin as [<- | Hin]; [split; vm_compute; discriminate|]). destruct Hin.
Qed.

(* ---- the bytes of a read-only literal at the RAW machine memory. ZZwvB_inv.wvc_lit_pre reads them off the
   UNPOISONED memory (the form fs_img_facts takes); below SHADOW_OFF the two memories are the same byte for byte
   (ZZwvB_kit.zwk_j_mrestrict_low), and put's wsrc_kept arm for a table entry is memory-free. ---- *)
Lemma wvc_lit_raw : forall ly S U (W : world tfibsegs) m md (s : Z) (bs : list Z),
  ARU tfibsegs B ly S U W m md ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) m) ->
  In (s, bs) FS_RO_STRS ->
  zbytes_at tfibsegs W m s bs /\ WriterSpec.bytes_ok bs /\
  4096 <= s /\ s + Z.of_nat (length bs) <= alloc_ceiling.
Proof.
intros ly S U W m md s bs HARU HRO Hin.
destruct (wvc_ro_low (s, bs) Hin) as (Hlo & Hhi). cbn [fst snd] in Hlo, Hhi.
destruct (wvc_lit_pre B ly S U W (unpoison U m) md s bs 0 IMG (proj1 HARU)
  (proj1 (zwk_j_arodata_unpoison B ly S U W m md HARU) HRO) Hin) as (HZ & HBO & _ & H1 & H2).
split; [|split; [exact HBO | split; [exact H1 | exact H2]]].
unfold zbytes_at in HZ |- *.
apply (garr8_frame tfibsegs _ _ s bs HZ).
intros a Ha. unfold mbyte.
rewrite (zwk_j_mrestrict_low B ly S U W m md (w_H W) a HARU ltac:(lia)). reflexivity.
Qed.

Section St.
(* the arm instance: its fixed data and the entry state, as ZZwvB_step's Section (the hypotheses are that file's,
   word for word, so they pass straight through to wvc_ret_inv) *)
Variable F : wvc_fix.
Variables (ly0 : alayout) (S0 : astate) (U0 : list (Z * Z)) (W0 : world tfibsegs) (mem0 : word -> option byte)
  (md0 : Model) (regs0 : bvmap 5 word).
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
Hypothesis HE_kk : 0 < wf_n F -> 4096 <= wf_kids F /\ wf_kids F + 56 * wf_n F <= alloc_ceiling /\
                   (wf_ty F = 6 -> 4096 <= wf_keys F /\ wf_keys F + 8 * wf_n F <= alloc_ceiling).

(* ---- the invariant at the CLOSE point (after the closing indent, state wvc_ssN: the node alone) ---- *)
Definition wvc_invN (P : list (list Z))
    (W : world tfibsegs) (ms : machine_state) (mdc : Model)
    (ly : alayout) (S : astate) (U : list (Z * Z)) (buf : Z) : Prop :=
  let st := wvc_stP F P in
  let E := Ereg (ms_regs ms)
             (fs_extraT ++ wvc_xs regs0 (wf_str F) (wf_kids F) (wf_keys F) (wf_n F) (wf_d F)
                (wf_keys F + 8 * wf_n F) 0) in
  wvc_at B E (wvc_ssN (wf_ty F) (wf_p F)) wvc_SH0 W ms (wvc_STK F) (wf_ot F) (wvc_FP F)
    ly0 S0 W0 (unpoison U0 mem0) md0 [] ly S U mdc (wevk (wf_cap0 F) st) /\
  wvc_sem B F ly0 S0 U0 W0 mem0 regs0 ly S U W (ms_mem ms) buf st /\
  YK11.getr (ms_regs ms) 8%bv = w64 (wf_o F) /\
  YK11.getr (ms_regs ms) 9%bv = w64 (wf_v F) /\
  YK11.getr (ms_regs ms) 19%bv = w64 (wf_p F) /\
  YK11.getr (ms_regs ms) 3%bv = YK11.getr regs0 3%bv /\
  YK11.getr (ms_regs ms) 4%bv = YK11.getr regs0 4%bv /\
  spZ (ms_regs ms) = wf_sp F - WVC_F.

(* ---- the entry ra, read back from the frame slot 184 (the prologue's `sd ra,184(sp)`): the ONE-NODE chain clause
   of the writer specs needs the word at o - 16 when o = sp + 8 (ZZwvB_call3.wvc_callpre's side condition) ---- *)
Lemma wvc_ra8_frame : forall E (W : world tfibsegs) m p,
  Forall (YP09.chunk_ok tfibsegs E (rdW W m) (wf_sp F - WVC_F)) wvc_cs0 ->
  ew E (xatom 17) = Z_to_bv 64 p -> 0 <= p < 2 ^ 64 ->
  val_mem tfibsegs (rdW W m) (wf_sp F - 8) 8 p.
Proof.
intros E W m p HCS Hx Hp.
assert (Hc : In (YP09.mkChunk 184 (CVal 8 (SOff (xatom 17) 0))) wvc_cs0).
{ unfold wvc_cs0. apply in_or_app. right. apply in_map_iff. exists 12%nat.
  split; [reflexivity | apply in_seq; lia]. }
pose proof (proj1 (Forall_forall _ _) HCS _ Hc) as Hck.
replace (wf_sp F - 8) with (wf_sp F - WVC_F + 184) by (unfold WVC_F; lia).
refine (val_of_chunk_ok tfibsegs E (rdW W m) (wf_sp F - WVC_F) 184 8 (SOff (xatom 17) 0) p Hck _ _ _).
- rewrite fsw_SOff0. exact Hx.
- replace (8 * Z.of_N 8) with 64 by reflexivity. exact Hp.
- vm_compute. discriminate.
Qed.

(* ---- the same word as the writer specs' chain clause reads it, on the unpoisoned memory (a stack byte is never a
   user-poisoned shadow byte: ZZwvB_kit.zwk_p_stack_not_ush) ---- *)
Lemma wvc_ra_word : forall (regsC : bvmap 5 word) ke key ly S U (W : world tfibsegs) memC mdC buf st,
  ARU tfibsegs B ly S U W memC mdC ->
  Forall (YP09.chunk_ok tfibsegs (wvc_E F regs0 regsC ke key) (rdW W memC) (wf_sp F - WVC_F)) (wvc_csL (wf_p F)) ->
  wvc_sem B F ly0 S0 U0 W0 mem0 regs0 ly S U W memC buf st ->
  rdword (aview tfibsegs (w_H W) (unpoison U memC)) (wf_sp F - 8) = Some (raZ regs0).
Proof.
intros regsC ke key ly S U W memC mdC buf st HARU HCH HSEM.
pose proof (wvc_stk (wf_m F)) as (HF & _).
pose proof (wvc_sem_o_sp B F ly0 S0 U0 W0 mem0 regs0 ly S U W memC buf st HSEM) as Hosp.
pose proof HSEM as (HOUT & _). pose proof HOUT as (_ & Ho0 & Hotop & _).
assert (Hra : 0 <= raZ regs0 < 2 ^ 64) by (unfold raZ; apply u64_range).
assert (HCS : Forall (YP09.chunk_ok tfibsegs (wvc_E F regs0 regsC ke key) (rdW W memC) (wf_sp F - WVC_F)) wvc_cs0).
{ unfold wvc_csL in HCH. cbn [app] in HCH. do 6 (apply Forall_inv_tail in HCH). exact HCH. }
assert (Hval : val_mem tfibsegs (rdW W memC) (wf_sp F - 8) 8 (raZ regs0)).
{ apply (wvc_ra8_frame (wvc_E F regs0 regsC ke key) W memC (raZ regs0) HCS); [|exact Hra].
  rewrite (wvc_E_x F regs0 regsC ke key 17%nat).
  cbn [nth wvc_xs wvc_saved app map]. unfold raZ. rewrite Z_to_bv_bv_unsigned. reflexivity. }
assert (HK : forall k, 0 <= k < 8 ->
  aview tfibsegs (w_H W) (unpoison U memC) (wf_sp F - 8 + k) = aview tfibsegs (w_H W) memC (wf_sp F - 8 + k)).
{ intros k Hk. apply aview_unpoison_out.
  apply (zwk_p_stack_not_ush B ly S U W memC mdC (wf_sp F - 8 + k) HARU).
  unfold WVC_F in *. split; [lia|]. pose proof HE_top. pose proof HE_top47. lia. }
rewrite (rdword_ext (aview tfibsegs (w_H W) memC) (aview tfibsegs (w_H W) (unpoison U memC)) (wf_sp F - 8) HK).
exact (YF0x.val_mem_rdword (w_H W) memC (wf_sp F - 8) (raZ regs0) Hra Hval).
Qed.

(* ---- the premises EVERY loop callee shares at a call from the item loop: its fpreU with the one-node frame chain
   at s0 = o (ZZwvB_call3.wvc_callpre), the window's presence, and the three facts the journal carries over from the
   arm's entry (the layout top, the frame list, the stack bounds) ---- *)
Lemma wvc_call_facts : forall Pd r2 (regsC : bvmap 5 word) ke key ly S U (W : world tfibsegs) memC mdC buf STKc,
  ajournal tfibsegs B (wvc_STK F) (wf_ot F) (wvc_FP F) ly0 S0 W0 (unpoison U0 mem0) md0 []
    ly S W (unpoison U memC) mdC (wevk (wf_cap0 F) (wvc_stP F Pd)) ->
  ARU tfibsegs B ly S U W memC mdC ->
  wvc_sem B F ly0 S0 U0 W0 mem0 regs0 ly S U W memC buf (wvc_stP F Pd) ->
  Forall (YP09.chunk_ok tfibsegs (wvc_E F regs0 regsC ke key) (rdW W memC) (wf_sp F - WVC_F)) (wvc_csL (wf_p F)) ->
  spZ regsC = wf_sp F - WVC_F ->
  YK11.getr regsC 1%bv = w64 r2 -> In r2 WV_CONT_RAS ->
  YK11.getr regsC 8%bv = w64 (wf_o F) ->
  YK11.getr regsC 3%bv = YK11.getr regs0 3%bv -> YK11.getr regsC 4%bv = YK11.getr regs0 4%bv ->
  0 <= STKc -> STKc + WVC_F <= STK_write_value (wf_m F) ->
  exists ch,
    fpreU tfibsegs B STKc ly S U W regsC memC mdC ch /\
    wv_chain_o U W memC regsC (wf_o F) /\
    (forall a, spZ regsC <= a < wf_ot F -> apresent (w_H W) memC a) /\
    s0Z regsC = wf_o F /\ wf_ot F <= ly_top ly /\
    Z.of_nat (length (frames S)) <= FRL_CRT_CALLEE /\
    alloc_ceiling <= wf_sp F - WVC_F /\ wf_sp F + 8 <= wf_o F.
Proof.
intros Pd r2 regsC ke key ly S U W memC mdC buf STKc HJ HARU HSEM HCH Hsp R1 Hin R8 R3 R4 HSTK0 HSTK.
pose proof (wvc_stk (wf_m F)) as (HF & _).
pose proof (wvc_sem_o_sp B F ly0 S0 U0 W0 mem0 regs0 ly S U W memC buf (wvc_stP F Pd) HSEM) as Hosp.
pose proof HSEM as (HOUT & _). pose proof HOUT as (_ & Ho0 & Hotop & _).
destruct (wvc_ras_ok r2 Hin) as (Hr2a & Hr2b).
assert (Hlo : alloc_ceiling <= wf_sp F - WVC_F) by (unfold WVC_F in *; lia).
assert (Hra : raZ regsC = r2).
{ unfold raZ. rewrite R1. unfold w64. apply unsigned_lit_small. lia. }
assert (Hs0 : s0Z regsC = wf_o F).
{ unfold s0Z. rewrite R8. unfold w64. apply unsigned_lit_small.
  pose proof HE_top. pose proof HE_top47. lia. }
assert (Htop : wf_ot F <= ly_top ly).
{ pose proof HJ as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
  rewrite Etop. exact HE_top. }
assert (HFRL : Z.of_nat (length (frames S)) <= FRL_CRT_CALLEE).
{ pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _). rewrite Hfrs. cbn [app]. exact HE_frl. }
destruct (wvc_callpre B F ly0 S0 U0 W0 mem0 md0 regs0 ly S U W memC mdC _ buf (wvc_stP F Pd) regsC STKc
  HJ HARU HSEM
  (fun _ => wvc_ra_word regsC ke key ly S U W memC mdC buf (wvc_stP F Pd) HARU HCH HSEM)
  Hsp HE_sp16 HE_ot16 ltac:(lia) HSTK0 HSTK
  ltac:(apply ret_ok_even; rewrite R1; unfold w64; rewrite unsigned_lit_small by lia; exact Hr2b)
  ltac:(rewrite Hra; lia) ltac:(rewrite R3; exact HE_gp) ltac:(rewrite R4; exact HE_tp) Hs0 HE_oot Htop HE_o8 Hlo)
  as (ch & _ & HPRE & HCHO & HPRES).
exists ch. split; [exact HPRE|]. split; [exact HCHO|]. split; [exact HPRES|].
split; [exact Hs0|]. split; [exact Htop|]. split; [exact HFRL|]. split; [exact Hlo | lia].
Qed.

(* ---- the callee's budget at a mid-walk call: the arm's own budget, split at the pieces written so far
   (ZZwvB_comp.wv_budget_pre_prefix / wv_budget_pre_mid, with the journal's event count and the kept block bytes) ---- *)
Lemma wvc_bud_mid : forall Pd Pc Rest ly S U (W : world tfibsegs) memC mdC buf,
  wvc_WP F = Pd ++ Pc ++ Rest ->
  ajournal tfibsegs B (wvc_STK F) (wf_ot F) (wvc_FP F) ly0 S0 W0 (unpoison U0 mem0) md0 []
    ly S W (unpoison U memC) mdC (wevk (wf_cap0 F) (wvc_stP F Pd)) ->
  wvc_sem B F ly0 S0 U0 W0 mem0 regs0 ly S U W memC buf (wvc_stP F Pd) ->
  wbudget_pre S (WriterApp.w_cap (wvc_stP F Pd)) (WriterApp.w_cnt (wvc_stP F Pd))
    (wf_live F + WriterApp.w_cap (wvc_stP F Pd) - wf_cap0 F)
    (WriterApp.putN (wv_rst (wvc_stP F Pd)) Pc).
Proof.
intros Pd Pc Rest ly S U W memC mdC buf HWP HJ HSEM.
pose proof HSEM as (_ & _ & _ & _ & _ & HBK & HCNT & _).
assert (HBUDall : wbudget_pre S0 (wf_cap0 F) (wf_cnt0 F) (wf_live F)
  (WriterApp.putN (WriterApp.mkW (wf_failed0 F) (wf_text0 F) (wf_cap0 F) (wf_cnt0 F) (wf_fail0 F) [])
     (Pd ++ Pc))).
{ apply (wv_budget_pre_prefix S0 (wf_cap0 F) (wf_cnt0 F) (wf_live F) (wf_failed0 F) (wf_text0 F) (wf_fail0 F)
    (Pd ++ Pc) Rest HE_cap0).
  rewrite <- app_assoc, <- HWP. exact HE_bud. }
replace (wf_live F + WriterApp.w_cap (wvc_stP F Pd) - wf_cap0 F)
  with (wf_live F - wf_cap0 F + WriterApp.w_cap (wvc_stP F Pd)) by lia.
refine (wv_budget_pre_mid S0 S (wf_cap0 F) (wf_cnt0 F) (wf_live F) (wf_failed0 F) (wf_text0 F) (wf_fail0 F)
  Pd Pc HE_cap0 HBUDall _ _ _).
- pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & _). exact Hnev.
- exact (proj1 (proj2 HBK)).
- exact HCNT.
Qed.

(* ---- the callee's room premise at a mid-walk call: the arm's own room, split the same way (ZZwvB_comp.wv_room_mid) ---- *)
Lemma wvc_room_mid : forall Pd Pc Rest,
  wvc_WP F = Pd ++ Pc ++ Rest ->
  Z.of_nat (length (WriterApp.w_text (wvc_stP F Pd))) + Z.of_nat (length (concat Pc)) + 1 <= WMAX.
Proof.
intros Pd Pc Rest HWP.
pose proof (wv_room_mid (wvc_st0 F) Pd (Pc ++ Rest)) as HR.
rewrite <- HWP in HR. rewrite concat_app, length_app in HR.
cbn [WriterApp.w_text wvc_st0] in HR.
pose proof HE_room as HRM. unfold wvc_stP. lia.
Qed.

(* ---- the container's kids block at a call: one of the tree's live reader blocks, with room for every item ---- *)
Lemma wvc_kids_blk : forall ly S U (W : world tfibsegs) memC mdC buf st,
  ARU tfibsegs B ly S U W memC mdC ->
  wvc_sem B F ly0 S0 U0 W0 mem0 regs0 ly S U W memC buf st ->
  0 < wf_n F ->
  exists cap, wf_n F <= cap /\ In (wf_kids F, 56 * cap) (wf_D F).
Proof.
intros ly S U W memC mdC buf st HARU HSEM Hn0.
pose proof HSEM as (_ & _ & _ & _ & _ & _ & _ & _ & HN & _).
destruct (wvc_hdr_at B F ly0 S0 U0 W0 mem0 regs0 HE_hdr ly S U W memC buf st HSEM) as (num & capn & HHDR).
pose proof HHDR as (_ & _ & _ & _ & Hk1 & _).
destruct HE_ty as [(Hty & items & Ht & Hn & _) | (Hty & members & Ht & Hn)].
- destruct items as [|u0 items]; [rewrite Hn in Hn0; cbn [length] in Hn0; lia|].
  rewrite Ht in HN.
  destruct (wv_arr_item (rdW W memC) (fun a k => In (a, k) (wf_UL F)) (wf_v F) (u0 :: items) (wf_D F) 0%nat u0
    HN eq_refl) as (num2 & kids2 & n2 & cap2 & Di & Dpre & Du0 & Dpost & HH2 & En2 & Hnc & Hc2 & Hlk & ED & _ & _
    & _ & _).
  pose proof HH2 as (_ & _ & _ & _ & Hk2 & _).
  assert (Ekids : kids2 = wf_kids F) by exact (PjStruct.pj_u64_uniq _ _ _ _ _ Hk2 Hk1).
  exists cap2. split; [rewrite Hn, <- En2; exact Hnc|].
  rewrite ED, <- Ekids. left. reflexivity.
- destruct members as [|m0 members]; [rewrite Hn in Hn0; cbn [length] in Hn0; lia|].
  rewrite Ht in HN. destruct m0 as (nm0 & u0).
  destruct (wv_obj_mem (rdW W memC) (fun a k => In (a, k) (wf_UL F)) (wf_v F) ((nm0, u0) :: members) (wf_D F)
    0%nat nm0 u0 HN eq_refl)
    as (num2 & kids2 & keys2 & n2 & cap2 & Di & Dpre & x0 & k0 & Du0 & Dpost & HH2 & En2 & Hnc & Hc2 & Hlk & Hlky
        & ED & _ & _ & _ & _ & _ & _ & _).
  pose proof HH2 as (_ & _ & _ & _ & Hk2 & _).
  assert (Ekids : kids2 = wf_kids F) by exact (PjStruct.pj_u64_uniq _ _ _ _ _ Hk2 Hk1).
  exists cap2. split; [rewrite Hn, <- En2; exact Hnc|].
  rewrite ED, <- Ekids. left. reflexivity.
Qed.

(* ================= the four call steps: from a resume point to the next ================= *)
(* Each takes the facts the engine run of ZZwvB_runs1 / ZZwvB_runs2 delivered at the call (the journal, ARU, the
   frame chunks, the registers), the model split of the arm's pieces, and the callee's own data; it discharges the
   callee's contract (HPUT / HIND / HPS / the level-indexed write_value) and returns the loop invariant at the
   callee's return address, by ZZwvB_step.wvc_ret_inv. *)

(* ---- put of a read-only literal (the open bracket, the separator, the comma) ---- *)
Lemma wvc_call_put : forall r2 i' Pd Pc Rest ly S U (W : world tfibsegs) regsC memC mdC buf s (bs : list Z)
    (Q : world tfibsegs -> config -> Prop),
  wvc_WP F = Pd ++ Pc ++ Rest -> Pc = [bs] ->
  ajournal tfibsegs B (wvc_STK F) (wf_ot F) (wvc_FP F) ly0 S0 W0 (unpoison U0 mem0) md0 []
    ly S W (unpoison U memC) mdC (wevk (wf_cap0 F) (wvc_stP F Pd)) ->
  ARU tfibsegs B ly S U W memC mdC ->
  wvc_sem B F ly0 S0 U0 W0 mem0 regs0 ly S U W memC buf (wvc_stP F Pd) ->
  Forall (YP09.chunk_ok tfibsegs (wvc_E F regs0 regsC (wf_keys F + 8 * i') 0) (rdW W memC) (wf_sp F - WVC_F))
    (wvc_csL (wf_p F)) ->
  spZ regsC = wf_sp F - WVC_F ->
  YK11.getr regsC 1%bv = w64 r2 -> In r2 WV_CONT_RAS ->
  YK11.getr regsC 10%bv = w64 (wf_o F) -> YK11.getr regsC 11%bv = w64 s ->
  YK11.getr regsC 12%bv = w64 (Z.of_nat (length bs)) ->
  YK11.getr regsC 8%bv = w64 (wf_o F) -> YK11.getr regsC 9%bv = w64 (wf_v F) ->
  YK11.getr regsC 19%bv = w64 (wf_p F) -> YK11.getr regsC 21%bv = w64 i' ->
  YK11.getr regsC 23%bv = w64 (56 * i') -> YK11.getr regsC 25%bv = w64 (8 * i') ->
  YK11.getr regsC 18%bv = w64 (wf_v F + 40) ->
  YK11.getr regsC 20%bv = w64 ((wf_v F + 24) / 8 + SHADOW_OFF) ->
  YK11.getr regsC 22%bv = w64 (wf_d F + 1) -> YK11.getr regsC 24%bv = w64 (wf_v F + 24) ->
  YK11.getr regsC 26%bv = w64 0 ->
  YK11.getr regsC 27%bv = w64 ((wf_v F + 40) / 8 + SHADOW_OFF) ->
  YK11.getr regsC 3%bv = YK11.getr regs0 3%bv -> YK11.getr regsC 4%bv = YK11.getr regs0 4%bv ->
  0 <= i' < wf_n F ->
  In (s, bs) FS_RO_STRS ->
  (forall W' ms2 mdc2 ly' S' U' buf' key', wle W W' ->
     wvc_inv B F r2 i' (wf_keys F + 8 * i') key' (Pd ++ Pc) ly0 S0 U0 W0 mem0 md0 regs0 W' ms2 mdc2 ly' S' U' buf' ->
     SRr tfibsegs W' (mkCfg ms2 mdc2) Q) ->
  SRr tfibsegs W (cfg_at tfibsegs A_put regsC memC mdC) Q.
Proof.
intros r2 i' Pd Pc Rest ly S U W regsC memC mdC buf s bs Q HWP HPc HJ HARU HSEM HCH Hsp R1 Hin R10 R11 R12
  R8 R9 R19 R21 R23 R25 R18 R20 R22 R24 R26 R27 R3 R4 Hi Hro K.
subst Pc.
pose proof (wvc_stk (wf_m F)) as (HF & HSKp & _).
assert (SKp0 : 0 <= STK_put) by (vm_compute; discriminate).
pose proof HSEM as (HOUT & HGL & HHD & HUS & HBS & HBK & HCNT & HWK & HN & HPO & HNB & HUL & HD & HROOT & HBIN &
  HB0 & HRO & H8 & HCch & HU0).
destruct HGL as (peak & Hpk & HGLOB).
pose proof (proj1 HARU) as HAR.
destruct (wvc_call_facts Pd r2 regsC (wf_keys F + 8 * i') 0 ly S U W memC mdC buf STK_put
  HJ HARU HSEM HCH Hsp R1 Hin R8 R3 R4 SKp0 ltac:(lia))
  as (ch & HPRE & HCHO & HPRES & Hs0 & Htop & HFRL & Hlo & Hosp).
destruct (wvc_lit_raw ly S U W memC mdC s bs HARU HRO Hro) as (HZB & HBO & Hs1 & Hs2).
pose proof (wvc_room_mid Pd [bs] Rest HWP) as HROOM.
cbn [concat] in HROOM. rewrite app_nil_r in HROOM.
pose proof (wvc_bud_mid Pd [bs] Rest ly S U W memC mdC buf HWP HJ HSEM) as HBUDc.
eapply SRr_bind.
{ apply (HPUT ly S U W regsC memC mdC ch (wf_ot F) (wf_o F) s (Z.of_nat (length bs)) buf
    (WriterApp.w_cap (wvc_stP F Pd)) (WriterApp.w_failed (wvc_stP F Pd)) (WriterApp.w_text (wvc_stP F Pd)) bs
    (wf_live F + WriterApp.w_cap (wvc_stP F Pd) - wf_cap0 F) peak (WriterApp.w_cnt (wvc_stP F Pd))
    (WriterApp.w_fail (wvc_stP F Pd))).
  - exact HPRE.
  - exact HHD.
  - unfold FRL_CRT_CALLEE in *. lia.
  - exact R10.
  - exact R11.
  - exact R12.
  - exact HOUT.
  - exact HGLOB.
  - exact HU0.
  - rewrite Hsp. unfold WVC_F. lia.
  - exact HE_oot.
  - exact HE_ot16.
  - exact Htop.
  - exact HCHO.
  - exact HPRES.
  - exact HZB.
  - right; right; right. exists bs. split; [exact Hro | apply Nat.le_succ_diag_r].
  - reflexivity.
  - exact HBO.
  - split; [lia | lia].
  - left. unfold WVC_F in *. lia.
  - exact HROOM.
  - exact (proj1 HBK).
  - lia.
  - exact HBUDc. }
cbv beta. intros W' c' Hle (st' & buf' & U' & Est & Hus & Hwp).
subst st'. unfold wpost, fpostU in Hwp.
destruct Hwp as (ly2 & S2 & regs2 & mem2 & md2 & Ec & HJc & OK2 & PO2 & HPRS & HOUT2 & HKEPT & HBSW & HWK2 & HGL2
  & _).
subst c'.
destruct (wvc_ret_inv B HSS F ly0 S0 U0 W0 mem0 md0 regs0 HE_sp16 HE_oot HE_top HE_top47 HE_lo HE_cap0 HE_cnt0
  HE_p HE_d HE_dd HE_bud HE_ty HE_hdr HE_n HE_kk r2 i' Pd [bs] Rest ly S U W memC mdC buf regsC regsC
  (wf_keys F + 8 * i') 0 STK_put peak ly2 S2 U' W' regs2 mem2 md2 buf'
  HWP HJ HARU HSEM Hpk HCH R9 Hsp R8 R9 R19 R21 R23 R25 R3 R4 R18 R20 R22 R24 R26 R27 Hi
  HJc OK2 PO2 HPRS SKp0 ltac:(lia) Hus HOUT2 HKEPT HBSW HWK2 HGL2) as (key' & HINV).
rewrite R1.
exact (K W' (mkst regs2 (w64 r2) mem2 (seg_rom tfibsegs)) md2 ly2 S2 U' buf' key' Hle HINV).
Qed.

(* ---- indent at depth dep (the per-item indent at d + 1, the closing indent at d) ---- *)
Lemma wvc_call_indent : forall r2 i' Pd Pc Rest ly S U (W : world tfibsegs) regsC memC mdC buf dep
    (Q : world tfibsegs -> config -> Prop),
  wvc_WP F = Pd ++ Pc ++ Rest -> Pc = WriterValue.wind (wvc_pp F) dep ->
  ajournal tfibsegs B (wvc_STK F) (wf_ot F) (wvc_FP F) ly0 S0 W0 (unpoison U0 mem0) md0 []
    ly S W (unpoison U memC) mdC (wevk (wf_cap0 F) (wvc_stP F Pd)) ->
  ARU tfibsegs B ly S U W memC mdC ->
  wvc_sem B F ly0 S0 U0 W0 mem0 regs0 ly S U W memC buf (wvc_stP F Pd) ->
  Forall (YP09.chunk_ok tfibsegs (wvc_E F regs0 regsC (wf_keys F + 8 * i') 0) (rdW W memC) (wf_sp F - WVC_F))
    (wvc_csL (wf_p F)) ->
  spZ regsC = wf_sp F - WVC_F ->
  YK11.getr regsC 1%bv = w64 r2 -> In r2 WV_CONT_RAS ->
  YK11.getr regsC 10%bv = w64 (wf_o F) -> YK11.getr regsC 11%bv = w64 (wf_p F) ->
  YK11.getr regsC 12%bv = w64 dep -> 0 <= dep < 2 ^ 31 ->
  YK11.getr regsC 8%bv = w64 (wf_o F) -> YK11.getr regsC 9%bv = w64 (wf_v F) ->
  YK11.getr regsC 19%bv = w64 (wf_p F) -> YK11.getr regsC 21%bv = w64 i' ->
  YK11.getr regsC 23%bv = w64 (56 * i') -> YK11.getr regsC 25%bv = w64 (8 * i') ->
  YK11.getr regsC 18%bv = w64 (wf_v F + 40) ->
  YK11.getr regsC 20%bv = w64 ((wf_v F + 24) / 8 + SHADOW_OFF) ->
  YK11.getr regsC 22%bv = w64 (wf_d F + 1) -> YK11.getr regsC 24%bv = w64 (wf_v F + 24) ->
  YK11.getr regsC 26%bv = w64 0 ->
  YK11.getr regsC 27%bv = w64 ((wf_v F + 40) / 8 + SHADOW_OFF) ->
  YK11.getr regsC 3%bv = YK11.getr regs0 3%bv -> YK11.getr regsC 4%bv = YK11.getr regs0 4%bv ->
  0 <= i' < wf_n F ->
  (forall W' ms2 mdc2 ly' S' U' buf' key', wle W W' ->
     wvc_inv B F r2 i' (wf_keys F + 8 * i') key' (Pd ++ Pc) ly0 S0 U0 W0 mem0 md0 regs0 W' ms2 mdc2 ly' S' U' buf' ->
     SRr tfibsegs W' (mkCfg ms2 mdc2) Q) ->
  SRr tfibsegs W (cfg_at tfibsegs A_indent regsC memC mdC) Q.
Proof.
intros r2 i' Pd Pc Rest ly S U W regsC memC mdC buf dep Q HWP HPc HJ HARU HSEM HCH Hsp R1 Hin R10 R11 R12 Hdep
  R8 R9 R19 R21 R23 R25 R18 R20 R22 R24 R26 R27 R3 R4 Hi K.
subst Pc.
pose proof (wvc_stk (wf_m F)) as (HF & _ & HSKi & _).
assert (SKi0 : 0 <= STK_indent) by (vm_compute; discriminate).
pose proof HSEM as (HOUT & HGL & HHD & HUS & HBS & HBK & HCNT & HWK & HN & HPO & HNB & HUL & HD & HROOT & HBIN &
  HB0 & HRO & H8 & HCch & HU0).
destruct HGL as (peak & Hpk & HGLOB).
destruct (wvc_call_facts Pd r2 regsC (wf_keys F + 8 * i') 0 ly S U W memC mdC buf STK_indent
  HJ HARU HSEM HCH Hsp R1 Hin R8 R3 R4 SKi0 ltac:(lia))
  as (ch & HPRE & HCHO & HPRES & Hs0 & Htop & HFRL & Hlo & Hosp).
pose proof (wvc_room_mid Pd (WriterValue.wind (wvc_pp F) dep) Rest HWP) as HROOM.
pose proof (wvc_bud_mid Pd (WriterValue.wind (wvc_pp F) dep) Rest ly S U W memC mdC buf HWP HJ HSEM) as HBUDc.
eapply SRr_bind.
{ apply (HIND ly S U W regsC memC mdC ch (wf_ot F) (wf_o F) (wf_p F) dep buf
    (WriterApp.w_cap (wvc_stP F Pd)) (WriterApp.w_failed (wvc_stP F Pd)) (WriterApp.w_text (wvc_stP F Pd))
    (wf_live F + WriterApp.w_cap (wvc_stP F Pd) - wf_cap0 F) peak (WriterApp.w_cnt (wvc_stP F Pd))
    (WriterApp.w_fail (wvc_stP F Pd))).
  - exact HPRE.
  - exact HHD.
  - exact HFRL.
  - exact R10.
  - exact R11.
  - exact R12.
  - exact HE_p.
  - lia.
  - exact HOUT.
  - exact HGLOB.
  - exact HU0.
  - rewrite Hsp. unfold WVC_F. lia.
  - exact HE_oot.
  - exact HE_ot16.
  - exact Htop.
  - exact HCHO.
  - exact HPRES.
  - exact HROOM.
  - exact (proj1 HBK).
  - lia.
  - exact HBUDc. }
cbv beta. intros W' c' Hle (st' & buf' & U' & Est & Hus & Hwp).
subst st'. unfold wpost, fpostU in Hwp.
destruct Hwp as (ly2 & S2 & regs2 & mem2 & md2 & Ec & HJc & OK2 & PO2 & HPRS & HOUT2 & HKEPT & HBSW & HWK2 & HGL2).
subst c'.
destruct (wvc_ret_inv B HSS F ly0 S0 U0 W0 mem0 md0 regs0 HE_sp16 HE_oot HE_top HE_top47 HE_lo HE_cap0 HE_cnt0
  HE_p HE_d HE_dd HE_bud HE_ty HE_hdr HE_n HE_kk r2 i' Pd (WriterValue.wind (wvc_pp F) dep) Rest ly S U W memC
  mdC buf regsC regsC (wf_keys F + 8 * i') 0 STK_indent peak ly2 S2 U' W' regs2 mem2 md2 buf'
  HWP HJ HARU HSEM Hpk HCH R9 Hsp R8 R9 R19 R21 R23 R25 R3 R4 R18 R20 R22 R24 R26 R27 Hi
  HJc OK2 PO2 HPRS SKi0 ltac:(lia) Hus HOUT2 HKEPT HBSW HWK2 HGL2) as (key' & HINV).
rewrite R1.
exact (K W' (mkst regs2 (w64 r2) mem2 (seg_rom tfibsegs)) md2 ly2 S2 U' buf' key' Hle HINV).
Qed.

(* ---- put_string of an object key ---- *)
Lemma wvc_call_ps : forall r2 i' Pd Pc Rest ly S U (W : world tfibsegs) regsC memC mdC buf x kk (nm : list Z)
    (Q : world tfibsegs -> config -> Prop),
  wvc_WP F = Pd ++ Pc ++ Rest -> Pc = WriterSpec.spieces nm ->
  ajournal tfibsegs B (wvc_STK F) (wf_ot F) (wvc_FP F) ly0 S0 W0 (unpoison U0 mem0) md0 []
    ly S W (unpoison U memC) mdC (wevk (wf_cap0 F) (wvc_stP F Pd)) ->
  ARU tfibsegs B ly S U W memC mdC ->
  wvc_sem B F ly0 S0 U0 W0 mem0 regs0 ly S U W memC buf (wvc_stP F Pd) ->
  Forall (YP09.chunk_ok tfibsegs (wvc_E F regs0 regsC (wf_keys F + 8 * i') x) (rdW W memC) (wf_sp F - WVC_F))
    (wvc_csL (wf_p F)) ->
  spZ regsC = wf_sp F - WVC_F ->
  YK11.getr regsC 1%bv = w64 r2 -> In r2 WV_CONT_RAS ->
  YK11.getr regsC 10%bv = w64 (wf_o F) -> YK11.getr regsC 11%bv = w64 x ->
  YK11.getr regsC 8%bv = w64 (wf_o F) -> YK11.getr regsC 9%bv = w64 (wf_v F) ->
  YK11.getr regsC 19%bv = w64 (wf_p F) -> YK11.getr regsC 21%bv = w64 i' ->
  YK11.getr regsC 23%bv = w64 (56 * i') -> YK11.getr regsC 25%bv = w64 (8 * i') ->
  YK11.getr regsC 18%bv = w64 (wf_v F + 40) ->
  YK11.getr regsC 20%bv = w64 ((wf_v F + 24) / 8 + SHADOW_OFF) ->
  YK11.getr regsC 22%bv = w64 (wf_d F + 1) -> YK11.getr regsC 24%bv = w64 (wf_v F + 24) ->
  YK11.getr regsC 26%bv = w64 0 ->
  YK11.getr regsC 27%bv = w64 ((wf_v F + 40) / 8 + SHADOW_OFF) ->
  YK11.getr regsC 3%bv = YK11.getr regs0 3%bv -> YK11.getr regsC 4%bv = YK11.getr regs0 4%bv ->
  0 <= i' < wf_n F ->
  PjStruct.pj_cstr tfibsegs (rdW W memC) (fun a k => In (a, k) (wf_UL F)) x kk nm ->
  In (x, kk) (wf_D F) -> plain_bytes nm ->
  (forall W' ms2 mdc2 ly' S' U' buf' key', wle W W' ->
     wvc_inv B F r2 i' (wf_keys F + 8 * i') key' (Pd ++ Pc) ly0 S0 U0 W0 mem0 md0 regs0 W' ms2 mdc2 ly' S' U' buf' ->
     SRr tfibsegs W' (mkCfg ms2 mdc2) Q) ->
  SRr tfibsegs W (cfg_at tfibsegs A_put_string regsC memC mdC) Q.
Proof.
intros r2 i' Pd Pc Rest ly S U W regsC memC mdC buf x kk nm Q HWP HPc HJ HARU HSEM HCH Hsp R1 Hin R10 R11
  R8 R9 R19 R21 R23 R25 R18 R20 R22 R24 R26 R27 R3 R4 Hi HCS HinD Hplain K.
subst Pc.
pose proof (wvc_stk (wf_m F)) as (HF & _ & _ & HSKps & _).
assert (SKps0 : 0 <= STK_put_string) by (vm_compute; discriminate).
pose proof HSEM as (HOUT & HGL & HHD & HUS & HBS & HBK & HCNT & HWK & HN & HPO & HNB & HUL & HD & HROOT & HBIN &
  HB0 & HRO & H8 & HCch & HU0).
destruct HGL as (peak & Hpk & HGLOB).
pose proof (proj1 HARU) as HAR.
destruct (wvc_call_facts Pd r2 regsC (wf_keys F + 8 * i') x ly S U W memC mdC buf STK_put_string
  HJ HARU HSEM HCH Hsp R1 Hin R8 R3 R4 SKps0 ltac:(lia))
  as (ch & HPRE & HCHO & HPRES & Hs0 & Htop & HFRL & Hlo & Hosp).
(* the key string: a live reader block of the tree, other than the writer's buffer *)
destruct (HD x kk HinD) as (HinUL & Hne).
pose proof (HUL x kk HinD) as HRB.
pose proof (wv_rblock_low B ly S W (unpoison U memC) mdC memC x kk HAR HRB) as (Hx1 & Hx2).
pose proof HCS as (_ & Hlen & HCB).
pose proof HCB as (Hbytes & _).
assert (HCSOK : cstr_ok tfibsegs W memC x nm)
  by exact (wv_cstr_ok_block B ly S U W memC mdC x kk nm HARU HHD HRB HCB Hlen).
pose proof (wvc_room_mid Pd (WriterSpec.spieces nm) Rest HWP) as HROOM.
pose proof (wvc_bud_mid Pd (WriterSpec.spieces nm) Rest ly S U W memC mdC buf HWP HJ HSEM) as HBUDc.
eapply SRr_bind.
{ apply (HPS ly S U W regsC memC mdC ch (wf_ot F) (wf_o F) x buf
    (WriterApp.w_cap (wvc_stP F Pd)) (WriterApp.w_failed (wvc_stP F Pd)) (WriterApp.w_text (wvc_stP F Pd)) nm
    (wf_live F + WriterApp.w_cap (wvc_stP F Pd) - wf_cap0 F) peak (WriterApp.w_cnt (wvc_stP F Pd))
    (WriterApp.w_fail (wvc_stP F Pd))).
  - exact HPRE.
  - exact HHD.
  - exact HFRL.
  - exact R10.
  - exact R11.
  - exact HOUT.
  - exact HGLOB.
  - exact HU0.
  - rewrite Hsp. unfold WVC_F. lia.
  - exact HE_oot.
  - exact HE_ot16.
  - exact Htop.
  - exact HCHO.
  - exact (wv_ps_chain B STK_put_string ly S U W regsC memC mdC ch (wf_o F) HPRE
             ltac:(rewrite Hsp; unfold WVC_F; lia) (or_intror (or_introl Hs0)) HCHO).
  - exact HPRES.
  - exact HCSOK.
  - right; left. exists x, kk. split; [exact Hne|]. split; [exact HRB|].
    rewrite length_app. cbn [length]. lia.
  - unfold WriterSpec.bytes_ok. eapply Forall_impl; [|exact Hbytes]. intros c Hc. cbn beta in Hc. lia.
  - unfold WriterSpec.no_zero. eapply Forall_impl; [|exact Hbytes]. intros c Hc. cbn beta in Hc. lia.
  - exact Hplain.
  - left. unfold WVC_F in *. lia.
  - exact HROOM.
  - exact (proj1 HBK).
  - lia.
  - exact HBUDc. }
cbv beta. intros W' c' Hle (st' & buf' & U' & Est & Hus & Hwp).
subst st'. unfold wpost, fpostU in Hwp.
destruct Hwp as (ly2 & S2 & regs2 & mem2 & md2 & Ec & HJc & OK2 & PO2 & HPRS & HOUT2 & HKEPT & HBSW & HWK2 & _
  & HGL2).
subst c'.
destruct (wvc_ret_inv B HSS F ly0 S0 U0 W0 mem0 md0 regs0 HE_sp16 HE_oot HE_top HE_top47 HE_lo HE_cap0 HE_cnt0
  HE_p HE_d HE_dd HE_bud HE_ty HE_hdr HE_n HE_kk r2 i' Pd (WriterSpec.spieces nm) Rest ly S U W memC mdC buf
  regsC regsC (wf_keys F + 8 * i') x STK_put_string peak ly2 S2 U' W' regs2 mem2 md2 buf'
  HWP HJ HARU HSEM Hpk HCH R9 Hsp R8 R9 R19 R21 R23 R25 R3 R4 R18 R20 R22 R24 R26 R27 Hi
  HJc OK2 PO2 HPRS SKps0 ltac:(lia) Hus HOUT2 HKEPT HBSW HWK2 HGL2) as (key' & HINV).
rewrite R1.
exact (K W' (mkst regs2 (w64 r2) mem2 (seg_rom tfibsegs)) md2 ly2 S2 U' buf' key' Hle HINV).
Qed.

(* ---- the recursive write_value of the i-th item (the level below, by the arm's hypothesis HWV) ---- *)
Lemma wvc_call_item : forall r2 i' Pd Pc Rest ly S U (W : world tfibsegs) regsC memC mdC buf (u : PjTree.jv) Du
    (Q : world tfibsegs -> config -> Prop),
  write_value_spec_at B tfibsegs (Datatypes.S (2 - wf_m F)) ->
  wvc_WP F = Pd ++ Pc ++ Rest -> Pc = WriterValue.wvpieces u (wvc_pp F) (wf_d F + 1) ->
  (PjTree.depth (wf_t F) <= wf_m F)%nat -> (wf_m F <= 2)%nat ->
  (PjTree.depth u < PjTree.depth (wf_t F))%nat -> (wf_m F >= 1)%nat ->
  ajournal tfibsegs B (wvc_STK F) (wf_ot F) (wvc_FP F) ly0 S0 W0 (unpoison U0 mem0) md0 []
    ly S W (unpoison U memC) mdC (wevk (wf_cap0 F) (wvc_stP F Pd)) ->
  ARU tfibsegs B ly S U W memC mdC ->
  wvc_sem B F ly0 S0 U0 W0 mem0 regs0 ly S U W memC buf (wvc_stP F Pd) ->
  Forall (YP09.chunk_ok tfibsegs (wvc_E F regs0 regsC (wf_keys F + 8 * i') 0) (rdW W memC) (wf_sp F - WVC_F))
    (wvc_csL (wf_p F)) ->
  spZ regsC = wf_sp F - WVC_F ->
  YK11.getr regsC 1%bv = w64 r2 -> In r2 WV_CONT_RAS ->
  YK11.getr regsC 10%bv = w64 (wf_o F) -> YK11.getr regsC 11%bv = w64 (wf_kids F + 56 * i') ->
  YK11.getr regsC 12%bv = w64 (wf_p F) -> YK11.getr regsC 13%bv = w64 (wf_d F + 1) ->
  YK11.getr regsC 8%bv = w64 (wf_o F) -> YK11.getr regsC 9%bv = w64 (wf_v F) ->
  YK11.getr regsC 19%bv = w64 (wf_p F) -> YK11.getr regsC 21%bv = w64 i' ->
  YK11.getr regsC 23%bv = w64 (56 * i') -> YK11.getr regsC 25%bv = w64 (8 * i') ->
  YK11.getr regsC 18%bv = w64 (wf_v F + 40) ->
  YK11.getr regsC 20%bv = w64 ((wf_v F + 24) / 8 + SHADOW_OFF) ->
  YK11.getr regsC 22%bv = w64 (wf_d F + 1) -> YK11.getr regsC 24%bv = w64 (wf_v F + 24) ->
  YK11.getr regsC 26%bv = w64 0 ->
  YK11.getr regsC 27%bv = w64 ((wf_v F + 40) / 8 + SHADOW_OFF) ->
  YK11.getr regsC 3%bv = YK11.getr regs0 3%bv -> YK11.getr regsC 4%bv = YK11.getr regs0 4%bv ->
  0 <= i' < wf_n F ->
  PjStruct.pj_node tfibsegs (rdW W memC) (fun a k => In (a, k) (wf_UL F)) (wf_kids F + 56 * i') u Du ->
  (forall b, In b Du -> In b (wf_D F)) -> jv_plain u ->
  (forall x, wf_kids F + 56 * i' <= x < wf_kids F + 56 * i' + 56 -> PjStruct.pj_foot (wf_v F) (wf_D F) x) ->
  (forall W' ms2 mdc2 ly' S' U' buf' key', wle W W' ->
     wvc_inv B F r2 i' (wf_keys F + 8 * i') key' (Pd ++ Pc) ly0 S0 U0 W0 mem0 md0 regs0 W' ms2 mdc2 ly' S' U' buf' ->
     SRr tfibsegs W' (mkCfg ms2 mdc2) Q) ->
  SRr tfibsegs W (cfg_at tfibsegs A_write_value regsC memC mdC) Q.
Proof.
intros r2 i' Pd Pc Rest ly S U W regsC memC mdC buf u Du Q HWV HWP HPc Hdt Hm2 Hdu Hm1 HJ HARU HSEM HCH Hsp R1 Hin
  R10 R11 R12 R13 R8 R9 R19 R21 R23 R25 R18 R20 R22 R24 R26 R27 R3 R4 Hi HNODE HDu Hplain HFOOT K.
subst Pc.
pose proof (wvc_stk (wf_m F)) as (HF & _ & _ & _ & HSKrec).
pose proof HSEM as (HOUT & HGL & HHD & HUS & HBS & HBK & HCNT & HWK & HN & HPO & HNB & HUL & HD & HROOT & HBIN &
  HB0 & HRO & H8 & HCch & HU0).
destruct HGL as (peak & Hpk & HGLOB).
pose proof (proj1 HARU) as HAR.
pose proof HOUT as (_ & Ho0 & Hotop & _ & Hbuf64 & Hcap64 & _).
assert (HSTKc : STK_write_value (2 - Datatypes.S (2 - wf_m F)) + WVC_F <= STK_write_value (wf_m F))
  by (apply HSKrec; lia).
assert (HSTKc0 : 0 <= STK_write_value (2 - Datatypes.S (2 - wf_m F))).
{ pose proof (wvc_stk (2 - Datatypes.S (2 - wf_m F))) as (HF2 & _). unfold WVC_F in *. lia. }
destruct (wvc_call_facts Pd r2 regsC (wf_keys F + 8 * i') 0 ly S U W memC mdC buf
  (STK_write_value (2 - Datatypes.S (2 - wf_m F))) HJ HARU HSEM HCH Hsp R1 Hin R8 R3 R4 HSTKc0 HSTKc)
  as (ch & HPRE & HCHO & HPRES & Hs0 & Htop & HFRL & Hlo & Hosp).
(* the item node's placement: the i-th slot of the container's kids block *)
destruct (wvc_kids_blk ly S U W memC mdC buf (wvc_stP F Pd) HARU HSEM ltac:(lia)) as (cap2 & Hncap & Hkin).
pose proof (HUL _ _ Hkin) as HKRB.
assert (HPOBJ : FSH_Fn_reader.pobj tfibsegs B ly S W memC (wf_kids F + 56 * i'))
  by exact (wv_kid_pobj B ly S U W memC mdC (wf_kids F) cap2 i' HARU HHD HKRB ltac:(lia) ltac:(lia)).
(* the item node is apart from the writer's buffer: its bytes are in the tree's footprint, which is off the
   call's footprint (ZZwvB_call2.wvc_foot_off_fp) *)
assert (Hsep : WriterApp.w_cap (wvc_stP F Pd) <> 0 ->
  wf_kids F + 56 * i' + 56 <= buf - HEAD \/ buf + WriterApp.w_cap (wvc_stP F Pd) <= wf_kids F + 56 * i').
{ intros Hc0.
  assert (Hnot : forall y, wf_kids F + 56 * i' <= y < wf_kids F + 56 * i' + 56 ->
    ~ (buf - HEAD <= y < buf + WriterApp.w_cap (wvc_stP F Pd))).
  { intros y Hy Hb.
    apply (wvc_foot_off_fp B ly S W (unpoison U memC) mdC memC (wf_v F) (wf_D F) buf
      (WriterApp.w_cap (wvc_stP F Pd)) HAR HPO HUL (fun a k H => proj2 (HD a k H)) HROOT HBIN ltac:(lia)
      y (HFOOT y Hy)).
    exists (buf - HEAD, buf + WriterApp.w_cap (wvc_stP F Pd)). split.
    - apply in_or_app. right. unfold wbuf_fp.
      rewrite (proj2 (Z.eqb_neq (WriterApp.w_cap (wvc_stP F Pd)) 0) Hc0). left. reflexivity.
    - cbn [fst snd]. lia. }
  destruct (wvr_apart_pt (wf_kids F + 56 * i') 56 (buf - HEAD) (WriterApp.w_cap (wvc_stP F Pd) + HEAD)
    ltac:(lia) ltac:(unfold HEAD; lia)
    ltac:(intros y Hy Hb; apply (Hnot y Hy); unfold HEAD in *; lia)) as [H1 | H1];
  [left | right]; unfold HEAD in *; lia. }
pose proof (wvc_room_mid Pd (WriterValue.wvpieces u (wvc_pp F) (wf_d F + 1)) Rest HWP) as HROOM.
pose proof (wvc_bud_mid Pd (WriterValue.wvpieces u (wvc_pp F) (wf_d F + 1)) Rest ly S U W memC mdC buf HWP HJ
  HSEM) as HBUDc.
pose proof (wvc_d1 F S0 HE_p HE_dd HE_ty HE_n) as Hd1.
eapply SRr_bind.
{ apply (HWV ly S U W regsC memC mdC ch (wf_ot F) (wf_o F) (wf_kids F + 56 * i') (wf_p F) (wf_d F + 1) u Du Du buf
    (WriterApp.w_cap (wvc_stP F Pd)) (WriterApp.w_failed (wvc_stP F Pd)) (WriterApp.w_text (wvc_stP F Pd))
    (wf_live F + WriterApp.w_cap (wvc_stP F Pd) - wf_cap0 F) peak (WriterApp.w_cnt (wvc_stP F Pd))
    (WriterApp.w_fail (wvc_stP F Pd))).
  - lia.
  - exact HPRE.
  - exact HHD.
  - exact HFRL.
  - exact R10.
  - exact R11.
  - exact R12.
  - exact R13.
  - exact HE_p.
  - lia.
  - lia.
  - right; left. exact Hs0.
  - exact HOUT.
  - exact HGLOB.
  - exact HU0.
  - rewrite Hsp. unfold WVC_F. lia.
  - exact HE_oot.
  - exact HE_ot16.
  - exact Htop.
  - exact HCHO.
  - exact HPRES.
  - apply (PjStruct.pj_node_frame tfibsegs u (rdW W memC) (fun a k => In (a, k) (wf_UL F)) (rdW W memC)
            (fun a k => In (a, k) Du) (wf_kids F + 56 * i') Du HNODE);
      [intros a k Hak; exact Hak | intros y Hy; reflexivity].
  - exact HPOBJ.
  - intros a k Hak. exact (HUL a k (HDu (a, k) Hak)).
  - intros a k Hak. split; [exact Hak | exact (proj2 (HD a k (HDu (a, k) Hak)))].
  - exact Hsep.
  - exact Hplain.
  - intros y Hy Hf. apply (HE_foot y Hy).
    exact (wv_foot_sub (wf_v F) (wf_kids F + 56 * i') (wf_D F) Du HDu HFOOT y Hf).
  - exact HROOM.
  - exact (proj1 HBK).
  - lia.
  - exact HBUDc. }
cbv beta. intros W' c' Hle (st' & buf' & U' & Est & Hus & Hwp).
subst st'. unfold wpost, fpostU in Hwp.
destruct Hwp as (ly2 & S2 & regs2 & mem2 & md2 & Ec & HJc & OK2 & PO2 & HPRS & HOUT2 & HKEPT & HBSW & HWK2 & _
  & HGL2).
subst c'.
destruct (wvc_ret_inv B HSS F ly0 S0 U0 W0 mem0 md0 regs0 HE_sp16 HE_oot HE_top HE_top47 HE_lo HE_cap0 HE_cnt0
  HE_p HE_d HE_dd HE_bud HE_ty HE_hdr HE_n HE_kk r2 i' Pd (WriterValue.wvpieces u (wvc_pp F) (wf_d F + 1)) Rest
  ly S U W memC mdC buf regsC regsC (wf_keys F + 8 * i') 0
  (STK_write_value (2 - Datatypes.S (2 - wf_m F))) peak ly2 S2 U' W' regs2 mem2 md2 buf'
  HWP HJ HARU HSEM Hpk HCH R9 Hsp R8 R9 R19 R21 R23 R25 R3 R4 R18 R20 R22 R24 R26 R27 Hi
  HJc OK2 PO2 HPRS HSTKc0 HSTKc Hus HOUT2 HKEPT HBSW HWK2 HGL2) as (key' & HINV).
rewrite R1.
exact (K W' (mkst regs2 (w64 r2) mem2 (seg_rom tfibsegs)) md2 ly2 S2 U' buf' key' Hle HINV).
Qed.

End St.
End A.
