(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan) skip_ws call steps of the parse_items walk.
   pic_call_sw is the B-local port, to parse_items' window and chain, of the B parse_value walk's pv_wscall
   (a working branch a40df3dd279 proofs/omx-clap-core/fuzz_state/lib/B/Prog/FSW_parse_value_holds.v,
   a Theorem Labs lane): the callee's fpreU from the caller's journal (FSW_ret.fsw_fpreU_atFP), skip_ws_spec, and its post handed
   on with the callee journal at the caller's raised window (STK_skip_ws + (ot - spZ regsC), ot), which is the form
   FSW_parse_items_calls.pic_after_callT resumes from. Changed from pv_wscall: the chain fpreU reads is built here
   (FSW_parse_items_mem.pim_chain_q16: s0 = q + 16 at every parse_items call), rd_win is built from the journal, and the
   two journals are handed on uncomposed. pis_mrd_grows is a B-local copy of the A walk's pid_mrd_grows
   (a working branch 493982bffc9 proofs/omx-clap-core/fuzz_state/lib/A/FSW_pitems_dev.v), verbatim.
   pi_sw1 is the first call, 0x84f58 -> 0x84f5c (pf.c:217, the white space after `{`): stage A
   (FSW_parse_items.pi_stageA), the call, and the resume at 0x84f5c in FSW_parse_items.pi_ssB0 (the state stage B's two
   arms take), with the data both arms and the post read.
   rule 24: proves no function (kind: call-step lemmas). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require YF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSW_K FSW_K3 FSW_ret FSW_rd FSW_pj FSPstat FSH_Fn_reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require PjIn PjStruct ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Mem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require MState.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.Prog Require Import
FSW_parse_items_tbl FSW_parse_items FSW_parse_items_calls FSW_parse_items_mem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Local Ltac pis_cs := unfold acallee_saved; lazymatch goal with |- context [bv_unsigned ?q] =>
  let z := eval vm_compute in (bv_unsigned q) in change (bv_unsigned q) with z end; lia.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YI14.
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* ================= the frame and the words of struct pj_in, image-free ================= *)
Section F. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma pis_sink_nil : ~ YI16.sink_open_fp [].
Proof. intros (r & Hr & _). destruct Hr. Qed.
(* a byte that is defined stays defined as the memory grows (copied, see the header: pid_mrd_grows) *)
Lemma pis_mrd_grows : forall (m m' : word -> option byte) x, mem_grows m m' ->
  (exists b, Mem.mrd tfibsegs m x = Some b) -> exists b, Mem.mrd tfibsegs m' x = Some b.
Proof.
intros m m' x HG (b & Hb). unfold Mem.mrd in *.
destruct (m x) as [c|] eqn:E1; destruct (m' x) as [c'|] eqn:E2; try (eexists; reflexivity).
- exfalso. apply (HG x); [rewrite E1; discriminate | exact E2].
- exists b. exact Hb.
Qed.
(* the frame's thirteen saved words, read through any memory that agrees with it on [sp - 104, sp) *)
Lemma pis_frame_mb : forall (M M' : word -> option byte) sp regs0,
  (forall a, sp - 104 <= a < sp -> mbyte tfibsegs M' a = mbyte tfibsegs M a) ->
  pi_frame M sp regs0 -> pi_frame M' sp regs0.
Proof.
intros M M' sp regs0 E H. unfold pi_frame in *. rewrite Forall_forall in *. intros x Hx.
assert (Ho : -104 <= fst x /\ fst x + 8 <= 0)
  by (unfold pi_saved in Hx; cbn [In] in Hx; repeat (destruct Hx as [<-|Hx]; [cbn [fst]; lia|]); destruct Hx).
apply (pim_val_mb M M' _ 8 _); [|exact (H x Hx)]. intros i Hi. apply E. cbn in Hi. lia.
Qed.
(* ... as the chunks of the resume state's frame region (pi_cs), under any env whose xatoms 3 .. 15 hold them *)
Lemma pis_frame_chunks : forall regs2 xs m sp regs,
  (forall j, (j < 13)%nat -> nth (3 + j) xs (Z_to_bv 64 0) = YK11.getr regs (nth j pi_saved_regs 0%bv)) ->
  pi_frame m sp regs -> Forall (YP09.chunk_ok tfibsegs (Ereg regs2 (fs_extraT ++ xs)) m (sp - 144)) pi_cs.
Proof.
intros regs2 xs m sp regs HX Hfr.
assert (EX : forall i, (i < 13)%nat -> ew (Ereg regs2 (fs_extraT ++ xs)) (xatom (3 + i)) =
  YK11.getr regs (nth i pi_saved_regs 0%bv)) by (intros i Hi; rewrite fsw_ew_xatom; exact (HX i Hi)).
unfold pi_frame, pi_saved in Hfr.
repeat match goal with H : Forall _ (_ :: _) |- _ => apply Forall_cons_iff in H; destruct H as [? H] end.
cbn [fst snd] in *. unfold pi_cs.
repeat (apply Forall_cons; [
  lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal 8 (SOff (xatom ?j) 0))) =>
    let i := eval vm_compute in (j - 3)%nat in
    let r := eval vm_compute in (nth i pi_saved_regs 0%bv) in
    apply (chunk_ok_val tfibsegs _ _ _ off 8 _ (bv_unsigned (YK11.getr regs r)));
    [ rewrite fsw_SOff0; change j with (3 + i)%nat; rewrite (EX i ltac:(lia)); symmetry; apply Z_to_bv_bv_unsigned
    | apply u64_range | cbn; lia
    | replace (sp - 144 + off) with (sp + (off - 144)) by lia; assumption ] end|]).
apply Forall_nil.
Qed.
(* the three words of struct pj_in as the chunks of pi_qR, from pj_in_ok (its wr_at gives the write window) *)
Lemma pis_q_ok : forall E m q text len p d tb,
  bv_unsigned (ew E 9) = q -> ew E (xatom 0) = Z_to_bv 64 p -> ew E (xatom 1) = Z_to_bv 64 (text + len) ->
  ew E (xatom 2) = Z_to_bv 64 d ->
  PjIn.pj_in_ok tfibsegs m q text len p d tb -> YP09.region_ok tfibsegs E m pi_qR.
Proof.
intros E m q text len p d tb E9 EX0 EX1 EX2 HIN.
pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN) as (Hq0 & Hq64 & Ht0 & Hp & Htl & _ & _ & Hq8 & Hd).
pose proof HIN as (Bp & Be & Bd & Bw & _).
unfold pi_qR, YP09.region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite E9. split; [lia|]. split; [lia|]. split.
- intros o Ho. unfold YP09.writable_at. destruct Bw as (_ & _ & Bw3). exact (Bw3 o ltac:(lia)).
- constructor; [|constructor; [|constructor; [|constructor]]].
  + apply (fsw_pj_chunk8 tfibsegs E m q 0 (SOff (xatom 0) 0) p);
      [rewrite Z.add_0_r; split; [lia | exact Bp] | rewrite fsw_SOff0; exact EX0].
  + apply (fsw_pj_chunk8 tfibsegs E m q 8 (SOff (xatom 1) 0) (text + len));
      [split; [lia | exact Be] | rewrite fsw_SOff0; exact EX1].
  + apply (fsw_pj_chunk4 tfibsegs E m q 16 (SOff (xatom 2) 0) d);
      [split; [lia | exact Bd] | rewrite fsw_SOff0; exact EX2].
Qed.
(* struct pj_in's words as val_mem facts, and back *)
Lemma pis_in_vals : forall m q text len p d tb, PjIn.pj_in_ok tfibsegs m q text len p d tb ->
  val_mem tfibsegs m q 8 p /\ val_mem tfibsegs m (q + 8) 8 (text + len).
Proof.
intros m q text len p d tb HIN.
pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN) as (Hq0 & Hq64 & Ht0 & Hp & Htl & _).
pose proof HIN as (Bp & Be & _).
split.
- apply val_mem_word_mem. pose proof (fsw_pj_bytes_at_le8_word tfibsegs _ _ _ Bp) as Hw.
  rewrite MState.unsigned_lit in Hw by lia. exact Hw.
- apply val_mem_word_mem. pose proof (fsw_pj_bytes_at_le8_word tfibsegs _ _ _ Be) as Hw.
  rewrite MState.unsigned_lit in Hw by lia. exact Hw.
Qed.
Lemma pis_in_mk : forall m m0 q text len p d p0 d0 tb,
  PjIn.pj_in_ok tfibsegs m0 q text len p0 d0 tb ->
  val_mem tfibsegs m q 8 p -> val_mem tfibsegs m (q + 8) 8 (text + len) -> val_mem tfibsegs m (q + 16) 4 d ->
  (forall i, 0 <= i < 24 -> writable_at tfibsegs m (q + i)) ->
  pim_eqon m0 m text (text + len) -> text <= p <= text + len -> 0 <= d <= 32 ->
  PjIn.pj_in_ok tfibsegs m q text len p d tb.
Proof.
intros m m0 q text len p d p0 d0 tb HIN Vp Ve Vd Hw Et Hp Hd.
pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN) as (Hq0 & Hq64 & Ht0 & _ & Htl & _).
destruct HIN as (_ & _ & _ & _ & H5 & H6 & H7 & _ & H9 & H10 & H11 & _).
refine (conj _ (conj _ (conj _ (conj _ (conj H5 (conj H6 (conj H7 (conj Hp (conj H9 (conj _ (conj H11 Hd))))))))))).
- apply fsw_pj_word_mem_le8; [apply val_mem_word_mem; exact Vp | lia | lia | lia].
- apply fsw_pj_word_mem_le8; [apply val_mem_word_mem; exact Ve | lia | lia | lia].
- apply (proj1 (fsw_pj_word4_iff tfibsegs m (q + 16) d ltac:(lia) ltac:(lia))). exact Vd.
- split; [lia|]. split; [lia|]. intros i Hi. change (writable_at tfibsegs m (q + i)). exact (Hw i Hi).
- apply (pim_eqon_bytes m0 m text); [|exact H10]. rewrite H9. exact Et.
Qed.
End F.

(* ================= a call of skip_ws from parse_items (any of the four sites) ================= *)
Section S. Context {fx : YK11.FPState} {rc : YM05.RunCeil} (SK : YI16.sink_head).
Variable B : asyms.
(* callee: skip_ws (a Theorem Labs lane's B walk, a working branch) *)
Hypothesis HSW : @skip_ws_spec fx rc SK tfibsegs B.

(* the call at return address r: a0 = s1 = q, s0 = q + 16. The caller's journal runs from any start and any own list;
   the post comes back with the callee journal at the raised window, its upoison facts, the preserved registers and
   skip_ws_spec's post *)
Lemma pic_call_sw : forall STK ot FP ly S W0 mem0 md0 own lyc Sc U (W : world tfibsegs) memC mdC kc regsC q text len p d
    (tb : list byte) tcap (ws rest : list Z) live peak cnt fail (Qc : world tfibsegs -> config -> Prop),
  @ajournal rc SK tfibsegs B STK ot FP ly S W0 mem0 md0 own lyc Sc W (unpoison U memC) mdC kc ->
  ARU tfibsegs B lyc Sc U W memC mdC -> arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) memC) ->
  FSupoisonU.fs_heads B lyc Sc U ->
  YK0s.ret_ok (YK11.getr regsC 1) -> 4096 <= raZ regsC ->
  YK11.getr regsC 3 = w64 (as_gp B) -> YK11.getr regsC 4 = w64 (as_tp B) ->
  YK11.getr regsC 10 = w64 q -> YK11.getr regsC 8 = w64 (q + 16) ->
  spZ regsC mod 16 = 0 -> ot - STK <= spZ regsC - STK_skip_ws -> spZ regsC <= q -> q + 24 <= ot ->
  PjIn.pj_in_ok tfibsegs (mrestrict (w_H W) memC) q text len p d tb ->
  rd_text tfibsegs B lyc Sc W memC text len tcap ->
  ReaderRes.rest_at tb text p = ws ++ rest -> Forall (fun c => PjGrammar.ws c = true) ws ->
  (forall c r, rest = c :: r -> PjGrammar.ws c = false) ->
  fs_glob tfibsegs W memC live peak cnt fail ->
  (forall ly' S' (W' : world tfibsegs) regs' mem' md',
     @ajournal rc SK tfibsegs B (STK_skip_ws + (ot - spZ regsC)) ot [] lyc Sc W (unpoison U memC) mdC [] ly' S' W'
       (unpoison U mem') md' 0 ->
     upoison_ok B ly' S' U -> upoisoned tfibsegs W' mem' U -> aregs_preserved regsC regs' ->
     PjIn.pj_in_ok tfibsegs (mrestrict (w_H W') mem') q text len (p + Z.of_nat (length ws)) d tb ->
     wkeep tfibsegs W W' memC mem' (spZ regsC) ot q 8 ->
     ablocks B ly' S' = ablocks B lyc Sc ->
     rd_text tfibsegs B ly' S' W' mem' text len tcap ->
     fs_glob tfibsegs W' mem' live peak cnt fail ->
     SRr tfibsegs W' (mkCfg (mkst regs' (YK11.getr regsC 1) mem' (seg_rom tfibsegs)) md') Qc) ->
  SRr tfibsegs W (YG0d.cfg_at tfibsegs A_skip_ws regsC memC mdC) Qc.
Proof.
intros STK ot FP ly S W0 mem0 md0 own lyc Sc U W memC mdC kc regsC q text len p d tb tcap ws rest live peak cnt fail Qc
  HJ HARU HRO FH Hret Hra4 C3 C4 C10 C8 Hal16 Hwin Hspq Hqot HIN HTX Hrest Hws Hstop HGL K.
pose proof asan_consts as (CC1 & _ & CC3 & _).
assert (HSW0 : 0 <= STK_skip_ws) by (vm_compute; discriminate).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRS & Hstk & _).
pose proof Hstk as (Hal16o & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN) as (Bq0 & Bq24 & Bt0 & Bp & Btl & Bqt & Blen & Bq8 & Bd).
pose proof HTX as (Htx1 & HRB & Htc).
destruct (fsw_rblock_low B lyc Sc W (unpoison U memC) mdC memC text tcap (ARU_AR tfibsegs B lyc Sc U W memC mdC HARU) HRB)
  as (T1 & T2).
(* the chain fpreU reads: s0 = q + 16 *)
assert (HCH : exists ch1, achain lyc (aview tfibsegs (w_H W) (unpoison U memC)) (spZ regsC) (s0Z regsC) ch1).
{ assert (Es0 : s0Z regsC = q + 16) by (unfold s0Z; rewrite C8; unfold w64; apply wz; lia). rewrite Es0.
  destruct (pis_in_vals _ q text len p d tb HIN) as (Vp & Ve).
  apply (pim_chain_q16 lyc _ (spZ regsC) q (text + len) p).
  - rewrite (pim_rdword_U B lyc Sc U W memC mdC (q + 8) HARU) by lia.
    exact (YF0x.val_mem_rdword (w_H W) memC (q + 8) (text + len) ltac:(lia) Ve).
  - rewrite (pim_rdword_U B lyc Sc U W memC mdC q HARU) by lia.
    exact (YF0x.val_mem_rdword (w_H W) memC q p ltac:(lia) Vp).
  - unfold HEAD in *. lia.
  - lia.
  - exact Bq8.
  - lia. }
destruct HCH as [ch1 HCH].
assert (HPREc : fpreU tfibsegs B STK_skip_ws lyc Sc U W regsC memC mdC ch1).
{ apply (fsw_fpreU_atFP B STK ot FP ly S U W0 mem0 md0 own lyc Sc W memC mdC kc regsC STK_skip_ws (spZ regsC - ot) ch1
    HJ HARU HRO);
    [lia | rewrite Zminus_mod, Hal16, Hal16o; reflexivity | lia | vm_compute; discriminate | lia
    | exact Hret | exact Hra4 | exact C3 | exact C4 | exact HCH]. }
assert (HWIN : rd_win tfibsegs regsC lyc W memC q ot).
{ unfold rd_win. split; [lia|]. split; [lia|]. split; [exact Hal16o|]. split; [rewrite Etop; exact Htop|].
  intros a Ha. apply (fsw_apresent_unpoison B lyc Sc U W memC mdC a HARU); [lia|]. apply HPRS. lia. }
eapply SRr_bind.
{ exact (HSW lyc Sc U W regsC memC mdC ch1 q ot text len p d tb tcap ws rest live peak cnt fail HPREc FH C10 HIN HWIN HTX
    Hrest Hws Hstop HGL). }
cbv beta. intros W' c' _ (ly' & S' & regs' & mem' & md' & Ec & HJc & OK' & PO' & HP & HQ').
destruct HQ' as (QIN & QWK & QAB & QTX & QGL). subst c'.
exact (K ly' S' W' regs' mem' md' HJc OK' PO' HP QIN QWK QAB QTX QGL).
Qed.
End S.

(* ================= the first call, 0x84f58 -> 0x84f5c: stage A, skip_ws, the resume ================= *)
Section A1. Context {fx : YK11.FPState} {rc : YM05.RunCeil} (SK : YI16.sink_head).
Variable B : asyms.
Hypothesis HSS : FsShadowSyms B.
Hypothesis HSW : @skip_ws_spec fx rc SK tfibsegs B.

(* from parse_items' entry to its resume at 0x84f5c after skip_ws #1 (pf.c:217), where in->p has passed `{` and the
   white space ws: the resume state pi_ssB0 (the cursor atom xatom 20 holds the given c, which the state does not read),
   the journal from the entry (no tick, U unchanged), the registers stage B reads, struct pj_in, the text, the statics,
   the read-only view, the stack bytes of [sp, ot) outside struct pj_in as at the entry, and v's 56 bytes writable
   and defined *)
Lemma pi_sw1 : forall ly S U (W : world tfibsegs) regs mem md ch q ot v text len p (tb : list byte) tcap d STK
  (ws rest : list Z) c live peak cnt fail (Q : world tfibsegs -> config -> Prop),
  fpreU tfibsegs B STK ly S U W regs mem md ch -> FSupoisonU.fs_heads B ly S U ->
  FRAME_parse_items + STK_skip_ws <= STK ->
  YK11.getr regs 10 = w64 q -> YK11.getr regs 11 = w64 v -> YK11.getr regs 12 = w64 1 ->
  PjIn.pj_in_ok tfibsegs (mrestrict (w_H W) mem) q text len p d tb ->
  rd_win tfibsegs regs ly W mem q ot ->
  rd_text tfibsegs B ly S W mem text len tcap ->
  pobj tfibsegs B ly S W mem v -> PjStruct.pj_zero tfibsegs (mrestrict (w_H W) mem) v ->
  (v + 56 <= spZ regs - STK \/ ot <= v) -> (v + 56 <= text - HEAD \/ text + tcap <= v) ->
  0 <= d <= 1 ->
  ReaderRes.rest_at tb text p = 123 :: ws ++ rest -> Forall (fun c => PjGrammar.ws c = true) ws ->
  (forall c r, rest = c :: r -> PjGrammar.ws c = false) ->
  fs_glob tfibsegs W mem live peak cnt fail ->
  (forall ly' S' (W' : world tfibsegs) regs' mem' md',
     st_ok tfibsegs (Ereg regs' (fs_extraT ++ pi_xsR (p + 1 + Z.of_nat (length ws)) (text + len) (d + 1) regs 0 0 0 0 c))
       pi_ssB0 (restrict (w_H W') (mkst regs' (Z_to_bv 64 0x84f5c) mem' (seg_rom tfibsegs))) ->
     @ajournal rc SK tfibsegs B (STK + (ot - spZ regs)) ot ([(v, v + 56)] ++ FS_PSTAT_FP) ly S W (unpoison U mem) md []
       ly' S' W' (unpoison U mem') md' 0 ->
     ARU tfibsegs B ly' S' U W' mem' md' ->
     spZ regs' = spZ regs - 144 ->
     YK11.getr regs' 3 = YK11.getr regs 3 -> YK11.getr regs' 4 = YK11.getr regs 4 ->
     YK11.getr regs' 8 = w64 (q + 16) -> YK11.getr regs' 9 = w64 q -> YK11.getr regs' 18 = w64 1 ->
     YK11.getr regs' 19 = w64 v -> YK11.getr regs' 25 = w64 (pi_sh (q + 16)) ->
     YK11.getr regs' 26 = w64 SHADOW_OFF -> YK11.getr regs' 27 = w64 (pi_sh q) ->
     PjIn.pj_in_ok tfibsegs (mrestrict (w_H W') mem') q text len (p + 1 + Z.of_nat (length ws)) (d + 1) tb ->
     rd_text tfibsegs B ly' S' W' mem' text len tcap ->
     fs_glob tfibsegs W' mem' live peak cnt fail ->
     ablocks B ly' S' = ablocks B ly S ->
     arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W') mem') ->
     (forall a, spZ regs <= a < ot -> ~ (q <= a < q + 24) ->
        mbyte tfibsegs (mrestrict (w_H W') mem') a = mbyte tfibsegs (mrestrict (w_H W) mem) a /\
        (writable_at tfibsegs (mrestrict (w_H W) mem) a <-> writable_at tfibsegs (mrestrict (w_H W') mem') a)) ->
     (forall i, 0 <= i < 56 -> writable_at tfibsegs (mrestrict (w_H W') mem') (v + i)) ->
     (forall a, v <= a < v + 56 -> exists b, Mem.mrd tfibsegs (mrestrict (w_H W') mem') (Mem.wa a) = Some b) ->
     SRr tfibsegs W' (mkCfg (mkst regs' (Z_to_bv 64 0x84f5c) mem' (seg_rom tfibsegs)) md') Q) ->
  SRr tfibsegs W (YG0d.cfg_at tfibsegs A_parse_items regs mem md) Q.
Proof.
intros ly S U W regs mem md ch q ot v text len p tb tcap d STK ws rest c live peak cnt fail Q
  HPRE HHEADS HSTK H10 H11 H12 HIN HWIN HTX HPO HZERO HVSP HVTX Hd HREST Hws Hstop HGLOB K.
set (FP := [(v, v + 56)] ++ FS_PSTAT_FP).
pose proof HPRE as (HPREU & HRO).
pose proof asan_consts as (C1 & _ & C3 & _).
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof (fsw_sp B STK ly S U W regs mem md ch HPREU) as (Hal16 & HceilSTK & H47sp & HS0).
pose proof (fsw_ARU B STK ly S U W regs mem md ch HPREU) as HARU0.
pose proof HPREU as (HAPRE & _ & _). pose proof HAPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & _).
pose proof Hstk as (Hal16' & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HWIN as (Hsq & Hq24 & Hot16 & Hotly & Hpot).
pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN)
  as (Hq0 & Hq64 & Htext0 & Hptx & Htxhi & Hqapart & Htblen & Hq8 & Hdrange).
destruct (fsw_pobj_low B ly S W (unpoison U mem) md mem v HAR HPO) as (Hv4096 & Hvceil).
pose proof (fsw_pobj_off_img B ly S W (unpoison U mem) md mem v HAR HPO) as Hvimg.
pose proof HTX as (Htx4096 & Htxblk & Htxlen).
destruct (fsw_rblock_low B ly S W (unpoison U mem) md mem text tcap HAR Htxblk) as (Ht1 & Ht2).
assert (HSTKf : FRAME_parse_items = 144) by reflexivity.
assert (HSW0 : 0 <= STK_skip_ws) by (vm_compute; discriminate).
(* the text after `{`: in->p + 1 < in->end and the rest at p + 1 *)
pose proof (pi_rest_len _ q text len p d tb HIN) as Hrl. rewrite HREST in Hrl. cbn [length] in Hrl.
assert (Hp1 : p + 1 <= text + len) by lia.
assert (HREST1 : ReaderRes.rest_at tb text (p + 1) = ws ++ rest)
  by exact (pim_rest_skip tb text p [123] (ws ++ rest) ltac:(lia) HREST).
assert (HFP : forall a, v <= a < v + 56 -> inFP FP a)
  by (intros a Ha; exists (v, v + 56); split; [left; reflexivity | cbn [fst snd]; lia]).
(* ---- stage A ---- *)
apply (pi_stageA SK B HSS ly S U W regs mem md ch FP q ot v text len p tb tcap d STK Q HPREU ltac:(lia) H10 H11 H12
  HIN HWIN HTX HPO HZERO Hd HFP).
intros regsC memC mat HCA HMA HJ HARU.
set (mdC := with_vm_backing (m_vm_lazy md) mat md) in *.
destruct HCA as (R1 & Rsp & R10 & R8 & R9 & R18 & R19 & R25 & R26 & R27 & RF & HFR).
destruct HMA as (Vp & Ve & Vd & Vv0 & Vvz & FR & MG).
assert (RF' : forall r : bv 5, In r [3; 4; 20; 22; 23; 24]%bv -> YK11.getr regsC r = YK11.getr regs r)
  by (intros r Hr; rewrite Forall_forall in RF; exact (RF r Hr)).
(* the bytes stage A did not write: outside the frame, struct pj_in and v *)
assert (FRm : forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - 144 <= x < spZ regs) -> ~ (q <= x < q + 24) ->
  ~ (v <= x < v + 56) -> mrestrict (w_H W) memC (Z_to_bv 64 x) = mrestrict (w_H W) mem (Z_to_bv 64 x))
  by (intros x Hx H1 H2 H3; unfold mrestrict; rewrite (FR x Hx H1 H2 H3); reflexivity).
assert (EQtx : pim_eqon (mrestrict (w_H W) mem) (mrestrict (w_H W) memC) (text - HEAD) (text + tcap))
  by (intros a Ha; apply FRm; unfold HEAD in *; lia).
(* ---- skip_ws' data premises at the call ---- *)
assert (HIN1 : PjIn.pj_in_ok tfibsegs (mrestrict (w_H W) memC) q text len (p + 1) (d + 1) tb).
{ pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & JP & _).
  apply (pis_in_mk _ (mrestrict (w_H W) mem) q text len (p + 1) (d + 1) p d tb HIN Vp Ve Vd).
  - intros i Hi. apply (apresent_writable tfibsegs).
    apply (fsw_apresent_unpoison B ly S U W memC mdC (q + i) HARU); [lia|]. apply JP. lia.
  - eapply pim_eqon_sub; [exact EQtx | unfold HEAD; lia | lia].
  - lia.
  - lia. }
assert (HTX1 : rd_text tfibsegs B ly S W memC text len tcap).
{ split; [exact Htx4096|]. split; [|exact Htxlen].
  destruct Htxblk as (TB1 & TB2 & TB3 & TB4). split; [exact TB1|]. split; [exact TB2|]. split; [exact TB3|].
  apply (pim_eqon_val (mrestrict (w_H W) mem) _ (text - HEAD) 8 tcap); [|exact TB4].
  eapply pim_eqon_sub; [exact EQtx | lia | cbn; unfold HEAD in *; lia]. }
assert (NIMGv : forall a, v <= a < v + 56 -> ~ in_img tfibsegs a).
{ intros a Ha. destruct HPO as [[((cid & pos & Hin & Hc & H8 & H1 & H2) & _)|((b & m & Hb & H1 & H2) & _)] _].
  - exact (frm_img tfibsegs B LAWS ly S W (unpoison U mem) md cid pos a HAR Hin ltac:(lia)).
  - exact (blk_img tfibsegs B LAWS ly S W (unpoison U mem) md b m a HAR Hb ltac:(unfold HEAD in H1; lia)). }
assert (KIMG : forall a, in_img tfibsegs a -> mrestrict (w_H W) memC (Z_to_bv 64 a) = mrestrict (w_H W) mem (Z_to_bv 64 a)).
{ intros a Ha. pose proof (fs_segs_img a Ha) as Hlo. unfold FS_IMG_END in Hlo.
  apply FRm; [lia | lia | lia |].
  intros Hv. exact (NIMGv a Hv Ha). }
assert (HG1 : fs_glob tfibsegs W memC live peak cnt fail).
{ apply (pim_glob_eqon W W mem memC live peak cnt fail); [|exact HGLOB].
  intros a Ha. exact (KIMG a (pim_pstat_img a Ha)). }
assert (HRO1 : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) memC)).
{ apply (pim_ro_keep B (aview tfibsegs (w_H W) mem)); [exact HRO|].
  intros a Ha. apply aview_eq_of. exact (KIMG a (fsw_roP_img a Ha)). }
(* ---- the call ---- *)
apply (pic_call_sw SK B HSW (STK + (ot - spZ regs)) ot FP ly S W (unpoison U mem) md [] ly S U W memC mdC 0 regsC
  q text len (p + 1) (d + 1) tb tcap ws rest live peak cnt fail Q HJ HARU HRO1 HHEADS).
- rewrite R1. unfold YK0s.ret_ok. vm_compute. reflexivity.
- unfold raZ. rewrite R1. unfold w64. rewrite wz by lia. lia.
- rewrite (RF' 3%bv ltac:(cbn; tauto)). exact Hgp.
- rewrite (RF' 4%bv ltac:(cbn; tauto)). exact Htp.
- exact R10.
- exact R8.
- rewrite Rsp. rewrite Zminus_mod, Hal16. reflexivity.
- rewrite Rsp. lia.
- rewrite Rsp. lia.
- lia.
- exact HIN1.
- exact HTX1.
- exact HREST1.
- exact Hws.
- exact Hstop.
- exact HG1.
- intros ly' S' W' regs' mem' md' HJc OK' PO' HP QIN QWK QAB QTX QGL.
  rewrite R1. change (w64 0x84f5c) with (Z_to_bv 64 0x84f5c).
  set (xs := pi_xsR (p + 1 + Z.of_nat (length ws)) (text + len) (d + 1) regs 0 0 0 0 c).
  set (E := Ereg regs' (fs_extraT ++ xs)).
  assert (P : forall r : bv 5, acallee_saved (bv_unsigned r) -> YK11.getr regs' r = YK11.getr regsC r)
    by (intros r Hr; exact (fsw_pres _ _ r HP Hr)).
  assert (G2 : spZ regs' = spZ regs - 144) by (unfold spZ; rewrite (P 2%bv ltac:(pis_cs)); exact Rsp).
  assert (G9 : YK11.getr regs' 9 = w64 q) by (rewrite (P 9%bv ltac:(pis_cs)); exact R9).
  assert (G19 : YK11.getr regs' 19 = w64 v) by (rewrite (P 19%bv ltac:(pis_cs)); exact R19).
  assert (E2 : bv_unsigned (ew E 2) = spZ regs - 144) by (unfold E; rewrite (ew_Ereg_nat regs' _ 2 2%bv eq_refl); exact G2).
  assert (E9 : bv_unsigned (ew E 9) = q)
    by (unfold E; rewrite (ew_Ereg_nat regs' _ 9 9%bv eq_refl), G9; unfold w64; apply wz; lia).
  assert (E19 : bv_unsigned (ew E 19) = v)
    by (unfold E; rewrite (ew_Ereg_nat regs' _ 19 19%bv eq_refl), G19; unfold w64; apply wz; lia).
  destruct (pi_xsR_nth (p + 1 + Z.of_nat (length ws)) (text + len) (d + 1) regs 0 0 0 0 c)
    as (X0 & X1 & X2 & XR & X16 & X17 & X18 & X19 & X20).
  fold xs in X0, X1, X2, XR, X16, X17, X18, X19, X20.
  assert (EXn : forall j, ew E (xatom j) = nth j xs (Z_to_bv 64 0)) by (intros j; unfold E; apply fsw_ew_xatom).
  (* v's bytes across skip_ws: block or frame bytes off its empty footprint *)
  assert (VK : pim_eqon (mrestrict (w_H W) memC) (mrestrict (w_H W') mem') v (v + 56)).
  { intros x Hx.
    refine (proj2 (fsw_journal_kept_byte B _ _ _ ly S U W memC mdC ly' S' U W' mem' md' 0 x HJc HARU OK' PO' _
      (pim_inFP_nil x))).
    destruct HPO as [[((cid & pos & Hin & Hc & H8 & H1 & H2) & _)|((b & m & Hb & H1 & H2) & _)] _].
    - right. exists cid, pos. split; [exact Hin | lia].
    - left. exists b, m. split; [exact Hb | unfold HEAD in H1; lia]. }
  assert (VWC : forall i, 0 <= i < 56 -> writable_at tfibsegs (mrestrict (w_H W) memC) (v + i))
    by (intros i Hi; apply (writable_at_grows tfibsegs (mrestrict (w_H W) mem)); [exact MG | exact (proj2 HPO i Hi)]).
  assert (VW' : forall i, 0 <= i < 56 -> writable_at tfibsegs (mrestrict (w_H W') mem') (v + i))
    by (intros i Hi; apply (pim_eqon_wrat (mrestrict (w_H W) memC)); [eapply pim_eqon_sub; [exact VK | lia | lia] | exact (VWC i Hi)]).
  (* the frame across skip_ws: [sp - 144, sp) lies in skip_ws' window off in->p *)
  assert (HFR' : pi_frame (mrestrict (w_H W') mem') (spZ regs) regs).
  { apply (pis_frame_mb (mrestrict (w_H W) memC)); [|exact HFR].
    intros a Ha. exact (proj1 (QWK a ltac:(rewrite Rsp; lia) ltac:(lia))). }
  (* the resume *)
  pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ QIN) as (_ & _ & _ & Hp' & _).
  assert (HCS : Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W') mem') (spZ regs - 144)) pi_cs)
    by exact (pis_frame_chunks regs' xs _ (spZ regs) regs XR HFR').
  assert (HRS : Forall (YP09.region_ok tfibsegs E (mrestrict (w_H W') mem')) [pi_qR; pi_vR]).
  { constructor; [|constructor; [|constructor]].
    - apply (pis_q_ok E _ q text len (p + 1 + Z.of_nat (length ws)) (d + 1) tb E9);
        [rewrite EXn; exact X0 | rewrite EXn; exact X1 | rewrite EXn; exact X2 | exact QIN].
    - unfold pi_vR, YP09.region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E19. split; [lia|]. split; [lia|]. split; [intros o Ho; exact (VW' o ltac:(lia))|].
      assert (VZ : forall o, In o [8; 16; 24; 32; 40; 48] -> val_mem tfibsegs (mrestrict (w_H W') mem') (v + o) 8 0).
      { intros o Ho. rewrite Forall_forall in Vvz. apply (pim_eqon_val (mrestrict (w_H W) memC)); [|exact (Vvz o Ho)].
        cbn [In] in Ho. eapply pim_eqon_sub; [exact VK | |]; repeat (destruct Ho as [<-|Ho]; [lia|]); destruct Ho. }
      assert (V6 : val_mem tfibsegs (mrestrict (w_H W') mem') (v + 0) 4 6).
      { rewrite Z.add_0_r. apply (pim_eqon_val (mrestrict (w_H W) memC)); [|exact Vv0].
        eapply pim_eqon_sub; [exact VK | lia | cbn; lia]. }
      constructor; [apply (chunk_ok_val tfibsegs E _ v 0 4 (SLit 6) 6); [reflexivity | cbn; lia | cbn; lia | exact V6]|].
      constructor; [apply (chunk_ok_val tfibsegs E _ v 8 8 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | apply VZ; cbn; tauto]|].
      constructor; [apply (chunk_ok_val tfibsegs E _ v 16 8 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | apply VZ; cbn; tauto]|].
      constructor; [apply (chunk_ok_val tfibsegs E _ v 24 8 (SOff (xatom 16) 0) 0);
        [rewrite fsw_SOff0, EXn; exact X16 | cbn; lia | cbn; lia | apply VZ; cbn; tauto]|].
      constructor; [apply (chunk_ok_val tfibsegs E _ v 32 8 (SOff (xatom 17) 0) 0);
        [rewrite fsw_SOff0, EXn; exact X17 | cbn; lia | cbn; lia | apply VZ; cbn; tauto]|].
      constructor; [apply (chunk_ok_val tfibsegs E _ v 40 8 (SOff (xatom 18) 0) 0);
        [rewrite fsw_SOff0, EXn; exact X18 | cbn; lia | cbn; lia | apply VZ; cbn; tauto]|].
      constructor; [apply (chunk_ok_val tfibsegs E _ v 48 8 (SOff (xatom 19) 0) 0);
        [rewrite fsw_SOff0, EXn; exact X19 | cbn; lia | cbn; lia | apply VZ; cbn; tauto]|].
      constructor. }
  assert (HPD : YP09.pairwise_disjoint E (fsT_ret_regions 144 pi_cs [pi_qR; pi_vR])).
  { apply pairwise_disjoint_of_extents.
    unfold fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region, pi_qR, pi_vR, extent_of_region.
    cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite E2, E9, E19.
    unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address, FS_IMG_END in *.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
  assert (HGF : atoms_ok E pi_gfR).
  { unfold pi_gfR. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E9, E19, EXn, EXn, EXn, X0, X1, X2. rewrite !MState.unsigned_lit by lia.
    change (2 ^ 3) with 8. rewrite !Z.pow_0_r. unfold HEAD in *.
    split; [split; [lia | split; [exact Hq8 | lia]]|].
    assert (Hv8 : v mod 8 = 0) by (destruct HPO as [[(_ & Hm & _)|(_ & Hm & _)] _]; exact Hm).
    split; [split; [lia | split; [exact Hv8 | lia]]|].
    split; [split; [lia | split; [apply Z.mod_1_r | lia]]|].
    split; [split; [lia | split; [apply Z.mod_1_r | lia]]|].
    split; [|exact I]. split; [lia | split; [apply Z.mod_1_r | lia]]. }
  destruct (pic_after_callT B (STK + (ot - spZ regs)) ot FP [] ly S U W mem md W ly S U memC mdC 0 STK_skip_ws []
    (spZ regs) 144 regsC ly' S' U W' regs' mem' md' 0 xs pi_cs [pi_qR; pi_vR] pi_gfR 0x84f5c (proj1 HSS) (proj2 HSS)
    HJ HARU HJc ltac:(intros a Ha; exfalso; exact (pim_inFP_nil a Ha)) OK' PO' HP ltac:(rewrite Rsp; lia) ltac:(lia)
    HSW0 ltac:(rewrite Rsp, Zminus_mod, Hal16; reflexivity) ltac:(lia) ltac:(rewrite Rsp; lia)
    ltac:(vm_compute; reflexivity) HCS HRS HPD HGF) as (HJ2 & HARU2 & HST).
  change (0 + 0) with 0 in HJ2.
  apply (K ly' S' W' regs' mem' md' HST HJ2 HARU2 G2).
  + rewrite (P 3%bv ltac:(pis_cs)). exact (RF' 3%bv ltac:(cbn; tauto)).
  + rewrite (P 4%bv ltac:(pis_cs)). exact (RF' 4%bv ltac:(cbn; tauto)).
  + rewrite (P 8%bv ltac:(pis_cs)). exact R8.
  + exact G9.
  + rewrite (P 18%bv ltac:(pis_cs)). exact R18.
  + exact G19.
  + rewrite (P 25%bv ltac:(pis_cs)). exact R25.
  + rewrite (P 26%bv ltac:(pis_cs)). exact R26.
  + rewrite (P 27%bv ltac:(pis_cs)). exact R27.
  + exact QIN.
  + exact QTX.
  + exact QGL.
  + exact QAB.
  + exact (arodata_kept B _ _ _ ly S U W memC mdC ly' S' U W' mem' md' 0 HJc HARU OK' PO' pis_sink_nil
      (fun a _ => pim_inFP_nil a) HRO1).
  + intros a Ha Hq. rewrite Rsp in QWK. destruct (QWK a ltac:(lia) ltac:(lia)) as (M1 & W1).
    assert (Em : mrestrict (w_H W) memC (Z_to_bv 64 a) = mrestrict (w_H W) mem (Z_to_bv 64 a))
      by (apply FRm; lia).
    rewrite M1. split; [exact (pim_mb_of_mr _ _ _ _ a Em)|].
    rewrite <- W1. apply pim_wr_keep. exact Em.
  + exact VW'.
  + intros a Ha.
    assert (H0 : exists b, Mem.mrd tfibsegs (mrestrict (w_H W) mem) (Mem.wa a) = Some b).
    { destruct HZERO as (_ & (_ & _ & HZB)).
      pose proof (HZB (Z.to_nat (a - v)) ltac:(rewrite repeat_length; lia)) as Hx.
      rewrite pi_nth_repeat in Hx by lia. rewrite Z2Nat.id in Hx by lia. replace (v + (a - v)) with a in Hx by lia.
      eexists. exact Hx. }
    destruct (pis_mrd_grows _ _ (Mem.wa a) MG H0) as (b & Hb).
    exists b. unfold Mem.mrd, Mem.wa in *. rewrite (VK a Ha). exact Hb.
Qed.
End A1.
