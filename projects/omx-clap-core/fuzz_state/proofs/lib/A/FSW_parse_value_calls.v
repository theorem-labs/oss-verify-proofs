(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AFl3.v:106-108
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:383-389, 448-454, 493-498, 501-509 [Apache-2.0 OR MIT];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:625-631 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:208-214, 227-233 [Apache-2.0 OR MIT], for libreac/fuzz_identity's ASan
   build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_name_seg10.v, with its module paths and module names changed; 2634 of its 2686 lines of code are new or changed and 608 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSH_parse_value.v, with its module paths, module names and addresses changed; 133 of its 214 lines of code are new or changed and 2605 lines of the source are left out. *)
(* parse_value's OBJECT ARM (fs.asan 0x82f9c, pf.c:283-298) up to and through its parse_items call: the pre-call stage
   0x831a0 -> the callee entry A_parse_items (pvc_obj0) and the call step to the return state 0x832f8 (pvc_objcall).
   A lemma file for a Theorem Labs lane's composition in lib/A/FSH_parse_value.v (rule 24: no function proved here; the
   parse_value walk is new, a Theorem Labs lane's lookup / a Theorem Labs lane). Atom numbering and state shapes are
   FSH_parse_value.v's (8 = s0 = s, 9 = s1 = sp1, 19 = s3 = v, 20 = s4 = q, 23 = s7 = the shadow base, ...).
   MEASURED (sym_run_toN over pv_tbl from a state at 0x831a0 with NO memory region, vm_compute): the arm is
   0x831a0 `li a2, 1`, 0x831a4 `mv a0, s4`, 0x831a8 `mv a1, s3`, 0x831ac `j 0x832f4`, 0x832f4 `jal parse_items`
   (0x832e8-0x832f0, the array entry with a2 := 0, is skipped); the run reaches A_parse_items (0x84a04) with a0 = q,
   a1 = v, a2 = 1, ra = 0x832f8, every other register unchanged, no memory read or written (so no region for v and no
   shadow check: report-sites-A.tsv has no parse_value row in 0x831a0-0x832f4).
   The call step (same shape as FSH_parse_value.pv_strcall): the callee's fpreU by FSW_ret.fsw_fpreU_atFP, the callee's
   contract parse_items_spec as a Section hypothesis (owner: a Theorem Labs lane), and the journal composition by
   FSW_K3.fsw_ajournal_sub5 (not fsw_rt_atU3: v may sit in check_round_trip's fake frame, pobj's frame arm, which
   rt_atU3's three arms do not cover; the frame arms of sub5 do), FP1 = [(v, v + 56)] ++ FS_PSTAT_FP, k1 = rd_ev (ttrace
   (JObj ms)). The callee's frame-chain premise at q is a plain premise at the call state, as pv_strcall's chq
   (a Theorem Labs lane discharges it at composition from parse_value's own entry premise). *)
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
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSW_K FSW_frame FSW_ret FSH_Fn_reader FSW_rd
FSW_parse_value_tbl FSH_Fn_entry FSH_Fn_alloc FSW_K3 FSW_parse_string FSH_parse_value.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree PjGrammar PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterValue PjIn PjStruct ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Prog Require FSDocStrs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved.
   YI14 is required (not imported) so that the second probe names a loaded class. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YI14.
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* ================= the pre-call stage 0x831a0 -> A_parse_items ================= *)
(* the object arm's entry state: the register atoms only, no memory region (MEASURED: the arm reads and writes none) *)
Definition pvc_st0 : sstate := mkSS 0x831a0 sr_atoms [] None (mkFacts [] [] []).

Section O0. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.

Lemma pvc_st0_ok : forall (H : word -> bool) regs mem extra,
  st_ok tfibsegs (Ereg regs extra) pvc_st0 (restrict H (mkst regs (Z_to_bv 64 0x831a0) mem (seg_rom tfibsegs))).
Proof.
intros H regs mem extra.
rewrite restrict_mkst_fx. unfold pvc_st0. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn. exact I.
- cbn. repeat split.
Qed.

(* 0x831a0 -> THE CALLEE'S ENTRY A_parse_items (the run steps the `jal` 0x832f4): a2 := 1, a0 := s4 (q), a1 := s3 (v),
   ra := 0x832f8. No obligation, no token, no memory written. *)
Lemma pvc_obj0 : forall STK ot FP ly S S2 U (W : world tfibsegs) mem md regs mem2 md2 pos q v
  (Q : world tfibsegs -> config -> Prop),
  YK11.getr regs 19%bv = Z_to_bv 64 v -> YK11.getr regs 20%bv = Z_to_bv 64 q ->
  ajournal tfibsegs B STK ot FP ly S W (unpoison U mem) md [(0, pos)] ly S2 W (unpoison U mem2) md2 0 ->
  ARU tfibsegs B ly S2 U W mem2 md2 ->
  (forall ms' mdx',
     ms' = mkst (ms_regs ms') (Z_to_bv 64 A_parse_items) (ms_mem ms') (seg_rom tfibsegs) ->
     YK11.getr (ms_regs ms') 10%bv = Z_to_bv 64 q -> YK11.getr (ms_regs ms') 11%bv = Z_to_bv 64 v ->
     YK11.getr (ms_regs ms') 12%bv = Z_to_bv 64 1 -> YK11.getr (ms_regs ms') 1%bv = Z_to_bv 64 0x832f8 ->
     aregs_preserved regs (ms_regs ms') ->
     ajournal tfibsegs B STK ot FP ly S W (unpoison U mem) md [(0, pos)] ly S2 W (unpoison U (ms_mem ms')) mdx' 0 ->
     ARU tfibsegs B ly S2 U W (ms_mem ms') mdx' ->
     (forall x : word, mrestrict (w_H W) (ms_mem ms') x = mrestrict (w_H W) mem2 x) ->
     SRr tfibsegs W (mkCfg ms' mdx') Q) ->
  SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 0x831a0) mem2 (seg_rom tfibsegs)) md2) Q.
Proof.
intros STK ot FP ly S S2 U W mem md regs mem2 md2 pos q v Q R19 R20 HJ HARU K.
pose proof asan_consts as (C1 & _).
pose proof (pvc_st0_ok (w_H W) regs mem2 fs_extraT) as HS.
set (E := Ereg regs fs_extraT) in HS.
fsw_aj_run_toU pv_tbl_ok HS HJ HARU A_parse_items.
{ cbn [ss_mem pvc_st0]. apply awr_ok_nil. }
(* the state at the call: nothing written *)
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msF) =>
  assert (KEEP : forall x : word, mrestrict (w_H W) (ms_mem msF) x = mrestrict (w_H W) mem2 x) end.
{ intros x.
  rewrite (pv_frame_P _ _ _ _ (fun _ => False) HFr
    ltac:(intros a Ha; cbn [ss_mem pvc_st0] in Ha; exact (pv_wrange_nil _ _ Ha)) x ltac:(intros [])).
  reflexivity. }
lazymatch type of HS with st_ok _ ?Ey _ _ => set (E1 := Ey) in * end.
assert (F19 : ew E1 19 = Z_to_bv 64 v) by (subst E1; pv_ewo; subst E;
  rewrite (ew_Ereg_nat regs fs_extraT 19 19%bv eq_refl); exact R19).
assert (F20 : ew E1 20 = Z_to_bv 64 q) by (subst E1; pv_ewo; subst E;
  rewrite (ew_Ereg_nat regs fs_extraT 20 20%bv eq_refl); exact R20).
pv_reg HS (w_H W) (10%bv : bv 5) H10. pv_reg HS (w_H W) (11%bv : bv 5) H11.
pv_reg HS (w_H W) (12%bv : bv 5) H12. pv_reg HS (w_H W) (1%bv : bv 5) H1.
rewrite fsw_SOff0, F20 in H10. rewrite fsw_SOff0, F19 in H11.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) _ _ _ HS eq_refl) as Hshape.
lazymatch type of Hshape with _ = mkst _ (Z_to_bv 64 ?pc) _ _ =>
  let pc' := eval vm_compute in pc in change pc with pc' in Hshape end.
apply (K _ _); [exact Hshape | exact H10 | exact H11 | | | | exact HJ | exact HARU | exact KEEP].
- rewrite H12. apply pv_denot_lit. lia.
- rewrite H1. apply pv_denot_lit. lia.
- lazymatch type of HS with st_ok _ _ _ (restrict _ ?msF) =>
    apply (aregs_preserved_of_st_ok tfibsegs (w_H W) E1 _ msF regs fs_extraT HS) end;
    [subst E1; subst E; apply env_agree_refl | vm_compute; reflexivity].
Qed.
End O0.

(* ================= the parse_items call 0x832f4 -> 0x832f8 ================= *)
(* fuzz/alloc.c's statics are image bytes: they lie in fs.asan's last PT_LOAD, [0xa1000, 0x5fd000) (MEASURED:
   tfibsegs's fourth segment); restated from the pj_set walk's pS_img / pS_pstat_img (lib/A/Prog/FSW_pj_set_holds.v) *)
Lemma pvc_img : forall a, 659456 <= a < 6279168 -> in_img tfibsegs a.
Proof.
intros a Ha. unfold in_img.
assert (H : option_map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s))) (nth_error tfibsegs 3)
  = Some (659456, 5619712)) by (vm_compute; reflexivity).
destruct (nth_error tfibsegs 3) as [sg|] eqn:E; [|discriminate H].
exists sg. split; [exact (nth_error_In _ _ E)|].
cbn [option_map] in H. injection H as H1 H2. lia.
Qed.
Lemma pvc_pstat_img : forall a, inFP FS_PSTAT_FP a -> in_img tfibsegs a.
Proof.
intros a (r & Hr & Ha). unfold FS_PSTAT_FP in Hr. cbn [In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Ha; apply pvc_img; lia.
Qed.

Section OC. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* parse_value's level, = parse_items' level at this call (FSH_Fn_reader.v: parse_value at level k calls parse_items at
   level k) *)
Variable k : nat.
(* callee: parse_items at level k (owner: the Theorem Labs lane) *)
Hypothesis PI : @parse_items_spec fx rc SK tfibsegs B k.

(* the parse_items call: from the callee's entry state (pvc_obj0's hand-over) to its return 0x832f8. The caller's journal
   composes with the callee's over the FP-keyed core (FSW_K3.fsw_ajournal_sub5); the callee's window
   [sp1 - STK_parse_items (1 - k), ot) lies inside the caller's [ot - STK, ot) *)
Lemma pvc_objcall : forall STK ot FP ly S S2 U (W : world tfibsegs) mem md regsC memC mdC pos q s sp1 v text len p
    (tb : list byte) tcap (ms : list (list Z * PjTree.jv)) (pr : bool) (rest : list Z) live peak cnt fail
    (Qp : world tfibsegs -> config -> Prop),
  let tr := PjRoundTrip.ttrace (PjTree.JObj ms) in
  let wt := concat (WriterValue.wvpieces (PjTree.JObj ms) pr (Z.of_nat k)) in
  (k <= 1)%nat ->
  (* the state at the callee's entry *)
  spZ regsC = sp1 -> YK11.getr regsC 10%bv = Z_to_bv 64 q -> YK11.getr regsC 11%bv = Z_to_bv 64 v ->
  YK11.getr regsC 12%bv = Z_to_bv 64 1 -> YK11.getr regsC 1%bv = Z_to_bv 64 0x832f8 ->
  YK11.getr regsC 3%bv = w64 (as_gp B) -> YK11.getr regsC 4%bv = w64 (as_tp B) ->
  YK11.getr regsC 8%bv = Z_to_bv 64 s -> 0 <= s < 2 ^ 64 ->
  sp1 mod 16 = 0 -> ot - STK <= sp1 - STK_parse_items (1 - k) -> sp1 <= ot -> sp1 + 16 <= q ->
  (* the chain fpreU reads at the callee's entry (its s0 is still parse_value's s0 = s) *)
  (exists ch0, achain ly (aview tfibsegs (w_H W) (unpoison U memC)) sp1 s ch0) ->
  (* the chain parse_items' own premise reads at q (a Theorem Labs lane discharges it at composition) *)
  (exists chq, achain ly (aview tfibsegs (w_H W) (unpoison U memC)) sp1 q chq /\
     Forall (fun r => bad_next (fst (fst r)) (ly_top ly) (snd r) = true \/ q + 40 <= snd r) chq) ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) memC) ->
  FSupoisonU.fs_heads B ly S2 U ->
  (* parse_value's own frames premise (its fake frame (0, pos) is the one more live at the call) *)
  Z.of_nat (length (frames S)) <= FRL_parse_value (Z.of_nat k) ->
  PjIn.pj_in_ok tfibsegs (mrestrict (w_H W) memC) q text len p (Z.of_nat k) tb ->
  rd_win tfibsegs regsC ly W memC q ot ->
  rd_text tfibsegs B ly S2 W memC text len tcap ->
  ReaderRes.rest_at tb text p = wt ++ rest ->
  FSDocStrs.fs_doc_values (PjTree.JObj ms) -> FSDocStrs.fs_doc_strings (PjTree.JObj ms) ->
  PjRoundTrip.pj_wf ReaderRes.jr_strtod (PjTree.JObj ms) -> (PjTree.depth (PjTree.JObj ms) <= 2 - k)%nat ->
  pobj tfibsegs B ly S2 W memC v -> PjStruct.pj_zero tfibsegs (mrestrict (w_H W) memC) v ->
  (v + 56 <= sp1 - STK_parse_items (1 - k) \/ ot <= v) -> (v + 56 <= text - HEAD \/ text + tcap <= v) ->
  fs_glob tfibsegs W memC live peak cnt fail -> quiet cnt fail (Z.of_nat (length tr)) ->
  rd_sizes_ok tr -> live + rd_live tr < 2 ^ 64 ->
  st_nev S2 + rd_ev tr <= EV_MAX -> blocks_bytes S2 + rd_live tr <= LIVE_MAX ->
  ajournal tfibsegs B STK ot FP ly S W (unpoison U mem) md [(0, pos)] ly S2 W (unpoison U memC) mdC 0 ->
  ARU tfibsegs B ly S2 U W memC mdC ->
  (* parse_items' footprint is parse_value's (at composition FP = [(v, v + 56)] ++ FS_PSTAT_FP itself) *)
  (forall a, inFP ([(v, v + 56)] ++ FS_PSTAT_FP) a -> inFP FP a) ->
  (forall ly2 S3 W2 regs2 mem2 md2 (D Da : list (Z * Z)),
     Permutation Da D ->
     ajournal tfibsegs B STK ot FP ly S W (unpoison U mem) md [(0, pos)] ly2 S3 W2
       (unpoison (U ++ rd_heads Da) mem2) md2 (rd_ev tr) ->
     ARU tfibsegs B ly2 S3 (U ++ rd_heads Da) W2 mem2 md2 ->
     aregs_preserved regsC regs2 ->
     Forall (fun r => YK11.getr regs2 r = YK11.getr regsC r) [8; 9; 18; 20; 23; 24; 26]%bv ->
     YK11.getr regs2 10%bv = w64 0 ->
     PjIn.pj_in_ok tfibsegs (mrestrict (w_H W2) mem2) q text len (p + Z.of_nat (length wt)) (Z.of_nat k) tb ->
     wkeep tfibsegs W W2 memC mem2 sp1 ot q 24 ->
     Permutation (ablocks B ly2 S3) (ablocks B ly S2 ++ rd_hblocks D) ->
     rtree tfibsegs B ly2 S3 W2 mem2 v (PjTree.JObj ms) D -> rd_sum D = PjGrammar.held tr ->
     (length D <= length tr)%nat ->
     pobj tfibsegs B ly2 S3 W2 mem2 v -> rd_text tfibsegs B ly2 S3 W2 mem2 text len tcap ->
     (exists peak', peak <= peak' /\
        fs_glob tfibsegs W2 mem2 (live + PjGrammar.held tr) peak' (cnt + Z.of_nat (length tr)) fail) ->
     SRr tfibsegs W2 (YG0d.cfg_at tfibsegs 0x832f8 regs2 mem2 md2) Qp) ->
  SRr tfibsegs W (YG0d.cfg_at tfibsegs A_parse_items regsC memC mdC) Qp.
Proof.
intros STK ot FP ly S S2 U W mem md regsC memC mdC pos q s sp1 v text len p tb tcap ms pr rest live peak cnt fail Qp
  tr wt Hk Csp C10 C11 C12 C1 C3 C4 C8 Hs64 Hal16 Hwin Hsp1ot Hq16 HCH0 HCHq HRO FH Hfr0 HIN HWIN HTX Hrest Hvals
  Hstrs Hwf Hdep HPo HZo Hvst Hvtx HGL Hquiet Hsz Hlive Hnev Hbb HJ HARU HFPv K.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof asan_consts as (C1a & _).
destruct HCH0 as [ch0 HCH0q].
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _). cbn [app] in Hfrs.
assert (Hk01 : (1 - k = 0 \/ 1 - k = 1)%nat) by lia.
assert (HSTK0 : 0 <= STK_parse_items (1 - k)) by (destruct Hk01 as [E | E]; rewrite E; vm_compute; discriminate).
(* the callee's fpreU at its entry (its s0 is still parse_value's s0 = s) *)
assert (HPREc : fpreU tfibsegs B (STK_parse_items (1 - k)) ly S2 U W regsC memC mdC ch0).
{ apply (fsw_fpreU_atFP B STK ot FP ly S U W (unpoison U mem) md [(0, pos)] ly S2 W memC mdC 0 regsC
    (STK_parse_items (1 - k)) (sp1 - ot) ch0 HJ HARU HRO);
    [rewrite Csp; lia | | lia | exact HSTK0 | lia | rewrite C1; vm_compute; reflexivity | | rewrite C3; reflexivity
     | rewrite C4; reflexivity |].
  - assert (Hot16 : ot mod 16 = 0) by (pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _);
      exact (proj1 Hstk)).
    rewrite Zminus_mod, Hal16, Hot16. reflexivity.
  - unfold raZ. rewrite C1. rewrite (unsigned_lit_small 0x832f8) by lia. lia.
  - unfold s0Z. rewrite Csp, C8, (unsigned_lit_small s) by lia. exact HCH0q. }
(* the callee's frames premise: parse_value's own, plus its fake frame (0, pos) *)
assert (HFR : Z.of_nat (length (frames S2)) <= FRL_parse_value (Z.of_nat k + 1))
  by (rewrite Hfrs; cbn [length]; unfold FRL_parse_value in *; lia).
assert (HCHq' : exists chq, achain ly (aview tfibsegs (w_H W) (unpoison U memC)) (spZ regsC) q chq /\
  Forall (fun r => bad_next (fst (fst r)) (ly_top ly) (snd r) = true \/ q + 40 <= snd r) chq)
  by (rewrite Csp; exact HCHq).
assert (Hsp16 : spZ regsC + 16 <= q) by (rewrite Csp; exact Hq16).
assert (Hvst' : v + 56 <= spZ regsC - STK_parse_items (1 - k) \/ ot <= v) by (rewrite Csp; exact Hvst).
(* parse_items' contract at the callee's entry *)
eapply SRr_bind.
{ exact (PI ly S2 U W regsC memC mdC ch0 q ot v text len p tb tcap ms pr rest live peak cnt fail
    Hk HPREc FH HFR C10 C11 C12 HIN HWIN Hsp16 HCHq' HTX Hrest Hvals Hstrs Hwf Hdep HPo HZo Hvst' Hvtx HGL
    Hquiet Hsz Hlive Hnev Hbb). }
cbv beta. intros W' c' _ (D & Da & HDa & (ly' & S' & regs' & mem' & md' & Ec & HJc & OK' & PO' & HP & HQ')).
destruct HQ' as (Q10 & QIN & QWK & QPERM & QT & QSUM & QLEN & QPO & QTX & QGL).
subst c'. rewrite C1.
(* the journals compose: the callee's window [sp1 - STK_parse_items (1 - k), ot) lies inside the caller's
   [ot - STK, ot); the callee's footprint is v (a live block byte, a byte of a frame of frames S, or of parse_value's own
   fake frame) or a static (an image byte), all in parse_value's FP *)
assert (HJ2 : ajournal tfibsegs B STK ot FP ly S W (unpoison U mem) md ([] ++ [(0, pos)]) ly' S' W'
  (unpoison (U ++ rd_heads Da) mem') md' (0 + rd_ev tr)).
{ apply (fsw_ajournal_sub5 B STK ot FP ly S W (unpoison U mem) md [(0, pos)] ly S2 W (unpoison U memC) mdC 0
    (STK_parse_items (1 - k) + (ot - spZ regsC)) ot ([(v, v + 56)] ++ FS_PSTAT_FP) [] ly' S' W'
    (unpoison (U ++ rd_heads Da) mem') md' (rd_ev tr) HJ HJc); [rewrite Csp; lia | lia |].
  intros a Ha. pose proof (HFPv a Ha) as HaFP.
  destruct Ha as ((rlo, rhi) & Hr & Har). cbn [fst snd] in Har.
  apply in_app_or in Hr as [Hr | Hr].
  - cbn [In] in Hr. destruct Hr as [E | []]. injection E as <- <-.
    destruct HPo as [[((cid & pos' & Hcp & _ & _ & H1 & H2) & _) | ((b & m & Hb & H1 & H2) & _)] _].
    + rewrite Hfrs in Hcp. cbn [In] in Hcp. destruct Hcp as [E | Hcp].
      * injection E as <- <-. right; right; right; left.
        exists 0, pos. split; [left; reflexivity | left; unfold in_zr; cbn [fst snd]; lia].
      * right; right; right; right. split; [exact HaFP|].
        exists cid, pos'. split; [exact Hcp | unfold in_zr, frame_rng; cbn [fst snd]; lia].
    + left. split; [exact HaFP|]. exists b, m. split; [exact Hb | unfold HEAD in H1; lia].
  - right; right; left. split; [exact HaFP | exact (pvc_pstat_img a (ex_intro _ (rlo, rhi) (conj Hr Har)))]. }
cbn [app] in HJ2. rewrite Z.add_0_l in HJ2.
assert (HARU2 : ARU tfibsegs B ly' S' (U ++ rd_heads Da) W' mem' md')
  by (split; [exact (proj1 HJ2) | split; [exact OK' | exact PO']]).
assert (REGS : Forall (fun r => YK11.getr regs' r = YK11.getr regsC r) [8; 9; 18; 20; 23; 24; 26]%bv).
{ repeat (apply Forall_cons; [apply (fsw_pres regsC regs' _ HP); pv_cs|]). apply Forall_nil. }
rewrite Csp in QWK.
exact (K ly' S' W' regs' mem' md' D Da HDa HJ2 HARU2 HP REGS Q10 QIN QWK QPERM QT QSUM QLEN QPO QTX QGL).
Qed.
End OC.
