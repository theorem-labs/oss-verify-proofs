(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the IMAGE B (fs.asan-ubsan, UBSan trap mode) walk of parse_value against
   lib/B/FSH_Fn_reader.v parse_value_spec (CTX-free; the text of a working branch 035561e0fd4 = a working branch
   311139dc663: skip_ws_spec's post keeps [sp, ot) but [q, q + 8), parse_value_spec's k = 0 arm
   `q = spZ regs + 8 /\ raZ regs <= q`; both rulings a Theorem Labs lane and after the k = 0 gap report): the
   COMPOSITION, parse_value_holds : parse_value_spec tfibsegs B k (stages: FSW_parse_value.v; decode table:
   FSW_parse_value_tbl.v).
   rule 24 (lane brief (internal path), CONFIRM a Theorem Labs lane): proves function
   parse_value - fuzz_state image B asan-ubsan, entry 0x82fcc, level-indexed k = 0..2, narrow success form. Reuse search
   (run by a Theorem Labs lane, verbatim in the lane brief), the three result lines:
     proof-index: parse_value: 14 named, 35 by address, 0 related, 13 released lemma(s), an earlier delivery 58 named and 794
       name(s) holding it, 17 UNRELEASED working-branch file(s) in the lemma index, 0 UNRELEASED hit(s) on live working heads
     proof-index: parse_value_spec: 0 named, 0 by address, 0 related, 6 released lemma(s), 0 by file name, an earlier delivery 51
       named and 12 name(s) holding it, 2 UNRELEASED working-branch file(s) in the lemma index, 0 UNRELEASED hit(s) on live
       working heads
     proof-index: 0x82fcc: 0 named, 0 by address, 0 related, 0 released lemma(s), 0 by file name, an earlier delivery 0 named and
       0 name(s) holding it, 0 UNRELEASED working-branch file(s) in the lemma index, 105 UNRELEASED hit(s) on live working heads
   Port source (Lookup result): ported from a working branch 75e39a1f41d:proofs/omx-clap-core/fuzz_state/lib/
   B/Prog/{parse_value_disp,PvStr,PvItems,PvJoin,PvStep,PvHolds,ParseUnit}.v (COMPLETE old-form image-B walk of
   parse_value: entry/fake frame/skip_ws call pv_pro + pv_disp, parse_string arm pv_str_ok, parse_items arm pv_items_ok,
   epilogue pv_join + pvs_none, composition parse_value_step / parse_value_holds_b; all Qed, no admit), restated against
   parse_value_spec's frame lemma by lemma, NOT Required, NOT bridged; new-frame shape from image A's walk
   a working branch (ebb53c68f7d .. 00c6d1886e6: lib/A/FSH_parse_value.v pv_grant / pv_resume_sm /
   pv_seg0 / pv_sm / pv_epi / pv_strcall, lib/A/FSW_parse_value_calls.v pvc_objcall), copied and re-measured for B. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/B/Prog/FSW_parse_value_holds.v, with its module paths, module names and addresses changed; 800 of its 894 lines of code are new or changed and 2063 lines of the source are left out. *)
(* parse_value's STRING ARM as one segment (fs.asan, pf.c:283-298): from pv_front's string-arm hand-over at 0x831b0
   (the dispatch byte 34) to parse_value's return, into fpostU with parse_value_spec k's post for u = JStr s.
   The chain: FSH_parse_value.pv_str0 (0x831b0 -> A_parse_string), the parse_string call (pv_strcall', below, over
   parse_string_spec as a Section hypothesis), FSH_parse_value.pv_str1 (0x831d0 -> 0x83318) and FSH_parse_value.pv_epi
   (0x83318 -> ret). Also here: the two frame chains the callees' fpreU and parse_string's C5 premise read at the arm
   memory (pv_chains / pv_arm_chains), from parse_value_spec's chain premise (right arm: fpreU's chain at s0; left arm:
   s0 = q, 81b380a2d74) and the prologue's saved ra / s0. A lemma file for a Theorem Labs lane's composition (rule 24: no
   function proved here; parse_value's CONFIRM is FSH_parse_value.v's). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
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
FSW_parse_value_tbl FSH_Fn_entry FSH_Fn_alloc FSW_K3 FSW_parse_string FSH_parse_value FSW_parse_value_calls
FSW_parse_value_obj FSW_pj_string.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree PjGrammar PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterValue PjIn PjStruct ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Prog Require FSDocStrs FSW_pj_set_heads.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSW_parse_items_mdl.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Mem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YG0s.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved.
   YI14 is required (not imported) so that the second probe names a loaded class. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YI14.
Fail Definition probe_SK : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI16.sink_head := _.
Fail Definition probe_SH : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI14.sink_syms := _.

Section CHN. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.

(* ACem.rdword_of_val_mem, restated (ACem is not in this file's import set) *)
Lemma pv_rdword : forall H mem a v,
  val_mem tfibsegs (mrestrict H mem) a 8 v -> 0 <= v < 2 ^ 64 -> rdword (aview tfibsegs H mem) a = Some v.
Proof.
intros H mem a v Hv Hr.
assert (B0 : forall k, (k < 8)%nat -> aview tfibsegs H mem (a + Z.of_nat k) = Some (le_byte v 8 k)).
{ intros k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold le_byte. apply Z.mod_mod. lia. }
unfold rdword.
rewrite <- (Z.add_0_r a) at 1. change 0 with (Z.of_nat 0) at 1. rewrite (B0 0%nat) by lia.
change 1 with (Z.of_nat 1). rewrite (B0 1%nat) by lia. change 2 with (Z.of_nat 2) at 1. rewrite (B0 2%nat) by lia.
change 3 with (Z.of_nat 3). rewrite (B0 3%nat) by lia. change 4 with (Z.of_nat 4). rewrite (B0 4%nat) by lia.
change 5 with (Z.of_nat 5). rewrite (B0 5%nat) by lia. change 6 with (Z.of_nat 6). rewrite (B0 6%nat) by lia.
change 7 with (Z.of_nat 7). rewrite (B0 7%nat) by lia.
f_equal. apply YG0s.le_bytes8. exact Hr.
Qed.

(* ================= the frame chains the callees' fpreU / C5 premises read, at the arm memory ================= *)
(* a chain whose base is at least q + 40 has every NEXT pointer a stop or above q + 40 *)
Lemma pv_fpchain_far : forall (load : Z -> option Z) bp top ch qq, fpchain load bp top ch -> qq + 40 <= bp ->
  Forall (fun r => bad_next (fst (fst r)) top (snd r) = true \/ qq + 40 <= snd r) ch.
Proof.
intros load bp top ch qq. revert bp. induction ch as [|[[fp ra] nfp] ch IH]; intros bp H Hq; [constructor|].
cbn [fpchain] in H. destruct H as (E & H8 & Hra & Hnfp & H4 & Hrest). subst fp.
destruct (bad_next bp top nfp) eqn:Eb.
- subst ch. constructor; [left; cbn [fst snd]; exact Eb | constructor].
- assert (Hn : bp < nfp).
  { unfold bad_next in Eb. apply orb_false_iff in Eb as [Eb _]. apply orb_false_iff in Eb as [Eb1 _].
    apply Z.leb_gt in Eb1. lia. }
  constructor; [right; cbn [snd]; lia | apply (IH nfp Hrest); lia].
Qed.

(* FSW_parse_items_loop.pi_fpchain_kept, restated (that file is another lane's walk): fpchain reads at bp - 8 and
   bp - 16 only, so a reader change off [qq, qq + 24) keeps a chain whose NEXT pointers stay off it *)
Lemma pv_fpchain_kept : forall (l1 l2 : Z -> option Z) qq s top cl bp,
  fpchain l1 bp top cl -> (bp = qq \/ qq + 40 <= bp) -> s + 16 <= bp -> bp < top - 16 ->
  Forall (fun r => bad_next (fst (fst r)) top (snd r) = true \/ qq + 40 <= snd r) cl ->
  (forall a, s <= a -> a + 8 <= top -> a + 8 <= qq \/ qq + 24 <= a -> l2 a = l1 a) -> fpchain l2 bp top cl.
Proof.
intros l1 l2 qq s top cl. induction cl as [|[[fp ra] nfp] cl IH]; intros bp H Hq Hsb Htp HF Hl; cbn [fpchain] in *.
- destruct H as (r & Hr & Hr2). exists r. rewrite Hl by lia. split; assumption.
- destruct H as (E & H8 & Hra & Hnfp & H4 & Hrest). subst fp.
  inversion HF as [|? ? Hr HF']; subst. cbn [fst snd] in Hr.
  split; [reflexivity|]. split; [exact H8|]. split; [rewrite Hl by lia; exact Hra|].
  split; [rewrite Hl by lia; exact Hnfp|]. split; [exact H4|].
  destruct (bad_next bp top nfp) eqn:Eb; [exact Hrest|].
  assert (Hn : bp < nfp /\ nfp < top - 16).
  { unfold bad_next in Eb. apply orb_false_iff in Eb as [Eb _]. apply orb_false_iff in Eb as [Eb1 Eb2].
    apply Z.leb_gt in Eb1. apply Z.leb_gt in Eb2. lia. }
  apply (IH nfp Hrest); [| lia | lia | exact HF' | exact Hl].
  destruct Hr as [Hr | Hr]; [exfalso; congruence | right; exact Hr].
Qed.

Lemma pv_achain_kept : forall ly (rd1 rd2 : reader) s qq bp ch,
  achain ly rd1 s bp ch -> (bp = qq \/ qq + 40 <= bp) ->
  Forall (fun r => bad_next (fst (fst r)) (ly_top ly) (snd r) = true \/ qq + 40 <= snd r) ch ->
  (forall a, s <= a < ly_top ly -> ~ (qq <= a < qq + 24) -> rd2 a = rd1 a) -> achain ly rd2 s bp ch.
Proof.
intros ly rd1 rd2 s qq bp ch H Hb HF Hrd. unfold achain in *.
destruct H as [H | (H1 & H2 & H3 & H4 & H5)]; [left; exact H|]. right.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [|exact H5].
apply (pv_fpchain_kept (rdword rd1) (rdword rd2) qq s (ly_top ly) ch bp H4 Hb H1 H2 HF).
intros a Ha Htp Hout. apply rdword_ext. intros j Hj. apply Hrd; lia.
Qed.

(* parse_value's own record (s, ra, s0) on the entry's chain at s0 (right arm: fpreU's chain, all its words above
   q + 24; left arm: s0 = q and the spec's chain at q), and the chain at q, both at a reader that agrees with the
   entry's on [s, top) off [q, q + 24) and holds the prologue's saved ra / s0 *)
Lemma pv_chains : forall ly (rd0 rd' : reader) (regs : bvmap 5 word) q sp1 ch,
  achain ly rd0 (spZ regs) (s0Z regs) ch ->
  4096 <= raZ regs -> spZ regs mod 8 = 0 -> alloc_ceiling <= spZ regs -> ly_top ly <= 2 ^ 64 ->
  spZ regs <= q -> q + 24 <= ly_top ly -> sp1 + 16 <= spZ regs ->
  (q = spZ regs /\ (bad_next q (ly_top ly) (s0Z regs) = true \/ q + 40 <= s0Z regs) \/
   spZ regs + 16 <= q /\ s0Z regs = q /\ exists chq, achain ly rd0 (spZ regs) q chq /\
     Forall (fun r => bad_next (fst (fst r)) (ly_top ly) (snd r) = true \/ q + 40 <= snd r) chq) ->
  (forall a, spZ regs <= a < ly_top ly -> ~ (q <= a < q + 24) -> rd' a = rd0 a) ->
  rdword rd' (spZ regs - 8) = Some (raZ regs) -> rdword rd' (spZ regs - 16) = Some (s0Z regs) ->
  (exists ch0, achain ly rd' sp1 (spZ regs) ch0) /\
  (exists chq, achain ly rd' sp1 q chq /\
     Forall (fun r => bad_next (fst (fst r)) (ly_top ly) (snd r) = true \/ q + 40 <= snd r) chq).
Proof.
intros ly rd0 rd' regs q sp1 ch HCH Hra Hs8 Hsc Htop Hsq Hq24 Hsp1 HSPEC Hrd R8 R16.
assert (T : exists cht, achain ly rd' (spZ regs) (s0Z regs) cht /\
   Forall (fun r => bad_next (fst (fst r)) (ly_top ly) (snd r) = true \/ q + 40 <= snd r) cht).
{ destruct HSPEC as [(Eq & Hb) | (Hq16 & Es0 & chq & Hchq & HF)].
  - exists ch. unfold achain in HCH.
    destruct HCH as [(Hl & Ech) | (H1 & H2 & H3 & H4 & H5)].
    + subst ch. split; [left; split; [exact Hl | reflexivity] | constructor].
    + assert (Hfar : q + 40 <= s0Z regs).
      { destruct Hb as [Hb | Hb]; [|exact Hb]. unfold bad_next in Hb.
        apply orb_true_iff in Hb as [Hb | Hb]; [apply orb_true_iff in Hb as [Hb | Hb]|].
        - apply Z.leb_le in Hb. lia.
        - apply Z.leb_le in Hb. lia.
        - apply negb_true_iff in Hb. apply Z.eqb_neq in Hb. exfalso; exact (Hb H3). }
      pose proof (pv_fpchain_far (rdword rd0) (s0Z regs) (ly_top ly) ch q H4 Hfar) as HF.
      split; [|exact HF].
      apply (pv_achain_kept ly rd0 rd' (spZ regs) q (s0Z regs) ch); [| right; exact Hfar | exact HF | exact Hrd].
      right. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4 | exact H5].
  - exists chq. split; [|exact HF]. rewrite Es0.
    exact (pv_achain_kept ly rd0 rd' (spZ regs) q q chq Hchq (or_introl eq_refl) HF Hrd). }
destruct T as (cht & Hcht & HFt).
assert (C0 : achain ly rd' sp1 (spZ regs) ((spZ regs, raZ regs, s0Z regs) :: cht)).
{ exact (achain_push ly rd' rd' (spZ regs) (s0Z regs) (raZ regs) cht sp1 Hcht Htop (fun a _ => eq_refl) R8 R16 Hra Hsc
    Hs8 ltac:(lia) Hsp1). }
split; [exists ((spZ regs, raZ regs, s0Z regs) :: cht); exact C0|].
destruct HSPEC as [(Eq & Hb) | (Hq16 & Es0 & chq & Hchq & HF)].
- exists ((spZ regs, raZ regs, s0Z regs) :: cht). split; [rewrite Eq; exact C0|].
  constructor; [cbn [fst snd]; rewrite <- Eq; exact Hb | exact HFt].
- exists chq. split; [|exact HF].
  apply (achain_lower ly rd' (spZ regs) sp1 q chq); [|lia].
  exact (pv_achain_kept ly rd0 rd' (spZ regs) q q chq Hchq (or_introl eq_refl) HF Hrd).
Qed.

(* the arm form: the entry's afn_pre chain and ARU, the arm memory's ARU, the raw keep above s off [q, q + 8) and the
   prologue's saved words (pv_saved_ok) give the two chains at the arm memory *)
Lemma pv_arm_chains : forall ly S S2 U (W : world tfibsegs) regs mem md ma mda q sp1 ch,
  achain ly (aview tfibsegs (w_H W) (unpoison U mem)) (spZ regs) (s0Z regs) ch ->
  4096 <= raZ regs -> spZ regs mod 8 = 0 -> alloc_ceiling + 16 <= spZ regs -> ly_top ly <= 2 ^ 64 ->
  spZ regs <= q -> q + 24 <= ly_top ly -> sp1 + 16 <= spZ regs ->
  ARU tfibsegs B ly S U W mem md -> ARU tfibsegs B ly S2 U W ma mda ->
  (q = spZ regs /\ (bad_next q (ly_top ly) (s0Z regs) = true \/ q + 40 <= s0Z regs) \/
   spZ regs + 16 <= q /\ s0Z regs = q /\ exists chq,
     achain ly (aview tfibsegs (w_H W) (unpoison U mem)) (spZ regs) q chq /\
     Forall (fun r => bad_next (fst (fst r)) (ly_top ly) (snd r) = true \/ q + 40 <= snd r) chq) ->
  (forall a, spZ regs <= a < 2 ^ 64 -> ~ (q <= a < q + 8) ->
     mrestrict (w_H W) ma (Z_to_bv 64 a) = mrestrict (w_H W) mem (Z_to_bv 64 a)) ->
  pv_saved_ok (mrestrict (w_H W) ma) (spZ regs) regs ->
  (exists ch0, achain ly (aview tfibsegs (w_H W) (unpoison U ma)) sp1 (spZ regs) ch0) /\
  (exists chq, achain ly (aview tfibsegs (w_H W) (unpoison U ma)) sp1 q chq /\
     Forall (fun r => bad_next (fst (fst r)) (ly_top ly) (snd r) = true \/ q + 40 <= snd r) chq).
Proof.
intros ly S S2 U W regs mem md ma mda q sp1 ch HCH Hra Hs8 Hsc Htop Hsq Hq24 Hsp1 HARU0 HARUa HSPEC AGR VSV.
(* above alloc_ceiling the unpoisoned memories are the memories *)
assert (UPa : forall a, alloc_ceiling <= a < 2 ^ 64 ->
  mrestrict (w_H W) (unpoison U ma) (Z_to_bv 64 a) = mrestrict (w_H W) ma (Z_to_bv 64 a)).
{ intros a Ha. unfold mrestrict. rewrite (pv_unp_high B ly S2 U W ma mda a HARUa Ha). reflexivity. }
assert (UP0 : forall a, alloc_ceiling <= a < 2 ^ 64 ->
  mrestrict (w_H W) (unpoison U mem) (Z_to_bv 64 a) = mrestrict (w_H W) mem (Z_to_bv 64 a)).
{ intros a Ha. unfold mrestrict. rewrite (pv_unp_high B ly S U W mem md a HARU0 Ha). reflexivity. }
pose proof asan_consts as (C1 & _).
assert (Hs64 : spZ regs < 2 ^ 64) by (unfold spZ; pose proof (u64_range (YK11.getr regs 2%bv)); lia).
apply (pv_chains ly (aview tfibsegs (w_H W) (unpoison U mem)) (aview tfibsegs (w_H W) (unpoison U ma)) regs q sp1 ch
  HCH Hra Hs8 ltac:(lia) Htop Hsq Hq24 Hsp1 HSPEC).
- intros a Ha Hq. apply pvo_aview_pt. rewrite (UPa a ltac:(lia)), (UP0 a ltac:(lia)). apply AGR; lia.
- apply pv_rdword; [|unfold raZ; exact (u64_range _)].
  pose proof (VSV 0%nat ltac:(lia)) as V. cbn [Z.of_nat nth pv_saved pv_extra0 firstn tl] in V.
  replace (spZ regs - 8 * (0 + 1)) with (spZ regs - 8) in V by lia.
  apply (pvo_val_tr (mrestrict (w_H W) ma)); [|exact V].
  intros j Hj. apply UPa. lia.
- apply pv_rdword; [|unfold s0Z; exact (u64_range _)].
  pose proof (VSV 1%nat ltac:(lia)) as V. cbn [Z.of_nat nth pv_saved pv_extra0 firstn tl Pos.of_succ_nat] in V.
  replace (spZ regs - 8 * (1 + 1)) with (spZ regs - 16) in V by lia.
  apply (pvo_val_tr (mrestrict (w_H W) ma)); [|exact V].
  intros j Hj. apply UPa. lia.
Qed.
End CHN.

Section SC2. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis HPS : parse_string_spec tfibsegs B.

(* FSH_parse_value.pv_strcall with what the string arm carries across the callee ADDED: the frame's flag word (off the
   callee's FP FS_PSTAT_FP, in parse_value's own fake frame (0, pos) of S2: pvo_val_keep_call), v's 56 bytes (v in a
   frame or a live block of S2: FSW_pj_string.pjs_v_keep_call) and v's placement (FSW_rd.pobj_kept_call). Otherwise
   the statement and the proof are pv_strcall's. *)
Lemma pv_strcall' : forall STK ot FP ly S S2 U (W : world tfibsegs) mem md regsC memC mdC pos q s sp1 text len p d
    (tb : list byte) tcap Q live peak cnt fail v FL (Qp : world tfibsegs -> config -> Prop),
  spZ regsC = sp1 -> YK11.getr regsC 10%bv = Z_to_bv 64 q -> YK11.getr regsC 1%bv = Z_to_bv 64 0x831d0 ->
  YK11.getr regsC 3%bv = w64 (as_gp B) -> YK11.getr regsC 4%bv = w64 (as_tp B) ->
  YK11.getr regsC 8%bv = Z_to_bv 64 s -> 0 <= s < 2 ^ 64 ->
  sp1 mod 16 = 0 -> alloc_ceiling <= ly_stk_lo ly -> ly_stk_lo ly + STK_parse_string <= sp1 ->
  ot - STK <= sp1 - STK_parse_string -> sp1 <= ot -> sp1 + 16 <= q ->
  (exists ch0, achain ly (aview tfibsegs (w_H W) (unpoison U memC)) sp1 s ch0) ->
  (exists chq, achain ly (aview tfibsegs (w_H W) (unpoison U memC)) (sp1 - FRAME_parse_string) q chq) ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) memC) ->
  FSupoisonU.fs_heads B ly S2 U ->
  PjIn.pj_in_ok tfibsegs (mrestrict (w_H W) memC) q text len p d tb ->
  rd_win tfibsegs regsC ly W memC q ot ->
  rd_text tfibsegs B ly S2 W memC text len tcap ->
  p < text + len -> nth_error tb (Z.to_nat (p - text)) = Some (Z_to_bv 8 34) ->
  plain_run tb text len p Q ->
  fs_glob tfibsegs W memC live peak cnt fail -> quiet cnt fail 1 ->
  Q + 1 + HEAD < MALLOC_MAX -> live + Q + 1 < 2 ^ 64 ->
  st_nev S2 + EV_fuzz_malloc <= EV_MAX -> blocks_bytes S2 + (Q + 1 + HEAD) <= LIVE_MAX ->
  ajournal tfibsegs B STK ot FP ly S W (unpoison U mem) md [(0, pos)] ly S2 W (unpoison U memC) mdC 0 ->
  ARU tfibsegs B ly S2 U W memC mdC ->
  (forall a, inFP FS_PSTAT_FP a ->
     (inFP FP a /\ exists b n, In (b, n) (ablocks B ly S2) /\ b <= a < b + req_size n) \/
     in_tmp_block (ablocks B ly S) (ablocks B ly S2) a \/ (inFP FP a /\ in_img tfibsegs a)) ->
  (* ADDED: the flag word of parse_value's frame (0, pos), off FS_PSTAT_FP; v placed, off FS_PSTAT_FP *)
  In (0, pos) (frames S2) ->
  val_mem tfibsegs (mrestrict (w_H W) memC) (frame_addr ly 0 pos + 56) 8 FL ->
  (forall x, frame_addr ly 0 pos + 56 <= x < frame_addr ly 0 pos + 64 -> ~ inFP FS_PSTAT_FP x) ->
  ((exists cid pos', In (cid, pos') (frames S2) /\ 0 <= cid /\
      frame_addr ly cid pos' <= v /\ v + 56 <= frame_addr ly cid pos' + fs_frame_bytes cid) \/
   (exists b m, In (b, m) (ablocks B ly S2) /\ b + HEAD <= v /\ v + 56 <= b + req_size m)) ->
  (forall x, v <= x < v + 56 -> ~ inFP FS_PSTAT_FP x) ->
  pobj tfibsegs B ly S2 W memC v ->
  (forall ly2 S3 W2 regs2 mem2 md2 a,
     ajournal tfibsegs B STK ot FP ly S W (unpoison U mem) md [(0, pos)] ly2 S3 W2
       (unpoison (U ++ [(a - HEAD, HEAD)]) mem2) md2 EV_fuzz_malloc ->
     ARU tfibsegs B ly2 S3 (U ++ [(a - HEAD, HEAD)]) W2 mem2 md2 ->
     aregs_preserved regsC regs2 ->
     YK11.getr regs2 10%bv = w64 a -> 4096 + HEAD <= a ->
     ablocks B ly2 S3 = ablocks B ly S2 ++ [(a - HEAD, Q + 1 + HEAD)] ->
     fs_rblock tfibsegs B ly2 S3 W2 mem2 a (Q + 1) ->
     PjStruct.pj_cbytes tfibsegs (mrestrict (w_H W2) mem2) a (run_at tb text p Q) ->
     PjIn.pj_in_ok tfibsegs (mrestrict (w_H W2) mem2) q text len (p + Q + 2) d tb ->
     wkeep tfibsegs W W2 memC mem2 sp1 ot q 24 ->
     rd_text tfibsegs B ly2 S3 W2 mem2 text len tcap ->
     fs_glob tfibsegs W2 mem2 (live + Q + 1) (Z.max peak (live + Q + 1)) (cnt + 1) fail ->
     (* ADDED *)
     val_mem tfibsegs (mrestrict (w_H W2) mem2) (frame_addr ly 0 pos + 56) 8 FL ->
     (forall x, v <= x < v + 56 ->
        mbyte tfibsegs (mrestrict (w_H W2) mem2) x = mbyte tfibsegs (mrestrict (w_H W) memC) x) ->
     pobj tfibsegs B ly2 S3 W2 mem2 v ->
     FSupoisonU.fs_heads B ly2 S3 (U ++ [(a - HEAD, HEAD)]) ->
     SRr tfibsegs W2 (YG0d.cfg_at tfibsegs 0x831d0 regs2 mem2 md2) Qp) ->
  SRr tfibsegs W (YG0d.cfg_at tfibsegs A_parse_string regsC memC mdC) Qp.
Proof.
intros STK ot FP ly S S2 U W mem md regsC memC mdC pos q s sp1 text len p d tb tcap Q live peak cnt fail v FL Qp
  Csp C10 C1 C3 C4 C8 Hs64 Hal16 Hceil HSTK Hwin Hsp1ot Hq16 HCH0 HCH HRO FH HIN HWIN HTX Hplen Hquote HPR HGL Hquiet
  HQm Hlive Hnev Hbb HJ HARU HFP Hin0 HVFL HNFL LOC HVNF HPo K.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof asan_consts as (C1a & _).
destruct HCH as [chq HCHq]. destruct HCH0 as [ch0 HCH0q].
assert (HPREc : fpreU tfibsegs B STK_parse_string ly S2 U W regsC memC mdC ch0).
{ apply (fsw_fpreU_atFP B STK ot FP ly S U W (unpoison U mem) md [(0, pos)] ly S2 W memC mdC 0 regsC
    STK_parse_string (sp1 - ot) ch0 HJ HARU HRO);
    [rewrite Csp; lia | | lia | | lia | rewrite C1; vm_compute; reflexivity | | rewrite C3; reflexivity
     | rewrite C4; reflexivity |].
  - assert (Hot16 : ot mod 16 = 0) by (pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _);
      exact (proj1 Hstk)).
    rewrite Zminus_mod, Hal16, Hot16. reflexivity.
  - unfold STK_parse_string. vm_compute. discriminate.
  - unfold raZ. rewrite C1. rewrite (unsigned_lit_small 0x831d0) by lia. lia.
  - unfold s0Z. rewrite Csp, C8, (unsigned_lit_small s) by lia. exact HCH0q. }
eapply SRr_bind.
{ exact (HPS ly S2 U W regsC memC mdC ch0 q ot text len p d tb tcap Q live peak cnt fail
    HPREc FH ltac:(exists chq; rewrite Csp; exact HCHq) ltac:(rewrite Csp; lia) C10 HIN HWIN HTX Hplen Hquote HPR HGL
    Hquiet HQm Hlive Hnev Hbb). }
cbv beta. intros W' c' _ (a & ly' & S' & regs' & mem' & md' & Ec & HJc & OK' & PO' & HP & HQ').
destruct HQ' as (Q10 & Q4096 & Qab & QRB & Qcb & QIN & QWK & QTX & QGL).
subst c'. rewrite C1.
(* ADDED: the callee's own journal keeps the flag word, v's bytes and v's placement *)
assert (HARUc : ARU tfibsegs B ly' S' (U ++ [(a - HEAD, HEAD)]) W' mem' md')
  by (split; [exact (proj1 HJc) | split; [exact OK' | exact PO']]).
assert (Hbl : forall b n, In (b, n) (ablocks B ly S2) -> In (b, n) (ablocks B ly' S')).
{ intros b n Hb. rewrite Qab. apply in_or_app. left. exact Hb. }
assert (VFL' : val_mem tfibsegs (mrestrict (w_H W') mem') (frame_addr ly 0 pos + 56) 8 FL).
{ apply (pvo_val_keep_call B _ _ _ ly S2 U W memC mdC ly' S' (U ++ [(a - HEAD, HEAD)]) W' mem' md' _ 0 pos
    (frame_addr ly 0 pos + 56) 8 FL HJc HARU OK' PO' Hin0); [lia | lia | | | exact HVFL].
  - change (fs_frame_bytes 0) with 64. change (Z.of_nat 8) with 8. lia.
  - intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply HNFL. lia. }
assert (VKEEP : forall x, v <= x < v + 56 ->
  mbyte tfibsegs (mrestrict (w_H W') mem') x = mbyte tfibsegs (mrestrict (w_H W) memC) x).
{ destruct LOC as [Hf | Hb].
  - exact (pjs_v_keep_call B true _ _ ly S2 U W memC mdC ly' S' (U ++ [(a - HEAD, HEAD)]) W' mem' md' _ v
      HJc HARU HARUc Hf Hbl).
  - exact (pjs_v_keep_call B false _ _ ly S2 U W memC mdC ly' S' (U ++ [(a - HEAD, HEAD)]) W' mem' md' _ v
      HJc HARU HARUc Hb Hbl). }
assert (FH' : FSupoisonU.fs_heads B ly' S' (U ++ [(a - HEAD, HEAD)])).
{ intros r Hr. apply in_app_or in Hr as [Hr | Hr].
  - destruct (FH r Hr) as (H1 & m & H2 & H3). split; [exact H1|]. exists m. split; [exact (Hbl _ _ H2) | exact H3].
  - destruct Hr as [<- | []]. cbn [fst snd]. split; [reflexivity|]. exists (Q + 1 + HEAD).
    split; [rewrite Qab; apply in_or_app; right; left; reflexivity|].
    pose proof HPR as (HQ0 & _). unfold req_size, HEAD. destruct (Z.eqb_spec (Q + 1 + 16) 0); lia. }
assert (HPo' : pobj tfibsegs B ly' S' W' mem' v).
{ apply (pobj_kept_call B _ _ _ ly S2 U W memC mdC ly' S' (U ++ [(a - HEAD, HEAD)]) W' mem' md' _ v HJc HARU OK' PO'
    HVNF); [| exact FH' | exact HPo].
  intros x Hx Hsh. pose proof (pv_pstat_rng x Hx). unfold SHADOW_OFF in Hsh. lia. }
destruct (fsw_rt_atU3 B STK ot FP ly S W (unpoison U mem) md [(0, pos)] ly S2 U W memC mdC 0
  (STK_parse_string + (ot - spZ regsC)) ot FS_PSTAT_FP [] ly' S' (U ++ [(a - HEAD, HEAD)]) W' mem' md' EV_fuzz_malloc
  HJ HJc OK' PO' ltac:(rewrite Csp; lia) ltac:(lia) HFP) as (HJ2 & HARU2).
apply (K ly' S' W' regs' mem' md' a);
  [exact HJ2 | exact HARU2 | exact HP | exact Q10 | exact Q4096 | exact Qab | exact QRB | exact Qcb | exact QIN
   | rewrite Csp in QWK; exact QWK | exact QTX | exact QGL | exact VFL' | exact VKEEP | exact HPo' | exact FH'].
Qed.
End SC2.

(* ================= the string arm ================= *)
Section SAR. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASF : astack_free_law tfibsegs B.
Hypothesis FFL : frame_flag_lawP tfibsegs B.
Hypothesis HPS : parse_string_spec tfibsegs B.
Variable k : nat.

(* ---- small byte helpers ---- *)
Lemma pvs_wr_of_mbyte : forall (m : word -> option byte) x b, 0 <= x < 2 ^ 64 -> ~ in_img tfibsegs x ->
  mbyte tfibsegs m x = Some b -> writable_at tfibsegs m x.
Proof.
intros m x b Hx Hn H. unfold mbyte in H. rewrite (YCbq.seg_rom_none tfibsegs x Hx Hn) in H.
destruct (m (Z_to_bv 64 x)) eqn:E; [|discriminate H].
unfold writable_at, wview. rewrite E. discriminate.
Qed.

(* Mem.bytes_at reads through mrd, which is mbyte at a word address: an mbyte agreement on the range moves it *)
Lemma pvs_bytes_mb : forall (m m' : word -> option byte) a bs, Mem.bytes_at tfibsegs m a bs ->
  (forall i, (i < length bs)%nat -> mbyte tfibsegs m' (a + Z.of_nat i) = mbyte tfibsegs m (a + Z.of_nat i)) ->
  Mem.bytes_at tfibsegs m' a bs.
Proof.
intros m m' a bs (H0 & H1 & H) E. split; [exact H0|]. split; [exact H1|].
intros i Hi. change (Mem.mrd tfibsegs m' (Mem.wa (a + Z.of_nat i))) with (mbyte tfibsegs m' (a + Z.of_nat i)).
rewrite (E i Hi). exact (H i Hi).
Qed.

(* a sub-run of a zero run *)
Lemma pvs_zero_sub : forall (m : word -> option byte) v o n, Mem.bytes_at tfibsegs m v (repeat (Z_to_bv 8 0) 56) ->
  0 <= o -> o + Z.of_nat n <= 56 -> Mem.bytes_at tfibsegs m (v + o) (repeat (Z_to_bv 8 0) n).
Proof.
intros m v o n (H0 & H1 & H) Ho Hn. rewrite repeat_length in H1. split; [lia|]. split; [rewrite repeat_length; lia|].
intros i Hi. rewrite repeat_length in Hi.
replace (v + o + Z.of_nat i) with (v + Z.of_nat (Z.to_nat o + i)) by lia.
rewrite (H (Z.to_nat o + i)%nat) by (rewrite repeat_length; lia).
rewrite !nth_error_repeat by lia. reflexivity.
Qed.

Lemma pvs_le4_4 : forall (m : word -> option byte) a, 0 <= a -> a + 4 <= 2 ^ 64 ->
  val_mem tfibsegs m a 4 4 -> Mem.bytes_at tfibsegs m a (Mem.le4 (Z_to_bv 64 4)).
Proof.
intros m a H0 H1 Hv. split; [exact H0|]. split; [cbn; lia|].
intros i Hi. change (length (Mem.le4 (Z_to_bv 64 4))) with 4%nat in Hi.
change (Mem.mrd tfibsegs m (Mem.wa (a + Z.of_nat i))) with (mbyte tfibsegs m (a + Z.of_nat i)).
rewrite (Hv i Hi). destruct i as [|[|[|[|i]]]]; [vm_compute; reflexivity.. | lia].
Qed.

(* ================= the string arm: pv_front's hand-over at 0x831b0 -> parse_value's post ================= *)
Lemma pv_strarm : forall ly S U (W : world tfibsegs) regs mem md ch q ot v text len p (tb : list byte) tcap
    (s : list Z) (pr : bool) (ws rest : list Z) live peak cnt fail S2 pos ms' mdx',
  let tr := PjRoundTrip.ttrace (PjTree.JStr s) in
  let wt := concat (WriterValue.wvpieces (PjTree.JStr s) pr (Z.of_nat k)) in
  (k <= 2)%nat ->
  fpreU tfibsegs B (STK_parse_value (2 - k)) ly S U W regs mem md ch -> FSupoisonU.fs_heads B ly S U ->
  PjIn.pj_in_ok tfibsegs (mrestrict (w_H W) mem) q text len p (Z.of_nat k) tb -> rd_win tfibsegs regs ly W mem q ot ->
  ReaderRes.rest_at tb text p = ws ++ wt ++ rest -> plain_bytes s ->
  pobj tfibsegs B ly S W mem v ->
  (v + 56 <= spZ regs - STK_parse_value (2 - k) \/ ot <= v) -> (v + 56 <= text - HEAD \/ text + tcap <= v) ->
  quiet cnt fail (Z.of_nat (length tr)) -> rd_sizes_ok tr -> live + rd_live tr < 2 ^ 64 ->
  st_nev S + rd_ev tr <= EV_MAX -> blocks_bytes S + rd_live tr <= LIVE_MAX ->
  (* pv_front's string-arm hand-over (b0 = 34) *)
  In (0, pos) (frames S2) -> frames S2 = (0, pos) :: frames S ->
  ablocks B ly S2 = ablocks B ly S -> st_nev S2 = st_nev S -> blocks_bytes S2 = blocks_bytes S ->
  ms' = mkst (ms_regs ms') (Z_to_bv 64 0x831b0) (ms_mem ms') (seg_rom tfibsegs) ->
  YK11.getr (ms_regs ms') 8%bv = Z_to_bv 64 (spZ regs) ->
  YK11.getr (ms_regs ms') 9%bv = Z_to_bv 64 (32 * ((spZ regs - 160) / 32)) ->
  YK11.getr (ms_regs ms') 18%bv = Z_to_bv 64 (frame_addr ly 0 pos) ->
  YK11.getr (ms_regs ms') 19%bv = Z_to_bv 64 v ->
  YK11.getr (ms_regs ms') 20%bv = Z_to_bv 64 q ->
  YK11.getr (ms_regs ms') 23%bv = Z_to_bv 64 SHADOW_OFF ->
  YK11.getr (ms_regs ms') 24%bv = Z_to_bv 64 (SHADOW_OFF + frame_addr ly 0 pos / 8) ->
  YK11.getr (ms_regs ms') 26%bv = Z_to_bv 64 (frame_addr ly 0 pos) ->
  YK11.getr (ms_regs ms') 3%bv = YK11.getr regs 3%bv ->
  YK11.getr (ms_regs ms') 4%bv = YK11.getr regs 4%bv ->
  pv_inv (mrestrict (w_H W) (ms_mem ms')) regs (spZ regs) (frame_addr ly 0 pos) (flag_addr ly 0 pos) q
    (text + len) (p + Z.of_nat (length ws)) [34] ->
  ajournal tfibsegs B (STK_parse_value (2 - k) + (ot - spZ regs)) ot ([(v, v + 56)] ++ FS_PSTAT_FP) ly S W
    (unpoison U mem) md [(0, pos)] ly S2 W (unpoison U (ms_mem ms')) mdx' 0 ->
  ARU tfibsegs B ly S2 U W (ms_mem ms') mdx' ->
  YK11.getr (ms_regs ms') 2%bv = Z_to_bv 64 (32 * ((spZ regs - 160) / 32)) ->
  wkeep tfibsegs W W mem (ms_mem ms') (spZ regs) ot q 24 ->
  PjIn.pj_in_ok tfibsegs (mrestrict (w_H W) (ms_mem ms')) q text len (p + Z.of_nat (length ws)) (Z.of_nat k) tb ->
  rd_text tfibsegs B ly S2 W (ms_mem ms') text len tcap ->
  pobj tfibsegs B ly S2 W (ms_mem ms') v -> PjStruct.pj_zero tfibsegs (mrestrict (w_H W) (ms_mem ms')) v ->
  fs_glob tfibsegs W (ms_mem ms') live peak cnt fail ->
  (exists ch0, achain ly (aview tfibsegs (w_H W) (unpoison U (ms_mem ms'))) (32 * ((spZ regs - 160) / 32))
     (spZ regs) ch0) ->
  (exists chq, achain ly (aview tfibsegs (w_H W) (unpoison U (ms_mem ms'))) (32 * ((spZ regs - 160) / 32)) q chq) ->
  SRr tfibsegs W (mkCfg ms' mdx')
    (fun W' c' => exists D Da,
       Permutation Da D /\
       fpostU tfibsegs B (STK_parse_value (2 - k) + (ot - spZ regs)) ot ([(v, v + 56)] ++ FS_PSTAT_FP) regs ly S U W
         mem md (rd_ev tr) (U ++ rd_heads Da)
         (fun ly' S' W' regs' mem' md' =>
            YK11.getr regs' 10%bv = w64 0 /\
            PjIn.pj_in_ok tfibsegs (mrestrict (w_H W') mem') q text len
              (p + Z.of_nat (length ws) + Z.of_nat (length wt)) (Z.of_nat k) tb /\
            wkeep tfibsegs W W' mem mem' (spZ regs) ot q 24 /\
            Permutation (ablocks B ly' S') (ablocks B ly S ++ rd_hblocks D) /\
            rtree tfibsegs B ly' S' W' mem' v (PjTree.JStr s) D /\ rd_sum D = PjGrammar.held tr /\
            (length D <= length tr)%nat /\
            pobj tfibsegs B ly' S' W' mem' v /\
            rd_text tfibsegs B ly' S' W' mem' text len tcap /\
            (exists peak', peak <= peak' /\
               fs_glob tfibsegs W' mem' (live + PjGrammar.held tr) peak' (cnt + Z.of_nat (length tr)) fail)) W' c').
Proof.
intros ly S U W regs mem md ch q ot v text len p tb tcap s pr ws rest live peak cnt fail S2 pos ms' mdx' tr wt
  Hk HPRE FH HIN0 HWIN Hrest Hplain HPo0 Hvst Hvtx Hquiet Hsz Hlive Hnev Hbb
  Hin0 Hfrs2 Hab2 Hnev2 Hbb2 Hshape R8 R9 R18 R19 R20 R23 R24 R26 R3 R4 HINV HJ HARU
  R2 HWK HIN HTX HPo HZo HGL HCH0 HCHq.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HPREU & HRO). pose proof HPREU as (HAPRE & OK0 & PO0).
pose proof HAPRE as (HAR0 & Hret & Hra4 & Hgp & Htp & Hstk & _).
assert (HARU0 : ARU tfibsegs B ly S U W mem md) by (split; [exact HAR0 | split; [exact OK0 | exact PO0]]).
pose proof (fsw_sp B _ ly S U W regs mem md ch HPREU) as (Hal16 & Hceil & H47 & HSTK0).
pose proof HWIN as (Hsq & Hq24 & Hot16 & Hotly & Hpot).
pose proof Hstk as (_ & _ & Hlo0 & Hslo & Hshi & H47' & _ & _ & Htop2).
pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN0) as (_ & _ & _ & (Htp1 & Htp2) & _).
pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN) as (Hq0' & Hq64' & Ht0' & (Hp1' & Hp2') & Hend' & _).
assert (FSs : STK_parse_string + 255 <= STK_parse_value (2 - k)).
{ assert (Hk02 : (k = 0 \/ k = 1 \/ k = 2)%nat) by lia.
  destruct Hk02 as [E | [E | E]]; rewrite E; vm_compute; discriminate. }
pose proof (pv_stk k Hk) as FS4.
pose proof (fsw_pobj_low B ly S W (unpoison U mem) md mem v HAR0 HPo0) as (Hv4096 & Hvc).
assert (LOC : (exists cid pos', In (cid, pos') (frames S) /\ 0 <= cid /\ frame_addr ly cid pos' mod 8 = 0 /\
                 frame_addr ly cid pos' <= v /\ v + 56 <= frame_addr ly cid pos' + fs_frame_bytes cid) \/
              (exists b m, In (b, m) (ablocks B ly S) /\ b + HEAD <= v /\ v + 56 <= b + req_size m)).
{ destruct HPo0 as [[(Hf & _) | (Hb & _)] _]; [left; exact Hf | right; exact Hb]. }
assert (Hv8 : v mod 8 = 0) by (destruct HPo0 as [[(_ & H & _) | (_ & H & _)] _]; exact H).
(* v's bytes are client bytes: not image, not statics, off the shadow band *)
assert (VNI : forall x, v <= x < v + 56 -> ~ in_img tfibsegs x).
{ intros x Hx. refine (proj2 (al_client_img _ _ LAWS ly S W (unpoison U mem) md x HAR0 _)).
  destruct LOC as [(cid & pos' & Hc & _ & _ & H1 & H2) | (b & m & Hb & H1 & H2)].
  - right; left. exists cid, pos'. split; [exact Hc | lia].
  - left. exists b, m. split; [exact Hb | unfold HEAD in H1; lia]. }
assert (VNF : forall x, v <= x < v + 56 -> ~ inFP FS_PSTAT_FP x)
  by (intros x Hx Hf; exact (VNI x Hx (pvc_pstat_img x Hf))).
assert (HVB : v + 56 <= SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= v).
{ destruct LOC as [(cid & pos' & Hc & _ & _ & H1 & H2) | (b & m & Hb & H1 & H2)].
  - destruct (frames_bounds tfibsegs B LAWS ly S W (unpoison U mem) md cid pos' HAR0 Hc) as (_ & _ & Happ).
    unfold in_app, kLowShadowBeg, ASAN_CEIL, kHighMemBeg in Happ. unfold SHADOW_OFF. lia.
  - destruct (al_blocks tfibsegs B LAWS ly S W (unpoison U mem) md b m HAR0 Hb) as (_ & _ & _ & Happ & _).
    unfold in_app, kLowShadowBeg, ASAN_CEIL, kHighMemBeg in Happ. unfold SHADOW_OFF, HEAD in *. lia. }
(* ---- the text at in->p: the quoted plain string ---- *)
assert (Hwt : wt = 34 :: s ++ [34]).
{ unfold wt. cbn [WriterValue.wvpieces]. exact (FSW_parse_items_mdl.pim_spieces_plain s Hplain). }
assert (HR1 : ReaderRes.rest_at tb text (p + Z.of_nat (length ws)) = 34 :: s ++ 34 :: rest).
{ rewrite (pvo_rest_at tb text p ws wt rest Htp1 Hrest), Hwt. cbn [app]. rewrite <- app_assoc. reflexivity. }
assert (HRlen : Z.of_nat (length (ReaderRes.rest_at tb text (p + Z.of_nat (length ws))))
  = text + len - (p + Z.of_nat (length ws))).
{ pose proof HIN as (_ & _ & _ & _ & _ & _ & _ & _ & Hlen & _). unfold ReaderRes.rest_at, ReaderRes.zb.
  rewrite length_map, length_skipn. lia. }
destruct (FSW_parse_items_mdl.pim_key_run tb text len (p + Z.of_nat (length ws)) s rest ltac:(lia) HRlen HR1 Hplain)
  as (Hrun & Hrunat & Hq34 & Hplt).
assert (Hech : length (flat_map PjRoundTrip.ech s) = length s)
  by (rewrite (FSW_parse_items_mdl.pim_ech_plain s Hplain); reflexivity).
assert (Htr : tr = [PjGrammar.EAlloc (Datatypes.S (length s))])
  by (unfold tr; cbn [PjRoundTrip.ttrace]; rewrite Hech; reflexivity).
assert (TEV : rd_ev tr = EV_fuzz_malloc) by (rewrite Htr; cbn [rd_ev fold_right]; lia).
assert (TLV : rd_live tr = Z.of_nat (length s) + 1 + HEAD)
  by (rewrite Htr; cbn [rd_live fold_right PjGrammar.esize]; lia).
assert (TLN : length tr = 1%nat) by (rewrite Htr; reflexivity).
assert (TSZ : Z.of_nat (length s) + 1 + HEAD < MALLOC_MAX).
{ rewrite Htr in Hsz. unfold rd_sizes_ok in Hsz. apply Forall_cons_iff in Hsz as [He _].
  cbn [PjGrammar.esize] in He. lia. }
(* ---- 0x831b0 -> the callee's entry A_parse_string (pv_str0) ---- *)
assert (RAa : range_addressable (aview tfibsegs (w_H W) (ms_mem ms')) SHADOW_OFF v 56)
  by (destruct HPo as [[(_ & _ & Hr) | (_ & _ & Hr)] _]; exact Hr).
assert (WVa : forall o, 0 <= o < 56 -> writable_at tfibsegs (mrestrict (w_H W) (ms_mem ms')) (v + o))
  by (destruct HPo as [_ Hw]; exact Hw).
assert (HAWR : forall a, in_zr a (v, 56) ->
  awr_byte tfibsegs B (STK_parse_value (2 - k) + (ot - spZ regs)) ot ([(v, v + 56)] ++ FS_PSTAT_FP)
    (ablocks B ly S) (ablocks B ly S2) ly [(0, pos)] (frames S) a).
{ intros a Ha. unfold in_zr in Ha. cbn [fst snd] in Ha.
  assert (HFPa : inFP ([(v, v + 56)] ++ FS_PSTAT_FP) a)
    by (exists (v, v + 56); split; [left; reflexivity | cbn [fst snd]; lia]).
  destruct LOC as [(cid & pos' & Hc & Hc0 & H8 & H1 & H2) | (b & m & Hb & H1 & H2)].
  - right; right. split; [exact HFPa|]. exists cid, pos'. split; [exact Hc | unfold in_zr, frame_rng; cbn [fst snd]; lia].
  - left. right; left. split; [exact HFPa|]. exists b, m. split; [rewrite Hab2; exact Hb | unfold HEAD in H1; lia]. }
rewrite Hshape.
apply (pv_str0 B (STK_parse_value (2 - k) + (ot - spZ regs)) ot ([(v, v + 56)] ++ FS_PSTAT_FP) ly S S2 U W mem md
  (ms_regs ms') (ms_mem ms') mdx' pos q v _ R19 R23 R20 Hv4096 ltac:(lia) Hv8 ltac:(lia) HVB RAa WVa HAWR HJ HARU).
intros msC mdC HshC C10 C1c HPC Vty HJC HARUC KEEPC.
assert (KZC : forall z, 0 <= z < 2 ^ 64 -> ~ (v <= z < v + 4) ->
  mrestrict (w_H W) (ms_mem msC) (Z_to_bv 64 z) = mrestrict (w_H W) (ms_mem ms') (Z_to_bv 64 z)).
{ intros z Hz Hn. apply KEEPC. rewrite unsigned_lit_small by lia. exact Hn. }
assert (P2 : YK11.getr (ms_regs msC) 2%bv = Z_to_bv 64 (32 * ((spZ regs - 160) / 32)))
  by (rewrite (fsw_pres (ms_regs ms') (ms_regs msC) 2%bv HPC ltac:(pv_cs)); exact R2).
assert (P3 : YK11.getr (ms_regs msC) 3%bv = YK11.getr regs 3%bv)
  by (rewrite (fsw_pres (ms_regs ms') (ms_regs msC) 3%bv HPC ltac:(pv_cs)); exact R3).
assert (P4 : YK11.getr (ms_regs msC) 4%bv = YK11.getr regs 4%bv)
  by (rewrite (fsw_pres (ms_regs ms') (ms_regs msC) 4%bv HPC ltac:(pv_cs)); exact R4).
assert (P8 : YK11.getr (ms_regs msC) 8%bv = Z_to_bv 64 (spZ regs))
  by (rewrite (fsw_pres (ms_regs ms') (ms_regs msC) 8%bv HPC ltac:(pv_cs)); exact R8).
assert (P9 : YK11.getr (ms_regs msC) 9%bv = Z_to_bv 64 (32 * ((spZ regs - 160) / 32)))
  by (rewrite (fsw_pres (ms_regs ms') (ms_regs msC) 9%bv HPC ltac:(pv_cs)); exact R9).
assert (P18 : YK11.getr (ms_regs msC) 18%bv = Z_to_bv 64 (frame_addr ly 0 pos))
  by (rewrite (fsw_pres (ms_regs ms') (ms_regs msC) 18%bv HPC ltac:(pv_cs)); exact R18).
assert (P19 : YK11.getr (ms_regs msC) 19%bv = Z_to_bv 64 v)
  by (rewrite (fsw_pres (ms_regs ms') (ms_regs msC) 19%bv HPC ltac:(pv_cs)); exact R19).
assert (P20 : YK11.getr (ms_regs msC) 20%bv = Z_to_bv 64 q)
  by (rewrite (fsw_pres (ms_regs ms') (ms_regs msC) 20%bv HPC ltac:(pv_cs)); exact R20).
assert (P23 : YK11.getr (ms_regs msC) 23%bv = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (fsw_pres (ms_regs ms') (ms_regs msC) 23%bv HPC ltac:(pv_cs)); exact R23).
assert (P24 : YK11.getr (ms_regs msC) 24%bv = Z_to_bv 64 (SHADOW_OFF + frame_addr ly 0 pos / 8))
  by (rewrite (fsw_pres (ms_regs ms') (ms_regs msC) 24%bv HPC ltac:(pv_cs)); exact R24).
assert (P26 : YK11.getr (ms_regs msC) 26%bv = Z_to_bv 64 (frame_addr ly 0 pos))
  by (rewrite (fsw_pres (ms_regs ms') (ms_regs msC) 26%bv HPC ltac:(pv_cs)); exact R26).
assert (Hs64 : 0 <= spZ regs < 2 ^ 64) by (unfold spZ; exact (u64_range _)).
assert (Csp : spZ (ms_regs msC) = 32 * ((spZ regs - 160) / 32)).
{ unfold spZ at 1. rewrite P2. apply unsigned_lit_small. lia. }
pose proof (ARU_AR tfibsegs B ly S2 U W (ms_mem ms') mdx' HARU) as HAR2.
(* the bytes the walk writes later (parse_value's frame, its shadow, the flag byte) are off v and off the statics *)
assert (VOFF2 : forall z, v <= z < v + 56 -> ~ pe_wr (frame_addr ly 0 pos) (flag_addr ly 0 pos) z).
{ intros z Hz. apply (pvo_off_pe B ly S2 W (unpoison U (ms_mem ms')) mdx' pos (frames S) z HAR2 Hfrs2).
  right; right. destruct LOC as [(cid & pos' & Hc & _ & _ & H1 & H2) | (b & m & Hb & H1 & H2)].
  - right. exists cid, pos'. split; [exact Hc | lia].
  - left. exists b, m. split; [rewrite Hab2; exact Hb | unfold HEAD in H1; lia]. }
assert (NFL : forall x, frame_addr ly 0 pos + 56 <= x < frame_addr ly 0 pos + 64 -> ~ inFP FS_PSTAT_FP x).
{ intros x Hx Hf. apply (pvo_off_pe B ly S2 W (unpoison U (ms_mem ms')) mdx' pos (frames S) x HAR2 Hfrs2);
    [right; left; exact (pvc_pstat_img x Hf) | unfold pe_wr; left; lia]. }
(* the call memory msC: the arm memory but v's type word *)
assert (HROC : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) (ms_mem msC))).
{ pose proof HARUC as (_ & OKC & POC).
  apply (arodata_kept_own B _ _ _ ly S U W mem md [(0, pos)] ly S2 U W (ms_mem msC) mdC 0 HJC HARU0 OKC POC).
  - apply sink_closed_pos. unfold FS_PSTAT_FP. cbn [app]. repeat constructor; cbn [fst]; lia.
  - intros a Hro (r & Hr & Ha). apply in_app_or in Hr as [Hr | Hr].
    + destruct Hr as [<- | []]. cbn [fst snd] in Ha. exact (VNI a ltac:(lia) (fsw_roP_img a Hro)).
    + exact (pvo_pstat_not_ro a Hro (ex_intro _ r (conj Hr Ha))).
  - exact HRO. }
assert (FH2 : FSupoisonU.fs_heads B ly S2 U).
{ intros r Hr. destruct (FH r Hr) as (H1 & m & H2 & H3). split; [exact H1|]. exists m. rewrite Hab2. auto. }
assert (HWINC : rd_win tfibsegs (ms_regs msC) ly W (ms_mem msC) q ot).
{ split; [rewrite Csp; lia|]. split; [exact Hq24|]. split; [exact Hot16|]. split; [exact Hotly|].
  intros a Ha. rewrite Csp in Ha.
  pose proof HJC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresC & _).
  apply (fsw_apresent_unpoison B ly S2 U W (ms_mem msC) mdC a HARUC); [unfold kHighMemBeg; lia|].
  apply HpresC. lia. }
assert (HINC : PjIn.pj_in_ok tfibsegs (mrestrict (w_H W) (ms_mem msC)) q text len (p + Z.of_nat (length ws))
  (Z.of_nat k) tb).
{ apply (pvo_in_tr (mrestrict (w_H W) (ms_mem ms'))); [|exact HIN].
  pose proof HTX as (_ & (HinT & _ & Htc & _) & Hlt).
  intros a [Ha | Ha]; apply KZC; try lia.
  destruct Hvtx as [Hv | Hv]; unfold HEAD in *; lia. }
assert (HTXC : rd_text tfibsegs B ly S2 W (ms_mem msC) text len tcap).
{ destruct HTX as (Ht & QRB & Hlt). split; [exact Ht|]. split; [|exact Hlt].
  apply (pvo_rblock_tr B ly S2 S2 W (unpoison U (ms_mem ms')) mdx' (ms_mem ms') (ms_mem msC) text tcap HAR2 eq_refl);
    [|exact QRB].
  intros z Hz. apply KZC; [lia|]. destruct Hvtx as [Hv | Hv]; unfold HEAD in *; lia. }
assert (HGLC : fs_glob tfibsegs W (ms_mem msC) live peak cnt fail).
{ assert (GK : forall g, inFP FS_PSTAT_FP g ->
    mrestrict (w_H W) (ms_mem msC) (Z_to_bv 64 g) = mrestrict (w_H W) (ms_mem ms') (Z_to_bv 64 g)).
  { intros g Hg. pose proof (pv_pstat_rng g Hg). apply KZC; [lia|]. intros Hgv. exact (VNF g ltac:(lia) Hg). }
  unfold fs_glob, fs_glob_at in HGL |- *. destruct HGL as (V1 & V2 & V3 & V4 & Rest).
  set (m0 := mrestrict (w_H W) (ms_mem ms')). set (m1 := mrestrict (w_H W) (ms_mem msC)).
  split; [apply (pvo_val_tr m0 m1 G_LIVE 8 live (fun j Hj => GK (G_LIVE + Z.of_nat j) ltac:(exists (0x5da5c0, 0x5da5c8);
    split; [unfold FS_PSTAT_FP; cbn [In]; right; left; reflexivity | unfold G_LIVE; cbn [fst snd]; lia])) V1)|].
  split; [apply (pvo_val_tr m0 m1 G_PEAK 8 peak (fun j Hj => GK (G_PEAK + Z.of_nat j) ltac:(exists (0x5da5e0, 0x5da5e8);
    split; [unfold FS_PSTAT_FP; cbn [In]; right; right; left; reflexivity | unfold G_PEAK; cbn [fst snd]; lia])) V2)|].
  split; [apply (pvo_val_tr m0 m1 G_COUNT 8 cnt (fun j Hj => GK (G_COUNT + Z.of_nat j) ltac:(exists (0x5da600, 0x5da608);
    split; [unfold FS_PSTAT_FP; cbn [In]; right; right; right; left; reflexivity
           | unfold G_COUNT; cbn [fst snd]; lia])) V3)|].
  split; [apply (pvo_val_tr m0 m1 G_FAIL 8 fail (fun j Hj => GK (G_FAIL + Z.of_nat j) ltac:(exists (0xa3ca0, 0xa3ca8);
    split; [unfold FS_PSTAT_FP; cbn [In]; left; reflexivity | unfold G_FAIL; cbn [fst snd]; lia])) V4)|].
  exact Rest. }
assert (VFLC : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msC)) (frame_addr ly 0 pos + 56) 8 (flag_addr ly 0 pos)).
{ destruct HINV as (_ & VFL0 & _). apply (pvo_val_tr (mrestrict (w_H W) (ms_mem ms'))); [|exact VFL0].
  intros j Hj. destruct (frames_bounds tfibsegs B LAWS ly S2 W _ mdx' 0 pos HAR2 Hin0) as (HF1 & HF2 & _).
  change (fs_frame_bytes 0) with 64 in HF2.
  apply KZC; [lia|]. intros Hjv. apply (VOFF2 (frame_addr ly 0 pos + 56 + Z.of_nat j)); [lia | unfold pe_wr; left; lia]. }
assert (HPoC : pobj tfibsegs B ly S2 W (ms_mem msC) v).
{ destruct HPo as [HPl HPw]. split.
  - assert (RAC : range_addressable (aview tfibsegs (w_H W) (ms_mem msC)) SHADOW_OFF v 56).
    { intros x Hx. destruct (RAa x Hx) as (sv & Esv & Hok). exists sv. split; [|exact Hok].
      rewrite <- Esv. apply pvo_aview_pt. apply KZC.
      - assert (Hxc : 0 <= x < alloc_ceiling) by lia. pose proof (fsw_shadow_below x Hxc). lia.
      - unfold shadow_of_addr. Z.div_mod_to_equations. lia. }
    destruct HPl as [(Hf & H8 & _) | (Hb & H8 & _)]; [left | right]; (split; [assumption|]);
      (split; [exact H8 | exact RAC]).
  - intros i Hi. destruct (Z_lt_le_dec i 4) as [Hi4 | Hi4].
    + pose proof (Vty (Z.to_nat i) ltac:(lia)) as Hb. rewrite Z2Nat.id in Hb by lia.
      exact (pvs_wr_of_mbyte _ (v + i) _ ltac:(lia) (VNI (v + i) ltac:(lia)) Hb).
    + apply (writable_at_eq tfibsegs (mrestrict (w_H W) (ms_mem ms')) (mrestrict (w_H W) (ms_mem msC)) (v + i));
        [apply KZC; lia | exact (HPw i Hi)]. }
(* the chains at the call memory: msC is ms' above alloc_ceiling *)
assert (AGC : forall a, 32 * ((spZ regs - 160) / 32) - FRAME_parse_string <= a < 2 ^ 64 ->
  aview tfibsegs (w_H W) (unpoison U (ms_mem msC)) a = aview tfibsegs (w_H W) (unpoison U (ms_mem ms')) a).
{ intros a Ha.
  assert (Hac : alloc_ceiling <= a < 2 ^ 64) by (unfold FRAME_parse_string in *; lia).
  assert (Hav : ~ (v <= a < v + 4)) by lia.
  apply pvo_aview_pt. unfold mrestrict.
  rewrite (pv_unp_high B ly S2 U W (ms_mem msC) mdC a HARUC Hac), (pv_unp_high B ly S2 U W (ms_mem ms') mdx' a HARU Hac).
  exact (KZC a ltac:(lia) Hav). }
assert (Htop64 : ly_top ly <= 2 ^ 64) by lia.
assert (HCH0C : exists ch0, achain ly (aview tfibsegs (w_H W) (unpoison U (ms_mem msC)))
  (32 * ((spZ regs - 160) / 32)) (spZ regs) ch0).
{ destruct HCH0 as (ch0 & H). exists ch0.
  apply (achain_kept ly _ _ _ _ ch0 (32 * ((spZ regs - 160) / 32)) H ltac:(lia) Htop64).
  intros a Ha. apply AGC. unfold FRAME_parse_string. lia. }
assert (HCHqC : exists chq, achain ly (aview tfibsegs (w_H W) (unpoison U (ms_mem msC)))
  (32 * ((spZ regs - 160) / 32) - FRAME_parse_string) q chq).
{ destruct HCHq as (chq & H). exists chq.
  apply (achain_lower ly _ (32 * ((spZ regs - 160) / 32)) _ q chq); [|unfold FRAME_parse_string; lia].
  apply (achain_kept ly _ _ _ _ chq (32 * ((spZ regs - 160) / 32)) H ltac:(lia) Htop64).
  intros a Ha. apply AGC. unfold FRAME_parse_string. lia. }
(* ---- the parse_string call (pv_strcall') ---- *)
rewrite HshC.
change (mkCfg (mkst (ms_regs msC) (Z_to_bv 64 A_parse_string) (ms_mem msC) (seg_rom tfibsegs)) mdC)
  with (YG0d.cfg_at tfibsegs A_parse_string (ms_regs msC) (ms_mem msC) mdC).
assert (LOC2 : (exists cid pos', In (cid, pos') (frames S2) /\ 0 <= cid /\
      frame_addr ly cid pos' <= v /\ v + 56 <= frame_addr ly cid pos' + fs_frame_bytes cid) \/
   (exists b m, In (b, m) (ablocks B ly S2) /\ b + HEAD <= v /\ v + 56 <= b + req_size m)).
{ destruct LOC as [(cid & pos' & Hc & Hc0 & _ & H1 & H2) | (b & m & Hb & H1 & H2)].
  - left. exists cid, pos'. rewrite Hfrs2. split; [right; exact Hc|]. split; [exact Hc0|]. split; [exact H1 | exact H2].
  - right. exists b, m. rewrite Hab2. split; [exact Hb|]. split; [exact H1 | exact H2]. }
assert (HFPs : forall a, inFP FS_PSTAT_FP a ->
  (inFP ([(v, v + 56)] ++ FS_PSTAT_FP) a /\ exists b n, In (b, n) (ablocks B ly S2) /\ b <= a < b + req_size n) \/
  in_tmp_block (ablocks B ly S) (ablocks B ly S2) a \/
  (inFP ([(v, v + 56)] ++ FS_PSTAT_FP) a /\ in_img tfibsegs a)).
{ intros a Ha. right; right. split; [|exact (pvc_pstat_img a Ha)].
  destruct Ha as (r & Hr & Har). exists r. split; [apply in_or_app; right; exact Hr | exact Har]. }
rewrite TLN in Hquiet. cbn [Z.of_nat Pos.of_succ_nat] in Hquiet.
assert (BL : live + Z.of_nat (length s) + 1 < 2 ^ 64) by (rewrite TLV in Hlive; unfold HEAD in Hlive; lia).
assert (BE : st_nev S2 + EV_fuzz_malloc <= EV_MAX) by (rewrite Hnev2, <- TEV; exact Hnev).
assert (BB : blocks_bytes S2 + (Z.of_nat (length s) + 1 + HEAD) <= LIVE_MAX) by (rewrite Hbb2, <- TLV; exact Hbb).
apply (pv_strcall' B HPS (STK_parse_value (2 - k) + (ot - spZ regs)) ot ([(v, v + 56)] ++ FS_PSTAT_FP)
  ly S S2 U W mem md (ms_regs msC) (ms_mem msC) mdC pos q (spZ regs) (32 * ((spZ regs - 160) / 32)) text len
  (p + Z.of_nat (length ws)) (Z.of_nat k) tb tcap (Z.of_nat (length s)) live peak cnt fail v (flag_addr ly 0 pos) _
  Csp C10 C1c ltac:(rewrite P3; exact Hgp) ltac:(rewrite P4; exact Htp) P8 Hs64 ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(lia) ltac:(lia) ltac:(lia) HCH0C HCHqC HROC FH2 HINC HWINC HTXC Hplt Hq34 Hrun HGLC Hquiet TSZ
  BL BE BB HJC HARUC HFPs Hin0 VFLC NFL LOC2 VNF HPoC).
intros ly2 S3 W2 regs2 mem2 md2 a HJ2 HARU2 HP2 Q10 Q4096 Qab QRB Qcb QIN QWK QTX QGL VFL2 VK2 HPo2 FH3.
pose proof HJ2 as (HAR3 & Hly2 & _ & _ & _ & Hfrs3 & _). cbn [app] in Hfrs3.
destruct (al_layout tfibsegs B LAWS ly S W (unpoison U mem) md ly2 HAR0 Hly2) as (_ & HFA & _).
pose proof Hly2 as (_ & _ & _ & _ & _ & EF & _ & _ & _ & Elo & Ehi & _).
assert (EFL : flag_addr ly2 0 pos = flag_addr ly 0 pos) by (unfold flag_addr; rewrite EF; reflexivity).
assert (Hin3 : In (0, pos) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
assert (Hab3 : forall b m, In (b, m) (ablocks B ly S) -> In (b, m) (ablocks B ly2 S3)).
{ intros b m Hb. rewrite Qab. apply in_or_app. left. rewrite Hab2. exact Hb. }
destruct (fsw_rblock_low B ly2 S3 W2 _ md2 mem2 a (Z.of_nat (length s) + 1) HAR3 QRB) as (Ha1 & Ha2).
(* the new block is fresh, so apart from v *)
assert (Hnew : In (a - HEAD, Z.of_nat (length s) + 1 + HEAD) (ablocks B ly2 S3))
  by (rewrite Qab; apply in_or_app; right; left; reflexivity).
assert (Hfresh : ~ In (a - HEAD, Z.of_nat (length s) + 1 + HEAD) (ablocks B ly S)).
{ intros Hin. pose proof (FSW_pj_set_heads.pSh_ablocks_nodup B ly2 S3 W2 _ md2 HAR3) as ND. rewrite Qab, Hab2 in ND.
  apply (List.NoDup_remove_2 (ablocks B ly S) [] _ ND). rewrite app_nil_r. exact Hin. }
assert (HRQ : Z.of_nat (length s) + 1 + HEAD <= req_size (Z.of_nat (length s) + 1 + HEAD))
  by (unfold req_size, HEAD; destruct (Z.eqb_spec (Z.of_nat (length s) + 1 + 16) 0); lia).
assert (NAPART : forall z, a - HEAD <= z < a + Z.of_nat (length s) + 1 -> ~ (v <= z < v + 56)).
{ intros z Hz Hv. destruct LOC as [(cid & pos' & Hc & _ & _ & H1 & H2) | (b & m & Hb & H1 & H2)].
  - assert (Hc3 : In (cid, pos') (frames S3)) by (rewrite Hfrs3; right; exact Hc).
    pose proof (sep_block_frame tfibsegs B LAWS ly2 S3 W2 _ md2 _ _ cid pos' HAR3 Hnew Hc3) as Dj.
    unfold zdisjoint in Dj. cbn [fst snd] in Dj. rewrite (HFA cid pos') in Dj. unfold HEAD in *. lia.
  - assert (NE : (b, m) <> (a - HEAD, Z.of_nat (length s) + 1 + HEAD)) by (intros E; rewrite E in Hb; exact (Hfresh Hb)).
    pose proof (sep_blocks tfibsegs B LAWS ly2 S3 W2 _ md2 b m _ _ HAR3 (Hab3 b m Hb) Hnew NE) as Dj.
    unfold zdisjoint in Dj. cbn [fst snd] in Dj.
    assert (Hm : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
    unfold HEAD in *. lia. }
(* registers at the return *)
assert (G19 : YK11.getr regs2 19%bv = Z_to_bv 64 v)
  by (rewrite (fsw_pres (ms_regs msC) regs2 19%bv HP2 ltac:(pv_cs)); exact P19).
assert (G23 : YK11.getr regs2 23%bv = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (fsw_pres (ms_regs msC) regs2 23%bv HP2 ltac:(pv_cs)); exact P23).
(* ---- 0x831d0 -> the epilogue 0x83318 (pv_str1): v->str := a ---- *)
change (YG0d.cfg_at tfibsegs 0x831d0 regs2 mem2 md2)
  with (mkCfg (mkst regs2 (Z_to_bv 64 0x831d0) mem2 (seg_rom tfibsegs)) md2).
assert (RA2 : range_addressable (aview tfibsegs (w_H W2) mem2) SHADOW_OFF (v + 16) 8).
{ destruct HPo2 as [[(_ & _ & Hr) | (_ & _ & Hr)] _]; intros x Hx; apply Hr; lia. }
assert (WV2 : forall o, 16 <= o < 24 -> writable_at tfibsegs (mrestrict (w_H W2) mem2) (v + o))
  by (destruct HPo2 as [_ Hw]; intros o Ho; apply Hw; lia).
assert (HAWR2 : forall x, in_zr x (v + 16, 8) ->
  awr_byte tfibsegs B (STK_parse_value (2 - k) + (ot - spZ regs)) ot ([(v, v + 56)] ++ FS_PSTAT_FP)
    (ablocks B ly S) (ablocks B ly2 S3) ly2 [(0, pos)] (frames S) x).
{ intros x Hx. unfold in_zr in Hx. cbn [fst snd] in Hx.
  assert (HFPx : inFP ([(v, v + 56)] ++ FS_PSTAT_FP) x)
    by (exists (v, v + 56); split; [left; reflexivity | cbn [fst snd]; lia]).
  destruct LOC as [(cid & pos' & Hc & Hc0 & H8 & H1 & H2) | (b & m & Hb & H1 & H2)].
  - right; right. split; [exact HFPx|]. exists cid, pos'. split; [exact Hc|].
    unfold in_zr, frame_rng; cbn [fst snd]. rewrite (HFA cid pos'). lia.
  - left. right; left. split; [exact HFPx|]. exists b, m. split; [exact (Hab3 b m Hb) | unfold HEAD in H1; lia]. }
apply (pv_str1 B (STK_parse_value (2 - k) + (ot - spZ regs)) ot ([(v, v + 56)] ++ FS_PSTAT_FP) ly S U W mem md
  EV_fuzz_malloc ly2 S3 (U ++ [(a - HEAD, HEAD)]) W2 regs2 mem2 md2 pos v a _ G19 G23 Q10 Hv4096 ltac:(lia) Hv8
  ltac:(unfold HEAD in *; lia) HVB RA2 WV2 HAWR2 HJ2 HARU2).
intros ms3 md3 Hsh3 G21 K8 K9 K18 K20 K23 K24 K26 K3 K4 Vstr HJ3 HARU3 KEEP3.
rewrite Hsh3.
assert (KZ3 : forall z, 0 <= z < 2 ^ 64 -> ~ (v + 16 <= z < v + 24) ->
  mrestrict (w_H W2) (ms_mem ms3) (Z_to_bv 64 z) = mrestrict (w_H W2) mem2 (Z_to_bv 64 z)).
{ intros z Hz Hn. apply KEEP3. rewrite unsigned_lit_small by lia. exact Hn. }
assert (E8 : YK11.getr (ms_regs ms3) 8%bv = Z_to_bv 64 (spZ regs))
  by (rewrite K8, (fsw_pres (ms_regs msC) regs2 8%bv HP2 ltac:(pv_cs)); exact P8).
assert (E18 : YK11.getr (ms_regs ms3) 18%bv = Z_to_bv 64 (frame_addr ly2 0 pos))
  by (rewrite HFA, K18, (fsw_pres (ms_regs msC) regs2 18%bv HP2 ltac:(pv_cs)); exact P18).
assert (E24 : YK11.getr (ms_regs ms3) 24%bv = Z_to_bv 64 (SHADOW_OFF + frame_addr ly2 0 pos / 8))
  by (rewrite HFA, K24, (fsw_pres (ms_regs msC) regs2 24%bv HP2 ltac:(pv_cs)); exact P24).
assert (E26 : YK11.getr (ms_regs ms3) 26%bv = Z_to_bv 64 (frame_addr ly2 0 pos))
  by (rewrite HFA, K26, (fsw_pres (ms_regs msC) regs2 26%bv HP2 ltac:(pv_cs)); exact P26).
assert (E3 : YK11.getr (ms_regs ms3) 3%bv = YK11.getr regs 3%bv)
  by (rewrite K3, (fsw_pres (ms_regs msC) regs2 3%bv HP2 ltac:(pv_cs)); exact P3).
assert (E4 : YK11.getr (ms_regs ms3) 4%bv = YK11.getr regs 4%bv)
  by (rewrite K4, (fsw_pres (ms_regs msC) regs2 4%bv HP2 ltac:(pv_cs)); exact P4).
(* the thirteen saved words: at the arm (pv_inv), past v's type word, across the callee (its wkeep over [sp1, ot) off
   [q, q + 24)) and past v->str *)
assert (Vsv : pv_saved_ok (mrestrict (w_H W2) (ms_mem ms3)) (spZ regs) regs).
{ destruct HINV as (Vsv0 & _). intros j Hj kk Hkk.
  set (y := spZ regs - 8 * (Z.of_nat j + 1) + Z.of_nat kk).
  assert (Hy : 32 * ((spZ regs - 160) / 32) <= y < spZ regs) by (unfold y; lia).
  rewrite (pv_mb_pw (mrestrict (w_H W2) mem2) (mrestrict (w_H W2) (ms_mem ms3)) y (KZ3 y ltac:(lia) ltac:(lia))).
  rewrite (proj1 (QWK y ltac:(lia) ltac:(lia))).
  rewrite (pv_mb_pw (mrestrict (w_H W) (ms_mem ms')) (mrestrict (w_H W) (ms_mem msC)) y (KZC y ltac:(lia) ltac:(lia))).
  exact (Vsv0 j Hj kk Hkk). }
assert (Vfl : val_mem tfibsegs (mrestrict (w_H W2) (ms_mem ms3)) (frame_addr ly2 0 pos + 56) 8 (flag_addr ly2 0 pos)).
{ rewrite HFA, EFL. apply (pvo_val_tr (mrestrict (w_H W2) mem2)); [|exact VFL2].
  intros j Hj. destruct (frames_bounds tfibsegs B LAWS ly S2 W _ mdx' 0 pos HAR2 Hin0) as (HF1 & HF2 & _).
  change (fs_frame_bytes 0) with 64 in HF2.
  apply KZ3; [lia|]. intros Hjv. apply (VOFF2 (frame_addr ly 0 pos + 56 + Z.of_nat j)); [lia | unfold pe_wr; left; lia]. }
(* ---- 0x83318 -> ret (pv_epi), into parse_value_spec k's post ---- *)
rewrite TEV.
eapply SRr_mono; cycle 1.
{ intros W' c' _ HX. exists [(a, Z.of_nat (length s) + 1)], [(a, Z.of_nat (length s) + 1)].
  split; [apply Permutation_refl | exact HX]. }
apply (pv_epi B ML ASF FFL (STK_parse_value (2 - k) + (ot - spZ regs)) ot ([(v, v + 56)] ++ FS_PSTAT_FP) ly S U W mem md
  EV_fuzz_malloc ly2 S3 (U ++ [(a - HEAD, HEAD)]) W2 regs (ms_regs ms3) (ms_mem ms3) md3 pos (spZ regs) 0 []
  _ Hin3 E8 E18 E24 E26 G21 E3 E4 eq_refl Hret).
1: { lia. }
1: { exact Hal16. }
1: { rewrite Elo. lia. }
1: { rewrite Ehi. lia. }
1: { rewrite Ehi. exact H47'. }
1: { rewrite Elo. exact Hlo0. }
1: { lia. }
1: { exact Vsv. }
1: { exact Vfl. }
1: { exact HJ3. }
1: { exact HARU3. }
intros mat regsf memf Hf10 KEEPf. cbv beta.
rewrite HFA, EFL in KEEPf.
assert (KZf : forall z, 0 <= z < 2 ^ 64 -> ~ pe_wr (frame_addr ly 0 pos) (flag_addr ly 0 pos) z ->
  mrestrict (w_H W2) memf (Z_to_bv 64 z) = mrestrict (w_H W2) (ms_mem ms3) (Z_to_bv 64 z)).
{ intros z Hz Hn. apply KEEPf. rewrite unsigned_lit_small by lia. exact Hn. }
assert (OFF : forall z, (alloc_ceiling <= z \/ in_img tfibsegs z \/
    (exists b n, In (b, n) (ablocks B ly2 S3) /\ b <= z < b + req_size n) \/
    (exists cid pos', In (cid, pos') (frames S) /\
       frame_addr ly cid pos' <= z < frame_addr ly cid pos' + fs_frame_bytes cid)) ->
  ~ pe_wr (frame_addr ly 0 pos) (flag_addr ly 0 pos) z).
{ intros z Hz. rewrite <- (HFA 0 pos), <- EFL.
  apply (pvo_off_pe B ly2 S3 W2 (unpoison (U ++ [(a - HEAD, HEAD)]) mem2) md2 pos (frames S) z HAR3 Hfrs3).
  destruct Hz as [Hz | [Hz | [Hz | (cid & pos' & Hc & Hz)]]];
    [left; exact Hz | right; left; exact Hz | right; right; left; exact Hz |].
  right; right; right. exists cid, pos'. rewrite (HFA cid pos'). split; [exact Hc | exact Hz]. }
assert (VOFF : forall z, v <= z < v + 56 -> ~ pe_wr (frame_addr ly 0 pos) (flag_addr ly 0 pos) z).
{ intros z Hz. apply OFF. right; right.
  destruct LOC as [(cid & pos' & Hc & _ & _ & H1 & H2) | (b & m & Hb & H1 & H2)].
  - right. exists cid, pos'. split; [exact Hc | lia].
  - left. exists b, m. split; [exact (Hab3 b m Hb) | unfold HEAD in H1; lia]. }
assert (KZ : forall z, 0 <= z < 2 ^ 64 -> ~ pe_wr (frame_addr ly 0 pos) (flag_addr ly 0 pos) z ->
  ~ (v + 16 <= z < v + 24) ->
  mrestrict (w_H W2) memf (Z_to_bv 64 z) = mrestrict (w_H W2) mem2 (Z_to_bv 64 z)).
{ intros z Hz H1 H2. rewrite (KZf z Hz H1). exact (KZ3 z Hz H2). }
assert (BOFF : forall b n z, In (b, n) (ablocks B ly2 S3) -> b <= z < b + req_size n -> ~ (v + 16 <= z < v + 24) ->
  mrestrict (w_H W2) memf (Z_to_bv 64 z) = mrestrict (w_H W2) mem2 (Z_to_bv 64 z)).
{ intros b n z Hb Hz Hv. destruct (fsw_ablock_low B ly2 S3 W2 _ md2 b n HAR3 Hb) as (L1 & L2 & _).
  apply KZ; [lia | | exact Hv]. apply OFF. right; right; left. exists b, n. split; [exact Hb | exact Hz]. }
assert (THD : PjGrammar.held tr = Z.of_nat (length s) + 1)
  by (rewrite Htr; cbn [PjGrammar.held PjGrammar.held_ev]; lia).
split; [exact Hf10|].
split.
{ (* struct pj_in after the string: in->p past the closing quote *)
  replace (p + Z.of_nat (length ws) + Z.of_nat (length wt)) with (p + Z.of_nat (length ws) + Z.of_nat (length s) + 2)
    by (rewrite Hwt; cbn [length]; rewrite length_app; cbn [length]; lia).
  apply (pvo_in_tr (mrestrict (w_H W2) mem2)); [|exact QIN].
  pose proof QTX as (_ & (HinT & _ & Htc & _) & Hlt).
  pose proof (req_size_pos (tcap + HEAD) ltac:(unfold HEAD; lia)) as (_ & Hrq).
  intros z [Hz | Hz].
  - apply KZ; [lia | apply OFF; left; lia | lia].
  - apply (BOFF (text - HEAD) (tcap + HEAD) z HinT); [unfold HEAD in *; lia|].
    destruct Hvtx as [Hv | Hv]; unfold HEAD in *; lia. }
split.
{ (* the window [s, ot) off [q, q + 24): the entry keep, v's type word, the callee's wkeep, v->str, the epilogue *)
  intros z Hz Hq. pose proof (QWK z ltac:(lia) Hq) as (QW1 & QW2). pose proof (HWK z Hz Hq) as (HW1 & HW2).
  assert (E1 : mrestrict (w_H W2) memf (Z_to_bv 64 z) = mrestrict (w_H W2) mem2 (Z_to_bv 64 z))
    by (apply KZ; [lia | apply OFF; left; lia | lia]).
  assert (E2 : mrestrict (w_H W) (ms_mem msC) (Z_to_bv 64 z) = mrestrict (w_H W) (ms_mem ms') (Z_to_bv 64 z))
    by (apply KZC; lia).
  split.
  - rewrite (pv_mb_pw _ _ z E1), QW1, (pv_mb_pw _ _ z E2). exact HW1.
  - split; intros Hw.
    + apply (writable_at_eq tfibsegs (mrestrict (w_H W2) mem2) (mrestrict (w_H W2) memf) z E1).
      apply QW2. apply (writable_at_eq tfibsegs (mrestrict (w_H W) (ms_mem ms')) (mrestrict (w_H W) (ms_mem msC)) z E2).
      apply HW2. exact Hw.
    + apply HW2.
      apply (writable_at_eq tfibsegs (mrestrict (w_H W) (ms_mem msC)) (mrestrict (w_H W) (ms_mem ms')) z (eq_sym E2)).
      apply QW2. exact (writable_at_eq tfibsegs (mrestrict (w_H W2) memf) (mrestrict (w_H W2) mem2) z (eq_sym E1) Hw). }
split.
{ change (ablocks B ly2 (stack_free_state 0 pos S3)) with (ablocks B ly2 S3). rewrite Qab, Hab2.
  cbn [rd_hblocks map fst snd]. apply Permutation_refl. }
(* v's 56 bytes at memf, by where they were last written *)
assert (TF3 : forall x, v <= x < v + 56 ->
  mbyte tfibsegs (mrestrict (w_H W2) memf) x = mbyte tfibsegs (mrestrict (w_H W2) (ms_mem ms3)) x)
  by (intros x Hx; apply pv_mb_pw; apply KZf; [lia | exact (VOFF x Hx)]).
assert (T32 : forall x, v <= x < v + 56 -> ~ (v + 16 <= x < v + 24) ->
  mbyte tfibsegs (mrestrict (w_H W2) (ms_mem ms3)) x = mbyte tfibsegs (mrestrict (w_H W2) mem2) x)
  by (intros x Hx Hn; apply pv_mb_pw; apply KZ3; [lia | exact Hn]).
assert (TCa : forall x, v + 4 <= x < v + 56 ->
  mbyte tfibsegs (mrestrict (w_H W) (ms_mem msC)) x = mbyte tfibsegs (mrestrict (w_H W) (ms_mem ms')) x)
  by (intros x Hx; apply pv_mb_pw; apply KZC; lia).
pose proof HZo as (_ & Bz).
assert (SOME : forall y, v <= y < v + 56 -> exists b, mbyte tfibsegs (mrestrict (w_H W2) memf) y = Some b).
{ intros y Hy. rewrite (TF3 y Hy).
  destruct (Z_lt_le_dec y (v + 16)) as [H16 | H16]; [|destruct (Z_lt_le_dec y (v + 24)) as [H24 | H24]].
  - rewrite (T32 y Hy ltac:(lia)), (VK2 y Hy).
    destruct (Z_lt_le_dec y (v + 4)) as [H4 | H4].
    + pose proof (Vty (Z.to_nat (y - v)) ltac:(lia)) as Hb. rewrite Z2Nat.id in Hb by lia.
      replace (v + (y - v)) with y in Hb by lia. eauto.
    + rewrite (TCa y ltac:(lia)). destruct Bz as (_ & _ & Bz').
      pose proof (Bz' (Z.to_nat (y - v)) ltac:(rewrite repeat_length; lia)) as Hb.
      change (Mem.mrd tfibsegs (mrestrict (w_H W) (ms_mem ms')) (Mem.wa (v + Z.of_nat (Z.to_nat (y - v)))))
        with (mbyte tfibsegs (mrestrict (w_H W) (ms_mem ms')) (v + Z.of_nat (Z.to_nat (y - v)))) in Hb.
      rewrite Z2Nat.id in Hb by lia. replace (v + (y - v)) with y in Hb by lia.
      rewrite nth_error_repeat in Hb by lia. eauto.
  - pose proof (Vstr (Z.to_nat (y - (v + 16))) ltac:(lia)) as Hb. rewrite Z2Nat.id in Hb by lia.
    replace (v + 16 + (y - (v + 16))) with y in Hb by lia. eauto.
  - rewrite (T32 y Hy ltac:(lia)), (VK2 y Hy), (TCa y ltac:(lia)). destruct Bz as (_ & _ & Bz').
    pose proof (Bz' (Z.to_nat (y - v)) ltac:(rewrite repeat_length; lia)) as Hb.
    change (Mem.mrd tfibsegs (mrestrict (w_H W) (ms_mem ms')) (Mem.wa (v + Z.of_nat (Z.to_nat (y - v)))))
      with (mbyte tfibsegs (mrestrict (w_H W) (ms_mem ms')) (v + Z.of_nat (Z.to_nat (y - v)))) in Hb.
    rewrite Z2Nat.id in Hb by lia. replace (v + (y - v)) with y in Hb by lia.
    rewrite nth_error_repeat in Hb by lia. eauto. }
split.
{ (* the string node *)
  set (mf := mrestrict (w_H W2) memf).
  assert (FT : Mem.bytes_at tfibsegs mf v (Mem.le4 (Z_to_bv 64 4))).
  { apply (pvs_bytes_mb (mrestrict (w_H W) (ms_mem msC))); [apply pvs_le4_4; [lia | lia | exact Vty] |].
    intros i Hi. rewrite Mem.length_le4 in Hi.
    unfold mf. set (x := v + Z.of_nat i).
    rewrite (TF3 x ltac:(unfold x; lia)), (T32 x ltac:(unfold x; lia) ltac:(unfold x; lia)), (VK2 x ltac:(unfold x; lia)).
    reflexivity. }
  assert (FZ : forall o (n : nat), 4 <= o -> (o + Z.of_nat n <= 16 \/ 24 <= o /\ o + Z.of_nat n <= 56) ->
    Mem.bytes_at tfibsegs mf (v + o) (repeat (Z_to_bv 8 0) n)).
  { intros o n Ho Hn. apply (pvs_bytes_mb (mrestrict (w_H W) (ms_mem ms'))); [apply pvs_zero_sub; [exact Bz | lia | lia]|].
    intros i Hi. rewrite repeat_length in Hi.
    unfold mf. set (x := v + o + Z.of_nat i).
    rewrite (TF3 x ltac:(unfold x; lia)), (T32 x ltac:(unfold x; lia) ltac:(unfold x; lia)), (VK2 x ltac:(unfold x; lia)),
      (TCa x ltac:(unfold x; lia)).
    reflexivity. }
  assert (Ha64 : 0 <= a < 2 ^ 64) by (unfold HEAD in *; lia).
  assert (FS : Mem.bytes_at tfibsegs mf (v + 16) (Mem.le8 (Z_to_bv 64 a))).
  { apply (pvs_bytes_mb (mrestrict (w_H W2) (ms_mem ms3))).
    - exact (KindBGlue.word_mem_le8 tfibsegs _ (v + 16) a (proj1 (val_mem_word_mem tfibsegs _ (v + 16) a) Vstr)
        Ha64 ltac:(lia) ltac:(lia)).
    - intros i Hi. rewrite Mem.length_le8 in Hi. unfold mf. apply TF3. lia. }
  assert (Z8 : forall o, 4 <= o -> (o + 8 <= 16 \/ 24 <= o /\ o + 8 <= 56) -> PjStruct.pj_u64 tfibsegs mf (v + o) 0).
  { intros o Ho Hn. split; [lia|]. exact (FZ o 8%nat Ho ltac:(cbn [Z.of_nat]; lia)). }
  split; [|split].
  - cbn [PjStruct.pj_node].
    split; [constructor; [intros Hin; inversion Hin | constructor]|].
    split.
    { intros b x Hb Hx. destruct Hb as [<- | []]. unfold PjStruct.pj_holds in Hx. cbn [fst snd] in Hx.
      apply NAPART. unfold HEAD. lia. }
    exists 0, a, 0, 0, 0, 0. split.
    + cbn [PjTree.tag]. split.
      { split; [exact Hv8|]. split; [lia|]. split; [lia|]. intros y Hy. destruct (SOME y Hy) as (b & Hb).
        split; [exact (pvs_wr_of_mbyte mf y b ltac:(lia) (VNI y Hy) Hb) | exists b; exact Hb]. }
      split; [split; [lia | exact FT]|].
      split; [exact (Z8 8 ltac:(lia) ltac:(lia))|].
      split; [split; [lia | exact FS]|].
      split; [exact (Z8 24 ltac:(lia) ltac:(lia))|].
      split; [exact (Z8 32 ltac:(lia) ltac:(lia))|].
      split; [exact (Z8 40 ltac:(lia) ltac:(lia)) | exact (Z8 48 ltac:(lia) ltac:(lia))].
    + split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      exists (Z.of_nat (length s) + 1). split; [|reflexivity].
      split; [left; reflexivity|]. split; [lia|].
      rewrite Hrunat in Qcb. destruct Qcb as (Hc & Bs). split; [exact Hc|].
      apply (pvs_bytes_mb (mrestrict (w_H W2) mem2)); [exact Bs|].
      intros i Hi. rewrite length_map, length_app in Hi. cbn [length] in Hi.
      unfold mf. apply pv_mb_pw.
      apply (BOFF (a - HEAD) (Z.of_nat (length s) + 1 + HEAD) (a + Z.of_nat i) Hnew); [unfold HEAD in *; lia|].
      intros Hv. apply (NAPART (a + Z.of_nat i)); [unfold HEAD; lia | lia].
  - intros a' k' Hin. destruct Hin as [E | []]. injection E as <- <-.
    apply (pvo_rblock_tr B ly2 S3 (stack_free_state 0 pos S3) W2 (unpoison (U ++ [(a - HEAD, HEAD)]) mem2) md2 mem2
      memf a (Z.of_nat (length s) + 1) HAR3 eq_refl); [|exact QRB].
    intros z Hz. apply (BOFF (a - HEAD) (Z.of_nat (length s) + 1 + HEAD) z Hnew); [unfold HEAD in *; lia|].
    intros Hv. apply (NAPART z); [unfold HEAD in *; lia | lia].
  - apply incl_refl. }
split; [cbn [rd_sum fold_right fst snd]; rewrite THD; lia|].
split; [rewrite TLN; cbn [length]; lia|].
split.
{ (* pobj: the place from the entry, the shadow from the callee's post, the bytes present *)
  assert (Hfr' : frames (stack_free_state 0 pos S3) = frames S) by exact (pvo_frames_free S3 S pos Hfrs3).
  split.
  - assert (RA : range_addressable (aview tfibsegs (w_H W2) memf) SHADOW_OFF v 56).
    { assert (RA2' : range_addressable (aview tfibsegs (w_H W2) mem2) SHADOW_OFF v 56)
        by (destruct HPo2 as [[(_ & _ & Hr) | (_ & _ & Hr)] _]; exact Hr).
      intros x Hx. destruct (RA2' x Hx) as (sv & Esv & Hok). exists sv. split; [|exact Hok].
      rewrite <- Esv. apply pvo_aview_pt.
      assert (Hxc : 0 <= x < alloc_ceiling) by lia. pose proof (fsw_shadow_below x Hxc) as Hsb.
      assert (Hsh : SHADOW_OFF <= shadow_of_addr SHADOW_OFF x < SHADOW_OFF + 2 ^ 44)
        by (unfold shadow_of_addr; Z.div_mod_to_equations; lia).
      apply KZ; [lia | | lia].
      rewrite <- (HFA 0 pos), <- EFL.
      apply (pvo_shadow_off B ly2 S3 W2 (unpoison (U ++ [(a - HEAD, HEAD)]) mem2) md2 pos x HAR3 Hin3); [lia|].
      rewrite (HFA 0 pos). intros Hx'. apply (VOFF x Hx). unfold pe_wr. left. exact Hx'. }
    destruct LOC as [(cid & pos' & Hc & Hc0 & H8 & H1 & H2) | (b & m & Hb & H1 & H2)]; [left | right].
    + split; [|split; [exact Hv8 | exact RA]]. exists cid, pos'. rewrite (HFA cid pos'), Hfr'.
      split; [exact Hc|]. split; [exact Hc0|]. split; [exact H8|]. lia.
    + split; [|split; [exact Hv8 | exact RA]]. exists b, m. split; [exact (Hab3 b m Hb) | lia].
  - intros i Hi. destruct (SOME (v + i) ltac:(lia)) as (b & Hb).
    exact (pvs_wr_of_mbyte _ (v + i) b ltac:(lia) (VNI (v + i) ltac:(lia)) Hb). }
split.
{ (* the text: the block's head word *)
  destruct QTX as (Ht & QRB' & Hlt). split; [exact Ht|]. split; [|exact Hlt].
  apply (pvo_rblock_tr B ly2 S3 (stack_free_state 0 pos S3) W2 (unpoison (U ++ [(a - HEAD, HEAD)]) mem2) md2 mem2
    memf text tcap HAR3 eq_refl); [|exact QRB'].
  pose proof QRB' as (HinT & _ & Htc & _).
  pose proof (req_size_pos (tcap + HEAD) ltac:(unfold HEAD; lia)) as (_ & Hrq).
  intros z Hz. apply (BOFF (text - HEAD) (tcap + HEAD) z HinT); [unfold HEAD in *; lia|].
  destruct Hvtx as [Hv | Hv]; unfold HEAD in *; lia. }
{ (* fuzz/alloc.c's statics: image bytes *)
  exists (Z.max peak (live + Z.of_nat (length s) + 1)). split; [lia|].
  rewrite THD, TLN. replace (live + (Z.of_nat (length s) + 1)) with (live + Z.of_nat (length s) + 1) by lia.
  change (Z.of_nat 1) with 1.
  assert (GK : forall g, 659456 <= g -> g + 8 <= 6279168 -> forall j, (j < 8)%nat ->
    mrestrict (w_H W2) memf (Z_to_bv 64 (g + Z.of_nat j)) = mrestrict (w_H W2) mem2 (Z_to_bv 64 (g + Z.of_nat j))).
  { intros g H1 H2 j Hj. apply KZ; [lia | apply OFF; right; left; apply pvc_img; lia |].
    intros Hv. exact (VNI (g + Z.of_nat j) ltac:(lia) (pvc_img (g + Z.of_nat j) ltac:(lia))). }
  unfold fs_glob, fs_glob_at in QGL |- *. destruct QGL as (V1 & V2 & V3 & V4 & Rest).
  split; [exact (pvo_val_tr _ _ _ _ _ (GK G_LIVE ltac:(unfold G_LIVE; lia) ltac:(unfold G_LIVE; lia)) V1)|].
  split; [exact (pvo_val_tr _ _ _ _ _ (GK G_PEAK ltac:(unfold G_PEAK; lia) ltac:(unfold G_PEAK; lia)) V2)|].
  split; [exact (pvo_val_tr _ _ _ _ _ (GK G_COUNT ltac:(unfold G_COUNT; lia) ltac:(unfold G_COUNT; lia)) V3)|].
  split; [exact (pvo_val_tr _ _ _ _ _ (GK G_FAIL ltac:(unfold G_FAIL; lia) ltac:(unfold G_FAIL; lia)) V4)|].
  exact Rest. }
Qed.
End SAR.
