(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACem.v, with its module paths and module names changed; 1540 of its 1601 lines of code are new or changed and 390 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_pj_string.v, with its module paths, module names and numbers changed; 998 of its 1074 lines of code are new or changed and 1525 lines of the source are left out. *)
(* pj_parse (A 0x82eac, pf.c:296-309) on fs.asan (sha256 64b53ff86172...), 60 words 0x82eac .. 0x82f9c: its ASan
   contract FSH_Fn_reader.v pj_parse_spec (the narrow SUCCESS form on the harness document), proved by a symbolic walk of
   the machine code over fs's walk kit (FSW_K / K3 / rres / ret / rd / pj), theorem pj_parse_holds.
   rule 24: pj_parse is CONFIRMED to have no ASan-image proof (ossv proof index v5 built 2026-10-29T01:50:18Z, released
   addresses only plain 0x1428c / ubsan 0x14454; a Theorem Labs lane's checker a Theorem Labs lane, confirm-resume-2.md). Its released
   plain proof lib/Prog/pj_parse.v (c8557374ad2e) is the template of the functional part.
   The walk (MEASURED, (internal path)):
   - STAGE A (pjp_stage_A, from a working branch eb28238b33c): the prologue, struct pj_in
     {text, text + len, 0} at sp - 48, __asan_memset(out, 0, 56) (RT_memset), the resume state at 0x82eec.
   - the call of parse_value at 0x82ef4 (level 0, Section hypothesis PV), struct pj_in at q = sp - 48, raised window top
     ot = sp - 16; the callee's frame chain is the left arm (q = its sp, s0 = out, bad_next); the resume is
     FSW_K3.fsw_after_callFPU_ot (out is in a live block or a live fake frame: fsw_fp_sub's first or fifth arm).
   - the tail 0x82ef8 .. 0x82f90: `bnez a0` is dead (a0 = 0 pinned from the post); a compact document leaves
     in->p = in->end and `bgeu` skips the white-space loop; a pretty one runs it once over the trailing newline, whose
     inline shadow check 0x82f20 .. 0x82f2c the TOKEN engine discharges from the text block's live body
     (FSW_rd.fsw_block_body_addressable), so __asan_report_load1 at 0x82f60 is UNTAKEN; pj_free (0x82f78) is not
     reached; a0 := 0 and FSW_ret.fsw_retU gives fpostU. *)
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
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSW_K FSW_K3 FSW_ret FSW_rres FSW_pj
FSH_Fn_reader FSW_rd FSW_pj_parse_tbl.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree PjGrammar PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterValue ReaderRes PjStruct PjIn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Prog Require FSDocStrs.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Mem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* sink probe (a Theorem Labs lane / fuzz_decode defect): with FSH_Gen's and FSH_Harness's Remove Hints in force, a bare
   `_ : YI16.sink_head` must FAIL to elaborate outside a section that binds one. *)
Fail Definition pjp_sink_probe : YI16.sink_head := _.

(* ---- the Lib-form struct pj_in at q, from the four facts a walk holds about the frame (reusable by parse_value,
   parse_items and parse_string, which all take PjIn.pj_in_ok at the caller's q) ---- *)
Lemma pjp_garr8_bytes_at : forall m p (l : list Z),
  garr8 tfibsegs m p l -> 0 <= p -> p + Z.of_nat (length l) <= 2 ^ 64 ->
  Mem.bytes_at tfibsegs m p (map (fun z => Z_to_bv 8 z) l).
Proof.
intros m p l Hg Hp Hl. split; [exact Hp|]. split; [rewrite length_map; exact Hl|].
intros i Hi. rewrite length_map in Hi. destruct (Hg i Hi) as (Hv & Hb).
pose proof (Hv 0%nat ltac:(lia)) as Hv0. cbn [Z.of_nat] in Hv0. rewrite Z.add_0_r in Hv0.
rewrite <- (fpj_mbyte_mrd tfibsegs m (p + Z.of_nat i)), Hv0.
rewrite nth_error_map, (nth_error_nth' l 0 Hi). cbn [option_map]. f_equal. f_equal.
unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
rewrite (Z.mod_small (nth i l 0) (2 ^ 8)) by (change (2 ^ 8) with 256; lia).
rewrite (Z.mod_small (nth i l 0) 256) by lia. reflexivity.
Qed.
Lemma pjp_pj_in_ok : forall m q text len (tb : list byte),
  val_mem tfibsegs m q 8 text -> val_mem tfibsegs m (q + 8) 8 (text + len) -> val_mem tfibsegs m (q + 16) 8 0 ->
  (forall a, q <= a < q + 24 -> writable_at tfibsegs m a) ->
  q mod 8 = 0 -> 0 <= q -> q + 24 <= 2 ^ 64 -> 0 < text -> 0 <= len -> text + len < 2 ^ 62 ->
  Z.of_nat (length tb) = len -> garr8 tfibsegs m text (map (fun b : byte => bv_unsigned b) tb) ->
  (q + 24 <= text \/ text + len <= q) ->
  PjIn.pj_in_ok tfibsegs m q text len text 0 tb.
Proof.
intros m q text len tb Vp Vend Vdep Hw Hq8 Hq0 Hq64 Ht0 Hlen0 Htl Hlentb Hbytes Hdisj.
assert (Hmaptb : map (fun z : Z => Z_to_bv 8 z) (map (fun b : byte => bv_unsigned b) tb) = tb).
{ rewrite map_map. rewrite <- (map_id tb) at 2. apply map_ext. intros b. apply Z_to_bv_bv_unsigned. }
split.
{ exact (proj2 (fsw_val_pj_u64 tfibsegs m q text Vp ltac:(lia) Hq0 ltac:(lia))). }
split.
{ exact (proj2 (fsw_val_pj_u64 tfibsegs m (q + 8) (text + len) Vend ltac:(lia) ltac:(lia) ltac:(lia))). }
split.
{ apply (proj2 (fsw_val_pj_u32 tfibsegs m (q + 16) 0 ltac:(intros k Hk; exact (Vdep k ltac:(lia)))
    ltac:(lia) ltac:(lia) ltac:(lia))). }
split.
{ split; [exact Hq0|]. split; [exact Hq64|]. intros i Hi. exact (Hw (q + i) ltac:(lia)). }
split; [exact Hq8|]. split; [exact Ht0|]. split; [exact Htl|]. split; [lia|]. split; [exact Hlentb|].
split.
{ rewrite <- Hmaptb. apply (pjp_garr8_bytes_at m text _ Hbytes ltac:(lia)).
  rewrite ?length_map, Hlentb. lia. }
split; [cbn; lia | lia].
Qed.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* owner RELOC: S0's one named shadow-cell hypothesis (FSH_Base.v FsShadowSyms), discharged by A/ACeg.v's TfibLib
   (tl_got_shadow / tl_shadow_cell) *)
Hypothesis SHS : FsShadowSyms B.
Let TMP_TL_got : as_got_shadow B = tfib_D_GOT_asan_shadow_memory_dynamic_address := proj1 SHS.
Let TMP_TL_cell : as_shadow_cell B = tfib_D_asan_shadow_memory_dynamic_address := proj2 SHS.
(* owner RUNTIME: of S0's runtime interface (FSH_Rt.v FsRt) this walk takes only the fr_memset field's type, FSupoisonU's
   ARU form of the donor's __asan_memset contract at PC_memset 0x521bc (spec header FSH_Fn_reader.v, aintrin_realizesU OSet) *)
Hypothesis RT_memset : FSupoisonU.aintrin_realizesU tfibsegs B OSet PC_memset.

(* ---- generic helpers ---- *)
Lemma pjp_aview_unpoison : forall U (H : word -> bool) m1 m2 a,
  aview tfibsegs H m1 a = aview tfibsegs H m2 a ->
  aview tfibsegs H (unpoison U m1) a = aview tfibsegs H (unpoison U m2) a.
Proof.
intros U H m1 m2 a E.
destruct (in_ush U (bv_unsigned (Z_to_bv 64 a))) eqn:Hu.
- apply (aview_at tfibsegs). rewrite (unpoison_in U m1 _ Hu), (unpoison_in U m2 _ Hu). reflexivity.
- rewrite (aview_at tfibsegs H (unpoison U m1) m1 a (unpoison_out U m1 _ Hu)).
  rewrite (aview_at tfibsegs H (unpoison U m2) m2 a (unpoison_out U m2 _ Hu)). exact E.
Qed.
Lemma pjp_apresent_unpoison : forall U (H : word -> bool) m1 m2 a,
  (apresent H m1 a -> apresent H m2 a) -> apresent H (unpoison U m1) a -> apresent H (unpoison U m2) a.
Proof.
intros U H m1 m2 a Hm (Hh & b & Hb). unfold apresent, unpoison in *. cbv beta in *.
destruct (in_ush U (bv_unsigned (Z_to_bv 64 a))) eqn:Hu.
- split; [exact Hh | eexists; reflexivity].
- destruct (Hm (conj Hh (ex_intro _ b Hb))) as (Hh2 & b2 & Hb2). split; [exact Hh2 | exists b2; exact Hb2].
Qed.

(* ---- the memset step: RT_memset's __asan_memset contract fed into FSW_K's fsw_intrin_atU (kit arity: awr_byte takes
   (segs, B) and fr0 := frames S after own, S0 400b2a240b3 YCbq.v:465-467) ---- *)
Lemma pjp_memset_step : forall STK sp0 FP ly S W0 mem0 md0 lyc Sc U W regsT memT mdc k d (o : Z),
  ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 [] lyc Sc W (unpoison U memT) mdc k ->
  ARU tfibsegs B lyc Sc U W memT mdc ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
  YK0s.ret_ok (getr regsT 1) -> getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  getr regsT 10 = w64 d -> getr regsT 11 = w64 0 -> getr regsT 12 = w64 56 ->
  0 <= d -> d + 56 <= 2 ^ 63 ->
  dest_ok tfibsegs B lyc Sc W regsT memT d 56 -> amem_range d 56 ->
  range_addressable (aview tfibsegs (w_H W) memT) SHADOW_OFF d 56 ->
  shadow_hull_vis (aview tfibsegs (w_H W) memT) d 56 ->
  (forall a, d <= a < d + 56 ->
     awr_byte tfibsegs B STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc [] (frames S) a) ->
  SRr tfibsegs W (mkCfg (mkst regsT (Z_to_bv 64 PC_memset) memT (seg_rom tfibsegs)) mdc)
    (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
       c2 = mkCfg (mkst regs2 (getr regsT 1) mem2 (seg_rom tfibsegs)) md2 /\
       ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 [] lyc Sc W (unpoison U mem2) md2 k /\
       ARU tfibsegs B lyc Sc U W mem2 md2 /\
       (aregs_preserved regsT regs2 /\ getr regs2 10 = w64 d /\
        (forall i, 0 <= i < 56 -> aview tfibsegs (w_H W) mem2 (d + i) = Some 0) /\
        (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + 56) -> ~ (spZ regsT - ESTACK <= a < spZ regsT) ->
           aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) memT a) /\
        (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a))).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 lyc Sc U W regsT memT mdc k d o HJ HARU Hsp Hal Hneg Hbud Hra Hgp Htp
  H10 H11 H12 Hd0 Hd1 Hdest Hamr Hrad Hhull Hwr.
pose proof (fsw_ecall_preU_at B STK sp0 FP ly S W0 mem0 md0 [] lyc Sc U W memT mdc k regsT o HJ HARU Hsp Hal Hneg Hbud
  Hra Hgp Htp) as HEC.
eapply (fsw_intrin_atU B STK sp0 FP ly S W0 mem0 md0 [] lyc Sc U W memT mdc k U
  (fun a => (d <= a < d + 56) \/ (spZ regsT - ESTACK <= a < spZ regsT)) (getr regsT 1) _
  (fun regs2 mem2 md2 => aregs_preserved regsT regs2 /\ getr regs2 10 = w64 d /\
     (forall i, 0 <= i < 56 -> aview tfibsegs (w_H W) mem2 (d + i) = Some 0) /\
     (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + 56) -> ~ (spZ regsT - ESTACK <= a < spZ regsT) ->
        aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) memT a) /\
     (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)) HJ).
- eapply SRr_mono.
  { exact (RT_memset lyc Sc U W regsT memT mdc d 0 56 HEC H10 H11 H12 ltac:(lia) Hd0 Hd1 Hdest Hamr Hrad
      (fun _ => Hhull) I). }
  cbv beta. intros W' c' _ (-> & regs2 & mem2 & md2 & Ec & HARU2 & HP & Hsame & H10' & Hset & Hfr & Hpr).
  split; [reflexivity|]. exists regs2, mem2, md2.
  split. { rewrite Ec. unfold cfg_at, raZ, w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  split; [exact HARU2|]. split; [exact Hsame|].
  split.
  { intros a Ha Hn. apply pjp_aview_unpoison.
    apply Hfr; [exact Ha | intros H; apply Hn; left; exact H | intros H; apply Hn; right; exact H]. }
  split; [intros a; apply pjp_apresent_unpoison; exact (Hpr a)|].
  split; [exact HP|]. split; [exact H10'|].
  split; [intros i Hi; rewrite (Hset i Hi); reflexivity|].
  split; [exact Hfr | exact Hpr].
- intros a [Ha|Ha]; [exact (Hwr a Ha)|]. left. left. unfold ESTACK in *. lia.
Qed.

(* the hull over the unpoisoned reading carries to the machine's own memory: a user-poisoned shadow byte reads 247
   there (upoisoned), so it is not None either *)
Lemma pjp_hull_unp : forall ly S U (W : world tfibsegs) mem md x n,
  ARU tfibsegs B ly S U W mem md -> 0 <= x -> x + n <= 2 ^ 63 -> 0 < n ->
  shadow_hull_vis (aview tfibsegs (w_H W) (unpoison U mem)) x n ->
  shadow_hull_vis (aview tfibsegs (w_H W) mem) x n.
Proof.
intros ly S U W mem md x n HARU Hx0 Hxn Hn H s Hs. pose proof (H s Hs) as Hne.
destruct HARU as (_ & _ & PO).
assert (Hsb : 0 <= s < 2 ^ 64).
{ unfold shadow_addr, SHADOW_OFF in Hs.
  assert (B1 : 0 <= x / 8) by (apply Z.div_pos; lia).
  assert (B2 : (x + n - 1) / 8 <= 1152921504606846976).
  { apply (Z.le_trans _ (9223372036854775808 / 8)); [apply Z.div_le_mono; lia | vm_compute; discriminate]. }
  assert (Hlo : 0 <= (2147450880 + x / 8) / 8 * 8).
  { assert (0 <= (2147450880 + x / 8) / 8) by (apply Z.div_pos; lia). lia. }
  assert (Hhi : (2147450880 + (x + n - 1) / 8) / 8 * 8 <= 2147450880 + (x + n - 1) / 8)
    by (pose proof (Z.mul_div_le (2147450880 + (x + n - 1) / 8) 8 ltac:(lia)); lia).
  assert (H64 : 2 ^ 64 = 18446744073709551616) by reflexivity. lia. }
destruct (in_ush U s) eqn:Hu.
- rewrite (PO s Hu). discriminate.
- rewrite <- (aview_at tfibsegs (w_H W) (unpoison U mem) mem s); [exact Hne|].
  apply unpoison_out. rewrite (wz s Hsb). exact Hu.
Qed.
(* a pobj's 56 bytes lie in one in_app range (a live block or a live fake frame), hence in amem_range *)
Lemma pjp_pobj_amem : forall ly S U (W : world tfibsegs) mem md v,
  ARU tfibsegs B ly S U W mem md -> pobj tfibsegs B ly S W mem v -> amem_range v 56.
Proof.
intros ly S U W mem md v HARU HPO. pose proof HARU as (HAR & _ & _).
pose proof asan_consts as (CC1 & _).
assert (HIA : in_app v 56).
{ destruct HPO as [[((cid & pos & Hin & Hc & Hal & Hf1 & Hf2) & _ & _) | (Hb & _ & _)] _].
  - destruct (al_frames tfibsegs B (AR_laws_ok tfibsegs B) ly S W (unpoison U mem) md cid pos HAR Hin)
      as (_ & Hfh & _ & _).
    eapply in_app_sub; [exact Hfh | lia | lia | lia].
  - destruct Hb as (b & n & Hin & Hb1 & Hb2).
    destruct (al_blocks tfibsegs B (AR_laws_ok tfibsegs B) ly S W (unpoison U mem) md b n HAR Hin)
      as (_ & _ & _ & Hia & _).
    unfold HEAD in *. eapply in_app_sub; [exact Hia | lia | lia | lia]. }
destruct HIA as (H1 & [H2|(H2 & H3)]); unfold amem_range, in_app, kLowShadowBeg, kLowMemEnd, kHighMemBeg,
  kHighMemEnd, ASAN_CEIL in *; [left; lia | right; lia].
Qed.

(* the hull of a pobj: the heap arm from AR's block shadow law, the fake-frame arm from FSW_rd.fsw_afobj_hull (S0) *)
Lemma pjp_pobj_hull : forall ly S U (W : world tfibsegs) mem md v,
  ARU tfibsegs B ly S U W mem md -> pobj tfibsegs B ly S W mem v ->
  shadow_hull_vis (aview tfibsegs (w_H W) mem) v 56.
Proof.
intros ly S U W mem md v HARU HPO. pose proof HARU as (HAR & _ & _).
pose proof (fsw_pobj_low B ly S W (unpoison U mem) md mem v HAR HPO) as (Hv0 & Hv1).
pose proof asan_consts as (CC1 & _).
destruct HPO as [[HF|(Hb & Hal & Hra)] Hw].
- destruct HF as ((cid & pos & Hin & Hc & Hal & Hf1 & Hf2) & _ & _).
  apply (pjp_hull_unp ly S U W mem md v 56 HARU ltac:(lia) ltac:(lia) ltac:(lia)).
  exact (fsw_afobj_hull B ly S W (unpoison U mem) md cid pos v 56 HAR Hin Hf1 Hf2 ltac:(lia)).
- destruct Hb as (b & n & Hin & Hb1 & Hb2).
  apply (pjp_hull_unp ly S U W mem md v 56 HARU ltac:(lia) ltac:(lia) ltac:(lia)).
  exact (shadow_hull_vis_of_block tfibsegs B (AR_laws_ok tfibsegs B) ly S W (unpoison U mem) md b n v 56 HAR Hin
    ltac:(unfold HEAD in *; lia) Hb2 ltac:(lia)).
Qed.

(* ---- small image / byte helpers of this walk ---- *)
Lemma pjp_u8 : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof.
intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
apply Z.mod_small. exact Hz.
Qed.
(* fs.asan's last rw PT_LOAD [0xa1000, 0x5fd000) holds fuzz/alloc.c's four statics (MEASURED by Eval over tfibsegs) *)
Lemma pjp_rw_img : forall x, 0xa1000 <= x < 0x5fd000 -> in_img tfibsegs x.
Proof.
intros x Hx. unfold in_img. eexists. split; [right; right; right; left; reflexivity|].
match goal with |- Z.le ?lo x /\ Z.lt x (?lo' + ?sz) => let l := eval vm_compute in lo in
  let h := eval vm_compute in sz in change lo with l; change sz with h end. lia.
Qed.
(* an application byte is never a user-poisoned shadow byte *)
Lemma pjp_unpoison_app : forall ly S U (W : world tfibsegs) mem md a,
  ARU tfibsegs B ly S U W mem md -> 0 <= a < 2 ^ 64 -> ~ (SHADOW_OFF <= a < kHighMemBeg) ->
  unpoison U mem (Z_to_bv 64 a) = mem (Z_to_bv 64 a).
Proof.
intros ly S U W mem md a H Ha Hn. apply unpoison_out. rewrite (wz a Ha).
destruct (in_ush U a) eqn:E; [|reflexivity]. exfalso.
pose proof (ush_facts tfibsegs B ly S U W mem md a H E) as (_ & L). lia.
Qed.
(* fuzz/alloc.c's statics, carried by any change that keeps every image byte *)
Lemma pjp_glob_keep : forall (W : world tfibsegs) m m' live peak cnt fail,
  (forall x, in_img tfibsegs x -> aview tfibsegs (w_H W) m' x = aview tfibsegs (w_H W) m x) ->
  fs_glob tfibsegs W m live peak cnt fail -> fs_glob tfibsegs W m' live peak cnt fail.
Proof.
intros W m m' live peak cnt fail HK (G1 & G2 & G3 & G4 & R).
assert (VB : forall g v, 0xa1000 <= g -> g + 8 <= 0x5fd000 ->
  val_mem tfibsegs (mrestrict (w_H W) m) g 8 v -> val_mem tfibsegs (mrestrict (w_H W) m') g 8 v).
{ intros g v H1 H2 Hv k Hk.
  rewrite (mbyte_of_aview tfibsegs (w_H W) (w_H W) m m' (g + Z.of_nat k)
    (HK (g + Z.of_nat k) (pjp_rw_img (g + Z.of_nat k) ltac:(cbn in Hk; lia)))).
  exact (Hv k Hk). }
unfold fs_glob, fs_glob_at, G_LIVE, G_PEAK, G_COUNT, G_FAIL in *.
split; [apply VB; [lia | lia | exact G1]|]. split; [apply VB; [lia | lia | exact G2]|].
split; [apply VB; [lia | lia | exact G3]|]. split; [apply VB; [lia | lia | exact G4]|]. exact R.
Qed.
(* the read-only view, carried by any change that keeps every image byte *)
Lemma pjp_arodata_keep : forall (W : world tfibsegs) m m',
  (forall x, in_img tfibsegs x -> aview tfibsegs (w_H W) m' x = aview tfibsegs (w_H W) m x) ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) m) ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) m').
Proof.
intros W m m' HK HR a Ha Ho He. rewrite HK; [exact (HR a Ha Ho He) | exact (fsw_roP_img a Ha)].
Qed.
(* the callee-saved registers other than sp, s0 and s1 *)
Lemma pjp_cs_other : forall (P : bv 5 -> Prop), P 3%bv -> P 4%bv -> P 18%bv -> P 19%bv -> P 20%bv -> P 21%bv ->
  P 22%bv -> P 23%bv -> P 24%bv -> P 25%bv -> P 26%bv -> P 27%bv ->
  forall r : bv 5, acallee_saved (bv_unsigned r) -> bv_unsigned r <> 2 -> bv_unsigned r <> 8 ->
  bv_unsigned r <> 9 -> P r.
Proof.
intros P P3 P4 P18 P19 P20 P21 P22 P23 P24 P25 P26 P27 r Hr H2 H8 H9. unfold acallee_saved in Hr.
assert (Hc : bv_unsigned r = 3 \/ bv_unsigned r = 4 \/ bv_unsigned r = 18 \/ bv_unsigned r = 19 \/
  bv_unsigned r = 20 \/ bv_unsigned r = 21 \/ bv_unsigned r = 22 \/ bv_unsigned r = 23 \/
  bv_unsigned r = 24 \/ bv_unsigned r = 25 \/ bv_unsigned r = 26 \/ bv_unsigned r = 27) by lia.
repeat (destruct Hc as [Hc | Hc]; [match goal with HP : P ?q |- _ =>
  lazymatch goal with Hq : bv_unsigned r = ?z |- _ =>
    let w := eval vm_compute in (bv_unsigned q) in
    lazymatch w with z => replace r with q by (apply bv_eq; rewrite Hc; reflexivity); exact HP end end end|]).
replace r with (27%bv : bv 5) by (apply bv_eq; rewrite Hc; reflexivity). exact P27.
Qed.

(* ---- the walk ---- *)

(* ---- STAGE A: pj_parse's entry, prologue and __asan_memset of `out`, up to the resume state at 0x82eec.
   The walk's own text, 0x82eac .. 0x82ee8 and the call at 0x82ee8; the continuation gets the composed journal, ARU,
   the resume symbolic state (FSW_ret's fss_retT with the six frame words as chunks over the extra atoms xs), the
   registers the rest of the walk reads (sp, s0 = out, s1 = the shadow base), out's 56 zero bytes and the one
   unchanged-outside clause of the whole stage. ---- *)
Definition pjp_xs (t0 len : Z) (s1 s0 ra : word) : list word :=
  [Z_to_bv 64 t0; Z_to_bv 64 (t0 + len); s1; s0; ra].
Definition pjp_cs : list YP09.chunk :=
  [YP09.mkChunk 0 (CVal 8 (SOff (xatom 0) 0)); YP09.mkChunk 8 (CVal 8 (SOff (xatom 1) 0));
   YP09.mkChunk 16 (CVal 8 (SLit 0)); YP09.mkChunk 24 (CVal 8 (SOff (xatom 2) 0));
   YP09.mkChunk 32 (CVal 8 (SOff (xatom 3) 0)); YP09.mkChunk 40 (CVal 8 (SOff (xatom 4) 0))].

Lemma pjp_stage_A : forall (Q : world tfibsegs -> config -> Prop) ly S U W regs mem md ch t0 len out tcap,
  fpreU tfibsegs B STK_pj_parse ly S U W regs mem md ch ->
  getr regs 10 = w64 t0 -> getr regs 11 = w64 len -> getr regs 12 = w64 out ->
  0 <= len ->
  rd_text tfibsegs B ly S W mem t0 len tcap ->
  pobj tfibsegs B ly S W mem out ->
  (out + 56 <= spZ regs - STK_pj_parse \/ spZ regs <= out) ->
  (forall regs2 mem2 md2,
     ajournal tfibsegs B STK_pj_parse (spZ regs) ([(out, out + 56)] ++ FS_PSTAT_FP) ly S W (unpoison U mem) md []
       ly S W (unpoison U mem2) md2 0 ->
     ARU tfibsegs B ly S U W mem2 md2 ->
     spZ regs2 = spZ regs - 48 ->
     getr regs2 8 = w64 out ->
     getr regs2 9 = Z_to_bv 64 SHADOW_OFF ->
     (forall r : bv 5, acallee_saved (bv_unsigned r) -> bv_unsigned r <> 2 -> bv_unsigned r <> 8 ->
        bv_unsigned r <> 9 -> getr regs2 r = getr regs r) ->
     st_ok tfibsegs (Ereg regs2 (fs_extraT ++ pjp_xs t0 len (getr regs 9) (getr regs 8) (getr regs 1)))
       (fss_retT 0x82eec 48 pjp_cs [] [])
       (restrict (w_H W) (mkst regs2 (Z_to_bv 64 0x82eec) mem2 (seg_rom tfibsegs))) ->
     (forall i, 0 <= i < 56 -> aview tfibsegs (w_H W) mem2 (out + i) = Some 0) ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (out <= a < out + 56) ->
        ~ (spZ regs - 48 - ESTACK <= a < spZ regs) ->
        aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) mem a) ->
     SRr tfibsegs W (mkCfg (mkst regs2 (Z_to_bv 64 0x82eec) mem2 (seg_rom tfibsegs)) md2) Q) ->
  SRr tfibsegs W (YG0d.cfg_at tfibsegs A_pj_parse regs mem md) Q.
Proof.
intros Q ly S U W regs mem md ch t0 len out tcap HPRE H10 H11 H12 Hlen0 HTX HPO HOS HK.

pose proof (AR_laws_ok tfibsegs B) as LAWS.
destruct HPRE as [HPU HRO].
pose proof (fsw_ARU B _ ly S U W regs mem md ch HPU) as HARU.
pose proof (fsw_sp B _ ly S U W regs mem md ch HPU) as (Hal16 & Hceil & H47 & HS0).
pose proof HPU as (HAP & HUOK & HUPO).
pose proof HAP as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof asan_consts as (C1 & _ & C3 & _).
assert (FS : STK_pj_parse = ltac:(let v := eval vm_compute in (STK_pj_parse) in exact v)) by (vm_compute; reflexivity).
assert (FV : STK_parse_value 2 = ltac:(let v := eval vm_compute in (STK_parse_value 2) in exact v)) by (vm_compute; reflexivity).
pose proof (fsw_pobj_low B ly S W (unpoison U mem) md mem out HAR HPO) as (Hout0 & Hout1).
pose proof (fsw_entryT B STK_pj_parse 48 ly S U W regs mem md ch A_pj_parse TMP_TL_got TMP_TL_cell HPU
  ltac:(lia) ltac:(vm_compute; reflexivity)) as HS.
pose proof (ajournal_init tfibsegs B STK_pj_parse ([(out, out + 56)] ++ FS_PSTAT_FP) ly S W regs (unpoison U mem) md ch HAP)
  as HJ.
set (E := Ereg regs fs_extraT) in HS.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs fs_extraT 2 2%bv eq_refl); reflexivity).
unfold YG0d.cfg_at. change (w64 A_pj_parse) with (Z_to_bv 64 A_pj_parse).
(* ---- 0x82eac .. 0x82ee8: prologue, shadow base, struct pj_in at sp - 48, the memset arguments ---- *)
fsw_aj_run_toU pj_parse_tbl_ok HS HJ HARU PC_memset.
{ cbn [ss_mem fss0T fsT_regions].
  eapply awr_ok_cons_stack with (n := 2%nat); [reflexivity | exact Usp | cbn; lia | cbn; lia |].
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
(* ---- the registers and the memory at the __asan_memset call (0x82ee8 -> 0x82eec) ---- *)
pose proof (fsw_reg_lit _ E _ ms 1%bv 0x82eec HS ltac:(vm_compute; reflexivity) ltac:(lia)) as R1.
pose proof (fsw_reg_off _ E _ ms 2%bv 2 (-48) (spZ regs) HS ltac:(vm_compute; reflexivity) Usp ltac:(lia)) as R2.
pose proof (fsw_reg_atom _ regs fs_extraT _ ms 3%bv 3%bv 3 HS ltac:(vm_compute; reflexivity) eq_refl) as R3.
pose proof (fsw_reg_atom _ regs fs_extraT _ ms 4%bv 4%bv 4 HS ltac:(vm_compute; reflexivity) eq_refl) as R4.
pose proof (fsw_reg_atom _ regs fs_extraT _ ms 8%bv 12%bv 12 HS ltac:(vm_compute; reflexivity) eq_refl) as R8.
pose proof (fsw_reg_atom _ regs fs_extraT _ ms 10%bv 12%bv 12 HS ltac:(vm_compute; reflexivity) eq_refl) as R10.
pose proof (fsw_reg_lit _ E _ ms 11%bv 0 HS ltac:(vm_compute; reflexivity) ltac:(lia)) as R11.
pose proof (fsw_reg_lit _ E _ ms 12%bv 56 HS ltac:(vm_compute; reflexivity) ltac:(lia)) as R12.
assert (Hspc : spZ (ms_regs ms) = spZ regs + -48) by (unfold spZ at 1; rewrite R2; lia).
assert (SB1 : same_below mem (ms_mem ms) alloc_ceiling).
{ apply (same_below_frameN E _ mem (ms_mem ms) alloc_ceiling HF); [|lia].
  intros a (r & Hin & Ha). cbn [ss_mem fss0T fsT_regions In] in Hin.
  destruct Hin as [<-|[<-|[<-|[]]]];
    cbn [fstk fs_got_region fs_bcell_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
    [rewrite Usp in Ha; lia | lia | lia]. }
pose proof (pobj_below B ly S W (unpoison U (ms_mem ms)) _ mem (ms_mem ms) out (proj1 HJ) SB1 HPO) as HPO2.
assert (HDEST : dest_ok tfibsegs B ly S W (ms_regs ms) (ms_mem ms) out 56).
{ intros a Ha. split; [replace a with (out + (a - out)) by lia; exact (proj2 HPO2 (a - out) ltac:(lia))|].
  split.
  - destruct HPO2 as [[((cid & pos & Hin & Hc & Hal & Hf1 & Hf2) & _ & _) | (Hb & _ & _)] _].
    + destruct (al_frames tfibsegs B LAWS ly S W (unpoison U (ms_mem ms)) _ cid pos (proj1 HJ) Hin)
        as (_ & _ & Hfb & _). exact (proj2 (Hfb a ltac:(lia))).
    + destruct Hb as (b & n & Hin & Hb1 & Hb2).
      destruct (al_blocks tfibsegs B LAWS ly S W (unpoison U (ms_mem ms)) _ b n (proj1 HJ) Hin)
        as (_ & _ & _ & _ & Hbb & _). exact (proj2 (Hbb a ltac:(unfold HEAD in *; lia))).
  - rewrite Hspc. unfold ESTACK in *. lia. }
assert (HAMR : amem_range out 56) by exact (pjp_pobj_amem ly S U W (ms_mem ms) _ out HARU HPO2).
assert (HRAD : range_addressable (aview tfibsegs (w_H W) (ms_mem ms)) SHADOW_OFF out 56)
  by (destruct HPO2 as [[(_ & _ & H)|(_ & _ & H)] _]; exact H).
assert (HHULL : shadow_hull_vis (aview tfibsegs (w_H W) (ms_mem ms)) out 56)
  by exact (pjp_pobj_hull ly S U W (ms_mem ms) _ out HARU HPO2).
assert (HWR : forall a, out <= a < out + 56 ->
  awr_byte tfibsegs B STK_pj_parse (spZ regs) ([(out, out + 56)] ++ FS_PSTAT_FP) (ablocks B ly S) (ablocks B ly S)
    ly [] (frames S) a).
{ intros a Ha.
  assert (HinFP : inFP ([(out, out + 56)] ++ FS_PSTAT_FP) a)
    by (apply inFP_app; left; apply inFP_cons; left; exact Ha).
  destruct HPO2 as [[((cid & pos & Hin & Hc & Hal & Hf1 & Hf2) & _ & _) | (Hb & _ & _)] _].
  - right. right. split; [exact HinFP|]. exists cid, pos. split; [exact Hin|].
    unfold in_zr, frame_rng. cbn [fst snd]. lia.
  - destruct Hb as (b & n & Hin & Hb1 & Hb2).
    left. right. left. split; [exact HinFP|]. exists b, n. split; [exact Hin | unfold HEAD in *; lia]. }
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E _ ms HS eq_refl). cbn [ss_pc].
eapply SRr_bind.
{ exact (pjp_memset_step STK_pj_parse (spZ regs) ([(out, out + 56)] ++ FS_PSTAT_FP) ly S W (unpoison U mem) md
    ly S U W (ms_regs ms) (ms_mem ms) _ 0 out (-48) HJ HARU Hspc ltac:(reflexivity) ltac:(lia) ltac:(unfold ESTACK; lia)
    ltac:(rewrite R1; apply YK0s.ret_ok_even; vm_compute; reflexivity)
    ltac:(rewrite R3; exact Hgp) ltac:(rewrite R4; exact Htp)
    ltac:(rewrite R10; exact H12) ltac:(rewrite R11; reflexivity) ltac:(rewrite R12; reflexivity)
    ltac:(lia) ltac:(lia) HDEST HAMR HRAD HHULL HWR). }
intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & -> & HJ2 & HARU2 & HP2 & H10c & HZERO & HKEEP & HPRES).
(* ---- back at 0x82eec: the resume state, the frame read as six chunks over the extra atoms xs ---- *)
set (xs := pjp_xs t0 len (getr regs 9) (getr regs 8) (getr regs 1)).
set (cs := pjp_cs).
set (E2 := Ereg regs2 (fs_extraT ++ xs)).
assert (X0 : ew E2 (xatom 0) = Z_to_bv 64 t0) by (subst E2 xs; unfold pjp_xs; rewrite fsw_ew_xatom; reflexivity).
assert (X1 : ew E2 (xatom 1) = Z_to_bv 64 (t0 + len)) by (subst E2 xs; unfold pjp_xs; rewrite fsw_ew_xatom; reflexivity).
assert (X2 : ew E2 (xatom 2) = getr regs 9) by (subst E2 xs; unfold pjp_xs; rewrite fsw_ew_xatom; reflexivity).
assert (X3 : ew E2 (xatom 3) = getr regs 8) by (subst E2 xs; unfold pjp_xs; rewrite fsw_ew_xatom; reflexivity).
assert (X4 : ew E2 (xatom 4) = getr regs 1) by (subst E2 xs; unfold pjp_xs; rewrite fsw_ew_xatom; reflexivity).
pose proof (fsw_region_nth E _ _ 0 _ HS eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
(* the six frame words at the call, read off the pre-call state's one stack region *)
pose proof (fsw_rblock_low B ly S W (unpoison U mem) md mem t0 tcap HAR (proj1 (proj2 HTX))) as (Ht00 & Ht01).
assert (Htcap : 0 < tcap) by (destruct HTX as (_ & (_ & _ & Hn & _) & _); exact Hn).
unfold HEAD in Ht00.
assert (Hlent : len < tcap) by exact (proj2 (proj2 HTX)).
assert (Ura : bv_unsigned (getr regs 1) = raZ regs) by reflexivity.
assert (Vp : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (spZ regs + -48) 8 t0).
{ eapply (fsw_field E _ 2 (spZ regs) _ _ _ _ _ (-48) 8%N (SOff 10 0) t0);
  [exact HR0 | exact Usp | cbn; tauto
  | rewrite fsw_SOff0; subst E; rewrite (ew_Ereg_nat regs fs_extraT 10 10%bv eq_refl); exact H10
  | replace (8 * Z.of_N 8) with 64 by reflexivity; lia
  | change (Z.of_N 8) with 8; lia]. }
assert (Vend : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (spZ regs + -40) 8 (t0 + len)).
{ eapply (fsw_field E _ 2 (spZ regs) _ _ _ _ _ (-40) 8%N (SAlu ALU_ADD (SOff 10 0) (SOff 11 0)) (t0 + len));
  [exact HR0 | exact Usp | cbn; tauto | | replace (8 * Z.of_N 8) with 64 by reflexivity; lia
  | change (Z.of_N 8) with 8; lia].
  rewrite denot_lit_U, U_SAlu. cbn [zalu_raw].
  rewrite (U_atom E 10 t0 ltac:(subst E; rewrite (ew_Ereg_nat regs fs_extraT 10 10%bv eq_refl); exact H10) ltac:(lia)).
  rewrite (U_atom E 11 len ltac:(subst E; rewrite (ew_Ereg_nat regs fs_extraT 11 11%bv eq_refl); exact H11) ltac:(lia)).
  rewrite zcanon_id by (unfold M64; lia). reflexivity. }
assert (Vdep : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (spZ regs + -32) 8 0).
{ eapply (fsw_field E _ 2 (spZ regs) _ _ _ _ _ (-32) 8%N (SLit 0) 0);
  [exact HR0 | exact Usp | cbn; tauto | reflexivity
  | replace (8 * Z.of_N 8) with 64 by reflexivity; lia
  | change (Z.of_N 8) with 8; lia]. }
assert (Vs1 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (spZ regs + -24) 8 (bv_unsigned (getr regs 9))).
{ eapply (fsw_field E _ 2 (spZ regs) _ _ _ _ _ (-24) 8%N (SOff 9 0) (bv_unsigned (getr regs 9)));
  [exact HR0 | exact Usp | cbn; tauto
  | rewrite fsw_SOff0; subst E; rewrite (ew_Ereg_nat regs fs_extraT 9 9%bv eq_refl);
    symmetry; apply Z_to_bv_bv_unsigned
  | pose proof (u64_range (getr regs 9));
    replace (8 * Z.of_N 8) with 64 by reflexivity; lia
  | change (Z.of_N 8) with 8; lia]. }
assert (Vs0 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (spZ regs + -16) 8 (bv_unsigned (getr regs 8))).
{ eapply (fsw_field E _ 2 (spZ regs) _ _ _ _ _ (-16) 8%N (SOff 8 0) (bv_unsigned (getr regs 8)));
  [exact HR0 | exact Usp | cbn; tauto
  | rewrite fsw_SOff0; subst E; rewrite (ew_Ereg_nat regs fs_extraT 8 8%bv eq_refl);
    symmetry; apply Z_to_bv_bv_unsigned
  | pose proof (u64_range (getr regs 8));
    replace (8 * Z.of_N 8) with 64 by reflexivity; lia
  | change (Z.of_N 8) with 8; lia]. }
assert (Vra : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (spZ regs + -8) 8 (raZ regs)).
{ eapply (fsw_field E _ 2 (spZ regs) _ _ _ _ _ (-8) 8%N (SOff 1 0) (raZ regs));
  [exact HR0 | exact Usp | cbn; tauto
  | rewrite fsw_SOff0; subst E; rewrite (ew_Ereg_nat regs fs_extraT 1 1%bv eq_refl);
    unfold raZ; symmetry; apply Z_to_bv_bv_unsigned
  | unfold raZ; pose proof (u64_range (getr regs 1));
    replace (8 * Z.of_N 8) with 64 by reflexivity; lia
  | change (Z.of_N 8) with 8; lia]. }
assert (Usp2 : bv_unsigned (ew E2 2) = spZ regs - 48).
{ subst E2. rewrite (ew_Ereg_nat regs2 (fs_extraT ++ xs) 2 2%bv eq_refl).
  rewrite (fsw_pres (ms_regs ms) regs2 2%bv HP2 ltac:(unfold acallee_saved; vm_compute; lia)). lia. }
assert (CHK : Forall (YP09.chunk_ok tfibsegs E2 (mrestrict (w_H W) (ms_mem ms)) (spZ regs - 48)) cs).
{ subst cs. repeat apply Forall_cons; try apply Forall_nil.
  - eapply (chunk_ok_val tfibsegs E2 _ _ 0 8%N (SOff (xatom 0) 0) t0);
    [rewrite fsw_SOff0; exact X0 | replace (8 * Z.of_N 8) with 64 by reflexivity; lia
    | change (Z.of_N 8) with 8; lia
    | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; replace (spZ regs - 48 + 0) with (spZ regs + -48) by lia; exact Vp].
  - eapply (chunk_ok_val tfibsegs E2 _ _ 8 8%N (SOff (xatom 1) 0) (t0 + len));
    [rewrite fsw_SOff0; exact X1 | replace (8 * Z.of_N 8) with 64 by reflexivity; lia
    | change (Z.of_N 8) with 8; lia
    | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; replace (spZ regs - 48 + 8) with (spZ regs + -40) by lia; exact Vend].
  - eapply (chunk_ok_val tfibsegs E2 _ _ 16 8%N (SLit 0) 0);
    [reflexivity | replace (8 * Z.of_N 8) with 64 by reflexivity; lia | change (Z.of_N 8) with 8; lia
    | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; replace (spZ regs - 48 + 16) with (spZ regs + -32) by lia; exact Vdep].
  - eapply (chunk_ok_val tfibsegs E2 _ _ 24 8%N (SOff (xatom 2) 0) (bv_unsigned (getr regs 9)));
    [rewrite fsw_SOff0, X2; symmetry; apply Z_to_bv_bv_unsigned
    | pose proof (u64_range (getr regs 9)); replace (8 * Z.of_N 8) with 64 by reflexivity; lia
    | change (Z.of_N 8) with 8; lia
    | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; replace (spZ regs - 48 + 24) with (spZ regs + -24) by lia; exact Vs1].
  - eapply (chunk_ok_val tfibsegs E2 _ _ 32 8%N (SOff (xatom 3) 0) (bv_unsigned (getr regs 8)));
    [rewrite fsw_SOff0, X3; symmetry; apply Z_to_bv_bv_unsigned
    | pose proof (u64_range (getr regs 8)); replace (8 * Z.of_N 8) with 64 by reflexivity; lia
    | change (Z.of_N 8) with 8; lia
    | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; replace (spZ regs - 48 + 32) with (spZ regs + -16) by lia; exact Vs0].
  - eapply (chunk_ok_val tfibsegs E2 _ _ 40 8%N (SOff (xatom 4) 0) (raZ regs));
    [rewrite fsw_SOff0, X4; unfold raZ; symmetry; apply Z_to_bv_bv_unsigned
    | unfold raZ; pose proof (u64_range (getr regs 1)); replace (8 * Z.of_N 8) with 64 by reflexivity; lia
    | change (Z.of_N 8) with 8; lia
    | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; replace (spZ regs - 48 + 40) with (spZ regs + -8) by lia; exact Vra]. }
assert (KEEP : forall a, spZ regs - 48 <= a < spZ regs ->
  mbyte tfibsegs (mrestrict (w_H W) mem2) a = mbyte tfibsegs (mrestrict (w_H W) (ms_mem ms)) a).
{ intros a Ha. apply (mbyte_of_aview tfibsegs). apply HKEEP; [lia| |rewrite Hspc; unfold ESTACK; lia].
  intros Hout. destruct HOS as [HOS1|HOS1]; lia. }
pose proof (fsw_resume_after_rtU_args B STK_pj_parse (spZ regs) ([(out, out + 56)] ++ FS_PSTAT_FP) ly S W
  (unpoison U mem) md [] ly S U W mem2 md2 0 (ms_regs ms) regs2 (ms_mem ms) 48 xs cs [] [] 0x82eec
  TMP_TL_got TMP_TL_cell HJ2 HARU2 HP2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(reflexivity)
  ltac:(unfold pjp_cs in *; subst cs; vm_compute; reflexivity)
  ltac:(unfold pjp_cs in *; subst cs; repeat apply Forall_cons; try apply Forall_nil; cbn; lia)
  CHK KEEP (Forall_nil _)
  ltac:(unfold pjp_cs in *; subst cs; apply pairwise_disjoint_of_extents;
        unfold fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region, extent_of_region;
        cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val];
        change (Ereg regs2 (fs_extraT ++ xs)) with E2; rewrite Usp2;
        unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address;
        cbn [zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd];
        revert Hceil C1 H47 FS; clear; intros; repeat split; lia)
  ltac:(exact I)) as HS2.
(* ---- the continuation: the facts the rest of the walk reads off this state ---- *)
rewrite R1. change (Z_to_bv 64 536300) with (Z_to_bv 64 0x82eec).
apply (HK regs2 mem2 md2 HJ2 HARU2).
- unfold spZ at 1. rewrite (fsw_pres (ms_regs ms) regs2 2%bv HP2 ltac:(unfold acallee_saved; vm_compute; lia)). lia.
- rewrite (fsw_pres (ms_regs ms) regs2 8%bv HP2 ltac:(unfold acallee_saved; vm_compute; lia)), R8. exact H12.
- rewrite (fsw_pres (ms_regs ms) regs2 9%bv HP2 ltac:(unfold acallee_saved; vm_compute; lia)).
  rewrite (fsw_reg_extra _ regs fs_extraT _ ms 9%bv 0 HS ltac:(vm_compute; reflexivity)). reflexivity.
- intros r Hr Hn2 Hn8 Hn9. rewrite (fsw_pres (ms_regs ms) regs2 r HP2 Hr). revert r Hr Hn2 Hn8 Hn9.
  apply pjp_cs_other;
    [ exact (fsw_reg_atom _ regs fs_extraT _ ms 3%bv 3%bv 3 HS ltac:(vm_compute; reflexivity) eq_refl)
    | exact (fsw_reg_atom _ regs fs_extraT _ ms 4%bv 4%bv 4 HS ltac:(vm_compute; reflexivity) eq_refl)
    | exact (fsw_reg_atom _ regs fs_extraT _ ms 18%bv 18%bv 18 HS ltac:(vm_compute; reflexivity) eq_refl)
    | exact (fsw_reg_atom _ regs fs_extraT _ ms 19%bv 19%bv 19 HS ltac:(vm_compute; reflexivity) eq_refl)
    | exact (fsw_reg_atom _ regs fs_extraT _ ms 20%bv 20%bv 20 HS ltac:(vm_compute; reflexivity) eq_refl)
    | exact (fsw_reg_atom _ regs fs_extraT _ ms 21%bv 21%bv 21 HS ltac:(vm_compute; reflexivity) eq_refl)
    | exact (fsw_reg_atom _ regs fs_extraT _ ms 22%bv 22%bv 22 HS ltac:(vm_compute; reflexivity) eq_refl)
    | exact (fsw_reg_atom _ regs fs_extraT _ ms 23%bv 23%bv 23 HS ltac:(vm_compute; reflexivity) eq_refl)
    | exact (fsw_reg_atom _ regs fs_extraT _ ms 24%bv 24%bv 24 HS ltac:(vm_compute; reflexivity) eq_refl)
    | exact (fsw_reg_atom _ regs fs_extraT _ ms 25%bv 25%bv 25 HS ltac:(vm_compute; reflexivity) eq_refl)
    | exact (fsw_reg_atom _ regs fs_extraT _ ms 26%bv 26%bv 26 HS ltac:(vm_compute; reflexivity) eq_refl)
    | exact (fsw_reg_atom _ regs fs_extraT _ ms 27%bv 27%bv 27 HS ltac:(vm_compute; reflexivity) eq_refl) ].
- exact HS2.
- exact HZERO.
- intros a Ha Hout Hstk2. rewrite (HKEEP a Ha Hout ltac:(rewrite Hspc; unfold ESTACK in *; lia)).
  apply (aview_at tfibsegs). apply HF. rewrite (wz a Ha). intros (r & Hin & Hr).
  cbn [ss_mem fss0T fsT_regions In] in Hin.
  destruct Hin as [<-|[<-|[<-|[]]]];
    cbn [fstk fs_got_region fs_bcell_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    [rewrite Usp in Hr; unfold ESTACK in *; lia | lia | lia].
Qed.

(* ================= the call of parse_value (0x82ef4 -> 0x82ef8), the tail, and pj_parse_holds =================
   After stage A the walk is at 0x82eec with struct pj_in at sp - 48 holding {p = text, end = text + len, depth = 0},
   s0 = out (zeroed), s1 = the shadow base, ra / s0 / s1 saved at sp - 8 / sp - 16 / sp - 24. 0x82eec `mv a0,sp` and
   0x82ef0 `mv a1,s0` set the two arguments; parse_value (level 0) runs over the whole document and leaves
   in->p = text + |wt|, where wt is the writer's text of the value and the document is wt ++ (if pr then [10] else []).
   The tail, 0x82ef8 .. 0x82f90: `bnez a0` is dead (parse_value answers 0); `bgeu in->p, in->end` decides the
   white-space loop (taken at once for a compact document, one iteration over the trailing newline for a pretty one);
   the loop's inline shadow check at 0x82f20-0x82f2c is discharged by the TOKEN engine over rd_text's live block, so
   __asan_report_load1 at 0x82f60 is UNTAKEN; then in->p = in->end, `beq` jumps to 0x82f94, a0 := 0 and the epilogue
   returns. pj_free at 0x82f78 is the failure exit and is never reached. ---- *)
(* the resume env after parse_value returns (FSW_K's fss_ret: extra atoms from 32): 32 = in->p, 33 = the entry ra,
   34 = the entry s0, 35 = the entry s1 *)
Definition pjp_rxs (p' : Z) (ra s0 s1 : word) : list word := [Z_to_bv 64 p'; ra; s0; s1].
(* the frame words the tail reads at [sp - 48, sp): in->p, in->end = in->p + dd, the saved s1 / s0 / ra *)
Definition pjp_rcs (dd : Z) : list YP09.chunk :=
  [YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 8 (SOff 32 dd));
   YP09.mkChunk 24 (CVal 8 (SOff 35 0)); YP09.mkChunk 32 (CVal 8 (SOff 34 0));
   YP09.mkChunk 40 (CVal 8 (SOff 33 0))].
(* the document byte at in->p (a pretty document's trailing newline), read only, based at atom 32 *)
Definition pjp_nl_region : YP09.region :=
  YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 10))].
(* the largest alloc_ceiling of any run (YCbq.asan_consts) *)
Definition PJP_CEIL : Z := 0x7fffff800000.
(* the shadow entry of the token run: the one byte at in->p *)
Definition pjp_SH : list shent := [mkSHE 32 0 1].
(* the callee-saved registers at pj_parse's ret: sp back up by the frame, s0 / s1 reloaded (atoms 34 / 35) *)
Definition pjp_expect (r : bv 5) : sv :=
  match bv_unsigned r with 2 => SOff 2 48 | 8 => SOff 34 0 | 9 => SOff 35 0 | z => SOff (Z.to_nat z) 0 end.

(* owner READER (a Theorem Labs lane): parse_value's ASan contract at level 0, FSH_Fn_reader.v parse_value_spec *)
Hypothesis PV : @parse_value_spec fx rc SK tfibsegs B 0%nat.

(* a goal over bv 5 register literals: their unsigned values, then arithmetic *)
Ltac pjp_lit_tac := repeat match goal with |- context [bv_unsigned ?q] =>
  let z := eval vm_compute in (bv_unsigned q) in change (bv_unsigned q) with z end;
  try unfold acallee_saved; lia.

Theorem pj_parse_holds : @pj_parse_spec fx rc SK tfibsegs B.
Proof.
intros ly S U W regs mem md ch t0 len out tcap t pr live peak cnt fail. cbv zeta.
intros HPRE HH HFRL H10 H11 H12 HTX HZB HLEN HWF HDEP HDV HDS HPO HOS HOT HGL HQ HSZ HLIVE HNEV HBB.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as HPRE'. destruct HPRE' as [HAPU HRO].
pose proof (fsw_sp B _ ly S U W regs mem md ch HAPU) as (Hal16 & Hceil & H47 & HSTK0).
pose proof HAPU as (HAP & HUOK & HUPO).
pose proof HAP as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof (fsw_ARU B _ ly S U W regs mem md ch HAPU) as HARU.
pose proof Hstk as (_ & _ & Hlo1 & Hlo2 & _ & _ & _ & Htop & _).
assert (FSP : STK_pj_parse = ltac:(let v := eval vm_compute in (STK_pj_parse) in exact v)) by (vm_compute; reflexivity).
assert (FPV : STK_parse_value 2 = ltac:(let v := eval vm_compute in (STK_parse_value 2) in exact v)) by (vm_compute; reflexivity).
rewrite FSP in Hceil.
pose proof (fsw_pobj_low B ly S W (unpoison U mem) md mem out HAR HPO) as (Hout0 & Hout1).
pose proof (fsw_rblock_low B ly S W (unpoison U mem) md mem t0 tcap HAR (proj1 (proj2 HTX))) as (Ht00 & Ht01).
pose proof (proj2 (proj2 HTX)) as Hlentcap.
assert (Hlen0 : 0 <= len) by (rewrite <- HLEN; lia).
unfold HEAD in Ht00, HOT.
(* ---- the document's bytes, and the position parse_value leaves in->p at ---- *)
remember (if pr then 1 else 0) as dd eqn:Edd.
set (wt := concat (WriterValue.wvpieces t pr 0)).
set (tb := map (fun z => Z_to_bv 8 z) (WriterValue.wdoc t pr)).
assert (EWD : WriterValue.wdoc t pr = wt ++ (if pr then [10] else [])).
{ subst wt. unfold WriterValue.wdoc, WriterValue.wdpieces. rewrite concat_app.
  destruct pr; cbn [concat]; rewrite ?app_nil_r; reflexivity. }
assert (HBOK : Forall (fun b => 0 <= b < 256) (WriterValue.wdoc t pr)).
{ pose proof (garr8_bytes_ok tfibsegs _ t0 _ HZB) as HB0. unfold YI00.bytes_ok in HB0.
  apply Forall_app in HB0. exact (proj1 HB0). }
assert (Hzb : ReaderRes.zb tb = WriterValue.wdoc t pr).
{ subst tb. unfold ReaderRes.zb. rewrite map_map. rewrite <- (map_id (WriterValue.wdoc t pr)) at 2.
  apply map_ext_in. intros a Ha. exact (pjp_u8 a (proj1 (Forall_forall _ _) HBOK a Ha)). }
assert (Hlentb : Z.of_nat (length tb) = len) by (subst tb; rewrite length_map; exact HLEN).
assert (ELEN : Z.of_nat (length wt) = len - dd).
{ rewrite <- HLEN, EWD, length_app. subst dd. destruct pr; cbn [length]; lia. }
assert (Hdd : 0 <= dd <= 1) by (subst dd; destruct pr; lia).
assert (Hlen1 : Z.of_nat (length (WriterValue.wdoc t pr ++ [0])) = len + 1)
  by (rewrite length_app, Nat2Z.inj_add, HLEN; reflexivity).
(* ---- STAGE A ---- *)
apply (pjp_stage_A _ ly S U W regs mem md ch t0 len out tcap HPRE H10 H11 H12 Hlen0 HTX HPO HOS).
intros regs2 mem2 md2 HJ2 HARU2 Hsp2 R8 R9 RCS HS2 HZERO HKEEP.
(* ---- what stage A leaves at mem2 ---- *)
assert (HOUTIMG : forall x, out <= x < out + 56 -> ~ in_img tfibsegs x).
{ intros x Hx. pose proof HPO as HPOi.
  destruct HPOi as [[((cid & pos & Hin & _ & _ & F1 & F2) & _ & _)|((b & n & Hin & Bb1 & Bb2) & _ & _)] _].
  - exact (frm_img tfibsegs B LAWS ly S W (unpoison U mem) md cid pos x HAR Hin ltac:(lia)).
  - exact (blk_img tfibsegs B LAWS ly S W (unpoison U mem) md b n x HAR Hin ltac:(unfold HEAD in *; lia)). }
assert (HOUTSH : forall x, out <= x < out + 56 -> ~ (SHADOW_OFF <= x < kHighMemBeg)).
{ intros x Hx. pose proof (fsw_pobj_off_shadow B ly S W (unpoison U mem) md mem out HAR HPO x Hx) as Hs.
  unfold SHADOW_OFF, kHighMemBeg in *. lia. }
assert (KEEPB : forall a, 0 <= a < alloc_ceiling -> ~ (out <= a < out + 56) ->
  aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) mem a).
{ intros a Ha Hno. apply HKEEP; [lia | exact Hno | unfold ESTACK in *; lia]. }
assert (KEEPM : forall a, 0 <= a < alloc_ceiling -> ~ (out <= a < out + 56) ->
  mbyte tfibsegs (mrestrict (w_H W) mem2) a = mbyte tfibsegs (mrestrict (w_H W) mem) a)
  by (intros a Ha Hno; apply (mbyte_of_aview tfibsegs); exact (KEEPB a Ha Hno)).
assert (KEEPI : forall x, in_img tfibsegs x -> aview tfibsegs (w_H W) mem2 x = aview tfibsegs (w_H W) mem x).
{ intros x Hx. apply KEEPB; [pose proof (fs_segs_img x Hx); unfold FS_IMG_END in *; lia
  | intros Hr; exact (HOUTIMG x Hr Hx)]. }
assert (HGL2 : fs_glob tfibsegs W mem2 live peak cnt fail)
  by exact (pjp_glob_keep W mem mem2 live peak cnt fail KEEPI HGL).
assert (HRO2 : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) mem2))
  by exact (pjp_arodata_keep W mem mem2 KEEPI HRO).
assert (HZB2 : zbytes_at tfibsegs W mem2 t0 (WriterValue.wdoc t pr ++ [0])).
{ apply (garr8_frame tfibsegs _ _ t0 _ HZB). intros a Ha. rewrite Hlen1 in Ha.
  apply KEEPM; [lia | lia]. }
assert (HTX2 : rd_text tfibsegs B ly S W mem2 t0 len tcap).
{ pose proof HTX as (X1 & (Y1 & Y2 & Y3 & Y4) & X3). split; [exact X1|]. split; [|exact X3].
  split; [exact Y1|]. split; [exact Y2|]. split; [exact Y3|].
  intros k Hk. rewrite KEEPM; [exact (Y4 k Hk) | cbn in Hk; unfold HEAD in *; lia
  | cbn in Hk; unfold HEAD in *; lia]. }
assert (HRA2 : range_addressable (aview tfibsegs (w_H W) mem2) SHADOW_OFF out 56).
{ assert (HRA0 : range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF out 56)
    by (destruct (proj1 HPO) as [(_ & _ & Hr)|(_ & _ & Hr)]; exact Hr).
  intros x Hx. destruct (HRA0 x Hx) as (s & Es & Hok). exists s. split; [|exact Hok].
  rewrite <- Es. apply KEEPB.
  - apply fsw_shadow_below. lia.
  - intros Hr. apply (HOUTSH (shadow_of_addr SHADOW_OFF x) Hr).
    unfold shadow_of_addr, SHADOW_OFF, kHighMemBeg. Z.div_mod_to_equations. lia. }
assert (HPRESo : forall i, 0 <= i < 56 -> apresent (w_H W) mem2 (out + i)).
{ intros i Hi.
  assert (Hpr : apresent (w_H W) (unpoison U mem2) (out + i)).
  { pose proof HPO as HPOi.
    destruct HPOi as [[((cid & pos & Hin & _ & _ & F1 & F2) & _ & _)|((b & n & Hin & Bb1 & Bb2) & _ & _)] _].
    - destruct (al_frames tfibsegs B LAWS ly S W (unpoison U mem2) md2 cid pos (proj1 HARU2) Hin)
        as (_ & _ & Hfb & _). exact (proj1 (Hfb (out + i) ltac:(lia))).
    - destruct (al_blocks tfibsegs B LAWS ly S W (unpoison U mem2) md2 b n (proj1 HARU2) Hin)
        as (_ & _ & _ & _ & Hbb & _). exact (proj1 (Hbb (out + i) ltac:(unfold HEAD in *; lia))). }
  destruct Hpr as (Hh & bb & Hb). split; [exact Hh|]. exists bb.
  rewrite <- (pjp_unpoison_app ly S U W mem2 md2 (out + i) HARU2 ltac:(lia)
    ltac:(exact (HOUTSH (out + i) ltac:(lia)))). exact Hb. }
assert (HPO2 : pobj tfibsegs B ly S W mem2 out).
{ split.
  - destruct (proj1 HPO) as [(Hpl & Ha8 & _)|(Hpl & Ha8 & _)]; [left|right];
      (split; [exact Hpl | split; [exact Ha8 | exact HRA2]]).
  - intros i Hi. apply (apresent_writable tfibsegs). exact (HPRESo i Hi). }
assert (HZBO : forall i, 0 <= i < 56 -> mbyte tfibsegs (mrestrict (w_H W) mem2) (out + i) = Some (Z_to_bv 8 0)).
{ intros i Hi. pose proof (HZERO i Hi) as Hv. unfold aview in Hv.
  destruct (mbyte tfibsegs (mrestrict (w_H W) mem2) (out + i)) as [bb|] eqn:Eb; cbn in Hv; [|discriminate].
  injection Hv as Hv. f_equal. apply bv_eq. rewrite Hv. vm_compute. reflexivity. }
assert (HOUT8 : out mod 8 = 0) by (destruct (proj1 HPO) as [(_ & Ha8 & _)|(_ & Ha8 & _)]; exact Ha8).
(* ---- 0x82eec .. the call of parse_value at 0x82ef4 ---- *)
assert (Usp2 : bv_unsigned (ew (Ereg regs2 (fs_extraT ++ pjp_xs t0 len (getr regs 9) (getr regs 8) (getr regs 1))) 2)
  = spZ regs - 48)
  by (rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl); exact Hsp2).
fsw_aj_run_toU pj_parse_tbl_ok HS2 HJ2 HARU2 A_parse_value.
{ cbn [ss_mem fss_retT fsT_ret_regions app].
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -48);
    [reflexivity | rewrite Usp2; lia | cbn; lia | cbn; lia |].
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
assert (SB2 : same_below mem2 (ms_mem ms) alloc_ceiling).
{ apply (same_below_frameN _ _ mem2 (ms_mem ms) alloc_ceiling HF); [|lia].
  intros a (r & Hin & Ha). cbn [ss_mem fss_retT fsT_ret_regions In app] in Hin.
  destruct Hin as [<-|[<-|[<-|[]]]];
    cbn [fstk_ret fs_got_region fs_bcell_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
    [rewrite Usp2 in Ha; lia | lia | lia]. }
assert (KEEPC : forall a, 0 <= a < alloc_ceiling -> ~ (out <= a < out + 56) ->
  mbyte tfibsegs (mrestrict (w_H W) (ms_mem ms)) a = mbyte tfibsegs (mrestrict (w_H W) mem) a).
{ intros a Ha Hno. rewrite (mbyte_below (w_H W) mem2 (ms_mem ms) alloc_ceiling a SB2 Ha).
  exact (KEEPM a Ha Hno). }
(* the registers at the call *)
pose proof (fsw_reg_lit _ _ _ ms 1%bv 0x82ef8 HS2 ltac:(vm_compute; reflexivity) ltac:(lia)) as R1.
pose proof (fsw_reg_atom _ regs2 _ _ ms 2%bv 2%bv 2 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R2.
pose proof (fsw_reg_atom _ regs2 _ _ ms 3%bv 3%bv 3 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R3.
pose proof (fsw_reg_atom _ regs2 _ _ ms 4%bv 4%bv 4 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R4.
pose proof (fsw_reg_atom _ regs2 _ _ ms 8%bv 8%bv 8 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R8c.
pose proof (fsw_reg_atom _ regs2 _ _ ms 10%bv 2%bv 2 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R10.
pose proof (fsw_reg_atom _ regs2 _ _ ms 11%bv 8%bv 8 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R11.
assert (Hspc : spZ (ms_regs ms) = spZ regs - 48) by (unfold spZ; rewrite R2; exact Hsp2).
assert (R10' : getr (ms_regs ms) 10 = w64 (spZ regs - 48)).
{ rewrite R10. unfold w64. rewrite <- Hsp2. unfold spZ. symmetry. apply Z_to_bv_bv_unsigned. }
assert (R11' : getr (ms_regs ms) 11 = w64 out) by (rewrite R11; exact R8).
(* the frame words at the call *)
pose proof (fsw_region_nth _ _ _ 0 _ HS2 eq_refl) as HR2. cbn [ms_mem restrict] in HR2.
assert (X0 : ew (Ereg regs2 (fs_extraT ++ pjp_xs t0 len (getr regs 9) (getr regs 8) (getr regs 1))) (xatom 0)
  = Z_to_bv 64 t0) by (unfold pjp_xs; rewrite fsw_ew_xatom; reflexivity).
assert (X1 : ew (Ereg regs2 (fs_extraT ++ pjp_xs t0 len (getr regs 9) (getr regs 8) (getr regs 1))) (xatom 1)
  = Z_to_bv 64 (t0 + len)) by (unfold pjp_xs; rewrite fsw_ew_xatom; reflexivity).
assert (Vp : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (spZ regs - 48 + 0) 8 t0).
{ eapply (fsw_field _ _ 2 (spZ regs - 48) _ _ _ _ _ 0 8%N (SOff (xatom 0) 0) t0);
  [exact HR2 | exact Usp2 | cbn; tauto | rewrite fsw_SOff0; exact X0
  | replace (8 * Z.of_N 8) with 64 by reflexivity; lia | change (Z.of_N 8) with 8; lia]. }
rewrite Z.add_0_r in Vp.
assert (Vend : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (spZ regs - 48 + 8) 8 (t0 + len)).
{ eapply (fsw_field _ _ 2 (spZ regs - 48) _ _ _ _ _ 8 8%N (SOff (xatom 1) 0) (t0 + len));
  [exact HR2 | exact Usp2 | cbn; tauto | rewrite fsw_SOff0; exact X1
  | replace (8 * Z.of_N 8) with 64 by reflexivity; lia | change (Z.of_N 8) with 8; lia]. }
assert (Vdep : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (spZ regs - 48 + 16) 8 0).
{ eapply (fsw_field _ _ 2 (spZ regs - 48) _ _ _ _ _ 16 8%N (SLit 0) 0);
  [exact HR2 | exact Usp2 | cbn; tauto | reflexivity
  | replace (8 * Z.of_N 8) with 64 by reflexivity; lia | change (Z.of_N 8) with 8; lia]. }
assert (Hwr : forall a, spZ regs - 48 <= a < spZ regs - 48 + 24 ->
  writable_at tfibsegs (mrestrict (w_H W) (ms_mem ms)) a).
{ intros a Ha. pose proof HR2 as (_ & _ & Hw & _).
  specialize (Hw (a - (spZ regs - 48)) ltac:(cbn; lia)).
  cbn [YP09.r_base base_val] in Hw. rewrite Usp2 in Hw.
  replace (spZ regs - 48 + (a - (spZ regs - 48))) with a in Hw by lia. exact Hw. }
assert (HZBc : zbytes_at tfibsegs W (ms_mem ms) t0 (WriterValue.wdoc t pr ++ [0])).
{ apply (garr8_frame tfibsegs _ _ t0 _ HZB). intros a Ha. rewrite Hlen1 in Ha. apply KEEPC; lia. }
assert (HGARR : garr8 tfibsegs (mrestrict (w_H W) (ms_mem ms)) t0 (map (fun b : byte => bv_unsigned b) tb)).
{ rewrite <- Hzb in HZBc. unfold ReaderRes.zb in HZBc.
  exact (proj1 (proj1 (garr8_app tfibsegs _ t0 _ [0]) HZBc)). }
assert (HPIN : PjIn.pj_in_ok tfibsegs (mrestrict (w_H W) (ms_mem ms)) (spZ regs - 48) t0 len t0 0 tb).
{ apply (pjp_pj_in_ok _ _ t0 len tb Vp Vend Vdep Hwr
    ltac:(pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as Hdm; rewrite Hal16, Z.add_0_r in Hdm;
          rewrite Hdm; replace (16 * (spZ regs / 16) - 48) with ((2 * (spZ regs / 16) - 6) * 8) by lia;
          apply Z_mod_mult)
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hlentb HGARR ltac:(lia)). }
(* parse_value's premises at the call *)
pose proof (fsw_fpreU_atFP B STK_pj_parse (spZ regs) ([(out, out + 56)] ++ FS_PSTAT_FP) ly S U W (unpoison U mem) md []
    ly S W (ms_mem ms) _ 0 (ms_regs ms) (STK_parse_value 2) (-48) [] HJ2 HARU2
    (arodata_below B W mem2 (ms_mem ms) SB2 HRO2) ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(rewrite R1; apply YK0s.ret_ok_even; vm_compute; reflexivity)
    ltac:(unfold raZ; rewrite R1, unsigned_lit_small by lia; lia)
    ltac:(rewrite R3; rewrite RCS by (unfold acallee_saved; vm_compute; lia); exact Hgp)
    ltac:(rewrite R4; rewrite RCS by (unfold acallee_saved; vm_compute; lia); exact Htp)
    ltac:(apply achain_low; unfold s0Z; rewrite R8c, R8; unfold w64;
          rewrite unsigned_lit_small by lia; lia)) as HPREc.
assert (HPOc : pobj tfibsegs B ly S W (ms_mem ms) out)
  by exact (pobj_below B ly S W _ _ mem2 (ms_mem ms) out (proj1 HARU2) SB2 HPO2).
assert (HZEROc : PjStruct.pj_zero tfibsegs (mrestrict (w_H W) (ms_mem ms)) out).
{ assert (HB0 : forall i, 0 <= i < 56 ->
    mbyte tfibsegs (mrestrict (w_H W) (ms_mem ms)) (out + i) = Some (Z_to_bv 8 0)).
  { intros i Hi. rewrite (mbyte_below (w_H W) mem2 (ms_mem ms) alloc_ceiling (out + i) SB2 ltac:(lia)).
    exact (HZBO i Hi). }
  split.
  - split; [exact HOUT8|]. split; [lia|]. split; [lia|]. intros a Ha. split.
    + pose proof (proj2 HPOc (a - out) ltac:(lia)) as Hw.
      replace (out + (a - out)) with a in Hw by lia. unfold writable_at in Hw. unfold Mem.wa. exact Hw.
    + exists (Z_to_bv 8 0). rewrite <- (fpj_mbyte_mrd tfibsegs _ a).
      replace a with (out + (a - out)) by lia. exact (HB0 (a - out) ltac:(lia)).
  - split; [lia|]. split; [rewrite repeat_length; lia|].
    intros i Hi. rewrite repeat_length in Hi. rewrite nth_error_repeat by exact Hi.
    rewrite <- (fpj_mbyte_mrd tfibsegs _ (out + Z.of_nat i)). exact (HB0 (Z.of_nat i) ltac:(lia)). }
assert (HTXc : rd_text tfibsegs B ly S W (ms_mem ms) t0 len tcap).
{ pose proof HTX2 as (X1' & X2' & X3'). split; [exact X1'|]. split; [|exact X3'].
  exact (fs_rblock_below B ly S W _ _ mem2 (ms_mem ms) t0 tcap (proj1 HARU2) SB2 X2'). }
assert (HRESTc : ReaderRes.rest_at tb t0 t0 = [] ++ wt ++ (if pr then [10] else [])).
{ unfold ReaderRes.rest_at. replace (Z.to_nat (t0 - t0)) with 0%nat by (rewrite Z.sub_diag; reflexivity).
  rewrite skipn_O, Hzb, EWD. reflexivity. }
assert (HWIN : rd_win tfibsegs (ms_regs ms) ly W (ms_mem ms) (spZ regs - 48) (spZ regs - 16)).
{ split; [lia|]. split; [lia|]. split; [rewrite Zminus_mod, Hal16; reflexivity|]. split; [lia|].
  intros a Ha. pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpr2 & _).
  apply (fsw_apresent_unpoison B ly S U W (ms_mem ms) _ a HARU2); [unfold kHighMemBeg; lia|].
  apply Hpr2. lia. }
assert (HCHAIN : (spZ regs - 48) = spZ (ms_regs ms) /\
  (bad_next (spZ regs - 48) (ly_top ly) (s0Z (ms_regs ms)) = true \/ spZ regs - 48 + 40 <= s0Z (ms_regs ms)) \/
  spZ (ms_regs ms) + 16 <= spZ regs - 48 /\ s0Z (ms_regs ms) = spZ regs - 48 /\
  (exists chq, achain ly (aview tfibsegs (w_H W) (unpoison U (ms_mem ms))) (spZ (ms_regs ms)) (spZ regs - 48) chq /\
     Forall (fun r => bad_next (fst (fst r)) (ly_top ly) (snd r) = true \/ spZ regs - 48 + 40 <= snd r) chq)).
{ left. split; [lia|].
  assert (Hs0 : s0Z (ms_regs ms) = out)
    by (unfold s0Z; rewrite R8c, R8; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
  rewrite Hs0. destruct HOS as [HOS1|HOS1]; [left|right; lia].
  unfold bad_next. apply Bool.orb_true_intro. left. apply Bool.orb_true_intro. left.
  apply Z.leb_le. lia. }
(* ---- parse_value ---- *)
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) _ _ ms HS2 eq_refl). cbn [ss_pc].
eapply SRr_bind.
{ exact (PV ly S U W (ms_regs ms) (ms_mem ms) _ [] (spZ regs - 48) (spZ regs - 16) out t0 len t0 tb tcap t pr
    [] (if pr then [10] else []) live peak cnt fail ltac:(lia) HPREc HH
    ltac:(unfold FRL_parse_value, FRL_CRT_CALLEE in *; cbn [Z.of_nat]; lia)
    R10' R11' HPIN HWIN HCHAIN HTXc HRESTc ltac:(constructor) HDV HDS HWF
    ltac:(cbn [Nat.sub]; exact HDEP) HPOc HZEROc
    ltac:(change (2 - 0)%nat with 2%nat; destruct HOS as [HO|HO]; [left; lia | right; lia])
    ltac:(unfold HEAD; destruct HOT as [HO|HO]; [left; lia | right; lia])
    (fs_glob_below W mem2 (ms_mem ms) live peak cnt fail SB2 HGL2) HQ HSZ HLIVE HNEV HBB). }
intros W3 c3 Hwle3 (D & Da & HPerm & HPOST).
unfold fpostU in HPOST.
destruct HPOST as (ly3 & S3 & regs3 & mem3 & md3 & Ec3 & HJc & OK3 & PO3 & HP3 & H10f & HPIN3 & HWK3 & HBL3 &
  HTREE3 & HSUM3 & HLEN3 & HPO3 & HTX3 & peak3 & Hpeak3 & HGL3).
subst c3. rewrite R1.
pose proof HJc as (HAR3 & _).
assert (HARU3 : ARU tfibsegs B ly3 S3 (U ++ rd_heads Da) W3 mem3 md3)
  by (split; [exact HAR3 | split; [exact OK3 | exact PO3]]).
set (p' := t0 + (len - dd)).
(* ---- the facts the resume state and the tail read ---- *)
assert (Hp'b : t0 <= p' /\ p' + 1 <= t0 + tcap /\ 0 <= p' /\ p' + 8 <= 2 ^ 64) by (subst p'; lia).
assert (U32 : bv_unsigned (ew (Ereg regs3 (pjp_rxs p' (getr regs 1) (getr regs 8) (getr regs 9))) 32) = p').
{ change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. cbn [nth pjp_rxs]. apply wz. lia. }
assert (E33 : ew (Ereg regs3 (pjp_rxs p' (getr regs 1) (getr regs 8) (getr regs 9))) 33 = getr regs 1)
  by (change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E34 : ew (Ereg regs3 (pjp_rxs p' (getr regs 1) (getr regs 8) (getr regs 9))) 34 = getr regs 8)
  by (change 34%nat with (32 + 2)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E35 : ew (Ereg regs3 (pjp_rxs p' (getr regs 1) (getr regs 8) (getr regs 9))) 35 = getr regs 9)
  by (change 35%nat with (32 + 3)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (Esp3 : bv_unsigned (ew (Ereg regs3 (pjp_rxs p' (getr regs 1) (getr regs 8) (getr regs 9))) 2)
  = spZ regs - 48).
{ rewrite (ew_Ereg_nat regs3 _ 2 2%bv eq_refl).
  rewrite (fsw_pres (ms_regs ms) regs3 2%bv HP3 ltac:(unfold acallee_saved; vm_compute; lia)). exact Hspc. }
(* the saved s1 / s0 / ra at the call *)
assert (X2 : ew (Ereg regs2 (fs_extraT ++ pjp_xs t0 len (getr regs 9) (getr regs 8) (getr regs 1))) (xatom 2)
  = getr regs 9) by (unfold pjp_xs; rewrite fsw_ew_xatom; reflexivity).
assert (X3 : ew (Ereg regs2 (fs_extraT ++ pjp_xs t0 len (getr regs 9) (getr regs 8) (getr regs 1))) (xatom 3)
  = getr regs 8) by (unfold pjp_xs; rewrite fsw_ew_xatom; reflexivity).
assert (X4 : ew (Ereg regs2 (fs_extraT ++ pjp_xs t0 len (getr regs 9) (getr regs 8) (getr regs 1))) (xatom 4)
  = getr regs 1) by (unfold pjp_xs; rewrite fsw_ew_xatom; reflexivity).
assert (Vs1 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (spZ regs - 48 + 24) 8 (bv_unsigned (getr regs 9))).
{ eapply (fsw_field _ _ 2 (spZ regs - 48) _ _ _ _ _ 24 8%N (SOff (xatom 2) 0) (bv_unsigned (getr regs 9)));
  [exact HR2 | exact Usp2 | cbn; tauto | rewrite fsw_SOff0, X2; symmetry; apply Z_to_bv_bv_unsigned
  | pose proof (u64_range (getr regs 9)); replace (8 * Z.of_N 8) with 64 by reflexivity; lia
  | change (Z.of_N 8) with 8; lia]. }
assert (Vs0 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (spZ regs - 48 + 32) 8 (bv_unsigned (getr regs 8))).
{ eapply (fsw_field _ _ 2 (spZ regs - 48) _ _ _ _ _ 32 8%N (SOff (xatom 3) 0) (bv_unsigned (getr regs 8)));
  [exact HR2 | exact Usp2 | cbn; tauto | rewrite fsw_SOff0, X3; symmetry; apply Z_to_bv_bv_unsigned
  | pose proof (u64_range (getr regs 8)); replace (8 * Z.of_N 8) with 64 by reflexivity; lia
  | change (Z.of_N 8) with 8; lia]. }
assert (Vra : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (spZ regs - 48 + 40) 8 (bv_unsigned (getr regs 1))).
{ eapply (fsw_field _ _ 2 (spZ regs - 48) _ _ _ _ _ 40 8%N (SOff (xatom 4) 0) (bv_unsigned (getr regs 1)));
  [exact HR2 | exact Usp2 | cbn; tauto | rewrite fsw_SOff0, X4; symmetry; apply Z_to_bv_bv_unsigned
  | pose proof (u64_range (getr regs 1)); replace (8 * Z.of_N 8) with 64 by reflexivity; lia
  | change (Z.of_N 8) with 8; lia]. }
(* the bytes at or above the callee's window top are kept by its journal's frames clause *)
assert (KEEPHI : forall a, spZ regs - 16 <= a < spZ regs ->
  mbyte tfibsegs (mrestrict (w_H W3) mem3) a = mbyte tfibsegs (mrestrict (w_H W) (ms_mem ms)) a).
{ intros a Ha. pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
  apply (mbyte_of_aview tfibsegs).
  rewrite <- (fsw_aview_unpoison_high B ly3 S3 (U ++ rd_heads Da) W3 mem3 md3 a HARU3
    ltac:(unfold kHighMemBeg; lia)).
  rewrite <- (fsw_aview_unpoison_high B ly S U W (ms_mem ms) _ a HARU2 ltac:(unfold kHighMemBeg; lia)).
  apply F1; [lia | intros Hx; lia]. }
(* the live user-poisoned heads after the call: the old ones, and one per new reader block *)
assert (HH3 : FSupoisonU.fs_heads B ly3 S3 (U ++ rd_heads Da)).
{ intros r Hr. apply in_app_or in Hr. destruct Hr as [Hr|Hr].
  - destruct (HH r Hr) as (E16 & m & Hm & M16). split; [exact E16|]. exists m. split; [|exact M16].
    apply (Permutation_in _ (Permutation_sym HBL3)). apply in_or_app. left. exact Hm.
  - unfold rd_heads in Hr. apply in_map_iff in Hr. destruct Hr as (bb & <- & Hin).
    destruct bb as (a & k). cbn [fst snd].
    destruct (proj1 (proj2 HTREE3) a k (Permutation_in _ HPerm Hin)) as (Hin3 & _ & Hk & _).
    split; [reflexivity|]. exists (k + HEAD). split; [exact Hin3|].
    unfold req_size, HEAD in *. destruct (Z.eqb_spec (k + 16) 0); lia. }
(* the text block is off the callee's footprint, so its bytes are kept across the call *)
assert (HTXOFF : forall a, t0 - HEAD <= a < t0 + tcap -> ~ inFP ([(out, out + 56)] ++ FS_PSTAT_FP) a).
{ intros a Ha (r & Hin & Hr). cbn [app In] in Hin. pose proof HTX as (_ & (Hinb & _ & _ & _) & _).
  assert (Hrq : req_size (tcap + HEAD) = tcap + HEAD)
    by (unfold req_size, HEAD in *; destruct (Z.eqb_spec (tcap + 16) 0); lia).
  destruct Hin as [<-|Hr'].
  - cbn [fst snd] in Hr. unfold HEAD in *. lia.
  - apply (blk_img tfibsegs B LAWS ly S W (unpoison U mem) md (t0 - HEAD) (tcap + HEAD) a HAR Hinb
      ltac:(unfold HEAD in *; lia)).
    unfold FS_PSTAT_FP in Hr'. destruct Hr' as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hr;
      apply pjp_rw_img; lia. }
assert (KEEPTX : forall a, t0 - HEAD <= a < t0 + tcap ->
  mbyte tfibsegs (mrestrict (w_H W3) mem3) a = mbyte tfibsegs (mrestrict (w_H W) (ms_mem ms)) a).
{ intros a Ha. pose proof HTX as (_ & (Hinb & _ & _ & _) & _).
  assert (Hrq : req_size (tcap + HEAD) = tcap + HEAD)
    by (unfold req_size, HEAD in *; destruct (Z.eqb_spec (tcap + 16) 0); lia).
  pose proof (fsw_journal_kept_byte B (STK_parse_value (2 - 0) + (spZ regs - 16 - spZ (ms_regs ms)))
    (spZ regs - 16) ([(out, out + 56)] ++ FS_PSTAT_FP) ly S U W (ms_mem ms) _ ly3 S3 (U ++ rd_heads Da) W3 mem3 md3
    (rd_ev (PjRoundTrip.ttrace t)) a HJc HARU2 OK3 PO3
    ltac:(left; exists (t0 - HEAD), (tcap + HEAD); split; [exact Hinb | unfold HEAD in *; lia])
    (HTXOFF a Ha)) as (_ & Eb). unfold mbyte. rewrite Eb. reflexivity. }
assert (HZB3 : zbytes_at tfibsegs W3 mem3 t0 (WriterValue.wdoc t pr ++ [0])).
{ apply (garr8_frame tfibsegs _ _ t0 _ HZBc). intros a Ha. rewrite Hlen1 in Ha.
  apply KEEPTX. unfold HEAD in *. lia. }
(* in->p after the call, and in->end *)
assert (Hpp : t0 + Z.of_nat (length (@nil Z))
  + Z.of_nat (length (concat (WriterValue.wvpieces t pr (Z.of_nat 0)))) = p').
{ change (concat (WriterValue.wvpieces t pr (Z.of_nat 0))) with wt. rewrite ELEN. cbn [length Z.of_nat].
  subst p'. lia. }
rewrite Hpp in HPIN3.
pose proof HPIN3 as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12).
assert (Vp3 : val_mem tfibsegs (mrestrict (w_H W3) mem3) (spZ regs - 48 + 0) 8 p').
{ rewrite Z.add_0_r. apply fsw_pj_u64_val. split; [lia | exact Q1]. }
assert (Vend3 : val_mem tfibsegs (mrestrict (w_H W3) mem3) (spZ regs - 48 + 8) 8 (t0 + len)).
{ apply fsw_pj_u64_val. split; [lia | exact Q2]. }
(* ---- the resume state at 0x82ef8 ---- *)
destruct (fsw_after_callFPU_ot B STK_pj_parse (spZ regs) ([(out, out + 56)] ++ FS_PSTAT_FP) [] ly S U W mem md W
  ly S U (ms_mem ms) _ 0 (STK_parse_value 2) ([(out, out + 56)] ++ FS_PSTAT_FP) (spZ regs - 16) 48 (ms_regs ms)
  ly3 S3 (U ++ rd_heads Da) W3 regs3 mem3 md3 (rd_ev (PjRoundTrip.ttrace t))
  (pjp_rxs p' (getr regs 1) (getr regs 8) (getr regs 9)) (pjp_rcs dd) 0x82ef8 HJ2 HARU2)
  as (HJ3 & HARU3' & HS3).
- (* the callee journal, at the raised window top *)
  cbn [Nat.sub] in HJc. exact HJc.
- (* fsw_fp_sub: out lies in a live block or a live fake frame, the statics are image bytes of the caller's FP *)
  intros x Hx. destruct Hx as (r & Hin & Hxr). cbn [app In] in Hin.
  destruct Hin as [<-|Hr].
  + cbn [fst snd] in Hxr.
    pose proof HPO as HPOi.
    destruct HPOi as [[((cid & pos & Hin & _ & _ & F1 & F2) & _ & _)|((b & n & Hin & Bb1 & Bb2) & _ & _)] _].
    * right. right. right. right.
      split; [exists (out, out + 56); split; [left; reflexivity | cbn [fst snd]; lia]|].
      exists cid, pos. split; [exact Hin | unfold in_zr, frame_rng; cbn [fst snd]; lia].
    * left. split; [exists (out, out + 56); split; [left; reflexivity | cbn [fst snd]; lia]|].
      exists b, n. split; [exact Hin | unfold HEAD in *; lia].
  + right. right. left. split; [exists r; split; [right; exact Hr | exact Hxr]|].
    unfold FS_PSTAT_FP in Hr. destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hxr;
      apply pjp_rw_img; lia.
- exact OK3.
- exact PO3.
- exact HP3.
- exact Hspc.
- lia.
- vm_compute; intros Hc; discriminate Hc.
- rewrite FSP, FPV. lia.
- reflexivity.
- lia.
- lia.
- vm_compute; reflexivity.
- (* the five frame words, read on the memory AFTER the call *)
  unfold pjp_rcs. repeat apply Forall_cons; try apply Forall_nil.
  + apply (chunk_ok_val tfibsegs _ _ _ 0 8%N (SOff 32 0) p');
      [rewrite fsw_SOff0; apply bv_eq; rewrite U32; symmetry; apply wz; lia
      | lia | cbn; lia | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; exact Vp3].
  + apply (chunk_ok_val tfibsegs _ _ _ 8 8%N (SOff 32 dd) (t0 + len));
      [apply bv_eq; rewrite denot_SOff, U32; rewrite (wz (t0 + len) ltac:(lia));
       replace (p' + dd) with (t0 + len) by (subst p'; lia); apply zcanon_id; unfold M64; lia
      | lia | cbn; lia | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; exact Vend3].
  + apply (chunk_ok_val tfibsegs _ _ _ 24 8%N (SOff 35 0) (bv_unsigned (getr regs 9)));
      [rewrite fsw_SOff0, E35; symmetry; apply Z_to_bv_bv_unsigned | apply u64_range | cbn; lia
      | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; intros k Hk;
        rewrite (proj1 (HWK3 (spZ regs - 48 + 24 + Z.of_nat k) ltac:(rewrite Hspc; cbn in Hk; lia)
          ltac:(cbn in Hk; lia)));
        exact (Vs1 k Hk)].
  + apply (chunk_ok_val tfibsegs _ _ _ 32 8%N (SOff 34 0) (bv_unsigned (getr regs 8)));
      [rewrite fsw_SOff0, E34; symmetry; apply Z_to_bv_bv_unsigned | apply u64_range | cbn; lia
      | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; intros k Hk;
        rewrite (KEEPHI (spZ regs - 48 + 32 + Z.of_nat k) ltac:(cbn in Hk; lia)); exact (Vs0 k Hk)].
  + apply (chunk_ok_val tfibsegs _ _ _ 40 8%N (SOff 33 0) (bv_unsigned (getr regs 1)));
      [rewrite fsw_SOff0, E33; symmetry; apply Z_to_bv_bv_unsigned | apply u64_range | cbn; lia
      | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; intros k Hk;
        rewrite (KEEPHI (spZ regs - 48 + 40 + Z.of_nat k) ltac:(cbn in Hk; lia)); exact (Vra k Hk)].
- (* ---- the tail: 0x82ef8 .. 0x82f90 ---- *)
  rewrite Z.add_0_l in HJ3.
  (* the callee-saved registers the tail must give back *)
  assert (RKEEP : forall r : bv 5, acallee_saved (bv_unsigned r) -> bv_unsigned r <> 2 -> bv_unsigned r <> 8 ->
    bv_unsigned r <> 9 -> getr regs3 r = getr regs r).
  { intros r Hr Hn2 Hn8 Hn9. rewrite (fsw_pres (ms_regs ms) regs3 r HP3 Hr).
    rewrite <- (RCS r Hr Hn2 Hn8 Hn9). revert r Hr Hn2 Hn8 Hn9.
    apply pjp_cs_other;
      [ exact (fsw_reg_atom _ regs2 _ _ ms 3%bv 3%bv 3 HS2 ltac:(vm_compute; reflexivity) eq_refl)
      | exact (fsw_reg_atom _ regs2 _ _ ms 4%bv 4%bv 4 HS2 ltac:(vm_compute; reflexivity) eq_refl)
      | exact (fsw_reg_atom _ regs2 _ _ ms 18%bv 18%bv 18 HS2 ltac:(vm_compute; reflexivity) eq_refl)
      | exact (fsw_reg_atom _ regs2 _ _ ms 19%bv 19%bv 19 HS2 ltac:(vm_compute; reflexivity) eq_refl)
      | exact (fsw_reg_atom _ regs2 _ _ ms 20%bv 20%bv 20 HS2 ltac:(vm_compute; reflexivity) eq_refl)
      | exact (fsw_reg_atom _ regs2 _ _ ms 21%bv 21%bv 21 HS2 ltac:(vm_compute; reflexivity) eq_refl)
      | exact (fsw_reg_atom _ regs2 _ _ ms 22%bv 22%bv 22 HS2 ltac:(vm_compute; reflexivity) eq_refl)
      | exact (fsw_reg_atom _ regs2 _ _ ms 23%bv 23%bv 23 HS2 ltac:(vm_compute; reflexivity) eq_refl)
      | exact (fsw_reg_atom _ regs2 _ _ ms 24%bv 24%bv 24 HS2 ltac:(vm_compute; reflexivity) eq_refl)
      | exact (fsw_reg_atom _ regs2 _ _ ms 25%bv 25%bv 25 HS2 ltac:(vm_compute; reflexivity) eq_refl)
      | exact (fsw_reg_atom _ regs2 _ _ ms 26%bv 26%bv 26 HS2 ltac:(vm_compute; reflexivity) eq_refl)
      | exact (fsw_reg_atom _ regs2 _ _ ms 27%bv 27%bv 27 HS2 ltac:(vm_compute; reflexivity) eq_refl) ]. }
  assert (RK2 : forall (q : bv 5) (n : nat), Z.of_nat n = bv_unsigned q -> acallee_saved (bv_unsigned q) ->
    bv_unsigned q <> 2 -> bv_unsigned q <> 8 -> bv_unsigned q <> 9 ->
    sv_denot (Ereg regs3 (pjp_rxs p' (getr regs 1) (getr regs 8) (getr regs 9))) (SOff n 0) = getr regs q).
  { intros q n Hn Hq Hn2 Hn8 Hn9. rewrite fsw_SOff0, (ew_Ereg_nat regs3 _ n q Hn).
    exact (RKEEP q Hq Hn2 Hn8 Hn9). }
  (* a0 = 0 (parse_value's success post): pin it, so `bnez a0` at 0x82ef8 is decided *)
  assert (HS4 : st_ok tfibsegs (Ereg regs3 (pjp_rxs p' (getr regs 1) (getr regs 8) (getr regs 9)))
    (mkSS (ss_pc (fss_ret 0x82ef8 48 (pjp_rcs dd)))
       (sr_set (ss_regs (fss_ret 0x82ef8 48 (pjp_rcs dd))) 10%bv (SLit 0))
       (ss_mem (fss_ret 0x82ef8 48 (pjp_rcs dd))) (ss_resv (fss_ret 0x82ef8 48 (pjp_rcs dd)))
       (ss_facts (fss_ret 0x82ef8 48 (pjp_rcs dd))))
    (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 0x82ef8) mem3 (seg_rom tfibsegs)))).
  { apply (st_ok_regs tfibsegs _ _ _ _ HS3). intros qr. destruct (decide (qr = 10%bv)) as [->|Hq10].
    2: { rewrite sr_get_set_other by exact Hq10. reflexivity. }
    rewrite sr_get_set_same by reflexivity.
    change (sr_get (ss_regs (fss_ret 0x82ef8 48 (pjp_rcs dd))) 10%bv) with (SOff 10 0).
    rewrite fsw_SOff0, (ew_Ereg_nat regs3 _ 10 10%bv eq_refl), H10f. reflexivity. }
  (* the atom facts the tail's branches and the token run read *)
  pose proof (st_ok_add_fact tfibsegs _ _ _ 32%nat (mkAF 4096 PJP_CEIL 0) HS4
    ltac:(unfold afact_ok, PJP_CEIL; cbn [af_lo af_hi af_al2]; rewrite U32; rewrite Z.pow_0_r;
          split; [lia | split; [apply Z.mod_1_r | lia]])) as HS5.
  pose proof (st_ok_add_fact tfibsegs _ _ _ 9%nat (mkAF SHADOW_OFF SHADOW_OFF 0) HS5
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2];
          rewrite (ew_Ereg_nat regs3 _ 9 9%bv eq_refl),
            (fsw_pres (ms_regs ms) regs3 9%bv HP3 ltac:(unfold acallee_saved; vm_compute; lia)),
            (fsw_reg_atom _ regs2 _ _ ms 9%bv 9%bv 9 HS2 ltac:(vm_compute; reflexivity) eq_refl), R9,
            (wz SHADOW_OFF ltac:(unfold SHADOW_OFF; lia));
          rewrite Z.pow_0_r; split; [lia | split; [apply Z.mod_1_r | lia]])) as HS6.
  clear HS3 HS4 HS5.
  destruct pr; cbn in Edd; subst dd.
  + (* ---- a pretty document: one white-space iteration over the trailing newline at in->p ---- *)
    (* the newline byte at in->p, as a read-only region at atom 32 *)
    assert (HNL : mbyte tfibsegs (mrestrict (w_H W3) mem3) p' = Some (Z_to_bv 8 10)).
    { assert (Hi : (Z.to_nat (p' - t0) < length tb)%nat)
        by (apply Nat2Z.inj_lt; rewrite Z2Nat.id by lia; rewrite Hlentb; subst p'; lia).
      pose proof (proj2 (proj2 Q10) (Z.to_nat (p' - t0)) Hi) as Hb.
      rewrite Z2Nat.id in Hb by lia. replace (t0 + (p' - t0)) with p' in Hb by lia.
      change (lib.Lib.Mem.mrd tfibsegs (mrestrict (w_H W3) mem3) (lib.Lib.Mem.wa p') = Some (Z_to_bv 8 10)).
      rewrite Hb.
      assert (Hlw : length wt = Z.to_nat (p' - t0))
        by (apply Nat2Z.inj; rewrite ELEN, Z2Nat.id by lia; subst p'; lia).
      subst tb. rewrite nth_error_map, EWD, <- Hlw, nth_error_app2 by lia. rewrite Nat.sub_diag.
      reflexivity. }
    assert (RNL : region_ok tfibsegs (Ereg regs3 (pjp_rxs p' (getr regs 1) (getr regs 8) (getr regs 9)))
      (mrestrict (w_H W3) mem3) pjp_nl_region).
    { unfold pjp_nl_region, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U32. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val tfibsegs _ _ _ 0 1%N (SLit 10) 10);
        [reflexivity | cbn; lia | cbn; lia
        | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; intros k Hk; rewrite Z.add_0_r;
          replace (p' + Z.of_nat k) with p' by (cbn in Hk; lia); rewrite HNL; f_equal; f_equal;
          cbn in Hk; assert (k = 0)%nat by lia; subst k; reflexivity]. }
    pose proof (st_ok_add_region' tfibsegs _ _ _ pjp_nl_region HS6 ltac:(vm_compute; reflexivity) RNL
      ltac:(cbn [ss_mem add_atom fss_ret all_disjoint]; split; [|exact I];
            unfold extent_disjoint, pjp_nl_region, fstk_ret;
            cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite U32, Esp3; left; lia)) as HS7.
    clear HS6.
    (* the shadow entry: the byte at in->p is in the text block's body *)
    assert (RAp : range_addressable (aview tfibsegs (w_H W3) mem3) SHADOW_OFF p' 1).
    { pose proof HTX3 as (_ & (Hin3 & _ & _ & _) & _).
      assert (Hrq : req_size (tcap + HEAD) = tcap + HEAD)
        by (unfold req_size, HEAD in *; destruct (Z.eqb_spec (tcap + 16) 0); lia).
      exact (fsw_block_body_addressable B ly3 S3 (U ++ rd_heads Da) W3 mem3 md3 (t0 - HEAD) (tcap + HEAD) p' 1
        HARU3 HH3 Hin3 ltac:(unfold HEAD in *; lia) ltac:(lia) ltac:(unfold HEAD in *; lia)). }
    assert (SHOK : sh_ok tfibsegs (SOff 9 0) pjp_SH
      (Ereg regs3 (pjp_rxs p' (getr regs 1) (getr regs 8) (getr regs 9))) (mrestrict (w_H W3) mem3)).
    { unfold sh_ok, pjp_SH. constructor; [|constructor].
      apply (shent_ok_of_range tfibsegs (w_H W3) mem3 _ (SOff 9 0) 32 p' 1 p' 0 1 RAp).
      - apply U_atom; [rewrite (ew_Ereg_nat regs3 _ 9 9%bv eq_refl),
          (fsw_pres (ms_regs ms) regs3 9%bv HP3 ltac:(unfold acallee_saved; vm_compute; lia)),
          (fsw_reg_atom _ regs2 _ _ ms 9%bv 9%bv 9 HS2 ltac:(vm_compute; reflexivity) eq_refl), R9; reflexivity
        | unfold SHADOW_OFF; lia].
      - apply U_atom; [apply bv_eq; rewrite U32; symmetry; apply wz; lia | lia].
      - lia.
      - lia.
      - intros x Hx. cbn [Z.min Z.max] in Hx.
        pose proof HTX3 as (_ & (Hin3 & _ & _ & _) & _).
        assert (Hrq : req_size (tcap + HEAD) = tcap + HEAD)
          by (unfold req_size, HEAD in *; destruct (Z.eqb_spec (tcap + 16) 0); lia).
        destruct (al_blocks tfibsegs B LAWS ly3 S3 W3 (unpoison (U ++ rd_heads Da) mem3) md3
          (t0 - HEAD) (tcap + HEAD) (proj1 HARU3) Hin3) as (_ & _ & _ & Happ & _).
        pose proof (in_app_addr _ _ x Happ ltac:(unfold HEAD in *; lia)) as Hax.
        unfold app_addr, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia. }
    fsw_aj_run_tokU pj_parse_tbl_ok HS7 HJ3 HARU3' SHOK fs_Bspan.
    { cbn [ss_mem add_atom fss_ret].
      apply awr_ok_cons_ro; [cbn; lia|].
      eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -48);
        [reflexivity | rewrite Esp3; lia | cbn; lia | cbn; lia | apply awr_ok_nil]. }
    assert (SB : same_below mem3 (ms_mem ms0) alloc_ceiling).
    { lazymatch goal with HFx : frame_of _ _ mem3 (ms_mem ms0) |- _ =>
        apply (same_below_frameN _ _ mem3 (ms_mem ms0) alloc_ceiling HFx) end; [|lia].
      intros a (r & Hin & Ha). cbn [ss_mem add_atom fss_ret In] in Hin.
      destruct Hin as [<-|[<-|[]]];
        cbn [pjp_nl_region fstk_ret YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; [lia|].
      rewrite Esp3 in Ha. lia. }
    (* the token run's two fresh atoms (36, 37) leave every atom the return reads unchanged *)
    assert (DEN : forall n z, n <> 36%nat -> n <> 37%nat ->
      sv_denot (ewset (ewset (Ereg regs3 (pjp_rxs p' (getr regs 1) (getr regs 8) (getr regs 9))) 36 w) 37 w0)
        (SOff n z) = sv_denot (Ereg regs3 (pjp_rxs p' (getr regs 1) (getr regs 8) (getr regs 9))) (SOff n z)).
    { intros n z Hn1 Hn2. apply bv_eq. rewrite !denot_SOff. rewrite !ew_ewset_other by assumption. reflexivity. }
    pose proof (st_ok_restrict_reg tfibsegs _ _ _ ms0 1%bv HS7) as R1F.
    lazymatch type of R1F with _ = sv_denot _ ?X => replace X with (SOff 33 0) in R1F by (vm_compute; reflexivity) end.
    rewrite DEN, fsw_SOff0, E33 in R1F by lia.
    eapply SRr_mono; [|intros W' c' _ Hp; exists D, Da; split; [exact HPerm | exact Hp]].
      eapply (fsw_retU B pj_parse_tbl pj_parse_tbl_ok W3 _ _ ms0 _ STK_pj_parse (spZ regs)
        ([(out, out + 56)] ++ FS_PSTAT_FP) regs ly S U W mem md ly3 S3 (U ++ rd_heads Da)
        (rd_ev (PjRoundTrip.ttrace t))).
      { exact HS7. }
      { reflexivity. }
      { vm_compute. reflexivity. }
      { rewrite R1F. exact Hra. }
      { exact HJ3. }
      { exact HARU3'. }
      { apply (fsw_preserved _ _ _ ms0 regs pjp_expect HS7); [vm_compute; reflexivity|].
        intros r Hr. cbv [CALLEE_SAVED In] in Hr. repeat (destruct Hr as [<-|Hr]); [..|destruct Hr].
        all: lazymatch goal with |- sv_denot _ (pjp_expect ?q) = _ =>
               let e := eval vm_compute in (pjp_expect q) in change (pjp_expect q) with e end.
        all: rewrite DEN by lia.
        all: first [ eapply fsw_sp_back; exact Esp3 | rewrite fsw_SOff0; exact E34
                   | rewrite fsw_SOff0; exact E35 | apply RK2; pjp_lit_tac ]. }
      intros matf. cbv beta.
      split; [exact (fsw_reg_lit _ _ _ ms0 10%bv 0 HS7 ltac:(vm_compute; reflexivity) ltac:(lia))|].
      split; [exact HBL3|].
      split; [exact (rnode_below B ly3 S3 W3 (unpoison (U ++ rd_heads Da) mem3) md3 mem3 (ms_mem ms0) D out t D
        HAR3 SB ltac:(lia) ltac:(lia) HTREE3)|].
      split; [exact HSUM3|]. split; [exact HLEN3|].
      split; [exact (pobj_below B ly3 S3 W3 (unpoison (U ++ rd_heads Da) mem3) md3 mem3 (ms_mem ms0) out
        HAR3 SB HPO3)|].
      split.
      { pose proof HTX3 as (Y1 & Y2 & Y3). split; [exact Y1|]. split; [|exact Y3].
        exact (fs_rblock_below B ly3 S3 W3 (unpoison (U ++ rd_heads Da) mem3) md3 mem3 (ms_mem ms0) t0 tcap
          HAR3 SB Y2). }
      split.
      { apply (garr8_frame tfibsegs _ _ t0 _ HZB3). intros a Ha. rewrite Hlen1 in Ha.
        exact (mbyte_below (w_H W3) mem3 (ms_mem ms0) alloc_ceiling a SB ltac:(lia)). }
      exists peak3. split; [exact Hpeak3|].
      exact (fs_glob_below W3 mem3 (ms_mem ms0) _ _ _ _ SB HGL3).
  + (* ---- a compact document: in->p is already in->end, the loop is not entered ---- *)
    fsw_aj_runU pj_parse_tbl_ok HS6 HJ3 HARU3'.
    { cbn [ss_mem add_atom fss_ret].
      eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -48);
        [reflexivity | rewrite Esp3; lia | cbn; lia | cbn; lia | apply awr_ok_nil]. }
    assert (SB : same_below mem3 (ms_mem ms0) alloc_ceiling).
    { lazymatch goal with HFx : frame_of _ _ mem3 (ms_mem ms0) |- _ =>
        apply (same_below_frameN _ _ mem3 (ms_mem ms0) alloc_ceiling HFx) end; [|lia].
      intros a (r & Hin & Ha). cbn [ss_mem add_atom fss_ret In] in Hin.
      destruct Hin as [<-|[]]. cbn [fstk_ret YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
      rewrite Esp3 in Ha. lia. }
    pose proof (fsw_reg_extra _ regs3 _ _ ms0 1%bv 1 HS6 ltac:(vm_compute; reflexivity)) as R1F.
    cbn [nth pjp_rxs] in R1F.
    eapply SRr_mono; [|intros W' c' _ Hp; exists D, Da; split; [exact HPerm | exact Hp]].
      eapply (fsw_retU B pj_parse_tbl pj_parse_tbl_ok W3 _ _ ms0 _ STK_pj_parse (spZ regs)
        ([(out, out + 56)] ++ FS_PSTAT_FP) regs ly S U W mem md ly3 S3 (U ++ rd_heads Da)
        (rd_ev (PjRoundTrip.ttrace t))).
      { exact HS6. }
      { reflexivity. }
      { vm_compute. reflexivity. }
      { rewrite R1F. exact Hra. }
      { exact HJ3. }
      { exact HARU3'. }
      { apply (fsw_preserved _ _ _ ms0 regs pjp_expect HS6); [vm_compute; reflexivity|].
        intros r Hr. cbv [CALLEE_SAVED In] in Hr. repeat (destruct Hr as [<-|Hr]); [..|destruct Hr].
        all: lazymatch goal with |- sv_denot _ (pjp_expect ?q) = _ =>
               let e := eval vm_compute in (pjp_expect q) in change (pjp_expect q) with e end.
        all: first [ eapply fsw_sp_back; exact Esp3 | rewrite fsw_SOff0; exact E34
                   | rewrite fsw_SOff0; exact E35 | apply RK2; pjp_lit_tac ]. }
      intros matf. cbv beta.
      split; [exact (fsw_reg_lit _ _ _ ms0 10%bv 0 HS6 ltac:(vm_compute; reflexivity) ltac:(lia))|].
      split; [exact HBL3|].
      split; [exact (rnode_below B ly3 S3 W3 (unpoison (U ++ rd_heads Da) mem3) md3 mem3 (ms_mem ms0) D out t D
        HAR3 SB ltac:(lia) ltac:(lia) HTREE3)|].
      split; [exact HSUM3|]. split; [exact HLEN3|].
      split; [exact (pobj_below B ly3 S3 W3 (unpoison (U ++ rd_heads Da) mem3) md3 mem3 (ms_mem ms0) out
        HAR3 SB HPO3)|].
      split.
      { pose proof HTX3 as (Y1 & Y2 & Y3). split; [exact Y1|]. split; [|exact Y3].
        exact (fs_rblock_below B ly3 S3 W3 (unpoison (U ++ rd_heads Da) mem3) md3 mem3 (ms_mem ms0) t0 tcap
          HAR3 SB Y2). }
      split.
      { apply (garr8_frame tfibsegs _ _ t0 _ HZB3). intros a Ha. rewrite Hlen1 in Ha.
        exact (mbyte_below (w_H W3) mem3 (ms_mem ms0) alloc_ceiling a SB ltac:(lia)). }
      exists peak3. split; [exact Hpeak3|].
      exact (fs_glob_below W3 mem3 (ms_mem ms0) _ _ _ _ SB HGL3).
Qed.

End W.
