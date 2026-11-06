(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ARM_gone of the ASan walk of fuzz_reply's LLVMFuzzerTestOneInput, PHASE 1
   (lib/A/W_LLVMFuzzerTestOneInput_gone.v's GP1): the join 0x846f0 to the reads[] loop's head 0x84738
   (fuzz_reply.asan 0x846f0-0x84734, fuzz_reply.c:635-639).  The six shadow bytes of `char prefix[48]` (the fake
   frame's +32) go from 0xf8 to 0 and `size_t at = 0` is stored at F+208 (one plain run: it writes the fake frame's
   shadow, which the token run refuses); then `snprintf(prefix, 48, "%s %d ", PHD_EVENT_PARAM_GESTURE, id)`
   (W_sites.v asnprintf_realizes, lifted into the arm's journal by W_sites.v aj_gx_entry_at); then
   `li a2,0; li t0,4; addi t1,s1,192`.  The stack premise of the call is discharged here: aj_gx_entry_at checks
   3 * ESTACK - (F - sp0) <= LLVMF_STK (12,288 + at most 352 <= 32,768) and hands back the scratch's presence from
   the journal (ascratch_ok), which ecall_pre_stk_of turns into the contract's ecall_pre_stk. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_LLVMFuzzerTestOneInput_gone_p1.v, with its module paths and module names changed; 469 of its 539 lines of code are new or changed and 754 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A (fuzz_link.asan, the PUBLISHED pin, sha256 059dae63e07c...; listing
   (internal path) (internal record, sha256 e84d6f0c6974)): the call of
   wrapper_snprintf (0x43088) as one step of the walk's journal, at the two sites of the call:
     0x82b14 (+0x340, return cut LF_sn_ra): snprintf(g_names + 8 k, 8, .str 0x20fa0 "nl%d", k), k = 0 .. 63;
     0x839c4 (+0x11f0): snprintf(m + MD_MARK + 16 n, 16, .str.21 0x21240 "%s", name).
   The contract is lib/A/Rt/LinkSnpDef.v `asnprintf_link_realizes`, taken
   as the Section hypothesis SNP in its exact shape; its journal lift is lib/A/Rt/LinkSnpJ.v `link_snprintf_journal`.

   - lf_snp_pre: the contract's own premise bundle `asnprintf_link_fpre` at FF_link and LINK_SNP_STK, from the
     journal, arodata_okP, the three argument registers, the format's address (one of the two literals,
     `lf_snp_fmt`), the varargs' facts and the destination's facts (`lf_snp_dest`). The rest is computed: the
     stack-guard .got word (AR's const cell 0xa2658 -> 0x651c50), the guard's eight bytes (image bytes, so readable
     at every memory), the format's bytes (arodata_okP over the read-only segment) and its shadow (AR's zero rows
     and constant shadow cells), by lib/A/Prog/LLVMFuzzerTestOneInputKpre.v's image checkers.
   - lf_snp_stepF / lf_snp_step: the contract lifted onto ajournal_gx at the call. The post is link_amem.v's
     `apostF` at K = LINK_SNP_STK, EV = 0, E = the written bytes, with Q = `lf_snp_Q` (the layout, the allocator
     state and the world of the call, the model materialised, a0 = |T|, the bytes sn_bytes (n - 1) T at d, every
     byte outside the written bytes and the window kept, presence kept but at in-image written bytes);
     lf_snp_step hands the continuation in link_amem.v's `apostF_continue` shape.
   - lf_snp_at: the g_names site, with the text `lf_gname_z k` (LLVMFuzzerTestOneInputSu.v's format chain:
     lf_fmt_parse, lf_pf_text, lf_sn_bytes) and the post at the bytes `lf_gname_z k ++ [0]`.
   - the helpers of the second site: lf_snp_arg_int / lf_snp_arg_str (the varargs), lf_snp_dest_gnames /
     lf_snp_dest_heap / lf_hull_of_ra (the destination).

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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m AF0x.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalk LinkWalkSide LinkWalkZsh BoxBase.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkEntry LinkEntryA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Rt Require Import PfFacts SnShared SnFF.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMfDefs LinkPfPiece LinkSnpDef LinkSnpJ.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputSu.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputKpre.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ==========================================================================
   1. The two format literals, and the image facts the call reads, by computation
   ========================================================================== *)

(* "%s" at .str.21 0x21240 (the op_mark site); "nl%d" at .str 0x20fa0 is LLVMFuzzerTestOneInputSu.v's LF_FMT *)
Definition LF_FMT_S : list Z := [37; 115].

(* the format of a call site of this function, with its parsed pieces *)
Definition lf_snp_fmt (f : Z) (fmt : list Z) (ps : list pf_piece) : Prop :=
  (f = LA_STR /\ fmt = LF_FMT /\ ps = [PLit 110; PLit 108; Pd]) \/
  (f = LA_STR21 /\ fmt = LF_FMT_S /\ ps = [Ps]).

Lemma lf_fmt_nl_bytes : kp_bytes_b tfibsegs Tfib_owned_static TFIB_ERRNO LA_STR (LF_FMT ++ [0]) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma lf_fmt_s_bytes : kp_bytes_b tfibsegs Tfib_owned_static TFIB_ERRNO LA_STR21 (LF_FMT_S ++ [0]) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma lf_fmt_nl_ra : kp_ra_b LA_STR 5 = true. Proof. vm_compute. reflexivity. Qed.
Lemma lf_fmt_nl_hull : kp_hull_b LA_STR 5 = true. Proof. vm_compute. reflexivity. Qed.
Lemma lf_fmt_s_ra : kp_ra_b LA_STR21 3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma lf_fmt_s_hull : kp_hull_b LA_STR21 3 = true. Proof. vm_compute. reflexivity. Qed.
(* the guard __stack_chk_guard 0x651c50: eight image bytes (.bss), so readable at every memory *)
Lemma lf_guard_img : kp_somes_b tfibsegs LA_GUARD 8 = true. Proof. vm_compute. reflexivity. Qed.
Lemma lf_fmt_s_parse : pf_parse LF_FMT_S = Some [Ps]. Proof. vm_compute. reflexivity. Qed.

(* ==========================================================================
   2. Byte facts
   ========================================================================== *)

Lemma lf_aview_of_mbyte : forall segs H (mem : word -> option byte) a v, 0 <= v < 256 ->
  mbyte segs (mrestrict H mem) a = Some (Z_to_bv 8 v) -> aview segs H mem a = Some v.
Proof.
  intros segs H mem a v Hv E. unfold aview. rewrite E. cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. exact Hv.
Qed.

(* the bytes l at f that kp_bytes_b checks, as the walk's view reads them *)
Lemma lf_lit_rd : forall segs B H (mem : word -> option byte) f l,
  as_owned_static B = Tfib_owned_static -> as_errno B = TFIB_ERRNO ->
  arodata_okP segs PCAP_RLO PCAP_RHI B (aview segs H mem) ->
  kp_bytes_b segs Tfib_owned_static TFIB_ERRNO f l = true -> Forall (fun z => 0 <= z < 256) l ->
  forall i, 0 <= i < Z.of_nat (length l) -> aview segs H mem (f + i) = Some (nth (Z.to_nat i) l 0).
Proof.
  intros segs B H mem f l Ho He HR Hb Hl i Hi.
  pose proof (kp_bytes_mbyte segs Tfib_owned_static TFIB_ERRNO B H mem f l Ho He HR Hb (Z.to_nat i) ltac:(lia))
    as E.
  rewrite Z2Nat.id in E by lia.
  apply lf_aview_of_mbyte; [|exact E].
  rewrite Forall_forall in Hl. apply Hl. apply nth_In. lia.
Qed.

Lemma lf_rdword_some : forall (rd : reader) a, (forall i, 0 <= i < 8 -> rd (a + i) <> None) ->
  exists v, rdword rd a = Some v.
Proof.
  intros rd a H. unfold rdword.
  pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
  pose proof (H 1 ltac:(lia)) as H1. pose proof (H 2 ltac:(lia)) as H2. pose proof (H 3 ltac:(lia)) as H3.
  pose proof (H 4 ltac:(lia)) as H4. pose proof (H 5 ltac:(lia)) as H5. pose proof (H 6 ltac:(lia)) as H6.
  pose proof (H 7 ltac:(lia)) as H7.
  destruct (rd a) as [b0|]; [|congruence]. destruct (rd (a + 1)) as [b1|]; [|congruence].
  destruct (rd (a + 2)) as [b2|]; [|congruence]. destruct (rd (a + 3)) as [b3|]; [|congruence].
  destruct (rd (a + 4)) as [b4|]; [|congruence]. destruct (rd (a + 5)) as [b5|]; [|congruence].
  destruct (rd (a + 6)) as [b6|]; [|congruence]. destruct (rd (a + 7)) as [b7|]; [|congruence].
  eexists. reflexivity.
Qed.

Lemma lf_nth_error_nth : forall (l : list byte) k d, (k < length l)%nat -> nth_error l k = Some (nth k l d).
Proof.
  induction l as [|x l IH]; intros [|k] d Hk; cbn [length nth_error nth] in *; [lia | lia | reflexivity | apply IH; lia].
Qed.

(* the value list of a C string and its NUL, read as numbers *)
Lemma lf_nth_map_bz : forall (s : list byte) k,
  nth k (map (fun b : byte => bv_unsigned b) s ++ [0]) 0 = bv_unsigned (nth k (s ++ [zb 0]) (zb 0)).
Proof.
  induction s as [|b s IH]; intros [|k]; cbn [map app nth].
  - reflexivity.
  - destruct k; reflexivity.
  - reflexivity.
  - apply IH.
Qed.

Lemma lf_acstr_rd : forall segs m a s, acstr_at segs m a s ->
  forall i, 0 <= i <= Z.of_nat (length s) ->
  ard segs m (a + i) = Some (nth (Z.to_nat i) (map (fun b : byte => bv_unsigned b) s ++ [0]) 0).
Proof.
  intros segs m a s ((_ & _ & Hb) & _) i Hi. unfold ard.
  replace (a + i) with (a + Z.of_nat (Z.to_nat i)) by lia.
  rewrite (Hb (Z.to_nat i) ltac:(rewrite length_app; cbn [length]; lia)).
  rewrite (lf_nth_error_nth (s ++ [zb 0]) (Z.to_nat i) (zb 0) ltac:(rewrite length_app; cbn [length]; lia)).
  cbn [option_map]. rewrite lf_nth_map_bz. reflexivity.
Qed.

Lemma lf_bytes_nz : forall nm : list byte, ~ In (zb 0) nm ->
  Forall (fun c => 0 < c < 256) (map (fun b : byte => bv_unsigned b) nm).
Proof.
  induction nm as [|b nm IH]; intros Hn; cbn [map]; constructor.
  - pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with 256 in Hr.
    assert (H0 : bv_unsigned b <> 0).
    { intros H0. apply Hn. left. apply bv_eq. rewrite H0. reflexivity. }
    cbv beta. lia.
  - apply IH. intros H. apply Hn. right. exact H.
Qed.

(* a3 as the walk holds it *)
Lemma lf_arg3 : forall (regsT : bvmap 5 word) q, getr regsT 13 = w64 q -> 0 <= q < 2 ^ 64 -> argZ regsT 3 = q.
Proof.
  intros regsT q Ha3 Hq. change (argZ regsT 3) with (bv_unsigned (getr regsT 13)). rewrite Ha3. unfold w64.
  rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia.
Qed.

(* the shadow hull of [d, d + w) lies in the shadow of the 64-byte-aligned span around it *)
Lemma lf_hull_of_ra : forall (rd : reader) p n d w,
  range_addressable rd SHADOW_OFF p n -> 0 <= d -> 0 < w ->
  p <= d / 64 * 64 -> (d + w - 1) / 64 * 64 + 64 <= p + n ->
  shadow_hull_vis rd d w.
Proof.
  intros rd p n d w HR Hd Hw Hlo Hhi s Hs.
  assert (Hword : forall x, 0 <= x -> shadow_addr x / 8 * 8 = SHADOW_OFF + x / 64 * 8).
  { intros x Hx. unfold shadow_addr.
    assert (E0 : SHADOW_OFF + x / 8 = 268431360 * 8 + x / 8) by reflexivity.
    rewrite E0, Z.div_add_l by lia. rewrite Z.div_div by lia. change (8 * 8) with 64.
    change SHADOW_OFF with 2147450880. lia. }
  rewrite (Hword d Hd), (Hword (d + w - 1) ltac:(lia)) in Hs.
  assert (E : s = shadow_of_addr SHADOW_OFF (8 * (s - SHADOW_OFF))).
  { unfold shadow_of_addr. rewrite Z.mul_comm, Z.div_mul by lia. lia. }
  assert (Hx : p <= 8 * (s - SHADOW_OFF) < p + n) by lia.
  destruct (HR _ Hx) as (v & Hv & _). rewrite E, Hv. discriminate.
Qed.

(* ==========================================================================
   3. The premise bundle and the journal step
   ========================================================================== *)

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Variable B : asyms.
(* the image instance: its allocator laws, its symbols, its segments *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : pa_segs = tfibsegs.
(* the snprintf contract (lib/A/Rt/LinkSnpDef.v, the walk's open item W5) *)
Hypothesis SNP : asnprintf_link_realizes SEGS B PCAP_RLO PCAP_RHI LA_W_SNPRINTF.

(* What the call's journal gives the step: AR at the call, the window above the allocator's ceiling, below 2^47 *)
Lemma lf_aj_facts : forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memT mdT k,
  ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdT k ->
  AR SEGS B lyc Sc W memT mdT /\ alloc_ceiling <= sp0 - STK /\ sp0 <= 2 ^ 47.
Proof.
  intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdT k HJ.
  pose proof (aj_stk_ceiling SK SEGS B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdT k HJ) as Hc.
  pose proof (ajournal_gx_row SK SEGS B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdT k HJ)
    as (_ & H47 & _ & Hhi).
  pose proof HJ as (_ & HXO & (memS & HJi & _) & _). pose proof HJi as (HAR & _).
  split; [exact HAR|]. split; [exact Hc | lia].
Qed.

(* the stack-guard .got word holds the guard's address: AR's constant cell (AF0m.v Tfib_const_abs) *)
Lemma lf_got_guard : forall ly S rd, ARm B ly S rd -> rdword rd LA_GOT_GUARD = Some LA_GUARD.
Proof.
  intros ly S rd HM.
  assert (Hin : In (z8 (ANum LA_GOT_GUARD) LA_GUARD) (as_const B ly)).
  { rewrite (ts_const B TB ly). apply (cell_lookup_In _ (ANum LA_GOT_GUARD)). vm_compute. reflexivity. }
  assert (P64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  apply (rdword_cell B ly rd LA_GOT_GUARD LA_GUARD); [unfold LA_GUARD; lia|].
  exact (proj1 (Forall_forall _ _) (am_const B ly S rd HM) _ Hin).
Qed.

(* the guard's eight bytes are image bytes, readable at every memory *)
Lemma lf_guard_word : forall (W : world SEGS) memT, exists cval, rdword (aview SEGS (w_H W) memT) LA_GUARD = Some cval.
Proof.
  intros W memT.
  assert (Hs : kp_somes_b SEGS LA_GUARD 8 = true) by (rewrite HSEGS; exact lf_guard_img).
  apply lf_rdword_some. intros i Hi.
  destruct (kp_somes_mbyte SEGS (rdW W memT) LA_GUARD 8 Hs (Z.to_nat i) ltac:(lia)) as (b & Hb).
  rewrite Z2Nat.id in Hb by lia. unfold aview. rewrite Hb. cbn [option_map]. discriminate.
Qed.

(* the format's bytes, shadow, pieces and range, at either site *)
Lemma lf_snp_fmt_facts : forall ly S (W : world SEGS) memT md f fmt ps,
  AR SEGS B ly S W memT md ->
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W) memT) ->
  lf_snp_fmt f fmt ps ->
  (forall i, 0 <= i <= Z.of_nat (length fmt) ->
     aview SEGS (w_H W) memT (f + i) = Some (nth (Z.to_nat i) (fmt ++ [0]) 0)) /\
  range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF f (Z.of_nat (length fmt) + 1) /\
  shadow_hull_vis (aview SEGS (w_H W) memT) f (Z.of_nat (length fmt) + 1) /\
  pf_parse fmt = Some ps /\ Forall pf_link_piece ps /\ Forall (fun p => p <> Pps) ps /\ fmt <> [] /\
  LINK_FMT_LO <= f /\ f + Z.of_nat (length fmt) + 1 <= 0x21300.
Proof.
  intros ly S W memT md f fmt ps (HM & _) HRO Hf.
  assert (Hb : forall a l, kp_bytes_b tfibsegs Tfib_owned_static TFIB_ERRNO a l = true ->
    kp_bytes_b SEGS Tfib_owned_static TFIB_ERRNO a l = true) by (intros a l H; rewrite HSEGS; exact H).
  destruct Hf as [(-> & -> & ->) | (-> & -> & ->)].
  - split.
    { intros i Hi.
      apply (lf_lit_rd SEGS B (w_H W) memT LA_STR (LF_FMT ++ [0]) (ts_owned B TB) (ts_errno B TB) HRO
        (Hb _ _ lf_fmt_nl_bytes)).
      + unfold LF_FMT. cbn [app]. repeat (apply Forall_cons; [cbv beta; lia|]). apply Forall_nil.
      + rewrite length_app. cbn [length]. lia. }
    replace (Z.of_nat (length LF_FMT) + 1) with 5 by reflexivity.
    split; [exact (kp_ra B TB ly S _ LA_STR 5 HM lf_fmt_nl_ra)|].
    split; [exact (kp_hull B TB ly S _ LA_STR 5 HM lf_fmt_nl_hull)|].
    split; [exact lf_fmt_parse|].
    split; [repeat (apply Forall_cons; [exact I|]); apply Forall_nil|].
    split; [repeat (apply Forall_cons; [discriminate|]); apply Forall_nil|].
    split; [unfold LF_FMT; discriminate|].
    change (Z.of_nat (length LF_FMT)) with 4. unfold LINK_FMT_LO, LA_STR. lia.
  - split.
    { intros i Hi.
      apply (lf_lit_rd SEGS B (w_H W) memT LA_STR21 (LF_FMT_S ++ [0]) (ts_owned B TB) (ts_errno B TB) HRO
        (Hb _ _ lf_fmt_s_bytes)).
      + unfold LF_FMT_S. cbn [app]. repeat (apply Forall_cons; [cbv beta; lia|]). apply Forall_nil.
      + rewrite length_app. cbn [length]. lia. }
    replace (Z.of_nat (length LF_FMT_S) + 1) with 3 by reflexivity.
    split; [exact (kp_ra B TB ly S _ LA_STR21 3 HM lf_fmt_s_ra)|].
    split; [exact (kp_hull B TB ly S _ LA_STR21 3 HM lf_fmt_s_hull)|].
    split; [exact lf_fmt_s_parse|].
    split; [apply Forall_cons; [exact I | apply Forall_nil]|].
    split; [apply Forall_cons; [discriminate | apply Forall_nil]|].
    split; [unfold LF_FMT_S; discriminate|].
    change (Z.of_nat (length LF_FMT_S)) with 2. unfold LINK_FMT_LO, LA_STR21. lia.
Qed.

(* The destination's premises of the contract, over w written bytes at d: below the allocator's ceiling (so off
   every stack window), writable, in application memory with its word slack, addressable, its shadow hull
   readable, at a place the chain does not read (LinkSnpDef.v link_snp_place) and apart from the runtime cells the
   chain reads after its first store. *)
Definition lf_snp_dest (W : world SEGS) (memT : word -> option byte) (d w : Z) : Prop :=
  0 < d /\ d + w <= alloc_ceiling /\
  (forall a, d <= a < d + w -> writable_at SEGS (rdW W memT) a) /\
  amem_range d (w + 8) /\
  range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF d w /\
  shadow_hull_vis (aview SEGS (w_H W) memT) d w /\
  link_snp_place d w /\
  Forall (zdisjoint (d, w)) link_snp_rt_cells.

(* the g_names site: d = g_names + 8 k, at most 8 bytes, at every AR state *)
Lemma lf_snp_dest_gnames : forall ly S (W : world SEGS) memT md kk w,
  AR SEGS B ly S W memT md -> 0 <= kk < 64 -> 1 <= w <= 8 ->
  lf_snp_dest W memT (LA_G_NAMES + 8 * kk) w.
Proof.
  intros ly S W memT md kk w (HM & _) Hk Hw.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (EG : LA_G_NAMES = 0x62fac0) by reflexivity.
  destruct (lf_zsh_gnames_rd B TB ly S _ HM) as (Hra & Hhv).
  unfold lf_snp_dest.
  split; [lia|]. split; [lia|].
  split.
  { intros a Ha. assert (Hwr : forall m, writable_at SEGS m a).
    { intros m. rewrite HSEGS. apply LA_G_NAMES_writable. lia. }
    apply Hwr. }
  split; [unfold amem_range; left; lia|].
  split; [apply (lf_ra_sub _ LA_G_NAMES 512); [exact Hra | lia | lia]|].
  split; [apply (lf_hull_sub _ LA_G_NAMES 512); [exact Hhv | lia | lia | lia | lia]|].
  split; [right; unfold LA_GOT_GUARD, LA_GUARD; lia|].
  unfold link_snp_rt_cells, LA_REAL_VFPRINTF, LA_REAL_VSNPRINTF, LA_ASAN_INITED, LA_SHADOW_BASE, LA_CHECK_PRINTF,
    LA_REAL_STRNLEN, LA_INTERCEPT_STRLEN, LA_REAL_MEMCHR, LA_MEM_LAYOUT, LA_COMMON_FLAGS.
  repeat (apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia|]). apply Forall_nil.
Qed.

(* a destination off the image (a heap block: the op_mark site's model block). AR places a heap block only off the
   image, below IMG_LO or above IMG_TOP (YG0d.v AR_blocks_law), and link_snp_place admits both since W7(a). *)
Lemma lf_snp_dest_heap : forall (W : world SEGS) memT d w,
  0 < d -> YCbq.off_img d w -> d + w <= alloc_ceiling ->
  (forall a, d <= a < d + w -> writable_at SEGS (rdW W memT) a) ->
  amem_range d (w + 8) ->
  range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF d w ->
  shadow_hull_vis (aview SEGS (w_H W) memT) d w ->
  lf_snp_dest W memT d w.
Proof.
  intros W memT d w Hd0 Hoff Hc Hwr Ham Hra Hhv.
  split; [exact Hd0|]. split; [exact Hc|]. split; [exact Hwr|]. split; [exact Ham|].
  split; [exact Hra|]. split; [exact Hhv|].
  split; [unfold link_snp_place; destruct Hoff as [Hl | Hh]; [right; right; exact Hl | left; exact Hh]|].
  exact (link_snp_rt_cells_of_off d w Hoff).
Qed.

(* a %d argument in a3 *)
Lemma lf_snp_arg_int : forall (regsT : bvmap 5 word) (rd : reader) rs v,
  getr regsT 13 = w64 v -> 0 <= v < 2 ^ 31 ->
  pf_args_asan rd rs (map (argZ regsT) [3; 4; 5; 6; 7]) [AInt v] /\
  SnFF.pf_args_slack (map (argZ regsT) [3; 4; 5; 6; 7]) [AInt v] /\
  SnFF.pf_args_amem (map (argZ regsT) [3; 4; 5; 6; 7]) [AInt v].
Proof.
  intros regsT rd rs v H13 Hv.
  assert (P31 : 2 ^ 31 = 2147483648) by reflexivity. assert (P64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  pose proof (lf_arg3 regsT v H13 ltac:(lia)) as E.
  cbn [map pf_args_asan SnFF.pf_args_slack SnFF.pf_args_amem pf_arg_asan]. rewrite E.
  split; [split; [split; [lia | reflexivity] | exact I]|]. split; exact I.
Qed.

(* a %s argument in a3: a C string at q, its slack to the next 8-byte word readable, in application memory, its
   shadow addressable and visible, off the call's window and apart from the destination *)
Lemma lf_snp_arg_str : forall (W : world SEGS) memT (regsT : bvmap 5 word) q (nm : list byte) d w sp,
  getr regsT 13 = w64 q -> 0 < q < 2 ^ 64 ->
  acstr_at SEGS (rdW W memT) q nm -> Z.of_nat (length nm) + 8 < 2 ^ 31 ->
  (forall x, q + Z.of_nat (length nm) < x < str_end q (map (fun b : byte => bv_unsigned b) nm) ->
     aview SEGS (w_H W) memT x <> None) ->
  amem_range q (Z.of_nat (length nm) + 8) ->
  range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF q (Z.of_nat (length nm) + 1) ->
  shadow_hull_vis (aview SEGS (w_H W) memT) q (Z.of_nat (length nm) + 1) ->
  q + Z.of_nat (length nm) + 8 <= sp - LINK_SNP_STK \/ sp <= q ->
  q + Z.of_nat (length nm) + 8 <= d \/ d + w <= q ->
  pf_args_asan (aview SEGS (w_H W) memT) (snp_out LINK_SNP_STK sp d w) (map (argZ regsT) [3; 4; 5; 6; 7])
    [APtr (map (fun b : byte => bv_unsigned b) nm)] /\
  SnFF.pf_args_slack (map (argZ regsT) [3; 4; 5; 6; 7]) [APtr (map (fun b : byte => bv_unsigned b) nm)] /\
  SnFF.pf_args_amem (map (argZ regsT) [3; 4; 5; 6; 7]) [APtr (map (fun b : byte => bv_unsigned b) nm)] /\
  pf_text [Ps] [APtr (map (fun b : byte => bv_unsigned b) nm)] = Some (map (fun b : byte => bv_unsigned b) nm).
Proof.
  intros W memT regsT q nm d w sp H13 Hq Hqs Hql Hsl Hqm Hqra Hqhv Hwin Hdst.
  pose proof (lf_arg3 regsT q H13 ltac:(lia)) as E.
  pose proof (str_end_ge q (map (fun b : byte => bv_unsigned b) nm)) as Hse. rewrite length_map in Hse.
  cbn [map pf_args_asan SnFF.pf_args_slack SnFF.pf_args_amem]. rewrite E.
  split.
  { split; [|exact I]. unfold pf_arg_asan.
    split; [apply lf_bytes_nz; exact (proj2 Hqs)|].
    split; [lia|].
    split; [rewrite length_map; exact Hql|].
    split; [intros i Hi; rewrite length_map in Hi; exact (lf_acstr_rd _ _ _ _ Hqs i Hi)|].
    split; [intros x Hx; apply Hsl; rewrite length_map in Hx; exact Hx|].
    split.
    { unfold snp_out. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold zdisjoint;
        cbn [fst snd]; lia. }
    split; [unfold amem_range in *; rewrite length_map; lia|].
    split; [rewrite length_map; exact Hqra | rewrite length_map; exact Hqhv]. }
  split; [split; [unfold amem_range in *; lia | exact I]|].
  split; [split; [rewrite length_map; exact Hqm | exact I]|].
  cbn [pf_text option_map]. rewrite app_nil_r. reflexivity.
Qed.

(* THE PREMISE BUNDLE of the contract at a call site of this function, xs = [] (at most five varargs, a3 .. a7):
   the caller gives the journal and its window, arodata_okP, the argument registers, the format (one of the two
   literals), the varargs' facts and the destination's; the guard cells, the format's bytes and shadow and the
   bounds are computed here. *)
Lemma lf_snp_pre : forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memT mdT k
    (regsT : bvmap 5 word) d n f fmt ps args T,
  ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdT k ->
  sp0 - STK <= spZ regsT - LINK_SNP_STK -> spZ regsT <= sp0 ->
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W) memT) ->
  getr regsT 10 = w64 d -> getr regsT 11 = w64 n -> getr regsT 12 = w64 f ->
  lf_snp_fmt f fmt ps ->
  pf_args_asan (aview SEGS (w_H W) memT) (snp_out LINK_SNP_STK (spZ regsT) d (sn_len (n - 1) T))
    (map (argZ regsT) [3; 4; 5; 6; 7]) args ->
  SnFF.pf_args_slack (map (argZ regsT) [3; 4; 5; 6; 7]) args ->
  SnFF.pf_args_amem (map (argZ regsT) [3; 4; 5; 6; 7]) args ->
  pf_text ps args = Some T ->
  1 <= n < 2 ^ 31 -> Z.of_nat (length T) < 2 ^ 31 - 1 ->
  lf_snp_dest W memT d (sn_len (n - 1) T) ->
  exists cval, asnprintf_link_fpre SEGS FF_link LINK_SNP_STK W memT regsT d n f []
    (map (argZ regsT) [3; 4; 5; 6; 7]) T cval.
Proof.
  intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdT k regsT d n f fmt ps args T
    HJ Hlo Hhi HRO Ha0 Ha1 Ha2 HF HA HSL HAM HT Hn HTl HD.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HSTKv : LINK_SNP_STK = 8192) by reflexivity.
  assert (P47 : 2 ^ 47 = 140737488355328) by reflexivity.
  assert (P63 : 2 ^ 63 = 9223372036854775808) by reflexivity.
  destruct (lf_aj_facts G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdT k HJ) as (HAR & Hceil & H47).
  destruct (lf_snp_fmt_facts lyc Sc W memT mdT f fmt ps HAR HRO HF)
    as (Hfb & Hfra & Hfhv & Hpar & Hpc & Hnp & Hne & Hflo & Hfhi).
  pose proof HD as (Hd0 & Hdc & Hdw & Hdam & Hdra & Hdhv & Hdpl & Hdrt).
  (* the destination is above the stack-guard .got word (the image arms) or below the image (the low arm, W7(a));
     either way it misses the format range [LINK_FMT_LO, 0x21300) *)
  assert (Hpl : LA_GOT_GUARD + 8 <= d \/ d + sn_len (n - 1) T <= YImgTop.IMG_LO)
    by (unfold link_snp_place in Hdpl; unfold YImgTop.IMG_TOP, YImgTop.IMG_LO, LA_GOT_GUARD in *; lia).
  destruct (lf_guard_word W memT) as (cval & Hcv).
  exists cval. unfold asnprintf_link_fpre.
  split; [exact Ha0|]. split; [exact Ha1|]. split; [exact Ha2|].
  split; [exact (lf_got_guard lyc Sc _ (proj1 HAR))|].
  split; [exact Hcv|].
  split; [split; [rewrite app_nil_r; reflexivity | intros i Hi; cbn [length] in Hi; lia]|].
  split; [cbn [length Z.of_nat]; lia|].
  split.
  { unfold snp_out. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold zdisjoint;
      cbn [fst snd length Z.of_nat]; lia. }
  split.
  { unfold FF_link. exists fmt, ps, args.
    split.
    { unfold fmt_at. split; [unfold LINK_FMT_LO in Hflo; lia|]. split; [exact Hfb|].
      split.
      { unfold snp_out. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold zdisjoint;
          cbn [fst snd]; unfold LA_GOT_GUARD, YImgTop.IMG_LO, LINK_FMT_LO in *; destruct Hpl as [Hpl | Hpl]; lia. }
      split; [unfold amem_range; left; lia|]. split; [exact Hfra | exact Hfhv]. }
    split; [exact Hpar|]. split; [exact Hpc|]. split; [exact HA|]. split; [exact HT|].
    split; [apply pf_prec_pos_nopps; exact Hnp|].
    split; [exact Hflo|]. split; [unfold LINK_FMT_HI, LA_GOT_GUARD; lia|].
    split; [exact HSL|]. split; [exact Hne | exact HAM]. }
  split; [exact Hn|]. split; [exact HTl|]. split; [exact Hd0|]. split; [lia|].
  split; [intros a Ha; split; [exact (Hdw a Ha) | lia]|].
  split; [exact Hdam|]. split; [exact Hdra|]. split; [exact Hdhv|]. split; [exact Hdpl | exact Hdrt].
Qed.

(* The post's own part: the call's layout, allocator state and world; the model materialised; a0 = |T|; the bytes
   sn_bytes (n - 1) T at d; every byte outside the written bytes and the window kept; presence kept but at the
   written bytes inside the image. *)
Definition lf_snp_Q (lyc : alayout) (Sc : astate) (W : world SEGS) (regsT : bvmap 5 word)
    (memT : word -> option byte) (mdT : Model) (d n : Z) (T : list Z)
  : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun ly2 S2 W2 regs2 mem2 md2 =>
    ly2 = lyc /\ S2 = Sc /\ W2 = W /\ same_but_materialized mdT md2 /\
    getr regs2 10 = w64 (Z.of_nat (length T)) /\
    (forall i, 0 <= i < sn_len (n - 1) T ->
       aview SEGS (w_H W) mem2 (d + i) = Some (nth (Z.to_nat i) (sn_bytes (n - 1) T) 0)) /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + sn_len (n - 1) T) ->
       ~ (spZ regsT - LINK_SNP_STK <= a < spZ regsT) ->
       aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) /\
    (forall a, 0 <= a < 2 ^ 64 -> apresent (w_H W) memT a ->
       ~ (d <= a < d + sn_len (n - 1) T /\ YImgTop.IMG_LO <= a < YImgTop.IMG_TOP) ->
       apresent (w_H W) mem2 a).

(* THE JOURNAL STEP: the contract at the call, its post as link_amem.v's apostF *)
Lemma lf_snp_stepF : forall G XO OUT (W : world SEGS) regsT memT STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdT k
    d n f (ws T : list Z) cval,
  gx_ok SEGS B G ->
  ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdT k ->
  sp0 - STK <= spZ regsT - LINK_SNP_STK -> spZ regsT <= sp0 -> spZ regsT mod 16 = 0 ->
  YK0s.ret_ok (getr regsT 1) ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W) memT) ->
  asnprintf_link_fpre SEGS FF_link LINK_SNP_STK W memT regsT d n f [] ws T cval ->
  (forall a, d <= a < d + sn_len (n - 1) T -> ajw B G XO OUT STK sp0 FP ly S lyc Sc own a) ->
  YK0o.frm_zero (@YK11.fp_csr fx) ->
  SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 LA_W_SNPRINTF) memT (seg_rom SEGS)) mdT)
    (apostF SK SEGS B LINK_SNP_STK 0 (fun a => d <= a < d + sn_len (n - 1) T) G XO OUT STK sp0 FP
       ly S W0 mem0 md0 own lyc Sc W memT mdT k regsT (lf_snp_Q lyc Sc W regsT memT mdT d n T)).
Proof.
  intros G XO OUT W regsT memT STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdT k d n f ws T cval
    HG HJ Hlo Hhi H16 Hra Hgp Htp HRO HPRE HAJW HFRM.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HSTKv : LINK_SNP_STK = 8192) by reflexivity.
  assert (P47 : 2 ^ 47 = 140737488355328) by reflexivity.
  assert (P64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HK : ESTACK <= LINK_SNP_STK) by (unfold LINK_SNP_STK, ESTACK; lia).
  destruct (lf_aj_facts G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdT k HJ) as (HAR & Hceil & H47).
  destruct (aj_gx_ecall_pre SK SEGS B LINK_SNP_STK G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdT k
    regsT HJ HK H16 Hlo Hhi Hra Hgp Htp) as (_ & _ & HWIN).
  eapply SRr_mono.
  { exact (link_snprintf_journal SK SEGS B LAWS pa_segs_low PCAP_RLO PCAP_RHI SNP G XO OUT W regsT memT STK sp0 FP
      ly S W0 mem0 md0 own lyc Sc mdT k (getr regsT 1) d n f [] ws T cval HG HJ Hlo Hhi H16 eq_refl Hra Hgp Htp
      HRO HPRE HAJW HFRM). }
  cbv beta. intros W2 c2 _ (-> & fx' & regs2 & mem2 & md2 & -> & HJ2 & Hfp & Hfz & HAR2 & HP2 & Hs & Ha0 & Hby &
    Hkept & Hpres).
  assert (Efs : m_fds md2 = m_fds mdT /\ m_fs md2 = m_fs mdT).
  { pose proof Hs as Hs'. unfold same_but_materialized in Hs'. rewrite Hs'. apply wvb_fds_fs. }
  unfold apostF, apost.
  exists fx'. split; [exact (fxr_of_frm0 fx fx' Hfp Hfz)|].
  exists lyc, Sc, regs2, mem2, md2.
  split; [reflexivity|].
  split; [rewrite Z.add_0_r; exact HJ2|].
  split; [exact HP2|]. split; [reflexivity|].
  split; [exact (proj1 Efs)|]. split; [exact (proj2 Efs)|].
  split.
  { apply (akept_step SK SEGS B LAWS pa_segs_low lyc Sc W memT mdT W memT W mem2
      (spZ regsT - LINK_SNP_STK) (spZ regsT) (fun a => d <= a < d + sn_len (n - 1) T)
      (fun a => d <= a < d + sn_len (n - 1) T)
      (fun a => (d <= a < d + sn_len (n - 1) T) \/ (spZ regsT - LINK_SNP_STK <= a < spZ regsT)) HAR).
    - lia.
    - lia.
    - exact (akept_refl SK SEGS B LAWS pa_segs_low lyc Sc W memT _ _ _ HWIN).
    - intros a Ha HX. apply Hkept; [exact Ha | intros H; apply HX; left; exact H | intros H; apply HX; right; exact H].
    - intros a Ha Hp. apply Hpres; [lia | exact Hp|]. intros (_ & _ & Ht). unfold YImgTop.IMG_TOP in Ht. lia.
    - intros a H; exact H.
    - intros a H; exact H. }
  split; [exact (ashadow_kept_AR SK SEGS B LAWS pa_segs_low lyc Sc lyc Sc W memT mdT W mem2 md2 HAR HAR2)|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact Hs|]. split; [exact Ha0|]. split; [exact Hby|]. split; [exact Hkept | exact Hpres].
Qed.

(* the same step, handing the continuation in link_amem.v's apostF_continue shape *)
Lemma lf_snp_step : forall G XO OUT (W : world SEGS) regsT memT STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdT k
    d n f (ws T : list Z) cval (R : world SEGS -> config -> Prop),
  gx_ok SEGS B G ->
  ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdT k ->
  sp0 - STK <= spZ regsT - LINK_SNP_STK -> spZ regsT <= sp0 -> spZ regsT mod 16 = 0 ->
  YK0s.ret_ok (getr regsT 1) ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W) memT) ->
  asnprintf_link_fpre SEGS FF_link LINK_SNP_STK W memT regsT d n f [] ws T cval ->
  (forall a, d <= a < d + sn_len (n - 1) T -> ajw B G XO OUT STK sp0 FP ly S lyc Sc own a) ->
  YK0o.frm_zero (@YK11.fp_csr fx) ->
  (forall (fx' : YK11.FPState) (W2 : world SEGS) (c2 : config), wle W W2 -> @BoxBase.fxr fx fx' ->
     apost (fx := fx') SK SEGS B LINK_SNP_STK 0 (fun a => d <= a < d + sn_len (n - 1) T) G XO OUT STK sp0 FP
       ly S W0 mem0 md0 own lyc Sc W memT mdT k regsT (lf_snp_Q lyc Sc W regsT memT mdT d n T) W2 c2 ->
     SRr SEGS W2 c2 R) ->
  SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 LA_W_SNPRINTF) memT (seg_rom SEGS)) mdT) R.
Proof.
  intros G XO OUT W regsT memT STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdT k d n f ws T cval R
    HG HJ Hlo Hhi H16 Hra Hgp Htp HRO HPRE HAJW HFRM HC.
  exact (apostF_continue SK SEGS B LINK_SNP_STK 0 _ G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdT k
    regsT _ W _ R
    (lf_snp_stepF G XO OUT W regsT memT STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdT k d n f ws T cval
       HG HJ Hlo Hhi H16 Hra Hgp Htp HRO HPRE HAJW HFRM) HC).
Qed.

(* ==========================================================================
   4. The g_names site, 0x82b14: snprintf(g_names + 8 k, 8, "nl%d", k)
   ========================================================================== *)

Lemma lf_snp_at : forall XO OUT (W : world SEGS) regsT memT STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdT k raw kk,
  gx_ok SEGS B G_HARNESS ->
  ajournal_gx SEGS B G_HARNESS XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdT k ->
  sp0 - STK <= spZ regsT - LINK_SNP_STK -> spZ regsT <= sp0 -> spZ regsT mod 16 = 0 ->
  getr regsT 1 = raw -> YK0s.ret_ok raw ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  getr regsT 10 = w64 (LA_G_NAMES + 8 * kk) -> getr regsT 11 = w64 8 -> getr regsT 12 = w64 LA_STR ->
  getr regsT 13 = w64 kk -> 0 <= kk < 64 ->
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W) memT) ->
  YK0o.frm_zero (@YK11.fp_csr fx) ->
  SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 LA_W_SNPRINTF) memT (seg_rom SEGS)) mdT)
    (fun W2 c2 => W2 = W /\ exists (fx' : YK11.FPState) regs2 mem2 md2,
       c2 = mkCfg (@YK11.mkst fx' regs2 raw mem2 (seg_rom SEGS)) md2 /\
       @BoxBase.fxr fx fx' /\ YK0o.frm_zero (@YK11.fp_csr fx') /\
       ajournal_gx SEGS B G_HARNESS XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
       aregs_preserved regsT regs2 /\ same_but_materialized mdT md2 /\
       getr regs2 10 = w64 (Z.of_nat (length (lf_gname_z kk))) /\
       (forall i, 0 <= i <= Z.of_nat (length (lf_gname_z kk)) ->
          aview SEGS (w_H W) mem2 (LA_G_NAMES + 8 * kk + i) = Some (nth (Z.to_nat i) (lf_gname_z kk ++ [0]) 0)) /\
       (forall a, 0 <= a < 2 ^ 64 ->
          ~ (LA_G_NAMES + 8 * kk <= a <= LA_G_NAMES + 8 * kk + Z.of_nat (length (lf_gname_z kk))) ->
          ~ (spZ regsT - LINK_SNP_STK <= a < spZ regsT) ->
          aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) /\
       (forall a, 0 <= a < 2 ^ 64 -> apresent (w_H W) memT a ->
          ~ (LA_G_NAMES + 8 * kk <= a <= LA_G_NAMES + 8 * kk + Z.of_nat (length (lf_gname_z kk))) ->
          apresent (w_H W) mem2 a)).
Proof.
  intros XO OUT W regsT memT STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdT k raw kk
    HG HJ Hlo Hhi H16 Hraw Hrok Hgp Htp Ha0 Ha1 Ha2 Ha3 Hk HRO HFRM.
  assert (P31 : 2 ^ 31 = 2147483648) by reflexivity.
  assert (Hk100 : 0 <= kk < 100) by lia.
  destruct (lf_sn_bytes kk Hk100) as (Hsb & Hsl).
  pose proof (lf_sn_len_range kk Hk100) as Hslr.
  pose proof (lf_gname_z_len kk Hk100) as Hgl.
  destruct (lf_aj_facts G_HARNESS XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdT k HJ) as (HAR & _ & _).
  destruct (lf_snp_arg_int regsT (aview SEGS (w_H W) memT)
    (snp_out LINK_SNP_STK (spZ regsT) (LA_G_NAMES + 8 * kk) (sn_len (8 - 1) (lf_gname_z kk))) kk Ha3 ltac:(lia))
    as (HA & HSL & HAM).
  assert (HD : lf_snp_dest W memT (LA_G_NAMES + 8 * kk) (sn_len (8 - 1) (lf_gname_z kk))).
  { apply (lf_snp_dest_gnames lyc Sc W memT mdT kk _ HAR Hk). change (8 - 1) with 7. lia. }
  destruct (lf_snp_pre G_HARNESS XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdT k regsT
    (LA_G_NAMES + 8 * kk) 8 LA_STR LF_FMT [PLit 110; PLit 108; Pd] [AInt kk] (lf_gname_z kk)
    HJ Hlo Hhi HRO Ha0 Ha1 Ha2 (or_introl (conj eq_refl (conj eq_refl eq_refl))) HA HSL HAM (lf_pf_text kk Hk100)
    ltac:(lia) ltac:(lia) HD) as (cval & HPRE).
  assert (HAJW : forall a, LA_G_NAMES + 8 * kk <= a < LA_G_NAMES + 8 * kk + sn_len (8 - 1) (lf_gname_z kk) ->
    ajw B G_HARNESS XO OUT STK sp0 FP ly S lyc Sc own a).
  { intros a Ha. right. left. change (8 - 1) with 7 in Ha.
    apply (inG_of_In G_HARNESS LA_G_NAMES 512 a); [unfold G_HARNESS; cbn [In]; right; left; reflexivity | lia]. }
  eapply SRr_mono.
  { exact (link_snprintf_journal SK SEGS B LAWS pa_segs_low PCAP_RLO PCAP_RHI SNP G_HARNESS XO OUT W regsT memT STK
      sp0 FP ly S W0 mem0 md0 own lyc Sc mdT k raw (LA_G_NAMES + 8 * kk) 8 LA_STR [] (map (argZ regsT) [3; 4; 5; 6; 7])
      (lf_gname_z kk) cval HG HJ Hlo Hhi H16 Hraw Hrok Hgp Htp HRO HPRE HAJW HFRM). }
  cbv beta. intros W2 c2 _ (-> & fx' & regs2 & mem2 & md2 & -> & HJ2 & Hfp & Hfz & _ & HP2 & Hs & Hr0 & Hby &
    Hkept & Hpres).
  change (8 - 1) with 7 in Hby, Hkept, Hpres. rewrite Hsb, Hsl in Hby. rewrite Hsl in Hkept, Hpres.
  split; [reflexivity|]. exists fx', regs2, mem2, md2.
  split; [reflexivity|].
  split; [exact (fxr_of_frm0 fx fx' Hfp Hfz)|].
  split; [exact Hfz|].
  split; [exact HJ2|]. split; [exact HP2|]. split; [exact Hs|]. split; [exact Hr0|].
  split; [intros i Hi; exact (Hby i ltac:(lia))|].
  split.
  { intros a Ha H1 H2. apply Hkept; [exact Ha | intros H; apply H1; lia | exact H2]. }
  intros a Ha Hp H1. apply Hpres; [exact Ha | exact Hp | intros (H2 & _); apply H1; lia].
Qed.

End a.

About lf_snp_pre.
Print Assumptions lf_snp_pre.
About lf_snp_stepF.
Print Assumptions lf_snp_stepF.
About lf_snp_step.
Print Assumptions lf_snp_step.
About lf_snp_at.
Print Assumptions lf_snp_at.
About lf_snp_arg_str.
Print Assumptions lf_snp_arg_str.
About lf_snp_dest_heap.
About lf_hull_of_ra.
Print Assumptions lf_hull_of_ra.
