(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed and off_img at fuzz_command's ASan image end 0x606000; ajournal no longer keeps footprint (FP) bytes in the image or at or above alloc_ceiling (fp_spares FP a also requires ~ inFP FP a, and the clause for bytes at or above alloc_ceiling outside [sp0 - STK, sp0) requires ~ inFP FP a), awr_byte (and awr_ok) take the start state's side-stack frames as a new parameter and also admit footprint writes to the program's statics as_prog_static in the image, to the caller's stack above sp0 and to those caller frames (awr_prog_or_caller), acall_kept_of_journal, region_kept_stack_sub, awr_byte_present and aj_intrin_at take the matching premises, ajournal_sub_wide composes a callee whose footprint lies in what the caller may write, awr_byte_present_prog and aj_intrin_at_prog take prog_rw for stores to the statics, AR_errno_present gives the errno cell's value from errno_rom, and astack_rd/astack_pres (stack bytes readable/present from sp to the stack top) give a frame chain for any s0 but an aligned sp + 8 (chain_pre_any, achain_any) and carry across an ajournal (astack_rd_journal, astack_pres_journal). *)
(* Modified by Theorem Labs, 2026-10: the malloc/free journal lemmas (aj_free_at, aj_free_at_io, aj_free_null_at, aj_free_null_at_io, aj_malloc_at, aj_malloc_at_io, aj_malloc_at04, aj_malloc_at04_io, aj_malloc, aj_free) no longer take In (call_trace0 ...) (as_universe B); the model laws get the trace length (call_trace_len) and the contracts the event bound. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/Reusable/YCbq.v, with its module paths and module names changed; 1154 of its 1305 lines of code are new or changed and 3194 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LinkWalkSide.v, with its module paths and module names changed; 415 of its 474 lines of code are new or changed and 1246 lines of the source are left out. *)
(* remember (image A 0x89db4, listing (internal path) (internal record, sha256 e02062b286f1)):
   the two outgoing transfers of the function, each as ONE step a symbolic walk over the caller's journal `ajournal_gx`
   applies under SRr_bind. The walk itself is lib/A/Prog/remember.v; this file states and
   proves only the two steps.

     rem_strcmp_call : +0x64 `jal wrapper_strcmp` (0x4304c), inside the loop, at sp = entry sp - 64;
     rem_snp_tail    : +0xf4 `j wrapper_snprintf` (0x43088), a TAIL jump: sp is back at the entry sp (+0xf0) and ra
                       is remember's own ra, so the wrapper returns straight to remember's caller; the step ENDS at
                       the wrapper's return config, which is remember's own return config.

   rem_strcmp_call is model_decide.v's dec_strcmp_call
   at K = REMEMBER_AK = 8256 and the call's sp = entry sp - 64: the string premises come from
   the Pre (acstr_at / astr_rt_ok at the call memory memc, kept to memT outside [sp - K, sp)), the runtime pre-state
   from the journal (link_ajkit.v aj_gx_ecall_pre at w = 2 * ESTACK: 64 + 8192 = 8256 gives the room), and the step
   goes through link_ajkit.v aj_gx_call_at (rem_art_at below, model_decide.v's dec_art_at), which keeps the conjunct
   `same_but_materialized mdT md2` that LinkWalk.v's aj_gx_strcmp_at drops (the walk's apost needs m_fds / m_fs).

   rem_snp_tail is lib/A/Rt/LinkSnpJ.v link_snprintf_journal (the journal step of the snprintf contract: the runtime
   pre-state from the journal, ~ aowned of the written bytes from `ajw` and their writability, the lift
   aj_gx_call_atFo at window LINK_SNP_STK = 2 * ESTACK) at d = p + 4 + 16 n, n = 16, f = LA_FMT_S, xs = [], and the
   function's own premise bundle rem_snp_fpre below. How each premise of LinkSnpDef.v asnprintf_link_realizes is met
   (the instruction that needs each is in LinkSnpDef.v's header):
   - ecall_pre, ly_stk_lo + LINK_SNP_STK <= sp, the window present: aj_gx_ecall_pre at w = 2 * ESTACK (8192 <= 8256);
   - arodata_okP at PCAP_RLO / PCAP_RHI: the walk invariant, a hypothesis;
   - the guard cells `rdword LA_GOT_GUARD = Some LA_GUARD` and `exists cval, rdword LA_GUARD = Some cval`: TWO EXTRA
     HYPOTHESES at memT. They are not derivable at an abstract B and an abstract PAImg: AR's const law (YG0d.v:469)
     holds only the shadow cell, the uar cell and their .got words; the row `z8 (ANum 0xa2658) 0x651c50` is in
     `as_const B ly` only through PcapSyms B (AE22.v canary_cell_in), and the guard object's bytes need seg_rom at
     the concrete segments (AFii.v can_bytes). The walk feeds them from its own instance hypothesis (agreed with
     remember's walk, 2026-10-30);
   - FF_link at fmt = "%s" = [37; 115], ps = [Ps], args = [APtr (map bv_unsigned nm)], T = map bv_unsigned nm: the
     format's and the name's bytes from acstr_at, their shadow, band and slack from astr_rt_ok, their separation from
     snp_out = [(sp - 8192, 8192); (d, |nm| + 1)] from astr_rt_ok's apart_frame at K = 8256 (the 64 spare bytes cover
     the slack up to the NUL's 8-byte word end) and from `apart q (|nm| + 8) p MK_SIZE`;
   - va_words at xs = [] (a3 = q), 1 <= 16 < 2 ^ 31, sn_len 15 T = |nm| + 1 (|nm| <= 15);
   - the destination: writable by amarks_at, outside the window by amarks_blk_ok's apart_frame, amem_range /
     range_addressable / shadow_hull_vis from amarks_blk_ok over the whole block ([d, d + 16) is inside
     [p, p + MK_SIZE) for n <= 31); written bytes the journal lets a callee write: the `ajw` hypothesis (the write set);
     link_snp_place by the block's `YCbq.off_img p MK_SIZE` (above the image: its first arm IMG_TOP <= d; below
     it: its last arm d + 16 <= p + MK_SIZE <= IMG_LO); link_snp_rt_cells_of_off on the same two arms;
   - frm0: the entry's rounding mode, a hypothesis.
   The contract keeps presence everywhere but at in-image destination bytes; the marks block is off the image, so
   the step's post keeps every present byte present.

   Section hypotheses: STRCMP (RtString.astrcmp_realizes at the strcmp trampoline; discharged by lib/A/Rt/
   RtStrcmpClosed.v link_strcmp_closed), SNP (LinkSnpDef.v asnprintf_link_realizes at PCAP_RLO / PCAP_RHI and
   LA_W_SNPRINTF; the closed abbreviation is lib/A/Rt/LinkSnpInst.v link_asnprintf_contract), LAWS (AR_laws), and the
   instance hypotheses TL (PALib) and HV (LinkVals) every walk takes.
   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YImgTop YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require RtString.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Rt Require Import PfFacts SnShared SnFF.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMfDefs LinkPfPiece LinkSnpDef.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit LinkWalk.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkSnpJ.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import model_decide_c remember_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ==========================================================================
   1. Byte and range facts
   ========================================================================== *)

Lemma rem_aview_some_grow : forall segs H m m' a,
  mem_grows (mrestrict H m) (mrestrict H m') -> aview segs H m a <> None -> aview segs H m' a <> None.
Proof.
intros segs H m m' a Hg Hn. unfold aview, mbyte in *.
destruct (mrestrict H m' (Z_to_bv 64 a)) eqn:E2; [discriminate|].
destruct (mrestrict H m (Z_to_bv 64 a)) eqn:E1; [|exact Hn].
exfalso. apply (Hg (Z_to_bv 64 a)); [rewrite E1; discriminate | exact E2].
Qed.

Lemma rem_nth_error_nth : forall (l : list byte) k d, (k < length l)%nat -> nth_error l k = Some (nth k l d).
Proof.
induction l as [|x l IH]; intros [|k] d Hk; cbn [length nth_error nth] in *; [lia | lia | reflexivity | apply IH; lia].
Qed.

(* the value list of a C string and its NUL, read as numbers *)
Lemma rem_nth_map_bz : forall (s : list byte) k,
  nth k (map (fun b : byte => bv_unsigned b) s ++ [0]) 0 = bv_unsigned (nth k (s ++ [zb 0]) (zb 0)).
Proof.
induction s as [|b s IH]; intros [|k]; cbn [map app nth].
- reflexivity.
- destruct k; reflexivity.
- reflexivity.
- apply IH.
Qed.

(* the bytes of a C string, as the reader sees them *)
Lemma rem_acstr_rd : forall segs m a s, acstr_at segs m a s ->
  forall i, 0 <= i <= Z.of_nat (length s) ->
  ard segs m (a + i) = Some (nth (Z.to_nat i) (map (fun b : byte => bv_unsigned b) s ++ [0]) 0).
Proof.
intros segs m a s ((_ & _ & Hb) & _) i Hi. unfold ard.
replace (a + i) with (a + Z.of_nat (Z.to_nat i)) by lia.
rewrite (Hb (Z.to_nat i) ltac:(rewrite length_app; cbn [length]; lia)).
rewrite (rem_nth_error_nth (s ++ [zb 0]) (Z.to_nat i) (zb 0) ltac:(rewrite length_app; cbn [length]; lia)).
cbn [option_map].
rewrite rem_nth_map_bz. reflexivity.
Qed.

(* the bytes of a C string are 1..255 *)
Lemma rem_bytes_nz : forall nm : list byte, ~ In (zb 0) nm ->
  Forall (fun c => 0 < c < 256) (map (fun b : byte => bv_unsigned b) nm).
Proof.
induction nm as [|b nm IH]; intros Hn; cbn [map]; constructor.
- pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with 256 in Hr.
  assert (H0 : bv_unsigned b <> 0).
  { intros H0. apply Hn. left. apply bv_eq. rewrite H0. reflexivity. }
  cbv beta. lia.
- apply IH. intros H. apply Hn. right. exact H.
Qed.

Lemma rem_amem_sub : forall p n p' n', amem_range p n -> p <= p' -> 0 <= n' -> p' + n' <= p + n -> amem_range p' n'.
Proof. intros p n p' n' H H1 H2 H3. unfold amem_range in *. lia. Qed.

Lemma rem_hull_sub : forall (rd : reader) p n p' n', shadow_hull_vis rd p n -> p <= p' -> 0 < n' -> p' + n' <= p + n ->
  shadow_hull_vis rd p' n'.
Proof.
intros rd p n p' n' H H1 H2 H3 s Hs. apply H. unfold shadow_addr in *.
assert (A1 : p / 8 <= p' / 8) by (apply Z.div_le_mono; lia).
assert (A2 : (p' + n' - 1) / 8 <= (p + n - 1) / 8) by (apply Z.div_le_mono; lia).
assert (B1 : (SHADOW_OFF + p / 8) / 8 <= (SHADOW_OFF + p' / 8) / 8) by (apply Z.div_le_mono; lia).
assert (B2 : (SHADOW_OFF + (p' + n' - 1) / 8) / 8 <= (SHADOW_OFF + (p + n - 1) / 8) / 8)
  by (apply Z.div_le_mono; lia).
lia.
Qed.

(* ==========================================================================
   2. The step lemmas
   ========================================================================== *)

Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis TL : PALib B.
Hypothesis HV : LinkVals (L := link_listing).
Hypothesis STRCMP : RtString.astrcmp_realizes pa_segs B (pa_sigma LS___interceptor_trampoline_strcmp).
Hypothesis SNP : asnprintf_link_realizes pa_segs B PCAP_RLO PCAP_RHI LA_W_SNPRINTF.

(* the journal's bounds a step needs: the window is above the allocator's ceiling and below 2 ^ 47 *)
Lemma rem_aj_bounds : forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k,
  ajournal_gx pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  alloc_ceiling <= sp0 - STK /\ sp0 <= 2 ^ 47 /\ 0 <= XO /\
  (forall a, sp0 - STK <= a < sp0 -> apresent (w_H W) memc a).
Proof.
intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (HSTK & HXO & (memS & HJ & _) & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
destruct Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
split; [lia|]. split; [lia|]. split; [exact HXO|]. intros a Ha. apply Hpres. lia.
Qed.

(* ---- the kept views of a string the Pre states at the call memory memc, at a later memory memT that agrees with
   memc outside [sp - K, sp) and keeps every byte memc has ---- *)

Lemma rem_ra_keep : forall (W : world pa_segs) regs memc memT p n,
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - REMEMBER_AK <= a < spZ regs) ->
     aview pa_segs (w_H W) memT a = aview pa_segs (w_H W) memc a) ->
  alloc_ceiling <= spZ regs - REMEMBER_AK ->
  0 <= p -> p + n <= 2 ^ 47 ->
  range_addressable (ard pa_segs (mrestrict (w_H W) memc)) SHADOW_OFF p n ->
  range_addressable (aview pa_segs (w_H W) memT) SHADOW_OFF p n.
Proof.
intros W regs memc memT p n UN Hceil Hp Hpn HR. pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
assert (HKv : REMEMBER_AK = 8256) by reflexivity.
apply (ra_shadow_eq (aview pa_segs (w_H W) memc)); [exact HR|].
intros x Hx. apply UN; unfold shadow_addr, SHADOW_OFF; lia.
Qed.

Lemma rem_astr_keep : forall (W : world pa_segs) regs memc memT p s,
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - REMEMBER_AK <= a < spZ regs) ->
     aview pa_segs (w_H W) memT a = aview pa_segs (w_H W) memc a) ->
  acstr_at pa_segs (mrestrict (w_H W) memc) p s -> apart_frame regs REMEMBER_AK p (Z.of_nat (length s) + 1) ->
  0 <= p -> p + Z.of_nat (length s) + 1 <= 2 ^ 64 ->
  astr_at pa_segs W memT p s.
Proof.
intros W regs memc memT p s UN ((_ & _ & Hb) & Hnz) Hap Hp Hp64. split; [|exact Hnz].
intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
rewrite UN by (unfold apart_frame in Hap; lia).
unfold aview. rewrite (Hb i ltac:(rewrite length_app; cbn [length]; lia)).
rewrite (rem_nth_error_nth (s ++ [zb 0]) i (Z_to_bv 8 0) ltac:(rewrite length_app; cbn [length]; lia)). reflexivity.
Qed.

Lemma rem_aread_keep : forall (W : world pa_segs) regs memc memT regsT p s n,
  alloc_ceiling <= spZ regs - REMEMBER_AK ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - REMEMBER_AK <= a < spZ regs) ->
     aview pa_segs (w_H W) memT a = aview pa_segs (w_H W) memc a) ->
  mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) memT) ->
  acstr_at pa_segs (mrestrict (w_H W) memc) p s -> astr_rt_ok pa_segs regs REMEMBER_AK (mrestrict (w_H W) memc) p s ->
  spZ regsT = spZ regs - 64 -> 0 < n <= Z.of_nat (length s) + 1 ->
  aread_ok pa_segs (2 * ESTACK) W regsT memT p n.
Proof.
intros W regs memc memT regsT p s n Hceil UN GR ((_ & _ & Hb) & Hnz) (Hp & Hl31 & Hamr & Hra & Hhv & Htl & Hap)
  HspT Hn.
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
assert (HKv : REMEMBER_AK = 8256) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hp47 : p + Z.of_nat (length s) + 8 <= 2 ^ 47 - 1) by (unfold amem_range in Hamr; lia).
unfold aread_ok. split; [lia|]. split; [lia|]. split; [lia|]. split.
- intros a Ha. split.
  + apply (rem_aview_some_grow _ _ _ _ _ GR). unfold aview.
    replace a with (p + Z.of_nat (Z.to_nat (a - p))) by lia.
    rewrite (Hb (Z.to_nat (a - p)) ltac:(rewrite length_app; cbn [length]; lia)).
    rewrite (rem_nth_error_nth (s ++ [zb 0]) (Z.to_nat (a - p)) (Z_to_bv 8 0)
      ltac:(rewrite length_app; cbn [length]; lia)). cbn [option_map].
    discriminate.
  + unfold ascratch_stk. rewrite HspT. unfold apart_frame in Hap. lia.
- split; [unfold amem_range in *; lia|]. split.
  + apply (rem_ra_keep W regs memc memT p n UN Hceil); [lia | lia |]. intros x Hx. apply Hra. lia.
  + intros _ x Hx. apply (rem_aview_some_grow _ _ _ _ _ GR). exact (Hhv x ltac:(unfold shadow_addr in *; lia)).
Qed.

Lemma rem_atail_keep : forall (W : world pa_segs) regs memc memT p s,
  mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) memT) ->
  astr_rt_ok pa_segs regs REMEMBER_AK (mrestrict (w_H W) memc) p s -> atail_vis pa_segs W memT (p + astr_len s).
Proof.
intros W regs memc memT p s GR (_ & _ & _ & _ & _ & Htl & _) a Ha. apply (rem_aview_some_grow _ _ _ _ _ GR).
exact (Htl a Ha).
Qed.

Lemma rem_rtrom_keep : forall (W : world pa_segs) regs memc memT rlo rhi,
  alloc_ceiling <= spZ regs - REMEMBER_AK ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - REMEMBER_AK <= a < spZ regs) ->
     aview pa_segs (w_H W) memT a = aview pa_segs (w_H W) memc a) ->
  arodata_okP pa_segs rlo rhi B (aview pa_segs (w_H W) memc) ->
  rt_rom_view pa_segs B W memT.
Proof.
intros W regs memc memT rlo rhi Hceil UN Hro a Hrom Hno Herr. pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
assert (HKv : REMEMBER_AK = 8256) by reflexivity.
assert (Hi : in_img pa_segs a) by (destruct Hrom as (sg & Hin & _ & Hr); exists sg; split; [exact Hin | exact Hr]).
pose proof (pa_segs_low a Hi) as Hlow.
rewrite UN by lia. apply Hro; [left; exact Hrom | exact Hno | exact Herr].
Qed.

(* link_ajkit's aj_gx_art_at with the conjunct `same_but_materialized mdc md2` kept (model_decide.v's dec_art_at) *)
Lemma rem_art_at : forall stk pc G XO OUT W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k
    raw (Qr : bvmap 5 word -> (word -> option byte) -> Prop),
  gx_ok pa_segs B G ->
  ajournal_gx pa_segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  0 <= stk -> sp0 - STK <= spZ regsT - stk -> spZ regsT <= sp0 ->
  getr regsT 1 = raw ->
  SRr pa_segs W (cfg_at pa_segs pc regsT memT mdc) (art_post pa_segs B stk lyc Sc W regsT memT mdc (fun _ => False) Qr) ->
  SRr pa_segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom pa_segs)) mdc)
    (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
       c2 = mkCfg (mkst regs2 raw mem2 (seg_rom pa_segs)) md2 /\
       ajournal_gx pa_segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
       aregs_preserved regsT regs2 /\ same_but_materialized mdc md2 /\ Qr regs2 mem2 /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - stk <= a < spZ regsT) ->
          aview pa_segs (w_H W) mem2 a = aview pa_segs (w_H W) memT a) /\
       (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros stk pc G XO OUT W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k raw Qr
  HG HJX Hstk Hlo Hhi Hraw HC.
eapply SRr_mono.
{ apply (aj_gx_call_at SK pa_segs B LAWS pa_segs_low stk (fun _ => False) pc G XO OUT W regsT memT STK sp0 FP ly S
    W0 mem md own lyc Sc mdc k raw
    (fun regs' mem' md' => AR pa_segs B lyc Sc W mem' md' /\ aregs_preserved regsT regs' /\
       same_but_materialized mdc md' /\ Qr regs' mem' /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ ascratch_stk stk regsT a -> ~ (fun _ => False) a ->
          aview pa_segs (w_H W) mem' a = aview pa_segs (w_H W) memT a) /\
       (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem' a) /\
       (forall a, ascratch_stk stk regsT a -> apresent (w_H W) mem' a))
    HG HJX Hstk Hlo Hhi Hraw).
  - intros a [].
  - intros regs' mem' md' (HAR' & _ & Hs & _ & Hf & Hp & _).
    split; [exact HAR'|]. split; [exact Hs|]. split; [|exact Hp].
    intros a Ha Hw He. exact (Hf a Ha Hw He).
  - exact HC. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & _ & HP & Hs & HQ & Hfr & Hpres2 & _).
split; [reflexivity|]. exists regs2, mem2, md2. split; [reflexivity|].
split; [exact HJ2|]. split; [exact HP|]. split; [exact Hs|]. split; [exact HQ|].
split; [intros a Ha Hw; exact (Hfr a Ha Hw (fun H => H)) | exact Hpres2].
Qed.

(* ---- (a) +0x64 jal wrapper_strcmp, at sp = entry sp - 64 ---- *)
Lemma rem_strcmp_call : forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs regsT memT mdT raw
    x y sx sy,
  gx_ok pa_segs B G ->
  ajournal_gx pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdT k ->
  arodata_okP pa_segs PCAP_RLO PCAP_RHI B (aview pa_segs (w_H W) memc) ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - REMEMBER_AK -> spZ regs <= sp0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - REMEMBER_AK <= a < spZ regs) ->
     aview pa_segs (w_H W) memT a = aview pa_segs (w_H W) memc a) ->
  mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) memT) ->
  spZ regsT = spZ regs - 64 ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
  getr regsT 10 = w64 x -> getr regsT 11 = w64 y ->
  acstr_at pa_segs (mrestrict (w_H W) memc) x sx ->
  astr_rt_ok pa_segs regs REMEMBER_AK (mrestrict (w_H W) memc) x sx ->
  acstr_at pa_segs (mrestrict (w_H W) memc) y sy ->
  astr_rt_ok pa_segs regs REMEMBER_AK (mrestrict (w_H W) memc) y sy ->
  SRr pa_segs W (mkCfg (mkst regsT (Z_to_bv 64 (pa_sigma LS___interceptor_trampoline_strcmp)) memT (seg_rom pa_segs)) mdT)
    (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
       c2 = mkCfg (mkst regs2 raw mem2 (seg_rom pa_segs)) md2 /\
       ajournal_gx pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
       aregs_preserved regsT regs2 /\ same_but_materialized mdT md2 /\
       (getr regs2 10 = w64 0 <-> sx = sy) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - 2 * ESTACK <= a < spZ regsT) ->
          aview pa_segs (w_H W) mem2 a = aview pa_segs (w_H W) memT a) /\
       (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs regsT memT mdT raw x y sx sy
  HG HJ HROD Hal16 Hwlo Hwhi UN GR HspT Hgp Htp Hra Hraw Hx Hy Hxs Hxs_rt Hys Hys_rt.
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
assert (HKv : REMEMBER_AK = 8256) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
destruct (rem_aj_bounds G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdT k HJ) as (Hceil & H47 & HXO & _).
assert (Hceil' : alloc_ceiling <= spZ regs - REMEMBER_AK) by lia.
pose proof Hxs_rt as (Hx0 & Hxl & Hxm & _ & _ & _ & Hxa).
pose proof Hys_rt as (Hy0 & Hyl & Hym & _ & _ & _ & Hya).
assert (Hx47 : x + Z.of_nat (length sx) + 8 <= 2 ^ 47 - 1) by (unfold amem_range in Hxm; lia).
assert (Hy47 : y + Z.of_nat (length sy) + 8 <= 2 ^ 47 - 1) by (unfold amem_range in Hym; lia).
pose proof (aj_gx_ecall_pre SK pa_segs B (2 * ESTACK) G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdT k regsT
  HJ ltac:(lia) ltac:(rewrite HspT; lia) ltac:(lia) ltac:(lia) ltac:(rewrite Hra; exact Hraw) Hgp Htp) as HPRE.
eapply SRr_mono.
{ apply (rem_art_at (2 * ESTACK) (pa_sigma LS___interceptor_trampoline_strcmp) G XO OUT W regsT memT STK sp0 FP ly S
    W0 mem0 md0 own lyc Sc mdT k raw (fun regs' _ => getr regs' 10 = w64 0 <-> sx = sy)
    HG HJ ltac:(lia) ltac:(lia) ltac:(lia) Hra).
  apply (STRCMP lyc Sc W regsT memT mdT x y sx sy HPRE Hx Hy Hx0 Hy0
    (rem_astr_keep W regs memc memT x sx UN Hxs Hxa ltac:(lia) ltac:(lia))
    (rem_astr_keep W regs memc memT y sy UN Hys Hya ltac:(lia) ltac:(lia))
    (rem_aread_keep W regs memc memT regsT x sx (astr_len sx + 1) Hceil' UN GR Hxs Hxs_rt HspT
       ltac:(unfold astr_len; lia))
    (rem_aread_keep W regs memc memT regsT y sy (astr_len sy + 1) Hceil' UN GR Hys Hys_rt HspT
       ltac:(unfold astr_len; lia))
    (rem_atail_keep W regs memc memT x sx GR Hxs_rt) (rem_atail_keep W regs memc memT y sy GR Hys_rt)
    (rem_rtrom_keep W regs memc memT PCAP_RLO PCAP_RHI Hceil' UN HROD)). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP & Hs & HQ & Hfr & Hpres2).
split; [reflexivity|]. exists regs2, mem2, md2. split; [reflexivity|].
split; [exact HJ2|]. split; [exact HP|]. split; [exact Hs|].
split; [exact HQ|].
split; [exact Hfr | exact Hpres2].
Qed.

(* ---- (b) +0xf4 j wrapper_snprintf: the tail jump ---- *)

Lemma rem_sn_len : forall nm : list byte, (length nm <= 15)%nat ->
  sn_len (16 - 1) (map (fun b : byte => bv_unsigned b) nm) = Z.of_nat (length nm) + 1.
Proof.
intros nm Hl. unfold sn_len, sn_bytes. change (Z.to_nat (16 - 1)) with 15%nat.
rewrite firstn_all2 by (rewrite length_map; lia). rewrite length_app, length_map. cbn [length]. lia.
Qed.

Lemma rem_sn_bytes : forall nm : list byte, (length nm <= 15)%nat ->
  sn_bytes (16 - 1) (map (fun b : byte => bv_unsigned b) nm) = map (fun b : byte => bv_unsigned b) nm ++ [0].
Proof.
intros nm Hl. unfold sn_bytes. change (Z.to_nat (16 - 1)) with 15%nat.
rewrite firstn_all2 by (rewrite length_map; lia). reflexivity.
Qed.

(* a3 = q *)
Lemma rem_arg3 : forall (regsT : bvmap 5 word) q, getr regsT 13 = w64 q -> 0 <= q < 2 ^ 64 -> argZ regsT 3 = q.
Proof.
intros regsT q Ha3 Hq. change (argZ regsT 3) with (bv_unsigned (getr regsT 13)). rewrite Ha3. unfold w64.
rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia.
Qed.

(* the function's own premises of the snprintf contract at the tail jump *)
Lemma rem_snp_fpre : forall (W : world pa_segs) memT regs regsT p n q (nm : list byte) cval sp0,
  spZ regsT = spZ regs -> spZ regs <= sp0 -> sp0 <= 2 ^ 47 ->
  getr regsT 10 = w64 (p + (MK_NAME + MARK_LEN * n)) -> getr regsT 11 = w64 16 ->
  getr regsT 12 = w64 LA_FMT_S -> getr regsT 13 = w64 q ->
  0 <= n <= 31 -> YCbq.off_img p MK_SIZE ->
  amarks_blk_ok pa_segs regs REMEMBER_AK (mrestrict (w_H W) memT) p ->
  (exists gbs, amarks_at pa_segs (mrestrict (w_H W) memT) p gbs) ->
  acstr_at pa_segs (mrestrict (w_H W) memT) q nm -> (length nm <= 15)%nat ->
  astr_rt_ok pa_segs regs REMEMBER_AK (mrestrict (w_H W) memT) q nm ->
  apart q (Z.of_nat (length nm) + 8) p MK_SIZE ->
  acstr_at pa_segs (mrestrict (w_H W) memT) LA_FMT_S S_FMT_S ->
  astr_rt_ok pa_segs regs REMEMBER_AK (mrestrict (w_H W) memT) LA_FMT_S S_FMT_S ->
  rdword (aview pa_segs (w_H W) memT) LA_GOT_GUARD = Some LA_GUARD ->
  rdword (aview pa_segs (w_H W) memT) LA_GUARD = Some cval ->
  asnprintf_link_fpre pa_segs FF_link LINK_SNP_STK W memT regsT (p + (MK_NAME + MARK_LEN * n)) 16 LA_FMT_S []
    (map (argZ regsT) [3; 4; 5; 6; 7]) (map (fun b : byte => bv_unsigned b) nm) cval.
Proof.
intros W memT regs regsT p n q nm cval sp0 HspT Hwhi H47 Ha0 Ha1 Ha2 Ha3 Hn Htop Hmok Hmat Hqs Hlen Hqrt Hap
  Hfs Hfrt HGOT Hcval.
destruct Hmat as [gbs ((_ & Hwr) & Hgl)]. unfold awrange in Hwr.
pose proof Hmok as (Hp0 & Hpm & Hpra & Hphv & _ & Hpap).
pose proof Hqrt as (Hq0 & Hql & Hqm & Hqra & Hqhv & Hqtl & Hqap).
pose proof Hfrt as (Hf0 & Hfl & Hfm & Hfra & Hfhv & _ & Hfap).
change (length S_FMT_S) with 2%nat in Hfl, Hfm, Hfap.
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
assert (P47 : 2 ^ 47 = 140737488355328) by reflexivity.
assert (P63 : 2 ^ 63 = 9223372036854775808) by reflexivity.
assert (P64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
assert (P31 : 2 ^ 31 = 2147483648) by reflexivity.
assert (HKv : REMEMBER_AK = 8256) by reflexivity. assert (HSTKv : LINK_SNP_STK = 8192) by reflexivity.
assert (HMS : MK_SIZE = 516) by reflexivity.
assert (HTOP : YImgTop.IMG_TOP = 0x654000) by reflexivity.
unfold YCbq.off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in Htop.
assert (HFv : LA_FMT_S = 0x21680) by reflexivity.
assert (Hp_hi : p + 524 <= 2 ^ 47 - 1) by (unfold amem_range in Hpm; rewrite HMS in Hpm; lia).
assert (Hq_hi : q + Z.of_nat (length nm) + 8 <= 2 ^ 47 - 1) by (unfold amem_range in Hqm; lia).
pose proof (str_end_ge q (map (fun b : byte => bv_unsigned b) nm)) as Hse. rewrite length_map in Hse.
pose proof (rem_sn_len nm Hlen) as Hw.
pose proof (rem_arg3 regsT q Ha3 ltac:(lia)) as Harg3.
set (d := p + (MK_NAME + MARK_LEN * n)) in *.
assert (Hd : d = p + (4 + 16 * n)) by reflexivity.
unfold asnprintf_link_fpre. rewrite Hw.
split; [exact Ha0|]. split; [exact Ha1|]. split; [exact Ha2|].
split; [exact HGOT|]. split; [exact Hcval|].
(* va_words at xs = [] *)
split; [split; [rewrite app_nil_r; reflexivity | intros i Hi; cbn [length] in Hi; lia]|].
split; [cbn [length]; lia|].
split.
{ unfold snp_out. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold zdisjoint; cbn [fst snd length].
  - rewrite HSTKv. lia.
  - unfold apart_frame in Hpap. rewrite HKv, HMS in Hpap. lia. }
split.
{ unfold FF_link. exists [37; 115], [Ps], [APtr (map (fun b : byte => bv_unsigned b) nm)].
  split.
  { unfold fmt_at. split; [lia|]. split.
    { intros i Hi. cbn [length] in Hi.
      pose proof (rem_acstr_rd _ _ _ _ Hfs i ltac:(change (length S_FMT_S) with 2%nat; lia)) as E.
      change (map (fun b : byte => bv_unsigned b) S_FMT_S) with [37; 115] in E. exact E. }
    split.
    { unfold snp_out. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold zdisjoint;
        cbn [fst snd length].
      - unfold apart_frame in Hfap. rewrite HKv in Hfap. rewrite HSTKv. lia.
      - lia. }
    split; [eapply rem_amem_sub; [exact Hfm | lia | cbn [length]; lia | cbn [length]; lia]|].
    split; [exact Hfra | exact Hfhv]. }
  split; [reflexivity|].
  split; [apply Forall_cons; [exact I | apply Forall_nil]|].
  split.
  { cbn [map pf_args_asan]. rewrite Harg3. split; [|exact I].
    unfold pf_arg_asan.
    split; [apply rem_bytes_nz; exact (proj2 Hqs)|].
    split; [lia|].
    split; [rewrite length_map; lia|].
    split; [intros i Hi; rewrite length_map in Hi; exact (rem_acstr_rd _ _ _ _ Hqs i Hi)|].
    split; [intros x Hx; unfold str_end in Hx; rewrite length_map in Hx; exact (Hqtl x Hx)|].
    split.
    { unfold snp_out. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold zdisjoint; cbn [fst snd].
      - unfold apart_frame in Hqap. rewrite HKv in Hqap. rewrite HSTKv. lia.
      - unfold apart in Hap. rewrite HMS in Hap. lia. }
    split; [eapply rem_amem_sub; [exact Hqm | lia | lia | rewrite length_map; lia]|].
    split; [rewrite length_map; exact Hqra | rewrite length_map; exact Hqhv]. }
  split; [cbn [pf_text option_map]; rewrite app_nil_r; reflexivity|].
  split; [apply pf_prec_pos_nopps; apply Forall_cons; [discriminate | apply Forall_nil]|].
  split; [unfold LINK_FMT_LO; lia|].
  split; [unfold LINK_FMT_HI, LA_GOT_GUARD; cbn [length]; lia|].
  split; [cbn [map SnFF.pf_args_slack]; rewrite Harg3; split; [|exact I];
          eapply rem_amem_sub; [exact Hqm | lia | lia | lia]|].
  split; [discriminate|].
  cbn [map SnFF.pf_args_amem]. rewrite Harg3. split; [rewrite length_map; exact Hqm | exact I]. }
split; [lia|].
split; [rewrite length_map; lia|].
split; [lia|].
split; [lia|].
split.
{ intros a Ha. split.
  - replace a with (p + (a - p)) by lia. apply Hwr. rewrite Hgl, HMS. lia.
  - unfold apart_frame in Hpap. rewrite HKv, HMS in Hpap. rewrite HSTKv. lia. }
split; [eapply rem_amem_sub; [exact Hpm | lia | lia | rewrite HMS; lia]|].
split; [intros x Hx; exact (Hpra x ltac:(rewrite HMS; lia))|].
split; [apply (rem_hull_sub _ p MK_SIZE); [exact Hphv | lia | lia | rewrite HMS; lia]|].
split; [unfold link_snp_place, YImgTop.IMG_TOP, YImgTop.IMG_LO; lia|].
apply link_snp_rt_cells_of_off. unfold YImgTop.IMG_TOP, YImgTop.IMG_LO. lia.
Qed.

Lemma rem_snp_tail : forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdT k regs regsT raw p n q
    (nm : list byte),
  gx_ok pa_segs B G ->
  ajournal_gx pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdT k ->
  arodata_okP pa_segs PCAP_RLO PCAP_RHI B (aview pa_segs (w_H W) memT) ->
  YK0o.frm_zero (@YK11.fp_csr fx) ->
  spZ regsT = spZ regs -> spZ regs mod 16 = 0 ->
  sp0 - STK <= spZ regs - REMEMBER_AK -> spZ regs <= sp0 ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  getr regsT 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  getr regsT 10 = w64 (p + (MK_NAME + MARK_LEN * n)) -> getr regsT 11 = w64 16 ->
  getr regsT 12 = w64 LA_FMT_S -> getr regsT 13 = w64 q ->
  0 <= n <= 31 ->
  In (p, MK_SIZE) (ablocks B lyc Sc) -> YCbq.off_img p MK_SIZE ->
  amarks_blk_ok pa_segs regs REMEMBER_AK (mrestrict (w_H W) memT) p ->
  (exists gbs, amarks_at pa_segs (mrestrict (w_H W) memT) p gbs) ->
  q <> 0 -> acstr_at pa_segs (mrestrict (w_H W) memT) q nm -> (length nm <= 15)%nat ->
  astr_rt_ok pa_segs regs REMEMBER_AK (mrestrict (w_H W) memT) q nm ->
  apart q (Z.of_nat (length nm) + 8) p MK_SIZE ->
  acstr_at pa_segs (mrestrict (w_H W) memT) LA_FMT_S S_FMT_S ->
  astr_rt_ok pa_segs regs REMEMBER_AK (mrestrict (w_H W) memT) LA_FMT_S S_FMT_S ->
  (forall a, p + (MK_NAME + MARK_LEN * n) <= a < p + (MK_NAME + MARK_LEN * n) + Z.of_nat (length nm) + 1 ->
     ajw B G XO OUT STK sp0 FP ly S lyc Sc own a) ->
  (* the two guard cells (not derivable at an abstract B / PAImg; see the header) *)
  rdword (aview pa_segs (w_H W) memT) LA_GOT_GUARD = Some LA_GUARD ->
  (exists cval, rdword (aview pa_segs (w_H W) memT) LA_GUARD = Some cval) ->
  SRr pa_segs W (mkCfg (mkst regsT (Z_to_bv 64 LA_W_SNPRINTF) memT (seg_rom pa_segs)) mdT)
    (fun W2 c2 => W2 = W /\ exists (fx' : YK11.FPState) regs2 mem2 md2,
       c2 = mkCfg (@YK11.mkst fx' regs2 raw mem2 (seg_rom pa_segs)) md2 /\
       (forall kk : bv 5, bv_unsigned kk <> 10 ->
          Sem.reg_get (@YK11.fp_regs fx') kk = Sem.reg_get (@YK11.fp_regs fx) kk) /\
       YK0o.frm_zero (@YK11.fp_csr fx') /\
       ajournal_gx pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
       aregs_preserved regsT regs2 /\ same_but_materialized mdT md2 /\
       (forall i, 0 <= i <= Z.of_nat (length nm) ->
          aview pa_segs (w_H W) mem2 (p + (MK_NAME + MARK_LEN * n) + i)
            = Some (bv_unsigned (nth (Z.to_nat i) (nm ++ [zb 0]) (zb 0)))) /\
       (forall a, 0 <= a < 2 ^ 64 ->
          ~ (p + (MK_NAME + MARK_LEN * n) <= a < p + (MK_NAME + MARK_LEN * n) + Z.of_nat (length nm) + 1) ->
          ~ (spZ regs - 2 * ESTACK <= a < spZ regs) ->
          aview pa_segs (w_H W) mem2 a = aview pa_segs (w_H W) memT a) /\
       (forall a, 0 <= a < 2 ^ 64 -> apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdT k regs regsT raw p n q nm
  HG HJ HROD Hfrm HspT Hal16 Hwlo Hwhi Hgp Htp Hra Hraw Hraw4k Ha0 Ha1 Ha2 Ha3 Hn Hblk Htop
  Hmok Hmat Hq0 Hqs Hlen Hqrt Hap Hfs Hfrt Hajw HGOT HCAN.
destruct HCAN as [cval Hcval].
assert (HKv : REMEMBER_AK = 8256) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
assert (HSTKv : LINK_SNP_STK = 8192) by reflexivity.
destruct (rem_aj_bounds G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdT k HJ) as (Hceil & H47 & HXO & _).
pose proof (rem_snp_fpre W memT regs regsT p n q nm cval sp0 HspT Hwhi H47 Ha0 Ha1 Ha2 Ha3 Hn Htop Hmok Hmat
  Hqs Hlen Hqrt Hap Hfs Hfrt HGOT Hcval) as HF.
pose proof (rem_sn_len nm Hlen) as Hw.
pose proof (rem_sn_bytes nm Hlen) as Hb.
set (d := p + (MK_NAME + MARK_LEN * n)) in *.
assert (Hd : d = p + (4 + 16 * n)) by reflexivity.
eapply SRr_mono.
{ apply (link_snprintf_journal SK pa_segs B LAWS pa_segs_low PCAP_RLO PCAP_RHI SNP G XO OUT W regsT memT STK sp0 FP
    ly S W0 mem0 md0 own lyc Sc mdT k raw d 16 LA_FMT_S [] (map (argZ regsT) [3; 4; 5; 6; 7])
    (map (fun b : byte => bv_unsigned b) nm) cval HG HJ ltac:(lia) ltac:(lia) ltac:(rewrite HspT; exact Hal16)
    Hra Hraw Hgp Htp HROD HF).
  - intros a Ha. rewrite Hw in Ha. exact (Hajw a ltac:(lia)).
  - exact Hfrm. }
cbv beta. intros W2 c2 _ (-> & fx' & regs2 & mem2 & md2 & -> & HJ2 & Hfp & Hfz & _ & HP2 & Hs & _ & Hby & Hfr & Hpr).
split; [reflexivity|]. exists fx', regs2, mem2, md2.
split; [reflexivity|].
split; [exact Hfp|]. split; [exact Hfz|]. split; [exact HJ2|]. split; [exact HP2|]. split; [exact Hs|].
split.
{ intros i Hi. rewrite (Hby i ltac:(rewrite Hw; lia)). rewrite Hb. f_equal. apply rem_nth_map_bz. }
split.
{ intros a Ha Hn1 Hn2. apply Hfr; [exact Ha | intros Hc; apply Hn1; rewrite Hw in Hc; lia | rewrite HspT; exact Hn2]. }
(* the contract keeps presence but at the destination's bytes inside the image; the marks block is off it *)
intros a Ha Hp. apply (Hpr a Ha Hp). intros [[H1 H2] [H3 H4]]. rewrite Hw in H2.
unfold YCbq.off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in Htop. unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in H3, H4.
assert (HMS : MK_SIZE = 516) by reflexivity. lia.
Qed.

End r.

About rem_strcmp_call.
Print Assumptions rem_strcmp_call.
About rem_snp_tail.
Print Assumptions rem_snp_tail.
