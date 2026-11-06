(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed and off_img at fuzz_command's ASan image end 0x606000; ajournal no longer keeps footprint (FP) bytes in the image or at or above alloc_ceiling (fp_spares FP a also requires ~ inFP FP a, and the clause for bytes at or above alloc_ceiling outside [sp0 - STK, sp0) requires ~ inFP FP a), awr_byte (and awr_ok) take the start state's side-stack frames as a new parameter and also admit footprint writes to the program's statics as_prog_static in the image, to the caller's stack above sp0 and to those caller frames (awr_prog_or_caller), acall_kept_of_journal, region_kept_stack_sub, awr_byte_present and aj_intrin_at take the matching premises, ajournal_sub_wide composes a callee whose footprint lies in what the caller may write, awr_byte_present_prog and aj_intrin_at_prog take prog_rw for stores to the statics, AR_errno_present gives the errno cell's value from errno_rom, and astack_rd/astack_pres (stack bytes readable/present from sp to the stack top) give a frame chain for any s0 but an aligned sp + 8 (chain_pre_any, achain_any) and carry across an ajournal (astack_rd_journal, astack_pres_journal). *)
(* Modified by Theorem Labs, 2026-10: the malloc/free journal lemmas (aj_free_at, aj_free_at_io, aj_free_null_at, aj_free_null_at_io, aj_malloc_at, aj_malloc_at_io, aj_malloc_at04, aj_malloc_at04_io, aj_malloc, aj_free) no longer take In (call_trace0 ...) (as_universe B); the model laws get the trace length (call_trace_len) and the contracts the event bound. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Reusable/YCbq.v, with its numbers changed; 205 of its 373 lines of code are new or changed and 3177 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/PaRt.v, with its module paths and module names changed; 145 of its 189 lines of code are new or changed and 329 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan+UBSan image B (fuzz_segconf.asan-ubsan, pin sha256 c3796c0b38f3...): the snprintf /
   vsnprintf step lemmas of refuse's image-B walk at a destination OFF the image (a sub-lane of a sub-lane,
   the image-B refuse walk lane, the image-B G3 walk owner, 2026-10-30). Proves no function of the binary: no symbolic execution, no machine code.

   rbs_aj_snprintf_atSF and rbs_aj_vsnprintf_atSF are lib/B/Prog/refuse_pft.v's r_aj_snprintf_atSF (line 209) and
   r_aj_vsnprintf_atSF (line 290) with exactly these changes:
   - the premise `img_hi <= d` (the destination ABOVE the image) is replaced by `(d + n <= img_lo \/ img_hi <= d)`
     (the destination OFF the image: refuse's destination is the refusal slot of the reader's heap block c, and
     refuse_c.v's refuse_pre gives only `off_img c 16616`, so the block may lie below the image too);
   - the premises `img_lo <= gotw` and `img_lo <= guard` are added next to `0 <= img_lo`;
   - every other premise, in the same order, and the conclusion are unchanged.
   The row texts (RtPFCmd.cmd_asnprintf_realizes, RtPFSeg.seg_avsnprintf_icpt_realizes) ask only
   `zdisjoint (d, sn_len (n - 1) T) (img_lo, img_hi - img_lo)`; refuse_pft.v used `img_hi <= d` only to keep the
   read-only list cr, the GOT word gotw and the guard cell guard apart from the written part. Here that fact (HOUT)
   asks its range to start at or above img_lo, which cr's Forall and the two added premises give.
   The proofs are refuse_pft.v's, over its shared r_snp_pre / r_snp_post (Required, not copied). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtPFupoison RtPFPf RtPFShared RtPFCmd RtPFSeg.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI04 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaArt PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require refuse_pft.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.

(* snprintf(d, n, f, ...) under row 4 (cmd_asnprintf_realizes at FF, K, img_lo .. img_hi, cr), the destination off
   the image: refuse_pft.r_aj_snprintf_atSF with `img_hi <= d` replaced by `d + n <= img_lo \/ img_hi <= d` and
   `img_lo <= gotw`, `img_lo <= guard` added *)
Lemma rbs_aj_snprintf_atSF : forall (FF : fmt_fam) K gotw guard img_lo img_hi cr pc,
cmd_asnprintf_realizes segs B FF K gotw guard img_lo img_hi cr pc ->
ESTACK <= K -> 0 <= img_lo -> img_lo <= gotw -> img_lo <= guard -> img_hi <= 2 ^ 47 ->
Forall (fun r => img_lo <= fst r /\ 0 <= snd r /\ fst r + snd r <= img_hi) cr ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d n f T (o : Z) raw,
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 d -> getr regsT 11 = w64 n -> getr regsT 12 = w64 f ->
1 <= n < 2 ^ 31 -> 0 < d -> d + n <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> K - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
(forall a, d <= a < d + n -> awr_byte segs B STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) (frames S) lyc own a /\
  ~ (sp0 + o - K <= a < sp0 + o)) ->
(forall a, d <= a < d + n -> inFP FP a -> (Exists (in_zr a) (as_prog_static B) /\ in_img segs a) \/ sp0 <= a < ly_top lyc ->
  writable_at segs (mrestrict (w_H W) memT) a) ->
amem_range d (n + 8) ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF d n ->
shadow_hull_vis (aview segs (w_H W) memT) d n ->
(d + n <= img_lo \/ img_hi <= d) -> img_hi <= sp0 + o - K ->
aguard_ok segs W memT gotw guard -> 0 <= gotw -> gotw + 8 <= img_hi -> 0 <= guard -> guard + 8 <= img_hi ->
FF (aview segs (w_H W) memT) (snp_out K (spZ regsT) d (sn_len (n - 1) T)) f (map (argZ regsT) [3; 4; 5; 6; 7]) T ->
Z.of_nat (length T) < 2 ^ 31 - 1 ->
RtDefs.rt_rom_view segs B W memT ->
frm0 fx ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists (fx1 : YK11.FPState) regs2 mem2 md2, fxrel fx fx1 /\
c2 = mkCfg (@mkst fx1 regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
aregs_preserved regsT regs2 /\
getr regs2 10 = w64 (Z.of_nat (length T)) /\
(forall i, 0 <= i < sn_len (n - 1) T -> aview segs (w_H W) mem2 (d + i) = Some (nth (Z.to_nat i) (sn_bytes (n - 1) T) 0)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + sn_len (n - 1) T) -> ~ (sp0 + o - K <= a < sp0 + o) ->
  aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) /\
same_but_materialized mdc md2).
Proof using LAWS segs_low.
intros FF K gotw guard img_lo img_hi cr pc AP HKe Hil Hlgc Hlgv Hih Hcr W regsT memT STK sp0 FP ly S W0 mem md own lyc
Sc mdc k d n f T o raw HJ Ha0 Ha1 Ha2 Hn Hd Hdn Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hdest HPC Hamr Hrad Hhull Hdi Hwi
Hguard Hgc0 Hgc1 Hgv0 Hgv1 HFF HT Hcv Hfrm.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (_ & _ & _ & _ & Hshi & H47 & _).
assert (ESTACK = 4096) as Hes by reflexivity.
destruct (refuse_pft.r_snp_pre segs B LAWS segs_low K W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d n T o
  raw HJ ltac:(lia) Hsp' Hal Hneg HKe Hbud Hgp Htp Hra Hraw Hdest HPC Hrad Hhull)
  as ((HEP & Hslo & Hscr) & Hlen & HDW & HDEST & HRADl & HHULLl).
destruct Hguard as (Hgw & cval & Hcw).
assert (HCR : forall r, In r cr -> img_lo <= fst r /\ 0 <= snd r /\ fst r + snd r <= img_hi)
  by (rewrite Forall_forall in Hcr; exact Hcr).
(* what lies in [img_lo, img_hi) is apart from the window and the written part *)
assert (HOUT : forall x w, img_lo <= x -> 0 <= w -> x + w <= img_hi ->
  Forall (zdisjoint (x, w)) (snp_out K (spZ regsT) d (sn_len (n - 1) T))).
{ intros x w Hxl Hw Hx. unfold snp_out. rewrite Hsp'.
  apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia|].
  apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia | apply Forall_nil]. }
apply (refuse_pft.r_snp_post segs B LAWS segs_low K pc W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d n T o
  raw HJ Hra Hsp' Hneg Hbud ltac:(lia) (fun a Ha => proj1 (Hdest a Ha))).
apply (AP lyc Sc W regsT memT mdc d n f [] (map (argZ regsT) [3; 4; 5; 6; 7]) T cval HEP).
- exact Hslo.
- exact Hscr.
- exact Ha0. - exact Ha1. - exact Ha2. - exact Hcv.
- apply Forall_forall. intros r Hr. destruct (HCR r Hr) as (H1 & H2 & H3). lia.
- apply Forall_forall. intros [x w] Hr. destruct (HCR (x, w) Hr) as (H1 & H2 & H3). cbn [fst snd] in *.
  apply HOUT; lia.
- exact Hgw. - exact Hcw. - exact Hgc0. - lia. - exact Hgv0. - lia.
- apply HOUT; lia. - apply HOUT; lia.
- split; [rewrite app_nil_r; reflexivity | intros i Hi; cbn [length] in Hi; lia].
- cbn [length]. rewrite Hsp'. lia.
- cbn [length]. unfold snp_out. rewrite Hsp'.
  apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia|].
  apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia | apply Forall_nil].
- exact HFF.
- exact Hn. - exact HT. - exact Hd. - lia.
- unfold snp_out. rewrite Hsp'. cbn [pairwise]. split; [|split; [apply Forall_nil | exact I]].
  apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia | apply Forall_nil].
- exact HDEST.
- unfold amem_range in *; lia.
- exact HRADl. - exact HHULLl.
- unfold zdisjoint. cbn [fst snd]. lia.
- exact Hfrm.
Qed.

(* vsnprintf(d, n, f, ap) under row 5 (seg_avsnprintf_icpt_realizes at FF, K, img_lo .. img_hi, cr), the
   destination off the image: refuse_pft.r_aj_vsnprintf_atSF with `img_hi <= d` replaced by
   `d + n <= img_lo \/ img_hi <= d` and `img_lo <= gotw`, `img_lo <= guard` added *)
Lemma rbs_aj_vsnprintf_atSF : forall (FF : fmt_fam) K gotw guard img_lo img_hi cr pc,
seg_avsnprintf_icpt_realizes segs B FF K gotw guard img_lo img_hi cr pc ->
ESTACK <= K -> 0 <= img_lo -> img_lo <= gotw -> img_lo <= guard -> img_hi <= 2 ^ 47 ->
Forall (fun r => img_lo <= fst r /\ 0 <= snd r /\ fst r + snd r <= img_hi) cr ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d n f ap ws T (o : Z) raw,
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 d -> getr regsT 11 = w64 n -> getr regsT 12 = w64 f -> getr regsT 13 = w64 ap ->
1 <= n < 2 ^ 31 -> 0 < d -> d + n <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> K - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
(forall a, d <= a < d + n -> awr_byte segs B STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) (frames S) lyc own a /\
  ~ (sp0 + o - K <= a < sp0 + o)) ->
(forall a, d <= a < d + n -> inFP FP a -> (Exists (in_zr a) (as_prog_static B) /\ in_img segs a) \/ sp0 <= a < ly_top lyc ->
  writable_at segs (mrestrict (w_H W) memT) a) ->
amem_range d n ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF d n ->
shadow_hull_vis (aview segs (w_H W) memT) d n ->
(d + n <= img_lo \/ img_hi <= d) -> img_hi <= sp0 + o - K ->
aguard_ok segs W memT gotw guard -> 0 <= gotw -> gotw + 8 <= img_hi -> 0 <= guard -> guard + 8 <= img_hi ->
words_at (aview segs (w_H W) memT) ap ws -> 0 <= ap -> ap + 8 * Z.of_nat (length ws) < 2 ^ 63 ->
Forall (zdisjoint (ap, 8 * Z.of_nat (length ws))) (snp_out K (spZ regsT) d (sn_len (n - 1) T)) ->
FF (aview segs (w_H W) memT) (snp_out K (spZ regsT) d (sn_len (n - 1) T)) f ws T ->
Z.of_nat (length T) < 2 ^ 31 - 1 ->
RtDefs.rt_rom_view segs B W memT ->
(* the four premises row 5's text (RtPFSeg.v:211-218) adds: the arguments at or above the call's sp, the destination
   below the window or above the arguments, the arguments below 2 ^ 47, the destination's slack word *)
sp0 + o <= ap -> (d + n <= sp0 + o - K \/ ap + 8 * Z.of_nat (length ws) <= d) -> ap + 8 * Z.of_nat (length ws) <= 2 ^ 47 ->
amem_range d (n + 8) ->
frm0 fx ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists (fx1 : YK11.FPState) regs2 mem2 md2, fxrel fx fx1 /\
c2 = mkCfg (@mkst fx1 regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
aregs_preserved regsT regs2 /\
getr regs2 10 = w64 (Z.of_nat (length T)) /\
(forall i, 0 <= i < sn_len (n - 1) T -> aview segs (w_H W) mem2 (d + i) = Some (nth (Z.to_nat i) (sn_bytes (n - 1) T) 0)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + sn_len (n - 1) T) -> ~ (sp0 + o - K <= a < sp0 + o) ->
  aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) /\
same_but_materialized mdc md2).
Proof using LAWS segs_low.
intros FF K gotw guard img_lo img_hi cr pc AP HKe Hil Hlgc Hlgv Hih Hcr W regsT memT STK sp0 FP ly S W0 mem md own lyc
Sc mdc k d n f ap ws T o raw HJ Ha0 Ha1 Ha2 Ha3 Hn Hd Hdn Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hdest HPC Hamr Hrad Hhull
Hdi Hwi Hguard Hgc0 Hgc1 Hgv0 Hgv1 Hws Hap0 Hap1 Hapd HFF HT Hcv Hsa Hdo Ha47 Ham8 Hfrm.
assert (ESTACK = 4096) as Hes by reflexivity.
destruct (refuse_pft.r_snp_pre segs B LAWS segs_low K W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d n T o
  raw HJ ltac:(lia) Hsp' Hal Hneg HKe Hbud Hgp Htp Hra Hraw Hdest HPC Hrad Hhull)
  as ((HEP & Hslo & Hscr) & Hlen & HDW & HDEST & HRADl & HHULLl).
destruct Hguard as (Hgw & cval & Hcw).
assert (HCR : forall r, In r cr -> img_lo <= fst r /\ 0 <= snd r /\ fst r + snd r <= img_hi)
  by (rewrite Forall_forall in Hcr; exact Hcr).
(* what lies in [img_lo, img_hi) is apart from the window and the written part *)
assert (HOUT : forall x w, img_lo <= x -> 0 <= w -> x + w <= img_hi ->
  Forall (zdisjoint (x, w)) (snp_out K (spZ regsT) d (sn_len (n - 1) T))).
{ intros x w Hxl Hw Hx. unfold snp_out. rewrite Hsp'.
  apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia|].
  apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia | apply Forall_nil]. }
apply (refuse_pft.r_snp_post segs B LAWS segs_low K pc W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d n T o
  raw HJ Hra Hsp' Hneg Hbud ltac:(lia) (fun a Ha => proj1 (Hdest a Ha))).
apply (AP lyc Sc W regsT memT mdc d n f ap ws T cval HEP).
- exact Hslo.
- exact Hscr.
- exact Ha0. - exact Ha1. - exact Ha2. - exact Ha3. - exact Hcv.
- apply Forall_forall. intros r Hr. destruct (HCR r Hr) as (H1 & H2 & H3). lia.
- apply Forall_forall. intros [x w] Hr. destruct (HCR (x, w) Hr) as (H1 & H2 & H3). cbn [fst snd] in *.
  apply HOUT; lia.
- exact Hgw. - exact Hcw. - exact Hgc0. - lia. - exact Hgv0. - lia.
- apply HOUT; lia. - apply HOUT; lia.
- exact Hws. - exact Hap0. - exact Hap1. - exact Hapd.
- exact HFF.
- exact Hn. - exact HT. - exact Hd. - lia.
- unfold snp_out. rewrite Hsp'. cbn [pairwise]. split; [|split; [apply Forall_nil | exact I]].
  apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia | apply Forall_nil].
- exact HDEST.
- unfold amem_range in *; lia.
- exact HRADl. - exact HHULLl.
- unfold zdisjoint. cbn [fst snd]. lia.
- exact Hfrm.
- rewrite Hsp'. exact Hsa.
- rewrite Hsp'. destruct Hdo as [Hq | Hq]; [left | right]; lia.
- exact Ha47.
- unfold amem_range in *; lia.
Qed.
End s.
