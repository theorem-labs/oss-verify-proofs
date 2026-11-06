(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed and off_img at fuzz_command's ASan image end 0x606000; ajournal no longer keeps footprint (FP) bytes in the image or at or above alloc_ceiling (fp_spares FP a also requires ~ inFP FP a, and the clause for bytes at or above alloc_ceiling outside [sp0 - STK, sp0) requires ~ inFP FP a), awr_byte (and awr_ok) take the start state's side-stack frames as a new parameter and also admit footprint writes to the program's statics as_prog_static in the image, to the caller's stack above sp0 and to those caller frames (awr_prog_or_caller), acall_kept_of_journal, region_kept_stack_sub, awr_byte_present and aj_intrin_at take the matching premises, and AR_errno_present gives the errno cell's value from errno_rom. *)
(* Modified by Theorem Labs, 2026-10: the malloc/free journal lemmas (aj_free_at, aj_free_at_io, aj_free_null_at, aj_free_null_at_io, aj_malloc_at, aj_malloc_at_io, aj_malloc_at04, aj_malloc_at04_io, aj_malloc, aj_free) no longer take In (call_trace0 ...) (as_universe B); the model laws get the trace length (call_trace_len) and the contracts the event bound. *)
(* Modified by Theorem Labs, 2026-10: only aj_malloc_at04 (lib/Reusable/YCbq.v) and amalloc04_rule_triv (lib/Reusable/YCbp.v), restated for fuzz_command's strndup entry: the contract astrndup_realizes (lib/A/Rt/RtAlloc.v) in place of amalloc_realizes, its trace adup_trace with the length bound adup_trace_len, the entry's string premises and the premises on its source (a live block holds the prefix it reads, and no errno byte is in it), the copied bytes in the post, and the rule astrndup04_rule (lib/A/Rt/RtAlloc04.v). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI08 YN3v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG08 YCbq YI16 YC5d YCbp.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtAlloc RtAlloc04.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* The rule a program walk uses at a call of strndup (RtAlloc04.v astrndup04_rule), closed from the entry contract
   (RtAlloc.v astrndup_realizes) and the model laws, as cgif_file_fuzzer closes amalloc04_rule from amalloc_realizes
   (YCbq.v aj_malloc_at04, YCbp.v amalloc04_rule_triv).

   The meter is ameter_triv, as in YCbp: every program walk that takes this rule takes its meter as a Section
   Variable (lib/A/Prog/verbs_receive_c.v), and ameter_triv is the only meter this unit defines. For a meter given
   only by ameter_laws the rule is not provable: mo_le MT Sc S2 (mo_malloc MT n) is then any relation between the
   states before and after the allocation, and the laws say nothing of a malloc step.

   The contract names three program counters, the rule two: [mid] (the malloc entry's own return address in the
   unwinder's trace, adup_trace) shows only in the trace the model records, and the rule's post does not name that
   trace, so the rule holds for every [mid] the contract is given with (RtAPI.v: PC_STRNDUP_RA0, PC_STRNDUP_MID). *)

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis errno_low : api_env segs B.
Hypothesis LAWS : AR_laws segs B.
Hypothesis ML : model_laws (as_universe B).

(* adup_trace is at most kUnwindMax long, as call_trace is (YG0d.v call_trace_len): the model admits it under the
   event bound alone. The first case of adup_trace is the one-element trace the unwinder records when the malloc
   body's frame pointer is out of the stack or the return address is below a page (RtAlloc.v:92-97). *)
Lemma adup_trace_len : forall ly pc0 mid regs ch, (length (adup_trace ly pc0 mid regs ch) <= kUnwindMax)%nat.
Proof.
intros ly pc0 mid regs ch. unfold adup_trace.
destruct ((spZ regs - STRNDUP_FRAME <=? ly_bot ly) || (ly_top ly - 16 <=? spZ regs - STRNDUP_FRAME) || (mid <? 4096))%bool;
[cbn [length]; unfold kUnwindMax; lia|].
destruct (frame0_ok ly regs); unfold unwind_of_chain; apply firstn_le_length.
Qed.

(* One call of strndup as one step of the caller's journal: aj_malloc_at04 with the contract of the entry. *)
Lemma aj_strndup_at04 : forall pc pc_ra0 mid, astrndup_realizes segs B pc pc_ra0 mid ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x m buf (o : Z) raw ch,
let kk := PStrFun.strnlen_res m buf in
let n := kk + 1 in
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 x -> getr regsT 11 = w64 m -> 0 <= m < 2 ^ 32 -> 0 < x ->
abytes_atR (aview segs (w_H W) memT) x buf ->
PStrFun.memchr_ok x 0 m buf ->
aread_ok segs ASTACK W regsT memT x (Z.min n (Z.of_nat (length buf))) ->
(exists p mm, In (p, mm) (ablocks B lyc Sc) /\ p <= x /\ x + Z.min n (Z.of_nat (length buf)) <= p + req_size mm) ->
~ (exists a, x <= a < x + Z.min n (Z.of_nat (length buf)) /\ aerrno_cell B a) ->
rt_rom_view segs B W memT ->
0 <= n < MALLOC_MAX -> blocks_bytes Sc + n <= LIVE_MAX ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
st_nev Sc < EV_MAX ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal segs B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + 1) /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] /\
acall_kept segs B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => res <= a < res + req_size n) /\
abytes_atR (aview segs (w_H W2) mem2) res (firstn (Z.to_nat kk) buf ++ [Z_to_bv 8 0])).
Proof.
intros pc pc_ra0 mid ANDUP W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x m buf o raw ch.
cbv zeta.
intros HJ Hx Hm Hmr Hx0 Hbuf Hmc Hrd Hsrc Herr Hrom Hn Hlive Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hev Hch.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (proj1 errno_low) as [He0 He1].
assert (ASTACK = 16384) as Has by reflexivity.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (HstkC : astk_ok ASTACK lyc (spZ regsT)).
{ unfold astk_ok, ly_bot in *. rewrite Hsp', Eslo, Eshi, Etop. repeat split; try zlia.
all: rewrite Z.add_mod, Hal16, Hal by zlia; reflexivity. }
assert (HPRE : acall_pre segs B lyc Sc W regsT memT mdc ch).
{ destruct HstkC as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
split; [exact HAR|]. split; [exact (aregime_small _ Hev)  |]. split; [rewrite Hra; exact Hraw|].
split; [exact Q1|]. split; [zlia|]. split; [zlia|]. split; [zlia|].
split; [intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia|].
split; [exact Hgp|]. split; [exact Htp|]. split; [exact Hch | exact (conj HQT (mroom_of_regime (as_universe B) Sc (am_wf _ _ _ _ (proj1 HAR)) (aregime_to_mid Sc (aregime_small _ Hev)) (qtight_qloose Sc HQT)))]. }
pose proof (am_wf _ _ _ _ (proj1 HAR)) as HWF.
pose proof (ml_malloc_ns _ ML Sc (PStrFun.strnlen_res m buf + 1) (adup_trace lyc pc_ra0 mid regsT ch) HWF (or_introl Hev) Hn Hlive
(or_intror (conj (adup_trace_len lyc pc_ra0 mid regsT ch) Hev))) as HTOK.
assert (Hn' : PStrFun.strnlen_res m buf + 1 < MALLOC_MAX) by lia.
pose proof (ANDUP lyc Sc W regsT memT mdc x m buf ch HPRE Hx Hm Hmr Hx0 (proj1 (abytes_atR_view segs W memT x buf) Hbuf)
Hmc Hrd Hsrc Herr Hrom Hn' Hlive (or_intror Hev)) as HREAL.
eapply SRr_mono.
{ exact (amreal_SRr04 segs _ W _ _ HREAL (atok_asafe _ _ _ HTOK) (atok_agprog _ _ _ HTOK) (atok_nospin _ _ HTOK)). }
intros W2 c2 HwleW (r & tr & Hpath & Hgf & Hleaf).
pose proof (atok_apath_flag _ _ _ tr r HTOK Hpath) as [HQ HNS]. rewrite (last_flag_true tr Hgf) in HNS.
destruct r as [p S2]. unfold malloc_post in HQ.
destruct HQ as (HWF2 & Hnev2 & Hsecs2 & Hfrs2 & Hbl & _). cbn [fst snd] in *.
destruct Hleaf as (ly2 & regs2 & mem2 & md2 & -> & HPOST & Hres & HQT2 & HBY).
pose proof HPOST as (HAR2 & Hly2 & Hwle2' & HP & Hio2 & Hfr2 & Hpres2).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly2 HAR Hly2) as (Eab & Efa & Eown).
set (f2 := fun b : sptr * Z => (sptr_addr B ly2 (fst b), snd b)).
set (fc := fun b : sptr * Z => (sptr_addr B lyc (fst b), snd b)).
assert (Efc : forall b, In b (blocks Sc) -> f2 b = fc b).
{ intros b Hb. exact (map_eq_In f2 fc (blocks Sc) b Eab Hb). }
assert (Hsecsle : (length (st_secs Sc) <= length (st_secs S2))%nat) by exact (secs_ext_length _ _ Hsecs2).
destruct (asptr_null_dec p) as [-> | Hnn].
-
exfalso. discriminate (HNS eq_refl).
-
assert (Hbl' : blocks S2 = blocks Sc ++ [(p, PStrFun.strnlen_res m buf + 1)] /\ ~ In p (map fst (blocks Sc))).
{ destruct p; [exfalso; exact (Hnn eq_refl) | exact Hbl | exact Hbl | exact Hbl]. }
clear Hbl. destruct Hbl' as [Hbl Hfresh].
set (res := sptr_addr B ly2 p) in *.
assert (Eab2 : ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, PStrFun.strnlen_res m buf + 1)]).
{ unfold ablocks. change (map f2 (blocks S2) = map fc (blocks Sc) ++ [(res, PStrFun.strnlen_res m buf + 1)]).
rewrite Hbl, map_app. cbn [map]. f_equal. apply map_ext_in. exact Efc. }
assert (Hnew : In (res, PStrFun.strnlen_res m buf + 1) (ablocks B ly2 S2)) by (rewrite Eab2; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 res _ HAR2 Hnew) as (_ & Hr4096 & _).
assert (Hdisj : forall b mm a, In (b, mm) (ablocks B lyc Sc) -> b <= a < b + req_size mm ->
~ (res <= a < res + req_size (PStrFun.strnlen_res m buf + 1))).
{ intros b mm a Hb Hr HE. apply in_split in Hb as (b1 & b2 & Ebq).
pose proof (sep_blocks_pos segs B LAWS ly2 S2 W2 mem2 md2 (b, mm) (res, PStrFun.strnlen_res m buf + 1) b1 b2 [] HAR2
ltac:(rewrite Eab2, Ebq, <- app_assoc; reflexivity)) as Hd.
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. zlia. }
assert (HJ1 : ajournal segs B ASTACK (spZ regsT) [] lyc Sc W memT mdc [] ly2 S2 W2 mem2 md2 1).
{ eapply (acall_post_journal segs B LAWS segs_low errno_low);
[exact HPOST | exact HAR | exact HstkC | exact Hfrs2 | zlia | zlia | exact Hsecsle | | | exact HQT2].
- intros a [_ Ha]. exists res, (PStrFun.strnlen_res m buf + 1). split; [right; exact Hnew|]. split; [exact Ha|]. right.
intros Hold. exact (Hdisj res _ a Hold Ha Ha).
- intros q mm i Hq Hnq Hi. exfalso. apply Hnq. rewrite Eab2. apply in_or_app. left. exact Hq. }
exists ly2, S2, regs2, mem2, md2, res.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ rewrite Hsp' in HJ1. change own with ([] ++ own); eapply (ajournal_sub segs B LAWS segs_low);
[exact HJ | exact HJ1 | zlia | zlia | intros a (rg & [] & _)]. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hfrs2|]. split; [exact Hr4096|]. split; [exact Eab2|].
split.
{ rewrite Hsp' in HJ1. eapply (acall_kept_of_journal segs B LAWS segs_low);
[exact HJ1 | exact HAR | intros a (rg & [] & _) | | exact sink_closed_nil | intros a (rg & [] & _)].
intros b mm i Hb Hi _. rewrite Eab2. apply in_or_app. left. exact Hb. }
exact (proj2 (abytes_atR_view segs W2 mem2 res _) (HBY Hnn)).
Qed.

(* The rule, for the meter the program walks are closed with. *)
Theorem astrndup04_rule_triv : forall pc pc_ra0 mid,
astrndup_realizes segs B pc pc_ra0 mid -> astrndup04_rule segs B ameter_triv pc pc_ra0.
Proof.
intros pc pc_ra0 mid ANDUP W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x m buf o raw ch.
cbv zeta.
intros HJ Hx Hm Hmr Hx0 Hbuf Hmc Hrd Hsrc Herr Hrom Hn Hlive Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hev Hch _.
eapply SRr_mono; [exact (aj_strndup_at04 pc pc_ra0 mid ANDUP W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x m buf o raw ch
HJ Hx Hm Hmr Hx0 Hbuf Hmc Hrd Hsrc Herr Hrom Hn Hlive Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hev Hch)|].
cbn beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & res & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
exists ly2, S2, regs2, mem2, md2, res. repeat (split; [assumption|]). exact I.
Qed.

End b.
