(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed and off_img at fuzz_command's ASan image end 0x606000; ajournal no longer keeps footprint (FP) bytes in the image or at or above alloc_ceiling (fp_spares FP a also requires ~ inFP FP a, and the clause for bytes at or above alloc_ceiling outside [sp0 - STK, sp0) requires ~ inFP FP a), awr_byte (and awr_ok) take the start state's side-stack frames as a new parameter and also admit footprint writes to the program's statics as_prog_static in the image, to the caller's stack above sp0 and to those caller frames (awr_prog_or_caller), acall_kept_of_journal, region_kept_stack_sub, awr_byte_present and aj_intrin_at take the matching premises, ajournal_sub_wide composes a callee whose footprint lies in what the caller may write, awr_byte_present_prog and aj_intrin_at_prog take prog_rw for stores to the statics, AR_errno_present gives the errno cell's value from errno_rom, and astack_rd/astack_pres (stack bytes readable/present from sp to the stack top) give a frame chain for any s0 but an aligned sp + 8 (chain_pre_any, achain_any) and carry across an ajournal (astack_rd_journal, astack_pres_journal). *)
(* Modified by Theorem Labs, 2026-10: the malloc/free journal lemmas (aj_free_at, aj_free_at_io, aj_free_null_at, aj_free_null_at_io, aj_malloc_at, aj_malloc_at_io, aj_malloc_at04, aj_malloc_at04_io, aj_malloc, aj_free) no longer take In (call_trace0 ...) (as_universe B); the model laws get the trace length (call_trace_len) and the contracts the event bound. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Reusable/YCbq.v, with its numbers changed; 205 of its 373 lines of code are new or changed and 3177 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/PaRt.v, with its module paths and module names changed; 418 of its 454 lines of code are new or changed and 337 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan image A: the parts of the snprintf / vsnprintf calls refuse's walk shares (the
   interceptor lane's interface rows 4 and 5, its interface record at commit e45889d6935a), FFR (the family fact
   refuse's walk uses of segconf's printf grammar) with its proof at the interceptor lane's family FR_seg, and the
   bridge from FFR's premises to row 4's released family FR_cmd at refuse's two address prefixes. Statement and
   proof text of the image-A refuse walk, 2026-10-30.

   The interceptor texts are the released carriers, Required here: lib/A/Rt/RtPFShared.v (words_at, snp_out,
   fmt_fam, sn_bytes, sn_len, fmt_at, pf_arg_asan, str_end), RtPFPf.v (pf_parse, pf_text, pf_dec), RtPFCmd.v for
   row 4 (RtFormat.v's asnprintf_realizes is RtPFCmd.asnprintf_sh, cmd_asnprintf_realizes at FR_cmd, CMD_SNP_K,
   CMD_IMG_LO .. CMD_IMG_HI, CMD_SNP_CR), and RtPFSeg.v, segconf's rows 4 and 5 over its grammar (family FR_seg).
   The walk (lib/A/Prog/refuse_a.v) applies the two rows itself, with r_snp_pre and r_snp_post below for the
   parts the two calls share.

   FFR (ffr_family below) says that a family FF renders each of refuse's 19 formats (the two address prefixes and
   the 17 refusal formats) at SegModel.fmt's text, given the format as an image literal below the GOT word and the
   arguments as refuse's callers give them. It is not an assumption: r_ffr_seg (end of file) proves it at the
   interceptor lane's family RtPFSeg.FR_seg 0x10000 gotw. r_fr_cmd_addr gives row 4's released family FR_cmd
   from FFR's premises at the two address prefixes. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegABase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtPFPf RtPFShared RtPFSx RtPFCmd RtFormat RtPFSeg.

(* ======== FFR: the family fact refuse's walk uses (r_ffr_seg, end of file, proves it at the interceptor
   lane's FR_seg) ======== *)
(* An argument word w of a format, as refuse's callers give it (refuse_c.v's sa_va_args and refuse_va_locs, and
   for the address prefix c->reading or the literal "reac-pw.conf"): a string's bytes (each 1 .. 255), NUL and
   slack, its length, its shadow, its 8 bytes past the NUL in application memory, and its read span apart from the
   regions rs the printf call writes; an integer below 2 ^ 31 in the word itself. *)
Definition ffr_arg (rd : reader) (rs : list (Z * Z)) (w : Z) (x : SegModel.arg) : Prop :=
match x with
| SegModel.AS s =>
    0 < w /\ sa_str rd w s /\ Forall (fun x => 0 < x < 256) s /\ (length s <= 65535)%nat /\
    sa_addr rd w (Z.of_nat (length s) + 1) /\
    amem_range w (Z.of_nat (length s) + 8) /\ Forall (zdisjoint (w, seg_spec.cstr_span w s)) rs
| SegModel.AI z => 0 <= z < 2 ^ 31 /\ w = z
end.
Fixpoint ffr_args (rd : reader) (rs : list (Z * Z)) (ws : list Z) (xs : list SegModel.arg) : Prop :=
match xs, ws with
| [], _ => True
| x :: xs', w :: ws' => ffr_arg rd rs w x /\ ffr_args rd rs ws' xs'
| _ :: _, [] => False
end.
(* The format at f: an image literal (SegABase.sa_lit's reader part) below the GOT word gotw (the place
   fuzz_command's FR_cmd asks, RtPFCmd.v:94-95), its bytes, NUL and slack, its shadow, 8 bytes past its NUL in
   application memory, and its read span apart from rs. *)
Definition ffr_fmt (segs : list Segment) (B : asyms) (gotw : Z) (rd : reader) (rs : list (Z * Z)) (f : Z)
(fmt : list Z) : Prop :=
0x10000 <= f /\ f + Z.of_nat (length fmt) + 1 <= gotw /\
sa_str rd f fmt /\ sa_addr rd f (Z.of_nat (length fmt) + 1) /\ sa_img segs B f (Z.of_nat (length fmt) + 1) /\
amem_range f (Z.of_nat (length fmt) + 8) /\ Forall (zdisjoint (f, seg_spec.cstr_span f fmt)) rs.
(* refuse's 19 formats: the two address prefixes it passes to snprintf and the 17 its callers pass on to
   vsnprintf *)
Definition REFUSE_ALL_FMTS : list (list Z) := SegModel.F_addr_line :: SegModel.F_addr :: seg_spec.REFUSE_FORMATS.
(* FFR: the family renders each of them at SegModel's text *)
Definition ffr_family (segs : list Segment) (B : asyms) (gotw : Z) (FF : fmt_fam) : Prop :=
forall rd rs f fmt ws xs,
In fmt REFUSE_ALL_FMTS -> seg_spec.conv_kinds fmt = map seg_spec.arg_is_s xs ->
ffr_fmt segs B gotw rd rs f fmt -> ffr_args rd rs ws xs ->
FF rd rs f ws (SegModel.fmt fmt xs).

(* ======== the parts of the snprintf / vsnprintf steps through a program walk's journal ========
   From fuzz_command's cwc_aj_snprintf_atSF (lib/A/Prog/PaRt.v at origin/ossv/recipes 501c0d516c69), with the
   window K as a parameter. r_snp_pre builds a row's pre-state from the journal (PaArt.v's ecall_pre_stk_at), its
   dest_ok from the per-byte awr_byte premise (YCbq.v's awr_byte_present), and the range facts at the written
   length; r_snp_post rebuilds the journal from the row's post with YCbq.v's ajournal_after_write: the call writes
   its window [sp0 + o - K, sp0 + o), which the journal's stack window holds, and the sn_len (n - 1) T bytes it
   fills, which awr_byte lets the walk write. The FP state comes back related by PaFx.v's fxrel (fxrel_of_frm0).
   The kept clause is the row's own: every byte outside the written part [d, d + sn_len (n - 1) T) and the window
   reads the same. The two rows have the same post. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI04 YI16 YA0n YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaArt PaFx.

Section st. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.

(* the contract's pre-state at window K, the written length, the written part against the window, dest_ok, and
   the range facts at the written length, from the journal and the step's premises *)
Lemma r_snp_pre : forall K W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d n (T : list Z) (o : Z) raw,
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
1 <= n ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK <= K -> K - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
(forall a, d <= a < d + n -> awr_byte segs B STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) (frames S) lyc own a /\
  ~ (sp0 + o - K <= a < sp0 + o)) ->
(forall a, d <= a < d + n -> inFP FP a -> (Exists (in_zr a) (as_prog_static B) /\ in_img segs a) \/ sp0 <= a < ly_top lyc ->
  writable_at segs (mrestrict (w_H W) memT) a) ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF d n ->
shadow_hull_vis (aview segs (w_H W) memT) d n ->
ecall_pre_stk segs B K lyc Sc W regsT memT mdc /\
1 <= sn_len (n - 1) T <= n /\
(d + sn_len (n - 1) T <= sp0 + o - K \/ sp0 + o <= d) /\
dest_ok segs B lyc Sc W regsT memT d (sn_len (n - 1) T) /\
range_addressable (aview segs (w_H W) memT) SHADOW_OFF d (sn_len (n - 1) T) /\
shadow_hull_vis (aview segs (w_H W) memT) d (sn_len (n - 1) T).
Proof using LAWS segs_low.
intros K W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d n T o raw
HJ Hn Hsp' Hal Hneg HKe Hbud Hgp Htp Hra Hraw Hdest HPC Hrad Hhull.
assert (ESTACK = 4096) as Hes by reflexivity.
assert (Hlen : 1 <= sn_len (n - 1) T <= n).
{ unfold sn_len, sn_bytes. rewrite length_app, length_firstn. cbn [length]. lia. }
split; [eapply ecall_pre_stk_at; try eassumption; first [lia | rewrite Hra; exact Hraw]|].
set (len := sn_len (n - 1) T) in *.
split; [exact Hlen|].
split.
{ destruct (Z_le_gt_dec (sp0 + o) d) as [Hge|Hlt]; [right; exact Hge|left].
  destruct (Z_le_gt_dec (d + len) (sp0 + o - K)) as [Hle|Hgt]; [exact Hle|exfalso].
  destruct (Z_le_gt_dec (sp0 + o - K) d) as [Hd1|Hd1].
  - exact (proj2 (Hdest d ltac:(lia)) ltac:(lia)).
  - exact (proj2 (Hdest (sp0 + o - K) ltac:(lia)) ltac:(lia)). }
split.
{ intros a Ha. destruct (Hdest a ltac:(lia)) as [Hw Hns].
  destruct (awr_byte_present segs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw (HPC a ltac:(lia))) as [Hp Hno].
  split; [exact Hp|]. split; [exact Hno|]. rewrite Hsp'. lia. }
split; [intros x Hx; apply Hrad; lia|].
intros s Hs. apply Hhull. split; [lia|].
assert (E1 : (d + len - 1) / 8 <= (d + n - 1) / 8) by (apply Z.div_le_mono; lia).
unfold shadow_addr in *.
assert (E2 : (SHADOW_OFF + (d + len - 1) / 8) / 8 <= (SHADOW_OFF + (d + n - 1) / 8) / 8) by (apply Z.div_le_mono; lia).
lia.
Qed.

(* the step's post from the contract's (the post both contracts state): the journal again with the same k, the FP
   state related by fxrel, the registers kept, the filled bytes, the kept bytes, present bytes still present *)
Lemma r_snp_post : forall K pc W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d n (T : list Z) (o : Z) raw,
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 1 = raw -> spZ regsT = sp0 + o -> o <= 0 -> K - o <= STK ->
sn_len (n - 1) T <= n ->
(forall a, d <= a < d + n -> awr_byte segs B STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) (frames S) lyc own a) ->
SRr segs W (cfg_at segs pc regsT memT mdc)
(fun W' c' => W' = W /\ exists (fx' : YK11.FPState) regs' mem' md',
c' = @cfg_at fx' segs (raZ regsT) regs' mem' md' /\
(forall r : bv 5, bv_unsigned r <> 10 -> Sem.reg_get (@fp_regs fx') r = Sem.reg_get (@fp_regs fx) r) /\
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx')) 5) 7 = 0 /\
AR segs B lyc Sc W mem' md' /\ aregs_preserved regsT regs' /\ same_but_materialized mdc md' /\
getr regs' 10 = w64 (Z.of_nat (length T)) /\
(forall i, 0 <= i < sn_len (n - 1) T -> aview segs (w_H W) mem' (d + i) = Some (nth (Z.to_nat i) (sn_bytes (n - 1) T) 0)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + sn_len (n - 1) T) ->
~ (spZ regsT - K <= a < spZ regsT) -> aview segs (w_H W) mem' a = aview segs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem' a)) ->
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
intros K pc W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d n T o raw HJ Hra Hsp' Hneg Hbud Hlen Hdest HC.
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HQT).
eapply SRr_mono; [exact HC|].
cbv beta. intros W2 c2 _ (-> & fx1 & regs2 & mem2 & md2 & -> & Hf1 & Hf2 & HAR2 & HP & Hsame & H10 & Hby & Hfr & Hgr).
assert (Hkeep : forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + sn_len (n - 1) T) -> ~ (sp0 + o - K <= a < sp0 + o) ->
  aview segs (w_H W) mem2 a = aview segs (w_H W) memT a).
{ intros a H0 H1 H2. apply (Hfr a H0 H1). rewrite Hsp'. exact H2. }
split; [reflexivity|]. exists fx1, regs2, mem2, md2.
split; [exact (fxrel_of_frm0 fx fx1 Hf1 Hf2)|].
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write segs B LAWS segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
  (fun a => (d <= a < d + sn_len (n - 1) T) \/ (sp0 + o - K <= a < sp0 + o)) Sc own HJ).
  - intros a Ha Hna. apply (Hkeep a Ha); intros H'; apply Hna; [left | right]; exact H'.
  - exact Hgr.
  - exact Hsame.
  - intros a [Ha | Ha]; left; [apply Hdest; lia | left; lia].
  - exact HAR2.
  - reflexivity. - reflexivity. - lia. - exact Hfrs. - exact HQT. }
split; [exact HP|]. split; [exact H10|]. split; [exact Hby|]. split; [exact Hkeep|].
split; [exact Hgr | exact Hsame].
Qed.
End st.

(* ======== the FR_cmd bridge for refuse's two address prefixes ========
   refuse's snprintf calls (0x88f5c, 0x88f74) pass SegModel.F_addr_line ("%s:%d: ") with [AS where; AI line] and
   SegModel.F_addr ("%s: ") with [AS where]; row 4 as released is RtFormat.asnprintf_realizes = RtPFCmd's
   cmd_asnprintf_realizes at FR_cmd. r_fr_cmd_addr gives FR_cmd at SegModel.fmt's text from ffr_fmt and ffr_args
   (at the GOT word CMD_GOTW): the parse of each prefix by computation, its text against SegModel.fmt (cut_nul s = s
   for a NUL-free s, and pf_dec z = SegModel.dec z below 2 ^ 31: the two digit loops agree while their fuel, 11 and
   20, covers the digits), the string argument's pf_arg_asan from ffr_arg (str_end w s - w is seg_spec.cstr_span w s),
   and the slack and amem facts from amem_range w (|s| + 8). *)
Lemma r_pf_digits_dec_go : forall f1 f2 x acc, (1 <= f1)%nat -> (f1 <= f2)%nat -> 0 <= x < 10 ^ Z.of_nat f1 ->
  pf_digits f1 x acc = SegModel.dec_go f2 x acc.
Proof.
induction f1 as [|f1 IH]; intros f2 x acc H1 H12 Hx; [lia|].
destruct f2 as [|f2]; [lia|].
cbn [pf_digits SegModel.dec_go].
destruct (Z.ltb_spec x 10) as [Hlt|Hge].
- rewrite Z.mod_small by lia. reflexivity.
- destruct f1 as [|f1']; [assert (10 ^ Z.of_nat 1 = 10) by reflexivity; lia|].
  apply IH; [lia | lia |].
  rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hx by lia.
  split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.
Lemma r_pf_dec : forall z, 0 <= z < 2 ^ 31 -> pf_dec z = SegModel.dec z.
Proof.
intros z Hz. unfold pf_dec, SegModel.dec. destruct (Z.ltb_spec z 0) as [H|H]; [lia|].
apply r_pf_digits_dec_go; [lia | lia |].
assert (E : 10 ^ Z.of_nat 11 = 100000000000) by reflexivity. rewrite E. lia.
Qed.
Lemma r_str_end_span : forall w s, str_end w s - w = seg_spec.cstr_span w s.
Proof.
intros w s. unfold str_end, seg_spec.cstr_span.
pose proof (Z.div_mod (w + Z.of_nat (length s)) 8 ltac:(lia)) as E1.
pose proof (Z.mod_pos_bound (w + Z.of_nat (length s)) 8 ltac:(lia)) as B1.
rewrite <- (Z.mod_unique (- (w + Z.of_nat (length s) + 1)) 8 (- ((w + Z.of_nat (length s)) / 8) - 1)
  (7 - (w + Z.of_nat (length s)) mod 8)) by lia.
lia.
Qed.
(* the format of ffr_fmt is RtPFShared's fmt_at *)
Lemma r_fmt_at_of_ffr : forall segs B gotw rd rs f fmt, ffr_fmt segs B gotw rd rs f fmt -> fmt_at rd rs f fmt.
Proof.
intros segs B gotw rd rs f fmt (Hf0 & _ & ((Hzs & _) & _) & (_ & _ & Ham & Hra & Hhv) & _ & _ & Hd).
split; [lia|]. split.
- intros i Hi. specialize (Hzs (Z.to_nat i) ltac:(rewrite length_app; cbn [length]; lia)).
  rewrite Z2Nat.id in Hzs by lia. exact Hzs.
- split.
  + rewrite Forall_forall in Hd |- *. intros [x y] Hin. specialize (Hd _ Hin).
    pose proof (Z.mod_pos_bound (- (f + Z.of_nat (length fmt) + 1)) 8 ltac:(lia)).
    unfold zdisjoint, seg_spec.cstr_span in *. cbn [fst snd] in *. lia.
  + split; [exact Ham|]. split; [exact Hra | apply Hhv; lia].
Qed.
(* a string argument of ffr_arg is RtPFShared's pf_arg_asan, with RtPFCmd's slack and amem facts *)
Lemma r_arg_asan_str : forall rd rs w s, ffr_arg rd rs w (SegModel.AS s) ->
  pf_arg_asan rd rs w (APtr s) /\ amem_range w (str_end w s - w) /\ amem_range w (Z.of_nat (length s) + 8) /\
  ~ In 0 s.
Proof.
intros rd rs w s (Hw & ((Hzs & Hnz) & Htl) & Hb & Hlen & (_ & _ & Ham1 & Hra & Hhv) & Ham & Hd).
(* |s| <= 65535 as a Z bound (lia does not read the abstract nat literal) *)
assert (Hl : Z.of_nat (length s) <= 65535).
{ apply Nat2Z.inj_le in Hlen. assert (E : Z.of_nat 65535 = 65535) by (vm_compute; reflexivity).
  rewrite E in Hlen. exact Hlen. }
clear Hlen.
pose proof (Z.mod_pos_bound (w + Z.of_nat (length s)) 8 ltac:(lia)) as Hm.
assert (Hse : Z.of_nat (length s) + 1 <= str_end w s - w <= Z.of_nat (length s) + 8) by (unfold str_end; lia).
split; [|split; [unfold amem_range in *; lia | split; [exact Ham | exact Hnz]]].
split; [exact Hb|]. split; [exact Hw|]. split; [lia|].
split.
{ intros i Hi. specialize (Hzs (Z.to_nat i) ltac:(rewrite length_app; cbn [length]; lia)).
  rewrite Z2Nat.id in Hzs by lia. exact Hzs. }
split; [exact Htl|].
split; [rewrite r_str_end_span; exact Hd|].
split; [exact Ham1|]. split; [exact Hra | apply Hhv; lia].
Qed.
Lemma r_fr_cmd_addr : forall segs B rd rs f fmt ws xs,
In fmt [SegModel.F_addr_line; SegModel.F_addr] -> seg_spec.conv_kinds fmt = map seg_spec.arg_is_s xs ->
ffr_fmt segs B CMD_GOTW rd rs f fmt -> ffr_args rd rs ws xs ->
FR_cmd rd rs f ws (SegModel.fmt fmt xs).
Proof.
intros segs B rd rs f fmt ws xs Hin Hk Hf Ha.
pose proof (r_fmt_at_of_ffr segs B CMD_GOTW rd rs f fmt Hf) as HFA.
destruct Hf as (Hf0 & Hfg & _).
destruct Hin as [<- | [<- | []]].
- assert (Ek : seg_spec.conv_kinds SegModel.F_addr_line = [true; false]) by reflexivity.
  rewrite Ek in Hk.
  destruct xs as [|[s|z0] [|[s2|z] [|x3 xs]]]; cbn [map seg_spec.arg_is_s] in Hk; try discriminate Hk.
  destruct ws as [|w1 [|w2 ws]]; cbn [ffr_args] in Ha; [contradiction | destruct Ha as [_ []] |].
  destruct Ha as (H1 & H2 & _).
  destruct (r_arg_asan_str rd rs w1 s H1) as (A1 & S1 & M1 & N1).
  destruct H2 as [Hz Ew]. subst w2.
  hnf. exists SegModel.F_addr_line, [Ps; PLit 58; Pd; PLit 58; PLit 32], [APtr s; AInt z].
  split; [exact HFA|]. split; [reflexivity|]. split; [apply pf_cmd_piece_all|].
  (* pf_args_asan, cmd_args_slack and cmd_args_amem recurse on the word list: the tail ws is destructed *)
  split; [split; [exact A1 | split; [split; [lia | reflexivity] | destruct ws; exact I]]|].
  split.
  { assert (E : SegModel.fmt SegModel.F_addr_line [SegModel.AS s; SegModel.AI z] =
      SegModel.cut_nul s ++ 58 :: SegModel.dec z ++ [58; 32]) by reflexivity.
    rewrite E, (SegModel.cut_nul_id s N1), <- (r_pf_dec z Hz). reflexivity. }
  split; [exact I|]. split; [unfold CMD_IMG_LO; lia|]. split; [exact Hfg|].
  split; [split; [exact S1 | destruct ws; exact I]|]. split; [intros E; discriminate E|].
  split; [exact M1 | destruct ws; exact I].
- assert (Ek : seg_spec.conv_kinds SegModel.F_addr = [true]) by reflexivity.
  rewrite Ek in Hk.
  destruct xs as [|[s|z0] [|x2 xs]]; cbn [map seg_spec.arg_is_s] in Hk; try discriminate Hk.
  destruct ws as [|w1 ws]; cbn [ffr_args] in Ha; [contradiction|].
  destruct Ha as (H1 & _).
  destruct (r_arg_asan_str rd rs w1 s H1) as (A1 & S1 & M1 & N1).
  hnf. exists SegModel.F_addr, [Ps; PLit 58; PLit 32], [APtr s].
  split; [exact HFA|]. split; [reflexivity|]. split; [apply pf_cmd_piece_all|].
  split; [split; [exact A1 | destruct ws; exact I]|].
  split.
  { assert (E : SegModel.fmt SegModel.F_addr [SegModel.AS s] = SegModel.cut_nul s ++ [58; 32]) by reflexivity.
    rewrite E, (SegModel.cut_nul_id s N1). reflexivity. }
  split; [exact I|]. split; [unfold CMD_IMG_LO; lia|]. split; [exact Hfg|].
  split; [split; [exact S1 | destruct ws; exact I]|]. split; [intros E; discriminate E|].
  split; [exact M1 | destruct ws; exact I].
Qed.

(* ======== FFR proved at the interceptor lane's family FR_seg (lib/A/Rt/RtPFSeg.v) ========
   r_ffr_seg: ffr_family at RtPFSeg.FR_seg 0x10000 gotw. Each of refuse's 19 formats parses under seg_parse into
   pieces of the six kinds refuse's formats use (a literal byte other than '%', %d, %s, %u, %zu, %.24s: r_pk), and
   printing those pieces back (r_unparse) gives the format again; both facts are checked by computation
   (r_fmts_ok). Over such pieces, seg_text at the argument list r_wargs qs xs (APtr s for a string, AU64 z at %zu,
   AInt z at the other integer conversions) is SegModel.fmt's text (r_text_unparse, by induction over the pieces:
   cut_nul s = s for a NUL-free s, and pf_dec z = pf_udec z = SegModel.dec z below 2 ^ 31), and ffr_args gives
   pf_args_asan, cmd_args_slack and cmd_args_amem at those arguments (r_wargs_rel, r_args_rel_facts). *)
Definition r_pk (q : seg_piece) : bool :=
  match q with
  | PRel (PLit b) => negb (b =? 37)
  | PRel Pd | PRel Ps | Pu | Pzu | P24s => true
  | _ => false
  end.
Definition r_tok (q : seg_piece) : list Z :=
  match q with
  | PRel (PLit b) => [b]
  | PRel Pd => [37; 100]
  | PRel Ps => [37; 115]
  | Pu => [37; 117]
  | Pzu => [37; 122; 117]
  | P24s => [37; 46; 50; 52; 115]
  | _ => []
  end.
Fixpoint r_unparse (qs : list seg_piece) : list Z :=
  match qs with [] => [] | q :: qs' => r_tok q ++ r_unparse qs' end.
(* the pf_arg a conversion piece takes for a SegModel argument *)
Definition r_warg (q : seg_piece) (x : SegModel.arg) : pf_arg :=
  match x with
  | SegModel.AS s => APtr s
  | SegModel.AI z => match q with Pzu => AU64 z | _ => AInt z end
  end.
Fixpoint r_wargs (qs : list seg_piece) (xs : list SegModel.arg) : list pf_arg :=
  match qs with
  | [] => []
  | q :: qs' =>
      match q with
      | PRel (PLit _) => r_wargs qs' xs
      | _ => match xs with [] => [] | x :: xs' => r_warg q x :: r_wargs qs' xs' end
      end
  end.
Definition r_xok (x : SegModel.arg) : Prop :=
  match x with SegModel.AS s => ~ In 0 s | SegModel.AI z => 0 <= z < 2 ^ 31 end.

Fixpoint r_zleqb (a b : list Z) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => (x =? y) && r_zleqb a' b'
  | _, _ => false
  end.
Lemma r_zleqb_eq : forall a b, r_zleqb a b = true -> a = b.
Proof.
induction a as [|x a IH]; intros [|y b] H; cbn [r_zleqb] in H.
- reflexivity.
- discriminate H.
- discriminate H.
- apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. subst y. f_equal. exact (IH b H2).
Qed.
(* the format parses into r_pk pieces that print back to it, and it is nonempty *)
Definition r_fmt_okb (fmt : list Z) : bool :=
  match seg_parse fmt with
  | Some qs => forallb r_pk qs && r_zleqb (r_unparse qs) fmt && match fmt with [] => false | _ :: _ => true end
  | None => false
  end.
Lemma r_fmts_ok : forallb r_fmt_okb REFUSE_ALL_FMTS = true.
Proof. vm_compute. reflexivity. Qed.
Lemma r_fmt_of_in : forall fmt, In fmt REFUSE_ALL_FMTS ->
  exists qs, seg_parse fmt = Some qs /\ forallb r_pk qs = true /\ r_unparse qs = fmt /\ fmt <> [].
Proof.
intros fmt Hin. pose proof (proj1 (forallb_forall r_fmt_okb REFUSE_ALL_FMTS) r_fmts_ok fmt Hin) as Hb.
revert Hb. unfold r_fmt_okb. destruct (seg_parse fmt) as [qs|] eqn:Ep; intros Hb; [|discriminate Hb].
apply andb_prop in Hb as [Hb Hne]. apply andb_prop in Hb as [Hq Hu].
exists qs. split; [first [exact Ep | reflexivity]|]. split; [exact Hq|]. split; [exact (r_zleqb_eq _ _ Hu)|].
destruct fmt as [|c f']; [cbn in Hne; discriminate Hne | intros E; discriminate E].
Qed.

Lemma r_pf_udec : forall z, 0 <= z < 2 ^ 31 -> pf_udec z = SegModel.dec z.
Proof.
intros z Hz. unfold pf_udec, SegModel.dec. destruct (Z.ltb_spec z 0) as [H|H]; [lia|].
apply r_pf_digits_dec_go; [lia | lia |].
assert (E : 10 ^ Z.of_nat 20 = 100000000000000000000) by reflexivity. rewrite E. lia.
Qed.

(* the text: over r_pk pieces, seg_text at r_wargs is SegModel.fmt of the printed pieces *)
Lemma r_text_unparse : forall qs xs, forallb r_pk qs = true ->
  seg_spec.conv_kinds (r_unparse qs) = map seg_spec.arg_is_s xs -> Forall r_xok xs ->
  seg_text qs (r_wargs qs xs) = Some (SegModel.fmt (r_unparse qs) xs).
Proof.
induction qs as [|q qs IH]; intros xs Hq Hk Hx.
- destruct xs as [|x xs]; [reflexivity | cbn in Hk; discriminate Hk].
- cbn [forallb] in Hq. apply andb_prop in Hq as [Hq1 Hq].
  destruct q as [[b| | | | | | | ]| | | ]; cbn [r_pk] in Hq1; try discriminate Hq1;
    cbn [r_unparse r_tok app] in Hk |- *.
  + (* a literal byte other than '%' *)
    apply negb_true_iff in Hq1.
    assert (Ek : seg_spec.conv_kinds (b :: r_unparse qs) = seg_spec.conv_kinds (r_unparse qs))
      by (cbn [seg_spec.conv_kinds]; rewrite Hq1; reflexivity).
    assert (Ef : SegModel.fmt (b :: r_unparse qs) xs = b :: SegModel.fmt (r_unparse qs) xs)
      by (cbn [SegModel.fmt]; rewrite Hq1; reflexivity).
    rewrite Ek in Hk. rewrite Ef. cbn [r_wargs seg_text seg_step]. rewrite (IH xs Hq Hk Hx). reflexivity.
  + (* %d *)
    change (seg_spec.conv_kinds (37 :: 100 :: r_unparse qs)) with (false :: seg_spec.conv_kinds (r_unparse qs)) in Hk.
    destruct xs as [|[s|z] xs]; cbn [map seg_spec.arg_is_s] in Hk; try discriminate Hk.
    apply (f_equal (@tl bool)) in Hk. cbn [tl] in Hk.
    pose proof (Forall_inv Hx) as Hz. pose proof (Forall_inv_tail Hx) as Hx'. cbn [r_xok] in Hz.
    change (SegModel.fmt (37 :: 100 :: r_unparse qs) (SegModel.AI z :: xs))
      with (SegModel.dec z ++ SegModel.fmt (r_unparse qs) xs).
    cbn [r_wargs r_warg seg_text seg_step]. rewrite (IH xs Hq Hk Hx'), (r_pf_dec z Hz). reflexivity.
  + (* %s *)
    change (seg_spec.conv_kinds (37 :: 115 :: r_unparse qs)) with (true :: seg_spec.conv_kinds (r_unparse qs)) in Hk.
    destruct xs as [|[s|z] xs]; cbn [map seg_spec.arg_is_s] in Hk; try discriminate Hk.
    apply (f_equal (@tl bool)) in Hk. cbn [tl] in Hk.
    pose proof (Forall_inv Hx) as Hs. pose proof (Forall_inv_tail Hx) as Hx'. cbn [r_xok] in Hs.
    change (SegModel.fmt (37 :: 115 :: r_unparse qs) (SegModel.AS s :: xs))
      with (SegModel.cut_nul s ++ SegModel.fmt (r_unparse qs) xs).
    rewrite (SegModel.cut_nul_id s Hs).
    cbn [r_wargs r_warg seg_text seg_step]. rewrite (IH xs Hq Hk Hx'). reflexivity.
  + (* %u *)
    change (seg_spec.conv_kinds (37 :: 117 :: r_unparse qs)) with (false :: seg_spec.conv_kinds (r_unparse qs)) in Hk.
    destruct xs as [|[s|z] xs]; cbn [map seg_spec.arg_is_s] in Hk; try discriminate Hk.
    apply (f_equal (@tl bool)) in Hk. cbn [tl] in Hk.
    pose proof (Forall_inv Hx) as Hz. pose proof (Forall_inv_tail Hx) as Hx'. cbn [r_xok] in Hz.
    change (SegModel.fmt (37 :: 117 :: r_unparse qs) (SegModel.AI z :: xs))
      with (SegModel.dec z ++ SegModel.fmt (r_unparse qs) xs).
    cbn [r_wargs r_warg seg_text seg_step]. rewrite (IH xs Hq Hk Hx'), (Z.mod_small z (2 ^ 32)) by lia.
    rewrite (r_pf_udec z Hz). reflexivity.
  + (* %zu *)
    change (seg_spec.conv_kinds (37 :: 122 :: 117 :: r_unparse qs))
      with (false :: seg_spec.conv_kinds (r_unparse qs)) in Hk.
    destruct xs as [|[s|z] xs]; cbn [map seg_spec.arg_is_s] in Hk; try discriminate Hk.
    apply (f_equal (@tl bool)) in Hk. cbn [tl] in Hk.
    pose proof (Forall_inv Hx) as Hz. pose proof (Forall_inv_tail Hx) as Hx'. cbn [r_xok] in Hz.
    change (SegModel.fmt (37 :: 122 :: 117 :: r_unparse qs) (SegModel.AI z :: xs))
      with (SegModel.dec z ++ SegModel.fmt (r_unparse qs) xs).
    cbn [r_wargs r_warg seg_text seg_step]. rewrite (IH xs Hq Hk Hx'), (r_pf_udec z Hz). reflexivity.
  + (* %.24s *)
    change (seg_spec.conv_kinds (37 :: 46 :: 50 :: 52 :: 115 :: r_unparse qs))
      with (true :: seg_spec.conv_kinds (r_unparse qs)) in Hk.
    destruct xs as [|[s|z] xs]; cbn [map seg_spec.arg_is_s] in Hk; try discriminate Hk.
    apply (f_equal (@tl bool)) in Hk. cbn [tl] in Hk.
    pose proof (Forall_inv Hx) as Hs. pose proof (Forall_inv_tail Hx) as Hx'. cbn [r_xok] in Hs.
    change (SegModel.fmt (37 :: 46 :: 50 :: 52 :: 115 :: r_unparse qs) (SegModel.AS s :: xs))
      with (firstn 24 (SegModel.cut_nul s) ++ SegModel.fmt (r_unparse qs) xs).
    rewrite (SegModel.cut_nul_id s Hs).
    cbn [r_wargs r_warg seg_text seg_step]. rewrite (IH xs Hq Hk Hx'). reflexivity.
Qed.

(* no r_pk piece is %.*s, so every precision clause holds *)
Lemma r_prec_pos : forall qs, forallb r_pk qs = true -> forall args, seg_prec_pos qs args.
Proof.
induction qs as [|q qs IH]; intros Hq args; [exact I|].
cbn [forallb] in Hq. apply andb_prop in Hq as [Hq1 Hq].
destruct q as [[b| | | | | | | ]| | | ]; cbn [r_pk] in Hq1; try discriminate Hq1.
all: first [exact (IH Hq args) | destruct args as [|a args]; [exact I | exact (IH Hq args)]].
Qed.
Lemma r_seg_pk_all : forall qs, Forall seg_pk qs.
Proof. induction qs as [|q qs IH]; constructor; [destruct q; exact I | exact IH]. Qed.

(* the argument facts: ffr_args gives, word by word, pf_arg_asan and the slack and amem facts at r_wargs *)
Lemma r_xok_of_ffr : forall rd rs xs ws, ffr_args rd rs ws xs -> Forall r_xok xs.
Proof.
intros rd rs. induction xs as [|x xs IH]; intros ws Ha; [constructor|].
destruct ws as [|w ws]; cbn [ffr_args] in Ha; [destruct Ha|]. destruct Ha as [H1 H2].
constructor; [|exact (IH ws H2)].
destruct x as [s|z]; cbn [r_xok]; cbn [ffr_arg] in H1.
- destruct H1 as (_ & ((_ & Hnz) & _) & _). exact Hnz.
- destruct H1 as [Hz _]. exact Hz.
Qed.
Definition r_arg_facts (rd : reader) (rs : list (Z * Z)) (w : Z) (a : pf_arg) : Prop :=
  pf_arg_asan rd rs w a /\
  match a with
  | APtr s => amem_range w (str_end w s - w) /\ amem_range w (Z.of_nat (length s) + 8)
  | _ => True
  end.
Fixpoint r_args_rel (rd : reader) (rs : list (Z * Z)) (ws : list Z) (args : list pf_arg) {struct args} : Prop :=
  match args, ws with
  | [], _ => True
  | a :: args', w :: ws' => r_arg_facts rd rs w a /\ r_args_rel rd rs ws' args'
  | _ :: _, [] => False
  end.
Lemma r_warg_facts : forall rd rs q w x, ffr_arg rd rs w x -> r_arg_facts rd rs w (r_warg q x).
Proof.
intros rd rs q w [s|z] H.
- destruct (r_arg_asan_str rd rs w s H) as (A & S & M & _). cbn [r_warg r_arg_facts]. exact (conj A (conj S M)).
- cbn [ffr_arg] in H. destruct H as [Hz ->].
  destruct q as [[b| | | | | | | ]| | | ]; cbn [r_warg r_arg_facts pf_arg_asan];
    first [split; [split; [lia | reflexivity] | exact I] | split; [reflexivity | exact I]].
Qed.
Lemma r_wargs_rel : forall rd rs qs ws xs, ffr_args rd rs ws xs -> r_args_rel rd rs ws (r_wargs qs xs).
Proof.
intros rd rs qs. induction qs as [|q qs IH]; intros ws xs Ha; [exact I|].
destruct q as [[b| | | | | | | ]| | | ].
1: exact (IH ws xs Ha).
all: destruct xs as [|x xs]; [exact I|];
  destruct ws as [|w ws]; cbn [ffr_args] in Ha; [destruct Ha|];
  destruct Ha as [H1 H2]; split; [apply r_warg_facts; exact H1 | exact (IH ws xs H2)].
Qed.
Lemma r_args_rel_facts : forall rd rs args ws, r_args_rel rd rs ws args ->
  pf_args_asan rd rs ws args /\ cmd_args_slack ws args /\ cmd_args_amem ws args.
Proof.
intros rd rs. induction args as [|a args IH]; intros ws Hr.
- (* pf_args_asan, cmd_args_slack and cmd_args_amem recurse on the word list: ws is destructed *)
  destruct ws; (split; [exact I | split; exact I]).
- destruct ws as [|w ws]; cbn [r_args_rel] in Hr; [destruct Hr|]. destruct Hr as [Ha Hr].
  destruct (IH ws Hr) as (P1 & P2 & P3).
  destruct a as [v|u|s]; cbn [r_arg_facts] in Ha; destruct Ha as [Ha Hx].
  + exact (conj (conj Ha P1) (conj P2 P3)).
  + exact (conj (conj Ha P1) (conj P2 P3)).
  + destruct Hx as [S M]. exact (conj (conj Ha P1) (conj (conj S P2) (conj M P3))).
Qed.

(* FFR at the interceptor lane's family: the formats as image literals in [0x10000, gotw) *)
Lemma r_ffr_seg : forall segs B gotw, ffr_family segs B gotw (RtPFSeg.FR_seg 0x10000 gotw).
Proof.
intros segs B gotw. unfold ffr_family. intros rd rs f fmt ws xs Hin Hk Hf Ha.
destruct (r_fmt_of_in fmt Hin) as (qs & Ep & Hq & Eu & Hne).
pose proof (r_fmt_at_of_ffr segs B gotw rd rs f fmt Hf) as HFA.
destruct Hf as (Hf0 & Hfg & _).
destruct (r_args_rel_facts rd rs (r_wargs qs xs) ws (r_wargs_rel rd rs qs ws xs Ha)) as (A1 & A2 & A3).
unfold RtPFSeg.FR_seg, seg_fam. cbv beta.
exists fmt, qs, (r_wargs qs xs).
split; [exact HFA|]. split; [exact Ep|]. split; [apply r_seg_pk_all|]. split; [exact A1|].
split.
{ rewrite <- Eu. apply r_text_unparse; [exact Hq | rewrite Eu; exact Hk | exact (r_xok_of_ffr rd rs xs ws Ha)]. }
split; [exact (r_prec_pos qs Hq _)|]. split; [exact Hf0|]. split; [exact Hfg|]. split; [exact A2|].
split; [exact Hne | exact A3].
Qed.
