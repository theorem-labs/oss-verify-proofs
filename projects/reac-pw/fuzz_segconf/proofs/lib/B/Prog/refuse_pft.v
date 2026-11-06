(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed and off_img at fuzz_command's ASan image end 0x606000; ajournal no longer keeps footprint (FP) bytes in the image or at or above alloc_ceiling (fp_spares FP a also requires ~ inFP FP a, and the clause for bytes at or above alloc_ceiling outside [sp0 - STK, sp0) requires ~ inFP FP a), awr_byte (and awr_ok) take the start state's side-stack frames as a new parameter and also admit footprint writes to the program's statics as_prog_static in the image, to the caller's stack above sp0 and to those caller frames (awr_prog_or_caller), acall_kept_of_journal, region_kept_stack_sub, awr_byte_present and aj_intrin_at take the matching premises, ajournal_sub_wide composes a callee whose footprint lies in what the caller may write, awr_byte_present_prog and aj_intrin_at_prog take prog_rw for stores to the statics, AR_errno_present gives the errno cell's value from errno_rom, and astack_rd/astack_pres (stack bytes readable/present from sp to the stack top) give a frame chain for any s0 but an aligned sp + 8 (chain_pre_any, achain_any) and carry across an ajournal (astack_rd_journal, astack_pres_journal). *)
(* Modified by Theorem Labs, 2026-10: the malloc/free journal lemmas (aj_free_at, aj_free_at_io, aj_free_null_at, aj_free_null_at_io, aj_malloc_at, aj_malloc_at_io, aj_malloc_at04, aj_malloc_at04_io, aj_malloc, aj_free) no longer take In (call_trace0 ...) (as_universe B); the model laws get the trace length (call_trace_len) and the contracts the event bound. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Reusable/YCbq.v, with its numbers changed; 205 of its 373 lines of code are new or changed and 3177 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/PaRt.v, with its module paths and module names changed; 254 of its 304 lines of code are new or changed and 323 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10-30: copied for image B (fuzz_segconf.asan-ubsan) from lib/A/Prog/refuse_pft.v at commit 781e28832d34 (a sub-lane, commit 24ba8b52b52f) by the image-B refuse walk lane of the image-B G3 walk owner: Require paths (lib/B/Rt, lib/B/Prog, image B's kit copies of the unit owner 694f3575dda2); the VERBATIM local copies of the row texts replaced by the carriers the image-B wrapper-layer owner landed (lib/B/Rt/RtPFShared.v, RtPFCmd.v, RtPFSeg.v), so r_aj_vsnprintf_atSF is stated over RtPFSeg.seg_avsnprintf_icpt_realizes (rt_rom_view in place of consts_view, and that text's four further premises); FFR's text unchanged. *)
(* reac-pw/fuzz_segconf, ASan image A: the snprintf / vsnprintf texts refuse's walk takes (the image-A wrapper-layer owner's
    interface rows 4 and 5, provenance/segi/INTERFACE-A-interceptors.md at commit e45889d6935a), their step
   lemmas through a program walk's journal, and FFR, the one fact refuse's walk assumes of segconf's printf
   grammar. Statement and proof text of the image-A refuse walk lane (the image-A G3 walk owner), 2026-10-30.

   INTERCEPTOR TEXT PENDING the image-A wrapper-layer owner's carriers lib/A/Rt/RtPFShared.v, lib/A/Rt/RtPFCmd.v (RtFormat.v's
   asnprintf_realizes is RtPFCmd.asnprintf_sh, its cmd_asnprintf_realizes at the image's family) and
   lib/A/Rt/RtPFSeg.v (segconf's grammar extension). The blocks marked VERBATIM are byte-exact copies of the
   donor's lines at origin/ossv/recipes 501c0d516c69 (proofs/plugin-hostd/fuzz_command/lib/A/Rt/<file>), so the
   swap to the carriers is a rename (refuse_pft.X -> RtPFShared.X / RtPFCmd.X). The family is a parameter FF of
   type fmt_fam here, where the carriers will fix segconf's (FR_seg); the window K, the image span img_lo .. img_hi
   and the read-only list cr are parameters too, where RtPFCmd.asnprintf_sh fixes fuzz_command's (CMD_SNP_K,
   CMD_IMG_LO, CMD_IMG_HI, CMD_SNP_CR).

   FFR (ffr_family below) is an ASSUMPTION OF THIS LANE, not a released text: "the family FF renders each of
   refuse's 19 formats (the two address prefixes and the 17 refusal formats) at SegModel.fmt's text, given the
   format as an image literal below the GOT word and the arguments as refuse's callers give them". the image-A wrapper-layer owner's
   grammar (RtPFSeg.v) is to discharge exactly this text; it may not stay in the final theorem. *)
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
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* ======== the carriers (the image-B wrapper-layer owner, lib/B/Rt): RtPFShared.v (words_at, snp_out, fmt_fam, sn_bytes, sn_len),
   RtPFCmd.v (row 4: cmd_asnprintf_realizes, which RtPFSeg.seg_asnprintf_realizes takes at FR_seg) and RtPFSeg.v
   (row 5: seg_avsnprintf_icpt_realizes). The image-A file carried verbatim local copies of them; this copy
   Requires the carriers instead (the image-B G3 walk owner 18:2xZ: swap the pending copies). ======== *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtPFupoison RtPFPf RtPFShared RtPFCmd RtPFSeg.

(* ======== FFR: the family fact refuse's walk assumes (an assumption of the image-A refuse walk lane; the image-A wrapper-layer owner's grammar
   is to discharge it) ======== *)
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

(* ======== the snprintf / vsnprintf steps through a program walk's journal ========
   (image B: r_aj_vsnprintf_atSF is stated over RtPFSeg.seg_avsnprintf_icpt_realizes, row 5's final text, which
   asks rt_rom_view where the A file's local copy asked consts_view, and four premises more)
   fuzz_command's cwc_aj_snprintf_atSF (lib/A/Prog/PaRt.v at origin/ossv/recipes 501c0d516c69) with the family FF,
   the window K, the image span img_lo .. img_hi and the read-only list cr as parameters. The step builds the
   contract's ecall_pre_stk from the journal (PaArt.v's ecall_pre_stk_at), its dest_ok from the per-byte awr_byte
   premise (YCbq.v's awr_byte_present), applies the contract, and rebuilds the journal with YCbq.v's
   ajournal_after_write: the call writes its window [sp0 + o - K, sp0 + o), which the journal's stack window holds,
   and the sn_len (n - 1) T bytes it fills, which awr_byte lets the walk write. The FP state comes back related by
   PaFx.v's fxrel (fxrel_of_frm0). The kept clause is the contract's own: every byte outside the written part
   [d, d + sn_len (n - 1) T) and the window reads the same. r_snp_pre and r_snp_post are the parts the two steps
   share: the contract's pre-state, destination and range facts from the journal, and the journal and the kept
   bytes from the contract's post (the two contracts have the same post). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI04 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaArt PaFx.

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

(* snprintf(d, n, f, ...) under the copied row-4 contract (cmd_asnprintf_realizes at FF, K, img_lo .. img_hi, cr):
   the arguments are the five register words a3 .. a7 (no stack arguments) *)
Lemma r_aj_snprintf_atSF : forall (FF : fmt_fam) K gotw guard img_lo img_hi cr pc,
cmd_asnprintf_realizes segs B FF K gotw guard img_lo img_hi cr pc ->
ESTACK <= K -> 0 <= img_lo -> img_hi <= 2 ^ 47 ->
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
img_hi <= d -> img_hi <= sp0 + o - K ->
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
intros FF K gotw guard img_lo img_hi cr pc AP HKe Hil Hih Hcr W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k
d n f T o raw HJ Ha0 Ha1 Ha2 Hn Hd Hdn Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hdest HPC Hamr Hrad Hhull Hdi Hwi
Hguard Hgc0 Hgc1 Hgv0 Hgv1 HFF HT Hcv Hfrm.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (_ & _ & _ & _ & Hshi & H47 & _).
assert (ESTACK = 4096) as Hes by reflexivity.
destruct (r_snp_pre K W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d n T o raw HJ ltac:(lia)
  Hsp' Hal Hneg HKe Hbud Hgp Htp Hra Hraw Hdest HPC Hrad Hhull) as ((HEP & Hslo & Hscr) & Hlen & HDW & HDEST & HRADl & HHULLl).
destruct Hguard as (Hgw & cval & Hcw).
assert (HCR : forall r, In r cr -> img_lo <= fst r /\ 0 <= snd r /\ fst r + snd r <= img_hi)
  by (rewrite Forall_forall in Hcr; exact Hcr).
(* what lies below img_hi is apart from the window and the written part *)
assert (HOUT : forall x w, 0 <= w -> x + w <= img_hi ->
  Forall (zdisjoint (x, w)) (snp_out K (spZ regsT) d (sn_len (n - 1) T))).
{ intros x w Hw Hx. unfold snp_out. rewrite Hsp'.
  apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia|].
  apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia | apply Forall_nil]. }
apply (r_snp_post K pc W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d n T o raw HJ Hra Hsp' Hneg Hbud
  ltac:(lia) (fun a Ha => proj1 (Hdest a Ha))).
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

(* vsnprintf(d, n, f, ap) under the copied row-5 contract (sh_avsnprintf_icpt_realizes at FF, K, img_lo .. img_hi,
   cr): the argument words ws at ap, apart from what the call writes; the read-only list read as the image has it *)
Lemma r_aj_vsnprintf_atSF : forall (FF : fmt_fam) K gotw guard img_lo img_hi cr pc,
seg_avsnprintf_icpt_realizes segs B FF K gotw guard img_lo img_hi cr pc ->
ESTACK <= K -> 0 <= img_lo -> img_hi <= 2 ^ 47 ->
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
img_hi <= d -> img_hi <= sp0 + o - K ->
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
intros FF K gotw guard img_lo img_hi cr pc AP HKe Hil Hih Hcr W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k
d n f ap ws T o raw HJ Ha0 Ha1 Ha2 Ha3 Hn Hd Hdn Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hdest HPC Hamr Hrad Hhull Hdi Hwi
Hguard Hgc0 Hgc1 Hgv0 Hgv1 Hws Hap0 Hap1 Hapd HFF HT Hcv Hsa Hdo Ha47 Ham8 Hfrm.
assert (ESTACK = 4096) as Hes by reflexivity.
destruct (r_snp_pre K W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d n T o raw HJ ltac:(lia)
  Hsp' Hal Hneg HKe Hbud Hgp Htp Hra Hraw Hdest HPC Hrad Hhull) as ((HEP & Hslo & Hscr) & Hlen & HDW & HDEST & HRADl & HHULLl).
destruct Hguard as (Hgw & cval & Hcw).
assert (HCR : forall r, In r cr -> img_lo <= fst r /\ 0 <= snd r /\ fst r + snd r <= img_hi)
  by (rewrite Forall_forall in Hcr; exact Hcr).
(* what lies below img_hi is apart from the window and the written part *)
assert (HOUT : forall x w, 0 <= w -> x + w <= img_hi ->
  Forall (zdisjoint (x, w)) (snp_out K (spZ regsT) d (sn_len (n - 1) T))).
{ intros x w Hw Hx. unfold snp_out. rewrite Hsp'.
  apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia|].
  apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia | apply Forall_nil]. }
apply (r_snp_post K pc W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d n T o raw HJ Hra Hsp' Hneg Hbud
  ltac:(lia) (fun a Ha => proj1 (Hdest a Ha))).
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
End st.
