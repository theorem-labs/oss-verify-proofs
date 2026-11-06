(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed and off_img at fuzz_command's ASan image end 0x606000; ajournal no longer keeps footprint (FP) bytes in the image or at or above alloc_ceiling (fp_spares FP a also requires ~ inFP FP a, and the clause for bytes at or above alloc_ceiling outside [sp0 - STK, sp0) requires ~ inFP FP a), awr_byte (and awr_ok) take the start state's side-stack frames as a new parameter and also admit footprint writes to the program's statics as_prog_static in the image, to the caller's stack above sp0 and to those caller frames (awr_prog_or_caller), acall_kept_of_journal, region_kept_stack_sub, awr_byte_present and aj_intrin_at take the matching premises, ajournal_sub_wide composes a callee whose footprint lies in what the caller may write, awr_byte_present_prog and aj_intrin_at_prog take prog_rw for stores to the statics, AR_errno_present gives the errno cell's value from errno_rom, and astack_rd/astack_pres (stack bytes readable/present from sp to the stack top) give a frame chain for any s0 but an aligned sp + 8 (chain_pre_any, achain_any) and carry across an ajournal (astack_rd_journal, astack_pres_journal). *)
(* Modified by Theorem Labs, 2026-10: the malloc/free journal lemmas (aj_free_at, aj_free_at_io, aj_free_null_at, aj_free_null_at_io, aj_malloc_at, aj_malloc_at_io, aj_malloc_at04, aj_malloc_at04_io, aj_malloc, aj_free) no longer take In (call_trace0 ...) (as_universe B); the model laws get the trace length (call_trace_len) and the contracts the event bound. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Reusable/YCbq.v, with its numbers changed; 205 of its 373 lines of code are new or changed and 3177 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/PaRt.v, with its module paths and module names changed; 430 of its 480 lines of code are new or changed and 323 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3): the helper lemmas of segment B11a's
   RBT cut (lib/B/Prog/pf_seg_B11a_h.v): the snprintf step through the walk's journal and the record after
   snprintf(cur->model, 24, "%s", low) at 0x88a04; the B11a segment lane of the image-B G3 walk owner (a piece sub-lane), 2026-10-30.
   proves no function (kind: segment lemma of reac_segconf_parse_file's walk, helpers of B11a's RBT cut)
   Pure helper lemmas, no machine run of the segment.

   ADAPTED from a working branch + U piece walks; templates lib/B/Prog/pf_seg_B3_t.v (the B3 segment lane,
   a lane branch 151b4054f431: the snprintf step b3t_*, copied here with the prefix b11ht_, module paths
   unchanged: image B's kit and Rt carriers) and lib/B/Prog/pf_seg_B11a_f.v's b11f_rconf_model (the record update
   through the three model windows, here through the one window the first snprintf writes).
   - b11ht_snp_pre, b11ht_snp_post, b11ht_aj_snprintf_FF, b11ht_aj_snprintf_atSF: the snprintf step at row 4
     (RtFormat.asnprintf_realizes = RtPFCmd.asnprintf_sh) through YCbq.ajournal;
   - b11ht_FR_s / b11ht_FR_s_regs: FR_cmd at "%s" with one string argument;
   - b11ht_rseg_model1 / b11ht_rconf_model1: the record after the model field of entry gi is written with the C
     string T and its NUL (|T| < 24), every other byte of c kept: r_upd cf gi (b11_set_model T). *)
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

From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtPFPf RtPFShared RtPFSx RtPFCmd RtFormat.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI04 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaArt PaFx.

(* ======== row 4's closed facts ======== *)
Lemma b11ht_K_estack : ESTACK <= CMD_SNP_K.
Proof. unfold CMD_SNP_K, ESTACK. lia. Qed.
Lemma b11ht_img_lo_0 : 0 <= CMD_IMG_LO.
Proof. unfold CMD_IMG_LO. lia. Qed.
Lemma b11ht_img_hi_47 : CMD_IMG_HI <= 2 ^ 47.
Proof. unfold CMD_IMG_HI, kImgEnd. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma b11ht_cr_img : Forall (fun r => CMD_IMG_LO <= fst r /\ 0 <= snd r /\ fst r + snd r <= CMD_IMG_HI) CMD_SNP_CR.
Proof.
unfold CMD_SNP_CR, CMD_IMG_LO, CMD_IMG_HI, kImgEnd.
repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia.
Qed.
(* off_img of a range holds of every subrange (a caller narrows a block's or a frame's off_img to the written part) *)
Lemma b11ht_off_img_sub : forall a n a' n', YCbq.off_img a n -> a <= a' -> 0 <= n' -> a' + n' <= a + n ->
  YCbq.off_img a' n'.
Proof. intros a n a' n' H H1 H2 H3. unfold YCbq.off_img in *. lia. Qed.

(* ======== the format "%s" ======== *)
Lemma b11ht_F_s_len : Z.of_nat (length SegModel.F_s) = 2.
Proof. vm_compute. reflexivity. Qed.
Lemma b11ht_parse_F_s : pf_parse SegModel.F_s = Some [Ps].
Proof. vm_compute. reflexivity. Qed.

(* str_end's span is seg_spec.cstr_span (r_str_end_span of refuse_pft.v) *)
Lemma b11ht_str_end_span : forall w s, str_end w s - w = seg_spec.cstr_span w s.
Proof.
intros w s. unfold str_end, seg_spec.cstr_span.
pose proof (Z.div_mod (w + Z.of_nat (length s)) 8 ltac:(lia)) as E1.
pose proof (Z.mod_pos_bound (w + Z.of_nat (length s)) 8 ltac:(lia)) as B1.
rewrite <- (Z.mod_unique (- (w + Z.of_nat (length s) + 1)) 8 (- ((w + Z.of_nat (length s)) / 8) - 1)
  (7 - (w + Z.of_nat (length s)) mod 8)) by lia.
lia.
Qed.

(* the bytes of a string sa_str reads, over a reader whose values are bytes, are 1 .. 255 *)
Lemma b11ht_bytes_range : forall (rd : reader) (p : Z) (l : list Z),
  sa_str rd p l -> (forall a v, rd a = Some v -> 0 <= v < 256) -> Forall (fun c => 0 < c < 256) l.
Proof.
intros rd p l ((Hzs & Hn0) & _) Hrng.
apply Forall_forall. intros c Hc.
destruct (In_nth l c 0 Hc) as [i [Hi Hn]].
assert (Hi' : (i < length (l ++ [0%Z]))%nat) by (rewrite length_app; cbn [length]; lia).
specialize (Hzs i Hi'). rewrite app_nth1 in Hzs by exact Hi. rewrite Hn in Hzs.
pose proof (Hrng _ _ Hzs) as R.
assert (c <> 0) by (intros ->; exact (Hn0 Hc)).
lia.
Qed.
(* the same over the ASan reader (SegABase.sa_aview_rng) *)
Lemma b11ht_bytes_range_aview : forall segs H mem p l,
  sa_str (aview segs H mem) p l -> Forall (fun c => 0 < c < 256) l.
Proof. intros segs H mem p l Hs. exact (b11ht_bytes_range _ p l Hs (sa_aview_rng segs H mem)). Qed.

(* FR_cmd at "%s" with one string argument s at w: the format literal at fp (its bytes and NUL from sa_str, its amem
   and shadow from sa_addr, below the GOT word CMD_GOTW), the argument's bytes, NUL and slack word (sa_str), its
   amem and shadow (sa_addr), 8 bytes past its NUL in application memory, and both read spans apart from rs *)
Lemma b11ht_FR_s : forall (rd : reader) (rs : list (Z * Z)) (fp w : Z) (s : list Z) (r1 r2 r3 r4 : Z),
  0 < fp -> CMD_IMG_LO <= fp -> fp + 3 <= CMD_GOTW ->
  sa_str rd fp SegModel.F_s -> sa_addr rd fp 3 ->
  Forall (zdisjoint (fp, 3)) rs ->
  0 < w -> Forall (fun c => 0 < c < 256) s -> Z.of_nat (length s) + 8 < 2 ^ 31 ->
  sa_str rd w s -> sa_addr rd w (Z.of_nat (length s) + 1) ->
  amem_range w (Z.of_nat (length s) + 8) ->
  Forall (zdisjoint (w, seg_spec.cstr_span w s)) rs ->
  FR_cmd rd rs fp [w; r1; r2; r3; r4] s.
Proof.
intros rd rs fp w s r1 r2 r3 r4 Hf0 Hflo Hfg ((Hfz & _) & _) (_ & _ & Hfam & Hfra & Hfhv) Hfd
  Hw Hb Hl ((Hzs & _) & Htl) (_ & _ & Ham1 & Hra & Hhv) Ham Hd.
pose proof b11ht_F_s_len as EF.
assert (E3 : Z.of_nat (length SegModel.F_s) + 1 = 3) by (rewrite EF; reflexivity).
pose proof (Z.mod_pos_bound (w + Z.of_nat (length s)) 8 ltac:(lia)) as Hm.
unfold FR_cmd. exists SegModel.F_s, [Ps], [APtr s].
split.
{ (* fmt_at *)
  split; [exact Hf0|]. rewrite E3. split.
  - intros i Hi. specialize (Hfz (Z.to_nat i) ltac:(rewrite length_app; cbn [length]; lia)).
    rewrite Z2Nat.id in Hfz by lia. exact Hfz.
  - split; [exact Hfd|]. split; [exact Hfam|]. split; [exact Hfra | apply Hfhv; lia]. }
split; [exact b11ht_parse_F_s|].
split; [apply pf_cmd_piece_all|].
split.
{ (* pf_args_asan: the one string argument *)
  split; [|exact I].
  split; [exact Hb|]. split; [exact Hw|]. split; [exact Hl|].
  split.
  { intros i Hi. specialize (Hzs (Z.to_nat i) ltac:(rewrite length_app; cbn [length]; lia)).
    rewrite Z2Nat.id in Hzs by lia. exact Hzs. }
  split; [exact Htl|].
  split; [rewrite b11ht_str_end_span; exact Hd|].
  split; [exact Ham1|]. split; [exact Hra | apply Hhv; lia]. }
split; [cbn [pf_text option_map]; rewrite app_nil_r; reflexivity|].
split; [exact I|].
split; [exact Hflo|].
split; [lia|].
split; [split; [unfold amem_range, str_end in *; lia | exact I]|].
split; [intros E; discriminate E|].
split; [exact Ham | exact I].
Qed.

(* the same at the step's argument words map (argZ regs) [3; 4; 5; 6; 7], with a3 = w *)
Lemma b11ht_FR_s_regs : forall (rd : reader) (rs : list (Z * Z)) (fp w : Z) (s : list Z) (regs : bvmap 5 word),
  argZ regs 3 = w ->
  0 < fp -> CMD_IMG_LO <= fp -> fp + 3 <= CMD_GOTW ->
  sa_str rd fp SegModel.F_s -> sa_addr rd fp 3 ->
  Forall (zdisjoint (fp, 3)) rs ->
  0 < w -> Forall (fun c => 0 < c < 256) s -> Z.of_nat (length s) + 8 < 2 ^ 31 ->
  sa_str rd w s -> sa_addr rd w (Z.of_nat (length s) + 1) ->
  amem_range w (Z.of_nat (length s) + 8) ->
  Forall (zdisjoint (w, seg_spec.cstr_span w s)) rs ->
  FR_cmd rd rs fp (map (argZ regs) [3; 4; 5; 6; 7]) s.
Proof.
intros rd rs fp w s regs E3. cbn [map]. rewrite E3.
exact (b11ht_FR_s rd rs fp w s (argZ regs 4) (argZ regs 5) (argZ regs 6) (argZ regs 7)).
Qed.

(* ======== the snprintf step through a program walk's journal ========
   the image-A refuse walk lane's r_snp_pre, r_snp_post and r_aj_snprintf_atSF (refuse_pft.v), copied: the step builds the
   contract's ecall_pre_stk from the journal (PaArt.v's ecall_pre_stk_at), its dest_ok from the per-byte awr_byte
   premise (YCbq.v's awr_byte_present), applies the contract, and rebuilds the journal with YCbq.v's
   ajournal_after_write: the call writes its window [sp0 + o - K, sp0 + o), which the journal's stack window holds,
   and the sn_len (n - 1) T bytes it fills, which awr_byte lets the walk write. The FP state comes back related by
   PaFx.v's fxrel (fxrel_of_frm0). *)
Section st. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.

(* the contract's pre-state at window K, the written length, the written part against the window, dest_ok, and
   the range facts at the written length, from the journal and the step's premises *)
Lemma b11ht_snp_pre : forall K W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d n (T : list Z) (o : Z) raw,
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

(* the step's post from the contract's: the journal again with the same k, the FP state related by fxrel, the
   registers kept, the filled bytes, the kept bytes, present bytes still present *)
Lemma b11ht_snp_post : forall K pc W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d n (T : list Z) (o : Z) raw,
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

(* snprintf(d, n, f, ...) under cmd_asnprintf_realizes at any FF, K, img_lo .. img_hi, cr (refuse_pft.v's
   r_aj_snprintf_atSF): the arguments are the five register words a3 .. a7 (no stack arguments). One change against
   refuse_pft's text: its premise img_hi <= d is here d + sn_len (n - 1) T <= img_lo \/ img_hi <= d (what YCbq's
   blk_off_imgP / frm_off_imgP give for a heap block or a side-stack frame, as off_img), with img_lo <= gotw and
   img_lo <= guard added, so what lies inside the image span is apart from the written part either way. *)
Lemma b11ht_aj_snprintf_FF : forall (FF : fmt_fam) K gotw guard img_lo img_hi cr pc,
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
(d + sn_len (n - 1) T <= img_lo \/ img_hi <= d) -> img_hi <= sp0 + o - K ->
aguard_ok segs W memT gotw guard -> 0 <= gotw -> gotw + 8 <= img_hi -> 0 <= guard -> guard + 8 <= img_hi ->
img_lo <= gotw -> img_lo <= guard ->
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
Hguard Hgc0 Hgc1 Hgv0 Hgv1 Hgl Hvl HFF HT Hcv Hfrm.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (_ & _ & _ & _ & Hshi & H47 & _).
assert (ESTACK = 4096) as Hes by reflexivity.
destruct (b11ht_snp_pre K W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d n T o raw HJ ltac:(lia)
  Hsp' Hal Hneg HKe Hbud Hgp Htp Hra Hraw Hdest HPC Hrad Hhull) as ((HEP & Hslo & Hscr) & Hlen & HDW & HDEST & HRADl & HHULLl).
destruct Hguard as (Hgw & cval & Hcw).
assert (HCR : forall r, In r cr -> img_lo <= fst r /\ 0 <= snd r /\ fst r + snd r <= img_hi)
  by (rewrite Forall_forall in Hcr; exact Hcr).
(* what lies inside the image span is apart from the window and the written part *)
assert (HOUT : forall x w, img_lo <= x -> 0 <= w -> x + w <= img_hi ->
  Forall (zdisjoint (x, w)) (snp_out K (spZ regsT) d (sn_len (n - 1) T))).
{ intros x w Hxl Hw Hx. unfold snp_out. rewrite Hsp'.
  apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia|].
  apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; destruct Hdi as [Hdi | Hdi]; lia | apply Forall_nil]. }
apply (b11ht_snp_post K pc W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d n T o raw HJ Hra Hsp' Hneg Hbud
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

(* the step at row 4 as released: RtFormat.asnprintf_realizes = RtPFCmd.asnprintf_sh, i.e. cmd_asnprintf_realizes at
   FR_cmd, CMD_SNP_K, CMD_IMG_LO .. CMD_IMG_HI, CMD_SNP_CR; the destination off the image is YCbq.off_img, which is
   b11ht_aj_snprintf_FF's disjunction at CMD_IMG_LO = 0x10000 and CMD_IMG_HI = kImgEnd = 0x601000 *)
Lemma b11ht_aj_snprintf_atSF : forall (gotw guard pc : Z),
RtFormat.asnprintf_realizes segs B pc gotw guard ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d n f T (o : Z) raw,
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 d -> getr regsT 11 = w64 n -> getr regsT 12 = w64 f ->
1 <= n < 2 ^ 31 -> 0 < d -> d + n <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> CMD_SNP_K - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
(forall a, d <= a < d + n -> awr_byte segs B STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) (frames S) lyc own a /\
  ~ (sp0 + o - CMD_SNP_K <= a < sp0 + o)) ->
(forall a, d <= a < d + n -> inFP FP a -> (Exists (in_zr a) (as_prog_static B) /\ in_img segs a) \/ sp0 <= a < ly_top lyc ->
  writable_at segs (mrestrict (w_H W) memT) a) ->
amem_range d (n + 8) ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF d n ->
shadow_hull_vis (aview segs (w_H W) memT) d n ->
YCbq.off_img d (sn_len (n - 1) T) -> CMD_IMG_HI <= sp0 + o - CMD_SNP_K ->
aguard_ok segs W memT gotw guard -> 0 <= gotw -> gotw + 8 <= CMD_IMG_HI -> 0 <= guard -> guard + 8 <= CMD_IMG_HI ->
CMD_IMG_LO <= gotw -> CMD_IMG_LO <= guard ->
FR_cmd (aview segs (w_H W) memT) (snp_out CMD_SNP_K (spZ regsT) d (sn_len (n - 1) T)) f
  (map (argZ regsT) [3; 4; 5; 6; 7]) T ->
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
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + sn_len (n - 1) T) -> ~ (sp0 + o - CMD_SNP_K <= a < sp0 + o) ->
  aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) /\
same_but_materialized mdc md2).
Proof using LAWS segs_low.
intros gotw guard pc AP.
exact (b11ht_aj_snprintf_FF FR_cmd CMD_SNP_K gotw guard CMD_IMG_LO CMD_IMG_HI CMD_SNP_CR pc AP
  b11ht_K_estack b11ht_img_lo_0 b11ht_img_hi_47 b11ht_cr_img).
Qed.
End st.


(* ======== the record after snprintf(cur->model, 24, "%s", T) ======== *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_seg_B11a_k pf_seg_B11a_f.

Lemma b11ht_map_bytes : forall l : list Z, Forall (fun x => 0 <= x < 256) l ->
  map bv_unsigned (map (Z_to_bv 8) l) = l.
Proof.
induction l as [|x l IH]; intros H; [reflexivity|].
apply Forall_cons_iff in H as [Hx Hl]. cbn [map]. rewrite (b11f_unsigned_byte x Hx), (IH Hl). reflexivity.
Qed.
Lemma b11ht_bytes_T0 : forall T : list Z, Forall (fun x => 0 <= x < 256) T -> Forall (fun x => 0 <= x < 256) (T ++ [0]).
Proof. intros T H. apply Forall_app. split; [exact H | constructor; [lia | constructor]]. Qed.
Lemma b11ht_nth_byte : forall (l : list Z) i, Forall (fun x => 0 <= x < 256) l ->
  bv_unsigned (nth i (map (Z_to_bv 8) l) ZB0) = nth i l 0.
Proof.
intros l i H. change ZB0 with (Z_to_bv 8 0). rewrite map_nth.
destruct (Nat.lt_ge_cases i (length l)) as [Hi | Hi].
- apply b11f_unsigned_byte. rewrite Forall_forall in H. apply H. apply nth_In. exact Hi.
- rewrite (nth_overflow l 0 Hi). reflexivity.
Qed.

(* entry gi's slice after the model field [36, 36 + |T| + 1) is written: every other field reads its old bytes, the
   model field holds T, its NUL, then the old bytes *)
Lemma b11ht_rseg_model1 : forall (bs : list byte) (gi : nat) (s : rseg) (T : list Z),
  (356 * gi + 356 <= length bs)%nat ->
  seg_spec.rseg_enc s (seg_spec.fld (356 * gi)%nat 356 bs) ->
  (length T < 24)%nat -> ~ In 0 T -> Forall (fun x => 0 <= x < 256) T ->
  seg_spec.rseg_enc (b11_set_model T s)
    (seg_spec.fld (356 * gi)%nat 356 (b11f_put bs (356 * gi + 36)%nat (map (Z_to_bv 8) (T ++ [0])))).
Proof.
intros bs gi s T Hl Hs HT HT0 HTb.
set (p := map (Z_to_bv 8) (T ++ [0])).
assert (Lp : length p = S (length T)) by (unfold p; rewrite length_map, length_app; cbn [length]; lia).
assert (Hk : (356 * gi + 36 + length p <= length bs)%nat) by lia.
assert (ERo : seg_spec.RS_ROLE = 0x10) by reflexivity.
assert (ERs : seg_spec.RS_ROLE_SET = 0x14) by reflexivity.
assert (EIg : seg_spec.RS_IGNORE = 0x18) by reflexivity.
assert (EIs : seg_spec.RS_IGNORE_SET = 0x1c) by reflexivity.
assert (EMo : seg_spec.RS_MODEL = 0x24) by reflexivity.
assert (EMs : seg_spec.RS_MODEL_SET = 0x3c) by reflexivity.
assert (EMf : seg_spec.RS_MODEL_FILE = 0x40) by reflexivity.
assert (ERf : seg_spec.RS_ROLE_FILE = 0xa0) by reflexivity.
assert (EIf : seg_spec.RS_IGNORE_FILE = 0x100) by reflexivity.
assert (ESg : seg_spec.RS_SEEN_GEN = 0x160) by reflexivity.
(* a field outside [36, 60) of the slice reads the old bytes *)
assert (Hkeep : forall a n, (a + n <= 36 \/ 60 <= a)%nat -> (a + n <= 356)%nat ->
  seg_spec.fld a n (seg_spec.fld (356 * gi)%nat 356 (b11f_put bs (356 * gi + 36)%nat p)) =
  seg_spec.fld a n (seg_spec.fld (356 * gi)%nat 356 bs)).
{ intros a n Ha Hn. rewrite !b11f_fld_fld by exact Hn. apply b11f_fld_put_out; lia. }
assert (HkeepZ : forall o n : Z, 0 <= o -> 0 <= n -> (o + n <= 36 \/ 60 <= o) -> o + n <= 356 ->
  seg_spec.fldz o n (seg_spec.fld (356 * gi)%nat 356 (b11f_put bs (356 * gi + 36)%nat p)) =
  seg_spec.fldz o n (seg_spec.fld (356 * gi)%nat 356 bs)).
{ intros o n Ho Hn H1 H2. unfold seg_spec.fldz. apply Hkeep; lia. }
unfold seg_spec.rseg_enc in Hs |- *.
destruct Hs as (Ls & Hname & Hrole & Hrs & Hig & Higs & Hmodel & Hms & Hmf & Hrf & Hif & Hsg).
unfold b11_set_model.
cbn [rs_name rs_role rs_role_set rs_ignore rs_ignore_set rs_model rs_model_set rs_model_file rs_role_file
  rs_ignore_file rs_seen_gen].
split. { rewrite b11f_fld_len, b11f_put_len by lia. lia. }
split. { rewrite Hkeep by lia. exact Hname. }
split. { rewrite HkeepZ by lia. exact Hrole. }
split. { rewrite HkeepZ by lia. exact Hrs. }
split. { rewrite HkeepZ by lia. exact Hig. }
split. { rewrite HkeepZ by lia. exact Higs. }
(* model [36, 60): T, its NUL, then the old bytes *)
split.
{ unfold seg_spec.fldz. rewrite EMo. change (Z.to_nat 36) with 36%nat. change (Z.to_nat 24) with 24%nat.
  rewrite b11f_fld_fld by lia.
  unfold seg_spec.cstr_enc.
  split; [rewrite b11f_fld_len, b11f_put_len by lia; lia|].
  split; [exact HT|]. split; [exact HT0|].
  unfold seg_spec.zs. rewrite firstn_map.
  unfold seg_spec.fld. rewrite firstn_firstn. replace (Nat.min (S (length T)) 24) with (S (length T)) by lia.
  change (firstn (S (length T)) (skipn (356 * gi + 36)%nat (b11f_put bs (356 * gi + 36)%nat p)))
    with (seg_spec.fld (356 * gi + 36)%nat (S (length T)) (b11f_put bs (356 * gi + 36)%nat p)).
  rewrite (b11f_fld_put_at bs (356 * gi + 36)%nat p (S (length T)) Lp) by lia.
  unfold p. exact (b11ht_map_bytes _ (b11ht_bytes_T0 T HTb)). }
split. { rewrite HkeepZ by lia. exact Hms. }
split. { rewrite HkeepZ by lia. exact Hmf. }
split. { rewrite HkeepZ by lia. exact Hrf. }
split. { rewrite HkeepZ by lia. exact Hif. }
rewrite HkeepZ by lia. exact Hsg.
Qed.

(* the record update: from sa_rconf at the entry reader, the bytes T ++ [0] at cur + 0x24 and every other byte of the
   block c kept, sa_rconf of r_upd cf gi (b11_set_model T) at the exit reader *)
Lemma b11ht_rconf_model1 : forall (rd0 rd : reader) (c : Z) (cf : rconf) (gi : nat) (T : list Z),
  sa_rconf rd0 c cf -> (gi < length (rc_seg cf))%nat ->
  (length T < 24)%nat -> ~ In 0 T -> Forall (fun x => 0 <= x < 256) T ->
  (forall i, (i < S (length T))%nat ->
     rd (seg_spec.rseg_addr c gi + seg_spec.RS_MODEL + Z.of_nat i) = Some (nth i (T ++ [0]) 0)) ->
  (forall a, c <= a < c + seg_spec.SEG_C_SIZE ->
     ~ (seg_spec.rseg_addr c gi + seg_spec.RS_MODEL <= a
          < seg_spec.rseg_addr c gi + seg_spec.RS_MODEL + Z.of_nat (S (length T))) ->
     rd a = rd0 a) ->
  sa_rconf rd c (r_upd cf gi (b11_set_model T)).
Proof.
intros rd0 rd c cf gi T Hrc Hgi HT HT0 HTb Hby Hkp.
unfold sa_rconf in Hrc |- *. destruct Hrc as (bs & Hbs & Henc).
set (p := map (Z_to_bv 8) (T ++ [0])).
assert (Lp : length p = S (length T)) by (unfold p; rewrite length_map, length_app; cbn [length]; lia).
pose proof Henc as (Hlen0 & Hn320 & _).
assert (EC : seg_spec.SEG_C_SIZE = 16616) by reflexivity.
assert (Lbs : Z.of_nat (length bs) = 16616) by (rewrite Hlen0; exact EC).
assert (Hgi32 : (gi < 32)%nat) by lia.
assert (Hk : (356 * gi + 36 + length p <= length bs)%nat) by lia.
assert (EA : seg_spec.rseg_addr c gi + seg_spec.RS_MODEL = c + Z.of_nat (356 * gi + 36)%nat)
  by (unfold seg_spec.rseg_addr, seg_spec.RSEG_SIZE, seg_spec.RS_MODEL; lia).
exists (b11f_put bs (356 * gi + 36)%nat p). split.
- (* the exit reader holds the new bytes *)
  unfold sa_bytes. intros i Hi. rewrite b11f_put_len in Hi by exact Hk.
  destruct (Nat.ltb_spec i (356 * gi + 36)%nat) as [H1 | H1].
  { rewrite b11f_put_out by (exact Hk || lia). rewrite Hkp by (rewrite ?EA; lia). exact (Hbs i Hi). }
  destruct (Nat.ltb_spec i (356 * gi + 36 + length p)%nat) as [H2 | H2].
  { rewrite b11f_put_in by (exact Hk || lia). unfold p. rewrite b11ht_nth_byte by exact (b11ht_bytes_T0 T HTb).
    replace (c + Z.of_nat i) with (seg_spec.rseg_addr c gi + seg_spec.RS_MODEL + Z.of_nat (i - (356 * gi + 36))%nat)
      by (rewrite EA; lia).
    apply Hby. lia. }
  rewrite b11f_put_out by (exact Hk || lia). rewrite Hkp by (rewrite ?EA; lia). exact (Hbs i Hi).
- (* the new bytes encode the updated record *)
  unfold seg_spec.rconf_enc in Henc |- *.
  destruct Henc as (Hlen & Hn32 & Hseg & Hn & Hr8 & Href & Hnref & Hrefused & Hovf & Hread & Hgen).
  assert (Hfar : forall o n, 11392 <= Z.of_nat o ->
    seg_spec.fld o n (b11f_put bs (356 * gi + 36)%nat p) = seg_spec.fld o n bs).
  { intros o n Ho. apply b11f_fld_put_out; [exact Hk | lia]. }
  assert (HfarZ : forall o n, 11392 <= o ->
    seg_spec.fldz o n (b11f_put bs (356 * gi + 36)%nat p) = seg_spec.fldz o n bs).
  { intros o n Ho. unfold seg_spec.fldz. apply Hfar. rewrite Z2Nat.id by lia. exact Ho. }
  assert (ERN : seg_spec.RC_N = 0x2c80) by reflexivity.
  assert (ERF : seg_spec.RC_REFUSAL = 0x2e88) by reflexivity.
  assert (ENR : seg_spec.RC_NREF = 0x34c8) by reflexivity.
  assert (ERD : seg_spec.RC_REFUSED = 0x34cc) by reflexivity.
  assert (EOV : seg_spec.RC_OVERFLOW = 0x34d0) by reflexivity.
  assert (ERE : seg_spec.RC_READING = 0x4080) by reflexivity.
  assert (EGE : seg_spec.RC_GEN = 0x40e0) by reflexivity.
  split. { rewrite b11f_put_len by exact Hk. exact Hlen. }
  split. { rewrite b11f_upd_len. exact Hn32. }
  split.
  { intros i Hi. rewrite b11f_upd_len in Hi.
    destruct (Nat.eq_dec i gi) as [E | Hne].
    - subst i. rewrite b11f_nth_upd_same by exact Hgi.
      apply b11ht_rseg_model1; [lia | exact (Hseg gi Hgi) | exact HT | exact HT0 | exact HTb].
    - rewrite b11f_nth_upd_other by exact Hne. rewrite b11f_fld_put_out by lia. exact (Hseg i Hi). }
  split. { rewrite b11f_upd_len. rewrite HfarZ by lia. exact Hn. }
  split. { exact Hr8. }
  split. { intros i Hi. rewrite Hfar by lia. exact (Href i Hi). }
  split. { rewrite HfarZ by lia. exact Hnref. }
  split. { rewrite HfarZ by lia. exact Hrefused. }
  split. { rewrite HfarZ by lia. exact Hovf. }
  split. { rewrite HfarZ by lia. exact Hread. }
  rewrite HfarZ by lia. exact Hgen.
Qed.
