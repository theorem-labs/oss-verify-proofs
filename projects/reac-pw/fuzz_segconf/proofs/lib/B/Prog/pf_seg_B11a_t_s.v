(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed and off_img at fuzz_command's ASan image end 0x606000; ajournal no longer keeps footprint (FP) bytes in the image or at or above alloc_ceiling (fp_spares FP a also requires ~ inFP FP a, and the clause for bytes at or above alloc_ceiling outside [sp0 - STK, sp0) requires ~ inFP FP a), awr_byte (and awr_ok) take the start state's side-stack frames as a new parameter and also admit footprint writes to the program's statics as_prog_static in the image, to the caller's stack above sp0 and to those caller frames (awr_prog_or_caller), acall_kept_of_journal, region_kept_stack_sub, awr_byte_present and aj_intrin_at take the matching premises, ajournal_sub_wide composes a callee whose footprint lies in what the caller may write, awr_byte_present_prog and aj_intrin_at_prog take prog_rw for stores to the statics, AR_errno_present gives the errno cell's value from errno_rom, and astack_rd/astack_pres (stack bytes readable/present from sp to the stack top) give a frame chain for any s0 but an aligned sp + 8 (chain_pre_any, achain_any) and carry across an ajournal (astack_rd_journal, astack_pres_journal). *)
(* Modified by Theorem Labs, 2026-10: the malloc/free journal lemmas (aj_free_at, aj_free_at_io, aj_free_null_at, aj_free_null_at_io, aj_malloc_at, aj_malloc_at_io, aj_malloc_at04, aj_malloc_at04_io, aj_malloc, aj_free) no longer take In (call_trace0 ...) (as_universe B); the model laws get the trace length (call_trace_len) and the contracts the event bound. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Reusable/YCbq.v, with its numbers changed; 205 of its 373 lines of code are new or changed and 3177 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/PaRt.v, with its module paths and module names changed; 382 of its 431 lines of code are new or changed and 324 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3): helper of the RS1 cut of segment B11a of
   reac_segconf_parse_file's walk (lib/B/Prog/pf_seg_B11a_t.v): the snprintf step through the walk's journal, the
   "%s" format fact, the C strings of the block reac_segconf and the record lemmas the cut's second snprintf
   (0x88a3c, snprintf(cur->model_file, 96, "%s", c->reading)) and its model_set store (0x88a24) need.
   proves no function (kind: segment lemma of reac_segconf_parse_file's walk, helper of B11a's RS1 cut: no
   instruction is walked here). The B11a segment lane of the image-B G3 walk owner, 2026-10-30 (a sub-lane).
   ADAPTED from a working branch + U piece walks; templates a lane clone
   lib/B/Prog/pf_seg_B3_t.v (the B3 segment lane, 151b4054f431: b3t_* copied with the prefix b11ts_, itself the
   image-A refuse walk lane's refuse_pft.v r_snp_pre / r_snp_post / r_aj_snprintf_atSF) and a lane clone
   lib/B/Prog/pf_seg_B8b_m.v (the B8b segment lane, 49a20292ece9: pb8b_cstr_sa_str, pb8b_reading_str, pb8b_cstr_rng,
   pb8b_cstr_splice0, pb8b_upd_nth_twice re-derived here). Row 4 on image B is RtFormat.asnprintf_realizes =
   RtPFCmd.asnprintf_sh (lib/B/Rt/RtPFCmd.v, image B's constants CMD_GOTW 0xa3e98, CMD_SNP_K = 2 * ESTACK,
   CMD_IMG_LO 0x10000, CMD_IMG_HI kImgEnd); no lemma here names an image-A number.
   - b11ts_snp_pre, b11ts_snp_post, b11ts_aj_snprintf_FF, b11ts_aj_snprintf_atSF: the snprintf step;
   - b11ts_FR_s / b11ts_FR_s_regs: FR_cmd at "%s" with one string argument;
   - b11ts_reading_str / b11ts_reading_rng: c->reading as an sa_str at the struct's reader, its bytes in range;
   - b11ts_cstr_put0: a 96-byte field with snprintf's text and NUL at its head holds the C string;
   - b11ts_cf1_model: the record b11_cf1 then rs_with_model is the record with rs_with_model alone. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_seg_B11a_k.

(* ======== row 4's closed facts ======== *)
Lemma b11ts_K_estack : ESTACK <= CMD_SNP_K.
Proof. unfold CMD_SNP_K, ESTACK. lia. Qed.
Lemma b11ts_img_lo_0 : 0 <= CMD_IMG_LO.
Proof. unfold CMD_IMG_LO. lia. Qed.
Lemma b11ts_img_hi_47 : CMD_IMG_HI <= 2 ^ 47.
Proof. unfold CMD_IMG_HI, kImgEnd. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma b11ts_cr_img : Forall (fun r => CMD_IMG_LO <= fst r /\ 0 <= snd r /\ fst r + snd r <= CMD_IMG_HI) CMD_SNP_CR.
Proof.
unfold CMD_SNP_CR, CMD_IMG_LO, CMD_IMG_HI, kImgEnd.
repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia.
Qed.
(* off_img of a range holds of every subrange (a caller narrows a block's or a frame's off_img to the written part) *)
Lemma b11ts_off_img_sub : forall a n a' n', YCbq.off_img a n -> a <= a' -> 0 <= n' -> a' + n' <= a + n ->
  YCbq.off_img a' n'.
Proof. intros a n a' n' H H1 H2 H3. unfold YCbq.off_img in *. lia. Qed.

(* ======== the format "%s" ======== *)
Lemma b11ts_F_s_len : Z.of_nat (length SegModel.F_s) = 2.
Proof. vm_compute. reflexivity. Qed.
Lemma b11ts_parse_F_s : pf_parse SegModel.F_s = Some [Ps].
Proof. vm_compute. reflexivity. Qed.

(* str_end's span is seg_spec.cstr_span (r_str_end_span of refuse_pft.v) *)
Lemma b11ts_str_end_span : forall w s, str_end w s - w = seg_spec.cstr_span w s.
Proof.
intros w s. unfold str_end, seg_spec.cstr_span.
pose proof (Z.div_mod (w + Z.of_nat (length s)) 8 ltac:(lia)) as E1.
pose proof (Z.mod_pos_bound (w + Z.of_nat (length s)) 8 ltac:(lia)) as B1.
rewrite <- (Z.mod_unique (- (w + Z.of_nat (length s) + 1)) 8 (- ((w + Z.of_nat (length s)) / 8) - 1)
  (7 - (w + Z.of_nat (length s)) mod 8)) by lia.
lia.
Qed.

(* the bytes of a string sa_str reads, over a reader whose values are bytes, are 1 .. 255 *)
Lemma b11ts_bytes_range : forall (rd : reader) (p : Z) (l : list Z),
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
Lemma b11ts_bytes_range_aview : forall segs H mem p l,
  sa_str (aview segs H mem) p l -> Forall (fun c => 0 < c < 256) l.
Proof. intros segs H mem p l Hs. exact (b11ts_bytes_range _ p l Hs (sa_aview_rng segs H mem)). Qed.

(* FR_cmd at "%s" with one string argument s at w: the format literal at fp (its bytes and NUL from sa_str, its amem
   and shadow from sa_addr, below the GOT word CMD_GOTW), the argument's bytes, NUL and slack word (sa_str), its
   amem and shadow (sa_addr), 8 bytes past its NUL in application memory, and both read spans apart from rs *)
Lemma b11ts_FR_s : forall (rd : reader) (rs : list (Z * Z)) (fp w : Z) (s : list Z) (r1 r2 r3 r4 : Z),
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
pose proof b11ts_F_s_len as EF.
assert (E3 : Z.of_nat (length SegModel.F_s) + 1 = 3) by (rewrite EF; reflexivity).
pose proof (Z.mod_pos_bound (w + Z.of_nat (length s)) 8 ltac:(lia)) as Hm.
unfold FR_cmd. exists SegModel.F_s, [Ps], [APtr s].
split.
{ (* fmt_at *)
  split; [exact Hf0|]. rewrite E3. split.
  - intros i Hi. specialize (Hfz (Z.to_nat i) ltac:(rewrite length_app; cbn [length]; lia)).
    rewrite Z2Nat.id in Hfz by lia. exact Hfz.
  - split; [exact Hfd|]. split; [exact Hfam|]. split; [exact Hfra | apply Hfhv; lia]. }
split; [exact b11ts_parse_F_s|].
split; [apply pf_cmd_piece_all|].
split.
{ (* pf_args_asan: the one string argument *)
  split; [|exact I].
  split; [exact Hb|]. split; [exact Hw|]. split; [exact Hl|].
  split.
  { intros i Hi. specialize (Hzs (Z.to_nat i) ltac:(rewrite length_app; cbn [length]; lia)).
    rewrite Z2Nat.id in Hzs by lia. exact Hzs. }
  split; [exact Htl|].
  split; [rewrite b11ts_str_end_span; exact Hd|].
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
Lemma b11ts_FR_s_regs : forall (rd : reader) (rs : list (Z * Z)) (fp w : Z) (s : list Z) (regs : bvmap 5 word),
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
exact (b11ts_FR_s rd rs fp w s (argZ regs 4) (argZ regs 5) (argZ regs 6) (argZ regs 7)).
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
Lemma b11ts_snp_pre : forall K W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d n (T : list Z) (o : Z) raw,
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
Lemma b11ts_snp_post : forall K pc W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d n (T : list Z) (o : Z) raw,
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
Lemma b11ts_aj_snprintf_FF : forall (FF : fmt_fam) K gotw guard img_lo img_hi cr pc,
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
destruct (b11ts_snp_pre K W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d n T o raw HJ ltac:(lia)
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
apply (b11ts_snp_post K pc W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d n T o raw HJ Hra Hsp' Hneg Hbud
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
   b11ts_aj_snprintf_FF's disjunction at CMD_IMG_LO = 0x10000 and CMD_IMG_HI = kImgEnd = 0x601000 *)
Lemma b11ts_aj_snprintf_atSF : forall (gotw guard pc : Z),
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
exact (b11ts_aj_snprintf_FF FR_cmd CMD_SNP_K gotw guard CMD_IMG_LO CMD_IMG_HI CMD_SNP_CR pc AP
  b11ts_K_estack b11ts_img_lo_0 b11ts_img_hi_47 b11ts_cr_img).
Qed.
End st.

(* ======== C strings of the struct reac_segconf (pf_seg_B8b_m.v's pb8b_cstr_sa_str / pb8b_reading_str) ======== *)
Lemma b11ts_nth_firstn : forall {A} (l : list A) (n k : nat) (d : A), (k < n)%nat -> nth k (firstn n l) d = nth k l d.
Proof.
intros A l. induction l as [|x l IH]; intros n k d Hk; [destruct n; reflexivity|].
destruct n as [|n]; [lia|]. destruct k as [|k]; [reflexivity|]. cbn [firstn nth]. apply IH. lia.
Qed.
Lemma b11ts_nth_skipn : forall {A} (l : list A) (a k : nat) (d : A), nth k (skipn a l) d = nth (a + k) l d.
Proof.
intros A l a. revert l. induction a as [|a IH]; intros l k d; [reflexivity|].
destruct l as [|x l]; [destruct k; reflexivity|]. exact (IH l k d).
Qed.
Lemma b11ts_in_firstn : forall {A} (n : nat) (l : list A) (x : A), In x (firstn n l) -> In x l.
Proof. intros A n l x H. rewrite <- (firstn_skipn n l). apply in_or_app. left. exact H. Qed.
Lemma b11ts_nth_map_bv : forall (l : list byte) k, (k < length l)%nat ->
  nth k (map bv_unsigned l) 0 = bv_unsigned (nth k l ZB0).
Proof.
induction l as [|x l IH]; intros k Hk; [cbn in Hk; lia|].
destruct k as [|k]; [reflexivity|]. cbn [map nth]. apply IH. cbn [length] in Hk. lia.
Qed.
Lemma b11ts_fld_nth : forall a n (bs : list byte) k d, (k < n)%nat -> nth k (seg_spec.fld a n bs) d = nth (a + k) bs d.
Proof. intros a n bs k d Hk. unfold seg_spec.fld. rewrite b11ts_nth_firstn by exact Hk. apply b11ts_nth_skipn. Qed.
Lemma b11ts_nth_zb : forall (l : list Z) i, Forall (fun z => 0 <= z < 256) l ->
  bv_unsigned (nth i (seg_spec.zb l) ZB0) = nth i l 0.
Proof.
induction l as [|z l IH]; intros i H; [destruct i; reflexivity|].
apply Forall_cons_iff in H as [Hz Hl]. destruct i as [|i]; cbn [nth seg_spec.zb map]; [|exact (IH i Hl)].
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. lia.
Qed.
(* the C string of a cap-byte field at off, with 7 more bytes of the block after the field, is an sa_str *)
Lemma b11ts_cstr_sa_str : forall (rd : reader) (c : Z) (bs : list byte) (off cap : nat) (s : list Z),
  sa_bytes rd c bs -> seg_spec.cstr_enc cap s (seg_spec.fld off cap bs) -> (off + cap + 7 <= length bs)%nat ->
  sa_str rd (c + Z.of_nat off) s.
Proof.
intros rd c bs off cap s Hb (Lf & Ls & Hn & Hz) Hl.
unfold sa_str, sa_strz, sa_zs, sa_tail, sa_bytes in *.
split; [split|].
- intros k Hk. rewrite length_app in Hk; cbn [length] in Hk.
  rewrite <- Hz. rewrite b11ts_nth_firstn by lia. unfold seg_spec.zs.
  rewrite b11ts_nth_map_bv by lia. rewrite b11ts_fld_nth by lia.
  replace (c + Z.of_nat off + Z.of_nat k) with (c + Z.of_nat (off + k)) by lia.
  apply Hb. lia.
- exact Hn.
- intros x Hx. pose proof (Z.mod_pos_bound (c + Z.of_nat off + Z.of_nat (length s)) 8 ltac:(lia)) as M.
  replace x with (c + Z.of_nat (Z.to_nat (x - c))) by lia.
  rewrite Hb by lia. discriminate.
Qed.
Lemma b11ts_cstr_rng : forall cap s f, seg_spec.cstr_enc cap s f -> Forall (fun z => 0 <= z < 256) s.
Proof.
intros cap s f (_ & _ & _ & Hz). apply Forall_forall. intros z Iz.
assert (I2 : In z (firstn (S (length s)) (seg_spec.zs f))) by (rewrite Hz; apply in_or_app; left; exact Iz).
apply b11ts_in_firstn in I2. unfold seg_spec.zs in I2. apply in_map_iff in I2. destruct I2 as (bt & <- & _).
pose proof (bv_unsigned_in_range _ bt) as R. change (bv_modulus 8) with 256 in R. cbv beta. lia.
Qed.
Lemma b11ts_reading_rng : forall (rd : reader) (c : Z) (cf : SegModel.rconf), sa_rconf rd c cf ->
  Forall (fun z => 0 <= z < 256) (SegModel.rc_reading cf).
Proof.
intros rd c cf (bs & _ & Hc). destruct Hc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hrd & _).
exact (b11ts_cstr_rng _ _ _ Hrd).
Qed.
Lemma b11ts_reading_str : forall (rd : reader) (c : Z) (cf : SegModel.rconf),
  sa_rconf rd c cf -> 0 <= c -> sa_str rd (c + seg_spec.RC_READING) (SegModel.rc_reading cf).
Proof.
intros rd c cf (bs & Hb & Hc) Hc0.
destruct Hc as (L & _ & _ & _ & _ & _ & _ & _ & _ & Hrd & _). unfold seg_spec.SEG_C_SIZE in L. unfold seg_spec.fldz in Hrd.
replace (c + seg_spec.RC_READING) with (c + Z.of_nat (Z.to_nat seg_spec.RC_READING)) by (unfold seg_spec.RC_READING; lia).
apply (b11ts_cstr_sa_str rd c bs (Z.to_nat seg_spec.RC_READING) 96); [exact Hb | exact Hrd | unfold seg_spec.RC_READING; lia].
Qed.
(* a cap-byte field g with its first |fl| + 1 bytes replaced by fl and its NUL holds the C string fl *)
Lemma b11ts_cstr_put0 : forall cap (g : list byte) (fl : list Z), length g = cap -> (length fl < cap)%nat ->
  ~ In 0 fl -> Forall (fun z => 0 <= z < 256) fl ->
  seg_spec.cstr_enc cap fl (seg_spec.zb (fl ++ [0]) ++ skipn (S (length fl)) g).
Proof.
intros cap g fl Lg Hl Hn Hr.
assert (Lnw : length (seg_spec.zb (fl ++ [0])) = S (length fl))
  by (unfold seg_spec.zb; rewrite length_map, length_app; cbn [length]; lia).
assert (Hr0 : Forall (fun z => 0 <= z < 256) (fl ++ [0]))
  by (apply Forall_app; split; [exact Hr | constructor; [cbv beta; lia | constructor]]).
split; [rewrite length_app, length_skipn, Lnw; lia|]. split; [exact Hl|]. split; [exact Hn|].
unfold seg_spec.zs. rewrite map_app, firstn_app, length_map, Lnw, Nat.sub_diag. cbn [firstn]. rewrite app_nil_r.
rewrite firstn_all2 by (rewrite length_map; lia).
exact (sa_zs_zb _ Hr0).
Qed.

(* ======== the record ======== *)
Lemma b11ts_upd_nth_twice : forall {A} (i : nat) (f g : A -> A) (l : list A),
  SegModel.upd_nth i g (SegModel.upd_nth i f l) = SegModel.upd_nth i (fun x => g (f x)) l.
Proof.
intros A i f g l. revert i. induction l as [|x l IH]; intros i; [destruct i; reflexivity|].
destruct i as [|i]; [reflexivity|]. cbn [SegModel.upd_nth]. f_equal. apply IH.
Qed.
Lemma b11ts_cf1_model : forall cf gi val m file,
  SegModel.r_upd (b11_cf1 cf gi val) gi (SegModel.rs_with_model m file) =
  SegModel.r_upd cf gi (SegModel.rs_with_model m file).
Proof.
intros cf gi val m file. unfold b11_cf1, SegModel.r_upd, SegModel.r_set_segs. cbn [SegModel.rc_seg].
rewrite b11ts_upd_nth_twice. reflexivity.
Qed.
