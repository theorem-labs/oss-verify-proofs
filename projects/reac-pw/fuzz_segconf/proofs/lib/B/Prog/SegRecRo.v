(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_command/lib/A/Prog/CmdRecRo.v (origin/ossv/recipes 501c0d516c69) for reac-pw/fuzz_segconf's image A (fuzz_segconf.asan): module paths; Cmd*/cmd_* -> Seg*/seg_* (CmdRep -> SegRep: the contracts' file for aval_mem and astr_argA); g_rec's GOT word facts (crf_got_rec_in, cmd_got_rec) left out, fuzz_segconf.asan's program has no such word; the image's end 0x606000 -> YG0f.kImgEnd; cmd_str_tail over SegRep's astr_argA, whose five fuzz_command names are parameters (LMAX, any; str_at := astr_atR, addr_b := seg_addr_b, hull_b := seg_hull_b, ro_ends := seg_ro_ends). *)
(* Modified by Theorem Labs, 2026-10: the image-B twin of lib/A/Prog/SegRecRo.v (commit 4f361f065164): module paths and image B's values. *)
(* The program's read-only bytes and string tails on fuzz_command.asan: cmd_ro_ok from arodata_okP (M3,
   cmd_ro_ok_of_aro), CmdRo's objects read-only (cmd_ro_in_img), the read-only span (cmd_ro_low), a literal's word
   tail at every state (cmd_tail_vis_at), the word tail of a string argument on either arm of astr_argA
   (cmd_str_tail) or in a side-stack frame object (cmd_fobj_tail), and g_rec's GOT word (cmd_got_rec). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YM05 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0s YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0d_tail.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YF0m YB1v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegBase SegRo SegGlob SegRep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegRecBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Lemma crf_req_size_ge : forall k, k <= req_size k.
Proof. intros k. unfold req_size. destruct (Z.eqb_spec k 0); cbv iota; lia. Qed.

(* Every lemma below is closed over exactly `segs B LAWS HB`, the [IMG] ones over `segs B LAWS HB IMG`
   (the Section form of the per-binary facts' statements). *)
Section ro. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis HB : SegBSyms B.
(* the word tail of a string in an object of a live side-stack frame: the frame is 8-aligned and a multiple of 8
   long, so the NUL's word lies inside it, and AR_frames_law makes every byte of it present *)
Lemma seg_fobj_tail : forall ly S (W : world segs) mem md s x, AR segs B ly S W mem md ->
afobj segs B ly S W mem s (Z.of_nat (length x) + 1) -> astr_atR (aview segs (w_H W) mem) s x ->
atail_vis segs W mem (s + Z.of_nat (length x)).
Proof using LAWS HB.
intros ly S W mem md s x HAR [(cid & pos & Hin & Hc & Hal & Hlo & Hhi) _] _ a Ha.
pose proof (al_frames _ _ LAWS ly S W mem md cid pos HAR Hin) as (_ & _ & HP & _).
assert (Hfb : fs_frame_bytes cid mod 8 = 0).
{ unfold fs_frame_bytes. rewrite Z.shiftl_mul_pow2 by lia. replace (64 * 2 ^ cid) with (8 * 2 ^ cid * 8) by ring.
  apply Z_mod_mult. }
assert (Hr : frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid).
{ clear - Hal Hfb Hlo Hhi Ha. Z.div_mod_to_equations. lia. }
exact (crf_present_view segs (w_H W) mem a (proj1 (HP a Hr))).
Qed.
Hypothesis IMG : seg_img_facts segs B.
(* CmdRo's objects are read-only bytes (CMD_RO_IN) *)
Lemma seg_ro_in_img : seg_ro_in (in_roP segs SEG_RLO SEG_RHI).
Proof using LAWS HB IMG. exact (cif_ro_in _ _ IMG). Qed.
Lemma SEG_RO_IN : seg_ro_in (in_roP segs SEG_RLO SEG_RHI).
Proof using LAWS HB IMG. exact seg_ro_in_img. Qed.
(* every read-only byte lies in the image's span *)
Lemma seg_ro_low : forall a, in_roP segs SEG_RLO SEG_RHI a -> 0x10000 <= a < kImgEnd.
Proof using LAWS HB IMG. intros a Ha. pose proof (cif_ro_end _ _ IMG a Ha). unfold kImgEnd, SEG_RHI in *. lia. Qed.
(* the relro range [CMD_RLO, CMD_RHI) lies in the image, under three names the walks carry *)
Lemma relro_img : forall a, SEG_RLO <= a < SEG_RHI -> in_img segs a.
Proof using LAWS HB IMG. exact (cif_relro_img _ _ IMG). Qed.
Lemma RELRO_IMG : forall a, SEG_RLO <= a < SEG_RHI -> in_img segs a.
Proof using LAWS HB IMG. exact relro_img. Qed.
Lemma RRO : forall a, SEG_RLO <= a < SEG_RHI -> in_img segs a.
Proof using LAWS HB IMG. exact relro_img. Qed.
(* the program's statics are no read-only bytes *)
Lemma RPG : forall a, inFP seg_PG a -> ~ in_roP segs SEG_RLO SEG_RHI a.
Proof using LAWS HB IMG. exact (cif_prog_not_ro _ _ IMG). Qed.
(* every read-only byte is below the overflow-list head: CmdBase.v's class ro_below_ofl, under the name
   the check_round_trip walk carries (ROB) *)
Lemma ROB : ro_below_ofl segs SEG_RLO SEG_RHI.
Proof using LAWS HB IMG. exact (cif_ro_below_ofl _ _ IMG). Qed.
(* every byte of CmdRo's objects reads as CmdRo has it, from arodata_okP: each object is read-only, unowned and
   not the errno cell (IMG), so arodata_okP shows the image's byte, which is CmdRo's (IMG) *)
Lemma seg_ro_obj_bytes : forall ly S (W : world segs) mem md e, AR segs B ly S W mem md ->
arodata_okP segs SEG_RLO SEG_RHI B (aview segs (w_H W) mem) -> In e seg_ro_list ->
abytes_atR (aview segs (w_H W) mem) (fst e) (snd e).
Proof using LAWS HB IMG.
intros ly S W mem md e _ HR He i Hi.
pose proof (crf_ro_list_in e i He Hi) as Hin.
pose proof (seg_ro_in_to _ (cif_ro_unowned _ _ IMG) _ Hin) as [Ho Hn].
rewrite (HR _ (seg_ro_in_to _ (cif_ro_in _ _ IMG) _ Hin) Ho Hn).
exact (cif_ro_image _ _ IMG e He i Hi).
Qed.
(* M3: the program's read-only bytes and literal tails, from arodata_okP and the image *)
Lemma seg_ro_ok_of_aro : forall ly S (W : world segs) mem md, AR segs B ly S W mem md ->
arodata_okP segs SEG_RLO SEG_RHI B (aview segs (w_H W) mem) -> seg_ro_ok (aview segs (w_H W) mem).
Proof using LAWS HB IMG.
intros ly S W mem md HAR HR. split.
- apply crf_ro_bytes_of. intros e He. exact (seg_ro_obj_bytes ly S W mem md e HAR HR He).
- intros e He a Ha. apply crf_rom_view_some. apply (cif_rom_some _ _ IMG). exact (cif_tails_rom _ _ IMG e a He Ha).
Qed.
(* a literal's word tail, at every state: its bytes are read-only bytes with an image byte *)
Lemma seg_tail_vis_at : forall ly S (W : world segs) mem md e, AR segs B ly S W mem md -> In e seg_ro_ends ->
atail_vis segs W mem e.
Proof using LAWS HB IMG.
intros ly S W mem md e _ He a Ha. apply crf_rom_view_some. apply (cif_rom_some _ _ IMG). exact (cif_tails_rom _ _ IMG e a He Ha).
Qed.
(* the word tail of a string argument, either arm of astr_argA: in a live block, the NUL is a byte of the block
   (AR_block_word_vis); read-only, its end is one of CmdRo's literal ends (cmd_tail_vis_at) *)
Lemma seg_str_tail : forall LMAX ly S (W : world segs) mem md p x, AR segs B ly S W mem md ->
astr_argA B LMAX astr_atR seg_addr_b seg_hull_b seg_ro_ends ly S (aview segs (w_H W) mem)
(in_roP segs SEG_RLO SEG_RHI) [] p (Some x) ->
atail_vis segs W mem (p + astr_len x).
Proof using LAWS HB IMG.
intros LMAX ly S W mem md p x HAR (_ & _ & _ & [[(q & k & Hin & Hq & Hk) _] | (_ & _ & _ & Hend)]).
- intros a Ha. pose proof (crf_req_size_ge k) as Hreq.
  assert (Hj : q <= p + astr_len x < q + req_size k) by (unfold astr_len; lia).
  exact (AR_block_word_vis segs B ly S W mem md q k (p + astr_len x) a HAR Hin Hj ltac:(lia)).
- exact (seg_tail_vis_at ly S W mem md (p + astr_len x) HAR Hend).
Qed.
End ro.
Print Assumptions seg_ro_in_img.
Print Assumptions seg_ro_low.
Print Assumptions seg_ro_ok_of_aro.
Print Assumptions seg_tail_vis_at.
Print Assumptions seg_str_tail.
Print Assumptions seg_fobj_tail.
Print Assumptions relro_img.
Print Assumptions RELRO_IMG.
Print Assumptions RRO.
Print Assumptions RPG.
Print Assumptions SEG_RO_IN.
