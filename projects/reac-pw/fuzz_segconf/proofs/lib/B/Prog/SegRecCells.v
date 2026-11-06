(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_command/lib/A/Prog/CmdRecCells.v (origin/ossv/recipes 501c0d516c69) for reac-pw/fuzz_segconf's image A (fuzz_segconf.asan): module paths; Cmd*/cmd_* -> Seg*/seg_*; the shadow-base cell 0xb10b8 -> 0xabff8 and its .got word 0xa63f0 -> 0xa2a50 (listing objects 12 and 0); the replace_str flag byte 0xae8d5 -> 0xa9815 (asan_flags_dont_use_directly 0xa97f8 + 29, the same runtime layout); the stack-protector .got word 0xa7098 -> 0xa36d8 and guard 0x6045d8 -> 0x5ff078; the program statics are fuzz_segconf's one range (A_LONGL); g_rec's facts (crf_grec_chk, cmd_cf_grec) and check_words_add's literal facts (crf_cwa_lits_chk, cmd_cf_lit), which name objects fuzz_segconf.asan does not have, left out with the plain proof's RecInv. *)
(* Modified by Theorem Labs, 2026-10: the image-B twin of lib/A/Prog/SegRecCells.v (commit 4f361f065164): module paths and image B's values. *)
(* The record's cells and check_words_add's seven per-binary facts (CwaFacts of an earlier version of
   lib/A/Prog/check_words_add_s1.v:47-83), so a walk builds that record by exact:
   cmd_cf_cell / cmd_cf_got / cmd_cf_env (PALib's pal_cell / pal_got_shadow / pal_env over any instance),
   cmd_cf_grec (g_rec addressable), cmd_cf_lit (the four literals check_words_add reads), and REC_CELLS
   (cmd_rec_cells: the runtime's replace_str flag byte, the stack-protector GOT word and guard, the errno cell).
   cmd_str_tail and cmd_ro_low, the other two CwaFacts facts, are in CmdRecRo.v. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YF0m YB1v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib SegObj SegPgBase SegBase SegRo SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegRecBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(** * The closed checks (each one boolean computation over the record's lists) *)
(* the shadow-base cell and its GOT word: the record has one 8-byte cell of each value *)
Lemma crf_cell_addrs : crf_z8_addrs (Tfib_const crf_ly0) SHADOW_OFF = [0xac7b8].
Proof. vm_compute. reflexivity. Qed.
Lemma crf_got_addrs : crf_z8_addrs (Tfib_const crf_ly0) 0xac7b8 = [0xa3210].
Proof. vm_compute. reflexivity. Qed.
(* the replace_str flag byte (0xae8b8 + 29) and the stack-protector GOT word *)
Lemma crf_flag_chk : seg_byte 0xa9fd5 = Some 1.
Proof. vm_compute. reflexivity. Qed.
Lemma crf_guard_got_chk : seg_word_b 0xa3e98 0x5ff838 = true.
Proof. vm_compute. reflexivity. Qed.

(* the shadow-base cell and its GOT word are the record's: aso_const_law names them among the constant cells *)
Lemma seg_shadow_cells : forall B, SegBSyms B -> as_shadow_cell B = 0xac7b8 /\ as_got_shadow B = 0xa3210.
Proof.
intros B HB. pose proof (aso_const_law _ (ts_ok B HB) crf_ly0) as (H1 & _ & H3 & _).
rewrite (ts_const B HB) in H1, H3.
apply crf_z8_addrs_in in H1. rewrite crf_cell_addrs in H1. destruct H1 as [H1|[]].
rewrite <- H1 in H3. apply crf_z8_addrs_in in H3. rewrite crf_got_addrs in H3. destruct H3 as [H3|[]].
split; [exact (eq_sym H1) | exact (eq_sym H3)].
Qed.

(* Every lemma below is closed over exactly `segs B LAWS HB`, the [IMG] ones over `segs B LAWS HB IMG`
   (the form of the statements lib/A/Prog/CmdRecFacts.v proves). *)
Section cells. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis HB : SegBSyms B.
(* a list of image ranges whose checks hold: each is addressable, with readable shadow words, at every AR state *)
Lemma seg_lits_chk : forall l, forallb (fun an => seg_addr_b (fst an) (snd an) && seg_hull_b (fst an) (snd an)) l = true ->
forall ly S (W : world segs) mem md, AR segs B ly S W mem md ->
Forall (fun an => range_addressable (aview segs (w_H W) mem) SHADOW_OFF (fst an) (snd an)
               /\ shadow_hull_vis (aview segs (w_H W) mem) (fst an) (snd an)) l.
Proof using LAWS HB.
intros l Hl ly S W mem md HAR. apply Forall_forall. intros an Han.
pose proof (proj1 (forallb_forall _ _) Hl an Han) as Hb. apply andb_prop in Hb as [H1 H2].
exact (seg_aread_ok_chk segs B LAWS HB ly S W mem md (fst an) (snd an) HAR H1 H2).
Qed.
Hypothesis IMG : seg_img_facts segs B.
(* PALib's pal_env over any segments: the errno cell is in the image (it has an image byte) and the allocator's
   one-frame traces are in the record's universe *)
Lemma seg_cf_env : api_env segs B.
Proof using LAWS HB IMG.
split; [rewrite (ts_errno B HB); unfold TFIB_ERRNO, kLowMemEnd; lia|]. split.
- intros a Ha. pose proof (cif_errno _ _ IMG a Ha) as H. rewrite (ts_errno B HB) in Ha. unfold TFIB_ERRNO in Ha.
  exact (seg_rom_in_img segs a ltac:(lia) H).
- rewrite (ts_code B HB). split; apply (ts_universe_drv B HB); unfold DRV_TRACES; cbn;
  repeat (first [left; reflexivity | right]).
Qed.
(* REC_CELLS: the flag byte is a const cell, the guard's GOT word a const cell and the guard an image byte, and the
   errno cell has image bytes (the core's AR_errno_present) *)
Lemma seg_rec_cells : forall ly S (W : world segs) mem md, AR segs B ly S W mem md ->
aview segs (w_H W) mem 0xa9fd5 = Some 1 /\ aguard_ok segs W mem 0xa3e98 0x5ff838 /\
exists ev, rd32 (aview segs (w_H W) mem) (as_errno B) ev.
Proof using LAWS HB IMG.
intros ly S W mem md HAR. split; [|split].
- exact (seg_byte_ok segs B LAWS HB ly S W mem md _ _ HAR crf_flag_chk).
- split; [exact (seg_word_chk segs B LAWS HB ly S W mem md _ _ HAR crf_guard_got_chk)|].
  apply crf_rdword_some. intros k Hk. apply crf_rom_view_some. apply (cif_guard_rom _ _ IMG). lia.
- exact (AR_errno_present segs B W mem (cif_errno _ _ IMG)).
Qed.
(* every byte of g_rec, record.spill and g_quitting is writable: PRW is the core's prog_rw (YCbq.v:1145), and the
   record's ts_prog says that cmd_PG's (lo, hi) ranges are its program statics' (lo, len) ranges *)
Hypothesis PRW : prog_rw segs B.
Lemma PROG_WRITABLE : forall (m : word -> option byte) a, inFP seg_PG a -> writable_at segs m a.
Proof using LAWS HB PRW.
intros m a Ha. apply (PRW m a). rewrite (ts_prog B HB).
destruct Ha as (r & Hr & Ha). unfold seg_PG, A_LONGL in Hr. unfold TFIB_PROG_STATIC.
destruct Hr as [<-|[]]; cbn [fst snd] in Ha;
apply Exists_cons_hd;
unfold in_zr; cbn [fst snd]; lia.
Qed.
End cells.

(* PALib's pal_cell and pal_got_shadow over any instance whose object atoms are the listing's (cmd_val_objs) *)
Section pi. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {PI : PAImg seg_listing}.
Variable B : asyms.
Hypothesis HB : SegBSyms B.
Hypothesis VOBJS : seg_val_objs.
Lemma crf_obj12 : nth 12 seg_objs 0 = 0xac7b8.
Proof using. vm_compute. reflexivity. Qed.
Lemma crf_obj0 : nth 0 seg_objs 0 = 0xa3210.
Proof using. vm_compute. reflexivity. Qed.
Lemma seg_cf_cell : as_shadow_cell B = pa_val (A_OBJ 12).
Proof using HB VOBJS.
rewrite (VOBJS 12%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)), crf_obj12. exact (proj1 (seg_shadow_cells B HB)).
Qed.
Lemma seg_cf_got : as_got_shadow B = pa_val (A_OBJ 0).
Proof using HB VOBJS.
rewrite (VOBJS 0%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)), crf_obj0. exact (proj2 (seg_shadow_cells B HB)).
Qed.
End pi.
Print Assumptions seg_cf_cell.
Print Assumptions seg_cf_got.
Print Assumptions seg_cf_env.
Print Assumptions seg_rec_cells.
Print Assumptions PROG_WRITABLE.
