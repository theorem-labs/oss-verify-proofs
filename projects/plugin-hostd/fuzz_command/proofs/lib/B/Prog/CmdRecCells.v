(* The record's cells and check_words_add's seven per-binary facts on fuzz_command.asan-ubsan (the B twin of
   lib/A/Prog/CmdRecCells.v; CwaFacts, on the A side an earlier version of
   lib/A/Prog/check_words_add_s1.v:47-83), so a walk builds that record by exact:
   cmd_cf_cell / cmd_cf_got / cmd_cf_env (PALib's pal_cell / pal_got_shadow / pal_env over any instance),
   cmd_cf_grec (g_rec addressable), cmd_cf_lit (the four literals check_words_add reads), and REC_CELLS
   (cmd_rec_cells: the runtime's replace_str flag byte, the stack-protector GOT word and guard, the errno cell).
   cmd_str_tail and cmd_ro_low, the other two CwaFacts facts, are in CmdRecRo.v. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YM05 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v YG00 YG0a YG01 YG0f YG0n YG0s YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdAddr CmdPa.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdPaLib CmdObj CmdBase CmdRo CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(** * The closed checks (each one boolean computation over the record's lists) *)
(* the shadow-base cell and its GOT word: the record has one 8-byte cell of each value *)
Lemma crf_cell_addrs : crf_z8_addrs (Tfib_const crf_ly0) SHADOW_OFF = [0xb0c38].
Proof. vm_compute. reflexivity. Qed.
Lemma crf_got_addrs : crf_z8_addrs (Tfib_const crf_ly0) 0xb0c38 = [0xa5f50].
Proof. vm_compute. reflexivity. Qed.
(* g_rec's 960 bytes are addressable *)
Lemma crf_grec_chk : cmd_addr_b A_G_REC RecInv.REC_SIZE = true.
Proof. vm_compute. reflexivity. Qed.
(* check_words_add's literals "-", "own", "default", "pool:", through their NULs (its CWA_LITS; on
   fuzz_command.asan-ubsan check_words_add forms these four addresses at 0x88eec..0x88f4c) *)
Lemma crf_cwa_lits_chk : forallb (fun an => cmd_addr_b (fst an) (snd an) && cmd_hull_b (fst an) (snd an))
[(0x21b00, 2); (0x21b20, 4); (0x21b40, 8); (0x21b60, 6)] = true.
Proof. vm_compute. reflexivity. Qed.
(* the replace_str flag byte (__asan::asan_flags_dont_use_directly 0xae438 + 29) and the stack-protector GOT word *)
Lemma crf_flag_chk : cmd_byte 0xae455 = Some 1.
Proof. vm_compute. reflexivity. Qed.
Lemma crf_guard_got_chk : cmd_word_b 0xa6bf8 0x604158 = true.
Proof. vm_compute. reflexivity. Qed.

(* the shadow-base cell and its GOT word are the record's: aso_const_law names them among the constant cells *)
Lemma cmd_shadow_cells : forall B, CmdBSyms B -> as_shadow_cell B = 0xb0c38 /\ as_got_shadow B = 0xa5f50.
Proof.
intros B HB. pose proof (aso_const_law _ (ts_ok B HB) crf_ly0) as (H1 & _ & H3 & _).
rewrite (ts_const B HB) in H1, H3.
apply crf_z8_addrs_in in H1. rewrite crf_cell_addrs in H1. destruct H1 as [H1|[]].
rewrite <- H1 in H3. apply crf_z8_addrs_in in H3. rewrite crf_got_addrs in H3. destruct H3 as [H3|[]].
split; [exact (eq_sym H1) | exact (eq_sym H3)].
Qed.

(* Every lemma below is closed over exactly `segs B LAWS HB`, the [IMG] ones over `segs B LAWS HB IMG`
   (the form of the statements lib/B/Prog/CmdRecFacts.v proves). *)
Section cells. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis HB : CmdBSyms B.
(* g_rec's body is addressable at every AR state *)
Lemma cmd_cf_grec : forall ly S (W : world segs) mem md, AR segs B ly S W mem md ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF A_G_REC RecInv.REC_SIZE.
Proof using LAWS HB.
intros ly S W mem md HAR. exact (cmd_addressable_chk segs B LAWS HB ly S W mem md A_G_REC RecInv.REC_SIZE HAR crf_grec_chk).
Qed.
(* a list of image ranges whose checks hold: each is addressable, with readable shadow words, at every AR state *)
Lemma cmd_lits_chk : forall l, forallb (fun an => cmd_addr_b (fst an) (snd an) && cmd_hull_b (fst an) (snd an)) l = true ->
forall ly S (W : world segs) mem md, AR segs B ly S W mem md ->
Forall (fun an => range_addressable (aview segs (w_H W) mem) SHADOW_OFF (fst an) (snd an)
               /\ shadow_hull_vis (aview segs (w_H W) mem) (fst an) (snd an)) l.
Proof using LAWS HB.
intros l Hl ly S W mem md HAR. apply Forall_forall. intros an Han.
pose proof (proj1 (forallb_forall _ _) Hl an Han) as Hb. apply andb_prop in Hb as [H1 H2].
exact (cmd_aread_ok_chk segs B LAWS HB ly S W mem md (fst an) (snd an) HAR H1 H2).
Qed.
(* the four literals check_words_add reads (its CWA_LITS) *)
Lemma cmd_cf_lit : forall ly S (W : world segs) mem md, AR segs B ly S W mem md ->
Forall (fun an => range_addressable (aview segs (w_H W) mem) SHADOW_OFF (fst an) (snd an)
               /\ shadow_hull_vis (aview segs (w_H W) mem) (fst an) (snd an))
[(0x21b00, 2); (0x21b20, 4); (0x21b40, 8); (0x21b60, 6)].
Proof using LAWS HB.
intros ly S W mem md HAR. exact (cmd_lits_chk _ crf_cwa_lits_chk ly S W mem md HAR).
Qed.
Hypothesis IMG : cmd_img_facts segs B.
(* PALib's pal_env over any segments: the errno cell is in the image (it has an image byte) and the allocator's
   one-frame traces are in the record's universe *)
Lemma cmd_cf_env : api_env segs B.
Proof using LAWS HB IMG.
split; [rewrite (ts_errno B HB); unfold TFIB_ERRNO, kLowMemEnd; lia|]. split.
- intros a Ha. pose proof (cif_errno _ _ IMG a Ha) as H. rewrite (ts_errno B HB) in Ha. unfold TFIB_ERRNO in Ha.
  exact (seg_rom_in_img segs a ltac:(lia) H).
- rewrite (ts_code B HB). split; apply (ts_universe_drv B HB); unfold DRV_TRACES; cbn;
  repeat (first [left; reflexivity | right]).
Qed.
(* REC_CELLS: the flag byte is a const cell, the guard's GOT word a const cell and the guard an image byte, and the
   errno cell has image bytes (the core's AR_errno_present) *)
Lemma cmd_rec_cells : forall ly S (W : world segs) mem md, AR segs B ly S W mem md ->
aview segs (w_H W) mem 0xae455 = Some 1 /\ aguard_ok segs W mem 0xa6bf8 0x604158 /\
exists ev, rd32 (aview segs (w_H W) mem) (as_errno B) ev.
Proof using LAWS HB IMG.
intros ly S W mem md HAR. split; [|split].
- exact (cmd_byte_ok segs B LAWS HB ly S W mem md _ _ HAR crf_flag_chk).
- split; [exact (cmd_word_chk segs B LAWS HB ly S W mem md _ _ HAR crf_guard_got_chk)|].
  apply crf_rdword_some. intros k Hk. apply crf_rom_view_some. apply (cif_guard_rom _ _ IMG). lia.
- exact (AR_errno_present segs B W mem (cif_errno _ _ IMG)).
Qed.
(* every byte of g_rec, record.spill and g_quitting is writable: PRW is the core's prog_rw (YCbq.v:1145), and the
   record's ts_prog says that cmd_PG's (lo, hi) ranges are its program statics' (lo, len) ranges *)
Hypothesis PRW : prog_rw segs B.
Lemma PROG_WRITABLE : forall (m : word -> option byte) a, inFP cmd_PG a -> writable_at segs m a.
Proof using LAWS HB PRW.
intros m a Ha. apply (PRW m a). rewrite (ts_prog B HB).
destruct Ha as (r & Hr & Ha). unfold cmd_PG, A_G_REC, A_REC_SPILL, A_G_QUITTING in Hr. unfold TFIB_PROG_STATIC.
destruct Hr as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Ha;
[apply Exists_cons_hd | apply Exists_cons_tl, Exists_cons_hd | apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd];
unfold in_zr; cbn [fst snd]; lia.
Qed.
End cells.

(* PALib's pal_cell and pal_got_shadow over any instance whose object atoms are the listing's (cmd_val_objs) *)
Section pi. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {PI : PAImg cmd_listing}.
Variable B : asyms.
Hypothesis HB : CmdBSyms B.
Hypothesis VOBJS : cmd_val_objs.
Lemma crf_obj12 : nth 12 cmd_objs 0 = 0xb0c38.
Proof using. vm_compute. reflexivity. Qed.
Lemma crf_obj0 : nth 0 cmd_objs 0 = 0xa5f50.
Proof using. vm_compute. reflexivity. Qed.
Lemma cmd_cf_cell : as_shadow_cell B = pa_val (A_OBJ 12).
Proof using HB VOBJS.
rewrite (VOBJS 12%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)), crf_obj12. exact (proj1 (cmd_shadow_cells B HB)).
Qed.
Lemma cmd_cf_got : as_got_shadow B = pa_val (A_OBJ 0).
Proof using HB VOBJS.
rewrite (VOBJS 0%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)), crf_obj0. exact (proj2 (cmd_shadow_cells B HB)).
Qed.
End pi.
Print Assumptions cmd_cf_cell.
Print Assumptions cmd_cf_got.
Print Assumptions cmd_cf_env.
Print Assumptions cmd_cf_grec.
Print Assumptions cmd_cf_lit.
Print Assumptions cmd_rec_cells.
Print Assumptions PROG_WRITABLE.
