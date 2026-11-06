(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the boundary states and segment statements of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86530), the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh6.v (the CL_*_stmtX statements: from a point of the function to its return, under the entry's context) and A/ACf5.v (rtcx, rt_base: the entry's facts bundled once). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths, module names, addresses and numbers changed; 469 of its 518 lines of code are new or changed and 289 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths and module names changed; 100 of its 125 lines of code are new or changed and 493 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3): the KIT of segment B11a of
   reac_segconf_parse_file's walk -- the internal cut points, the state each carries, and the cut statements.
   Statement text only: no machine run is proved here. The B11a segment lane of the image-B G3 walk owner, 2026-10-30.
   ADAPTED from the image-A G3 walk owner's image-A kit lib/A/Prog/pf_a11a_k.v (commit c379667ff414, an
   image-A segment lane): the same form (a context b11_cx, one INV_ / _stmt pair per internal cut, every cut targeting the post
   written with SegModel.r_key's model branch); the cut pcs, the registers and the slots are re-derived from image
   B's code (reac_segconf_parse_file.fuzz_segconf.asan-ubsan.s), which differs from A's in its registers (B keeps
   val in slot 0x70 and cur in slot 0xc0, the fold's index in a6, the destination in slot 0x90) and in the three
   UBSan trap branches to the `unimp` at 0x891c8.

   THE SEGMENT. pf_pieces.v states it as
     S_B11a : forall (f0 : YK11.FPState) (n : nat), HA_MISS n -> HA_LOWOUT n -> H_MODEL (fx := f0) B n.
   MODEL 0x886d4 -> MISS 0x88a50 (reac_box_catalogue_by_token returned NULL) or LOWOUT 0x88c70 (a hit).
   91 instructions over seven ranges (plan section 5.2 row B11a, re-checked against the excerpt): 0x886d4-0x88764,
   0x889a8-0x88a48, 0x89010-0x89028, 0x89034-0x89044, 0x89244-0x8924c, 0x8929c-0x892a4, 0x892a8-0x892ac
   = 36 + 40 + 6 + 4 + 2 + 2 + 1. The last five are the slow arms of the four inline checks (B#18, B#19, B#26, B#27)
   and the error calls they jump to, which do not return.

   THE CODE, with the internal cuts this file names (BASE + AF_reac_segconf_parse_file = 0x87e38):
     MODEL 0x886d4  sb zero,92(s5) / 93 / 94                 model low (F + 0x2e0) comes INTO scope: three SHADOW
                                                             bytes written (cells 0x5c..0x5e), so this run is the
                                                             PLAIN executor
     CHK   0x886e0  a0 = slot 0x70 = vp; check B#18 (load1 at vp; slow arm 0x89010-0x89018, error 0x8929c)
           0x886f4  a2 = val[0]; beqz a2 -> 0x889a8 (a3 = 0, then ZST with li = 0)
           0x886fc  a6 = 0; a1 = vp + 1
     LOOP  0x88704  a3 = 23; beq a6,a3 -> ZST                  the fold loop's head, index li = a6, a2 = val[li]
           0x8870c  a3 = vp + li; a4 = slot 0x90 + li = F + 0x2e0 + li
           0x88718  a5 = ((a2 - 0x41) <u 26) << 5; a2 += a5   the ASCII fold (SegModel.lower)
           0x88728  sb a2,0(a4)                                low[li] = lower(val[li]); NOT instrumented
           0x8872c  beq a3,s10 -> 0x891c8                      UBSan trap T18 (vp + li + 1 wraps; s10 = -1)
           0x88730  a2 = a1 + li = vp + 1 + li; check B#19 (load1; slow arm 0x88758-0x88760, error 0x89244-0x89248)
           0x88744  a2 = val[li + 1]; a6 = li + 1; a3 = a6; beqz a2 -> ZST; j LOOP
     ZST   0x889ac  a0 = slot 0x10 = ~(F + 0x2e0); bltu a0,a3 -> 0x891c8   UBSan trap T21 (low + li wraps)
           0x889b4  a1 = slot 0x90 = low; a0 = low + li; check B#26 (store1; slow arm 0x8901c-0x89024, error
                    0x892a0); 0x889d0 sb zero,0(a0); a0 = low; 0x889d8 jal reac_box_catalogue_by_token
     RBT   0x889dc  beqz a0 -> MISS 0x88a50                    by_token's return
           0x889e0  a0 = slot 0xc0 = cur; andi a0,a0,3; bnez -> 0x891c8   UBSan trap T22 (cur misaligned)
           0x889ec  s3 = cur; a0 = cur + 0x24; a2 = 0x21340 "%s"; a1 = 24; a3 = slot 0x90 = low; 0x88a04 jal snprintf
           0x88a08  a3 = s3; a0 = cur + 0x3c; check B#27 (store4; slow arm 0x89034-0x89040, error 0x892a8)
           0x88a20  sw 1 -> cur->model_set; a0 = cur + 0x40; a2 = "%s"; a1 = 96; a3 = slot 0x48 = &c->reading
           0x88a3c  jal snprintf; 0x88a40 a0 = -8; 0x88a44 `j` LOWOUT 0x88c70

   THE THREE UBSAN TRAP BRANCHES (to the `unimp` 0x891c8), by the fact that keeps each not taken (pf_pieces.v's pf_tf
   and the cut's own facts):
     T18 0x8872c `beq a3,s10` (a3 = vp + li, s10 = -1): vp + li lies in buf, inside the class-5 frame, below 2 ^ 47
         (pf_tf's F + fs_frame_bytes 5 <= 2 ^ 47, pf_inb);
     T21 0x889b0 `bltu a0,a3` (a0 = slot 0x10 = pf_nt (F + 0x2e0), a3 = li <= 23): F + 0x2e0 + li < 2 ^ 64 (pf_tf);
     T22 0x889e8 `bnez (cur & 3)`: cur = c + 356 gi with c mod 16 = 0 (pf_tf) and 356 = 4 * 89.

   THE SPINE STEP. With the two strcasecmp results of H_MODEL (key is not "role", key is "model"),
   SegModel.r_key's model branch is the match on by_token below (pf_seg_B11a_f.v's b11f_r_key). Every cut of this
   file therefore targets [b11_post], the post written with that match; the segment file rewrites H_MODEL's post to
   it once.

   WHAT EVERY INTERNAL CUT CARRIES ([b11_cx]): exactly what INV_MISS (pf_pieces.v) carries but its by_token conjunct
   and its registers -- pf_base at scope PF_SC_L146 (the entry facts, the journal from the entry with the class-5
   frame owned, the caller's objects, the 23 slots, the frame's 144 shadow cells with model low in scope), pf_mid
   (the line account), pf_st (c holds cf, cur = Some gi in slot 0xc0, cur_name, the counters' room), the value in
   buf, and slot 0x70 = vp. Each cut adds its own registers and its own fact about model low. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase refuse_c
  reac_segconf_parse_file_c SegInstB pf_pieces.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(** ** The cut pcs, as listing offsets (BASE + AF_reac_segconf_parse_file = 0x87e38, B's SegList) *)
Definition B11_MODEL : Z := PF_MODEL.                              (* 0x886d4, pf_pieces.v *)
Definition B11_CHK : Z := AF_reac_segconf_parse_file + 0x8a8.      (* 0x886e0 ld a0,112(s1) *)
Definition B11_LOOP : Z := AF_reac_segconf_parse_file + 0x8cc.     (* 0x88704 li a3,23 *)
Definition B11_ZST : Z := AF_reac_segconf_parse_file + 0xb74.      (* 0x889ac ld a0,16(s1) *)
Definition B11_RBT : Z := AF_reac_segconf_parse_file + 0xba4.      (* 0x889dc beqz a0: by_token's return *)
(* the calls and the two returns inside the HIT path *)
Definition B11_CALL_BT : Z := AF_reac_segconf_parse_file + 0xba0.  (* 0x889d8 jal reac_box_catalogue_by_token *)
Definition B11_CALL_SN1 : Z := AF_reac_segconf_parse_file + 0xbcc. (* 0x88a04 jal snprintf (cur->model) *)
Definition B11_RET_SN1 : Z := AF_reac_segconf_parse_file + 0xbd0.  (* 0x88a08 mv a3,s3 *)
Definition B11_CALL_SN2 : Z := AF_reac_segconf_parse_file + 0xc04. (* 0x88a3c jal snprintf (cur->model_file) *)
Definition B11_RET_SN2 : Z := AF_reac_segconf_parse_file + 0xc08.  (* 0x88a40 li a0,-8 *)
(* each cut pc at B's base seg_text (the excerpt's addresses) *)
Lemma b11_cut_pcs :
  seg_text + B11_MODEL = 0x886d4 /\ seg_text + B11_CHK = 0x886e0 /\ seg_text + B11_LOOP = 0x88704 /\
  seg_text + B11_ZST = 0x889ac /\ seg_text + B11_RBT = 0x889dc /\ seg_text + B11_CALL_BT = 0x889d8 /\
  seg_text + B11_CALL_SN1 = 0x88a04 /\ seg_text + B11_RET_SN1 = 0x88a08 /\ seg_text + B11_CALL_SN2 = 0x88a3c /\
  seg_text + B11_RET_SN2 = 0x88a40.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* the fold's cap: `li a3,23` at 0x88704, low[li] with li + 1 < sizeof low = 24 *)
Definition B11_CAP : nat := 23%nat.
(* the byte the fold stores: `addi a5,a2,-65; sltiu a5,a5,26; slli a5,a5,5; add a2,a2,a5` (0x88718-0x88724) *)
Definition B11_FOLD (x : Z) : Z := x + Z.shiftl (Z.b2z ((x + -65) mod 18446744073709551616 <? 26)) 5.

(** ** The post of every cut of this segment: SegModel.r_key's model branch, by cases on by_token *)
Definition b11_step (cf : rconf) (gi : nat) (nm val : list Z) (ln : Z) : rconf * option nat * list Z :=
  match by_token (r_low val 0 24) with
  | None => (refuse cf (ln + 1) F_badmodel [AS nm; AS val; AS known], Some gi, nm)
  | Some _ => (r_upd cf gi (rs_with_model (snprintf_s 24 F_s [AS (r_low val 0 24)])
                                          (snprintf_s 96 F_s [AS (rc_reading cf)])), Some gi, nm)
  end.
(* the record between the two snprintf calls of the hit path: entry gi's model field written (0x88a04), its model_set
   and model_file still the old ones *)
Definition b11_set_model (m : list Z) (s : rseg) : rseg :=
  RSeg (rs_name s) (rs_role s) (rs_role_set s) (rs_ignore s) (rs_ignore_set s) m (rs_model_set s) (rs_model_file s)
       (rs_role_file s) (rs_ignore_file s) (rs_seen_gen s).
Definition b11_cf1 (cf : rconf) (gi : nat) (val : list Z) : rconf :=
  r_upd cf gi (b11_set_model (snprintf_s 24 F_s [AS (r_low val 0 24)])).

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.

Definition b11_post (v : pfv) (cf : rconf) (gi : nat) (nm val : list Z) (o : nat) (ln : Z)
  : world SEGS -> config -> Prop := pf_postm B v (b11_step cf gi nm val ln) o ln.

(** *** What every internal cut carries *)
(* the bytes of model low the fold has written: the first li bytes are the folded prefix of val *)
Definition b11_low (rd : reader) (v : pfv) (pos : Z) (li : nat) (val : list Z) : Prop :=
  forall j, (j < li)%nat -> rd (pf_F v pos + PF_O_L146 + Z.of_nat j) = Some (lower (nth j val 0)).

Definition b11_cx (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) (gi : nat) (vp : Z) (val : list Z) : Prop :=
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_L146 /\ pf_mid v o ln d n /\
  pf_st v pos (rdW Wc memc) cf (Some gi) nm (length (skipn o (p_s v))) /\
  sa_str (rdW Wc memc) vp val /\ pf_inb (pf_F v pos + PF_O_BUF) vp val /\
  pf_sl (rdW Wc memc) (pf_s1 v) [(0x70, vp)].

(** *** CHK (0x886e0): model low in scope, nothing folded yet; the registers are INV_KV's *)
Definition INV_CHK (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) (gi : nat) (vp : Z) (val : list Z) : Prop :=
  b11_cx n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val /\
  pf_rg rX (PF_RL v pos ++ PF_RM v o ln).
Definition B11_CHK_stmt (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val,
  INV_CHK n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val ->
  SRr SEGS Wc (cfg_at SEGS (BASE + B11_CHK) rX memc mdc) (b11_post v cf gi nm val o ln).

(** *** LOOP (0x88704): the fold loop's head at index li. a0 = vp, a1 = vp + 1, a2 = val[li] (not NUL), a6 = li;
    model low[0 .. li) holds the folded prefix. *)
Definition INV_LOOP (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) (gi : nat) (vp : Z) (val : list Z) (li : nat) : Prop :=
  b11_cx n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val /\
  (li <= B11_CAP)%nat /\ (li < length val)%nat /\
  b11_low (rdW Wc memc) v pos li val /\
  pf_rg rX (PF_RL v pos ++ PF_RM v o ln ++
            [(10, vp); (11, vp + 1); (12, nth li val 0); (16, Z.of_nat li)]).
Definition B11_LOOP_stmt (n : nat) (li : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val,
  INV_LOOP n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val li ->
  SRr SEGS Wc (cfg_at SEGS (BASE + B11_LOOP) rX memc mdc) (b11_post v cf gi nm val o ln).

(** *** ZST (0x889ac): the fold is over; a3 = li = |r_low val 0 24|, model low[0 .. li) holds the folded value,
    and 0x889d0 stores its NUL. *)
Definition INV_ZST (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) (gi : nat) (vp : Z) (val : list Z) (li : nat) : Prop :=
  b11_cx n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val /\
  li = length (r_low val 0 24) /\ (li <= B11_CAP)%nat /\
  b11_low (rdW Wc memc) v pos li val /\
  pf_rg rX (PF_RL v pos ++ PF_RM v o ln ++ [(13, Z.of_nat li)]).
Definition B11_ZST_stmt (n : nat) (li : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val,
  INV_ZST n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val li ->
  SRr SEGS Wc (cfg_at SEGS (BASE + B11_ZST) rX memc mdc) (b11_post v cf gi nm val o ln).

(** *** RBT (0x889dc): reac_box_catalogue_by_token has returned a0 = &fuzz_catalogue[i] for the row of the folded
    value, or NULL; model low holds the folded value as a C string. *)
Definition INV_RBT (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) (gi : nat) (vp : Z) (val : list Z) : Prop :=
  b11_cx n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val /\
  sa_str (rdW Wc memc) (pf_F v pos + PF_O_L146) (r_low val 0 24) /\
  pf_rg rX (PF_RL v pos ++ PF_RM v o ln ++ [(10, seg_spec.cat_ptr catA (by_token (r_low val 0 24)))]).
Definition B11_RBT_stmt (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val,
  INV_RBT n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val ->
  SRr SEGS Wc (cfg_at SEGS (BASE + B11_RBT) rX memc mdc) (b11_post v cf gi nm val o ln).

(** *** RS1 (0x88a08, snprintf(cur->model, 24, "%s", low)'s return, at the FP state it returns): the hit path; c
    holds the record with entry gi's model field written (b11_cf1: model = the folded value, model_set and
    model_file still the old ones), s3 = cur (0x889ec, callee-saved). The rest of the hit path (check B#27, the `sw`
    of model_set 0x88a24, snprintf(cur->model_file, 96, "%s", c->reading) 0x88a3c) leads to LOWOUT. *)
Definition INV_RS1 (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) (gi : nat) (vp : Z) (val : list Z) : Prop :=
  b11_cx n v pos lyc Sc Wc rX memc mdc (b11_cf1 cf gi val) nm o ln d gi vp val /\
  (exists i, by_token (r_low val 0 24) = Some i) /\
  pf_rg rX (PF_RL v pos ++ PF_RM v o ln ++ [(19, seg_spec.rseg_addr (p_c v) gi)]).
Definition B11_RS1_stmt (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val,
  INV_RS1 n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val ->
  SRr SEGS Wc (cfg_at SEGS (BASE + B11_RET_SN1) rX memc mdc) (b11_post v cf gi nm val o ln).

End e.
End f.
End d.
