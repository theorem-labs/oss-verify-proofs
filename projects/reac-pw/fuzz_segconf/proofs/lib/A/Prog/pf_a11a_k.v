(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the boundary states and segment statements of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86530), the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh6.v (the CL_*_stmtX statements: from a point of the function to its return, under the entry's context) and A/ACf5.v (rtcx, rt_base: the entry's facts bundled once). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths, module names, addresses and numbers changed; 469 of its 518 lines of code are new or changed and 289 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths and module names changed; 82 of its 107 lines of code are new or changed and 493 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan): the KIT of segment A11a of reac_segconf_parse_file's
   walk -- the internal cut points, the state each carries, and the cut statements. Statement text only: no
   machine run is proved here. Segment A11a's proof, by the G3 walk owner, 2026-10-30.

   THE SEGMENT. pf_pieces.v states it as
     S_A11a : forall (f0 : YK11.FPState) (n : nat), HA_MISS n -> HA_LOWOUT n -> H_MODEL (fx := f0) B n.
   MODEL 0x8826c -> MISS 0x885a8 (reac_box_catalogue_by_token returned NULL) or LOWOUT 0x88774 (a hit).
   84 instructions over seven ranges (reports/pfm.md's table, re-checked against
   dis/reac_segconf_parse_file.fuzz_segconf.asan.s): 0x8826c-0x882f0, 0x88518-0x885a0, 0x88ab4-0x88acc,
   0x88ae4-0x88af4, 0x88cdc-0x88ce8, 0x88d44-0x88d50, 0x88d5c-0x88d60 = 33 + 34 + 6 + 4 + 3 + 3 + 1.
   The last four ranges are the slow arms of the four inline checks (#18, #19, #26, #27) and the error calls
   they jump to, which do not return.

   THE CODE, with the internal cuts this file names:
     MODEL 0x8826c  sb zero,0x5c(s11) / 0x5d / 0x5e         low146 (F + 0x2e0) comes INTO scope: three SHADOW
                                                            bytes written, so this run is the PLAIN executor
     CHK   0x88278  check #18 on s9 = vp (load1)            token run from here on
           0x88288  a2 = val[0]                             lbu 0(s9)
           0x8828c  s4 = slot 0x30 = F + PF_O_L146          the fold's destination
           0x88290  beqz a2 -> 0x88518                      the empty value: ZST with li = 0
           0x88294  a0 = 0; 0x88298 a1 = s9 + 1
     LOOP  0x8829c  a3 = 23; beq a0,a3 -> ZST               the fold loop's head, index li = a0, a2 = val[li]
           0x882a4  a3 = ((a2 - 0x41) <u 26) << 5; a2 += a3 the ASCII fold (SegModel.lower)
           0x882b4  a3 = s4 + a0; sb a2,0(a3)               low146[li] = lower(val[li]); NOT instrumented
           0x882bc  a2 = a1 + a0                            = vp + 1 + li
           0x882c0  check #19 on a2 (load1)
           0x882d0  a2 = val[li + 1]; a0 = li + 1; a3 = a0
           0x882dc  bnez a2 -> LOOP                         else fall to 0x882e0 `j` ZST
           0x88518  a3 = 0                                  the empty-value path joins here
     ZST   0x8851c  a0 = s4 + a3                            &low146[li]
           0x88520  check #26 (store1); 0x88530 sb zero,0(a0)
           0x88534  a0 = s4; 0x88538 jal reac_box_catalogue_by_token
           0x8853c  beqz a0 -> MISS 0x885a8
     HIT   0x88540  a4 = slot 0xb0 = cur = &c->seg[gi]
           0x88544  a0 = cur + 0x24 (cur->model); a2 = 0x21340 = F_s (A_OBJ 35); a1 = 24; a3 = s4 = low146
           0x88558  s4 = a4 = cur; 0x8855c jal snprintf
           0x88560  a0 = cur + 0x3c; check #27 (store4); 0x88578 sw 1 -> cur->model_set
           0x8857c  a0 = cur + 0x40 (cur->model_file); a2 = F_s; a1 = 96; a3 = slot 0x58 = &c->reading
           0x88590  jal snprintf
           0x88594  s8 = slot 0x90 = c; 0x88598 a0 = -8; 0x8859c `j` LOWOUT 0x88774

   THE SPINE STEP. With the two strcasecmp results of H_MODEL (key is not "role", key is "model"),
   SegModel.r_key's model branch is the match on by_token below (pf_a11a_f.v's a11f_r_key, the port of the
   plain walk's pf_p7_lemmas.v p7_r_key at commit cfdd99183965). Every cut of this file therefore
   targets [a11_post], the post written with that match; pf_a11a.v rewrites it to H_MODEL's post once.

   WHAT EVERY INTERNAL CUT CARRIES ([a11_cx]): exactly what INV_MISS / INV_LOWOUT (pf_pieces.v) carry minus
   their own conjuncts -- pf_base at scope PF_SC_L146 (the entry facts, the journal from the entry with the
   class-5 frame owned, the caller's objects, the 19 slots, the frame's 144 shadow cells), pf_mid (the line
   account), pf_st (c holds cf, cur = Some gi, cur_name, the counters' room), the value in buf, and slot 0xb0.
   Each cut adds its own registers and its own fact about low146.
   These survive the three calls of the segment: reac_box_catalogue_by_token's post keeps every byte outside
   its own stack window (sa_kept ... (fun _ => False), its _c.v), and each snprintf keeps every byte outside
   its destination and its scratch window (RtPFCmd.v's cmd_asnprintf_realizes), and the destinations lie in
   the block c, inside this walk's footprint seg_spec.RC_PARSE_W c. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable SegSyms SegList SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase refuse_c
  reac_segconf_parse_file_c SegInstA pf_pieces.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(** ** The cut pcs, as listing offsets (BASE + AF_reac_segconf_parse_file = 0x87a78) *)
Definition A11_MODEL : Z := PF_MODEL.                             (* 0x8826c, pf_pieces.v *)
Definition A11_CHK : Z := AF_reac_segconf_parse_file + 0x800.     (* 0x88278 *)
Definition A11_LOOP : Z := AF_reac_segconf_parse_file + 0x824.    (* 0x8829c *)
Definition A11_ZST : Z := AF_reac_segconf_parse_file + 0xaa4.     (* 0x8851c *)
Definition A11_HIT : Z := AF_reac_segconf_parse_file + 0xac8.     (* 0x88540 *)
(* the two returns inside the segment: by_token's and the first snprintf's *)
Definition A11_RET_BT : Z := AF_reac_segconf_parse_file + 0xac4.  (* 0x8853c *)
Definition A11_RET_SN1 : Z := AF_reac_segconf_parse_file + 0xae8. (* 0x88560 *)
Definition A11_RET_SN2 : Z := AF_reac_segconf_parse_file + 0xb1c. (* 0x88594 *)

(* the fold's cap: `addi a3, zero, 0x17` at 0x8829c, low[li] with li + 1 < sizeof low = 24 *)
Definition A11_CAP : nat := 23%nat.
(* the index the fold's byte test uses: `addi a3, a2, -0x41`, `sltiu a3, a3, 0x1a`, `slli a3, a3, 5` *)
Definition A11_FOLD (x : Z) : Z := x + Z.shiftl (Z.b2z ((x + -65) mod 18446744073709551616 <? 26)) 5.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.

(** *** The post of every cut of this segment: SegModel.r_key's model branch, by cases on by_token *)
Definition a11_step (cf : rconf) (gi : nat) (nm val : list Z) (ln : Z) : rconf * option nat * list Z :=
  match by_token (r_low val 0 24) with
  | None => (refuse cf (ln + 1) F_badmodel [AS nm; AS val; AS known], Some gi, nm)
  | Some _ => (r_upd cf gi (rs_with_model (snprintf_s 24 F_s [AS (r_low val 0 24)])
                                          (snprintf_s 96 F_s [AS (rc_reading cf)])), Some gi, nm)
  end.
Definition a11_post (v : pfv) (cf : rconf) (gi : nat) (nm val : list Z) (o : nat) (ln : Z)
  : world SEGS -> config -> Prop := pf_postm B v (a11_step cf gi nm val ln) o ln.

(** *** What every internal cut carries *)
(* the bytes of low146 the fold has written: the first li bytes are the folded prefix of val *)
Definition a11_low (rd : reader) (v : pfv) (pos : Z) (li : nat) (val : list Z) : Prop :=
  forall j, (j < li)%nat -> rd (pf_F v pos + PF_O_L146 + Z.of_nat j) = Some (lower (nth j val 0)).

Definition a11_cx (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) (gi : nat) (vp : Z) (val : list Z) : Prop :=
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_L146 /\ pf_mid v o ln d n /\
  pf_st v pos (rdW Wc memc) cf (Some gi) nm (length (skipn o (p_s v))) /\
  sa_str (rdW Wc memc) vp val /\ pf_inb (pf_F v pos + PF_O_BUF) vp val /\
  pf_sl (rdW Wc memc) (pf_s1 v) [(0xb0, seg_spec.rseg_addr (p_c v) gi)].

(** *** CHK (0x88278): low146 in scope, nothing folded yet; the registers are INV_KV's *)
Definition A11_INV_CHK (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) (gi : nat) (kp vp : Z) (key val : list Z) : Prop :=
  a11_cx n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val /\
  pf_kv (rdW Wc memc) v pos (pf_tline (p_s v) o) kp vp key val /\
  pf_rg rX (PF_RL v pos ++ PF_RM v o ln ++
            [(20, seg_spec.rseg_addr (p_c v) gi); (23, kp); (25, vp)]).
Definition A11_CHK_stmt (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf nm o ln d gi kp vp key val,
  A11_INV_CHK n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi kp vp key val ->
  SRr SEGS Wc (cfg_at SEGS (BASE + A11_CHK) rX memc mdc) (a11_post v cf gi nm val o ln).

(** *** LOOP (0x8829c): the fold loop's head at index li. a0 = li, a1 = vp + 1, a2 = val[li] (not NUL),
    a3 is dead (0x8829c overwrites it), s4 = low146; low146[0 .. li) holds the folded prefix. *)
Definition A11_INV_LOOP (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) (gi : nat) (vp : Z) (val : list Z) (li : nat) : Prop :=
  a11_cx n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val /\
  (li <= A11_CAP)%nat /\ (li < length val)%nat /\
  a11_low (rdW Wc memc) v pos li val /\
  pf_rg rX (PF_RL v pos ++ PF_RM v o ln ++
            [(10, Z.of_nat li); (11, vp + 1); (12, nth li val 0);
             (20, pf_F v pos + PF_O_L146); (25, vp)]).
Definition A11_LOOP_stmt (n : nat) (li : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val,
  A11_INV_LOOP n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val li ->
  SRr SEGS Wc (cfg_at SEGS (BASE + A11_LOOP) rX memc mdc) (a11_post v cf gi nm val o ln).

(** *** ZST (0x8851c): the fold is over; a3 = li = |r_low val 0 24|, s4 = low146, low146[0 .. li) holds the
    folded value, and 0x88530 stores its NUL. *)
Definition A11_INV_ZST (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) (gi : nat) (vp : Z) (val : list Z) (li : nat) : Prop :=
  a11_cx n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val /\
  li = length (r_low val 0 24) /\ (li <= A11_CAP)%nat /\
  a11_low (rdW Wc memc) v pos li val /\
  pf_rg rX (PF_RL v pos ++ PF_RM v o ln ++
            [(13, Z.of_nat li); (20, pf_F v pos + PF_O_L146); (25, vp)]).
Definition A11_ZST_stmt (n : nat) (li : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val,
  A11_INV_ZST n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val li ->
  SRr SEGS Wc (cfg_at SEGS (BASE + A11_ZST) rX memc mdc) (a11_post v cf gi nm val o ln).

(** *** HIT (0x88540): by_token found row i; low146 holds the folded value as a C string; a0 is the row's
    address (not NULL, which is why the branch at 0x8853c fell through), s4 is still low146. *)
Definition A11_INV_HIT (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) (gi : nat) (vp : Z) (val : list Z) (i : nat) : Prop :=
  a11_cx n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val /\
  by_token (r_low val 0 24) = Some i /\
  sa_str (rdW Wc memc) (pf_F v pos + PF_O_L146) (r_low val 0 24) /\
  pf_rg rX (PF_RL v pos ++ PF_RM v o ln ++
            [(10, seg_spec.cat_ptr catA (Some i)); (20, pf_F v pos + PF_O_L146); (25, vp)]).
Definition A11_HIT_stmt (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val i,
  A11_INV_HIT n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val i ->
  SRr SEGS Wc (cfg_at SEGS (BASE + A11_HIT) rX memc mdc) (a11_post v cf gi nm val o ln).

End e.
End f.
End d.
