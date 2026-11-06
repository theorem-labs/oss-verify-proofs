(* proves no function (rule 24; kind: model instance + model rules): fr_RINV for image B and SEG_HEAD's two RINV rules *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the image-B (fuzz_reply.asan-ubsan) twin of lib/A/ReplyRINV.v at f57b3e2d0ca
   (a working branch): fr_RINV, the concrete relational invariant of the entry walk of
   LLVMFuzzerTestOneInput, over lib/B's records (the Section variable `RINV : lfcx -> Z -> lmod -> Prop` of
   lib/B/W_LLVMFuzzerTestOneInput_cut.v :620 and of lib/B/W_LLVMFuzzerTestOneInput_head.v :242), the two SEG_HEAD
   premises over RINV proved against it, and RI_pro: fr_RINV holds at the first head.
   What is here, each with its source in A's file (f57b3e2d0ca lib/A/ReplyRINV.v):
     fr_pair_cost, fr_cost, fr_pair_ok, fr_entry_ok, fr_count, fr_relay, fr_gone, fr_RINV   A :97-181, the same text
       (a comment's W_rep / _cut line reference is B's, and fr_RINV's comment is shortened);
     RI_head_nout_obl, RI_head_skip_obl                                                      A :187-191, the same text,
       over B's lm_clear_O / lm_set_k / hd_kb / hd_k' (lib/B/W_LLVMFuzzerTestOneInput_head.v :246, :248, :250, :251);
     pro_m, RI_pro_obl                                                                       A :293-300, the same text
       (pro_m names pro_new_src, a verbatim copy of lib/B/W_op_add.v :148-149 oa_new_src; see the swaps);
     RI_head_nout_holds_b, RI_pro_holds_b (the satisfiability witness)                       A :633-634, :636-665;
     fr_pair_ok_mono, fr_Forall2_impl, fr_step_k, RI_head_skip_holds_b                       A :767-776, :780-802;
     RI_head_nout_b, RI_head_skip_b: the premises RI_head_nout (_head.v :274) and RI_head_skip (_head.v :278) in their
       exact text with RINV := fr_RINV.
   Read A's header (A :3-37) for why fr_RINV has this shape (the counting invariant, no bound on t, the split cost bound,
   KEEP UNCONSTRAINED); every reason carries over: the model, its records' fields and the C program are the same.
   The other obligations of A's file (drain, small, write, exit, add, gone, remove arms) are not here: B has no segment
   file for those arms at cb5e14dbcf9, and SEG_HEAD's premises need none of them.
   A -> B swaps (A at f57b3e2d0ca, B at cb5e14dbcf9):
     imports (where A Imports a lib/A module, this file Imports lib/B's, in A's order):
       lib/A/AB1v (A :54)                            -> lib/B/YB1v (as _head.v :55)
       lib/Reusable/YE01 (A :55), lib/A/AE2k (A :56) -> lib/B/YE01, lib/B/YE2k (as _head.v :57)
       lib/A/ACfn, Imported (A :59)                  -> lib/B/YCfn, Required only (as _head.v :60, _cut.v :138)
       lib/A/W_syms .. W_journal (A :61-62)          -> lib/B's files of the same names (as _head.v :62-63)
       lib/A/W_rep W_contract W_sites W_frame (A :70) -> lib/B's files of the same names
       lib/A/W_op_add (A :70)                        -> NOT loaded: lib/B/W_op_add.v does not compile at cb5e14dbcf9
         (line 1239: "Expects a disjunctive pattern with 1 branch or a conjunctive pattern made of 2 patterns"); the
         one name A reads from it, oa_new_src (B W_op_add.v :148-149), is copied verbatim below as pro_new_src
       (none in A)                                   -> lib/B/ReplyGuardB, Required (as _head.v :67: RelocB's sink guard)
       lib/A/W_LLVMFuzzerTestOneInput_cut (A :71)    -> lib/B/W_LLVMFuzzerTestOneInput_cut
       lib/A/W_LLVMFuzzerTestOneInput_head (A :73)   -> lib/B/W_LLVMFuzzerTestOneInput_head
     not loaded: A's lib/A W_LLVMFuzzerTestOneInput_small _write _drain _event _exit _add (A :73-75; no lib/B file at
       cb5e14dbcf9); lib/Prog RelayRunT relay_remove_b_c relay_instance_gone_b_c (A :65-66) and SlotReads SlotDrain3
       SlotPass2Aux (A :69), Required only in A for the arms' proofs not ported here.
     names (each from the Import above; the text that names it is unchanged):
       lfcx, c_n, lf_base      A _cut.v :235, :238    -> B _cut.v :320, :323
       lmod, lm_*, LM          A _cut.v :287          -> B _cut.v :375
       OPS_MAX                 A _cut.v :99           -> B _cut.v :197
       in_byte, picks          A _cut.v :361-362      -> B _cut.v :447-448
       nopen, pick             A _cut.v :370, :372    -> B _cut.v :456, :458
       fr_RG                   A _cut.v :102          -> B _cut.v :200 (fr_globals_b)
       ctl, ct_cl .. ct_ei     A W_rep.v :56          -> B W_rep.v :57
       aout_at                 A W_rep.v :185         -> B W_rep.v :176
       oa_new_src              A W_op_add.v :124      -> pro_new_src below, a verbatim copy of B W_op_add.v :148-149
       ra_new                  A W_contract.v :1141   -> B W_contract.v :1131 (same text)
       lm_clear_O, lm_set_k    A _head.v :386, :998   -> B _head.v :246, :248
       hd_kb, hd_k'            A _head.v :1000-1001   -> B _head.v :250-251
     The model types rentry / hsrc / hlist and the plain proof's notions (keys_total, keys_texts, same_set, texts,
     SlotInv's ecap_ok / WRITE_MAX / slot_open) are lib/Prog's, shared by both images.
     B's lf_base takes the same seven Section variables as A's (B MT XM_LIB RLO RHI fr_live_pre G_fr), and its
     fr_lib_pre_cf the same first nine conjuncts in the same order, so RI_pro_holds_b's destruct patterns are A's.
     B's Context adds {SK : YI16.sink_head}: lib/B/ReplyGuardB.v removes the sink classes' hints, so lf_base's sink
     argument comes from the Context (as _head.v :137).
  CONSTANT-SWAP TABLE: every constant this file's text reads.  Each B value is read from image B's own binary
  (fuzz_reply.asan-ubsan, sha256 10ffb5f9202ae2bd..., through its fuzz_reply.objdump.txt (sha256 17f5c434bf57; internal record)) or
  from a file at cb5e14dbcf9; none is A's value plus an offset.
    name                        | A value | B value | where B's value comes from
    OPS_MAX                     | 512     | 512     | B _cut.v :197; B binary 0x84818 `li a0,512`, 0x8481c `bne s9,a0` (the
                                |         |         | loop's bound)
    FIRST_FD (fr_relay, pro_m)  | 100     | 100     | B binary op_add 0x8523c `addiw a0,a1,100` (the new fd, 100 + g_nfd)
    slots (length lm_hs, < 4)   | 4       | 4       | B binary 0x84664 `li a4,4` (the open-count loop); op_add 0x851e0
                                |         |         | `li a0,384` with the stride 0x851fc `addi s2,s2,96` (384 / 96)
    CLIENT_FD (fr_gone, = 3)    | 3       | 3       | B binary 0x84544 `li a0,3`, 0x84558 `sw a0,32(a3)` to g_client 0xa2560
    g_client after finish (-1)  | -1      | -1      | B binary relay_finish 0x82440 `li a1,-1`, 0x82444 `sw a1,292(a0)` to
                                |         |         | g_client 0xa2560
    op modulus (mod 10)         | 10      | 10      | B binary 0x8460c `li a2,10`, 0x84610 `mul`, 0x84614 `sub` (op = b % 10)
    input bound (c_n < 2 ^ 26)  | 2 ^ 26  | 2 ^ 26  | B _cut.v :247 (fr_lib_pre_cf), :398 (ainput_at); B binary 0x8451c
                                |         |         | `srli a0,s5,0x1a`, 0x84530 `bnez a0,85014` (the size refusal)
    held capacity (< 2 ^ 24)    | 2 ^ 24  | 2 ^ 24  | no image value: the model bound of lib/Prog/SlotInv.v :263 (pair_ok),
                                |         |         | one file for both images
    SlotInv.WRITE_MAX           | 65535   | 65535   | no image value: lib/Prog/SlotInv.v :25, one file for both images
    SlotInv.ecap_ok             | (def.)  | (def.)  | no image value: lib/Prog/SlotInv.v :98, one file for both images *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01 YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep CheckRep RelayKeys RelayModel ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require drain_b_c gestures_end_b_c SlotInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_sites W_frame.
(* RelocB's sink-instance guard (after the Import of YE2k), as lib/B's segment files Require it *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_head.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section rinv.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
(* _cut's Section w parameters that RI_pro's lf_base names (A :84-89); fr_RINV itself names none of them *)
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable fr_live_pre : astate -> Prop.
Variable G_fr : list (Z * Z).

(* ================================================================== fr_RINV *)
(* The cost of one relay entry and the source it is paired with: the bytes the controller may still be sent for
   them (the gesture ends of the held keys, keys_total = |text| + 5 each), the worker's bytes not yet read (the
   pending stream) and the relay's unfinished line when it keeps it (re_skip = 0).  SlotInv.v:55-56 pair_cost, with
   length (re_U e) for re_used e (see A's header). *)
Definition fr_pair_cost (e : rentry) (p : hsrc * nat) : Z :=
  gestures_end_b_c.keys_total (re_keys e) + Z.of_nat (length (pending_stream (fst p))) +
  (if re_skip e =? 0 then Z.of_nat (length (re_U e)) else 0).
(* SlotInv.v:58-59 slot_cost *)
Definition fr_cost (es : list rentry) (hj : list (hsrc * nat)) : Z :=
  fold_right Z.add 0 (map (fun q => fr_pair_cost (fst q) (snd q)) (combine es hj)).

(* One relay entry e and the open harness source p = (h, slot) with the same fd, after t operations: the model
   clauses of SlotInv.v:253-263 pair_ok. *)
Definition fr_pair_ok (m : lmod) (t : Z) (e : rentry) (p : hsrc * nat) : Prop :=
  let h := fst p in
  (* SlotInv.v:256 (src_at at g_s + 96 * slot, a slot < 4): the source is the model's slot *)
  (snd p < 4)%nat /\ nth (snd p) (lm_hs m) None = Some h /\
  (* SlotInv.v:257: the entry follows the source's fd (op_add's relay_add(g_s[i].fd), fuzz_reply.c:581, :590) *)
  hs_fd h = re_fd e /\
  (* SlotInv.v:258: while the relay reads the source, its unfinished line is the reference splitter's
     (relay.c's buffer and fuzz_reply.c:217-240 reference_feed see the same bytes) *)
  (re_eof e = 0 -> re_skip e = hs_overlong h /\ (re_skip e = 0 -> bzs (re_U e) = bzs (hs_W h))) /\
  (* SlotInv.v:259: the relay holds a key for exactly the gestures the harness holds open (fuzz_reply.c:49-51) *)
  same_set (drain_b_c.keys_texts (re_keys e)) (texts (hs_held h)) /\ NoDup (texts (hs_held h)) /\
  (* SlotInv.v:260: between operations check_no_loss has emptied the expected list (fuzz_reply.c:607, :627) *)
  hl_recs (hs_expected h) = [] /\
  (* SlotInv.v:263: the capacities the list growth keeps in range *)
  SlotInv.ecap_ok (hl_cap (hs_expected h)) /\ hl_cap (hs_held h) < 2 ^ 24 /\
  (* SlotInv.v:262: the worker's unread bytes, at most one write of fuzz_take(fuzz_u16) per operation
     (fuzz_reply.c:705-707); with t < OPS_MAX at a drain this keeps the expected list's capacity ecap_ok *)
  Z.of_nat (length (pending_stream h)) <= SlotInv.WRITE_MAX * t /\
  (* the pending list's read offset (B W_rep.v asrc_at): the drain model reads from it *)
  0 <= hs_off h.

(* The model facts of one relay entry (B W_rep.v aentry_ok, model clauses; SlotInv's relay_at:269 entry_ok): eof is a
   flag, the struct's two 4-byte paddings, one key per held gesture text, and skip is a flag. *)
Definition fr_entry_ok (e : rentry) : Prop :=
  (re_eof e = 0 \/ re_eof e = 1) /\
  length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat /\
  NoDup (drain_b_c.keys_texts (re_keys e)) /\
  (re_skip e = 0 \/ re_skip e = 1).

(* (1) the counting invariant after t operations.  fuzz_reply.c:681, :684: the prologue's op_add opens slot 0 with
   g_nfd = 1 (2 * 1 <= 0 + 1 + 1); :581: an op_add that opens a slot raises g_nfd and the open count by one (both
   sides + 2); :630 (source_reset, :537 memset): op_remove closes one slot (the right side - 1 + 1); every other
   operation, and an op_add with no free slot (:577-578), keeps both counts (the right side + 1).  amodel_at's
   g_nfd range (B _cut.v :393) is restated because RINV-only rules read the fds' range. *)
Definition fr_count (t : Z) (m : lmod) : Prop :=
  2 * lm_nfd m <= t + 1 + nopen (lm_hs m) /\ 0 <= lm_nfd m <= OPS_MAX.

(* (2) the relay's table is exactly the open slots, each once (SlotInv.v:265-276 relay_at, model clauses).
   fuzz_reply.c:581, :590: op_add appends the entry of the fd FIRST_FD + g_nfd (FIRST_FD = 100, :117) for the slot it
   opens; :624, :630: op_remove removes the picked slot's entry (relay_remove) and closes the slot (source_reset);
   drain (:604), relay_instance_gone (:642) and the default arm (:733-737) keep the table's fds; pick (:550-561)
   returns only an open slot. *)
Definition fr_relay (cx : lfcx) (t : Z) (m : lmod) : Prop :=
  length (lm_hs m) = 4%nat /\
  NoDup (map re_fd (lm_es m)) /\
  Forall (fun e => 100 <= re_fd e < 100 + lm_nfd m) (lm_es m) /\
  Forall fr_entry_ok (lm_es m) /\
  exists hj : list (hsrc * nat),
    (* each entry with its source, in the relay's table order *)
    Forall2 (fr_pair_ok m t) (lm_es m) hj /\
    (* each slot at most once *)
    NoDup (map snd hj) /\
    (* a slot no entry follows is closed (SlotInv.v:274-275: its 96 bytes zero; here the model's None) *)
    (forall i, (i < 4)%nat -> SlotInv.slot_open hj i = false -> nth i (lm_hs m) None = None) /\
    (* the input-cost bound (SlotInv.v:313 slot_cost <= k, and k <= n, :300) *)
    fr_cost (lm_es m) hj <= lm_k m /\ fr_cost (lm_es m) hj <= c_n cx.

(* the controller's flags against g_gone (SlotInv.v:240 globals_at): until the default arm (fuzz_reply.c:733-737)
   the controller is connected (g_client = CLIENT_FD = 3), not broken and its sends not dead; after it, one of the
   three says so *)
Definition fr_gone (m : lmod) : Prop :=
  (lm_gn m = 0 -> ct_cl (lm_c m) = 3 /\ ct_br (lm_c m) = 0 /\ ct_dd (lm_c m) = 0) /\
  (lm_gn m = 1 -> ct_cl (lm_c m) = -1 \/ ct_br (lm_c m) = 1 \/ ct_dd (lm_c m) = 1).

(* the relational invariant after t operations.  The input bound is SlotInv.v:300's ss_n E < INPUT_MAX (the
   contract's 0 < n < 2 ^ 26, B _cut.v :398 ainput_at), restated because the cost bound reads it in RINV-only rules.
   KEEP UNCONSTRAINED (A :172-179): fr_RINV reads only lm_es, lm_hs, lm_k, lm_nfd, lm_gn and lm_c's ct_cl / ct_br /
   ct_dd; a clause on lm_out, lm_cap, lm_O, lm_mx, ct_ei, ctl's errno field or the stream makes the remove and drain
   arms' rules unsatisfiable. *)
Definition fr_RINV (cx : lfcx) (t : Z) (m : lmod) : Prop :=
  fr_count t m /\ fr_relay cx t m /\ c_n cx < 2 ^ 26 /\ fr_gone m.

(* ================================================================== the obligations *)
(* lib/B/W_LLVMFuzzerTestOneInput_head.v :274 RI_head_nout (g_nout := 0 at 0x8461c) *)
Definition RI_head_nout_obl : Prop := forall cx t m, fr_RINV cx t m -> fr_RINV cx t (lm_clear_O m).
(* lib/B/W_LLVMFuzzerTestOneInput_head.v :278 RI_head_skip (`continue` at 0x8471c -> 0x8480c) *)
Definition RI_head_skip_obl : Prop := forall cx t m, 0 <= t < OPS_MAX -> 0 <= lm_k m < c_n cx -> lm_O m = [] ->
  picks (in_byte cx (lm_k m) mod 10) = true -> in_byte cx (lm_k m) mod 10 <> 1 ->
  pick (lm_hs m) (hd_kb cx m) = None -> fr_RINV cx t m -> fr_RINV cx (t + 1) (lm_set_k m (hd_k' cx m)).

(* The source op_add opens (descriptor fd, the 6000-byte buffer q, everything else zero; lib/Prog/op_add_c.v:22
   new_src): a VERBATIM COPY of lib/B/W_op_add.v :148-149 oa_new_src, which this file cannot load (that file does not
   compile at cb5e14dbcf9, see the header); replace it by W_op_add.oa_new_src when W_op_add.v builds. *)
Definition pro_new_src (fd q : Z) (pj : list byte) : hsrc :=
HS fd 1 0 0 empty_list 0 q pj 0 0 [] empty_list empty_list.
(* The model at the first head: A's copy (A :292-294) of a working branch a7e2bf5856c
   lib/A/W_LLVMFuzzerTestOneInput_pro.v :203 pro_m.  B has no _pro.v at cb5e14dbcf9 (its SEG_PRO, B _cut.v :739, is a
   Section hypothesis whose INV_H model is existential); the prologue is the same C code (fuzz_reply.c:681-684:
   op_add opens slot 0 with fd FIRST_FD = 100 and g_nfd = 1, the relay's table has its one entry), so the model is
   A's, over B's LM (B _cut.v :375, the same eleven fields in the same order). *)
Definition pro_m (q T' : Z) (pj : list byte) (c : ctl) (O : list byte) (cap out : Z) : lmod :=
  LM 0 [Some (pro_new_src 100 q pj); None; None; None] T' [ra_new 100] c O 0 cap out 0 1.
(* A :295-300 RI_pro (pro-a2 _pro.v:205), over B's lf_base.  MT and fr_live_pre are this Section's variables, so
   RI_pro_holds_b holds at EVERY meter and every live-state clause, not at a chosen one (in particular not only at
   ameter_triv) *)
Definition RI_pro_obl : Prop := forall cx q T' pj c O cap out,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  (exists c0 mx0, aout_at B fr_RG (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) c0 O mx0 (Z.of_nat (length O)) cap out) ->
  ct_cl c = 3 -> ct_br c = 0 -> ct_dd c = 0 -> ct_ei c = 0 ->
  fr_RINV cx 0 (pro_m q T' pj c O cap out).

(* ================================================================== proofs *)
(* g_nout := 0 changes lm_O only, which fr_RINV does not read (A :633-634) *)
Lemma RI_head_nout_holds_b : RI_head_nout_obl.
Proof. intros cx t m H. exact H. Qed.

(* fr_RINV holds at the first head (A :636-665): it is not vacuous *)
Lemma RI_pro_holds_b : RI_pro_obl.
Proof.
  intros cx q T' pj c O cap out HB _ Hcl Hbr Hdd _.
  assert (Hn : 0 <= c_n cx < 2 ^ 26).
  { destruct HB as (_ & _ & _ & _ & _ & Hn & _). destruct Hn as [(Hz & _) | (Hn & _)]; lia. }
  split; [|split; [|split]].
  - unfold fr_count, pro_m, nopen, OPS_MAX. cbn. lia.
  - unfold fr_relay, pro_m. cbn [lm_hs lm_es lm_nfd lm_k].
    split; [reflexivity|].
    split; [apply NoDup_ListNoDup; repeat constructor; intros []|].
    split; [constructor; [cbn; lia | constructor]|].
    split.
    { constructor; [|constructor]. unfold fr_entry_ok. cbn.
      split; [left; reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [apply NoDup_ListNoDup; constructor | left; reflexivity]. }
    exists [(pro_new_src 100 q pj, 0%nat)].
    split.
    { constructor; [|constructor]. unfold fr_pair_ok. cbn.
      split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
      split; [intros _; split; [reflexivity | intros _; reflexivity]|].
      split; [intros y; split; intros []|]. split; [apply NoDup_ListNoDup; constructor|]. split; [reflexivity|].
      split; [left; reflexivity|]. split; [lia|]. split; [unfold SlotInv.WRITE_MAX; lia | lia]. }
    split; [apply NoDup_ListNoDup; repeat constructor; intros []|].
    split.
    { intros i Hi Ho. destruct i as [|[|[|[|i]]]]; cbn in Ho |- *;
        first [discriminate Ho | reflexivity | lia]. }
    unfold fr_cost, fr_pair_cost. cbn. lia.
  - exact (proj2 Hn).
  - unfold fr_gone, pro_m. cbn [lm_gn lm_c]. split; intros H; [auto | discriminate H].
Qed.

(* ---- the steps that keep the table and the open slots (A :766-794) *)
Lemma fr_pair_ok_mono : forall m m' t t' e p, lm_hs m' = lm_hs m -> t <= t' ->
  fr_pair_ok m t e p -> fr_pair_ok m' t' e p.
Proof.
  intros m m' t t' e p E Ht (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
  rewrite <- E in H2. unfold SlotInv.WRITE_MAX in H10.
  repeat (split; [assumption|]). split; [unfold SlotInv.WRITE_MAX; lia | exact H11].
Qed.
Lemma fr_Forall2_impl : forall (T1 T2 : Type) (R R' : T1 -> T2 -> Prop) l1 l2,
  (forall x y, R x y -> R' x y) -> Forall2 R l1 l2 -> Forall2 R' l1 l2.
Proof. intros T1 T2 R R' l1 l2 H HF. induction HF; constructor; auto. Qed.
(* an operation that keeps the slots, the table and g_nfd, moves the cursor forward and keeps the flags' link *)
Lemma fr_step_k : forall cx t m m', fr_RINV cx t m ->
  lm_hs m' = lm_hs m -> lm_es m' = lm_es m -> lm_nfd m' = lm_nfd m -> lm_k m <= lm_k m' -> fr_gone m' ->
  fr_RINV cx (t + 1) m'.
Proof.
  intros cx t m m' ((HC & Hnfd) & HR & Hn & _) Ehs Ees Enfd Hk HG.
  destruct HR as (Hlen & Hnd & Hrng & Hent & hj & HF & HNDs & Hcl & Hc & Hcn).
  split; [|split; [|split; [exact Hn | exact HG]]].
  - unfold fr_count. rewrite Ehs, Enfd. lia.
  - unfold fr_relay. rewrite Ehs, Ees, Enfd.
    split; [exact Hlen|]. split; [exact Hnd|]. split; [exact Hrng|]. split; [exact Hent|].
    exists hj.
    split; [exact (fr_Forall2_impl _ _ _ _ _ _ (fun e p => fr_pair_ok_mono m m' t (t + 1) e p Ehs ltac:(lia)) HF)|].
    split; [exact HNDs|]. split; [exact Hcl|]. split; [lia | exact Hcn].
Qed.

(* _head.v :278: `continue` (an op that picks, no open source, op <> 1) consumes the input bytes only (A :797-802) *)
Lemma RI_head_skip_holds_b : RI_head_skip_obl.
Proof.
  intros cx t m _ _ _ _ _ _ H. apply (fr_step_k cx t m _ H); try reflexivity.
  - unfold lm_set_k, hd_k'. cbn [lm_k]. destruct (lm_k m + 1 <? c_n cx); lia.
  - destruct H as (_ & _ & _ & HG). exact HG.
Qed.

(* ================================================================== the two premises, as lf_seg_head_b takes them
   lib/B/W_LLVMFuzzerTestOneInput_head.v :274 and :278, text for text, with RINV := fr_RINV *)
Lemma RI_head_nout_b : forall cx t m, fr_RINV cx t m -> fr_RINV cx t (lm_clear_O m).
Proof. exact RI_head_nout_holds_b. Qed.
Lemma RI_head_skip_b : forall cx t m, 0 <= t < OPS_MAX -> 0 <= lm_k m < c_n cx -> lm_O m = [] ->
  picks (in_byte cx (lm_k m) mod 10) = true -> in_byte cx (lm_k m) mod 10 <> 1 ->
  pick (lm_hs m) (hd_kb cx m) = None -> fr_RINV cx t m -> fr_RINV cx (t + 1) (lm_set_k m (hd_k' cx m)).
Proof. exact RI_head_skip_holds_b. Qed.
End rinv.
