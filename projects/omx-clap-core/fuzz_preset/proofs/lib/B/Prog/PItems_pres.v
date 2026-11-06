(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the SEGMENT PRES of parse_items' image-B walk, in ONE file, so that
   every segment file imports the pres it needs and holds only lemmas and Section hypotheses (the neighbours' LEMMA
   statements): pres living in the segment files made import cycles (Entry <-> Head, Body <-> Value;
   01:0xZ). Texts as published for each segment, each tagged with its segment:
     Body        body-iface-v1.v (sha256 65e5ff92...): pi_jrb,
                 pi_jrl_unfold, pi_run_eqB, pi_sblk, pi_post, pi_cur, pi_loop_pre,
                 pi_body_pre, pi_key_pre, pi_free_pre, pi_goal, pi_aj, pi_body_spec;
     Value       the internal file value-iface-v1.txt: pi_val_k, pi_val_eq, pi_key,
                 pi_val_pre (with Body's requested measure N added);
     Head        (IRC 01:0xZ, updated): pi_head_pre, pi_close_pre, PI_O_CLOSE2;
     Entry       the internal file entry-iface-v1.txt: pi_Qstable, pi_epi_pre.
   CHANGES when merging them: the `Context {CN : PrhNames ..}` line is dropped (the class is gone from the kit's
   lib/A/PRH_Base.v (sha256 168022d10e46; internal record)); pi_body_spec quantifies the CURRENT float state too (it is stated after the Section, over
   the generalised constants), so the loop's re-entry after parse_value (which may change the float state) meets
   it; pi_val_pre gains Body's measure argument N.
   THE POST is pi_post = the post of tparse_items_specX, an alias of the text's own PRH_FnParse.tpiP_Q (its hull use
   and injected-reading conjuncts included; read it through tpiP_R_of, build it through tpiP_Q_of_R).
   THE TRAVELLING FACTS of form (b): every block pre carries, inside the existential that
   binds its prefix trace tr0, PItems_posb.pi_posb S Sc tr0 (the run position from the entry state to the block state)
   and PItems_posb.pi_live (the live requests moved by tr0); the entry-keyed rp_* binders and pi_pos are gone. The
   ledger's most / own (g_most, g_own_ran_out) are parameters of every pre and spec, right after ran: every text the
   walk calls keeps them, so they are the entry's at every block and in the post.
   THE ROOM (lib/A/PRH_FnParse.v (sha256 f86c5e872a2d; internal record)): room_live_cf is an INVARIANT (rd_room S gt = room_live_cf S /\ largest
   single request /\ live room, no kr); the kr binders below are VESTIGIAL. Earlier form, superseded: rd_room over the GRANTED trace (PRH_FnParse.v rd_room: margin room,
   request bound, live room). Each block's pre carries ONE conjunct `rd_room Sc gt kr` with gt the granted trace of
   the block's own continuation (jrl / pi_jrb / pi_val_k at ok = []); the head carries the whole call's
   (prhPi_gtrace), the closer ROOM_cf_k Sc kr (nothing left to charge), the missing-colon path RK_free + kr.
   prhPv_rk is additive and LIVE_rd monotone along a trace prefix, so a member call is charged its own granted
   jr_value trace with kr_v = prhPv_rk (the rest after it) + kr.
   EVERY cfg_at names its float state explicitly ((fx := fx) inside the Section, (fx := fxc) in the specs): an
   inferred FPState instance is exactly the hazard the walk brief forbids, and the build showed one was being picked.
   Numerals: 4, 8, 24, 56 LENGTH; 34, 44, 58, 91, 93, 123, 125 WORD (ASCII); 0x520 LENGTH (a byte offset inside the
   body); 2 ^ 64 DERIVED. No ADDRESS.
   THE RE-HIDING MOVE (the texts' current form): the callees parse_string, grow, parse_value and fuzz_free free, so the
   walk runs at the world relation wle' segs RZ_cf (YA0nH): every segment spec takes its journal pi_ajR at wle' and
   concludes pi_goalR at wle' (YA0nH.SRr' and the post fpostWFbm, which is at wle'). pi_goalR / pi_ajR are the forms
   over a relation R beside pi_goal / pi_aj, which are them at wle (pi_goal_R_wle / pi_aj_R_wle). THE HULL (route
   (b)): pi_ent carries the text's hull budget, PItems_posb.pi_posb the block's hull use since the entry. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YG0s YP07 YI00 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YC80 YC80x YPsym YC4aP YImgTop YC1fP YC1fPx YCbqG YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YK06 YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetReqAt PresetRun PresetRoom PresetLiveBounds.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoom YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import
PRH_Base PRH_Reader PRH_FnReader PRH_Charge PRH_FnParse PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PItems_defs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require PItems_posb.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* the second copy of the close-brace block: the instruction after the second closer test, 0x87f58 *)
Definition PI_O_CLOSE2 : Z := 0x520.

(* ---- the grammar after jrl's grow: the rest of one member of PjGrammar.jrl (PjGrammar.v:307-316), verbatim ---- *)
Definition pi_jrb (f d : nat) (o : bool) (n cap1 : nat) (acc : list (list Z * jv)) (y : list Z) : M (jv * list Z) :=
  jbind (jr_name o y) (fun '(name, y1) =>
  jbind (jrv prh_jr_strtod f d y1) (fun '(v, r) =>
  match skip r with
  | c :: r1 =>
    if c =? 44 then jrl prh_jr_strtod f d o (S n) cap1 ((name, v) :: acc) r1
    else if c =? closer o then jret (mk o (rev ((name, v) :: acc)), r1)
    else jrefuse
  | [] => jrefuse
  end)).

Lemma pi_jrl_unfold : forall f d o n cap acc y,
  jrl prh_jr_strtod (S f) d o n cap acc y = jbind (grow o n cap) (fun cap1 => pi_jrb f d o n cap1 acc y).
Proof. reflexivity. Qed.

(* the continuation after grow: as pi_run_eq (PItems_defs.v), with pi_jrb for the loop *)
Definition pi_run_eqB (d : nat) (o : bool) (x0 : list Z) (ok0 : list bool) (tr0 : list PjGrammar.ev)
  (f n cap1 : nat) (acc : list (list Z * PjTree.jv)) (y : list Z) : Prop :=
  forall ok1 r t ok2,
    pi_jrb f (Nat.succ d) o n cap1 acc y ok1 = (r, t, ok2) ->
    PjGrammar.jr_items prh_jr_strtod d o x0 (ok0 ++ ok1) = (r, tr0 ++ t, ok2).


(* the slot blocks of the half-built container, in pj_nodeR's order (PRH_Reader.v kids_blkR / keys_blkR) *)
Definition pi_sblk (o : bool) (kids keys : Z) (cap : nat) : list (Z * Z) :=
  kids_blkR kids (Z.of_nat cap) ++ keys_blkR (if o then 6 else 5) keys (Z.of_nat cap).

Section pres. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PIi : PrhImg}
  {RL : PrhRoomLive}.
Context {L : ptable asym} {PA : PAImg L}.
Local Notation segs := pa_segs.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* the post of tparse_items_specX: the text's own PRH_FnParse.tpiP_Q (tpiP_Q_check: it IS the text's post), in
   PItems_entry.v's argument order; kr is vestigial *)
Definition pi_post (ly : alayout) (S : astate) (d : nat) (o : bool) (tb : list Z) (text len p q v : Z)
  (Lam : list (Z * Z)) (peak cnt fail ran most own : Z) (kr : nat)
  : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  tpiP_Q B d ly S q text len p tb v o Lam peak cnt fail ran most own.

(* the cursor, the text, the node and the ledger at the current state, as every block of the loop holds them (the
   cursor at pc, the depth word d + 1 as the prologue wrote it) *)
Definition pi_cur (regs0 : bvmap 5 word) (e q v text len : Z) (tb : list Z) (d : nat)
  (lyc : alayout) (Sc : astate) (Hpc : list Z) (Wc : world segs) (memc : word -> option byte)
  (pc : Z) (Lamc : list (Z * Z)) (peakc cntc failc ranc most own : Z) : Prop :=
  pj_in_okR segs (rdW Wc memc) q text len pc (Z.of_nat d + 1) tb /\
  range_addressable (aview segs (w_H Wc) memc) SHADOW_OFF q 24 /\
  src_rd Wc memc text tb /\ prhReader_home B lyc Sc Hpc Lamc text len /\
  prhReader_at B lyc Sc Lamc regs0 e v 56 /\ range_addressable (aview segs (w_H Wc) memc) SHADOW_OFF v 56 /\
  prh_ledger B lyc Sc Hpc Wc memc Lamc peakc cntc failc ranc most own /\
  cntc + 2 * Z.of_nat (length (rest_atR tb text pc)) + 2 < 2 ^ 64 - 1.

(* (no CTX premise in the pres, resume 03:5xZ) A state-free CTX predicate over text and len would have to hold for
   EVERY text, which no finite CTX satisfies: the top theorem would then be vacuous. It is not needed: every callee
   text is quantified over its own CTX, so a segment instantiates parse_string / parse_value at CTX' := the actual
   spine at the call (In (raZ :: spine ch) [raZ :: spine ch] is trivial), and the record's prh_free_univ_at (in
   pi_ent) carries the missing-colon free's trace. *)

(* THE LOOP INVARIANT, at a grow call (PjGrammar.jrl's entry). acc is in READING order (pi_cont's); jrl holds it
   newest first, (rev acc). The frame cache is NOT required: the first member reaches 0x87b70 (PI_O_LOOP) before it
   is written. *)
Definition pi_loop_pre (fx0 : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs)
  (mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z)) (CTX : list (list Z)) (regs0 : bvmap 5 word)
  (e q v : Z) (o : bool) (text len : Z) (tb : list Z) (p : Z) (d : nat) (Lam : list (Z * Z))
  (peak cnt fail ran most own : Z) (kr : nat) (lyc : alayout) (Sc : astate) (Hpc : list Z) (Wc : world segs)
  (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word)
  (CTX0 : list (list Z)) (CW : list (list Z)) : Prop :=
  pi_fpok fx0 fx /\
  pi_ent B fx0 ly S Hp W regs0 mem ch CTX Lam peak cnt fail ran most own e q text len p d kr tb v o CTX0 CW /\
  (* the overlay stays normal at THIS block's state: every callee text that reaches strtod asks for it at its call *)
  YAkMemnorm.memnorm segs memc /\
  pi_frame regs0 regs W mem Wc memc e q v /\
  pi_regs regs q v o /\ getr regs 21 = w64 (-1) /\
  exists (f n cap : nat) acc kids keys Di pc ok0 tr0 D0 Lamc peakc cntc failc ranc,
    pi_cur regs0 e q v text len tb d lyc Sc Hpc Wc memc pc Lamc peakc cntc failc ranc most own /\
    (* the loop segment's G4: grow at 0x87b74 adds up to two calls without consuming a byte, and the next
       callee (parse_string at the key, parse_value at an array's value) needs cnt' + 2 |rest| + 2 < 2 ^ 64 - 1 at the
       same rest; so the loop head carries two more. PI_O_LOOP is entered once, from the head, where the opener byte
       pays for it: |rest at pc| <= |rest at p| - 1 and rd_pre's cnt + 2 |rest at p| + 2 < 2 ^ 64 - 1. Later members
       re-enter at PI_O_BODY, after the value segment's second grow, where vspec's calls + 2 |r| <= 2 |x| (PjGrammar.v) and
       the comma byte pay for that grow. *)
    cntc + 2 * Z.of_nat (length (rest_atR tb text pc)) + 4 < 2 ^ 64 - 1 /\
    pi_cont (rdW Wc memc) (prh_lin Lamc) o v kids keys n cap acc Di /\
    (* the members read so far are deep enough for every refusal exit's pj_fdR (MAXD - d) (PItemsValue 06:1xZ) *)
    Forall (fun m => (PjTree.depth (snd m) <= PjGrammar.MAXD - Nat.succ d)%nat) acc /\
    pj_apartR (pi_sblk o kids keys cap) v /\
    Permutation D0 (pi_sblk o kids keys cap ++ Di) /\
    (2 * length (rest_atR tb text pc) + 2 <= f)%nat /\
    pi_run_eq d o (rest_atR tb text p) ok0 tr0 f n cap acc (rest_atR tb text pc) /\
    pi_led Lam peak cnt fail ran most ok0 tr0 D0 Lamc peakc cntc failc ranc /\
    (* the prefix's block move, as the record's post states it, and its byte bound: every exit reads its post's
       rd_blocks_move and blocks_bytes clauses off these (PItemsBody 06:1xZ G2; pi_blk is its projection) *)
    rd_blocks_move B ly S lyc Sc D0 tr0 (rest_atR tb text p) d /\
    (* THE TRAVELLING POSITION AND LIVE REQUESTS (form (b), f97c8b2f046b; PItems_posb.v): the run position from the
       entry state S to this block's state Sc over the prefix trace tr0, and the live requests moved by tr0 *)
    PItems_posb.pi_posb S Sc tr0 /\
    PItems_posb.pi_live (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
      (PresetRoom.rs_live (YGcfRoom.room_of_cf Sc)) tr0 /\
    blocks_bytes Sc <= blocks_bytes S + prh_held tr0 /\ length ok0 = PjGrammar.calls tr0 /\
    Ledger.lsum D0 = PjGrammar.held tr0 /\
    rd_room Sc (snd (fst (jrl prh_jr_strtod f (Nat.succ d) o n cap (rev acc) (rest_atR tb text pc) []))) /\
    (* THE BATCH KIT'S INVARIANTS (PItems_defs.v pi_grant / pi_ncaps / pi_forder / pi_fl_eq, _eqB, _eqV): the granted prefix, the
       capacities, and the free order with the kit's model jfl at this point of the loop *)
    pi_grant ok0 tr0 /\ cap = PresetReqAt.ncap n /\ pi_ncaps (rdW Wc memc) kids acc /\
    exists af, pi_forder (rdW Wc memc) (prh_lin Lamc) o kids keys n Di acc af /\
      pi_fl_eq d o (rest_atR tb text p) ok0 f n cap af (rest_atR tb text pc).

(* AT 0x87bbc (PI_O_BODY), after grow: f is the fuel of jrl's body, slot n is free (n < cap), the frame cache is
   written, the rest has at most N bytes (the rest shrinks by at least two bytes a member) *)
Definition pi_body_pre (fx0 : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs)
  (mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z)) (CTX : list (list Z)) (regs0 : bvmap 5 word)
  (e q v : Z) (o : bool) (text len : Z) (tb : list Z) (p : Z) (d : nat) (Lam : list (Z * Z))
  (peak cnt fail ran most own : Z) (kr : nat) (lyc : alayout) (Sc : astate) (Hpc : list Z) (Wc : world segs)
  (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word) (N : nat)
  (CTX0 : list (list Z)) (CW : list (list Z)) : Prop :=
  pi_fpok fx0 fx /\
  pi_ent B fx0 ly S Hp W regs0 mem ch CTX Lam peak cnt fail ran most own e q text len p d kr tb v o CTX0 CW /\
  (* the overlay stays normal at THIS block's state: every callee text that reaches strtod asks for it at its call *)
  YAkMemnorm.memnorm segs memc /\
  pi_frame regs0 regs W mem Wc memc e q v /\
  pi_regs regs q v o /\ pi_regs_body regs Wc memc v /\ getr regs 21 = w64 (-1) /\
  exists (f n cap : nat) acc kids keys Di pc ok0 tr0 D0 Lamc peakc cntc failc ranc,
    pi_cur regs0 e q v text len tb d lyc Sc Hpc Wc memc pc Lamc peakc cntc failc ranc most own /\
    (length (rest_atR tb text pc) <= N)%nat /\ (n < cap)%nat /\
    pi_cont (rdW Wc memc) (prh_lin Lamc) o v kids keys n cap acc Di /\
    (* the members read so far are deep enough for every refusal exit's pj_fdR (MAXD - d) (PItemsValue 06:1xZ) *)
    Forall (fun m => (PjTree.depth (snd m) <= PjGrammar.MAXD - Nat.succ d)%nat) acc /\
    pj_apartR (pi_sblk o kids keys cap) v /\
    Permutation D0 (pi_sblk o kids keys cap ++ Di) /\
    (2 * length (rest_atR tb text pc) + 1 <= f)%nat /\
    pi_run_eqB d o (rest_atR tb text p) ok0 tr0 f n cap (rev acc) (rest_atR tb text pc) /\
    pi_led Lam peak cnt fail ran most ok0 tr0 D0 Lamc peakc cntc failc ranc /\
    (* the prefix's block move, as the record's post states it, and its byte bound: every exit reads its post's
       rd_blocks_move and blocks_bytes clauses off these (PItemsBody 06:1xZ G2; pi_blk is its projection) *)
    rd_blocks_move B ly S lyc Sc D0 tr0 (rest_atR tb text p) d /\
    (* THE TRAVELLING POSITION AND LIVE REQUESTS (form (b), f97c8b2f046b; PItems_posb.v): the run position from the
       entry state S to this block's state Sc over the prefix trace tr0, and the live requests moved by tr0 *)
    PItems_posb.pi_posb S Sc tr0 /\
    PItems_posb.pi_live (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
      (PresetRoom.rs_live (YGcfRoom.room_of_cf Sc)) tr0 /\
    blocks_bytes Sc <= blocks_bytes S + prh_held tr0 /\ length ok0 = PjGrammar.calls tr0 /\
    Ledger.lsum D0 = PjGrammar.held tr0 /\
    rd_room Sc (snd (fst (pi_jrb f (Nat.succ d) o n cap (rev acc) (rest_atR tb text pc) []))) /\
    (* THE BATCH KIT'S INVARIANTS (PItems_defs.v pi_grant / pi_ncaps / pi_forder / pi_fl_eq, _eqB, _eqV): the granted prefix, the
       capacities, and the free order with the kit's model jfl at this point of the loop *)
    pi_grant ok0 tr0 /\ cap = PresetReqAt.ncap (Nat.succ n) /\ pi_ncaps (rdW Wc memc) kids acc /\
    exists af, pi_forder (rdW Wc memc) (prh_lin Lamc) o kids keys n Di acc af /\
      pi_fl_eqB d o (rest_atR tb text p) ok0 f n cap af (rest_atR tb text pc).

(* AT 0x87bc0 (PI_O_KEY): the object arm of pi_body_pre *)
Definition pi_key_pre (fx0 : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs)
  (mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z)) (CTX : list (list Z)) (regs0 : bvmap 5 word)
  (e q v : Z) (o : bool) (text len : Z) (tb : list Z) (p : Z) (d : nat) (Lam : list (Z * Z))
  (peak cnt fail ran most own : Z) (kr : nat) (lyc : alayout) (Sc : astate) (Hpc : list Z) (Wc : world segs)
  (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word) (N : nat)
  (CTX0 : list (list Z)) (CW : list (list Z)) : Prop :=
  o = true /\
  pi_body_pre fx0 ly S Hp W mem md ch CTX regs0 e q v o text len tb p d Lam peak cnt fail ran most own kr
    lyc Sc Hpc Wc memc mdc k regs N CTX0 CW.

(* AT 0x87ec8 (PI_O_FREE), the missing colon. keys[n] holds kx, the block (kx, kk) parse_string allocated in THIS
   call: it is in the current ledger, not in the entry ledger Lam and no block of the entry state, so nothing of it is
   in FP = rd_fp q v (q's two cells are in the caller window, v's 56 bytes were the caller's before the call). The run
   is decided: jr_name frees that block and refuses (PjGrammar.v:246-247), so the whole run ends in the refusal with
   the free event. *)
Definition pi_free_pre (fx0 : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs)
  (mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z)) (CTX : list (list Z)) (regs0 : bvmap 5 word)
  (e q v : Z) (o : bool) (text len : Z) (tb : list Z) (p : Z) (d : nat) (Lam : list (Z * Z))
  (peak cnt fail ran most own : Z) (kr : nat) (lyc : alayout) (Sc : astate) (Hpc : list Z) (Wc : world segs)
  (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word)
  (CTX0 : list (list Z)) (CW : list (list Z)) : Prop :=
  o = true /\
  pi_fpok fx0 fx /\
  pi_ent B fx0 ly S Hp W regs0 mem ch CTX Lam peak cnt fail ran most own e q text len p d kr tb v o CTX0 CW /\
  (* the overlay stays normal at THIS block's state: every callee text that reaches strtod asks for it at its call *)
  YAkMemnorm.memnorm segs memc /\
  pi_frame regs0 regs W mem Wc memc e q v /\
  pi_regs regs q v o /\ pi_regs_body regs Wc memc v /\ getr regs 21 = w64 (-1) /\
  exists (n cap : nat) acc kids keys Di ok0 tr0 D0 Lamc peakc cntc failc ranc kx kk,
    pj_in_afterR segs (rdW Wc memc) q text len (Z.of_nat d + 1) (Z.of_nat d + 1) /\
    prhReader_at B lyc Sc Lamc regs0 e v 56 /\ range_addressable (aview segs (w_H Wc) memc) SHADOW_OFF v 56 /\
    prh_ledger B lyc Sc Hpc Wc memc Lamc peakc cntc failc ranc most own /\
    (n < cap)%nat /\
    pi_cont (rdW Wc memc) (prh_lin Lamc) o v kids keys n cap acc Di /\
    (* the members read so far are deep enough for every refusal exit's pj_fdR (MAXD - d) (PItemsValue 06:1xZ) *)
    Forall (fun m => (PjTree.depth (snd m) <= PjGrammar.MAXD - Nat.succ d)%nat) acc /\
    pj_apartR (pi_sblk o kids keys cap) v /\
    Permutation D0 (pi_sblk o kids keys cap ++ Di ++ [(kx, kk)]) /\
    val_mem segs (rdW Wc memc) (keys + 8 * Z.of_nat n) 8 kx /\ In (kx, kk) Lamc /\ ~ In (kx, kk) Lam /\
    ~ (exists b m, In (b, m) (ablocks B ly S) /\ b <= kx - cf_head < b + m) /\
    (forall ok1, jr_items prh_jr_strtod d o (rest_atR tb text p) (ok0 ++ ok1) =
       (None, tr0 ++ [EFree (Z.to_nat kk)], ok1)) /\
    pi_led Lam peak cnt fail ran most ok0 tr0 D0 Lamc peakc cntc failc ranc /\
    (* the prefix's block move, as the record's post states it, and its byte bound: every exit reads its post's
       rd_blocks_move and blocks_bytes clauses off these (PItemsBody 06:1xZ G2; pi_blk is its projection) *)
    rd_blocks_move B ly S lyc Sc D0 tr0 (rest_atR tb text p) d /\
    (* THE TRAVELLING POSITION AND LIVE REQUESTS (form (b), f97c8b2f046b; PItems_posb.v): the run position from the
       entry state S to this block's state Sc over the prefix trace tr0, and the live requests moved by tr0; the
       fuzz_free call composes its own post transfer (HFr) onto pi_posb by PItems_posb.pi_posb_call *)
    PItems_posb.pi_posb S Sc tr0 /\
    PItems_posb.pi_live (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
      (PresetRoom.rs_live (YGcfRoom.room_of_cf Sc)) tr0 /\
    blocks_bytes Sc <= blocks_bytes S + prh_held tr0 /\ length ok0 = PjGrammar.calls tr0 /\
    Ledger.lsum D0 = PjGrammar.held tr0 /\
    room_live_cf Sc /\
    (* the live class-24 count at the free path's entry, i.e. at the fuzz_free call 0x87f30 (no call in between):
       tfuzz_free_specX's premise, a CUT premise of this block and not a Section law over all states (an
       audit: as a law it is false, nothing bounds the count, PRH_FnAlloc.v:29-31). In form (b) the predecessor's
       hand-off (the key block, the missing-colon arm) owes it from pi_ent's class-24 pkR premise at its
       pi_live (PItems_posb.pi_lc_at; ccnt24 is PresetRoom.ccnt kBatchClass by conversion, PRH_FnReader.v's header).
       The entry-keyed form's run-event premise (an index of the model run whose event is this free) is GONE: the
       kit's tfuzz_free_specX states the position in its post, keyed on its own HFr event, with no entry position. *)
    YGcfRoomLive.ccnt24 Sc <= PresetLiveBounds.L24 + PresetLiveBounds.DRV /\
    (* THE BATCH KIT'S INVARIANTS (PItems_defs.v pi_grant / pi_ncaps / pi_forder / pi_fl_eq, _eqB, _eqV): the granted prefix, the
       capacities, and the free order with the kit's model jfl at this point of the loop *)
    pi_grant ok0 tr0 /\ cap = PresetReqAt.ncap (Nat.succ n) /\
    (* jr_name refused at the missing colon, so jfl's body is decided: the completed slots, then the arrays *)
    exists af, pi_forder (rdW Wc memc) (prh_lin Lamc) o kids keys n Di acc af /\
      (forall ok1, prhPi_frees d o (rest_atR tb text p) (ok0 ++ ok1) = af ++ PresetReqAt.arrz o cap).

(* ---- the value segment's pre v2 (value-pre-v2.v, 01:20Z) ---- *)
(* the rest of one member from the value on: jrl's body after jr_name (PjGrammar.v:309-316), verbatim *)
Definition pi_val_k (f D : nat) (o : bool) (n cap : nat) (accr : list (list Z * jv)) (nm y1 : list Z)
  : M (jv * list Z) :=
  jbind (jrv prh_jr_strtod f D y1) (fun '(t, r) =>
    match skip r with
    | c :: r1 =>
        if c =? 44 then jrl prh_jr_strtod f D o (S n) cap ((nm, t) :: accr) r1
        else if c =? closer o then jret (mk o (rev ((nm, t) :: accr)), r1)
        else jrefuse
    | [] => jrefuse
    end).

(* the whole call's run splits at the value into the prefix (ok0, tr0) and pi_val_k (jrl's acc = rev acc) *)
Definition pi_val_eq (d : nat) (o : bool) (x0 : list Z) (ok0 : list bool) (tr0 : list ev)
  (f n cap : nat) (acc : list (list Z * jv)) (nm y1 : list Z) : Prop :=
  forall ok1 r t ok2, pi_val_k f (Nat.succ d) o n cap (rev acc) nm y1 ok1 = (r, t, ok2) ->
    jr_items prh_jr_strtod d o x0 (ok0 ++ ok1) = (r, tr0 ++ t, ok2).

(* the key just read (object): keys + 8n holds the key's block, not yet in pi_cont's Di; array: none *)
Definition pi_key (m : word -> option byte) (lblk : Z -> Z -> Prop) (o : bool) (keys : Z) (n : nat)
  (nm : list Z) (Dk : list (Z * Z)) : Prop :=
  if o then exists x kx, Dk = [(x, kx)] /\ rd_u64 segs m (keys + 8 * Z.of_nat n) x /\ pj_cstrR segs m lblk x kx nm
  else nm = [] /\ Dk = [].



(* PI_O_VAL (0x87cd8): the kid slot's checks, the memset, parse_value. N bounds the rest (the walk's induction). *)
Definition pi_val_pre (fx0 : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs)
  (mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z)) (CTX : list (list Z)) (regs0 : bvmap 5 word)
  (e q v : Z) (o : bool) (text len : Z) (tb : list Z) (p : Z) (d : nat) (Lam : list (Z * Z))
  (peak cnt fail ran most own : Z) (kr : nat) (lyc : alayout) (Sc : astate) (Hpc : list Z) (Wc : world segs)
  (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word) (N : nat)
  (CTX0 : list (list Z)) (CW : list (list Z)) : Prop :=
  pi_fpok fx0 fx /\
  pi_ent B fx0 ly S Hp W regs0 mem ch CTX Lam peak cnt fail ran most own e q text len p d kr tb v o CTX0 CW /\
  (* the overlay stays normal at THIS block's state: every callee text that reaches strtod asks for it at its call *)
  YAkMemnorm.memnorm segs memc /\
  pi_frame regs0 regs W mem Wc memc e q v /\
  pi_regs regs q v o /\ pi_regs_body regs Wc memc v /\ getr regs 21 = w64 (-1) /\
  exists (f n cap : nat) acc kids keys Di nm Dk pc ok0 tr0 D0 Lamc peakc cntc failc ranc,
    pi_cur regs0 e q v text len tb d lyc Sc Hpc Wc memc pc Lamc peakc cntc failc ranc most own /\
    (length (rest_atR tb text pc) <= N)%nat /\ (n < cap)%nat /\
    pi_cont (rdW Wc memc) (prh_lin Lamc) o v kids keys n cap acc Di /\
    (* the members read so far are deep enough for every refusal exit's pj_fdR (MAXD - d) (PItemsValue 06:1xZ) *)
    Forall (fun m => (PjTree.depth (snd m) <= PjGrammar.MAXD - Nat.succ d)%nat) acc /\
    pj_apartR (pi_sblk o kids keys cap) v /\
    pi_key (rdW Wc memc) (prh_lin Lamc) o keys n nm Dk /\
    Permutation D0 (pi_sblk o kids keys cap ++ Di ++ Dk) /\
    (2 * length (rest_atR tb text pc) + 1 <= f)%nat /\
    pi_val_eq d o (rest_atR tb text p) ok0 tr0 f n cap acc nm (rest_atR tb text pc) /\
    pi_led Lam peak cnt fail ran most ok0 tr0 D0 Lamc peakc cntc failc ranc /\
    (* the prefix's block move, as the record's post states it, and its byte bound: every exit reads its post's
       rd_blocks_move and blocks_bytes clauses off these (PItemsBody 06:1xZ G2; pi_blk is its projection) *)
    rd_blocks_move B ly S lyc Sc D0 tr0 (rest_atR tb text p) d /\
    (* THE TRAVELLING POSITION AND LIVE REQUESTS (form (b), f97c8b2f046b; PItems_posb.v): the run position from the
       entry state S to this block's state Sc over the prefix trace tr0, and the live requests moved by tr0 *)
    PItems_posb.pi_posb S Sc tr0 /\
    PItems_posb.pi_live (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
      (PresetRoom.rs_live (YGcfRoom.room_of_cf Sc)) tr0 /\
    blocks_bytes Sc <= blocks_bytes S + prh_held tr0 /\ length ok0 = PjGrammar.calls tr0 /\
    Ledger.lsum D0 = PjGrammar.held tr0 /\
    rd_room Sc (snd (fst (pi_val_k f (Nat.succ d) o n cap (rev acc) nm (rest_atR tb text pc) []))) /\
    (* THE BATCH KIT'S INVARIANTS (PItems_defs.v pi_grant / pi_ncaps / pi_forder / pi_fl_eq, _eqB, _eqV): the granted prefix, the
       capacities, and the free order with the kit's model jfl at this point of the loop *)
    pi_grant ok0 tr0 /\ cap = PresetReqAt.ncap (Nat.succ n) /\ pi_ncaps (rdW Wc memc) kids acc /\
    exists af lk, pi_forder (rdW Wc memc) (prh_lin Lamc) o kids keys n Di acc af /\
      (cf_head = PresetReqAt.HEAD -> map (fun b => snd b + cf_head) Dk = lk) /\
      pi_fl_eqV d o (rest_atR tb text p) ok0 f n cap af lk (rest_atR tb text pc).


(* ---- PItems_head.v: back from the first skip_ws, PI_O_HEAD (0x87b24) ---- *)
Definition pi_head_pre (fx0 : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs)
  (mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z)) (CTX : list (list Z)) (regs0 : bvmap 5 word)
  (e q v : Z) (o : bool) (text len : Z) (tb : list Z) (p : Z) (d : nat) (Lam : list (Z * Z))
  (peak cnt fail ran most own : Z) (kr : nat) (lyc : alayout) (Sc : astate) (Hpc : list Z) (Wc : world segs)
  (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word)
  (CTX0 : list (list Z)) (CW : list (list Z)) : Prop :=
  pi_fpok fx0 fx /\
  pi_ent B fx0 ly S Hp W regs0 mem ch CTX Lam peak cnt fail ran most own e q text len p d kr tb v o CTX0 CW /\
  (* the overlay stays normal at THIS block's state: every callee text that reaches strtod asks for it at its call *)
  YAkMemnorm.memnorm segs memc /\
  (* THE TRAVELLING POSITION AND LIVE REQUESTS (form (b); PItems_posb.v) over the EMPTY prefix trace:
     the prologue and skip_ws make no allocator event (tskip_ws_specX's post keeps S), so this block has no trace
     binder; the head hands tr0 = [] on to the loop and closer pres *)
  PItems_posb.pi_posb S Sc [] /\
  PItems_posb.pi_live (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
    (PresetRoom.rs_live (YGcfRoom.room_of_cf Sc)) [] /\
  pi_frame regs0 regs W mem Wc memc e q v /\
  getr regs 9 = w64 q /\ getr regs 19 = w64 v /\ getr regs 18 = w64 (if o then 1 else 0) /\ getr regs 8 = w64 (q + 16) /\
  getr regs 26 = w64 SHADOW_OFF /\ getr regs 27 = w64 (pi_sh q) /\ getr regs 25 = w64 (pi_sh (q + 16)) /\
  getr regs 21 = w64 (-1) /\ (Nat.succ d <= PjGrammar.MAXD)%nat /\
  (* the prologue and skip_ws allocate nothing (tskip_ws_specX's post keeps ablocks), so the head's empty arm can
     give the post's rd_blocks_move with D = [] (05:5xZ) *)
  ablocks B lyc Sc = ablocks B ly S /\
  exists p1, rest_atR tb text p1 = PjGrammar.skip (tl (rest_atR tb text p)) /\
    pi_cur regs0 e q v text len tb d lyc Sc Hpc Wc memc p1 Lam peak cnt fail ran most own /\
    pi_cont (rdW Wc memc) (prh_lin Lam) o v 0 0 0 0 [] [] /\
    rd_room Sc (prhPi_gtrace d o (rest_atR tb text p)).

(* ---- PItems_head.v: the closer, PI_O_CLOSE (0x87e4c) and its second copy PI_O_CLOSE2 (0x87f58) ---- *)
Definition pi_close_pre (fx0 : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs)
  (mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z)) (CTX : list (list Z)) (regs0 : bvmap 5 word)
  (e q v : Z) (o : bool) (text len : Z) (tb : list Z) (p : Z) (d : nat) (Lam : list (Z * Z))
  (peak cnt fail ran most own : Z) (kr : nat) (lyc : alayout) (Sc : astate) (Hpc : list Z) (Wc : world segs)
  (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word)
  (CTX0 : list (list Z)) (CW : list (list Z)) : Prop :=
  pi_fpok fx0 fx /\
  pi_ent B fx0 ly S Hp W regs0 mem ch CTX Lam peak cnt fail ran most own e q text len p d kr tb v o CTX0 CW /\
  (* the overlay stays normal at THIS block's state: every callee text that reaches strtod asks for it at its call *)
  YAkMemnorm.memnorm segs memc /\
  pi_frame regs0 regs W mem Wc memc e q v /\ pi_regs regs q v o /\
  exists pc ok tr okr D Lam' peak' cnt' fail' ran' t r,
    getr regs 10 = w64 pc /\
    PjGrammar.jr_items prh_jr_strtod d o (rest_atR tb text p) ok = (Some (t, r), tr, okr) /\
    rest_atR tb text pc = PjGrammar.closer o :: r /\
    prh_ledger B lyc Sc Hpc Wc memc Lam' peak' cnt' fail' ran' most own /\ room_live_cf Sc /\
    rd_ledger_move Lam peak cnt fail ran most ok (prhPi_gtrace d o (rest_atR tb text p)) tr D Lam' peak' cnt' fail' ran' /\
    (* the subtree's blocks move, built by whoever read the members (the value segment on the member arm, the head's own
       empty arm); the closer makes no call and passes it to the post (05:5xZ) *)
    rd_blocks_move B ly S lyc Sc D tr (rest_atR tb text p) d /\
    (* THE TRAVELLING POSITION AND LIVE REQUESTS (form (b); PItems_posb.v) over the WHOLE trace tr:
       the closer makes no call, so the post's position transfer and live requests are these (pi_posb_post) *)
    PItems_posb.pi_posb S Sc tr /\
    PItems_posb.pi_live (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
      (PresetRoom.rs_live (YGcfRoom.room_of_cf Sc)) tr /\
    blocks_bytes Sc <= blocks_bytes S + prh_held tr /\
    Ledger.lsum D = PjGrammar.held tr /\
    pj_in_okR segs (rdW Wc memc) q text len pc (Z.of_nat d + 1) tb /\
    pj_nodeR segs (rdW Wc memc) (prh_lin Lam') v t D /\
    (* the node at the CURRENT state, so its 56 bytes are bounded and apart from the cursor's cells when the
       closer's two stores land (02:0xZ); both callers carry it already, as pi_cur's fifth conjunct *)
    prhReader_at B lyc Sc Lam' regs0 e v 56 /\
    Ledger.lsum D <= 224 * (Z.of_nat (length (rest_atR tb text p)) - Z.of_nat (length r)) /\
    range_addressable (aview segs (w_H Wc) memc) SHADOW_OFF q 24 /\
    (* THE BATCH KIT SOME-ARM CONJUNCTS, carried to the post by the closer (it stores only the cursor's cells): the tree's
       free order against the kit's model at this call's (d, o, rest, ok), and its capacities *)
    (cf_head = PresetReqAt.HEAD -> forall nn, (PjTree.depth t <= nn)%nat ->
       exists F, PRH_PjOrder.pj_foR segs (rdW Wc memc) (prh_lin Lam') nn v D F /\
         map (fun b => snd b + cf_head) F = prhPi_frees d o (rest_atR tb text p) ok) /\
    pj_ncapR segs (rdW Wc memc) v t.


(* ---- PItemsEntry: a post is STABLE when it reads memory only through rdW and ignores the model (the kit's post does) ---- *)
Definition pi_Qstable (Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop) : Prop :=
  forall ly S Hp W regs m m' md md',
    (forall x, mrestrict (w_H W) m' x = mrestrict (w_H W) m x) ->
    Q ly S Hp W regs m md -> Q ly S Hp W regs m' md'.

(* ---- PItems_entry.v: the EPILOGUE's pre, PI_O_EPI (0x87e88 .. 0x87ec4) ---- *)
Definition pi_epi_pre (fx0 : YK11.FPState) (regs0 : bvmap 5 word) (W : world segs) (mem : word -> option byte) (e q v : Z)
  (Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  (lyc : alayout) (Sc : astate) (Hpc : list Z) (Wc : world segs) (regs : bvmap 5 word) (memc : word -> option byte)
  (mdc : Model) (res : Z) : Prop :=
  pi_fpok fx0 fx /\ YAkMemnorm.memnorm segs memc /\
  pi_frame regs0 regs W mem Wc memc e q v /\
  getr regs 21 = w64 res /\
  pi_Qstable Q /\
  (forall regs', getr regs' 10 = w64 res -> Q lyc Sc Hpc Wc regs' memc mdc).

Context {PL : PAListing L}.

(* the goal every segment concludes over a world relation R: SRrG at R from the block at offset off (current fx) to
   the text's post at the entry, its journal at R. The segment specs take it at wle' segs RZ_cf (YA0nH.SRr' and fpostWFbm) *)
Definition pi_goalR (R : world segs -> world segs -> Prop) (fx0 : YK11.FPState) (ly : alayout) (S : astate)
  (Hp : list Z) (W : world segs)
  (mem : word -> option byte) (md : Model) (regs0 : bvmap 5 word) (e q v : Z) (o : bool) (text len : Z)
  (tb : list Z) (p : Z) (d : nat) (Lam : list (Z * Z)) (peak cnt fail ran most own : Z) (kr : nat)
  (off : Z) (Wc : world segs) (memc : word -> option byte) (mdc : Model) (regs : bvmap 5 word)
  (CW : list (list Z)) : Prop :=
  SRrG segs R Wc (cfg_at (fx := fx) segs (pa_val A_TEXT + PI_AT off) regs memc mdc)
    (fpostWFbmR (fx := fx0) B ARx SK R (YCbqGwild.wbudget CW 0) (STK_parse_items d) e (rd_fp q v) regs0 ly S Hp W
       mem md (pi_post ly S d o tb text len p q v Lam peak cnt fail ran most own kr)).
(* the goal at wle (the form before the re-hiding move) *)
Definition pi_goal := pi_goalR (@wle segs).
Lemma pi_goal_R_wle : forall fx0 ly S Hp W mem md regs0 e q v o text len tb p d Lam peak cnt fail ran most own kr
  off Wc memc mdc regs CW,
  pi_goal fx0 ly S Hp W mem md regs0 e q v o text len tb p d Lam peak cnt fail ran most own kr off Wc memc mdc regs CW =
  pi_goalR (@wle segs) fx0 ly S Hp W mem md regs0 e q v o text len tb p d Lam peak cnt fail ran most own kr off Wc memc
    mdc regs CW.
Proof. reflexivity. Qed.

(* the journal every segment starts from, over a world relation R: wle before the first free, wle' segs RZ_cf after
   one (the segment specs take it at wle') *)
Definition pi_ajR (R : world segs -> world segs -> Prop) (ly : alayout) (S : astate) (Hp : list Z)
  (W : world segs) (mem : word -> option byte) (md : Model)
  (regs0 : bvmap 5 word) (d : nat) (e q v : Z)
  (lyc : alayout) (Sc : astate) (Hpc : list Z) (Wc : world segs) (memc : word -> option byte) (mdc : Model) (k : Z)
  (WS : list (list Z)) : Prop :=
  (* the journal at the BUDGET WS (the batch kit 240b06ed4fd4): the wild traces the run's allocator calls stored so far; every
     so far; every segment pre carries `YCbqGwild.wbudget CW 0 WS` (they are all CW's), and the post is at wbudget CW 0 *)
  ajournal_xwR (SK := SK) segs B prh_pst ARx R (STK_parse_items d + e) (spZ regs0 + e) (rd_fp q v)
    ly S Hp W mem md [] lyc Sc Hpc Wc memc mdc k WS.
(* the journal at wle *)
Definition pi_aj := pi_ajR (@wle segs).
Lemma pi_aj_R_wle : forall ly S Hp W mem md regs0 d e q v lyc Sc Hpc Wc memc mdc k WS,
  pi_aj ly S Hp W mem md regs0 d e q v lyc Sc Hpc Wc memc mdc k WS =
  pi_ajR (@wle segs) ly S Hp W mem md regs0 d e q v lyc Sc Hpc Wc memc mdc k WS.
Proof. reflexivity. Qed.

End pres.

(* ---- the SEGMENT SPECS: each block's lemma statement as a Definition quantifying the CURRENT float state fxc,
   so a neighbour can take it as a Section hypothesis and apply it at whatever float state the run reached
   (01:20Z). The nesting d is a PARAMETER, not a binder (01:3xZ): parse_items at d needs
   parse_value's text at S d only, so every spec a caller takes is fixed at the caller's d. The segment lemmas
   prove these; the induction cut is pi_body_spec d N. ---- *)
Definition pi_head_spec {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PIi : PrhImg} {RL : PrhRoomLive}
  {L : ptable asym} {PA : PAImg L} {PL : PAListing L} (B : asyms)
  (ARx : alayout -> astate -> list Z -> world pa_segs -> (word -> option byte) -> Model -> Prop)
  (SK : YI16.sink_head) (d : nat) (CTX0 : list (list Z)) (CW : list (list Z)) : Prop :=
  forall (fxc fx0 : YK11.FPState) ly S Hp W mem md ch CTX regs0 e q v o text len tb p Lam peak cnt fail ran most own kr
    lyc Sc Hpc Wc memc mdc k regs WS0,
  pi_ajR B ARx SK (wle' pa_segs YGcfRehidePost.RZ_cf) ly S Hp W mem md regs0 d e q v lyc Sc Hpc Wc memc mdc k WS0 ->
  YCbqGwild.wbudget CW 0 WS0 ->
  pi_head_pre (fx := fxc) B fx0 ly S Hp W mem md ch CTX regs0 e q v o text len tb p d Lam peak cnt fail ran most own kr lyc Sc Hpc Wc memc mdc k regs CTX0 CW ->
  pi_goalR (fx := fxc) B ARx SK (wle' pa_segs YGcfRehidePost.RZ_cf) fx0 ly S Hp W mem md regs0 e q v o text len tb p d
    Lam peak cnt fail ran most own kr PI_O_HEAD Wc memc mdc regs CW.
Definition pi_loop_spec {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PIi : PrhImg} {RL : PrhRoomLive}
  {L : ptable asym} {PA : PAImg L} {PL : PAListing L} (B : asyms)
  (ARx : alayout -> astate -> list Z -> world pa_segs -> (word -> option byte) -> Model -> Prop)
  (SK : YI16.sink_head) (d : nat) (CTX0 : list (list Z)) (CW : list (list Z)) : Prop :=
  forall (fxc fx0 : YK11.FPState) ly S Hp W mem md ch CTX regs0 e q v o text len tb p Lam peak cnt fail ran most own kr
    lyc Sc Hpc Wc memc mdc k regs WS0,
  pi_ajR B ARx SK (wle' pa_segs YGcfRehidePost.RZ_cf) ly S Hp W mem md regs0 d e q v lyc Sc Hpc Wc memc mdc k WS0 ->
  YCbqGwild.wbudget CW 0 WS0 ->
  pi_loop_pre (fx := fxc) B fx0 ly S Hp W mem md ch CTX regs0 e q v o text len tb p d Lam peak cnt fail ran most own kr lyc Sc Hpc Wc memc mdc k regs CTX0 CW ->
  pi_goalR (fx := fxc) B ARx SK (wle' pa_segs YGcfRehidePost.RZ_cf) fx0 ly S Hp W mem md regs0 e q v o text len tb p d
    Lam peak cnt fail ran most own kr PI_O_LOOP Wc memc mdc regs CW.
Definition pi_body_spec {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PIi : PrhImg} {RL : PrhRoomLive}
  {L : ptable asym} {PA : PAImg L} {PL : PAListing L} (B : asyms)
  (ARx : alayout -> astate -> list Z -> world pa_segs -> (word -> option byte) -> Model -> Prop)
  (SK : YI16.sink_head) (d : nat) (CTX0 : list (list Z)) (CW : list (list Z)) (N : nat) : Prop :=
  forall (fxc fx0 : YK11.FPState) ly S Hp W mem md ch CTX regs0 e q v o text len tb p Lam peak cnt fail ran most own kr
    lyc Sc Hpc Wc memc mdc k regs WS0,
  pi_ajR B ARx SK (wle' pa_segs YGcfRehidePost.RZ_cf) ly S Hp W mem md regs0 d e q v lyc Sc Hpc Wc memc mdc k WS0 ->
  YCbqGwild.wbudget CW 0 WS0 ->
  pi_body_pre (fx := fxc) B fx0 ly S Hp W mem md ch CTX regs0 e q v o text len tb p d Lam peak cnt fail ran most own kr lyc Sc Hpc Wc memc mdc k regs N CTX0 CW ->
  pi_goalR (fx := fxc) B ARx SK (wle' pa_segs YGcfRehidePost.RZ_cf) fx0 ly S Hp W mem md regs0 e q v o text len tb p d
    Lam peak cnt fail ran most own kr PI_O_BODY Wc memc mdc regs CW.
Definition pi_key_spec {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PIi : PrhImg} {RL : PrhRoomLive}
  {L : ptable asym} {PA : PAImg L} {PL : PAListing L} (B : asyms)
  (ARx : alayout -> astate -> list Z -> world pa_segs -> (word -> option byte) -> Model -> Prop)
  (SK : YI16.sink_head) (d : nat) (CTX0 : list (list Z)) (CW : list (list Z)) (N : nat) : Prop :=
  forall (fxc fx0 : YK11.FPState) ly S Hp W mem md ch CTX regs0 e q v o text len tb p Lam peak cnt fail ran most own kr
    lyc Sc Hpc Wc memc mdc k regs WS0,
  pi_ajR B ARx SK (wle' pa_segs YGcfRehidePost.RZ_cf) ly S Hp W mem md regs0 d e q v lyc Sc Hpc Wc memc mdc k WS0 ->
  YCbqGwild.wbudget CW 0 WS0 ->
  pi_key_pre (fx := fxc) B fx0 ly S Hp W mem md ch CTX regs0 e q v o text len tb p d Lam peak cnt fail ran most own kr lyc Sc Hpc Wc memc mdc k regs N CTX0 CW ->
  pi_goalR (fx := fxc) B ARx SK (wle' pa_segs YGcfRehidePost.RZ_cf) fx0 ly S Hp W mem md regs0 e q v o text len tb p d
    Lam peak cnt fail ran most own kr PI_O_KEY Wc memc mdc regs CW.
Definition pi_free_spec {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PIi : PrhImg} {RL : PrhRoomLive}
  {L : ptable asym} {PA : PAImg L} {PL : PAListing L} (B : asyms)
  (ARx : alayout -> astate -> list Z -> world pa_segs -> (word -> option byte) -> Model -> Prop)
  (SK : YI16.sink_head) (d : nat) (CTX0 : list (list Z)) (CW : list (list Z)) : Prop :=
  forall (fxc fx0 : YK11.FPState) ly S Hp W mem md ch CTX regs0 e q v o text len tb p Lam peak cnt fail ran most own kr
    lyc Sc Hpc Wc memc mdc k regs WS0,
  pi_ajR B ARx SK (wle' pa_segs YGcfRehidePost.RZ_cf) ly S Hp W mem md regs0 d e q v lyc Sc Hpc Wc memc mdc k WS0 ->
  YCbqGwild.wbudget CW 0 WS0 ->
  pi_free_pre (fx := fxc) B fx0 ly S Hp W mem md ch CTX regs0 e q v o text len tb p d Lam peak cnt fail ran most own kr lyc Sc Hpc Wc memc mdc k regs CTX0 CW ->
  pi_goalR (fx := fxc) B ARx SK (wle' pa_segs YGcfRehidePost.RZ_cf) fx0 ly S Hp W mem md regs0 e q v o text len tb p d
    Lam peak cnt fail ran most own kr PI_O_FREE Wc memc mdc regs CW.
Definition pi_val_spec {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PIi : PrhImg} {RL : PrhRoomLive}
  {L : ptable asym} {PA : PAImg L} {PL : PAListing L} (B : asyms)
  (ARx : alayout -> astate -> list Z -> world pa_segs -> (word -> option byte) -> Model -> Prop)
  (SK : YI16.sink_head) (d : nat) (CTX0 : list (list Z)) (CW : list (list Z)) (N : nat) : Prop :=
  forall (fxc fx0 : YK11.FPState) ly S Hp W mem md ch CTX regs0 e q v o text len tb p Lam peak cnt fail ran most own kr
    lyc Sc Hpc Wc memc mdc k regs WS0,
  pi_ajR B ARx SK (wle' pa_segs YGcfRehidePost.RZ_cf) ly S Hp W mem md regs0 d e q v lyc Sc Hpc Wc memc mdc k WS0 ->
  YCbqGwild.wbudget CW 0 WS0 ->
  pi_val_pre (fx := fxc) B fx0 ly S Hp W mem md ch CTX regs0 e q v o text len tb p d Lam peak cnt fail ran most own kr lyc Sc Hpc Wc memc mdc k regs N CTX0 CW ->
  pi_goalR (fx := fxc) B ARx SK (wle' pa_segs YGcfRehidePost.RZ_cf) fx0 ly S Hp W mem md regs0 e q v o text len tb p d
    Lam peak cnt fail ran most own kr PI_O_VAL Wc memc mdc regs CW.
Definition pi_close_spec {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PIi : PrhImg} {RL : PrhRoomLive}
  {L : ptable asym} {PA : PAImg L} {PL : PAListing L} (B : asyms)
  (ARx : alayout -> astate -> list Z -> world pa_segs -> (word -> option byte) -> Model -> Prop)
  (SK : YI16.sink_head) (d : nat) (CTX0 : list (list Z)) (CW : list (list Z)) : Prop :=
  forall (fxc fx0 : YK11.FPState) ly S Hp W mem md ch CTX regs0 e q v o text len tb p Lam peak cnt fail ran most own kr
    lyc Sc Hpc Wc memc mdc k regs WS0,
  pi_ajR B ARx SK (wle' pa_segs YGcfRehidePost.RZ_cf) ly S Hp W mem md regs0 d e q v lyc Sc Hpc Wc memc mdc k WS0 ->
  YCbqGwild.wbudget CW 0 WS0 ->
  pi_close_pre (fx := fxc) B fx0 ly S Hp W mem md ch CTX regs0 e q v o text len tb p d Lam peak cnt fail ran most own kr lyc Sc Hpc Wc memc mdc k regs CTX0 CW ->
  pi_goalR (fx := fxc) B ARx SK (wle' pa_segs YGcfRehidePost.RZ_cf) fx0 ly S Hp W mem md regs0 e q v o text len tb p d
    Lam peak cnt fail ran most own kr PI_O_CLOSE Wc memc mdc regs CW.
Definition pi_close2_spec {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PIi : PrhImg} {RL : PrhRoomLive}
  {L : ptable asym} {PA : PAImg L} {PL : PAListing L} (B : asyms)
  (ARx : alayout -> astate -> list Z -> world pa_segs -> (word -> option byte) -> Model -> Prop)
  (SK : YI16.sink_head) (d : nat) (CTX0 : list (list Z)) (CW : list (list Z)) : Prop :=
  forall (fxc fx0 : YK11.FPState) ly S Hp W mem md ch CTX regs0 e q v o text len tb p Lam peak cnt fail ran most own kr
    lyc Sc Hpc Wc memc mdc k regs WS0,
  pi_ajR B ARx SK (wle' pa_segs YGcfRehidePost.RZ_cf) ly S Hp W mem md regs0 d e q v lyc Sc Hpc Wc memc mdc k WS0 ->
  YCbqGwild.wbudget CW 0 WS0 ->
  pi_close_pre (fx := fxc) B fx0 ly S Hp W mem md ch CTX regs0 e q v o text len tb p d Lam peak cnt fail ran most own kr lyc Sc Hpc Wc memc mdc k regs CTX0 CW ->
  pi_goalR (fx := fxc) B ARx SK (wle' pa_segs YGcfRehidePost.RZ_cf) fx0 ly S Hp W mem md regs0 e q v o text len tb p d
    Lam peak cnt fail ran most own kr PI_O_CLOSE2 Wc memc mdc regs CW.
Definition pi_epi_spec {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PIi : PrhImg} {RL : PrhRoomLive}
  {L : ptable asym} {PA : PAImg L} {PL : PAListing L} (B : asyms)
  (ARx : alayout -> astate -> list Z -> world pa_segs -> (word -> option byte) -> Model -> Prop)
  (SK : YI16.sink_head) (d : nat) : Prop :=
  forall (P : list (list Z) -> Prop) (fxc fx0 : YK11.FPState) ly S Hp W mem md (regs0 : bvmap 5 word) e q v
    (Q : alayout -> astate -> list Z -> world pa_segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
    lyc Sc Hpc Wc memc mdc k (regs : bvmap 5 word) res WS0,
  pi_ajR B ARx SK (wle' pa_segs YGcfRehidePost.RZ_cf) ly S Hp W mem md regs0 d e q v lyc Sc Hpc Wc memc mdc k WS0 ->
  P WS0 ->
  pi_epi_pre (fx := fxc) fx0 regs0 W mem e q v Q lyc Sc Hpc Wc regs memc mdc res ->
  SRr' pa_segs YGcfRehidePost.RZ_cf Wc (cfg_at (fx := fxc) pa_segs (pa_val A_TEXT + PI_AT PI_O_EPI) regs memc mdc)
    (fpostWFbm (fx := fx0) B ARx SK P (STK_parse_items d) e (rd_fp q v) regs0 ly S Hp W mem md Q).
