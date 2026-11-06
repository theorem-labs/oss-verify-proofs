(* fuzz_preset, slice S5b, lanes IelemA / IelemB: the BOUNDARY STATES of parse_items' element loop in image A
   (A 0x87298, listing slot 5934) and the four step lemmas of the loop over them, against the RECORD texts of
   lib/A/PRH_FnParse.v (tparse_value_specX / tparse_items_specX).
   rule 24: no function is proved here. Each step lemma takes its callee's contract and its neighbouring boundary
   state as a named Section hypothesis; the loop head is the state lane IproB's prologue reaches. IelemB owns the
   definition of vrd_ielem_a (a Theorem Labs lane's ruling, 2026-10-29 00:36Z).

   THE LOOP, by rows of the #102 pin A' image's disassembly of parse_items (row r = listing slot r + 5932):
     row 108  A 0x87440  the LOOP HEAD, vrd_ielem_a: `beqz s3, +0x198` - an array jumps over the key path
     rows 109..209        the object's key path, vrd_ikey_a: white space, the quote test (byte 34), parse_string
                          (row 148, A 0x874e0), the key slot store at keys[n] (row 166), white space, the `:`
                          test (row 205) and the cursor past it (row 209) -> vrd_islot_a
     rows 210..237        the element step, vrd_ival_a: the slot address kids + 56 n (rows 215..221),
                          `jal __asan_memset` (row 223, A 0x8760c) zeroing the 56-byte slot, `jal parse_value`
                          (row 231, A 0x8762c) at nesting d + 1, `v->n := n + 1` (rows 234..236), the branch on
                          the result (row 237)
     rows 238..279        white space, the `,` test (rows 273..275) and the cursor past the comma (row 279)
     rows 280..283        the capacity step, vrd_igrow_a: `jal grow` (row 281, A 0x876f4) and the branch back to
                          the loop head (row 282) -> vrd_ielem_a with one more element, or an exit
     rows 305..309, 326..346  the loop's exits: the closer test (rows 326..335: `]` = 93 / `}` = 125, s2 := -1 first
                          at row 329) which on a match moves the cursor, lowers the cursor's depth (rows 343..345),
                          sets s2 := 0 (row 342); the refusal of the key's colon, which frees the key just stored
                          (`jal fuzz_free`, row 308, A 0x87760); and the common refusal join `li s2, -1` (row 309).
                          EVERY exit reaches row 310 (A 0x87768, slot 6242) with s2 = the result: that is the exit
                          boundary vrd_iexit_a. (Rows 293..304, with `mv s2, zero` at row 302, are the PROLOGUE's
                          empty-container exit, reached only from row 63; no step of the loop goes there.)
     rows 310..325        the epilogue: a0 := s2, the twelve callee-saved registers, `addi sp, sp, 0x90`, `ret`

   THE NESTING DEPTH IS IN NO REGISTER. parse_value's arguments are a0 = the cursor q and a1 = the node slot
   (rows 229..230: `add a1, a1, a0`, then `mv a0, s0` with s0 = q). The depth travels in MEMORY, in the cursor's
   third field, the 4-byte word at q + 16: parse_items raised it from d to d + 1 in its prologue (A 0x87324
   `sw a2, 0(s1)` with s1 = q + 16, rows 34..37, after refusing at 31) and lowers it again on the success exit
   (A 0x877f4, rows 343..345). So the callee contract this lane takes is PRH_FnParse.tparse_value_specX (S d) CTX,
   and every boundary state carries pj_in_okR at depth Z.of_nat d + 1.

   THE REGISTER MAP AT THE LOOP HEAD (A 0x87440), read off rows 16..107 (IproA's vrd_irun_tail measures it):
     s0 = q, s1 = q + 16, s2 = shadow_addr (v + 40), s3 = (o ? 1 : 0), s4 = v, s5 = 32, s6 = v + 40 (&v->n),
     s7 = shadow_addr (q + 8), s8 = v + 24 (&v->kids), s9 = 4294977024 = 0x100002600 = 0x800013 << 9 (the
     white-space bitmask rows 100, 103, 107 build: bits 9, 10, 13, 32), s10 = SHADOW_OFF, s11 = shadow_addr q,
     sp = sp0 - 144, and on the frame sp + 8 = q + 8, sp + 16 = shadow_addr (q + 16), sp + 24 = shadow_addr (v + 24),
     sp + 32 = v + 32 (&v->keys), sp + 136 = the entry ra, sp + 40 .. sp + 128 = the twelve saved registers.
     s2 holds the shadow address of v->n INSIDE the loop; the 0 / -1 return value is put in s2 only on the exits.

   THE MODEL (a Theorem Labs lane's ruling of record, 00:36Z, IproB's shape): every boundary carries the continuation ip_cont
   of PjGrammar.jr_items' run from that position, the GRANTED PREFIX ip_ok (one `true` per allocator call of the
   trace ip_tr: every refusal leaves the loop) and the TAIL quantified, so a later refusal stays reachable; the fuel
   ip_f is bounded below by the rest of the text, so that jrv ip_f meets parse_value's own jr_value (S d); the room
   is over the GRANTED continuation trace snd (fst (ip_cont P [])).

   THE POST-IMPLICATION RESTATEMENT (lane A'Ipro, a Theorem Labs lane's approval 2026-10-29, against the kit text
   a working branch 3ac20a5c9e30: PRH_FnParse.v 94232293d483, PRH_FnReader.v fb7b12dfa169, PRH_Base.v
   ee2f5cd7ed35, PRH_FnAlloc.v 95e26ff95e63). The call data gains the text's most / own (ie_most, ie_own) and loses
   the six room-position fields of the entry-keyed form: the text has no entry position, its post quantifies the
   model run and position itself. vrd_ient_ok mirrors the text's premises (the memnorm and live-count premises in
   the slot the entry position held). Every position carries the ledger at most / own, the text's rd_ledger_move
   at most and the WHOLE call's granted trace, the text's POSITION TRANSFER and its LIVE REQUESTS from the call's
   entry state over the events made so far (rd_hevs (ip_tr P)); the exit also carries the text's OUTCOME clause.
   The epilogue's conclusion is the text's post body, vrd_items_q, verbatim.

   THE REBIND ON THE KIT'S CUT (lane RBase, a working branch 7cdbb61b5fa0: PRH_FnParse.v f0d92dcec7e9,
   PRH_Base.v ef7c8ca98529, PRH_FnReader.v f1ae32e3b2cd, PRH_FnAlloc.v 4d8aeba047e5, PRH_Reader.v 4266e709561a). Each
   statement moved ONLY where a cut text forces it:
   - DW is GONE (tparse_items_specX's fourth parameter is the cursor set CW : list (list Z)): the Props take CW;
     vrd_ient_ok states prh_univ_closure B CTX0 (DW-SPLIT arity, PRH_Base.v:1203), prh_cur_entry without DW
     (:1111), and, in ONE trailing slot, the text's two new premises prh_cw_entry B CW (:1488) and
     wild_room (as_universe B) CW 0 (st_depot S) (PRH_FnParse.v:425), with ie_CW E = CW.
   - THE POST IS BUDGETED (fpostWFbm .. (YCbqGwild.wbudget CW 0)): every callee of the loop that can store a cursor
     trace posts at a budget, so a position's journal is at a budget. vrd_ient gains the field ie_CW (the call's cursor
     set) and vrd_ijrn's journal is at the budget ie_CW E itself, which is `exists WS, journal at WS /\ wbudget CW 0 WS`
     (wfresh CW WS = 0 iff incl WS CW: YCbqGwild.wfresh_incl / wfresh_zero_incl, YCbqG.ajournal_xw_incl); the
     epilogue's conclusion is fpostWFb at wbudget CW 0 (the m-keep stays the top's, as before).
   - THE POST GAINED THE FREE ORDER (both arms) AND pj_ncapR (Some arm) (FREEORD-NONE, CAP): vrd_items_q carries
     them verbatim, vrd_iexit_a's answer appends them, and each loop boundary appends the invariants that make them
     provable (the batch kit's layer, after a Theorem Labs lane's B' twin a working branch 34d46afa0965
     lib/B/Prog/PItems_defs.v pi_ncaps / pi_forder / pi_fl_eq / pi_fl_eqB / pi_fl_eqV): the container's cap is
     PresetReqAt.ncap of its count (vrd_ielem_a / vrd_islot_a: ncap (S n), after the grow; vrd_icomma_a: ncap n), the
     members' caps (vrd_incaps), the completed slots' order list against an accumulator af (vrd_iforder), and the
     model's free list prhPi_frees factored through PresetReqAt.jfl at the boundary (vrd_jfb after the grow,
     vrd_jfvk after the key, jfl itself before the grow). vrd_inode is unchanged, so its frame lemmas stand.
   vrd_imodel is unchanged in text (rd_room's live conjunct moved inside PRH_FnParse.rd_room, same name).

   THE RE-HIDING MOVE (a free, or a realloc of a live block, re-hides shadow, so the texts of parse_value,
   parse_items, parse_string and grow conclude YA0nH.SRr' SEGS RZ_cf with their journals at wle' SEGS RZ_cf): every
   step Prop concludes SRr' SEGS RZ_cf, and vrd_ijrn's journal from the call's entry is at wle'. THE HULL BUDGET (the
   texts' threaded allocator hull premise, lib/Spec/PresetHullBudget.v): vrd_ient_ok carries the text's hull_budget
   over the call's all-granted events, every loop position the hull use over its events so far (vrd_imodel), the exit
   the use over the all-granted events, and vrd_items_q the text's hull_used conjunct in the text's place.

   This file carries the boundary definitions and the four step lemmas as the Props tvrd_ikey_a / tvrd_ival_a /
   tvrd_igrow_a / tvrd_iexit_a, and their GENERIC forms tvrd_ikey_aP / tvrd_ival_aP / tvrd_igrow_aP / tvrd_iexit_aP
   (the memory invariant Pm, and the element count as the loop's progress), each old Prop the corollary of its
   generic form at Pm := fun _ => True. No Axiom, Parameter, Admitted, admit or Abort.
   Numerals: listing slots and pcs (DERIVED: A_prog_base + 4 * slot), 56 / 8 / 4 / 24 / 144 (LENGTH: the node, the
   fields, the cursor, parse_items' own frame pi_frame F_parse_items), 32 / 44 / 58 / 93 / 123 / 125 (the grammar's
   bytes), 4294977024 (DERIVED: the white-space bitmask the code builds). No ADDRESS literal. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YGcfRoomPre YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetReqAt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import
Img0 Listing_prog PAImg_prog PRH_Base PRH_Img PRH_Reader PRH_FnReader PRH_Charge PRH_FnParse VrdFrame.
(* the re-hiding move's SRr' / wle' (YA0nH) and preset's zone (YGcfRehidePost.RZ_cf); the threaded hull budget *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the boundaries, as listing slots of A_prog_listing (slot k is at A_prog_base + 4 k) ---- *)
Definition A_IELEM_SLOT : nat := 6040%nat.   (* row 108, A 0x87440: the loop head *)
Definition A_ISLOT_SLOT : nat := 6142%nat.   (* row 210, A 0x875d8: the value slot's address computation *)
Definition A_ICOMMA_SLOT : nat := 6212%nat.  (* row 280, A 0x876f0: a0 := v, just before `jal grow` *)
Definition A_IEPI_SLOT : nat := 6242%nat.    (* row 310, A 0x87768: `mv a0, s2`, which every exit joins *)
Definition A_IPC (k : nat) : Z := A_prog_base + 4 * Z.of_nat k.

(* ---- the model's positions in PjGrammar.jrl, VERBATIM pieces of its body (so that every unfolding below is
   reflexivity, not a pair-eta argument) ---- *)

(* after the name: the value, then the separator *)
Definition vrd_jval (d : nat) (o : bool) (n cap1 : nat) (acc : list (list Z * jv)) (f : nat) (name y1 : list Z)
  : PjGrammar.M (jv * list Z) :=
  PjGrammar.jbind (PjGrammar.jrv prh_jr_strtod f d y1) (fun '(v, r) =>
  match PjGrammar.skip r with
  | c :: r1 =>
      if c =? 44 then PjGrammar.jrl prh_jr_strtod f d o (S n) cap1 ((name, v) :: acc) r1
      else if c =? PjGrammar.closer o then PjGrammar.jret (PjGrammar.mk o (rev ((name, v) :: acc)), r1)
      else PjGrammar.jrefuse
  | [] => PjGrammar.jrefuse
  end).

(* after the grow: the name, then vrd_jval (the machine does the grow of iteration i at the end of iteration
   i - 1, and the one of iteration 0 in the prologue, so at the machine's loop head the model's grow has run) *)
Definition vrd_jtail (d : nat) (o : bool) (n cap1 : nat) (acc : list (list Z * jv)) (f : nat) (y : list Z)
  : PjGrammar.M (jv * list Z) :=
  PjGrammar.jbind (PjGrammar.jr_name o y) (fun '(name, y1) => vrd_jval d o n cap1 acc f name y1).

Lemma vrd_jrl_unfold : forall d o n cap acc f y,
  PjGrammar.jrl prh_jr_strtod (S f) d o n cap acc y =
  PjGrammar.jbind (PjGrammar.grow o n cap) (fun cap1 => vrd_jtail d o n cap1 acc f y).
Proof. reflexivity. Qed.

(* IproB's three clauses (the grow just made, for every tail okt; the loop's call of jrl before that grow; the
   granted prefix okp) give this file's factorisation at the loop head *)
Lemma vrd_jr_items_after_grow : forall d o x (okp okg : list bool) tr0 trg f n cap0 cap acc y,
  (forall okt, PjGrammar.grow o n cap0 (okg ++ okt) = (Some cap, trg, okt)) ->
  (forall okt r t ok2, PjGrammar.jrl prh_jr_strtod (S f) (S d) o n cap0 acc y okt = (r, t, ok2) ->
     PjGrammar.jr_items prh_jr_strtod d o x (okp ++ okt) = (r, tr0 ++ t, ok2)) ->
  forall okt, PjGrammar.jr_items prh_jr_strtod d o x ((okp ++ okg) ++ okt) =
    (fst (fst (vrd_jtail (S d) o n cap acc f y okt)),
     (tr0 ++ trg) ++ snd (fst (vrd_jtail (S d) o n cap acc f y okt)),
     snd (vrd_jtail (S d) o n cap acc f y okt)).
Proof.
  intros d o x okp okg tr0 trg f n cap0 cap acc y HG HM okt.
  rewrite <- app_assoc.
  destruct (vrd_jtail (S d) o n cap acc f y okt) as [[r t] ok2] eqn:ET. cbn [fst snd].
  rewrite (HM (okg ++ okt) r (trg ++ t) ok2); [rewrite app_assoc; reflexivity|].
  rewrite vrd_jrl_unfold. unfold PjGrammar.jbind at 1. rewrite HG. cbv beta iota. rewrite ET. reflexivity.
Qed.

(* ---- the model's FREE LIST at the same positions (FREEORD-NONE): PresetReqAt.jfl (PresetReqAt.v:273-294), VERBATIM
   pieces of its body as vrd_jtail / vrd_jval are of jrl's (a Theorem Labs lane's B' twins PItems_defs.v pi_jfb / pi_jfv_k at
   a working branch 34d46afa0965, same bodies). jfl threads the accumulator af of the completed slots'
   blocks (each slot: its value's list, then its key's) and ends in af ++ the container's arrays. ---- *)

(* jfl's body after a granted grow (the loop head) *)
Definition vrd_jfb (f d : nat) (o : bool) (n cap1 : nat) (af y : list Z) (ok1 : list bool) : list Z :=
  match PjGrammar.jr_name o y ok1 with
  | (None, _, _) => af ++ PresetReqAt.arrz o cap1
  | (Some (_, y1), tn, ok2) =>
    let af1 := af ++ PresetReqAt.jfv ReaderRes.jr_strtod f d y1 ok2 ++ PresetReqAt.lf tn in
    match PjGrammar.jrv ReaderRes.jr_strtod f d y1 ok2 with
    | (Some (_, r), _, ok3) =>
      match PjGrammar.skip r with
      | c :: r1 => if c =? 44 then PresetReqAt.jfl ReaderRes.jr_strtod f d o (S n) cap1 af1 r1 ok3
                   else af1 ++ PresetReqAt.arrz o cap1
      | [] => af1 ++ PresetReqAt.arrz o cap1
      end
    | (None, _, _) => af1 ++ PresetReqAt.arrz o cap1
    end
  end.

(* jfl's body after the key (lk = PresetReqAt.lf of the key's trace: its one block, [] for an array) *)
Definition vrd_jfvk (f d : nat) (o : bool) (n cap1 : nat) (af lk y1 : list Z) (ok2 : list bool) : list Z :=
  let af1 := af ++ PresetReqAt.jfv ReaderRes.jr_strtod f d y1 ok2 ++ lk in
  match PjGrammar.jrv ReaderRes.jr_strtod f d y1 ok2 with
  | (Some (_, r), _, ok3) =>
    match PjGrammar.skip r with
    | c :: r1 => if c =? 44 then PresetReqAt.jfl ReaderRes.jr_strtod f d o (S n) cap1 af1 r1 ok3
                 else af1 ++ PresetReqAt.arrz o cap1
    | [] => af1 ++ PresetReqAt.arrz o cap1
    end
  | (None, _, _) => af1 ++ PresetReqAt.arrz o cap1
  end.

Lemma vrd_jfl_unfold : forall f d o n cap af y ok,
  PresetReqAt.jfl ReaderRes.jr_strtod (S f) d o n cap af y ok =
  match PjGrammar.grow o n cap ok with
  | (None, tg, _) => af ++ PresetReqAt.gheld o cap tg
  | (Some cap1, _, ok1) => vrd_jfb f d o n cap1 af y ok1
  end.
Proof. reflexivity. Qed.

Lemma vrd_jfb_key : forall f d o n cap1 af y ok1 nm y1 tn ok2,
  PjGrammar.jr_name o y ok1 = (Some (nm, y1), tn, ok2) ->
  vrd_jfb f d o n cap1 af y ok1 = vrd_jfvk f d o n cap1 af (PresetReqAt.lf tn) y1 ok2.
Proof. intros f d o n cap1 af y ok1 nm y1 tn ok2 E. unfold vrd_jfb. rewrite E. reflexivity. Qed.

(* ---- THE BUDGET CW (the kit's cut): a budget within the cursor set costs no fresh trace, and the other way round, so a
   position's journal at the budget CW is the post's `exists WS, .. /\ wbudget CW 0 WS` (vrd_ijrn's note) ---- *)
Lemma vrd_wbudget_cw : forall CW : list (list Z), YCbqGwild.wbudget CW 0 CW.
Proof. intros CW. unfold YCbqGwild.wbudget. rewrite (YCbqGwild.wfresh_incl CW CW (incl_refl CW)). lia. Qed.

Lemma vrd_wbudget_incl : forall CW WS : list (list Z), YCbqGwild.wbudget CW 0 WS -> incl WS CW.
Proof. intros CW WS H. apply YCbqGwild.wfresh_zero_incl. unfold YCbqGwild.wbudget in H. lia. Qed.

(* after a call whose budget WS1 is within CW, the composed budget CW ++ WS1 (YCbqG.ajournal_xw_sub) widens back
   to CW (YCbqG.ajournal_xw_incl) *)
Lemma vrd_budget_back : forall CW WS1 : list (list Z), YCbqGwild.wbudget CW 0 WS1 -> incl (CW ++ WS1) CW.
Proof. intros CW WS1 H. apply incl_app; [apply incl_refl | exact (vrd_wbudget_incl CW WS1 H)]. Qed.

(* ---- THE ALL-GRANTED RUN MAKES NO REFUSED CALL: under the empty grant list (every call granted, PjGrammar.take) no
   reader of the grammar emits an EFail event. With PjGrammar.agrees it turns "the run under ok has the all-granted
   result and trace" into "ok grants every call of that trace" (vrd_granted_of_same): a first refused call would end
   the trace in EFail (agrees' refusal clause), which the all-granted trace never holds. ---- *)
Definition vrd_nofail {A : Type} (m : PjGrammar.M A) : Prop :=
  forall n, ~ In (PjGrammar.EFail n) (snd (fst (m []))).

Lemma vrd_nf_ret : forall (A : Type) (a : A), vrd_nofail (PjGrammar.jret a).
Proof. intros A a n H. exact H. Qed.

Lemma vrd_nf_refuse : forall (A : Type), vrd_nofail (@PjGrammar.jrefuse A).
Proof. intros A n H. exact H. Qed.

Lemma vrd_nf_alloc : forall k, vrd_nofail (PjGrammar.jalloc k).
Proof. intros k n H. cbn in H. destruct H as [H | []]. discriminate H. Qed.

Lemma vrd_nf_realloc : forall a b, vrd_nofail (PjGrammar.jrealloc a b).
Proof. intros a b n H. cbn in H. destruct H as [H | []]. discriminate H. Qed.

Lemma vrd_nf_free : forall k, vrd_nofail (PjGrammar.jfree k).
Proof. intros k n H. cbn in H. destruct H as [H | []]. discriminate H. Qed.

Lemma vrd_nf_bind : forall (A C : Type) (m : PjGrammar.M A) (k : A -> PjGrammar.M C),
  PjGrammar.agrees m -> vrd_nofail m -> (forall a, vrd_nofail (k a)) -> vrd_nofail (PjGrammar.jbind m k).
Proof.
  intros A C m k Hag Hm Hk n H.
  pose proof (Hm n) as Hmn. pose proof (PjGrammar.agrees_nil _ m Hag) as E0.
  unfold PjGrammar.jbind in H. cbv beta in H. revert E0 Hmn H.
  destruct (m []) as [[[a|] t] ok1]; intros E0 Hmn H; cbn [fst snd] in E0, Hmn, H.
  - assert (Eo : ok1 = []) by (injection E0; intros; assumption). subst ok1.
    pose proof (Hk a n) as Hkn. revert Hkn H.
    destruct (k a []) as [[r t'] ok2]; intros Hkn H; cbn [fst snd] in Hkn, H.
    apply in_app_or in H as [H | H]; [exact (Hmn H) | exact (Hkn H)].
  - exact (Hmn H).
Qed.

Ltac vrd_ag := first
  [ apply PjGrammar.agrees_grow | apply PjGrammar.agrees_jr_name | apply PjGrammar.agrees_jr_string
  | apply PjGrammar.agrees_alloc | apply PjGrammar.agrees_realloc | apply PjGrammar.agrees_free
  | apply PjGrammar.agrees_ret | apply PjGrammar.agrees_refuse | apply PjGrammar.agrees_lit
  | apply PjGrammar.agrees_jr_number
  | apply (proj1 (PjGrammar.agrees_fuel _ _)) | apply (proj2 (PjGrammar.agrees_fuel _ _)) ].

Ltac vrd_nf := repeat (cbv beta iota zeta; match goal with
  | |- vrd_nofail (PjGrammar.jbind _ _) => apply vrd_nf_bind; [vrd_ag | |]
  | |- forall p : (_ * _), _ => intros [? ?]
  | |- forall _, _ => intros ?
  | |- vrd_nofail (PjGrammar.jret _) => apply vrd_nf_ret
  | |- vrd_nofail PjGrammar.jrefuse => apply vrd_nf_refuse
  | |- vrd_nofail (PjGrammar.jalloc _) => apply vrd_nf_alloc
  | |- vrd_nofail (PjGrammar.jrealloc _ _) => apply vrd_nf_realloc
  | |- vrd_nofail (PjGrammar.jfree _) => apply vrd_nf_free
  | |- vrd_nofail (PjGrammar.jr_cont _ _ _ _) => unfold PjGrammar.jr_cont
  | H : forall z, vrd_nofail (PjGrammar.jr_string z) |- vrd_nofail (PjGrammar.jr_string _) => apply H
  | H : forall o n cap, vrd_nofail (PjGrammar.grow o n cap) |- vrd_nofail (PjGrammar.grow _ _ _) => apply H
  | H : forall o y, vrd_nofail (PjGrammar.jr_name o y) |- vrd_nofail (PjGrammar.jr_name _ _) => apply H
  | H : forall w v x, vrd_nofail (PjGrammar.lit w v x) |- vrd_nofail (PjGrammar.lit _ _ _) => apply H
  | H : forall x, vrd_nofail (PjGrammar.jr_number _ x) |- vrd_nofail (PjGrammar.jr_number _ _) => apply H
  | H : forall d x, vrd_nofail (PjGrammar.jrv _ _ d x) |- vrd_nofail (PjGrammar.jrv _ _ _ _) => apply H
  | H : forall d o n cap acc y, vrd_nofail (PjGrammar.jrl _ _ d o n cap acc y)
    |- vrd_nofail (PjGrammar.jrl _ _ _ _ _ _ _ _) => apply H
  | |- vrd_nofail (match ?t with _ => _ end) => destruct t
  end).

Lemma vrd_nf_jr_string : forall z, vrd_nofail (PjGrammar.jr_string z).
Proof. intros z. unfold PjGrammar.jr_string. vrd_nf. Qed.

Lemma vrd_nf_grow : forall o n cap, vrd_nofail (PjGrammar.grow o n cap).
Proof. intros o n cap. unfold PjGrammar.grow. vrd_nf. Qed.

Lemma vrd_nf_jr_name : forall o y, vrd_nofail (PjGrammar.jr_name o y).
Proof. pose proof vrd_nf_jr_string. intros o y. unfold PjGrammar.jr_name. vrd_nf. Qed.

Lemma vrd_nf_lit : forall w v x, vrd_nofail (PjGrammar.lit w v x).
Proof. intros w v x. unfold PjGrammar.lit. vrd_nf. Qed.

Lemma vrd_nf_jr_number : forall sm x, vrd_nofail (PjGrammar.jr_number sm x).
Proof. intros sm x. unfold PjGrammar.jr_number. vrd_nf. Qed.

Lemma vrd_nf_fuel : forall sm f,
  (forall d x, vrd_nofail (PjGrammar.jrv sm f d x)) /\
  (forall d o n cap acc y, vrd_nofail (PjGrammar.jrl sm f d o n cap acc y)).
Proof.
  intros sm. pose proof vrd_nf_jr_string. pose proof vrd_nf_grow. pose proof vrd_nf_jr_name. pose proof vrd_nf_lit.
  pose proof (vrd_nf_jr_number sm).
  induction f as [|f [IHv IHl]].
  - split; intros; apply vrd_nf_refuse.
  - split.
    + intros d x. cbn [PjGrammar.jrv]. vrd_nf.
    + intros d o n cap acc y. cbn [PjGrammar.jrl]. vrd_nf.
Qed.

Lemma vrd_nf_jr_value : forall sm d x, vrd_nofail (PjGrammar.jr_value sm d x).
Proof. intros sm d x. apply (proj1 (vrd_nf_fuel sm _)). Qed.

Lemma vrd_nf_jr_items : forall sm d o x, vrd_nofail (PjGrammar.jr_items sm d o x).
Proof.
  intros sm d o x. pose proof (proj2 (vrd_nf_fuel sm (2 * length x + 2))).
  unfold PjGrammar.jr_items. vrd_nf.
Qed.

(* the first refused call of a grant list *)
Lemma vrd_first_false : forall ok i, nth i ok true = false ->
  exists j, (j <= i)%nat /\ nth j ok true = false /\ PjGrammar.ok_upto ok j.
Proof.
  induction ok as [|b ok IH]; intros i Hn.
  - destruct i; discriminate Hn.
  - destruct b.
    + destruct i as [|i]; [discriminate Hn|].
      destruct (IH i Hn) as (j & Hj & Hjn & Hju).
      exists (S j). split; [lia|]. split; [exact Hjn|].
      intros k Hk. destruct k as [|k]; [reflexivity|]. change (nth k ok true = true). apply Hju. lia.
    + exists 0%nat. split; [lia|]. split; [reflexivity|]. intros k Hk. lia.
Qed.

Lemma vrd_granted_of_same : forall (A : Type) (m : PjGrammar.M A) ok r t okr (c f : Z),
  PjGrammar.agrees m -> vrd_nofail m -> m ok = (r, t, okr) -> fst (m []) = (r, t) ->
  PRH_Base.prh_granted ok c f (PjGrammar.calls t).
Proof.
  intros A m ok r t okr c f Hag Hnf Hm Hf i Hi Hn. exfalso.
  destruct (vrd_first_false ok i Hn) as (j & Hji & Hjn & Hju).
  assert (Ht : snd (fst (m [])) = t) by (rewrite Hf; reflexivity).
  destruct (proj2 (Hag ok) j ltac:(rewrite Ht; lia) Hjn Hju) as (P & Ev & rest & Hmo & _ & _ & _).
  rewrite Hm in Hmo. injection Hmo as _ Et _.
  apply (Hnf (PjGrammar.esize Ev)). rewrite Ht, Et. apply in_or_app. right. left. reflexivity.
Qed.

Section W.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg} {RL : PrhRoomLive}.
#[local] Notation PAI := PI_prog_A.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PAI).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).

(* ---- the call's data, fixed for the whole loop: exactly the binders of tparse_items_specX ---- *)
Record vrd_ient : Type := MkIEnt {
  ie_ly : alayout; ie_S : astate; ie_Hp : list Z; ie_W : world SEGS;
  ie_regs : bvmap 5 word; ie_mem : word -> option byte; ie_md : Model;
  ie_ch : list (Z * Z * Z);
  ie_Lam : list (Z * Z); ie_peak : Z; ie_cnt : Z; ie_fail : Z; ie_ran : Z;
  (* the text's g_most and g_own_ran_out (`forall .. most own`): the ledger states them at every position and the
     post states the SAME most own (PRH_Base.prh_ledger's E sweep) *)
  ie_most : Z; ie_own : Z;
  ie_e : Z; ie_q : Z; ie_text : Z; ie_len : Z; ie_p : Z;
  ie_d : nat; ie_tb : list Z; ie_v : Z; ie_o : bool;
  (* THE CALL CHAIN THE LOOP'S OWN CALLS USE. Inside parse_items s0 = q (row 24 `mv s0, a0`), a struct pointer,
     not a frame pointer, and rd_pre puts q between the entry sp and sp + e, so q is above alloc_ceiling, below
     ly_top - 16 and 8-aligned: achain's CUT disjunct is refuted at s0 = q and the entry chain ie_ch does not
     serve. ie_ch2 is the spine of the chain achain admits there; vrd_ijrn carries a chain with that spine at each
     position's own view (the plain form of record text e8db3183ba3), at the LOOP's sp (sp0 - 144), which is the
     WEAKEST place to state it (achain's Forall over the records only gets easier as sp falls). *)
  ie_ch2 : list (Z * Z * Z);
  (* NO ROOM-POSITION FIELDS: the text is in the POST-IMPLICATION form (no entry position premise; the post
     quantifies the model run and position itself), so the six rp binders the entry-keyed form carried are gone *)
  (* THE CURSOR SET CW, the text's fourth parameter (the kit's cut: tparse_items_specX d CTX CTX0 CW, PRH_FnParse.v:391).
     The post is at the budget wbudget CW 0, so every position's journal is at a budget; carrying CW here keeps the
     boundary predicates' arity, and vrd_ient_ok ties it to the Props' CW (ie_CW E = CW) *)
  ie_CW : list (list Z)
}.

(* ---- a state the loop passes through ---- *)
Record vrd_ipos : Type := MkIPos {
  ip_fx : YK11.FPState;
  ip_ly : alayout; ip_S : astate; ip_Hp : list Z; ip_W : world SEGS;
  ip_regs : bvmap 5 word; ip_mem : word -> option byte; ip_md : Model; ip_k : Z;
  (* the progress: n elements read, the capacity and the two arrays, the cursor, the model accumulator (newest
     first, as PjGrammar.jrl builds it), the model's fuel left, the continuation of the model run, the ok list
     the run has eaten, the trace it made and the blocks it owns *)
  ip_n : Z; ip_cap : Z; ip_kids : Z; ip_keys : Z; ip_p : Z;
  ip_acc : list (list Z * jv); ip_f : nat;
  ip_cont : PjGrammar.M (jv * list Z);
  ip_ok : list bool; ip_tr : list ev; ip_D : list (Z * Z);
  ip_Lam : list (Z * Z); ip_peak : Z; ip_cnt : Z; ip_fail : Z; ip_ran : Z
}.

(* the machine configuration of a position, at the pc of a listing slot *)
Definition vrd_cfg (k : nat) (P : vrd_ipos) : config :=
  mkCfg (@YK11.mkst (ip_fx P) (ip_regs P) (w64 (A_IPC k)) (ip_mem P) (YK11.seg_rom SEGS)) (ip_md P).

(* ---- the pieces every boundary state shares ---- *)

(* the twelve callee-saved registers, the entry ra and the four live spill slots, on the frame at sp0 - 144 *)
Definition vrd_iframe (E : vrd_ient) (P : vrd_ipos) : Prop :=
  let sp0 := spZ (ie_regs E) in let m := rdW (ip_W P) (ip_mem P) in
  spZ (ip_regs P) = sp0 - 144 /\
  val_mem SEGS m (sp0 - 8) 8 (raZ (ie_regs E)) /\
  val_mem SEGS m (sp0 - 16) 8 (bv_unsigned (getr (ie_regs E) 8)) /\
  val_mem SEGS m (sp0 - 24) 8 (bv_unsigned (getr (ie_regs E) 9)) /\
  val_mem SEGS m (sp0 - 32) 8 (bv_unsigned (getr (ie_regs E) 18)) /\
  val_mem SEGS m (sp0 - 40) 8 (bv_unsigned (getr (ie_regs E) 19)) /\
  val_mem SEGS m (sp0 - 48) 8 (bv_unsigned (getr (ie_regs E) 20)) /\
  val_mem SEGS m (sp0 - 56) 8 (bv_unsigned (getr (ie_regs E) 21)) /\
  val_mem SEGS m (sp0 - 64) 8 (bv_unsigned (getr (ie_regs E) 22)) /\
  val_mem SEGS m (sp0 - 72) 8 (bv_unsigned (getr (ie_regs E) 23)) /\
  val_mem SEGS m (sp0 - 80) 8 (bv_unsigned (getr (ie_regs E) 24)) /\
  val_mem SEGS m (sp0 - 88) 8 (bv_unsigned (getr (ie_regs E) 25)) /\
  val_mem SEGS m (sp0 - 96) 8 (bv_unsigned (getr (ie_regs E) 26)) /\
  val_mem SEGS m (sp0 - 104) 8 (bv_unsigned (getr (ie_regs E) 27)) /\
  val_mem SEGS m (sp0 - 136) 8 (ie_q E + 8) /\
  val_mem SEGS m (sp0 - 128) 8 (shadow_addr (ie_q E + 16)) /\
  val_mem SEGS m (sp0 - 120) 8 (shadow_addr (ie_v E + 24)) /\
  val_mem SEGS m (sp0 - 112) 8 (ie_v E + 32) /\
  (forall a, sp0 - 144 <= a < sp0 -> apresent (w_H (ip_W P)) (ip_mem P) a).

(* the registers the loop keeps live (the map in this file's header) *)
Definition vrd_iregs (E : vrd_ient) (P : vrd_ipos) : Prop :=
  getr (ip_regs P) 3 = w64 (as_gp B) /\ getr (ip_regs P) 4 = w64 (as_tp B) /\
  getr (ip_regs P) 8 = w64 (ie_q E) /\
  getr (ip_regs P) 9 = w64 (ie_q E + 16) /\
  getr (ip_regs P) 18 = w64 (shadow_addr (ie_v E + 40)) /\
  getr (ip_regs P) 19 = w64 (if ie_o E then 1 else 0) /\
  getr (ip_regs P) 20 = w64 (ie_v E) /\
  getr (ip_regs P) 21 = w64 32 /\
  getr (ip_regs P) 22 = w64 (ie_v E + 40) /\
  getr (ip_regs P) 23 = w64 (shadow_addr (ie_q E + 8)) /\
  getr (ip_regs P) 24 = w64 (ie_v E + 24) /\
  getr (ip_regs P) 25 = w64 4294977024 /\
  getr (ip_regs P) 26 = w64 SHADOW_OFF /\
  getr (ip_regs P) 27 = w64 (shadow_addr (ie_q E)).

(* the node the loop is filling: an array (type 5) or an object (type 6) with n elements and capacity cap; Dx are
   the blocks the position owns besides the arrays and the members (the key just read, at vrd_islot_a) *)
Definition vrd_inode (E : vrd_ient) (P : vrd_ipos) (Dx : list (Z * Z)) : Prop :=
  let m := rdW (ip_W P) (ip_mem P) in
  pj_hdrR SEGS m (ie_v E) (if ie_o E then 6 else 5) 0 0 (ip_kids P) (ip_keys P) (ip_n P) (ip_cap P) /\
  0 <= ip_n P <= ip_cap P /\ ip_cap P <= 2 ^ 54 /\
  (ip_cap P = 0 -> ip_kids P = 0 /\ ip_keys P = 0) /\
  (0 < ip_cap P -> prh_lin (ip_Lam P) (ip_kids P) (56 * ip_cap P) /\
     (ie_o E = true -> prh_lin (ip_Lam P) (ip_keys P) (8 * ip_cap P))) /\
  Z.of_nat (length (ip_acc P)) = ip_n P /\
  (exists Di, Permutation (ip_D P)
       (Dx ++ kids_blkR (ip_kids P) (ip_cap P) ++
        keys_blkR (if ie_o E then 6 else 5) (ip_keys P) (ip_cap P) ++ Di) /\
     (if ie_o E
      then pj_memsR SEGS m (prh_lin (ip_Lam P)) (pj_nodeR SEGS m (prh_lin (ip_Lam P)))
             (ip_kids P) (ip_keys P) (rev (ip_acc P)) Di
      else pj_itemsR (pj_nodeR SEGS m (prh_lin (ip_Lam P))) (ip_kids P) (map snd (rev (ip_acc P))) Di)) /\
  rd_rw SEGS m (ip_kids P + 56 * ip_n P) (56 * (ip_cap P - ip_n P)) /\
  range_addressable (aview SEGS (w_H (ip_W P)) (ip_mem P)) SHADOW_OFF (ie_v E) 56 /\
  (0 < ip_cap P -> range_addressable (aview SEGS (w_H (ip_W P)) (ip_mem P)) SHADOW_OFF
       (ip_kids P) (56 * ip_cap P)) /\
  (ie_o E = true -> 0 < ip_cap P ->
     range_addressable (aview SEGS (w_H (ip_W P)) (ip_mem P)) SHADOW_OFF (ip_keys P) (8 * ip_cap P)) /\
  (* AN ARRAY'S keys FIELD IS ZERO (defect found by a Theorem Labs lane's Ival walk, a Theorem Labs lane's approval 2026-10-29):
     pj_nodeR's JArr arm asks keys = 0 (PRH_Reader.v:144) and pj_fshapeR asks keys = 0 /\ ks = false (:173), so
     without this every array exit - the success exit's pj_nodeR and every res = -1 pj_fdR, the grow refusals
     included - is unprovable. parse_items writes v->keys only for an object, and v is zeroed at entry. *)
  (ie_o E = false -> ip_keys P = 0).

(* the cursor, the text, the ledger and the frames bound at a position; inside parse_items the cursor's depth is
   d + 1. The LAST conjunct is the allocator counter's slack over the text left (a Theorem Labs lane's Ival walk measurement,
   a Theorem Labs lane's approval 2026-10-29): parse_value's rd_pre asks it at the row-231 call at the position's own cursor,
   and only vrd_ient_ok's entry rd_pre carried it, at ie_p E *)
Definition vrd_icur (E : vrd_ient) (P : vrd_ipos) : Prop :=
  let m := rdW (ip_W P) (ip_mem P) in
  pj_in_okR SEGS m (ie_q E) (ie_text E) (ie_len E) (ip_p P) (Z.of_nat (ie_d E) + 1) (ie_tb E) /\
  range_addressable (aview SEGS (w_H (ip_W P)) (ip_mem P)) SHADOW_OFF (ie_q E) 24 /\
  src_rd (ip_W P) (ip_mem P) (ie_text E) (ie_tb E) /\
  prhReader_home B (ip_ly P) (ip_S P) (ip_Hp P) (ip_Lam P) (ie_text E) (ie_len E) /\
  prh_ledger B (ip_ly P) (ip_S P) (ip_Hp P) (ip_W P) (ip_mem P)
    (ip_Lam P) (ip_peak P) (ip_cnt P) (ip_fail P) (ip_ran P) (ie_most E) (ie_own E) /\
  Z.of_nat (length (frames (ip_S P))) + Z.of_nat (PjGrammar.MAXD - ie_d E) <= fs_frames 0 /\
  ip_cnt P + 2 * Z.of_nat (length (rest_atR (ie_tb E) (ie_text E) (ip_p P))) + 2 < 2 ^ 64 - 1.

(* the journal from the call's entry to the position, and the caller window the call was granted. THE JOURNAL IS AT
   THE BUDGET ie_CW E (the kit's cut: the post's fpostWFbm .. (wbudget CW 0); the cursor frees below this call store only
   CW's traces or fixed ones, prh_cw_entry): the wild traces stored since the entry are CW's. That is the post's
   `exists WS, .. WS /\ wbudget CW 0 WS` at WS := CW (wfresh CW CW = 0), and conversely any such WS widens to CW
   (YCbqG.ajournal_xw_incl, as incl WS CW).
   THE RE-HIDING MOVE: the journal is at the world relation wle' SEGS RZ_cf (the hidden set grows only inside the zone
   RZ_cf), not at wle. Every loop position lies after a call that can free or reallocate (the prologue's first grow,
   then parse_value, parse_string and grow inside the loop), and those texts post their journals at wle'; a journal
   at wle lifts to wle' (YCbqG.ajournal_xwR_mono with YA0nH.wle_wle'). *)
Definition vrd_ijrn (E : vrd_ient) (P : vrd_ipos) : Prop :=
  ajournal_xwR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) (STK_parse_items (ie_d E) + ie_e E)
    (spZ (ie_regs E) + ie_e E) (rd_fp (ie_q E) (ie_v E))
    (ie_ly E) (ie_S E) (ie_Hp E) (ie_W E) (ie_mem E) (ie_md E) []
    (ip_ly P) (ip_S P) (ip_Hp P) (ip_W P) (ip_mem P) (ip_md P) (ip_k P) (ie_CW E) /\
  (forall a, spZ (ie_regs E) <= a < spZ (ie_regs E) + ie_e E -> ~ inFP (rd_fp (ie_q E) (ie_v E)) a ->
     aview SEGS (w_H (ip_W P)) (ip_mem P) a = aview SEGS (w_H (ie_W E)) (ie_mem E) a) /\
  frm_zero (@YK11.fp_csr (ip_fx P)) /\ fregs_kept_x fx (ip_fx P) /\
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H (ip_W P)) (ip_mem P)) /\
  rd_blocks_move B (ie_ly E) (ie_S E) (ip_ly P) (ip_S P) (ip_D P) (ip_tr P)
    (rest_atR (ie_tb E) (ie_text E) (ie_p E)) (ie_d E) /\
  (* the chain of the loop's own calls, PLAINLY at this position's view (record text e8db3183ba3, PRH_FnParse.v
     blob e31806f7bdb0: the rd'-quantified per-reader form is REFUTED, PItemsB / PValueB on image B): a chain at
     (sp, q) with the spine the call contexts (vrd_ient_ok) are about *)
  (exists ch', achain (ip_ly P) (aview SEGS (w_H (ip_W P)) (ip_mem P)) (spZ (ie_regs E) - 144) (ie_q E) ch' /\
     spine ch' = spine (ie_ch2 E)).

(* the model: the whole call's run factors through the position's continuation, with the trace so far in front,
   and the ledger has moved by that trace. THE ORACLE (a Theorem Labs lane's ruling of record, IproB's shape): the ok list
   the steps have eaten is the GRANTED PREFIX - one `true` per allocator call the trace made, because every
   refusal leaves the loop - and the TAIL okr is quantified, so every later refusal (fuzz_alloc_fail's chosen
   failure, the class-full NULL inside parse_value, parse_string or a later grow) stays reachable. The room is the
   margin, request and live room of the GRANTED continuation (ip_cont P []), and the fuel covers the text left.
   WHY NOT prhPi_gtrace AT THE CURSOR (the first text's form, found by IelemB and by IproB independently): that is
   the trace of a jr_items run started at the loop position, not of the rest of this run, and it is unreachable:
   text "[{}]", o = false, d < MAXD, kr = 0. At entry prhPi_gtrace d false "[{}]" = [EGrow 0 448] gives
   room for 2; at the loop head the cursor is at '{' and prhPi_gtrace d false "{}]" = [EGrow 0 448] again, so
   the old form asked for that room AFTER the first grow, while that grow needs it BEFORE, with the tail's on top.
   The continuation's granted trace splits additively: the entry trace is ip_tr P ++ that trace.
   THE TWO CONJUNCTS AFTER Forall (IelemD's boundary defect, a Theorem Labs lane's approval 2026-10-29): a refusal INSIDE the
   loop (grow at row 281, parse_value in the element step, the key's parse_string) leaves through vrd_iexit_a, whose
   blocks_bytes bound and pj_fdR of the partly built node follow from no other conjunct here: the user bytes held
   since the call's entry (PRH_Charge.prh_held: heads counted), and the depth of the elements read so far
   (cont_depth's own loop invariant, PjGrammar.v:1475), which VrdFrame.vrd_node_fd turns into pj_fdR. Then
   Ledger.lsum (ip_D P) = held (ip_tr P) (IelemD's composition finding; a Theorem Labs lane's ruling, record text
   35c30929451): composing rd_ledger_move across a call re-associates the peak only when the blocks the position
   owns hold exactly the user bytes its trace holds.
   THE LEDGER MOVE IS THE TEXT'S (#102's refusal rule, kit PRH_FnParse.v blob 94232293d483): it takes most and the
   ALL-GRANTED trace gt, here the WHOLE call's, prhPi_gtrace at the entry cursor - the one the post states, so the
   exit hands it to the epilogue unchanged. On the granted prefix ip_ok P the refusal peak is 0 whatever gt is
   (PRH_Base.prh_refused_peak_granted).
   THE POSITION (POST-IMPLICATION form, a Theorem Labs lane's ruling 17:40Z; a Theorem Labs lane's restatement ruling for this lane):
   the text's position-transfer conjunct from the call's entry state ie_S E to this position, over the events made
   so far, rd_hevs (ip_tr P), at ANY model run and position the caller picks. A callee's own transfer composes onto
   it by PRH_Base.prh_run_at_app_iff (vrd_xfer_app below); at the exit it IS the post's conjunct, tr = ip_tr P.
   THE LIVE REQUESTS (the post's hlive_from conjunct, same composition) come next.
   THE HULL USE (the text's threaded hull budget, PresetHullBudget) is the LAST conjunct: the two secondary-mapping
   meters moved, from the call's entry state, by at most the counts of the events made so far. With the entry budget
   (vrd_ient_ok) it pays a callee's budget (PresetHullBudget.hull_budget_infix: the events so far, then the callee's
   all-granted list, inside the call's all-granted list) and composes with the callee's hull_used
   (PresetHullBudget.hull_used_app). *)

Definition vrd_imodel (E : vrd_ient) (P : vrd_ipos) : Prop :=
  ip_ok P = repeat true (PjGrammar.calls (ip_tr P)) /\
  (forall okr, PjGrammar.jr_items prh_jr_strtod (ie_d E) (ie_o E)
       (rest_atR (ie_tb E) (ie_text E) (ie_p E)) (ip_ok P ++ okr) =
     (fst (fst (ip_cont P okr)), ip_tr P ++ snd (fst (ip_cont P okr)), snd (ip_cont P okr))) /\
  rd_ledger_move (ie_Lam E) (ie_peak E) (ie_cnt E) (ie_fail E) (ie_ran E) (ie_most E) (ip_ok P)
    (prhPi_gtrace (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E))) (ip_tr P)
    (ip_D P) (ip_Lam P) (ip_peak P) (ip_cnt P) (ip_fail P) (ip_ran P) /\
  rd_room (ip_S P) (snd (fst (ip_cont P []))) /\
  (2 * length (rest_atR (ie_tb E) (ie_text E) (ip_p P)) + 1 <= ip_f P)%nat /\
  blocks_bytes (ip_S P) <= blocks_bytes (ie_S E) + prh_held (ip_tr P) /\
  Forall (fun m => (PjTree.depth (snd m) <= PjGrammar.MAXD - S (ie_d E))%nat) (ip_acc P) /\
  Ledger.lsum (ip_D P) = PjGrammar.held (ip_tr P) /\
  (* THE POSITION TRANSFER, from the call's entry to this position (the post's conjunct at S := ie_S E,
     tr := ip_tr P, S' := ip_S P) *)
  (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
     (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm x os i H0 hist (ie_S E) ->
     PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs (ip_tr P)) ->
     exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (PresetReqAt.rd_hevs (ip_tr P)))%nat H0 hist'
       (ip_S P)) /\
  (* the live requests moved by the events made so far (the post's hlive_from conjunct) *)
  Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf (ip_S P)))
    (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf (ie_S E))) (PresetReqAt.rd_hevs (ip_tr P))) /\
  (* the hull meters moved by at most the events made so far *)
  PresetHullBudget.hull_used (ie_S E) (ip_S P) (PresetReqAt.rd_hevs (ip_tr P)).

(* ---- THE BATCH KIT'S LAYER (the kit's cut: the post's free order and capacity conjuncts, FREEORD-NONE / CAP). The post's
   Some arm asks pj_ncapR of the container's tree and, with its None arm, pj_free's ORDER LIST of what the call leaves in
   the node against the model's prhPi_frees. No other conjunct of a boundary gives either (pj_nodeR / pj_fdR give
   neither the caps nor an order), so each boundary carries them, as a Theorem Labs lane's B' twin does (PItems_defs.v
   pi_ncaps / pi_forder, a working branch 34d46afa0965). They are SEPARATE conjuncts, appended last, so
   vrd_inode and its frame lemmas are untouched. ---- *)

(* the members' capacities: each member read so far (rev (ip_acc P), in slot order, member i at kids + 56 i) is a
   tree whose containers have cap = ncap of their count (PRH_Reader.pj_ncapR) *)
Definition vrd_incaps (E : vrd_ient) (P : vrd_ipos) : Prop :=
  pj_kidsR (fun a (mb : list Z * jv) => pj_ncapR SEGS (rdW (ip_W P) (ip_mem P)) a (snd mb)) (ip_kids P)
    (rev (ip_acc P)).

(* the completed slots' ORDER LIST (PRH_PjOrder.pf_oitemsR: each slot's value subtree, then its key), at every depth
   bound nn covering the members read so far (the Some arm asks n >= depth t, below MAXD - d too; a refusal's
   n >= MAXD - d is covered by vrd_imodel's depth conjunct), maps to af, the accumulator of the model's jfl at this
   point; its block list Di is the rest of ip_D P beside the extra blocks Dx (the key just read, at vrd_islot_a) and
   the two arrays: a permutation of vrd_inode's Di when Dx is the same list (only the permutation of ip_D ties them) *)
Definition vrd_iforder (E : vrd_ient) (P : vrd_ipos) (Dx : list (Z * Z)) (af : list Z) : Prop :=
  cf_head = PresetReqAt.HEAD -> forall nn, Forall (fun mb => (PjTree.depth (snd mb) <= nn)%nat) (ip_acc P) ->
  exists Di Facc,
    Permutation (ip_D P)
      (Dx ++ kids_blkR (ip_kids P) (ip_cap P) ++ keys_blkR (if ie_o E then 6 else 5) (ip_keys P) (ip_cap P) ++ Di) /\
    PRH_PjOrder.pf_oitemsR SEGS (rdW (ip_W P) (ip_mem P)) (prh_lin (ip_Lam P))
      (PRH_PjOrder.pj_foR SEGS (rdW (ip_W P) (ip_mem P)) (prh_lin (ip_Lam P)) nn) (ie_o E) (ip_kids P) (ip_keys P)
      (Z.to_nat (ip_n P)) Di Facc /\
    map (fun b => snd b + cf_head) Facc = af.

(* ---- THE LOOP HEAD (A 0x87440, slot 6040): the state lane IproB's prologue reaches and every step of this lane
   returns to, with the count and the accumulator one longer ---- *)
Definition vrd_ielem_a (E : vrd_ient) (P : vrd_ipos) : Prop :=
  vrd_iframe E P /\ vrd_iregs E P /\ vrd_inode E P [] /\ vrd_icur E P /\ vrd_ijrn E P /\ vrd_imodel E P /\
  (* the loop head is entered with room for one more element: grow has just run *)
  ip_n P < ip_cap P /\
  (* the model is at the point of jrl's body after this iteration's grow *)
  ip_cont P = vrd_jtail (S (ie_d E)) (ie_o E) (Z.to_nat (ip_n P)) (Z.to_nat (ip_cap P)) (ip_acc P)
                 (ip_f P) (rest_atR (ie_tb E) (ie_text E) (ip_p P)) /\
  (* THE BATCH KIT'S LAYER after the grow: cap = ncap (S n), the members' caps, the order list against af, and the model's
     free list at jfl's body after the grow (vrd_jfb), at the same fuel as ip_cont *)
  ip_cap P = Z.of_nat (PresetReqAt.ncap (S (Z.to_nat (ip_n P)))) /\ vrd_incaps E P /\
  exists af, vrd_iforder E P [] af /\
    (forall okr, prhPi_frees (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E)) (ip_ok P ++ okr) =
       vrd_jfb (ip_f P) (S (ie_d E)) (ie_o E) (Z.to_nat (ip_n P)) (Z.to_nat (ip_cap P)) af
         (rest_atR (ie_tb E) (ie_text E) (ip_p P)) okr).

(* ---- after the key path (A 0x875d8, slot 6142): this element's key is read and stored and the cursor is past
   the colon; for an array nothing was read and the name is empty ---- *)
Definition vrd_islot_a (E : vrd_ient) (P : vrd_ipos) (nm : list Z) : Prop :=
  vrd_iframe E P /\ vrd_iregs E P /\ vrd_icur E P /\ vrd_ijrn E P /\ vrd_imodel E P /\
  ip_n P < ip_cap P /\
  (* the key slot keys[n] holds the new name's block, which the position owns beside the members; for an array
     nm is empty and nothing was stored *)
  (if ie_o E
   then exists x k, rd_u64 SEGS (rdW (ip_W P) (ip_mem P)) (ip_keys P + 8 * ip_n P) x /\
          pj_cstrR SEGS (rdW (ip_W P) (ip_mem P)) (prh_lin (ip_Lam P)) x k nm /\ vrd_inode E P [(x, k)]
   else nm = [] /\ vrd_inode E P []) /\
  (* the model has eaten the name and is at the value *)
  ip_cont P = vrd_jval (S (ie_d E)) (ie_o E) (Z.to_nat (ip_n P)) (Z.to_nat (ip_cap P)) (ip_acc P) (ip_f P) nm
                (rest_atR (ie_tb E) (ie_text E) (ip_p P)) /\
  (* THE BATCH KIT'S LAYER after the key: cap = ncap (S n), the members' caps; the key slot keys[n]'s block list Dk (the key
     just read for an object, [] for an array) is the extra block of the order list, its requests are the model's lk
     (PresetReqAt.lf of the key's trace), and the model's free list is at jfl's body after the key (vrd_jfvk) *)
  ip_cap P = Z.of_nat (PresetReqAt.ncap (S (Z.to_nat (ip_n P)))) /\ vrd_incaps E P /\
  exists Dk af lk,
    pj_keyR SEGS (rdW (ip_W P) (ip_mem P)) (prh_lin (ip_Lam P)) (ie_o E) (ip_keys P + 8 * ip_n P) Dk /\
    vrd_iforder E P Dk af /\
    (cf_head = PresetReqAt.HEAD -> map (fun b => snd b + cf_head) Dk = lk) /\
    (forall okr, prhPi_frees (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E)) (ip_ok P ++ okr) =
       vrd_jfvk (ip_f P) (S (ie_d E)) (ie_o E) (Z.to_nat (ip_n P)) (Z.to_nat (ip_cap P)) af lk
         (rest_atR (ie_tb E) (ie_text E) (ip_p P)) okr).

(* ---- after the element and the comma (A 0x876f0, slot 6212, row 280 `mv a0, s4`): one more element is in the
   node and the cursor is past the comma. NO a0 CLAUSE: at this pc `mv a0, s4` has NOT run yet, and row 279's
   `sd a0, 0(s0)` left a0 = p (the cursor past the comma), not v; the step lemma runs the `mv` itself and reads
   v out of s4, which vrd_iregs pins (defect found and corrected by IelemC, 2026-10-29) ---- *)
Definition vrd_icomma_a (E : vrd_ient) (P : vrd_ipos) : Prop :=
  vrd_iframe E P /\ vrd_iregs E P /\ vrd_inode E P [] /\ vrd_icur E P /\ vrd_ijrn E P /\ vrd_imodel E P /\
  0 < ip_n P /\
  (* the counter's slack for grow's (at most two) calls on top of vrd_icur's: grow asks cnt + 2 < 2 ^ 64 - 1 and
     the loop head after it needs vrd_icur's slack again (the comma byte just consumed pays for it) *)
  ip_cnt P + 2 * Z.of_nat (length (rest_atR (ie_tb E) (ie_text E) (ip_p P))) + 4 < 2 ^ 64 - 1 /\
  (* the model is at jrl's head for the next element: its grow is the machine's `jal grow` below *)
  ip_cont P = PjGrammar.jrl prh_jr_strtod (S (ip_f P)) (S (ie_d E)) (ie_o E) (Z.to_nat (ip_n P))
                (Z.to_nat (ip_cap P)) (ip_acc P) (rest_atR (ie_tb E) (ie_text E) (ip_p P)) /\
  (* THE BATCH KIT'S LAYER before the grow: cap = ncap n (the n accepted members), the members' caps, the order list against
     af, and the model's free list at jfl's head, at the same fuel as ip_cont *)
  ip_cap P = Z.of_nat (PresetReqAt.ncap (Z.to_nat (ip_n P))) /\ vrd_incaps E P /\
  exists af, vrd_iforder E P [] af /\
    (forall okr, prhPi_frees (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E)) (ip_ok P ++ okr) =
       PresetReqAt.jfl ReaderRes.jr_strtod (S (ip_f P)) (S (ie_d E)) (ie_o E) (Z.to_nat (ip_n P))
         (Z.to_nat (ip_cap P)) af (rest_atR (ie_tb E) (ie_text E) (ip_p P)) okr).

(* ---- THE EXIT (A 0x87768, slot 6242, `mv a0, s2`): the state the epilogue starts from, s2 = the result, with
   the whole call's answer already established. The position transfer, the OUTCOME and the live requests are the
   text's post conjuncts at S := ie_S E, S' := ip_S P, tr := ip_tr P; the OUTCOME's `(res, tr)` is the instance's
   answer below, so it is stated as fst of the granted run against fst of the run at ip_ok P (the epilogue reads
   the post's res and tr off that run). The step that exits establishes it: on a success exit from the granted
   prefix alone (vrd_outcome_granted below), on a refusal exit from the refusing callee's outcome clause or
   refused-arm exclusion (PRH_Base.v, THE OUTCOME UNDER THE RUN HYPOTHESIS). ---- *)
Definition vrd_iexit_a (E : vrd_ient) (P : vrd_ipos) (res : Z) : Prop :=
  vrd_iframe E P /\ vrd_ijrn E P /\
  getr (ip_regs P) 3 = w64 (as_gp B) /\ getr (ip_regs P) 4 = w64 (as_tp B) /\
  getr (ip_regs P) 18 = w64 res /\ (res = 0 \/ res = -1) /\
  prh_ledger B (ip_ly P) (ip_S P) (ip_Hp P) (ip_W P) (ip_mem P)
    (ip_Lam P) (ip_peak P) (ip_cnt P) (ip_fail P) (ip_ran P) (ie_most E) (ie_own E) /\
  room_live_cf (ip_S P) /\
  (* THE POSITION TRANSFER (the post's conjunct) *)
  (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
     (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm x os i H0 hist (ie_S E) ->
     PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs (ip_tr P)) ->
     exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (PresetReqAt.rd_hevs (ip_tr P)))%nat H0 hist'
       (ip_S P)) /\
  (* THE OUTCOME (the post's conjunct) *)
  (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
     (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm x os i H0 hist (ie_S E) ->
     PRH_Base.prh_run_at sm x os i
       (PresetReqAt.rd_hevs (prhPi_gtrace (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E)))) ->
     PRH_Base.prh_cons_from sm x os i
       (length (PresetReqAt.rd_hevs (prhPi_gtrace (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E))))) ->
     (ie_fail E < ie_cnt E \/
      ie_cnt E + Z.of_nat (PjGrammar.calls (prhPi_gtrace (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E))))
        <= ie_fail E) ->
     ip_ran P = ie_ran E /\
     fst (PjGrammar.jr_items ReaderRes.jr_strtod (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E)) []) =
       fst (PjGrammar.jr_items ReaderRes.jr_strtod (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E))
              (ip_ok P)) /\
     exists hist', PresetRoomPos.iface_room_pos sm x os
       (i + length (PresetReqAt.rd_hevs (prhPi_gtrace (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E)))))%nat
       H0 hist' (ip_S P)) /\
  rd_ledger_move (ie_Lam E) (ie_peak E) (ie_cnt E) (ie_fail E) (ie_ran E) (ie_most E) (ip_ok P)
    (prhPi_gtrace (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E))) (ip_tr P)
    (ip_D P) (ip_Lam P) (ip_peak P) (ip_cnt P) (ip_fail P) (ip_ran P) /\
  (* the live room handed on to the caller's next call, as the record text's post now asks (prh_held: the
     corrected form a Theorem Labs lane relayed, heads counted; the plain held form is false on a run that allocates) *)
  blocks_bytes (ip_S P) <= blocks_bytes (ie_S E) + prh_held (ip_tr P) /\
  Ledger.lsum (ip_D P) = PjGrammar.held (ip_tr P) /\
  (* the answer of the whole call, in the shape tparse_items_specX asks for *)
  (exists r2 okr,
     PjGrammar.jr_items prh_jr_strtod (ie_d E) (ie_o E)
       (rest_atR (ie_tb E) (ie_text E) (ie_p E)) (ip_ok P) =
     ((if res =? 0 then Some (PjGrammar.mk (ie_o E) (rev (ip_acc P)), r2) else None), ip_tr P, okr) /\
     (res = 0 ->
        pj_in_okR SEGS (rdW (ip_W P) (ip_mem P)) (ie_q E) (ie_text E) (ie_len E)
          (ie_text E + ie_len E - Z.of_nat (length r2)) (Z.of_nat (ie_d E)) (ie_tb E) /\
        pj_nodeR SEGS (rdW (ip_W P) (ip_mem P)) (prh_lin (ip_Lam P)) (ie_v E)
          (PjGrammar.mk (ie_o E) (rev (ip_acc P))) (ip_D P) /\
        Ledger.lsum (ip_D P) <=
          224 * (Z.of_nat (length (rest_atR (ie_tb E) (ie_text E) (ie_p E))) - Z.of_nat (length r2)) /\
        (* The kit's cut, APPENDED: the post's Some-arm free order and capacity (FREEORD-NONE, CAP) *)
        (cf_head = PresetReqAt.HEAD -> forall n, (PjTree.depth (PjGrammar.mk (ie_o E) (rev (ip_acc P))) <= n)%nat ->
           exists F, PRH_PjOrder.pj_foR SEGS (rdW (ip_W P) (ip_mem P)) (prh_lin (ip_Lam P)) n (ie_v E) (ip_D P) F /\
             map (fun b => snd b + cf_head) F =
               prhPi_frees (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E)) (ip_ok P)) /\
        pj_ncapR SEGS (rdW (ip_W P) (ip_mem P)) (ie_v E) (PjGrammar.mk (ie_o E) (rev (ip_acc P)))) /\
     (res = -1 ->
        pj_in_afterR SEGS (rdW (ip_W P) (ip_mem P)) (ie_q E) (ie_text E) (ie_len E)
          (Z.of_nat (ie_d E) + 1) 33 /\
        pj_fdR SEGS (rdW (ip_W P) (ip_mem P)) (prh_lin (ip_Lam P)) (PjGrammar.MAXD - ie_d E)
          (ie_v E) (ip_D P) /\
        (* The kit's cut, APPENDED: the post's None-arm free order (FREEORD-NONE) *)
        (cf_head = PresetReqAt.HEAD -> forall n, (PjGrammar.MAXD - ie_d E <= n)%nat ->
           exists F, PRH_PjOrder.pj_foR SEGS (rdW (ip_W P) (ip_mem P)) (prh_lin (ip_Lam P)) n (ie_v E) (ip_D P) F /\
             map (fun b => snd b + cf_head) F =
               prhPi_frees (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E)) (ip_ok P)))) /\
  (* the live requests moved by the events the instance made (the post's hlive_from conjunct) *)
  Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf (ip_S P)))
    (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf (ie_S E))) (PresetReqAt.rd_hevs (ip_tr P))) /\
  (* THE HULL USE (the post's conjunct): the meters moved by at most the call's all-granted events *)
  PresetHullBudget.hull_used (ie_S E) (ip_S P)
    (PresetReqAt.rd_hevs (prhPi_gtrace (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E)))) /\
  (* THE OUTCOME OF AN INJECTED READING (the post's conjunct): at a model run and position whose next events are the
     call's under the model's grant list with the chosen failure at call fail - cnt (PresetReqAt.okk), all consumer
     events, with the chosen failure inside the call's window, no call of the instance was refused *)
  (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
     (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm x os i H0 hist (ie_S E) ->
     PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs (snd (fst (PjGrammar.jr_items ReaderRes.jr_strtod (ie_d E)
       (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E)) (PresetReqAt.okk (Z.to_nat (ie_fail E - ie_cnt E))))))) ->
     PRH_Base.prh_cons_from sm x os i (length (PresetReqAt.rd_hevs (snd (fst (PjGrammar.jr_items ReaderRes.jr_strtod
       (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E)) (PresetReqAt.okk (Z.to_nat (ie_fail E - ie_cnt E)))))))) ->
     ie_cnt E <= ie_fail E <
       ie_cnt E + Z.of_nat (PjGrammar.calls (prhPi_gtrace (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E)))) ->
     PRH_Base.prh_granted (ip_ok P) (ie_cnt E) (ie_fail E) (PjGrammar.calls (ip_tr P))).

(* the listing slots the loop RETURNS TO: parse_string (row 148, slot 6080), __asan_memset (row 223, 6155),
   parse_value (row 231, 6163), grow (row 281, 6213) and fuzz_free (row 308, 6240), each + 1 *)
Definition A_IRET_SLOTS : list nat := [6081%nat; 6156%nat; 6164%nat; 6214%nat; 6241%nat].

(* ---- the entry data of one call, as tparse_items_specX hands it over (the kit's cut, PRH_FnParse.v blob f0d92dcec7e9:
   the kit's call-graph universe closure, the cursor chain's stop word, the cursor set CW and its wild room, the entry
   chain plainly at the entry view; the POST-IMPLICATION form has NO entry room position) ---- *)
Definition vrd_ient_ok (CTX CTX0 : list (list Z)) (CW : list (list Z)) (E : vrd_ient) : Prop :=
  fpre B ARx (STK_parse_items (ie_d E)) (ie_ly E) (ie_S E) (ie_Hp E) (ie_W E)
    (ie_regs E) (ie_mem E) (ie_md E) (ie_ch E) /\
  getr (ie_regs E) 10 = w64 (ie_q E) /\ getr (ie_regs E) 11 = w64 (ie_v E) /\
  getr (ie_regs E) 12 = w64 (if ie_o E then 1 else 0) /\
  rd_pre B (STK_parse_items (ie_d E)) (ie_ly E) (ie_S E) (ie_Hp E) (ie_W E) (ie_regs E) (ie_mem E)
    (ie_Lam E) (ie_peak E) (ie_cnt E) (ie_fail E) (ie_ran E) (ie_most E) (ie_own E) (ie_e E) (ie_q E) (ie_text E)
    (ie_len E) (ie_p E) (ie_d E) (ie_tb E) (ie_v E) /\
  ie_p E < ie_text E + ie_len E /\
  nth_error (ie_tb E) (Z.to_nat (ie_p E - ie_text E)) = Some (if ie_o E then 123 else 91) /\
  rd_room (ie_S E)
    (prhPi_gtrace (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E))) /\
  (* ONE SLOT for the text's three position-free premises the entry-keyed form did not have (in the slot the entry
     room position held, so every other conjunct keeps its place): the normal memory overlay at entry, and THE
     LIVE COUNTS AT THE INNER CALLS along the ALL-GRANTED events, verbatim *)
  (YAkMemnorm.memnorm SEGS (ie_mem E) /\
   Z.of_nat (PresetRun.pkR YGcfRoomLive.rl_sec_req (PresetRoom.rs_live (YGcfRoom.room_of_cf (ie_S E)))
     (PresetReqAt.rd_hevs (prhPi_gtrace (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E))))) <=
     PresetLiveBounds.LSEC + PresetLiveBounds.DRV /\
   Z.of_nat (PresetRun.pkR (PresetRoom.in_cls YG00.kBatchClass) (PresetRoom.rs_live (YGcfRoom.room_of_cf (ie_S E)))
     (PresetReqAt.rd_hevs (prhPi_gtrace (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E))))) <=
     PresetLiveBounds.L24 + PresetLiveBounds.DRV) /\
  (* the premises of tparse_items_specX this file did not mirror (PRH_FnParse.v blob f0d92dcec7e9), in its order except
     prh_cw_entry, which is in the trailing slot below:
     the call's own context, the universe closure and the cursor chain's stop word (the kit's cut: no DW), the entry chain
     with its spine at the entry view, the PARTITIONED chain at the cursor (a Theorem Labs lane's 06:39Z ruling; the key path's
     parse_string call needs it, from prh_s0 F_parse_string q), and the chain from prh_s0 F_parse_items q at the
     loop's sp that parse_items' own fuzz_free needs (the kit owner's (2), replacing D4) *)
  In (raZ (ie_regs E) :: spine (ie_ch E)) CTX /\
  prh_univ_closure B CTX0 /\
  prh_cur_entry (ie_W E) (ie_mem E) (ie_regs E) (ie_q E) /\
  (exists ch', achain (ie_ly E) (aview SEGS (w_H (ie_W E)) (ie_mem E)) (spZ (ie_regs E)) (s0Z (ie_regs E)) ch' /\
     spine ch' = spine (ie_ch E)) /\
  ((spZ (ie_regs E) <= ie_q E < spZ (ie_regs E) + 16) \/
   (spZ (ie_regs E) + 16 <= ie_q E /\
    exists ch', achain (ie_ly E) (aview SEGS (w_H (ie_W E)) (ie_mem E)) (spZ (ie_regs E))
                  (prh_s0 F_parse_string (ie_q E)) ch')) /\
  (exists ch, achain (ie_ly E) (aview SEGS (w_H (ie_W E)) (ie_mem E)) (spZ (ie_regs E) - pi_frame F_parse_items)
                (prh_s0 F_parse_items (ie_q E)) ch) /\
  (* and the contexts the loop's OWN calls run at, over ie_ch2 *)
  (forall k, In k A_IRET_SLOTS -> In (A_IPC k :: spine (ie_ch2 E)) CTX) /\
  Z.of_nat (length (frames (ie_S E))) + Z.of_nat (PjGrammar.MAXD - ie_d E) <= fs_frames 0 /\
  (* ONE TRAILING SLOT for the kit's cut's new entry premises (PRH_FnParse.v f0d92dcec7e9 :403 and :425, verbatim): the
     cursor set (every cursor free trace at q is CW's, or its word is pj_parse's code word) and the depot's room for CW
     with no fresh slot; and the call's CW is the Props' (the journal's budget, vrd_ijrn). Its LAST component is the
     text's hull budget: room for the call's all-granted events (PresetHullBudget.hull_budget) *)
  (ie_CW E = CW /\
   prh_cw_entry B CW (ie_W E) (ie_mem E) (ie_regs E) (ie_q E) /\
   YCbqGwild.wild_room (as_universe B) CW 0 (st_depot (ie_S E)) /\
   PresetHullBudget.hull_budget (ie_S E)
     (PresetReqAt.rd_hevs (prhPi_gtrace (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E))))).

(* ---- the four step lemmas of the loop. THE RE-HIDING MOVE: each concludes SRr' SEGS RZ_cf (YA0nH: the step relation
   whose continuation worlds are at wle' SEGS RZ_cf). The key path, the element step and the capacity step call
   parse_string, parse_value and grow, whose texts conclude SRr'; the epilogue makes no call, and its premise and post
   carry the journal from the call's entry, which crosses those calls. ---- *)

(* 1. the key path, rows 108..209: `jal parse_string` for an object's key, the colon test, the key slot store *)
Definition tvrd_ikey_a (CTX CTX0 : list (list Z)) (CW : list (list Z)) : Prop :=
  forall E P, vrd_ient_ok CTX CTX0 CW E -> vrd_ielem_a E P ->
  SRr' SEGS YGcfRehidePost.RZ_cf (ip_W P) (vrd_cfg A_IELEM_SLOT P)
    (fun W2 c2 =>
       (exists P' nm, W2 = ip_W P' /\ c2 = vrd_cfg A_ISLOT_SLOT P' /\ vrd_islot_a E P' nm) \/
       (exists P' res, W2 = ip_W P' /\ c2 = vrd_cfg A_IEPI_SLOT P' /\ vrd_iexit_a E P' res)).

(* 2. the element step, rows 210..279: `jal __asan_memset` zeroing kids[n], `jal parse_value` at nesting d + 1
      (the depth is the word at q + 16, no register), the count update, the comma or the closer *)
Definition tvrd_ival_a (CTX CTX0 : list (list Z)) (CW : list (list Z)) : Prop :=
  forall E P nm, vrd_ient_ok CTX CTX0 CW E -> vrd_islot_a E P nm ->
  SRr' SEGS YGcfRehidePost.RZ_cf (ip_W P) (vrd_cfg A_ISLOT_SLOT P)
    (fun W2 c2 =>
       (exists P', W2 = ip_W P' /\ c2 = vrd_cfg A_ICOMMA_SLOT P' /\ vrd_icomma_a E P') \/
       (exists P' res, W2 = ip_W P' /\ c2 = vrd_cfg A_IEPI_SLOT P' /\ vrd_iexit_a E P' res)).

(* 3. the capacity step, rows 280..283: `jal grow` and the branch back to the loop head *)
Definition tvrd_igrow_a (CTX CTX0 : list (list Z)) (CW : list (list Z)) : Prop :=
  forall E P, vrd_ient_ok CTX CTX0 CW E -> vrd_icomma_a E P ->
  SRr' SEGS YGcfRehidePost.RZ_cf (ip_W P) (vrd_cfg A_ICOMMA_SLOT P)
    (fun W2 c2 =>
       (exists P', W2 = ip_W P' /\ c2 = vrd_cfg A_IELEM_SLOT P' /\ vrd_ielem_a E P') \/
       (exists P' res, W2 = ip_W P' /\ c2 = vrd_cfg A_IEPI_SLOT P' /\ vrd_iexit_a E P' res)).

(* THE BODY OF tparse_items_specX's POST as ONE named predicate: the epilogue's conclusion below and the segment
   master's returning arms (VrdIPro.v's vrd_ipost) both state it, so the two cannot drift apart. It IS the text's own
   named post body PRH_FnParse.tpiP_Q (tpiP_Q_check: the text concludes fpostWFbm .. at tpiP_Q), under this file's
   argument order. The memory keep of fpostWFbm (fQmn) is the generic invariant's, assembled once at the function's
   top, so the step lemmas state fpostWFb (at the text's budget wbudget CW 0) at this body. *)
Definition vrd_items_q (d : nat) (o : bool) (q v text len p : Z) (tb : list Z) (ly : alayout) (S : astate)
  (Lam : list (Z * Z)) (peak cnt fail ran most own : Z)
  : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  tpiP_Q (L := A_prog_listing) (PA := PAI) B d ly S q text len p tb v o Lam peak cnt fail ran most own.

(* 4. the epilogue, rows 310..325: a0 := s2, the twelve register restores, `addi sp, sp, 0x90`, `ret`.
      The conclusion is the caller-window post of tparse_items_specX itself, at the text's budget wbudget CW 0. *)
Definition tvrd_iexit_a (CTX CTX0 : list (list Z)) (CW : list (list Z)) : Prop :=
  forall E P res, vrd_ient_ok CTX CTX0 CW E -> vrd_iexit_a E P res ->
  SRr' SEGS YGcfRehidePost.RZ_cf (ip_W P) (vrd_cfg A_IEPI_SLOT P)
    (fpostWFb B ARx SK (YCbqGwild.wbudget CW 0) (STK_parse_items (ie_d E)) (ie_e E) (rd_fp (ie_q E) (ie_v E))
      (ie_regs E) (ie_ly E) (ie_S E) (ie_Hp E) (ie_W E) (ie_mem E) (ie_md E)
      (vrd_items_q (ie_d E) (ie_o E) (ie_q E) (ie_v E) (ie_text E) (ie_len E) (ie_p E) (ie_tb E) (ie_ly E) (ie_S E)
         (ie_Lam E) (ie_peak E) (ie_cnt E) (ie_fail E) (ie_ran E) (ie_most E) (ie_own E))).

(* ---- THE FOUR STEP PROPS IN THE GENERIC FORM, WITH PROGRESS (a Theorem Labs lane's ruling on A2Ipro's review, 2026-10-29;
   the generic-invariant rule of a Theorem Labs lane, 12:19Z). REASON: an SRr post is opaque once Qed, so an end-state memory
   invariant must be in the step's statement; the generic SRr_memnorm was measured not provable (a Theorem Labs lane), so it
   cannot be added afterwards. Without it parse_value's memnorm entry premise at row 231 has no source: memnorm of the
   entry memory (vrd_ient_ok) says nothing of the memory at the call (the Ival walk's counterexample, VrdIVal.v:32-40 on
   a working branch c913e10deeb, with its overlay byte added after the entry), and fpostWFm's keep cannot
   cross the loop. Each Prop takes Pm of the start memory and gives Pm of the reached one; a prover proves its Prop
   for every Pm with the laws its _G form below names: srr_inv_laws SEGS Pm (all four), srr_inv_call SEGS Pm (ikey,
   ival, igrow: they cross calls) and srr_inv_mn SEGS Pm (ival: parse_value's entry premise). The top instantiates Pm
   ONCE as `fun m => memnorm SEGS (ie_mem E) -> memnorm SEGS m`, with vrd_ient_ok's memnorm conjunct.
   PROGRESS: the element count of the reached position, so the loop assembly has the decreasing measure
   2 ^ 54 - ip_n (vrd_ielem_a gives ip_n < ip_cap and vrd_inode ip_cap <= 2 ^ 54 at the loop head): the key path and
   the capacity step keep it, the element step adds the one element it stored.
   Each old Prop is the corollary at Pm := fun _ => True (tvrd_*_of_P below). For ival that corollary is sound but
   has no source: srr_inv_mn at Pm := fun _ => True would say every memory is normal, so no prover can give
   tvrd_ival_aP (fun _ => True), and the old tvrd_ival_a is unprovable as stated (the counterexample above). ---- *)
Definition tvrd_ikey_aP (Pm : (word -> option byte) -> Prop) (CTX CTX0 : list (list Z)) (CW : list (list Z))
  : Prop :=
  forall E P, vrd_ient_ok CTX CTX0 CW E -> vrd_ielem_a E P -> Pm (ip_mem P) ->
  SRr' SEGS YGcfRehidePost.RZ_cf (ip_W P) (vrd_cfg A_IELEM_SLOT P)
    (fun W2 c2 =>
       ((exists P' nm, W2 = ip_W P' /\ c2 = vrd_cfg A_ISLOT_SLOT P' /\ vrd_islot_a E P' nm /\ ip_n P' = ip_n P) \/
        (exists P' res, W2 = ip_W P' /\ c2 = vrd_cfg A_IEPI_SLOT P' /\ vrd_iexit_a E P' res)) /\
       Pm (ms_mem (cfg_ms c2))).

(* THE NESTING PREMISE (a Theorem Labs lane's approval, 2026-10-30, on A2Step2's reviewer IvalGReview): the element step calls
   parse_value at depth S (ie_d E), and the top closes parse_items at d by DESCENDING induction on d, so it has
   parse_value only at S d .. MAXD. The step therefore takes parse_value's text at exactly that depth, for every float
   state, as a premise; it is not a Section hypothesis of its prover. *)
Definition tvrd_ival_aP (Pm : (word -> option byte) -> Prop) (CTX CTX0 : list (list Z)) (CW : list (list Z))
  : Prop :=
  forall E P nm,
  (forall fx' : YK11.FPState,
     @tparse_value_specX fx' rc ci cp PI RL A_prog_listing PI_prog_A B ARx SK (S (ie_d E)) CTX CTX0 CW) ->
  vrd_ient_ok CTX CTX0 CW E -> vrd_islot_a E P nm -> Pm (ip_mem P) ->
  SRr' SEGS YGcfRehidePost.RZ_cf (ip_W P) (vrd_cfg A_ISLOT_SLOT P)
    (fun W2 c2 =>
       ((exists P', W2 = ip_W P' /\ c2 = vrd_cfg A_ICOMMA_SLOT P' /\ vrd_icomma_a E P' /\ ip_n P' = ip_n P + 1) \/
        (exists P' res, W2 = ip_W P' /\ c2 = vrd_cfg A_IEPI_SLOT P' /\ vrd_iexit_a E P' res)) /\
       Pm (ms_mem (cfg_ms c2))).

Definition tvrd_igrow_aP (Pm : (word -> option byte) -> Prop) (CTX CTX0 : list (list Z)) (CW : list (list Z))
  : Prop :=
  forall E P, vrd_ient_ok CTX CTX0 CW E -> vrd_icomma_a E P -> Pm (ip_mem P) ->
  SRr' SEGS YGcfRehidePost.RZ_cf (ip_W P) (vrd_cfg A_ICOMMA_SLOT P)
    (fun W2 c2 =>
       ((exists P', W2 = ip_W P' /\ c2 = vrd_cfg A_IELEM_SLOT P' /\ vrd_ielem_a E P' /\ ip_n P' = ip_n P) \/
        (exists P' res, W2 = ip_W P' /\ c2 = vrd_cfg A_IEPI_SLOT P' /\ vrd_iexit_a E P' res)) /\
       Pm (ms_mem (cfg_ms c2))).

Definition tvrd_iexit_aP (Pm : (word -> option byte) -> Prop) (CTX CTX0 : list (list Z)) (CW : list (list Z))
  : Prop :=
  forall E P res, vrd_ient_ok CTX CTX0 CW E -> vrd_iexit_a E P res -> Pm (ip_mem P) ->
  SRr' SEGS YGcfRehidePost.RZ_cf (ip_W P) (vrd_cfg A_IEPI_SLOT P)
    (fun W2 c2 =>
       fpostWFb B ARx SK (YCbqGwild.wbudget CW 0) (STK_parse_items (ie_d E)) (ie_e E) (rd_fp (ie_q E) (ie_v E))
         (ie_regs E) (ie_ly E) (ie_S E) (ie_Hp E) (ie_W E) (ie_mem E) (ie_md E)
         (vrd_items_q (ie_d E) (ie_o E) (ie_q E) (ie_v E) (ie_text E) (ie_len E) (ie_p E) (ie_tb E) (ie_ly E) (ie_S E)
            (ie_Lam E) (ie_peak E) (ie_cnt E) (ie_fail E) (ie_ran E) (ie_most E) (ie_own E)) W2 c2 /\
       Pm (ms_mem (cfg_ms c2))).

(* the old Props, each the corollary of its generic form at Pm := fun _ => True *)
Lemma tvrd_ikey_a_of_P : forall CTX CTX0 CW, tvrd_ikey_aP (fun _ => True) CTX CTX0 CW -> tvrd_ikey_a CTX CTX0 CW.
Proof.
  intros CTX CTX0 CW H E P HE HP.
  eapply (SRrG_mono SEGS (wle' SEGS YGcfRehidePost.RZ_cf)); [exact (H E P HE HP I)|].
  intros W2 c2 _ ([(P' & nm & HW & Hc & HS & _) | HX] & _); [left; exists P', nm; tauto | right; exact HX].
Qed.

(* the old ival Prop has no nesting premise, so its corollary needs parse_value at every depth *)
Lemma tvrd_ival_a_of_P : forall CTX CTX0 CW,
  (forall (d : nat) (fx' : YK11.FPState),
     @tparse_value_specX fx' rc ci cp PI RL A_prog_listing PI_prog_A B ARx SK (S d) CTX CTX0 CW) ->
  tvrd_ival_aP (fun _ => True) CTX CTX0 CW -> tvrd_ival_a CTX CTX0 CW.
Proof.
  intros CTX CTX0 CW HPV H E P nm HE HP.
  eapply (SRrG_mono SEGS (wle' SEGS YGcfRehidePost.RZ_cf)); [exact (H E P nm (HPV (ie_d E)) HE HP I)|].
  intros W2 c2 _ ([(P' & HW & Hc & HS & _) | HX] & _); [left; exists P'; tauto | right; exact HX].
Qed.

Lemma tvrd_igrow_a_of_P : forall CTX CTX0 CW, tvrd_igrow_aP (fun _ => True) CTX CTX0 CW -> tvrd_igrow_a CTX CTX0 CW.
Proof.
  intros CTX CTX0 CW H E P HE HP.
  eapply (SRrG_mono SEGS (wle' SEGS YGcfRehidePost.RZ_cf)); [exact (H E P HE HP I)|].
  intros W2 c2 _ ([(P' & HW & Hc & HS & _) | HX] & _); [left; exists P'; tauto | right; exact HX].
Qed.

Lemma tvrd_iexit_a_of_P : forall CTX CTX0 CW, tvrd_iexit_aP (fun _ => True) CTX CTX0 CW -> tvrd_iexit_a CTX CTX0 CW.
Proof.
  intros CTX CTX0 CW H E P res HE HP.
  eapply (SRrG_mono SEGS (wle' SEGS YGcfRehidePost.RZ_cf)); [exact (H E P res HE HP I)|].
  intros W2 c2 _ (HQ & _). exact HQ.
Qed.

(* the SHAPE each step's prover exports (the consumer review's G1): its generic Prop for every memory invariant with
   exactly the laws it needs, in this premise order, so the four closed theorems compose at the top without
   reordering. A Section hypothesis is abstracted only where a proof uses it, so the shape is fixed here, not left to
   each prover's Section. *)
Definition tvrd_ikey_aG (CTX CTX0 : list (list Z)) (CW : list (list Z)) : Prop :=
  forall Pm, srr_inv_laws SEGS Pm -> YSRrMemnorm.srr_inv_call SEGS Pm -> tvrd_ikey_aP Pm CTX CTX0 CW.
Definition tvrd_ival_aG (CTX CTX0 : list (list Z)) (CW : list (list Z)) : Prop :=
  forall Pm, srr_inv_laws SEGS Pm -> YSRrMemnorm.srr_inv_call SEGS Pm -> YSRrMemnorm.srr_inv_mn SEGS Pm ->
  tvrd_ival_aP Pm CTX CTX0 CW.
Definition tvrd_igrow_aG (CTX CTX0 : list (list Z)) (CW : list (list Z)) : Prop :=
  forall Pm, srr_inv_laws SEGS Pm -> YSRrMemnorm.srr_inv_call SEGS Pm -> tvrd_igrow_aP Pm CTX CTX0 CW.
Definition tvrd_iexit_aG (CTX CTX0 : list (list Z)) (CW : list (list Z)) : Prop :=
  forall Pm, srr_inv_laws SEGS Pm -> tvrd_iexit_aP Pm CTX CTX0 CW.

(* ---- THE LOOP'S CALL CHAIN ACROSS A WRITE OF THE READER'S CELLS (a Theorem Labs lane's request, 2026-10-29: the S3 walk's key
   path stores q->p, the Ival walk stores the node, the grow step's callee writes the node; YCbq.v's achain_kept needs
   agreement on EVERY address at or above sp, so it does not apply). On image A parse_items keeps s0 = q, so the chain
   from q reads the word at q - 16 first; that word is below alloc_ceiling (prh_cur_entry at the entry, kept to the
   position by the frame and the caller window), so the chain stops after one record and reads only [q - 16, q),
   which no cell of rd_fp q v covers (the node is below alloc_ceiling: vrd_node_low). ---- *)

(* a value stored as 8 bytes reads back as that word (cgif YCem.v:101-115 rdword_of_val_mem, restated over this
   file's imports) *)
Lemma vrd_rdword_of_val_mem : forall (H : word -> bool) mem a v,
  val_mem SEGS (mrestrict H mem) a 8 v -> 0 <= v < 2 ^ 64 -> rdword (aview SEGS H mem) a = Some v.
Proof.
  intros H mem a v Hv Hr.
  assert (Bk : forall k, (k < 8)%nat -> aview SEGS H mem (a + Z.of_nat k) = Some (le_byte v 8 k)).
  { intros k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
    rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold le_byte. apply Z.mod_mod. lia. }
  unfold rdword.
  rewrite <- (Z.add_0_r a) at 1. change 0 with (Z.of_nat 0) at 1. rewrite (Bk 0%nat) by lia.
  change 1 with (Z.of_nat 1). rewrite (Bk 1%nat) by lia. change 2 with (Z.of_nat 2) at 1. rewrite (Bk 2%nat) by lia.
  change 3 with (Z.of_nat 3). rewrite (Bk 3%nat) by lia. change 4 with (Z.of_nat 4). rewrite (Bk 4%nat) by lia.
  change 5 with (Z.of_nat 5). rewrite (Bk 5%nat) by lia. change 6 with (Z.of_nat 6). rewrite (Bk 6%nat) by lia.
  change 7 with (Z.of_nat 7). rewrite (Bk 7%nat) by lia.
  f_equal. apply le_bytes8. exact Hr.
Qed.

(* the node lies below alloc_ceiling: rd_pre's prhReader_at at the entry, its real-stack window excluded
   (PRH_FnParse.v blob 26fdeac063ff), puts it in an allocator block (a harness block's user bytes included) or a fake
   frame of the entry state *)
Lemma vrd_node_low : forall HL (LAWS : AR_laws_x SEGS B ARx HL) CTX CTX0 CW E,
  vrd_ient_ok CTX CTX0 CW E -> ie_v E + 56 <= alloc_ceiling.
Proof.
  intros HL LAWS CTX CTX0 CW E HEN.
  destruct HEN as ((HAFN & _) & _ & _ & _ & HRD & _).
  pose proof HAFN as (HAR & _).
  pose proof HRD as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hnode & _ & _ & Hvwin & HLED0 & _).
  pose proof Hnode as (_ & _ & _ & _ & Hvat & _).
  pose proof cf_head_nonneg as Hcf0.
  destruct Hvat as [(a0 & k0 & Hin & Hle & Hhi) | [(b0 & m0 & Hin & _ & Hle & Hhi) | [(cid & pos & Hin & Hle & Hhi) | Hww]]].
  - destruct HLED0 as (_ & _ & HFL & _).
    destruct (proj1 (Forall_forall _ _) HFL (a0, k0) Hin) as (Hk0 & Hab0 & _). cbn [fst snd] in Hab0.
    destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR Hab0) as (_ & _ & Hc0 & _).
    unfold req_size in Hc0. destruct (Z.eqb_spec (k0 + cf_head) 0); lia.
  - destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR Hin) as (_ & _ & Hc0 & _).
    unfold req_size in Hc0. destruct (Z.eqb_spec m0 0); lia.
  - destruct (frames_bounds_x SEGS B ARx LAWS _ _ _ _ _ _ cid pos HAR Hin) as (_ & Hc0 & _). lia.
  - lia.
Qed.

(* the chain grow's text asks at parse_items' call (kit walkkit a3bdeca3920, PRH_FnReader.v blob 4e74cfa4213d:
   grow keeps s0 = v + pi_s0cur F_grow, 48 on both pins): its START v + 48 is below alloc_ceiling (vrd_node_low), so
   achain's cut disjunct holds with the empty chain, at any layout, view and sp *)
Lemma vrd_node_chain : forall HL (LAWS : AR_laws_x SEGS B ARx HL) CTX CTX0 CW E (ly : alayout) (rd : reader) (sp : Z),
  pi_s0cur F_grow = Some 48 -> vrd_ient_ok CTX CTX0 CW E ->
  exists ch, achain ly rd sp (prh_s0 F_grow (ie_v E)) ch.
Proof.
  intros HL LAWS CTX CTX0 CW E ly rd sp Hs0 HEN. exists [].
  apply achain_low. unfold prh_s0. rewrite Hs0.
  pose proof (vrd_node_low HL LAWS CTX CTX0 CW E HEN). lia.
Qed.

(* the general form: any later world, memory and layout (same stack top) that agree with the position on every
   address at or above the loop's sp outside rd_fp q v - after a call (the callee's world W2, its heap blocks and its
   windows below sp changed) as after a store into the reader's cells (a Theorem Labs lane's request, the Ival walk's measurement) *)
Lemma vrd_chain_keep_w : forall HL (LAWS : AR_laws_x SEGS B ARx HL) CTX CTX0 CW E P (W' : world SEGS)
    (m' : word -> option byte) (ly' : alayout),
  pi_frame F_parse_items = 144 -> pi_s0cur F_parse_items = Some 0 ->
  vrd_ient_ok CTX CTX0 CW E -> vrd_iframe E P -> vrd_ijrn E P -> ly_top ly' = ly_top (ip_ly P) ->
  (forall a, spZ (ie_regs E) - 144 <= a < 2 ^ 64 -> ~ inFP (rd_fp (ie_q E) (ie_v E)) a ->
     aview SEGS (w_H W') m' a = aview SEGS (w_H (ip_W P)) (ip_mem P) a) ->
  exists ch', achain ly' (aview SEGS (w_H W') m') (spZ (ie_regs E) - 144) (ie_q E) ch' /\
    spine ch' = spine (ie_ch2 E).
Proof.
  intros HL LAWS CTX CTX0 CW E P W' m' ly' Himg Hs0c HEN HFR HJN Hly HM.
  pose proof (vrd_node_low HL LAWS CTX CTX0 CW E HEN) as Hvceil.
  destruct HEN as ((HAFN & _) & _ & _ & _ & HRD & _ & _ & _ & _ & _ & _ & HCUR & _).
  pose proof HAFN as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & _ & Htop & Htop2).
  assert (HSTK : 144 <= STK_parse_items (ie_d E)).
  { unfold STK_parse_items. rewrite Himg. pose proof (pi_frame_nonneg F_parse_value).
    assert (0 <= LEAF_pv_pi) by (unfold LEAF_pv_pi, zmaxl; cbn [fold_right]; lia).
    assert (0 <= Z.of_nat (PjGrammar.MAXD - ie_d E) * (pi_frame F_parse_value + 144))
      by (apply Z.mul_nonneg_nonneg; lia).
    lia. }
  pose proof HRD as (_ & _ & _ & _ & Hinok & Hfwin & Hqlo & Hqhi & _).
  pose proof Hfwin as (_ & _ & Hetop & _).
  pose proof Hinok as (_ & _ & _ & _ & Hq8 & _).
  destruct HJN as (_ & HWIN & _ & _ & _ & _ & (ch' & Hch & Hsp)).
  exists ch'. split; [|exact Hsp]. apply (achain_ly_top (ip_ly P)); [exact Hly|].
  (* the two words the chain reads are outside rd_fp q v *)
  assert (Hagr : forall a, ie_q E - 16 <= a < ie_q E ->
     aview SEGS (w_H W') m' a = aview SEGS (w_H (ip_W P)) (ip_mem P) a).
  { intros a Ha. apply HM; [lia|]. intros (r & Hin & Hr). cbn [rd_fp In] in Hin.
    destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr; lia. }
  (* the word at q - 16 is below alloc_ceiling *)
  assert (Hlow : forall w, rdword (aview SEGS (w_H (ip_W P)) (ip_mem P)) (ie_q E - 16) = Some w -> w < alloc_ceiling).
  { intros w Hw.
    pose proof (proj2 HCUR F_parse_items (or_intror eq_refl)) as Hlo.
    unfold prh_s0 in Hlo. rewrite Hs0c, Z.add_0_r in Hlo.
    apply Hlo. unfold prh_word_entry.
    pose proof HFR as (_ & H8 & H16 & _).
    destruct (Z.eq_dec (ie_q E) (spZ (ie_regs E))) as [Eq0 | Nq0];
      [| destruct (Z.eq_dec (ie_q E) (spZ (ie_regs E) + 8)) as [Eq8 | Nq8]].
    - rewrite (proj2 (Z.eqb_neq (ie_q E - 16) (spZ (ie_regs E) - 8)) ltac:(lia)).
      rewrite (proj2 (Z.eqb_eq (ie_q E - 16) (spZ (ie_regs E) - 16)) ltac:(lia)).
      assert (Hr : rdword (aview SEGS (w_H (ip_W P)) (ip_mem P)) (spZ (ie_regs E) - 16) =
                   Some (bv_unsigned (getr (ie_regs E) 8))).
      { apply vrd_rdword_of_val_mem; [exact H16|].
        pose proof (bv_unsigned_in_range 64 (getr (ie_regs E) 8)) as Hb. change (bv_modulus 64) with (2 ^ 64) in Hb.
        exact Hb. }
      replace (ie_q E - 16) with (spZ (ie_regs E) - 16) in Hw by lia. rewrite Hr in Hw.
      injection Hw as <-. reflexivity.
    - rewrite (proj2 (Z.eqb_eq (ie_q E - 16) (spZ (ie_regs E) - 8)) ltac:(lia)).
      assert (Hr : rdword (aview SEGS (w_H (ip_W P)) (ip_mem P)) (spZ (ie_regs E) - 8) = Some (raZ (ie_regs E))).
      { apply vrd_rdword_of_val_mem; [exact H8|].
        pose proof (bv_unsigned_in_range 64 (getr (ie_regs E) 1)) as Hb. change (bv_modulus 64) with (2 ^ 64) in Hb.
        exact Hb. }
      replace (ie_q E - 16) with (spZ (ie_regs E) - 8) in Hw by lia. rewrite Hr in Hw.
      injection Hw as <-. reflexivity.
    - rewrite (proj2 (Z.eqb_neq (ie_q E - 16) (spZ (ie_regs E) - 8)) ltac:(lia)).
      rewrite (proj2 (Z.eqb_neq (ie_q E - 16) (spZ (ie_regs E) - 16)) ltac:(lia)).
      rewrite (rdword_ext (aview SEGS (w_H (ip_W P)) (ip_mem P)) _ (ie_q E - 16)); [exact Hw|].
      intros k Hk. symmetry. apply HWIN; [lia|]. intros (r & Hin & Hr). cbn [rd_fp In] in Hin.
      destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr; lia. }
  destruct Hch as [Hc1 | (Hc1 & Hc2 & Hc3 & Hc4 & Hc5)]; [left; exact Hc1|].
  right. split; [exact Hc1|]. split; [exact Hc2|]. split; [exact Hc3|]. split; [|exact Hc5].
  destruct ch' as [|[[fp ra] nfp] rest].
  - cbn [fpchain] in Hc4 |- *. destruct Hc4 as (r & Hr & Hr4). exists r. split; [|exact Hr4].
    rewrite (rdword_ext (aview SEGS (w_H (ip_W P)) (ip_mem P)) (aview SEGS (w_H W') m') (ie_q E - 8));
      [exact Hr | intros k Hk; apply Hagr; lia].
  - cbn [fpchain] in Hc4 |- *. destruct Hc4 as (-> & Hfp8 & Hra & Hnfp & Hra4 & Hrest).
    pose proof (Hlow nfp Hnfp) as Hnl.
    assert (Hbad : bad_next (ie_q E) (ly_top (ip_ly P)) nfp = true).
    { unfold bad_next. apply orb_true_iff. left. apply orb_true_iff. left. apply Z.leb_le. lia. }
    rewrite Hbad in Hrest |- *.
    split; [reflexivity|]. split; [exact Hfp8|].
    split; [rewrite (rdword_ext (aview SEGS (w_H (ip_W P)) (ip_mem P)) (aview SEGS (w_H W') m') (ie_q E - 8));
            [exact Hra | intros k Hk; apply Hagr; lia]|].
    split; [rewrite (rdword_ext (aview SEGS (w_H (ip_W P)) (ip_mem P)) (aview SEGS (w_H W') m') (ie_q E - 16));
            [exact Hnfp | intros k Hk; apply Hagr; lia]|].
    split; [exact Hra4 | exact Hrest].
Qed.

(* the same world and layout, agreement everywhere outside rd_fp q v (the form the S3 walk cites) *)
Lemma vrd_chain_keep : forall HL (LAWS : AR_laws_x SEGS B ARx HL) CTX CTX0 CW E P (m' : word -> option byte),
  pi_frame F_parse_items = 144 -> pi_s0cur F_parse_items = Some 0 ->
  vrd_ient_ok CTX CTX0 CW E -> vrd_iframe E P -> vrd_ijrn E P ->
  (forall a, ~ inFP (rd_fp (ie_q E) (ie_v E)) a ->
     aview SEGS (w_H (ip_W P)) m' a = aview SEGS (w_H (ip_W P)) (ip_mem P) a) ->
  exists ch', achain (ip_ly P) (aview SEGS (w_H (ip_W P)) m') (spZ (ie_regs E) - 144) (ie_q E) ch' /\
    spine ch' = spine (ie_ch2 E).
Proof.
  intros HL LAWS CTX CTX0 CW E P m' Himg Hs0c HEN HFR HJN HM.
  exact (vrd_chain_keep_w HL LAWS CTX CTX0 CW E P (ip_W P) m' (ip_ly P) Himg Hs0c HEN HFR HJN eq_refl
           (fun a _ Hn => HM a Hn)).
Qed.

(* ---- THE POST-IMPLICATION CONJUNCTS AT A POSITION: their witnesses and their composition. The position transfer
   and the live requests hold at the empty trace (vrd_xfer_nil, vrd_live_nil); the OUTCOME holds on any exit whose ok
   list is the granted prefix (vrd_outcome_granted). The FIRST loop head is not at the empty trace (ip_tr = the first
   grow's trace): its conjuncts come from grow's granted arm (4 or 7) through vrd_xfer_app / vrd_live_app, which is
   VrdIPro.v's vrd_ielem_entry. A callee whose post states its events with cf_head (grow's prhPg_evs, parse_string's
   prhPs_evs, fuzz_free's HFr) meets these rd_hevs (PresetReqAt.HEAD) forms only through the instance fact
   `cf_head = PresetReqAt.HEAD`, which each producer takes as the Section hypothesis HI_head (a Theorem Labs lane's spelling,
   discharged by reflexivity at CfParams_preset). ---- *)

(* the one strtod name of the texts and the helpers' name are the same function (same body: musl strtod's model
   over the text with its terminating zero) *)
Lemma vrd_strtod_same : ReaderRes.jr_strtod = prh_jr_strtod.
Proof. reflexivity. Qed.

(* the position transfer over no events: the position stays *)
Lemma vrd_xfer_nil : forall (S : astate) (sm : list Z -> Z * Z) (x : list Z)
    (os : list (option nat * option nat * option nat)) (i : nat) (H0 : list Z) (hist : list YG00.chunk),
  PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
  PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs []) ->
  exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (PresetReqAt.rd_hevs []))%nat H0 hist' S.
Proof.
  intros S sm x os i H0 hist HP _. exists hist.
  replace (i + length (PresetReqAt.rd_hevs []))%nat with i by (cbn; lia). exact HP.
Qed.

(* the live requests over no events *)
Lemma vrd_live_nil : forall (S : astate),
  Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
    (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) (PresetReqAt.rd_hevs [])).
Proof. intros S. unfold PresetReqAt.hlive_from, PresetReqAt.rd_hevs. cbn [flat_map fold_left]. apply Permutation_refl. Qed.

(* a callee's position transfer composes onto the position's: the events split by PRH_Base.prh_run_at_app_iff *)
Lemma vrd_xfer_app : forall (S1 S2 S3 : astate) (t1 t2 : list ev),
  (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
     (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm x os i H0 hist S1 ->
     PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs t1) ->
     exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (PresetReqAt.rd_hevs t1))%nat H0 hist' S2) ->
  (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
     (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm x os i H0 hist S2 ->
     PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs t2) ->
     exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (PresetReqAt.rd_hevs t2))%nat H0 hist' S3) ->
  forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
    (H0 : list Z) (hist : list YG00.chunk),
  PresetRoomPos.iface_room_pos sm x os i H0 hist S1 ->
  PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs (t1 ++ t2)) ->
  exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (PresetReqAt.rd_hevs (t1 ++ t2)))%nat H0 hist' S3.
Proof.
  intros S1 S2 S3 t1 t2 H1 H2 sm x os i H0 hist HP HR.
  assert (Ha : PresetReqAt.rd_hevs (t1 ++ t2) = PresetReqAt.rd_hevs t1 ++ PresetReqAt.rd_hevs t2)
    by (unfold PresetReqAt.rd_hevs; apply flat_map_app).
  rewrite Ha in HR |- *.
  apply PRH_Base.prh_run_at_app_iff in HR as [HR1 HR2].
  destruct (H1 sm x os i H0 hist HP HR1) as (h1 & Hh1).
  destruct (H2 sm x os _ H0 h1 Hh1 HR2) as (h2 & Hh2).
  exists h2. rewrite length_app, Nat.add_assoc. exact Hh2.
Qed.

(* a callee's live-request move composes onto the position's the same way: rd_hevs and hlive_from split over the
   append, and hlive_from respects a permuted start (PresetReqAtNoMiss.hlive_from_perm) *)
Lemma vrd_live_app : forall (S1 S2 S3 : astate) (t1 t2 : list ev),
  Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S2))
    (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf S1)) (PresetReqAt.rd_hevs t1)) ->
  Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S3))
    (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf S2)) (PresetReqAt.rd_hevs t2)) ->
  Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S3))
    (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf S1)) (PresetReqAt.rd_hevs (t1 ++ t2))).
Proof.
  intros S1 S2 S3 t1 t2 H1 H2.
  assert (Ha : PresetReqAt.rd_hevs (t1 ++ t2) = PresetReqAt.rd_hevs t1 ++ PresetReqAt.rd_hevs t2)
    by (unfold PresetReqAt.rd_hevs; apply flat_map_app).
  rewrite Ha, PresetReqAt.hlive_from_app.
  eapply Permutation_trans; [exact H2|].
  apply PresetReqAtNoMiss.hlive_from_perm. exact H1.
Qed.

Lemma vrd_nth_rep_true : forall n k, nth k (repeat true n) true = true.
Proof. induction n as [|n IH]; intros [|k]; cbn; auto. Qed.

(* THE OUTCOME ON THE GRANTED PREFIX: an exit whose ok list is the granted prefix of its own trace (every success
   exit of the loop) meets the post's OUTCOME clause with no further fact - by PjGrammar.agrees the all-granted run
   IS the run at that prefix (so the granted trace is ip_tr P and the transfer gives the advance), and prh_oks
   refuses nothing there, so g_ran_out is unchanged. *)
Lemma vrd_outcome_granted : forall E P r okr peak' cnt' fail',
  ip_ok P = repeat true (PjGrammar.calls (ip_tr P)) ->
  PjGrammar.jr_items prh_jr_strtod (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E)) (ip_ok P) =
    (r, ip_tr P, okr) ->
  rd_ledger_move (ie_Lam E) (ie_peak E) (ie_cnt E) (ie_fail E) (ie_ran E) (ie_most E) (ip_ok P)
    (prhPi_gtrace (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E))) (ip_tr P)
    (ip_D P) (ip_Lam P) peak' cnt' fail' (ip_ran P) ->
  (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
     (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm x os i H0 hist (ie_S E) ->
     PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs (ip_tr P)) ->
     exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (PresetReqAt.rd_hevs (ip_tr P)))%nat H0 hist'
       (ip_S P)) ->
  (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
     (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm x os i H0 hist (ie_S E) ->
     PRH_Base.prh_run_at sm x os i
       (PresetReqAt.rd_hevs (prhPi_gtrace (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E)))) ->
     PRH_Base.prh_cons_from sm x os i
       (length (PresetReqAt.rd_hevs (prhPi_gtrace (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E))))) ->
     (ie_fail E < ie_cnt E \/
      ie_cnt E + Z.of_nat (PjGrammar.calls (prhPi_gtrace (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E))))
        <= ie_fail E) ->
     ip_ran P = ie_ran E /\
     fst (PjGrammar.jr_items ReaderRes.jr_strtod (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E)) []) =
       fst (PjGrammar.jr_items ReaderRes.jr_strtod (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E))
              (ip_ok P)) /\
     exists hist', PresetRoomPos.iface_room_pos sm x os
       (i + length (PresetReqAt.rd_hevs (prhPi_gtrace (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E)))))%nat
       H0 hist' (ip_S P)).
Proof.
  intros E P r okr peak' cnt' fail' Hok Hans HLM HXF sm x os i H0 hist HP HR _ _.
  rewrite vrd_strtod_same.
  set (X := rest_atR (ie_tb E) (ie_text E) (ie_p E)) in *.
  pose proof (PjGrammar.agrees_jr_items prh_jr_strtod (ie_d E) (ie_o E) X (ip_ok P)) as (HA & _).
  assert (HE := HA (fun k _ => eq_trans (f_equal (fun l => nth k l true) Hok) (vrd_nth_rep_true _ k))).
  rewrite Hans in HE. injection HE as Hr Htr Hokr.
  assert (Hg : prhPi_gtrace (ie_d E) (ie_o E) X = ip_tr P) by (unfold prhPi_gtrace; rewrite Htr; reflexivity).
  rewrite Hg in HR |- *.
  split; [|split].
  - destruct HLM as ((_ & [Hran | (_ & k & _ & Hk & _)] & _) & _); [exact Hran|].
    unfold prh_refused in Hk. rewrite Hok, vrd_nth_rep_true in Hk. discriminate Hk.
  - rewrite Hans, Hr, Htr. destruct (PjGrammar.jr_items prh_jr_strtod (ie_d E) (ie_o E) X []) as [[a b] c].
    reflexivity.
  - exact (HXF sm x os i H0 hist HP HR).
Qed.

(* ---- THE BUDGET AT A POSITION (the kit's cut): the room a callee's text asks at its call state, from the entry room and
   the position's journal at the budget CW (YCbqGwild.ajournal_xw_roomR at wle', no fresh trace spent) ---- *)
Lemma vrd_wild_room_at : forall CTX CTX0 CW E P, vrd_ient_ok CTX CTX0 CW E -> vrd_ijrn E P ->
  YCbqGwild.wild_room (as_universe B) CW 0 (st_depot (ip_S P)).
Proof.
  intros CTX CTX0 CW E P HEN (HJ & _).
  destruct HEN as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (HCW & _ & HWR & _)).
  rewrite HCW in HJ.
  assert (H0 : (YCbqGwild.wfresh CW CW <= 0)%nat)
    by (rewrite (YCbqGwild.wfresh_incl CW CW (incl_refl CW)); lia).
  pose proof (YCbqGwild.ajournal_xw_roomR SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf)
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CW 0 HJ HWR H0) as HR.
  rewrite (YCbqGwild.wfresh_incl CW CW (incl_refl CW)) in HR. exact HR.
Qed.

(* ---- THE RUNNER STEPS AT A POSITION (the kit's cut; RItems' request): the engine's runners and call rules are stated at
   the empty budget, so a step runs from the position's journal rebased to its depot (YCbqGwild.ajournal_xw_rebaseR)
   and steps back to the budget ie_CW E after it (YCbqGwild.ajournal_xw_unbase0R, over the wild part of P's journal).
   THE RE-HIDING MOVE: both journals are at wle' SEGS RZ_cf, as vrd_ijrn's; the runners and call rules are taken at
   their R forms there (R := wle' SEGS RZ_cf, laws YA0nH.wle'_refl / wle'_trans). ---- *)
Lemma vrd_ijrn_base : forall E P, vrd_ijrn E P ->
  ajournal_xR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) (STK_parse_items (ie_d E) + ie_e E)
    (spZ (ie_regs E) + ie_e E)
    (rd_fp (ie_q E) (ie_v E)) (ie_ly E) (set_depot (st_depot (ip_S P)) (ie_S E)) (ie_Hp E) (ie_W E) (ie_mem E)
    (ie_md E) [] (ip_ly P) (ip_S P) (ip_Hp P) (ip_W P) (ip_mem P) (ip_md P) (ip_k P).
Proof.
  intros E P (HJ & _).
  exact (YCbqGwild.ajournal_xw_rebaseR SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf)
           _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ).
Qed.

Lemma vrd_ijrn_unbase : forall E P ly' S' Hp' W' mem' md' k', vrd_ijrn E P ->
  ajournal_xR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) (STK_parse_items (ie_d E) + ie_e E)
    (spZ (ie_regs E) + ie_e E)
    (rd_fp (ie_q E) (ie_v E)) (ie_ly E) (set_depot (st_depot (ip_S P)) (ie_S E)) (ie_Hp E) (ie_W E) (ie_mem E)
    (ie_md E) [] ly' S' Hp' W' mem' md' k' ->
  ajournal_xwR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) (STK_parse_items (ie_d E) + ie_e E)
    (spZ (ie_regs E) + ie_e E)
    (rd_fp (ie_q E) (ie_v E)) (ie_ly E) (ie_S E) (ie_Hp E) (ie_W E) (ie_mem E) (ie_md E) [] ly' S' Hp' W' mem' md' k'
    (ie_CW E).
Proof.
  intros E P ly' S' Hp' W' mem' md' k' (HJ & _) HJ'.
  exact (YCbqGwild.ajournal_xw_unbase0R SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf)
           _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ' (ajxR_wild HJ)).
Qed.

(* ---- THE HULL AT A CALL OF THE LOOP (the text's threaded hull budget, PresetHullBudget). A position carries the hull
   use from the entry over its events so far A (vrd_imodel's last conjunct) and the entry carries the budget over the
   call's all-granted events G (vrd_ient_ok). When G is A, then a callee's all-granted list Ec, then the rest Q, the
   callee's budget is PresetHullBudget.hull_budget_infix, and after the callee's use the call's use over G follows by
   PresetHullBudget.hull_used_app and hull_used_infix (vrd_huse_out), on every arm of the callee; after a granted
   callee the position's use over its events so far is hull_used_app itself. ---- *)
Lemma vrd_huse_out : forall (S0 S S' : astate) (A Ec Q : list PresetReqAt.hev),
  PresetHullBudget.hull_used S0 S A -> PresetHullBudget.hull_used S S' Ec ->
  PresetHullBudget.hull_used S0 S' (A ++ Ec ++ Q).
Proof.
  intros S0 S S' A Ec Q H1 H2. rewrite app_assoc.
  exact (PresetHullBudget.hull_used_infix S0 S' [] (A ++ Ec) Q (PresetHullBudget.hull_used_app S0 S S' A Ec H1 H2)).
Qed.


(* ---- THE OUTCOME OF AN INJECTED READING (the text's conjunct, vrd_iexit_a's last). A loop position is on the granted
   prefix, so the model's grant list okk j with the chosen failure at j (PresetReqAt.okk) begins with the position's own
   oks (rd_ledger_move's prh_oks keeps the chosen call out of the prefix): a run of the call's events under okk j
   passes the position's events and goes on with the continuation's events under okk (j - k0) (vrd_inj_at). A callee's
   events are a prefix of the continuation's (vrd_jbind_prefix, vrd_run_prefix). The instance's oks at an exit are
   the prefix's, then the callee's (vrd_granted_app). ---- *)
Lemma vrd_okk_split : forall k j, (k <= j)%nat -> PresetReqAt.okk j = repeat true k ++ PresetReqAt.okk (j - k).
Proof.
  induction k as [|k IH]; intros j Hj; [cbn [repeat app]; rewrite Nat.sub_0_r; reflexivity|].
  destruct j as [|j]; [lia|].
  change (PresetReqAt.okk (S j)) with (true :: PresetReqAt.okk j). cbn [repeat app Nat.sub]. f_equal.
  apply IH. lia.
Qed.

Lemma vrd_granted_rep : forall k c f n, PRH_Base.prh_granted (repeat true k) c f n.
Proof. intros k c f n i _ H. rewrite vrd_nth_rep_true in H. discriminate H. Qed.

Lemma vrd_granted_app : forall k ok2 c f k2,
  PRH_Base.prh_granted ok2 (c + Z.of_nat k) f k2 ->
  PRH_Base.prh_granted (repeat true k ++ ok2) c f (k + k2).
Proof.
  intros k ok2 c f k2 H i Hi Hn. destruct (Nat.lt_ge_cases i k) as [Hl | Hl].
  - rewrite app_nth1 in Hn by (rewrite repeat_length; exact Hl). rewrite vrd_nth_rep_true in Hn. discriminate Hn.
  - rewrite app_nth2 in Hn by (rewrite repeat_length; exact Hl). rewrite repeat_length in Hn.
    pose proof (H (i - k)%nat ltac:(lia) Hn) as E. lia.
Qed.

Lemma vrd_jbind_prefix : forall (A C : Type) (m : PjGrammar.M A) (k : A -> PjGrammar.M C) ok,
  exists t2, snd (fst (PjGrammar.jbind m k ok)) = snd (fst (m ok)) ++ t2.
Proof.
  intros A C m k ok. unfold PjGrammar.jbind. destruct (m ok) as [[[a|] t] ok1]; cbn [fst snd].
  - destruct (k a ok1) as [[r t'] ok2]. cbn [fst snd]. exists t'. reflexivity.
  - exists []. rewrite app_nil_r. reflexivity.
Qed.

Lemma vrd_run_prefix : forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
    (i : nat) (t1 t2 : list ev),
  PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs (t1 ++ t2)) ->
  PRH_Base.prh_cons_from sm x os i (length (PresetReqAt.rd_hevs (t1 ++ t2))) ->
  PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs t1) /\
  PRH_Base.prh_cons_from sm x os i (length (PresetReqAt.rd_hevs t1)).
Proof.
  intros sm x os i t1 t2 HR HC. rewrite PresetHullBudget.hull_rd_app in HR, HC. rewrite length_app in HC.
  apply PRH_Base.prh_run_at_app_iff in HR as [HR1 _]. apply PRH_Base.prh_cons_from_app_iff in HC as [HC1 _].
  exact (conj HR1 HC1).
Qed.

Lemma vrd_inj_at : forall E P (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
    (i : nat) (H0 : list Z) (hist : list YG00.chunk),
  vrd_imodel E P ->
  PresetRoomPos.iface_room_pos sm x os i H0 hist (ie_S E) ->
  PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs (snd (fst (PjGrammar.jr_items ReaderRes.jr_strtod (ie_d E)
    (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E)) (PresetReqAt.okk (Z.to_nat (ie_fail E - ie_cnt E))))))) ->
  PRH_Base.prh_cons_from sm x os i (length (PresetReqAt.rd_hevs (snd (fst (PjGrammar.jr_items ReaderRes.jr_strtod
    (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E)) (PresetReqAt.okk (Z.to_nat (ie_fail E - ie_cnt E)))))))) ->
  ie_cnt E <= ie_fail E ->
  (PjGrammar.calls (ip_tr P) <= Z.to_nat (ie_fail E - ie_cnt E))%nat /\
  exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (PresetReqAt.rd_hevs (ip_tr P)))%nat H0 hist' (ip_S P) /\
    PRH_Base.prh_run_at sm x os (i + length (PresetReqAt.rd_hevs (ip_tr P)))%nat
      (PresetReqAt.rd_hevs (snd (fst (ip_cont P
         (PresetReqAt.okk (Z.to_nat (ie_fail E - ie_cnt E) - PjGrammar.calls (ip_tr P))))))) /\
    PRH_Base.prh_cons_from sm x os (i + length (PresetReqAt.rd_hevs (ip_tr P)))%nat
      (length (PresetReqAt.rd_hevs (snd (fst (ip_cont P
         (PresetReqAt.okk (Z.to_nat (ie_fail E - ie_cnt E) - PjGrammar.calls (ip_tr P)))))))).
Proof.
  intros E P sm x os i H0 hist HM HP HR HC Hle.
  destruct HM as (Hok & Hfac & HLM & _ & _ & _ & _ & _ & HXF & _).
  set (k0 := PjGrammar.calls (ip_tr P)) in *.
  set (j := Z.to_nat (ie_fail E - ie_cnt E)) in *.
  assert (Hk : (k0 <= j)%nat).
  { destruct (Nat.le_gt_cases k0 j) as [H|H]; [exact H|]. exfalso.
    destruct HLM as ((Hoks & _) & _).
    pose proof (Hoks j H ltac:(unfold j; lia)) as Hn.
    rewrite Hok, vrd_nth_rep_true in Hn. discriminate Hn. }
  split; [exact Hk|].
  rewrite vrd_strtod_same in HR, HC.
  rewrite (vrd_okk_split k0 j Hk), <- Hok, (Hfac (PresetReqAt.okk (j - k0))) in HR, HC.
  cbn [fst snd] in HR, HC.
  rewrite PresetHullBudget.hull_rd_app in HR, HC. rewrite length_app in HC.
  apply PRH_Base.prh_run_at_app_iff in HR as [HR1 HR2].
  apply PRH_Base.prh_cons_from_app_iff in HC as [_ HC2].
  destruct (HXF sm x os i H0 hist HP HR1) as (hist' & Hh').
  exists hist'. split; [exact Hh'|]. split; [exact HR2 | exact HC2].
Qed.

(* an exit on the granted prefix itself: no refusal at all *)
Lemma vrd_inj_granted : forall E P, ip_ok P = repeat true (PjGrammar.calls (ip_tr P)) ->
  forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
    (H0 : list Z) (hist : list YG00.chunk),
  PresetRoomPos.iface_room_pos sm x os i H0 hist (ie_S E) ->
  PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs (snd (fst (PjGrammar.jr_items ReaderRes.jr_strtod (ie_d E)
    (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E)) (PresetReqAt.okk (Z.to_nat (ie_fail E - ie_cnt E))))))) ->
  PRH_Base.prh_cons_from sm x os i (length (PresetReqAt.rd_hevs (snd (fst (PjGrammar.jr_items ReaderRes.jr_strtod
    (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E)) (PresetReqAt.okk (Z.to_nat (ie_fail E - ie_cnt E)))))))) ->
  ie_cnt E <= ie_fail E <
    ie_cnt E + Z.of_nat (PjGrammar.calls (prhPi_gtrace (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E)))) ->
  PRH_Base.prh_granted (ip_ok P) (ie_cnt E) (ie_fail E) (PjGrammar.calls (ip_tr P)).
Proof. intros E P Hok sm x os i H0 hist _ _ _ _. rewrite Hok. apply vrd_granted_rep. Qed.

(* an exit after a callee: the exit's oks and trace are the position's, then the callee's okc and trc. The call's
   clause follows from the callee's at the position (the continuation's run under the model's list from there, the
   chosen failure at or after the position's counter), by vrd_inj_at and vrd_granted_app *)
Lemma vrd_inj_exit : forall E P (okc : list bool) (trc : list ev),
  vrd_imodel E P ->
  (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
     (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm x os i H0 hist (ip_S P) ->
     PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs (snd (fst (ip_cont P
       (PresetReqAt.okk (Z.to_nat (ie_fail E - ie_cnt E) - PjGrammar.calls (ip_tr P))))))) ->
     PRH_Base.prh_cons_from sm x os i (length (PresetReqAt.rd_hevs (snd (fst (ip_cont P
       (PresetReqAt.okk (Z.to_nat (ie_fail E - ie_cnt E) - PjGrammar.calls (ip_tr P)))))))) ->
     ie_cnt E + Z.of_nat (PjGrammar.calls (ip_tr P)) <= ie_fail E <
       ie_cnt E + Z.of_nat (PjGrammar.calls (prhPi_gtrace (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E)))) ->
     PRH_Base.prh_granted okc (ie_cnt E + Z.of_nat (PjGrammar.calls (ip_tr P))) (ie_fail E) (PjGrammar.calls trc)) ->
  forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
    (H0 : list Z) (hist : list YG00.chunk),
  PresetRoomPos.iface_room_pos sm x os i H0 hist (ie_S E) ->
  PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs (snd (fst (PjGrammar.jr_items ReaderRes.jr_strtod (ie_d E)
    (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E)) (PresetReqAt.okk (Z.to_nat (ie_fail E - ie_cnt E))))))) ->
  PRH_Base.prh_cons_from sm x os i (length (PresetReqAt.rd_hevs (snd (fst (PjGrammar.jr_items ReaderRes.jr_strtod
    (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E)) (PresetReqAt.okk (Z.to_nat (ie_fail E - ie_cnt E)))))))) ->
  ie_cnt E <= ie_fail E <
    ie_cnt E + Z.of_nat (PjGrammar.calls (prhPi_gtrace (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E)))) ->
  PRH_Base.prh_granted (ip_ok P ++ okc) (ie_cnt E) (ie_fail E) (PjGrammar.calls (ip_tr P ++ trc)).
Proof.
  intros E P okc trc HM HCe sm x os i H0 hist HP HR HC (Hle & Hlt).
  pose proof HM as (Hok & _).
  destruct (vrd_inj_at E P sm x os i H0 hist HM HP HR HC Hle) as (Hk & hist' & HP' & HR' & HC').
  rewrite Hok, PjGrammar.calls_app. apply vrd_granted_app.
  apply (HCe sm x os _ H0 hist' HP' HR' HC'). split; [lia | exact Hlt].
Qed.

(* the callee's part of vrd_inj_exit, for a callee m whose events begin the continuation's at the position, from the
   callee's two outcome clauses at its entry state ip_S P and counter cntc (no wrap): inside the callee's window its
   injected-reading clause; past it the callee's run under the model's list is its all-granted run (agrees), so its
   outcome clause makes the actual result the all-granted one, which grants every call of its trace
   (vrd_granted_of_same) *)
Lemma vrd_inj_callee : forall E P (A : Type) (m : PjGrammar.M A) (okc : list bool) (resc : option A) (trc : list ev)
    (okrc : list bool) (cntc : Z),
  PjGrammar.agrees m -> vrd_nofail m ->
  (forall okt, exists t2, snd (fst (ip_cont P okt)) = snd (fst (m okt)) ++ t2) ->
  m okc = (resc, trc, okrc) ->
  cntc = ie_cnt E + Z.of_nat (PjGrammar.calls (ip_tr P)) ->
  (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
     (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm x os i H0 hist (ip_S P) ->
     PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs (snd (fst (m (PresetReqAt.okk (Z.to_nat (ie_fail E - cntc))))))) ->
     PRH_Base.prh_cons_from sm x os i
       (length (PresetReqAt.rd_hevs (snd (fst (m (PresetReqAt.okk (Z.to_nat (ie_fail E - cntc)))))))) ->
     cntc <= ie_fail E < cntc + Z.of_nat (PjGrammar.calls (snd (fst (m [])))) ->
     PRH_Base.prh_granted okc cntc (ie_fail E) (PjGrammar.calls trc)) ->
  (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
     (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm x os i H0 hist (ip_S P) ->
     PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs (snd (fst (m [])))) ->
     PRH_Base.prh_cons_from sm x os i (length (PresetReqAt.rd_hevs (snd (fst (m []))))) ->
     (ie_fail E < cntc \/ cntc + Z.of_nat (PjGrammar.calls (snd (fst (m [])))) <= ie_fail E) ->
     fst (m []) = (resc, trc)) ->
  forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
    (H0 : list Z) (hist : list YG00.chunk),
  PresetRoomPos.iface_room_pos sm x os i H0 hist (ip_S P) ->
  PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs (snd (fst (ip_cont P
    (PresetReqAt.okk (Z.to_nat (ie_fail E - ie_cnt E) - PjGrammar.calls (ip_tr P))))))) ->
  PRH_Base.prh_cons_from sm x os i (length (PresetReqAt.rd_hevs (snd (fst (ip_cont P
    (PresetReqAt.okk (Z.to_nat (ie_fail E - ie_cnt E) - PjGrammar.calls (ip_tr P)))))))) ->
  ie_cnt E + Z.of_nat (PjGrammar.calls (ip_tr P)) <= ie_fail E <
    ie_cnt E + Z.of_nat (PjGrammar.calls (prhPi_gtrace (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E)))) ->
  PRH_Base.prh_granted okc (ie_cnt E + Z.of_nat (PjGrammar.calls (ip_tr P))) (ie_fail E) (PjGrammar.calls trc).
Proof.
  intros E P A m okc resc trc okrc cntc Hag Hnf Hpre Hm Ec HINJ HOUT sm x os i H0 hist HP HR HC (Hle & Hlt).
  set (j' := (Z.to_nat (ie_fail E - ie_cnt E) - PjGrammar.calls (ip_tr P))%nat) in *.
  assert (Ej : j' = Z.to_nat (ie_fail E - cntc)) by (unfold j'; subst cntc; lia).
  destruct (Hpre (PresetReqAt.okk j')) as (t2 & Et). rewrite Et in HR, HC.
  destruct (vrd_run_prefix sm x os i _ _ HR HC) as (HRm & HCm).
  rewrite <- Ec.
  destruct (Z_lt_le_dec (ie_fail E) (cntc + Z.of_nat (PjGrammar.calls (snd (fst (m [])))))) as [Hin | Hout].
  - rewrite Ej in HRm, HCm. apply (HINJ sm x os i H0 hist HP HRm HCm). lia.
  - assert (Hu : PjGrammar.ok_upto (PresetReqAt.okk j') (PjGrammar.calls (snd (fst (m []))))).
    { intros k Hk. unfold PresetReqAt.okk. rewrite app_nth1 by (rewrite repeat_length; lia).
      apply vrd_nth_rep_true. }
    pose proof (proj1 (Hag (PresetReqAt.okk j')) Hu) as Em. rewrite Em in HRm, HCm. cbn [fst snd] in HRm, HCm.
    pose proof (HOUT sm x os i H0 hist HP HRm HCm ltac:(right; exact Hout)) as Hf.
    exact (vrd_granted_of_same _ m okc resc trc okrc cntc (ie_fail E) Hag Hnf Hm Hf).
Qed.


End W.

Print Assumptions vrd_wild_room_at.
Print Assumptions vrd_ijrn_base.
Print Assumptions vrd_ijrn_unbase.
Print Assumptions vrd_budget_back.
Print Assumptions vrd_jfb_key.
