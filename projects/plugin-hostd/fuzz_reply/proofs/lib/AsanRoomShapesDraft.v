(** * OSSVerify.Core.AsanRoomShapes: the linux-placement agreement of
      an AddressSanitizer build whose own allocator may refuse a full size
      class

    [agrees_in_room_unless_at env lim_plain lim_san refusal plain san] is
    [agrees_in_room env lim_plain lim_san plain san]
    (OSSVerify.Core.RoomShapes) with each execution of the sanitizer
    build cut where it is about to execute the instruction at [refusal]
    ([at_refusal]: not halted, in no system call, program counter at
    [refusal]; the premises of AsanShapes'
    [must_exit_in_or_refuse_at_cfg_refused]).  A statement uses it with
    [refusal] the address, in the sanitizer build's image, of the first
    instruction of the path its AddressSanitizer runtime takes when a size
    class is full ([class_full_at], docs/facts.md), the same address that
    build's halts statement read budget-class-full names.  The budget
    premise, which reads only the plain build, does not exclude it.
    No step of the sanitizer build is taken from such a configuration
    ([cut_at]), so nothing it does after it is claimed: no error, and no
    output beyond the trace it had written there.  The plain build is stated
    as in [agrees_in_room], with no cut.

    For each claimed policy [p]:
    - the budget premise and the plain build's part are [agrees_in_room]'s,
      word for word;
    - no canonical execution of [p] of the sanitizer build, and no execution
      of it before an unplaced or budget-refused configuration, reaches an
      error before it is cut ([guarded_reaches_error_unless_at]);
    - every canonical trace of [p] of the sanitizer build, cut so, is one of
      the plain build;
    - every canonical trace of [p] of the plain build is one of the
      sanitizer build, cut so, or extends the trace with which a canonical
      execution of [p] of the sanitizer build comes to a cut
      ([canon_cut_at]).

    The exception is per execution, as for the halts shape: a canonical
    execution of the sanitizer build that is never cut is held to all of
    [agrees_in_room].

    Why.  Each size class of the runtime's allocator has a region of
    3.5 GiB, and its quarantine holds freed chunks back rather than reusing
    them at once; a program that allocates and frees chunks of one small
    size class over and over can fill that region in the ASan build, where
    the plain build's allocator reuses the same memory and goes on.
    Without the exception such a statement is false for a reason that is not
    the program's.

    Built from lps definitions and RoomShapes' only.  This file is separate
    from AsanShapes.v and RoomShapes.v because a statement's fingerprint
    hashes the code of each of them (docs/versioning.md): a definition added
    to either would change the fingerprint of every statement of its shapes.
    The fingerprint of a statement of this shape hashes this file and
    RoomShapes.v. *)

From Stdlib Require Import ZArith List Classical_Prop.
From stdpp.bitvector Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase MemImageType RiscvSemantics State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import RoomShapesDraft.
Import ListNotations.

(** A configuration about to execute the instruction at [refusal]: not
    halted, in no system call, with its program counter at [refusal]. *)
Definition at_refusal (refusal : Z) (c : config) : Prop :=
  m_halted (cfg_model c) = None
  /\ ms_svc_pending (cfg_ms c) = None
  /\ bv_unsigned (ms_pc (cfg_ms c)) = refusal.

(** Where an execution of the sanitizer build is cut. *)
Definition cut_at (refusal : Z) (segs : list Segment) (c : config) : Prop :=
  at_refusal refusal c.

(** RoomShapes' [star_canon_fb], except that no step is taken from a
    configuration where it is cut. *)
Inductive star_canon_fb_ua (refusal : Z) (p : policy) (segs : list Segment) (cfg : SpuriousCfg)
    : bool -> strip -> Z -> config -> list event -> config -> Prop :=
| scfu_refl : forall dev s st c, star_canon_fb_ua refusal p segs cfg dev s st c [] c
| scfu_canon : forall dev s s' st st' c1 evs c2 tr c3,
    ~ cut_at refusal segs c1 ->
    (dev = true -> ~ unplaced_at segs c1) ->
    sstep_cfg segs cfg c1 evs (SNext c2) ->
    canonical_step p s st segs c1 c2 ->
    strip_next p segs c1 c2 s s' ->
    stack_next segs c1 c2 st st' ->
    star_canon_fb_ua refusal p segs cfg dev s' st' c2 tr c3 ->
    star_canon_fb_ua refusal p segs cfg dev s st c1 (evs ++ tr) c3
| scfu_fallback : forall dev s s' st st' c1 evs c2 tr c3,
    ~ cut_at refusal segs c1 ->
    ~ canon_can_step p s st segs cfg c1 ->
    ~ unplaced_at segs c1 ->
    sstep_cfg segs cfg c1 evs (SNext c2) ->
    strip_next p segs c1 c2 s s' ->
    stack_next segs c1 c2 st st' ->
    star_canon_fb_ua refusal p segs cfg true s' st' c2 tr c3 ->
    star_canon_fb_ua refusal p segs cfg dev s st c1 (evs ++ tr) c3.

(** RoomShapes' [canon_run], cut. *)
Definition canon_run_ua (refusal : Z) (p : policy) (segs : list Segment) (cfg : SpuriousCfg) (c : config)
    (tr : list event) (c' : config) : Prop :=
  star_canon_fb_ua refusal p segs cfg false full_strip (stack_low (m_vmmaps (cfg_model c)) p) c tr c'.

(** RoomShapes' [star_guarded], cut. *)
Inductive star_guarded_ua (refusal : Z) (segs : list Segment) (cfg : SpuriousCfg)
    : config -> list event -> config -> Prop :=
| sgu_refl : forall c, star_guarded_ua refusal segs cfg c [] c
| sgu_step : forall c1 evs c2 tr c3,
    ~ cut_at refusal segs c1 ->
    ~ unplaced_at segs c1 ->
    ~ budget_refused_at segs c1 ->
    sstep_cfg segs cfg c1 evs (SNext c2) ->
    star_guarded_ua refusal segs cfg c2 tr c3 ->
    star_guarded_ua refusal segs cfg c1 (evs ++ tr) c3.

(** ** What the statement reads of the sanitizer build, for one policy [p] *)

(** RoomShapes' [canon_trace], cut. *)
Definition canon_trace_unless_at (cfg : SpuriousCfg) (p : policy) (refusal : Z) (img : Image) (lim : Z)
    (en : ExecEntry) (inp : ProcInput) (tr : list event) : Prop :=
  match img, en with
  | mkImage segs pc ph, mkEntry sp brk0 mbase rnd =>
    exists tr' c, canon_run_ua refusal p segs cfg (init_config segs pc ph sp brk0 mbase rnd lim inp) tr' c
                  /\ is_prefix tr tr'
  end.

(** A canonical execution of [p] that comes to a cut, with trace [tr]. *)
Definition canon_cut_at (cfg : SpuriousCfg) (p : policy) (refusal : Z) (img : Image) (lim : Z)
    (en : ExecEntry) (inp : ProcInput) (tr : list event) : Prop :=
  match img, en with
  | mkImage segs pc ph, mkEntry sp brk0 mbase rnd =>
    exists c, canon_run_ua refusal p segs cfg (init_config segs pc ph sp brk0 mbase rnd lim inp) tr c
              /\ cut_at refusal segs c
  end.

(** RoomShapes' [guarded_reaches_error], cut: an error that a canonical
    execution of [p] reaches, or that any other execution reaches before an
    unplaced or budget-refused configuration, in neither case from a
    configuration where it is cut. *)
Definition guarded_reaches_error_unless_at (cfg : SpuriousCfg) (p : policy) (refusal : Z) (img : Image)
    (lim : Z) (en : ExecEntry) (inp : ProcInput) : Prop :=
  match img, en with
  | mkImage segs pc ph, mkEntry sp brk0 mbase rnd =>
    exists tr c evs,
      ((star_guarded_ua refusal segs cfg (init_config segs pc ph sp brk0 mbase rnd lim inp) tr c
        /\ ~ unplaced_at segs c /\ ~ budget_refused_at segs c)
       \/ canon_run_ua refusal p segs cfg (init_config segs pc ph sp brk0 mbase rnd lim inp) tr c)
      /\ ~ cut_at refusal segs c
      /\ sstep_cfg segs cfg c evs SError
  end.

(** ** The shape *)

(** [agrees_in_room_unless_at env lim_plain lim_san refusal plain san]: for
    every claimed placement policy [p], every valid input and every valid
    pair of entries on which no canonical execution of [p] of the plain
    build is refused memory for exceeding [lim_plain], when the environment
    refuses only what [env] allows:
    - no canonical execution of [p] of the plain build, and no execution of
      it before an unplaced or budget-refused configuration, reaches an
      error;
    - the same for the sanitizer build, each execution cut at [cut_at];
    - every canonical trace of [p] of the sanitizer build, cut so, is one
      of the plain build;
    - every canonical trace of [p] of the plain build is one of the
      sanitizer build, cut so, or extends the trace with which a canonical
      execution of [p] of the sanitizer build comes to a cut. *)
Definition agrees_in_room_unless_at (env : SpuriousCfg) (lim_plain lim_san : Z) (refusal : Z)
    (plain san : Image) : Prop :=
  forall (p : policy) (en_plain en_san : ExecEntry) (inp : ProcInput),
    policy_ok p ->
    valid_entry plain en_plain inp ->
    valid_entry san en_san inp ->
    valid_input inp ->
    ~ canon_budget_refused env p plain lim_plain en_plain inp ->
    ~ guarded_reaches_error env p plain lim_plain en_plain inp
    /\ ~ guarded_reaches_error_unless_at env p refusal san lim_san en_san inp
    /\ (forall tr, canon_trace_unless_at env p refusal san lim_san en_san inp tr ->
                   canon_trace env p plain lim_plain en_plain inp tr)
    /\ (forall tr, canon_trace env p plain lim_plain en_plain inp tr ->
                   canon_trace_unless_at env p refusal san lim_san en_san inp tr
                   \/ exists tr0, is_prefix tr0 tr /\ canon_cut_at env p refusal san lim_san en_san inp tr0).

(** ** From [agrees_in_room] *)

Lemma star_canon_fb_ua_canon_fb : forall refusal p segs cfg dev s st c tr c',
  star_canon_fb_ua refusal p segs cfg dev s st c tr c' -> star_canon_fb p segs cfg dev s st c tr c'.
Proof.
  intros refusal p segs cfg dev s st c tr c' H.
  induction H as [dev s st c | dev s s' st st' c1 evs c2 tr c3 _ Hd Hstep Hc Hs Hst _ IH
                  | dev s s' st st' c1 evs c2 tr c3 _ Hn Hu Hstep Hs Hst _ IH].
  - apply scf_refl.
  - eapply scf_canon; eassumption.
  - eapply scf_fallback; eassumption.
Qed.

Lemma star_guarded_ua_guarded : forall refusal segs cfg c tr c',
  star_guarded_ua refusal segs cfg c tr c' -> star_guarded segs cfg c tr c'.
Proof.
  intros refusal segs cfg c tr c' H.
  induction H as [c | c1 evs c2 tr c3 _ Hu Hb Hstep _ IH].
  - apply sg_refl.
  - eapply sg_step; eassumption.
Qed.

(** Every canonical execution is either never cut, or comes to a cut after a
    prefix of its trace. *)
Lemma star_canon_fb_ua_split : forall refusal p segs cfg dev s st c tr c',
  star_canon_fb p segs cfg dev s st c tr c' ->
  star_canon_fb_ua refusal p segs cfg dev s st c tr c'
  \/ exists tr0 tr1 c0, star_canon_fb_ua refusal p segs cfg dev s st c tr0 c0
                        /\ cut_at refusal segs c0 /\ tr = tr0 ++ tr1.
Proof.
  intros refusal p segs cfg dev s st c tr c' H.
  induction H as [dev s st c | dev s s' st st' c1 evs c2 tr c3 Hd Hstep Hc Hs Hst _ IH
                  | dev s s' st st' c1 evs c2 tr c3 Hn Hu Hstep Hs Hst _ IH].
  - left. apply scfu_refl.
  - destruct (classic (cut_at refusal segs c1)) as [Hcut | Hcut].
    + right. exists [], (evs ++ tr), c1. split; [apply scfu_refl | split; [exact Hcut | reflexivity]].
    + destruct IH as [IH | (tr0 & tr1 & c0 & H0 & Hc0 & E)].
      * left. eapply scfu_canon; eassumption.
      * right. exists (evs ++ tr0), tr1, c0. split; [eapply scfu_canon; eassumption |].
        split; [exact Hc0 | rewrite E, app_assoc; reflexivity].
  - destruct (classic (cut_at refusal segs c1)) as [Hcut | Hcut].
    + right. exists [], (evs ++ tr), c1. split; [apply scfu_refl | split; [exact Hcut | reflexivity]].
    + destruct IH as [IH | (tr0 & tr1 & c0 & H0 & Hc0 & E)].
      * left. eapply scfu_fallback; eassumption.
      * right. exists (evs ++ tr0), tr1, c0. split; [eapply scfu_fallback; eassumption |].
        split; [exact Hc0 | rewrite E, app_assoc; reflexivity].
Qed.

Lemma is_prefix_app_either {A} : forall (a b t : list A),
  is_prefix t (a ++ b) -> is_prefix t a \/ is_prefix a t.
Proof.
  induction a as [| x a IH]; intros b t H.
  - right. apply is_prefix_nil.
  - destruct t as [| y t]; [left; exact I |].
    cbn in H |- *. destruct H as [E H]. subst y.
    destruct (IH b t H) as [H1 | H1]; [left | right]; split; auto.
Qed.

(** A proof of the statement without the exception proves the statement with
    it, whatever [refusal] is: each cut execution is a prefix of an uncut
    one. *)
Lemma agrees_in_room_unless_at_of_agrees_in_room : forall env lim_plain lim_san refusal plain san,
  agrees_in_room env lim_plain lim_san plain san ->
  agrees_in_room_unless_at env lim_plain lim_san refusal plain san.
Proof.
  intros env lim_plain lim_san refusal plain [segs pc ph] H
    p en_plain [sp brk0 mbase rnd] inp Hp Hep Hes Hinp Hb.
  destruct (H p en_plain _ inp Hp Hep Hes Hinp Hb) as (Hpl & Hsn & Htr).
  split; [exact Hpl |].
  split; [| split].
  - intro Hx. cbn [guarded_reaches_error_unless_at] in Hx.
    destruct Hx as (tr & c & evs & Hr & _ & He). apply Hsn. cbn [guarded_reaches_error].
    exists tr, c, evs. split; [| exact He].
    destruct Hr as [(Hg & Hu & Hbr) | Hc].
    + left. split; [eapply star_guarded_ua_guarded; exact Hg | split; assumption].
    + right. unfold canon_run. eapply star_canon_fb_ua_canon_fb. exact Hc.
  - intros tr Hx. cbn [canon_trace_unless_at] in Hx. destruct Hx as (tr' & c & Hc & Hpre).
    apply Htr. cbn [canon_trace].
    exists tr', c. split; [unfold canon_run; eapply star_canon_fb_ua_canon_fb; exact Hc | exact Hpre].
  - intros tr Hx. pose proof (proj1 (Htr tr) Hx) as Hs.
    cbn [canon_trace] in Hs. destruct Hs as (tr' & c & Hc & Hpre). unfold canon_run in Hc.
    destruct (star_canon_fb_ua_split refusal _ _ _ _ _ _ _ _ _ Hc) as [Hu | (tr0 & tr1 & c0 & Hu0 & Hcut & E)].
    + left. cbn [canon_trace_unless_at]. exists tr', c. split; [exact Hu | exact Hpre].
    + subst tr'. destruct (is_prefix_app_either tr0 tr1 tr Hpre) as [H0 | H0].
      * left. cbn [canon_trace_unless_at]. exists tr0, c0. split; [exact Hu0 | exact H0].
      * right. exists tr0. split; [exact H0 |]. cbn [canon_cut_at]. exists c0. split; [exact Hu0 | exact Hcut].
Qed.
