(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(** * Common.Hoare — a Hoare/WP-style program logic over [msteps].

    PROTOTYPE / EXPLORATION.  Image-INDEPENDENT: nothing here knows about
    any particular binary.

    The existing library models a callee as its own [msteps] lemma
    parameterized by the return address ([Common/SeqExec.v]).  That works,
    but every such lemma is restated per binary, at that binary's
    addresses, and it carries no discipline about WHAT the callee may
    touch — so a caller cannot reuse any fact it held about its own
    registers or memory across the call without re-deriving it.

    This file packages the same reachability content as a triple with two
    explicit FOOTPRINTS:

      [triple segs C W P a b Q]

    "from any state satisfying [P] with pc = [a], execution reaches pc =
    [b] in a state satisfying [Q], clobbering no register outside [C] and
    no memory byte outside [W]".

    The triple is DEFINED semantically over [CatSim.msteps], so it is
    sound by construction; every rule below is a lemma about that
    definition.  The footprints are what make the frame rule
    ([triple_frame]) available: a callee summary states what it touches,
    and the caller keeps everything else for free instead of the callee's
    postcondition having to re-enumerate the caller's memory.

    Partial correctness only: [triple] says nothing about executions that
    never reach [b].  That is exactly the strength the equivalence proofs
    need — they build a [to_wexit] witness, i.e. an existential run — and
    [triple_wexit] / [triple_msteps] are the two hand-offs back to the
    shape files.

    ADDRESS PARAMETRICITY.  A triple mentions the code only through the
    fetch/decode facts used to prove it.  Since the [SD_*] decode facts of
    a per-binary [*_code.v] are statements about the instruction WORD, and
    are therefore already binary-independent, a summary of a fixed byte
    sequence (a musl function, say) needs only the [SF_*] fetch facts as
    hypotheses, at [at_ base off].  [Common/MuslCall.v] carries the worked
    example.  The [at_] helpers at the bottom of this file are the address
    arithmetic that makes such a section go through with no wrap-around
    side conditions. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan Require Import PropExec CatExec CatSim SeqExec.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Import ListNotations.
Open Scope bv_scope.

Section WithFP1.
Context {fx : FPState}.

(* ========================================================================= *)
(* Address arithmetic for address-parametric summaries                       *)
(* ========================================================================= *)

(** [at_ base d] is [base + d], the address of the instruction at byte
    offset [d] of a relocatable code blob loaded at [base].  All the
    lemmas below are wrap-around-free BY CONSTRUCTION (the underlying
    [Z_to_bv] wraps), so an address-parametric summary needs NO bound on
    [base]. *)
Definition at_ (base : word) (d : Z) : word := Z_to_bv 64 (bv_unsigned base + d).

Lemma at_0 : forall base, at_ base 0 = base.
Proof.
  intros base. unfold at_. rewrite Z.add_0_r. apply bv_eq.
  rewrite Z_to_bv_unsigned. apply bv_wrap_small, bv_unsigned_in_range.
Qed.

(** The workhorse: stepping the pc by any (possibly negative) displacement
    stays inside the [at_] normal form.  Covers [v_addi pc 4] from every
    straight-line step lemma and [btgt pc imm] from every jump/branch. *)
Lemma at_addi : forall base d e, v_addi (at_ base d) e = at_ base (d + e).
Proof.
  intros base d e. unfold at_, v_addi. apply bv_eq.
  rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

Lemma at_btgt : forall base d e, btgt (at_ base d) e = at_ base (d + e).
Proof. intros. unfold btgt. apply at_addi. Qed.

(** [at_] of a literal base collapses to a literal address — this is the
    one-line bridge a per-binary instantiation uses to feed its [SF_*]
    fetch lemmas to an address-parametric summary. *)
Lemma at_lit : forall (base : word) (d : Z) (a : word),
  Z_to_bv 64 (bv_unsigned base + d) = a -> at_ base d = a.
Proof. intros. assumption. Qed.

(** [at_] composes: an offset from an already-offset address.  ([v_addi]
    and [at_] are the same function, so this IS [at_addi].) *)
Lemma at_at : forall base d e, at_ (at_ base d) e = at_ base (d + e).
Proof. exact at_addi. Qed.

(** Byte-walk helpers: [wbytes]/[rdn] recurse on [a + 1], so every proof
    about a byte RANGE has to re-normalize [bv_unsigned (a + 1) + i]. *)
Lemma u_succ_shift : forall (a : word) (i : Z),
  Z_to_bv 64 (bv_unsigned (a + 1) + i) = Z_to_bv 64 (bv_unsigned a + (1 + i)).
Proof.
  intros a i. apply bv_eq. rewrite !Z_to_bv_unsigned, bv_add_unsigned.
  assert (H1 : bv_unsigned (1 : word) = 1%Z) by reflexivity. rewrite H1.
  unfold bv_wrap. rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

Lemma at_self : forall a : word, Z_to_bv 64 (bv_unsigned a + 0) = a.
Proof. intros a. exact (at_0 a). Qed.


(* ========================================================================= *)
(* Assertions and footprints                                                 *)
(* ========================================================================= *)

(** An assertion talks about the register file, the writable memory
    overlay and the read-only image.  It deliberately does NOT talk about
    the pc: the pc is the triple's index, exactly as in a Hoare logic for
    machine code. *)
Definition assn := bvmap 5 word -> (word -> option byte) -> (word -> option byte) -> Prop.

(** Footprints: which registers a fragment may clobber, and which memory
    bytes it may write.  Both are plain predicates, so [fun _ => True] is
    "anything" and set union is [\/]. *)
Definition regset := reg -> Prop.
Definition memset := word -> Prop.

Definition regs_agree (C : regset) (regs regs' : bvmap 5 word) : Prop :=
  forall r, ~ C r -> getr regs' r = getr regs r.

Definition mem_agree (W : memset) (m m' : word -> option byte) : Prop :=
  forall x, ~ W x -> m' x = m x.

Lemma regs_agree_refl : forall C regs, regs_agree C regs regs.
Proof. intros C regs r _. reflexivity. Qed.

Lemma mem_agree_refl : forall W m, mem_agree W m m.
Proof. intros W m x _. reflexivity. Qed.

Lemma regs_agree_trans : forall C regs1 regs2 regs3,
  regs_agree C regs1 regs2 -> regs_agree C regs2 regs3 -> regs_agree C regs1 regs3.
Proof. intros C r1 r2 r3 H1 H2 r Hr. rewrite (H2 r Hr). apply H1, Hr. Qed.

Lemma mem_agree_trans : forall W m1 m2 m3,
  mem_agree W m1 m2 -> mem_agree W m2 m3 -> mem_agree W m1 m3.
Proof. intros W m1 m2 m3 H1 H2 x Hx. rewrite (H2 x Hx). apply H1, Hx. Qed.

Lemma regs_agree_mono : forall (C C' : regset) regs regs',
  (forall r, C r -> C' r) -> regs_agree C regs regs' -> regs_agree C' regs regs'.
Proof. intros C C' regs regs' Hsub H r Hr. apply H. intro; apply Hr, Hsub; assumption. Qed.

Lemma mem_agree_mono : forall (W W' : memset) m m',
  (forall x, W x -> W' x) -> mem_agree W m m' -> mem_agree W' m m'.
Proof. intros W W' m m' Hsub H x Hx. apply H. intro; apply Hx, Hsub; assumption. Qed.

(** The two shapes an actual step chain produces.  A register writeback is
    a [regupd]; a store is a [wbytes].  These turn "the final state is this
    concrete chain of updates" into the agreement facts a triple owes. *)
Lemma regs_agree_upd : forall (C : regset) regs regs' r v,
  C r -> regs_agree C regs regs' -> regs_agree C regs (regupd regs' r v).
Proof.
  intros C regs regs' r v Hin H s Hs.
  rewrite getr_other by (intro Heq; subst; contradiction).
  apply H, Hs.
Qed.

Lemma mem_agree_wbytes : forall (W : memset) m m' a bs,
  (forall i, (0 <= i < Z.of_nat (length bs))%Z -> W (Z_to_bv 64 (bv_unsigned a + i))) ->
  mem_agree W m m' -> mem_agree W m (wbytes m' a bs).
Proof.
  intros W m m' a bs. revert m' a.
  induction bs as [|b bs IH]; intros m' a Hin H; cbn [wbytes] in *; [exact H|].
  assert (Ha : W a).
  { specialize (Hin 0%Z ltac:(cbn [length]; lia)). rewrite at_self in Hin. exact Hin. }
  apply IH.
  - intros i Hi. rewrite u_succ_shift. apply Hin. cbn [length] in *. lia.
  - intros x Hx. cbn beta. destruct (bv_eqb x a) eqn:Heq.
    + exfalso. apply Hx. unfold bv_eqb in Heq. apply Z.eqb_eq, bv_eq in Heq.
      subst x. exact Ha.
    + apply H, Hx.
Qed.

(* ========================================================================= *)
(* The triple                                                                *)
(* ========================================================================= *)

(** [triple segs C W P a b Q]: from every [P]-state at pc [a] there is an
    [msteps] run to pc [b] landing in [Q], touching only [C] and [W].

    The read-only image [rom] is quantified inside and threaded unchanged:
    [msteps] never writes it, so it is an assertion PARAMETER rather than
    part of the mutable state. *)
Definition triple (segs : list Segment)
                  (C : regset) (W : memset)
                  (P : assn) (a b : word) (Q : assn) : Prop :=
  forall regs mem rom, P regs mem rom ->
    exists regs' mem',
      msteps segs (mkst regs a mem rom) (mkst regs' b mem' rom)
      /\ Q regs' mem' rom
      /\ regs_agree C regs regs'
      /\ mem_agree W mem mem'.

(** Introduction: this is the definition, but naming it keeps the
    per-summary proof scripts readable (and stable if [triple] gains a
    field). *)
Lemma triple_intro : forall segs C W P a b Q,
  (forall regs mem rom, P regs mem rom ->
     exists regs' mem',
       msteps segs (mkst regs a mem rom) (mkst regs' b mem' rom)
       /\ Q regs' mem' rom
       /\ regs_agree C regs regs'
       /\ mem_agree W mem mem') ->
  triple segs C W P a b Q.
Proof. intros; assumption. Qed.

(* ------------------------------------------------------------------ *)
(* Structural rules                                                    *)
(* ------------------------------------------------------------------ *)

(** SKIP. *)
Lemma triple_skip : forall segs C W P a, triple segs C W P a a P.
Proof.
  intros segs C W P a regs mem rom HP.
  exists regs, mem. split; [apply mst_refl|].
  split; [exact HP|]. split; [apply regs_agree_refl|apply mem_agree_refl].
Qed.

(** SEQUENCING.  The footprints add up; use [triple_seq_same] when they
    are already the same set. *)
Lemma triple_seq : forall segs C1 W1 C2 W2 P Q R a b c,
  triple segs C1 W1 P a b Q ->
  triple segs C2 W2 Q b c R ->
  triple segs (fun r => C1 r \/ C2 r) (fun x => W1 x \/ W2 x) P a c R.
Proof.
  intros segs C1 W1 C2 W2 P Q R a b c H1 H2 regs mem rom HP.
  destruct (H1 _ _ _ HP) as (regs1 & mem1 & Hst1 & HQ & Hr1 & Hm1).
  destruct (H2 _ _ _ HQ) as (regs2 & mem2 & Hst2 & HR & Hr2 & Hm2).
  exists regs2, mem2. split; [eapply msteps_trans; eassumption|].
  split; [exact HR|]. split.
  - eapply regs_agree_trans;
      [ eapply regs_agree_mono; [|exact Hr1]
      | eapply regs_agree_mono; [|exact Hr2] ]; auto.
  - eapply mem_agree_trans;
      [ eapply mem_agree_mono; [|exact Hm1]
      | eapply mem_agree_mono; [|exact Hm2] ]; auto.
Qed.

(** CONSEQUENCE, both on the assertions and (weakening) on the
    footprints. *)
Lemma triple_conseq : forall segs C C' W W' P P' Q Q' a b,
  triple segs C W P a b Q ->
  (forall regs mem rom, P' regs mem rom -> P regs mem rom) ->
  (forall regs mem rom, Q regs mem rom -> Q' regs mem rom) ->
  (forall r, C r -> C' r) ->
  (forall x, W x -> W' x) ->
  triple segs C' W' P' a b Q'.
Proof.
  intros segs C C' W W' P P' Q Q' a b H HP HQ HC HW regs mem rom HP'.
  destruct (H _ _ _ (HP _ _ _ HP')) as (regs' & mem' & Hst & HQ0 & Hr & Hm).
  exists regs', mem'. split; [exact Hst|]. split; [apply HQ, HQ0|].
  split; [eapply regs_agree_mono; eauto | eapply mem_agree_mono; eauto].
Qed.

Lemma triple_seq_same : forall segs C W P Q R a b c,
  triple segs C W P a b Q ->
  triple segs C W Q b c R ->
  triple segs C W P a c R.
Proof.
  intros segs C W P Q R a b c H1 H2 regs mem rom HP.
  destruct (H1 _ _ _ HP) as (regs1 & mem1 & Hst1 & HQ & Hr1 & Hm1).
  destruct (H2 _ _ _ HQ) as (regs2 & mem2 & Hst2 & HR & Hr2 & Hm2).
  exists regs2, mem2. split; [eapply msteps_trans; eassumption|].
  split; [exact HR|].
  split; [eapply regs_agree_trans; eassumption | eapply mem_agree_trans; eassumption].
Qed.

(* ------------------------------------------------------------------ *)
(* The frame rule                                                      *)
(* ------------------------------------------------------------------ *)

(** [R] is FRAMEABLE past a fragment with footprints [(C, W)] when it is
    stable under any change confined to those footprints.  This is the
    "separation-logic-lite" of the design: there is no [*] connective and
    no heap splitting, but the caller-side obligation is exactly the one
    [*] would generate — [R] must not look at what the callee writes. *)
Definition frameable (C : regset) (W : memset) (R : assn) : Prop :=
  forall regs mem rom regs' mem',
    regs_agree C regs regs' -> mem_agree W mem mem' ->
    R regs mem rom -> R regs' mem' rom.

(** FRAME. *)
Lemma triple_frame : forall segs C W P Q R a b,
  triple segs C W P a b Q ->
  frameable C W R ->
  triple segs C W (fun regs mem rom => P regs mem rom /\ R regs mem rom) a b
                  (fun regs mem rom => Q regs mem rom /\ R regs mem rom).
Proof.
  intros segs C W P Q R a b H HR regs mem rom (HP & HRr).
  destruct (H _ _ _ HP) as (regs' & mem' & Hst & HQ & Hr & Hm).
  exists regs', mem'. split; [exact Hst|].
  split; [split; [exact HQ | eapply HR; eassumption]|].
  split; assumption.
Qed.

(** Frameability combinators.  These are what a caller actually uses: a
    register outside the clobber set keeps its value; a byte range outside
    the write set keeps its contents; and anything about [rom] alone is
    always frameable. *)
Lemma frameable_and : forall C W R1 R2,
  frameable C W R1 -> frameable C W R2 ->
  frameable C W (fun regs mem rom => R1 regs mem rom /\ R2 regs mem rom).
Proof. intros C W R1 R2 H1 H2 regs mem rom regs' mem' Hr Hm (A & B); split; eauto. Qed.

Lemma frameable_reg : forall (C : regset) W (r : reg) (v : word),
  ~ C r -> frameable C W (fun regs _ _ => getr regs r = v).
Proof.
  intros C W r v Hnc regs mem rom regs' mem' Hr _ Hv.
  rewrite (Hr r Hnc). exact Hv.
Qed.

(** A byte-range read is frameable when the range misses the write set.
    Stated over [rdn], the library's memory read, so it composes with the
    existing read-back lemmas. *)
Lemma frameable_rdn : forall segs (C : regset) (W : memset) (a : word) (n : nat) bs,
  (forall i, (0 <= i < Z.of_nat n)%Z -> ~ W (Z_to_bv 64 (bv_unsigned a + i))) ->
  frameable C W (fun _ mem _ => rdn segs mem a n = Some bs).
Proof.
  intros segs C W a n bs Hdisj regs mem rom regs' mem' _ Hm Hrd.
  rewrite <- Hrd. clear Hrd bs. revert a Hdisj.
  induction n as [|n IH]; intros a Hdisj; [reflexivity|].
  assert (Ha : ~ W a).
  { specialize (Hdisj 0%Z ltac:(lia)). rewrite at_self in Hdisj. exact Hdisj. }
  cbn [rdn]. rewrite (Hm a Ha). rewrite IH; [reflexivity|].
  intros i Hi. rewrite u_succ_shift. apply Hdisj. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The call rule                                                       *)
(* ------------------------------------------------------------------ *)

(** [ret_ok k]: [k] is a legal [ret] target, i.e. [jalr x0, 0(ra)] with
    [ra = k] lands on [k].  The ISA model masks bit 0, so this is
    "[k] is even" — always true of a real return address, and discharged
    by [bveq] whenever [k] is a literal. *)
Definition ret_ok (k : word) : Prop := v_jalr k 0 = k.

Lemma land_m2_even : forall z : Z, (z mod 2 = 0)%Z -> Z.land z (-2) = z.
Proof.
  intros z Hz.
  assert (Hl : Z.land z 1 = 0%Z).
  { replace 1%Z with (Z.ones 1) by reflexivity. rewrite Z.land_ones by lia. exact Hz. }
  replace (-2)%Z with (Z.lnot 1) by reflexivity.
  rewrite <- Z.ldiff_land.
  rewrite <- (Z.lor_ldiff_and z 1) at 2.
  rewrite Hl, Z.lor_0_r. reflexivity.
Qed.

Lemma ret_ok_even : forall k, (bv_unsigned k mod 2 = 0)%Z -> ret_ok k.
Proof.
  intros k Hk. unfold ret_ok, v_jalr, jalr_tgtZ.
  rewrite Z.add_0_r, land_m2_even by exact Hk.
  apply bv_eq. rewrite Z_to_bv_unsigned.
  apply bv_wrap_small, bv_unsigned_in_range.
Qed.

(** A PROCEDURE summary: the address-parametric form.  [proc segs C W P
    entry Q] says the callee, entered at [entry] with a legal return
    address in [ra], returns to that address — whatever it is.  This is
    the shape a musl function is proved in once. *)
Definition proc (segs : list Segment) (C : regset) (W : memset)
                (P : assn) (entry : word) (Q : assn) : Prop :=
  forall k : word, ret_ok k ->
    triple segs C W (fun regs mem rom => P regs mem rom /\ getr regs 1 = k) entry k Q.

(** [P] does not look at [ra] — the caller's precondition cannot, since
    the [jal] overwrites it. *)
Definition ra_indep (P : assn) : Prop :=
  forall regs v mem rom, P regs mem rom -> P (regupd regs 1 v) mem rom.

(** CALL.  [callsite] holds a [jal ra, entry] (any instruction that links
    [ret] into [ra] and jumps to [entry] without touching memory — the
    first hypothesis says exactly that, and is discharged by
    [SeqExec.step_jal_link] plus the binary's fetch/decode facts).  The
    resulting triple runs from the call site to the instruction after it,
    and clobbers [C] plus [ra].

    Note what the caller gets for free: every register outside [C] — sp
    and the callee-saved [s*] in a well-behaved callee — is preserved by
    the triple's own [regs_agree] component, with no help from [Q]. *)
Lemma triple_call : forall segs C W P Q callsite entry ret,
  (forall regs mem rom,
     RiscvSemantics.step segs (mkst regs callsite mem rom)
       = MachineOk (mkst (regupd regs 1 ret) entry mem rom)) ->
  ret_ok ret ->
  ra_indep P ->
  proc segs C W P entry Q ->
  triple segs (fun r => C r \/ r = 1) W P callsite ret Q.
Proof.
  intros segs C W P Q callsite entry ret Hjal Hret HraP Hproc regs mem rom HP.
  assert (Hpre : P (regupd regs 1 ret) mem rom
                 /\ getr (regupd regs 1 ret) 1 = ret).
  { split; [apply HraP, HP|]. apply getr_same. reg_neq_tac. }
  destruct (Hproc ret Hret (regupd regs 1 ret) mem rom Hpre)
    as (regs' & mem' & Hst & HQ & Hr & Hm).
  exists regs', mem'. split.
  - eapply mst_step; [reflexivity | apply Hjal | exact Hst].
  - split; [exact HQ|]. split; [|exact Hm].
    intros r Hr0.
    assert (HnC : ~ C r) by tauto.
    assert (Hne : r <> 1) by tauto.
    rewrite (Hr r HnC), getr_other by exact Hne. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The loop rule                                                       *)
(* ------------------------------------------------------------------ *)

(** LOOP, in the measure-decreasing form the compiled loops actually have:
    the invariant is indexed by a [nat] measure, one body iteration
    returns to the loop head with the measure decreased by one, and the
    measure-zero case exits.

    This replaces the hand-rolled induction each looping example carries
    ([DrainSim]'s per-iteration lemma, [MuslStrlen]'s chunk walk,
    ...): the caller supplies the two hypotheses and gets the whole loop. *)
Lemma triple_loop : forall segs C W (I : nat -> assn) (hd out : word) (Q : assn),
  (forall i, triple segs C W (I (S i)) hd hd (I i)) ->
  triple segs C W (I O) hd out Q ->
  forall n, triple segs C W (I n) hd out Q.
Proof.
  intros segs C W I hd out Q Hbody Hexit n.
  induction n as [|n IH]; [exact Hexit|].
  eapply triple_seq_same; [apply Hbody | exact IH].
Qed.

(** The same, with the measure read off the state instead of supplied by
    the caller: [Inv] holds now, and every state satisfying [Inv] has SOME
    measure. *)
Lemma triple_loop_measure :
  forall segs C W (I : nat -> assn) (hd out : word) (Q P : assn),
  (forall i, triple segs C W (I (S i)) hd hd (I i)) ->
  triple segs C W (I O) hd out Q ->
  (forall regs mem rom, P regs mem rom -> exists n, I n regs mem rom) ->
  triple segs C W P hd out Q.
Proof.
  intros segs C W I hd out Q P Hbody Hexit Hmeas regs mem rom HP.
  destruct (Hmeas _ _ _ HP) as (n & HI).
  exact (triple_loop segs C W I hd out Q Hbody Hexit n regs mem rom HI).
Qed.

(* ------------------------------------------------------------------ *)
(* Hand-off to the behaviour-shape relations                           *)
(* ------------------------------------------------------------------ *)

(** Forget the footprints: a triple is an [msteps] lemma of the shape the
    existing example proofs consume. *)
Lemma triple_msteps : forall segs C W P a b Q regs mem rom,
  triple segs C W P a b Q -> P regs mem rom ->
  exists regs' mem',
    msteps segs (mkst regs a mem rom) (mkst regs' b mem' rom) /\ Q regs' mem' rom.
Proof.
  intros segs C W P a b Q regs mem rom H HP.
  destruct (H _ _ _ HP) as (regs' & mem' & Hst & HQ & _ & _).
  exists regs', mem'. split; assumption.
Qed.

(** Prepend a triple to a [to_wexit] derivation: this is how a summary
    whose tail is an [ecall] hands off to [CatSim]'s syscall constructors
    ([tw_write_ret], [tw_exit_coden]).  The continuation is given the
    postcondition and must produce the rest of the behaviour. *)
Lemma triple_wexit : forall segs C W P a b Q bufs code regs mem rom,
  triple segs C W P a b Q ->
  P regs mem rom ->
  (forall regs' mem', Q regs' mem' rom ->
     to_wexit segs (mkst regs' b mem' rom) bufs code) ->
  to_wexit segs (mkst regs a mem rom) bufs code.
Proof.
  intros segs C W P a b Q bufs code regs mem rom H HP Hcont.
  destruct (H _ _ _ HP) as (regs' & mem' & Hst & HQ & _ & _).
  eapply msteps_to_wexit; [exact Hst | apply Hcont, HQ].
Qed.
End WithFP1.

