(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the lemma region_free_In, which the revised ledger proofs use). *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.

From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Prelude.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Lib Require Import PropExec MState Mem ITree Nodes.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AllocCeil RunRandom.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Section AC_1. Context {ACEIL : AllocCeiling} {RRND : RunRandom}.

Definition errno_of (r : word) : option Z :=
  if (2^64 - 4095 <=? bv_unsigned r)%Z then Some (2^64 - bv_unsigned r)%Z else None.

Lemma errno_of_Some : forall r e, errno_of r = Some e -> r = errno_ret e /\ (1 <= e <= 4095)%Z.
Proof.
  intros r e H. unfold errno_of in H. pose proof (bv_unsigned_in_range 64 r) as R. unfold bv_modulus in R.
  destruct (Z.leb_spec0 (2^64 - 4095) (bv_unsigned r)); [|discriminate]. inversion H; subst.
  split; [|lia]. apply bv_eq. unfold errno_ret. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64)%Z with (2^64)%Z.
  replace (- (2 ^ 64 - bv_unsigned r))%Z with (bv_unsigned r + (-1) * 2^64)%Z by lia.
  rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma errno_of_errno_ret : forall e, (1 <= e <= 4095)%Z -> errno_of (errno_ret e) = Some e.
Proof.
  intros e He. unfold errno_of. rewrite errno_ret_unsigned by lia. unfold two_pow_64.
  destruct (Z.leb_spec0 (2^64 - 4095) (2^64 - e)); [|lia]. f_equal. lia.
Qed.

Lemma errno_of_small : forall r, (bv_unsigned r <= 2^64 - 4096)%Z -> errno_of r = None.
Proof. intros r H. unfold errno_of. destruct (Z.leb_spec0 (2^64 - 4095) (bv_unsigned r)); [lia|reflexivity]. Qed.

Lemma errno_of_lit : forall z, (0 <= z <= 2^64 - 4096)%Z -> errno_of (Z_to_bv 64 z) = None.
Proof. intros. apply errno_of_small. rewrite unsigned_lit by lia. lia. Qed.

Inductive sret : Type := SErr (e : Z) | SVal (v : Z).

Definition dec_plain (ok : Z -> bool) (rsp : resp) : option sret :=
  match rsp with
  | mkEffectU r [] [] [] [] [] =>
      match errno_of r with
      | Some e => Some (SErr e)
      | None => if ok (bv_unsigned r) then Some (SVal (bv_unsigned r)) else None
      end
  | _ => None
  end.

Inductive read_ans : Type := RdErr (e : Z) | RdData (bs : list byte).

Definition dec_read (buf count : Z) (rsp : resp) : option read_ans :=
  match rsp with
  | mkEffectU r [] [] [] [] [] =>
      match errno_of r with
      | Some e => Some (RdErr e)
      | None => if (bv_unsigned r =? 0)%Z then Some (RdData []) else None
      end
  | mkEffectU r [(a, bs)] [] [] [] [] =>
      if bv_eqb a (Z_to_bv 64 buf) && (1 <=? Z.of_nat (length bs))%Z
         && (Z.of_nat (length bs) <=? count)%Z && (bv_unsigned r =? Z.of_nat (length bs))%Z
      then Some (RdData bs) else None
  | _ => None
  end.

Definition dec_count (count : Z) (rsp : resp) : option Z :=
  match rsp with
  | mkEffectU r [] [] [] [] [] => if (bv_unsigned r =? count)%Z then Some count else None
  | _ => None
  end.
Definition dec_write := dec_count.
Definition dec_writev := dec_count.

Definition dec_open : resp -> option sret := dec_plain (fun v => (3 <=? v)%Z && (v <=? 4096)%Z).

Definition dec_close : resp -> option sret := dec_plain (fun v => (v =? 0)%Z).

Definition dec_ioctl : resp -> option sret := dec_plain (fun _ => false).

Definition dec_set_tid (rsp : resp) : option Z :=
  match rsp with
  | mkEffectU r [] [] [] [] [] =>
      if (0 <? bv_unsigned r)%Z && (bv_unsigned r <? PID_MAX_ENVELOPE)%Z then Some (bv_unsigned r) else None
  | _ => None
  end.

Definition dec_exit (rsp : resp) : option Empty_set := None.

Definition dec_brk0 (rsp : resp) : option Z :=
  match rsp with mkEffectU r [] [] [] [] [] => Some (bv_unsigned r) | _ => None end.

Lemma dec_brk0_Some : forall rsp b, dec_brk0 rsp = Some b -> rsp = eff0 (Z_to_bv 64 b) /\ (0 <= b < 2^64)%Z.
Proof.
  intros [r ws zs us cs ci] b H. unfold dec_brk0 in H.
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate]. inversion H; subst.
  pose proof (bv_unsigned_in_range 64 r) as R. unfold bv_modulus in R.
  unfold eff0. rewrite Z_to_bv_bv_unsigned. split; [reflexivity|lia].
Qed.

Definition brk_new_pages (cur req : Z) : option (Z * Z) :=
  let lo := page_round_up_Z cur in let hi := page_round_up_Z req in
  if (lo <? hi)%Z then Some (lo, hi - lo)%Z else None.

Definition zeros_of (p : option (Z * Z)) : list (word * word) :=
  match p with Some (lo, n) => [(wa lo, Z_to_bv 64 n)] | None => [] end.

Inductive brk_ans : Type := BrkGrown | BrkSame.

Definition dec_brk (cur req : Z) (rsp : resp) : option brk_ans :=
  match rsp with
  | mkEffectU r [] zs [] [] [] =>
      if (bv_unsigned r =? cur)%Z && match zs with [] => true | _ => false end then Some BrkSame
      else if (bv_unsigned r =? req)%Z && listNN_eqb zs (zeros_of (brk_new_pages cur req)) then Some BrkGrown
      else None
  | _ => None
  end.

Lemma dec_brk_Some : forall cur req rsp a, dec_brk cur req rsp = Some a ->
  match a with
  | BrkSame => rsp = eff0 (Z_to_bv 64 cur)
  | BrkGrown => rsp = mkEffect (Z_to_bv 64 req) [] (zeros_of (brk_new_pages cur req))
  end.
Proof.
  intros cur req [r ws zs us cs ci] a H. unfold dec_brk in H.
  destruct ws; [|discriminate]. destruct us; [|destruct zs; discriminate]. destruct cs; [|destruct zs; discriminate]. destruct ci; [|destruct zs; discriminate].
  destruct (Z.eqb_spec (bv_unsigned r) cur).
  - destruct zs.
    + cbn [andb] in H. inversion H; subst. unfold eff0. rewrite Z_to_bv_bv_unsigned. reflexivity.
    + cbn [andb] in H. destruct (Z.eqb_spec (bv_unsigned r) req); [|discriminate].
      destruct (listNN_eqb _ _) eqn:E; [|discriminate]. inversion H; subst. apply listNN_eqb_eq in E.
      rewrite <- E, Z_to_bv_bv_unsigned. reflexivity.
  - cbn [andb] in H. destruct (Z.eqb_spec (bv_unsigned r) req); [|discriminate].
    destruct (listNN_eqb _ _) eqn:E; [|discriminate]. inversion H; subst. apply listNN_eqb_eq in E.
    rewrite <- E, Z_to_bv_bv_unsigned. reflexivity.
Qed.

Inductive mmap_ans : Type := MmErr (e : Z) | MmOk (a : Z).

Definition avoids (a n : Z) (avoid : list (Z * Z)) : bool :=
  forallb (fun iv => (a + n <=? fst iv)%Z || (snd iv <=? a)%Z) avoid.

Definition mmap_len (len : Z) : Z := page_round_up_Z len.

Definition mmap_addr_ok (len : Z) (avoid : list (Z * Z)) (a : Z) : bool :=
  (a mod page_size =? 0)%Z && (0 <? a)%Z && (a + mmap_len len <=? alloc_ceiling)%Z && avoids a (mmap_len len) avoid.

Definition dec_mmap (len : Z) (avoid : list (Z * Z)) (rsp : resp) : option mmap_ans :=
  match rsp with
  | mkEffectU r [] [] [] [] [] => match errno_of r with Some e => Some (MmErr e) | None => None end
  | mkEffectU r [] [(a, n)] [] [] [] =>
      if bv_eqb a r && bv_eqb n (Z_to_bv 64 (mmap_len len)) && mmap_addr_ok len avoid (bv_unsigned r)
      then Some (MmOk (bv_unsigned r)) else None
  | _ => None
  end.

Definition dec_mmap_none (len : Z) (avoid : list (Z * Z)) (rsp : resp) : option mmap_ans :=
  match rsp with
  | mkEffectU r [] [] [] [] [] => match errno_of r with Some e => Some (MmErr e) | None => None end
  | mkEffectU r [] [] [(a, n)] [] [] =>
      if bv_eqb a r && bv_eqb n (Z_to_bv 64 (mmap_len len)) && mmap_addr_ok len avoid (bv_unsigned r)
      then Some (MmOk (bv_unsigned r)) else None
  | _ => None
  end.

Lemma mmap_addr_ok_true : forall len avoid a, mmap_addr_ok len avoid a = true ->
  (a mod page_size = 0 /\ 0 < a /\ a + mmap_len len <= alloc_ceiling)%Z /\ avoids a (mmap_len len) avoid = true.
Proof.
  intros len avoid a H. unfold mmap_addr_ok in H.
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.eqb_eq in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3. auto.
Qed.

Lemma dec_mmap_Some : forall len avoid rsp x, dec_mmap len avoid rsp = Some x ->
  match x with
  | MmErr e => rsp = efferr e /\ (1 <= e <= 4095)%Z
  | MmOk a => rsp = mkEffect (Z_to_bv 64 a) [] [(wa a, Z_to_bv 64 (mmap_len len))] /\ mmap_addr_ok len avoid a = true
  end.
Proof.
  intros len avoid [r ws zs us cs ci] x H. unfold dec_mmap in H.
  destruct ws; [|discriminate]. destruct zs as [|[a n] [|? ?]]; try discriminate.
  - destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate]. destruct (errno_of r) eqn:E; [|discriminate]. inversion H; subst.
    apply errno_of_Some in E as [-> He]. auto.
  - destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
    destruct (bv_eqb a r) eqn:E1; [|discriminate]. destruct (bv_eqb n _) eqn:E2; [|discriminate].
    destruct (mmap_addr_ok len avoid (bv_unsigned r)) eqn:E3; [|discriminate]. cbn [andb] in H. inversion H; subst.
    apply bv_eqb_eq in E1. apply bv_eqb_eq in E2. subst. unfold wa. rewrite Z_to_bv_bv_unsigned. auto.
Qed.

Lemma dec_mmap_none_Some : forall len avoid rsp x, dec_mmap_none len avoid rsp = Some x ->
  match x with
  | MmErr e => rsp = efferr e /\ (1 <= e <= 4095)%Z
  | MmOk a => rsp = mkEffectU (Z_to_bv 64 a) [] [] [(wa a, Z_to_bv 64 (mmap_len len))] [] [] /\ mmap_addr_ok len avoid a = true
  end.
Proof.
  intros len avoid [r ws zs us cs ci] x H. unfold dec_mmap_none in H.
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us as [|[a n] [|? ?]]; try discriminate.
  - destruct cs; [|discriminate]. destruct ci; [|discriminate]. destruct (errno_of r) eqn:E; [|discriminate]. inversion H; subst. apply errno_of_Some in E as [-> He]. auto.
  - destruct cs; [|discriminate]. destruct ci; [|discriminate].
    destruct (bv_eqb a r) eqn:E1; [|discriminate]. destruct (bv_eqb n _) eqn:E2; [|discriminate].
    destruct (mmap_addr_ok len avoid (bv_unsigned r)) eqn:E3; [|discriminate]. cbn [andb] in H. inversion H; subst.
    apply bv_eqb_eq in E1. apply bv_eqb_eq in E2. subst. unfold wa. rewrite Z_to_bv_bv_unsigned. auto.
Qed.

Inductive range_ans : Type := RgErr (e : Z) | RgDone (changed : bool).

Definition dec_munmap (addr len : Z) (rsp : resp) : option range_ans :=
  match rsp with
  | mkEffectU r [] [] [] [] [] =>
      match errno_of r with Some e => Some (RgErr e) | None => if (bv_unsigned r =? 0)%Z then Some (RgDone false) else None end
  | mkEffectU r [] [] [(a, n)] [] [] =>
      if (bv_unsigned r =? 0)%Z && bv_eqb a (Z_to_bv 64 addr) && bv_eqb n (Z_to_bv 64 (mmap_len len))
      then Some (RgDone true) else None
  | _ => None
  end.

Definition dec_mprotect (addr len : Z) (rsp : resp) : option range_ans :=
  match rsp with
  | mkEffectU r [] [] [] [] [] =>
      match errno_of r with Some e => Some (RgErr e) | None => if (bv_unsigned r =? 0)%Z then Some (RgDone false) else None end
  | mkEffectU r [] [(a, n)] [] [] [] =>
      if (bv_unsigned r =? 0)%Z && bv_eqb a (Z_to_bv 64 addr) && bv_eqb n (Z_to_bv 64 (mmap_len len))
      then Some (RgDone true) else None
  | _ => None
  end.

Lemma dec_munmap_Some : forall addr len rsp x, dec_munmap addr len rsp = Some x ->
  match x with
  | RgErr e => rsp = efferr e /\ (1 <= e <= 4095)%Z
  | RgDone false => rsp = eff0 (Z_to_bv 64 0)
  | RgDone true => rsp = mkEffectU (Z_to_bv 64 0) [] [] [(Z_to_bv 64 addr, Z_to_bv 64 (mmap_len len))] [] []
  end.
Proof.
  intros addr len [r ws zs us cs ci] x H. unfold dec_munmap in H.
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us as [|[a n] [|? ?]]; try discriminate.
  - destruct cs; [|discriminate]. destruct ci; [|discriminate]. destruct (errno_of r) eqn:E. { inversion H; subst. apply errno_of_Some in E as [-> He]. auto. }
    destruct (Z.eqb_spec (bv_unsigned r) 0); [|discriminate]. inversion H; subst.
    unfold eff0. f_equal. apply bv_eq. rewrite unsigned_lit by lia. assumption.
  - destruct cs; [|discriminate]. destruct ci; [|discriminate]. destruct (Z.eqb_spec (bv_unsigned r) 0); [|discriminate].
    destruct (bv_eqb a _) eqn:E1; [|discriminate]. destruct (bv_eqb n _) eqn:E2; [|discriminate].
    cbn [andb] in H. inversion H; subst. apply bv_eqb_eq in E1. apply bv_eqb_eq in E2. subst.
    f_equal. apply bv_eq. rewrite unsigned_lit by lia. assumption.
Qed.

Lemma dec_mprotect_Some : forall addr len rsp x, dec_mprotect addr len rsp = Some x ->
  match x with
  | RgErr e => rsp = efferr e /\ (1 <= e <= 4095)%Z
  | RgDone false => rsp = eff0 (Z_to_bv 64 0)
  | RgDone true => rsp = mkEffect (Z_to_bv 64 0) [] [(Z_to_bv 64 addr, Z_to_bv 64 (mmap_len len))]
  end.
Proof.
  intros addr len [r ws zs us cs ci] x H. unfold dec_mprotect in H.
  destruct ws; [|discriminate]. destruct zs as [|[a n] [|? ?]]; try discriminate.
  - destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
    destruct (errno_of r) eqn:E. { inversion H; subst. apply errno_of_Some in E as [-> He]. auto. }
    destruct (Z.eqb_spec (bv_unsigned r) 0); [|discriminate]. inversion H; subst.
    unfold eff0. f_equal. apply bv_eq. rewrite unsigned_lit by lia. assumption.
  - destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate]. destruct (Z.eqb_spec (bv_unsigned r) 0); [|discriminate].
    destruct (bv_eqb a _) eqn:E1; [|discriminate]. destruct (bv_eqb n _) eqn:E2; [|discriminate].
    cbn [andb] in H. inversion H; subst. apply bv_eqb_eq in E1. apply bv_eqb_eq in E2. subst.
    f_equal. apply bv_eq. rewrite unsigned_lit by lia. assumption.
Qed.

Definition covered (maps : list (word * word)) (iv : Z * Z) : Prop :=
  exists e sz, In (e, sz) maps /\ (bv_unsigned e <= fst iv)%Z /\ (snd iv <= bv_unsigned e + bv_unsigned sz)%Z.

(* DO NOT TIDY THE SPELLING OF [region_free_In] AT ANY SITE IN THIS UNIT.
   The name resolves SEVEN ways here and two of the candidates differ in their
   CONCLUSION while agreeing in arity, so a mis-resolution raises no arity error and
   surfaces later as a regression in a file nobody edited.

   HARMLESS GROUP, four local declarations, each BYTE-IDENTICAL to the model's
   theories/Common/RefNodes.v:793 down to the first line of proof
   ([induction l as [|[b' s'] l IH]]):
     bpA/HF/HRefNodes.v:271 · bpA/Start/AsanRefNodes.v:298
     bpB/HF/BRefNodes.v:270 · bpB/Start/BothRefNodes.v:297
   Unqualified resolution AMONG THESE is safe because the candidates do not differ.

   THE HAZARD, and it is the pair to leave alone:
     THIS lemma, the [Lemma region_free_In] immediately below this comment — five
       arguments [maps a n e sz], conclusion a
       DISJUNCTION of two [bv_unsigned] inequalities.
     the model's LinuxProcessSem/State.v:6336 — ALSO five arguments [maps lo n a sz],
       nearly the same binder shape, conclusion the BOOLEAN [iv_overlap lo n a sz = false].
   Same name, same arity, different proposition. Qualifying a site here onto [State.]
   — or unqualifying a [State.]-qualified site into this scope — type-checks at the
   application and fails at its consumer.  This unit mirrors bpA into bpB, so any
   such edit lands twice.

   THE THREE SITES THAT REACH THE BOOLEAN FORM, AND THEY ARE THE ONES NOT TO TOUCH:
     CJ/Lib/NodesMM.v:202   pose proof (State.region_free_In maps lo n a sz H Hin)
     bpA/HF/LazyNodes.v:398 pose proof (State.region_free_In maps a n lo sz Hf Hin)
     bpB/HF/BazyNodes.v:394 pose proof (State.region_free_In maps a n lo sz Hf Hin)
   Each is followed by a use of [iv_overlap], which is how you can tell from the
   application alone that it is the boolean form and not this one.

   A FOURTH SITE REACHES THE BOOLEAN FORM AND IT IS UNQUALIFIED, WHICH MAKES IT THE
   MOST EXPOSED OF THE FOUR:
     Common/BudgetBridge/BBMCharge.v:272
   Nothing in its spelling says which lemma it means.  It was resolved by the
   consuming tactic, which is the cheap discriminator for this name: a site whose
   result feeds [lia] is the DISJUNCTION form, because [lia] cannot consume
   [iv_overlap _ _ _ _ = false]; a site followed by [unfold iv_overlap] is the
   BOOLEAN form.  Qualifying that line onto either local RefNodes copy would swap a
   boolean for a disjunction and typecheck at the edit.

   ONE MITIGATION, MEASURED, SO THE RISK IS NOT OVERSTATED: each of the three
   [State.]-qualified sites is the ONLY occurrence of the name in its file, so the
   usual trigger -- a qualified site sitting beside an unqualified neighbour and
   reading as an inconsistency to clean up -- DOES NOT OCCUR HERE.  The danger is a
   unit-wide normalisation pass, not a local edit.

   Measured 2026-11-07 by RepairG3bLead4.SpirvRed5 at model sha 75d69e0079f9.
   CANDIDATES ENUMERATED FROM THE MODEL AS WELL AS THIS TREE, BOTH MODEL
   DECLARATIONS: Common/RefNodes.v:793 (disjunction) and LinuxProcessSem/State.v:6336
   (boolean).  The five local declarations are POSITION-ALIGNED with the model's
   disjunction, not merely equal in arity -- [maps a n e sz] against [l lo n b s]
   binds list, base, length, entry-base, entry-size in that order in both -- so the
   locals are alpha-equivalent to each other and harmless among themselves.  The
   lethal axis here is CONCLUSION, against the model's boolean, not binder order.
   Spellings: 14 qualified onto a local copy ([HRefNodes.] 7, [BRefNodes.] 7), 3 onto
   [State.], 22 unqualified tokens of which 10 are application lines.  Of those 10 the
   tactic discriminator was run at THREE window widths, which is the test that
   matters and which I had not run when I first wrote this paragraph:
       3 lines   BOOLEAN 2   DISJUNCTION 5   unresolved 3
       6 lines   BOOLEAN 2   DISJUNCTION 7   unresolved 1
      12 lines   BOOLEAN 2   DISJUNCTION 8   unresolved 0
   THE BOOLEAN COLUMN SATURATES IMMEDIATELY -- flat at 2 across a 4x widening -- so
   those two are LOCAL hits and are established.  THE DISJUNCTION COLUMN NEVER
   PLATEAUS: 5, 7, 8, still climbing at the widest window tried.  That is the
   signature of SCAVENGING, not of resolving: [lia] is ubiquitous, so a wider window
   keeps admitting [lia]s that belong to OTHER hypotheses in the same proof.
   **SO THE DISJUNCTION COLUMN IS NOT ESTABLISHED AT ANY WINDOW IN THIS NOTE.** The
   conservative 3-line reading is kept deliberately; the 12-line map looks complete
   and is less true.  Only BOOLEAN 2 is a result.
   The IN-SCOPE DECLARATION COUNT -- cheaper than the tactic test and subsuming it
   where a file has a singleton -- separately settles CJ/Spec/KLink.v:289 and :594 as
   BOOLEAN, those two files reaching only [State] directly.
   The INTRO-PATTERN test ([as [H|H]] destructures a disjunction and cannot be a
   boolean, and it reads the site's own line so it is window-independent) was run and
   settles NOTHING here: no site in this unit uses that form.
   SEVEN OF TEN RESOLVED.  THE REMAINING THREE ARE NOT RESOLVED AND MUST NOT BE READ
   AS PROBABLY FINE: bpA/Start/AsanNodesMmA.v:517 and :523 and
   bpB/Start/BothNodesMmA.v:512 have BOTH candidates reachable, so what they take is
   decided by import ORDER -- see the scope table below.  An earlier draft of this
   note claimed all ten, on a same-line grep that missed a [State] arriving on a
   continuation line; the three are listed here as unresolved rather than guessed.
   No single instrument reaches all of them: the tactic window is blind where the
   next tactic is [eauto] or a bullet, the in-scope count is blind where two
   candidates are reachable, and both are blind where the name arrives transitively.

   AND THE SECOND AND THIRD PROHIBITIONS, BOTH MORE DANGEROUS THAN THE FIRST BECAUSE
   ADDING AN IMPORT OR REORDERING ONE IS AN ORDINARY THING TO DO AND RENAMING A
   SPELLING IS NOT.  THE SCOPE TABLE SPLITS THIS UNIT TWO WAYS -- a unit-level
   verdict on this axis is wrong whichever way you take it:

     FRAGILE, CLASS WITHDRAWN -- I had these two as "one candidate in scope, correct
     by absence".  THAT ROW IS WITHDRAWN AND THE REASON MATTERS MORE THAN THE ROW:
       Common/BudgetBridge/BBMCharge.v   direct imports: [State], no RefNodes
       CJ/Spec/KLink.v                   direct imports: [State], no RefNodes
     The absence was measured over each file's OWN import sentences.  It is not a
     transitive answer, and this unit uses [Require Export] 101 times -- including
     [CJ/Lib/SysStep.v:12 Require Export Decode], which exports THIS FILE and with it
     the disjunction declaration, and [Drv/{S1,U1}ExitBase.v:13 Require Export
     SumWalkTac RefNodes].  So a carrier can arrive at a file that never names one.
     UNTIL SOMEONE ENUMERATES THE TRANSITIVE CLOSURE FOR THESE TWO, TREAT THEM AS
     FRAGILE WITH THE CLASS UNDETERMINED: do not add a [Require], do not reorder the
     imports, and qualify any site you touch.  Both prohibitions, because I cannot
     yet say which one applies.

     ALREADY AMBIGUOUS -- BOTH candidates in scope TODAY, so which one an unqualified
     site takes is decided by IMPORT ORDER.  There is nothing to add that would break
     these; the instability is live now.
       bpA/Start/AsanNodesMmA.v          [State] AND a RefNodes copy both reachable
       bpB/Start/BothNodesMmA.v          same, the twin
     DO NOT REORDER THE IMPORTS IN THESE TWO, and qualify any site you touch.

   HOW THAT TABLE WAS CORRECTED, because the first version of this note had the last
   two in the wrong class: a same-line grep for [Require .* State] reported State
   ABSENT from both, and a SENTENCE-AWARE read -- terminating at a period followed by
   whitespace rather than at a newline -- finds it PRESENT, arriving on a
   CONTINUATION LINE of a wrapped import list.  Both files wrap.  A unit whose import
   lists wrap cannot answer this question by line-oriented grep at all, and the files
   most at risk are the ones with the longest import blocks, which are exactly the
   ones that wrap.

   Note the consequence for the two fragile-by-absence files, which runs against the
   intuition: a normalising pass there would not RESOLVE an ambiguity -- it would
   CREATE one, by bringing a second declaration into a file that has exactly one.

   Both tests were run and they disagree, which is the point: the PROSE test passes
   at about 3 per cent, so the figure is almost all real application text, and it dies
   on the RESOLUTION test instead.  The predictor for which test will kill a figure is
   one grep -- count the LOCAL declarations: five here, so resolution was always the
   risk and the prose ratio was never going to matter.  The token total is a count of
   a NAME and not of a lemma; do not quote it as a use count. *)
Lemma region_free_In : forall maps a n e sz,
  region_free maps a n = true -> In (e, sz) maps ->
  (bv_unsigned a + bv_unsigned n <= bv_unsigned e \/ bv_unsigned e + bv_unsigned sz <= bv_unsigned a)%Z.
Proof.
  induction maps as [|[e0 sz0] maps IH]; intros a n e sz H Hin; [destruct Hin|].
  cbn [region_free] in H. apply andb_prop in H as [H1 H2].
  destruct Hin as [E|Hin]; [|exact (IH _ _ _ _ H2 Hin)].
  inversion E; subst. unfold iv_overlap in H1.
  destruct (Z.ltb_spec0 (bv_unsigned a) (bv_unsigned e + bv_unsigned sz));
  destruct (Z.ltb_spec0 (bv_unsigned e) (bv_unsigned a + bv_unsigned n)); cbn in H1; try discriminate; lia.
Qed.

Lemma avoids_of_region_free : forall maps a n avoid,
  region_free maps a n = true ->
  Forall (covered maps) avoid ->
  avoids (bv_unsigned a) (bv_unsigned n) avoid = true.
Proof.
  intros maps a n avoid Hrf Hc. unfold avoids. apply forallb_forall. intros [lo hi] Hin.
  pose proof (proj1 (Forall_forall _ _) Hc _ Hin) as (e & sz & He & H1 & H2). cbn in H1, H2. cbn [fst snd].
  pose proof (region_free_In _ _ _ _ _ Hrf He) as [H|H].
  - apply orb_true_intro. left. apply Z.leb_le. lia.
  - apply orb_true_intro. right. apply Z.leb_le. lia.
Qed.

Lemma mmap_len_bound : forall len, (0 < len)%Z -> (len <= mmap_len len < len + 4096)%Z.
Proof. intros len H. unfold mmap_len, page_round_up_Z, page_size. split; [|]; nia || lia. Qed.

End AC_1.
