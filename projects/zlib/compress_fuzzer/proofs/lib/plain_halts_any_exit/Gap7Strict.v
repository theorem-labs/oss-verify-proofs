(** * Gap7Strict — the STRICT declarative stream decoder, round 3:
    the lax [dec_stream_from] with the machine's header-accept guards,
    where the code-acceptance guard IS THE MACHINE'S OWN BUILDER.

    OWNER: an earlier development run.  (viii) round-3 per the chair's (c) ruling: the
    enumeration guards A2/A3/A4 are REPLACED by [build_accepts_b] — run
    [Inftrees.it_model] on the decoded lists at the machine's own call
    shapes and accept iff [o_ret = 0].  Grounds (chair record): the
    enumeration row-class bit twice in one round; a guard that is the
    machine's accept BY CONSTRUCTION ends the class.  A1 stays (the
    TOO_MANY caps live outside it_model, Inflate :1366 / inflate.c:900-905).

    DESIGN DECISIONS, STATED PLAINLY (q6 requirement (5)/(e)):
    - DEC-ONLY IS ABANDONED: this "declarative" decoder is NOT
      machine-independent — [build_accepts_b] references the machine's
      table builder.  That is the point: the premise side carries
      exactly the machine's acceptance, so no validation-asymmetry
      corner can exist between this decoder and the machine's header
      path.  It is a PREMISE-side artifact (one interface per
      consumer-need); the trusted declarative semantics are unchanged.
    - BUILDER CHOICE (q6 requirement (3)): [Inftrees.it_model], the
      LANDED spec-side builder — explicitly NOT any hash-qualified
      ItModel copy, so no ItGTblBridge re-pin is needed.
    - THE LIST->ZARR SEAM is spelled ONCE: [lens_of_list] below; every
      guard call goes through it.
    - CALL SHAPES (q6 requirement, verified): CL = CT_CODES/19/7
      (read_cl_lengths returns the scattered 19-slot layout,
      DeflateSpec:674 pins length 19); LEN = CT_LENS/nlit/9;
      DIST = CT_DISTS/ndist/6.  The machine's DIST call reads at the
      nlen offset of its lens area — as a function of the decoded [dst]
      LIST the offset is absorbed (the selection bridges via
      it_model_lens_ext's window agreement).
    - T0-INDEPENDENCE AS A LEMMA (q6 requirement): [it_model_tbl_ext]
      below — o_ret/o_bits/o_used do not depend on the initial table,
      so the guard's [tnone] instantiation decides acceptance for the
      machine's real call at its live cs table.  (ItGModelExt has the
      LENS-window twin; the t0 twin did not exist — ItGModelExt:456's
      own comment notes the real decoder does not pass tnone.)
    - THE ENOUGH OBLIGATION RELOCATES to the supply side (chair
      structure ruling): q5's wave delivers strict-success MODULO one
      NAMED lemma (emitted/valid lens pass the builder's space check);
      the universal theorem (valid => used <= ENOUGH; tight constants
      852/592, zlib's enough.c, DP-reflection class) is a separately
      commissioned item.  Under this guard the SELECTION's dyn arm is
      math-free.

    ROW TABLE (v3): A1 caps (guarded); ALL build-time causes — kraft,
    incompleteness incl. the CT_CODES exemption shape, and the row-5-bis
    ItOverflow/it_enough cause — are subsumed BY CONSTRUCTION in
    [build_accepts_b].  COVERED BY LAX SUCCESS (verified, unchanged):
    oversubscription (valid_lengths_b), rep-without-previous/overflow
    (rl_run:709 / read_lengths_fuel), missing-EOB + the mx=0
    PreEmpty-accept subtlety (hdecode over an empty code_table is
    None), truncations.  NON-GUARD: lit[256] <> 0 (derivable;
    re-assertion class).  CITE CONVENTION: "Inflate :N"/"Inftrees :N"
    are Rocq model lines; "inflate.c:N" is the C source.

    PA-EXPORTS: it_step_tbl_ext, it_loop_tbl_ext, it_model_tbl_ext,
    decode_dynamic_tables_strict_weaken, dec_blk_strict_weaken,
    dec_stream_strict_fuel_weaken, dec_stream_from_strict_weaken.

    TRUST BOUNDARY: pure Gallina, image-independent. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Inftrees DeflateSpec.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(* The list->zarr seam (ONCE), the t0-independence chain, the guard.   *)

Definition lens_of_list (l : list nat) : zarr := zlens l.

(** Replace a state's table, keeping every other field. *)
Definition with_tbl (st : ItSt) (t : ztbl) : ItSt :=
  {| s_huff := s_huff st; s_sym := s_sym st; s_len := s_len st;
     s_next := s_next st; s_curr := s_curr st; s_drop := s_drop st;
     s_low := s_low st; s_used := s_used st; s_min := s_min st;
     s_count := s_count st; s_tbl := t |}.

(** One trip's control flow and non-table fields ignore the table. *)
Lemma it_step_tbl_ext : forall c st t',
  match it_step c st with
  | ItCont r => exists u, it_step c (with_tbl st t') = ItCont (with_tbl r u)
  | ItBreak r => exists u, it_step c (with_tbl st t') = ItBreak (with_tbl r u)
  | ItOverflow _ => exists u, it_step c (with_tbl st t') = ItOverflow u
  end.
Proof.
  intros c st t'.
  destruct st as [h sy l n cu d lo u m cnt tb].
  unfold it_step, with_tbl; cbn
    [s_huff s_sym s_len s_next s_curr s_drop s_low s_used s_min s_count
     s_tbl].
  cbv zeta.
  destruct (Z.eqb _ 0); cbn [andb].
  - destruct (Z.eqb l (x_max c)); cbn [andb].
    + eexists; reflexivity.
    + destruct (Z.ltb (x_root c) _ && negb (Z.eqb _ lo))%bool.
      * destruct (it_enough _ _); eexists; reflexivity.
      * eexists; reflexivity.
  - destruct (Z.eqb l (x_max c)); cbn [andb];
      (destruct (Z.ltb (x_root c) _ && negb (Z.eqb _ lo))%bool;
       [ destruct (it_enough _ _); eexists; reflexivity
       | eexists; reflexivity ]).
Qed.

Lemma it_loop_tbl_ext : forall n c st t',
  match it_loop n c st, it_loop n c (with_tbl st t') with
  | Some (ItBreak a), Some (ItBreak b) =>
      s_used b = s_used a /\ exists u, b = with_tbl a u
  | Some (ItOverflow _), Some (ItOverflow _) => True
  | Some (ItCont _), Some (ItCont _) => True
  | None, None => True
  | _, _ => False
  end.
Proof.
  induction n as [|n IH]; intros c st t'; cbn [it_loop]; [exact I|].
  pose proof (it_step_tbl_ext c st t') as HS.
  destruct (it_step c st) as [r|r|t] eqn:E.
  - destruct HS as [u ->]. exact (IH c r u).
  - destruct HS as [u ->].
    split; [reflexivity | exists u; reflexivity].
  - destruct HS as [u ->]. exact I.
Qed.

(** THE BRIDGE: acceptance (and bits/used) ignore the initial table, so
    the guard's [tnone] run decides the machine's real call. *)
Lemma it_model_tbl_ext : forall ty lens codes root0 t0 t1,
  match it_model ty lens codes root0 t0, it_model ty lens codes root0 t1
  with
  | Some o, Some o' => o_ret o' = o_ret o /\ o_bits o' = o_bits o
                       /\ o_used o' = o_used o
  | None, None => True
  | _, _ => False
  end.
Proof.
  intros ty lens codes root0 t0 t1.
  unfold it_model, it_pre. cbv zeta.
  destruct (Z.eqb (it_findmax _ _ _) 0); [cbn; repeat split|].
  destruct (it_kraft _ _ _ _) as [lft|]; [|cbn; repeat split].
  destruct (it_incomplete _ _ _); [cbn; repeat split|].
  destruct (it_enough _ _); [cbn; repeat split|].
  (* name the two loop calls; the t0-side state is the one mentioning t0 *)
  match goal with
  | |- context [it_loop ?n ?c ?st] =>
      match st with
      | context [t0] =>
          set (N := n) in *; set (C := c) in *; set (ST0 := st) in *
      end
  end.
  match goal with
  | |- context [it_loop N C ?st] =>
      match st with
      | context [t1] => set (ST1 := st) in *
      end
  end.
  pose proof (it_loop_tbl_ext N C ST0 t1) as HL.
  replace (with_tbl ST0 t1) with ST1 in HL
    by (unfold ST1, ST0, with_tbl; reflexivity).
  revert HL.
  destruct (it_loop N C ST0) as [[a|a|ta]|];
    destruct (it_loop N C ST1) as [[b|b|tb]|];
    intro HL; cbn;
    first [ exact I
          | exact (conj eq_refl (conj eq_refl eq_refl))
          | (destruct HL as (Hu & _);
             exact (conj eq_refl (conj eq_refl Hu)))
          | destruct HL ].
Qed.

(** THE GUARD: the machine's own builder accepts the decoded list. *)
Definition build_accepts_b (ty : Z) (l : list nat) (root0 : Z) : bool :=
  match it_model ty (lens_of_list l) (Z.of_nat (length l)) root0 tnone
  with
  | Some o => (o_ret o =? 0)%Z
  | None => false
  end.

(* ------------------------------------------------------------------ *)
(* The strict chain: lax text + guards.                                *)

Definition decode_dynamic_tables_strict (bits : list bool)
  : option (list nat * list nat * list bool) :=
  match read_bits 5%nat bits with
  | None => None
  | Some (hlit, r1) =>
      match read_bits 5%nat r1 with
      | None => None
      | Some (hdist, r2) =>
          match read_bits 4%nat r2 with
          | None => None
          | Some (hclen, r3) =>
              let nlit := (Z.to_nat hlit + 257)%nat in
              let ndist := (Z.to_nat hdist + 1)%nat in
              let ncl := (Z.to_nat hclen + 4)%nat in
              match read_cl_lengths ncl r3 with
              | None => None
              | Some (cl, r4) =>
                  if valid_lengths_b cl 7%nat
                     && build_accepts_b CT_CODES cl 7 then
                    match read_lengths cl (nlit + ndist)%nat r4 with
                    | None => None
                    | Some (ls, r5) =>
                        let lit := firstn nlit ls in
                        let dst := skipn nlit ls in
                        if valid_lengths_b lit 15%nat
                           && valid_lengths_b dst 15%nat
                           && (length lit <=? 286)%nat
                           && (length dst <=? 30)%nat
                           && build_accepts_b CT_LENS lit 9
                           && build_accepts_b CT_DISTS dst 6
                        then Some (lit, dst, r5)
                        else None
                    end
                  else None
              end
          end
      end
  end.

Definition dec_blk_strict (bits : list bool) (acc : list Z)
  : option (bool * list Z * list bool) :=
  match read_bits 1%nat bits with
  | None => None
  | Some (bfinal, r1) =>
      match read_bits 2%nat r1 with
      | None => None
      | Some (btype, r2) =>
          let fin := Z.eqb bfinal 1 in
          if Z.eqb btype 0 then
            match decode_stored r2 with
            | None => None
            | Some (payload, r3) => Some (fin, acc ++ payload, r3)
            end
          else if Z.eqb btype 1 then
            match decode_symbols fixed_lit_lengths fixed_dist_lengths r2 with
            | None => None
            | Some (syms, r3) =>
                match resolve_lz syms acc with
                | None => None
                | Some out => Some (fin, out, r3)
                end
            end
          else if Z.eqb btype 2 then
            match decode_dynamic_tables_strict r2 with
            | None => None
            | Some (lit, dst, r3) =>
                match decode_symbols lit dst r3 with
                | None => None
                | Some (syms, r4) =>
                    match resolve_lz syms acc with
                    | None => None
                    | Some out => Some (fin, out, r4)
                    end
                end
            end
          else None
      end
  end.

Fixpoint dec_stream_strict_fuel (fuel : nat) (bits : list bool)
                                (acc : list Z)
  : option (list Z * list bool) :=
  match fuel with
  | O => None
  | S f =>
      match dec_blk_strict bits acc with
      | None => None
      | Some (fin, acc', rem) =>
          if fin then Some (acc', rem) else dec_stream_strict_fuel f rem acc'
      end
  end.

Definition dec_stream_from_strict (bits : list bool) (acc : list Z)
  : option (list Z * list bool) :=
  dec_stream_strict_fuel (S (length bits)) bits acc.

(* ------------------------------------------------------------------ *)
(* Weakening: strict success is lax success at the same value.         *)

Lemma decode_dynamic_tables_strict_weaken : forall bits lit dst rem,
  decode_dynamic_tables_strict bits = Some (lit, dst, rem) ->
  decode_dynamic_tables bits = Some (lit, dst, rem).
Proof.
  intros bits lit dst rem H.
  unfold decode_dynamic_tables_strict in H.
  unfold decode_dynamic_tables.
  destruct (read_bits 5%nat bits) as [[hlit r1]|]; [|discriminate].
  destruct (read_bits 5%nat r1) as [[hdist r2]|]; [|discriminate].
  destruct (read_bits 4%nat r2) as [[hclen r3]|]; [|discriminate].
  destruct (read_cl_lengths _ r3) as [[cl r4]|]; [|discriminate].
  destruct (valid_lengths_b cl 7%nat) eqn:Ev; cbn [andb] in H;
    [|discriminate].
  destruct (build_accepts_b CT_CODES cl 7); [|discriminate].
  destruct (read_lengths _ _ r4) as [[ls r5]|]; [|discriminate].
  destruct (valid_lengths_b (firstn _ ls) 15%nat) eqn:Ev1;
    cbn [andb] in H; [|discriminate].
  destruct (valid_lengths_b (skipn _ ls) 15%nat) eqn:Ev2;
    cbn [andb] in H; [|discriminate].
  destruct ((length (firstn _ ls) <=? 286)%nat); cbn [andb] in H;
    [|discriminate].
  destruct ((length (skipn _ ls) <=? 30)%nat); cbn [andb] in H;
    [|discriminate].
  destruct (build_accepts_b CT_LENS (firstn _ ls) 9); cbn [andb] in H;
    [|discriminate].
  destruct (build_accepts_b CT_DISTS (skipn _ ls) 6); [|discriminate].
  exact H.
Qed.

Lemma dec_blk_strict_weaken : forall bits acc fin out rem,
  dec_blk_strict bits acc = Some (fin, out, rem) ->
  dec_blk bits acc = Some (fin, out, rem).
Proof.
  intros bits acc fin out rem H.
  unfold dec_blk_strict in H. unfold dec_blk.
  destruct (read_bits 1%nat bits) as [[bfinal r1]|]; [|discriminate].
  destruct (read_bits 2%nat r1) as [[btype r2]|]; [|discriminate].
  destruct (Z.eqb btype 0); [exact H|].
  destruct (Z.eqb btype 1); [exact H|].
  destruct (Z.eqb btype 2); [|exact H].
  destruct (decode_dynamic_tables_strict r2) as [[[lit dst] r3]|] eqn:ED;
    [|discriminate].
  rewrite (decode_dynamic_tables_strict_weaken r2 lit dst r3 ED).
  exact H.
Qed.

Lemma dec_stream_strict_fuel_weaken : forall fuel bits acc out rem,
  dec_stream_strict_fuel fuel bits acc = Some (out, rem) ->
  dec_stream_fuel fuel bits acc = Some (out, rem).
Proof.
  induction fuel as [|f IH]; intros bits acc out rem H;
    cbn [dec_stream_strict_fuel] in H; cbn [dec_stream_fuel];
    [discriminate|].
  destruct (dec_blk_strict bits acc) as [[[fin acc'] r]|] eqn:EB;
    [|discriminate].
  rewrite (dec_blk_strict_weaken bits acc fin acc' r EB).
  destruct fin; [exact H | exact (IH r acc' out rem H)].
Qed.

Lemma dec_stream_from_strict_weaken : forall bits acc out rem,
  dec_stream_from_strict bits acc = Some (out, rem) ->
  dec_stream_from bits acc = Some (out, rem).
Proof.
  intros bits acc out rem H.
  exact (dec_stream_strict_fuel_weaken (S (length bits)) bits acc out rem H).
Qed.

(* ------------------------------------------------------------------ *)
(* Requirement 6 (chair, adopted from the falsifier): the supply-side  *)
(* residue and its bridge FREEZE HERE, in the guard's own packet — a   *)
(* residue spelled downstream of its consumer is premise-band drift,   *)
(* and this round has paid for that class twice.  Both are STATEMENTS  *)
(* (the round's _STMT convention); neither is consumed by the heads.   *)

(** The per-entry cap (MAXBITS).  The sort window is the reason it is
    load-bearing: [it_offs] forms only offs[1..15] (Inftrees :398 seeds
    offs[1] = 0 and fills 2..15), and [it_sort] (:194) writes
    work[offs l] for EVERY nonzero length l — an entry > 15 reads the
    zarr DEFAULT offs = 0 and clobbers the low work slots.  Every
    supplier has the cap for free: CODES lens are 3-bit header reads
    (<= 7), LENS/DISTS lens come off the CL alphabet (<= 15), q5's
    emitted lens carry MAX_BITS/MAX_BL_BITS.  Uniform (not per-arm)
    premise: the CODES arm does not need it (it_enough has no CODES
    disjunct) but every CODES supplier satisfies it, and one premise
    keeps the statement one vocabulary unit. *)
Definition lens_capped (l : list nat) : Prop :=
  forall len, In len l -> (len <= 15)%nat.

(** THE NAMED ENOUGH RESIDUE (the separately-commissioned theorem's
    frozen target; q5's wave may discharge its emitted-lens instances
    instead — same text, restricted quantifier).  The loop from an
    accepted pre-state never overflows the machine's table budget.
    The CT_CODES arm is TRIVIAL by the it_enough CODES exemption
    (Inftrees :106 — no CODES disjunct, identically false) and is kept
    for call-shape uniformity.

    AMENDED r4 (2026-08-21, owner g1 + q6 ruling on g6's falsifier):
    the r3 text (pin , no entry cap) is FALSE — witness
    [1;2;2;47;47] at the LENS arm is kraft-invisible but sort-visible
    (the band capped [length l], never l's ENTRIES).  Machine-checked:
    g6's stmt_falsifier (FalsProbe.v , EnoughFitsDesign.v
    ) + the owner reproduction against the landed name
    (TreeFals.v , tree_stmt_falsifier, PA closed).  Repair =
    the [lens_capped] premise, spelled exactly as g6's
    EnoughFits_capped_STMT so their Tier-A pack re-points by name
    only.  [build_accepts_of_kraft_STMT] below carries its own
    per-arm entry caps (the sort window was never open there); its
    <=1 arm was SEPARATELY falsified and repaired in this same
    revision — kill #6, see its own AMENDED r4 note. *)
Definition EnoughFits_STMT : Prop :=
  forall ty (l : list nat) root0 c st,
    (ty = CT_CODES /\ (length l <= 19)%nat /\ root0 = 7
     \/ ty = CT_LENS /\ (length l <= 286)%nat /\ root0 = 9
     \/ ty = CT_DISTS /\ (length l <= 30)%nat /\ root0 = 6) ->
    lens_capped l ->
    it_pre ty (lens_of_list l) (Z.of_nat (length l)) root0 tnone
      = PreGo c st ->
    forall n t, it_loop n c st <> Some (ItOverflow t).

(** THE CHARACTERIZATION BRIDGE (machine-side; the one new lemma of the
    (c) layering — its body is expected from the landed staged-build
    corpus + GtItTotal's totality; g1 owns the proof, LATER PIECE):
    q5's kraft facts + the residue imply the guard.  The kraft premises
    are spelled EXACTLY as round 2's A2/A3/A4 (q5's citation check is
    GREEN against those shapes, and this bridge is what keeps their
    supply kraft-shaped under the (c) guard).

    AMENDED r4 (2026-08-21, owner g1; caught in the owner's own
    pre-grind enumeration, sixth premise-band kill): the r3 LENS/DISTS
    incomplete arm [forall len, In len l -> len <= 1] spelled zlib's
    "at most one CODE" class (inftrees.c's max==1/left>0 allowance) as
    "all LENGTHS <= 1" — witness [1;1;1]: cnt[1] = 3 over-subscribes,
    it_kraft = None, PreErr, ret -1, while the residue INSTANCE holds
    vacuously (no PreGo).  Machine-checked: TreeFals2.v ,
    bridge_stmt_falsifier, PA closed.  Repair: the arm gains the
    at-most-one-1-entry conjunct (filter spelling, no new imports);
    q5's degenerate supplies (zero or one distance code) satisfy it
    definitionally. *)
Definition build_accepts_of_kraft_STMT : Prop :=
  forall ty (l : list nat) root0,
    (ty = CT_CODES /\ (length l <= 19)%nat /\ root0 = 7
       /\ (kraft_sum l 7 = 2 ^ 7)%nat
       /\ (forall len, In len l -> (len <= 7)%nat)
     \/ ty = CT_LENS /\ (length l <= 286)%nat /\ root0 = 9
       /\ ((kraft_sum l 15 = 2 ^ 15)%nat
           \/ ((forall len, In len l -> (len <= 1)%nat)
               /\ (length (filter (Nat.eqb 1%nat) l) <= 1)%nat))
       /\ (forall len, In len l -> (len <= 15)%nat)
     \/ ty = CT_DISTS /\ (length l <= 30)%nat /\ root0 = 6
       /\ ((kraft_sum l 15 = 2 ^ 15)%nat
           \/ ((forall len, In len l -> (len <= 1)%nat)
               /\ (length (filter (Nat.eqb 1%nat) l) <= 1)%nat))
       /\ (forall len, In len l -> (len <= 15)%nat)) ->
    (* the residue INSTANCE at this l (q6 req-6 pass recommendation:
       the global EnoughFits_STMT composes only for the commission
       route; the instance serves BOTH the universal theorem (trivial
       specialization) and q5's emitted-lens discharges directly) *)
    (forall c st,
        it_pre ty (lens_of_list l) (Z.of_nat (length l)) root0 tnone
          = PreGo c st ->
        forall n t, it_loop n c st <> Some (ItOverflow t)) ->
    build_accepts_b ty l root0 = true.

Set Printing Width 2000.
Print Assumptions it_step_tbl_ext.
Print Assumptions it_loop_tbl_ext.
Print Assumptions it_model_tbl_ext.
Print Assumptions decode_dynamic_tables_strict_weaken.
Print Assumptions dec_blk_strict_weaken.
Print Assumptions dec_stream_strict_fuel_weaken.
Print Assumptions dec_stream_from_strict_weaken.
