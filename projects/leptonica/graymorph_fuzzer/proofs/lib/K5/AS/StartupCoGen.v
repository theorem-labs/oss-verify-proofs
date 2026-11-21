(* SPDX-License-Identifier: MIT *)
(* Theorem Labs, 2026-11 (LPS 75d69e00): THE START-UP'S JOIN AND HAND-OFF TABLES, COMPUTED.

   LPS 75d69e00 leaves [kb_rseq] free ([Run.recorded_kernel], Run.v:4575-4581), so the initial
   knowledge is one state per CONFIG_RSEQ value ([AsanPlanCore.init_kn_with r]) and the recorded
   join ([js_j]) and hole ([HS_*]) tables, collected over one older initial state, no longer
   describe either run.  Instead of recording new literals, each image's tables are COMPUTED
   from its own start state by the loop below, and the certificate re-checks them.

   [lsub J p] puts [J j] where [p] has [PVia j js ...], so the shipped plan term is used
   unedited.  [gc_go chk dflt n J H] runs [chk H J] (one image's [check] call over the hole table
   [H] and the join-state table [J]) at most [n] times: a refusal (code 3) at [PMerge j] or at
   [PHandoff h], or a missing hole (code 4), records the arriving state at that entry the first
   time and meets it into the entry afterwards (the knowledge facts common to both; the first
   arrival's registers, maps and pc); any other stop ends the run.  Only [COk] returns a shape.

   NOTHING HERE IS TRUSTED.  A table is a value; the certificate
   [check .. (gc_get (go_H R)) .. init (lsub (gc_jget (go_J R) dflt) plan) = COk s] is what is
   proved, by computation, and a wrong table can only make it fail.

   Design: a number-indexed collector, in the shape of openssl/pem's shipped
   Start/PlanCoGen.v. *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.AS Require Import AxSymExec3 AsanPlanCore AsanPlan.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

(* every [PVia j js ..]'s join state replaced by [J j]; the other nodes are rebuilt unchanged *)
Fixpoint lsub (J : nat -> acs) (p : plan) {struct p} : plan :=
  match p with
  | PRun x0 x1 => PRun x0 (lsub J x1)
  | PSplit x0 x1 x2 x3 => PSplit x0 x1 (lsub J x2) (lsub J x3)
  | PCase2 x0 x1 x2 x3 => PCase2 x0 x1 (lsub J x2) (lsub J x3)
  | PCaseDisj x0 x1 x2 x3 => PCaseDisj x0 x1 (lsub J x2) (lsub J x3)
  | PShDisj x0 x1 x2 x3 x4 => PShDisj x0 x1 x2 x3 (lsub J x4)
  | PContra => PContra
  | PFact x0 x1 => PFact x0 (lsub J x1)
  | PJoin x0 x1 x2 x3 => PJoin x0 x1 x2 (lsub J x3)
  | PForget x0 x1 => PForget x0 (lsub J x1)
  | PDropRange x0 x1 x2 => PDropRange x0 x1 (lsub J x2)
  | PGcKeep x0 x1 => PGcKeep x0 (lsub J x1)
  | PBump x0 x1 => PBump x0 (lsub J x1)
  | PHavoc x0 x1 => PHavoc x0 (lsub J x1)
  | PHavocBig x0 x1 => PHavocBig x0 (lsub J x1)
  | PFresh x0 x1 x2 x3 => PFresh x0 x1 x2 (lsub J x3)
  | PSys x0 x1 => PSys x0 (lsub J x1)
  | PMmap x0 x1 => PMmap (lsub J x0) (lsub J x1)
  | PMmapIn x0 x1 x2 => PMmapIn (lsub J x0) (lsub J x1) (lsub J x2)
  | PMprotect x0 x1 => PMprotect (lsub J x0) (lsub J x1)
  | PBrk2 x0 x1 => PBrk2 (lsub J x0) (lsub J x1)
  | PX x0 x1 x2 => PX x0 x1 (lsub J x2)
  | PExt x0 x1 x2 => PExt x0 x1 (lsub J x2)
  | PEmit x0 x1 x2 => PEmit x0 x1 (lsub J x2)
  | PExt2 x0 x1 x2 x3 => PExt2 x0 x1 (lsub J x2) (lsub J x3)
  | PLoop x0 x1 x2 x3 x4 => PLoop x0 x1 x2 (lsub J x3) (lsub J x4)
  | PNext => PNext
  | PHandoff x0 => PHandoff x0
  | PExit => PExit
  | PSpin => PSpin
  | PFog x0 x1 x2 => PFog x0 x1 (lsub J x2)
  | PFogNew x0 x1 x2 => PFogNew x0 x1 (lsub J x2)
  | PGhost x0 x1 x2 => PGhost x0 x1 (lsub J x2)
  | PUnvis x0 x1 x2 => PUnvis x0 x1 (lsub J x2)
  | PHavocBrk x0 x1 x2 => PHavocBrk x0 x1 (lsub J x2)
  | PIntro x0 x1 x2 => PIntro x0 x1 (lsub J x2)
  | PDiamond x0 x1 x2 => PDiamond x0 x1 (lsub J x2)
  | PRename x0 x1 => PRename x0 (lsub J x1)
  | PCompact x0 => PCompact (lsub J x0)
  | PVia x0 _ x2 x3 x4 => PVia x0 (J x0) x2 (lsub J x3) (lsub J x4)
  | PMerge x0 => PMerge x0
  | PAbstractCell x0 x1 x2 => PAbstractCell x0 x1 (lsub J x2)
  | PHavocWords x0 x1 => PHavocWords x0 (lsub J x1)
  | PRespell x0 x1 x2 => PRespell x0 x1 (lsub J x2)
  | PMmapInH x0 x1 x2 => PMmapInH (lsub J x0) (lsub J x1) (lsub J x2)
  | PHavocCell x0 x1 x2 => PHavocCell x0 x1 (lsub J x2)
  | PBrk2S x0 x1 => PBrk2S (lsub J x0) (lsub J x1)
  | PCaseDisjJ x0 x1 x2 x3 x4 => PCaseDisjJ x0 x1 x2 x3 (lsub J x4)
  | PFreshAnd x0 x1 => PFreshAnd x0 (lsub J x1)
  | PVisSlice x0 x1 x2 => PVisSlice x0 x1 (lsub J x2)
  | PKWrJoin x0 x1 x2 x3 x4 x5 x6 => PKWrJoin x0 x1 x2 x3 x4 x5 (lsub J x6)
  | PIntroW x0 x1 x2 => PIntroW x0 x1 (lsub J x2)
  end.

(* an arriving state with its store log and reservation dropped *)
Definition cg_clean (c : acs) : acs :=
  let s := a_ss c in
  ACS (SSR (s_pc s) (s_regs s) [] (s_know s) (s_next s) None) (a_maps c) (a_totsz c) (a_ylo c) (a_eager c)
      (a_vis c) (a_ghost c) (a_abytes c) (a_brk c) (a_fd c) (a_tidset c).
(* the meet: the facts of [c0] that [c] also has; the ledger bounds widened to cover both *)
Definition cg_meet (c0 c : acs) : acs :=
  let s := a_ss c0 in
  ACS (SSR (s_pc s) (s_regs s) [] (List.filter (fun K => existsb (kentry_eqb K) (kn c)) (s_know s)) (s_next s) None)
      (a_maps c0) (Z.max (a_totsz c0) (a_totsz c)) (Z.min (a_ylo c0) (a_ylo c)) (Z.max (a_eager c0) (a_eager c))
      (a_vis c0) (a_ghost c0) (Z.max (a_abytes c0) (a_abytes c)) (a_brk c0) (a_fd c0) (a_tidset c0).
Definition cg_tag (p : plan) : Z :=
  match p with PMerge j => 1000000 + Z.of_nat j | PHandoff h => 100000 + Z.of_nat h | PExt id _ _ => Z.of_nat id | _ => -1 end.

(* a table: (index, state, met at least once) *)
Definition gtab := list (nat * acs * bool).
Fixpoint gc_get (t : gtab) (i : nat) : option acs :=
  match t with [] => None | (j, c, _) :: r => if Nat.eqb i j then Some c else gc_get r i end.
Fixpoint gc_seen (t : gtab) (i : nat) : bool :=
  match t with [] => false | (j, _, b) :: r => if Nat.eqb i j then b else gc_seen r i end.
Fixpoint gc_put (t : gtab) (i : nat) (c : acs) : gtab :=
  match t with
  | [] => [(i, c, true)]
  | (j, c0, b) :: r => if Nat.eqb i j then (j, c, true) :: r else (j, c0, b) :: gc_put r i c
  end.
Definition gc_absorb (t : gtab) (i : nat) (cs : acs) : gtab :=
  if gc_seen t i then match gc_get t i with Some c0 => gc_put t i (cg_meet c0 cs) | None => gc_put t i (cg_clean cs) end
  else gc_put t i (cg_clean cs).
Definition gc_jget (J : gtab) (dflt : acs) (j : nat) : acs := match gc_get J j with Some c => c | None => dflt end.

Record gc_out := GCO { go_log : list (Z * Z * Z * Z); go_J : gtab; go_H : gtab; go_shape : option shape }.
Fixpoint gc_go (chk : (nat -> option acs) -> (nat -> acs) -> cres) (dflt : acs) (n : nat) (J H : gtab)
         (log : list (Z * Z * Z * Z)) : gc_out :=
  match n with
  | O => GCO (rev log) J H None
  | S n' =>
    match chk (gc_get H) (gc_jget J dflt) with
    | COk s => GCO (rev ((0, 0, 0, 0) :: log)) J H (Some s)
    | CErr c w cs =>
        let row := (c, s_pc (a_ss cs), cg_tag w, Z.of_nat (nxt cs)) in
        if (Z.eqb c 3 || Z.eqb c 4)%bool then
          match w with
          | PMerge j => gc_go chk dflt n' (gc_absorb J j cs) H (row :: log)
          | PHandoff h => gc_go chk dflt n' J (gc_absorb H h cs) (row :: log)
          | _ => GCO (rev (row :: log)) J H None
          end
        else GCO (rev (row :: log)) J H None
    end
  end.

(* THE HAND-OFF TABLE, COLLECTED UNDER THE FINAL JOIN TABLE ONLY.  [check] runs a [PVia]'s
   continuation from its join state BEFORE its arms, so until an arm's first refusal at [PMerge j]
   replaces the recorded seed [J j], the continuation runs from that seed, which was collected over
   the older initial state, and the hand-offs it reaches are recorded from it.  [gc_go] then meets
   every later arrival into those entries, and the meet keeps only the facts the old state and the
   new one spell alike.  At LPS 727298f3 the stack window's [KWr] (8 MiB then, the model's
   [StoreOk.stack_window_depth] bytes now) and argv[0]'s word at sp0 + 8 (the strings now sit above
   the AT_RANDOM bytes) are not among them, so every hand-off state lost them.  [gc_go2] runs
   [gc_go] once for the join table and then again over that join table with an empty hole table:
   the first run ended in [COk] with that join table and no merge reads the hole table, so the
   second run's hand-off states come from runs from the given start state only.  Its log is the two
   runs' logs, the first ending in the [(0, 0, 0, 0)] row. *)
Definition gc_go2 (chk : (nat -> option acs) -> (nat -> acs) -> cres) (dflt : acs) (n : nat) (J : gtab) : gc_out :=
  let R := gc_go chk dflt n J [] [] in
  match go_shape R with
  | Some _ => let R2 := gc_go chk dflt n (go_J R) [] [] in GCO (go_log R ++ go_log R2) (go_J R2) (go_H R2) (go_shape R2)
  | None => R
  end.

(* the shape a run returned, or a hole no plan reaches (so a failed run cannot certify) *)
Definition gc_shape (R : gc_out) : shape := match go_shape R with Some s => s | None => SHole 999999 end.

(* every state in a table passes a boolean test, and so does each one [gc_get] returns *)
Lemma gc_get_forallb : forall (P : acs -> bool) (t : gtab) i c,
  forallb (fun e => P (snd (fst e))) t = true -> gc_get t i = Some c -> P c = true.
Proof.
  intros P t i c. induction t as [|[[j c0] b] r IH]; cbn [gc_get forallb]; [discriminate|].
  intros Hall Hg. apply andb_prop in Hall as [H1 H2].
  destruct (Nat.eqb i j); [injection Hg as <-; exact H1 | exact (IH H2 Hg)].
Qed.
