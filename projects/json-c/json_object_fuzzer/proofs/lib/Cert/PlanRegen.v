(* SPDX-License-Identifier: MIT *)
(* Made from projects/yajl-ruby/json_fuzzer/proofs/lib/XQ/PlanRegen.v (itself made from
   projects/cjson/cjson_read_fuzzer/proofs/lib/AS/PlanRegen.v, projects/jsoncons/fuzz_bigint/proofs/lib/PlanRegenK.v
   and projects/double-conversion/string_to_double_fuzzer/proofs/lib/PlanRegen.v), over this unit's plan and
   state types: the LPS 727298f3 start-up certificate data computed in the build.

   1. [psh f]: a plan's variable renumbering, a total function applied where the plan is checked, so a
   recorded plan is not rewritten by hand.  LPS 727298f3 gives the launch two more plan variables
   ([V_G] = 11 and [V_GID] = 12; NX0 11 -> 13) and more of the auxv to read, so the start-up run adds its
   fresh variables at other numbers than the run the recorded plans were written against.  Each map is
   read off the new run (its state where the plan names a variable), never chosen.

   WHICH plan fields are variables: read from [QOTP.AP.check]'s arms -- PBump m, PLoop J, PRename m (both
   sides), PVia lo; every embedded expr and kentry.  Every other nat field stays: registers (PHavoc,
   PFresh, PDiamond, PRespell), list indices (PForget, PFog, PFogNew), ids (PExt, PEmit, PExt2, PHandoff,
   PMerge, PVia j), counts (PJoin, PHavocBig).  The states written inside PLoop and PVia are left alone.
   SOUNDNESS DOES NOT REST ON THIS CLASSIFICATION: the certificates vm_compute through [psh] and re-check
   the resulting plan; a wrong map or classification can only make a certificate fail.

   2. The hand-off states are computed by this unit's own collector, [QOTP.AP.collect] (the check's run,
   handing every state it reaches at a hand-off the table has no state for to a list) and [QOTP.AP.HS_of]
   (the meet, [acs_meet], of every state collected at one hand-off): one run with the empty table collects
   every hand-off state.  A state computed this way is a definition, not an assumption: the certificate
   that names it re-runs [check], which must entail it at every hand-off it reaches. *)
From Stdlib Require Import ZArith NArith List.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt8n QDlz QOTP.
Import ListNotations. Import Qt8n. Import QDlz. Import QOTP. Import AX2. Import APC. Import AP.

Section Shift.
  Variable f : nat -> nat.

  Fixpoint esh (e : expr) : expr :=
    match e with
    | ELit _ => e
    | EVar v => EVar (f v)
    | EAlu op a b => EAlu op (esh a) (esh b)
    | EAluw op a b => EAluw op (esh a) (esh b)
    | EMd op a b => EMd op (esh a) (esh b)
    | EMdw op a b => EMdw op (esh a) (esh b)
    | EExt sx lo n a => EExt sx lo n (esh a)
    | EBlob _ _ _ _ => e
    end.
  Definition sash (a : saddr) : saddr := SA (esh (a_base a)) (a_off a).
  Definition ksh (K : kentry) : kentry :=
    match K with
    | KWord a w v => KWord (sash a) w (esh v)
    | KZero a n => KZero (sash a) (esh n)
    | KBlob a n k => KBlob (sash a) (esh n) k
    | KImg _ _ => K
    | KAlign x m => KAlign (esh x) m
    | KRange x lo hi => KRange (esh x) lo hi
    | KWr a n => KWr (sash a) (esh n)
    | KDisj a1 n1 a2 n2 => KDisj (sash a1) (esh n1) (sash a2) (esh n2)
    | KFill a n c => KFill (sash a) (esh n) c
    | KUnk a n => KUnk (sash a) (esh n)
    end.
  Definition pesh (p : expr * expr) : expr * expr := (esh (fst p), esh (snd p)).

  Fixpoint psh (p : plan) : plan :=
    match p with
    | PRun stops k => PRun stops (psh k)
    | PSplit e mid k1 k2 => PSplit (esh e) mid (psh k1) (psh k2)
    | PCase2 e mid k1 k2 => PCase2 (esh e) mid (psh k1) (psh k2)
    | PCaseDisj b1 b2 k1 k2 => PCaseDisj (esh b1) (esh b2) (psh k1) (psh k2)
    | PShDisj b1 n1 b2 n2 k => PShDisj (esh b1) (esh n1) (esh b2) (esh n2) (psh k)
    | PContra => PContra
    | PFact K k => PFact (ksh K) (psh k)
    | PJoin b off n k => PJoin (esh b) off n (psh k)
    | PForget ixs k => PForget ixs (psh k)
    | PDropRange b n k => PDropRange (esh b) (esh n) (psh k)
    | PGcKeep ws k => PGcKeep (map pesh ws) (psh k)
    | PBump m k => PBump (f m) (psh k)
    | PHavoc rs k => PHavoc rs (psh k)
    | PHavocBig K k => PHavocBig K (psh k)
    | PFresh r logc base k => PFresh r logc (option_map esh base) (psh k)
    | PSys y k => PSys y (psh k)
    | PMmap ka kb => PMmap (psh ka) (psh kb)
    | PMmapIn ka kb kc => PMmapIn (psh ka) (psh kb) (psh kc)
    | PMprotect ka kb => PMprotect (psh ka) (psh kb)
    | PBrk2 ka kb => PBrk2 (psh ka) (psh kb)
    | PX x args k => PX x (map esh args) (psh k)
    | PExt id args k => PExt id (map esh args) (psh k)
    | PEmit id args k => PEmit id (map esh args) (psh k)
    | PExt2 id args k1 k2 => PExt2 id (map esh args) (psh k1) (psh k2)
    | PLoop J N inv body k => PLoop (f J) (esh N) inv (psh body) (psh k)
    | PNext => PNext
    | PHandoff h => PHandoff h
    | PExit => PExit
    | PSpin => PSpin
    | PFog i sz k => PFog i sz (psh k)
    | PFogNew i sz k => PFogNew i sz (psh k)
    | PGhost b n k => PGhost (esh b) (esh n) (psh k)
    | PUnvis b n k => PUnvis (esh b) (esh n) (psh k)
    | PHavocBrk lo hi k => PHavocBrk lo hi (psh k)
    | PIntro lo hi k => PIntro lo hi (psh k)
    | PDiamond joinpc rs k => PDiamond joinpc rs (psh k)
    | PRename m k => PRename (map (fun q => (f (fst q), f (snd q))) m) (psh k)
    | PCompact k => PCompact (psh k)
    | PVia j js lo karms k => PVia j js (f lo) (psh karms) (psh k)
    | PMerge j => PMerge j
    | PAbstractCell b n k => PAbstractCell (esh b) n (psh k)
    | PHavocWords bs k => PHavocWords (map esh bs) (psh k)
    | PRespell r e k => PRespell r (esh e) (psh k)
    | PMmapInH ka kb kc => PMmapInH (psh ka) (psh kb) (psh kc)
    end.
End Shift.

(* A map given as a table read off the new run: ascending thresholds [(t, d)] in the OLD numbering; an old
   variable [v] moves by the [d] of the last [t <= v], and by 0 below the first threshold.  A threshold
   with [d = 0] after a moving one is a point where the recorded plan resets the counter ([PBump]), so the
   old variables just below it that the recorded run never made need not map below it. *)
Fixpoint tbl_d (tbl : list (nat * nat)) (v acc : nat) : nat :=
  match tbl with [] => acc | (t, d) :: r => if Nat.leb t v then tbl_d r v d else acc end.
Definition tshift (tbl : list (nat * nat)) (v : nat) : nat := (v + tbl_d tbl v 0)%nat.

(* the result shape of a run, or [SNil] when it refuses *)
Definition shape_of (c : cres) : shape := match c with COk s => s | CErr _ _ _ => SNil end.

(* what a collecting run keeps: the meets at two hand-offs, and the run's shape *)
Definition coll2 (c : cres2) (h1 h2 : nat) : option acs * option acs * shape :=
  (HS_of (snd c) h1, HS_of (snd c) h2, shape_of (fst c)).
(* a collected hand-off state, or [d] when the run never reached that hand-off (then the
   certificate's own check fails there) *)
Definition hs_or (o : option acs) (d : acs) : acs := match o with Some c => c | None => d end.
