(* SPDX-License-Identifier: MIT *)
(* Made from spirv-tools/spvtools_binary_parser_fuzzer's bpA/Start/AsPlanRegen.v (itself made from
   double-conversion/string_to_double_fuzzer's PlanRegen.v), over this unit's plan and state types
   (Common/AsanPlan.v [plan], Common/AsanPlanCore.v [acs]).

   A recorded plan's variable renumbering, as a total increasing function applied where the plan is
   checked, so a recorded plan is never rewritten by hand.  LPS 727298f3 gives the launch one more plan
   variable ([V_GID], NX0 14 -> 15) and more of the auxv to read, so the runs allocate their fresh
   variables at other numbers than the runs the recorded plans were written against.  The map is read
   off the new run (a probe that stops the run where the plan names a variable and prints the state),
   never chosen.

   WHICH plan fields are variables, read from [AsanPlan.check]'s arms: PBump m ([node_bump] compares it
   with [nxt]), PLoop J, PLoopAuto J, PVia lo, PBand v and PDiamondBand v ([band_var]: 0 = read from a0,
   otherwise a variable), both sides of PRename m; every embedded expr, kentry and state.  Every other
   nat field stays: registers (PFresh r, PHavoc rs, the [rs] of the diamonds, [lr_hav]), widths, map
   and list indices, ids, depths and counts.
   SOUNDNESS DOES NOT REST ON THIS CLASSIFICATION: a certificate vm_computes through [psh] and re-checks
   the shifted plan; a wrong map or classification can only make a certificate fail. *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import AxSymExec3 AsanPlanCore AsanPlan.
Import ListNotations. Import AX2. Import APC. Import AP.

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
  Definition amsh (m : amap) : amap := AM (esh (am_base m)) (esh (am_len m)) (am_kind m).
  Definition fdsh (d : afd) : afd :=
    match d with FdFile k len off => FdFile k (esh len) (esh off) | _ => d end.
  Definition sesh (s : sentry) : sentry := SE (sash (e_addr s)) (e_width s) (esh (e_val s)).
  (* a state's renumbering; its fresh counter moves with the map *)
  Definition ash (cs : acs) : acs :=
    let ss := a_ss cs in
    ACS (SSR (s_pc ss) (map esh (s_regs ss)) (map sesh (s_log ss)) (map ksh (s_know ss)) (f (s_next ss))
             (option_map sash (s_resv ss)))
        (map amsh (a_maps cs)) (a_totsz cs) (a_ylo cs) (a_eager cs) (map pesh (a_vis cs))
        (map pesh (a_ghost cs)) (a_abytes cs) (esh (a_brk cs)) (fdsh (a_fd cs)) (a_tidset cs).
  Definition lrsh (r : lrecipe) : lrecipe :=
    LR (lr_hav r) (map (fun q => (fst q, esh (snd q))) (lr_regs r))
       (map (fun c => let '(b, off, w, v) := c in (esh b, off, w, esh v)) (lr_cells r))
       (map esh (lr_dropb r)).

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
    | PMmap k1 k2 => PMmap (psh k1) (psh k2)
    | PMmapIn k1 k2 k3 => PMmapIn (psh k1) (psh k2) (psh k3)
    | PMprotect k1 k2 => PMprotect (psh k1) (psh k2)
    | PBrk2 k1 k2 => PBrk2 (psh k1) (psh k2)
    | PX x args k => PX x (map esh args) (psh k)
    | PExt id args k => PExt id (map esh args) (psh k)
    | PEmit id args k => PEmit id (map esh args) (psh k)
    | PExt2 id args k1 k2 => PExt2 id (map esh args) (psh k1) (psh k2)
    | PLoop J N inv body k => PLoop (f J) (esh N) (ash inv) (psh body) (psh k)
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
    | PVia j js lo karms k => PVia j (ash js) (f lo) (psh karms) (psh k)
    | PMerge j => PMerge j
    | PAbstractCell b n k => PAbstractCell (esh b) n (psh k)
    | PHavocWords bs k => PHavocWords (map esh bs) (psh k)
    | PRespell r e k => PRespell r (esh e) (psh k)
    | PMmapInH k1 k2 k3 => PMmapInH (psh k1) (psh k2) (psh k3)
    | PJoinX b off n k => PJoinX (esh b) off n (psh k)
    | PDiamondT joinpc depth rs k => PDiamondT joinpc depth rs (psh k)
    | PBand v k1 k2 => PBand (f v) (psh k1) (psh k2)
    | PIntroG lo hi n k => PIntroG lo hi n (psh k)
    | PDiamondDisj b1 b2 joinpc rs k => PDiamondDisj (esh b1) (esh b2) joinpc rs (psh k)
    | PDiamondTX joinpc depth rs R k => PDiamondTX joinpc depth rs R (psh k)
    | PGcDisj live k => PGcDisj (map esh live) (psh k)
    | PGcRangeAuto k => PGcRangeAuto (psh k)
    | PLoopAuto J N r body k => PLoopAuto (f J) (esh N) (lrsh r) (psh body) (psh k)
    | PDiamondBand v joinpc depth rs k => PDiamondBand (f v) joinpc depth rs (psh k)
    end.
End Shift.

(** the step map: variables at or above [b] move up by [d]; the launch variables below [b] stay *)
Definition vshift (b d : nat) (v : nat) : nat := if Nat.ltb v b then v else (v + d)%nat.
