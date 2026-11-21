(* SPDX-License-Identifier: MIT *)
(* The main side's variable renumbering, as a TOTAL FUNCTION applied to the
   main-side data where it is defined, so no encoded table is re-encoded.

   WHY: the main-side data (plans, template states) is numbered for NX0 = 9, with post-renamed variables
   9..44 and fresh variables from 45; under coturn's NX0 = 11 (V_G 9, V_GID 10) the post-renamed variables
   are 11..46, three image-data value variables take 47..49, and main's fresh variables start at 50
   (PostPlan{Asan,Both}.v's PRename).
   So every variable literal the main plans and main template states carry moves by
       v < 9  ->  v        (globals, unchanged)
       9..44  ->  v + 2    (the renamed post variables, order kept)
       v >= 45 -> v + 5    (main's own fresh variables, a translation, so every fresh-allocation offset is kept).
   The map is strictly monotone, so every "v < nx" / range fact the checker tests is preserved.

   WHICH plan fields are variables, read from AsanPlan.check's arms (each passes the nat through vN / vNm into a
   variable position): PBump m (node_bump's next-variable bound), PLoop J (the loop counter variable), PRename m
   (both sides), PVia lo (the join's variable floor), PKeep vs (the live variables), PHandoffM m (both sides).
   Every other nat field stays, each read from its arm: PHavoc rs, PFresh r, PSrlSplit / PSrlSplitAll / PAndRange /
   PAndRangeR / PRespell r, PCaseNJ / PCaseDisjJ / PDiamond rs = registers; PForget ixs = knowledge-list indices;
   PFog / PFogNew / PDisjNth i, PVisPerm perm = vis / list indices; PExt / PEmit / PExt2 id = external ids;
   PHandoff h, PMerge j, PVia j = hole / join ids; PJoin n, PFreshCell / PFreshCellK n, PHavocBig K = counts.
   Every embedded expr / kentry is shifted. The two embedded STATES (PVia js, PLoop inv) are NOT: in every main plan
   they are references to named states (plain plans by name; PlanCodec's pc_acs only reads pe_acs, never an inline
   state). Those named template states are NOT shifted either: they were collected under the released layout and
   carry its facts, so they are re-collected per r by MainCol's collector, which seeds each one with [ash] of the
   old state and replaces it by its arrivals. [ash] is that seed and nothing else. Plans are shifted once, where
   they are checked ([psh p]).
   SOUNDNESS DOES NOT REST ON THIS CLASSIFICATION: the main certificates vm_compute through these functions and
   re-check the shifted data; a wrong classification can only make a certificate red. *)
From Stdlib Require Import ZArith NArith List.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlanCore AsanPlan.
Import ListNotations. Import AX2. Import AP.
Open Scope N_scope.

Definition vsh (v : N) : N := if N.ltb v 9 then v else if N.ltb v 45 then v + 2 else v + 5.
Definition vshn (n : nat) : nat := N.to_nat (vsh (N.of_nat n)).

Fixpoint esh (e : expr) : expr :=
  match e with
  | ELit _ => e
  | EVar v => EVar (vsh v)
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
  | KPriv tg rs args k => KPriv tg (map (fun r => (sash (fst r), esh (snd r))) rs) (map esh args) k
  end.
Definition pesh (p : expr * expr) : expr * expr := (esh (fst p), esh (snd p)).
Definition msh (m : amap) : amap := AM (esh (am_base m)) (esh (am_len m)) (am_kind m).
Definition fdsh (f : afd) : afd := match f with FdFile k l o => FdFile k (esh l) (esh o) | _ => f end.
Definition sesh (x : sentry) : sentry := SE (sash (e_addr x)) (e_width x) (esh (e_val x)).
Definition ssh (ss : sym_state) : sym_state :=
  SSR (s_pc ss) (map esh (s_regs ss)) (map sesh (s_log ss)) (map ksh (s_know ss)) (vsh (s_next ss))
      (option_map sash (s_resv ss)).
Definition ash (cs : acs) : acs :=
  ACS (ssh (a_ss cs)) (map msh (a_maps cs)) (a_totsz cs) (a_ylo cs) (a_eager cs) (map pesh (a_vis cs))
      (map pesh (a_ghost cs)) (a_abytes cs) (esh (a_brk cs)) (fdsh (a_fd cs)) (a_tidset cs).
Definition pairsh (p : nat * nat) : nat * nat := (vshn (fst p), vshn (snd p)).

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
  | PBump m k => PBump (vshn m) (psh k)
  | PHavoc rs k => PHavoc rs (psh k)
  | PHavocBig K k => PHavocBig K (psh k)
  | PFresh r logc base k => PFresh r logc (option_map esh base) (psh k)
  | PSys y k => PSys y (psh k)
  | PMmap ka kb => PMmap (psh ka) (psh kb)
  | PMmapIn a b c => PMmapIn (psh a) (psh b) (psh c)
  | PMprotect a b => PMprotect (psh a) (psh b)
  | PBrk2 a b => PBrk2 (psh a) (psh b)
  | PMunmap2 a b => PMunmap2 (psh a) (psh b)
  | PX x args k => PX x (map esh args) (psh k)
  | PExt id args k => PExt id (map esh args) (psh k)
  | PEmit id args k => PEmit id (map esh args) (psh k)
  | PExt2 id args k1 k2 => PExt2 id (map esh args) (psh k1) (psh k2)
  | PLoop J N inv body k => PLoop (vshn J) (esh N) inv (psh body) (psh k)   (* inv: a named state, shifted where defined *)
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
  | PRename m k => PRename (map pairsh m) (psh k)
  | PCompact k => PCompact (psh k)
  | PVia j js lo karms k => PVia j js (vshn lo) (psh karms) (psh k)   (* js: a named state, shifted where defined *)
  | PMerge j => PMerge j
  | PAbstractCell b n k => PAbstractCell (esh b) n (psh k)
  | PHavocWords bs k => PHavocWords (map esh bs) (psh k)
  | PRespell r e k => PRespell r (esh e) (psh k)
  | PMmapInH a b c => PMmapInH (psh a) (psh b) (psh c)
  | PCaseDisjJ b1 b2 joinpc rs k => PCaseDisjJ (esh b1) (esh b2) joinpc rs (psh k)
  | PCaseP k1 k2 => PCaseP (psh k1) (psh k2)
  | PCaseNJ e cuts joinpc rs ws k =>
      PCaseNJ (esh e) cuts joinpc rs (map (fun w => (esh (fst (fst w)), snd (fst w), snd w)) ws) (psh k)
  | PVisAbsorb b n k => PVisAbsorb (esh b) (esh n) (psh k)
  | PFreshCell b n k => PFreshCell (esh b) n (psh k)
  | PVisSplit b n d k => PVisSplit (esh b) n d (psh k)
  | PVisHead b m L k => PVisHead (esh b) m (esh L) (psh k)
  | PUnvisHead b m k => PUnvisHead (esh b) m (psh k)
  | PGhostDedup k => PGhostDedup (psh k)
  | PHavocBrkP lo hi k => PHavocBrkP lo hi (psh k)
  | PKeep ws vs k => PKeep (map pesh ws) (map vshn vs) (psh k)
  | PFactMem K k => PFactMem (ksh K) (psh k)
  | PVisRespell b n b' n' k => PVisRespell (esh b) (esh n) (esh b') (esh n') (psh k)
  | PMapRespell b n b' n' k => PMapRespell (esh b) (esh n) (esh b') (esh n') (psh k)
  | PMemRespell b lo hi b' d k => PMemRespell (esh b) lo hi (esh b') d (psh k)
  | PSrlSplit r s k => PSrlSplit r s (psh k)
  | PAndRange r logc ub k => PAndRange r logc (esh ub) (psh k)
  | PAndRangeR r logc rs k => PAndRangeR r logc rs (psh k)
  | PSrlSplitAll r s k => PSrlSplitAll r s (psh k)
  | PFdHavoc lo hi k => PFdHavoc lo hi (psh k)
  | PFreshCellK b n k => PFreshCellK (esh b) n (psh k)
  | PVisPerm perm k => PVisPerm perm (psh k)
  | PHandoffM m => PHandoffM (map pairsh m)
  | PFdRespell len off k => PFdRespell (esh len) (esh off) (psh k)
  | PDisjNth b1 n1 i k => PDisjNth (esh b1) (esh n1) i (psh k)
  | PMmapInS a b c => PMmapInS (psh a) (psh b) (psh c)
  end.

Fixpoint pseed (p : plan) : plan :=
  match p with
  | PRun stops k => PRun stops (pseed k)
  | PSplit e mid k1 k2 => PSplit e mid (pseed k1) (pseed k2)
  | PCase2 e mid k1 k2 => PCase2 e mid (pseed k1) (pseed k2)
  | PCaseDisj b1 b2 k1 k2 => PCaseDisj b1 b2 (pseed k1) (pseed k2)
  | PShDisj b1 n1 b2 n2 k => PShDisj b1 n1 b2 n2 (pseed k)
  | PContra => p
  | PFact K k => PFact K (pseed k)
  | PJoin b off n k => PJoin b off n (pseed k)
  | PForget ixs k => PForget ixs (pseed k)
  | PDropRange b n k => PDropRange b n (pseed k)
  | PGcKeep ws k => PGcKeep ws (pseed k)
  | PBump m k => PBump m (pseed k)
  | PHavoc rs k => PHavoc rs (pseed k)
  | PHavocBig K k => PHavocBig K (pseed k)
  | PFresh r logc base k => PFresh r logc base (pseed k)
  | PSys y k => PSys y (pseed k)
  | PMmap ka kb => PMmap (pseed ka) (pseed kb)
  | PMmapIn a b c => PMmapIn (pseed a) (pseed b) (pseed c)
  | PMprotect a b => PMprotect (pseed a) (pseed b)
  | PBrk2 a b => PBrk2 (pseed a) (pseed b)
  | PMunmap2 a b => PMunmap2 (pseed a) (pseed b)
  | PX x args k => PX x args (pseed k)
  | PExt id args k => PExt id args (pseed k)
  | PEmit id args k => PEmit id args (pseed k)
  | PExt2 id args k1 k2 => PExt2 id args (pseed k1) (pseed k2)
  | PLoop J0 N inv body k => PLoop J0 N (ash inv) (pseed body) (pseed k)
  | PNext => p
  | PHandoff h => p
  | PExit => p
  | PSpin => p
  | PFog i sz k => PFog i sz (pseed k)
  | PFogNew i sz k => PFogNew i sz (pseed k)
  | PGhost b n k => PGhost b n (pseed k)
  | PUnvis b n k => PUnvis b n (pseed k)
  | PHavocBrk lo hi k => PHavocBrk lo hi (pseed k)
  | PIntro lo hi k => PIntro lo hi (pseed k)
  | PDiamond joinpc rs k => PDiamond joinpc rs (pseed k)
  | PRename m k => PRename m (pseed k)
  | PCompact k => PCompact (pseed k)
  | PVia j js lo karms k => PVia j (ash js) lo (pseed karms) (pseed k)
  | PMerge j => p
  | PAbstractCell b n k => PAbstractCell b n (pseed k)
  | PHavocWords bs k => PHavocWords bs (pseed k)
  | PRespell r e k => PRespell r e (pseed k)
  | PMmapInH a b c => PMmapInH (pseed a) (pseed b) (pseed c)
  | PCaseDisjJ b1 b2 joinpc rs k => PCaseDisjJ b1 b2 joinpc rs (pseed k)
  | PCaseP k1 k2 => PCaseP (pseed k1) (pseed k2)
  | PCaseNJ e cuts joinpc rs ws k => PCaseNJ e cuts joinpc rs ws (pseed k)
  | PVisAbsorb b n k => PVisAbsorb b n (pseed k)
  | PFreshCell b n k => PFreshCell b n (pseed k)
  | PVisSplit b n d k => PVisSplit b n d (pseed k)
  | PVisHead b m L k => PVisHead b m L (pseed k)
  | PUnvisHead b m k => PUnvisHead b m (pseed k)
  | PGhostDedup k => PGhostDedup (pseed k)
  | PHavocBrkP lo hi k => PHavocBrkP lo hi (pseed k)
  | PKeep ws vs k => PKeep ws vs (pseed k)
  | PFactMem K k => PFactMem K (pseed k)
  | PVisRespell b n b' n' k => PVisRespell b n b' n' (pseed k)
  | PMapRespell b n b' n' k => PMapRespell b n b' n' (pseed k)
  | PMemRespell b lo hi b' d k => PMemRespell b lo hi b' d (pseed k)
  | PSrlSplit r s k => PSrlSplit r s (pseed k)
  | PAndRange r logc ub k => PAndRange r logc ub (pseed k)
  | PAndRangeR r logc rs k => PAndRangeR r logc rs (pseed k)
  | PSrlSplitAll r s k => PSrlSplitAll r s (pseed k)
  | PFdHavoc lo hi k => PFdHavoc lo hi (pseed k)
  | PFreshCellK b n k => PFreshCellK b n (pseed k)
  | PVisPerm perm k => PVisPerm perm (pseed k)
  | PHandoffM m => p
  | PFdRespell len off k => PFdRespell len off (pseed k)
  | PDisjNth b1 n1 i k => PDisjNth b1 n1 i (pseed k)
  | PMmapInS a b c => PMmapInS (pseed a) (pseed b) (pseed c)
  end.

(* The two states a plan embeds, the join state of [PVia] and the loop invariant of [PLoop], are left by [psh] as
   they were written (under the released numbering). [pseed] renumbers them by [ash], so a plan whose join or
   invariant the collector never had to replace still meets its own states in the new numbering; where the
   collector does replace a join ([MainCol.pjs]) that replacement wins. *)
Definition pshj (p : plan) : plan := pseed (psh p).
