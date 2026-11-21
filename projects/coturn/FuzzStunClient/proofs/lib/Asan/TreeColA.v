(* SPDX-License-Identifier: MIT *)
(* coturn MAIN TREE COLLECTOR, image A: TreeColB.v with image A's glue (MainGlueDefs, MainGlue,
   TOTmplRAsan.ta_chk_with). A computation, not a proof: it proves nothing and no certificate
   depends on its correctness; a collected tree is certified afterwards by one [mtree_ok] reflection per r.

   [tcol rsb esc ch C t] walks a released main tree top-down exactly as [MainGlue.mtree_ok] does (same classes, same
   start templates: a child starts from its parent's table entry, MCase children from [mcase_lo/hi] on the scrutinee
   shifted by [esc]) and at every node runs [ncol], the per-node collector, on the node's plan renumbered by
   [VarShift.pshj]:
     a refusal (3) or a missing entry (4) at [PHandoff h]  -> the node's table entry h := arrival / meet   (as MainCol)
     the same at [PMerge j]                                 -> the plan's join state j := arrival / meet    (as MainCol)
     a refusal (3) at [PLoop J N inv body k]                -> the loop invariant is TRANSPLANTED, once ([tpl])
     anything else (a [PNext] refusal included)            -> the node stops and its rows say where.
   The output tree carries every node's collected table and its rewritten plan, so tables are per node (the tree
   checker never requires two nodes to share one).

   THE INVARIANT TRANSPLANT [tpl J inv a] (a = the state arriving at the loop head). The released invariant states
   the released stack layout in its loop-independent facts; the loop-dependent part is what the loop is about.
     - loop variable J and the invariant's pattern variables (>= J) are moved above the arrival's variables if the
       arrival reaches past J (a translation, so every offset between them is kept, and the plan's body and
       continuation are renumbered by the same map in [pinv]);
     - a register that is a pattern variable or mentions J (or a pattern variable) is the invariant's; any other
       register is the arrival's;
     - knowledge = the invariant's facts that mention J or a pattern variable ++ the arrival's facts (none of which
       can mention J or above: their variables are below the arrival's next variable <= J);
     - maps / vis / ghost / brk / tid are the arrival's, and so is fd except a loop-dependent file offset ([fdmerge]) (the checker demands them equal at entry and at every
       [PNext]); totsz / eager / abytes the larger, ylo the smaller (the checker's order at both points).
   Selection is by WHAT A FACT STATES (does it mention the loop's variables), never by a literal it contains.
   NOTHING about the transplant is trusted: the checker establishes the invariant on entry ([entails_h] at J := 0)
   and its PRESERVATION by the body (the [PNext] check at J + 1); a transplanted fact the body does not preserve is a
   [PNext] refusal, reported with its node, not weakened around. *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanMainLib AsanShape MainGlueDefs MainGlue StartupHSMainAsan ItabAsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import VarShift MainCol TOTmplRAsan.
Import ListNotations. Import AX2. Import AP.
Open Scope N_scope.

Section VSF.
  Variable f : N -> N.
  Definition vshn_f (n : nat) : nat := N.to_nat (f (N.of_nat n)).
Fixpoint esh_f (e : expr) : expr :=
  match e with
  | ELit _ => e
  | EVar v => EVar (f v)
  | EAlu op a b => EAlu op (esh_f a) (esh_f b)
  | EAluw op a b => EAluw op (esh_f a) (esh_f b)
  | EMd op a b => EMd op (esh_f a) (esh_f b)
  | EMdw op a b => EMdw op (esh_f a) (esh_f b)
  | EExt sx lo n a => EExt sx lo n (esh_f a)
  | EBlob _ _ _ _ => e
  end.
Definition sash_f (a : saddr) : saddr := SA (esh_f (a_base a)) (a_off a).
Definition ksh_f (K : kentry) : kentry :=
  match K with
  | KWord a w v => KWord (sash_f a) w (esh_f v)
  | KZero a n => KZero (sash_f a) (esh_f n)
  | KBlob a n k => KBlob (sash_f a) (esh_f n) k
  | KImg _ _ => K
  | KAlign x m => KAlign (esh_f x) m
  | KRange x lo hi => KRange (esh_f x) lo hi
  | KWr a n => KWr (sash_f a) (esh_f n)
  | KDisj a1 n1 a2 n2 => KDisj (sash_f a1) (esh_f n1) (sash_f a2) (esh_f n2)
  | KFill a n c => KFill (sash_f a) (esh_f n) c
  | KUnk a n => KUnk (sash_f a) (esh_f n)
  | KPriv tg rs args k => KPriv tg (map (fun r => (sash_f (fst r), esh_f (snd r))) rs) (map esh_f args) k
  end.
Definition pesh_f (p : expr * expr) : expr * expr := (esh_f (fst p), esh_f (snd p)).
Definition msh_f (m : amap) : amap := AM (esh_f (am_base m)) (esh_f (am_len m)) (am_kind m).
Definition fdsh_f (f : afd) : afd := match f with FdFile k l o => FdFile k (esh_f l) (esh_f o) | _ => f end.
Definition sesh_f (x : sentry) : sentry := SE (sash_f (e_addr x)) (e_width x) (esh_f (e_val x)).
Definition ssh_f (ss : sym_state) : sym_state :=
  SSR (s_pc ss) (map esh_f (s_regs ss)) (map sesh_f (s_log ss)) (map ksh_f (s_know ss)) (f (s_next ss))
      (option_map sash_f (s_resv ss)).
Definition ash_f (cs : acs) : acs :=
  ACS (ssh_f (a_ss cs)) (map msh_f (a_maps cs)) (a_totsz cs) (a_ylo cs) (a_eager cs) (map pesh_f (a_vis cs))
      (map pesh_f (a_ghost cs)) (a_abytes cs) (esh_f (a_brk cs)) (fdsh_f (a_fd cs)) (a_tidset cs).
Definition pairsh_f (p : nat * nat) : nat * nat := (vshn_f (fst p), vshn_f (snd p)).

Fixpoint psh_f (p : plan) : plan :=
  match p with
  | PRun stops k => PRun stops (psh_f k)
  | PSplit e mid k1 k2 => PSplit (esh_f e) mid (psh_f k1) (psh_f k2)
  | PCase2 e mid k1 k2 => PCase2 (esh_f e) mid (psh_f k1) (psh_f k2)
  | PCaseDisj b1 b2 k1 k2 => PCaseDisj (esh_f b1) (esh_f b2) (psh_f k1) (psh_f k2)
  | PShDisj b1 n1 b2 n2 k => PShDisj (esh_f b1) (esh_f n1) (esh_f b2) (esh_f n2) (psh_f k)
  | PContra => PContra
  | PFact K k => PFact (ksh_f K) (psh_f k)
  | PJoin b off n k => PJoin (esh_f b) off n (psh_f k)
  | PForget ixs k => PForget ixs (psh_f k)
  | PDropRange b n k => PDropRange (esh_f b) (esh_f n) (psh_f k)
  | PGcKeep ws k => PGcKeep (map pesh_f ws) (psh_f k)
  | PBump m k => PBump (vshn_f m) (psh_f k)
  | PHavoc rs k => PHavoc rs (psh_f k)
  | PHavocBig K k => PHavocBig K (psh_f k)
  | PFresh r logc base k => PFresh r logc (option_map esh_f base) (psh_f k)
  | PSys y k => PSys y (psh_f k)
  | PMmap ka kb => PMmap (psh_f ka) (psh_f kb)
  | PMmapIn a b c => PMmapIn (psh_f a) (psh_f b) (psh_f c)
  | PMprotect a b => PMprotect (psh_f a) (psh_f b)
  | PBrk2 a b => PBrk2 (psh_f a) (psh_f b)
  | PMunmap2 a b => PMunmap2 (psh_f a) (psh_f b)
  | PX x args k => PX x (map esh_f args) (psh_f k)
  | PExt id args k => PExt id (map esh_f args) (psh_f k)
  | PEmit id args k => PEmit id (map esh_f args) (psh_f k)
  | PExt2 id args k1 k2 => PExt2 id (map esh_f args) (psh_f k1) (psh_f k2)
  | PLoop J N inv body k => PLoop (vshn_f J) (esh_f N) inv (psh_f body) (psh_f k)   (* inv: a named state, shifted where defined *)
  | PNext => PNext
  | PHandoff h => PHandoff h
  | PExit => PExit
  | PSpin => PSpin
  | PFog i sz k => PFog i sz (psh_f k)
  | PFogNew i sz k => PFogNew i sz (psh_f k)
  | PGhost b n k => PGhost (esh_f b) (esh_f n) (psh_f k)
  | PUnvis b n k => PUnvis (esh_f b) (esh_f n) (psh_f k)
  | PHavocBrk lo hi k => PHavocBrk lo hi (psh_f k)
  | PIntro lo hi k => PIntro lo hi (psh_f k)
  | PDiamond joinpc rs k => PDiamond joinpc rs (psh_f k)
  | PRename m k => PRename (map pairsh_f m) (psh_f k)
  | PCompact k => PCompact (psh_f k)
  | PVia j js lo karms k => PVia j js (vshn_f lo) (psh_f karms) (psh_f k)   (* js: a named state, shifted where defined *)
  | PMerge j => PMerge j
  | PAbstractCell b n k => PAbstractCell (esh_f b) n (psh_f k)
  | PHavocWords bs k => PHavocWords (map esh_f bs) (psh_f k)
  | PRespell r e k => PRespell r (esh_f e) (psh_f k)
  | PMmapInH a b c => PMmapInH (psh_f a) (psh_f b) (psh_f c)
  | PCaseDisjJ b1 b2 joinpc rs k => PCaseDisjJ (esh_f b1) (esh_f b2) joinpc rs (psh_f k)
  | PCaseP k1 k2 => PCaseP (psh_f k1) (psh_f k2)
  | PCaseNJ e cuts joinpc rs ws k =>
      PCaseNJ (esh_f e) cuts joinpc rs (map (fun w => (esh_f (fst (fst w)), snd (fst w), snd w)) ws) (psh_f k)
  | PVisAbsorb b n k => PVisAbsorb (esh_f b) (esh_f n) (psh_f k)
  | PFreshCell b n k => PFreshCell (esh_f b) n (psh_f k)
  | PVisSplit b n d k => PVisSplit (esh_f b) n d (psh_f k)
  | PVisHead b m L k => PVisHead (esh_f b) m (esh_f L) (psh_f k)
  | PUnvisHead b m k => PUnvisHead (esh_f b) m (psh_f k)
  | PGhostDedup k => PGhostDedup (psh_f k)
  | PHavocBrkP lo hi k => PHavocBrkP lo hi (psh_f k)
  | PKeep ws vs k => PKeep (map pesh_f ws) (map vshn_f vs) (psh_f k)
  | PFactMem K k => PFactMem (ksh_f K) (psh_f k)
  | PVisRespell b n b' n' k => PVisRespell (esh_f b) (esh_f n) (esh_f b') (esh_f n') (psh_f k)
  | PMapRespell b n b' n' k => PMapRespell (esh_f b) (esh_f n) (esh_f b') (esh_f n') (psh_f k)
  | PMemRespell b lo hi b' d k => PMemRespell (esh_f b) lo hi (esh_f b') d (psh_f k)
  | PSrlSplit r s k => PSrlSplit r s (psh_f k)
  | PAndRange r logc ub k => PAndRange r logc (esh_f ub) (psh_f k)
  | PAndRangeR r logc rs k => PAndRangeR r logc rs (psh_f k)
  | PSrlSplitAll r s k => PSrlSplitAll r s (psh_f k)
  | PFdHavoc lo hi k => PFdHavoc lo hi (psh_f k)
  | PFreshCellK b n k => PFreshCellK (esh_f b) n (psh_f k)
  | PVisPerm perm k => PVisPerm perm (psh_f k)
  | PHandoffM m => PHandoffM (map pairsh_f m)
  | PFdRespell len off k => PFdRespell (esh_f len) (esh_f off) (psh_f k)
  | PDisjNth b1 n1 i k => PDisjNth (esh_f b1) (esh_f n1) i (psh_f k)
  | PMmapInS a b c => PMmapInS (psh_f a) (psh_f b) (psh_f c)
  end.
End VSF.

Open Scope Z_scope.

(* ---- the transplant ---- *)
Fixpoint evars_ge (v : N) (e : expr) : bool :=
  match e with
  | EVar w => N.leb v w
  | ELit _ | EBlob _ _ _ _ => false
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => (evars_ge v a || evars_ge v b)%bool
  | EExt _ _ _ a => evars_ge v a
  end.
Definition kexprs (K : kentry) : list expr := match K with
  | KWord a _ v => [a_base a; v] | KZero a n | KBlob a n _ | KWr a n | KFill a n _ | KUnk a n => [a_base a; n]
  | KImg _ _ => [] | KAlign x _ | KRange x _ _ => [x] | KDisj a1 n1 a2 n2 => [a_base a1; n1; a_base a2; n2]
  | KPriv _ rs args _ => map snd rs ++ args end.
Definition kmentions (v : N) (K : kentry) : bool := existsb (evars_ge v) (kexprs K).

(* the fd table: the arrival's, except a file offset the invariant states as a function of the loop variable (a loop
   that reads or seeks per iteration, e.g. the invariant's offset 65536·J + 262144 against an arrival's 262144) *)
Definition fdmerge (J : N) (fi fa : afd) : afd :=
  match fi, fa with
  | FdFile _ _ oi, FdFile k l oa => FdFile k l (if evars_ge J oi then oi else oa)
  | _, _ => fa
  end.
Definition tpl (J : N) (inv a : acs) : N * acs :=
  let d := if N.leb (nxt a) J then 0%N else (nxt a - J)%N in
  let f := fun v => if N.ltb v J then v else (v + d)%N in
  let i1 := ash_f f inv in
  let J' := (J + d)%N in
  let lo := N.succ J' in
  let hi := nxt i1 in
  let keepr (ri : expr) : bool :=
    (match ri with EVar v => (N.leb lo v && N.ltb v hi)%bool | _ => false end || evars_ge J' ri)%bool in
  let regs := map (fun pr => if keepr (fst pr) then fst pr else snd pr) (combine (s_regs (a_ss i1)) (s_regs (a_ss a))) in
  let kn' := filter (kmentions J') (kn i1) ++ filter (fun K => negb (kmentions J' K)) (kn a) in
  (J', ACS (SSR (s_pc (a_ss i1)) regs [] kn' hi None) (a_maps a) (Z.max (a_totsz a) (a_totsz i1))
           (Z.min (a_ylo a) (a_ylo i1)) (Z.max (a_eager a) (a_eager i1)) (a_vis a) (a_ghost a)
           (Z.max (a_abytes a) (a_abytes i1)) (a_brk a) (fdmerge J' (a_fd i1) (a_fd a)) (a_tidset a)).

Fixpoint zlook {A : Type} (L : list (Z * A)) (k : Z) : option A :=
  match L with [] => None | (k', x) :: L' => if Z.eqb k k' then Some x else zlook L' k end.

(* the plan with each transplanted [PLoop] (keyed by its released invariant's next variable) replaced *)
Fixpoint pinv (LL : list (Z * (N * acs))) (p : plan) : plan :=
  match p with
  | PRun stops k => PRun stops (pinv LL k)
  | PSplit e mid k1 k2 => PSplit e mid (pinv LL k1) (pinv LL k2)
  | PCase2 e mid k1 k2 => PCase2 e mid (pinv LL k1) (pinv LL k2)
  | PCaseDisj b1 b2 k1 k2 => PCaseDisj b1 b2 (pinv LL k1) (pinv LL k2)
  | PShDisj b1 n1 b2 n2 k => PShDisj b1 n1 b2 n2 (pinv LL k)
  | PContra => p
  | PFact K k => PFact K (pinv LL k)
  | PJoin b off n k => PJoin b off n (pinv LL k)
  | PForget ixs k => PForget ixs (pinv LL k)
  | PDropRange b n k => PDropRange b n (pinv LL k)
  | PGcKeep ws k => PGcKeep ws (pinv LL k)
  | PBump m k => PBump m (pinv LL k)
  | PHavoc rs k => PHavoc rs (pinv LL k)
  | PHavocBig K k => PHavocBig K (pinv LL k)
  | PFresh r logc base k => PFresh r logc base (pinv LL k)
  | PSys y k => PSys y (pinv LL k)
  | PMmap ka kb => PMmap (pinv LL ka) (pinv LL kb)
  | PMmapIn a b c => PMmapIn (pinv LL a) (pinv LL b) (pinv LL c)
  | PMprotect a b => PMprotect (pinv LL a) (pinv LL b)
  | PBrk2 a b => PBrk2 (pinv LL a) (pinv LL b)
  | PMunmap2 a b => PMunmap2 (pinv LL a) (pinv LL b)
  | PX x args k => PX x args (pinv LL k)
  | PExt id args k => PExt id args (pinv LL k)
  | PEmit id args k => PEmit id args (pinv LL k)
  | PExt2 id args k1 k2 => PExt2 id args (pinv LL k1) (pinv LL k2)
  | PLoop J0 N inv body k =>
      match zlook LL (Z.of_N (nxt inv)) with
      | Some (J', inv') =>
          let f := fun v => if N.ltb v (N.of_nat J0) then v else (v + (J' - N.of_nat J0))%N in
          PLoop (N.to_nat J') N inv' (psh_f f (pinv LL body)) (psh_f f (pinv LL k))
      | None => PLoop J0 N inv (pinv LL body) (pinv LL k)
      end
  | PNext => p
  | PHandoff h => p
  | PExit => p
  | PSpin => p
  | PFog i sz k => PFog i sz (pinv LL k)
  | PFogNew i sz k => PFogNew i sz (pinv LL k)
  | PGhost b n k => PGhost b n (pinv LL k)
  | PUnvis b n k => PUnvis b n (pinv LL k)
  | PHavocBrk lo hi k => PHavocBrk lo hi (pinv LL k)
  | PIntro lo hi k => PIntro lo hi (pinv LL k)
  | PDiamond joinpc rs k => PDiamond joinpc rs (pinv LL k)
  | PRename m k => PRename m (pinv LL k)
  | PCompact k => PCompact (pinv LL k)
  | PVia j js lo karms k => PVia j js lo (pinv LL karms) (pinv LL k)
  | PMerge j => p
  | PAbstractCell b n k => PAbstractCell b n (pinv LL k)
  | PHavocWords bs k => PHavocWords bs (pinv LL k)
  | PRespell r e k => PRespell r e (pinv LL k)
  | PMmapInH a b c => PMmapInH (pinv LL a) (pinv LL b) (pinv LL c)
  | PCaseDisjJ b1 b2 joinpc rs k => PCaseDisjJ b1 b2 joinpc rs (pinv LL k)
  | PCaseP k1 k2 => PCaseP (pinv LL k1) (pinv LL k2)
  | PCaseNJ e cuts joinpc rs ws k => PCaseNJ e cuts joinpc rs ws (pinv LL k)
  | PVisAbsorb b n k => PVisAbsorb b n (pinv LL k)
  | PFreshCell b n k => PFreshCell b n (pinv LL k)
  | PVisSplit b n d k => PVisSplit b n d (pinv LL k)
  | PVisHead b m L k => PVisHead b m L (pinv LL k)
  | PUnvisHead b m k => PUnvisHead b m (pinv LL k)
  | PGhostDedup k => PGhostDedup (pinv LL k)
  | PHavocBrkP lo hi k => PHavocBrkP lo hi (pinv LL k)
  | PKeep ws vs k => PKeep ws vs (pinv LL k)
  | PFactMem K k => PFactMem K (pinv LL k)
  | PVisRespell b n b' n' k => PVisRespell b n b' n' (pinv LL k)
  | PMapRespell b n b' n' k => PMapRespell b n b' n' (pinv LL k)
  | PMemRespell b lo hi b' d k => PMemRespell b lo hi b' d (pinv LL k)
  | PSrlSplit r s k => PSrlSplit r s (pinv LL k)
  | PAndRange r logc ub k => PAndRange r logc ub (pinv LL k)
  | PAndRangeR r logc rs k => PAndRangeR r logc rs (pinv LL k)
  | PSrlSplitAll r s k => PSrlSplitAll r s (pinv LL k)
  | PFdHavoc lo hi k => PFdHavoc lo hi (pinv LL k)
  | PFreshCellK b n k => PFreshCellK b n (pinv LL k)
  | PVisPerm perm k => PVisPerm perm (pinv LL k)
  | PHandoffM m => p
  | PFdRespell len off k => PFdRespell len off (pinv LL k)
  | PDisjNth b1 n1 i k => PDisjNth b1 n1 i (pinv LL k)
  | PMmapInS a b c => PMmapInS (pinv LL a) (pinv LL b) (pinv LL c)
  end.

Definition oelse (a b : option nat) : option nat := match a with Some _ => a | None => b end.
Fixpoint plo (j : nat) (p : plan) : option nat :=
  match p with
  | PRun stops k => plo j k
  | PSplit e mid k1 k2 => oelse (plo j k1) (plo j k2)
  | PCase2 e mid k1 k2 => oelse (plo j k1) (plo j k2)
  | PCaseDisj b1 b2 k1 k2 => oelse (plo j k1) (plo j k2)
  | PShDisj b1 n1 b2 n2 k => plo j k
  | PContra => None
  | PFact K k => plo j k
  | PJoin b off n k => plo j k
  | PForget ixs k => plo j k
  | PDropRange b n k => plo j k
  | PGcKeep ws k => plo j k
  | PBump m k => plo j k
  | PHavoc rs k => plo j k
  | PHavocBig K k => plo j k
  | PFresh r logc base k => plo j k
  | PSys y k => plo j k
  | PMmap ka kb => oelse (plo j ka) (plo j kb)
  | PMmapIn a b c => oelse (plo j a) (oelse (plo j b) (plo j c))
  | PMprotect a b => oelse (plo j a) (plo j b)
  | PBrk2 a b => oelse (plo j a) (plo j b)
  | PMunmap2 a b => oelse (plo j a) (plo j b)
  | PX x args k => plo j k
  | PExt id args k => plo j k
  | PEmit id args k => plo j k
  | PExt2 id args k1 k2 => oelse (plo j k1) (plo j k2)
  | PLoop J0 N inv body k => oelse (plo j body) (plo j k)
  | PNext => None
  | PHandoff h => None
  | PExit => None
  | PSpin => None
  | PFog i sz k => plo j k
  | PFogNew i sz k => plo j k
  | PGhost b n k => plo j k
  | PUnvis b n k => plo j k
  | PHavocBrk lo hi k => plo j k
  | PIntro lo hi k => plo j k
  | PDiamond joinpc rs k => plo j k
  | PRename m k => plo j k
  | PCompact k => plo j k
  | PVia j' js lo karms k => if Nat.eqb j j' then Some lo else oelse (plo j karms) (plo j k)
  | PMerge j => None
  | PAbstractCell b n k => plo j k
  | PHavocWords bs k => plo j k
  | PRespell r e k => plo j k
  | PMmapInH a b c => oelse (plo j a) (oelse (plo j b) (plo j c))
  | PCaseDisjJ b1 b2 joinpc rs k => plo j k
  | PCaseP k1 k2 => oelse (plo j k1) (plo j k2)
  | PCaseNJ e cuts joinpc rs ws k => plo j k
  | PVisAbsorb b n k => plo j k
  | PFreshCell b n k => plo j k
  | PVisSplit b n d k => plo j k
  | PVisHead b m L k => plo j k
  | PUnvisHead b m k => plo j k
  | PGhostDedup k => plo j k
  | PHavocBrkP lo hi k => plo j k
  | PKeep ws vs k => plo j k
  | PFactMem K k => plo j k
  | PVisRespell b n b' n' k => plo j k
  | PMapRespell b n b' n' k => plo j k
  | PMemRespell b lo hi b' d k => plo j k
  | PSrlSplit r s k => plo j k
  | PAndRange r logc ub k => plo j k
  | PAndRangeR r logc rs k => plo j k
  | PSrlSplitAll r s k => plo j k
  | PFdHavoc lo hi k => plo j k
  | PFreshCellK b n k => plo j k
  | PVisPerm perm k => plo j k
  | PHandoffM m => None
  | PFdRespell len off k => plo j k
  | PDisjNth b1 n1 i k => plo j k
  | PMmapInS a b c => oelse (plo j a) (oelse (plo j b) (plo j c))
  end.

(* ---- the join meet ([PMerge] only; see the header) ----
   Constraints, each read from [entails_h] / [regs_match_h] (AsanPlanCore.v) at this commit:
   (1) a pattern variable must lie in [lo, nxt js): the entry's next variable is raised above every fresh name;
   (2) if no register needs generalising the meet is the exact one (the window may stay empty);
   (3) pattern variables are linear: each generalised slot gets its own fresh name;
   (4) a kept register must mention only variables below lo: a register the arrivals AGREE on but that mentions a
       variable >= lo (other than an existing pattern variable of the entry) is generalised too;
   (5) pc / maps / vis / ghost / brk / fd / tid are equalities and are NOT joined (copied from the entry; if they
       differ the join stays refused and the node's rows say so);
   (6) the entry's facts must mention only variables below lo: facts are intersected AND filtered by that. *)
Fixpoint evars_lt (v : N) (e : expr) : bool :=
  match e with
  | EVar w => N.ltb w v
  | ELit _ | EBlob _ _ _ _ => true
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => (evars_lt v a && evars_lt v b)%bool
  | EExt _ _ _ a => evars_lt v a
  end.
Definition is_pv (lo hi : N) (e : expr) : bool := match e with EVar v => (N.leb lo v && N.ltb v hi)%bool | _ => false end.
Fixpoint rgen (lo hi : N) (nx : N) (ro rc : list expr) : list expr * N :=
  match ro, rc with
  | a :: ro', b :: rc' =>
      if (is_pv lo hi a)%bool then let '(t, n') := rgen lo hi nx ro' rc' in (a :: t, n')
      else if (expr_eqb a b && evars_lt lo a)%bool then let '(t, n') := rgen lo hi nx ro' rc' in (a :: t, n')
      else let '(t, n') := rgen lo hi (N.succ nx) ro' rc' in (EVar nx :: t, n')
  | _, _ => ([], nx)
  end.
(* [jmeet] records a join entry, and that entry is read back by [PVia], whose test is [entails_h A lo hi cs js];
   its knowledge conjunct is [forallb (kn_incl1_h A k)] ([AsanPlanCore.kn_incl1_h]).  [kn_incl1_h] accepts a fact
   five ways.  [jkeepK] keeps the facts three of them accept: [kentry_eqb]; [kpriv_geb]; and [kentry_eqb_h]
   behind the [kflat_h] gate (saddr_eqb_h: the same address spelled with the offset folded into the base).
   [kimg_sub_covered] and [kunk_covered] are not reproduced ([kunk_covered] reads the atable [A], and [jmeet]
   takes none), so a fact only they accept is dropped from the recorded join entry.
   The [evars_lt lo] guard stands: a join entry mentions only variables below the join's own bound.  This file
   is a computation like MainCol.v -- it proves nothing, and every table it emits is re-checked by a certificate. *)
Definition jkeepK (k : list kentry) (K : kentry) : bool :=
  (existsb (fun X => kentry_eqb X K) k
   || existsb (fun X => kpriv_geb X K) k
   || (if kflat_h k K then existsb (fun X => kentry_eqb_h X K) k else false))%bool.
Definition jmeet (lo : N) (c0 c : acs) : acs :=
  let s := a_ss c0 in
  let hi := nxt c0 in
  let base := N.max lo hi in
  let '(regs, nx') := rgen lo hi base (s_regs s) (s_regs (a_ss c)) in
  let kn' := List.filter (fun K => (jkeepK (kn c) K && forallb (evars_lt lo) (kexprs K))%bool) (s_know s) in
  {| a_ss := SSR (s_pc s) regs [] kn' (N.max hi nx') None; a_maps := a_maps c0; a_totsz := Z.max (a_totsz c0) (a_totsz c);
     a_ylo := Z.min (a_ylo c0) (a_ylo c); a_eager := Z.max (a_eager c0) (a_eager c); a_vis := a_vis c0;
     a_ghost := a_ghost c0; a_abytes := Z.max (a_abytes c0) (a_abytes c); a_brk := a_brk c0; a_fd := a_fd c0;
     a_tidset := a_tidset c0 |}.

(* ---- keep-lists ----
   The post hand-off carries three image-data variables, 47..49 (VarShift's header), that the released plans'
   [PKeep ws vs] lists do not name, so [kn_keepm] drops every fact about them (e.g. the thread id EVar 48's
   range [1, 2^22), which decides the lock-acquire branch at 0x9a938). [pkx] appends 47..49 to every keep-list;
   the checker re-checks it all. *)
Definition NEWV : list nat := [47; 48; 49]%nat.
Fixpoint pkx (p : plan) : plan :=
  match p with
  | PRun stops k => PRun stops (pkx k)
  | PSplit e mid k1 k2 => PSplit e mid (pkx k1) (pkx k2)
  | PCase2 e mid k1 k2 => PCase2 e mid (pkx k1) (pkx k2)
  | PCaseDisj b1 b2 k1 k2 => PCaseDisj b1 b2 (pkx k1) (pkx k2)
  | PShDisj b1 n1 b2 n2 k => PShDisj b1 n1 b2 n2 (pkx k)
  | PContra => p
  | PFact K k => PFact K (pkx k)
  | PJoin b off n k => PJoin b off n (pkx k)
  | PForget ixs k => PForget ixs (pkx k)
  | PDropRange b n k => PDropRange b n (pkx k)
  | PGcKeep ws k => PGcKeep ws (pkx k)
  | PBump m k => PBump m (pkx k)
  | PHavoc rs k => PHavoc rs (pkx k)
  | PHavocBig K k => PHavocBig K (pkx k)
  | PFresh r logc base k => PFresh r logc base (pkx k)
  | PSys y k => PSys y (pkx k)
  | PMmap ka kb => PMmap (pkx ka) (pkx kb)
  | PMmapIn a b c => PMmapIn (pkx a) (pkx b) (pkx c)
  | PMprotect a b => PMprotect (pkx a) (pkx b)
  | PBrk2 a b => PBrk2 (pkx a) (pkx b)
  | PMunmap2 a b => PMunmap2 (pkx a) (pkx b)
  | PX x args k => PX x args (pkx k)
  | PExt id args k => PExt id args (pkx k)
  | PEmit id args k => PEmit id args (pkx k)
  | PExt2 id args k1 k2 => PExt2 id args (pkx k1) (pkx k2)
  | PLoop J0 N inv body k => PLoop J0 N inv (pkx body) (pkx k)
  | PNext => p
  | PHandoff h => p
  | PExit => p
  | PSpin => p
  | PFog i sz k => PFog i sz (pkx k)
  | PFogNew i sz k => PFogNew i sz (pkx k)
  | PGhost b n k => PGhost b n (pkx k)
  | PUnvis b n k => PUnvis b n (pkx k)
  | PHavocBrk lo hi k => PHavocBrk lo hi (pkx k)
  | PIntro lo hi k => PIntro lo hi (pkx k)
  | PDiamond joinpc rs k => PDiamond joinpc rs (pkx k)
  | PRename m k => PRename m (pkx k)
  | PCompact k => PCompact (pkx k)
  | PVia j js lo karms k => PVia j js lo (pkx karms) (pkx k)
  | PMerge j => p
  | PAbstractCell b n k => PAbstractCell b n (pkx k)
  | PHavocWords bs k => PHavocWords bs (pkx k)
  | PRespell r e k => PRespell r e (pkx k)
  | PMmapInH a b c => PMmapInH (pkx a) (pkx b) (pkx c)
  | PCaseDisjJ b1 b2 joinpc rs k => PCaseDisjJ b1 b2 joinpc rs (pkx k)
  | PCaseP k1 k2 => PCaseP (pkx k1) (pkx k2)
  | PCaseNJ e cuts joinpc rs ws k => PCaseNJ e cuts joinpc rs ws (pkx k)
  | PVisAbsorb b n k => PVisAbsorb b n (pkx k)
  | PFreshCell b n k => PFreshCell b n (pkx k)
  | PVisSplit b n d k => PVisSplit b n d (pkx k)
  | PVisHead b m L k => PVisHead b m L (pkx k)
  | PUnvisHead b m k => PUnvisHead b m (pkx k)
  | PGhostDedup k => PGhostDedup (pkx k)
  | PHavocBrkP lo hi k => PHavocBrkP lo hi (pkx k)
  | PKeep ws vs k => PKeep ws (vs ++ NEWV) (pkx k)
  | PFactMem K k => PFactMem K (pkx k)
  | PVisRespell b n b' n' k => PVisRespell b n b' n' (pkx k)
  | PMapRespell b n b' n' k => PMapRespell b n b' n' (pkx k)
  | PMemRespell b lo hi b' d k => PMemRespell b lo hi b' d (pkx k)
  | PSrlSplit r s k => PSrlSplit r s (pkx k)
  | PAndRange r logc ub k => PAndRange r logc ub (pkx k)
  | PAndRangeR r logc rs k => PAndRangeR r logc rs (pkx k)
  | PSrlSplitAll r s k => PSrlSplitAll r s (pkx k)
  | PFdHavoc lo hi k => PFdHavoc lo hi (pkx k)
  | PFreshCellK b n k => PFreshCellK b n (pkx k)
  | PVisPerm perm k => PVisPerm perm (pkx k)
  | PHandoffM m => p
  | PFdRespell len off k => PFdRespell len off (pkx k)
  | PDisjNth b1 n1 i k => PDisjNth b1 n1 i (pkx k)
  | PMmapInS a b c => PMmapInS (pkx a) (pkx b) (pkx c)
  end.

Fixpoint prsp (RS : list (nat * nat * expr)) (p : plan) : plan :=
  match p with
  | PRun stops k => PRun stops (prsp RS k)
  | PSplit e mid k1 k2 => PSplit e mid (prsp RS k1) (prsp RS k2)
  | PCase2 e mid k1 k2 => PCase2 e mid (prsp RS k1) (prsp RS k2)
  | PCaseDisj b1 b2 k1 k2 => PCaseDisj b1 b2 (prsp RS k1) (prsp RS k2)
  | PShDisj b1 n1 b2 n2 k => PShDisj b1 n1 b2 n2 (prsp RS k)
  | PContra => p
  | PFact K k => PFact K (prsp RS k)
  | PJoin b off n k => PJoin b off n (prsp RS k)
  | PForget ixs k => PForget ixs (prsp RS k)
  | PDropRange b n k => PDropRange b n (prsp RS k)
  | PGcKeep ws k => PGcKeep ws (prsp RS k)
  | PBump m k => PBump m (prsp RS k)
  | PHavoc rs k => PHavoc rs (prsp RS k)
  | PHavocBig K k => PHavocBig K (prsp RS k)
  | PFresh r logc base k => PFresh r logc base (prsp RS k)
  | PSys y k => PSys y (prsp RS k)
  | PMmap ka kb => PMmap (prsp RS ka) (prsp RS kb)
  | PMmapIn a b c => PMmapIn (prsp RS a) (prsp RS b) (prsp RS c)
  | PMprotect a b => PMprotect (prsp RS a) (prsp RS b)
  | PBrk2 a b => PBrk2 (prsp RS a) (prsp RS b)
  | PMunmap2 a b => PMunmap2 (prsp RS a) (prsp RS b)
  | PX x args k => PX x args (prsp RS k)
  | PExt id args k => PExt id args (prsp RS k)
  | PEmit id args k => PEmit id args (prsp RS k)
  | PExt2 id args k1 k2 => PExt2 id args (prsp RS k1) (prsp RS k2)
  | PLoop J0 N inv body k => PLoop J0 N inv (prsp RS body) (prsp RS k)
  | PNext => p
  | PHandoff h => fold_right (fun e k => match e with (h', r, x) => if Nat.eqb h h' then PRespell r x k else k end) p RS
  | PExit => p
  | PSpin => p
  | PFog i sz k => PFog i sz (prsp RS k)
  | PFogNew i sz k => PFogNew i sz (prsp RS k)
  | PGhost b n k => PGhost b n (prsp RS k)
  | PUnvis b n k => PUnvis b n (prsp RS k)
  | PHavocBrk lo hi k => PHavocBrk lo hi (prsp RS k)
  | PIntro lo hi k => PIntro lo hi (prsp RS k)
  | PDiamond joinpc rs k => PDiamond joinpc rs (prsp RS k)
  | PRename m k => PRename m (prsp RS k)
  | PCompact k => PCompact (prsp RS k)
  | PVia j js lo karms k => PVia j js lo (prsp RS karms) (prsp RS k)
  | PMerge j => p
  | PAbstractCell b n k => PAbstractCell b n (prsp RS k)
  | PHavocWords bs k => PHavocWords bs (prsp RS k)
  | PRespell r e k => PRespell r e (prsp RS k)
  | PMmapInH a b c => PMmapInH (prsp RS a) (prsp RS b) (prsp RS c)
  | PCaseDisjJ b1 b2 joinpc rs k => PCaseDisjJ b1 b2 joinpc rs (prsp RS k)
  | PCaseP k1 k2 => PCaseP (prsp RS k1) (prsp RS k2)
  | PCaseNJ e cuts joinpc rs ws k => PCaseNJ e cuts joinpc rs ws (prsp RS k)
  | PVisAbsorb b n k => PVisAbsorb b n (prsp RS k)
  | PFreshCell b n k => PFreshCell b n (prsp RS k)
  | PVisSplit b n d k => PVisSplit b n d (prsp RS k)
  | PVisHead b m L k => PVisHead b m L (prsp RS k)
  | PUnvisHead b m k => PUnvisHead b m (prsp RS k)
  | PGhostDedup k => PGhostDedup (prsp RS k)
  | PHavocBrkP lo hi k => PHavocBrkP lo hi (prsp RS k)
  | PKeep ws vs k => PKeep ws vs (prsp RS k)
  | PFactMem K k => PFactMem K (prsp RS k)
  | PVisRespell b n b' n' k => PVisRespell b n b' n' (prsp RS k)
  | PMapRespell b n b' n' k => PMapRespell b n b' n' (prsp RS k)
  | PMemRespell b lo hi b' d k => PMemRespell b lo hi b' d (prsp RS k)
  | PSrlSplit r s k => PSrlSplit r s (prsp RS k)
  | PAndRange r logc ub k => PAndRange r logc ub (prsp RS k)
  | PAndRangeR r logc rs k => PAndRangeR r logc rs (prsp RS k)
  | PSrlSplitAll r s k => PSrlSplitAll r s (prsp RS k)
  | PFdHavoc lo hi k => PFdHavoc lo hi (prsp RS k)
  | PFreshCellK b n k => PFreshCellK b n (prsp RS k)
  | PVisPerm perm k => PVisPerm perm (prsp RS k)
  | PHandoffM m => p
  | PFdRespell len off k => PFdRespell len off (prsp RS k)
  | PDisjNth b1 n1 i k => PDisjNth b1 n1 i (prsp RS k)
  | PMmapInS a b c => PMmapInS (prsp RS a) (prsp RS b) (prsp RS c)
  end.
(* ---- hole register respelling ----
   Two paths can reach one hole with a register spelled differently, once folded to a literal (an arm whose
   facts decide it) and once as the general expression, e.g. s5 = 1 against ((b & -(0 <u X)) & 3) + 1 (Main5
   t_14, hole 2100). [entails] needs equal registers, so no meet helps. When a hole entry
   and an arrival differ ONLY in registers, and one side has a literal where the other does not, the entry
   keeps (or takes) the general expression and every [PHandoff h] of that hole is preceded by [PRespell r e]; [node_respell]
   then decides each arm (it accepts only a provably equal respelling). Nothing is trusted. *)
Definition is_lit (e : expr) : bool := match e with ELit _ => true | _ => false end.
Fixpoint rgen2 (i : nat) (st ar : list expr) : list expr * list (nat * expr) * bool :=
  match st, ar with
  | x :: st', y :: ar' =>
      let '(rs, ch, ok) := rgen2 (S i) st' ar' in
      if expr_eqb x y then (x :: rs, ch, ok)
      else if (is_lit x && negb (is_lit y))%bool then (y :: rs, (i, y) :: ch, ok)
      else if (is_lit y && negb (is_lit x))%bool then (x :: rs, (i, x) :: ch, ok)
      else (x :: rs, ch, false)
  | _, _ => ([], [], true)
  end.
Definition same_but_regs (st ar : acs) : bool :=
  entails ar (with_ss st (mk_ss (s_pc (a_ss st)) (s_regs (a_ss ar)) (kn st) (nxt st))).

(* ---- the per-node collector ---- *)
Definition tc_tag (w : plan) : Z :=
  match w with PMerge j => 1000 + Z.of_nat j | PHandoff h => 100 + Z.of_nat h | PLoop _ _ _ _ _ => 2000
             | PNext => 3000 | _ => 0 end.
Section NCol.
  Variable chk : (nat -> option acs) -> plan -> cres.
  Variable p0 : plan.
  Definition ncur (J : list (nat * acs)) (L : list (Z * (N * acs))) (RS : list (nat * nat * expr)) : plan := prsp RS (pinv L (pjs J p0)).
  Fixpoint ncol (n : nat) (H J : list (nat * acs)) (L : list (Z * (N * acs))) (RS : list (nat * nat * expr)) (RH RJ : list nat)
           (log : list (Z * Z * Z)) : list (Z * Z * Z) * list (nat * acs) * list (nat * acs) * list (Z * (N * acs)) * list (nat * nat * expr) * bool :=
    match n with
    | O => (rev log, H, J, L, RS, false)
    | S n' =>
      match chk (tlook H) (ncur J L RS) with
      | COk _ => (rev log, H, J, L, RS, true)
      | CErr c w cs =>
          let row := (c, s_pc (a_ss cs), tc_tag w) in
          let stop := (rev (row :: log), H, J, L, RS, false) in
          let coll := (Z.eqb c 3 || Z.eqb c 4)%bool in
          match w with
          | PHandoff h =>
              if coll then
                match (if existsb (Nat.eqb h) RH then tlook H h else None) with
                | Some st =>
                    let '(rs, chg, okr) := rgen2 0 (s_regs (a_ss st)) (s_regs (a_ss cs)) in
                    match chg with
                    | _ :: _ =>
                        if (okr && same_but_regs st cs)%bool then
                          ncol n' (tupd H h (with_ss st (mk_ss (s_pc (a_ss st)) rs (kn st) (nxt st)))) J L
                               (map (fun e => (h, fst e, snd e)) chg ++ RS) RH RJ (row :: log)
                        else ncol n' (tupd H h (mc_next true (Some st) cs)) J L RS (h :: RH) RJ (row :: log)
                    | [] => ncol n' (tupd H h (mc_next true (Some st) cs)) J L RS (h :: RH) RJ (row :: log)
                    end
                | None => ncol n' (tupd H h (mc_next false None cs)) J L RS (h :: RH) RJ (row :: log)
                end
              else stop
          | PMerge j =>
              if coll then
                let lo := match plo j p0 with Some l => N.of_nat l | None => nxt cs end in
                let e := match (if existsb (Nat.eqb j) RJ then tlook J j else None) with
                         | Some o => jmeet lo o cs | None => mc_clean cs end in
                (* a changed join changes every downstream arrival: holes take a fresh arrival again *)
                ncol n' H (tupd J j e) L RS [] (j :: RJ) (row :: log)
              else stop
          | PLoop J0 _ inv _ _ =>
              if (Z.eqb c 3 && negb (existsb (fun e => N.eqb (nxt (snd (snd e))) (nxt inv)) L))%bool
              then ncol n' H J ((Z.of_N (nxt inv), tpl (N.of_nat J0) inv cs) :: L) RS RH RJ (row :: log) else stop
          | PNext =>
              (* Houdini step: drop from the newest transplanted invariant every fact whose J+1 instance the end of
                 the body does not establish; stop if nothing drops. Entry and J+1 are re-checked on the next pass. *)
              match L with
              | (key, (Jl, inv)) :: L' =>
                  let keepK := fun K => existsb (kentry_eqb K) (kn cs) in
                  let ok1 := fun K => forallb keepK (kn (inst (set_kn inv [K]) Jl (eaddz (EVar Jl) 1))) in
                  let kn' := filter ok1 (kn inv) in
                  if (Z.eqb c 3 && Nat.ltb (List.length kn') (List.length (kn inv)))%bool
                  then ncol n' H J ((key, (Jl, set_kn inv kn')) :: L') RS RH RJ (row :: log) else stop
              | [] => stop
              end
          | _ => stop
          end
      end
    end.
End NCol.

(* ---- the tree collector ---- *)
Definition rowN : Type := (Z * list (Z * Z * Z) * bool)%type.
Definition seedT (HT : list (nat * (nat * acs))) : list (nat * acs) := map (fun e => (fst e, ash (snd (snd e)))) HT.
Definition seedR (HR : list (nat * (shape * acs))) : list (nat * acs) := map (fun e => (fst e, ash (snd (snd e)))) HR.
Definition newT (H : list (nat * acs)) (HT : list (nat * (nat * acs))) : list (nat * (nat * acs)) :=
  map (fun e => (fst e, (fst (snd e), match tlook H (fst e) with Some s => s | None => ash (snd (snd e)) end))) HT.
Definition newR (H : list (nat * acs)) (HR : list (nat * (shape * acs))) : list (nat * (shape * acs)) :=
  map (fun e => (fst e, (fst (snd e), match tlook H (fst e) with Some s => s | None => ash (snd (snd e)) end))) HR.
Fixpoint lkT (HT : list (nat * (nat * acs))) (j : nat) : option acs :=
  match HT with [] => None | (k, (_, s)) :: T => if Nat.eqb j k then Some s else lkT T j end.
Fixpoint lkR (HR : list (nat * (shape * acs))) (j : nat) : option acs :=
  match HR with [] => None | (k, (_, s)) :: T => if Nat.eqb j k then Some s else lkR T j end.

Section TCol.
  Variable rsb : bool.
  (* The shift applied to an [MCase] scrutinee (see the MCase arm below): every caller passes [VarShift.esh]. *)
  Variable esc : expr -> expr.
  Definition runnode (C : class) (ch : acs) (p : plan) (seed : list (nat * acs)) : plan * list (nat * acs) * rowN :=
    let q := pkx (pshj p) in
    let '(lg, H, J, L, RS, ok) := ncol (fun HS r => ta_chk_with rsb C (pay_start ch C) HS r) q 64 seed [] [] [] [] [] [] in
    (prsp RS (pinv L (pjs J q)), H, (Z.modulo (pfp p) 100000, lg, ok)).
  (* The shape a hole's rtree child checks to, from its own check (the rtree_ok shape of a leaf or a prefix node):
     a collected child can check to another shape than the released hole shape (the revised model can change what a
     child prints or exits with), so the emitted hole shape is the child's computed one (the released one where the
     child does not check).
     Nothing is trusted: rtree_ok and the parent's class check re-check it. *)
  Fixpoint rshape (ch : acs) (C : class) (t : rtree) : option shape :=
    match t with
    | RLeaf p => match ta_chk_with rsb C (pay_start ch C) HS_none p with COk s => Some s | CErr _ _ _ => None end
    | RClass C' t' => rshape ch C' t'
    | RPreS p HR RT => match ta_chk_with rsb C (pay_start ch C) (hs_ofS HR) p with COk s => Some (subst_holes (rs_of HR) s) | CErr _ _ _ => None end
    end.
  Definition rshapes (HR : list (nat * (shape * acs))) (C : class) (RT : list (nat * rtree)) : list (nat * (shape * acs)) :=
    map (fun e => (fst e, (match lookupT RT (fst e) with
                           | Some t => match rshape (snd (snd e)) C t with Some s => s | None => fst (snd e) end
                           | None => fst (snd e) end, snd (snd e)))) HR.
  Fixpoint rcol (ch : acs) (C : class) (t : rtree) : rtree * list rowN :=
    match t with
    | RLeaf p => let '(p', _, rw) := runnode C ch p [] in (RLeaf p', [rw])
    | RClass C' t' => let '(t'', rs) := rcol ch C' t' in (RClass C' t'', rs)
    | RPreS p HR RT =>
        let '(p', H, rw) := runnode C ch p (seedR HR) in
        let HR' := newR H HR in
        let '(RT', rs) := (fix forest (RT : list (nat * rtree)) : list (nat * rtree) * list rowN :=
              match RT with
              | [] => ([], [])
              | (j, t') :: RT' =>
                  let '(F, rs) := forest RT' in
                  match lkR HR' j with
                  | Some chj => let '(t'', r) := rcol chj C t' in ((j, t'') :: F, r ++ rs)
                  | None => ((j, t') :: F, rs)
                  end
              end) RT in
        (RPreS p' (rshapes HR' C RT') RT', rw :: rs)
    end.
  Definition rforest (HR' : list (nat * (shape * acs))) (C : class) (RT : list (nat * rtree)) : list (nat * rtree) * list rowN :=
    fold_right (fun e acc => let '(F, rs) := acc in
      match lkR HR' (fst e) with
      | Some chj => let '(t'', r) := rcol chj C (snd e) in ((fst e, t'') :: F, r ++ rs)
      | None => (e :: F, rs)
      end) ([], []) RT.
  Fixpoint tcol (ch : acs) (C : class) (t : mtree) : mtree * list rowN :=
    let mforest := fix mforest (HT' : list (nat * (nat * acs))) (PT : list (nat * mtree)) : list (nat * mtree) * list rowN :=
      match PT with
      | [] => ([], [])
      | (j, t') :: PT' =>
          let '(F, rs) := mforest HT' PT' in
          match lkT HT' j with
          | Some chj => let '(t'', r) := tcol chj C t' in ((j, t'') :: F, r ++ rs)
          | None => ((j, t') :: F, rs)
          end
      end in
    match t with
    | MLeaf L p => let '(p', _, rw) := runnode C ch p [] in (MLeaf L p', [rw])
    | MPre L p HT PT =>
        let '(p', H, rw) := runnode C ch p (seedT HT) in
        let HT' := newT H HT in
        let '(PT', rs) := mforest HT' PT in (MPre L p' HT' PT', rw :: rs)
    | MSplit q mid le gt =>
        let '(le', r1) := tcol ch (C ++ [(q, QMIN, mid)]) le in
        let '(gt', r2) := tcol ch (C ++ [(q, mid + 1, QMAX)]) gt in (MSplit q mid le' gt', r1 ++ r2)
    | MCase e mid le gt =>
        (* The mtree's [MCase] scrutinee holds variable INDICES as literals, exactly as plans and states do. A
           released tree's scrutinees are in the released numbering ([EVar 45]) while every collected state is in
           the revised one ([EVar 50] = [vsh 45]), so on an unshifted scrutinee [mcase_lo]/[mcase_hi] narrow a
           variable that does not denote and the branch they exist to decide stays undecided. [esc] shifts it:
           [esh] is [VarShift]'s own total function, the same one behind [ash] and [psh], so the scrutinee moves
           by the identical map as the states it is compared against. The sibling [MSplit] above splits by class
           QUANTITY and carries no variable literal, so it needs no shift.
           The shifted scrutinee goes into the EMITTED tree too: [mtree_ok] re-checks the collected tree against
           the revised states, so the emitted [MCase] carries the revised spelling. Nothing here is trusted. *)
        let e' := esc e in
        let '(le', r1) := tcol (mcase_lo ch e' mid) C le in
        let '(gt', r2) := tcol (mcase_hi ch e' mid) C gt in (MCase e' mid le' gt', r1 ++ r2)
    | MClass C' t' => let '(t'', rs) := tcol ch C' t' in (MClass C' t'', rs)
    | MEmpty L => (t, [])
    | MPreS L p HR PT =>
        let '(p', H, rw) := runnode C ch p (seedR HR) in
        let HR' := newR H HR in
        let '(PT', rs) := rforest HR' C PT in (MPreS L p' (rshapes HR' C PT') PT', rw :: rs)
    | MPreX L p HT PT HR RT =>
        let '(p', H, rw) := runnode C ch p (seedT HT ++ seedR HR) in
        let HT' := newT H HT in let HR' := newR H HR in
        let '(PT', r1) := mforest HT' PT in
        let '(RT', r2) := rforest HR' C RT in (MPreX L p' HT' PT' (rshapes HR' C RT') RT', rw :: r1 ++ r2)
    | MLoop _ _ _ _ _ _ _ => (t, [(-1, [], false)])
    end.
End TCol.
