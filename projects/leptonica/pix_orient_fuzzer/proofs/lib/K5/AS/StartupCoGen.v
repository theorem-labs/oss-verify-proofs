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
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AS Require Import AxSymExec3 AsanPlanCore AsanPlan.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
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

(* THE SAME TABLES FROM ONE RUN.  [gc_go2] runs [check] once per entry it adds or meets, and every
   run goes again through the whole plan up to its first refusal: about forty runs for a plan with
   two [PVia]s and four hand-offs, most of them through the long hand-off tails behind the
   [PVia]s (in this family's start-up, tails of hundreds of [XMemset] nodes each), so
   the tables cost tens of hours there.  [gc_cc] is [check]'s text (K5/AS/AsanPlan.v) with the two
   tables and the log ([gc_m]) threaded through it in [check]'s own order, run once.  Three arms
   differ from [check]'s:
   - [PMerge j] tests the arriving state against the table's entry [j] (where [check] tests it
     against the join state its [PVia] was given, which in the certificate is that entry); a
     refusal meets the state into the entry ([gc_absorb], as [gc_go] does) and the test is made
     again against the new entry.
   - [PHandoff h] does the same with the hand-off table (a missing entry takes the state).
   - [PVia j _ lo karms k] runs its arms first, again until a run of them changes no entry (at
     most [rounds] runs, [PMerge] giving a placeholder shape there), so that entry [j] is one every
     arrival entails; then, as [check] does, the continuation from that entry and the arms with the
     continuation's shape.
   So the join entries are the ones [gc_go]'s reruns reach, and the hand-off states come from runs
   from the final join states only, as in [gc_go2]'s second run.  A state at a hand-off or merge
   does not depend on the tables, and a state that passes an entry passes the entry met with
   another state, so each node meets the tables the certificate checks it with.  NOTHING HERE IS
   TRUSTED either: [check] re-checks the tables in the certificate. *)
Definition gc_m : Type := (gtab * gtab * list (Z * Z * Z * Z))%type.
Definition gc_row (c : Z) (w : plan) (cs : acs) : Z * Z * Z * Z := (c, s_pc (a_ss cs), cg_tag w, Z.of_nat (nxt cs)).

Section Coll.
Variable segs : list MemImageType.Segment.
Variable IT : itab.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable XN : nat -> list expr -> acs -> option acs.
Variable XE : nat -> list expr -> acs -> option (Z * list spiece * acs).
Variable XB : nat -> list expr -> acs -> option (acs * acs).
Variable KC : nat.
Variable bfuel : nat.
Variable dflt : acs.
Variable rounds : nat.

Fixpoint gc_cc (fuel : nat) (lc : option loopctx) (cs : acs) (p : plan) (m : gc_m) {struct fuel} : cres * gc_m :=
  match fuel with
  | O => (CErr 0 p cs, m)
  | S f =>
  let cc_in := gc_cc in
  let cc (f : nat) := cc_in f lc in
  let gcb := match lc with Some c => lc_bnd c | None => nx0 end in
  if negb match lc with Some c => Nat.leb (lc_bnd c) (nxt cs) | None => true end then (CErr 9 p cs, m) else
  match p with
  | PRun stops k =>
      match run_block_gc segs IT gcb KC bfuel (stops ++ STOPS A) cs with
      | Some cs' => cc f cs' k m
      | None => (CErr 1 p cs, m)
      end
  | PSplit e mid k1 k2 =>
      if expr_vars_lt nx0 e then
      match crange (kn cs) e with
      | Some (lo, hi) =>
          if (Z.leb lo mid && Z.ltb mid hi)%bool then
            match cc f (set_kn cs (KRange e lo mid :: kn cs)) k1 m with
            | (COk s1, m) =>
                match cc f (set_kn cs (KRange e (mid + 1) hi :: kn cs)) k2 m with
                | (COk s2, m) => (COk (SCase e mid s1 s2), m)
                | err => err
                end
            | err => err
            end
          else
            if Z.leb hi mid then cc f cs k1 m else cc f cs k2 m
      | None => (CErr 3 p cs, m)
      end
      else (CErr 3 p cs, m)
  | PCase2 e mid k1 k2 =>
      match crange (kn cs) e with
      | Some (lo, hi) =>
          if negb (Z.leb lo mid && Z.ltb mid hi)%bool then (if Z.leb hi mid then cc f cs k1 m else cc f cs k2 m) else
          if (Z.leb lo mid && Z.ltb mid hi)%bool then
            let cs1 := set_kn cs (KRange e lo mid :: kn cs) in
            let cs2 := set_kn cs (KRange e (mid + 1) hi :: kn cs) in
            if kn_contra (kn cs1) then cc f cs2 k2 m
            else if kn_contra (kn cs2) then cc f cs1 k1 m
            else
            match cc f cs1 k1 m with
            | (COk s1, m) =>
                match cc f cs2 k2 m with
                | (COk s2, m) => if shape_eqb s1 s2 then (COk s1, m) else (CErr 6 p cs, m)
                | err => err
                end
            | err => err
            end
          else (CErr 3 p cs, m)
      | None => (CErr 3 p cs, m)
      end
  | PCaseDisj b1 b2 k1 k2 =>
      match node_casedisj cs b1 b2 with
      | Some (csa, csb) =>
          match cc f csa k1 m with
          | (COk s1, m) => match cc f csb k2 m with
                      | (COk s2, m) => if shape_eqb s1 s2 then (COk s1, m) else (CErr 6 p cs, m)
                      | err => err
                      end
          | err => err
          end
      | None => (CErr 3 p cs, m)
      end
  | PShDisj b1 n1 b2 n2 k => match node_shdisj A cs b1 n1 b2 n2 with Some cs' => cc f cs' k m | None => (CErr 3 p cs, m) end
  | PContra => if kn_contra (kn cs) then (COk SNil, m) else (CErr 3 p cs, m)
  | PFact K k => if fact_ok (kn cs) K then cc f (add_kn cs [K]) k m else (CErr 3 p cs, m)
  | PJoin b off n k => match node_join segs cs b off n with Some cs' => cc f cs' k m | None => (CErr 3 p cs, m) end
  | PForget ixs k => cc f (set_kn cs (drop_ixs ixs 0 (kn cs))) k m
  | PDropRange b n k => cc f (node_droprange cs b n) k m
  | PGcKeep ws k => cc f (set_kn cs (kn_keep (kn cs) ws)) k m
  | PBump mb k => match node_bump cs mb with Some cs' => cc f cs' k m | None => (CErr 3 p cs, m) end
  | PHavoc rs k => match node_havoc nx0 cs rs with Some cs' => cc f cs' k m | None => (CErr 3 p cs, m) end
  | PHavocBig K k => match node_havocbig nx0 cs K with Some cs' => cc f cs' k m | None => (CErr 3 p cs, m) end
  | PFresh r logc base k => match node_fresh nx0 cs r logc base with Some cs' => cc f cs' k m | None => (CErr 3 p cs, m) end
  | PSys y k =>
      if is_ecall_at segs cs then
        match node_sys A nx0 y cs with Some cs' => cc f cs' k m | None => (CErr 3 p cs, m) end
      else (CErr 2 p cs, m)
  | PBrk2 ka kb =>
      if is_ecall_at segs cs then
        match node_brk2 A LIMIT cs with
        | Some (csa, csb) => cc f csb kb m
        | None => (CErr 3 p cs, m)
        end
      else (CErr 2 p cs, m)
  | PMmap ka kb =>
      if is_ecall_at segs cs then
        match node_mmap2 A nx0 LIMIT cs with
        | Some (csa, csb) => cc f csb kb m
        | None => (CErr 3 p cs, m)
        end
      else (CErr 2 p cs, m)
  | PMmapIn ka kb kc =>
      if is_ecall_at segs cs then
        match node_mmapin A LIMIT false cs with
        | Some (csa, csb, cscs) => cc f csb kb m
        | None => (CErr 3 p cs, m)
        end
      else (CErr 2 p cs, m)
  | PMmapInH ka kb kc =>
      if is_ecall_at segs cs then
        match node_mmapin A LIMIT true cs with
        | Some (csa, csb, cscs) => cc f csb kb m
        | None => (CErr 3 p cs, m)
        end
      else (CErr 2 p cs, m)
  | PMprotect ka kb =>
      if is_ecall_at segs cs then
        match node_mprotect2 A LIMIT cs with
        | Some (csa, csb) => cc f csb kb m
        | None => (CErr 3 p cs, m)
        end
      else (CErr 2 p cs, m)
  | PX x args k => match node_x segs A nx0 x args cs with Some cs' => cc f cs' k m | None => (CErr 3 p cs, m) end
  | PHavocCell b n k => match node_havoccell segs nx0 cs b n with Some cs' => cc f cs' k m | None => (CErr 3 p cs, m) end
  | PBrk2S ka kb =>
      if is_ecall_at segs cs then
        match node_brk2s A LIMIT cs with
        | Some (csa, csb) =>
            match cc f csa ka m with
            | (COk sa, m) => match cc f csb kb m with
                        | (COk sb, m) => if shape_eqb sa sb then (COk sa, m) else (CErr 6 p cs, m)
                        | err => err
                        end
            | err => err
            end
        | None => (CErr 3 p cs, m)
        end
      else (CErr 2 p cs, m)
  | PFreshAnd r k =>
      let '(e', sa) := AX2.deand (reg cs r) in
      match node_fresh nx0 cs r 0 (Some (eaddz e' (- sa))) with Some cs' => cc f cs' k m | None => (CErr 3 p cs, m) end
  | PVisSlice b n k => match vis_slice A LIMIT cs b n with Some cs' => cc f cs' k m | None => (CErr 3 p cs, m) end
  | PKWrJoin b1 o1 n1 b2 o2 n2 k => match node_kwrjoin cs b1 o1 n1 b2 o2 n2 with Some cs' => cc f cs' k m | None => (CErr 3 p cs, m) end
  | PIntroW w fs k => match node_introw nx0 cs w fs with Some cs' => cc f cs' k m | None => (CErr 3 p cs, m) end
  | PCaseDisjJ b1 b2 joinpc rs k =>
      match node_casedisj cs b1 b2 with
      | Some (cs1, cs2) =>
          match run_block_gc segs IT gcb KC bfuel (joinpc :: STOPS A) cs1 with
          | Some ca =>
              match run_block_gc segs IT gcb KC bfuel (joinpc :: STOPS A) cs2 with
              | Some cb =>
                  match node_diamond_join A nx0 (nxt cs) joinpc rs ca cb with
                  | Some csj => cc f csj k m
                  | None => (CErr 3 p ca, m)
                  end
              | None => (CErr 1 p cs2, m)
              end
          | None => (CErr 1 p cs1, m)
          end
      | None => (CErr 3 p cs, m)
      end
  | PExt id args k => match XN id args cs with Some cs' => cc f cs' k m | None => (CErr 3 p cs, m) end
  | PEmit id args k =>
      match XE id args cs with
      | Some (fd, ps, cs') => match cc f cs' k m with (COk s, m) => (COk (SEmitP fd ps s), m) | err => err end
      | None => (CErr 3 p cs, m)
      end
  | PExt2 id args k1 k2 =>
      match XB id args cs with
      | Some (csa, csb) =>
          match cc f csa k1 m with
          | (COk sa, m) => match cc f csb k2 m with (COk sb, m) => (COk (SAlt2 sa sb), m) | err => err end
          | err => err
          end
      | None => (CErr 3 p cs, m)
      end
  | PLoop J N inv body k =>
      match loop_ok nx0 cs J N inv with
      | Some nhi =>
          let lo := S J in let hi := nxt inv in
          if (Z.eqb (pc inv) (pc cs) && entails_h A lo hi cs (inst inv J (ELit 0)))%bool then
            match cc_in f (Some (LC (pc cs) (inst inv J (eaddz (EVar J) 1)) lo hi)) (loop_body_state J N nhi inv) body m with
            | (COk SNext, m) => cc f (inst inv J N) k m
            | (COk _, m) => (CErr 7 p cs, m)
            | err => err
            end
          else (CErr 3 p cs, m)
      | None => (CErr 3 p cs, m)
      end
  | PNext =>
      match lc with
      | Some (LC h nx lo hi) =>
          if (Z.eqb (pc cs) h && entails_h A lo hi cs nx)%bool then (COk SNext, m) else (CErr 3 p cs, m)
      | _ => (CErr 8 p cs, m)
      end
  | PHandoff h =>
      let '(Jt, Ht, lg) := m in
      let hok (t : gtab) := match gc_get t h with Some ch => entails cs ch | None => false end in
      if hok Ht then (COk (SHole (hole_of h)), m) else
      let Ht' := gc_absorb Ht h cs in
      let m' := (Jt, Ht', gc_row (match gc_get Ht h with Some _ => 3 | None => 4 end) p cs :: lg) in
      if hok Ht' then (COk (SHole (hole_of h)), m') else (CErr 3 p cs, m')
  | PExit =>
      if is_ecall_at segs cs then
        match node_exit cs with Some code => (COk (SExit code), m) | None => (CErr 3 p cs, m) end
      else (CErr 2 p cs, m)
  | PSpin => if node_spin segs cs then (COk SNil, m) else (CErr 2 p cs, m)
  | PFog i sz k => match node_fog cs i sz with Some cs' => cc f cs' k m | None => (CErr 3 p cs, m) end
  | PFogNew i sz k => match node_fognew cs i sz with Some cs' => cc f cs' k m | None => (CErr 3 p cs, m) end
  | PGhost b n k => match node_ghost LIMIT cs b n with Some cs' => cc f cs' k m | None => (CErr 3 p cs, m) end
  | PUnvis b n k => match node_unvis A cs b n with Some cs' => cc f cs' k m | None => (CErr 3 p cs, m) end
  | PHavocBrk lo hi k => match node_havocbrk nx0 cs lo hi with Some cs' => cc f cs' k m | None => (CErr 3 p cs, m) end
  | PIntro lo hi k => match node_intro nx0 cs lo hi with Some cs' => cc f cs' k m | None => (CErr 3 p cs, m) end
  | PRename mr k => match node_rename gcb cs mr with Some cs' => cc f cs' k m | None => (CErr 3 p cs, m) end
  | PCompact k => match node_compact gcb cs with Some cs' => cc f cs' k m | None => (CErr 3 p cs, m) end
  | PVia j _ lo karms k =>
      (* the arms, until a run of them changes no table entry; then the continuation from entry [j] *)
      let fix arms (n : nat) (m : gc_m) {struct n} : cres * gc_m :=
        match n with
        | O => (CErr 5 p cs, m)
        | S n' =>
            match cc_in f (Some (JC j (gc_jget (fst (fst m)) dflt j) SNil (nxt cs) lo)) cs karms m with
            | (COk _, m1) => if Nat.eqb (length (snd m1)) (length (snd m)) then (COk SNil, m1) else arms n' m1
            | err => err
            end
        end in
      match arms rounds m with
      | (COk _, m) =>
          let js := gc_jget (fst (fst m)) dflt j in
          if via_ok nx0 cs js lo then
            match cc f js k m with
            | (COk sk, m) => cc_in f (Some (JC j js sk (nxt cs) lo)) cs karms m
            | err => err
            end
          else (CErr 3 p cs, m)
      | err => err
      end
  | PMerge j =>
      match lc with
      | Some (JC j' _ sk _ lo) =>
          let '(Jt, Ht, lg) := m in
          let mok (t : gtab) := let js := gc_jget t dflt j in
            (Nat.eqb j j' && Z.eqb (pc cs) (pc js) && shape_vars_lt nx0 sk && entails_h A lo (nxt js) cs js)%bool in
          if mok Jt then (COk sk, m) else
          if negb (Nat.eqb j j') then (CErr 3 p cs, m) else
          let Jt' := gc_absorb Jt j cs in
          let m' := (Jt', Ht, gc_row 3 p cs :: lg) in
          if mok Jt' then (COk sk, m') else (CErr 3 p cs, m')
      | _ => (CErr 8 p cs, m)
      end
  | PAbstractCell b n k => match node_abstractcell A cs b n with Some cs' => cc f cs' k m | None => (CErr 3 p cs, m) end
  | PHavocWords bs k => match node_havocwords nx0 cs bs with Some cs' => cc f cs' k m | None => (CErr 3 p cs, m) end
  | PRespell r e k => match node_respell cs r e with Some cs' => cc f cs' k m | None => (CErr 3 p cs, m) end
  | PDiamond joinpc rs k =>
      match branch_probe IT cs with
      | Some e =>
          match crange (kn cs) e with
          | Some (lo, hi) =>
              if (Z.ltb hi 1 || Z.ltb 0 lo)%bool then
                match run_block_gc segs IT gcb KC bfuel (joinpc :: STOPS A) cs with
                | Some cs' => if Z.eqb (pc cs') joinpc then cc f cs' k m else (CErr 3 p cs', m)
                | None => (CErr 1 p cs, m)
                end
              else
                let cs1 := set_kn cs (KRange e lo 0 :: kn cs) in
                let cs2 := set_kn cs (KRange e 1 hi :: kn cs) in
                match run_block_gc segs IT gcb KC bfuel (joinpc :: STOPS A) cs1 with
                | Some ca =>
                    match run_block_gc segs IT gcb KC bfuel (joinpc :: STOPS A) cs2 with
                    | Some cb =>
                        match node_diamond_join A nx0 (nxt cs) joinpc rs ca cb with
                        | Some csj => cc f csj k m
                        | None => (CErr 3 p ca, m)
                        end
                    | None => (CErr 1 p cs2, m)
                    end
                | None => (CErr 1 p cs1, m)
                end
          | None => (CErr 3 p cs, m)
          end
      | None => (CErr 2 p cs, m)
      end
  end
  end.
End Coll.

(* one [gc_cc] run from the join seeds [J] and an empty hand-off table: its tables, its log (a row
   per entry it added or met, then [(0, 0, 0, 0)] when the run ended in [COk], or the row of the
   refusal that ended it) and the shape it returned *)
Definition gc_one (run : gc_m -> cres * gc_m) (J : gtab) : gc_out :=
  match run (J, [], []) with
  | (COk s, (J', H', lg)) => GCO (rev ((0, 0, 0, 0) :: lg)) J' H' (Some s)
  | (CErr c w cs, (J', H', lg)) => GCO (rev (gc_row c w cs :: lg)) J' H' None
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
